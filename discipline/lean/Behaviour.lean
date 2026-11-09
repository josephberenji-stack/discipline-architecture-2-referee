import Mathlib
import Lean

/-! THE BEHAVIOUR STEP (`BEHAVIOUR-DESIGN.md`, registered 899241a;  the readings of its words are `METHOD-LOG.md`
entry 16).  Not a check:  machine lines for `behaviour_report.py`'s `behaviour.tsv`.  `TIME` lines carry the clock (ms).

The text after the body marker line is pasted after the imports of the modules under review (Mathlib among them), as
`RefereeCore.lean` is.  It needs Mathlib:  the probe builders of the classes M, S and P are Mathlib's.

    BEHAVE  ROW   D  kind  shape  candidates                      (`#referee_behave_rows D …`)
    BEHAVE  CAND  D  N  ok  tested  value  failed                 (one per candidate with at least one law tested)
    BEHAVE  PAIR  D  N  ok  tested  value  failed                 (`#referee_behave_pairs D N …`, controls 4 and 7)

`value` is `agree`, `disagree` or `unchecked`;  `failed` is the comma-separated names of the laws that failed. -/

-- BODY (the marker:  everything below is pasted)

open Lean Meta Elab Command

namespace RefereeBehave

/-- a line out:  to the file named by `REFEREE_BEHAVE_FILE` as it is made (Lean holds a command's output until the
command ends), else to the command's output. -/
def emit (s : String) : IO Unit := do
  match ← IO.getEnv "REFEREE_BEHAVE_FILE" with
  | some f =>
    let h ← IO.FS.Handle.mk f .append
    h.putStrLn s!"BEHAVE\t{s}"
    h.flush
  | none => IO.println s!"BEHAVE\t{s}"

/-! ## 1. Shape:  the carrier classes (the table of `BEHAVIOUR-DESIGN.md` § 1) -/

/-- the carrier classes.  `X` is a carrier outside the table:  a shape holding one has no candidates. -/
inductive Cls where
  | N | W | M | S | P | R | C | F | Pr | X
  deriving BEq, Inhabited, Repr

def Cls.str : Cls → String
  | .N => "N" | .W => "W" | .M => "M" | .S => "S" | .P => "P" | .R => "R" | .C => "C" | .F => "F" | .Pr => "Prop"
  | .X => "X"

/-- `List α` with `α` read as a letter (the element type matters only for building probes). -/
def isListOf (t : Expr) : Bool := t.isAppOfArity ``List 1

/-- the class of one carrier.  Outside heads are read first;  a project constant is unfolded one step at a time (at
most 20 rounds) until an outside head or a quotient shows. -/
partial def clsOf (t : Expr) (fuel : Nat := 20) : MetaM Cls := do
  let t ← instantiateMVars t
  if t.isProp then return .Pr
  if t.isForall then
    -- F:  a sequence `ℕ → T` with T of class N, R or C
    let .forallE _ d b _ := t | return .X
    if b.hasLooseBVars then return .X
    if (← clsOf d fuel) == .N && (← whnfR d).isConstOf ``Nat then
      match ← clsOf b fuel with
      | .N | .R | .C => return .F
      | .Pr => return .S   -- a predicate on a finite type of class N (`Fin n → Prop`):  a subset
      | _ => return .X
    if (← whnfR d).isAppOf ``Fin then
      if (← clsOf b fuel) == .Pr || b.isConstOf ``Bool then return .S
    return .X
  let f := t.getAppFn
  match f.constName? with
  | some n =>
    if n == ``Nat || n == ``Int || n == ``Fin || n == ``ZMod then return .N
    if n == ``List || n == ``FreeMonoid then return .W
    if n == ``Multiset then return .M
    if n == ``Finset then return .S
    if n == ``Set then
      -- a set over a finite type
      let some a := t.getArg? 0 | return .X
      let fin ← (try (some <$> synthInstance (← mkAppM ``Finite #[a])) catch _ => pure none)
      return if fin.isSome then .S else .X
    if n == ``Polynomial || n == ``MvPolynomial then return .P
    if n == ``Real then return .R
    if n == ``Complex then return .C
    if n == ``Subtype then
      -- a list with a no-repeat condition
      let some a := t.getArg? 0 | return .X
      if isListOf (← whnfR a) then return .S
      return .X
    if n == ``Quotient || n == ``Quot then
      -- a quotient of lists:  by the permutation setoid (M), or of coefficient lists (P)
      let some a := t.getArg? 0 | return .X
      if !isListOf (← whnfR a) then return .X
      let isPerm := (t.getArg? 1).any fun s => s.isAppOf ``List.isSetoid
      return if isPerm then .M else .P
    if fuel == 0 then return .X
    match ← unfoldDefinition? t with
    | some t' => clsOf t' (fuel - 1)
    | none => return .X
  | none => return .X

/-- the type with its leading type parameters set to `ℕ` and its instances filled;  the arguments supplied.  Implicit
value binders before the first explicit one are left as metavariables (the `n` of `Fin n`). -/
partial def monoArgs (ty : Expr) : MetaM (Expr × Array Expr) := do
  match ty with
  | .forallE _ d b bi =>
    let isTy ← (do pure (← whnfD d).isSort) <|> pure false
    if isTy then
      let (t, a) ← monoArgs (b.instantiate1 (mkConst ``Nat))
      return (t, #[mkConst ``Nat] ++ a)
    else if bi.isInstImplicit then
      let some inst ← (try synthInstance? d catch _ => pure none) | return (ty, #[])
      let (t, a) ← monoArgs (b.instantiate1 inst)
      return (t, #[inst] ++ a)
    else if bi.isImplicit || bi.isStrictImplicit then
      let m ← mkFreshExprMVar d
      let (t, a) ← monoArgs (b.instantiate1 m)
      return (t, #[m] ++ a)
    else return (ty, #[])
  | _ => return (ty, #[])

/-- the shape:  the class of every explicit argument, then of the result. -/
partial def shapeOf (t : Expr) : MetaM (Array Cls) := do
  match t with
  | .forallE _ d b bi =>
    if bi.isImplicit || bi.isStrictImplicit then
      -- an implicit argument is inferred, not a carrier of the shape
      return ← shapeOf (b.instantiate1 (← mkFreshExprMVar d))
    if b.hasLooseBVars then
      -- a dependent arrow:  read under a local
      return ← withLocalDecl `x bi d fun x => do
        let rest ← shapeOf (b.instantiate1 x)
        if bi.isInstImplicit then return rest
        return #[← clsOf d] ++ rest
    if bi.isInstImplicit then return ← shapeOf b
    return #[← clsOf d] ++ (← shapeOf b)
  | _ => return #[← clsOf t]

def shapeStr (s : Array Cls) : String := " → ".intercalate (s.toList.map Cls.str)

/-- the number of explicit binders of a type, read without unfolding (a cheap filter before the shape). -/
def explicitArity (t : Expr) : Nat := Id.run do
  let mut e := t
  let mut n := 0
  while e.isForall do
    if e.bindingInfo! == .default then
      unless e.bindingDomain!.isSort do n := n + 1
    e := e.bindingBody!
  return n

/-- the shape of a declaration at `ℕ`. -/
def declShape (ci : ConstantInfo) : MetaM (Array Cls × Expr × Array Expr) := do
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  let (t, args) ← monoArgs (ci.type.instantiateLevelParams ci.levelParams us)
  return (← shapeOf t, t, args)

/-! ## 2. Probes (`BEHAVIOUR-DESIGN.md` § 2):  one literal set per class, built by each side's own constructors -/

/-- N:  0 to 6. -/
def nLits : List Nat := [0, 1, 2, 3, 4, 5, 6]

/-- W:  the words over {0, 1, 2} of length at most 3 (40 words). -/
def wLits : List (List Nat) :=
  let l1 := [0, 1, 2].map fun a => [a]
  let l2 := [0, 1, 2].flatMap fun a => [0, 1, 2].map fun b => [a, b]
  let l3 := [0, 1, 2].flatMap fun a => [0, 1, 2].flatMap fun b => [0, 1, 2].map fun c => [a, b, c]
  [[]] ++ l1 ++ l2 ++ l3

/-- M:  the multisets of those words (each word read up to order:  20 multisets). -/
def mLits : List (List Nat) :=
  wLits.foldl (fun acc w => let s := w.mergeSort (· ≤ ·); if acc.contains s then acc else acc ++ [s]) []

/-- S:  the subsets of {0, 1, 2}. -/
def sLits : List (List Nat) :=
  [[], [0], [1], [2], [0, 1], [0, 2], [1, 2], [0, 1, 2]]

/-- P:  coefficient lists (lowest degree first) of the polynomials of degree at most 3 over `ZMod q`. -/
def pLits (q : Nat) : List (List Nat) := Id.run do
  let mut out := []
  for a in List.range q do
    for b in List.range q do
      for c in List.range q do
        for d in List.range q do
          out := out ++ [[a, b, c, d]]
  return out

/-- the numeral `n` in the type `T` (`OfNat`), or `none`. -/
def numIn (T : Expr) (n : Nat) : MetaM (Option Expr) := do
  try return some (← mkNumeral T n) catch _ => return none

/-- a list literal in `List A`, its letters numerals of `A`. -/
def listIn (A : Expr) (w : List Nat) : MetaM (Option Expr) := do
  let mut es := #[]
  for a in w do
    let some e ← numIn A a | return none
    es := es.push e
  try return some (← mkListLit A es.toList) catch _ => return none

/-- the probes of a carrier `T`, by its class;  `none` when the class has no probes (R, C, X) or a literal cannot be
built in `T`. -/
partial def probesOf (T : Expr) : MetaM (Option (Array Expr)) := do
  let T ← instantiateMVars T
  if T.hasMVar then return none
  let cls ← clsOf T
  let build (xs : List Expr) : MetaM (Option (Array Expr)) := do
    -- each probe must have the carrier's type
    let mut out := #[]
    for x in xs do
      unless ← (try isDefEq (← inferType x) T catch _ => pure false) do return none
      out := out.push x
    return some out
  match cls with
  | .N =>
    let mut xs := []
    for n in nLits do
      let some e ← numIn T n | return none
      xs := xs ++ [e]
    build xs
  | .W =>
    let Tw ← whnfR T
    if Tw.isAppOfArity ``List 1 then
      let A := Tw.getArg! 0
      let mut xs := []
      for w in wLits do
        let some e ← listIn A w | return none
        xs := xs ++ [e]
      return ← build xs
    if Tw.isAppOfArity ``FreeMonoid 1 then
      let A := Tw.getArg! 0
      let mut xs := []
      for w in wLits do
        let some e ← listIn A w | return none
        xs := xs ++ [← mkAppM ``FreeMonoid.ofList #[e]]
      return ← build xs
    return none
  | .M =>
    -- `Multiset` and a project quotient of lists by permutation:  the quotient map applied to the word
    let Tq ← whnfR T
    let Tq ← if Tq.isAppOf ``Multiset then whnfD Tq else pure Tq
    let Tq ← if Tq.isAppOf ``Quotient || Tq.isAppOf ``Quot then pure Tq else whnfD Tq
    unless Tq.isAppOf ``Quotient || Tq.isAppOf ``Quot do return none
    let A := (← whnfR (Tq.getArg! 0)).getArg! 0
    let mut xs := []
    for w in mLits do
      let some l ← listIn A w | return none
      let e ← if Tq.isAppOf ``Quotient then mkAppOptM ``Quotient.mk #[Tq.getArg! 0, Tq.getArg! 1, l]
              else mkAppOptM ``Quot.mk #[Tq.getArg! 0, Tq.getArg! 1, l]
      xs := xs ++ [e]
    build xs
  | .S =>
    let Tw ← whnfR T
    if Tw.isAppOfArity ``Finset 1 || Tw.isAppOfArity ``Set 1 then
      let A := Tw.getArg! 0
      let mut xs := []
      for s in sLits do
        let some l ← listIn A s | return none
        let e ← if Tw.isAppOf ``Finset then mkAppM ``List.toFinset #[l]
                else mkAppM ``setOf #[← withLocalDeclD `x A fun x => do
                  mkLambdaFVars #[x] (← mkAppM ``Membership.mem #[l, x])]
        xs := xs ++ [e]
      return ← build xs
    return none
  | .P =>
    let Tw ← whnfR T
    if Tw.isAppOfArity ``Polynomial 2 then
      let R := Tw.getArg! 0
      let q ← if (← isDefEq R (← mkAppM ``ZMod #[mkNatLit 2])) then pure 2
              else if (← isDefEq R (← mkAppM ``ZMod #[mkNatLit 3])) then pure 3 else pure 0
      if q == 0 then return none
      let mut xs := []
      for cs in pLits q do
        -- c₀ + c₁ X + c₂ X² + c₃ X³, each coefficient by `Polynomial.C`
        let mut acc ← mkAppOptM ``OfNat.ofNat #[T, mkRawNatLit 0, none]
        for i in [0:cs.length] do
          let some c ← numIn R cs[i]! | return none
          let mono ← mkAppM ``HMul.hMul #[← mkAppM ``Polynomial.C #[c],
            ← mkAppM ``HPow.hPow #[← mkAppOptM ``Polynomial.X #[R, none], mkNatLit i]]
          acc ← mkAppM ``HAdd.hAdd #[acc, mono]
        xs := xs ++ [acc]
      return ← build xs
    -- a project quotient of coefficient lists over `Fin q` (q = 2, 3) or ℕ:  the quotient map of the list
    let Tq ← whnfD T
    unless Tq.isAppOf ``Quot || Tq.isAppOf ``Quotient do return none
    let A := (← whnfR (Tq.getArg! 0)).getArg! 0
    let mut xs := []
    for q in [2, 3] do
      for cs in pLits q do
        let some l ← listIn A cs | return none
        let e ← if Tq.isAppOf ``Quotient then mkAppOptM ``Quotient.mk #[Tq.getArg! 0, Tq.getArg! 1, l]
                else mkAppOptM ``Quot.mk #[Tq.getArg! 0, Tq.getArg! 1, l]
        xs := xs ++ [e]
    build xs
  | .F =>
    -- `n ↦ c` (c = 1), `n ↦ n`, `n ↦ 1/(n+1)`, in the sequence's value type
    let .forallE _ _ V _ := T | return none
    let some one ← numIn V 1 | return none
    let c ← withLocalDeclD `n (mkConst ``Nat) fun n => mkLambdaFVars #[n] one
    let idf ← withLocalDeclD `n (mkConst ``Nat) fun n => do
      mkLambdaFVars #[n] (← (try mkAppOptM ``Nat.cast #[V, none, n] catch _ => pure n))
    let inv ← withLocalDeclD `n (mkConst ``Nat) fun n => do
      let nv ← (try mkAppOptM ``Nat.cast #[V, none, n] catch _ => pure n)
      mkLambdaFVars #[n] (← mkAppM ``HDiv.hDiv #[one, ← mkAppM ``HAdd.hAdd #[nv, one]])
    build [c, idf, inv]
  | _ => return none

/-! ## 3. Laws (`BEHAVIOUR-DESIGN.md` § 3) -/

/-- the module of a constant, as a name. -/
def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

/-- a declaration of the core (`Init`), or of this file's prelude. -/
def isCore (env : Environment) (c : Name) : Bool :=
  match moduleOf env c with
  | some m => m.getRoot == `Init
  | none => false

/-- a project declaration:  its module's root is one of `roots`. -/
def isProject (env : Environment) (roots : List Name) (c : Name) : Bool :=
  match moduleOf env c with
  | some m => roots.contains m.getRoot
  | none => true   -- declared in the check file itself (the planted controls)

/-- the probe builders of a class (the shared vocabulary beside the core). -/
def builders : Cls → List Name
  | .N => [``Nat, ``Int, ``Fin, ``ZMod, ``OfNat.ofNat, ``Nat.cast, ``Int.cast]
  | .W => [``List, ``FreeMonoid, ``FreeMonoid.ofList, ``FreeMonoid.toList]
  | .M => [``Multiset, ``Multiset.ofList, ``Quotient.mk, ``Quot.mk, ``Quotient, ``Quot]
  | .S => [``Finset, ``Set, ``List.toFinset, ``setOf, ``Membership.mem]
  | .P => [``Polynomial, ``Polynomial.C, ``Polynomial.X, ``MvPolynomial, ``MvPolynomial.C, ``MvPolynomial.X]
  | .R => [``Real]
  | .C => [``Complex]
  | .F => []
  | .Pr => []
  | .X => []

/-- a constant that does not count against the vocabulary:  an instance, a name Lean generates, a theorem (a proof
inside a type), or one of the type classes of arithmetic and order the core states its laws with. -/
def freeConst (env : Environment) (c : Name) : Bool :=
  c.isInternal || Meta.isInstanceCore env c || (match env.find? c with | some (.thmInfo _) => true | _ => false)

/-- a law of `N`:  an outside theorem with an `=` or `↔` conclusion that mentions `N`, every other constant of which is
in the core, among the probe builders of the shape's classes, or free. -/
def isLawOf (env : Environment) (vocab : NameSet) (n : Name) (ty : Expr) : Bool := Id.run do
  let mut e := ty
  while e.isForall do e := e.bindingBody!
  unless e.isAppOf ``Eq || e.isAppOf ``Iff do return false
  let cs := ty.getUsedConstants
  unless cs.contains n do return false
  return cs.all fun c => c == n || isCore env c || vocab.contains c || freeConst env c

/-! ## 4. Transport and check (`BEHAVIOUR-DESIGN.md` § 4) -/

/-- replace every application of `n` to its `k` leading arguments by `d`;  a Bool-valued `d` against a Prop-valued `n`
is read as `d … = true`;  a bundled function (`⇑N x`) as `d x`. -/
def subst (e : Expr) (n : Name) (k : Nat) (d : Expr) (toProp : Bool) : Expr :=
  e.replace fun x =>
    if x.isAppOf ``DFunLike.coe && x.getAppNumArgs ≥ 5 && (x.getArg! 4).getAppFn.isConstOf n then
      some (mkAppN d (x.getAppArgs.extract 5 x.getAppNumArgs))
    else if x.getAppFn.isConstOf n && x.getAppNumArgs ≥ k then
      let r := mkAppN d (x.getAppArgs.extract k x.getAppNumArgs)
      some (if toProp then mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) r (mkConst ``true) else r)
    else none

/-- the time limits, milliseconds:  2 s per law by `decide`, 10 s per law by the fixed script. -/
def decideMs : Nat := 2000
def scriptMs : Nat := 10000

/-- the heartbeat cap of one `decide` (a single reduction cannot be stopped by the clock;  the clock is read between
probe tuples). -/
def tupleHeartbeats : Nat := 20000000

def holds (p : Expr) : MetaM (Option Bool) := do
  tryCatchRuntimeEx (withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := tupleHeartbeats }) do
    let d ← mkDecide p
    let r ← withTransparency .default <| whnf d
    if r.isConstOf ``true then return some true
    if r.isConstOf ``false then return some false
    return none) (fun _ => return none)

/-- the law on every probe tuple:  `some true` (every tuple holds), `some false` (one fails), `none` (not testable:
a binder with no probes, a body that does not reduce, or the clock ran out). -/
partial def checkLaw (e : Expr) (deadline : Nat) : MetaM (Option Bool) := do
  if (← IO.monoMsNow) > deadline then return none
  match e with
  | .forallE _ d b bi =>
    if b.hasLooseBVars then
      if (← whnfD d).isSort then return ← checkLaw (b.instantiate1 (mkConst ``Nat)) deadline
      if bi.isInstImplicit then
        let some inst ← (try synthInstance? d catch _ => pure none) | return none
        return ← checkLaw (b.instantiate1 inst) deadline
      let some ps ← probesOf d | return none
      let mut tested := false
      for v in ps do
        match ← checkLaw (b.instantiate1 v) deadline with
        | some false => return some false
        | some true => tested := true
        | none => return none
      return if tested then some true else none
    else
      -- a hypothesis:  decided on the probe;  a false hypothesis makes the instance vacuous (it holds)
      if !(← (try isProp d catch _ => pure false)) then return none
      match ← holds d with
      | some true => checkLaw b deadline
      | some false => return some true
      | none => return none
  | _ =>
    if !(← (try isProp e catch _ => pure false)) then return none
    holds e

/-- the evaluator:  a closed `Bool` term run by Lean's compiled-code evaluator. -/
unsafe def evalBoolUnsafe (e : Expr) : MetaM Bool := Meta.evalExpr Bool (mkConst ``Bool) e

@[implemented_by evalBoolUnsafe]
opaque evalBool (e : Expr) : MetaM Bool

/-- the law as one `Bool` term:  every binder with probes becomes `List.all` over its probe list, a hypothesis
`¬ decide h ∨ …`, the conclusion `decide`.  `none` when a binder has no probes or a proposition is not decidable. -/
partial def lawTerm (e : Expr) : MetaM (Option Expr) := do
  match e with
  | .forallE n d b bi =>
    if b.hasLooseBVars then
      if (← whnfD d).isSort then return ← lawTerm (b.instantiate1 (mkConst ``Nat))
      if bi.isInstImplicit then
        let some inst ← (try synthInstance? d catch _ => pure none) | return none
        return ← lawTerm (b.instantiate1 inst)
      if (← (try isProp d catch _ => pure false)) then return none
      let some ps ← probesOf d | return none
      let l ← mkListLit d ps.toList
      withLocalDeclD n d fun x => do
        let some inner ← lawTerm (b.instantiate1 x) | return none
        let f ← mkLambdaFVars #[x] inner
        return some (← mkAppM ``List.all #[l, f])
    else
      if !(← (try isProp d catch _ => pure false)) then return none
      let some hd ← (try some <$> mkDecide d catch _ => pure none) | return none
      let some inner ← lawTerm b | return none
      return some (← mkAppM ``or #[← mkAppM ``not #[hd], inner])
  | _ =>
    if !(← (try isProp e catch _ => pure false)) then return none
    try return some (← mkDecide e) catch _ => return none

/-- the law decided on every probe tuple by the evaluator, in one run;  `none` when it cannot be built or run, or the
run took longer than the law's 2 s. -/
def checkLawEval (e : Expr) : MetaM (Option Bool) := do
  let some t ← lawTerm e | return none
  let t ← instantiateMVars t
  if t.hasMVar || t.hasFVar then return none
  let t0 ← IO.monoMsNow
  let r ← (try some <$> evalBool t catch _ => pure none)
  if (← IO.monoMsNow) - t0 > decideMs then return none
  return r

/-- the fixed script of § 4 for a shape with R or C. -/
def scriptCheck (e : Expr) (dn : Name) : TermElabM Bool := do
  let deadline := (← IO.monoMsNow) + scriptMs
  tryCatchRuntimeEx (withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 200000000 }) do
    let g ← mkFreshExprMVar e
    let tac ← `(tactic| (intros; simp only [$(mkIdent dn):ident]; first | rfl | (constructor <;> intro h <;> exact h) | aesop))
    let gs ← Term.withoutErrToSorry <| Tactic.run g.mvarId! (Tactic.evalTactic tac)
    if (← IO.monoMsNow) > deadline then return false
    return gs.isEmpty) (fun _ => pure false)

/-- value agreement:  on every probe tuple of `D`'s arguments where `N` is applied to the same literals, the two
values are equal.  Checked only where the two sides take the same carriers and `N` computes. -/
partial def agreeGo (t : Expr) (dacc nacc : Expr) (fuel : Nat) : MetaM (Option Bool) := do
  match t with
  | .forallE _ d b _ =>
    if fuel == 0 then return none
    let some ps ← probesOf d | return none
    let mut any := false
    for v in ps do
      match ← agreeGo (b.instantiate1 v) (mkApp dacc v) (mkApp nacc v) (fuel - 1) with
      | some false => return some false
      | some true => any := true
      | none => return none
    return if any then some true else none
  | _ =>
    if t.isProp then holds (← mkAppM ``Iff #[dacc, nacc])
    else holds (← mkEq dacc nacc)

def valueAgree (dhead nhead : Expr) : MetaM String := do
  let dt ← inferType dhead
  let nt ← inferType nhead
  unless ← (try isDefEq dt nt catch _ => pure false) do return "unchecked"
  match ← agreeGo (← instantiateMVars dt) dhead nhead 4 with
  | some true => return "agree"
  | some false => return "disagree"
  | none => return "unchecked"

/-- the result type after every arrow. -/
def resultOf (t : Expr) : Expr := Id.run do
  let mut e := t
  while e.isForall do e := e.bindingBody!
  return e

/-- the size of a law's statement (for "the 50 shortest"). -/
def lawSize (ty : Expr) : Nat := ty.sizeWithoutSharing

/-- the project roots, read from the environment variable `REFEREE_BEHAVE_ROOTS` (comma-separated). -/
def projectRoots : IO (List Name) := do
  let s := (← IO.getEnv "REFEREE_BEHAVE_ROOTS").getD "F1Lib,F1M,F1H,F1C1,F1C3,EngineV7,F1Program,Labels,LabelsNext"
  return (s.splitOn ",").map String.toName

/-- the head of `D` read at `ℕ`, its type there, and whether it is Bool-valued. -/
def readD (dn : Name) : MetaM (Expr × Expr × Array Cls) := do
  let some dci := (← getEnv).find? dn | throwError "unknown {dn}"
  let (s, t, args) ← declShape dci
  let us := dci.levelParams.map fun _ => Level.zero
  let h ← instantiateMVars (mkAppN (mkConst dn us) args)
  return (h, ← instantiateMVars t, s)

/-- a law's leading type parameters set to `ℕ` and its leading instances filled;  the binders after them kept. -/
partial def lawMono (ty : Expr) : MetaM Expr := do
  match ty with
  | .forallE _ d b bi =>
    let isTy ← (do pure (← whnfD d).isSort) <|> pure false
    if isTy then
      unless ← isDefEq (← inferType (mkConst ``Nat)) d do return ty
      return ← lawMono (b.instantiate1 (mkConst ``Nat))
    if bi.isInstImplicit then
      let some inst ← (try synthInstance? (← instantiateMVars d) catch _ => pure none) | return ty
      return ← lawMono (b.instantiate1 inst)
    return ty
  | _ => return ty

/-- score one candidate `N` (with `k` leading arguments set by `monoArgs`) for `D`:  the 50 shortest laws of `N`,
transported and checked.  Returns (ok, tested, failed laws, value). -/
def scoreOne (dn : Name) (dhead dty : Expr) (dshape : Array Cls) (nn : Name) (k : Nat) (nargs : Array Expr)
    (toProp : Bool) (laws : Array Name) : TermElabM (Nat × Nat × Array Name × String) := do
  let env ← getEnv
  let script := dshape.contains .R || dshape.contains .C
  let debug := (← IO.getEnv "REFEREE_BEHAVE_DEBUG").isSome
  let mut ok := 0
  let mut tested := 0
  let mut failed := #[]
  for l in laws do
    let some lci := env.find? l | continue
    let (r?, why) : Option Bool × String ← tryCatchRuntimeEx (withNewMCtxDepth do
      let us ← lci.levelParams.mapM fun _ => mkFreshLevelMVar
      let lty := lci.type.instantiateLevelParams lci.levelParams us
      -- the law's leading type parameters are set to `ℕ` and its instances filled, as `D` is read at `ℕ`
      let lty ← lawMono lty
      let e := subst lty nn k dhead toProp
      -- the transported statement must be well typed
      let e ← instantiateMVars e
      unless (← (try Meta.check e; pure true catch _ => pure false)) do return (none, "ill-typed")
      if script then
        if e.hasMVar then return (none, "metavariables")
        return (some (← scriptCheck e dn), "script")
      -- the evaluator first (one run over every tuple);  where it cannot run, `decide` by reduction
      match ← checkLawEval e with
      | some r => return (some r, "eval")
      | none => return (← checkLaw e ((← IO.monoMsNow) + decideMs), "whnf")) (fun ex => do
        pure (none, s!"exception {(← ex.toMessageData.toString).take 80}"))
    if debug then emit s!"LAW\t{dn}\t{nn}\t{l}\t{r?}\t{why}"
    match r? with
    | some true => ok := ok + 1; tested := tested + 1
    | some false => tested := tested + 1; failed := failed.push l
    | none => pure ()
  let value ← tryCatchRuntimeEx (do
    if nargs.any (·.hasMVar) then return "unchecked"
    let some nci := env.find? nn | return "unchecked"
    let nhead := mkAppN (mkConst nn (nci.levelParams.map fun _ => Level.zero)) nargs
    if toProp then return "unchecked"
    valueAgree dhead nhead) (fun _ => pure "unchecked")
  return (ok, tested, failed, value)

/-- the law index:  for every name in `cs`, the outside theorems with an `=` or `↔` conclusion that mention it, with
the size of their statements.  One pass over the environment for all rows;  the vocabulary is applied per row. -/
def lawIndex (roots : List Name) (cs : NameSet) : CoreM (Std.HashMap Name (Array (Nat × Name))) := do
  let env ← getEnv
  let mut m : Std.HashMap Name (Array (Nat × Name)) := {}
  for (t, ci) in env.constants.map₁.toList do
    unless ci matches .thmInfo _ do continue
    if t.isInternal || isProject env roots t then continue
    let e := resultOf ci.type
    unless e.isAppOf ``Eq || e.isAppOf ``Iff do continue
    for c in ci.type.getUsedConstants do
      if cs.contains c then
        m := m.insert c (((m.get? c).getD #[]).push (lawSize ci.type, t))
  return m

/-- the laws of `n` for a row:  those of the index in the row's vocabulary. -/
def lawsOf (env : Environment) (idx : Std.HashMap Name (Array (Nat × Name))) (vocab : NameSet) (n : Name) :
    Array (Nat × Name) :=
  ((idx.get? n).getD #[]).filter fun (_, t) =>
    match env.find? t with
    | some ci => isLawOf env vocab n ci.type
    | none => false

def take50 (xs : Array (Nat × Name)) : Array Name :=
  ((xs.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.toString < b.2.toString)).extract 0 50).map (·.2)

def vocabOf (shape : Array Cls) : NameSet :=
  shape.foldl (fun s c => (builders c).foldl (·.insert ·) s) {}

def joinNames (xs : Array Name) : String := if xs.isEmpty then "-" else ",".intercalate (xs.toList.map toString)

/-- the kind of a declaration, as the report prints it. -/
def kindOf (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"

/-- the candidates of one row:  outside definitions and inductive types of the row's shape. -/
structure Row where
  dn : Name
  dhead : Expr
  dty : Expr
  shape : Array Cls
  boolRes : Bool
  cands : Array (Name × Nat × Array Expr × Bool) := #[]
  deriving Inhabited

/-- `#referee_behave_rows D₁ D₂ …`:  for each row, the candidates of its shape among the outside definitions,
structures, classes and inductive relations, each scored on its laws;  one `ROW` line per row and one `CAND` line per
candidate with a law tested.  One pass over the environment for the candidates and one for the laws, for all rows. -/
elab "#referee_behave_rows " ds:ident* : command => liftTermElabM do
  let env ← getEnv
  let roots ← projectRoots
  let mut rows : Array Row := #[]
  for d in ds do
    let dn ← realizeGlobalConstNoOverloadWithInfo d
    let some dci := env.find? dn | throwError "unknown {dn}"
    -- a theorem is not decoded:  the step decodes definitions (`BEHAVIOUR-DESIGN.md`, the rows `inversion`, …)
    if dci matches .thmInfo _ then
      emit s!"ROW\t{dn}\ttheorem\t-\t0"
      continue
    let (dhead, dty, dshape) ← readD dn
    if dshape.contains .X then
      emit s!"ROW\t{dn}\t{kindOf dci}\t{shapeStr dshape}\t0"
      continue
    rows := rows.push { dn, dhead, dty, shape := dshape, boolRes := (← whnfR (resultOf dty)).isConstOf ``Bool }
  let arities := rows.map (·.shape.size - 1)
  emit s!"TIME\tscan\t{← IO.monoMsNow}"
  for (c, ci) in env.constants.map₁.toList do
    let ok := match ci with
      | .defnInfo _ => true
      | .inductInfo _ => true
      | _ => false
    unless ok do continue
    if c.isInternal || isProject env roots c then continue
    unless arities.contains (explicitArity ci.type) do continue
    let r? ← tryCatchRuntimeEx (withNewMCtxDepth do
      let (s, _, args) ← declShape ci
      let args ← args.mapM instantiateMVars
      return some (s, args)) (fun _ => pure none)
    let some (s, args) := r? | continue
    for i in [0:rows.size] do
      let r := rows[i]!
      if s == r.shape then
        rows := rows.set! i { r with cands := r.cands.push (c, args.size, args, false) }
      else if r.boolRes && s.size == r.shape.size && s.back? == some .Pr &&
          (s.extract 0 (s.size - 1)) == (r.shape.extract 0 (r.shape.size - 1)) then
        rows := rows.set! i { r with cands := r.cands.push (c, args.size, args, true) }
  for r in rows do
    emit s!"ROW\t{r.dn}\t{kindOf (env.find? r.dn).get!}\t{shapeStr r.shape}\t{r.cands.size}"
  emit s!"TIME\tcandidates\t{← IO.monoMsNow}"
  let cset : NameSet := rows.foldl (fun s r => r.cands.foldl (fun s (c, _) => s.insert c) s) {}
  let idx ← lawIndex roots cset
  emit s!"TIME\tlaws\t{← IO.monoMsNow}"
  for r in rows do
    let vocab := vocabOf r.shape
    for (c, k, args, tp) in r.cands do
      let ls := take50 (lawsOf env idx vocab c)
      if ls.isEmpty then continue
      let (ok, tested, failed, value) ← scoreOne r.dn r.dhead r.dty r.shape c k args tp ls
      if tested > 0 then
        emit s!"CAND\t{r.dn}\t{c}\t{ok}\t{tested}\t{value}\t{joinNames failed}"
    emit s!"TIME\t{r.dn}\tscored\t{← IO.monoMsNow}"

/-- `#referee_behave_pairs D₁ N₁ D₂ N₂ …`:  each `D` scored on its `N`'s laws whatever the two shapes (controls 4 and
7);  one `PAIR` line each. -/
elab "#referee_behave_pairs " xs:ident* : command => liftTermElabM do
  let env ← getEnv
  let roots ← projectRoots
  let mut pairs : Array (Name × Name) := #[]
  for i in [0:xs.size / 2] do
    pairs := pairs.push (← realizeGlobalConstNoOverloadWithInfo xs[2 * i]!,
                         ← realizeGlobalConstNoOverloadWithInfo xs[2 * i + 1]!)
  let nset : NameSet := pairs.foldl (fun s (_, n) => s.insert n) {}
  let idx ← lawIndex roots nset
  for (dn, nn) in pairs do
    let some dci := env.find? dn | throwError "unknown {dn}"
    let some nci := env.find? nn | throwError "unknown {nn}"
    if dci matches .thmInfo _ then
      emit s!"PAIR\t{dn}\t{nn}\t0\t0\tunchecked\t-"
      continue
    let r? ← tryCatchRuntimeEx (withNewMCtxDepth do
      let (dhead, dty, dshape) ← readD dn
      let (nshape, _, nargs) ← declShape nci
      let nargs ← nargs.mapM instantiateMVars
      let boolRes := (← whnfR (resultOf dty)).isConstOf ``Bool
      let tp := boolRes && nshape.back? == some .Pr
      let ls := take50 (lawsOf env idx (vocabOf (dshape ++ nshape)) nn)
      some <$> scoreOne dn dhead dty dshape nn nargs.size nargs tp ls) (fun _ => pure none)
    match r? with
    | some (ok, tested, failed, value) => emit s!"PAIR\t{dn}\t{nn}\t{ok}\t{tested}\t{value}\t{joinNames failed}"
    | none => emit s!"PAIR\t{dn}\t{nn}\t0\t0\tunchecked\t-"

end RefereeBehave
