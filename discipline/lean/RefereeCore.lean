/-
  RefereeCore.lean -- the Lean half of the referee.  This text is not a module:  `referee_lean.py` pastes it, after
  the imports of the modules under review, into a generated check file, with the project's roots and its two
  registries (`@@ROOTS@@`, `@@OPEN@@`, `@@TARGETS@@`) filled in from `registry.tsv`.  Every check prints one machine line
      REFEREE<TAB>check<TAB>theorem<TAB>status<TAB>detail
  with status PASS, FAIL, REVIEW (a person or a literature reading must decide) or INFO;  the Python half reads only
  these lines.  `REFEREE_OFF` (a list of check names, filled in by `--mutate`) switches checks off so that the
  self-test can show each check is needed.

  THE CHECKS.
    L0 axioms        the theorem depends on propext, Classical.choice, Quot.sound only (`sorryAx`, `native_decide`'s
                     auxiliary axioms and every declared `axiom` fail).
    L1 stand-ins     no constant the theorem reaches (its statement and proof, through every project declaration they
                     use, definitions included) is `opaque`, `unsafe`, `partial`, `@[implemented_by]` or `@[extern]`:
                     each of these is a name whose meaning the kernel does not see (FAIL).  An `opaque` given an
                     explicit value is REVIEW, not FAIL:  the kernel checked the value but no theorem can read it, so
                     a person (or an unpacking step) must look at what it hides.  An `opaque` with no value (its value
                     is the type's `default`) is FAIL.
    L2 hypotheses    every hypothesis of the statement (an explicit or instance binder whose type is a proposition, a
                     project structure with a proposition field, or a project class with a proposition field) is
                     either a side condition on the theorem's own parameters built from core relations, or is
                     inhabited by a declaration on file (closed theorem, definition or instance of that exact type).
                     An uninhabited closed hypothesis is UNBUILT (FAIL for any claim stronger than C);  a hypothesis
                     that mentions a project proposition (a `def ... : Prop` of the project) is REVIEW:  it may carry
                     the hard part.
    L3 refuted       a hypothesis whose negation (`¬ T`, `T → False`, `IsEmpty T`) is a declaration on file makes the
                     theorem VACUOUS (FAIL), unless it is a reduction:  its conclusion is no registered open problem
                     and another declaration on file uses it (REVIEW, class RED:  the implication is the result).
    L4 names         every backticked identifier of the module's doc header resolves to a declaration (done in Python
                     from the `#referee_names` lines, which print every resolvable name of the module).
    R1 structural    the proof reaches no theorem outside the project and outside the logic core:  it holds by
                     unfolding definitions and logic alone (DEF).
    R2 restatement   the conclusion is an `↔` with a registered open problem on a side (B, restatement).
    R3 conditional   the conclusion is a registered open problem and the statement has hypotheses (C).
    R4 target gate   the type is definitionally a registered target statement, with no binders at all.  Even then
                     the status is REVIEW:  a person confirms the registered statement is the published one.
    R1i inputs       every theorem the proof uses whose conclusion is a project proposition (a `def … : Prop`, a
                     named input of a staged argument) carries content of its own (R1 run on the supplier):  an input
                     supplied by a theorem that holds by unfolding and logic alone is REVIEW (the hard step may have
                     moved into a definition).
    DUP twins        no two project definitions the theorem reaches have identical types and values under different
                     names, unless a project theorem states their equivalence (`↔`, `=` or `≃` between them):  twins
                     without such a bridge are REVIEW.
    SHADOW copies    no project declaration the theorem reaches is a copy of a library declaration (its name, with the
                     project root removed, is a library constant of the same type):  a copy decides what a name means
                     by namespace or import order (REVIEW).
    R1k carrier      what carries the theorem, printed as the row's status (like CLASS) and changing no verdict:  CONTENT
                     (R1 passes), else FIELD (a proposition field of a project structure or class is read:  an axiom
                     stored in a record), HYP (a hypothesis is a project proposition), IND (a recursor of a project type),
                     UNFOLD (definitions and logic only).  The walk is R1's, recording everything instead of stopping.
    UNFOLD           (`#referee_unfold`, not a check) the machine account of every declaration of a module:  kinds, the
                     constants each uses, what carries each theorem, the fields of each structure, the instances.  The
                     Python half reads it for the package checks UNFOLD, BRIDGED and CARRIER (UNFOLD-DESIGN.md).
    L7 storage       (off unless asked for) per module:  no outside-library object (a type, an instance, an
                     operation, a predicate) is reached by a statement or a definition of the module, directly or
                     through another project file (FAIL);  one reached only inside proofs is REVIEW;  a `Bridge`
                     module may hold them, and nothing else may read a bridge (FAIL).  For a project that rebuilds its
                     objects and uses the outside library only to show equivalence.
-/
import Lean
open Lean Meta Elab Command

namespace RefereeCore

/-- the project's root namespaces (from `registry.tsv`, kind `root`);  every module outside Lean's core and the
outside libraries is the project's as well (`isProjectModule`). -/
def projectRoots : List Name := @@ROOTS@@ ++ [`RefereeControls]
/-- the logic core:  theorems of these prefixes do not count as content for R1. -/
def logicCore : List Name := [`Iff, `Eq, `And, `Or, `Exists, `PLift, `ULift, `Subsingleton, `True, `False, `Not,
  `id, `absurd, `congrArg, `congrFun, `congr, `propext, `funext, `Nonempty, `HEq, `cast, `of_eq_true, `eq_self,
  `eq_true, `implies_true, `forall_const, `PUnit, `Unit, `trivial, `rfl, `Quot, `exists_prop, `and_self,
  `iff_self, `not_not, `Function.comp, `Classical.choice, `Classical.em, `Classical.byContradiction,
  `Classical.not_not, `forall_true_iff, `true_and, `and_true, `imp_self, `iff_true, `true_iff]
def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]
/-- relations a side condition may be built from (on the theorem's own parameters). -/
def coreRelations : List Name := [`Ne, `Eq, `LE.le, `LT.lt, `GE.ge, `GT.gt, `Not, `And, `Or, `Iff, `Membership.mem,
  `Dvd.dvd, `Nat.Prime, `Prime, `NeZero, `Finite, `Fintype, `Nonempty, `IsEmpty, `HasSubset.Subset, `Odd, `Even,
  `True, `False]

def openProblems : List Name := @@OPEN@@
def targetStatements : List Name := @@TARGETS@@
def off : List String := @@OFF@@

def emit (check thm status detail : String) : CommandElabM Unit :=
  logInfo m!"REFEREE\t{check}\t{thm}\t{status}\t{detail}"

/-- Lean's core and the outside libraries:  every other module is the project's, not only the names of
`projectRoots`. -/
def notProjectLibs : List Name := [`Init, `Std, `Lean, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
  `ImportGraph, `LeanSearchClient, `Cli]

/-- a module of the project:  under a project root, or under none of Lean's core and the outside libraries. -/
def isProjectModule (m : Name) : Bool :=
  projectRoots.any (·.isPrefixOf m) || !notProjectLibs.any (·.isPrefixOf m)

def inProject (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => isProjectModule (env.header.moduleNames[i.toNat]!)
  | none => true

def isCore (c : Name) : Bool := logicCore.any (fun r => r.isPrefixOf c || r == c)

/-- every constant reachable from `n` through project declarations (statement and value). -/
partial def closure (env : Environment) (n : Name) (seen : NameSet) : NameSet := Id.run do
  let some ci := env.find? n | return seen
  let mut s := seen
  let cs := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
  for c in cs do
    if s.contains c then continue
    s := s.insert c
    if inProject env c then s := closure env c s
  return s

/-- what a statement means:  the constants reached from a type, through the types and values of the project
definitions it uses (a definition's value is part of what the statement says).  An `opaque` is recorded and not
entered (its value is hidden from the statement);  a theorem contributes its type only. -/
partial def stmtClosure (env : Environment) (e : Expr) (seen : NameSet) : NameSet := Id.run do
  let mut s := seen
  for c in e.getUsedConstants do
    if s.contains c then continue
    s := s.insert c
    if !inProject env c then continue
    match env.find? c with
    | some (.defnInfo dv) => s := stmtClosure env dv.value (stmtClosure env dv.type s)
    | some (.opaqueInfo _) => pure ()
    | some ci => s := stmtClosure env ci.type s
    | none => pure ()
  return s

/-- plumbing a tactic puts into a proof term without content of its own (found 1 Nov 2026:  `ext`, `funext`,
`Subtype.property` and instances from `norm_num` made a theorem that holds by `rfl` pass R1):  extensionality lemmas,
structure projections and instances. -/
def plumbingTheorems : List Name := [`Set.ext, `funext, `congrFun', `Subtype.ext, `Subtype.property, `Subtype.prop,
  `Prod.ext, `Function.funext_iff, `Set.ext_iff, `Finset.ext, `Sigma.ext, `PSigma.ext, `Subtype.coe_prop,
  `Subtype.mem, `SetCoe.ext, `Set.mem_setOf_eq, `Set.mem_def, `setOf, `Iff.intro, `Iff.mp, `Iff.mpr, `Eq.symm,
  `Eq.trans, `Eq.subst, `Eq.mpr, `Eq.mp, `Eq.refl, `HEq.refl]

def plumbing (env : Environment) (c : Name) : Bool :=
  plumbingTheorems.contains c || env.isProjectionFn c || Meta.isInstanceCore env c

/-- the first theorem outside the project and outside the logic core that the proof of `n` reaches, if any. -/
partial def firstContent (env : Environment) (n : Name) (seen : IO.Ref NameSet) : IO (Option Name) := do
  let some ci := env.find? n | return none
  let some v := ci.value? (allowOpaque := true) | return none
  for c in v.getUsedConstants do
    if (← seen.get).contains c then continue
    seen.modify (·.insert c)
    if inProject env c then
      if let some w ← firstContent env c seen then return some w
    else
      match env.find? c with
      | some (.thmInfo _) => if !isCore c && !plumbing env c then return some c
      | _ => pure ()
  return none

/-- does a structure or class have a field whose type is a proposition? -/
def hasPropField (s : Name) : MetaM Bool := do
  let env ← getEnv
  if !isStructure env s then return false
  let some ctor := (getStructureInfo? env s).map (·.structName) | return false
  let some ci := env.find? (s ++ `mk) | (do let _ := ctor; return false)
  forallTelescope ci.type fun xs _ => do
    for x in xs do
      if ← isProp (← inferType x) then return true
    return false

/-- the project's declarations:  every constant of a project module, and every constant of the file being checked. -/
def projectConsts (env : Environment) : Array (Name × ConstantInfo) := Id.run do
  let mut out := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if isProjectModule m then
      for n in env.header.moduleData[i]!.constNames do
        if let some ci := env.find? n then out := out.push (n, ci)
  for (n, ci) in env.constants.map₂.toList do out := out.push (n, ci)
  return out

/-- an inhabitant of `t` on file:  a project declaration whose type is `t` or `Nonempty t`, or a global instance. -/
def inhabitant? (t : Expr) : MetaM (Option Name) := do
  let env ← getEnv
  let mut found : Option Name := none
  for (n, ci) in projectConsts env do
    if found.isSome then break
    if n.isInternal then continue
    let ty := ci.type
    if ty == t then found := some n
    else if ty.isAppOfArity ``Nonempty 1 && ty.appArg! == t then found := some n
    -- a universe-polymorphic inhabitant:  same head constant, and the type matches `t` once the inhabitant's own
    -- universe parameters are instantiated (`Point.{u,v}` for `.{u₁,v₁}`)
    else if !ci.levelParams.isEmpty && ty.getAppFn.isConst && t.getAppFn.isConst &&
        ty.getAppFn.constName! == t.getAppFn.constName! then
      let ok ← (try withNewMCtxDepth do
          let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
          isDefEq (ci.instantiateTypeLevelParams us) t
        catch _ => pure false)
      if ok then found := some n
  if found.isNone then
    if let some inst ← (try withLCtx {} #[] (synthInstance? t) catch _ => pure none) then
      found := some (inst.getAppFn.constName?.getD `instance)
  return found

/-- a refutation of `t` on file:  a project declaration of type `¬ t`, `t → False` or `IsEmpty t`. -/
def refutation? (t : Expr) : MetaM (Option Name) := do
  let env ← getEnv
  let mut found : Option Name := none
  for (n, ci) in projectConsts env do
    if found.isSome then break
    if n.isInternal then continue
    let ty := ci.type
    if (ty.isAppOfArity ``Not 1 && ty.appArg! == t) || (ty.isAppOfArity `IsEmpty 1 && ty.appArg! == t) then
      found := some n
    else if let .forallE _ a b _ := ty then
      if a == t && b.isConstOf ``False then found := some n
  return found

/-- a project proposition:  a project constant whose type ends in `Prop`. -/
def isProjectProp (env : Environment) (c : Name) : MetaM Bool := do
  if !inProject env c then return false
  let some ci := env.find? c | return false
  forallTelescope ci.type fun _ b => return b.isSort && b.sortLevel! == levelZero

def mentionsOpen (e : Expr) : List Name := e.getUsedConstants.toList.filter (openProblems.contains ·)

/-- the first other project declaration whose type or value reaches `c`, if any. -/
def usersOf (env : Environment) (c : Name) : Option Name := Id.run do
  for (n, ci) in projectConsts env do
    if n == c then continue
    if ci.type.getUsedConstants.contains c || ((ci.value? (allowOpaque := true)).map (·.getUsedConstants.contains c)).getD false then
      return some n
  return none

/-! The carrier walk (R1k and the unfold pass):  the same traversal as `firstContent`, through every project declaration the
proof reaches, recording everything it meets instead of stopping at the first outside theorem. -/

/-- what one walk of a proof meets. -/
structure CarrierAcc where
  seen : NameSet := {}
  /-- the first theorem outside the project and the logic core (R1's content), if any -/
  content : Option Name := none
  /-- proposition fields of project structures and classes read (an axiom stored in a record) -/
  fields : NameSet := {}
  /-- recursors of project types (an induction, a case split, or a definition by recursion it unfolds) -/
  recs : NameSet := {}
  /-- project theorems reached, outside theorems reached (logic core excluded) -/
  thms : Nat := 0
  outThms : Nat := 0
  /-- `Decidable.decide` evaluated by the kernel -/
  decide : Bool := false

/-- a theorem (Lean's core has no `ConstantInfo.isThm`;  Batteries adds it, and a project without Mathlib does not
load Batteries). -/
def isTheorem : Option ConstantInfo → Bool
  | some (.thmInfo _) => true
  | _ => false

/-- a projection that returns a proof:  reading it reads an axiom stored in a structure or class. -/
def propProjection (c : Name) : MetaM Bool := do
  let env ← getEnv
  if (env.getProjectionFnInfo? c).isNone then return false
  let some ci := env.find? c | return false
  forallTelescope ci.type fun _ b => isProp b

partial def carrierWalk (n : Name) : StateT CarrierAcc MetaM Unit := do
  let env ← getEnv
  let some ci := env.find? n | return
  let some v := ci.value? (allowOpaque := true) | return
  for c in v.getUsedConstants do
    if (← get).seen.contains c then continue
    modify fun a => { a with seen := a.seen.insert c }
    if c == ``Decidable.decide || c == ``of_decide_eq_true then modify fun a => { a with decide := true }
    if inProject env c then
      if ← propProjection c then modify fun a => { a with fields := a.fields.insert c }
      if isRecCore env c || isAuxRecursor env c then modify fun a => { a with recs := a.recs.insert c }
      if isTheorem (env.find? c) && (env.getProjectionFnInfo? c).isNone then modify fun a => { a with thms := a.thms + 1 }
      carrierWalk c
    else
      match env.find? c with
      | some (.thmInfo _) =>
        if !isCore c then modify fun a => { a with outThms := a.outThms + 1, content := a.content <|> some c }
      | _ => pure ()

/-- the heads of a statement's hypotheses that are project propositions (`def … : Prop`, or a family of them). -/
def hypPropHeads (t : Expr) : MetaM (List Name) := do
  let env ← getEnv
  forallTelescope t fun xs _ => do
    let mut hs : List Name := []
    for x in xs do
      let ty ← inferType x
      if ← isProp ty then
        let h := ty.getAppFn
        if h.isConst && (env.find? h.constName!).any (·.isDefinition) && (← isProjectProp env h.constName!) then
          hs := h.constName! :: hs
    return hs.eraseDups

/-- R1k:  what carries a theorem.  CONTENT when the proof reaches an outside theorem (R1 PASS);  otherwise, first match,
FIELD (an axiom stored in a project structure or class), HYP (a hypothesis that is a project proposition), IND (a
recursor of a project type), UNFOLD (definitions and logic only). -/
def r1Kind (a : CarrierAcc) (hs : List Name) : String :=
  if a.content.isSome then "CONTENT" else if !a.fields.isEmpty then "FIELD"
  else if !hs.isEmpty then "HYP" else if !a.recs.isEmpty then "IND" else "UNFOLD"

def runThm (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.find? n | emit "L4" n.toString "FAIL" "not a declaration in the environment"
  let thm := n.toString
  -- L0
  if !off.contains "L0" then
    let axs ← liftCoreM (collectAxioms n)
    let bad := axs.toList.filter (fun a => !allowedAxioms.contains a)
    if bad.isEmpty then emit "L0" thm "PASS" s!"{axs.toList}" else emit "L0" thm "FAIL" s!"extra axioms {bad}"
  -- L1
  if !off.contains "L1" then
    let cl := closure env n {}
    let mut bad : Array String := #[]
    let mut hidden : Array String := #[]
    for c in cl.toList do
      match env.find? c with
      | some (.opaqueInfo oi) =>
        if inProject env c && !oi.isUnsafe then
          -- `opaque c : T` with no value elaborates its value as the type's default:  a stand-in (FAIL);  an explicit
          -- value was checked by the kernel but is hidden from every theorem (REVIEW)
          let hd := oi.value.getAppFn.constName?.getD Name.anonymous
          if hd == ``Inhabited.default || hd == ``Classical.ofNonempty || hd == `instInhabitedOfNonempty then
            bad := bad.push s!"opaque {c}"
          else hidden := hidden.push s!"opaque with a value {c}"
      | some ci' =>
        if ci'.isUnsafe && inProject env c then bad := bad.push s!"unsafe {c}"
        if ci'.isPartial && inProject env c then bad := bad.push s!"partial {c}"
      | none => pure ()
      if inProject env c then
        if (Compiler.getImplementedBy? env c).isSome then bad := bad.push s!"implemented_by {c}"
        if isExtern env c then bad := bad.push s!"extern {c}"
    if !bad.isEmpty then emit "L1" thm "FAIL" s!"{bad.toList.take 8}"
    else if !hidden.isEmpty then emit "L1" thm "REVIEW" s!"{hidden.toList.take 8}: the value is checked but hidden; unpack it"
    else emit "L1" thm "PASS" s!"{cl.size} constants reached, no stand-in"
  -- L1u:  where each `opaque` with a value is reached.  From the statement (through the definitions it unfolds to),
  -- the statement's meaning runs through the hidden value:  REVIEW.  Only from the proof:  the hiding cannot change
  -- what is stated, and making the constant transparent only adds definitional equalities, so no proof depends on
  -- it:  PASS.
  if !off.contains "L1u" then
    let cl := closure env n {}
    let st := stmtClosure env ci.type {}
    let mut inStmt : Array Name := #[]
    let mut inProof : Array Name := #[]
    for c in cl.toList do
      match env.find? c with
      | some (.opaqueInfo oi) =>
        let hd := oi.value.getAppFn.constName?.getD Name.anonymous
        if inProject env c && !oi.isUnsafe && !(hd == ``Inhabited.default || hd == ``Classical.ofNonempty) then
          if st.contains c then inStmt := inStmt.push c else inProof := inProof.push c
      | _ => pure ()
    if !inStmt.isEmpty then
      emit "L1u" thm "REVIEW" s!"statement-level: {inStmt.toList.take 8}; proof-only: {inProof.size}"
    else if !inProof.isEmpty then
      emit "L1u" thm "PASS" s!"proof-only: {inProof.toList.take 8}"
    else
      emit "L1u" thm "INFO" "no opaque with a value reached"
  -- L2, L3, R2, R3, R4 read the statement
  liftTermElabM do
    forallTelescope ci.type fun xs body => do
      let mut hyps : Array (String × String) := #[]
      let mut unbuilt := 0
      let mut review := 0
      let mut vacuous := 0
      for x in xs do
        let t ← instantiateMVars (← inferType x)
        let isP ← isProp t
        let head := t.getAppFn.constName?.getD Name.anonymous
        let structHyp ← if !isP && head != Name.anonymous && inProject env head then hasPropField head else pure false
        if !(isP || structHyp) then continue
        let dependent := t.hasFVar
        -- one line per row:  the pretty printer breaks long types across lines, and the driver reads one line per
        -- row, so a hypothesis cut at a line break would lose its status
        let tStr := ((toString (← ppExpr t)).replace "\n" " ").replace "  " " "
        let mut st := ""
        if !dependent then
          match ← inhabitant? t with
          | some w => st := s!"discharged by {w}"
          | none => st := "UNBUILT"; unbuilt := unbuilt + 1
          if !off.contains "L3" then
            if let some r ← refutation? t then st := st ++ s!"; REFUTED by {r}"; vacuous := vacuous + 1
        else
          let cs := t.getUsedConstants.toList
          let mut carries := false
          for c in cs do
            if ← isProjectProp env c then carries := true
          if structHyp || carries || !(mentionsOpen t).isEmpty then
            st := "carries a project proposition"; review := review + 1
          else if cs.all (fun c => coreRelations.contains c || !inProject env c) then st := "side condition"
          else st := "side condition (project data)"
        hyps := hyps.push (String.mk (tStr.toList.take 90), st)
      if !off.contains "L2" then
        let status := if unbuilt > 0 then "FAIL" else if review > 0 then "REVIEW" else "PASS"
        let detail := String.intercalate " | " (hyps.toList.map fun (a, b) => s!"{a} :: {b}") ++ s!" || unbuilt={unbuilt}"
        liftCommandElabM <| emit "L2" thm status (if hyps.isEmpty then "no hypotheses" else detail)
      if !off.contains "L3" then
        -- a reduction:  a theorem under a refuted hypothesis whose conclusion is no registered open problem and
        -- which another declaration on file uses (as in a proof by contraposition) is REVIEW;  otherwise it is
        -- vacuous, FAIL.
        let concl ← instantiateMVars body
        let usedBy := if vacuous > 0 && (mentionsOpen concl).isEmpty then usersOf env n else none
        let (st3, d3) := if vacuous == 0 then ("PASS", "no hypothesis refuted on file")
          else match usedBy with
            | some u => ("REVIEW", s!"a hypothesis is refuted on file: a reduction, used by {u};  report the implication, not the conclusion")
            | none => ("FAIL", "a hypothesis is refuted on file: the theorem is vacuous")
        liftCommandElabM <| emit "L3" thm st3 d3
      -- R2
      let body ← instantiateMVars body
      if !off.contains "R2" then
        let restate := body.isAppOfArity ``Iff 2 &&
          !(mentionsOpen (body.getArg! 0) ++ mentionsOpen (body.getArg! 1)).isEmpty
        liftCommandElabM <| emit "R2" thm (if restate then "FAIL" else "PASS")
          (if restate then s!"restatement: ↔ with {mentionsOpen body}" else "not an equivalence with an open problem")
      -- R3
      let headC := body.getAppFn.constName?.getD Name.anonymous
      if !off.contains "R3" then
        let cond := openProblems.contains headC && !xs.isEmpty
        liftCommandElabM <| emit "R3" thm (if cond then "FAIL" else "PASS")
          (if cond then s!"conditional: {headC} under {xs.size} binders" else "conclusion is not an open problem under hypotheses")
      -- R4
      if !off.contains "R4" then
        let mut hit : Option Name := none
        for c in targetStatements do
          if xs.isEmpty then
            if let some cc := env.find? c then
              if ← isDefEq body cc.type <||> isDefEq body (mkConst c) then hit := some c
        liftCommandElabM <| match hit with
          | some c => emit "R4" thm "REVIEW" s!"typechecks as the registered target statement {c}; a person confirms"
          | none => emit "R4" thm "INFO" "not a registered target statement"
      -- IFF (Joseph, 1 Nov 2026:  an iff stays only "unless iff is defining an explicit boundary"):  an iff that holds
      -- by definitions and logic alone rewords a definition, FAIL;  a top-level iff whose right side is a comparison,
      -- an equation, a membership or a connective of them that names a number states its boundary, PASS;  any other
      -- iff is REVIEW.  The row changes no class.
      if !off.contains "IFF" then
        let isIff := body.isAppOfArity ``Iff 2
        let nested := !isIff && (body.find? (·.isAppOfArity ``Iff 2)).isSome
        if isIff || nested then
          let seenI ← IO.mkRef ({} : NameSet)
          let fc ← firstContent env n seenI
          let rhs := if isIff then body.getArg! 1 else body
          let natLit := (rhs.find? (·.isRawNatLit)).isSome
          let rh := rhs.getAppFn.constName?.getD Name.anonymous
          let shape := [``Eq, ``Ne, ``LE.le, ``LT.lt, ``GE.ge, ``GT.gt, ``Or, ``And, ``Membership.mem, ``Not].contains rh
          let (st, d) :=
            if fc.isNone then ("FAIL", "rewording: an iff that holds by definitions and logic alone")
            else if isIff && natLit && shape then ("PASS", "boundary: the right side states it in numbers")
            else if nested then ("REVIEW", "an iff inside the statement: a person decides whether it states a boundary")
            else ("REVIEW", "an iff whose right side names no boundary in numbers: state the boundary, or two implications")
          liftCommandElabM <| emit "IFF" thm st d
        else liftCommandElabM <| emit "IFF" thm "INFO" "not an iff"
  -- R1
  if !off.contains "R1" then
    let seen ← IO.mkRef ({} : NameSet)
    match ← firstContent env n seen with
    | some w => emit "R1" thm "PASS" s!"reaches {w}"
    | none => emit "R1" thm "FAIL" "structural: holds by definitions and logic alone"
  -- R1k:  the kind of carrier, as the row's status (like CLASS);  it changes no verdict
  if !off.contains "R1k" then
    let (k, d) ← liftTermElabM do
      let (_, a) ← (carrierWalk n).run {}
      let hs ← hypPropHeads ci.type
      let showL (xs : List Name) : String := ", ".intercalate ((xs.take 4).map toString)
      let d := match r1Kind a hs with
        | "CONTENT" => s!"reaches {a.content.getD Name.anonymous}"
        | "FIELD" => s!"reads the stored axioms {showL a.fields.toList}"
        | "HYP" => s!"under the project propositions {showL hs}"
        | "IND" => s!"recursion on project types {showL a.recs.toList}"
        | _ => "definitions and logic only"
      return (r1Kind a hs, d)
    emit "R1k" thm k d
  -- R7:  the proof's top step.  If the proof, under its binders, is one application of a project theorem that is
  -- itself structural, the theorem packages that structural step;  its content is in the arguments.
  if !off.contains "R7" then
    let some v := ci.value? (allowOpaque := true) | pure ()
    let body := Id.run do
      let mut e := v
      while e.isLambda do e := e.bindingBody!
      return e
    let hd := body.getAppFn
    match hd.constName? with
    | some c =>
      if inProject env c && c != n then
        match env.find? c with
        | some (.thmInfo _) =>
          let seen ← IO.mkRef ({} : NameSet)
          match ← firstContent env c seen with
          | none => emit "R7" thm "REVIEW" s!"packaged: the top step is the structural lemma {c}; the content is in its arguments"
          | some _ => emit "R7" thm "PASS" s!"top step {c} carries content"
        | _ => emit "R7" thm "PASS" "top step is not a project theorem"
      else emit "R7" thm "PASS" "top step is not a project theorem"
    | none => emit "R7" thm "PASS" "no single top step"

/-- the head constant of a theorem's conclusion, under its binders. -/
def conclHead (ty : Expr) : Option Name := Id.run do
  let mut e := ty
  while e.isForall do e := e.bindingBody!
  return e.getAppFn.constName?

/-- does `t` state an equivalence between `a` and `b` (`↔`, `=` or `≃`, under binders)? -/
def statesEquiv (t : Expr) (a b : Name) : Bool := Id.run do
  let mut e := t
  while e.isForall do e := e.bindingBody!
  let hd := e.getAppFn.constName?.getD Name.anonymous
  if !(hd == ``Iff || hd == ``Eq || hd == `Equiv || hd == `Equiv.Perm) then return false
  let used := e.getUsedConstants
  return used.contains a && used.contains b

/-- the library constant a project declaration copies, if any:  its name with a project root removed names a constant
outside the project of the same type. -/
def copyOf? (env : Environment) (c : Name) : Option Name := Id.run do
  let some ci := env.find? c | return none
  for r in projectRoots do
    if r.isPrefixOf c && r != c then
      let rest := c.replacePrefix r Name.anonymous
      if let some lib := env.find? rest then
        if !inProject env rest && lib.type == ci.type then return some rest
  return none

/-- a name the compiler wrote, never a person, so the walk skips it.  Decided on the LAST name component only.
`Name.isInternal` marks a component starting with `_` (auxiliary proofs `_proof_<n>`, private names), but on Lean
4.33.1 the equation lemmas (`f.eq_<n>`), unfolding lemmas (`f.eq_def`) and matcher equations (`match_<n>.eq_<k>`)
carry no underscore and arrive as ordinary theorems.  Skipped:  `eq_` followed by digits, `eq_def`, `match_`
followed by digits, `sizeOf_spec`, `congr_simp`, a constructor's `inj` / `injEq` and projections.  A person's theorem
named `eq_of_…` or `controlled_…` is checked.  The shapes are a fact about the
toolchain:  on a new toolchain, rerun the census and compare before trusting this list. -/
def generatedName (env : Environment) (c : Name) : Bool :=
  let last := match c with | .str _ t => t | _ => ""
  let numbered (pre : String) : Bool :=
    last.startsWith pre && last.length > pre.length && (last.drop pre.length).all Char.isDigit
  let parentIsCtor := match c with
    | .str p _ => (env.find? p).any (·.isCtor)
    | _ => false
  -- the compiler's matchers carry one or more numeric suffixes (`match_1`, `match_1_1`)
  let matcher : Bool := last.startsWith "match_" && last.length > 6 && (last.drop 6).all (fun ch => ch.isDigit || ch == '_')
  c.isInternal || numbered "eq_" || last == "eq_def" || matcher || last == "sizeOf_spec" || last == "congr_simp" ||
    ((last == "inj" || last == "injEq") && parentIsCtor) || env.isProjectionFn c ||
    isAuxRecursor env c || isNoConfusion env c

/-- R1i, DUP, SHADOW:  the checks for proofs built from supplied inputs (INPUTS-DESIGN.md). -/
def runInputs (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some _ := env.find? n | return
  let thm := n.toString
  let cl := closure env n {}
  -- R1i
  if !off.contains "R1i" then
    let mut weak : Array String := #[]
    let mut nIn := 0
    for c in cl.toList do
      if c == n || !inProject env c then continue
      match env.find? c with
      | some (.thmInfo ti) =>
        match conclHead ti.type with
        | some h =>
          if ← liftTermElabM (isProjectProp env h) then
            nIn := nIn + 1
            let seen ← IO.mkRef ({} : NameSet)
            if (← firstContent env c seen).isNone then weak := weak.push s!"{h} by {c}"
        | none => pure ()
      | _ => pure ()
    if !weak.isEmpty then emit "R1i" thm "REVIEW" s!"input supplied by unfolding alone: {weak.toList.take 6}"
    else if nIn > 0 then emit "R1i" thm "PASS" s!"{nIn} supplied inputs, each carries content"
    else emit "R1i" thm "INFO" "no supplied input"
  -- DUP
  if !off.contains "DUP" then
    let mut defs : Array (Name × Expr × Expr) := #[]
    for c in cl.toList do
      if !inProject env c || generatedName env c then continue
      match env.find? c with
      | some (.defnInfo dv) => defs := defs.push (c, dv.type, dv.value)
      | _ => pure ()
    let mut pairs : Array (Name × Name) := #[]
    for i in [0:defs.size] do
      for j in [i+1:defs.size] do
        let (a, ta, va) := defs[i]!
        let (b, tb, vb) := defs[j]!
        if ta == tb && va == vb then pairs := pairs.push (a, b)
    if pairs.isEmpty then emit "DUP" thm "PASS" s!"{defs.size} project definitions, no twins"
    else
      let mut unbridged : Array String := #[]
      let mut bridged : Array String := #[]
      for (a, b) in pairs do
        let mut br : Option Name := none
        for (m, ci) in projectConsts env do
          if br.isSome then break
          if let .thmInfo _ := ci then
            if statesEquiv ci.type a b then br := some m
        match br with
        | some m => bridged := bridged.push s!"{a} = {b} by {m}"
        | none => unbridged := unbridged.push s!"{a} = {b}"
      if !unbridged.isEmpty then emit "DUP" thm "REVIEW" s!"twins without a proved equivalence: {unbridged.toList.take 6}"
      else emit "DUP" thm "PASS" s!"twins, each bridged: {bridged.toList.take 6}"
  -- SHADOW
  if !off.contains "SHADOW" then
    let mut copies : Array String := #[]
    for c in cl.toList do
      if !inProject env c then continue
      if let some lib := copyOf? env c then copies := copies.push s!"{c} copies {lib}"
    if copies.isEmpty then emit "SHADOW" thm "PASS" "no copy of a library declaration"
    else emit "SHADOW" thm "REVIEW" s!"{copies.toList.take 6}"


/-! THE UNFOLD PASS.  Not a check:  an account of every declaration of a module (or, in the check file, of a namespace),
printed as machine lines for the Python half to aggregate over a whole package (`referee_lean.py --unfold-out`,
`unfold_report.py`).  Each line is `UNFOLD<TAB>record<TAB>…`;  schema 1:
    DECL    name  kind  module  flags  type
    EDGE    from  to  part  to_kind  to_origin          (part:  type | value)
    THM     name  r1k  first_content  fields  hyps  recs  decide  rfl  n_project_thms  n_outside_thms  concl  stmt_types
    FIELD   structure  field  is_prop  type
    INSTOF  instance  class  class_origin  project_types
    MSTRUCT name  is_class  module  fields              (`#referee_unfold_library`:  the outside library's structures)
kind:  theorem, def, propdef (a `def … : Prop` or a family of them), abbrev, instance, structure, class, inductive,
ctor, rec, opaque, axiom;  origin:  project, mathlib, core (Init, Std, Lean), lib (the other outside libraries).  Names
Lean generates are opened and their constants credited to the declaration that made them. -/

def unfoldSchema : Nat := 1

def originStr (env : Environment) (c : Name) : String :=
  match moduleOfConst' env c with
  | none => "project"
  | some m =>
    if (`Mathlib).isPrefixOf m then "mathlib"
    else if [`Init, `Std, `Lean].any (·.isPrefixOf m) then "core"
    else if !isProjectModule m then "lib" else "project"
where moduleOfConst' (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

/-- one field of a machine line:  no tab, no line break, runs of spaces collapsed, cut at `n` characters. -/
def cleanField (s : String) (n : Nat := 300) : String :=
  let s := (s.replace "\t" " ").replace "\n" " "
  let s := " ".intercalate ((s.splitOn " ").filter (· ≠ ""))
  if s.length > n then String.ofList (s.toList.take n) ++ "…" else s

def declKind (env : Environment) (c : Name) : MetaM String := do
  -- an instance first:  an instance of a class of propositions (`Nontrivial α`) is stored as a theorem
  if Meta.isInstanceCore env c then return "instance"
  match env.find? c with
  | some (.thmInfo _) => return "theorem"
  | some (.defnInfo d) =>
    if ← forallTelescope d.type fun _ b => return b.isProp then return "propdef"
    if getReducibilityStatusCore env c == .reducible then return "abbrev"
    return "def"
  | some (.axiomInfo _) => return "axiom"
  | some (.opaqueInfo _) => return "opaque"
  | some (.inductInfo _) =>
    if isClass env c then return "class"
    if isStructure env c then return "structure"
    return "inductive"
  | some (.ctorInfo _) => return "ctor"
  | some (.recInfo _) => return "rec"
  | some (.quotInfo _) => return "quot"
  | none => return "?"

def declFlags (env : Environment) (c : Name) : String :=
  let fs := (if isNoncomputable env c then ["noncomputable"] else []) ++
    (if isPrivateName c then ["private"] else []) ++
    (if (Compiler.getImplementedBy? env c).isSome then ["implemented_by"] else []) ++
    (if isExtern env c then ["extern"] else []) ++
    (match env.find? c with
     | some ci => (if ci.isPartial then ["partial"] else []) ++ (if ci.isUnsafe then ["unsafe"] else [])
     | none => [])
  if fs.isEmpty then "-" else ",".intercalate fs

/-- the constants an expression uses, with generated project constants opened (credited to the caller). -/
partial def usedOpened (env : Environment) (e : Expr) (vis : NameSet) : NameSet × NameSet := Id.run do
  let mut out : NameSet := {}
  let mut vis := vis
  for c in e.getUsedConstants do
    if generatedName env c && inProject env c then
      if vis.contains c then continue
      vis := vis.insert c
      if let some ci := env.find? c then
        for part in [some ci.type, ci.value? (allowOpaque := true)] do
          if let some x := part then
            let (o, v) := usedOpened env x vis
            vis := v
            for y in o do out := out.insert y
    else out := out.insert c
  return (out, vis)

/-- the project structures, classes and inductive types a type mentions. -/
def projectTypesIn (env : Environment) (e : Expr) : List Name :=
  e.getUsedConstants.toList.filter (fun c => inProject env c && (env.find? c).any (·.isInductive)) |>.eraseDups

def isRflProof (v : Expr) : Bool := Id.run do
  let mut e := v
  while e.isLambda do e := e.bindingBody!
  let f := e.getAppFn
  return f.isConst && [``Eq.refl, ``rfl, ``Iff.rfl, ``Iff.refl, ``HEq.refl].contains f.constName!

def showNames (xs : List Name) : String := if xs.isEmpty then "-" else ",".intercalate (xs.map toString)

def unfoldOut (s : String) : CommandElabM Unit := IO.println s!"UNFOLD\t{s}"

/-- the machine lines of one declaration. -/
def unfoldDecl (c : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.find? c | return
  let lines ← liftTermElabM do
    let k ← declKind env c
    let mod := (env.getModuleIdxFor? c).map (fun i => toString env.header.moduleNames[i.toNat]!) |>.getD "-"
    let mut ls : Array String := #[s!"DECL\t{c}\t{k}\t{mod}\t{declFlags env c}\t{cleanField (toString (← ppExpr ci.type))}"]
    let (tu, v0) := usedOpened env ci.type {}
    for d in tu.toList do
      ls := ls.push s!"EDGE\t{c}\t{d}\ttype\t{← declKind env d}\t{originStr env d}"
    if let some v := ci.value? (allowOpaque := true) then
      let (vu, _) := usedOpened env v v0
      for d in vu.toList do
        if !tu.contains d then ls := ls.push s!"EDGE\t{c}\t{d}\tvalue\t{← declKind env d}\t{originStr env d}"
    if k == "theorem" then
      let (_, a) ← (carrierWalk c).run {}
      let hs ← hypPropHeads ci.type
      let rflp := (ci.value? (allowOpaque := true)).map isRflProof |>.getD false
      let concl := (conclHead ci.type).map toString |>.getD "-"
      ls := ls.push (s!"THM\t{c}\t{r1Kind a hs}\t{a.content.map toString |>.getD "-"}\t{showNames a.fields.toList}\t" ++
        s!"{showNames hs}\t{showNames a.recs.toList}\t{a.decide}\t{rflp}\t{a.thms}\t{a.outThms}\t{concl}\t" ++
        s!"{showNames (projectTypesIn env ci.type)}")
    if k == "structure" || k == "class" then
      for f in getStructureFieldsFlattened env c (includeSubobjectFields := false) do
        match env.find? (c ++ f) with
        | some pci =>
          let (isP, fty) ← forallTelescope pci.type fun _ b => do return (← isProp b, cleanField (toString (← ppExpr b)) 200)
          ls := ls.push s!"FIELD\t{c}\t{f}\t{isP}\t{fty}"
        | none => ls := ls.push s!"FIELD\t{c}\t{f}\t?\t-"
    if k == "instance" then
      let cls ← forallTelescope ci.type fun _ b => return b.getAppFn.constName?
      if let some cl := cls then
        ls := ls.push s!"INSTOF\t{c}\t{cl}\t{originStr env cl}\t{showNames (projectTypesIn env ci.type)}"
    return ls
  for l in lines do unfoldOut l

/-- the declarations to unfold:  a module's, or in the check file those under a namespace;  generated names are
reached through the declarations that make them. -/
def unfoldRoots (env : Environment) (m : Name) : Array Name := Id.run do
  match env.getModuleIdx? m with
  | some idx => return env.header.moduleData[idx.toNat]!.constNames.filter (!generatedName env ·)
  | none =>
    let mut out := #[]
    for (n, _) in env.constants.map₂.toList do
      if m.isPrefixOf n && !generatedName env n then out := out.push n
    return out

elab "#referee_unfold " m:ident : command => do
  if off.contains "UNFOLD" then return
  let env ← getEnv
  let roots := unfoldRoots env m.getId
  unfoldOut s!"SCHEMA\t{unfoldSchema}\t{m.getId}"
  for c in roots do
    try unfoldDecl c
    catch e => unfoldOut s!"ERROR\t{c}\t{cleanField (← e.toMessageData.toString)}"
  unfoldOut s!"END\t{m.getId}\t{roots.size}"

/-- every structure and class of the outside library (Mathlib), with its fields:  what the counterparts report
matches the project's objects against. -/
elab "#referee_unfold_library" : command => do
  let env ← getEnv
  let mut k : Nat := 0
  for (c, _) in env.constants.map₁.toList do
    if originStr env c != "mathlib" || c.isInternal || !isStructure env c then continue
    let fs := getStructureFieldsFlattened env c (includeSubobjectFields := false)
    let mod := (env.getModuleIdxFor? c).map (fun i => toString env.header.moduleNames[i.toNat]!) |>.getD "-"
    unfoldOut s!"MSTRUCT\t{c}\t{isClass env c}\t{mod}\t{",".intercalate (fs.toList.map toString)}"
    k := k + 1
  unfoldOut s!"END\tlibrary\t{k}"

/-! THE DECODE STEP (`DECODE-DESIGN.md`).  Not a check:  machine lines for `unfold_report.py`'s `decode.tsv`.
    MDECL   name  kind  origin  head  lhs_head  rhs_head  lhs  rhs  consts   (`#referee_decode_library`)
    DDECL   name  kind  module  unpacked  stops  rounds                      (`#referee_decode M`)
A constant set leaves out the logic core (`decodeIgnore`), instances, numerals and names Lean generates. -/

def decodeIgnore : List Name :=
  [``Eq, ``Iff, ``And, ``Or, ``Not, ``Exists, ``True, ``False, ``ite, ``dite, ``Decidable, ``OfNat.ofNat,
   ``OfNat, ``instOfNatNat, ``Nat.cast, ``NatCast.natCast]

/-- a constructor of a proposition (`Eq.refl`, `Iff.intro`, `And.intro`, …):  it builds a proof. -/
def proofCtor (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.ctorInfo ci) => match env.find? ci.induct with
    | some (.inductInfo ii) => (ii.type.getForallBody).isProp
    | _ => false
  | _ => false

/-- casts and the identity:  the plumbing of a proof term inside a value, not the object's content. -/
def decodeCasts : List Name := [``Eq.mpr, ``Eq.mp, ``Eq.rec, ``Eq.ndrec, ``cast, ``id]

def decodeKeep (env : Environment) (c : Name) : Bool :=
  !decodeIgnore.contains c && !decodeCasts.contains c && !c.isInternal &&
    (!generatedName env c || env.isProjectionFn c) && !Meta.isInstanceCore env c &&
    !(c.toString.startsWith "inst") && !isTheorem (env.find? c) && !(`Lean).isPrefixOf c &&
    c != ``Decidable.decide && !proofCtor env c

/-- the constant set of an expression, as the decode step counts it. -/
def decodeConsts (env : Environment) (e : Expr) : NameSet :=
  e.getUsedConstants.foldl (fun s c => if decodeKeep env c then s.insert c else s) {}

def showSet (s : NameSet) : String :=
  if s.isEmpty then "-" else ",".intercalate (s.toList.map toString |>.mergeSort (· ≤ ·))

/-- the conclusion's head and, for `↔`, `=` and `≃`, its two sides. -/
def decodeSides (ty : Expr) : Option Name × Option Expr × Option Expr := Id.run do
  let mut e := ty
  while e.isForall do e := e.bindingBody!
  let f := e.getAppFn
  let as := e.getAppArgs
  match f.constName? with
  | some n =>
    if n == ``Iff && as.size == 2 then return (some n, some as[0]!, some as[1]!)
    if n == ``Eq && as.size == 3 then return (some n, some as[1]!, some as[2]!)
    if n == `Equiv && as.size == 2 then return (some n, some as[0]!, some as[1]!)
    return (some n, none, none)
  | none => return (none, none, none)

def sideHead (x : Option Expr) : String :=
  match x with
  | some e => (e.getAppFn.constName?.map toString).getD "-"
  | none => "-"

def decodeKindCheap (env : Environment) (c : Name) : Option String :=
  match env.find? c with
  | some (.thmInfo _) => some "theorem"
  | some (.defnInfo _) => some "def"
  | some (.inductInfo _) => some (if isClass env c then "class" else if isStructure env c then "structure" else "inductive")
  | _ => none

/-- every declaration of the outside library (Mathlib and the core) with its decode sets. -/
elab "#referee_decode_library" : command => do
  let env ← getEnv
  let mut k : Nat := 0
  -- Lean keeps a command's output until the command ends;  with REFEREE_DECODE_FILE set, the lines go straight to
  -- that file instead, so a run over all of Mathlib can be watched and does not hold every line in memory
  let file? ← IO.getEnv "REFEREE_DECODE_FILE"
  let h? ← file?.mapM (IO.FS.Handle.mk · .write)
  let emit (s : String) : IO Unit := match h? with
    | some h => h.putStrLn s!"UNFOLD\t{s}"
    | none => IO.println s!"UNFOLD\t{s}"
  -- module by module:  the origin is read once per module (a lookup per constant took 7 minutes over Mathlib)
  for i in [0:env.header.moduleData.size] do
   let m := env.header.moduleNames[i]!
   let o := if (`Mathlib).isPrefixOf m then "mathlib"
     else if [`Init, `Std, `Lean].any (·.isPrefixOf m) then "core"
     else if !isProjectModule m then "lib" else "project"
   if o == "project" then continue
   for c in env.header.moduleData[i]!.constNames do
    let some ci := env.find? c | continue
    if c.isInternal || generatedName env c || Meta.isInstanceCore env c then continue
    let some kd := decodeKindCheap env c | continue
    let (h, l, r) := decodeSides ci.type
    let mut cs := decodeConsts env ci.type
    if kd == "def" then
      if let some v := ci.value? then
        for x in (decodeConsts env v).toList do cs := cs.insert x
    let ls := (l.map (decodeConsts env)).getD {}
    let rs := (r.map (decodeConsts env)).getD {}
    emit s!"MDECL\t{c}\t{kd}\t{o}\t{(h.map toString).getD "-"}\t{sideHead l}\t{sideHead r}\t{showSet ls}\t{showSet rs}\t{showSet cs}"
    k := k + 1
    if k % 20000 == 0 then if let some h := h? then h.flush
  emit s!"END\tdecode-library\t{k}"
  if let some h := h? then h.flush

/-- a project constant that the unpacking stops at:  a type, a constructor, a recursor, an axiom or an opaque. -/
def decodeStop (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.defnInfo _) => (env.getProjectionFnInfo? c).isSome
  | some (.thmInfo _) => false
  | _ => true

/-- a project constant that belongs to a project inductive (its constructors, recursors, `casesOn`, `ctorIdx` and the
like):  the unpacking stops at the inductive. -/
def decodeTypeOwner? (env : Environment) (c : Name) : Option Name :=
  if !inProject env c then none
  else if (env.find? c).any (fun ci => ci.isInductive) then some c
  else match c with
    | .str p _ => if (env.find? p).any (fun ci => ci.isInductive) && inProject env p then some p else none
    | _ => none

/-- the constants of an expression with generated project constants opened, except those that belong to a project
inductive (kept, so that the unpacking stops there). -/
partial def decodeOpen (env : Environment) (e : Expr) (vis : NameSet) : NameSet × NameSet := Id.run do
  let mut out : NameSet := {}
  let mut vis := vis
  for c in e.getUsedConstants do
    if (decodeTypeOwner? env c).isNone && generatedName env c && inProject env c then
      if vis.contains c then continue
      vis := vis.insert c
      if let some ci := env.find? c then
        -- a matcher's value is compiled plumbing:  only its type (the discriminants and alternatives) counts
        let parts := if Meta.isMatcherCore env c then [some ci.type] else [some ci.type, ci.value? (allowOpaque := true)]
        for part in parts do
          if let some x := part then
            let (o, v) := decodeOpen env x vis
            vis := v
            for y in o do out := out.insert y
    else out := out.insert c
  return (out, vis)

/-- delta-expand the project constants of `D`'s value (its type, for a definition with no value) until only outside
constants remain, at most 20 rounds. -/
def decodeUnpack (env : Environment) (c : Name) : NameSet × NameSet × Nat := Id.run do
  let some ci := env.find? c | return ({}, {}, 0)
  let start := (ci.value? (allowOpaque := true)).getD ci.type
  let mut out : NameSet := {}
  let mut stops : NameSet := {}
  let mut seen : NameSet := ({} : NameSet).insert c
  let mut front : Array Name := (decodeOpen env start {}).1.toArray
  let mut rounds := 0
  while !front.isEmpty && rounds < 20 do
    rounds := rounds + 1
    let mut next : Array Name := #[]
    for d in front do
      if seen.contains d then continue
      seen := seen.insert d
      if !inProject env d then
        if decodeKeep env d then out := out.insert d
      else if let some t := decodeTypeOwner? env d then stops := stops.insert t
      else if decodeStop env d then stops := stops.insert d
      else if let some di := env.find? d then
        if let some v := di.value? (allowOpaque := true) then
          next := next ++ (decodeOpen env v {}).1.toArray
    front := next
  for d in front do if inProject env d then stops := stops.insert d
  return (out, stops, rounds)

/-- the unpacked constant set of every definition of a module (or, in the check file, of a namespace). -/
elab "#referee_decode " m:ident : command => do
  let env ← getEnv
  let roots := unfoldRoots env m.getId
  let mut k : Nat := 0
  for c in roots do
    let some (.defnInfo _) := env.find? c | continue
    if Meta.isInstanceCore env c || (env.getProjectionFnInfo? c).isSome then continue
    let (u, s, r) := decodeUnpack env c
    let mod := (env.getModuleIdxFor? c).map (fun i => toString env.header.moduleNames[i.toNat]!) |>.getD "-"
    unfoldOut s!"DDECL\t{c}\tdef\t{mod}\t{showSet u}\t{showSet s}\t{r}"
    k := k + 1
  unfoldOut s!"END\tdecode\t{m.getId}\t{k}"

/-- LS:  the skip filter on a name, which need not exist:  PASS when the walk would check it, INFO when it would skip
it as generated.  The self-test plants a person's `eq_of_x` (must be PASS) and a generated `eq_1` (must be INFO). -/
elab "#referee_skip " id:ident : command => do
  if off.contains "LS" then return
  let c := id.getId
  if generatedName (← getEnv) c then emit "LS" c.toString "INFO" "skipped: a generated name"
  else emit "LS" c.toString "PASS" "checked: a person's name"

/-- every theorem a module declares (read from the compiled environment, so names in sections, private names and
names with special characters are all found);  generated names (`generatedName`) are skipped. -/
elab "#referee_module " m:ident : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId | emit "MODULE" m.getId.toString "FAIL" "module not loaded"
  let mut n := 0
  for c in env.header.moduleData[idx.toNat]!.constNames do
    if generatedName env c then continue
    match env.find? c with
    | some (.thmInfo _) => runThm c; runInputs c; n := n + 1
    | _ => pure ()
  emit "MODULE" m.getId.toString "INFO" s!"{n} theorems checked"

elab "#referee " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  runThm n; runInputs n

/-- L4:  every backticked identifier of a module's header must name a declaration or a module of the environment
(matched on its last one, two or three name components, so `Sheaf.sections` and `Pkg.Sheaf.sections` both resolve). -/
elab "#referee_resolve " m:ident s:str : command => do
  let env ← getEnv
  let toks := (s.getString.splitOn " ").filter (fun t => t.length > 2)
  let mut suf : Std.HashSet String := {}
  for (n, _) in env.constants.toList do
    let cs := n.components.reverse
    let mut acc : List String := []
    for c in cs.take 3 do
      acc := c.toString :: acc
      suf := suf.insert (".".intercalate acc)
  for mn in env.header.moduleNames do suf := suf.insert mn.toString
  -- a word of the syntax (a token, or the leading word of a parser such as the tactic `native_decide`) is not a
  -- declaration name
  let pst := Lean.Parser.parserExtension.getState env
  let isSyntaxWord (t : String) : Bool := (pst.tokens.find? t).isSome ||
    pst.categories.toList.any fun (_, cat) => (cat.tables.leadingTable.get? (Name.mkSimple t)).isSome
  let bad := toks.filter (fun t => !suf.contains t && !isSyntaxWord t)
  logInfo m!"REFEREE\tL4\t{m.getId}\t{if bad.isEmpty then "PASS" else "FAIL"}\t{if bad.isEmpty then s!"all {toks.length} header names resolve" else s!"unresolved header names {bad.take 12}"}"

/-! L7 storage, for a project whose rule is that the outside library is a bridge, never storage:  its objects are
rebuilt, and the outside library is used only to show the two are equivalent.  The walk starts at every declaration a module adds and
follows every constant its statements, definitions and proofs use, through the project's own declarations in every
module (so an object that arrives inside another file's definition is found), and stops at the first constant of an
outside library.  An outside constant that is not a proof is an object.  It sits on the data path when a statement or
a definition reaches it, and on the proof path when only a proof does.  The lists below are by module-name prefix,
not by `projectRoots`, so every module outside them is walked as project. -/

/-- Lean's own core:  its objects are the logic's (ℕ, ℤ, ℚ, `List`, `Fin`, `Array`), never storage. -/
def coreLibs : List Name := [`Init, `Std, `Lean]
/-- the outside libraries:  Mathlib and the packages it brings. -/
def outsideLibs : List Name := [`Mathlib, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets, `ImportGraph,
  `LeanSearchClient, `Cli]

/-- the module a constant was declared in (`none` for the file being checked). -/
def moduleOfConst (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

/-- a bridge:  a module, or in the check file a namespace, with a component named `Bridge`. -/
def isBridgeName (n : Name) : Bool := n.components.any (· == `Bridge)

/-- 0 core, 1 outside library, 2 project (the check file's own constants are project). -/
def libKind (env : Environment) (c : Name) : Nat :=
  match moduleOfConst env c with
  | none => 2
  | some m => if coreLibs.any (·.isPrefixOf m) then 0 else if outsideLibs.any (·.isPrefixOf m) then 1 else 2

/-- a constant is a bridge constant when its module (or, in the check file, its name) is a bridge. -/
def isBridgeConst (env : Environment) (c : Name) : Bool :=
  match moduleOfConst env c with
  | some m => isBridgeName m
  | none => isBridgeName c

/-- the values of a declaration:  a theorem's proof, a definition's body, an opaque constant's value. -/
def valuesOfCI : ConstantInfo → List Expr
  | .thmInfo tv => [tv.value]
  | .defnInfo dv => [dv.value]
  | .opaqueInfo ov => [ov.value]
  | _ => []

/-- what an outside object is:  a type (a type former, or a constant returning one), a predicate, an instance,
a constructor, a recursor, or an operation (any other data). -/
def objectKind (c : Name) (ci : ConstantInfo) : MetaM String := do
  match ci with
  | .inductInfo _ =>
    forallTelescopeReducing ci.type fun _ b => return if b.isProp then "predicate" else "type"
  | .ctorInfo _ => return "constructor"
  | .recInfo _ => return "recursor"
  | _ =>
    if Meta.isInstanceCore (← getEnv) c then return "instance"
    forallTelescopeReducing ci.type fun _ b => do
      match b with
      | .sort .zero => return "predicate"
      | .sort _ => return "type"
      | _ => return "operation"

/-- the state of one walk:  the best path (0 data, 1 proof) each constant was reached on;  each outside object with
its path and the project declaration it arrived through;  bridge constants read;  outside theorems reached. -/
structure StorageState where
  seen : NameMap Nat := {}
  objs : NameMap (Nat × Name × String) := {}
  bridges : NameMap (Nat × Name) := {}
  laws : NameSet := {}

/-- visit constant `c` on path `t` (0 data, 1 proof), reached from the project declaration `via`. -/
partial def storageVisit (reviewIsBridge : Bool) (c : Name) (t : Nat) (via : Name) :
    StateRefT StorageState MetaM Unit := do
  if let some t0 := (← get).seen.find? c then
    if t0 ≤ t then return
  modify fun s => { s with seen := s.seen.insert c t }
  let env ← getEnv
  let some ci := env.find? c | return
  match libKind env c with
  | 0 => return
  | 1 =>
    if ← (try isProp ci.type catch _ => pure false) then
      modify fun s => { s with laws := s.laws.insert c }
    else
      let k ← objectKind c ci
      modify fun s => { s with objs := s.objs.insert c (t, via, k) }
  | _ =>
    if !reviewIsBridge && isBridgeConst env c then
      modify fun s => { s with bridges := s.bridges.insert c (t, via) }
    let isPf ← (try isProp ci.type catch _ => pure false)
    -- a generated proof constant (`_proof_`, `_auxLemma`, `_simp_`) states only what a proof needs
    let tType := if isPf && c.isInternal then max t 1 else t
    for d in ci.type.getUsedConstants do storageVisit reviewIsBridge d tType c
    let tVal := if isPf then max t 1 else t
    for v in valuesOfCI ci do
      for d in v.getUsedConstants do storageVisit reviewIsBridge d tVal c

/-- the declarations a module adds, or, in the check file, the declarations under a namespace;  generated
(internal) names are reached through the declarations that use them, on the path those use them on. -/
def storageRoots (env : Environment) (m : Name) : Array Name := Id.run do
  match env.getModuleIdx? m with
  | some idx => return env.header.moduleData[idx.toNat]!.constNames.filter (!·.isInternal)
  | none =>
    let mut out := #[]
    for (n, _) in env.constants.map₂.toList do
      if m.isPrefixOf n && !n.isInternal then out := out.push n
    return out

/-- `name [kind] (path; direct | via d (module))`, for the report. -/
def storageItem (env : Environment) (roots : Array Name) (c : Name) (t : Nat) (via : Name) (k : String) : String :=
  let path := if t == 0 then "data" else "proof"
  let route := if roots.contains via then "direct"
    else s!"via {via} ({(moduleOfConst env via).getD `this_file})"
  s!"{c} [{k}] ({path}; {route})"

elab "#referee_storage " m:ident : command => do
  if off.contains "L7" then return
  let env ← getEnv
  let mod := m.getId
  let roots := storageRoots env mod
  let bridge := isBridgeName mod
  let st ← liftTermElabM do
    let ((), st) ← (roots.forM fun r => storageVisit bridge r 0 r).run {}
    return st
  let objs := st.objs.toList
  let data := objs.filter (·.2.1 == 0)
  let proof := objs.filter (·.2.1 == 1)
  let brs := st.bridges.toList
  for (c, (t, via, k)) in objs do
    emit "L7obj" mod.toString (if t == 0 then "data" else "proof") (storageItem env roots c t via k)
  for (c, (t, via)) in brs do
    emit "L7obj" mod.toString "bridge-read" (storageItem env roots c t via "bridge")
  let fmt (xs : List (Name × Nat × Name × String)) : String :=
    ", ".intercalate (xs.take 10 |>.map fun (c, t, via, k) => storageItem env roots c t via k)
  let brNames := (brs.take 5).map (·.1)
  let byKind (xs : List (Name × Nat × Name × String)) : String :=
    ", ".intercalate (["type", "operation", "instance", "predicate", "constructor", "recursor"].filterMap fun k =>
      let n := (xs.filter (·.2.2.2 == k)).length
      if n == 0 then none else some s!"{k} {n}")
  let counts := s!"{roots.size} declarations; outside objects: {data.length} on the data path ({byKind data}), {proof.length} on the proof path ({byKind proof}); outside theorems reached: {st.laws.size}"
  if roots.isEmpty then
    emit "L7" mod.toString "FAIL" "no declarations found: the module is not loaded, or the namespace is empty"
  else if bridge then
    emit "L7" mod.toString "PASS" s!"bridge module: outside objects are its subject; {counts}"
  else if !brs.isEmpty then
    emit "L7" mod.toString "FAIL" s!"reads a bridge, which nothing native may import: {brNames}; {counts}"
  else if !data.isEmpty then
    emit "L7" mod.toString "FAIL" s!"outside-library objects as storage on the data path: {fmt data}; {counts}"
  else if !proof.isEmpty then
    emit "L7" mod.toString "REVIEW" s!"outside-library objects on the proof path only: {fmt proof}; {counts}"
  else
    emit "L7" mod.toString "PASS" s!"no outside object reached; {counts}"

/-- the signature of a module:  every declaration it adds, with a hash of its type, a hash of its value and its
axioms.  A change to comments and docstrings only leaves every line the same (a before/after comparison for a
cleanup that must not change any declaration). -/
elab "#referee_signature " m:ident : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId | logInfo m!"REFEREE_SIG\t{m.getId}\tMISSING\t-\t-"
  let mut out : Array String := #[]
  for n in env.header.moduleData[idx.toNat]!.constNames do
    let some ci := env.find? n | continue
    let vh := (ci.value? (allowOpaque := true)).map (·.hash) |>.getD 0
    let axs ← liftCoreM (collectAxioms n)
    out := out.push s!"{n}\t{ci.type.hash}\t{vh}\t{axs.toList}"
  logInfo m!"REFEREE_SIG_BEGIN {m.getId} {out.size}"
  for l in out.qsort (· < ·) do logInfo m!"REFEREE_SIG\t{l}"

end RefereeCore
