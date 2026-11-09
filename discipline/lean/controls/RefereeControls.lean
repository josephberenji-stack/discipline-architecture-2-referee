/-
  RefereeControls.lean -- the planted faults of the Lean referee.  Each `ctrl_*` declaration is a
  fault one check must catch;  `good_*` declarations are the positive controls that must pass.  The self-test
  (`referee_lean.py --selftest`) pastes this text after its imports and runs `#referee` on every name in
  `controls.tsv`, then compares each check's status with the expected one.  Doc names for L4:  `good_gap`, `ctrl_not_defined_anywhere`.

  The L5 control (planted; it must fail):
  Provenance:  A. Person, 1 Oct 2026, verbatim:  "the step, the whole, and the maps between them".
  (1) The map from the levels to the top is not exhibited.  [OPEN]
  (2) The statement `∀ n : ℕ, 0 ≤ n` for every level.  [OPEN]
-/
namespace RefereeControls

/-! R1:  a theorem that holds by unfolding a definition. -/
def CtrlP : Prop := ∀ n : ℕ, n = n
theorem ctrl_definitional : CtrlP ↔ ∀ n : ℕ, n = n := Iff.rfl

/-! R2:  an iff-restatement of an open problem. -/
theorem ctrl_restatement : RiemannHypothesis ↔ (RiemannHypothesis ∧ True) :=
  ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩

/-! R3 and L2:  a conditional end statement whose hypothesis is an unbuilt structure that carries the conclusion. -/
structure CtrlStepper where
  step : ℕ → ℕ
  carries : RiemannHypothesis
theorem ctrl_conditional (S : CtrlStepper) : RiemannHypothesis := S.carries

/-! L3:  a conditional whose hypothesis is refuted on file:  vacuous. -/
structure CtrlCapped where
  bound : ℕ
  below : ∀ n : ℕ, n < bound
theorem ctrl_capped_empty : IsEmpty CtrlCapped := ⟨fun c => absurd (c.below c.bound) (lt_irrefl _)⟩
theorem ctrl_vacuous (C : CtrlCapped) : RiemannHypothesis := (ctrl_capped_empty.false C).elim
/-- L3, a reduction:  under the refuted hypothesis, a plain conclusion, used by `ctrl_reduction_use`. -/
theorem ctrl_reduction (C : CtrlCapped) : C.bound < C.bound + 1 := Nat.lt_succ_self _
/-- the use of `ctrl_reduction`, by contraposition. -/
theorem ctrl_reduction_use : ¬ (∃ C : CtrlCapped, ¬ C.bound < C.bound + 1) := fun ⟨C, h⟩ => h (ctrl_reduction C)
/-- L3, vacuous and unused:  under the refuted hypothesis, a plain conclusion that nothing uses. -/
theorem ctrl_vacuous_unused (C : CtrlCapped) : C.bound = C.bound := rfl

/-! L2:  a typeclass argument that carries the hard part, with no instance on file. -/
class CtrlOracle where
  rh : RiemannHypothesis
theorem ctrl_class_carries [CtrlOracle] : RiemannHypothesis := CtrlOracle.rh

universe uRC wRC

/-! L2, universes:  a universe-polymorphic inhabitant discharges the hypothesis at other universe names. -/
structure GoodUnivBox where
  obj : Type uRC
  ok : True
/-- the polymorphic inhabitant of `GoodUnivBox`. -/
def goodUnivBoxPt : GoodUnivBox.{uRC} := ⟨PUnit, trivial⟩
theorem good_univ_discharged (B : GoodUnivBox.{wRC}) : B.ok = trivial := rfl

/-! L2, universes:  the same shape with no inhabitant at any universe stays unbuilt. -/
structure CtrlUnivEmpty where
  obj : Type uRC
  carries : RiemannHypothesis
theorem ctrl_univ_unbuilt (B : CtrlUnivEmpty.{wRC}) : RiemannHypothesis := B.carries

/-! L2, a long hypothesis:  an unbuilt hypothesis that pretty-prints over several lines still makes the class C. -/
def CtrlLongPropertyNameForTheLineBreakControl (alphaNumber betaNumber : ℕ) : Prop := alphaNumber + betaNumber = 0
theorem ctrl_long_unbuilt
    (h : ∀ (alphaNumberOfTheControl betaNumberOfTheControl : ℕ), 1 ≤ alphaNumberOfTheControl →
      CtrlLongPropertyNameForTheLineBreakControl alphaNumberOfTheControl betaNumberOfTheControl →
      CtrlLongPropertyNameForTheLineBreakControl betaNumberOfTheControl alphaNumberOfTheControl) :
    RiemannHypothesis ∨ True := Or.inr trivial

/-! L1:  an opaque constant standing in for an unbuilt object. -/
opaque ctrlWitness : ℕ
theorem ctrl_opaque : ctrlWitness = ctrlWitness ∨ 0 < ctrlWitness + 1 := Or.inr (Nat.succ_pos _)

/-! L1:  an opaque constant given a value:  the kernel checked the value, no theorem can read it (REVIEW). -/
opaque ctrlValued : ℕ := 7
theorem ctrl_opaque_valued : ctrlValued = ctrlValued := rfl
/-- L1u, proof-only:  the proof passes through `ctrlValued`, the statement does not mention it. -/
theorem good_opaque_proofonly : (0 : Nat) ≤ 1 := (fun (_ : Nat) => Nat.zero_le 1) ctrlValued

/-! L1:  an implemented_by stand-in. -/
def ctrlFastImpl (n : ℕ) : ℕ := n
@[implemented_by ctrlFastImpl] def ctrlSlow (n : ℕ) : ℕ := n + 0
theorem ctrl_implemented_by : ctrlSlow 3 = 3 := rfl

/-! L0:  a declared axiom, a `sorry`, a `native_decide`. -/
axiom ctrl_fake_axiom : ∀ n : ℕ, n + 0 = n
theorem ctrl_axiom : (5 : ℕ) + 0 = 5 := ctrl_fake_axiom 5
theorem ctrl_sorry : (1 : ℕ) = 2 := sorry
theorem ctrl_native : (10 : ℕ) * 10 = 100 := by native_decide

/-! R4:  a fake target theorem (it typechecks as the registered target but uses sorry);  R4 must not PASS it, L0 fails
it. -/
theorem ctrl_target_fake : RiemannHypothesis := sorry


/-! R6:  a presheaf whose sections are the target (a proposition), and the restatement read off it. -/
structure Psh where
  Sec : ℕ → Type
  res : ∀ N, Sec (N + 1) → Sec N
def CtrlCappedAt (_N : ℕ) : Prop := RiemannHypothesis
def ctrlCapPsh : Psh where
  Sec N := PLift (CtrlCappedAt N)
  res _ x := ⟨x.down⟩
theorem ctrl_encoded_iff : (∀ N, Nonempty (ctrlCapPsh.Sec N)) ↔ RiemannHypothesis :=
  ⟨fun h => (h 0).some.down, fun h _ => ⟨⟨h⟩⟩⟩

/-! R5:  a name that claims more than the proof proves. -/
theorem ctrl_proof_of_target : (2 : ℕ) ≤ 3 := by norm_num

/-! R7 and the headline-name rule:  a headline name over one application of a structural lemma. -/
theorem ctrl_pass {P Q : Prop} (h : P → Q) (hp : P) : Q := h hp
theorem ctrl_main_top : ∀ n : ℕ, 0 ≤ n := ctrl_pass (fun h => h) (fun n => Nat.zero_le n)

/-! LS:  a person's theorem whose name begins `eq_`:  the skip filter must not hide it (it hid 22 such theorems once). -/
theorem eq_of_x (a b : ℕ) (h : a = b) : b = a := h.symm

/-! LS:  a person's theorem whose name begins `control`:  the skip filter must not hide it (it hid
`controlled_potential` in openai/math PinchedKahler). -/
theorem controlled_x (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 := Nat.le_succ_of_le h

/-! R1i:  a staged theorem whose named input is supplied by `trivial` (fires), and one whose input is supplied by a real
lemma (silent). -/
def CtrlInputEasy : Prop := True
theorem ctrl_input_easy_supplied : CtrlInputEasy := trivial
theorem ctrl_staged_easy_stage (_h : CtrlInputEasy) : ∀ n : ℕ, n + 0 = n := fun n => Nat.add_zero n
theorem ctrl_staged_easy : ∀ n : ℕ, n + 0 = n := ctrl_staged_easy_stage ctrl_input_easy_supplied
def GoodInputHard : Prop := ∀ n : ℕ, 0 + n = n
theorem good_input_hard_supplied : GoodInputHard := fun n => Nat.zero_add n
theorem good_staged_hard_stage (h : GoodInputHard) : ∀ n : ℕ, 0 + n = n := h
theorem good_staged_hard : ∀ n : ℕ, 0 + n = n := good_staged_hard_stage good_input_hard_supplied

/-! DUP:  two definitions with one body under two names, crossed without a proved equivalence (fires), and with one
(silent). -/
def CtrlTwinA (n : ℕ) : Prop := n ≤ n + 1
def CtrlTwinB (n : ℕ) : Prop := n ≤ n + 1
theorem ctrl_twin_crossed (n : ℕ) (h : CtrlTwinA n) : CtrlTwinB n := h
def GoodTwinA (n : ℕ) : Prop := n < n + 1
def GoodTwinB (n : ℕ) : Prop := n < n + 1
theorem good_twin_bridge (n : ℕ) : GoodTwinA n ↔ GoodTwinB n := Iff.rfl
theorem good_twin_crossed (n : ℕ) (h : GoodTwinA n) : GoodTwinB n := (good_twin_bridge n).1 h

/-- DUP positive control:  two different definitions with the same `match` shape share compiler matchers
(`ctrlMatchA.match_1` and `ctrlMatchB.match_1` are identical);  the matchers are generated, not twins a person wrote. -/
def ctrlMatchA (n : ℕ) : ℕ := match n with | 0 => 1 | _ + 1 => 2
def ctrlMatchB (n : ℕ) : ℕ := match n with | 0 => 3 | _ + 1 => 4
theorem good_match_twins : ctrlMatchA 0 + ctrlMatchB 0 = 4 := rfl

/-! SHADOW:  a project copy of the library's `Nat.le_refl`;  inside this namespace the name `Nat.le_refl` now means the
copy (fires). -/
theorem Nat.le_refl (n : ℕ) : n ≤ n := _root_.Nat.le_refl n
theorem ctrl_shadow_use (n : ℕ) : n ≤ n := Nat.le_refl n

/-! Positive controls. -/
theorem good_gap (n : ℕ) (h : 0 < n) : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
def GoodCrit : Prop := ∀ n : ℕ, 0 ≤ n
theorem good_crit_proved : GoodCrit := fun n => Nat.zero_le n
theorem good_discharged (h : GoodCrit) : ∀ n : ℕ, 0 + n ≥ 0 := fun n => by have := h n; omega

/-! R1k:  what carries a structural theorem.  One planted case per kind;  `ctrl_definitional` is UNFOLD and `good_gap`
CONTENT. -/
/-- a record that stores its own law as a field. -/
structure CtrlLaws where
  op : ℕ → ℕ → ℕ
  comm : ∀ a b, op a b = op b a
/-- FIELD:  the law is read from the record, not proved. -/
theorem ctrl_r1_field (L : CtrlLaws) (a b : ℕ) : L.op a b = L.op b a := L.comm a b
/-- a project proposition and its twin under another name. -/
def CtrlHypP (n : ℕ) : Prop := n = n
def CtrlHypQ (n : ℕ) : Prop := n = n
/-- HYP:  the conclusion is carried by a hypothesis that is a project proposition. -/
theorem ctrl_r1_hyp (n : ℕ) (h : CtrlHypP n) : CtrlHypQ n := h
/-- a project inductive type and a definition by recursion on it. -/
inductive CtrlTree where
  | leaf
  | node (l r : CtrlTree)
def CtrlTree.size : CtrlTree → ℕ
  | .leaf => 1
  | .node l r => l.size + r.size
/-- IND:  the proof unfolds a definition by recursion on a project type. -/
theorem ctrl_r1_ind : (CtrlTree.node .leaf .leaf).size = 2 := rfl

/-! BRIDGED:  a project object that already carries an outside-library structure (here `Nontrivial`), and a law about it
proved by unfolding alone (fires);  `ctrl_definitional` mentions no such object (PASS). -/
/-- a project object with an outside-library instance. -/
structure CtrlBit where
  v : Bool
instance : Nontrivial CtrlBit := ⟨⟨⟨false⟩, ⟨true⟩, fun h => Bool.false_ne_true (congrArg CtrlBit.v h)⟩⟩
def CtrlBit.same (x : CtrlBit) : CtrlBit := ⟨x.v⟩
/-- a law of the bridged object proved by unfolding:  the bridge is not used. -/
theorem ctrl_bridged_law (x : CtrlBit) : (CtrlBit.same x).v = x.v := rfl

/-! CARRIER:  a project proposition that theorems assume and no theorem establishes (fires);  `GoodCrit` is assumed by
`good_discharged` and established by `good_crit_proved` (PASS). -/
def CtrlCarried (n : ℕ) : Prop := ∃ m, m * m = n
theorem ctrl_carried_a (n : ℕ) (h : CtrlCarried n) : CtrlCarried (n * 1) := by rw [Nat.mul_one]; exact h
theorem ctrl_carried_b (n : ℕ) (h : CtrlCarried n) : CtrlCarried (n + 0) := by rw [Nat.add_zero]; exact h

/-- IFF control:  an iff that holds by unfolding a definition (a rewording). -/
def ctrlEven (n : ℕ) : Prop := n % 2 = 0
theorem ctrl_iff_reword (n : ℕ) : ctrlEven n ↔ n % 2 = 0 := Iff.rfl
/-- IFF control:  the right side states the boundary in numbers. -/
theorem ctrl_iff_boundary (n : ℕ) : n < 2 ↔ n = 0 ∨ n = 1 := by omega
/-- IFF control:  an iff with content and no number on the right. -/
theorem ctrl_iff_plain (a b : ℕ) : a + b = b + a ↔ True := ⟨fun _ => trivial, fun _ => Nat.add_comm a b⟩
/-- IFF control:  an iff inside a conjunction. -/
theorem ctrl_iff_nested (n : ℕ) : (n < 1 ↔ n = 0) ∧ True := ⟨by omega, trivial⟩

/-- CARRY control:  the conclusion is one of the hypotheses. -/
theorem ctrl_carry_hyp (P : Prop) (h : P) : P ∧ True := ⟨h, trivial⟩
/-- the model of a count, declared a model choice.  [model choice] -/
def ctrlModelPart (n : ℕ) : ℕ := n + 16
/-- CARRY control:  the statement names a declared model choice. -/
theorem ctrl_carry_model (n : ℕ) : ctrlModelPart n = n + 16 := rfl
/-- CARRY control:  a theorem with no hypothesis carrying it and no model choice. -/
theorem good_carry_free (n : ℕ) (h : 2 ≤ n) : 1 < n := by omega
/-- R1 control (1 Nov 2026):  a theorem that holds by `rfl` in substance, proved through `ext`;  the proof term carries
`Set.ext` and nothing with content. -/
def ctrlSetOf : Set ℕ := {n | n = n}
theorem ctrl_ext_rfl : ctrlSetOf = {n | n = n} := by ext n; exact Iff.rfl
/-- R1 control:  the same through `funext`. -/
def ctrlFn : ℕ → ℕ := fun n => n + 0
theorem ctrl_funext_rfl : ctrlFn = fun n => n + 0 := by funext n; rfl

/-- IFFSET control (from the VM thread's SetCtrl, 1 Nov 2026):  a predicate defined to be another. -/
def ctrlSetP (n : ℕ) : Prop := n < 5
/-- IFFSET control:  the set of `ctrlSetP` is the set of `n < 5`, by the definition and a membership lemma. -/
theorem ctrl_set_hollow_def : {n : ℕ | ctrlSetP n} = {n | n < 5} := by ext n; simp only [Set.mem_ofPred_eq, ctrlSetP]
/-- IFFSET control:  a union read back. -/
theorem ctrl_set_hollow_union : {n : ℕ | n < 3 ∨ n = 7} = {n | n < 3} ∪ {n | n = 7} := rfl
/-- IFFSET control:  a rewording through a logic lemma (`and_comm`), which R1 counts as content. -/
theorem ctrl_set_and_comm : {n : ℕ | ctrlSetP n ∧ n > 3} = {n | n > 3 ∧ ctrlSetP n} := by ext n; simp [and_comm]
/-- IFFSET control:  two bare conditions, equal by arithmetic. -/
theorem ctrl_set_bare : {n : ℕ | n % 2 = 0} = {n | ¬ n % 2 = 1} := by ext n; simp only [Set.mem_ofPred_eq]; omega
/-- IFFSET control (positive, from SetCtrl):  a side is built (an explicit finite set) and the proof needs arithmetic. -/
theorem good_set_real : {n : ℕ | n * n = 4} = {2} := by
  ext n; simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    have h3 : n ≤ 2 := by nlinarith
    interval_cases n <;> simp_all
  · rintro rfl; rfl
/-- IFF control:  an iff that holds by a logic lemma alone. -/
theorem ctrl_iff_logic (P Q : Prop) : P ∧ Q ↔ Q ∧ P := and_comm

/-! R1:  a theorem that holds by `rfl`, stated through a project instance whose value uses an outside theorem (3 Nov
2026:  `Nat.Prime.ne_zero`, inside a `NeZero`-style instance, made such a theorem pass R1). -/
/-- a class with one proposition. -/
class CtrlNZ (n : ℕ) : Prop where
  ne : n ≠ 0
/-- the instance, from primality:  its value uses `Nat.Prime.ne_zero`. -/
instance ctrlNZ_of_prime (n : ℕ) [h : Fact n.Prime] : CtrlNZ n := ⟨h.out.ne_zero⟩
/-- a definition that needs the instance and ignores it. -/
def ctrlId (n : ℕ) [CtrlNZ n] (x : ℕ) : ℕ := x
theorem ctrl_instance_rfl (n : ℕ) [Fact n.Prime] (x : ℕ) : ctrlId n x = x := rfl

/-- LS control (2 Nov 2026):  a structure with `@[ext]`;  Lean writes `CtrlPt.ext` and `CtrlPt.ext_iff`. -/
@[ext] structure CtrlPt where
  /-- first coordinate. -/
  x : ℕ
  /-- second coordinate. -/
  y : ℕ
/-- LS control:  an enumeration;  Lean writes `CtrlColour.ofNat_ctorIdx`. -/
inductive CtrlColour where
  | red
  | blue
  deriving DecidableEq


/-! The circle gate's controls (9 Nov 2026).  The self-test's registry names `riemannZeta` as a problem object (kind
`data`) and `riemannZeta_zero` as a known result (kind `known`). -/

/-- a construction that takes in the problem's own data, ζ, and cancels it (circle gate Q1 must FAIL). -/
noncomputable def zetaShadow (s : ℂ) : ℂ := riemannZeta s + riemannZeta (1 - s) - riemannZeta s - riemannZeta (1 - s) + s

/-- Q1 control:  a true statement about a construction fed with ζ, which says nothing about ζ. -/
theorem ctrl_circle_data (s : ℂ) : zetaShadow s = s := by
  unfold zetaShadow
  ring

/-- Q2 control:  a hypothesis that `ρ` is a zero of ζ, never used, so the statement holds for every `ρ`. -/
theorem ctrl_circle_every (ρ : ℂ) (_h : riemannZeta ρ = 0) : ρ + 0 = ρ := add_zero ρ

/-- Q2 control for the swap:  no hypothesis, but the statement holds with any function in ζ's place. -/
theorem ctrl_circle_swap (s : ℂ) : riemannZeta s - riemannZeta s = 0 := sub_self _

/-- Q2 good control and Q5 control:  the value of ζ at 0, which depends on ζ and is a known result. -/
theorem ctrl_circle_dep : riemannZeta 0 = -1 / 2 := riemannZeta_zero

/-- the circle gate's passing control:  depends on ζ, is no registered known result, and does not circle. -/
theorem ctrl_circle_new : riemannZeta 0 ≠ 0 := by
  rw [riemannZeta_zero]
  norm_num

end RefereeControls

/-! L7 (storage):  each namespace below is walked as if it were a module.  `RefereeStorageHelper` plays another
project file. -/
namespace RefereeStorageHelper
/-- a project definition whose type is `ℕ → ℕ` and whose body stores `ZMod 7`. -/
def hidden (n : ℕ) : ℕ := ((n : ZMod 7)).val
/-- a project theorem whose statement is about `ℝ`. -/
theorem real_fact : (0 : ℝ) ≤ 1 := zero_le_one
end RefereeStorageHelper

namespace RefereeStorageDirect
/-- an outside-library object stored directly (must FAIL). -/
def direct : Finset ℕ := Finset.range 3
end RefereeStorageDirect

namespace RefereeStorageThrough
/-- no outside name in this text:  the object arrives through `hidden`'s body (must FAIL). -/
theorem through (n : ℕ) : RefereeStorageHelper.hidden n = RefereeStorageHelper.hidden n := rfl
end RefereeStorageThrough

namespace RefereeStorageProofOnly
/-- `ℝ` is reached only inside the proof (must be REVIEW). -/
theorem pp (n : ℕ) : n ≤ n := by
  have _h := RefereeStorageHelper.real_fact
  exact Nat.le_refl n
end RefereeStorageProofOnly

namespace RefereeStorageClean
/-- core only (must PASS). -/
def clean (n : ℕ) : ℕ := n + 1
/-- core only (must PASS). -/
theorem clean_pos (n : ℕ) : 0 < clean n := Nat.succ_pos n
end RefereeStorageClean

namespace Bridge.RefereeStorageBridged
/-- a bridge holds outside-library objects (must PASS). -/
def bridged : ZMod 5 := 2
/-- a bridge constant with core type. -/
def bridgedNat : ℕ := 2
end Bridge.RefereeStorageBridged

namespace RefereeStorageReadsBridge
/-- a native declaration that reads a bridge (must FAIL). -/
def rb : ℕ := Bridge.RefereeStorageBridged.bridgedNat + 1
end RefereeStorageReadsBridge
