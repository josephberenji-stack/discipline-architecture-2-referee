import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-!
# Doubling:  a worked example for the Lean referee

Five theorems, one of each kind the referee separates.  Nothing here is new mathematics;  the file exists so that
the referee's classes can be seen on statements whose status is obvious.

## Main results

* `double_eq`: `double n = n + n`, by unfolding the definition (class DEF).
* `double_eq_two_mul`: `double n = 2 * n`, using a library lemma (class A?, held for a person).
* `eq_of_double_eq`: `double` is injective (class A?;  a person's theorem whose name begins with eq_).
* `prime_above_ten`: a prime above 10, under a hypothesis nothing on file builds (class C).
* `two_pow_ten`: a statement left on `sorry` (class D).
-/

namespace Example

/-- Twice a natural number. -/
def double (n : ℕ) : ℕ := n + n

/-- `double n` is `n + n`:  this holds by unfolding `double`, so it says nothing beyond the definition. -/
theorem double_eq (n : ℕ) : double n = n + n := rfl

/-- `double n` is `2 * n`. -/
theorem double_eq_two_mul (n : ℕ) : double n = 2 * n := by
  unfold double
  ring

/-- `double` is injective. -/
theorem eq_of_double_eq {a b : ℕ} (h : double a = double b) : a = b := by
  unfold double at h
  omega

/-- A source of primes:  for every `n` a prime between `n` and `2n + 2`.  Nothing in this file builds one. -/
structure PrimeSource where
  /-- the prime above `n`. -/
  above : ∀ n : ℕ, ∃ p, n < p ∧ p.Prime ∧ p < 2 * n + 2

/-- There is a prime above 10, given a `PrimeSource`:  a conditional result, since no `PrimeSource` is on file. -/
theorem prime_above_ten (S : PrimeSource) : ∃ p, 10 < p ∧ p.Prime :=
  let ⟨p, h1, h2, _⟩ := S.above 10
  ⟨p, h1, h2⟩

/-- `2 ^ 10 = 1024`, left on `sorry`:  the kernel accepts the declaration, the referee does not. -/
theorem two_pow_ten : (2 : ℕ) ^ 10 = 1024 := sorry

end Example
