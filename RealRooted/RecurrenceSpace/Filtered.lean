import Mathlib.Tactic.Linarith
import RealRooted.RecurrenceSpace.Operators

/-!
# Finite certificates for filtered recurrence operators

This module proves the filtered finite-check theorem proposed in RealRooted issue #1978.
Operators are finite `K[X]`-linear combinations of words in the forward shift, sequence
index multiplication, and coefficientwise differentiation.
-/

open Finset Polynomial

namespace RealRooted

noncomputable section

variable {K : Type*} [Field K]

/-- Exponents specifying the word `N^u S^j D^s`. -/
structure RecurrenceWord where
  /-- Exponent of the forward shift. -/
  shiftOrder : ℕ
  /-- Exponent of coefficientwise differentiation. -/
  derivativeOrder : ℕ
  /-- Exponent of index multiplication. -/
  indexOrder : ℕ
  deriving DecidableEq

/-- Apply a recurrence word in the order `N^u S^j D^s`. -/
def RecurrenceWord.apply (w : RecurrenceWord) (f : ℕ → K[X]) : ℕ → K[X] :=
  (LinearRecurrence.indexMul ^ w.indexOrder)
    ((LinearRecurrence.forwardShift ^ w.shiftOrder)
      ((sequenceDerivative ^ w.derivativeOrder) f))

/-- A finite polynomial-coefficient combination of recurrence words. -/
structure FilteredOperator where
  /-- The finite collection of words used by the operator. -/
  support : Finset RecurrenceWord
  /-- The polynomial coefficient multiplying each word. -/
  coeff : RecurrenceWord → K[X]

/-- Apply a filtered operator to a polynomial-valued sequence. -/
def FilteredOperator.apply (L : FilteredOperator (K := K))
    (f : ℕ → K[X]) : ℕ → K[X] :=
  ∑ w ∈ L.support, L.coeff w • w.apply f

private theorem shiftAction_pow_le {p : Polynomial K[X]} {a b : ℕ} (hab : a ≤ b)
    {f : ℕ → K[X]} (hf : LinearRecurrence.shiftAction (p ^ a) f = 0) :
    LinearRecurrence.shiftAction (p ^ b) f = 0 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, mul_comm (p ^ a), LinearRecurrence.shiftAction_mul_apply, hf, map_zero]

private theorem shiftAction_pow_iterate_derivative {p : Polynomial K[X]} (q s : ℕ)
    (f : ℕ → K[X]) (hf : LinearRecurrence.shiftAction (p ^ q) f = 0) :
    LinearRecurrence.shiftAction (p ^ (q + s)) ((sequenceDerivative ^ s) f) = 0 := by
  induction s generalizing f q with
  | zero => simpa using hf
  | succ s ih =>
      rw [pow_succ', Module.End.mul_apply]
      have hs := ih q f hf
      have hc := shiftAction_pow_succ_sequenceDerivative_eq_zero p (q + s)
        ((sequenceDerivative ^ s) f) hs
      simpa only [Nat.add_assoc, Nat.add_comm s 1] using hc

private theorem shiftAction_pow_iterate_index {p : Polynomial K[X]} (q u : ℕ)
    (f : ℕ → K[X]) (hf : LinearRecurrence.shiftAction (p ^ q) f = 0) :
    LinearRecurrence.shiftAction (p ^ (q + u))
      ((LinearRecurrence.indexMul ^ u) f) = 0 := by
  induction u generalizing f q with
  | zero => simpa using hf
  | succ u ih =>
      rw [pow_succ', Module.End.mul_apply]
      have hu := ih q f hf
      have hc := shiftAction_pow_succ_indexMul_eq_zero p (q + u)
        ((LinearRecurrence.indexMul ^ u) f) hu
      simpa only [Nat.add_assoc, Nat.add_comm u 1] using hc

private theorem shiftAction_pow_forwardShift {p : Polynomial K[X]} (q j : ℕ)
    (f : ℕ → K[X]) (hf : LinearRecurrence.shiftAction (p ^ q) f = 0) :
    LinearRecurrence.shiftAction (p ^ q) ((LinearRecurrence.forwardShift ^ j) f) = 0 := by
  have hcomm := shiftAction_commute (p ^ q) (X ^ j) f
  have hshift : LinearRecurrence.shiftAction (X ^ j) f =
      (LinearRecurrence.forwardShift ^ j) f := by
    rw [LinearRecurrence.shiftAction_pow_apply]
    congr 1
    ext g n
    simp [LinearRecurrence.shiftAction]
  rw [hshift] at hcomm
  rw [hcomm, hf, map_zero]

private theorem shiftAction_pow_word {p : Polynomial K[X]} (h : ℕ)
    (f : ℕ → K[X]) (hf : LinearRecurrence.shiftAction p f = 0)
    (w : RecurrenceWord) (hw : w.indexOrder + w.derivativeOrder < h) :
    LinearRecurrence.shiftAction (p ^ h) (w.apply f) = 0 := by
  have hbase : LinearRecurrence.shiftAction (p ^ 1) f = 0 := by simpa using hf
  have hd := shiftAction_pow_iterate_derivative 1 w.derivativeOrder f hbase
  have hs := shiftAction_pow_forwardShift (1 + w.derivativeOrder) w.shiftOrder
    ((sequenceDerivative ^ w.derivativeOrder) f) hd
  have hi := shiftAction_pow_iterate_index (1 + w.derivativeOrder) w.indexOrder
    ((LinearRecurrence.forwardShift ^ w.shiftOrder)
      ((sequenceDerivative ^ w.derivativeOrder) f)) hs
  apply shiftAction_pow_le (p := p) (a := 1 + w.derivativeOrder + w.indexOrder)
    (b := h) (by lia)
  exact hi

/-- Every filtered operator of weight below `h` sends a sequence annihilated by `p(S)`
to a sequence annihilated by `p(S)^h`. -/
theorem FilteredOperator.shiftAction_pow_apply_eq_zero
    (L : FilteredOperator (K := K))
    (p : Polynomial K[X]) (h : ℕ) (f : ℕ → K[X])
    (hf : LinearRecurrence.shiftAction p f = 0)
    (hweight : ∀ w ∈ L.support, w.indexOrder + w.derivativeOrder < h) :
    LinearRecurrence.shiftAction (p ^ h) (L.apply f) = 0 := by
  rw [FilteredOperator.apply, map_sum]
  apply sum_eq_zero
  intro w hw
  rw [map_smul, shiftAction_pow_word h f hf w (hweight w hw), smul_zero]

/-- Filtered finite check: under a monic degree-`k` source recurrence, a filtered
residual of weight below `h` vanishes identically exactly when its first `h * k`
entries vanish. -/
theorem FilteredOperator.apply_eq_zero_iff (L : FilteredOperator (K := K))
    (p : Polynomial K[X]) (h k : ℕ) (f : ℕ → K[X]) (hp : p.Monic)
    (hdegree : p.natDegree = k) (hf : LinearRecurrence.shiftAction p f = 0)
    (hweight : ∀ w ∈ L.support, w.indexOrder + w.derivativeOrder < h) :
    L.apply f = 0 ↔ ∀ n < h * k, L.apply f n = 0 := by
  constructor
  · intro hzero n _
    rw [hzero]
    rfl
  · intro hinit
    apply LinearRecurrence.eq_zero_of_monic_of_shiftAction_eq_zero (hp.pow h)
      (L.shiftAction_pow_apply_eq_zero p h f hf hweight)
    rw [hp.natDegree_pow, hdegree]
    exact hinit

end

end RealRooted
