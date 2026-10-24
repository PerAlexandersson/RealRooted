import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import RealRooted.RecurrenceSpace.Filtered

/-!
# Universal source-and-lift defect identity

This module formalizes the universal defect identity and its two propagation corollaries
from RealRooted issue #1978.  The identity is valid for arbitrary polynomial-valued
sequences; recurrence and lift assumptions enter only in the corollaries.
-/

open Finset Polynomial

namespace RealRooted

noncomputable section

variable {K : Type*} [Field K]

/-- An affine polynomial-valued function of a natural-number index. -/
def affineIndex (c₁ c₀ : K[X]) (n : ℕ) : K[X] :=
  (n : K[X]) * c₁ + c₀

/-- The defect in a constant-coefficient pure-lag recurrence. -/
def lagDefect {k : ℕ} (a : Fin k → K[X]) (P : ℕ → K[X]) (n : ℕ) : K[X] :=
  P (n + k) - ∑ i, a i * P (n + i)

/-- The defect in an affine-index first-order differential lift. -/
def liftDefect (d₁ d₀ A₁ A₀ B : K[X]) (P : ℕ → K[X]) (n : ℕ) : K[X] :=
  affineIndex d₁ d₀ n * P (n + 1) - affineIndex A₁ A₀ n * P n -
    B * (P n).derivative

/-- The monic characteristic polynomial of a pure-lag recurrence. -/
def lagCharacteristic {k : ℕ} (a : Fin k → K[X]) : Polynomial K[X] :=
  (LinearRecurrence.mk k a).charPoly

/-- The correction polynomial `J` in the universal defect identity. -/
def defectCorrection {k : ℕ} (a : Fin k → K[X]) (d₁ A₁ B : K[X]) :
    Polynomial K[X] :=
  ∑ i : Fin k, (monomial (i + 1) ((k - i : ℕ) * a i * d₁) -
    monomial i ((k - i : ℕ) * a i * A₁ + B * (a i).derivative))

private def correctionSummand {k : ℕ} (a : Fin k → K[X])
    (d₁ A₁ B : K[X]) (P : ℕ → K[X]) (n : ℕ) (i : Fin k) : K[X] :=
  (k - i : ℕ) * a i * d₁ * P (n + i + 1) -
    ((k - i : ℕ) * a i * A₁ + B * (a i).derivative) * P (n + i)

private def correctionAction {k : ℕ} (a : Fin k → K[X])
    (d₁ A₁ B : K[X]) (P : ℕ → K[X]) (n : ℕ) : K[X] :=
  ∑ i, correctionSummand a d₁ A₁ B P n i

private theorem shiftAction_defectCorrection_apply {k : ℕ} (a : Fin k → K[X])
    (d₁ A₁ B : K[X]) (P : ℕ → K[X]) (n : ℕ) :
    LinearRecurrence.shiftAction (defectCorrection a d₁ A₁ B) P n =
      correctionAction a d₁ A₁ B P n := by
  have shiftAction_sum (g : Fin k → Polynomial K[X]) :
      LinearRecurrence.shiftAction (∑ i, g i) =
        ∑ i, LinearRecurrence.shiftAction (g i) := by
    simp [LinearRecurrence.shiftAction]
  have shiftAction_sub (p q : Polynomial K[X]) :
      LinearRecurrence.shiftAction (p - q) =
        LinearRecurrence.shiftAction p - LinearRecurrence.shiftAction q := by
    simp [LinearRecurrence.shiftAction]
  rw [defectCorrection]
  rw [shiftAction_sum]
  simp only [LinearMap.sum_apply, Finset.sum_apply, correctionAction]
  apply Fintype.sum_congr
  intro i
  rw [shiftAction_sub, LinearMap.sub_apply,
    LinearRecurrence.shiftAction_monomial_apply,
    LinearRecurrence.shiftAction_monomial_apply]
  simp [correctionSummand, Nat.add_assoc]

private theorem derivative_lagDefect {k : ℕ} (a : Fin k → K[X])
    (P : ℕ → K[X]) (n : ℕ) :
    (lagDefect a P n).derivative = (P (n + k)).derivative -
      ∑ i : Fin k, ((a i).derivative * P (n + i) +
        a i * (P (n + i)).derivative) := by
  rw [lagDefect, map_sub, map_sum]
  apply congrArg₂ (fun x y ↦ x - y) rfl
  apply sum_congr rfl
  intro i _
  exact derivative_mul

private theorem affineIndex_sub {k : ℕ} (c₁ c₀ : K[X]) (n : ℕ)
    (i : Fin k) :
    affineIndex c₁ c₀ (n + k) - affineIndex c₁ c₀ (n + i) =
      (k - i : ℕ) * c₁ := by
  have hi : (i : ℕ) + (k - i) = k := Nat.add_sub_of_le i.isLt.le
  have hi' : (k : K[X]) = (i : ℕ) + (k - i : ℕ) := by
    rw [← Nat.cast_add, hi]
  simp only [affineIndex, Nat.cast_add]
  rw [hi']
  ring

private theorem correction_summand_identity {k : ℕ} (a : Fin k → K[X])
    (d₁ d₀ A₁ A₀ B : K[X]) (P : ℕ → K[X]) (n : ℕ) (i : Fin k) :
    -affineIndex d₁ d₀ (n + k) * a i * P (n + i + 1) +
        affineIndex A₁ A₀ (n + k) * a i * P (n + i) +
        B * ((a i).derivative * P (n + i) + a i * (P (n + i)).derivative) +
        correctionSummand a d₁ A₁ B P n i =
      -a i * liftDefect d₁ d₀ A₁ A₀ B P (n + i) := by
  have hd := affineIndex_sub d₁ d₀ n i
  have hA := affineIndex_sub A₁ A₀ n i
  have hd' := sub_eq_iff_eq_add.mp hd
  have hA' := sub_eq_iff_eq_add.mp hA
  simp only [liftDefect, correctionSummand]
  rw [hd', hA']
  ring

/-- The universal source-and-lift defect identity, valid for every polynomial sequence: the
lag defect of the lift defect is a combination of lag defects plus the correction action. -/
theorem lagDefect_liftDefect {k : ℕ} (a : Fin k → K[X])
    (d₁ d₀ A₁ A₀ B : K[X]) (P : ℕ → K[X]) (n : ℕ) :
    lagDefect a (liftDefect d₁ d₀ A₁ A₀ B P) n =
      affineIndex d₁ d₀ (n + k) * lagDefect a P (n + 1) -
        affineIndex A₁ A₀ (n + k) * lagDefect a P n -
        B * (lagDefect a P n).derivative +
        LinearRecurrence.shiftAction (defectCorrection a d₁ A₁ B) P n := by
  change liftDefect d₁ d₀ A₁ A₀ B P (n + k) -
      ∑ i, a i * liftDefect d₁ d₀ A₁ A₀ B P (n + i) = _
  rw [shiftAction_defectCorrection_apply, derivative_lagDefect]
  have hs :
      ∑ i,
          (-affineIndex d₁ d₀ (n + k) * a i * P (n + i + 1) +
            affineIndex A₁ A₀ (n + k) * a i * P (n + i) +
            B * ((a i).derivative * P (n + i) + a i * (P (n + i)).derivative) +
            correctionSummand a d₁ A₁ B P n i) =
        ∑ i, -(a i * liftDefect d₁ d₀ A₁ A₀ B P (n + i)) := by
    apply sum_congr rfl
    intro i _
    simpa only [neg_mul] using
      correction_summand_identity a d₁ d₀ A₁ A₀ B P n i
  rw [sub_eq_add_neg, ← sum_neg_distrib, ← hs]
  simp only [lagDefect, liftDefect, correctionAction]
  simp_rw [mul_sub, mul_sum]
  simp_rw [Finset.sum_add_distrib]
  simp only [Nat.add_assoc, Nat.add_comm 1 k]
  ring_nf
  rw [Finset.sum_neg_distrib]
  ring

/-- Evaluating the lag characteristic polynomial at the shift gives the lag defect. -/
theorem shiftAction_lagCharacteristic_apply {k : ℕ} (a : Fin k → K[X])
    (P : ℕ → K[X]) (n : ℕ) :
    LinearRecurrence.shiftAction (lagCharacteristic a) P n = lagDefect a P n := by
  simp [LinearRecurrence.shiftAction, lagCharacteristic, LinearRecurrence.charPoly,
    lagDefect, ← C_mul_X_pow_eq_monomial, LinearRecurrence.forwardShift_pow_apply]

private theorem shiftAction_defectCorrection_eq_smul_lagDefect {k : ℕ}
    (a : Fin k → K[X]) (d₁ A₁ B gamma : K[X]) (P : ℕ → K[X])
    (hfactor : defectCorrection a d₁ A₁ B = C gamma * lagCharacteristic a) :
    LinearRecurrence.shiftAction (defectCorrection a d₁ A₁ B) P =
      gamma • lagDefect a P := by
  rw [hfactor, LinearRecurrence.shiftAction_mul_apply]
  calc
    LinearRecurrence.shiftAction (C gamma)
        (LinearRecurrence.shiftAction (lagCharacteristic a) P) =
      gamma • LinearRecurrence.shiftAction (lagCharacteristic a) P := by
        ext n
        simp [LinearRecurrence.shiftAction]
    _ = gamma • lagDefect a P := by
      congr 1
      funext n
      exact shiftAction_lagCharacteristic_apply a P n

/-- A source recurrence and `k` zero lift-defect seeds imply the differential lift when
the correction polynomial is a multiple of the source characteristic polynomial. -/
theorem liftDefect_eq_zero_of_lagDefect_eq_zero {k : ℕ} (a : Fin k → K[X])
    (d₁ d₀ A₁ A₀ B gamma : K[X]) (P : ℕ → K[X])
    (hsource : ∀ n, lagDefect a P n = 0)
    (hfactor : defectCorrection a d₁ A₁ B = C gamma * lagCharacteristic a)
    (hseed : ∀ n < k, liftDefect d₁ d₀ A₁ A₀ B P n = 0) :
    liftDefect d₁ d₀ A₁ A₀ B P = 0 := by
  let E : LinearRecurrence K[X] := LinearRecurrence.mk k a
  have hcorr := shiftAction_defectCorrection_eq_smul_lagDefect a d₁ A₁ B gamma P hfactor
  have hsol : E.IsSolution (liftDefect d₁ d₀ A₁ A₀ B P) := by
    intro n
    have hid :
        liftDefect d₁ d₀ A₁ A₀ B P (n + k) -
          ∑ i, a i * liftDefect d₁ d₀ A₁ A₀ B P (n + i) = _ :=
      lagDefect_liftDefect a d₁ d₀ A₁ A₀ B P n
    have hc := congr_fun hcorr n
    simp only [Pi.smul_apply, smul_eq_mul, hsource, map_zero, mul_zero, sub_zero,
      zero_add] at hid hc
    rw [hc] at hid
    simpa [E] using sub_eq_zero.mp hid
  rw [E.eq_iff_eqOn_range_order _ 0 hsol E.solSpace.zero_mem]
  intro n hn
  exact hseed n (mem_range.mp hn)

/-- A source recurrence valid from `n₀` and `k` consecutive lift-defect seeds imply
the differential lift from `n₀` onward. -/
theorem liftDefect_eq_zero_from_of_lagDefect_eq_zero_from {k : ℕ}
    (a : Fin k → K[X]) (d₁ d₀ A₁ A₀ B gamma : K[X]) (P : ℕ → K[X]) (n₀ : ℕ)
    (hsource : ∀ n, n₀ ≤ n → lagDefect a P n = 0)
    (hfactor : defectCorrection a d₁ A₁ B = C gamma * lagCharacteristic a)
    (hseed : ∀ n, n₀ ≤ n → n < n₀ + k → liftDefect d₁ d₀ A₁ A₀ B P n = 0) :
    ∀ n, n₀ ≤ n → liftDefect d₁ d₀ A₁ A₀ B P n = 0 := by
  let E := liftDefect d₁ d₀ A₁ A₀ B P
  have hcorr := shiftAction_defectCorrection_eq_smul_lagDefect a d₁ A₁ B gamma P hfactor
  intro m hm
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hmk : m < n₀ + k
      · exact hseed m hm hmk
      · let n := m - k
        have hn : n₀ ≤ n := by
          dsimp only [n]
          lia
        have hnk : n + k = m := by
          dsimp only [n]
          lia
        have hid := lagDefect_liftDefect a d₁ d₀ A₁ A₀ B P n
        have hc := congr_fun hcorr n
        have hRn := hsource n hn
        have hRn1 := hsource (n + 1) (by lia)
        simp only [Pi.smul_apply, smul_eq_mul, hRn, hRn1, map_zero, mul_zero,
          sub_zero, zero_add] at hid hc
        rw [hc] at hid
        change E (n + k) - ∑ i, a i * E (n + i) = 0 at hid
        have hrec : E (n + k) = ∑ i, a i * E (n + i) := by
          exact sub_eq_zero.mp hid
        change E m = 0
        rw [← hnk, hrec]
        apply sum_eq_zero
        intro i _
        have hi : E (n + i) = 0 := ih (n + i) (by have := i.isLt; lia) (by lia)
        rw [hi, mul_zero]

/-- Conversely, a differential lift, one zero source-defect seed, and nonvanishing affine
leaders imply the pure-lag recurrence when the same factor certificate holds. -/
theorem lagDefect_eq_zero_of_liftDefect_eq_zero {k : ℕ} (a : Fin k → K[X])
    (d₁ d₀ A₁ A₀ B gamma : K[X]) (P : ℕ → K[X])
    (hlift : ∀ n, liftDefect d₁ d₀ A₁ A₀ B P n = 0)
    (hfactor : defectCorrection a d₁ A₁ B = C gamma * lagCharacteristic a)
    (hseed : lagDefect a P 0 = 0)
    (hleader : ∀ n, affineIndex d₁ d₀ (n + k) ≠ 0) :
    lagDefect a P = 0 := by
  have hcorr := shiftAction_defectCorrection_eq_smul_lagDefect a d₁ A₁ B gamma P hfactor
  apply funext
  intro m
  change lagDefect a P m = 0
  induction m with
  | zero => exact hseed
  | succ n ih =>
      have hid :
          liftDefect d₁ d₀ A₁ A₀ B P (n + k) -
            ∑ i, a i * liftDefect d₁ d₀ A₁ A₀ B P (n + i) = _ :=
        lagDefect_liftDefect a d₁ d₀ A₁ A₀ B P n
      have hc : LinearRecurrence.shiftAction (defectCorrection a d₁ A₁ B) P n = 0 := by
        rw [congr_fun hcorr n, Pi.smul_apply, smul_eq_mul, ih, mul_zero]
      simp only [hlift, mul_zero, sum_const_zero, sub_zero, ih, derivative_zero,
        hc] at hid
      have hmul : affineIndex d₁ d₀ (n + k) * lagDefect a P (n + 1) = 0 := by
        simpa only [add_zero] using hid.symm
      exact (mul_eq_zero.mp hmul).resolve_left (hleader n)

/-- A differential lift valid from `n₀`, one source-defect seed, and explicit
source-defect seeds at every exceptional leader rank imply the source recurrence
from `n₀` onward.  A finite exceptional set can discharge `hexception` by cases. -/
theorem lagDefect_eq_zero_from_of_liftDefect_eq_zero_from_of_exceptional {k : ℕ}
    (a : Fin k → K[X]) (d₁ d₀ A₁ A₀ B gamma : K[X]) (P : ℕ → K[X]) (n₀ : ℕ)
    (hlift : ∀ n, n₀ ≤ n → liftDefect d₁ d₀ A₁ A₀ B P n = 0)
    (hfactor : defectCorrection a d₁ A₁ B = C gamma * lagCharacteristic a)
    (hseed : lagDefect a P n₀ = 0)
    (hexception : ∀ n, n₀ ≤ n → affineIndex d₁ d₀ (n + k) = 0 →
      lagDefect a P (n + 1) = 0) :
    ∀ n, n₀ ≤ n → lagDefect a P n = 0 := by
  have hcorr := shiftAction_defectCorrection_eq_smul_lagDefect a d₁ A₁ B gamma P hfactor
  intro m hm
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction r with
  | zero => simpa using hseed
  | succ r ih =>
      let n := n₀ + r
      have hn : n₀ ≤ n := by simp [n]
      have hRn : lagDefect a P n = 0 := by simpa [n] using ih
      by_cases hleader : affineIndex d₁ d₀ (n + k) = 0
      · simpa [n, Nat.add_assoc] using hexception n hn hleader
      · have hid := lagDefect_liftDefect a d₁ d₀ A₁ A₀ B P n
        change liftDefect d₁ d₀ A₁ A₀ B P (n + k) -
          ∑ i, a i * liftDefect d₁ d₀ A₁ A₀ B P (n + i) = _ at hid
        have hc : LinearRecurrence.shiftAction (defectCorrection a d₁ A₁ B) P n = 0 := by
          rw [congr_fun hcorr n, Pi.smul_apply, smul_eq_mul, hRn, mul_zero]
        have hEnk := hlift (n + k) (by lia)
        have hEi : ∀ i : Fin k, liftDefect d₁ d₀ A₁ A₀ B P (n + i) = 0 :=
          fun i ↦ hlift (n + i) (by lia)
        simp only [hEnk, hEi, mul_zero, sum_const_zero, sub_zero, hRn,
          derivative_zero, hc] at hid
        have hmul : affineIndex d₁ d₀ (n + k) * lagDefect a P (n + 1) = 0 := by
          simpa only [add_zero] using hid.symm
        have := (mul_eq_zero.mp hmul).resolve_left hleader
        simpa [n, Nat.add_assoc] using this

/-- The regular-leader specialization of
`lagDefect_eq_zero_from_of_liftDefect_eq_zero_from_of_exceptional`. -/
theorem lagDefect_eq_zero_from_of_liftDefect_eq_zero_from {k : ℕ}
    (a : Fin k → K[X]) (d₁ d₀ A₁ A₀ B gamma : K[X]) (P : ℕ → K[X]) (n₀ : ℕ)
    (hlift : ∀ n, n₀ ≤ n → liftDefect d₁ d₀ A₁ A₀ B P n = 0)
    (hfactor : defectCorrection a d₁ A₁ B = C gamma * lagCharacteristic a)
    (hseed : lagDefect a P n₀ = 0)
    (hleader : ∀ n, n₀ ≤ n → affineIndex d₁ d₀ (n + k) ≠ 0) :
    ∀ n, n₀ ≤ n → lagDefect a P n = 0 := by
  apply lagDefect_eq_zero_from_of_liftDefect_eq_zero_from_of_exceptional a
    d₁ d₀ A₁ A₀ B gamma P n₀ hlift hfactor hseed
  intro n hn hzero
  exact absurd hzero (hleader n hn)

/-- A zero lift defect with a nonzero scalar leader is the derivative recurrence in
the coefficient order used by the root-window theorems. -/
theorem derivativeRecurrence_of_liftDefect_eq_zero
    (d₁ d₀ A₁ A₀ B : K[X]) (P : ℕ → K[X]) (delta : ℕ → K)
    (hlift : ∀ n, liftDefect d₁ d₀ A₁ A₀ B P n = 0)
    (hdelta : ∀ n, affineIndex d₁ d₀ n = C (delta n))
    (hdelta_ne : ∀ n, delta n ≠ 0) (n : ℕ) :
    P (n + 1) = C (delta n)⁻¹ * B * (P n).derivative +
      C (delta n)⁻¹ * affineIndex A₁ A₀ n * P n := by
  have h := hlift n
  rw [liftDefect, hdelta n] at h
  have hc : C (delta n) ≠ 0 := C_ne_zero.mpr (hdelta_ne n)
  apply mul_left_cancel₀ hc
  rw [mul_add]
  simp only [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hdelta_ne n), C_1, one_mul]
  linear_combination h

end

end RealRooted
