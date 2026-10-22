import RealRooted.CombinatorialExamples.PathPowerClique

/-!
# Fault-free two-column Ferrers-tile polynomials

This file formalizes Ahlberg--Alexandersson, *Polynomials from tilings of
rectangles*, Lemmas 6.2 and 6.3, at the algebraic level.
-/

open Polynomial

namespace RealRooted
namespace FerrersTiling

noncomputable section

/-- The fault-free polynomial `B_d` for the rectangular tile `(k,k)`.
Its coefficient of `X^m` is the bars-and-stars number from Lemma 6.2. -/
def rectangleFaultFreePolynomial (k d : ℕ) : ℝ[X] :=
  pathPowerCliquePolynomial k (d + k - 1)

/-- The closed coefficient formula from Ahlberg--Alexandersson, Lemma 6.2. -/
@[simp]
theorem coeff_rectangleFaultFreePolynomial (k d m : ℕ) :
    (rectangleFaultFreePolynomial k d).coeff m =
      (Nat.choose (d + k - 1 - (k - 1) * m) m : ℝ) := by
  exact coeff_pathPowerCliquePolynomial k (d + k - 1) m

/-- The recurrence `B_d = B_(d-1) + X B_(d-k)` from
Ahlberg--Alexandersson, Lemma 6.3. -/
theorem rectangleFaultFreePolynomial_eq_add (k d : ℕ)
    (hk : 2 ≤ k) (hdk : k ≤ d) :
    rectangleFaultFreePolynomial k d =
      rectangleFaultFreePolynomial k (d - 1) +
        X * rectangleFaultFreePolynomial k (d - k) := by
  have h := pathPowerCliquePolynomial_add_lag k (d - 1) hk
  simpa [rectangleFaultFreePolynomial,
    show d - 1 + k = d + k - 1 by lia,
    show d - 1 + k - 1 = (d - 1) + k - 1 by rfl,
    show d - k + k - 1 = d - 1 by lia] using h

/-- The initial values are `B_d = 1 + d X` when `d ≤ k`. -/
theorem rectangleFaultFreePolynomial_eq_one_add (k d : ℕ)
    (hk : 2 ≤ k) (hdk : d ≤ k) :
    rectangleFaultFreePolynomial k d = 1 + C (d : ℝ) * X := by
  ext m
  rw [coeff_rectangleFaultFreePolynomial, coeff_add]
  rcases m with _ | _ | m
  · simp
  · rw [coeff_one, coeff_C_mul, coeff_X]
    norm_num
    lia
  · rw [coeff_one, coeff_C_mul, coeff_X]
    simp only [Nat.succ_ne_zero, ite_false, zero_add]
    norm_cast
    apply Nat.choose_eq_zero_of_lt
    have hm : 2 ≤ m + 2 := by lia
    have hmul : 2 * k ≤ (m + 2) * k := Nat.mul_le_mul_right k hm
    have hid : (k - 1) * (m + 2) + (m + 2) = (m + 2) * k := by
      calc
        (k - 1) * (m + 2) + (m + 2) = ((k - 1) + 1) * (m + 2) := by ring
        _ = k * (m + 2) := by rw [Nat.sub_add_cancel (by lia)]
        _ = (m + 2) * k := by ring
    by_cases hle : (k - 1) * (m + 2) ≤ d + k - 1
    · apply (Nat.sub_lt_iff_lt_add hle).2
      have hbound : d + k - 1 < (m + 2) * k :=
        lt_of_lt_of_le (by lia) hmul
      rw [← hid] at hbound
      simpa [show m + 1 + 1 = m + 2 by lia, Nat.add_comm] using hbound
    · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hle)]
      lia

/-- Consecutive fault-free rectangle polynomials interlace. -/
theorem rectangleFaultFreePolynomial_interl (k d : ℕ)
    (hk : 2 ≤ k) (hd : 1 ≤ d) :
    Interl (rectangleFaultFreePolynomial k (d - 1))
      (rectangleFaultFreePolynomial k d) := by
  have h := strictInterl_pathPowerCliquePolynomial_add
    k (d - 1 + k - 1) 1 hk (by norm_num) (by lia)
  simpa [rectangleFaultFreePolynomial,
    show d - 1 + k - 1 + 1 = d + k - 1 by lia] using h.toInterl

/-- Every fault-free rectangle polynomial is Pólya-frequency, hence real-rooted. -/
theorem rectangleFaultFreePolynomial_isPFPolynomial (k d : ℕ) :
    IsPFPolynomial (rectangleFaultFreePolynomial k d) :=
  isPFPolynomial_pathPowerCliquePolynomial k (d + k - 1)

/-- Every fault-free rectangle polynomial is real-rooted. -/
theorem rectangleFaultFreePolynomial_splits (k d : ℕ) :
    (rectangleFaultFreePolynomial k d).Splits :=
  splits_pathPowerCliquePolynomial k (d + k - 1)

end

end FerrersTiling
end RealRooted
