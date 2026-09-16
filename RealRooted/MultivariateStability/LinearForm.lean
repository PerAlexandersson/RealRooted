import RealRooted.MultivariateStability
import Mathlib.Data.Complex.BigOperators

/-!
# Stable homogeneous linear forms

This file proves that a nonzero homogeneous linear form with nonnegative real
coefficients is multivariate stable.  The variables may be indexed with
repetition, which makes the result convenient for finite combinatorial sums.
-/

namespace RealRooted

open scoped BigOperators

noncomputable section

/-- A finite homogeneous linear form with nonnegative real coefficients, at
least one of them positive, is upper-half-plane stable. -/
theorem MvUpperHalfPlaneStable.finset_sum_C_mul_X
    {σ ι : Type*} (s : Finset ι) (a : ι → Real) (f : ι → σ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hpos : ∃ i ∈ s, 0 < a i) :
    MvUpperHalfPlaneStable
      (∑ i ∈ s,
        MvPolynomial.C (a i : Complex) * MvPolynomial.X (f i)) := by
  intro z hz hzero
  simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X] at hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at him
  obtain ⟨i, hi, hai⟩ := hpos
  have hsum : 0 < ∑ j ∈ s, a j * (z (f j)).im := by
    apply Finset.sum_pos'
    · intro j hj
      exact mul_nonneg (ha j hj) (hz (f j)).le
    · exact ⟨i, hi, mul_pos hai (hz (f i))⟩
  exact (ne_of_gt hsum) him

/-- Real-coefficient form of stability for a finite nonnegative homogeneous
linear form. -/
theorem MvRealStable.finset_sum_C_mul_X
    {σ ι : Type*} (s : Finset ι) (a : ι → Real) (f : ι → σ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hpos : ∃ i ∈ s, 0 < a i) :
    MvRealStable
      (∑ i ∈ s,
        MvPolynomial.C (a i) * MvPolynomial.X (f i)) := by
  unfold MvRealStable complexifyMv
  simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  exact MvUpperHalfPlaneStable.finset_sum_C_mul_X s a f ha hpos

/-- A nontrivial nonnegative combination of two coordinate variables is
multivariate real stable. -/
theorem MvRealStable.C_mul_X_add_C_mul_X {σ : Type*} (i j : σ)
    {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) (hpos : 0 < a ∨ 0 < b) :
    MvRealStable
      (MvPolynomial.C a * MvPolynomial.X i +
        MvPolynomial.C b * MvPolynomial.X j) := by
  let weight : Fin 2 → Real := fun k => if k = 0 then a else b
  let label : Fin 2 → σ := fun k => if k = 0 then i else j
  have hstable := MvRealStable.finset_sum_C_mul_X
    (Finset.univ : Finset (Fin 2)) weight label (by
      intro k hk
      fin_cases k
      · exact ha
      · exact hb) (by
        rcases hpos with ha | hb
        · exact ⟨0, Finset.mem_univ _, by simpa [weight]⟩
        · exact ⟨1, Finset.mem_univ _, by simpa [weight]⟩)
  simpa [weight, label, Fin.sum_univ_two] using hstable

end

end RealRooted
