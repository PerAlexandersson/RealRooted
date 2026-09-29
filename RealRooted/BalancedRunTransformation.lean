import RealRooted.BasisTransform

/-!
# Balanced run transformation

This file defines the balanced kernel

`U n m = choose n m ⁻¹ · ∑ k, choose m k · choose (n - m) k · X ^ k`

and the coefficientwise linear map sending `X ^ m` to `U n m`.  This is the
kernel transform used by the interlacing comparison for Motzkin ascent
polynomials.  Its reflection symmetry gives the equal central pair when the
rank is odd.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- The normalized balanced run kernel `U_{n,m}`. -/
def balancedRunPolynomial (n m : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k
      (((Nat.choose m k : ℝ) * (Nat.choose (n - m) k : ℝ)) /
        (Nat.choose n m : ℝ))

/-- Coefficients of the balanced run kernel. -/
theorem coeff_balancedRunPolynomial (n m k : ℕ) (hm : m ≤ n) :
    (balancedRunPolynomial n m).coeff k =
      ((Nat.choose m k : ℝ) * (Nat.choose (n - m) k : ℝ)) /
        (Nat.choose n m : ℝ) := by
  rw [balancedRunPolynomial, Polynomial.finsetSum_coeff]
  by_cases hk : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      simp [coeff_monomial, hbk]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).elim
  · have hmk : m < k := lt_of_le_of_lt hm (Nat.lt_of_not_ge hk)
    have hsum :
        (∑ b ∈ Finset.range (n + 1),
          (monomial b
            (((Nat.choose m b : ℝ) *
                (Nat.choose (n - m) b : ℝ)) /
              (Nat.choose n m : ℝ))).coeff k) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [coeff_monomial]
      split_ifs with hbk
      · subst b
        exact (hk (Nat.le_of_lt_succ (Finset.mem_range.mp hb))).elim
      · rfl
    rw [hsum, Nat.choose_eq_zero_of_lt hmk]
    simp

/-- Every balanced run kernel has nonnegative coefficients. -/
theorem hasNonnegCoeffs_balancedRunPolynomial (n m : ℕ) :
    HasNonnegCoeffs (balancedRunPolynomial n m) := by
  intro j
  rw [balancedRunPolynomial, Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun k _ => by
    rw [coeff_monomial]
    split <;> positivity

/-- A balanced run kernel in its natural range is nonzero. -/
theorem balancedRunPolynomial_ne_zero (n m : ℕ) (hm : m ≤ n) :
    balancedRunPolynomial n m ≠ 0 := by
  have hcoeff : 0 < (balancedRunPolynomial n m).coeff 0 := by
    rw [coeff_balancedRunPolynomial n m 0 hm]
    have hchoose : 0 < (Nat.choose n m : ℝ) := by
      exact_mod_cast Nat.choose_pos hm
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
    positivity
  intro hzero
  rw [hzero] at hcoeff
  simp at hcoeff

/-- The balanced kernel is invariant under complementing its basis index. -/
theorem balancedRunPolynomial_reflection (n m : ℕ) (hm : m ≤ n) :
    balancedRunPolynomial n m = balancedRunPolynomial n (n - m) := by
  ext k
  rw [coeff_balancedRunPolynomial n m k hm,
    coeff_balancedRunPolynomial n (n - m) k (Nat.sub_le n m),
    Nat.sub_sub_self hm, Nat.choose_symm hm]
  ring

/-- At odd rank, the two central balanced kernels coincide. -/
theorem balancedRunPolynomial_odd_central (r : ℕ) :
    balancedRunPolynomial (2 * r + 1) (r + 1) =
      balancedRunPolynomial (2 * r + 1) r := by
  have hreflect := balancedRunPolynomial_reflection (2 * r + 1) r (by lia)
  have hindex : 2 * r + 1 - r = r + 1 := by lia
  rw [hindex] at hreflect
  exact hreflect.symm

/-- The fixed-rank balanced run basis transform. -/
def balancedRunTransform (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  Polynomial.basisTransform (balancedRunPolynomial n) p

@[simp] theorem balancedRunTransform_X_pow (n m : ℕ) :
    balancedRunTransform n (X ^ m) = balancedRunPolynomial n m := by
  simp [balancedRunTransform]

@[simp] theorem balancedRunTransform_zero (n : ℕ) :
    balancedRunTransform n 0 = 0 := by
  simp [balancedRunTransform]

theorem balancedRunTransform_add (n : ℕ) (p q : ℝ[X]) :
    balancedRunTransform n (p + q) =
      balancedRunTransform n p + balancedRunTransform n q := by
  simp [balancedRunTransform, Polynomial.basisTransform_add]

theorem balancedRunTransform_smul (n : ℕ) (a : ℝ) (p : ℝ[X]) :
    balancedRunTransform n (a • p) = a • balancedRunTransform n p := by
  change Polynomial.basisTransform (balancedRunPolynomial n) (a • p) =
    a • Polynomial.basisTransform (balancedRunPolynomial n) p
  rw [Polynomial.basisTransform_smul, Polynomial.smul_eq_C_mul]

/-- The balanced run transform as a real-linear map. -/
def balancedRunTransformLinearMap (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := balancedRunTransform n
  map_add' := balancedRunTransform_add n
  map_smul' := balancedRunTransform_smul n

@[simp] theorem balancedRunTransformLinearMap_apply (n : ℕ) (p : ℝ[X]) :
    balancedRunTransformLinearMap n p = balancedRunTransform n p := rfl

/-- The balanced run transform preserves coefficientwise nonnegativity. -/
theorem HasNonnegCoeffs.balancedRunTransform {n : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (balancedRunTransform n p) :=
  hp.basisTransform (hasNonnegCoeffs_balancedRunPolynomial n)

end RealRooted
