import RealRooted.Derivative
import RealRooted.BasisTransform
import RealRooted.Transforms.BrandenE.Basic
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Binomial-basis images under Brändén's E transform

This module packages the ambient-degree binomial basis, its images under the
`E` transform, the associated Euler differential step, and the elementary
coefficient and root-window geometry used by the proper-position theory.
-/

open Polynomial

noncomputable section

namespace RealRooted

universe u

variable {R : Type u}

section Semiring

variable [Semiring R]

/-- The `k`th ambient-degree binomial basis polynomial. -/
def brandenBinomialBasis (n k : ℕ) : R[X] :=
  X ^ k * (X + 1) ^ (n - k)

/-- Image of an ambient-degree binomial basis polynomial under `brandenE`. -/
def brandenBasisImage (n k : ℕ) : R[X] :=
  brandenE (brandenBinomialBasis n k)

/-- The first-order Euler step governing the binomial-basis images. -/
def brandenEulerStep (r : R) (p : R[X]) : R[X] :=
  (X + C r) * p + X * (1 + X) * p.derivative

@[simp] theorem brandenBasisImage_zero :
    brandenBasisImage (R := R) 0 0 = 1 := by
  rw [brandenBasisImage, brandenBinomialBasis]
  simp only [pow_zero, Nat.zero_sub, mul_one]
  rw [show (1 : R[X]) = X ^ 0 by simp, brandenE_X_pow]
  rfl

@[simp] theorem brandenBasisImage_self (n : ℕ) :
    brandenBasisImage (R := R) n n = orderedBellPolynomial n := by
  simp [brandenBasisImage, brandenBinomialBasis]

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- Coefficients of the Euler step form a lower-bidiagonal transform. -/
theorem coeff_brandenEulerStep (r : R) (p : R[X]) (k : ℕ) :
    (brandenEulerStep r p).coeff k =
      (r + k) * p.coeff k + k * p.coeff (k - 1) := by
  have hform : brandenEulerStep r p =
      C r * p + X * p + X * p.derivative + X ^ 2 * p.derivative := by
    simp [brandenEulerStep]
    ring
  rw [hform]
  cases k with
  | zero => simp
  | succ k =>
      cases k with
      | zero =>
          simp [Polynomial.coeff_derivative, Polynomial.coeff_X_pow_mul']
          ring
      | succ k =>
          simp [Polynomial.coeff_derivative, Polynomial.coeff_X_pow_mul']
          ring

theorem brandenBasisImage_succ_zero (n : ℕ) :
    brandenBasisImage (R := R) (n + 1) 0 =
      brandenEulerStep 1 (brandenBasisImage n 0) := by
  rw [brandenBasisImage, brandenBasisImage, brandenBinomialBasis,
    brandenBinomialBasis]
  simp only [pow_zero, one_mul, Nat.sub_zero, pow_succ']
  simpa [brandenEulerStep] using brandenE_mul_X_add_C 1 ((X + 1) ^ n : R[X])

theorem brandenBasisImage_succ_succ (n k : ℕ) :
    brandenBasisImage (R := R) (n + 1) (k + 1) =
      brandenEulerStep 0 (brandenBasisImage n k) := by
  rw [brandenBasisImage, brandenBasisImage, brandenBinomialBasis,
    brandenBinomialBasis]
  rw [Nat.add_sub_add_right, pow_succ']
  rw [show X * X ^ k * (X + 1) ^ (n - k) =
      X * (X ^ k * (X + 1) ^ (n - k)) by ring]
  simpa [brandenEulerStep] using
    brandenE_X_mul (X ^ k * (X + 1) ^ (n - k) : R[X])

theorem brandenBasisImage_succ_same (n k : ℕ) (hk : k ≤ n) :
    brandenBasisImage (R := R) (n + 1) k =
      brandenEulerStep 1 (brandenBasisImage n k) := by
  rw [brandenBasisImage, brandenBasisImage, brandenBinomialBasis,
    brandenBinomialBasis]
  rw [show n + 1 - k = (n - k) + 1 by lia, pow_succ']
  rw [show X ^ k * ((X + 1) * (X + 1) ^ (n - k)) =
      (X + 1) * (X ^ k * (X + 1) ^ (n - k)) by ring]
  simpa [brandenEulerStep] using
    brandenE_mul_X_add_C 1 (X ^ k * (X + 1) ^ (n - k) : R[X])

theorem brandenEulerStep_C_mul (r a : R) (p : R[X]) :
    brandenEulerStep r (C a * p) = C a * brandenEulerStep r p := by
  simp [brandenEulerStep, Polynomial.derivative_mul]
  ring

end CommSemiring

section CommRing

variable [CommRing R]

/-- Reflection across `-1 / 2` conjugates the Euler parameter `r` to
`1 - r`, up to sign. -/
theorem brandenEulerStep_comp_reflect (r : R) (p : R[X]) :
    (brandenEulerStep r p).comp (C (-1) - X) =
      -(brandenEulerStep (1 - r) (p.comp (C (-1) - X))) := by
  simp only [brandenEulerStep, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.X_comp, Polynomial.C_comp, Polynomial.one_comp,
    Polynomial.derivative_comp, Polynomial.derivative_sub,
    Polynomial.derivative_C, Polynomial.derivative_X, zero_sub]
  norm_num [map_sub, map_add, map_mul, map_neg]
  ring

/-- The binomial-basis images are exchanged by reflection across `-1 / 2`. -/
theorem brandenBasisImage_reflect :
    ∀ n k : ℕ, k ≤ n →
      (brandenBasisImage (R := R) n k).comp (C (-1) - X) =
        C ((-1 : R) ^ n) * brandenBasisImage n (n - k) := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by lia
      subst k
      simp
  | succ n ih =>
      intro k hk
      cases k with
      | zero =>
          rw [brandenBasisImage_succ_zero, brandenEulerStep_comp_reflect,
            ih 0 (by lia), brandenEulerStep_C_mul]
          rw [show 1 - (1 : R) = 0 by ring]
          simp only [Nat.sub_zero]
          rw [← brandenBasisImage_succ_succ n n]
          rw [show (-1 : R) ^ (n + 1) = -((-1 : R) ^ n) by ring, map_neg]
          ring
      | succ k =>
          have hkn : k ≤ n := by lia
          rw [brandenBasisImage_succ_succ, brandenEulerStep_comp_reflect,
            ih k hkn, brandenEulerStep_C_mul]
          rw [show 1 - (0 : R) = 1 by ring]
          rw [← brandenBasisImage_succ_same n (n - k) (by lia)]
          rw [show n + 1 - (k + 1) = n - k by lia]
          rw [show (-1 : R) ^ (n + 1) = -((-1 : R) ^ n) by ring, map_neg]
          ring

end CommRing

section Real

/-- Binomial-basis images have nonnegative coefficients. -/
theorem brandenBasisImage_nonneg (n k : ℕ) :
    HasNonnegCoeffs (brandenBasisImage (R := ℝ) n k) := by
  apply HasNonnegCoeffs.basisTransform
  · exact (hasNonnegCoeffs_X.pow k).mul
      (hasNonnegCoeffs_X_add_one.pow (n - k))
  · exact hasNonnegCoeffs_orderedBellPolynomial

theorem brandenEulerStep_nonneg {r : ℝ} {p : ℝ[X]}
    (hr : 0 ≤ r) (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (brandenEulerStep r p) := by
  rw [brandenEulerStep]
  apply HasNonnegCoeffs.add
  · exact (hasNonnegCoeffs_X_add_C hr).mul hp
  · simpa [add_comm] using
      ((hasNonnegCoeffs_X.mul hasNonnegCoeffs_X_add_one).mul hp.derivative)

/-- Every Euler step raises the exact degree of a positive-leading input and
preserves positivity of its leading coefficient. -/
theorem brandenEulerStep_degree_pos {r : ℝ} {p : ℝ[X]} {n : ℕ}
    (hp_pos : HasPosLeadingCoeff p) (hdeg : p.natDegree = n) :
    (brandenEulerStep r p).natDegree = n + 1 ∧
      HasPosLeadingCoeff (brandenEulerStep r p) := by
  have hupper : (brandenEulerStep r p).natDegree ≤ n + 1 := by
    rw [brandenEulerStep]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · calc
        ((X + C r) * p).natDegree
            ≤ (X + C r).natDegree + p.natDegree := Polynomial.natDegree_mul_le
        _ = n + 1 := by rw [natDegree_X_add_C, hdeg]; lia
    · by_cases hn : n = 0
      · have hpder : p.derivative = 0 := by
          have hpdeg0 : p.natDegree = 0 := by simpa [hn] using hdeg
          rw [Polynomial.eq_C_of_natDegree_eq_zero hpdeg0]
          simp
        simp [hpder]
      · calc
          (X * (1 + X) * p.derivative).natDegree
              ≤ (X * (1 + X)).natDegree + p.derivative.natDegree :=
                Polynomial.natDegree_mul_le
          _ ≤ 2 + (n - 1) := by
            apply Nat.add_le_add
            · compute_degree
            · rw [p.natDegree_derivative, hdeg]
          _ = n + 1 := by lia
  have hp_top : 0 < p.coeff n := by
    rw [← hdeg]
    exact hp_pos
  have hp_above : p.coeff (n + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; lia)
  have hcoeff : 0 < (brandenEulerStep r p).coeff (n + 1) := by
    rw [coeff_brandenEulerStep, hp_above]
    norm_num
    positivity
  have hdegree : (brandenEulerStep r p).natDegree = n + 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hupper hcoeff.ne'
  refine ⟨hdegree, ?_⟩
  rw [HasPosLeadingCoeff, leadingCoeff, hdegree]
  exact hcoeff

/-- Exact degree and positive leading coefficient of every in-range basis
image. -/
theorem brandenBasisImage_degree_pos :
    ∀ n k : ℕ, k ≤ n →
      (brandenBasisImage (R := ℝ) n k).natDegree = n ∧
        HasPosLeadingCoeff (brandenBasisImage n k) := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by lia
      subst k
      rw [brandenBasisImage_zero]
      exact ⟨natDegree_one, hasPosLeadingCoeff_one⟩
  | succ n ih =>
      intro k hk
      cases k with
      | zero =>
          rw [brandenBasisImage_succ_zero]
          exact brandenEulerStep_degree_pos (r := 1)
            (ih 0 (by lia)).2 (ih 0 (by lia)).1
      | succ k =>
          have hkn : k ≤ n := by lia
          rw [brandenBasisImage_succ_succ]
          exact brandenEulerStep_degree_pos (r := 0)
            (ih k hkn).2 (ih k hkn).1

theorem brandenBasisImage_roots_nonpos (n k : ℕ) :
    ∀ r ∈ (brandenBasisImage (R := ℝ) n k).roots, r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs (brandenBasisImage_nonneg n k)

/-- Every root of an in-range basis image lies to the right of `-1`. -/
theorem brandenBasisImage_roots_ge_neg_one (n k : ℕ) (hk : k ≤ n) :
    ∀ r ∈ (brandenBasisImage (R := ℝ) n k).roots, -1 ≤ r := by
  intro r hr
  by_contra hnot
  have hrlt : r < -1 := lt_of_not_ge hnot
  let t : ℝ := -1 - r
  have ht : 0 < t := by dsimp [t]; linarith
  have href := congrArg (Polynomial.eval t) (brandenBasisImage_reflect n k hk)
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C] at href
  have harg : (C (-1) - X : ℝ[X]).eval t = r := by simp [t]
  rw [harg] at href
  have hleft : (brandenBasisImage n k).eval r = 0 :=
    (mem_roots (brandenBasisImage_degree_pos n k hk).2.ne_zero).mp hr
  rw [hleft] at href
  have hpow : ((-1 : ℝ) ^ n) ≠ 0 := by positivity
  have hother_pos : 0 < (brandenBasisImage n (n - k)).eval t :=
    eval_pos_of_hasNonnegCoeffs (brandenBasisImage_nonneg n (n - k))
      (brandenBasisImage_degree_pos n (n - k) (by lia)).2.ne_zero ht
  exact (mul_ne_zero hpow hother_pos.ne') href.symm

end Real

end RealRooted
