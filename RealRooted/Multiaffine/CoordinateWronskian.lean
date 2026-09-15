import RealRooted.Multiaffine.Rayleigh

/-!
# Coordinate Wronskians of multivariate polynomials

This file packages the first-order determinant associated with one coordinate.
Its directional-derivative specialization is a weighted row sum of Rayleigh
differences, making the orientation and positivity hypotheses explicit.
-/

namespace MvPolynomial

noncomputable section

/-- The Wronskian of two multivariate polynomials in one coordinate, with the
same orientation as `Polynomial.wronskian`. -/
def coordinateWronskian {R σ : Type*} [CommRing R]
    (P Q : MvPolynomial σ R) (i : σ) : MvPolynomial σ R :=
  P * pderiv i Q - pderiv i P * Q

/-- The coordinate Wronskian of a polynomial with itself vanishes. -/
@[simp] theorem coordinateWronskian_self {R σ : Type*} [CommRing R]
    (P : MvPolynomial σ R) (i : σ) : coordinateWronskian P P i = 0 := by
  simp only [coordinateWronskian]
  ring

/-- Swapping the two polynomials negates their coordinate Wronskian. -/
theorem coordinateWronskian_swap {R σ : Type*} [CommRing R]
    (P Q : MvPolynomial σ R) (i : σ) :
    coordinateWronskian Q P i = -coordinateWronskian P Q i := by
  simp only [coordinateWronskian]
  ring

/-- Coordinate Wronskians commute with injective variable renamings. -/
theorem coordinateWronskian_rename
    {R σ τ : Type*} [CommRing R] (f : σ → τ)
    (hf : Function.Injective f) (P Q : MvPolynomial σ R) (i : σ) :
    coordinateWronskian (rename f P) (rename f Q) (f i) =
      rename f (coordinateWronskian P Q i) := by
  simp only [coordinateWronskian, pderiv_rename hf, map_mul, map_sub]

/-- Coordinate Wronskians are additive in their left argument. -/
theorem coordinateWronskian_add_left {R σ : Type*} [CommRing R]
    (P Q S : MvPolynomial σ R) (i : σ) :
    coordinateWronskian (P + Q) S i =
      coordinateWronskian P S i + coordinateWronskian Q S i := by
  simp only [coordinateWronskian, map_add]
  ring

/-- Coordinate Wronskians respect subtraction in their left argument. -/
theorem coordinateWronskian_sub_left {R σ : Type*} [CommRing R]
    (P Q S : MvPolynomial σ R) (i : σ) :
    coordinateWronskian (P - Q) S i =
      coordinateWronskian P S i - coordinateWronskian Q S i := by
  simp only [coordinateWronskian, map_sub]
  ring

/-- Scaling the left argument scales its coordinate Wronskian. -/
theorem coordinateWronskian_C_mul_left {R σ : Type*} [CommRing R]
    (c : R) (P Q : MvPolynomial σ R) (i : σ) :
    coordinateWronskian (C c * P) Q i =
      C c * coordinateWronskian P Q i := by
  simp only [coordinateWronskian, pderiv_C_mul]
  ring

/-- Coordinate Wronskians commute with finite sums in their left argument. -/
theorem coordinateWronskian_sum_left
    {R σ ι : Type*} [CommRing R] {s : Finset ι}
    (P : ι → MvPolynomial σ R) (Q : MvPolynomial σ R) (i : σ) :
    coordinateWronskian (∑ j ∈ s, P j) Q i =
      ∑ j ∈ s, coordinateWronskian (P j) Q i := by
  simp only [coordinateWronskian, map_sum, Finset.sum_mul,
    Finset.sum_sub_distrib]

/-- Coordinate Wronskians are additive in their right argument. -/
theorem coordinateWronskian_add_right {R σ : Type*} [CommRing R]
    (P Q S : MvPolynomial σ R) (i : σ) :
    coordinateWronskian P (Q + S) i =
      coordinateWronskian P Q i + coordinateWronskian P S i := by
  simp only [coordinateWronskian, map_add]
  ring

/-- Partial differentiation commutes with a constant-coefficient directional
derivative. -/
theorem pderiv_directionalPDeriv {R σ : Type*} [CommRing R] [Fintype σ]
    (b : σ → R) (P : MvPolynomial σ R) (i : σ) :
    pderiv i (RealRooted.directionalPDeriv b P) =
      RealRooted.directionalPDeriv b (pderiv i P) := by
  classical
  simp only [RealRooted.directionalPDeriv, map_sum, pderiv_C_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pderiv_comm]

/-- The Wronskian of a directional derivative against its source polynomial
is the corresponding weighted row sum of Rayleigh differences. -/
theorem coordinateWronskian_directionalPDeriv_left
    {R σ : Type*} [CommRing R] [Fintype σ]
    (b : σ → R) (P : MvPolynomial σ R) (i : σ) :
    coordinateWronskian (RealRooted.directionalPDeriv b P) P i =
      ∑ j, C (b j) * rayleighDifference P i j := by
  rw [coordinateWronskian, pderiv_directionalPDeriv]
  simpa only [mul_comm] using pderiv_mul_directionalPDeriv_sub b P i

/-- A finitely indexed sum of coordinate derivatives has Wronskian equal to
the corresponding indexed sum of Rayleigh differences. The polynomial's
variable type itself need not be finite. -/
theorem coordinateWronskian_sum_pderiv_left
    {R σ ι : Type*} [CommRing R] [Fintype ι]
    (f : ι → σ) (b : ι → R) (P : MvPolynomial σ R) (i : σ) :
    coordinateWronskian
        (∑ j : ι, C (b j) * pderiv (f j) P) P i =
      ∑ j : ι, C (b j) * rayleighDifference P i (f j) := by
  classical
  rw [coordinateWronskian_sum_left]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [coordinateWronskian, rayleighDifference, pderiv_C_mul,
    pderiv_comm i]
  ring

/-- Multiplying a coordinate derivative by its coordinate contributes a
weighted Rayleigh difference and one diagonal correction. -/
theorem coordinateWronskian_X_mul_pderiv_left
    {R σ : Type*} [CommRing R] [DecidableEq σ]
    (P : MvPolynomial σ R) (i j : σ) :
    coordinateWronskian (X j * pderiv j P) P i =
      X j * rayleighDifference P i j -
        if i = j then P * pderiv i P else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [coordinateWronskian, rayleighDifference, pderiv_mul,
      pderiv_X_self, one_mul, if_pos]
    ring
  · simp only [coordinateWronskian, rayleighDifference, pderiv_mul,
      pderiv_X_of_ne (Ne.symm hij), zero_mul, zero_add, if_neg hij,
      sub_zero, pderiv_comm i]
    ring

/-- An injectively indexed Euler sum has Wronskian equal to the weighted
Rayleigh row minus its unique diagonal correction. -/
theorem coordinateWronskian_sum_X_mul_pderiv_left
    {R σ ι : Type*} [CommRing R] [Fintype ι]
    (f : ι → σ) (hf : Function.Injective f)
    (P : MvPolynomial σ R) (i : ι) :
    coordinateWronskian
        (∑ j : ι, X (f j) * pderiv (f j) P) P (f i) =
      (∑ j : ι, X (f j) * rayleighDifference P (f i) (f j)) -
        P * pderiv (f i) P := by
  classical
  rw [coordinateWronskian_sum_left]
  simp_rw [coordinateWronskian_X_mul_pderiv_left]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp [hf.eq_iff]

/-- A nonnegative directional derivative has nonnegative coordinate
Wronskian against a Rayleigh polynomial. -/
theorem IsRayleigh.eval_coordinateWronskian_directionalPDeriv_nonneg
    {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℝ}
    (hP : IsRayleigh P) (b : σ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (i : σ) (x : σ → ℝ) :
    0 ≤ eval x
      (coordinateWronskian (RealRooted.directionalPDeriv b P) P i) := by
  classical
  rw [coordinateWronskian_directionalPDeriv_left, map_sum]
  apply Finset.sum_nonneg
  intro j hj
  rw [eval_mul, eval_C]
  exact mul_nonneg (hb j) (hP i j x)

/-- A nonnegatively weighted finite sum of coordinate derivatives has
nonnegative coordinate Wronskian against a Rayleigh polynomial. -/
theorem IsRayleigh.eval_coordinateWronskian_sum_pderiv_nonneg
    {σ ι : Type*} [Fintype ι] {P : MvPolynomial σ ℝ}
    (hP : IsRayleigh P) (f : ι → σ) (b : ι → ℝ)
    (hb : ∀ j, 0 ≤ b j) (i : σ) (x : σ → ℝ) :
    0 ≤ eval x
      (coordinateWronskian
        (∑ j : ι, C (b j) * pderiv (f j) P) P i) := by
  classical
  rw [coordinateWronskian_sum_pderiv_left, map_sum]
  apply Finset.sum_nonneg
  intro j hj
  rw [eval_mul, eval_C]
  exact mul_nonneg (hb j) (hP i (f j) x)

end

end MvPolynomial
