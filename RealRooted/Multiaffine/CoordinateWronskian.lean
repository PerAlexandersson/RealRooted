import RealRooted.Mathlib.Algebra.MvPolynomial.Homogenize
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

/-- Dehomogenization commutes with coordinate Wronskians in every ordinary
coordinate. -/
theorem dehomogenize_coordinateWronskian_some
    {R σ : Type*} [CommRing R]
    (P Q : MvPolynomial (Option σ) R) (i : σ) :
    dehomogenize (coordinateWronskian P Q (some i)) =
      coordinateWronskian (dehomogenize P) (dehomogenize Q) i := by
  simp only [coordinateWronskian, map_sub, map_mul,
    dehomogenize_pderiv_some]

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

/-- The coordinate Wronskian of two multiaffine polynomials is the determinant
of their constant and linear parts in that coordinate. -/
theorem IsMultiaffine.coordinateWronskian_eq_specializeZero
    {R σ : Type*} [CommRing R] {P Q : MvPolynomial σ R}
    (hP : IsMultiaffine P) (hQ : IsMultiaffine Q) (i : σ) :
    coordinateWronskian P Q i =
      specializeZero i P * MvPolynomial.pderiv i Q -
        MvPolynomial.pderiv i P * specializeZero i Q := by
  have hPdecomp := hP.eq_specializeZero_add_X_mul_pderiv i
  have hQdecomp := hQ.eq_specializeZero_add_X_mul_pderiv i
  rw [coordinateWronskian]
  linear_combination
    MvPolynomial.pderiv i Q * hPdecomp -
      MvPolynomial.pderiv i P * hQdecomp

/-- The coordinate Wronskian of two multiaffine polynomials does not depend
on the coordinate in which it is taken. -/
theorem IsMultiaffine.notMem_vars_coordinateWronskian
    {R σ : Type*} [CommRing R] {P Q : MvPolynomial σ R}
    (hP : IsMultiaffine P) (hQ : IsMultiaffine Q) (i : σ) :
    i ∉ (coordinateWronskian P Q i).vars := by
  classical
  have hiP0 : i ∉ (specializeZero i P).vars := by
    intro hi
    have hiErase := vars_specializeZero_subset_erase P i hi
    exact (Finset.mem_erase.mp hiErase).1 rfl
  have hiQ0 : i ∉ (specializeZero i Q).vars := by
    intro hi
    have hiErase := vars_specializeZero_subset_erase Q i hi
    exact (Finset.mem_erase.mp hiErase).1 rfl
  have hiPi : i ∉ (MvPolynomial.pderiv i P).vars :=
    hP.notMem_vars_pderiv_self i
  have hiQi : i ∉ (MvPolynomial.pderiv i Q).vars :=
    hQ.notMem_vars_pderiv_self i
  have hiLeft :
      i ∉ (specializeZero i P * MvPolynomial.pderiv i Q).vars := by
    intro hi
    exact (Finset.mem_union.mp (vars_mul _ _ hi)).elim hiP0 hiQi
  have hiRight :
      i ∉ (MvPolynomial.pderiv i P * specializeZero i Q).vars := by
    intro hi
    exact (Finset.mem_union.mp (vars_mul _ _ hi)).elim hiPi hiQ0
  rw [hP.coordinateWronskian_eq_specializeZero hQ i]
  intro hi
  exact (Finset.mem_union.mp
    (vars_sub_subset
      (p := specializeZero i P * MvPolynomial.pderiv i Q)
      (q := MvPolynomial.pderiv i P * specializeZero i Q) hi)).elim
        hiLeft hiRight

/-- A coordinate absent from both inputs has zero coordinate Wronskian. -/
theorem coordinateWronskian_eq_zero_of_notMem_vars
    {R σ : Type*} [CommRing R] {P Q : MvPolynomial σ R} {i : σ}
    (hiP : i ∉ P.vars) (hiQ : i ∉ Q.vars) :
    coordinateWronskian P Q i = 0 := by
  rw [coordinateWronskian, pderiv_eq_zero_of_notMem_vars hiP,
    pderiv_eq_zero_of_notMem_vars hiQ]
  ring

/-- A variable absent from both inputs is absent from their coordinate
Wronskian, regardless of the coordinate in which it is taken. -/
theorem notMem_vars_coordinateWronskian_of_notMem_vars
    {R σ : Type*} [CommRing R] {P Q : MvPolynomial σ R} {k : σ}
    (hkP : k ∉ P.vars) (hkQ : k ∉ Q.vars) (i : σ) :
    k ∉ (coordinateWronskian P Q i).vars := by
  classical
  have hkPi : k ∉ (pderiv i P).vars :=
    fun h => hkP (vars_pderiv_subset P i h)
  have hkQi : k ∉ (pderiv i Q).vars :=
    fun h => hkQ (vars_pderiv_subset Q i h)
  intro h
  unfold coordinateWronskian at h
  rcases Finset.mem_union.mp
      (vars_sub_subset
        (p := P * pderiv i Q) (q := pderiv i P * Q) h) with
    hleft | hright
  · exact (Finset.mem_union.mp (vars_mul P (pderiv i Q) hleft)).elim
      hkP hkQi
  · exact (Finset.mem_union.mp (vars_mul (pderiv i P) Q hright)).elim
      hkPi hkQ

/-- A Rayleigh difference is a coordinate Wronskian of a partial derivative
against the original polynomial. -/
theorem rayleighDifference_eq_coordinateWronskian_pderiv
    {R σ : Type*} [CommRing R] (P : MvPolynomial σ R) (i j : σ) :
    rayleighDifference P i j = coordinateWronskian (pderiv i P) P j := by
  simp only [rayleighDifference, coordinateWronskian, pderiv_comm]
  ring

/-- A Rayleigh difference of a multiaffine polynomial does not depend on its
second active coordinate. -/
theorem IsMultiaffine.notMem_vars_rayleighDifference_right
    {R σ : Type*} [CommRing R] {P : MvPolynomial σ R}
    (hP : IsMultiaffine P) (i j : σ) :
    j ∉ (rayleighDifference P i j).vars := by
  rw [rayleighDifference_eq_coordinateWronskian_pderiv]
  exact (hP.pderiv i).notMem_vars_coordinateWronskian hP j

/-- A Rayleigh difference of a multiaffine polynomial does not depend on its
first active coordinate. -/
theorem IsMultiaffine.notMem_vars_rayleighDifference_left
    {R σ : Type*} [CommRing R] {P : MvPolynomial σ R}
    (hP : IsMultiaffine P) (i j : σ) :
    i ∉ (rayleighDifference P i j).vars := by
  rw [rayleighDifference_comm]
  exact hP.notMem_vars_rayleighDifference_right j i

/-- When both inputs are supported on `s`, global coordinate-Wronskian
nonnegativity is equivalent to checking only the coordinates in `s`. -/
theorem eval_coordinateWronskian_nonneg_iff_finset
    {R σ : Type*} [CommRing R] [Preorder R]
    (P Q : MvPolynomial σ R) (s : Finset σ)
    (hP : P.vars ⊆ s) (hQ : Q.vars ⊆ s) :
    (∀ i x, 0 ≤ eval x (coordinateWronskian P Q i)) ↔
      ∀ i ∈ s, ∀ x, 0 ≤ eval x (coordinateWronskian P Q i) := by
  classical
  constructor
  · intro h i hi x
    exact h i x
  · intro h i x
    by_cases hi : i ∈ s
    · exact h i hi x
    · have hiP : i ∉ P.vars := fun hiVars => hi (hP hiVars)
      have hiQ : i ∉ Q.vars := fun hiVars => hi (hQ hiVars)
      rw [coordinateWronskian_eq_zero_of_notMem_vars hiP hiQ, map_zero]

/-- Coordinate Wronskians commute with injective variable renamings. -/
theorem coordinateWronskian_rename
    {R σ τ : Type*} [CommRing R] (f : σ → τ)
    (hf : Function.Injective f) (P Q : MvPolynomial σ R) (i : σ) :
    coordinateWronskian (rename f P) (rename f Q) (f i) =
      rename f (coordinateWronskian P Q i) := by
  simp only [coordinateWronskian, pderiv_rename hf, map_mul, map_sub]

/-- Injectively renaming both polynomials preserves universal nonnegativity of
their coordinate Wronskians, including coordinates outside the image. -/
theorem eval_coordinateWronskian_rename_nonneg
    {R σ τ : Type*} [CommRing R] [Preorder R]
    (f : σ → τ) (hf : Function.Injective f) (P Q : MvPolynomial σ R)
    (h : ∀ i x, 0 ≤ eval x (coordinateWronskian P Q i)) :
    ∀ j y, 0 ≤ eval y (coordinateWronskian (rename f P) (rename f Q) j) := by
  classical
  intro j y
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hj
    rw [coordinateWronskian_rename f hf, eval_rename]
    exact h i (y ∘ f)
  · have hjP : j ∉ (rename f P).vars := by
      intro hjVars
      obtain ⟨i, _, hi⟩ := mem_vars_rename f P hjVars
      exact hj ⟨i, hi⟩
    have hjQ : j ∉ (rename f Q).vars := by
      intro hjVars
      obtain ⟨i, _, hi⟩ := mem_vars_rename f Q hjVars
      exact hj ⟨i, hi⟩
    rw [coordinateWronskian_eq_zero_of_notMem_vars hjP hjQ, map_zero]

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

/-- Multiplying the left argument by a coordinate gives a coordinate-scaled
Wronskian minus the derivative of that coordinate. -/
theorem coordinateWronskian_X_mul_left
    {R σ : Type*} [CommRing R] [DecidableEq σ]
    (P Q : MvPolynomial σ R) (i k : σ) :
    coordinateWronskian (X k * P) Q i =
      X k * coordinateWronskian P Q i -
        if i = k then P * Q else 0 := by
  classical
  by_cases hik : i = k
  · subst k
    simp only [coordinateWronskian, pderiv_mul, pderiv_X_self,
      one_mul, if_pos]
    ring
  · simp only [coordinateWronskian, pderiv_mul,
      pderiv_X_of_ne (Ne.symm hik), zero_mul, zero_add, if_neg hik,
      sub_zero]
    ring

/-- Multiplying the right argument by a coordinate gives a coordinate-scaled
Wronskian plus the derivative of that coordinate. -/
theorem coordinateWronskian_X_mul_right
    {R σ : Type*} [CommRing R] [DecidableEq σ]
    (P Q : MvPolynomial σ R) (i k : σ) :
    coordinateWronskian P (X k * Q) i =
      X k * coordinateWronskian P Q i +
        if i = k then P * Q else 0 := by
  classical
  by_cases hik : i = k
  · subst k
    simp only [coordinateWronskian, pderiv_mul, pderiv_X_self,
      one_mul, if_pos]
    ring
  · simp only [coordinateWronskian, pderiv_mul,
      pderiv_X_of_ne (Ne.symm hik), zero_mul, zero_add, if_neg hik]
    ring

/-- Away from the adjoined coordinate, the coordinate Wronskian of two
affine extensions is a quadratic whose coefficients are the four endpoint
Wronskians. -/
theorem coordinateWronskian_add_X_mul_add_X_mul_of_ne
    {R σ : Type*} [CommRing R]
    (P Q A B : MvPolynomial σ R) (i k : σ) (hik : i ≠ k) :
    coordinateWronskian (P + X k * Q) (A + X k * B) i =
      coordinateWronskian P A i +
        X k * (coordinateWronskian P B i +
          coordinateWronskian Q A i) +
        X k ^ 2 * coordinateWronskian Q B i := by
  classical
  rw [coordinateWronskian_add_left, coordinateWronskian_add_right,
    coordinateWronskian_add_right, coordinateWronskian_X_mul_right,
    coordinateWronskian_X_mul_left, coordinateWronskian_X_mul_left,
    coordinateWronskian_X_mul_right]
  simp only [if_neg hik]
  ring

/-- The four coordinate Wronskians of four polynomials satisfy the
two-dimensional Plücker relation. -/
theorem coordinateWronskian_plucker
    {R σ : Type*} [CommRing R]
    (P Q A B : MvPolynomial σ R) (i : σ) :
    coordinateWronskian P A i * coordinateWronskian Q B i =
      coordinateWronskian P Q i * coordinateWronskian A B i +
        coordinateWronskian P B i * coordinateWronskian Q A i := by
  simp only [coordinateWronskian]
  ring

/-- The discriminant of the coordinate Wronskian of two affine extensions
has a difference-of-Wronskians form. -/
theorem coordinateWronskian_quadratic_discriminant
    {R σ : Type*} [CommRing R]
    (P Q A B : MvPolynomial σ R) (i : σ) :
    (coordinateWronskian P B i + coordinateWronskian Q A i) ^ 2 -
        4 * coordinateWronskian Q B i * coordinateWronskian P A i =
      (coordinateWronskian P B i - coordinateWronskian Q A i) ^ 2 -
        4 * coordinateWronskian P Q i * coordinateWronskian A B i := by
  calc
    _ = (coordinateWronskian P B i + coordinateWronskian Q A i) ^ 2 -
        4 * (coordinateWronskian P A i *
          coordinateWronskian Q B i) := by ring
    _ = (coordinateWronskian P B i + coordinateWronskian Q A i) ^ 2 -
        4 * (coordinateWronskian P Q i *
          coordinateWronskian A B i +
            coordinateWronskian P B i *
              coordinateWronskian Q A i) := by
      rw [coordinateWronskian_plucker P Q A B i]
    _ = _ := by ring

/-- Pointwise nonpositivity of the coordinate-Wronskian quadratic
discriminant is exactly its Plücker square-versus-product inequality. -/
theorem eval_coordinateWronskian_quadratic_discriminant_nonpos_iff
    (P Q A B : MvPolynomial σ Real) (i : σ) (x : σ → Real) :
    eval x
        ((coordinateWronskian P B i + coordinateWronskian Q A i) ^ 2 -
          4 * coordinateWronskian Q B i * coordinateWronskian P A i) ≤ 0 ↔
      eval x (coordinateWronskian P B i - coordinateWronskian Q A i) ^ 2 ≤
        4 * eval x (coordinateWronskian P Q i) *
          eval x (coordinateWronskian A B i) := by
  rw [coordinateWronskian_quadratic_discriminant]
  simp only [eval_sub, eval_pow, eval_mul, map_ofNat]
  constructor <;> intro h <;> linarith

/-- At the adjoined coordinate, a fresh right factor exposes the exact
coordinate-reduced remainder of the left argument. -/
theorem coordinateWronskian_X_mul_right_self
    {R σ : Type*} [CommRing R]
    (P : MvPolynomial σ R) {Q : MvPolynomial σ R}
    {k : σ} (hkQ : k ∉ Q.vars) :
    coordinateWronskian P (X k * Q) k =
      Q * (P - X k * pderiv k P) := by
  classical
  rw [coordinateWronskian_X_mul_right, if_pos rfl, coordinateWronskian,
    pderiv_eq_zero_of_notMem_vars hkQ]
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
