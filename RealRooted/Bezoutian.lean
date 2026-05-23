import RealRooted.Basic
import RealRooted.Linear
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Bezout matrices and interlacing

This file records the planned Bezout-matrix characterization of the relation
`Prec P Q`.  The main theorem is left as a `sorry` on purpose: it is a
breadcrumb for a future formalization pass.

For polynomials

`p(X) = \sum_i a_i X^i`, `q(X) = \sum_i b_i X^i`,

the Bezoutian is

`(p(X) q(Y) - p(Y) q(X)) / (X - Y)`.

The coefficient of `X^i Y^j` is

`∑ k ≤ min i j, a_{i+j+1-k} b_k - b_{i+j+1-k} a_k`.

The matrix below uses this coefficient formula directly.  With the current
`Prec P Q` convention, the expected positive-semidefinite orientation is
`bezoutMatrix n Q P`, not `bezoutMatrix n P Q`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The `(i,j)` coefficient of the Bezoutian
`(p(X) q(Y) - p(Y) q(X)) / (X - Y)`.

This definition is independent of a matrix size.  Coefficients outside the
degrees of `p` and `q` vanish through `Polynomial.coeff`. -/
def bezoutEntry (p q : ℝ[X]) (i j : ℕ) : ℝ :=
  Finset.sum (Finset.range (min i j + 1)) fun k =>
    p.coeff (i + j + 1 - k) * q.coeff k -
      q.coeff (i + j + 1 - k) * p.coeff k

/-- The `n × n` Bezout matrix attached to two polynomials. -/
def bezoutMatrix (n : ℕ) (p q : ℝ[X]) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => bezoutEntry p q i.1 j.1

lemma bezoutEntry_self (p : ℝ[X]) (i j : ℕ) :
    bezoutEntry p p i j = 0 := by
  simp [bezoutEntry]

lemma bezoutEntry_swap (p q : ℝ[X]) (i j : ℕ) :
    bezoutEntry q p i j = -bezoutEntry p q i j := by
  simp [bezoutEntry]

lemma bezoutEntry_zero_left (p : ℝ[X]) (i j : ℕ) :
    bezoutEntry 0 p i j = 0 := by
  simp [bezoutEntry]

lemma bezoutMatrix_self (n : ℕ) (p : ℝ[X]) :
    bezoutMatrix n p p = 0 := by
  ext i j
  simp [bezoutMatrix, bezoutEntry_self]

lemma bezoutMatrix_swap (n : ℕ) (p q : ℝ[X]) :
    bezoutMatrix n q p = -bezoutMatrix n p q := by
  ext i j
  change bezoutEntry q p i.1 j.1 = -bezoutEntry p q i.1 j.1
  exact bezoutEntry_swap p q i.1 j.1

lemma bezoutMatrix_linear_eq_diagonal (a b : ℝ) :
    bezoutMatrix 1 (X + C a) (X + C b) =
      Matrix.diagonal (fun _ : Fin 1 => b - a) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [bezoutMatrix, bezoutEntry, Matrix.diagonal]

lemma bezoutMatrix_linear_posSemidef_one {a b : ℝ} (hab : a ≤ b) :
    (bezoutMatrix 1 (X + C a) (X + C b)).PosSemidef := by
  rw [bezoutMatrix_linear_eq_diagonal]
  exact Matrix.PosSemidef.diagonal (fun _ => sub_nonneg.mpr hab)

lemma not_bezoutMatrix_linear_posSemidef_one_swap {a b : ℝ} (hab : a < b) :
    ¬ (bezoutMatrix 1 (X + C b) (X + C a)).PosSemidef := by
  intro h
  have hdiag :
      0 ≤ (bezoutMatrix 1 (X + C b) (X + C a)) (0 : Fin 1) (0 : Fin 1) :=
    Matrix.PosSemidef.diag_nonneg h
  simp [bezoutMatrix, bezoutEntry] at hdiag
  linarith

/-- Every polynomial of the form `X + C a` is real-rooted. -/
lemma isRealRooted_X_add_C (a : ℝ) : IsRealRooted (X + C a) := by
  simpa [sub_eq_add_neg] using isRealRooted_X_sub_C (-a)

/-- The unique root of `X + C a` is `-a`. -/
lemma roots_X_add_C (a : ℝ) :
    (X + C a : ℝ[X]).roots = {(-a : ℝ)} := by
  rw [show X + C a = X - C (-a) by simp [sub_eq_add_neg], roots_X_sub_C]

/-- Ordered linear factors satisfy the `Prec` orientation predicted by the
positive-semidefinite Bezout matrix orientation. -/
lemma prec_X_add_C_of_le {a b : ℝ} (hab : a ≤ b) :
    Prec (X + C b) (X + C a) := by
  refine ⟨?_, ?_, [(-b : ℝ)], [(-a : ℝ)], ?_, ?_, ?_, ?_, ?_⟩
  · exact isRealRooted_X_add_C b
  · exact isRealRooted_X_add_C a
  · simp
  · simp
  · rw [roots_X_add_C]
    simp
  · rw [roots_X_add_C]
    simp
  · exact Or.inr ⟨by simp, by simp [ListAlternates, ListInterlaces, hab]⟩

/-- The `1 × 1` Bezoutian positive-semidefinite sanity check implies the
corresponding linear `Prec` orientation. -/
lemma prec_of_bezoutMatrix_linear_posSemidef_one {a b : ℝ}
    (h : (bezoutMatrix 1 (X + C a) (X + C b)).PosSemidef) :
    Prec (X + C b) (X + C a) := by
  have hdiag :
      0 ≤ (bezoutMatrix 1 (X + C a) (X + C b)) (0 : Fin 1) (0 : Fin 1) := by
    exact Matrix.PosSemidef.diag_nonneg h
  rw [bezoutMatrix_linear_eq_diagonal] at hdiag
  have hab : a ≤ b := by
    simpa [Matrix.diagonal] using hdiag
  exact prec_X_add_C_of_le hab

lemma bezoutMatrix_quadratic_commonFactor_eq_vecMulVec (a b c : ℝ) :
    bezoutMatrix 2 ((X + C a) * (X + C c)) ((X + C b) * (X + C c)) =
      (b - a) • Matrix.vecMulVec (fun i : Fin 2 => if i = 0 then c else 1)
        (star (fun i : Fin 2 => if i = 0 then c else 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bezoutMatrix, bezoutEntry, Matrix.vecMulVec, coeff_add, coeff_mul,
      Finset.antidiagonal, Finset.range, coeff_X, coeff_C]
  all_goals ring

lemma bezoutMatrix_quadratic_commonFactor_posSemidef_two {a b c : ℝ}
    (hab : a ≤ b) :
    (bezoutMatrix 2 ((X + C a) * (X + C c))
      ((X + C b) * (X + C c))).PosSemidef := by
  rw [bezoutMatrix_quadratic_commonFactor_eq_vecMulVec]
  exact (Matrix.posSemidef_vecMulVec_self_star
    (fun i : Fin 2 => if i = 0 then c else 1)).smul (sub_nonneg.mpr hab)

lemma not_bezoutMatrix_quadratic_commonFactor_posSemidef_two_swap {a b c : ℝ}
    (hab : a < b) :
    ¬ (bezoutMatrix 2 ((X + C b) * (X + C c))
      ((X + C a) * (X + C c))).PosSemidef := by
  intro h
  have hdiag :
      0 ≤ (bezoutMatrix 2 ((X + C b) * (X + C c))
        ((X + C a) * (X + C c))) (1 : Fin 2) (1 : Fin 2) :=
    Matrix.PosSemidef.diag_nonneg h
  rw [bezoutMatrix_quadratic_commonFactor_eq_vecMulVec] at hdiag
  simp [Matrix.vecMulVec] at hdiag
  linarith

/-- Multiplying the ordered linear `Prec` example by a common linear factor
preserves the expected Bezoutian orientation in degree two. -/
lemma prec_quadratic_commonFactor_of_le {a b c : ℝ} (hab : a ≤ b) :
    Prec (((X + C b) * (X + C c)) : ℝ[X])
      (((X + C a) * (X + C c)) : ℝ[X]) := by
  have hb : IsRealRooted (X + C b) := isRealRooted_X_add_C b
  have hc : IsRealRooted (X + C c) := isRealRooted_X_add_C c
  have ha : IsRealRooted (X + C a) := isRealRooted_X_add_C a
  by_cases hca : c ≤ a
  · refine ⟨isRealRooted_mul hb hc, isRealRooted_mul ha hc,
      [(-b : ℝ), -c], [(-a : ℝ), -c], ?_, ?_, ?_, ?_, ?_⟩
    · simp
      linarith
    · simp
      linarith
    · rw [roots_mul (mul_ne_zero hb.1 hc.1), roots_X_add_C, roots_X_add_C]
      rfl
    · rw [roots_mul (mul_ne_zero ha.1 hc.1), roots_X_add_C, roots_X_add_C]
      rfl
    · exact Or.inr ⟨by simp, by
        simp [ListAlternates, ListInterlaces]
        constructor <;> linarith⟩
  · by_cases hcb : c ≤ b
    · have hac : a ≤ c := le_of_not_ge hca
      refine ⟨isRealRooted_mul hb hc, isRealRooted_mul ha hc,
        [(-b : ℝ), -c], [(-c : ℝ), -a], ?_, ?_, ?_, ?_, ?_⟩
      · simp
        linarith
      · simp
        linarith
      · rw [roots_mul (mul_ne_zero hb.1 hc.1), roots_X_add_C, roots_X_add_C]
        rfl
      · rw [roots_mul (mul_ne_zero ha.1 hc.1), roots_X_add_C, roots_X_add_C,
          Multiset.add_comm]
        rfl
      · exact Or.inr ⟨by simp, by
          simp [ListAlternates, ListInterlaces]
          constructor <;> linarith⟩
    · have hbc : b ≤ c := le_of_not_ge hcb
      refine ⟨isRealRooted_mul hb hc, isRealRooted_mul ha hc,
        [(-c : ℝ), -b], [(-c : ℝ), -a], ?_, ?_, ?_, ?_, ?_⟩
      · simp
        linarith
      · simp
        linarith
      · rw [roots_mul (mul_ne_zero hb.1 hc.1), roots_X_add_C, roots_X_add_C,
          Multiset.add_comm]
        rfl
      · rw [roots_mul (mul_ne_zero ha.1 hc.1), roots_X_add_C, roots_X_add_C,
          Multiset.add_comm]
        rfl
      · exact Or.inr ⟨by simp, by
          simp [ListAlternates, ListInterlaces]
          constructor <;> linarith⟩

/-- The common-factor `2 × 2` Bezoutian positive-semidefinite sanity check
implies the corresponding quadratic `Prec` orientation. -/
lemma prec_of_bezoutMatrix_quadratic_commonFactor_posSemidef_two {a b c : ℝ}
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
      ((X + C b) * (X + C c))).PosSemidef) :
    Prec (((X + C b) * (X + C c)) : ℝ[X])
      (((X + C a) * (X + C c)) : ℝ[X]) := by
  have hdiag :
      0 ≤ (bezoutMatrix 2 ((X + C a) * (X + C c))
        ((X + C b) * (X + C c))) (1 : Fin 2) (1 : Fin 2) := by
    exact Matrix.PosSemidef.diag_nonneg h
  rw [bezoutMatrix_quadratic_commonFactor_eq_vecMulVec] at hdiag
  have hab : a ≤ b := by
    simp [Matrix.vecMulVec] at hdiag
    linarith
  exact prec_quadratic_commonFactor_of_le hab

lemma bezoutMatrix_quadratic_nonCommon_eq_decomp :
    bezoutMatrix 2 ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))
        ((X + C (2 : ℝ)) * (X + C (4 : ℝ))) =
      ((1 / 2 : ℝ) • Matrix.vecMulVec (fun i : Fin 2 => if i = 0 then (5 : ℝ) else 2)
        (star (fun i : Fin 2 => if i = 0 then (5 : ℝ) else 2))) +
        Matrix.diagonal (fun i : Fin 2 => if i = 0 then (3 / 2 : ℝ) else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bezoutMatrix, bezoutEntry, Matrix.vecMulVec, Matrix.diagonal, coeff_add,
      coeff_mul, Finset.antidiagonal, Finset.range, coeff_X, coeff_C, coeff_one]

lemma bezoutMatrix_quadratic_nonCommon_posSemidef_two :
    (bezoutMatrix 2 ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))
      ((X + C (2 : ℝ)) * (X + C (4 : ℝ)))).PosSemidef := by
  rw [bezoutMatrix_quadratic_nonCommon_eq_decomp]
  apply Matrix.PosSemidef.add
  · exact (Matrix.posSemidef_vecMulVec_self_star
      (fun i : Fin 2 => if i = 0 then (5 : ℝ) else 2)).smul (by norm_num)
  · exact Matrix.PosSemidef.diagonal (by intro i; fin_cases i <;> norm_num)

lemma not_bezoutMatrix_quadratic_nonCommon_posSemidef_two_swap :
    ¬ (bezoutMatrix 2 ((X + C (2 : ℝ)) * (X + C (4 : ℝ)))
      ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))).PosSemidef := by
  intro h
  have hdiag :
      0 ≤ (bezoutMatrix 2 ((X + C (2 : ℝ)) * (X + C (4 : ℝ)))
        ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))) (1 : Fin 2) (1 : Fin 2) :=
    Matrix.PosSemidef.diag_nonneg h
  norm_num [bezoutMatrix, bezoutEntry, coeff_add, coeff_mul, Finset.antidiagonal,
    Finset.range, coeff_X, coeff_C, coeff_one] at hdiag

/-- If four linear-factor constants interleave as `a ≤ b ≤ c ≤ d`, then the
corresponding quadratic factors satisfy the expected `Prec` orientation. -/
lemma prec_quadratic_of_const_interleaves {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    Prec (((X + C b) * (X + C d)) : ℝ[X])
      (((X + C a) * (X + C c)) : ℝ[X]) := by
  have ha : IsRealRooted (X + C a) := isRealRooted_X_add_C a
  have hb : IsRealRooted (X + C b) := isRealRooted_X_add_C b
  have hc : IsRealRooted (X + C c) := isRealRooted_X_add_C c
  have hd : IsRealRooted (X + C d) := isRealRooted_X_add_C d
  refine ⟨isRealRooted_mul hb hd, isRealRooted_mul ha hc,
    [(-d : ℝ), -b], [(-c : ℝ), -a], ?_, ?_, ?_, ?_, ?_⟩
  · simp
    linarith
  · simp
    linarith
  · rw [roots_mul (mul_ne_zero hb.1 hd.1), roots_X_add_C, roots_X_add_C,
      Multiset.add_comm]
    rfl
  · rw [roots_mul (mul_ne_zero ha.1 hc.1), roots_X_add_C, roots_X_add_C,
      Multiset.add_comm]
    rfl
  · exact Or.inr ⟨by simp, by
      simp [ListAlternates, ListInterlaces]
      constructor
      · linarith
      · constructor <;> linarith⟩

/-- The `Prec` side of the concrete non-common-factor quadratic Bezoutian
orientation example. -/
lemma prec_quadratic_nonCommon_example :
    Prec (((X + C (2 : ℝ)) * (X + C (4 : ℝ))) : ℝ[X])
      (((X + C (1 : ℝ)) * (X + C (3 : ℝ))) : ℝ[X]) := by
  exact prec_quadratic_of_const_interleaves (by norm_num) (by norm_num) (by norm_num)

/--
Planned Bezoutian characterization of weak interlacing/proper position.

The matrix-size parameter `n` should be at least the degrees of both
polynomials.  The orientation is chosen so that, for example,
`Prec (X + 2) (X + 1)` corresponds to the positive semidefinite matrix
`bezoutMatrix n (X + 1) (X + 2)`.

This theorem is intentionally left as a future formalization target.
-/
theorem prec_iff_bezoutMatrix_posSemidef
    {p q : ℝ[X]} {n : ℕ}
    (_hp_pos : HasPosLeadingCoeff p)
    (_hq_pos : HasPosLeadingCoeff q)
    (_hp_deg : p.natDegree ≤ n)
    (_hq_deg : q.natDegree ≤ n) :
    Prec p q ↔ (bezoutMatrix n q p).PosSemidef := by
  sorry

end RealRooted
