module

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
public import RealRooted.Bezoutian.StrictInterleaving
public import RealRooted.Mathlib.Algebra.Polynomial.Bezoutian
import RealRooted.Linear
import RealRooted.QuadraticRoot
public import RealRooted.Basic.Coefficients
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Elementary real Bezout matrices

Coefficient and matrix definitions, scalar transport, explicit linear and
quadratic formulas, and small positive-definiteness certificates.
-/

@[expose] public section

open Polynomial Matrix

noncomputable section

namespace RealRooted

/-- The `(i,j)` coefficient of the Bezoutian
`(p(X) q(Y) - p(Y) q(X)) / (X - Y)`.

This definition is independent of a matrix size. Coefficients outside the
degrees of `p` and `q` vanish through `Polynomial.coeff`. -/
abbrev bezoutEntry (p q : ℝ[X]) (i j : ℕ) : ℝ := Polynomial.bezoutEntry p q i j

/-- The `n × n` Bezout matrix attached to two polynomials. -/
abbrev bezoutMatrix (n : ℕ) (p q : ℝ[X]) : Matrix (Fin n) (Fin n) ℝ :=
  Polynomial.bezoutMatrix n p q

/-- The `i`-th row of the Bezout matrix of `p` and `q`, as a polynomial in `X`. -/
abbrev bezoutRowPoly (n : ℕ) (p q : ℝ[X]) (i : Fin n) : ℝ[X] :=
  Polynomial.bezoutRowPoly n p q i

lemma bezoutEntry.comm (p q : ℝ[X]) (i j : ℕ) :
    bezoutEntry p q i j = bezoutEntry p q j i :=
  Polynomial.bezoutEntry.comm p q i j

lemma bezoutEntry.cast_complex (p q : ℝ[X]) (i j : ℕ) :
    (bezoutEntry p q i j : ℂ) =
      bezoutSeqEntry (p.map Complex.ofRealHom).coeff
        (q.map Complex.ofRealHom).coeff i j := by
  simp [bezoutEntry, Polynomial.bezoutEntry, bezoutSeqEntry, coeff_map]

lemma bezoutMatrix.isHermitian (n : ℕ) (p q : ℝ[X]) :
    (bezoutMatrix n p q).IsHermitian := by
  ext i j
  exact Polynomial.bezoutEntry.comm p q j i

lemma Matrix.PosDef.sum_pos {m : ℕ} {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.PosDef)
    {x : Fin m → ℝ} (hx : x ≠ 0) :
    0 < ∑ i : Fin m, ∑ j : Fin m, B i j * x i * x j := by
  have h_dot := hB.dotProduct_mulVec_pos hx
  simp only [dotProduct, mulVec, star_trivial] at h_dot
  have h_sum : ∑ i : Fin m, x i * ∑ j : Fin m, B i j * x j =
      ∑ i : Fin m, ∑ j : Fin m, B i j * x i * x j := by
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  simp_all

lemma bezoutEntry.C_mul_C_mul (u v : ℝ) (p q : ℝ[X]) (i j : ℕ) :
    bezoutEntry (C u * p) (C v * q) i j = u * v * bezoutEntry p q i j := by
  simp only [bezoutEntry, Polynomial.bezoutEntry, bezoutSeqEntry, coeff_C_mul,
    Finset.mul_sum]
  grind

lemma bezoutMatrix.C_mul_C_mul (n : ℕ) (u v : ℝ) (p q : ℝ[X]) :
    bezoutMatrix n (C u * p) (C v * q) = (u * v) • bezoutMatrix n p q := by
  ext i j
  simpa [bezoutMatrix, Polynomial.bezoutMatrix] using
    bezoutEntry.C_mul_C_mul u v p q i j

/-- Every polynomial of the form `X + C a` is real-rooted. -/
lemma Polynomial.isRealRooted_X_add_C (a : ℝ) :
    (X + C a : ℝ[X]) ≠ 0 ∧ (X + C a).Splits := by
  simpa [sub_eq_add_neg] using isRealRooted_X_sub_C (-a)

lemma StrictInterlSameDegree.X_add_C_iff {a b : ℝ} :
    StrictInterlSameDegree (X + C b) (X + C a) ↔ a < b := by
  simp [StrictInterlSameDegree, Polynomial.isRealRooted_X_add_C,
    List.interleaves_singleton_singleton]

lemma Polynomial.isRealRooted_of_natDegree_two_of_discrim_nonneg {p : ℝ[X]}
    (hdeg : p.natDegree = 2)
    (hdisc : 0 ≤ discrim (p.coeff 2) (p.coeff 1) (p.coeff 0)) :
    p ≠ 0 ∧ p.Splits :=
  ⟨ne_zero_of_natDegree_gt (n := 0) (by lia),
    splits_of_natDegree_eq_two_of_discrim_nonneg hdeg hdisc⟩

lemma bezoutMatrix.fin_two_eq_coeff_of_natDegree_le_two {p q : ℝ[X]}
    (hp_deg : p.natDegree ≤ 2) (hq_deg : q.natDegree ≤ 2) :
    bezoutMatrix 2 q p =
    !![q.coeff 1 * p.coeff 0 - p.coeff 1 * q.coeff 0,
      q.coeff 2 * p.coeff 0 - p.coeff 2 * q.coeff 0;
      q.coeff 2 * p.coeff 0 - p.coeff 2 * q.coeff 0,
      q.coeff 2 * p.coeff 1 - p.coeff 2 * q.coeff 1] := by
  have hp3 : p.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hp_deg)
  have hq3 : q.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hq_deg)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bezoutMatrix, Polynomial.bezoutMatrix, Polynomial.bezoutEntry,
      bezoutSeqEntry, hp3, hq3, Finset.sum_range_succ]

lemma _root_.Matrix.posDef_fin_two_of_entries {a b c : ℝ}
    (ha : 0 < a) (hdet : 0 < a * c - b * b) :
    (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  refine .of_dotProduct_mulVec_pos (.ext (by simp)) fun x hx ↦ ?_
  have h : x 0 = 0 → x 1 ≠ 0 := by simpa [funext_iff, Fin.forall_fin_two] using hx
  simp only [star_trivial, cons_mulVec, cons_dotProduct, dotProduct_of_isEmpty,
    add_zero, empty_mulVec, dotProduct_cons, gt_iff_lt]
  change 0 < x 0 * (a * x 0 + b * x 1) + x 1 * (b * x 0 + c * x 1)
  rcases eq_or_ne (x 1) 0 with h1 | h1
  · rw [h1]
    nlinarith [mul_self_pos.mpr (fun h0 ↦ h h0 h1 : x 0 ≠ 0)]
  · nlinarith [sq_nonneg (a * x 0 + b * x 1), mul_pos hdet (mul_self_pos.mpr h1)]

/-- An explicit `LDLᵀ` certificate for positive definiteness of a symmetric
`3 × 3` real matrix. -/
lemma _root_.Matrix.posDef_fin_three_of_ldl {d₀ d₁ d₂ l₁₀ l₂₀ l₂₁ : ℝ}
    (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    (!![d₀, d₀ * l₁₀, d₀ * l₂₀;
        d₀ * l₁₀, d₀ * l₁₀ ^ 2 + d₁,
          d₀ * l₁₀ * l₂₀ + d₁ * l₂₁;
        d₀ * l₂₀, d₀ * l₁₀ * l₂₀ + d₁ * l₂₁,
          d₀ * l₂₀ ^ 2 + d₁ * l₂₁ ^ 2 + d₂] :
      Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · exact Matrix.IsHermitian.ext (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp)
  · intro x hx
    have hform :
        dotProduct (star x) (Matrix.mulVec
          ((!![d₀, d₀ * l₁₀, d₀ * l₂₀;
            d₀ * l₁₀, d₀ * l₁₀ ^ 2 + d₁,
              d₀ * l₁₀ * l₂₀ + d₁ * l₂₁;
            d₀ * l₂₀, d₀ * l₁₀ * l₂₀ + d₁ * l₂₁,
              d₀ * l₂₀ ^ 2 + d₁ * l₂₁ ^ 2 + d₂] :
            Matrix (Fin 3) (Fin 3) ℝ)) x) =
          d₀ * (x 0 + l₁₀ * x 1 + l₂₀ * x 2) ^ 2 +
          d₁ * (x 1 + l₂₁ * x 2) ^ 2 + d₂ * (x 2) ^ 2 := by
      rw [Matrix.vec3_dotProduct]
      simp only [Matrix.mulVec, Matrix.vec3_dotProduct]
      simp
      ring
    rw [hform]
    by_cases hx₂ : x 2 = 0
    · by_cases hx₁ : x 1 = 0
      · have hx₀ : x 0 ≠ 0 := by
          intro hx₀
          apply hx
          funext i
          fin_cases i <;> assumption
        simp [hx₂, hx₁, mul_pos hd₀ (sq_pos_of_ne_zero hx₀)]
      · have h₁ : 0 < d₁ * (x 1 + l₂₁ * x 2) ^ 2 := by
          simp [hx₂, mul_pos hd₁ (sq_pos_of_ne_zero hx₁)]
        positivity
    · have h₂ : 0 < d₂ * (x 2) ^ 2 :=
        mul_pos hd₂ (sq_pos_of_ne_zero hx₂)
      positivity

lemma bezoutEntry.eq_zero_of_le_left (p q : ℝ[X]) {n : ℕ} {i j : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) (hi : n ≤ i) :
    bezoutEntry p q i j = 0 :=
  Polynomial.bezoutEntry.eq_zero_of_le_left p q hp hq hi

lemma bezoutEntry.eq_zero_of_le_right (p q : ℝ[X]) {n : ℕ} {i j : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) (hj : n ≤ j) :
    bezoutEntry p q i j = 0 :=
  Polynomial.bezoutEntry.eq_zero_of_le_right p q hp hq hj

lemma bezoutEntry.telescoping (p q : ℝ[X]) (i j : ℕ) :
    bezoutEntry p q i (j + 1) - bezoutEntry p q (i + 1) j =
    p.coeff (i + 1) * q.coeff (j + 1) - p.coeff (j + 1) * q.coeff (i + 1) :=
  Polynomial.bezoutEntry.telescoping p q i j

lemma bezoutEntry.coeff_mul_sub_coeff_mul (p q : ℝ[X]) (i j : ℕ) :
    p.coeff i * q.coeff j - p.coeff j * q.coeff i =
      (if i ≠ 0 then bezoutEntry p q (i - 1) j else 0) -
        (if j ≠ 0 then bezoutEntry p q i (j - 1) else 0) :=
  Polynomial.bezoutEntry.coeff_mul_sub_coeff_mul p q i j

lemma bezoutEntry.bilinear_mul_sub (p q : ℝ[X]) {n : ℕ} (t₁ t₂ : ℝ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (t₁ - t₂) * ∑ i : Fin n, ∑ j : Fin n,
    bezoutEntry p q i.val j.val * t₁ ^ i.val * t₂ ^ j.val =
    p.eval t₁ * q.eval t₂ - p.eval t₂ * q.eval t₁ :=
  Polynomial.bezoutEntry.bilinear_mul_sub p q t₁ t₂ hp hq

end RealRooted
