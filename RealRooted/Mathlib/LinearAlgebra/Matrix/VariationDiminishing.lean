module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.SignVariation
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Variation diminution for totally nonnegative matrices

This module develops the forward variation-diminishing theorem for a finite
rectangular totally nonnegative matrix.  The intended proof follows Karlin,
*Total Positivity*, Vol. I, Chapter 5, Section 1, Theorems 1.1--1.4, followed
by Section 3, Theorem 3.1.  In particular, this is not the dual-kernel theorem
from Chapter 5, Section 2.

The source-faithful finite proof is decomposed as follows.

1. The zero vector is split off.  Karlin assigns it `S^- = -1`, whereas
   `Fin.signVariations` assigns it `0`.  The resulting inequality is checked
   directly below.
2. For a nonzero input, its ordered nonzero support is partitioned into its
   maximal consecutive same-sign blocks.  If there are `q` blocks, then
   `q - 1 = Fin.signVariations x`.
3. Each block is aggregated into one column, with weights `|x j|`.  The
   aggregated matrix is totally nonnegative: multilinearity of the determinant
   expands each minor as a sum of minors of the original matrix.  Monotonicity
   of the block map makes every selected tuple of original columns strictly
   increasing, so every summand has the same nonnegative sign.
4. The input coefficients of the aggregated matrix alternate strictly.  The
   sign-consistency and alternating-coefficient argument of Section 1 bounds
   the output variation by `q - 1` in the strict case.
5. Section 3, Theorem 3.1 supplies the non-strict limit step.  One approximates
   the TN kernel by strict kernels and uses the lower-semicontinuity inequality
   for `S^-` at the limiting output.  No rank hypothesis is introduced.

The first missing formal lemma is Step 3.  Its intended Lean statement is:

```lean
lemma Matrix.IsTotallyNonnegRect.aggregate_monotone
    {m n q : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}
    (hM : M.IsTotallyNonnegRect) (block : Fin n → Fin q)
    (hblock : Monotone block) (weight : Fin n → ℝ)
    (hweight : ∀ j, 0 ≤ weight j) :
    ((fun i s ↦ ∑ j with block j = s, M i j * weight j) :
      Matrix (Fin m) (Fin q) ℝ).IsTotallyNonnegRect
```

This is the consecutive-block determinant expansion used in Chapter 5,
Section 1.  It requires a finite Cauchy--Binet/multilinearity development not
yet present in the local rectangular-TN API.  Until that lemma and the strict
sector and limit lemmas in Steps 4--5 are proved, this file deliberately does
not declare the full theorem with an unproved backend.
-/

public section

open scoped BigOperators

namespace Fin

/-- The local `S^-` convention gives the zero vector zero sign variations. -/
@[simp]
lemma signVariations_zero (n : ℕ) :
    signVariations (0 : Fin n → ℝ) = 0 := by
  exact signVariations_eq_zero_of_forall_nonneg 0 (fun _ ↦ le_rfl)

end Fin

namespace Matrix

/-- A totally nonnegative rectangular matrix sends a nonnegative vector to a
nonnegative vector.  This is the positive one-block sector of the forward
variation-diminishing argument. -/
lemma IsTotallyNonnegRect.mulVec_nonneg {m n : ℕ}
    {M : Matrix (Fin m) (Fin n) ℝ} (hM : M.IsTotallyNonnegRect)
    {x : Fin n → ℝ} (hx : ∀ j, 0 ≤ x j) (i : Fin m) :
    0 ≤ M.mulVec x i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg (fun j _ ↦ mul_nonneg (hM.nonneg i j) (hx j))

/-- A totally nonnegative rectangular matrix sends a nonpositive vector to a
nonpositive vector.  This is the negative one-block sector of the forward
variation-diminishing argument. -/
lemma IsTotallyNonnegRect.mulVec_nonpos {m n : ℕ}
    {M : Matrix (Fin m) (Fin n) ℝ} (hM : M.IsTotallyNonnegRect)
    {x : Fin n → ℝ} (hx : ∀ j, x j ≤ 0) (i : Fin m) :
    M.mulVec x i ≤ 0 := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonpos
    (fun j _ ↦ mul_nonpos_of_nonneg_of_nonpos (hM.nonneg i j) (hx j))

/-- The forward variation-diminishing inequality on the nonnegative
one-block sector. -/
theorem IsTotallyNonnegRect.signVariations_mulVec_le_of_nonneg
    {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}
    (hM : M.IsTotallyNonnegRect) (x : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j) :
    Fin.signVariations (M.mulVec x) ≤ Fin.signVariations x := by
  have hy : ∀ i, 0 ≤ M.mulVec x i := hM.mulVec_nonneg hx
  calc
    Fin.signVariations (M.mulVec x) = 0 :=
      Fin.signVariations_eq_zero_of_forall_nonneg _ hy
    _ ≤ Fin.signVariations x := Nat.zero_le _

/-- The forward variation-diminishing inequality on the nonpositive
one-block sector. -/
theorem IsTotallyNonnegRect.signVariations_mulVec_le_of_nonpos
    {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}
    (hM : M.IsTotallyNonnegRect) (x : Fin n → ℝ)
    (hx : ∀ j, x j ≤ 0) :
    Fin.signVariations (M.mulVec x) ≤ Fin.signVariations x := by
  have hy : ∀ i, M.mulVec x i ≤ 0 := hM.mulVec_nonpos hx
  calc
    Fin.signVariations (M.mulVec x) = 0 :=
      Fin.signVariations_eq_zero_of_forall_nonpos _ hy
    _ ≤ Fin.signVariations x := Nat.zero_le _

/-- The zero-vector case, stated separately because the local convention is
`S^-(0) = 0`, rather than Karlin's `S^-(0) = -1`. -/
theorem IsTotallyNonnegRect.signVariations_mulVec_le_of_eq_zero
    {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}
    (hM : M.IsTotallyNonnegRect) (x : Fin n → ℝ) (hx : x = 0) :
    Fin.signVariations (M.mulVec x) ≤ Fin.signVariations x := by
  subst x
  exact hM.signVariations_mulVec_le_of_nonneg 0 (fun _ ↦ le_rfl)

/-- The full forward inequality for a matrix with one input column.  This is
the one-block base case of the consecutive-block decomposition. -/
theorem IsTotallyNonnegRect.signVariations_mulVec_le_fin_one
    {m : ℕ} {M : Matrix (Fin m) (Fin 1) ℝ}
    (hM : M.IsTotallyNonnegRect) (x : Fin 1 → ℝ) :
    Fin.signVariations (M.mulVec x) ≤ Fin.signVariations x := by
  rcases le_total 0 (x 0) with hx | hx
  · apply hM.signVariations_mulVec_le_of_nonneg
    intro j
    simpa [Subsingleton.elim j 0] using hx
  · apply hM.signVariations_mulVec_le_of_nonpos
    intro j
    simpa [Subsingleton.elim j 0] using hx

end Matrix
