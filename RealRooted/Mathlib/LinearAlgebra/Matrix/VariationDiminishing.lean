module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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

/-- A common nonzero sign for all maximal minors makes multiplication by the
rectangular matrix injective. This is the rank step in Karlin, Chapter 5,
Section 1, Theorem 1.1. -/
lemma mulVec_ne_zero_of_strictMaximalMinors
    {m q : ℕ} {A : Matrix (Fin m) (Fin q) ℝ}
    (hqm : q ≤ m)
    (hminor :
      ∀ ⦃rows rows' : Fin q → Fin m⦄,
        StrictMono rows → StrictMono rows' →
          0 < (A.submatrix rows id).det *
            (A.submatrix rows' id).det)
    {x : Fin q → ℝ} (hx : x ≠ 0) :
    A.mulVec x ≠ 0 := by
  let rows : Fin q → Fin m := Fin.castLE hqm
  let B : Matrix (Fin q) (Fin q) ℝ := A.submatrix rows id
  have hrows : StrictMono rows := Fin.strictMono_castLE hqm
  have hdetprod : 0 < B.det * B.det := by
    simpa [B] using hminor hrows hrows
  have hdet : B.det ≠ 0 := by
    intro h
    rw [h, zero_mul] at hdetprod
    exact (lt_irrefl 0) hdetprod
  have hunit : IsUnit B :=
    B.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet)
  have hinj : Function.Injective B.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  intro hAx
  apply hx
  apply hinj
  ext i
  have hi := congrFun hAx (rows i)
  simpa [B, rows, Matrix.mulVec, dotProduct] using hi

private theorem not_exists_strictlyAlternating_rows_of_strictMaximalMinors
    {m q : ℕ} {A : Matrix (Fin m) (Fin q) ℝ} (hq : 0 < q)
    (hminor :
      ∀ ⦃rows rows' : Fin q → Fin m⦄,
        StrictMono rows → StrictMono rows' →
          0 < (A.submatrix rows id).det *
            (A.submatrix rows' id).det)
    (x : Fin q → ℝ) :
    ¬ ∃ rows : Fin (q + 1) → Fin m,
      StrictMono rows ∧
        Fin.StrictlyAlternates (fun i => A.mulVec x (rows i)) := by
  rintro ⟨rows, hrows, hz⟩
  let B : Matrix (Fin (q + 1)) (Fin q) ℝ := A.submatrix rows id
  let z : Fin (q + 1) → ℝ := fun i => A.mulVec x (rows i)
  change Fin.StrictlyAlternates z at hz
  rw [Fin.StrictlyAlternates] at hz
  let c : Fin (q + 1) → ℝ := fun i =>
    (-1 : ℝ) ^ (i : ℕ) * (B.submatrix i.succAbove id).det
  have hBmul : B.mulVec x = z := by
    ext i
    simp [B, z, Matrix.mulVec, dotProduct]
  have hdet (i j : Fin (q + 1)) :
      0 < (B.submatrix i.succAbove id).det *
        (B.submatrix j.succAbove id).det := by
    simpa [B, Function.comp_def] using
      hminor (hrows.comp (Fin.strictMono_succAbove i))
        (hrows.comp (Fin.strictMono_succAbove j))
  have hc : Fin.StrictlyAlternates c := by
    change ∀ i : Fin q, c i.castSucc * c i.succ < 0
    intro i
    have hd := hdet i.castSucc i.succ
    have hp : ((-1 : ℝ) ^ (i : ℕ)) ^ 2 = 1 := by
      rw [← pow_mul]
      simp
    calc
      c i.castSucc * c i.succ =
          -(((B.submatrix i.castSucc.succAbove id).det *
            (B.submatrix i.succ.succAbove id).det) *
              ((-1 : ℝ) ^ (i : ℕ)) ^ 2) := by
        simp only [c, Fin.val_castSucc, Fin.val_succ, pow_succ]
        ring
      _ = -((B.submatrix i.castSucc.succAbove id).det *
            (B.submatrix i.succ.succAbove id).det) := by rw [hp, mul_one]
      _ < 0 := neg_lt_zero.mpr hd
  have hc0 : c 0 ≠ 0 := by
    have hd := hdet 0 0
    intro hc0
    have hc0' : (B.submatrix (0 : Fin (q + 1)).succAbove id).det = 0 := by
      simpa [c] using hc0
    rw [hc0', zero_mul] at hd
    exact (lt_irrefl 0) hd
  let i0 : Fin q := ⟨0, hq⟩
  have hz0 : z 0 ≠ 0 := by
    intro hz0
    have hzpair := hz i0
    have hi0 : i0.castSucc = (0 : Fin (q + 1)) := by
      ext
      rfl
    rw [hi0, hz0, zero_mul] at hzpair
    exact (lt_irrefl 0) hzpair
  have hkernel : B.transpose.mulVec c = 0 :=
    transpose_mulVec_alternating_det_submatrix_succAbove B
  have hdot : c ⬝ᵥ z = 0 := by
    rw [← hBmul, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose B c, hkernel]
    simp
  rcases hc.pointwise_mul_pos_or_neg hz hc0 hz0 with hpos | hneg
  · have hsum : 0 < c ⬝ᵥ z := by
      rw [dotProduct]
      exact Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
    linarith
  · have hsum : c ⬝ᵥ z < 0 := by
      rw [dotProduct]
      have hpos : 0 < ∑ i, -(c i * z i) :=
        Finset.sum_pos (fun i _ => neg_pos.mpr (hneg i))
          Finset.univ_nonempty
      rw [Finset.sum_neg_distrib] at hpos
      linarith
    linarith

/-- Karlin's strict maximal-minor variation bound, in the local `S^-`
convention. Karlin proves the stronger `S^+` bound in Chapter 5, Section 1,
Theorem 1.1. -/
theorem signVariations_mulVec_le_card_sub_one_of_strictMaximalMinors
    {m q : ℕ} {A : Matrix (Fin m) (Fin q) ℝ}
    (hqm : q ≤ m)
    (hminor :
      ∀ ⦃rows rows' : Fin q → Fin m⦄,
        StrictMono rows → StrictMono rows' →
          0 < (A.submatrix rows id).det *
            (A.submatrix rows' id).det)
    (x : Fin q → ℝ) :
    Fin.signVariations (A.mulVec x) ≤ q - 1 := by
  by_cases hq0 : q = 0
  · subst q
    have hzero : A.mulVec x = 0 := by
      ext i
      simp [Matrix.mulVec, dotProduct]
    simp [hzero]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    by_contra hle
    have hlarge : q ≤ Fin.signVariations (A.mulVec x) := by omega
    exact not_exists_strictlyAlternating_rows_of_strictMaximalMinors
      hq hminor x
        (Fin.exists_strictMono_strictlyAlternates_of_le_signVariations
          hq hlarge)

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
