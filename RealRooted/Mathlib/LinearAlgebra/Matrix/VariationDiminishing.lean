module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import RealRooted.Mathlib.LinearAlgebra.Matrix.SignVariation

/-!
# Strict maximal-minor variation bound

This module proves Karlin's strict maximal-minor variation bound
(*Total Positivity*, Vol. I, Chapter 5, Section 1, Theorem 1.1) in the local
`S^-` convention: if all maximal minors of a rectangular matrix `A` with
`q ≤ m` columns are nonzero and have one common sign, then
`Fin.signVariations (A.mulVec x) ≤ q - 1` for every `x`.  It also records the
convention `Fin.signVariations 0 = 0`; Karlin assigns the zero vector
`S^- = -1`.

The full forward variation-diminishing theorem for finite rectangular totally
nonnegative matrices is `Matrix.IsTotallyNonnegRect.signVariations_mulVec_le`
in `RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularRankDeficient`, proved
for sign-regular matrices through the sign-block decomposition, strict
approximation, and the rank-deficient reduction.
-/

public section

open scoped BigOperators

namespace Fin

/-- The local `S^-` convention gives the zero vector zero sign variations. -/
@[simp]
lemma signVariations_zero (n : ℕ) :
    signVariations (0 : Fin n → ℝ) = 0 :=
  signVariations_eq_zero_of_forall_nonneg 0 (fun _ ↦ le_rfl)

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
  have hdetprod : 0 < B.det * B.det := by simpa [B] using hminor hrows hrows
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
    apply Fin.strictlyAlternates_iff.mpr
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
    have hc0' : (B.submatrix (0 : Fin (q + 1)).succAbove id).det = 0 := by simpa [c] using hc0
    rw [hc0', zero_mul] at hd
    exact (lt_irrefl 0) hd
  let i0 : Fin q := ⟨0, hq⟩
  have hz0 : z 0 ≠ 0 := by
    intro hz0
    have hzpair := Fin.strictlyAlternates_iff.mp hz i0
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
    have hlarge : q ≤ Fin.signVariations (A.mulVec x) := by lia
    exact not_exists_strictlyAlternating_rows_of_strictMaximalMinors
      hq hminor x
        (Fin.exists_strictMono_strictlyAlternates_of_le_signVariations
          hq hlarge)

end Matrix
