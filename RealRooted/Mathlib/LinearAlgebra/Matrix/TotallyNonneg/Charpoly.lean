import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Real eigenvalues of totally nonnegative matrices are nonnegative

The coefficients of the characteristic polynomial of a totally nonnegative
matrix are signed sums of principal minors
(`Matrix.charpoly_coeff_eq_sum_minors`), and all principal minors are
nonnegative.  Evaluating at a negative argument therefore produces a sum of
one strictly positive term (the empty minor) and nonnegative terms, all with
the same sign `(-1) ^ card`, so the characteristic polynomial has no negative
real root.

This is the elementary half of Gantmacher-Krein: realness of the whole
spectrum needs the compound-matrix and Perron-Frobenius machinery, but the
sign of the real eigenvalues only needs the minor expansion.
-/

open Polynomial Finset

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m] [LinearOrder m]

/-- Principal minors of a totally nonnegative matrix are nonnegative. -/
lemma IsTotallyNonneg.principalMinor_nonneg {A : Matrix m m ℝ}
    (hA : A.IsTotallyNonneg) (s : Finset m) :
    0 ≤ (A.submatrix (Subtype.val : s → m) (Subtype.val : s → m)).det := by
  have hcoe : (Subtype.val : s → m) ∘ ⇑(s.orderIsoOfFin rfl)
      = ⇑(s.orderEmbOfFin rfl) := by
    funext x
    exact s.coe_orderIsoOfFin_apply rfl x
  calc (0 : ℝ)
      ≤ (A.submatrix (⇑(s.orderEmbOfFin rfl)) (⇑(s.orderEmbOfFin rfl))).det :=
        hA (s.orderEmbOfFin rfl).strictMono (s.orderEmbOfFin rfl).strictMono
    _ = ((A.submatrix (Subtype.val : s → m) Subtype.val).submatrix
          (⇑(s.orderIsoOfFin rfl).toEquiv) (⇑(s.orderIsoOfFin rfl).toEquiv)).det := by
        rw [submatrix_submatrix]
        congr 1 <;> exact hcoe.symm
    _ = (A.submatrix (Subtype.val : s → m) Subtype.val).det :=
        det_submatrix_equiv_self _ _

/-- The characteristic polynomial of a totally nonnegative matrix does not
vanish at negative arguments. -/
theorem IsTotallyNonneg.eval_charpoly_ne_zero_of_neg
    {A : Matrix m m ℝ} (hA : A.IsTotallyNonneg) {t : ℝ} (ht : t < 0) :
    A.charpoly.eval t ≠ 0 := by
  set N := Fintype.card m with hN
  have hdeg : A.charpoly.natDegree = N := A.charpoly_natDegree_eq_dim
  have heval : A.charpoly.eval t
      = ∑ j ∈ Finset.range (N + 1), A.charpoly.coeff j * t ^ j := by
    rw [eval_eq_sum_range, hdeg]
  have hterm : ∀ j ∈ Finset.range (N + 1),
      A.charpoly.coeff j * t ^ j
        = (-1 : ℝ) ^ N * ((∑ s ∈ Finset.univ.powersetCard (N - j),
            (A.submatrix (Subtype.val : s → m) Subtype.val).det) * (-t) ^ j) := by
    intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hcoeff := A.charpoly_coeff_eq_sum_minors (N - j) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hjN] at hcoeff
    have ht' : t ^ j = (-1 : ℝ) ^ j * (-t) ^ j := by
      rw [← mul_pow]
      norm_num
    calc A.charpoly.coeff j * t ^ j
        = ((-1 : ℝ) ^ (N - j) * ∑ s ∈ Finset.univ.powersetCard (N - j),
            (A.submatrix (Subtype.val : s → m) Subtype.val).det) * t ^ j := by
          rw [hcoeff]
      _ = (-1 : ℝ) ^ (N - j) * (-1 : ℝ) ^ j * ((∑ s ∈ Finset.univ.powersetCard (N - j),
            (A.submatrix (Subtype.val : s → m) Subtype.val).det) * (-t) ^ j) := by
          rw [ht']; ring
      _ = (-1 : ℝ) ^ N * ((∑ s ∈ Finset.univ.powersetCard (N - j),
            (A.submatrix (Subtype.val : s → m) Subtype.val).det) * (-t) ^ j) := by
          rw [← pow_add, Nat.sub_add_cancel hjN]
  have hsum : A.charpoly.eval t
      = (-1 : ℝ) ^ N * ∑ j ∈ Finset.range (N + 1),
          (∑ s ∈ Finset.univ.powersetCard (N - j),
            (A.submatrix (Subtype.val : s → m) Subtype.val).det) * (-t) ^ j := by
    rw [heval, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hpos : 0 < ∑ j ∈ Finset.range (N + 1),
      (∑ s ∈ Finset.univ.powersetCard (N - j),
        (A.submatrix (Subtype.val : s → m) Subtype.val).det) * (-t) ^ j := by
    have hnt : (0 : ℝ) < -t := neg_pos.mpr ht
    refine Finset.sum_pos' (fun j _ => ?_) ⟨N, Finset.self_mem_range_succ N, ?_⟩
    · exact mul_nonneg
        (Finset.sum_nonneg fun s _ => hA.principalMinor_nonneg s)
        (le_of_lt (pow_pos hnt j))
    · have hzero : Finset.univ.powersetCard (N - N) = {(∅ : Finset m)} := by
        simp
      rw [hzero, Finset.sum_singleton]
      have hempty : (A.submatrix (Subtype.val : (∅ : Finset m) → m) Subtype.val).det = 1 :=
        det_isEmpty
      rw [hempty, one_mul]
      exact pow_pos hnt N
  rw [hsum]
  exact mul_ne_zero (pow_ne_zero N (by norm_num)) hpos.ne'

/-- **Real eigenvalues of a totally nonnegative matrix are nonnegative.** -/
theorem IsTotallyNonneg.nonneg_of_isRoot_charpoly
    {A : Matrix m m ℝ} (hA : A.IsTotallyNonneg) {t : ℝ}
    (h : A.charpoly.IsRoot t) : 0 ≤ t :=
  not_lt.mp fun ht => hA.eval_charpoly_ne_zero_of_neg ht h

end Matrix
