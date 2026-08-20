import RealRooted.ThresholdMatrix
import RealRooted.VeroneseMatrix

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Marker-one threshold matrices preserve interlacing sequences

This file proves the `2 × 2` entry condition for threshold rows whose marker is
`1`, and deduces that such threshold matrices carry interlacing sequences to
interlacing sequences.

The entries of a marker-one threshold row are `X` strictly before the threshold
and `1` from the threshold onward, so the matrix acting on a sequence
`{h j}` produces

```text
r k = X * ∑_{j < k} h j + ∑_{j ≥ k} h j.
```

That is exactly the construction in Branden's Corollary 8.7, and the form used
by Branden--Saud Leite, *Totally nonnegative matrices, chain enumeration and
zeros of polynomials* (arXiv:2412.06595), Lemma 3.1(2), after conjugating by
`t ↦ t/(1-t)`.

Monotonicity of the threshold in the row index and of the column index leaves
exactly six entry patterns; three are reflexivity, two reduce to the single
inequality `u * V ≤ U * v`, and one is the degenerate shared-root case.
-/

/-- A marker-one threshold entry is `X` before the threshold and `1` from the
threshold onward. -/
theorem thresholdEntry_one (t j : ℕ) :
    thresholdEntry t (1 : ℝ[X]) j = if j < t then X else 1 := by
  unfold thresholdEntry
  split_ifs <;> simp_all

/-- Reflexivity of `Prec0` on real-rooted polynomials. -/
theorem prec0_refl_of_realRooted {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) : Prec0 p p :=
  (prec_refl hp.1 hp.2).toPrec0

/-- `X * (C s * X + C v)` is real-rooted for positive `s`. -/
theorem isRealRooted_X_mul_affine {s v : ℝ} (hs : 0 < s) :
    (X * (C s * X + C v)) ≠ 0 ∧ (X * (C s * X + C v)).Splits := by
  obtain ⟨hne, hsplits⟩ := isRealRooted_affine_factor (s := s) (t := v) hs
  refine ⟨mul_ne_zero isRealRooted_X.1 hne, ?_⟩
  exact isRealRooted_X.2.mul hsplits

/-- Degree-one to degree-two step: a positive affine form precedes the
`X`-multiple of another one under the cross inequality. -/
theorem prec0_affine_to_X_mul_affine {u v U V : ℝ}
    (hu : 0 < u) (hU : 0 < U) (hcross : u * V ≤ U * v)
    (hv : 0 ≤ v) (hV : 0 ≤ V) :
    Prec0 (C U * X + C V) (X * (C u * X + C v)) :=
  (prec_to_prec_mul_X_of_nonneg
    (prec_affine_linear_affine_linear_of_cross hu hU hcross)
    (hasNonnegCoeffs_affine_linear hu.le hv)
    (hasNonnegCoeffs_affine_linear hU.le hV)).toPrec0

/-! ### The six entry patterns -/

private theorem case_XXXX {s t : ℝ} (hs : 0 < s) :
    Prec0 ((C s * X + C t) * X + X) ((C s * X + C t) * X + X) := by
  rw [show (C s * X + C t) * X + X = X * (C s * X + C (t + 1)) by rw [C_add, C_1]; ring]
  exact prec0_refl_of_realRooted (isRealRooted_X_mul_affine hs)

private theorem case_X1XX {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 ((C s * X + C t) * 1 + X) ((C s * X + C t) * X + X) := by
  rw [show (C s * X + C t) * 1 + X = C (s + 1) * X + C t by rw [C_add, C_1]; ring,
      show (C s * X + C t) * X + X = X * (C s * X + C (t + 1)) by rw [C_add, C_1]; ring]
  exact prec0_affine_to_X_mul_affine hs (by positivity) (by nlinarith) (by positivity) ht.le

private theorem case_X1X1 {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 ((C s * X + C t) * 1 + 1) ((C s * X + C t) * X + X) := by
  rw [show (C s * X + C t) * 1 + 1 = C s * X + C (t + 1) by rw [C_add, C_1]; ring,
      show (C s * X + C t) * X + X = X * (C s * X + C (t + 1)) by rw [C_add, C_1]; ring]
  exact prec0_affine_to_X_mul_affine hs hs le_rfl (by positivity) (by positivity)

private theorem case_11XX {s t : ℝ} (hs : 0 < s) :
    Prec0 ((C s * X + C t) * 1 + X) ((C s * X + C t) * 1 + X) := by
  rw [show (C s * X + C t) * 1 + X = C (s + 1) * X + C t by rw [C_add, C_1]; ring]
  exact prec0_refl_of_realRooted (isRealRooted_affine_factor (by positivity))

private theorem case_11X1 {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 ((C s * X + C t) * 1 + 1) ((C s * X + C t) * 1 + X) := by
  rw [show (C s * X + C t) * 1 + 1 = C s * X + C (t + 1) by rw [C_add, C_1]; ring,
      show (C s * X + C t) * 1 + X = C (s + 1) * X + C t by rw [C_add, C_1]; ring]
  exact prec0_affine_linear_affine_linear_of_cross hs (by positivity) (by nlinarith)

private theorem case_1111 {s t : ℝ} (hs : 0 < s) :
    Prec0 ((C s * X + C t) * 1 + 1) ((C s * X + C t) * 1 + 1) := by
  rw [show (C s * X + C t) * 1 + 1 = C s * X + C (t + 1) by rw [C_add, C_1]; ring]
  exact prec0_refl_of_realRooted (isRealRooted_affine_factor hs)

/-- **The marker-one `2 × 2` entry property.**  For thresholds `t₁ ≤ t₂` and
columns `j₁ ≤ j₂`, the four marker-one threshold entries satisfy the affine
`2 × 2` interlacing condition. -/
theorem has2x2_thresholdEntry_one {t₁ t₂ j₁ j₂ : ℕ} (ht : t₁ ≤ t₂) (hj : j₁ ≤ j₂) :
    Has2x2InterlacingProperty0
      (thresholdEntry t₁ (1 : ℝ[X]) j₁) (thresholdEntry t₁ (1 : ℝ[X]) j₂)
      (thresholdEntry t₂ (1 : ℝ[X]) j₁) (thresholdEntry t₂ (1 : ℝ[X]) j₂) := by
  intro s t hs ht0
  simp only [thresholdEntry_one]
  split_ifs <;>
    first
      | (exfalso; lia)
      | exact case_XXXX hs
      | exact case_X1XX hs ht0
      | exact case_X1X1 hs ht0
      | exact case_11XX hs
      | exact case_11X1 hs ht0
      | exact case_1111 hs

/-! ### Marker-one threshold matrices -/

/-- The marker-one threshold rows with thresholds `0, 1, …, n-1`. -/
def thresholdOneRows (n : ℕ) : List (ℕ × ℝ[X]) :=
  (List.range n).map fun k => (k, (1 : ℝ[X]))

@[simp] theorem length_thresholdOneRows (n : ℕ) : (thresholdOneRows n).length = n := by
  simp [thresholdOneRows]

theorem get_thresholdOneRows {n : ℕ} (i : Fin (thresholdOneRows n).length) :
    (thresholdOneRows n).get i = (i.1, (1 : ℝ[X])) := by
  simp only [thresholdOneRows, List.get_eq_getElem, List.getElem_map, List.getElem_range]

theorem thresholdOneRows_marker_nonneg {n : ℕ} :
    ∀ p ∈ thresholdOneRows n, HasNonnegCoeffs p.2 := by
  intro p hp
  simp only [thresholdOneRows, List.mem_map, List.mem_range] at hp
  obtain ⟨k, -, rfl⟩ := hp
  simpa using isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one

/-- **Marker-one threshold matrices preserve interlacing sequences.**  This is
the specialization of Branden's Corollary 8.7 used by Branden--Saud Leite for
their Lemma 3.1(2): acting by the matrix whose `k`-th row is `X` before column
`k` and `1` from column `k` on carries an interlacing sequence with nonnegative
coefficients to another one. -/
theorem thresholdOneMatrix_preserves_interlacing {q n : ℕ}
    (fs : List ℝ[X]) (hfs_len : fs.length = q) (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (thresholdMatrix q (thresholdOneRows n)) fs) := by
  refine thresholdMatrix_preserves_interlacing_seq0_of_entry
    (thresholdOneRows n) thresholdOneRows_marker_nonneg ?_ fs hfs_len hfs
  intro i₁ i₂ j₁ j₂ hi hj
  rw [get_thresholdOneRows, get_thresholdOneRows]
  exact has2x2_thresholdEntry_one hi hj

end RealRooted
