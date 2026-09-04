import RealRooted.ThresholdMatrix.Basic

/-!
# Haglund--Zhang threshold matrices and OEIS A046802

The `1`/`1 + X` threshold-entry classification, its matrix-preservation
backend, the binomial Eulerian recursion, and the sequence-facing A046802
surface.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-! ## Haglund--Zhang / A046802 backend -/

namespace OEIS
namespace Backend

/-- Haglund--Zhang notation for threshold entries. -/
abbrev hzEntry (t : ℕ) (α : ℝ[X]) (j : ℕ) : ℝ[X] :=
  thresholdEntry t α j

/-- Haglund--Zhang notation for threshold rows. -/
abbrev hzRow (q t : ℕ) (α : ℝ[X]) : List ℝ[X] :=
  thresholdRow q t α

/-- Haglund--Zhang notation for threshold matrices. -/
abbrev hzMatrix (q : ℕ) (rows : List (ℕ × ℝ[X])) : List (List ℝ[X]) :=
  thresholdMatrix q rows

/-- Threshold list for the binomial Eulerian specialization. -/
abbrev hzBinomialThresholds (n : ℕ) : List ℕ :=
  List.range n

lemma hzBinomialThresholds_mono (n : ℕ) :
    ∀ i j : Fin (hzBinomialThresholds n).length, i ≤ j →
      (hzBinomialThresholds n).get i ≤ (hzBinomialThresholds n).get j := by
  intro i j hij
  simp only [hzBinomialThresholds, List.get_eq_getElem, List.getElem_range]
  exact hij

/-- Row data for the binomial Eulerian specialization: all markers are `1 + X`. -/
abbrev hzBinomialRows (ts : List ℕ) : List (ℕ × ℝ[X]) :=
  ts.map (fun t => (t, (1 + X : ℝ[X])))

/-- Matrix for the binomial Eulerian specialization. -/
abbrev hzBinomialMatrix (q : ℕ) (ts : List ℕ) : List (List ℝ[X]) :=
  hzMatrix q (hzBinomialRows ts)

/-- The one-row terminal data for `(1 + X) f₀ + f₁ + ...`. -/
abbrev hzTerminalRows : List (ℕ × ℝ[X]) :=
  [(0, (1 + X : ℝ[X]))]

/-- The one-row terminal matrix for `(1 + X) f₀ + f₁ + ...`. -/
abbrev hzTerminalMatrix (q : ℕ) : List (List ℝ[X]) :=
  hzMatrix q hzTerminalRows

/-- Haglund--Zhang terminal polynomial `(1 + X) f₀ + f₁ + ...`.

The length parameter is kept explicit so this is literally the action of the
terminal threshold row of width `q`. -/
def hzTerminalPolynomial (q : ℕ) (fs : List ℝ[X]) : ℝ[X] :=
  ((hzRow q 0 (1 + X)).zipWith (· * ·) fs).sum

@[simp] lemma length_hzBinomialRows (ts : List ℕ) :
    (hzBinomialRows ts).length = ts.length := by
  simp [hzBinomialRows]

@[simp] lemma length_hzBinomialMatrix (q : ℕ) (ts : List ℕ) :
    (hzBinomialMatrix q ts).length = ts.length := by
  simp [hzBinomialMatrix]

@[simp] lemma length_hzTerminalRows :
    hzTerminalRows.length = 1 := by
  simp [hzTerminalRows]

@[simp] lemma length_hzTerminalMatrix (q : ℕ) :
    (hzTerminalMatrix q).length = 1 := by
  simp [hzTerminalMatrix]

/-- Validity data for a Haglund--Zhang threshold matrix. -/
structure HZData (rows : List (ℕ × ℝ[X])) : Prop where
  /-- Every diagonal marker is `1` or `1 + X`. -/
  alpha_mem : ∀ p ∈ rows, p.2 = 1 ∨ p.2 = 1 + X
  /-- Thresholds are nondecreasing down the rows. -/
  thresh_mono : ∀ i j : Fin rows.length, i ≤ j → (rows.get i).1 ≤ (rows.get j).1
  /-- Equal-threshold compatibility in the matrix orientation. -/
  compat : ∀ i j : Fin rows.length, i ≤ j → (rows.get i).1 = (rows.get j).1 →
    (rows.get i).2 = 1 + X → (rows.get j).2 = 1 + X

lemma HZData.alpha_nonneg {rows : List (ℕ × ℝ[X])} (h : HZData rows) :
    ∀ p ∈ rows, HasNonnegCoeffs p.2 := by
  intro p hp
  rcases h.alpha_mem p hp with hα | hα <;> rw [hα]
  · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one
  · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one_add_X

lemma hzBinomialRows_data {ts : List ℕ}
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j) :
    HZData (hzBinomialRows ts) := by
  constructor
  · intro p hp
    simp only [hzBinomialRows, List.mem_map] at hp
    obtain ⟨t, _, rfl⟩ := hp
    exact Or.inr rfl
  · intro i j hij
    let i' : Fin ts.length := ⟨i.1, by simpa using i.2⟩
    let j' : Fin ts.length := ⟨j.1, by simpa using j.2⟩
    have hij' : i' ≤ j' := hij
    have hkey := hmono i' j' hij'
    simpa [hzBinomialRows, List.get_eq_getElem, i', j'] using hkey
  · intro i j _ _ _
    simp [hzBinomialRows, List.get_eq_getElem, List.getElem_map]

lemma hzTerminalRows_data :
    HZData hzTerminalRows := by
  constructor
  · intro p hp
    have hp' : p = (0, (1 + X : ℝ[X])) := by simpa [hzTerminalRows] using hp
    subst p
    exact Or.inr rfl
  · intro i j _
    simp [hzTerminalRows]
  · intro i j _ _ _
    simp [hzTerminalRows]

@[simp] lemma matPolyAction_hzTerminalMatrix (q : ℕ) (fs : List ℝ[X]) :
    matPolyAction (hzTerminalMatrix q) fs = [hzTerminalPolynomial q fs] := by
  simp [hzTerminalPolynomial, hzTerminalMatrix, hzTerminalRows, hzMatrix,
    thresholdMatrix, matPolyAction]

@[simp] lemma sum_matPolyAction_hzTerminalMatrix (q : ℕ) (fs : List ℝ[X]) :
    (matPolyAction (hzTerminalMatrix q) fs).sum = hzTerminalPolynomial q fs := by
  simp

lemma hzTerminalPolynomial_mem_matPolyAction (q : ℕ) (fs : List ℝ[X]) :
    hzTerminalPolynomial q fs ∈ matPolyAction (hzTerminalMatrix q) fs := by
  simp

/-! ### Finite-entry shape helpers -/

private lemma hzMiddleQuadratic_eq (s t : ℝ) :
    ((C s * X + C t) * (1 + X) + X : ℝ[X]) =
      C s * X ^ 2 + C (s + t + 1) * X + C t := by
  grind

private lemma eval_hzMiddleQuadratic (s t r : ℝ) :
    (((C s * X + C t) * (1 + X) + X : ℝ[X]).eval r) =
      s * r ^ 2 + (s + t + 1) * r + t := by
  rw [hzMiddleQuadratic_eq]
  simp [eval_add, eval_mul, eval_C, eval_X, pow_two]

private lemma hzMiddleQuadratic_natDegree {s t : ℝ} (hs : 0 < s) :
    (((C s * X + C t) * (1 + X) + X : ℝ[X]).natDegree) = 2 := by
  rw [hzMiddleQuadratic_eq]
  exact natDegree_quadratic hs.ne'

private lemma hzMiddleQuadratic_splits {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ((C s * X + C t) * (1 + X) + X : ℝ[X]).Splits := by
  rw [hzMiddleQuadratic_eq]
  exact quadraticPoly_splits_of_le hs (by
    nlinarith [sq_nonneg (s - t), hs, ht])

private lemma hzMiddleQuadratic_posLeadingCoeff {s t : ℝ} (hs : 0 < s) :
    HasPosLeadingCoeff ((C s * X + C t) * (1 + X) + X : ℝ[X]) := by
  unfold HasPosLeadingCoeff
  rw [hzMiddleQuadratic_eq, leadingCoeff_quadratic hs.ne']
  exact hs

private lemma hzXAffineAddOne_eq (s t : ℝ) :
    (X * (C s * X + C t + 1) : ℝ[X]) =
      C s * X ^ 2 + C (t + 1) * X + C 0 := by
  grind

private lemma eval_hzXAffineAddOne (s t r : ℝ) :
    ((X * (C s * X + C t + 1) : ℝ[X]).eval r) =
      s * r ^ 2 + (t + 1) * r := by
  rw [hzXAffineAddOne_eq]
  simp [eval_add, eval_mul, eval_C, eval_X, pow_two]

private lemma hzXAffineAddOne_natDegree {s t : ℝ} (hs : 0 < s) :
    ((X * (C s * X + C t + 1) : ℝ[X]).natDegree) = 2 := by
  rw [hzXAffineAddOne_eq]
  exact natDegree_quadratic hs.ne'

private lemma hzXAffineAddOne_splits {s t : ℝ} (hs : 0 < s) :
    (X * (C s * X + C t + 1) : ℝ[X]).Splits := by
  rw [hzXAffineAddOne_eq]
  exact quadraticPoly_splits_of_le hs (by
    nlinarith [sq_nonneg (t + 1)])

private lemma hzXAffineAddOne_posLeadingCoeff {s t : ℝ} (hs : 0 < s) :
    HasPosLeadingCoeff (X * (C s * X + C t + 1) : ℝ[X]) := by
  unfold HasPosLeadingCoeff
  rw [hzXAffineAddOne_eq, leadingCoeff_quadratic hs.ne']
  exact hs

private lemma prec0_hz_linear_to_quadratic_of_eval_nonpos
    {f F : ℝ[X]}
    (hfdeg : f.natDegree = 1)
    (hFdeg : F.natDegree = 2)
    (hF_splits : F.Splits)
    (hF_pos : HasPosLeadingCoeff F)
    (hroot_nonpos : ∀ r, f.IsRoot r → F.eval r ≤ 0) :
    Prec0 f F := by
  have hInter : Interlaces (1 : ℝ[X]) f := interlaces_one_linear hfdeg
  have hF_ne : F ≠ 0 := by
    intro hF
    rw [hF, natDegree_zero] at hFdeg
    norm_num at hFdeg
  have hno : ∀ r, f.IsRoot r → ¬ (1 : ℝ[X]).IsRoot r := by
    intro r _ h
    simp at h
  have hroot :
      ∀ r, f.IsRoot r → F.eval r * (1 : ℝ[X]).eval r ≤ 0 := by
    intro r hr
    simpa using hroot_nonpos r hr
  exact
    (prec_of_interlaces_eval_mul_nonpos_of_no_common
      hInter hasPosLeadingCoeff_one hF_ne hF_splits hF_pos
      (by lia) (by lia) hno hroot).toPrec0

private lemma prec0_hz_affine_add_one_self {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + 1) (C s * X + C t + 1) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  exact prec0_refl_of_realRooted
    (isRealRooted_affine_factor (s := s) (t := t + 1) hs)

private lemma prec0_hz_affine_add_one_affine_add_one_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) (C s * X + C t + (1 + X)) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
    C (s + 1) * X + C (t + 1) by grind]
  exact
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t + 1) (U := s + 1) (V := t + 1)
      hs (by positivity) (by nlinarith [ht])

private lemma prec0_hz_affine_add_one_add_X_self {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + (1 + X)) (C s * X + C t + (1 + X)) := by
  rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
    C (s + 1) * X + C (t + 1) by grind]
  exact prec0_refl_of_realRooted
    (isRealRooted_affine_factor (s := s + 1) (t := t + 1) (by positivity))

private lemma prec0_hz_affine_add_one_affine_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) (C s * X + C t + X) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t + 1) (U := s + 1) (V := t)
      hs (by positivity) (by nlinarith [hs, ht])

private lemma prec0_hz_affine_add_one_add_X_affine_add_X
    {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + (1 + X)) (C s * X + C t + X) := by
  rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
    C (s + 1) * X + C (t + 1) by grind]
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    prec0_affine_linear_affine_linear_of_cross
      (u := s + 1) (v := t + 1) (U := s + 1) (V := t)
      (by positivity) (by positivity) (by nlinarith)

private lemma prec0_hz_affine_add_X_self {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + X) (C s * X + C t + X) := by
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact prec0_refl_of_realRooted
    (isRealRooted_affine_factor (s := s + 1) (t := t) (by positivity))

private lemma prec0_hz_affine_add_one_middleQuadratic
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) ((C s * X + C t) * (1 + X) + X) := by
  apply prec0_hz_linear_to_quadratic_of_eval_nonpos
  · rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    grind
  · exact hzMiddleQuadratic_natDegree hs
  · exact hzMiddleQuadratic_splits hs ht
  · exact hzMiddleQuadratic_posLeadingCoeff hs
  · intro r hr
    have hroot0 : t + (1 + s * r) = 0 := by
      simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C, eval_X,
        add_assoc, add_comm, add_left_comm] using hr
    have hroot : s * r + (t + 1) = 0 := by nlinarith
    rw [eval_hzMiddleQuadratic]
    have hscaled : s ^ 2 * (s * r ^ 2 + (s + t + 1) * r + t) = -s ^ 2 := by
      linear_combination (s ^ 2 * r + s ^ 2) * hroot
    have hscale_pos : 0 < s ^ 2 := sq_pos_of_pos hs
    nlinarith [hscaled, sq_nonneg s, hscale_pos]

private lemma prec0_hz_affine_add_one_add_X_middleQuadratic
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + (1 + X)) ((C s * X + C t) * (1 + X) + X) := by
  apply prec0_hz_linear_to_quadratic_of_eval_nonpos
  · rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
        C (s + 1) * X + C (t + 1) by grind]
    grind
  · exact hzMiddleQuadratic_natDegree hs
  · exact hzMiddleQuadratic_splits hs ht
  · exact hzMiddleQuadratic_posLeadingCoeff hs
  · intro r hr
    have hroot0 : t + (1 + (r + s * r)) = 0 := by
      simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C, eval_X,
        add_assoc, add_comm, add_left_comm] using hr
    have hroot : (s + 1) * r + (t + 1) = 0 := by nlinarith
    rw [eval_hzMiddleQuadratic]
    have hscaled : (s + 1) ^ 2 * (s * r ^ 2 + (s + t + 1) * r + t) =
        -s ^ 2 + s * t - s - t ^ 2 - t - 1 := by
      linear_combination ((s ^ 2 + s) * r + s ^ 2 + s + t + 1) * hroot
    have hscale_pos : 0 < (s + 1) ^ 2 := by positivity
    have hnonpos : -s ^ 2 + s * t - s - t ^ 2 - t - 1 ≤ 0 := by
      nlinarith [sq_nonneg (s - t), hs, ht]
    nlinarith

private lemma prec0_hz_affine_add_X_middleQuadratic
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + X) ((C s * X + C t) * (1 + X) + X) := by
  apply prec0_hz_linear_to_quadratic_of_eval_nonpos
  · rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
    grind
  · exact hzMiddleQuadratic_natDegree hs
  · exact hzMiddleQuadratic_splits hs ht
  · exact hzMiddleQuadratic_posLeadingCoeff hs
  · intro r hr
    have hroot0 : t + (r + s * r) = 0 := by
      simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C, eval_X,
        add_assoc, add_comm, add_left_comm] using hr
    have hroot : (s + 1) * r + t = 0 := by nlinarith
    rw [eval_hzMiddleQuadratic]
    have hscaled : (s + 1) ^ 2 * (s * r ^ 2 + (s + t + 1) * r + t) =
        -t ^ 2 := by
      linear_combination ((s ^ 2 + s) * r + s ^ 2 + 2 * s + t + 1) * hroot
    have hscale_pos : 0 < (s + 1) ^ 2 := by positivity
    nlinarith [hscaled, sq_nonneg t, hscale_pos]

private lemma prec0_hz_affine_add_one_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) (X * (C s * X + C t + 1)) := by
  have hf_rr :
      ((C s * X + C t + 1 : ℝ[X]) ≠ 0 ∧
        (C s * X + C t + 1 : ℝ[X]).Splits) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact isRealRooted_affine_factor (s := s) (t := t + 1) hs
  have hf_nn : HasNonnegCoeffs (C s * X + C t + 1 : ℝ[X]) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact hasNonnegCoeffs_affine_linear hs.le (by nlinarith)
  simpa using (prec_self_mul_X_of_nonneg hf_rr.1 hf_rr.2 hf_nn).toPrec0

private lemma prec0_hz_affine_add_one_add_X_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + (1 + X)) (X * (C s * X + C t + 1)) := by
  apply prec0_hz_linear_to_quadratic_of_eval_nonpos
  · rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
        C (s + 1) * X + C (t + 1) by grind]
    grind
  · exact hzXAffineAddOne_natDegree hs
  · exact hzXAffineAddOne_splits hs
  · exact hzXAffineAddOne_posLeadingCoeff hs
  · intro r hr
    have hroot0 : t + (1 + (r + s * r)) = 0 := by
      simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C, eval_X,
        add_assoc, add_comm, add_left_comm] using hr
    have hroot : (s + 1) * r + (t + 1) = 0 := by nlinarith
    rw [eval_hzXAffineAddOne]
    have hscaled : (s + 1) ^ 2 * (s * r ^ 2 + (t + 1) * r) =
        -(t + 1) ^ 2 := by
      linear_combination ((s ^ 2 + s) * r + t + 1) * hroot
    have hscale_pos : 0 < (s + 1) ^ 2 := by positivity
    nlinarith [hscaled, sq_nonneg (t + 1), hscale_pos]

private lemma prec0_hz_affine_add_X_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + X) (X * (C s * X + C t + 1)) := by
  apply prec0_hz_linear_to_quadratic_of_eval_nonpos
  · rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
    grind
  · exact hzXAffineAddOne_natDegree hs
  · exact hzXAffineAddOne_splits hs
  · exact hzXAffineAddOne_posLeadingCoeff hs
  · intro r hr
    have hroot0 : t + (r + s * r) = 0 := by
      simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C, eval_X,
        add_assoc, add_comm, add_left_comm] using hr
    have hroot : (s + 1) * r + t = 0 := by nlinarith
    rw [eval_hzXAffineAddOne]
    have hscaled : (s + 1) ^ 2 * (s * r ^ 2 + (t + 1) * r) =
        -t * (s + t + 1) := by
      linear_combination ((s ^ 2 + s) * r + s + t + 1) * hroot
    have hscale_pos : 0 < (s + 1) ^ 2 := by positivity
    nlinarith [hscaled, ht, hs]

private lemma prec0_hz_affine_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t) (X * (C s * X + C t + 1)) := by
  apply prec0_hz_linear_to_quadratic_of_eval_nonpos
  · grind
  · exact hzXAffineAddOne_natDegree hs
  · exact hzXAffineAddOne_splits hs
  · exact hzXAffineAddOne_posLeadingCoeff hs
  · intro r hr
    have hroot0 : t + s * r = 0 := by
      simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C, eval_X,
        add_assoc, add_comm, add_left_comm] using hr
    have hroot : s * r + t = 0 := by nlinarith
    rw [eval_hzXAffineAddOne]
    have hscaled : s ^ 2 * (s * r ^ 2 + (t + 1) * r) = -s * t := by
      linear_combination (s ^ 2 * r + s) * hroot
    have hscale_pos : 0 < s ^ 2 := sq_pos_of_pos hs
    nlinarith [hscaled, hs, ht]

private lemma prec0_hz_affine_add_one_mul_one_add_X
    {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + 1) ((C s * X + C t + 1) * (1 + X)) := by
  have hd_rr :
      ((C s * X + C t + 1 : ℝ[X]) ≠ 0 ∧
        (C s * X + C t + 1 : ℝ[X]).Splits) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact isRealRooted_affine_factor (s := s) (t := t + 1) hs
  have hbase : Prec (1 : ℝ[X]) (1 + X) := by
    have hdeg : (1 + X : ℝ[X]).natDegree = 1 := by
      simpa [show (1 + X : ℝ[X]) = X + C (1 : ℝ) by grind] using
        (Polynomial.natDegree_X_add_C (x := (1 : ℝ)))
    exact (interlaces_one_linear (p := (1 + X : ℝ[X])) hdeg).toPrec
  have hmul := prec_mul_common_factor hd_rr.1 hd_rr.2 hbase
  simpa using hmul.toPrec0

private lemma prec0_hz_mul_one_add_X_self
    {s t : ℝ} (hs : 0 < s) :
    Prec0 ((C s * X + C t + 1) * (1 + X)) ((C s * X + C t + 1) * (1 + X)) := by
  have hlin_rr :
      ((C s * X + C t + 1 : ℝ[X]) ≠ 0 ∧
        (C s * X + C t + 1 : ℝ[X]).Splits) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact isRealRooted_affine_factor (s := s) (t := t + 1) hs
  have hS_rr : ((1 + X : ℝ[X]) ≠ 0 ∧ (1 + X : ℝ[X]).Splits) := by
    rw [show (1 + X : ℝ[X]) = C (1 : ℝ) * X + C 1 by grind]
    exact isRealRooted_affine_factor (s := 1) (t := 1) zero_lt_one
  exact prec0_refl_of_realRooted
    (isRealRooted_mul hlin_rr.1 hlin_rr.2 hS_rr.1 hS_rr.2)

private lemma prec0_hz_middleQuadratic_self
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 ((C s * X + C t) * (1 + X) + X)
      ((C s * X + C t) * (1 + X) + X) := by
  have hdeg := hzMiddleQuadratic_natDegree (s := s) (t := t) hs
  have hne : ((C s * X + C t) * (1 + X) + X : ℝ[X]) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    norm_num at hdeg
  exact prec0_refl_of_realRooted ⟨hne, hzMiddleQuadratic_splits hs ht⟩

private lemma prec0_hz_mul_one_add_X_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) :
    Prec0 ((C s * X + C t + 1) * (1 + X)) (X * (C s * X + C t + 1)) := by
  have hd_rr :
      ((C s * X + C t + 1 : ℝ[X]) ≠ 0 ∧
        (C s * X + C t + 1 : ℝ[X]).Splits) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact isRealRooted_affine_factor (s := s) (t := t + 1) hs
  have hbase : Prec (1 + X : ℝ[X]) X := by
    rw [show (1 + X : ℝ[X]) = X + 1 by grind]
    simpa using
      prec_affine_linear_affine_linear_of_cross
        (u := 1) (v := 1) (U := 1) (V := 0)
        zero_lt_one zero_lt_one (by norm_num)
  have hmul := prec_mul_common_factor hd_rr.1 hd_rr.2 hbase
  rw [show (X * (C s * X + C t + 1) : ℝ[X]) =
    (C s * X + C t + 1) * X by ring]
  simpa using hmul.toPrec0

private lemma prec0_hz_XAffineAddOne_self
    {s t : ℝ} (hs : 0 < s) :
    Prec0 (X * (C s * X + C t + 1)) (X * (C s * X + C t + 1)) := by
  have hdeg := hzXAffineAddOne_natDegree (s := s) (t := t) hs
  have hne : (X * (C s * X + C t + 1) : ℝ[X]) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    norm_num at hdeg
  exact prec0_refl_of_realRooted ⟨hne, hzXAffineAddOne_splits hs⟩

private lemma prec0_hz_middleQuadratic_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 ((C s * X + C t) * (1 + X) + X) (X * (C s * X + C t + 1)) := by
  have hself : Prec0 (X * (C s * X + C t + 1)) (X * (C s * X + C t + 1)) :=
    prec0_hz_XAffineAddOne_self hs
  have hlin : Prec0 (C s * X + C t) (X * (C s * X + C t + 1)) :=
    prec0_hz_affine_XAffineAddOne hs ht
  have hq_nn : HasNonnegCoeffs (X * (C s * X + C t + 1) : ℝ[X]) := by
    refine hasNonnegCoeffs_X.mul ?_
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact hasNonnegCoeffs_affine_linear hs.le (by nlinarith)
  have hlin_nn : HasNonnegCoeffs (C s * X + C t : ℝ[X]) :=
    hasNonnegCoeffs_affine_linear hs.le ht.le
  have hsum :=
    prec0_add_left_of_common_right_of_nonneg hself hlin hq_nn hlin_nn
  rw [show ((C s * X + C t) * (1 + X) + X : ℝ[X]) =
      X * (C s * X + C t + 1) + (C s * X + C t) by grind]
  exact hsum

private def HZ2x2EntryShape (a b c d : ℝ[X]) : Prop :=
  Threshold2x2EntryTuple a b c d 1 1 1 1 ∨
  Threshold2x2EntryTuple a b c d 1 1 (1 + X) 1 ∨
  Threshold2x2EntryTuple a b c d 1 1 (1 + X) (1 + X) ∨
  Threshold2x2EntryTuple a b c d 1 1 X 1 ∨
  Threshold2x2EntryTuple a b c d 1 1 X (1 + X) ∨
  Threshold2x2EntryTuple a b c d 1 1 X X ∨
  Threshold2x2EntryTuple a b c d (1 + X) 1 (1 + X) 1 ∨
  Threshold2x2EntryTuple a b c d (1 + X) 1 X 1 ∨
  Threshold2x2EntryTuple a b c d (1 + X) 1 X (1 + X) ∨
  Threshold2x2EntryTuple a b c d (1 + X) 1 X X ∨
  Threshold2x2EntryTuple a b c d (1 + X) (1 + X) (1 + X) (1 + X) ∨
  Threshold2x2EntryTuple a b c d (1 + X) (1 + X) X X ∨
  Threshold2x2EntryTuple a b c d X 1 X 1 ∨
  Threshold2x2EntryTuple a b c d X 1 X (1 + X) ∨
  Threshold2x2EntryTuple a b c d X 1 X X ∨
  Threshold2x2EntryTuple a b c d X (1 + X) X (1 + X) ∨
  Threshold2x2EntryTuple a b c d X (1 + X) X X ∨
  Threshold2x2EntryTuple a b c d X X X X

private lemma HZ2x2EntryShape.has2x2 {a b c d : ℝ[X]}
    (h : HZ2x2EntryShape a b c d) :
    Has2x2InterlacingProperty0 a b c d := by
  intro s t hs ht
  rcases h with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
  · simpa using prec0_hz_affine_add_one_self hs
  · simpa using prec0_hz_affine_add_one_affine_add_one_add_X hs ht
  · simpa using prec0_hz_affine_add_one_add_X_self hs
  · simpa using prec0_hz_affine_add_one_affine_add_X hs ht
  · simpa using prec0_hz_affine_add_one_add_X_affine_add_X hs
  · simpa using prec0_hz_affine_add_X_self hs
  · simpa [mul_add, add_mul, add_assoc, add_comm, add_left_comm] using
      prec0_hz_affine_add_one_mul_one_add_X hs
  · simpa using prec0_hz_affine_add_one_middleQuadratic hs ht
  · simpa using prec0_hz_affine_add_one_add_X_middleQuadratic hs ht
  · simpa using prec0_hz_affine_add_X_middleQuadratic hs ht
  · simpa [mul_add, add_mul, add_assoc, add_comm, add_left_comm] using
      prec0_hz_mul_one_add_X_self hs
  · simpa using prec0_hz_middleQuadratic_self hs ht
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using prec0_hz_affine_add_one_XAffineAddOne hs ht
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using prec0_hz_affine_add_one_add_X_XAffineAddOne hs ht
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using prec0_hz_affine_add_X_XAffineAddOne hs ht
  · rw [show ((C s * X + C t) * (1 + X) + (1 + X) : ℝ[X]) =
        (C s * X + C t + 1) * (1 + X) by grind]
    rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using prec0_hz_mul_one_add_X_XAffineAddOne hs
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using prec0_hz_middleQuadratic_XAffineAddOne hs ht
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using prec0_hz_XAffineAddOne_self hs

private lemma hzEntry_shape
    {t₁ t₂ j₁ j₂ : ℕ} {α₁ α₂ : ℝ[X]}
    (hα₁ : α₁ = 1 ∨ α₁ = 1 + X)
    (hα₂ : α₂ = 1 ∨ α₂ = 1 + X)
    (ht : t₁ ≤ t₂) (hj : j₁ ≤ j₂)
    (hcompat : t₁ = t₂ → α₁ = 1 + X → α₂ = 1 + X) :
    HZ2x2EntryShape
      (hzEntry t₁ α₁ j₁) (hzEntry t₁ α₁ j₂)
      (hzEntry t₂ α₂ j₁) (hzEntry t₂ α₂ j₂) := by
  rcases hα₁ with rfl | rfl <;> rcases hα₂ with rfl | rfl
  all_goals
    simp at hcompat
    unfold HZ2x2EntryShape Threshold2x2EntryTuple
    simp only [thresholdEntry]
    split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
    all_goals try lia

/-- The finite entrywise Haglund--Zhang `2 x 2` threshold check. -/
def HZEntryHas2x2Statement : Prop :=
  ∀ {t₁ t₂ j₁ j₂ : ℕ} {α₁ α₂ : ℝ[X]},
    (α₁ = 1 ∨ α₁ = 1 + X) →
    (α₂ = 1 ∨ α₂ = 1 + X) →
    t₁ ≤ t₂ → j₁ ≤ j₂ →
    (t₁ = t₂ → α₁ = 1 + X → α₂ = 1 + X) →
    Has2x2InterlacingProperty0
      (hzEntry t₁ α₁ j₁) (hzEntry t₁ α₁ j₂)
      (hzEntry t₂ α₂ j₁) (hzEntry t₂ α₂ j₂)

theorem hzEntry_has2x2 : HZEntryHas2x2Statement := by
  intro t₁ t₂ j₁ j₂ α₁ α₂ hα₁ hα₂ ht hj hcompat
  exact (hzEntry_shape hα₁ hα₂ ht hj hcompat).has2x2

lemma HZData.entry_has2x2 {q : ℕ} {rows : List (ℕ × ℝ[X])}
    (hrows : HZData rows) (hentry : HZEntryHas2x2Statement) :
    ∀ (i₁ i₂ : Fin rows.length) (j₁ j₂ : Fin q),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (hzEntry (rows.get i₁).1 (rows.get i₁).2 j₁.1)
        (hzEntry (rows.get i₁).1 (rows.get i₁).2 j₂.1)
        (hzEntry (rows.get i₂).1 (rows.get i₂).2 j₁.1)
        (hzEntry (rows.get i₂).1 (rows.get i₂).2 j₂.1) := by
  intro i₁ i₂ j₁ j₂ hi hj
  exact hentry
    (hrows.alpha_mem (rows.get i₁) (List.get_mem rows i₁))
    (hrows.alpha_mem (rows.get i₂) (List.get_mem rows i₂))
    (hrows.thresh_mono i₁ i₂ hi)
    hj
    (hrows.compat i₁ i₂ hi)

/-- Haglund--Zhang threshold matrices preserve interlacing once the finite
entrywise `2 x 2` check is available. -/
theorem haglund_zhang_s_inversion_interlacing_backend
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : HZData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (hzMatrix q rows) fs) :=
  thresholdMatrix_preserves_interlacing_seq0_of_entry rows
    hrows.alpha_nonneg (hrows.entry_has2x2 hentry) fs hfs_len hfs

theorem haglund_zhang_s_inversion_interlacing
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : HZData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (hzMatrix q rows) fs) :=
  haglund_zhang_s_inversion_interlacing_backend hzEntry_has2x2
    rows hrows fs hfs_len hfs

theorem haglund_zhang_s_inversion_interlacing_backend_weak
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : HZData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (hzMatrix q rows) fs) ∧
      ∀ f ∈ matPolyAction (hzMatrix q rows) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  thresholdMatrix_preserves_interlacing_seq0_of_entry_weak rows
    hrows.alpha_nonneg (hrows.entry_has2x2 hentry) fs hfs_len hfs hfs_real

theorem haglund_zhang_s_inversion_interlacing_weak
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : HZData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (hzMatrix q rows) fs) ∧
      ∀ f ∈ matPolyAction (hzMatrix q rows) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  haglund_zhang_s_inversion_interlacing_backend_weak hzEntry_has2x2
    rows hrows fs hfs_len hfs hfs_real

theorem haglund_zhang_s_inversion_sum_realRooted_backend
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : HZData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne : (matPolyAction (hzMatrix q rows) fs).sum ≠ 0) :
    (matPolyAction (hzMatrix q rows) fs).sum ≠ 0 ∧
      ((matPolyAction (hzMatrix q rows) fs).sum).Splits := by
  have hout :=
    haglund_zhang_s_inversion_interlacing_backend_weak hentry
      rows hrows fs hfs_len hfs hfs_real
  exact isRealRooted_sum_of_isInterlacingSeq0Nonneg hout.1 hout.2 hsum_ne

theorem haglund_zhang_s_inversion_sum_realRooted
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : HZData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne : (matPolyAction (hzMatrix q rows) fs).sum ≠ 0) :
    (matPolyAction (hzMatrix q rows) fs).sum ≠ 0 ∧
      ((matPolyAction (hzMatrix q rows) fs).sum).Splits :=
  haglund_zhang_s_inversion_sum_realRooted_backend hzEntry_has2x2
    rows hrows fs hfs_len hfs hfs_real hsum_ne

theorem haglund_zhang_terminal_polynomial_realRooted_backend
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hterminal_ne : hzTerminalPolynomial q fs ≠ 0) :
    hzTerminalPolynomial q fs ≠ 0 ∧ (hzTerminalPolynomial q fs).Splits := by
  have hout :=
    haglund_zhang_s_inversion_interlacing_backend_weak hentry
      hzTerminalRows hzTerminalRows_data fs hfs_len hfs hfs_real
  exact hout.2 (hzTerminalPolynomial q fs)
    (hzTerminalPolynomial_mem_matPolyAction q fs) hterminal_ne

theorem haglund_zhang_terminal_polynomial_realRooted
    {q : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hterminal_ne : hzTerminalPolynomial q fs ≠ 0) :
    hzTerminalPolynomial q fs ≠ 0 ∧ (hzTerminalPolynomial q fs).Splits :=
  haglund_zhang_terminal_polynomial_realRooted_backend hzEntry_has2x2
    fs hfs_len hfs hfs_real hterminal_ne

theorem haglund_zhang_terminal_polynomial_realRooted_of_interlacing
    {q : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs)
    (hterminal_ne : hzTerminalPolynomial q fs ≠ 0) :
    hzTerminalPolynomial q fs ≠ 0 ∧ (hzTerminalPolynomial q fs).Splits := by
  have hfs_weak := weakData_of_isInterlacingSeqNonneg hfs
  exact haglund_zhang_terminal_polynomial_realRooted
    fs hfs_len hfs_weak.1 hfs_weak.2 hterminal_ne

/-- Binomial Eulerian specialization: all diagonal markers are `1 + X`. -/
theorem haglund_zhang_binomial_eulerian_backend
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (hzBinomialMatrix q ts) fs) :=
  haglund_zhang_s_inversion_interlacing_backend hentry _
    (hzBinomialRows_data hmono) fs hfs_len hfs

theorem haglund_zhang_binomial_eulerian
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (hzBinomialMatrix q ts) fs) :=
  haglund_zhang_binomial_eulerian_backend hzEntry_has2x2
    ts hmono fs hfs_len hfs

theorem haglund_zhang_binomial_eulerian_range
    {q n : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (hzBinomialMatrix q (hzBinomialThresholds n)) fs) :=
  haglund_zhang_binomial_eulerian
    (hzBinomialThresholds n) (hzBinomialThresholds_mono n) fs hfs_len hfs

theorem haglund_zhang_binomial_eulerian_backend_weak
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (hzBinomialMatrix q ts) fs) ∧
      ∀ f ∈ matPolyAction (hzBinomialMatrix q ts) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  haglund_zhang_s_inversion_interlacing_backend_weak hentry
    _ (hzBinomialRows_data hmono) fs hfs_len hfs hfs_real

theorem haglund_zhang_binomial_eulerian_weak
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (hzBinomialMatrix q ts) fs) ∧
      ∀ f ∈ matPolyAction (hzBinomialMatrix q ts) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  haglund_zhang_binomial_eulerian_backend_weak hzEntry_has2x2
    ts hmono fs hfs_len hfs hfs_real

theorem haglund_zhang_binomial_eulerian_range_weak
    {q n : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (hzBinomialMatrix q (hzBinomialThresholds n)) fs) ∧
      ∀ f ∈ matPolyAction (hzBinomialMatrix q (hzBinomialThresholds n)) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  haglund_zhang_binomial_eulerian_weak
    (hzBinomialThresholds n) (hzBinomialThresholds_mono n)
    fs hfs_len hfs hfs_real

theorem haglund_zhang_binomial_eulerian_sum_realRooted_backend
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne :
      (matPolyAction (hzBinomialMatrix q ts) fs).sum ≠ 0) :
    (matPolyAction (hzBinomialMatrix q ts) fs).sum ≠ 0 ∧
      ((matPolyAction (hzBinomialMatrix q ts) fs).sum).Splits := by
  have hout :=
    haglund_zhang_binomial_eulerian_backend_weak hentry
      ts hmono fs hfs_len hfs hfs_real
  exact isRealRooted_sum_of_isInterlacingSeq0Nonneg hout.1 hout.2 hsum_ne

theorem haglund_zhang_binomial_eulerian_sum_realRooted
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne :
      (matPolyAction (hzBinomialMatrix q ts) fs).sum ≠ 0) :
    (matPolyAction (hzBinomialMatrix q ts) fs).sum ≠ 0 ∧
      ((matPolyAction (hzBinomialMatrix q ts) fs).sum).Splits :=
  haglund_zhang_binomial_eulerian_sum_realRooted_backend hzEntry_has2x2
    ts hmono fs hfs_len hfs hfs_real hsum_ne

theorem haglund_zhang_binomial_eulerian_range_sum_realRooted
    {q n : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne :
      (matPolyAction (hzBinomialMatrix q (hzBinomialThresholds n)) fs).sum ≠ 0) :
    (matPolyAction (hzBinomialMatrix q (hzBinomialThresholds n)) fs).sum ≠ 0 ∧
      ((matPolyAction (hzBinomialMatrix q (hzBinomialThresholds n)) fs).sum).Splits :=
  haglund_zhang_binomial_eulerian_sum_realRooted
    (hzBinomialThresholds n) (hzBinomialThresholds_mono n)
    fs hfs_len hfs hfs_real hsum_ne

private def realListAction (G : List (List ℝ)) (cs : List ℝ) : List ℝ :=
  G.map (fun row => (row.zipWith (· * ·) cs).sum)

private def hzConstEntry (t j : ℕ) : ℝ :=
  if j < t then 0 else 1

private def hzConstRow (q t : ℕ) : List ℝ :=
  (List.range q).map (hzConstEntry t)

private def hzConstMatrix (q n : ℕ) : List (List ℝ) :=
  (List.range n).map (hzConstRow q)

private lemma real_zipWith_mul_replicate_zero_sum (row : List ℝ) (n : ℕ) :
    (row.zipWith (· * ·) (List.replicate n (0 : ℝ))).sum = 0 := by
  induction n generalizing row with
  | zero =>
      cases row <;> rfl
  | succ n ih =>
      cases row with
      | nil => rfl
      | cons _ row =>
          rw [show n + 1 = Nat.succ n by rfl, List.replicate_succ]
          simp [ih row]

private lemma real_zipWith_mul_cons_replicate_zero_sum
    (row : List ℝ) (n : ℕ) :
    (row.zipWith (· * ·) (1 :: List.replicate n (0 : ℝ))).sum =
      row.headD 0 := by
  cases row with
  | nil => simp
  | cons _ row => simp [real_zipWith_mul_replicate_zero_sum]

private lemma headD_hzConstRow (n t : ℕ) :
    (hzConstRow (n + 1) t).headD 0 = if t = 0 then 1 else 0 := by
  by_cases ht : t = 0
  · simp [hzConstRow, hzConstEntry, List.head?_map, List.head?_range, ht]
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    simp [hzConstRow, hzConstEntry, List.head?_map, List.head?_range, ht, htpos]

private lemma realListAction_hzConstRow_delta (t n : ℕ) :
    ((hzConstRow (n + 1) t).zipWith (· * ·)
      (1 :: List.replicate n (0 : ℝ))).sum =
      if t = 0 then 1 else 0 := by
  rw [real_zipWith_mul_cons_replicate_zero_sum, headD_hzConstRow]

private lemma replicate_append_singleton_zero (n : ℕ) :
    List.replicate n (0 : ℝ) ++ [0] = List.replicate (n + 1) 0 := by
  simpa using
    (List.replicate_append_replicate (n := n) (m := 1) (a := (0 : ℝ)))

private lemma map_range_indicator_zero (n : ℕ) :
    (List.range (n + 1)).map (fun t => if t = 0 then (1 : ℝ) else 0) =
      1 :: List.replicate n 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1).succ by lia]
      rw [List.range_succ, List.map_append, ih]
      simp [replicate_append_singleton_zero]

private lemma realListAction_hzConstMatrix_delta (n : ℕ) :
    realListAction (hzConstMatrix (n + 1) (n + 2))
      (1 :: List.replicate n (0 : ℝ)) =
      1 :: List.replicate (n + 1) 0 := by
  simp only [realListAction, hzConstMatrix, List.map_map]
  change (List.range (n + 2)).map
      (fun t => ((hzConstRow (n + 1) t).zipWith (· * ·)
        (1 :: List.replicate n (0 : ℝ))).sum) =
      1 :: List.replicate (n + 1) 0
  rw [show n + 2 = n + 1 + 1 by lia]
  simpa [realListAction_hzConstRow_delta] using map_range_indicator_zero (n + 1)

private lemma coeff_zero_zipWith (row fs : List ℝ[X]) :
    ((row.zipWith (· * ·) fs).sum).coeff 0 =
      ((row.map (fun p => p.coeff 0)).zipWith (· * ·)
        (fs.map (fun p => p.coeff 0))).sum := by
  induction row generalizing fs with
  | nil =>
      simp
  | cons _ row ih =>
      cases fs with
      | nil => simp
      | cons _ fs => simp [ih, Polynomial.mul_coeff_zero]

private lemma coeff_zero_matPolyAction
    (G : List (List ℝ[X])) (fs : List ℝ[X]) :
    (matPolyAction G fs).map (fun p => p.coeff 0) =
      realListAction (G.map (fun row => row.map (fun p => p.coeff 0)))
        (fs.map (fun p => p.coeff 0)) := by
  simp [realListAction, matPolyAction, coeff_zero_zipWith]

private lemma coeff_zero_thresholdEntry_one_add_X (t j : ℕ) :
    (thresholdEntry t (1 + X : ℝ[X]) j).coeff 0 = hzConstEntry t j := by
  by_cases hlt : j < t
  · simp [thresholdEntry, hzConstEntry, hlt]
  · by_cases heq : j = t
    · simp [thresholdEntry, hzConstEntry, heq]
    · simp [thresholdEntry, hzConstEntry, hlt, heq]

private lemma coeff_zero_hzBinomialMatrix (q n : ℕ) :
    (hzBinomialMatrix q (hzBinomialThresholds n)).map
      (fun row => row.map (fun p => p.coeff 0)) =
      hzConstMatrix q n := by
  simp [hzBinomialMatrix, hzBinomialThresholds, hzBinomialRows, hzMatrix,
    thresholdMatrix, thresholdRow, coeff_zero_thresholdEntry_one_add_X,
    hzConstMatrix, hzConstRow]

private lemma coeff_zero_hzTerminalRow (q : ℕ) :
    (hzRow q 0 (1 + X)).map (fun p => p.coeff 0) =
      hzConstRow q 0 := by
  simp [hzRow, thresholdRow, hzConstRow, coeff_zero_thresholdEntry_one_add_X]

private lemma coeff_zero_hzTerminalPolynomial (q : ℕ) (fs : List ℝ[X]) :
    (hzTerminalPolynomial q fs).coeff 0 =
      ((hzConstRow q 0).zipWith (· * ·)
        (fs.map (fun p => p.coeff 0))).sum := by
  rw [hzTerminalPolynomial, coeff_zero_zipWith, coeff_zero_hzTerminalRow]

/-- The refined binomial Eulerian vector in the Haglund--Zhang recursion.

The vector has length `n + 1`.  The transition from `n` to `n + 1` has width
`n + 1` and `n + 2` threshold rows. -/
def hzBinomialRefined : ℕ → List ℝ[X]
  | 0 => [1]
  | n + 1 =>
      matPolyAction
        (hzBinomialMatrix (n + 1) (hzBinomialThresholds (n + 2)))
        (hzBinomialRefined n)

@[simp] theorem length_hzBinomialRefined (n : ℕ) :
    (hzBinomialRefined n).length = n + 1 := by
  induction n with
  | zero =>
      simp [hzBinomialRefined]
  | succ n =>
      simp [hzBinomialRefined]

@[simp] lemma mem_hzBinomialRefined_zero {f : ℝ[X]} :
    f ∈ hzBinomialRefined 0 ↔ f = 1 := by
  simp [hzBinomialRefined]

theorem coeff_zero_hzBinomialRefined (n : ℕ) :
    (hzBinomialRefined n).map (fun p => p.coeff 0) =
      1 :: List.replicate n 0 := by
  induction n with
  | zero =>
      simp [hzBinomialRefined]
  | succ n ih =>
      simp [hzBinomialRefined, coeff_zero_matPolyAction,
        coeff_zero_hzBinomialMatrix, ih, realListAction_hzConstMatrix_delta]

lemma hzBinomialRefined_zero_interlacing :
    IsInterlacingSeq0Nonneg (hzBinomialRefined 0) := by
  constructor
  · simp [hzBinomialRefined, IsInterlacingSeq0]
  · intro f hf
    have hf' : f = 1 := mem_hzBinomialRefined_zero.mp hf
    subst f
    exact hasNonnegCoeffs_one

lemma hzBinomialRefined_zero_splits :
    ∀ f ∈ hzBinomialRefined 0, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  intro f hf _
  have hf' : f = 1 := mem_hzBinomialRefined_zero.mp hf
  subst f
  exact ⟨one_ne_zero, Polynomial.Splits.one⟩

theorem hzBinomialRefined_interlacing_weak (n : ℕ) :
    IsInterlacingSeq0Nonneg (hzBinomialRefined n) ∧
      ∀ f ∈ hzBinomialRefined n, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  induction n with
  | zero =>
      exact ⟨hzBinomialRefined_zero_interlacing, hzBinomialRefined_zero_splits⟩
  | succ n ih =>
      simpa [hzBinomialRefined] using
        haglund_zhang_binomial_eulerian_range_weak
          (q := n + 1) (n := n + 2) (fs := hzBinomialRefined n)
          (by simp)
          ih.1 ih.2

/-- Interlacing projection from the Haglund--Zhang refined-vector induction. -/
theorem hzBinomialRefined_interlaces (n : ℕ) :
    IsInterlacingSeq0Nonneg (hzBinomialRefined n) :=
  (hzBinomialRefined_interlacing_weak n).1

/-- Real-rootedness projection from the Haglund--Zhang refined-vector induction. -/
theorem hzBinomialRefined_realRooted (n : ℕ) :
    ∀ f ∈ hzBinomialRefined n, f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  (hzBinomialRefined_interlacing_weak n).2

/-- The terminal binomial Eulerian polynomial obtained from the refined vector. -/
def hzBinomialEulerianPolynomial (n : ℕ) : ℝ[X] :=
  hzTerminalPolynomial (n + 1) (hzBinomialRefined n)

@[simp] theorem coeff_zero_hzBinomialEulerianPolynomial (n : ℕ) :
    (hzBinomialEulerianPolynomial n).coeff 0 = 1 := by
  rw [hzBinomialEulerianPolynomial, coeff_zero_hzTerminalPolynomial,
    coeff_zero_hzBinomialRefined]
  simp [realListAction_hzConstRow_delta]

theorem hzBinomialEulerianPolynomial_ne_zero (n : ℕ) :
    hzBinomialEulerianPolynomial n ≠ 0 := by
  intro h
  have hcoeff := coeff_zero_hzBinomialEulerianPolynomial n
  rw [h] at hcoeff
  norm_num at hcoeff

theorem hzBinomialEulerianPolynomial_realRooted_of_ne
    (n : ℕ) (hne : hzBinomialEulerianPolynomial n ≠ 0) :
    hzBinomialEulerianPolynomial n ≠ 0 ∧
      (hzBinomialEulerianPolynomial n).Splits := by
  simpa [hzBinomialEulerianPolynomial] using
    haglund_zhang_terminal_polynomial_realRooted
      (q := n + 1) (fs := hzBinomialRefined n)
      (by simp)
      (hzBinomialRefined_interlaces n) (hzBinomialRefined_realRooted n)
      (by simpa [hzBinomialEulerianPolynomial] using hne)

theorem hzBinomialEulerianPolynomial_splits_of_ne
    (n : ℕ) (hne : hzBinomialEulerianPolynomial n ≠ 0) :
    (hzBinomialEulerianPolynomial n).Splits :=
  (hzBinomialEulerianPolynomial_realRooted_of_ne n hne).2

theorem hzBinomialEulerianPolynomial_realRooted (n : ℕ) :
    hzBinomialEulerianPolynomial n ≠ 0 ∧
      (hzBinomialEulerianPolynomial n).Splits :=
  hzBinomialEulerianPolynomial_realRooted_of_ne
    n (hzBinomialEulerianPolynomial_ne_zero n)

theorem hzBinomialEulerianPolynomial_splits (n : ℕ) :
    (hzBinomialEulerianPolynomial n).Splits :=
  (hzBinomialEulerianPolynomial_realRooted n).2

end Backend

/-! ### OEIS A046802 surface -/

/-- The recurrence-defined A046802 row family, represented by the
Haglund--Zhang binomial Eulerian polynomial.  Agreement with the external OEIS
table is intentionally a separate theorem for the generated sequence file. -/
abbrev A046802 (n : ℕ) : ℝ[X] :=
  Backend.hzBinomialEulerianPolynomial n

/-- The refined Haglund--Zhang vector used as the interlacing certificate for
`A046802`. -/
abbrev A046802Refined (n : ℕ) : List ℝ[X] :=
  Backend.hzBinomialRefined n

@[simp] theorem A046802_eq_hzBinomialEulerianPolynomial (n : ℕ) :
    A046802 n = Backend.hzBinomialEulerianPolynomial n := rfl

@[simp] theorem A046802Refined_eq_hzBinomialRefined (n : ℕ) :
    A046802Refined n = Backend.hzBinomialRefined n := rfl

@[simp] theorem coeff_zero_A046802 (n : ℕ) :
    (A046802 n).coeff 0 = 1 :=
  Backend.coeff_zero_hzBinomialEulerianPolynomial n

/-- Interlacing certificate for the Haglund--Zhang refinement behind A046802. -/
theorem A046802_interlaces (n : ℕ) :
    IsInterlacingSeq0Nonneg (A046802Refined n) :=
  Backend.hzBinomialRefined_interlaces n

/-- Real-rootedness certificate for each nonzero refined polynomial behind A046802. -/
theorem A046802_refined_realRooted (n : ℕ) :
    ∀ f ∈ A046802Refined n, f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  Backend.hzBinomialRefined_realRooted n

theorem A046802_ne_zero (n : ℕ) :
    A046802 n ≠ 0 := by
  intro h
  have hcoeff := coeff_zero_A046802 n
  rw [h] at hcoeff
  norm_num at hcoeff

theorem A046802_realRooted (n : ℕ) :
    A046802 n ≠ 0 ∧ (A046802 n).Splits :=
  Backend.hzBinomialEulerianPolynomial_realRooted n

theorem A046802_splits (n : ℕ) :
    (A046802 n).Splits :=
  (A046802_realRooted n).2

/-- Real-rootedness for the recurrence-defined A046802 family represented by
the Haglund--Zhang binomial Eulerian polynomial. -/
theorem oeisA046802_realRooted (n : ℕ) :
    A046802 n ≠ 0 ∧ (A046802 n).Splits :=
  A046802_realRooted n

/-- Tactic-facing theorem for the `rr_s_inversion_binomial_eulerian_sequence`
route. -/
theorem rr_s_inversion_binomial_eulerian_sequence (n : ℕ) :
    A046802 n ≠ 0 ∧ (A046802 n).Splits :=
  A046802_realRooted n

end OEIS

end RealRooted
