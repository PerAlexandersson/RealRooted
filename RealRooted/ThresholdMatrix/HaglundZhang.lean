module

public import RealRooted.ThresholdMatrix.Basic

/-!
# Haglund--Zhang threshold matrices

The `1`/`1 + X` threshold-entry classification, its matrix-preservation
theorem, and the binomial Eulerian recursion.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-! ## Haglund--Zhang threshold matrices -/

namespace HaglundZhang

/-- Haglund--Zhang notation for threshold entries. -/
abbrev entry (t : ℕ) (α : ℝ[X]) (j : ℕ) : ℝ[X] :=
  thresholdEntry t α j

/-- Haglund--Zhang notation for threshold rows. -/
abbrev row (q t : ℕ) (α : ℝ[X]) : List ℝ[X] :=
  thresholdRow q t α

/-- Haglund--Zhang notation for threshold matrices. -/
abbrev matrix (q : ℕ) (rows : List (ℕ × ℝ[X])) : List (List ℝ[X]) :=
  thresholdMatrix q rows

/-- Threshold list for the binomial Eulerian specialization. -/
abbrev binomialThresholds (n : ℕ) : List ℕ :=
  List.range n

lemma binomialThresholds_mono (n : ℕ) :
    ∀ i j : Fin (binomialThresholds n).length, i ≤ j →
      (binomialThresholds n).get i ≤ (binomialThresholds n).get j := by
  intro i j hij
  simp only [binomialThresholds, List.get_eq_getElem, List.getElem_range]
  exact hij

/-- Diagonal marker for the binomial Eulerian specialization. -/
abbrev binomialMarker (t : ℕ) : ℝ[X] :=
  if t = 0 then 1 + X else 1

/-- Row data for the binomial Eulerian specialization: the zeroth marker is
`1 + X`, and every other marker is `1`. -/
abbrev binomialRows (ts : List ℕ) : List (ℕ × ℝ[X]) :=
  ts.map (fun t => (t, binomialMarker t))

/-- Matrix for the binomial Eulerian specialization. -/
abbrev binomialMatrix (q : ℕ) (ts : List ℕ) : List (List ℝ[X]) :=
  matrix q (binomialRows ts)

/-- The one-row terminal data for `(1 + X) f₀ + f₁ + ...`. -/
abbrev terminalRows : List (ℕ × ℝ[X]) :=
  [(0, (1 + X : ℝ[X]))]

/-- The one-row terminal matrix for `(1 + X) f₀ + f₁ + ...`. -/
abbrev terminalMatrix (q : ℕ) : List (List ℝ[X]) :=
  matrix q terminalRows

/-- Haglund--Zhang terminal polynomial `(1 + X) f₀ + f₁ + ...`.

The length parameter is kept explicit so this is literally the action of the
terminal threshold row of width `q`. -/
def terminalPolynomial (q : ℕ) (fs : List ℝ[X]) : ℝ[X] :=
  ((row q 0 (1 + X)).zipWith (· * ·) fs).sum

private lemma thresholdRow_zero_one_add_X (q : ℕ) :
    thresholdRow q 0 (1 + X : ℝ[X]) =
      if q = 0 then [] else (1 + X) :: List.replicate (q - 1) 1 := by
  cases q with
  | zero => simp [thresholdRow]
  | succ q =>
      simp only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
      apply List.ext_get
      · simp
      · intro i hi₁ hi₂
        rw [show (thresholdRow (q + 1) 0 (1 + X)).get ⟨i, hi₁⟩ =
            thresholdEntry 0 (1 + X) i by
              exact get_thresholdRow ⟨i, hi₁⟩]
        cases i with
        | zero => simp
        | succ i => simp [thresholdEntry]

private lemma replicate_one_zipWith_sum (fs : List ℝ[X]) :
    ((List.replicate fs.length 1).zipWith (fun x₁ x₂ ↦ x₁ * x₂) fs).sum =
      fs.sum := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
      simp only [List.length_cons, List.replicate_succ,
        List.zipWith_cons_cons, one_mul, List.sum_cons]
      rw [ih]

/-- The terminal row adds `X` times the first entry to the ordinary row sum. -/
theorem terminalPolynomial_cons (f : ℝ[X]) (fs : List ℝ[X]) :
    terminalPolynomial (f :: fs).length (f :: fs) =
      (f :: fs).sum + X * f := by
  rw [terminalPolynomial]
  change
    ((thresholdRow (f :: fs).length 0 (1 + X)).zipWith
      (fun x₁ x₂ ↦ x₁ * x₂) (f :: fs)).sum = _
  rw [thresholdRow_zero_one_add_X]
  simp only [List.length_cons, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one,
    List.zipWith_cons_cons, List.sum_cons]
  rw [replicate_one_zipWith_sum]
  ring

@[simp] lemma length_binomialRows (ts : List ℕ) :
    (binomialRows ts).length = ts.length := by
  simp [binomialRows]

@[simp] lemma length_binomialMatrix (q : ℕ) (ts : List ℕ) :
    (binomialMatrix q ts).length = ts.length := by
  simp [binomialMatrix]

@[simp] lemma length_terminalRows :
    terminalRows.length = 1 := by
  simp [terminalRows]

@[simp] lemma length_terminalMatrix (q : ℕ) :
    (terminalMatrix q).length = 1 := by
  simp [terminalMatrix]

/-- Validity data for a Haglund--Zhang threshold matrix. -/
structure RowData (rows : List (ℕ × ℝ[X])) : Prop where
  /-- Every diagonal marker is `1` or `1 + X`. -/
  alpha_mem : ∀ p ∈ rows, p.2 = 1 ∨ p.2 = 1 + X
  /-- Thresholds are nondecreasing down the rows. -/
  thresh_mono : ∀ i j : Fin rows.length, i ≤ j → (rows.get i).1 ≤ (rows.get j).1
  /-- Equal-threshold compatibility in the matrix orientation. -/
  compat : ∀ i j : Fin rows.length, i ≤ j → (rows.get i).1 = (rows.get j).1 →
    (rows.get i).2 = 1 + X → (rows.get j).2 = 1 + X

lemma RowData.alpha_nonneg {rows : List (ℕ × ℝ[X])} (h : RowData rows) :
    ∀ p ∈ rows, HasNonnegCoeffs p.2 := by
  intro p hp
  rcases h.alpha_mem p hp with hα | hα <;> rw [hα]
  · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one
  · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one_add_X

lemma binomialRows_rowData {ts : List ℕ}
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j) :
    RowData (binomialRows ts) := by
  constructor
  · intro p hp
    simp only [binomialRows, List.mem_map] at hp
    obtain ⟨t, _, rfl⟩ := hp
    by_cases ht : t = 0
    · exact Or.inr (by simp [binomialMarker, ht])
    · exact Or.inl (by simp [binomialMarker, ht])
  · intro i j hij
    let i' : Fin ts.length := ⟨i.1, by simpa using i.2⟩
    let j' : Fin ts.length := ⟨j.1, by simpa using j.2⟩
    have hij' : i' ≤ j' := hij
    have hkey := hmono i' j' hij'
    simpa [binomialRows, List.get_eq_getElem, i', j'] using hkey
  · intro i j _ heq hi
    simp only [binomialRows, List.get_eq_getElem, List.getElem_map] at heq hi ⊢
    simpa [binomialMarker, heq] using hi

lemma terminalRows_rowData :
    RowData terminalRows := by
  constructor
  · intro p hp
    have hp' : p = (0, (1 + X : ℝ[X])) := by simpa [terminalRows] using hp
    subst p
    exact Or.inr rfl
  · intro i j _
    simp [terminalRows]
  · intro i j _ _ _
    simp [terminalRows]

@[simp] lemma matPolyAction_terminalMatrix (q : ℕ) (fs : List ℝ[X]) :
    matPolyAction (terminalMatrix q) fs = [terminalPolynomial q fs] := by
  simp [terminalPolynomial, terminalMatrix, terminalRows, matrix,
    thresholdMatrix, matPolyAction]

@[simp] lemma sum_matPolyAction_terminalMatrix (q : ℕ) (fs : List ℝ[X]) :
    (matPolyAction (terminalMatrix q) fs).sum = terminalPolynomial q fs := by
  simp

lemma terminalPolynomial_mem_matPolyAction (q : ℕ) (fs : List ℝ[X]) :
    terminalPolynomial q fs ∈ matPolyAction (terminalMatrix q) fs := by
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

private lemma interl_hz_linear_to_quadratic_of_eval_nonpos
    {f F : ℝ[X]}
    (hfdeg : f.natDegree = 1)
    (hFdeg : F.natDegree = 2)
    (hF_splits : F.Splits)
    (hF_pos : HasPosLeadingCoeff F)
    (hroot_nonpos : ∀ r, f.IsRoot r → F.eval r ≤ 0) :
    Interl f F := by
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
    (strictInterl_of_interlaces_eval_mul_nonpos_of_no_common
      hInter hasPosLeadingCoeff_one hF_ne hF_splits hF_pos
      (by lia) (by lia) hno hroot).toInterl

private lemma interl_hz_affine_add_one_affine_add_one_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t + 1) (C s * X + C t + (1 + X)) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
    C (s + 1) * X + C (t + 1) by grind]
  exact
    interl_affine_linear_affine_linear_of_cross
      (u := s) (v := t + 1) (U := s + 1) (V := t + 1)
      hs (by positivity) (by nlinarith [ht])

private lemma interl_hz_affine_add_one_add_X_self {s t : ℝ} (hs : 0 < s) :
    Interl (C s * X + C t + (1 + X)) (C s * X + C t + (1 + X)) := by
  rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
    C (s + 1) * X + C (t + 1) by grind]
  exact Interl.refl fun _ =>
    (isRealRooted_affine_factor (s := s + 1) (t := t + 1) (by positivity)).2

private lemma interl_hz_affine_add_one_add_X_affine_add_X
    {s t : ℝ} (hs : 0 < s) :
    Interl (C s * X + C t + (1 + X)) (C s * X + C t + X) := by
  rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
    C (s + 1) * X + C (t + 1) by grind]
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    interl_affine_linear_affine_linear_of_cross
      (u := s + 1) (v := t + 1) (U := s + 1) (V := t)
      (by positivity) (by positivity) (by nlinarith)

private lemma interl_hz_affine_add_one_middleQuadratic
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t + 1) ((C s * X + C t) * (1 + X) + X) := by
  apply interl_hz_linear_to_quadratic_of_eval_nonpos
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

private lemma interl_hz_affine_add_one_add_X_middleQuadratic
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t + (1 + X)) ((C s * X + C t) * (1 + X) + X) := by
  apply interl_hz_linear_to_quadratic_of_eval_nonpos
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

private lemma interl_hz_affine_add_X_middleQuadratic
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t + X) ((C s * X + C t) * (1 + X) + X) := by
  apply interl_hz_linear_to_quadratic_of_eval_nonpos
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

private lemma interl_hz_affine_add_one_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t + 1) (X * (C s * X + C t + 1)) := by
  have hf_rr :
      ((C s * X + C t + 1 : ℝ[X]) ≠ 0 ∧
        (C s * X + C t + 1 : ℝ[X]).Splits) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact isRealRooted_affine_factor (s := s) (t := t + 1) hs
  have hf_nn : HasNonnegCoeffs (C s * X + C t + 1 : ℝ[X]) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact hasNonnegCoeffs_affine_linear hs.le (by nlinarith)
  simpa using (strictInterl_self_X_mul_of_nonneg hf_rr.1 hf_rr.2 hf_nn).toInterl

private lemma interl_hz_affine_add_one_add_X_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t + (1 + X)) (X * (C s * X + C t + 1)) := by
  apply interl_hz_linear_to_quadratic_of_eval_nonpos
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

private lemma interl_hz_affine_add_X_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t + X) (X * (C s * X + C t + 1)) := by
  apply interl_hz_linear_to_quadratic_of_eval_nonpos
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

private lemma interl_hz_affine_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t) (X * (C s * X + C t + 1)) := by
  apply interl_hz_linear_to_quadratic_of_eval_nonpos
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

private lemma interl_hz_affine_add_one_mul_one_add_X
    {s t : ℝ} (hs : 0 < s) :
    Interl (C s * X + C t + 1) ((C s * X + C t + 1) * (1 + X)) := by
  have hd_rr :
      ((C s * X + C t + 1 : ℝ[X]) ≠ 0 ∧
        (C s * X + C t + 1 : ℝ[X]).Splits) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact isRealRooted_affine_factor (s := s) (t := t + 1) hs
  have hbase : StrictInterl (1 : ℝ[X]) (1 + X) := by
    have hdeg : (1 + X : ℝ[X]).natDegree = 1 := by
      simp [show (1 + X : ℝ[X]) = X + C (1 : ℝ) by grind]
    exact (interlaces_one_linear (p := (1 + X : ℝ[X])) hdeg).toStrictInterl
  have hmul := hbase.mul_common_factor hd_rr.1 hd_rr.2
  simpa using hmul.toInterl

private lemma interl_hz_mul_one_add_X_self
    {s t : ℝ} (hs : 0 < s) :
    Interl ((C s * X + C t + 1) * (1 + X)) ((C s * X + C t + 1) * (1 + X)) := by
  have hlin_rr :
      ((C s * X + C t + 1 : ℝ[X]) ≠ 0 ∧
        (C s * X + C t + 1 : ℝ[X]).Splits) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact isRealRooted_affine_factor (s := s) (t := t + 1) hs
  have hS_rr : ((1 + X : ℝ[X]) ≠ 0 ∧ (1 + X : ℝ[X]).Splits) := by
    rw [show (1 + X : ℝ[X]) = C (1 : ℝ) * X + C 1 by grind]
    exact isRealRooted_affine_factor (s := 1) (t := 1) zero_lt_one
  exact Interl.refl fun _ =>
    (isRealRooted_mul hlin_rr.1 hlin_rr.2 hS_rr.1 hS_rr.2).2

private lemma interl_hz_middleQuadratic_self
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl ((C s * X + C t) * (1 + X) + X)
      ((C s * X + C t) * (1 + X) + X) := by
  exact Interl.refl fun _ => hzMiddleQuadratic_splits hs ht

private lemma interl_hz_mul_one_add_X_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) :
    Interl ((C s * X + C t + 1) * (1 + X)) (X * (C s * X + C t + 1)) := by
  have hd_rr :
      ((C s * X + C t + 1 : ℝ[X]) ≠ 0 ∧
        (C s * X + C t + 1 : ℝ[X]).Splits) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact isRealRooted_affine_factor (s := s) (t := t + 1) hs
  have hbase : StrictInterl (1 + X : ℝ[X]) X := by
    rw [show (1 + X : ℝ[X]) = X + 1 by grind]
    simpa using
      strictInterl_affine_linear_affine_linear_of_cross
        (u := 1) (v := 1) (U := 1) (V := 0)
        zero_lt_one zero_lt_one (by norm_num)
  have hmul := hbase.mul_common_factor hd_rr.1 hd_rr.2
  rw [show (X * (C s * X + C t + 1) : ℝ[X]) =
    (C s * X + C t + 1) * X by ring]
  simpa using hmul.toInterl

private lemma interl_hz_XAffineAddOne_self
    {s t : ℝ} (hs : 0 < s) :
    Interl (X * (C s * X + C t + 1)) (X * (C s * X + C t + 1)) := by
  exact Interl.refl fun _ => hzXAffineAddOne_splits hs

private lemma interl_hz_middleQuadratic_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl ((C s * X + C t) * (1 + X) + X) (X * (C s * X + C t + 1)) := by
  have hself : Interl (X * (C s * X + C t + 1)) (X * (C s * X + C t + 1)) :=
    interl_hz_XAffineAddOne_self hs
  have hlin : Interl (C s * X + C t) (X * (C s * X + C t + 1)) :=
    interl_hz_affine_XAffineAddOne hs ht
  have hq_nn : HasNonnegCoeffs (X * (C s * X + C t + 1) : ℝ[X]) := by
    refine hasNonnegCoeffs_X.mul ?_
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact hasNonnegCoeffs_affine_linear hs.le (by nlinarith)
  have hlin_nn : HasNonnegCoeffs (C s * X + C t : ℝ[X]) :=
    hasNonnegCoeffs_affine_linear hs.le ht.le
  have hsum :=
    interl_add_left_of_common_right_of_nonneg hself hlin hq_nn hlin_nn
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
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
  · simpa using interl_affine_add_one_self hs
  · simpa using interl_hz_affine_add_one_affine_add_one_add_X hs ht
  · simpa using interl_hz_affine_add_one_add_X_self hs
  · simpa using interl_affine_add_one_affine_add_X hs ht
  · simpa using interl_hz_affine_add_one_add_X_affine_add_X hs
  · simpa using interl_affine_add_X_self hs
  · simpa [mul_add, add_mul, add_assoc, add_comm, add_left_comm] using
      interl_hz_affine_add_one_mul_one_add_X hs
  · simpa using interl_hz_affine_add_one_middleQuadratic hs ht
  · simpa using interl_hz_affine_add_one_add_X_middleQuadratic hs ht
  · simpa using interl_hz_affine_add_X_middleQuadratic hs ht
  · simpa [mul_add, add_mul, add_assoc, add_comm, add_left_comm] using
      interl_hz_mul_one_add_X_self hs
  · simpa using interl_hz_middleQuadratic_self hs ht
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using interl_hz_affine_add_one_XAffineAddOne hs ht
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using interl_hz_affine_add_one_add_X_XAffineAddOne hs ht
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using interl_hz_affine_add_X_XAffineAddOne hs ht
  · rw [show ((C s * X + C t) * (1 + X) + (1 + X) : ℝ[X]) =
        (C s * X + C t + 1) * (1 + X) by grind]
    rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using interl_hz_mul_one_add_X_XAffineAddOne hs
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using interl_hz_middleQuadratic_XAffineAddOne hs ht
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using interl_hz_XAffineAddOne_self hs

private lemma hzEntry_shape
    {t₁ t₂ j₁ j₂ : ℕ} {α₁ α₂ : ℝ[X]}
    (hα₁ : α₁ = 1 ∨ α₁ = 1 + X)
    (hα₂ : α₂ = 1 ∨ α₂ = 1 + X)
    (ht : t₁ ≤ t₂) (hj : j₁ ≤ j₂)
    (hcompat : t₁ = t₂ → α₁ = 1 + X → α₂ = 1 + X) :
    HZ2x2EntryShape
      (entry t₁ α₁ j₁) (entry t₁ α₁ j₂)
      (entry t₂ α₂ j₁) (entry t₂ α₂ j₂) := by
  rcases hα₁ with rfl | rfl <;> rcases hα₂ with rfl | rfl <;>
    simp at hcompat <;>
    unfold HZ2x2EntryShape Threshold2x2EntryTuple <;>
    simp only [thresholdEntry] <;>
    split_ifs <;>
    lia

/-- The finite entrywise Haglund--Zhang `2 x 2` threshold check. -/
theorem has2x2InterlacingProperty0_entry {t₁ t₂ j₁ j₂ : ℕ} {α₁ α₂ : ℝ[X]}
    (hα₁ : α₁ = 1 ∨ α₁ = 1 + X) (hα₂ : α₂ = 1 ∨ α₂ = 1 + X)
    (ht : t₁ ≤ t₂) (hj : j₁ ≤ j₂)
    (hcompat : t₁ = t₂ → α₁ = 1 + X → α₂ = 1 + X) :
    Has2x2InterlacingProperty0
      (entry t₁ α₁ j₁) (entry t₁ α₁ j₂)
      (entry t₂ α₂ j₁) (entry t₂ α₂ j₂) :=
  (hzEntry_shape hα₁ hα₂ ht hj hcompat).has2x2

lemma RowData.entry_has2x2 {q : ℕ} {rows : List (ℕ × ℝ[X])}
    (hrows : RowData rows) :
    ∀ (i₁ i₂ : Fin rows.length) (j₁ j₂ : Fin q),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (entry (rows.get i₁).1 (rows.get i₁).2 j₁.1)
        (entry (rows.get i₁).1 (rows.get i₁).2 j₂.1)
        (entry (rows.get i₂).1 (rows.get i₂).2 j₁.1)
        (entry (rows.get i₂).1 (rows.get i₂).2 j₂.1) := by
  intro i₁ i₂ j₁ j₂ hi hj
  exact has2x2InterlacingProperty0_entry
    (hrows.alpha_mem (rows.get i₁) (List.get_mem rows i₁))
    (hrows.alpha_mem (rows.get i₂) (List.get_mem rows i₂))
    (hrows.thresh_mono i₁ i₂ hi)
    hj
    (hrows.compat i₁ i₂ hi)

/-- Haglund--Zhang threshold matrices preserve nonnegative interlacing
sequences. -/
theorem isInterlacingSeq0Nonneg_matPolyAction
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : RowData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (matrix q rows) fs) :=
  thresholdMatrix_preserves_interlacing_seq0_of_entry rows
    hrows.alpha_nonneg hrows.entry_has2x2 fs hfs_len hfs

theorem isInterlacingSeq0Nonneg_matPolyAction_and_realRooted
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : RowData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (matrix q rows) fs) ∧
      ∀ f ∈ matPolyAction (matrix q rows) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  thresholdMatrix_preserves_interlacing_seq0_of_entry_weak rows
    hrows.alpha_nonneg hrows.entry_has2x2 fs hfs_len hfs hfs_real

theorem isRealRooted_sum_matPolyAction
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : RowData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne : (matPolyAction (matrix q rows) fs).sum ≠ 0) :
    (matPolyAction (matrix q rows) fs).sum ≠ 0 ∧
      ((matPolyAction (matrix q rows) fs).sum).Splits := by
  have hout :=
    isInterlacingSeq0Nonneg_matPolyAction_and_realRooted
      rows hrows fs hfs_len hfs hfs_real
  exact isRealRooted_sum_of_isInterlacingSeq0Nonneg hout.1 hout.2 hsum_ne

theorem isRealRooted_terminalPolynomial
    {q : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hterminal_ne : terminalPolynomial q fs ≠ 0) :
    terminalPolynomial q fs ≠ 0 ∧ (terminalPolynomial q fs).Splits := by
  have hout :=
    isInterlacingSeq0Nonneg_matPolyAction_and_realRooted
      terminalRows terminalRows_rowData fs hfs_len hfs hfs_real
  exact hout.2 (terminalPolynomial q fs)
    (terminalPolynomial_mem_matPolyAction q fs) hterminal_ne

theorem isRealRooted_terminalPolynomial_of_interlacing
    {q : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs)
    (hterminal_ne : terminalPolynomial q fs ≠ 0) :
    terminalPolynomial q fs ≠ 0 ∧ (terminalPolynomial q fs).Splits := by
  have hfs_weak := weakData_of_isInterlacingSeqNonneg hfs
  exact isRealRooted_terminalPolynomial
    fs hfs_len hfs_weak.1 hfs_weak.2 hterminal_ne

/-- Binomial Eulerian specialization: all diagonal markers are `1 + X`. -/
theorem isInterlacingSeq0Nonneg_binomialMatrix
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (binomialMatrix q ts) fs) :=
  isInterlacingSeq0Nonneg_matPolyAction _
    (binomialRows_rowData hmono) fs hfs_len hfs

theorem isInterlacingSeq0Nonneg_binomialMatrix_binomialThresholds
    {q n : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (binomialMatrix q (binomialThresholds n)) fs) :=
  isInterlacingSeq0Nonneg_binomialMatrix
    (binomialThresholds n) (binomialThresholds_mono n) fs hfs_len hfs

theorem isInterlacingSeq0Nonneg_binomialMatrix_and_realRooted
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (binomialMatrix q ts) fs) ∧
      ∀ f ∈ matPolyAction (binomialMatrix q ts) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  isInterlacingSeq0Nonneg_matPolyAction_and_realRooted
    _ (binomialRows_rowData hmono) fs hfs_len hfs hfs_real

theorem isInterlacingSeq0Nonneg_binomialMatrix_binomialThresholds_and_realRooted
    {q n : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (binomialMatrix q (binomialThresholds n)) fs) ∧
      ∀ f ∈ matPolyAction (binomialMatrix q (binomialThresholds n)) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  isInterlacingSeq0Nonneg_binomialMatrix_and_realRooted
    (binomialThresholds n) (binomialThresholds_mono n)
    fs hfs_len hfs hfs_real

theorem isRealRooted_sum_binomialMatrix
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne :
      (matPolyAction (binomialMatrix q ts) fs).sum ≠ 0) :
    (matPolyAction (binomialMatrix q ts) fs).sum ≠ 0 ∧
      ((matPolyAction (binomialMatrix q ts) fs).sum).Splits := by
  have hout :=
    isInterlacingSeq0Nonneg_binomialMatrix_and_realRooted
      ts hmono fs hfs_len hfs hfs_real
  exact isRealRooted_sum_of_isInterlacingSeq0Nonneg hout.1 hout.2 hsum_ne

theorem isRealRooted_sum_binomialMatrix_binomialThresholds
    {q n : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne :
      (matPolyAction (binomialMatrix q (binomialThresholds n)) fs).sum ≠ 0) :
    (matPolyAction (binomialMatrix q (binomialThresholds n)) fs).sum ≠ 0 ∧
      ((matPolyAction (binomialMatrix q (binomialThresholds n)) fs).sum).Splits :=
  isRealRooted_sum_binomialMatrix
    (binomialThresholds n) (binomialThresholds_mono n)
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
  simp only [thresholdEntry, hzConstEntry]
  split_ifs <;> simp

private lemma coeff_zero_thresholdEntry_binomialMarker (t j : ℕ) :
    (thresholdEntry t (binomialMarker t) j).coeff 0 = hzConstEntry t j := by
  by_cases ht : t = 0
  · simp [binomialMarker, ht, coeff_zero_thresholdEntry_one_add_X]
  · simp only [binomialMarker, ht, ite_false, thresholdEntry, hzConstEntry]
    split_ifs <;> simp

private lemma coeff_zero_hzBinomialMatrix (q n : ℕ) :
    (binomialMatrix q (binomialThresholds n)).map
      (fun row => row.map (fun p => p.coeff 0)) =
      hzConstMatrix q n := by
  simp [binomialMatrix, binomialThresholds, binomialRows, matrix,
    thresholdMatrix, thresholdRow, coeff_zero_thresholdEntry_binomialMarker,
    hzConstMatrix, hzConstRow]

private lemma coeff_zero_hzTerminalRow (q : ℕ) :
    (row q 0 (1 + X)).map (fun p => p.coeff 0) =
      hzConstRow q 0 := by
  simp [row, thresholdRow, hzConstRow, coeff_zero_thresholdEntry_one_add_X]

private lemma coeff_zero_hzTerminalPolynomial (q : ℕ) (fs : List ℝ[X]) :
    (terminalPolynomial q fs).coeff 0 =
      ((hzConstRow q 0).zipWith (· * ·)
        (fs.map (fun p => p.coeff 0))).sum := by
  rw [terminalPolynomial, coeff_zero_zipWith, coeff_zero_hzTerminalRow]

/-- The refined binomial Eulerian vector in the Haglund--Zhang recursion.

The vector has length `n + 1`.  The transition from `n` to `n + 1` has width
`n + 1` and `n + 2` threshold rows. -/
def binomialRefined : ℕ → List ℝ[X]
  | 0 => [1]
  | n + 1 =>
      matPolyAction
        (binomialMatrix (n + 1) (binomialThresholds (n + 2)))
        (binomialRefined n)

@[simp] theorem length_binomialRefined (n : ℕ) :
    (binomialRefined n).length = n + 1 := by
  induction n with
  | zero =>
      simp [binomialRefined]
  | succ n =>
      simp [binomialRefined]

@[simp] lemma mem_binomialRefined_zero {f : ℝ[X]} :
    f ∈ binomialRefined 0 ↔ f = 1 := by
  simp [binomialRefined]

theorem coeff_zero_binomialRefined (n : ℕ) :
    (binomialRefined n).map (fun p => p.coeff 0) =
      1 :: List.replicate n 0 := by
  induction n with
  | zero =>
      simp [binomialRefined]
  | succ n ih =>
      simp [binomialRefined, coeff_zero_matPolyAction,
        coeff_zero_hzBinomialMatrix, ih, realListAction_hzConstMatrix_delta]

lemma binomialRefined_zero_interlacing :
    IsInterlacingSeq0Nonneg (binomialRefined 0) := by
  constructor
  · simp [binomialRefined, IsInterlacingSeq0]
  · intro f hf
    have hf' : f = 1 := mem_binomialRefined_zero.mp hf
    subst f
    exact hasNonnegCoeffs_one

lemma binomialRefined_zero_splits :
    ∀ f ∈ binomialRefined 0, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  intro f hf _
  have hf' : f = 1 := mem_binomialRefined_zero.mp hf
  subst f
  exact ⟨one_ne_zero, Polynomial.Splits.one⟩

theorem binomialRefined_interlacing_and_realRooted (n : ℕ) :
    IsInterlacingSeq0Nonneg (binomialRefined n) ∧
      ∀ f ∈ binomialRefined n, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  induction n with
  | zero =>
      exact ⟨binomialRefined_zero_interlacing, binomialRefined_zero_splits⟩
  | succ n ih =>
      simpa [binomialRefined] using
        isInterlacingSeq0Nonneg_binomialMatrix_binomialThresholds_and_realRooted
          (q := n + 1) (n := n + 2) (fs := binomialRefined n)
          (by simp)
          ih.1 ih.2

/-- Interlacing projection from the Haglund--Zhang refined-vector induction. -/
theorem binomialRefined_interlaces (n : ℕ) :
    IsInterlacingSeq0Nonneg (binomialRefined n) :=
  (binomialRefined_interlacing_and_realRooted n).1

/-- Real-rootedness projection from the Haglund--Zhang refined-vector induction. -/
theorem binomialRefined_realRooted (n : ℕ) :
    ∀ f ∈ binomialRefined n, f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  (binomialRefined_interlacing_and_realRooted n).2

/-- The terminal binomial Eulerian polynomial obtained from the refined vector. -/
def binomialEulerianPolynomial (n : ℕ) : ℝ[X] :=
  terminalPolynomial (n + 1) (binomialRefined n)

@[simp] theorem coeff_zero_binomialEulerianPolynomial (n : ℕ) :
    (binomialEulerianPolynomial n).coeff 0 = 1 := by
  rw [binomialEulerianPolynomial, coeff_zero_hzTerminalPolynomial,
    coeff_zero_binomialRefined]
  simp [realListAction_hzConstRow_delta]

theorem binomialEulerianPolynomial_ne_zero (n : ℕ) :
    binomialEulerianPolynomial n ≠ 0 := by
  intro h
  have hcoeff := coeff_zero_binomialEulerianPolynomial n
  rw [h] at hcoeff
  norm_num at hcoeff

theorem binomialEulerianPolynomial_realRooted_of_ne
    (n : ℕ) (hne : binomialEulerianPolynomial n ≠ 0) :
    binomialEulerianPolynomial n ≠ 0 ∧
      (binomialEulerianPolynomial n).Splits := by
  simpa [binomialEulerianPolynomial] using
    isRealRooted_terminalPolynomial
      (q := n + 1) (fs := binomialRefined n)
      (by simp)
      (binomialRefined_interlaces n) (binomialRefined_realRooted n)
      (by simpa [binomialEulerianPolynomial] using hne)

theorem binomialEulerianPolynomial_splits_of_ne
    (n : ℕ) (hne : binomialEulerianPolynomial n ≠ 0) :
    (binomialEulerianPolynomial n).Splits :=
  (binomialEulerianPolynomial_realRooted_of_ne n hne).2

theorem binomialEulerianPolynomial_realRooted (n : ℕ) :
    binomialEulerianPolynomial n ≠ 0 ∧
      (binomialEulerianPolynomial n).Splits :=
  binomialEulerianPolynomial_realRooted_of_ne
    n (binomialEulerianPolynomial_ne_zero n)

theorem binomialEulerianPolynomial_splits (n : ℕ) :
    (binomialEulerianPolynomial n).Splits :=
  (binomialEulerianPolynomial_realRooted n).2

/-- The terminal polynomial is the first entry of the next refined vector. -/
theorem getElem_zero_binomialRefined_succ (n : ℕ) :
    (binomialRefined (n + 1))[0] = binomialEulerianPolynomial n := by
  simp only [binomialRefined, matPolyAction, List.getElem_map, binomialMatrix,
    thresholdMatrix, binomialRows, binomialThresholds, List.getElem_range,
    binomialMarker]
  rfl

/-- Consecutive Haglund--Zhang terminal polynomials are in strict interlacing
position. -/
theorem binomialEulerianPolynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (binomialEulerianPolynomial n)
      (binomialEulerianPolynomial (n + 1)) := by
  let fs := binomialRefined (n + 1)
  let f : ℝ[X] := fs.get ⟨0, by simp [fs]⟩
  have hf_eq : f = binomialEulerianPolynomial n := by
    exact getElem_zero_binomialRefined_succ n
  have hdata := binomialRefined_interlacing_and_realRooted (n + 1)
  have hf_mem : f ∈ fs := List.get_mem fs _
  have hf_ne : f ≠ 0 := by
    rw [hf_eq]
    exact binomialEulerianPolynomial_ne_zero n
  have hf_splits : f.Splits := (hdata.2 f hf_mem hf_ne).2
  have hpair : fs.Pairwise Interl :=
    isInterlacingSeq0_iff_pairwise.mp hdata.1.1
  have hfs_eq : fs = f :: fs.drop 1 := by
    simpa [f] using
      (List.drop_eq_getElem_cons (l := fs) (i := 0) (h := by simp [fs]))
  have hcommon : ∀ p ∈ fs, Interl f p := by
    intro p hp
    rw [hfs_eq] at hp hpair
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (StrictInterl.refl hf_ne hf_splits).toInterl
    · exact (List.pairwise_cons.mp hpair).1 p hp
  have hf_total : Interl f fs.sum :=
    Interl.sum_left_of_common_left_of_nonneg fs f hcommon hdata.1.2
  have hf_nonneg : HasNonnegCoeffs f := hdata.1.2 f hf_mem
  have htotal_nonneg : HasNonnegCoeffs fs.sum :=
    hasNonnegCoeffs_sum fs hdata.1.2
  have hf_X : StrictInterl f (X * f) :=
    strictInterl_self_X_mul_of_nonneg hf_ne hf_splits hf_nonneg
  have hnext : Interl f (fs.sum + X * f) :=
    interl_add_right_of_common_left_of_nonneg hf_total hf_X.toInterl
      htotal_nonneg hf_nonneg.X_mul
  have hterminal :
      binomialEulerianPolynomial (n + 1) = fs.sum + X * f := by
    rw [binomialEulerianPolynomial]
    change terminalPolynomial (n + 2) fs = fs.sum + X * f
    have hlen : fs.length = n + 2 := by simp [fs]
    rw [← hlen]
    change terminalPolynomial fs.length fs = fs.sum + X * f
    rw [hfs_eq, terminalPolynomial_cons]
  have hnext_ne : fs.sum + X * f ≠ 0 := by
    rw [← hterminal]
    exact binomialEulerianPolynomial_ne_zero (n + 1)
  rw [← hf_eq, hterminal]
  exact hnext.toStrictInterl_of_ne hf_ne hnext_ne

end HaglundZhang

namespace OEIS

namespace Backend

@[deprecated (since := "2026-10-06")] alias HZData := HaglundZhang.RowData
@[deprecated (since := "2026-10-06")] alias hzRow := HaglundZhang.row
@[deprecated (since := "2026-10-06")] alias hzMatrix := HaglundZhang.matrix
@[deprecated (since := "2026-10-06")] alias hzBinomialMatrix := HaglundZhang.binomialMatrix
@[deprecated (since := "2026-10-06")] alias hzTerminalPolynomial :=
  HaglundZhang.terminalPolynomial
@[deprecated (since := "2026-10-06")] alias haglund_zhang_s_inversion_interlacing_weak :=
  HaglundZhang.isInterlacingSeq0Nonneg_matPolyAction_and_realRooted
@[deprecated (since := "2026-10-06")] alias haglund_zhang_binomial_eulerian_weak :=
  HaglundZhang.isInterlacingSeq0Nonneg_binomialMatrix_and_realRooted
@[deprecated (since := "2026-10-06")] alias haglund_zhang_terminal_polynomial_realRooted :=
  HaglundZhang.isRealRooted_terminalPolynomial

end Backend

end OEIS

end RealRooted
