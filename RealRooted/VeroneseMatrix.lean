import RealRooted.MatrixInterlacing
import RealRooted.VeroneseSection

/-!
# Matrix form of the Veronese linear-factor recursion

This file packages the Wagner-style matrix route for Veronese sections.  The
important point is to list the sections in the order
`S_{r-1}, S_{r-2}, ..., S_0`; in that order the multiplication-by-`X + a`
recursion is given by a cyclic bidiagonal matrix with its `X` entry in the
lower-left corner.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-! ## Lists and the cyclic matrix -/

/-- Veronese sections in descending residue order:
`[S_{r-1} p, S_{r-2} p, ..., S_0 p]`. -/
def veroneseSectionPolynomialListDesc (r : ℕ) (p : ℝ[X]) : List ℝ[X] :=
  List.ofFn fun i : Fin r => veroneseSectionPolynomial r (r - 1 - i.1) p

@[simp] theorem length_veroneseSectionPolynomialListDesc (r : ℕ) (p : ℝ[X]) :
    (veroneseSectionPolynomialListDesc r p).length = r := by
  simp [veroneseSectionPolynomialListDesc]

@[simp] theorem get_veroneseSectionPolynomialListDesc
    {r : ℕ} (p : ℝ[X]) (i : Fin r) :
    (veroneseSectionPolynomialListDesc r p).get
        ⟨i.1, by simp [length_veroneseSectionPolynomialListDesc]⟩ =
      veroneseSectionPolynomial r (r - 1 - i.1) p := by
  simp [veroneseSectionPolynomialListDesc]

/-- The row of the descending-order cyclic matrix for multiplication by
`X + a`.

For row `i < r - 1`, this has entries `C a` at column `i` and `1` at column
`i + 1`.  In the last row it has entries `C a` at the last column and `X` at
column `0`.  For `r = 1`, these contributions add to the single entry
`X + C a`. -/
def veroneseLinearFactorRowDesc (r : ℕ) (a : ℝ) (i : Fin r) : List ℝ[X] :=
  ((oneSupportSeq r i).map fun q => C a * q).zipWith (· + ·)
    (if hi : i.1 + 1 < r then
      oneSupportSeq r ⟨i.1 + 1, hi⟩
    else
      (oneSupportSeq r ⟨0, by omega⟩).map fun q => X * q)

/-- The descending-order cyclic matrix for multiplication by `X + a`. -/
def veroneseLinearFactorMatrixDesc (r : ℕ) (a : ℝ) : List (List ℝ[X]) :=
  List.ofFn fun i : Fin r => veroneseLinearFactorRowDesc r a i

@[simp] theorem length_veroneseLinearFactorMatrixDesc (r : ℕ) (a : ℝ) :
    (veroneseLinearFactorMatrixDesc r a).length = r := by
  simp [veroneseLinearFactorMatrixDesc]

@[simp] theorem length_veroneseLinearFactorRowDesc
    {r : ℕ} (a : ℝ) (i : Fin r) :
    (veroneseLinearFactorRowDesc r a i).length = r := by
  by_cases hi : i.1 + 1 < r
  · simp [veroneseLinearFactorRowDesc, hi]
  · simp [veroneseLinearFactorRowDesc, hi]

@[simp] theorem get_veroneseLinearFactorMatrixDesc
    {r : ℕ} (a : ℝ) (i : Fin r) :
    (veroneseLinearFactorMatrixDesc r a).get
        ⟨i.1, by simp [length_veroneseLinearFactorMatrixDesc]⟩ =
      veroneseLinearFactorRowDesc r a i := by
  simp [veroneseLinearFactorMatrixDesc]

theorem get_veroneseLinearFactorRowDesc
    {r : ℕ} (a : ℝ) (i j : Fin r) :
    (veroneseLinearFactorRowDesc r a i).get
        ⟨j.1, by simp [length_veroneseLinearFactorRowDesc]⟩ =
      C a * (if j = i then (1 : ℝ[X]) else 0) +
        (if hi : i.1 + 1 < r then
          (if j = ⟨i.1 + 1, hi⟩ then (1 : ℝ[X]) else 0)
        else
          (if j = ⟨0, by omega⟩ then X else 0)) := by
  by_cases hi : i.1 + 1 < r
  · simp [veroneseLinearFactorRowDesc, hi, oneSupportSeq]
  · simp [veroneseLinearFactorRowDesc, hi, oneSupportSeq]

/-! ## Small list-sum helpers -/

lemma zipWith_mul_sum_comm (xs ys : List ℝ[X]) :
    (xs.zipWith (· * ·) ys).sum = (ys.zipWith (· * ·) xs).sum := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp
  | cons x xs ih =>
      cases ys with
      | nil => simp
      | cons y ys =>
          simp [ih ys, mul_comm]

lemma zipWith_mul_sum_zipWith_add_left
    (xs ys fs : List ℝ[X])
    (hxs : xs.length = fs.length) (hys : ys.length = fs.length) :
    (((xs.zipWith (· + ·) ys).zipWith (· * ·) fs).sum)
      = ((xs.zipWith (· * ·) fs).sum) + ((ys.zipWith (· * ·) fs).sum) := by
  rw [zipWith_mul_sum_comm (xs.zipWith (· + ·) ys) fs]
  rw [zipWith_mul_sum_zipWith_add_right fs xs ys hxs hys]
  rw [zipWith_mul_sum_comm fs xs, zipWith_mul_sum_comm fs ys]

lemma zipWith_mul_scaled_oneSupportSeq_sum_eq_get
    (fs : List ℝ[X]) (i : Fin fs.length) (c : ℝ[X]) :
    ((((oneSupportSeq fs.length i).map fun q => c * q).zipWith (· * ·) fs).sum)
      = c * fs.get i := by
  rw [zipWith_mul_sum_comm]
  rw [zipWith_mul_sum_map_mul_right]
  simp [zipWith_mul_oneSupportSeq_sum_eq_get]

lemma zipWith_mul_oneSupportSeq_left_sum_eq_get
    (fs : List ℝ[X]) (i : Fin fs.length) :
    (((oneSupportSeq fs.length i).zipWith (· * ·) fs).sum) = fs.get i := by
  rw [zipWith_mul_sum_comm]
  exact zipWith_mul_oneSupportSeq_sum_eq_get fs i

/-! ## Elementary affine interlacing helpers -/

lemma prec0_C_C (a b : ℝ) : Prec0 (C a : ℝ[X]) (C b : ℝ[X]) := by
  by_cases ha : a = 0
  · left
    simp [ha]
  by_cases hb : b = 0
  · right
    left
    simp [hb]
  right
  right
  have hCa : (C a : ℝ[X]) ≠ 0 := C_ne_zero.mpr ha
  have hCb : (C b : ℝ[X]) ≠ 0 := C_ne_zero.mpr hb
  have hrr_a : IsRealRooted (C a : ℝ[X]) := isRealRooted_of_deg_zero hCa (by simp)
  have hrr_b : IsRealRooted (C b : ℝ[X]) := isRealRooted_of_deg_zero hCb (by simp)
  refine ⟨hrr_a, hrr_b, [], [], by simp, by simp, ?_, ?_, ?_⟩
  · exact (Polynomial.roots_C a).symm
  · exact (Polynomial.roots_C b).symm
  · exact Or.inr ⟨by simp, by simp [ListAlternates]⟩

lemma prec0_C_affine_linear {c u v : ℝ} (hu : 0 < u) :
    Prec0 (C c : ℝ[X]) (C u * X + C v) := by
  by_cases hc : c = 0
  · left
    simp [hc]
  right
  right
  have hC : (C c : ℝ[X]) ≠ 0 := C_ne_zero.mpr hc
  have hlin_rr : IsRealRooted (C u * X + C v : ℝ[X]) :=
    isRealRooted_affine_factor (s := u) (t := v) hu
  have hlin_nat : (C u * X + C v : ℝ[X]).natDegree = 1 := by
    simpa [add_comm] using Polynomial.natDegree_linear (a := u) (b := v) hu.ne'
  have hlin_deg : (C u * X + C v : ℝ[X]).degree = 1 := by
    rw [degree_eq_natDegree hlin_rr.1, hlin_nat]
    norm_num
  have hC_rr : IsRealRooted (C c : ℝ[X]) := isRealRooted_of_deg_zero hC (by simp)
  refine ⟨hC_rr, hlin_rr, [], [-(u⁻¹ * v)], by simp, by simp, ?_, ?_, ?_⟩
  · exact (Polynomial.roots_C c).symm
  · simpa [hlin_deg] using
      (Polynomial.roots_degree_eq_one (p := (C u * X + C v : ℝ[X])) hlin_deg).symm
  · exact Or.inl ⟨by simp, by simp [ListInterlaces]⟩

lemma affineLinear_root_le_of_cross {u v U V : ℝ}
    (hu : 0 < u) (hU : 0 < U) (hcross : u * V ≤ U * v) :
    -(u⁻¹ * v) ≤ -(U⁻¹ * V) := by
  rw [neg_le_neg_iff]
  rw [← div_eq_inv_mul, ← div_eq_inv_mul]
  rw [div_le_div_iff₀ hU hu]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcross

lemma prec_affine_linear_affine_linear_of_cross
    {u v U V : ℝ} (hu : 0 < u) (hU : 0 < U)
    (hcross : u * V ≤ U * v) :
    Prec (C u * X + C v) (C U * X + C V) := by
  have hroot : -(u⁻¹ * v) ≤ -(U⁻¹ * V) :=
    affineLinear_root_le_of_cross hu hU hcross
  have hp_nat : (C u * X + C v : ℝ[X]).natDegree = 1 := by
    simpa [add_comm] using Polynomial.natDegree_linear (a := u) (b := v) hu.ne'
  have hq_nat : (C U * X + C V : ℝ[X]).natDegree = 1 := by
    simpa [add_comm] using Polynomial.natDegree_linear (a := U) (b := V) hU.ne'
  have hp_rr : IsRealRooted (C u * X + C v : ℝ[X]) :=
    isRealRooted_affine_factor (s := u) (t := v) hu
  have hq_rr : IsRealRooted (C U * X + C V : ℝ[X]) :=
    isRealRooted_affine_factor (s := U) (t := V) hU
  have hp_deg : (C u * X + C v : ℝ[X]).degree = 1 := by
    rw [degree_eq_natDegree hp_rr.1, hp_nat]
    norm_num
  have hq_deg : (C U * X + C V : ℝ[X]).degree = 1 := by
    rw [degree_eq_natDegree hq_rr.1, hq_nat]
    norm_num
  refine ⟨hp_rr, hq_rr, [-(u⁻¹ * v)], [-(U⁻¹ * V)], by simp, by simp, ?_, ?_, ?_⟩
  · simpa [hp_deg] using
      (Polynomial.roots_degree_eq_one (p := (C u * X + C v : ℝ[X])) hp_deg).symm
  · simpa [hq_deg] using
      (Polynomial.roots_degree_eq_one (p := (C U * X + C V : ℝ[X])) hq_deg).symm
  · exact Or.inr ⟨by simp, by simpa [ListAlternates, ListInterlaces] using hroot⟩

lemma prec0_affine_linear_affine_linear_of_cross
    {u v U V : ℝ} (hu : 0 < u) (hU : 0 < U)
    (hcross : u * V ≤ U * v) :
    Prec0 (C u * X + C v) (C U * X + C V) :=
  (prec_affine_linear_affine_linear_of_cross hu hU hcross).toPrec0

lemma prec0_C_mul_affine_linear_X_mul_affine_linear
    {a u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) :
    Prec0 (C a * (C u * X + C v)) (X * (C u * X + C v)) := by
  by_cases ha0 : a = 0
  · left
    simp [ha0]
  have hf : IsRealRooted (C u * X + C v : ℝ[X]) :=
    isRealRooted_affine_factor (s := u) (t := v) hu
  have hfnn : HasNonnegCoeffs (C u * X + C v : ℝ[X]) :=
    hasNonnegCoeffs_affine_linear hu.le hv
  exact (prec_C_mul_left (prec_self_mul_X_of_nonneg hf hfnn) ha0).toPrec0

/-! ## Matrix action formula -/

theorem zipWith_mul_veroneseLinearFactorRowDesc_sum_eq_of_succ
    {r : ℕ} (a : ℝ) (i : Fin r) (hi : i.1 + 1 < r)
    (fs : List ℝ[X]) (hfs : fs.length = r) :
    ((veroneseLinearFactorRowDesc r a i).zipWith (· * ·) fs).sum =
      C a * fs.get ⟨i.1, by omega⟩ +
        fs.get ⟨i.1 + 1, by omega⟩ := by
  subst r
  rw [veroneseLinearFactorRowDesc]
  rw [dif_pos hi]
  rw [zipWith_mul_sum_zipWith_add_left]
  · have hscaled :
        ((((oneSupportSeq fs.length i).map fun q => C a * q).zipWith
            (· * ·) fs).sum) =
          C a * fs.get i := by
      exact zipWith_mul_scaled_oneSupportSeq_sum_eq_get fs i (C a)
    have hsupport :
        ((oneSupportSeq fs.length ⟨i.1 + 1, hi⟩).zipWith (· * ·) fs).sum =
          fs.get ⟨i.1 + 1, hi⟩ := by
      exact zipWith_mul_oneSupportSeq_left_sum_eq_get fs ⟨i.1 + 1, hi⟩
    simpa using congrArg₂ (fun x y => x + y) hscaled hsupport
  · simp
  · simp

theorem zipWith_mul_veroneseLinearFactorRowDesc_sum_eq_of_last
    {r : ℕ} (a : ℝ) (i : Fin r) (hi : ¬ i.1 + 1 < r)
    (fs : List ℝ[X]) (hfs : fs.length = r) :
    ((veroneseLinearFactorRowDesc r a i).zipWith (· * ·) fs).sum =
      C a * fs.get ⟨i.1, by omega⟩ +
        X * fs.get ⟨0, by omega⟩ := by
  subst r
  rw [veroneseLinearFactorRowDesc]
  rw [dif_neg hi]
  rw [zipWith_mul_sum_zipWith_add_left]
  · have hscaled :
        ((((oneSupportSeq fs.length i).map fun q => C a * q).zipWith
            (· * ·) fs).sum) =
          C a * fs.get i := by
      exact zipWith_mul_scaled_oneSupportSeq_sum_eq_get fs i (C a)
    have hsupport :
        ((((oneSupportSeq fs.length ⟨0, by omega⟩).map fun q => X * q).zipWith
            (· * ·) fs).sum) =
          X * fs.get ⟨0, by omega⟩ := by
      exact zipWith_mul_scaled_oneSupportSeq_sum_eq_get fs ⟨0, by omega⟩ X
    simpa using congrArg₂ (fun x y => x + y) hscaled hsupport
  · simp
  · simp

set_option linter.flexible false in
/-- Matrix-vector multiplication by the cyclic matrix is exactly the
Veronese-section recursion for multiplication by `X + a`, in descending
residue order. -/
theorem matPolyAction_veroneseLinearFactorMatrixDesc
    {r : ℕ} (hr : 0 < r) (a : ℝ) (p : ℝ[X]) :
    matPolyAction (veroneseLinearFactorMatrixDesc r a)
        (veroneseSectionPolynomialListDesc r p) =
      veroneseSectionPolynomialListDesc r ((X + C a) * p) := by
  apply List.ext_get
  · simp [matPolyAction]
  · intro n hn₁ hn₂
    let i : Fin r := ⟨n, by simpa [matPolyAction] using hn₁⟩
    by_cases hi : i.1 + 1 < r
    · have hrow :=
        zipWith_mul_veroneseLinearFactorRowDesc_sum_eq_of_succ
          (r := r) a i hi (veroneseSectionPolynomialListDesc r p)
          (length_veroneseSectionPolynomialListDesc r p)
      have hk_succ : r - 1 - i.1 = (r - 1 - (i.1 + 1)) + 1 := by omega
      have hk_lt : (r - 1 - (i.1 + 1)) + 1 < r := by omega
      have hrec :=
        veroneseSectionPolynomial_X_add_C_mul_succ
          (r := r) (k := r - 1 - (i.1 + 1)) hk_lt a p
      simp [matPolyAction, veroneseLinearFactorMatrixDesc,
        veroneseSectionPolynomialListDesc, i] at hrow ⊢
      rw [hrow]
      rw [show r - 1 - n = (r - 1 - (n + 1)) + 1 by omega]
      rw [hrec]
      ac_rfl
    · have hrow :=
        zipWith_mul_veroneseLinearFactorRowDesc_sum_eq_of_last
          (r := r) a i hi (veroneseSectionPolynomialListDesc r p)
          (length_veroneseSectionPolynomialListDesc r p)
      have hi_last : i.1 = r - 1 := by omega
      have hrec := veroneseSectionPolynomial_X_add_C_mul_zero (r := r) hr a p
      simp [matPolyAction, veroneseLinearFactorMatrixDesc,
        veroneseSectionPolynomialListDesc, i] at hrow ⊢
      have hn_last : n = r - 1 := by simpa [i] using hi_last
      rw [hrow]
      rw [show r - 1 - n = 0 by omega]
      rw [hrec]
      ac_rfl

/-! ## Conditional matrix-preserver step -/

/-- The 2-by-2 affine condition for the descending Veronese linear-factor
matrix, stated with `Fin r` indices rather than list indices. -/
def VeroneseLinearFactorMatrixDescHas2x2 (r : ℕ) (a : ℝ) : Prop :=
  ∀ (i₁ i₂ j₁ j₂ : Fin r), i₁ ≤ i₂ → j₁ ≤ j₂ →
    Has2x2InterlacingProperty0
      ((veroneseLinearFactorRowDesc r a i₁).get
        ⟨j₁.1, by simp [length_veroneseLinearFactorRowDesc]⟩)
      ((veroneseLinearFactorRowDesc r a i₁).get
        ⟨j₂.1, by simp [length_veroneseLinearFactorRowDesc]⟩)
      ((veroneseLinearFactorRowDesc r a i₂).get
        ⟨j₁.1, by simp [length_veroneseLinearFactorRowDesc]⟩)
      ((veroneseLinearFactorRowDesc r a i₂).get
        ⟨j₂.1, by simp [length_veroneseLinearFactorRowDesc]⟩)

set_option linter.flexible false in
theorem hasNonnegCoeffs_veroneseLinearFactorRowDesc_entry
    {r : ℕ} {a : ℝ} (ha : 0 ≤ a) (i : Fin r)
    {q : ℝ[X]} (hq : q ∈ veroneseLinearFactorRowDesc r a i) :
    HasNonnegCoeffs q := by
  have hone :
      ∀ {n : ℕ} {i : Fin n} {q : ℝ[X]},
        q ∈ oneSupportSeq n i → HasNonnegCoeffs q := by
    intro n i q hq
    rcases List.mem_iff_get.1 hq with ⟨k, hk⟩
    rw [← hk]
    by_cases hki : (⟨k.1, by simpa [oneSupportSeq] using k.2⟩ : Fin n) = i
    · simp [oneSupportSeq, hki, hasNonnegCoeffs_one]
    · simp [oneSupportSeq, hki, hasNonnegCoeffs_zero]
  have hzip :
      ∀ {xs ys : List ℝ[X]},
        (∀ q ∈ xs, HasNonnegCoeffs q) →
        (∀ q ∈ ys, HasNonnegCoeffs q) →
        ∀ q ∈ xs.zipWith (· + ·) ys, HasNonnegCoeffs q := by
    intro xs
    induction xs with
    | nil =>
        intro ys hxs hys q hq
        simp at hq
    | cons x xs ih =>
        intro ys hxs hys q hq
        cases ys with
        | nil =>
            simp at hq
        | cons y ys =>
            simp at hq
            rcases hq with rfl | hq
            · exact (hxs x (by simp)).add (hys y (by simp))
            · exact ih (fun q hq => hxs q (by simp [hq]))
                (fun q hq => hys q (by simp [hq])) q hq
  rw [veroneseLinearFactorRowDesc] at hq
  by_cases hi : i.1 + 1 < r
  · exact hzip
      (fun q hq => by
        rcases List.mem_map.1 hq with ⟨q', hq', rfl⟩
        exact nonnegCoeffs_C_mul ha (hone (i := i) hq'))
      (fun q hq => hone (i := ⟨i.1 + 1, hi⟩) hq) q (by simpa [hi] using hq)
  · have hleft :
        ∀ q ∈ (oneSupportSeq r i).map (fun q => C a * q), HasNonnegCoeffs q := by
      intro q hq
      rcases List.mem_map.1 hq with ⟨q', hq', rfl⟩
      exact nonnegCoeffs_C_mul ha (hone (i := i) hq')
    have hr : 0 < r := by omega
    have hright :
        ∀ q ∈ (oneSupportSeq r ⟨0, hr⟩).map (fun q => X * q), HasNonnegCoeffs q := by
      intro q hq
      rcases List.mem_map.1 hq with ⟨q', hq', rfl⟩
      exact hasNonnegCoeffs_X.mul (hone (n := r) (i := ⟨0, hr⟩) hq')
    exact hzip hleft hright q (by simpa [hi, hr] using hq)

/-- Conditional linear-factor step for the matrix route.  The only remaining
mathematical obligation is the finite 2-by-2 condition for
`veroneseLinearFactorMatrixDesc`. -/
theorem isInterlacingSeq0Nonneg_veroneseSectionPolynomialListDesc_X_add_C_mul
    {r : ℕ} (hr : 0 < r) {a : ℝ} (ha : 0 ≤ a)
    (h2x2 : VeroneseLinearFactorMatrixDescHas2x2 r a)
    {p : ℝ[X]}
    (hseq : IsInterlacingSeqNonneg (veroneseSectionPolynomialListDesc r p)) :
    IsInterlacingSeq0Nonneg
      (veroneseSectionPolynomialListDesc r ((X + C a) * p)) := by
  rw [← matPolyAction_veroneseLinearFactorMatrixDesc (r := r) hr a p]
  refine
    matrix_preserves_interlacing_seq0_of_2x2
      (n := r) (G := veroneseLinearFactorMatrixDesc r a)
      ?hrect ?hnonneg ?haff
      (veroneseSectionPolynomialListDesc r p)
      (length_veroneseSectionPolynomialListDesc r p) hseq
  · intro row hrow
    rcases List.mem_iff_get.1 hrow with ⟨i, hi⟩
    rw [← hi]
    let i' : Fin r := ⟨i.1, by simpa [veroneseLinearFactorMatrixDesc] using i.2⟩
    simp [veroneseLinearFactorMatrixDesc]
  · intro row hrow q hq
    rcases List.mem_iff_get.1 hrow with ⟨i, hi⟩
    rw [← hi] at hq
    let i' : Fin r := ⟨i.1, by simpa [veroneseLinearFactorMatrixDesc] using i.2⟩
    have hq' : q ∈ veroneseLinearFactorRowDesc r a i' := by
      simpa [veroneseLinearFactorMatrixDesc, i'] using hq
    exact hasNonnegCoeffs_veroneseLinearFactorRowDesc_entry
      (r := r) (a := a) ha i' hq'
  · intro i₁ i₂ j₁ j₂ hi hij
    let i₁' : Fin r := ⟨i₁.1, by simpa [veroneseLinearFactorMatrixDesc] using i₁.2⟩
    let i₂' : Fin r := ⟨i₂.1, by simpa [veroneseLinearFactorMatrixDesc] using i₂.2⟩
    have hi' : i₁' ≤ i₂' := by simpa [i₁', i₂'] using hi
    have h := h2x2 i₁' i₂' j₁ j₂ hi' hij
    simpa [VeroneseLinearFactorMatrixDescHas2x2, veroneseLinearFactorMatrixDesc,
      i₁', i₂'] using h

end RealRooted
