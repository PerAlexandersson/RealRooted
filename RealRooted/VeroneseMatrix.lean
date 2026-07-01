import RealRooted.MatrixInterlacing
import RealRooted.VeroneseSection

/-!
# Matrix form of the Veronese linear-factor recursion

This file packages the cyclic-matrix route for Veronese sections.  The
important point is to list the sections in the descending residue order
`S_{r-1}, S_{r-2}, ..., S_0`; in that order the multiplication-by-`X + a`
recursion is given by a cyclic bidiagonal matrix with its `X` entry in the
lower-left corner.

The main payoff is
`isRealRootedOrZero_veroneseSectionPolynomial_of_realRooted_nonneg_matrix`:
every fixed Veronese section of a real-rooted polynomial with nonnegative
coefficients is real-rooted-or-zero.  The proof factors the input polynomial
into nonnegative linear factors `X + a`, proves the finite `2 × 2` affine
condition for the cyclic matrix, and then iterates the matrix-preserver theorem
for weak interlacing sequences.

This is related to Athanasiadis--Wagner's Veronese-section results, but it is
not a direct formalization of their fully interlacing matrix theorem.  The
fully interlacing submatrix route and conditional interfaces live in
`RealRooted.VeroneseSection`; this file gives a self-contained matrix proof of
the real-rootedness consequence needed here.
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

theorem mem_veroneseSectionPolynomialListDesc
    {r k : ℕ} (p : ℝ[X]) (hk : k < r) :
    veroneseSectionPolynomial r k p ∈ veroneseSectionPolynomialListDesc r p := by
  let i : Fin r := ⟨r - 1 - k, by lia⟩
  have hget :
      (veroneseSectionPolynomialListDesc r p).get
          ⟨i.1, by simp [length_veroneseSectionPolynomialListDesc]⟩ =
        veroneseSectionPolynomial r k p := by
    have hidx : r - 1 - i.1 = k := by
      simp [i]
      lia
    simpa [hidx] using get_veroneseSectionPolynomialListDesc (r := r) (p := p) i
  rw [← hget]
  simp

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
      (oneSupportSeq r ⟨0, by lia⟩).map fun q => X * q)

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
          (if j = ⟨0, by lia⟩ then X else 0)) := by
  by_cases hi : i.1 + 1 < r
  · simp [veroneseLinearFactorRowDesc, hi, oneSupportSeq]
  · simp [veroneseLinearFactorRowDesc, hi, oneSupportSeq]

/-! ## Small list-sum helpers -/

lemma zipWith_mul_sum_comm (xs ys : List ℝ[X]) :
    (xs.zipWith (· * ·) ys).sum = (ys.zipWith (· * ·) xs).sum := by
  induction xs generalizing ys with
  | nil =>
      simp
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
    simp_all
  right
  right
  have hCa : (C a : ℝ[X]) ≠ 0 := C_ne_zero.mpr ha
  have hCb : (C b : ℝ[X]) ≠ 0 := C_ne_zero.mpr hb
  have hrr_a : ((C a : ℝ[X]) ≠ 0 ∧ (C a : ℝ[X]).Splits) := isRealRooted_of_deg_zero hCa (by simp)
  have hrr_b : ((C b : ℝ[X]) ≠ 0 ∧ (C b : ℝ[X]).Splits) := isRealRooted_of_deg_zero hCb (by simp)
  refine ⟨hrr_a, hrr_b, [], [], by simp, by simp, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact Or.inr ⟨by lia, by simp [ListAlternates]⟩

lemma prec0_C_affine_linear {c u v : ℝ} (hu : 0 < u) :
    Prec0 (C c : ℝ[X]) (C u * X + C v) := by
  by_cases hc : c = 0
  · left
    simp [hc]
  right
  right
  have hC : (C c : ℝ[X]) ≠ 0 := C_ne_zero.mpr hc
  have hlin_rr : ((C u * X + C v : ℝ[X]) ≠ 0 ∧ (C u * X + C v : ℝ[X]).Splits) :=
    isRealRooted_affine_factor (s := u) (t := v) hu
  have hlin_nat : (C u * X + C v : ℝ[X]).natDegree = 1 := by grind
  have hlin_deg : (C u * X + C v : ℝ[X]).degree = 1 := by
    rw [degree_eq_natDegree hlin_rr.1, hlin_nat]
    lia
  have hC_rr : ((C c : ℝ[X]) ≠ 0 ∧ (C c : ℝ[X]).Splits) := isRealRooted_of_deg_zero hC (by simp)
  refine ⟨hC_rr, hlin_rr, [], [-(u⁻¹ * v)], by simp, by simp, ?_, ?_, ?_⟩
  · simp
  · simpa [hlin_deg] using
      (Polynomial.roots_degree_eq_one (p := (C u * X + C v : ℝ[X])) hlin_deg).symm
  · exact Or.inl ⟨by simp, by simp [ListInterlaces]⟩

lemma prec0_congr {p q p' q' : ℝ[X]} (hp : p = p') (hq : q = q')
    (h : Prec0 p' q') : Prec0 p q := by
  lia

lemma affine_mul_C_add_C (s t b d : ℝ) :
    ((C s * X + C t) * C b + C d : ℝ[X]) =
      C (s * b) * X + C (t * b + d) := by
  grind

lemma affine_mul_C_add_X (s t b : ℝ) :
    ((C s * X + C t) * C b + X : ℝ[X]) =
      C (s * b + 1) * X + C (t * b) := by
  grind

lemma affine_mul_X_add_X_eq (s t : ℝ) :
    ((C s * X + C t) * X + X : ℝ[X]) =
      X * (C s * X + C (t + 1)) := by
  grind

lemma isRealRooted_affine_mul_X_add_X {s t : ℝ} (hs : 0 < s) :
    (((C s * X + C t) * X + X : ℝ[X]) ≠ 0 ∧ ((C s * X + C t) * X + X : ℝ[X]).Splits) := by
  rw [affine_mul_X_add_X_eq]
  exact isRealRooted_X_mul
    (isRealRooted_affine_factor (s := s) (t := t + 1) hs).1
    (isRealRooted_affine_factor (s := s) (t := t + 1) hs).2

lemma isRealRooted_affine_mul_C_add_X
    {A s t : ℝ} (hA : 0 ≤ A) (hs : 0 < s) :
    (((C s * X + C t) * C A + X : ℝ[X]) ≠ 0 ∧ ((C s * X + C t) * C A + X : ℝ[X]).Splits) := by
  simpa [affine_mul_C_add_X] using
    isRealRooted_affine_factor (s := s * A + 1) (t := t * A) (by positivity)

lemma affine_mul_C_add_same_eq (s t a : ℝ) :
    ((C s * X + C t) * C a + C a : ℝ[X]) =
      C a * (C s * X + C (t + 1)) := by
  grind

lemma affineLinear_root_le_of_cross {u v U V : ℝ}
    (hu : 0 < u) (hU : 0 < U) (hcross : u * V ≤ U * v) :
    -(u⁻¹ * v) ≤ -(U⁻¹ * V) := by
  rw [neg_le_neg_iff]
  rw [← div_eq_inv_mul, ← div_eq_inv_mul]
  rw [div_le_div_iff₀ hU hu]
  grind

lemma prec_affine_linear_affine_linear_of_cross
    {u v U V : ℝ} (hu : 0 < u) (hU : 0 < U)
    (hcross : u * V ≤ U * v) :
    Prec (C u * X + C v) (C U * X + C V) := by
  have hroot : -(u⁻¹ * v) ≤ -(U⁻¹ * V) :=
    affineLinear_root_le_of_cross hu hU hcross
  have hp_nat : (C u * X + C v : ℝ[X]).natDegree = 1 := by grind
  have hq_nat : (C U * X + C V : ℝ[X]).natDegree = 1 := by grind
  have hp_rr : ((C u * X + C v : ℝ[X]) ≠ 0 ∧ (C u * X + C v : ℝ[X]).Splits) :=
    isRealRooted_affine_factor (s := u) (t := v) hu
  have hq_rr : ((C U * X + C V : ℝ[X]) ≠ 0 ∧ (C U * X + C V : ℝ[X]).Splits) :=
    isRealRooted_affine_factor (s := U) (t := V) hU
  have hp_deg : (C u * X + C v : ℝ[X]).degree = 1 := by
    rw [degree_eq_natDegree hp_rr.1, hp_nat]
    lia
  have hq_deg : (C U * X + C V : ℝ[X]).degree = 1 := by
    rw [degree_eq_natDegree hq_rr.1, hq_nat]
    lia
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

lemma prec0_const_entries_affine_of_det_nonneg
    {A b c d s t : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 < s) (hdet : b * c ≤ A * d) :
    Prec0 ((C s * X + C t) * C b + C d)
      ((C s * X + C t) * C A + C c) := by
  by_cases hb0 : b = 0
  · by_cases hA0 : A = 0
    · refine
        prec0_congr (p' := C d) (q' := C c) ?_ ?_
          (prec0_C_C d c)
      · simp [hb0]
      · simp [hA0]
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
      refine
        prec0_congr (p' := C d)
          (q' := C (s * A) * X + C (t * A + c)) ?_ ?_ ?_
      · simp [hb0]
      · grind
      · exact
          prec0_C_affine_linear (c := d) (u := s * A) (v := t * A + c)
            (by simp_all)
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    by_cases hA0 : A = 0
    · have hc0 : c = 0 := by nlinarith [hdet, hbpos, hc]
      refine prec0_congr (q' := 0) rfl ?_ (prec0_zero_right _)
      simp_all
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
      have hcross : (b * s) * (A * t + c) ≤ (A * s) * (b * t + d) := by
        nlinarith [hdet, hs]
      refine
        prec0_congr
          (p' := C (b * s) * X + C (b * t + d))
          (q' := C (A * s) * X + C (A * t + c)) ?_ ?_ ?_
      · grind
      · grind
      · exact
          prec0_affine_linear_affine_linear_of_cross
            (u := b * s) (v := b * t + d) (U := A * s) (V := A * t + c)
            (by simp_all) (by simp_all) hcross

lemma prec0_const_entry_affine_plus_const_to_affine_plus_X
    {A b d s t : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hs : 0 < s) (ht : 0 ≤ t) :
    Prec0 ((C s * X + C t) * C b + C d)
      ((C s * X + C t) * C A + X) := by
  by_cases hb0 : b = 0
  · refine
      prec0_congr (p' := C d)
        (q' := C (s * A + 1) * X + C (t * A)) ?_ ?_ ?_
    · simp [hb0]
    · grind
    · exact
        prec0_C_affine_linear (c := d) (u := s * A + 1) (v := t * A)
          (by positivity)
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hcross : (b * s) * (A * t) ≤ (A * s + 1) * (b * t + d) := by
      nlinarith [mul_nonneg hA hs.le, mul_nonneg hb ht, mul_nonneg hd hA,
        mul_nonneg hd hs.le]
    refine
      prec0_congr
        (p' := C (b * s) * X + C (b * t + d))
        (q' := C (A * s + 1) * X + C (A * t)) ?_ ?_ ?_
    · grind
    · grind
    · exact
        prec0_affine_linear_affine_linear_of_cross
          (u := b * s) (v := b * t + d) (U := A * s + 1) (V := A * t)
          (by simp_all) (by positivity) hcross

lemma prec0_C_mul_affine_linear_X_mul_affine_linear
    {a u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) :
    Prec0 (C a * (C u * X + C v)) (X * (C u * X + C v)) := by
  by_cases ha0 : a = 0
  · left
    simp [ha0]
  have hf : ((C u * X + C v : ℝ[X]) ≠ 0 ∧ (C u * X + C v : ℝ[X]).Splits) :=
    isRealRooted_affine_factor (s := u) (t := v) hu
  have hfnn : HasNonnegCoeffs (C u * X + C v : ℝ[X]) :=
    hasNonnegCoeffs_affine_linear hu.le hv
  exact (prec_C_mul_left (prec_self_mul_X_of_nonneg hf.1 hf.2 hfnn) ha0).toPrec0

/-! ## Matrix action formula -/

theorem zipWith_mul_veroneseLinearFactorRowDesc_sum_eq_of_succ
    {r : ℕ} (a : ℝ) (i : Fin r) (hi : i.1 + 1 < r)
    (fs : List ℝ[X]) (hfs : fs.length = r) :
    ((veroneseLinearFactorRowDesc r a i).zipWith (· * ·) fs).sum =
      C a * fs.get ⟨i.1, by lia⟩ +
        fs.get ⟨i.1 + 1, by lia⟩ := by
  subst r
  rw [veroneseLinearFactorRowDesc]
  rw [dif_pos hi]
  rw [zipWith_mul_sum_zipWith_add_left]
  · have hscaled :
        ((((oneSupportSeq fs.length i).map fun q => C a * q).zipWith
            (· * ·) fs).sum) =
          C a * fs.get i :=
        zipWith_mul_scaled_oneSupportSeq_sum_eq_get fs i (C a)
    have hsupport :
        ((oneSupportSeq fs.length ⟨i.1 + 1, hi⟩).zipWith (· * ·) fs).sum =
          fs.get ⟨i.1 + 1, hi⟩ :=
        zipWith_mul_oneSupportSeq_left_sum_eq_get fs ⟨i.1 + 1, hi⟩
    simpa using congrArg₂ (fun x y => x + y) hscaled hsupport
  · simp
  · simp

theorem zipWith_mul_veroneseLinearFactorRowDesc_sum_eq_of_last
    {r : ℕ} (a : ℝ) (i : Fin r) (hi : ¬ i.1 + 1 < r)
    (fs : List ℝ[X]) (hfs : fs.length = r) :
    ((veroneseLinearFactorRowDesc r a i).zipWith (· * ·) fs).sum =
      C a * fs.get ⟨i.1, by lia⟩ +
        X * fs.get ⟨0, by lia⟩ := by
  subst r
  rw [veroneseLinearFactorRowDesc]
  rw [dif_neg hi]
  rw [zipWith_mul_sum_zipWith_add_left]
  · have hscaled :
        ((((oneSupportSeq fs.length i).map fun q => C a * q).zipWith
            (· * ·) fs).sum) =
          C a * fs.get i :=
        zipWith_mul_scaled_oneSupportSeq_sum_eq_get fs i (C a)
    have hsupport :
        ((((oneSupportSeq fs.length ⟨0, by lia⟩).map fun q => X * q).zipWith
            (· * ·) fs).sum) =
          X * fs.get ⟨0, by lia⟩ :=
        zipWith_mul_scaled_oneSupportSeq_sum_eq_get fs ⟨0, by lia⟩ X
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
    let i : Fin r := ⟨n, by simp_all⟩
    by_cases hi : i.1 + 1 < r
    · have hrow :=
        zipWith_mul_veroneseLinearFactorRowDesc_sum_eq_of_succ
          (r := r) a i hi (veroneseSectionPolynomialListDesc r p)
          (length_veroneseSectionPolynomialListDesc r p)
      have hk_succ : r - 1 - i.1 = (r - 1 - (i.1 + 1)) + 1 := by lia
      have hk_lt : (r - 1 - (i.1 + 1)) + 1 < r := by lia
      have hrec :=
        veroneseSectionPolynomial_X_add_C_mul_succ
          (r := r) (k := r - 1 - (i.1 + 1)) hk_lt a p
      simp [matPolyAction, veroneseLinearFactorMatrixDesc,
        veroneseSectionPolynomialListDesc, i] at hrow ⊢
      rw [hrow]
      simpa [i, add_comm, add_left_comm, add_assoc, hk_succ] using hrec.symm
    · have hrow :=
        zipWith_mul_veroneseLinearFactorRowDesc_sum_eq_of_last
          (r := r) a i hi (veroneseSectionPolynomialListDesc r p)
          (length_veroneseSectionPolynomialListDesc r p)
      have hi_last : i.1 = r - 1 := by
        have hle : r ≤ i.1 + 1 := Nat.le_of_not_gt hi
        have hle' : i.1 + 1 ≤ r := Nat.succ_le_of_lt i.2
        have hs : i.1 + 1 = r := le_antisymm hle' hle
        exact Nat.eq_sub_of_add_eq hs
      have hrec := veroneseSectionPolynomial_X_add_C_mul_zero (r := r) hr a p
      simp [matPolyAction, veroneseLinearFactorMatrixDesc,
        veroneseSectionPolynomialListDesc, i] at hrow ⊢
      rw [hrow]
      rw [show r - 1 - n = 0 by
        simpa [i] using congrArg (fun m => r - 1 - m) hi_last]
      rw [hrec]
      ring

/-! ## Cyclic matrix 2-by-2 check and preserver step -/

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
theorem veroneseLinearFactorMatrixDesc_has2x2_one (a : ℝ) :
    VeroneseLinearFactorMatrixDescHas2x2 1 a := by
  intro i₁ i₂ j₁ j₂ _ _ s t hs _
  fin_cases i₁
  fin_cases i₂
  fin_cases j₁
  fin_cases j₂
  simp [veroneseLinearFactorRowDesc, oneSupportSeq]
  have hlin : ((C s * X + C (t + 1) : ℝ[X]) ≠ 0 ∧ (C s * X + C (t + 1) : ℝ[X]).Splits) :=
    isRealRooted_affine_factor (s := s) (t := t + 1) hs
  have hxpa : ((X + C a : ℝ[X]) ≠ 0 ∧ (X + C a : ℝ[X]).Splits) := by
    simpa using isRealRooted_affine_factor (s := 1) (t := a) zero_lt_one
  have hrr : (((C s * X + C (t + 1)) * (X + C a) : ℝ[X]) ≠ 0 ∧
    ((C s * X + C (t + 1)) * (X + C a) : ℝ[X]).Splits) :=
    isRealRooted_mul hlin.1 hlin.2 hxpa.1 hxpa.2
  have hsum : (C s * X + C t : ℝ[X]) + 1 = C s * X + C (t + 1) := by grind
  have hfactor :
      ((C s * X + C t) * (C a + X) + (C a + X) : ℝ[X]) =
        (C s * X + C (t + 1)) * (X + C a) := by
    grind
  rw [hfactor]
  exact (prec_refl hrr.1 hrr.2).toPrec0

def veroneseLinearFactorConstEntry {r : ℕ} (a : ℝ) (i j : Fin r) : ℝ :=
  if j.1 = i.1 then a else if j.1 = i.1 + 1 then 1 else 0

lemma get_veroneseLinearFactorRowDesc_of_nonlast
    {r : ℕ} (a : ℝ) (i j : Fin r) (hi : i.1 + 1 < r) :
    (veroneseLinearFactorRowDesc r a i).get
        ⟨j.1, by simp [length_veroneseLinearFactorRowDesc]⟩ =
      C (veroneseLinearFactorConstEntry a i j) := by
  rw [get_veroneseLinearFactorRowDesc]
  unfold veroneseLinearFactorConstEntry
  grind

lemma veroneseLinearFactorConstEntry_nonneg
    {r : ℕ} {a : ℝ} (ha : 0 ≤ a) (i j : Fin r) :
    0 ≤ veroneseLinearFactorConstEntry a i j := by
  unfold veroneseLinearFactorConstEntry
  grind

lemma veroneseLinearFactorConstEntry_det_nonneg
    {r : ℕ} {a : ℝ} (ha : 0 ≤ a)
    {i₁ i₂ j₁ j₂ : Fin r} (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂) :
    veroneseLinearFactorConstEntry a i₁ j₂ *
        veroneseLinearFactorConstEntry a i₂ j₁ ≤
      veroneseLinearFactorConstEntry a i₁ j₁ *
        veroneseLinearFactorConstEntry a i₂ j₂ := by
  have hi_nat : i₁.1 ≤ i₂.1 := by lia
  have hj_nat : j₁.1 ≤ j₂.1 := by lia
  unfold veroneseLinearFactorConstEntry
  split_ifs <;> try lia
  all_goals nlinarith [ha, sq_nonneg a]

theorem veroneseLinearFactorMatrixDesc_has2x2_nonlast
    {r : ℕ} {a : ℝ} (ha : 0 ≤ a)
    {i₁ i₂ j₁ j₂ : Fin r} (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂)
    (hrow₁ : i₁.1 + 1 < r) (hrow₂ : i₂.1 + 1 < r) :
    Has2x2InterlacingProperty0
      ((veroneseLinearFactorRowDesc r a i₁).get
        ⟨j₁.1, by simp [length_veroneseLinearFactorRowDesc]⟩)
      ((veroneseLinearFactorRowDesc r a i₁).get
        ⟨j₂.1, by simp [length_veroneseLinearFactorRowDesc]⟩)
      ((veroneseLinearFactorRowDesc r a i₂).get
        ⟨j₁.1, by simp [length_veroneseLinearFactorRowDesc]⟩)
      ((veroneseLinearFactorRowDesc r a i₂).get
        ⟨j₂.1, by simp [length_veroneseLinearFactorRowDesc]⟩) := by
  intro s t hs _
  rw [get_veroneseLinearFactorRowDesc_of_nonlast (hi := hrow₁)]
  rw [get_veroneseLinearFactorRowDesc_of_nonlast (hi := hrow₁)]
  rw [get_veroneseLinearFactorRowDesc_of_nonlast (hi := hrow₂)]
  rw [get_veroneseLinearFactorRowDesc_of_nonlast (hi := hrow₂)]
  exact
    prec0_const_entries_affine_of_det_nonneg
      (veroneseLinearFactorConstEntry_nonneg ha i₁ j₁)
      (veroneseLinearFactorConstEntry_nonneg ha i₁ j₂)
      (veroneseLinearFactorConstEntry_nonneg ha i₂ j₁)
      (veroneseLinearFactorConstEntry_nonneg ha i₂ j₂)
      hs
      (veroneseLinearFactorConstEntry_det_nonneg ha hi hj)

def veroneseLinearFactorLastConstEntry {r : ℕ} (a : ℝ) (j : Fin r) : ℝ :=
  if j.1 = r - 1 then a else 0

lemma get_veroneseLinearFactorRowDesc_of_last
    {r : ℕ} (hr2 : 2 ≤ r) (a : ℝ) (i j : Fin r)
    (hi : ¬ i.1 + 1 < r) :
    (veroneseLinearFactorRowDesc r a i).get
        ⟨j.1, by simp [length_veroneseLinearFactorRowDesc]⟩ =
      if j.1 = 0 then X else C (veroneseLinearFactorLastConstEntry a j) := by
  have hilast : i.1 = r - 1 := by lia
  have hlast_ne_zero : r - 1 ≠ 0 := by lia
  rw [get_veroneseLinearFactorRowDesc]
  unfold veroneseLinearFactorLastConstEntry
  grind

lemma veroneseLinearFactorLastConstEntry_nonneg
    {r : ℕ} {a : ℝ} (ha : 0 ≤ a) (j : Fin r) :
    0 ≤ veroneseLinearFactorLastConstEntry a j := by
  unfold veroneseLinearFactorLastConstEntry
  grind

lemma veroneseLinearFactorLastConstEntry_det_nonneg
    {r : ℕ} {a : ℝ} {j₁ j₂ : Fin r} :
    veroneseLinearFactorLastConstEntry a j₂ *
        veroneseLinearFactorLastConstEntry a j₁ ≤
      veroneseLinearFactorLastConstEntry a j₁ *
        veroneseLinearFactorLastConstEntry a j₂ := by
  grind

lemma veroneseLinearFactorConstLastEntry_det_nonneg
    {r : ℕ} {a : ℝ} (ha : 0 ≤ a)
    {i j₁ j₂ : Fin r} (hj : j₁ ≤ j₂) :
    veroneseLinearFactorConstEntry a i j₂ *
        veroneseLinearFactorLastConstEntry a j₁ ≤
      veroneseLinearFactorConstEntry a i j₁ *
        veroneseLinearFactorLastConstEntry a j₂ := by
  have hj_nat : j₁.1 ≤ j₂.1 := by lia
  unfold veroneseLinearFactorConstEntry veroneseLinearFactorLastConstEntry
  split_ifs <;> try lia
  all_goals nlinarith [ha, sq_nonneg a]

theorem veroneseLinearFactorMatrixDesc_has2x2_mixed
    {r : ℕ} {a : ℝ} (ha : 0 ≤ a) (hr2 : 2 ≤ r)
    {i₁ i₂ j₁ j₂ : Fin r} (hj : j₁ ≤ j₂)
    (hrow₁ : i₁.1 + 1 < r) (hrow₂ : ¬ i₂.1 + 1 < r) :
    Has2x2InterlacingProperty0
      ((veroneseLinearFactorRowDesc r a i₁).get
        ⟨j₁.1, by simp [length_veroneseLinearFactorRowDesc]⟩)
      ((veroneseLinearFactorRowDesc r a i₁).get
        ⟨j₂.1, by simp [length_veroneseLinearFactorRowDesc]⟩)
      ((veroneseLinearFactorRowDesc r a i₂).get
        ⟨j₁.1, by simp [length_veroneseLinearFactorRowDesc]⟩)
      ((veroneseLinearFactorRowDesc r a i₂).get
        ⟨j₂.1, by simp [length_veroneseLinearFactorRowDesc]⟩) := by
  intro s t hs ht
  have hj_nat : j₁.1 ≤ j₂.1 := by lia
  rw [get_veroneseLinearFactorRowDesc_of_nonlast (hi := hrow₁)]
  rw [get_veroneseLinearFactorRowDesc_of_nonlast (hi := hrow₁)]
  rw [get_veroneseLinearFactorRowDesc_of_last hr2 (hi := hrow₂)]
  rw [get_veroneseLinearFactorRowDesc_of_last hr2 (hi := hrow₂)]
  by_cases hj₁0 : j₁.1 = 0
  · by_cases hj₂0 : j₂.1 = 0
    · have hj_eq : j₁ = j₂ := by lia
      subst j₂
      rw [if_pos hj₁0]
      let hrr :=
        isRealRooted_affine_mul_C_add_X
          (t := t) (veroneseLinearFactorConstEntry_nonneg ha i₁ j₁) hs
      exact (prec_refl hrr.1 hrr.2).toPrec0
    · rw [if_pos hj₁0, if_neg hj₂0]
      exact
        prec0_const_entry_affine_plus_const_to_affine_plus_X
          (veroneseLinearFactorConstEntry_nonneg ha i₁ j₁)
          (veroneseLinearFactorConstEntry_nonneg ha i₁ j₂)
          (veroneseLinearFactorLastConstEntry_nonneg ha j₂)
          hs ht.le
  · have hj₂0 : ¬ j₂.1 = 0 := by lia
    rw [if_neg hj₁0, if_neg hj₂0]
    exact
      prec0_const_entries_affine_of_det_nonneg
        (veroneseLinearFactorConstEntry_nonneg ha i₁ j₁)
        (veroneseLinearFactorConstEntry_nonneg ha i₁ j₂)
        (veroneseLinearFactorLastConstEntry_nonneg ha j₁)
        (veroneseLinearFactorLastConstEntry_nonneg ha j₂)
        hs
        (veroneseLinearFactorConstLastEntry_det_nonneg ha hj)

theorem veroneseLinearFactorMatrixDesc_has2x2_last_last
    {r : ℕ} {a : ℝ} (ha : 0 ≤ a) (hr2 : 2 ≤ r)
    {i₁ i₂ j₁ j₂ : Fin r} (hj : j₁ ≤ j₂)
    (hrow₁ : ¬ i₁.1 + 1 < r) (hrow₂ : ¬ i₂.1 + 1 < r) :
    Has2x2InterlacingProperty0
      ((veroneseLinearFactorRowDesc r a i₁).get
        ⟨j₁.1, by simp [length_veroneseLinearFactorRowDesc]⟩)
      ((veroneseLinearFactorRowDesc r a i₁).get
        ⟨j₂.1, by simp [length_veroneseLinearFactorRowDesc]⟩)
      ((veroneseLinearFactorRowDesc r a i₂).get
        ⟨j₁.1, by simp [length_veroneseLinearFactorRowDesc]⟩)
      ((veroneseLinearFactorRowDesc r a i₂).get
        ⟨j₂.1, by simp [length_veroneseLinearFactorRowDesc]⟩) := by
  intro s t hs _
  have hlast_ne_zero : r - 1 ≠ 0 := by lia
  have hj_nat : j₁.1 ≤ j₂.1 := by lia
  rw [get_veroneseLinearFactorRowDesc_of_last hr2 (hi := hrow₁)]
  rw [get_veroneseLinearFactorRowDesc_of_last hr2 (hi := hrow₁)]
  rw [get_veroneseLinearFactorRowDesc_of_last hr2 (hi := hrow₂)]
  rw [get_veroneseLinearFactorRowDesc_of_last hr2 (hi := hrow₂)]
  by_cases hj₁0 : j₁.1 = 0
  · by_cases hj₂0 : j₂.1 = 0
    · rw [if_pos hj₁0, if_pos hj₂0]
      exact
        (prec_refl (isRealRooted_affine_mul_X_add_X hs).1
          (isRealRooted_affine_mul_X_add_X hs).2).toPrec0
    · by_cases hj₂last : j₂.1 = r - 1
      · rw [if_pos hj₁0, if_neg hj₂0]
        simp only [veroneseLinearFactorLastConstEntry, hj₂last, if_true]
        rw [affine_mul_C_add_same_eq, affine_mul_X_add_X_eq]
        exact
          prec0_C_mul_affine_linear_X_mul_affine_linear
            (a := a) (u := s) (v := t + 1) hs (by grind)
      · simp [hj₁0, hj₂0, hj₂last,
          veroneseLinearFactorLastConstEntry, prec0_zero_left]
  · rw [if_neg hj₁0]
    have hj₂0 : ¬ j₂.1 = 0 := by lia
    rw [if_neg hj₂0]
    exact
      prec0_const_entries_affine_of_det_nonneg
        (veroneseLinearFactorLastConstEntry_nonneg ha j₁)
        (veroneseLinearFactorLastConstEntry_nonneg ha j₂)
        (veroneseLinearFactorLastConstEntry_nonneg ha j₁)
        (veroneseLinearFactorLastConstEntry_nonneg ha j₂)
        hs
        veroneseLinearFactorLastConstEntry_det_nonneg

theorem veroneseLinearFactorMatrixDesc_has2x2
    {r : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    VeroneseLinearFactorMatrixDescHas2x2 r a := by
  intro i₁ i₂ j₁ j₂ hi hj
  by_cases hr1 : r = 1
  · subst r
    exact veroneseLinearFactorMatrixDesc_has2x2_one a i₁ i₂ j₁ j₂ hi hj
  · have hr2 : 2 ≤ r := by lia
    by_cases hrow₂ : i₂.1 + 1 < r
    · have hrow₁ : i₁.1 + 1 < r := by lia
      exact veroneseLinearFactorMatrixDesc_has2x2_nonlast
        ha hi hj hrow₁ hrow₂
    · by_cases hrow₁ : i₁.1 + 1 < r
      · exact veroneseLinearFactorMatrixDesc_has2x2_mixed
          ha hr2 hj hrow₁ hrow₂
      · exact veroneseLinearFactorMatrixDesc_has2x2_last_last
          ha hr2 hj hrow₁ hrow₂

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
        simp
    | cons x xs ih =>
        intro ys hxs hys q hq
        cases ys with
        | nil =>
            simp at hq
        | cons y ys =>
            change q ∈ (x + y) :: xs.zipWith (· + ·) ys at hq
            rcases List.mem_cons.mp hq with hq | hq
            · subst q
              exact (hxs x (by simp)).add (hys y (by simp))
            · grind
  rw [veroneseLinearFactorRowDesc] at hq
  by_cases hi : i.1 + 1 < r
  · exact hzip
      (fun q hq => by
        rcases List.mem_map.1 hq with ⟨q', hq', rfl⟩
        exact nonnegCoeffs_C_mul ha (hone (i := i) hq'))
      (fun q hq => hone (i := ⟨i.1 + 1, hi⟩) hq) q (by lia)
  · have hleft :
        ∀ q ∈ (oneSupportSeq r i).map (fun q => C a * q), HasNonnegCoeffs q := by
      intro q hq
      rcases List.mem_map.1 hq with ⟨q', hq', rfl⟩
      exact nonnegCoeffs_C_mul ha (hone (i := i) hq')
    have hr : 0 < r := by lia
    have hright :
        ∀ q ∈ (oneSupportSeq r ⟨0, hr⟩).map (fun q => X * q), HasNonnegCoeffs q := by
      intro q hq
      rcases List.mem_map.1 hq with ⟨q', hq', rfl⟩
      exact hasNonnegCoeffs_X.mul (hone (n := r) (i := ⟨0, hr⟩) hq')
    grind

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
    have hi' : i₁' ≤ i₂' := by grind
    have h := h2x2 i₁' i₂' j₁ j₂ hi' hij
    simpa [VeroneseLinearFactorMatrixDescHas2x2, veroneseLinearFactorMatrixDesc,
      i₁', i₂'] using h

/-- The cyclic matrix proof gives the Veronese-section linear-factor step:
if the descending Veronese sections of `p` are nonnegative and interlacing,
then the sections of `(X + a) * p` are weakly interlacing for every `a ≥ 0`. -/
theorem isInterlacingSeq0Nonneg_veroneseSectionPolynomialListDesc_X_add_C_mul_of_nonneg
    {r : ℕ} (hr : 0 < r) {a : ℝ} (ha : 0 ≤ a)
    {p : ℝ[X]}
    (hseq : IsInterlacingSeqNonneg (veroneseSectionPolynomialListDesc r p)) :
    IsInterlacingSeq0Nonneg
      (veroneseSectionPolynomialListDesc r ((X + C a) * p)) :=
  isInterlacingSeq0Nonneg_veroneseSectionPolynomialListDesc_X_add_C_mul
    hr ha (veroneseLinearFactorMatrixDesc_has2x2 ha) hseq

/-- Iterable zero-aware linear-factor step.  It accepts weak interlacing input,
provided every nonzero input section is real-rooted, and returns the same
package after multiplication by `X + a`, `a ≥ 0`. -/
theorem isInterlacingSeq0Nonneg_and_real_veroneseSectionPolynomialListDesc_X_add_C_mul
    {r : ℕ} (hr : 0 < r) {a : ℝ} (ha : 0 ≤ a)
    {p : ℝ[X]}
    (hseq : IsInterlacingSeq0Nonneg (veroneseSectionPolynomialListDesc r p))
    (hreal : ∀ f ∈ veroneseSectionPolynomialListDesc r p,
      f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg
        (veroneseSectionPolynomialListDesc r ((X + C a) * p)) ∧
      ∀ f ∈ veroneseSectionPolynomialListDesc r ((X + C a) * p),
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  rw [← matPolyAction_veroneseLinearFactorMatrixDesc (r := r) hr a p]
  refine
    matrix_preserves_interlacing_seq0_of_2x2_weak
      (n := r) (G := veroneseLinearFactorMatrixDesc r a)
      ?hrect ?hnonneg ?haff
      (veroneseSectionPolynomialListDesc r p)
      (length_veroneseSectionPolynomialListDesc r p) hseq hreal
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
    have hi' : i₁' ≤ i₂' := by grind
    have h := veroneseLinearFactorMatrixDesc_has2x2 ha i₁' i₂' j₁ j₂ hi' hij
    simpa [VeroneseLinearFactorMatrixDescHas2x2, veroneseLinearFactorMatrixDesc,
      i₁', i₂'] using h

/-- Product of monic nonnegative linear factors `∏ (X + a)`. -/
def linearFactorProduct (as : List ℝ) : ℝ[X] :=
  (as.map fun a => X + C a).prod

@[simp] theorem linearFactorProduct_nil :
    linearFactorProduct [] = (1 : ℝ[X]) := by
  simp [linearFactorProduct]

@[simp] theorem linearFactorProduct_cons (a : ℝ) (as : List ℝ) :
    linearFactorProduct (a :: as) = (X + C a) * linearFactorProduct as := by
  simp [linearFactorProduct]

lemma veroneseSectionPolynomial_one_of_zero {r : ℕ} (hr : 0 < r) :
    veroneseSectionPolynomial r 0 (1 : ℝ[X]) = 1 := by
  ext n
  rw [coeff_veroneseSectionPolynomial (r := r) (k := 0) (p := (1 : ℝ[X])) hr]
  cases n with
  | zero =>
      lia
  | succ n =>
      have hpos : 0 < r * (n + 1) := Nat.mul_pos hr (Nat.succ_pos n)
      simp [Polynomial.coeff_one, Nat.ne_of_gt hpos]

lemma veroneseSectionPolynomial_one_of_pos {r k : ℕ} (hr : 0 < r) (hk : 0 < k) :
    veroneseSectionPolynomial r k (1 : ℝ[X]) = 0 := by
  ext n
  rw [coeff_veroneseSectionPolynomial (r := r) (k := k) (p := (1 : ℝ[X])) hr]
  simp [Polynomial.coeff_one]
  lia

lemma veroneseSectionPolynomialListDesc_one_eq_oneSupportSeq
    {r : ℕ} (hr : 0 < r) :
    veroneseSectionPolynomialListDesc r (1 : ℝ[X]) =
      oneSupportSeq r ⟨r - 1, by lia⟩ := by
  apply List.ext_get
  · simp [veroneseSectionPolynomialListDesc, oneSupportSeq]
  · intro n hn₁ hn₂
    let i : Fin r := ⟨n, by simpa [veroneseSectionPolynomialListDesc] using hn₁⟩
    rw [show (veroneseSectionPolynomialListDesc r (1 : ℝ[X])).get ⟨n, hn₁⟩ =
        veroneseSectionPolynomial r (r - 1 - i.1) (1 : ℝ[X]) by
      simpa [i] using get_veroneseSectionPolynomialListDesc
        (r := r) (p := (1 : ℝ[X])) i]
    rw [show (oneSupportSeq r ⟨r - 1, by lia⟩).get ⟨n, hn₂⟩ =
        (if n = r - 1 then (1 : ℝ[X]) else 0) by
      simp [oneSupportSeq, Fin.ext_iff]]
    by_cases hlast : n = r - 1
    · have hk : r - 1 - i.1 = 0 := by simp [i, hlast]
      simp [hlast, hk, veroneseSectionPolynomial_one_of_zero hr]
    · have hk : 0 < r - 1 - i.1 := by
        have hnlt : n < r := i.2
        simp [i]
        lia
      simp [hlast, veroneseSectionPolynomial_one_of_pos hr hk]

theorem isInterlacingSeq0Nonneg_and_real_veroneseSectionPolynomialListDesc_one
    {r : ℕ} (hr : 0 < r) :
    IsInterlacingSeq0Nonneg (veroneseSectionPolynomialListDesc r (1 : ℝ[X])) ∧
      ∀ f ∈ veroneseSectionPolynomialListDesc r (1 : ℝ[X]),
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  have hlist := veroneseSectionPolynomialListDesc_one_eq_oneSupportSeq (r := r) hr
  let last : Fin r := ⟨r - 1, by lia⟩
  refine ⟨?_, ?_⟩
  · rw [hlist]
    exact isInterlacingSeq0Nonneg_oneSupportSeq last
  · intro f hf hf0
    rw [hlist] at hf
    rcases List.mem_iff_get.1 hf with ⟨i, hi⟩
    let j : Fin r := ⟨i.1, by simpa [oneSupportSeq] using i.2⟩
    have hget :
        (oneSupportSeq r last).get i =
          (if j = last then (1 : ℝ[X]) else 0) := by
      simpa [j, last] using get_oneSupportSeq last j
    by_cases hidx : j = last
    · have hf_eq : f = 1 := by lia
      simp_all
    · lia

/-- General monic product case for the matrix route: for any product of
linear factors `X + a` with `a ≥ 0`, the descending Veronese sections are
weakly interlacing, and every nonzero section is real-rooted. -/
theorem isInterlacingSeq0Nonneg_and_real_veroneseSectionPolynomialListDesc_linearFactorProduct
    {r : ℕ} (hr : 0 < r) {as : List ℝ}
    (has : ∀ a ∈ as, 0 ≤ a) :
    IsInterlacingSeq0Nonneg
        (veroneseSectionPolynomialListDesc r (linearFactorProduct as)) ∧
      ∀ f ∈ veroneseSectionPolynomialListDesc r (linearFactorProduct as),
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  induction as with
  | nil =>
      simpa [linearFactorProduct] using
        isInterlacingSeq0Nonneg_and_real_veroneseSectionPolynomialListDesc_one
          (r := r) hr
  | cons a as ih =>
      have ha : 0 ≤ a := has a (by simp)
      have has_tail : ∀ b ∈ as, 0 ≤ b := by simp_all
      have htail := ih has_tail
      simpa [linearFactorProduct] using
        isInterlacingSeq0Nonneg_and_real_veroneseSectionPolynomialListDesc_X_add_C_mul
          (r := r) hr (a := a) ha (p := linearFactorProduct as) htail.1 htail.2

lemma linearFactorProduct_neg_roots_eq_rootsProduct (p : ℝ[X]) :
    linearFactorProduct (p.roots.toList.map fun x => -x) =
      (p.roots.map fun x => X - C x).prod := by
  unfold linearFactorProduct
  grind

lemma veroneseSectionPolynomialListDesc_C_mul
    {r : ℕ} (hr : 0 < r) (c : ℝ) (p : ℝ[X]) :
    veroneseSectionPolynomialListDesc r (C c * p) =
      (veroneseSectionPolynomialListDesc r p).map (fun q => C c * q) := by
  apply List.ext_get
  · simp
  · intro n hn₁ hn₂
    let i : Fin r := ⟨n, by simp_all⟩
    rw [show (veroneseSectionPolynomialListDesc r (C c * p)).get ⟨n, hn₁⟩ =
        veroneseSectionPolynomial r (r - 1 - i.1) (C c * p) by
      simpa [i] using get_veroneseSectionPolynomialListDesc (r := r) (p := C c * p) i]
    rw [show ((veroneseSectionPolynomialListDesc r p).map (fun q => C c * q)).get
        ⟨n, hn₂⟩ =
        C c * veroneseSectionPolynomial r (r - 1 - i.1) p by
      simp [List.get_eq_getElem, veroneseSectionPolynomialListDesc, i]]
    exact veroneseSectionPolynomial_C_mul hr c p

lemma prec0_C_mul_both {c : ℝ} (hc : c ≠ 0) {f g : ℝ[X]}
    (h : Prec0 f g) : Prec0 (C c * f) (C c * g) := by
  rcases h with hf | hg | hprec
  · left
    simp [hf]
  · right
    simp_all
  · exact Or.inr (Or.inr (prec_C_mul_right (prec_C_mul_left hprec hc) hc))

lemma isInterlacingSeq0Nonneg_map_C_mul
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc : c ≠ 0) {fs : List ℝ[X]}
    (hfs : IsInterlacingSeq0Nonneg fs) :
    IsInterlacingSeq0Nonneg (fs.map fun q => C c * q) := by
  refine ⟨?_, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise]
    refine List.pairwise_iff_get.2 ?_
    intro i j hij
    let i' : Fin fs.length := ⟨i.1, by grind⟩
    let j' : Fin fs.length := ⟨j.1, by grind⟩
    have hij' : i' < j' := by grind
    have hprec0 := hfs.1.prec0 (i := i') (j := j') hij'
    simpa [i', j'] using prec0_C_mul_both hc hprec0
  · intro p hp
    rcases List.mem_map.1 hp with ⟨q, hq, rfl⟩
    exact nonnegCoeffs_C_mul hc_nonneg (hfs.2 q hq)

lemma realRooted_mem_map_C_mul_of_realRooted
    {c : ℝ} (hc : c ≠ 0) {fs : List ℝ[X]}
    (hreal : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    ∀ f ∈ fs.map (fun q => C c * q), f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  simp_all

/-- General real-rooted nonnegative-coefficient case: the descending Veronese
sections are weakly interlacing, and every nonzero section is real-rooted. -/
theorem isInterlacingSeq0Nonneg_and_real_veroneseSectionPolynomialListDesc_of_realRooted_nonneg
    {r : ℕ} (hr : 0 < r) {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hprr_ne : p ≠ 0) (hprr_splits : p.Splits) :
    IsInterlacingSeq0Nonneg (veroneseSectionPolynomialListDesc r p) ∧
      ∀ f ∈ veroneseSectionPolynomialListDesc r p, f ≠ 0 → (f ≠ 0 ∧
        f.Splits) := by
  let as := p.roots.toList.map fun x => -x
  have has : ∀ a ∈ as, 0 ≤ a := by
    intro a ha
    rcases List.mem_map.1 ha with ⟨x, hx, rfl⟩
    have hx_root : x ∈ p.roots := Multiset.mem_toList.mp hx
    linarith [roots_nonpos_of_nonneg_coeffs hprr_splits hpnn x hx_root]
  have hprod := linearFactorProduct_neg_roots_eq_rootsProduct p
  have hfac :
      C p.leadingCoeff * linearFactorProduct as = p := by
    rw [hprod]
    exact Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
      (card_roots_of_splits hprr_splits)
  have hlead_pos : 0 < p.leadingCoeff := hpnn.pos_leadingCoeff hprr_ne
  have hlead_ne : p.leadingCoeff ≠ 0 := ne_of_gt hlead_pos
  have hpkg :=
    isInterlacingSeq0Nonneg_and_real_veroneseSectionPolynomialListDesc_linearFactorProduct
      (r := r) hr has
  have hlist :
      veroneseSectionPolynomialListDesc r p =
        (veroneseSectionPolynomialListDesc r (linearFactorProduct as)).map
          (fun q => C p.leadingCoeff * q) := by
    calc
      veroneseSectionPolynomialListDesc r p =
          veroneseSectionPolynomialListDesc r
            (C p.leadingCoeff * linearFactorProduct as) := by
            lia
      _ = (veroneseSectionPolynomialListDesc r (linearFactorProduct as)).map
          (fun q => C p.leadingCoeff * q) :=
            veroneseSectionPolynomialListDesc_C_mul hr p.leadingCoeff (linearFactorProduct as)
  refine ⟨?_, ?_⟩
  · rw [hlist]
    exact isInterlacingSeq0Nonneg_map_C_mul hlead_pos.le hlead_ne hpkg.1
  · simp_all

/-- In particular, each Veronese section of a real-rooted polynomial with
nonnegative coefficients is real-rooted, allowing the section to vanish. -/
theorem isRealRootedOrZero_veroneseSectionPolynomial_of_realRooted_nonneg_matrix
    {r k : ℕ} (hr : 0 < r) (hk : k < r) {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hprr_ne : p ≠ 0) (hprr_splits : p.Splits) :
    veroneseSectionPolynomial r k p = 0 ∨
      (veroneseSectionPolynomial r k p).Splits := by
  have hpkg :=
    isInterlacingSeq0Nonneg_and_real_veroneseSectionPolynomialListDesc_of_realRooted_nonneg
      (r := r) hr hpnn hprr_ne hprr_splits
  have hmem := mem_veroneseSectionPolynomialListDesc (r := r) (k := k) p hk
  by_cases hzero : veroneseSectionPolynomial r k p = 0
  · exact Or.inl hzero
  · exact Or.inr (hpkg.2 _ hmem hzero).2

end RealRooted
