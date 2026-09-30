import RealRooted.AffineFamily

/-!
# Interlacing for affine polynomials

Elementary interlacing lemmas for constants and positive-slope affine
polynomials.  These facts are shared by the Veronese and threshold-matrix
developments, so they live below both application layers.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Any two constant polynomials are in zero-aware interlacing. -/
lemma interl_C_C (a b : ℝ) : Interl (C a : ℝ[X]) (C b : ℝ[X]) := by
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
  have hrr_a : ((C a : ℝ[X]) ≠ 0 ∧ (C a : ℝ[X]).Splits) :=
    isRealRooted_of_deg_zero hCa (by simp)
  have hrr_b : ((C b : ℝ[X]) ≠ 0 ∧ (C b : ℝ[X]).Splits) :=
    isRealRooted_of_deg_zero hCb (by simp)
  refine ⟨hrr_a, hrr_b, [], [], by simp, by simp, by simp, by simp, ?_⟩
  exact Or.inr ⟨by lia, by simp [ListAlternates]⟩

/-- Factoring out `X` after adding it to an affine multiple of `X`. -/
lemma affine_mul_X_add_X_eq (s t : ℝ) :
    ((C s * X + C t) * X + X : ℝ[X]) =
      X * (C s * X + C (t + 1)) := by
  grind

/-- The polynomial obtained by adding `X` to a positive-slope affine multiple
of `X` is nonzero and real-rooted. -/
lemma isRealRooted_affine_mul_X_add_X {s t : ℝ} (hs : 0 < s) :
    (((C s * X + C t) * X + X : ℝ[X]) ≠ 0 ∧
      ((C s * X + C t) * X + X : ℝ[X]).Splits) := by
  rw [affine_mul_X_add_X_eq]
  exact isRealRooted_X_mul
    (isRealRooted_affine_factor (s := s) (t := t + 1) hs).1
    (isRealRooted_affine_factor (s := s) (t := t + 1) hs).2

/-- A cross-product inequality orders the roots of two positive-slope affine
polynomials. -/
lemma affineLinear_root_le_of_cross {u v U V : ℝ}
    (hu : 0 < u) (hU : 0 < U) (hcross : u * V ≤ U * v) :
    -(u⁻¹ * v) ≤ -(U⁻¹ * V) := by
  rw [neg_le_neg_iff]
  rw [← div_eq_inv_mul, ← div_eq_inv_mul]
  rw [div_le_div_iff₀ hU hu]
  grind

/-- Positive-slope affine polynomials strictly interlace when their
coefficient cross product has the corresponding order. -/
lemma strictInterl_affine_linear_affine_linear_of_cross
    {u v U V : ℝ} (hu : 0 < u) (hU : 0 < U)
    (hcross : u * V ≤ U * v) :
    StrictInterl (C u * X + C v) (C U * X + C V) := by
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

/-- Zero-aware form of
`strictInterl_affine_linear_affine_linear_of_cross`. -/
lemma interl_affine_linear_affine_linear_of_cross
    {u v U V : ℝ} (hu : 0 < u) (hU : 0 < U)
    (hcross : u * V ≤ U * v) :
    Interl (C u * X + C v) (C U * X + C V) :=
  (strictInterl_affine_linear_affine_linear_of_cross hu hU hcross).toInterl

lemma interl_C_affine_linear {c u v : ℝ} (hu : 0 < u) :
    Interl (C c : ℝ[X]) (C u * X + C v) := by
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
  have hC_rr : ((C c : ℝ[X]) ≠ 0 ∧ (C c : ℝ[X]).Splits) :=
    isRealRooted_of_deg_zero hC (by simp)
  refine ⟨hC_rr, hlin_rr, [], [-(u⁻¹ * v)], by simp, by simp, ?_, ?_, ?_⟩
  · simp
  · simpa [hlin_deg] using
      (Polynomial.roots_degree_eq_one (p := (C u * X + C v : ℝ[X])) hlin_deg).symm
  · exact Or.inl ⟨by simp, by simp [ListInterlaces]⟩

lemma interl_congr {p q p' q' : ℝ[X]} (hp : p = p') (hq : q = q')
    (h : Interl p' q') : Interl p q := by
  lia

lemma affine_mul_C_add_C (s t b d : ℝ) :
    ((C s * X + C t) * C b + C d : ℝ[X]) =
      C (s * b) * X + C (t * b + d) := by
  grind

lemma interl_const_entries_affine_of_det_nonneg
    {A b c d s t : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 < s) (hdet : b * c ≤ A * d) :
    Interl ((C s * X + C t) * C b + C d)
      ((C s * X + C t) * C A + C c) := by
  by_cases hb0 : b = 0
  · by_cases hA0 : A = 0
    · refine
        interl_congr (p' := C d) (q' := C c) ?_ ?_
          (interl_C_C d c)
      · simp [hb0]
      · simp [hA0]
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
      refine
        interl_congr (p' := C d)
          (q' := C (s * A) * X + C (t * A + c)) ?_ ?_ ?_
      · simp [hb0]
      · grind
      · exact
          interl_C_affine_linear (c := d) (u := s * A) (v := t * A + c)
            (by simp_all)
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    by_cases hA0 : A = 0
    · have hc0 : c = 0 := by nlinarith [hdet, hbpos, hc]
      refine interl_congr (q' := 0) rfl ?_ (interl_zero_right _)
      simp_all
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
      have hcross : (b * s) * (A * t + c) ≤ (A * s) * (b * t + d) := by
        nlinarith [hdet, hs]
      refine
        interl_congr
          (p' := C (b * s) * X + C (b * t + d))
          (q' := C (A * s) * X + C (A * t + c)) ?_ ?_ ?_
      · grind
      · grind
      · exact
          interl_affine_linear_affine_linear_of_cross
            (u := b * s) (v := b * t + d) (U := A * s) (V := A * t + c)
            (by simp_all) (by simp_all) hcross

lemma interl_affine_add_one_affine_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t + 1) (C s * X + C t + X) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    interl_affine_linear_affine_linear_of_cross
      (u := s) (v := t + 1) (U := s + 1) (V := t)
      hs (by positivity) (by linarith [hs, ht])

lemma interl_affine_add_X_self {s t : ℝ} (hs : 0 < s) :
    Interl (C s * X + C t + X) (C s * X + C t + X) := by
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact interl_affine_linear_affine_linear_of_cross
    (by positivity) (by positivity) le_rfl

lemma interl_affine_add_one_self {s t : ℝ} (hs : 0 < s) :
    Interl (C s * X + C t + 1) (C s * X + C t + 1) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  exact interl_affine_linear_affine_linear_of_cross hs hs le_rfl

@[deprecated interl_C_C (since := "2026-09-18")]
alias prec0_C_C := interl_C_C

@[deprecated strictInterl_affine_linear_affine_linear_of_cross
  (since := "2026-09-18")]
alias prec_affine_linear_affine_linear_of_cross :=
  strictInterl_affine_linear_affine_linear_of_cross

@[deprecated interl_affine_linear_affine_linear_of_cross
  (since := "2026-09-18")]
alias prec0_affine_linear_affine_linear_of_cross :=
  interl_affine_linear_affine_linear_of_cross

@[deprecated interl_congr (since := "2026-09-18")]
alias prec0_congr := interl_congr

@[deprecated interl_const_entries_affine_of_det_nonneg
  (since := "2026-09-18")]
alias prec0_const_entries_affine_of_det_nonneg :=
  interl_const_entries_affine_of_det_nonneg

/-- A positive affine form precedes the `X`-multiple of another one under the
cross inequality. -/
theorem interl_affine_to_X_mul_affine
    {u v U V : ℝ}
    (hu : 0 < u) (hU : 0 < U) (hcross : u * V ≤ U * v)
    (hv : 0 ≤ v) (hV : 0 ≤ V) :
    Interl (C U * X + C V) (X * (C u * X + C v)) :=
  (strictInterl_to_strictInterl_mul_X_of_nonneg
    (strictInterl_affine_linear_affine_linear_of_cross hu hU hcross)
    (hasNonnegCoeffs_affine_linear hu.le hv)
    (hasNonnegCoeffs_affine_linear hU.le hV)).toInterl

/-! ### Affine interlacing certificates

Interlacing between the constants `1` and `X`, the affine forms `s X + t`, and
their `X`-multiples, used by the 2×2 matrix-interlacing and threshold-matrix
certificates. -/

theorem interl_one_one : Interl (1 : ℝ[X]) 1 := by
  simpa using interl_C_C (1 : ℝ) 1

theorem interl_one_X : Interl (1 : ℝ[X]) X := by
  simpa using interl_C_affine_linear (c := 1) (u := 1) (v := 0) zero_lt_one

theorem interl_one_affine {s t : ℝ} (hs : 0 < s) :
    Interl (1 : ℝ[X]) (C s * X + C t) := by
  simpa using interl_C_affine_linear (c := 1) (u := s) (v := t) hs

theorem interl_one_affine_add_one {s t : ℝ} (hs : 0 < s) :
    Interl (1 : ℝ[X]) (C s * X + C t + 1) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  exact interl_C_affine_linear hs

theorem interl_one_affine_add_X {s t : ℝ} (hs : 0 < s) :
    Interl (1 : ℝ[X]) (C s * X + C t + X) := by
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact interl_C_affine_linear (by positivity)

theorem interl_X_X : Interl (X : ℝ[X]) X :=
  Interl.refl fun _ => isRealRooted_X.2

theorem interl_affine_X {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t) X := by
  simpa using interl_affine_linear_affine_linear_of_cross
    (u := s) (v := t) (U := 1) (V := 0) hs zero_lt_one (by nlinarith)

theorem interl_affine_add_one_X {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t + 1) X := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  simpa using interl_affine_linear_affine_linear_of_cross
    (u := s) (v := t + 1) (U := 1) (V := 0)
    hs zero_lt_one (by nlinarith)

theorem interl_affine_add_X_X {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t + X) X := by
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  simpa using interl_affine_linear_affine_linear_of_cross
    (u := s + 1) (v := t) (U := 1) (V := 0)
    (by positivity) zero_lt_one (by nlinarith)

theorem interl_affine_self {s t : ℝ} (hs : 0 < s) :
    Interl (C s * X + C t) (C s * X + C t) :=
  Interl.refl fun _ => (isRealRooted_affine_factor hs).2

theorem interl_affine_add_one_affine {s t : ℝ} (hs : 0 < s) :
    Interl (C s * X + C t + 1) (C s * X + C t) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  exact interl_affine_linear_affine_linear_of_cross hs hs (by nlinarith)

theorem interl_affine_affine_add_X {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t) (C s * X + C t + X) := by
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact interl_affine_linear_affine_linear_of_cross
    hs (by positivity) (by nlinarith)

theorem interl_X_affine_mul_X {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl X ((C s * X + C t) * X) := by
  rw [mul_comm]
  simpa using interl_affine_to_X_mul_affine
    (u := s) (v := t) (U := 1) (V := 0)
    hs zero_lt_one (by nlinarith) ht.le le_rfl

theorem interl_X_affine_mul_X_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl X ((C s * X + C t) * X + X) := by
  rw [show ((C s * X + C t) * X + X : ℝ[X]) =
    X * (C s * X + C (t + 1)) by grind]
  simpa using interl_affine_to_X_mul_affine
    (u := s) (v := t + 1) (U := 1) (V := 0)
    hs zero_lt_one (by nlinarith) (by positivity) le_rfl

theorem interl_affine_affine_mul_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t) ((C s * X + C t) * X) := by
  rw [show ((C s * X + C t) * X : ℝ[X]) = X * (C s * X + C t) by ring]
  exact interl_affine_to_X_mul_affine
    (u := s) (v := t) (U := s) (V := t) hs hs le_rfl ht.le ht.le

theorem interl_affine_add_X_affine_mul_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t + X) ((C s * X + C t) * X) := by
  rw [show ((C s * X + C t) * X : ℝ[X]) = X * (C s * X + C t) by ring]
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact interl_affine_to_X_mul_affine
    (u := s) (v := t) (U := s + 1) (V := t)
    hs (by positivity) (by nlinarith) ht.le ht.le

theorem interl_affine_affine_mul_X_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t) ((C s * X + C t) * X + X) := by
  rw [show ((C s * X + C t) * X + X : ℝ[X]) =
    X * (C s * X + C (t + 1)) by grind]
  exact interl_affine_to_X_mul_affine
    hs hs (by nlinarith) (by positivity) ht.le

theorem interl_affine_add_one_affine_mul_X_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t + 1) ((C s * X + C t) * X + X) := by
  rw [show ((C s * X + C t) * X + X : ℝ[X]) =
    X * (C s * X + C (t + 1)) by grind]
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  exact interl_affine_to_X_mul_affine hs hs le_rfl (by positivity) (by positivity)

theorem interl_affine_add_X_affine_mul_X_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl (C s * X + C t + X) ((C s * X + C t) * X + X) := by
  rw [show ((C s * X + C t) * X + X : ℝ[X]) =
    X * (C s * X + C (t + 1)) by grind]
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact interl_affine_to_X_mul_affine
    hs (by positivity) (by nlinarith [hs, ht]) (by positivity) ht.le

theorem interl_affine_mul_X_self {s t : ℝ} (hs : 0 < s) :
    Interl ((C s * X + C t) * X) ((C s * X + C t) * X) := by
  rw [show ((C s * X + C t) * X : ℝ[X]) = X * (C s * X + C t) by ring]
  exact Interl.refl fun _ => (isRealRooted_X_mul (isRealRooted_affine_factor hs).1
    (isRealRooted_affine_factor hs).2).2

theorem interl_affine_mul_X_add_X_affine_mul_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Interl ((C s * X + C t) * X + X) ((C s * X + C t) * X) := by
  rw [show ((C s * X + C t) * X + X : ℝ[X]) =
    X * (C s * X + C (t + 1)) by grind]
  rw [show ((C s * X + C t) * X : ℝ[X]) = X * (C s * X + C t) by ring]
  have hleft_nonneg : HasNonnegCoeffs (C s * X + C t + 1 : ℝ[X]) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact hasNonnegCoeffs_affine_linear hs.le (by positivity)
  simpa [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind] using
    (interl_affine_add_one_affine (t := t) hs).mul_X_both_of_nonneg
      hleft_nonneg
      (hasNonnegCoeffs_affine_linear (a := s) (b := t) hs.le ht.le)

theorem interl_affine_mul_X_add_X_self {s t : ℝ} (hs : 0 < s) :
    Interl ((C s * X + C t) * X + X) ((C s * X + C t) * X + X) := by
  rw [show ((C s * X + C t) * X + X : ℝ[X]) =
    X * (C s * X + C (t + 1)) by grind]
  exact Interl.refl fun _ => (isRealRooted_X_mul
    (isRealRooted_affine_factor (t := t + 1) hs).1
    (isRealRooted_affine_factor (t := t + 1) hs).2).2

end RealRooted
