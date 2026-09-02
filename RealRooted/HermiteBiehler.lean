import RealRooted.AissenSchoenbergWhitney
import RealRooted.Basic
import RealRooted.Bezoutian
import RealRooted.CommonInterleaverTwo
import RealRooted.HermiteBiehler.Basic
import RealRooted.HermiteBiehler.ConverseLowDegree
import RealRooted.HermiteBiehler.Forward
import RealRooted.HermiteBiehler.OddEven
import RealRooted.Interlacing.Multiplicity
import RealRooted.Interlacing.Residue
import Mathlib.Data.Complex.Basic

open Polynomial

noncomputable section

namespace RealRooted


lemma norm_conj_sub_le {z w : ℂ} (hz : 0 < z.im) (hw : w.im ≤ 0) :
    ‖(starRingEnd ℂ) z - w‖ ≤ ‖z - w‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im]
  nlinarith [mul_nonneg hz.le (neg_nonneg.mpr hw)]

lemma norm_conj_sub_lt {z w : ℂ} (hz : 0 < z.im) (hw : w.im < 0) :
    ‖(starRingEnd ℂ) z - w‖ < ‖z - w‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_lt_sqrt (Complex.normSq_nonneg _)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im]
  nlinarith [mul_pos hz (neg_pos.mpr hw)]

lemma multiset_prod_norm_conj_le {z : ℂ} (hz : 0 < z.im) (S : Multiset ℂ)
    (hS : ∀ w ∈ S, w.im ≤ 0) :
    ‖(S.map fun w => (starRingEnd ℂ) z - w).prod‖ ≤ ‖(S.map fun w => z - w).prod‖ := by
  induction S using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    have ha := hS a (Multiset.mem_cons_self a s)
    have hs : ∀ w ∈ s, w.im ≤ 0 := fun w hw => hS w (Multiset.mem_cons_of_mem hw)
    exact mul_le_mul (norm_conj_sub_le hz ha) (ih hs) (norm_nonneg _) (norm_nonneg _)

lemma multiset_prod_norm_conj_lt {z : ℂ} (hz : 0 < z.im) (S : Multiset ℂ)
    (hS : ∀ w ∈ S, w.im ≤ 0) {w₀ : ℂ} (hw₀ : w₀ ∈ S) (hneg : w₀.im < 0) :
    ‖(S.map fun w => (starRingEnd ℂ) z - w).prod‖ < ‖(S.map fun w => z - w).prod‖ := by
  obtain ⟨S', rfl⟩ : ∃ S', S = w₀ ::ₘ S' :=
    ⟨S.erase w₀, (Multiset.cons_erase hw₀).symm⟩
  simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
  have hS' : ∀ w ∈ S', w.im ≤ 0 := fun w hw => hS w (Multiset.mem_cons_of_mem hw)
  have h_norm_pos : 0 < ‖(S'.map fun w => z - w).prod‖ := by
    rw [norm_pos_iff]
    apply Multiset.prod_ne_zero
    intro h_zero
    obtain ⟨w, hw, hzw⟩ := Multiset.mem_map.mp h_zero
    have him : (z - w).im = 0 := by simp [*]
    have := hS' w hw
    simp only [Complex.sub_im] at him
    linarith
  calc ‖(starRingEnd ℂ) z - w₀‖ * ‖(S'.map fun w => (starRingEnd ℂ) z - w).prod‖
      ≤ ‖(starRingEnd ℂ) z - w₀‖ * ‖(S'.map fun w => z - w).prod‖ :=
        mul_le_mul_of_nonneg_left (multiset_prod_norm_conj_le hz S' hS') (norm_nonneg _)
    _ < ‖z - w₀‖ * ‖(S'.map fun w => z - w).prod‖ :=
        mul_lt_mul_of_pos_right (norm_conj_sub_lt hz hneg) h_norm_pos

lemma eval_eq_prod_roots_complex (p : ℂ[X]) (x : ℂ) :
    p.eval x = p.leadingCoeff * (p.roots.map fun a => x - a).prod :=
  (IsAlgClosed.splits p).eval_eq_prod_roots x

lemma roots_real_of_stable_norm_eq {p : ℂ[X]} (hp : p ≠ 0)
    (hstab : IsUpperHalfPlaneStable p) {z : ℂ} (hz : 0 < z.im)
    (heq : ‖p.eval ((starRingEnd ℂ) z)‖ = ‖p.eval z‖) :
    ∀ w ∈ p.roots, w.im = 0 := by
  intro w₀ hw₀
  by_contra hne
  have hle : ∀ w ∈ p.roots, w.im ≤ 0 := fun w hw =>
    im_nonpos_of_stable_root hstab (isRoot_of_mem_roots hw)
  have hneg : w₀.im < 0 := lt_of_le_of_ne (hle w₀ hw₀) hne
  have :
      ‖(p.roots.map fun w ↦ starRingEnd ℂ z - w).prod‖ <
        ‖(p.roots.map fun w ↦ z - w).prod‖ :=
    multiset_prod_norm_conj_lt hz p.roots hle hw₀ hneg
  rw [eval_eq_prod_roots_complex p, eval_eq_prod_roots_complex p, norm_mul, norm_mul] at heq
  simp_all

lemma no_upper_root_left_of_stable {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hf : HasPosLeadingCoeff f)
    {z : ℂ} (hz : 0 < z.im) (hroot : (complexify f).eval z = 0) : False := by
  set h := hermiteBiehlerPolynomial f g with hh
  have hzim : z.im ≠ 0 := hz.ne'
  have : (complexify g).eval z ≠ 0 := fun hg₀ ↦
    no_common_nonreal_root_of_stable hstab hzim hroot hg₀
  have : h.eval z = Complex.I * (complexify g).eval z := by simp [*]
  have hhz : h.eval z ≠ 0 := by simp [*]
  have hne : h ≠ 0 := fun h_zero ↦ hhz (by rw [h_zero, eval_zero])
  have : h.eval ((starRingEnd ℂ) z) =
      Complex.I * (starRingEnd ℂ) ((complexify g).eval z) := by
    rw [hh, eval_hermiteBiehlerPolynomial, eval_complexify_conj, eval_complexify_conj,
      hroot, map_zero, zero_add]
  have heq : ‖h.eval ((starRingEnd ℂ) z)‖ = ‖h.eval z‖ := by simp_all
  have hroots : ∀ w ∈ h.roots, w.im = 0 :=
    roots_real_of_stable_norm_eq hne hstab hz heq
  set P : ℂ[X] := (h.roots.map fun r ↦ X - C r).prod with hP
  have hfac : h = C h.leadingCoeff * P := (IsAlgClosed.splits (k := ℂ) h).eq_prod_roots
  have hevalh : h.eval z = h.leadingCoeff * P.eval z := by
    conv_lhs => rw [hfac]
    simp
  have hevalhc : (h.map (starRingEnd ℂ)).eval z =
      (starRingEnd ℂ) h.leadingCoeff * P.eval z := by
    rw [map_conj_of_roots_real hroots, eval_mul, eval_C]
  have hsum : h + h.map (starRingEnd ℂ) = 2 * complexify f := by
    rw [hh, hermiteBiehler_map_conj, hermiteBiehlerPolynomial]
    ring
  have hzero : (h.leadingCoeff + (starRingEnd ℂ) h.leadingCoeff) * P.eval z = 0 := by
    have hev := congrArg (fun q : ℂ[X] ↦ q.eval z) hsum
    simp only [eval_add, eval_mul, eval_ofNat] at hev
    rw [hroot, mul_zero, hevalh, hevalhc] at hev
    rw [add_mul]
    exact hev
  have hPz : P.eval z ≠ 0 := by
    intro hP₀
    apply hhz
    rw [hevalh, hP₀, mul_zero]
  have hlceq : (starRingEnd ℂ) h.leadingCoeff = -h.leadingCoeff := by
    rcases mul_eq_zero.mp hzero with hc | hc
    · exact eq_neg_of_add_eq_zero_right hc
    · exact absurd hc hPz
  have hmapneg := map_conj_neg_of_roots_real hlceq hroots
  rw [hh] at hmapneg
  have hf₀ : f = 0 := f_eq_zero_of_hermiteBiehler_map_conj_neg hmapneg
  simp_all

lemma no_upper_root_right_of_stable {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hg : HasPosLeadingCoeff g)
    {z : ℂ} (hz : 0 < z.im) (hroot : (complexify g).eval z = 0) : False := by
  set h := hermiteBiehlerPolynomial f g with hh
  have hzim : z.im ≠ 0 := hz.ne'
  have : (complexify f).eval z ≠ 0 := fun hf₀ ↦
    no_common_nonreal_root_of_stable hstab hzim hf₀ hroot
  have : h.eval z = (complexify f).eval z := by simp [*]
  have hhz : h.eval z ≠ 0 := by simp [*]
  have hne : h ≠ 0 := fun h_zero ↦ hhz (by rw [h_zero, eval_zero])
  have : h.eval ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((complexify f).eval z) := by
    rw [hh, eval_hermiteBiehlerPolynomial, eval_complexify_conj, eval_complexify_conj,
      hroot, map_zero, mul_zero, add_zero]
  have heq : ‖h.eval ((starRingEnd ℂ) z)‖ = ‖h.eval z‖ := by simp_all
  have hroots : ∀ w ∈ h.roots, w.im = 0 :=
    roots_real_of_stable_norm_eq hne hstab hz heq
  set P : ℂ[X] := (h.roots.map fun r ↦ X - C r).prod with hP
  have hfac : h = C h.leadingCoeff * P := (IsAlgClosed.splits (k := ℂ) h).eq_prod_roots
  have hevalh : h.eval z = h.leadingCoeff * P.eval z := by
    conv_lhs => rw [hfac]
    simp
  have hevalhc : (h.map (starRingEnd ℂ)).eval z =
      (starRingEnd ℂ) h.leadingCoeff * P.eval z := by
    rw [map_conj_of_roots_real hroots, eval_mul, eval_C]
  have hdiff : h - h.map (starRingEnd ℂ) = 2 * C Complex.I * complexify g := by
    rw [hh, hermiteBiehler_map_conj, hermiteBiehlerPolynomial]
    ring
  have hzero : (h.leadingCoeff - (starRingEnd ℂ) h.leadingCoeff) * P.eval z = 0 := by
    have hev := congrArg (fun q : ℂ[X] ↦ q.eval z) hdiff
    simp only [eval_sub, eval_mul, eval_ofNat, eval_C] at hev
    rw [hroot, mul_zero, hevalh, hevalhc] at hev
    rw [sub_mul]
    exact hev
  have hPz : P.eval z ≠ 0 := by
    intro hP₀
    apply hhz
    rw [hevalh, hP₀, mul_zero]
  have hlceq : (starRingEnd ℂ) h.leadingCoeff = h.leadingCoeff := by
    rcases mul_eq_zero.mp hzero with hc | hc
    · exact (sub_eq_zero.mp hc).symm
    · exact absurd hc hPz
  have hmapself := map_conj_self_of_roots_real hlceq hroots
  rw [hh] at hmapself
  have hg₀ : g = 0 := g_eq_zero_of_hermiteBiehler_map_conj_self hmapself
  simp_all

theorem splits_of_stable {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    f.Splits ∧ g.Splits := by
  constructor
  · apply Polynomial.splits_of_all_roots_real
    intro z hz
    by_contra him
    rcases lt_or_gt_of_ne him with hlt | hgt
    · exact no_upper_root_left_of_stable hstab hf (by simp [*]) (complexify_conj_root hz)
    · exact no_upper_root_left_of_stable hstab hf hgt hz
  · apply Polynomial.splits_of_all_roots_real
    intro z hz
    by_contra him
    rcases lt_or_gt_of_ne him with hlt | hgt
    · exact no_upper_root_right_of_stable hstab hg (by simp [*]) (complexify_conj_root hz)
    · exact no_upper_root_right_of_stable hstab hg hgt hz

/-- Planning stub for the converse Hermite--Biehler theorem.

The exact orientation hypotheses may still be adjusted, but the target is that
upper-half-plane stability of `f + i g` forces an interlacing relation between
-/
abbrev hermiteBiehlerConverseStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) →
    Prec g f ∨ Prec f g

/-- Analytic bridge from the Hermite--Biehler stable polynomial `q + i p` to
right-half-plane stability of `q(x^2) + x p(x^2)`.

This isolates the classical conformal-substitution part of the
-/
abbrev HermiteBiehlerStableToHurwitzOddEvenStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) →
    IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q))

/-! ## Reduction of the forward Hermite--Biehler/Hurwitz bridge to a
first-quadrant conformal-substitution interface -/

/-- Value of a complexified real polynomial at a real point. -/
theorem eval_complexify_ofReal (p : ℝ[X]) (t : ℝ) :
    (complexify p).eval (t : ℂ) = ((p.eval t : ℝ) : ℂ) := by
  simpa [complexify] using Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := p) t

/-- First-quadrant form of the forward Hermite--Biehler/Hurwitz conformal
substitution: it suffices to exclude roots of `q(x²) + x p(x²)` in the open
first quadrant `{Re > 0, Im > 0}`. -/
abbrev HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) →
    ∀ z : ℂ, 0 < z.re → 0 < z.im →
      (complexify (oddEvenPolynomial p q)).eval z ≠ 0

/-- Upper-half-plane substitution form of the forward Hermite--Biehler/Hurwitz
bridge: for any upper-half-plane point `w` with a right-half-plane square root
`z`, the Hurwitz combination `q(w) + z·p(w)` is nonzero.

This is the genuinely analytic conformal-substitution core: the quadratic map
`z ↦ z²` sends the open first quadrant onto the open upper half-plane, so this
interface and the first-quadrant interface above carry exactly the same
content. -/
abbrev HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) →
    ∀ ⦃w z : ℂ⦄, 0 < w.im → z ^ 2 = w → 0 < z.re →
      (complexify q).eval w + z * (complexify p).eval w ≠ 0

/-- The first-quadrant interface follows from the upper-half-plane substitution
interface: for `z` in the open first quadrant, `w = z²` lies in the open upper
half-plane and `z` is a right-half-plane square root of `w`. -/
theorem hermiteBiehlerStableToHurwitzOddEvenFirstQuadrant_of_upperHalfSubstitution
    (h : HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement) :
    HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement :=
  fun p q h_p h_q h_stable z hzre hzim => by
  rw [eval_complexify_oddEvenPolynomial]
  have h_w : 0 < (z ^ 2).im := by
    rw [pow_two, Complex.mul_im]
    positivity
  simp [*]

/-- Checked reduction of the forward Hermite--Biehler/Hurwitz odd/even bridge to
its first-quadrant conformal-substitution core.

`HermiteBiehlerStableToHurwitzOddEvenStatement` follows from
`HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement`: the real-axis case
`Im z = 0` is handled by positivity of the nonnegative-coefficient polynomial
`q(x²) + x p(x²)`, and the lower half-plane case `Im z < 0` is reduced to the
first quadrant by complex conjugation. -/
theorem hermiteBiehlerStableToHurwitzOddEven_of_firstQuadrant
    (h : HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement) :
    HermiteBiehlerStableToHurwitzOddEvenStatement := by
  intro p q h_p h_q h_stable z hzre
  -- The odd/even polynomial is nonzero, otherwise the stability hypothesis fails.
  have h_f_ne : oddEvenPolynomial p q ≠ 0 := by
    intro h₀
    rw [oddEvenPolynomial_eq_zero_iff] at h₀
    obtain ⟨hp₀, hq₀⟩ := h₀
    have h_I := h_stable Complex.I (by simp)
    simp_all
  rcases lt_trichotomy z.im 0 with h_im | h_im | h_im
  · -- Lower half-plane: reduce to the first quadrant by conjugation.
    have h_conj := eval_complexify_conj (oddEvenPolynomial p q) z
    have h_re : 0 < (starRingEnd ℂ z).re := by simp [*]
    have h_ci : 0 < (starRingEnd ℂ z).im := by simp [*]
    have h_ne : (complexify (oddEvenPolynomial p q)).eval (starRingEnd ℂ z) ≠ 0 :=
      h h_p h_q h_stable (starRingEnd ℂ z) h_re h_ci
    intro h₀
    apply h_ne
    rw [h_conj, h₀, map_zero]
  · -- Real axis: positivity of the nonnegative-coefficient polynomial.
    have h_z : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [h_im]
    rw [h_z, eval_complexify_ofReal]
    have h_pos : 0 < (oddEvenPolynomial p q).eval z.re :=
      eval_pos_of_hasNonnegCoeffs (hasNonnegCoeffs_oddEvenPolynomial h_p h_q) h_f_ne hzre
    simpa using h_pos.ne'
  · -- First quadrant: the interface applies directly.
    exact h h_p h_q h_stable z hzre h_im

/-- Composite reduction: the forward Hermite--Biehler/Hurwitz odd/even bridge
follows from the upper-half-plane substitution interface. -/
theorem hermiteBiehlerStableToHurwitzOddEven_of_upperHalfSubstitution
    (h : HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement) :
    HermiteBiehlerStableToHurwitzOddEvenStatement :=
  hermiteBiehlerStableToHurwitzOddEven_of_firstQuadrant
    (hermiteBiehlerStableToHurwitzOddEvenFirstQuadrant_of_upperHalfSubstitution h)

/-- Packaging form of the analytic Hermite--Biehler-to-Hurwitz odd/even
bridge, including the coefficient half of `IsHurwitzStable`. -/
theorem isHurwitzStable_oddEvenPolynomial_of_hermiteBiehlerStableToHurwitz
    (h : HermiteBiehlerStableToHurwitzOddEvenStatement) {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsHurwitzStable (oddEvenPolynomial p q) :=
  ⟨hasNonnegCoeffs_oddEvenPolynomial hp hq, h hp hq hstable⟩

theorem eval_derivative_eq_sum_complex (p : ℂ[X]) (x : ℂ) :
    p.derivative.eval x
      = p.leadingCoeff * (p.roots.map (fun w =>
          ((p.roots.erase w).map (fun u => x - u)).prod)).sum :=
  (IsAlgClosed.splits p).eval_derivative x

theorem im_deriv_mul_conj_eq (p : ℂ[X]) (x : ℝ) :
    (p.derivative.eval (x : ℂ) * (starRingEnd ℂ) (p.eval (x : ℂ))).im
      = Complex.normSq p.leadingCoeff *
          (p.roots.map (fun w =>
            Complex.normSq ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod * w.im)).sum := by
  rw [eval_derivative_eq_sum_complex, eval_eq_prod_roots_complex, map_mul]
  set S := (p.roots.map (fun w =>
    ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod)).sum with hS
  set T := (p.roots.map (fun u => (x : ℂ) - u)).prod with hT
  have hre : p.leadingCoeff * S * ((starRingEnd ℂ) p.leadingCoeff * (starRingEnd ℂ) T)
      = ((Complex.normSq p.leadingCoeff : ℝ) : ℂ) * (S * (starRingEnd ℂ) T) := by
    rw [← Complex.mul_conj]
    ring
  rw [hre, Complex.im_ofReal_mul]
  congr 1
  rw [hS, ← Multiset.sum_map_mul_right, multiset_sum_im, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro w hw
  simp only [Function.comp_apply]
  rw [hT, ← Multiset.prod_map_erase (f := fun u => (x : ℂ) - u) hw, map_mul]
  set P := ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod with hP
  have hps : P * ((starRingEnd ℂ) ((x : ℂ) - w) * (starRingEnd ℂ) P)
      = ((Complex.normSq P : ℝ) : ℂ) * (starRingEnd ℂ) ((x : ℂ) - w) := by
    rw [← Complex.mul_conj]
    ring
  simp_all

theorem im_deriv_mul_conj_neg {p : ℂ[X]}
    (hroots : ∀ w ∈ p.roots, w.im ≤ 0)
    {x : ℝ} (hne : p.eval (x : ℂ) ≠ 0)
    {w₀ : ℂ} (hw₀ : w₀ ∈ p.roots) (hneg : w₀.im < 0) :
    (p.derivative.eval (x : ℂ) * (starRingEnd ℂ) (p.eval (x : ℂ))).im < 0 := by
  have hp₀ : p ≠ 0 := fun h_zero => hne (by simp [h_zero])
  rw [im_deriv_mul_conj_eq]
  have hlc : 0 < Complex.normSq p.leadingCoeff :=
    Complex.normSq_pos.mpr (leadingCoeff_ne_zero.mpr hp₀)
  apply mul_neg_of_pos_of_neg hlc
  have hfac : ∀ w ∈ p.roots,
      ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod ≠ 0 := by
    intro w hw hzero
    apply hne
    rw [eval_eq_prod_roots_complex, ← Multiset.prod_map_erase (f := fun u => (x : ℂ) - u) hw,
      hzero, mul_zero, mul_zero]
  rw [← Multiset.sum_map_erase (f := fun w =>
    Complex.normSq ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod * w.im) hw₀]
  have hterm :
      Complex.normSq ((p.roots.erase w₀).map (fun u => (x : ℂ) - u)).prod *
        w₀.im < 0 := by
    have hP : ((p.roots.erase w₀).map (fun u => (x : ℂ) - u)).prod ≠ 0 := hfac w₀ hw₀
    exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hP) hneg
  have hrest : ((p.roots.erase w₀).map (fun w =>
      Complex.normSq ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod * w.im)).sum ≤ 0 := by
    apply multiset_sum_nonpos
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
    have hwmem : w ∈ p.roots := Multiset.mem_of_mem_erase hw
    exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (hroots w hwmem)
  linarith

theorem derivative_hermiteBiehler (f g : ℝ[X]) :
    (hermiteBiehlerPolynomial f g).derivative
      = hermiteBiehlerPolynomial f.derivative g.derivative := by
  simp only [hermiteBiehlerPolynomial, complexify, derivative_add, derivative_C_mul,
    derivative_map]

theorem im_hb_deriv_mul_conj (f g : ℝ[X]) (x : ℝ) :
    ((hermiteBiehlerPolynomial f g).derivative.eval (x : ℂ) *
        (starRingEnd ℂ) ((hermiteBiehlerPolynomial f g).eval (x : ℂ))).im
      = f.eval x * g.derivative.eval x - f.derivative.eval x * g.eval x := by
  rw [derivative_hermiteBiehler, eval_hermiteBiehlerPolynomial, eval_hermiteBiehlerPolynomial,
    eval_complexify_ofReal, eval_complexify_ofReal, eval_complexify_ofReal,
    eval_complexify_ofReal]
  simp [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.conj_I,
    Complex.conj_ofReal]
  ring

theorem wronskian_pos_of_stable {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnoreal : ∀ t : ℝ, (hermiteBiehlerPolynomial f g).eval (t : ℂ) ≠ 0)
    {w₀ : ℂ} (hw₀ : w₀ ∈ (hermiteBiehlerPolynomial f g).roots) (hneg : w₀.im < 0)
    (t : ℝ) :
    0 < f.derivative.eval t * g.eval t - f.eval t * g.derivative.eval t := by
  have him := im_deriv_mul_conj_neg
    (fun w hw => im_nonpos_of_stable_root hstab (isRoot_of_mem_roots hw)) (hnoreal t) hw₀ hneg
  rw [im_hb_deriv_mul_conj] at him
  linarith

theorem prec_of_stable_same_degree {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnoreal : ∀ t : ℝ, (hermiteBiehlerPolynomial f g).eval (t : ℂ) ≠ 0)
    {w₀ : ℂ} (hw₀ : w₀ ∈ (hermiteBiehlerPolynomial f g).roots) (hneg : w₀.im < 0)
    (hdeg : f.natDegree = g.natDegree) : Prec g f := by
  obtain ⟨hfs, hgs⟩ := splits_of_stable hf hg hstab
  exact (StrictPrecSameDegree.of_wronskian_pos (n := f.natDegree) hg hf hdeg.symm rfl hgs hfs
    (fun t => wronskian_pos_of_stable hstab hnoreal hw₀ hneg t)).to_prec

theorem hnoreal_of_no_common_real_root {f g : ℝ[X]}
    (hnc : ¬ ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r) :
    ∀ t : ℝ, (hermiteBiehlerPolynomial f g).eval (t : ℂ) ≠ 0 := by
  intro t ht
  rw [eval_hermiteBiehlerPolynomial, eval_complexify_ofReal, eval_complexify_ofReal] at ht
  have hf : f.eval t = 0 := by simpa using congrArg Complex.re ht
  have hg : g.eval t = 0 := by simpa using congrArg Complex.im ht
  exact hnc ⟨t, hf, hg⟩

theorem exists_neg_root_of_stable_no_real {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnoreal : ∀ t : ℝ, (hermiteBiehlerPolynomial f g).eval (t : ℂ) ≠ 0)
    (hpos : 0 < (hermiteBiehlerPolynomial f g).natDegree) :
    ∃ w₀ ∈ (hermiteBiehlerPolynomial f g).roots, w₀.im < 0 := by
  have hsplits : (hermiteBiehlerPolynomial f g).Splits := IsAlgClosed.splits _
  have hne_roots : (hermiteBiehlerPolynomial f g).roots ≠ 0 := by
    intro h₀
    have h_card : (hermiteBiehlerPolynomial f g).roots.card = 0 := by simp [h₀]
    rw [splits_iff_card_roots.mp hsplits] at h_card
    rw [h_card] at hpos
    lia
  obtain ⟨w₀, hw₀⟩ := Multiset.exists_mem_of_ne_zero hne_roots
  refine ⟨w₀, hw₀, ?_⟩
  have h_le : w₀.im ≤ 0 := im_nonpos_of_stable_root hstab (isRoot_of_mem_roots hw₀)
  rcases lt_or_eq_of_le h_le with h_lt | h_eq
  · exact h_lt
  · exfalso
    have hreal : w₀ = ((w₀.re : ℝ) : ℂ) := Complex.ext rfl h_eq
    have hroot : (hermiteBiehlerPolynomial f g).eval w₀ = 0 := isRoot_of_mem_roots hw₀
    rw [hreal] at hroot
    exact hnoreal w₀.re hroot

theorem prec_of_stable_same_degree_no_common {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnc : ¬ ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r)
    (hdeg : f.natDegree = g.natDegree) (hfpos : 0 < f.natDegree) : Prec g f := by
  have hnoreal := hnoreal_of_no_common_real_root hnc
  have hlead : 0 < f.coeff f.natDegree := hf
  have : (hermiteBiehlerPolynomial f g).natDegree = f.natDegree :=
    (hermiteBiehler_natDegree_of_posLead hlead rfl hdeg.symm).1
  have hpos : 0 < (hermiteBiehlerPolynomial f g).natDegree := by simp_all
  obtain ⟨w₀, hw₀mem, hw₀neg⟩ := exists_neg_root_of_stable_no_real hstab hnoreal hpos
  exact prec_of_stable_same_degree hf hg hstab hnoreal hw₀mem hw₀neg hdeg

theorem prec_of_stable_succ_degree {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnc : ¬ ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r)
    (hdeg : f.natDegree = g.natDegree + 1) : Prec g f := by
  have hnoreal := hnoreal_of_no_common_real_root hnc
  have : (hermiteBiehlerPolynomial f g).natDegree = f.natDegree :=
    (hermiteBiehler_natDegree_of_left_dominant hf.ne_zero (by simp [*])).1
  have hpos : 0 < (hermiteBiehlerPolynomial f g).natDegree := by simp [*]
  obtain ⟨w₀, hw₀mem, hw₀neg⟩ := exists_neg_root_of_stable_no_real hstab hnoreal hpos
  obtain ⟨hfs, hgs⟩ := splits_of_stable hf hg hstab
  exact prec_of_wronskian_pos_succ hf hg hdeg rfl hfs hgs
    (fun t => wronskian_pos_of_stable hstab hnoreal hw₀mem hw₀neg t)

theorem isUpperHalfPlaneStable_cofactor_of_stable {f g : ℝ[X]} {r : ℝ}
    (hrf : f.IsRoot r) (hrg : g.IsRoot r)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    IsUpperHalfPlaneStable
      (hermiteBiehlerPolynomial (f /ₘ (X - C r)) (g /ₘ (X - C r))) := by
  intro z hz hroot
  refine hstab z hz ?_
  rw [hermiteBiehlerPolynomial_factor_common_root hrf hrg, eval_mul, hroot, mul_zero]

theorem hermiteBiehlerConverse_general :
    ∀ (n : ℕ) (f g : ℝ[X]), f.natDegree = n → HasPosLeadingCoeff f →
      HasPosLeadingCoeff g → IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) →
      Prec g f ∨ Prec f g := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f g h_fn hf hg hstab
    rcases Nat.lt_or_ge n 3 with h_lt | h_ge
    · exact hermiteBiehlerConverse_of_natDegree_le_two hf hg (by lia) hstab
    · by_cases hc : ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r
      · obtain ⟨r, hrf, hrg⟩ := hc
        set f₁ := f /ₘ (X - C r) with hf₁
        set g₁ := g /ₘ (X - C r) with hg₁
        have h_f_drop : f₁.natDegree = f.natDegree - 1 := by
          rw [hf₁, natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C]
        have h_f₁_pos : HasPosLeadingCoeff f₁ := by
          rw [HasPosLeadingCoeff, hf₁, leadingCoeff_divByMonic_X_sub_C hrf]; exact hf
        have h_g₁_pos : HasPosLeadingCoeff g₁ := by
          rw [HasPosLeadingCoeff, hg₁, leadingCoeff_divByMonic_X_sub_C hrg]; exact hg
        have h_stab₁ : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f₁ g₁) :=
          isUpperHalfPlaneStable_cofactor_of_stable hrf hrg hstab
        have h_lt₁ : f₁.natDegree < n := by rw [h_f_drop, h_fn]; lia
        rcases ih f₁.natDegree h_lt₁ f₁ g₁ rfl h_f₁_pos h_g₁_pos h_stab₁ with h | h
        · exact Or.inl (prec_of_prec_cofactor hrf hrg h)
        · exact Or.inr (prec_of_prec_cofactor hrg hrf h)
      · push Not at hc
        obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable hf hg hstab
        rcases Nat.lt_or_ge g.natDegree f.natDegree with h_g_lt | h_g_ge
        · exact Or.inl (prec_of_stable_succ_degree hf hg hstab (by
            simp_all) (by lia))
        · have h_deg : f.natDegree = g.natDegree := by lia
          exact Or.inl (prec_of_stable_same_degree_no_common hf hg hstab
            (by simp_all) h_deg (by lia))

theorem hermiteBiehlerConverse {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    Prec g f ∨ Prec f g :=
  hermiteBiehlerConverse_general f.natDegree f g rfl hf hg h

theorem ratio_cofactor_eq {f g : ℝ[X]} {r : ℝ} (hrf : f.IsRoot r) (hrg : g.IsRoot r) {z : ℂ}
    (hz : z ≠ (r : ℂ)) :
    (complexify (g /ₘ (X - C r))).eval z / (complexify (f /ₘ (X - C r))).eval z
      = (complexify g).eval z / (complexify f).eval z := by
  have hff : f = (X - C r) * (f /ₘ (X - C r)) := (mul_divByMonic_eq_iff_isRoot.mpr hrf).symm
  have hgg : g = (X - C r) * (g /ₘ (X - C r)) := (mul_divByMonic_eq_iff_isRoot.mpr hrg).symm
  have hfac : ∀ (h : ℝ[X]), (complexify ((X - C r) * h)).eval z
      = (z - (r : ℂ)) * (complexify h).eval z := by
    intro h
    simp [complexify, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  conv_rhs => rw [hff, hgg, hfac, hfac]
  rw [mul_div_mul_left]
  exact sub_ne_zero.mpr hz

theorem im_ratio_nonpos_general {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (hpq : Prec g f)
    (h_deg₁ : 1 ≤ f.natDegree)
    {z : ℂ} (hz : 0 < z.im) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f g with
  | _ n ih =>
    subst hn
    by_cases hcom : ∃ r, r ∈ f.roots ∧ r ∈ g.roots
    · obtain ⟨r, hrf, hrg⟩ := hcom
      have hrfroot : f.IsRoot r := isRoot_of_mem_roots hrf
      have hrgroot : g.IsRoot r := isRoot_of_mem_roots hrg
      have hzr : z ≠ (r : ℂ) := by intro h; simp_all
      rw [← ratio_cofactor_eq hrfroot hrgroot hzr]
      have hpq₁ : Prec (g /ₘ (X - C r)) (f /ₘ (X - C r)) :=
        prec_cofactor_of_common_root hpq hrfroot hrgroot
      have hf₁ : HasPosLeadingCoeff (f /ₘ (X - C r)) := by
        unfold HasPosLeadingCoeff at hf ⊢
        rw [leadingCoeff_divByMonic_X_sub_C hrfroot]; exact hf
      have hg₁ : HasPosLeadingCoeff (g /ₘ (X - C r)) := by
        unfold HasPosLeadingCoeff at hg ⊢
        rw [leadingCoeff_divByMonic_X_sub_C hrgroot]; exact hg
      have hf₁deg : (f /ₘ (X - C r)).natDegree < f.natDegree := by
        rw [natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C]; lia
      by_cases hd₁ : 1 ≤ (f /ₘ (X - C r)).natDegree
      · exact ih _ hf₁deg hf₁ hg₁ hpq₁ hd₁ rfl
      · push Not at hd₁
        have hf₁deg₀ : (f /ₘ (X - C r)).natDegree = 0 := by lia
        have hg₁deg₀ : (g /ₘ (X - C r)).natDegree = 0 := by
          have hg₁_le := hpq₁.natDegree_le
          lia
        have hf₁c : complexify (f /ₘ (X - C r)) = C ((f /ₘ (X - C r)).coeff 0 : ℂ) := by
          rw [complexify, eq_C_of_natDegree_eq_zero hf₁deg₀]; simp
        have hg₁c : complexify (g /ₘ (X - C r)) = C ((g /ₘ (X - C r)).coeff 0 : ℂ) := by
          rw [complexify, eq_C_of_natDegree_eq_zero hg₁deg₀]; simp
        simp [*]
    · push Not at hcom
      have hfnd : f.roots.Nodup := by
        by_contra hnd
        obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup hpq hnd
        simp_all
      have hgnd : g.roots.Nodup := by
        by_contra hnd
        obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup_g hpq hnd
        simp_all
      exact im_ratio_nonpos hpq hf hg hfnd hgnd (fun s hsf hsg ↦ hcom s hsf hsg) h_deg₁ hz

theorem prec_of_stable_general {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (h_deg₁ : 1 ≤ f.natDegree) : Prec g f := by
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f g with
  | _ n ih =>
    subst hn
    by_cases hcom : ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r
    · obtain ⟨r, hrf, hrg⟩ := hcom
      have hstab₁ := isUpperHalfPlaneStable_cofactor_of_stable hrf hrg hstab
      have hf₁ : HasPosLeadingCoeff (f /ₘ (X - C r)) := by
        unfold HasPosLeadingCoeff at hf ⊢
        rw [leadingCoeff_divByMonic_X_sub_C hrf]; exact hf
      have hg₁ : HasPosLeadingCoeff (g /ₘ (X - C r)) := by
        unfold HasPosLeadingCoeff at hg ⊢
        rw [leadingCoeff_divByMonic_X_sub_C hrg]; exact hg
      have hf₁deg : (f /ₘ (X - C r)).natDegree < f.natDegree := by
        rw [natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C]; lia
      by_cases hd₁ : 1 ≤ (f /ₘ (X - C r)).natDegree
      · exact prec_of_prec_cofactor hrf hrg (ih _ hf₁deg hf₁ hg₁ hstab₁ hd₁ rfl)
      · push Not at hd₁
        have hf₁d₀ : (f /ₘ (X - C r)).natDegree = 0 := by lia
        have hfd₁ : f.natDegree = 1 := by
          rw [natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C] at hf₁d₀; lia
        obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable hf hg hstab
        have hg₁d₀ : (g /ₘ (X - C r)).natDegree = 0 := by
          rw [natDegree_divByMonic g (monic_X_sub_C r), natDegree_X_sub_C]; lia
        refine prec_of_prec_cofactor hrf hrg ?_
        obtain ⟨⟨hg₁₀, hg₁s⟩, ⟨hf₁₀, hf₁s⟩⟩ :
            ((g /ₘ (X - C r)) ≠ 0 ∧ (g /ₘ (X - C r)).Splits) ∧
              ((f /ₘ (X - C r)) ≠ 0 ∧ (f /ₘ (X - C r)).Splits) :=
          ⟨isRealRooted_of_deg_zero hg₁.ne_zero hg₁d₀,
            isRealRooted_of_deg_zero hf₁.ne_zero hf₁d₀⟩
        exact prec_degree_zero_degree_zero hg₁₀ hg₁s hf₁₀ hf₁s hg₁d₀ hf₁d₀
    · push Not at hcom
      obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable hf hg hstab
      rcases Nat.lt_or_ge g.natDegree f.natDegree with hglt | hgge
      · exact prec_of_stable_succ_degree hf hg hstab
          (fun ⟨r, hrf, hrg⟩ => hcom r hrf hrg) (by lia)
      · exact prec_of_stable_same_degree_no_common hf hg hstab
          (fun ⟨r, hrf, hrg⟩ => hcom r hrf hrg) (by lia) h_deg₁

theorem hermiteBiehlerStableToHurwitzOddEven_upperHalfSubstitution :
    HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement := by
  intro p q h_p h_q h_stable w z hwim hzw hzre
  have h_zim : 0 < z.im := by
    have h_we : w.im = 2 * z.re * z.im := by rw [← hzw, pow_two, Complex.mul_im]; ring
    simp_all
  intro heq
  have hpw : (complexify p).eval w ≠ 0 := by
    intro hp₀
    rw [hp₀, mul_zero, add_zero] at heq
    exact h_stable w hwim (by simp [*])
  have h_z_eq : z = -((complexify q).eval w / (complexify p).eval w) := by
    field_simp; linear_combination heq
  have h_q_ne : q ≠ 0 := by
    rintro rfl
    simp only [complexify, Polynomial.map_zero, eval_zero, zero_add] at heq
    have h_z₀ : z ≠ 0 := fun h => by rw [h] at hzre; simp at hzre
    refine hpw ?_
    rcases mul_eq_zero.mp heq with h | h
    · exact absurd h h_z₀
    · exact h
  have h_q_pos : HasPosLeadingCoeff q := hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero h_q h_q_ne
  by_cases h_q_deg : 1 ≤ q.natDegree
  · have h_p_ne : p ≠ 0 := by rintro rfl; simp [complexify] at hpw
    have h_p_pos : HasPosLeadingCoeff p := hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero h_p h_p_ne
    have h_prec : Prec p q := prec_of_stable_general h_q_pos h_p_pos h_stable h_q_deg
    have h_ratio : ((complexify p).eval w / (complexify q).eval w).im ≤ 0 :=
      im_ratio_nonpos_general h_q_pos h_p_pos h_prec h_q_deg hwim
    have h_qw : (complexify q).eval w ≠ 0 := by
      obtain ⟨-, ⟨-, hqs⟩, -⟩ := id h_prec
      exact eval_complexify_ne_zero_of_splits_of_im_pos hqs h_q_ne hwim
    have h_qp_im : 0 ≤ ((complexify q).eval w / (complexify p).eval w).im := by
      have h_recip : ((complexify q).eval w / (complexify p).eval w)
          = ((complexify p).eval w / (complexify q).eval w)⁻¹ := by simp
      rw [h_recip, Complex.inv_im]
      have h_normsq : 0 < Complex.normSq ((complexify p).eval w / (complexify q).eval w) :=
        Complex.normSq_pos.mpr (div_ne_zero hpw h_qw)
      have h_num : 0 ≤ -((complexify p).eval w / (complexify q).eval w).im := by simp [*]
      exact div_nonneg h_num h_normsq.le
    have h_zim_le : z.im ≤ 0 := by simp [*]
    linarith [h_zim, h_zim_le]
  · push Not at h_q_deg
    have h_q_deg₀ : q.natDegree = 0 := by lia
    have h_p_ne : p ≠ 0 := by rintro rfl; simp [complexify] at hpw
    have h_p_pos : HasPosLeadingCoeff p := hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero h_p h_p_ne
    obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable h_q_pos h_p_pos h_stable
    have h_p_deg₀ : p.natDegree = 0 := by lia
    have h_qc : (complexify q).eval w = ((q.coeff 0 : ℝ) : ℂ) := by
      rw [complexify, eq_C_of_natDegree_eq_zero h_q_deg₀]; simp
    have h_pc : (complexify p).eval w = ((p.coeff 0 : ℝ) : ℂ) := by
      rw [complexify, eq_C_of_natDegree_eq_zero h_p_deg₀]; simp
    simp_all

theorem hermiteBiehlerStableToHurwitzOddEven {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (h : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q)) :=
  hermiteBiehlerStableToHurwitzOddEven_of_upperHalfSubstitution
    hermiteBiehlerStableToHurwitzOddEven_upperHalfSubstitution hp hq h

end RealRooted
