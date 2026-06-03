import RealRooted.Basic
import RealRooted.Linear
import Mathlib.Analysis.Normed.Field.Approximation

/-!
# Root-continuity tools

This file collects coefficient and evaluation estimates used to control roots
under small perturbations of a real polynomial.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A real-rooted polynomial over `ℝ` splits over `ℝ`. -/
lemma IsRealRooted.splits {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) : p.Splits :=
  hp.2

/-- Finite coefficient sup bound over the `natDegree` range. -/
def coeffSumRange (p : ℝ[X]) : ℝ :=
  Finset.sum (Finset.range (p.natDegree + 1)) fun j => ‖p.coeff j‖

lemma coeff_norm_le_coeffSumRange (p : ℝ[X]) (i : ℕ) :
    ‖p.coeff i‖ ≤ coeffSumRange p := by
  by_cases hi : i ∈ Finset.range (p.natDegree + 1)
  · unfold coeffSumRange
    exact Finset.single_le_sum (fun j _ => norm_nonneg _) hi
  · have hlt : p.natDegree < i := by
      simp_all
    rw [coeff_eq_zero_of_natDegree_lt hlt, norm_zero]
    have hnonneg : 0 ≤ coeffSumRange p := by
      unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    lia

/-- Coefficient difference for the affine perturbation `f + μ g`. -/
lemma norm_coeff_sub_add_C_mul (f g : ℝ[X]) (μ : ℝ) (i : ℕ) :
    ‖(f + C μ * g).coeff i - f.coeff i‖ = ‖μ * g.coeff i‖ := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul]

/-- Uniform coefficient bound for `f + μ g` relative to `f`. -/
lemma norm_coeff_sub_add_C_mul_le
    (f g : ℝ[X]) {μ M : ℝ}
    (hμ : 0 ≤ μ)
    (hM : ∀ i : ℕ, ‖g.coeff i‖ ≤ M) :
    ∀ i : ℕ, ‖(f + C μ * g).coeff i - f.coeff i‖ ≤ μ * M := by
  intro i
  rw [norm_coeff_sub_add_C_mul]
  calc
    ‖μ * g.coeff i‖ = ‖μ‖ * ‖g.coeff i‖ := norm_mul _ _
    _ = μ * ‖g.coeff i‖ := by simp [Real.norm_of_nonneg hμ]
    _ ≤ μ * M := by
          exact mul_le_mul_of_nonneg_left (hM i) hμ

/-- Root continuity specialized to real-rooted target polynomials:
if monic `g` is coefficientwise close to monic `f`, then each root of `f` has a nearby real
root of `g`. -/
theorem exists_real_root_near_of_isRealRooted_of_monic_of_coeff_close
    {f g : ℝ[X]} {a ε : ℝ}
    (hε : 0 < ε)
    (ha : f.IsRoot a)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree)
    (hcoeff : ∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ε)
    (hg_rr : g ≠ 0 ∧ g.Splits) :
    ∃ b : ℝ, g.IsRoot b ∧
      ‖a - b‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  have ha_eval : f.eval a = 0 := by
    simp_all
  obtain ⟨b, hb_mem, hb_dist⟩ :=
    Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := f) (g := g) hε ha_eval hf_monic hg_monic hdeg hcoeff
      (IsRealRooted.splits hg_rr)
  refine ⟨b, ?_, hb_dist⟩
  simp_all

/-- Complex-root continuity wrapper (via `aroots`): if monic `g` is
coefficientwise close to monic `f`, then each complex root of `f` has a nearby
complex root of `g`. This is the `aroots`-valued form used in limit arguments
where the target root may not yet be known real. -/
theorem exists_complex_aroot_near_of_isRealRooted_of_monic_of_coeff_close
    {f g : ℝ[X]} {z : ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hz : f.aeval z = 0)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree)
    (hcoeff : ∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ε)
    (hg_rr : g ≠ 0 ∧ g.Splits) :
    ∃ w : ℂ, w ∈ g.aroots ℂ ∧
      ‖z - w‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖z‖ 1 := by
  obtain ⟨w, hw_mem, hw_dist⟩ :=
    Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := f) (g := g) (L := ℂ) hε hz hf_monic hg_monic hdeg hcoeff
      ((IsRealRooted.splits hg_rr).map (algebraMap ℝ ℂ))
  grind

/-- Uniform coefficient control for normalized left-family perturbations:
`(1/(t+1)) * (t f + g)` is coefficientwise `O((t+1)⁻¹)` away from `f`. -/
lemma norm_coeff_sub_normalized_left_family_le
    (f g : ℝ[X]) {t : ℝ} (ht : 0 < t) :
    ∀ i : ℕ,
      ‖(C (t + 1)⁻¹ * (C t * f + g)).coeff i - f.coeff i‖ ≤
        (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) := by
  intro i
  have hcoeff :
      (C (t + 1)⁻¹ * (C t * f + g)).coeff i - f.coeff i =
        (t + 1)⁻¹ * (g.coeff i - f.coeff i) := by
    have ht1 : t + 1 ≠ 0 := by grind
    calc
      (C (t + 1)⁻¹ * (C t * f + g)).coeff i - f.coeff i
          = ((t + 1)⁻¹ * (t * f.coeff i + g.coeff i)) - f.coeff i := by
              simp
      _ = (t + 1)⁻¹ * (g.coeff i - f.coeff i) := by
            grind
  have hden_nonneg : 0 ≤ (t + 1)⁻¹ := by
    positivity
  calc
    ‖(C (t + 1)⁻¹ * (C t * f + g)).coeff i - f.coeff i‖
        = ‖(t + 1)⁻¹ * (g.coeff i - f.coeff i)‖ := by lia
    _ = ‖(t + 1)⁻¹‖ * ‖g.coeff i - f.coeff i‖ := norm_mul _ _
    _ = (t + 1)⁻¹ * ‖g.coeff i - f.coeff i‖ := by
          simp [Real.norm_of_nonneg hden_nonneg]
    _ ≤ (t + 1)⁻¹ * (‖g.coeff i‖ + ‖f.coeff i‖) := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ (t + 1)⁻¹ * (coeffSumRange g + coeffSumRange f) := by
          gcongr
          · exact coeff_norm_le_coeffSumRange g i
          · exact coeff_norm_le_coeffSumRange f i
    _ = (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) := by grind

/-- Strict coefficient control from an explicit scalar bound. -/
lemma norm_coeff_sub_normalized_left_family_lt
    (f g : ℝ[X]) {t ε : ℝ} (ht : 0 < t)
    (hbound :
      (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) < ε) :
    ∀ i : ℕ, ‖(C (t + 1)⁻¹ * (C t * f + g)).coeff i - f.coeff i‖ < ε := by
  intro i
  exact lt_of_le_of_lt (norm_coeff_sub_normalized_left_family_le f g ht i) hbound

/-- For every target precision `ε > 0`, choosing `t` sufficiently large makes the normalized
left-family coefficient error smaller than `ε`. -/
theorem exists_t_pos_with_normalized_left_family_bound
    (f g : ℝ[X]) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) < ε := by
  let c : ℝ := coeffSumRange f + coeffSumRange g
  have hc : 0 ≤ c := by
    refine add_nonneg ?_ ?_
    · unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    · unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hε0 : ε ≠ 0 := ne_of_gt hε
  refine ⟨c / ε + 1, by positivity, ?_⟩
  have hden_pos : 0 < c / ε + 2 := by
    have hdiv_nonneg : 0 ≤ c / ε := div_nonneg hc (le_of_lt hε)
    linarith
  have hbound_div : c / (c / ε + 2) < ε := by
    rw [div_lt_iff₀ hden_pos]
    have hceq : ε * (c / ε) = c := by
      grind
    grind
  grind

/-- Root continuity for the normalized left affine family:
if `f, g` are monic of the same degree and `C t * f + g` is real-rooted, then under a
coefficient-smallness bound one gets a root of `C t * f + g` near any prescribed root of `f`. -/
theorem exists_real_root_near_in_left_family
    {f g : ℝ[X]} {a t ε : ℝ}
    (ha : f.IsRoot a)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree)
    (ht : 0 < t)
    (hcoeff_bound : (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) < ε)
    (hrr : (C t * f + g) ≠ 0 ∧ (C t * f + g).Splits) :
    ∃ b : ℝ, (C t * f + g).IsRoot b ∧
      ‖a - b‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  have hsum_nonneg : 0 ≤ coeffSumRange f + coeffSumRange g := by
    refine add_nonneg ?_ ?_
    · unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    · unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcoeff_nonneg : 0 ≤ (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) := by
    exact mul_nonneg (by positivity) hsum_nonneg
  have hε : 0 < ε := lt_of_le_of_lt hcoeff_nonneg hcoeff_bound
  let q : ℝ[X] := C (t + 1)⁻¹ * (C t * f + g)
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have ht1_ne : t + 1 ≠ 0 := by grind
  have hf_pos : HasPosLeadingCoeff f := by
    simp [HasPosLeadingCoeff, hf_monic.leadingCoeff]
  have hg_pos : HasPosLeadingCoeff g := by
    simp [HasPosLeadingCoeff, hg_monic.leadingCoeff]
  have hCt_f_pos : HasPosLeadingCoeff (C t * f) := by
    unfold HasPosLeadingCoeff
    simp_all
  have hsum_deg : (C t * f + g).natDegree = f.natDegree := by
    have hCt_deg : (C t * f).natDegree = f.natDegree := by
      rw [natDegree_C_mul ht_ne]
    exact
      (natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
        (hCt_deg.trans hdeg.symm) hCt_f_pos hg_pos).trans hCt_deg
  have hsum_lc : (C t * f + g).leadingCoeff = t + 1 := by
    have hg_coeff : g.coeff f.natDegree = 1 := by
      simpa [hdeg] using hg_monic.coeff_natDegree
    unfold Polynomial.leadingCoeff
    simp_all
  have hq_monic : q.Monic := by
    unfold q
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hq_deg : q.natDegree = f.natDegree := by
    rw [show q = C (t + 1)⁻¹ * (C t * f + g) by lia,
      natDegree_C_mul (inv_ne_zero ht1_ne), hsum_deg]
  have hq_rr : (q ≠ 0 ∧ q.Splits) := isRealRooted_C_mul hrr (inv_ne_zero ht1_ne)
  obtain ⟨b, hb_qroot, hb_dist⟩ :=
    exists_real_root_near_of_isRealRooted_of_monic_of_coeff_close
      (f := f) (g := q) (a := a) (ε := ε) hε ha hf_monic hq_monic hq_deg
      (norm_coeff_sub_normalized_left_family_lt f g ht hcoeff_bound) hq_rr
  have hb_qmem : b ∈ q.roots := (Polynomial.mem_roots hq_rr.1).mpr hb_qroot
  have hb_sum_mem : b ∈ (C t * f + g).roots := by
    simpa [q, roots_C_mul _ (inv_ne_zero ht1_ne)] using hb_qmem
  have hb_sum_root : (C t * f + g).IsRoot b := (Polynomial.mem_roots hrr.1).mp hb_sum_mem
  grind

/-- Complex-root continuity for the normalized left affine family:
if `f, g` are monic of the same degree and `C t * f + g` is real-rooted, then
under a coefficient-smallness bound one gets a complex root of `C t * f + g`
near any prescribed complex root of `f`. -/
theorem exists_complex_aroot_near_in_left_family
    {f g : ℝ[X]} {z : ℂ} {t ε : ℝ}
    (hz : f.aeval z = 0)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree)
    (ht : 0 < t)
    (hcoeff_bound : (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) < ε)
    (hrr : (C t * f + g) ≠ 0 ∧ (C t * f + g).Splits) :
    ∃ w : ℂ, w ∈ (C t * f + g).aroots ℂ ∧
      ‖z - w‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖z‖ 1 := by
  have hsum_nonneg : 0 ≤ coeffSumRange f + coeffSumRange g := by
    refine add_nonneg ?_ ?_
    · unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    · unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcoeff_nonneg : 0 ≤ (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) := by
    exact mul_nonneg (by positivity) hsum_nonneg
  have hε : 0 < ε := lt_of_le_of_lt hcoeff_nonneg hcoeff_bound
  let q : ℝ[X] := C (t + 1)⁻¹ * (C t * f + g)
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have ht1_ne : t + 1 ≠ 0 := by grind
  have hf_pos : HasPosLeadingCoeff f := by
    simp [HasPosLeadingCoeff, hf_monic.leadingCoeff]
  have hg_pos : HasPosLeadingCoeff g := by
    simp [HasPosLeadingCoeff, hg_monic.leadingCoeff]
  have hCt_f_pos : HasPosLeadingCoeff (C t * f) := by
    unfold HasPosLeadingCoeff
    simp_all
  have hsum_deg : (C t * f + g).natDegree = f.natDegree := by
    have hCt_deg : (C t * f).natDegree = f.natDegree := by
      rw [natDegree_C_mul ht_ne]
    exact
      (natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
        (hCt_deg.trans hdeg.symm) hCt_f_pos hg_pos).trans hCt_deg
  have hsum_lc : (C t * f + g).leadingCoeff = t + 1 := by
    have hg_coeff : g.coeff f.natDegree = 1 := by
      simpa [hdeg] using hg_monic.coeff_natDegree
    unfold Polynomial.leadingCoeff
    simp_all
  have hq_monic : q.Monic := by
    unfold q
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hq_deg : q.natDegree = f.natDegree := by
    rw [show q = C (t + 1)⁻¹ * (C t * f + g) by lia,
      natDegree_C_mul (inv_ne_zero ht1_ne), hsum_deg]
  have hq_rr : (q ≠ 0 ∧ q.Splits) := isRealRooted_C_mul hrr (inv_ne_zero ht1_ne)
  obtain ⟨w, hw_qroot, hw_dist⟩ :=
    exists_complex_aroot_near_of_isRealRooted_of_monic_of_coeff_close
      (f := f) (g := q) (z := z) (ε := ε) hε hz hf_monic hq_monic hq_deg
      (norm_coeff_sub_normalized_left_family_lt f g ht hcoeff_bound) hq_rr
  have hw_sum_mem : w ∈ (C t * f + g).aroots ℂ := by
    simpa [q, Polynomial.aroots_C_mul _ (inv_ne_zero ht1_ne)] using hw_qroot
  grind

/-- Any complex algebraic root of a real-rooted polynomial over `ℝ` has zero
imaginary part. -/
lemma im_eq_zero_of_mem_aroots_of_isRealRooted
    {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) {z : ℂ}
    (hz : z ∈ p.aroots ℂ) :
    z.im = 0 := by
  have hz_root : (p.map (algebraMap ℝ ℂ)).IsRoot z := by
    simp_all
  have hz_range : z ∈ (algebraMap ℝ ℂ).range :=
    (IsRealRooted.splits hp).mem_range_of_isRoot hp.1 hz_root
  rcases hz_range with ⟨r, rfl⟩
  simp

end RealRooted
