module

import RealRooted.MaWang.Strong
import RealRooted.RootContinuity
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Complex.Polynomial.Basic

public section

open Polynomial Filter

noncomputable section

namespace RealRooted.MaWang

/-- A sufficiently small normalized subtraction is uniformly small coefficientwise. -/
private lemma norm_coeff_normalized_sub_lt {F g : ℝ[X]} {M A δ η : ℝ}
    (hδ_pos : 0 < δ) (hη_pos : 0 < η)
    (hM : M = max 1 (coeffSumRange g))
    (hA : A = max 1 (‖F.leadingCoeff⁻¹‖ * M)) (hδA : δ * A = η / 2) :
    ∀ i : ℕ, ‖(C F.leadingCoeff⁻¹ * (F - C δ * g)).coeff i -
      (C F.leadingCoeff⁻¹ * F).coeff i‖ < η := by
  intro i
  have hgi_bound : ‖g.coeff i‖ ≤ M := by
    rw [hM]
    exact (coeff_norm_le_coeffSumRange g i).trans (le_max_right _ _)
  have hprod_bound : ‖F.leadingCoeff⁻¹‖ * ‖g.coeff i‖ ≤ A := by
    rw [hA]
    have hmax : ‖F.leadingCoeff⁻¹‖ * M ≤ max 1 (‖F.leadingCoeff⁻¹‖ * M) :=
      le_max_right _ _
    nlinarith [hgi_bound, norm_nonneg (F.leadingCoeff⁻¹), norm_nonneg (g.coeff i)]
  have hcoeff :
      (C F.leadingCoeff⁻¹ * (F - C δ * g)).coeff i -
          (C F.leadingCoeff⁻¹ * F).coeff i =
        -(F.leadingCoeff⁻¹ * (δ * g.coeff i)) := by
    simp [Polynomial.coeff_C_mul]
    ring
  calc
    ‖(C F.leadingCoeff⁻¹ * (F - C δ * g)).coeff i -
        (C F.leadingCoeff⁻¹ * F).coeff i‖
        = ‖-(F.leadingCoeff⁻¹ * (δ * g.coeff i))‖ := by rw [hcoeff]
    _ = ‖F.leadingCoeff⁻¹‖ * (δ * ‖g.coeff i‖) := by
      rw [norm_neg, norm_mul, norm_mul, Real.norm_of_nonneg hδ_pos.le]
    _ = δ * (‖F.leadingCoeff⁻¹‖ * ‖g.coeff i‖) := by ring
    _ ≤ δ * A := by gcongr
    _ = η / 2 := hδA
    _ < η := by linarith

/-- The root-continuity radius determined by an imaginary part is half that part. -/
private lemma perturbation_radius_eq_half {n : ℕ} (hn : n ≠ 0)
    {eps R u η : ℝ} (heps : 0 < eps) (hR : 0 < R)
    (hu : u = eps / (2 * R)) (hη : η = u ^ n / (n + 1)) :
    (((n : ℝ) + 1) * η) ^ ((n : ℝ)⁻¹) * R = eps / 2 := by
  have hu_nonneg : 0 ≤ u := by rw [hu]; positivity
  calc
    (((n : ℝ) + 1) * η) ^ ((n : ℝ)⁻¹) * R =
        (((n : ℝ) + 1) * (u ^ n / ((n : ℝ) + 1))) ^ ((n : ℝ)⁻¹) * R := by
          rw [hη]
    _ = (u ^ n) ^ ((n : ℝ)⁻¹) * R := by grind
    _ = u * R := by rw [Real.pow_rpow_inv_natCast hu_nonneg hn]
    _ = eps / 2 := by rw [hu]; field_simp [hR.ne']

/-- Positive real-rooted subtractions force every root of the normalization to be real. -/
private lemma map_normalization_roots_mem_range_of_sub_C_mul
    {f g F : ℝ[X]}
    (hgf : Interlaces g f) (hlc_ne : F.leadingCoeff ≠ 0)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hsub_rr : ∀ {δ : ℝ}, 0 < δ → ((F - C δ * g) ≠ 0 ∧ (F - C δ * g).Splits))
    (hq_monic : (C F.leadingCoeff⁻¹ * F).Monic)
    (hq_deg_pos : 0 < (C F.leadingCoeff⁻¹ * F).natDegree) :
    ∀ z ∈ ((C F.leadingCoeff⁻¹ * F).map (algebraMap ℝ ℂ)).roots,
      z ∈ (algebraMap ℝ ℂ).range := by
  let q : ℝ[X] := C F.leadingCoeff⁻¹ * F
  intro z hz
  by_contra hz_not_real
  have hzim_ne : z.im ≠ 0 := by
    intro hzim
    apply hz_not_real
    refine ⟨z.re, ?_⟩
    apply Complex.ext <;> simp [hzim]
  have hz_aroot : z ∈ q.aroots ℂ := by lia
  have hz_aeval : Polynomial.aeval z q = 0 := by simp_all
  let eps0 : ℝ := |z.im|
  have heps0_pos : 0 < eps0 := abs_pos.mpr hzim_ne
  let R : ℝ := max ‖z‖ 1
  let u : ℝ := eps0 / (2 * R)
  let η : ℝ := u ^ q.natDegree / (q.natDegree + 1)
  let M : ℝ := max 1 (coeffSumRange g)
  let A : ℝ := max 1 (‖F.leadingCoeff⁻¹‖ * M)
  let δ : ℝ := η / (2 * A)
  have hη_pos : 0 < η := by
    unfold η u R eps0
    positivity
  have hδ_pos : 0 < δ := by
    unfold δ A
    positivity
  let qδ : ℝ[X] := C F.leadingCoeff⁻¹ * (F - C δ * g)
  have hFδ_natdeg : (F - C δ * g).natDegree = F.natDegree :=
    natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound hgf hdeg_lo δ
  have hFδ_lc : (F - C δ * g).leadingCoeff = F.leadingCoeff := by
    have hlt : degree (C δ * g) < degree F :=
      degree_lt_degree <|
        (natDegree_C_mul_le δ g).trans_lt
          (natDegree_lt_of_interlaces_degree_lower_bound hgf hdeg_lo)
    rw [leadingCoeff_sub_of_degree_lt hlt]
  have hqδ_monic : qδ.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hqδ_deg : qδ.natDegree = q.natDegree := by
    simp only [qδ, q, natDegree_C_mul (inv_ne_zero hlc_ne), hFδ_natdeg]
  have hqδ_coeff : ∀ i : ℕ, ‖qδ.coeff i - q.coeff i‖ < η := by
    have hM : M = max 1 (coeffSumRange g) := rfl
    have hA : A = max 1 (‖F.leadingCoeff⁻¹‖ * M) := rfl
    simpa only [qδ, q] using
      norm_coeff_normalized_sub_lt (M := M) (A := A) hδ_pos hη_pos hM hA (by
        dsimp [δ]
        field_simp [show A ≠ 0 by unfold A; positivity])
  obtain ⟨w, hw_mem, hw_close⟩ :=
    Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := q) (g := qδ) hη_pos hz_aeval hq_monic hqδ_monic hqδ_deg hqδ_coeff
      (IsAlgClosed.splits _)
  have hFδ_rr := hsub_rr hδ_pos
  have hqδ_rr : qδ ≠ 0 ∧ qδ.Splits := by simp_all [qδ]
  have hw_root : (qδ.map (algebraMap ℝ ℂ)).IsRoot w := by simp_all
  rcases hqδ_rr.2.mem_range_of_isRoot hqδ_rr.1 hw_root with ⟨x, rfl⟩
  have him_le : eps0 ≤ ‖z - x‖ := by
    unfold eps0
    simpa using (Complex.abs_im_le_norm (z - x))
  have hR_pos : 0 < R := by grind
  have hbound_eq :
      (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R = eps0 / 2 :=
    perturbation_radius_eq_half (by lia) heps0_pos hR_pos rfl rfl
  have hclose_eps : ‖z - x‖ < eps0 := by
    calc
      ‖z - x‖ < (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R := hw_close
      _ = eps0 / 2 := hbound_eq
      _ < eps0 := by linarith
  linarith

/-- If every positive perturbation `F - C δ * g` is real-rooted, then `F` is
real-rooted as well. The interlacing hypothesis is only used to keep the degree
and leading coefficient stable under the subtraction. -/
theorem isRealRooted_of_interlaces_sub_C_mul_of_forall_pos
    {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hsub_rr : ∀ {δ : ℝ}, 0 < δ → ((F - C δ * g) ≠ 0 ∧ (F - C δ * g).Splits)) :
    F ≠ 0 ∧ F.Splits := by
  have hF_ne : F ≠ 0 := hF_pos.ne_zero
  have hlc_pos : 0 < F.leadingCoeff := by simpa [HasPosLeadingCoeff] using hF_pos
  have hlc_ne : F.leadingCoeff ≠ 0 := ne_of_gt hlc_pos
  let q : ℝ[X] := C F.leadingCoeff⁻¹ * F
  have hq_monic : q.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hq_ne : q ≠ 0 := mul_ne_zero (by simp [hlc_ne]) hF_ne
  have hq_deg_pos : 0 < q.natDegree := by
    simp only [q, natDegree_C_mul (inv_ne_zero hlc_ne)]
    obtain ⟨_, _, hdeg, _, _, _, _, _, _, _⟩ := hgf
    lia
  have hroots_real :
      ∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots, z ∈ (algebraMap ℝ ℂ).range := by
    simpa only [q] using map_normalization_roots_mem_range_of_sub_C_mul
      hgf hlc_ne hdeg_lo hsub_rr hq_monic hq_deg_pos
  have hq_split : q.Splits :=
    Polynomial.Splits.of_splits_map (i := algebraMap ℝ ℂ)
      (IsAlgClosed.splits _) hroots_real
  have hq_rr : q ≠ 0 ∧ q.Splits := ⟨hq_ne, hq_split⟩
  have hF_eq : C F.leadingCoeff * q = F := by
    change C F.leadingCoeff * (C F.leadingCoeff⁻¹ * F) = F
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc_ne, C_1, one_mul]
  rw [← hF_eq]
  simp_all [-hF_eq]

end RealRooted.MaWang

namespace RealRooted

export MaWang
  (isRealRooted_of_interlaces_sub_C_mul_of_forall_pos)

end RealRooted
