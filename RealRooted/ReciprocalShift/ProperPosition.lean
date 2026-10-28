module

import RealRooted.Mathlib.Data.List.Interleave.Padding
import RealRooted.Mathlib.Data.List.Sort.Endpoint
import RealRooted.ReciprocalShift.Interlacing.Inversion
import RealRooted.ReciprocalShift.Interlacing
public import RealRooted.PFPolynomial

/-!
# Interlacing under reciprocal shifts

This module proves that a degree-padded reciprocal shift reverses a proper
position pair of PF polynomials. The generic list endpoint and inverse-root
transport facts live in lower layers.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Filtering the zero endpoint leaves a strictly negative list whose inverse
remains nonpositive. -/
private theorem filtered_inverse_data (l : List ℝ)
    (hsorted : l.Pairwise (· ≤ ·)) (hnonpos : ∀ x ∈ l, x ≤ 0) :
    let neg := l.filter (fun r ↦ decide (r ≠ 0))
    let inv := neg.reverse.map (fun r ↦ 1 / r)
    l = neg ++ List.replicate (l.count 0) 0 ∧
      (∀ x ∈ neg, x < 0) ∧
      neg.length + l.count 0 = l.length ∧
      ∀ x ∈ inv, x ≤ 0 := by
  dsimp only
  have hdecomp := List.eq_filter_ne_append_replicate_count hsorted hnonpos
  refine ⟨hdecomp, ?_, by grind, ?_⟩
  · grind
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [List.mem_reverse] at hy
    exact (one_div_neg.mpr (by grind)).le

/-- Padded inversion transports the list-interlacing branch of a root model. -/
private theorem padded_inverse_shape_of_interlaces
    {D dp dq : ℕ} {ss rs : List ℝ}
    (hqd : dq ≤ D)
    (hss_length : ss.length = dp) (hrs_length : rs.length = dq)
    (hss_sorted : ss.Pairwise (· ≤ ·)) (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hss_nonpos : ∀ x ∈ ss, x ≤ 0) (hrs_nonpos : ∀ x ∈ rs, x ≤ 0)
    (hlensucc : ss.length + 1 = rs.length) (hinterlace : ListInterlaces ss rs) :
    let SSout := (rs.filter fun r ↦ decide (r ≠ 0)).reverse.map (fun r ↦ 1 / r) ++
      List.replicate (D - dq) 0
    let RSout := (ss.filter fun r ↦ decide (r ≠ 0)).reverse.map (fun r ↦ 1 / r) ++
      List.replicate (D - dp) 0
    (SSout.length + 1 = RSout.length ∧ ListInterlaces SSout RSout) ∨
      (SSout.length = RSout.length ∧ ListAlternates SSout RSout) := by
  dsimp only
  set ssneg := ss.filter (fun r ↦ decide (r ≠ 0))
  set rsneg := rs.filter (fun r ↦ decide (r ≠ 0))
  set zp := ss.count (0 : ℝ)
  set zq := rs.count (0 : ℝ)
  set Mss := ssneg.reverse.map (fun r ↦ 1 / r)
  set Mrs := rsneg.reverse.map (fun r ↦ 1 / r)
  obtain ⟨hss_decomp, hssneg_neg, hna, hMss_neg⟩ :=
    filtered_inverse_data ss hss_sorted hss_nonpos
  obtain ⟨hrs_decomp, hrsneg_neg, hnb, hMrs_neg⟩ :=
    filtered_inverse_data rs hrs_sorted hrs_nonpos
  set pa := D - dp
  set pb := D - dq
  set SSout := Mrs ++ List.replicate pb 0
  set RSout := Mss ++ List.replicate pa 0
  have hSSout_length : SSout.length = rsneg.length + pb := by simp [SSout, Mrs]
  have hRSout_length : RSout.length = ssneg.length + pa := by simp [RSout, Mss]
  have hpaval : ssneg.length + pa = D - zp := by grind
  have hpbval : rsneg.length + pb = D - zq := by grind
  have hinterleaves : List.Interleaves (· ≤ ·) ss rs :=
    (listInterlaces_iff_interleaves_of_length hlensucc).mp hinterlace
  rw [hss_decomp, hrs_decomp] at hinterleaves
  have hcore : List.Interleaves (· ≤ ·) ssneg rsneg :=
    hinterleaves.drop_replicate_of_lt hssneg_neg hrsneg_neg
  have hcore_length := (List.interleaves_iff_length_isChain_interleave.mp hcore).1
  simp only [wcovBy_iff_eq_or_covBy, Nat.covBy_iff_add_one_eq] at hcore_length
  rcases hcore_length with hsame | hsucc
  · have hzq_eq : zq = zp + 1 := by grind
    have hpa_eq : pa = pb + 1 := by grind
    have hmap : List.Interleaves (· ≤ ·) Mrs Mss :=
      interleaves_reverse_map_one_div_of_length_eq ssneg rsneg
        hssneg_neg hrsneg_neg hsame hcore
    have hmodel := List.Interleaves.append_replicate_right_of_length_eq
      (show Mrs.length = Mss.length by grind) hmap (le_refl 0) (by
        intro x hx
        rcases hx with hx | hx
        · exact hMrs_neg x hx
        · exact hMss_neg x hx) pb
    have hmodel_out : List.Interleaves (· ≤ ·) SSout RSout := by
      simpa only [SSout, RSout, hpa_eq] using hmodel.2
    left
    exact ⟨by grind, listInterlaces_of_interleaves_of_length (by grind) hmodel_out⟩
  · have hz_eq : zp = zq := by grind
    have hpa_eq : pa = pb + 1 := by grind
    have hmap : List.Interleaves (· ≤ ·) Mss Mrs :=
      interleaves_reverse_map_one_div_of_length_add_one_eq ssneg rsneg
        hssneg_neg hrsneg_neg hsucc hcore
    have hmodel := List.Interleaves.append_replicate_left_of_length_add_one_eq
      (show Mss.length + 1 = Mrs.length by grind) hmap (le_refl 0) (by
        intro x hx
        rcases hx with hx | hx
        · exact hMss_neg x hx
        · exact hMrs_neg x hx) pb
    have hmodel_out : List.Interleaves (· ≤ ·) RSout SSout := by
      simpa only [SSout, RSout, hpa_eq] using hmodel.2
    right
    exact ⟨by grind, listAlternates_of_interleaves_of_length (by grind) hmodel_out⟩

/-- Padded inversion transports the list-alternating branch of a root model. -/
private theorem padded_inverse_shape_of_alternates
    {D dp dq : ℕ} {ss rs : List ℝ}
    (hpd : dp ≤ D) (hqd : dq ≤ D)
    (hss_length : ss.length = dp) (hrs_length : rs.length = dq)
    (hss_sorted : ss.Pairwise (· ≤ ·)) (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hss_nonpos : ∀ x ∈ ss, x ≤ 0) (hrs_nonpos : ∀ x ∈ rs, x ≤ 0)
    (hlensame : ss.length = rs.length) (halternates : ListAlternates ss rs) :
    let SSout := (rs.filter fun r ↦ decide (r ≠ 0)).reverse.map (fun r ↦ 1 / r) ++
      List.replicate (D - dq) 0
    let RSout := (ss.filter fun r ↦ decide (r ≠ 0)).reverse.map (fun r ↦ 1 / r) ++
      List.replicate (D - dp) 0
    (SSout.length + 1 = RSout.length ∧ ListInterlaces SSout RSout) ∨
      (SSout.length = RSout.length ∧ ListAlternates SSout RSout) := by
  dsimp only
  set ssneg := ss.filter (fun r ↦ decide (r ≠ 0))
  set rsneg := rs.filter (fun r ↦ decide (r ≠ 0))
  set zp := ss.count (0 : ℝ)
  set zq := rs.count (0 : ℝ)
  set Mss := ssneg.reverse.map (fun r ↦ 1 / r)
  set Mrs := rsneg.reverse.map (fun r ↦ 1 / r)
  obtain ⟨hss_decomp, hssneg_neg, hna, hMss_neg⟩ :=
    filtered_inverse_data ss hss_sorted hss_nonpos
  obtain ⟨hrs_decomp, hrsneg_neg, hnb, hMrs_neg⟩ :=
    filtered_inverse_data rs hrs_sorted hrs_nonpos
  set pa := D - dp
  set pb := D - dq
  set SSout := Mrs ++ List.replicate pb 0
  set RSout := Mss ++ List.replicate pa 0
  have hSSout_length : SSout.length = rsneg.length + pb := by simp [SSout, Mrs]
  have hRSout_length : RSout.length = ssneg.length + pa := by simp [RSout, Mss]
  have hpaval : ssneg.length + pa = D - zp := by grind
  have hpbval : rsneg.length + pb = D - zq := by grind
  have hinterleaves : List.Interleaves (· ≤ ·) rs ss :=
    (listAlternates_iff_interleaves_of_length hlensame).mp halternates
  rw [hss_decomp, hrs_decomp] at hinterleaves
  have hcore : List.Interleaves (· ≤ ·) rsneg ssneg :=
    hinterleaves.drop_replicate_of_lt hrsneg_neg hssneg_neg
  have hcore_length := (List.interleaves_iff_length_isChain_interleave.mp hcore).1
  simp only [wcovBy_iff_eq_or_covBy, Nat.covBy_iff_add_one_eq] at hcore_length
  rcases hcore_length with hsame | hsucc
  · have hz_eq : zp = zq := by lia
    have hpa_eq : pa = pb := by grind
    have hmap : List.Interleaves (· ≤ ·) Mss Mrs :=
      interleaves_reverse_map_one_div_of_length_eq rsneg ssneg
        hrsneg_neg hssneg_neg hsame hcore
    have hmodel := List.Interleaves.append_replicate_right_of_length_eq
      (show Mss.length = Mrs.length by grind) hmap (le_refl 0) (by
        intro x hx
        rcases hx with hx | hx
        · exact hMss_neg x hx
        · exact hMrs_neg x hx) pa
    have hmodel_out : List.Interleaves (· ≤ ·) RSout SSout := by
      simpa only [SSout, RSout, hpa_eq] using hmodel.1
    right
    exact ⟨by grind, listAlternates_of_interleaves_of_length (by grind) hmodel_out⟩
  · have hzq_eq : zq = zp + 1 := by lia
    have hpa_eq : pa = pb := by grind
    have hmap : List.Interleaves (· ≤ ·) Mrs Mss :=
      interleaves_reverse_map_one_div_of_length_add_one_eq rsneg ssneg
        hrsneg_neg hssneg_neg hsucc hcore
    have hmodel := List.Interleaves.append_replicate_left_of_length_add_one_eq
      (show Mrs.length + 1 = Mss.length by grind) hmap (le_refl 0) (by
        intro x hx
        rcases hx with hx | hx
        · exact hMrs_neg x hx
        · exact hMss_neg x hx) pa
    have hmodel_out : List.Interleaves (· ≤ ·) SSout RSout := by
      simpa only [SSout, RSout, hpa_eq] using hmodel.1
    left
    exact ⟨by grind, listInterlaces_of_interleaves_of_length (by grind) hmodel_out⟩

/-- A bounded PF reciprocal shift is nonzero and split when its input is nonzero. -/
private theorem reciprocalShift_ne_zero_and_splits {D : ℕ} {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hp0 : p ≠ 0) (hdeg : p.natDegree ≤ D) :
    reciprocalShift D p ≠ 0 ∧ (reciprocalShift D p).Splits := by
  have hpf := reciprocalShift_preserves_pf hp hdeg
  refine ⟨fun hzero ↦ hp0 (Polynomial.reflect_eq_zero_iff.mp hzero), ?_⟩
  rcases hpf.2.1 with hzero | hsplits
  · simp_all
  · grind

/-- At a common degree bound, reciprocal shift reverses a strictly interlacing pair
of PF polynomials. -/
theorem reciprocalShift_reverses_strictInterl
    {D : ℕ} {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpd : p.natDegree ≤ D) (hqd : q.natDegree ≤ D) (hpq : StrictInterl p q) :
    StrictInterl (reciprocalShift D q) (reciprocalShift D p) := by
  obtain ⟨⟨hp_ne, hp_splits⟩, ⟨hq_ne, hq_splits⟩, ss, rs, hss_sorted, hrs_sorted,
    hss_roots, hrs_roots, hshape⟩ := hpq
  have hss_nonpos : ∀ x ∈ ss, x ≤ 0 :=
    fun x hx => hp.2.2 x (by rw [← hss_roots]; exact_mod_cast hx)
  have hrs_nonpos : ∀ x ∈ rs, x ≤ 0 :=
    fun x hx => hq.2.2 x (by rw [← hrs_roots]; exact_mod_cast hx)
  set SSout := (rs.filter fun r ↦ decide (r ≠ 0)).reverse.map (fun r ↦ 1 / r)
    ++ List.replicate (D - q.natDegree) 0 with hSSout
  set RSout := (ss.filter fun r ↦ decide (r ≠ 0)).reverse.map (fun r ↦ 1 / r)
    ++ List.replicate (D - p.natDegree) 0 with hRSout
  have hSSsorted : SSout.Pairwise (· ≤ ·) :=
    reciprocalShift_model_sorted rs _ hrs_sorted hrs_nonpos
  have hRSsorted : RSout.Pairwise (· ≤ ·) :=
    reciprocalShift_model_sorted ss _ hss_sorted hss_nonpos
  have hSSroots : (SSout : Multiset ℝ) = (reciprocalShift D q).roots :=
    reciprocalShift_model_roots hq_ne hq_splits hqd rs hrs_roots
  have hRSroots : (RSout : Multiset ℝ) = (reciprocalShift D p).roots :=
    reciprocalShift_model_roots hp_ne hp_splits hpd ss hss_roots
  have hrecipQ := reciprocalShift_ne_zero_and_splits hq hq_ne hqd
  have hrecipP := reciprocalShift_ne_zero_and_splits hp hp_ne hpd
  refine ⟨hrecipQ, hrecipP, SSout, RSout, hSSsorted, hRSsorted, hSSroots, hRSroots, ?_⟩
  have hss_length : ss.length = p.natDegree := by
    rw [← Multiset.coe_card, hss_roots, Polynomial.splits_iff_card_roots.mp hp_splits]
  have hrs_length : rs.length = q.natDegree := by
    rw [← Multiset.coe_card, hrs_roots, Polynomial.splits_iff_card_roots.mp hq_splits]
  rcases hshape with ⟨hlensucc, hinterlace⟩ | ⟨hlensame, halternates⟩
  · simpa only [hSSout, hRSout] using padded_inverse_shape_of_interlaces
      hqd hss_length hrs_length hss_sorted hrs_sorted hss_nonpos hrs_nonpos
      hlensucc hinterlace
  · simpa only [hSSout, hRSout] using padded_inverse_shape_of_alternates
      hpd hqd hss_length hrs_length hss_sorted hrs_sorted hss_nonpos hrs_nonpos
      hlensame halternates

end RealRooted
