import RealRooted.Mathlib.Data.List.Interleave.Padding
import RealRooted.Mathlib.Data.List.Sort.Endpoint
import RealRooted.ReciprocalShift.Interlacing.Inversion

/-!
# Proper position under reciprocal shifts

This module proves that a degree-padded reciprocal shift reverses a proper
position pair of PF polynomials. The generic list endpoint and inverse-root
transport facts live in lower layers.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- At a common degree bound, reciprocal shift reverses a proper-position pair
of PF polynomials. -/
theorem reciprocalShift_reverses_prec
    {D : ℕ} {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpd : p.natDegree ≤ D) (hqd : q.natDegree ≤ D) (hpq : Prec p q) :
    Prec (reciprocalShift D q) (reciprocalShift D p) := by
  obtain ⟨⟨hp_ne, hp_splits⟩, ⟨hq_ne, hq_splits⟩, ss, rs, hss_sorted, hrs_sorted,
    hss_roots, hrs_roots, hshape⟩ := hpq
  have hss_nonpos : ∀ x ∈ ss, x ≤ 0 := by
    intro x hx
    exact hp.2.2 x (by rw [← hss_roots]; exact_mod_cast hx)
  have hrs_nonpos : ∀ x ∈ rs, x ≤ 0 := by
    intro x hx
    exact hq.2.2 x (by rw [← hrs_roots]; exact_mod_cast hx)
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
  have hrecipQ : reciprocalShift D q ≠ 0 ∧ (reciprocalShift D q).Splits := by
    have hpf := reciprocalShift_preserves_pf hq hqd
    refine ⟨fun hzero ↦ hq_ne (Polynomial.reflect_eq_zero_iff.mp hzero), ?_⟩
    rcases hpf.2.1 with hzero | hsplits
    · simp_all
    · grind
  have hrecipP : reciprocalShift D p ≠ 0 ∧ (reciprocalShift D p).Splits := by
    have hpf := reciprocalShift_preserves_pf hp hpd
    refine ⟨fun hzero ↦ hp_ne (Polynomial.reflect_eq_zero_iff.mp hzero), ?_⟩
    rcases hpf.2.1 with hzero | hsplits
    · simp_all
    · grind
  refine ⟨hrecipQ, hrecipP, SSout, RSout, hSSsorted, hRSsorted, hSSroots, hRSroots, ?_⟩
  have hss_length : ss.length = p.natDegree := by
    rw [← Multiset.coe_card, hss_roots, card_roots_of_splits hp_splits]
  have hrs_length : rs.length = q.natDegree := by
    rw [← Multiset.coe_card, hrs_roots, card_roots_of_splits hq_splits]
  set ssneg := ss.filter (fun r ↦ decide (r ≠ 0)) with hssneg
  set rsneg := rs.filter (fun r ↦ decide (r ≠ 0)) with hrsneg
  set zp := ss.count (0 : ℝ) with hzp
  set zq := rs.count (0 : ℝ) with hzq
  have hss_decomp : ss = ssneg ++ List.replicate zp 0 := by
    simpa only [hssneg, hzp] using
      (List.eq_filter_ne_append_replicate_count hss_sorted hss_nonpos)
  have hrs_decomp : rs = rsneg ++ List.replicate zq 0 := by
    simpa only [hrsneg, hzq] using
      (List.eq_filter_ne_append_replicate_count hrs_sorted hrs_nonpos)
  have hssneg_neg : ∀ x ∈ ssneg, x < 0 := by
    grind
  have hrsneg_neg : ∀ x ∈ rsneg, x < 0 := by
    grind
  have hna : ssneg.length + zp = ss.length := by
    grind
  have hnb : rsneg.length + zq = rs.length := by
    grind
  set na := ssneg.length with hna_def
  set nb := rsneg.length with hnb_def
  set Mss := ssneg.reverse.map (fun r ↦ 1 / r) with hMss
  set Mrs := rsneg.reverse.map (fun r ↦ 1 / r) with hMrs
  have hMss_neg : ∀ x ∈ Mss, x ≤ 0 := by
    intro x hx
    rw [hMss, List.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [List.mem_reverse] at hy
    rw [← hyx]
    exact (one_div_neg.mpr (hssneg_neg y hy)).le
  have hMrs_neg : ∀ x ∈ Mrs, x ≤ 0 := by
    intro x hx
    rw [hMrs, List.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [List.mem_reverse] at hy
    rw [← hyx]
    exact (one_div_neg.mpr (hrsneg_neg y hy)).le
  have hSSout_eq : SSout = Mrs ++ List.replicate (D - q.natDegree) 0 := by
    assumption
  have hRSout_eq : RSout = Mss ++ List.replicate (D - p.natDegree) 0 := by
    assumption
  set pa := D - p.natDegree with hpa
  set pb := D - q.natDegree with hpb
  have hdp : na + zp = p.natDegree := by
    grind
  have hdq : nb + zq = q.natDegree := by
    grind
  have hpaval : na + pa = D - zp := by
    grind
  have hpbval : nb + pb = D - zq := by
    grind
  have hSSout_length : SSout.length = nb + pb := by
    grind
  have hRSout_length : RSout.length = na + pa := by
    grind
  rcases hshape with ⟨hlensucc, hinterlace⟩ | ⟨hlensame, halternates⟩
  · have hinterleaves : List.Interleaves (· ≤ ·) ss rs :=
      (listInterlaces_iff_interleaves_of_length hlensucc).mp hinterlace
    rw [hss_decomp, hrs_decomp] at hinterleaves
    have hcore : List.Interleaves (· ≤ ·) ssneg rsneg :=
      hinterleaves.drop_replicate_of_lt hssneg_neg hrsneg_neg
    have hcore_length := (List.interleaves_iff_length_isChain_interleave.mp hcore).1
    rcases hcore_length with hsame | hsucc
    · have hzq_eq : zq = zp + 1 := by
        grind
      have hmap : List.Interleaves (· ≤ ·) Mrs Mss :=
        interleaves_reverse_map_one_div_of_length_eq ssneg rsneg hssneg_neg hrsneg_neg hsame hcore
      have hpa_eq : pa = pb + 1 := by
        grind
      have hmodel_length : Mrs.length = Mss.length := by
        grind
      have hmodel := List.Interleaves.append_replicate_right_of_length_eq hmodel_length hmap
        (le_refl 0) (by
        intro x hx
        rcases hx with hx | hx
        · exact hMrs_neg x hx
        · exact hMss_neg x hx) pb
      left
      refine ⟨by grind, ?_⟩
      apply listInterlaces_of_interleaves_of_length (by grind)
      grind
    · have hz_eq : zp = zq := by
        grind
      have hmap : List.Interleaves (· ≤ ·) Mss Mrs :=
        interleaves_reverse_map_one_div_of_length_add_one_eq ssneg rsneg hssneg_neg hrsneg_neg
          hsucc hcore
      have hpa_eq : pa = pb + 1 := by
        grind
      have hmodel_length : Mss.length + 1 = Mrs.length := by
        grind
      have hmodel := List.Interleaves.append_replicate_left_of_length_add_one_eq hmodel_length hmap
        (le_refl 0) (by
        intro x hx
        rcases hx with hx | hx
        · exact hMss_neg x hx
        · exact hMrs_neg x hx) pb
      right
      refine ⟨by grind, ?_⟩
      apply listAlternates_of_interleaves_of_length (by grind)
      grind
  · have hinterleaves : List.Interleaves (· ≤ ·) rs ss :=
      (listAlternates_iff_interleaves_of_length hlensame).mp halternates
    rw [hss_decomp, hrs_decomp] at hinterleaves
    have hcore : List.Interleaves (· ≤ ·) rsneg ssneg :=
      hinterleaves.drop_replicate_of_lt hrsneg_neg hssneg_neg
    have hcore_length := (List.interleaves_iff_length_isChain_interleave.mp hcore).1
    have hdegree_eq : na + zp = nb + zq := by
      grind
    rcases hcore_length with hsame | hsucc
    · have hz_eq : zp = zq := by
        lia
      have hmap : List.Interleaves (· ≤ ·) Mss Mrs :=
        interleaves_reverse_map_one_div_of_length_eq rsneg ssneg hrsneg_neg hssneg_neg hsame hcore
      have hpa_eq : pa = pb := by
        grind
      have hmodel_length : Mss.length = Mrs.length := by
        grind
      have hmodel := List.Interleaves.append_replicate_right_of_length_eq hmodel_length hmap
        (le_refl 0) (by
        intro x hx
        rcases hx with hx | hx
        · exact hMss_neg x hx
        · exact hMrs_neg x hx) pa
      right
      refine ⟨by grind, ?_⟩
      apply listAlternates_of_interleaves_of_length (by grind)
      grind
    · have hzq_eq : zq = zp + 1 := by
        lia
      have hmap : List.Interleaves (· ≤ ·) Mrs Mss :=
        interleaves_reverse_map_one_div_of_length_add_one_eq rsneg ssneg hrsneg_neg hssneg_neg
          hsucc hcore
      have hpa_eq : pa = pb := by
        grind
      have hmodel_length : Mrs.length + 1 = Mss.length := by
        grind
      have hmodel := List.Interleaves.append_replicate_left_of_length_add_one_eq hmodel_length hmap
        (le_refl 0) (by
        intro x hx
        rcases hx with hx | hx
        · exact hMrs_neg x hx
        · exact hMss_neg x hx) pa
      left
      refine ⟨by grind, ?_⟩
      apply listInterlaces_of_interleaves_of_length (by grind)
      grind

end RealRooted
