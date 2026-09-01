import RealRooted.AffineFamily
import RealRooted.PosCombo
import RealRooted.ProductFamily
import RealRooted.SymmetricDecomposition.FPolynomial
import RealRooted.WagnerX

/-!
# Interlacing transport for the `f`-polynomial transform

Proper-position equivalences and positive-combination consequences of the
Brändén--Solus `f`-polynomial transform.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

theorem prec_fPolynomial_of_prec_of_hasNonnegCoeffs_of_minimal
    {d : ℕ} {u v : ℝ[X]}
    (hd : d = max u.natDegree v.natDegree)
    (h : Prec u v)
    (hu_nonneg : HasNonnegCoeffs u)
    (hv_nonneg : HasNonnegCoeffs v) :
    Prec (fPolynomial d u) (fPolynomial d v) := by
  let φ := fun r : ℝ => r / (1 - r)
  rcases h with ⟨hu_rr, hv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud : u.natDegree ≤ d := by simp_all
  have hvd : v.natDegree ≤ d := by simp_all
  have hfu_rr : ((fPolynomial d u) ≠ 0 ∧ (fPolynomial d u).Splits) :=
    isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hud hu_rr.1 hu_rr.2 hu_nonneg
  have hfv_rr : ((fPolynomial d v) ≠ 0 ∧ (fPolynomial d v).Splits) :=
    isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hvd hv_rr.1 hv_rr.2 hv_nonneg
  have hss_nonpos : ∀ s ∈ ss, s ≤ 0 := by
    intro s hs
    have hs_mem : s ∈ u.roots := by simpa [hss_eq] using Multiset.mem_coe.mpr hs
    exact roots_nonpos_of_nonneg_coeffs hu_rr.2 hu_nonneg s hs_mem
  have hrs_nonpos : ∀ r ∈ rs, r ≤ 0 := by
    intro r hr
    have hr_mem : r ∈ v.roots := by simpa [hrs_eq] using Multiset.mem_coe.mpr hr
    exact roots_nonpos_of_nonneg_coeffs hv_rr.2 hv_nonneg r hr_mem
  have hss_map_sorted : (ss.map φ).Pairwise (· ≤ ·) :=
    pairwise_map_transformedRoot_of_nonpos hss_sorted hss_nonpos
  have hrs_map_sorted : (rs.map φ).Pairwise (· ≤ ·) :=
    pairwise_map_transformedRoot_of_nonpos hrs_sorted hrs_nonpos
  have hss_map_eq : (↑(ss.map φ) : Multiset ℝ) = u.roots.map φ := by
    simpa [φ] using congrArg (fun t : Multiset ℝ => t.map φ) hss_eq
  have hrs_map_eq : (↑(rs.map φ) : Multiset ℝ) = v.roots.map φ := by
    simpa [φ] using congrArg (fun t : Multiset ℝ => t.map φ) hrs_eq
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · cases rs with
    | nil =>
        simp at hlen
    | cons r₁ rest =>
        have hlen_deg_u : ss.length = u.natDegree := by
          rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hu_rr.2]
        have hlen_deg_v : (r₁ :: rest).length = v.natDegree := by
          rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hv_rr.2]
        have hud_pad : d - u.natDegree = 1 := by grind
        have hvd_pad : d - v.natDegree = 0 := by lia
        have hleft_all : ∀ t ∈ ss.map φ, -1 ≤ t := by
          intro t ht
          rcases List.mem_map.mp ht with ⟨s, hs, rfl⟩
          exact le_of_lt (neg_one_lt_transformedRoot (hss_nonpos s hs))
        have hleft_sorted : ((-1) :: ss.map φ).Pairwise (· ≤ ·) :=
          List.pairwise_cons.mpr ⟨hleft_all, hss_map_sorted⟩
        have hleft_eq : (↑((-1) :: ss.map φ) : Multiset ℝ) = (fPolynomial d u).roots := by
          have hleft_multiset :
              (↑((-1) :: ss.map φ) : Multiset ℝ) =
                Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := by
            calc
              (↑((-1) :: ss.map φ) : Multiset ℝ)
                  = ({-1} : Multiset ℝ) + (↑(ss.map φ) : Multiset ℝ) := by simp
              _ = ({-1} : Multiset ℝ) + u.roots.map φ := by lia
              _ = Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := by simp_all
          calc
            (↑((-1) :: ss.map φ) : Multiset ℝ)
                = Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := hleft_multiset
            _ = (fPolynomial d u).roots := by
                    symm
                    simpa [φ] using
                      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
                        hud hu_rr.1 hu_rr.2 hu_nonneg
        have hright_eq : (↑((r₁ :: rest).map φ) : Multiset ℝ) = (fPolynomial d v).roots := by
          calc
            (↑((r₁ :: rest).map φ) : Multiset ℝ) = v.roots.map φ := by lia
            _ = (fPolynomial d v).roots := by
                symm
                simpa [φ, hvd_pad] using
                  roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
                    hvd hv_rr.1 hv_rr.2 hv_nonneg
        refine ⟨hfu_rr, hfv_rr, (-1) :: ss.map φ, (r₁ :: rest).map φ,
          hleft_sorted, hrs_map_sorted, hleft_eq, hright_eq, Or.inr ?_⟩
        refine ⟨by simp_all, ?_⟩
        simpa [φ] using
          listAlternates_neg_one_cons_map_of_listInterlaces_of_nonpos
            (ss := ss) (r₁ := r₁) (rs := rest) hint hrs_nonpos
  · have hlen_deg_u : ss.length = u.natDegree := by
      rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hu_rr.2]
    have hlen_deg_v : rs.length = v.natDegree := by
      rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hv_rr.2]
    have hud_pad : d - u.natDegree = 0 := by simp_all
    have hvd_pad : d - v.natDegree = 0 := by lia
    have hleft_eq : (↑(ss.map φ) : Multiset ℝ) = (fPolynomial d u).roots := by
      calc
        (↑(ss.map φ) : Multiset ℝ) = u.roots.map φ := by lia
        _ = (fPolynomial d u).roots := by
            symm
            simpa [φ, hud_pad] using
              roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
                hud hu_rr.1 hu_rr.2 hu_nonneg
    have hright_eq : (↑(rs.map φ) : Multiset ℝ) = (fPolynomial d v).roots := by
      calc
        (↑(rs.map φ) : Multiset ℝ) = v.roots.map φ := by lia
        _ = (fPolynomial d v).roots := by
            symm
            simpa [φ, hvd_pad] using
              roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
                hvd hv_rr.1 hv_rr.2 hv_nonneg
    refine ⟨hfu_rr, hfv_rr, ss.map φ, rs.map φ,
      hss_map_sorted, hrs_map_sorted, hleft_eq, hright_eq, Or.inr ?_⟩
    refine ⟨by simp_all, ?_⟩
    simpa [φ] using listAlternates_map_transformedRoot_of_nonpos halt hrs_nonpos

theorem prec_of_prec_fPolynomial_of_sameDegree_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {u v : ℝ[X]}
    (hud : u.natDegree = d) (hvd : v.natDegree = d)
    (hu_rr_ne : u ≠ 0) (hu_rr_splits : u.Splits)
    (hv_rr_ne : v ≠ 0) (hv_rr_splits : v.Splits)
    (h : Prec (fPolynomial d u) (fPolynomial d v))
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    Prec u v := by
  let φ := fun r : ℝ => r / (1 - r)
  rcases h with ⟨hfu_rr, hfv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud_le : u.natDegree ≤ d := by lia
  have hvd_le : v.natDegree ≤ d := by lia
  have hfu_deg : (fPolynomial d u).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hud_le hu_nonneg hu_rr_ne
  have hfv_deg : (fPolynomial d v).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hvd_le hv_nonneg hv_rr_ne
  have hss_len : ss.length = d := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hfu_rr.2, hfu_deg]
  have hrs_len : rs.length = d := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hfv_rr.2, hfv_deg]
  have hfu_roots :
      (fPolynomial d u).roots = u.roots.map φ := by
    simpa [φ, hud] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hud_le hu_rr_ne hu_rr_splits hu_nonneg
  have hfv_roots :
      (fPolynomial d v).roots = v.roots.map φ := by
    simpa [φ, hvd] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hvd_le hv_rr_ne hv_rr_splits hv_nonneg
  have hss_eq_map : (↑ss : Multiset ℝ) = u.roots.map φ := by lia
  have hrs_eq_map : (↑rs : Multiset ℝ) = v.roots.map φ := by lia
  have hss_gt_neg_one : ∀ s ∈ ss, -1 < s := by
    intro s hs
    have hs_mem : s ∈ (fPolynomial d u).roots := by simpa [hss_eq] using Multiset.mem_coe.mpr hs
    rw [hfu_roots] at hs_mem
    rcases Multiset.mem_map.mp hs_mem with ⟨r, hr, rfl⟩
    exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)
  have hrs_gt_neg_one : ∀ r ∈ rs, -1 < r := by
    intro r hr
    have hr_mem : r ∈ (fPolynomial d v).roots := by simpa [hrs_eq] using Multiset.mem_coe.mpr hr
    rw [hfv_roots] at hr_mem
    rcases Multiset.mem_map.mp hr_mem with ⟨s, hs, rfl⟩
    exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hv_rr_splits hv_nonneg s hs)
  have hss'_sorted : (ss.map untransformRoot).Pairwise (· ≤ ·) :=
    pairwise_map_untransformRoot_of_neg_one_lt hss_sorted hss_gt_neg_one
  have hrs'_sorted : (rs.map untransformRoot).Pairwise (· ≤ ·) :=
    pairwise_map_untransformRoot_of_neg_one_lt hrs_sorted hrs_gt_neg_one
  have hss'_eq : (↑(ss.map untransformRoot) : Multiset ℝ) = u.roots := by
    have hmap :
        (↑(ss.map untransformRoot) : Multiset ℝ) = (u.roots.map φ).map untransformRoot := by
      simpa [φ] using congrArg (fun t : Multiset ℝ => t.map untransformRoot) hss_eq_map
    calc
      (↑(ss.map untransformRoot) : Multiset ℝ)
          = (u.roots.map φ).map untransformRoot := hmap
      _ = u.roots.map (fun r : ℝ => untransformRoot (φ r)) := by simp
      _ = u.roots.map (fun r : ℝ => r) := by
            refine Multiset.map_congr rfl ?_
            intro r hr
            simp [φ, untransformRoot_transformedRoot
              (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)]
      _ = u.roots := by simp
  have hrs'_eq : (↑(rs.map untransformRoot) : Multiset ℝ) = v.roots := by
    have hmap :
        (↑(rs.map untransformRoot) : Multiset ℝ) = (v.roots.map φ).map untransformRoot := by
      simpa [φ] using congrArg (fun t : Multiset ℝ => t.map untransformRoot) hrs_eq_map
    calc
      (↑(rs.map untransformRoot) : Multiset ℝ)
          = (v.roots.map φ).map untransformRoot := hmap
      _ = v.roots.map (fun r : ℝ => untransformRoot (φ r)) := by simp
      _ = v.roots.map (fun r : ℝ => r) := by
            refine Multiset.map_congr rfl ?_
            intro r hr
            simp [φ, untransformRoot_transformedRoot
              (roots_nonpos_of_nonneg_coeffs hv_rr_splits hv_nonneg r hr)]
      _ = v.roots := by simp
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · lia
  · refine ⟨⟨hu_rr_ne, hu_rr_splits⟩, ⟨hv_rr_ne, hv_rr_splits⟩,
      ss.map untransformRoot, rs.map untransformRoot,
      hss'_sorted, hrs'_sorted, hss'_eq, hrs'_eq, Or.inr ?_⟩
    refine ⟨by simp_all, ?_⟩
    exact listAlternates_map_untransformRoot_of_neg_one_lt halt hss_gt_neg_one hrs_gt_neg_one

theorem prec_of_prec_fPolynomial_of_succDegree_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {u v : ℝ[X]}
    (hud : u.natDegree + 1 = d) (hvd : v.natDegree = d)
    (hu_rr_ne : u ≠ 0) (hu_rr_splits : u.Splits)
    (hv_rr_ne : v ≠ 0) (hv_rr_splits : v.Splits)
    (h : Prec (fPolynomial d u) (fPolynomial d v))
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    Prec u v := by
  let φ := fun r : ℝ => r / (1 - r)
  rcases h with ⟨hfu_rr, hfv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud_le : u.natDegree ≤ d := by lia
  have hvd_le : v.natDegree ≤ d := by lia
  have hud_pad : d - u.natDegree = 1 := by lia
  have hvd_pad : d - v.natDegree = 0 := by lia
  have hd_pos : 0 < d := by lia
  have hfu_deg : (fPolynomial d u).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hud_le hu_nonneg hu_rr_ne
  have hfv_deg : (fPolynomial d v).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hvd_le hv_nonneg hv_rr_ne
  have hss_len : ss.length = d := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hfu_rr.2, hfu_deg]
  have hrs_len : rs.length = d := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hfv_rr.2, hfv_deg]
  have hfu_roots :
      (fPolynomial d u).roots = ({-1} : Multiset ℝ) + u.roots.map φ := by
    simpa [φ, hud_pad] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hud_le hu_rr_ne hu_rr_splits hu_nonneg
  have hfv_roots :
      (fPolynomial d v).roots = v.roots.map φ := by
    simpa [φ, hvd_pad] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hvd_le hv_rr_ne hv_rr_splits hv_nonneg
  have hss_eq_full : (↑ss : Multiset ℝ) = ({-1} : Multiset ℝ) + u.roots.map φ := by lia
  have hrs_eq_map : (↑rs : Multiset ℝ) = v.roots.map φ := by lia
  cases ss with
  | nil =>
      simp_all
  | cons s ss' =>
      have hs_ge_neg_one : -1 ≤ s := by
        have hs_mem : s ∈ (↑(s :: ss') : Multiset ℝ) := by simp
        rw [hss_eq_full] at hs_mem
        rcases Multiset.mem_add.mp hs_mem with hs | hs
        · simp_all
        · rcases Multiset.mem_map.mp hs with ⟨r, hr, rfl⟩
          exact le_of_lt <|
            neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)
      have hs_eq : s = -1 := by
        have hminus_mem : (-1 : ℝ) ∈ s :: ss' := by
          have hminus_mem' : (-1 : ℝ) ∈ (↑(s :: ss') : Multiset ℝ) := by simp_all
          simpa using hminus_mem'
        rcases List.mem_cons.mp hminus_mem with hs | hs_tail
        · lia
        · have hs_le_neg_one : s ≤ -1 := List.rel_of_pairwise_cons hss_sorted hs_tail
          linarith
      have hss_tail_eq : (↑ss' : Multiset ℝ) = u.roots.map φ := by
        have hcons :
            ({-1} : Multiset ℝ) + (↑ss' : Multiset ℝ) =
              ({-1} : Multiset ℝ) + u.roots.map φ := by
          simp_all
        exact add_left_cancel hcons
      have hss_tail_sorted : ss'.Pairwise (· ≤ ·) := hss_sorted.tail
      have hss_tail_gt_neg_one : ∀ x ∈ ss', -1 < x := by
        intro x hx
        have hx_mem : x ∈ (↑ss' : Multiset ℝ) := by simpa using hx
        rw [hss_tail_eq] at hx_mem
        rcases Multiset.mem_map.mp hx_mem with ⟨r, hr, rfl⟩
        exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)
      have hrs_gt_neg_one : ∀ x ∈ rs, -1 < x := by
        intro x hx
        have hx_mem : x ∈ (↑rs : Multiset ℝ) := by simpa using hx
        rw [hrs_eq_map] at hx_mem
        rcases Multiset.mem_map.mp hx_mem with ⟨r, hr, rfl⟩
        exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hv_rr_splits hv_nonneg r hr)
      have hss'_sorted : (ss'.map untransformRoot).Pairwise (· ≤ ·) :=
        pairwise_map_untransformRoot_of_neg_one_lt hss_tail_sorted hss_tail_gt_neg_one
      have hrs'_sorted : (rs.map untransformRoot).Pairwise (· ≤ ·) :=
        pairwise_map_untransformRoot_of_neg_one_lt hrs_sorted hrs_gt_neg_one
      have hss'_eq : (↑(ss'.map untransformRoot) : Multiset ℝ) = u.roots := by
        have hmap :
            (↑(ss'.map untransformRoot) : Multiset ℝ) =
              (u.roots.map φ).map untransformRoot := by
          simpa [φ] using congrArg (fun t : Multiset ℝ => t.map untransformRoot) hss_tail_eq
        calc
          (↑(ss'.map untransformRoot) : Multiset ℝ)
              = (u.roots.map φ).map untransformRoot := hmap
          _ = u.roots.map (fun r : ℝ => untransformRoot (φ r)) := by simp
          _ = u.roots.map (fun r : ℝ => r) := by
                refine Multiset.map_congr rfl ?_
                intro r hr
                simp [φ, untransformRoot_transformedRoot
                  (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)]
          _ = u.roots := by simp
      have hrs'_eq : (↑(rs.map untransformRoot) : Multiset ℝ) = v.roots := by
        have hmap :
            (↑(rs.map untransformRoot) : Multiset ℝ) =
              (v.roots.map φ).map untransformRoot := by
          simpa [φ] using congrArg (fun t : Multiset ℝ => t.map untransformRoot) hrs_eq_map
        calc
          (↑(rs.map untransformRoot) : Multiset ℝ)
              = (v.roots.map φ).map untransformRoot := hmap
          _ = v.roots.map (fun r : ℝ => untransformRoot (φ r)) := by simp
          _ = v.roots.map (fun r : ℝ => r) := by
                refine Multiset.map_congr rfl ?_
                intro r hr
                simp [φ, untransformRoot_transformedRoot
                  (roots_nonpos_of_nonneg_coeffs hv_rr_splits hv_nonneg r hr)]
          _ = v.roots := by simp
      rcases hshape with ⟨hlen, _⟩ | ⟨hlen, halt⟩
      · lia
      · cases rs with
        | nil =>
            simp_all
        | cons r rs' =>
            have hint : ListInterlaces ss' (r :: rs') := by
              have hhalt : -1 ≤ r ∧ ListInterlaces ss' (r :: rs') := by
                simpa [hs_eq, ListAlternates] using halt
              lia
            refine ⟨⟨hu_rr_ne, hu_rr_splits⟩, ⟨hv_rr_ne, hv_rr_splits⟩,
              ss'.map untransformRoot, (r :: rs').map untransformRoot,
              hss'_sorted, hrs'_sorted, hss'_eq, hrs'_eq, Or.inl ?_⟩
            refine ⟨?_, ?_⟩
            · simp_all
            · exact listInterlaces_map_untransformRoot_of_neg_one_lt
                hint hss_tail_gt_neg_one hrs_gt_neg_one

private theorem not_prec_fPolynomial_of_right_degree_lt_of_sameDegree_left
    {d : ℕ} {u v : ℝ[X]}
    (hud : u.natDegree = d) (hvd : v.natDegree < d)
    (hu_rr_ne : u ≠ 0) (hu_rr_splits : u.Splits)
    (hv_rr_ne : v ≠ 0) (hv_rr_splits : v.Splits)
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    ¬ Prec (fPolynomial d u) (fPolynomial d v) := by
  let φ := fun r : ℝ => r / (1 - r)
  intro h
  rcases h with ⟨hfu_rr, hfv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud_le : u.natDegree ≤ d := by lia
  have hvd_le : v.natDegree ≤ d := le_of_lt hvd
  have hd_pos : 0 < d := by lia
  have hfu_deg : (fPolynomial d u).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hud_le hu_nonneg hu_rr_ne
  have hfv_deg : (fPolynomial d v).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hvd_le hv_nonneg hv_rr_ne
  have hss_len : ss.length = d := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hfu_rr.2, hfu_deg]
  have hrs_len : rs.length = d := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hfv_rr.2, hfv_deg]
  have hud_pad : d - u.natDegree = 0 := by lia
  have hfu_roots :
      (fPolynomial d u).roots = u.roots.map φ := by
    simpa [φ, hud_pad] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hud_le hu_rr_ne hu_rr_splits hu_nonneg
  have hss_gt_neg_one : ∀ x ∈ ss, -1 < x := by
    intro x hx
    have hx_mem : x ∈ (fPolynomial d u).roots := by simpa [hss_eq] using Multiset.mem_coe.mpr hx
    rw [hfu_roots] at hx_mem
    rcases Multiset.mem_map.mp hx_mem with ⟨r, hr, rfl⟩
    exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)
  have hminus_mem : (-1 : ℝ) ∈ rs := by
    have hminus_mem' : (-1 : ℝ) ∈ (fPolynomial d v).roots :=
      (mem_roots hfv_rr.1).2 (isRoot_neg_one_fPolynomial_of_natDegree_lt hvd)
    rw [← hrs_eq] at hminus_mem'
    simpa using hminus_mem'
  cases rs with
  | nil =>
      simp_all
  | cons r rs' =>
      have hfv_roots :
          (fPolynomial d v).roots =
            Multiset.replicate (d - v.natDegree) (-1) + v.roots.map φ := by
        simpa [φ] using
          roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
            hvd_le hv_rr_ne hv_rr_splits hv_nonneg
      have hr_ge_neg_one : -1 ≤ r := by
        have hr_mem : r ∈ (fPolynomial d v).roots := by
          simpa [hrs_eq] using Multiset.mem_coe.mpr (by simp : r ∈ r :: rs')
        rw [hfv_roots] at hr_mem
        rcases Multiset.mem_add.mp hr_mem with hr | hr
        · have hr' : r = -1 := (Multiset.mem_replicate.mp hr).2
          simp_all
        · rcases Multiset.mem_map.mp hr with ⟨s, hs, rfl⟩
          exact le_of_lt <|
            neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hv_rr_splits hv_nonneg s hs)
      have hr_eq : r = -1 := by
        rcases List.mem_cons.mp hminus_mem with hr | hr_tail
        · lia
        · have hr_le_neg_one : r ≤ -1 := List.rel_of_pairwise_cons hrs_sorted hr_tail
          linarith
      cases ss with
      | nil =>
          simp_all
      | cons s ss' =>
          rcases hshape with ⟨hlen, _⟩ | ⟨hlen, halt⟩
          · lia
          · have hs_le_r : s ≤ r := by
              have hhalt : s ≤ r ∧ ListInterlaces ss' (r :: rs') := by
                simpa [ListAlternates] using halt
              lia
            have hs_gt_neg_one : -1 < s := hss_gt_neg_one s (by simp)
            linarith

private theorem not_prec_fPolynomial_of_left_degree_le_sub_two_of_right_full
    {d : ℕ} {u v : ℝ[X]}
    (hud : u.natDegree + 2 ≤ d) (hvd : v.natDegree = d)
    (hu_rr_ne : u ≠ 0) (hu_rr_splits : u.Splits)
    (hv_rr_ne : v ≠ 0) (hv_rr_splits : v.Splits)
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    ¬ Prec (fPolynomial d u) (fPolynomial d v) := by
  let φ := fun r : ℝ => r / (1 - r)
  intro h
  rcases h with ⟨hfu_rr, hfv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud_le : u.natDegree ≤ d := by lia
  have hvd_le : v.natDegree ≤ d := by lia
  have hd_pos : 0 < d := by lia
  have hfu_deg : (fPolynomial d u).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hud_le hu_nonneg hu_rr_ne
  have hfv_deg : (fPolynomial d v).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hvd_le hv_nonneg hv_rr_ne
  have hss_len : ss.length = d := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hfu_rr.2, hfu_deg]
  have hrs_len : rs.length = d := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hfv_rr.2, hfv_deg]
  have hud_pad_two : 2 ≤ d - u.natDegree := by lia
  have hfu_roots :
      (fPolynomial d u).roots =
        Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := by
    simpa [φ] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hud_le hu_rr_ne hu_rr_splits hu_nonneg
  have hss_ge_neg_one : ∀ x ∈ ss, -1 ≤ x := by
    intro x hx
    have hx_mem : x ∈ (fPolynomial d u).roots := by simpa [hss_eq] using Multiset.mem_coe.mpr hx
    rw [hfu_roots] at hx_mem
    rcases Multiset.mem_add.mp hx_mem with hx | hx
    · have hx' : x = -1 := (Multiset.mem_replicate.mp hx).2
      simp_all
    · rcases Multiset.mem_map.mp hx with ⟨r, hr, rfl⟩
      exact le_of_lt <|
        neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)
  have hminus_mem : (-1 : ℝ) ∈ ss := by
    have hminus_mem' : (-1 : ℝ) ∈ (fPolynomial d u).roots := by
      rw [hfu_roots]
      exact Multiset.mem_add.mpr <| Or.inl <|
        Multiset.mem_replicate.mpr ⟨by lia, rfl⟩
    rw [← hss_eq] at hminus_mem'
    simpa using hminus_mem'
  cases ss with
  | nil =>
      simp_all
  | cons s ss' =>
      have hss_eq_full :
          (↑(s :: ss') : Multiset ℝ) =
            Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := by
        lia
      have hs_eq : s = -1 := by
        have hs_ge_neg_one : -1 ≤ s := hss_ge_neg_one s (by simp)
        rcases List.mem_cons.mp hminus_mem with hs | hs_tail
        · lia
        · have hs_le_neg_one : s ≤ -1 := List.rel_of_pairwise_cons hss_sorted hs_tail
          linarith
      have hkpos : 0 < d - u.natDegree := by lia
      have hrep :
          Multiset.replicate (d - u.natDegree) (-1) =
            ({-1} : Multiset ℝ) + Multiset.replicate (d - u.natDegree - 1) (-1) := by
        rw [show d - u.natDegree = 1 + (d - u.natDegree - 1) by lia, Multiset.replicate_add]
        simp
      have hss_tail_eq :
          (↑ss' : Multiset ℝ) =
            Multiset.replicate (d - u.natDegree - 1) (-1) + u.roots.map φ := by
        have hcons :
            ({-1} : Multiset ℝ) + (↑ss' : Multiset ℝ) =
              ({-1} : Multiset ℝ) +
                (Multiset.replicate (d - u.natDegree - 1) (-1) + u.roots.map φ) := by
          simp_all
        exact add_left_cancel hcons
      have hminus_mem_tail : (-1 : ℝ) ∈ ss' := by
        have hminus_mem_tail' : (-1 : ℝ) ∈ (↑ss' : Multiset ℝ) := by
          rw [hss_tail_eq]
          exact Multiset.mem_add.mpr <| Or.inl <|
            Multiset.mem_replicate.mpr ⟨by lia, rfl⟩
        simpa using hminus_mem_tail'
      have hfv_roots :
          (fPolynomial d v).roots = v.roots.map φ := by
        have hvd_pad : d - v.natDegree = 0 := by lia
        simpa [φ, hvd_pad] using
          roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
            hvd_le hv_rr_ne hv_rr_splits hv_nonneg
      have hrs_gt_neg_one : ∀ x ∈ rs, -1 < x := by
        intro x hx
        have hx_mem : x ∈ (fPolynomial d v).roots := by
          simpa [hrs_eq] using Multiset.mem_coe.mpr hx
        rw [hfv_roots] at hx_mem
        rcases Multiset.mem_map.mp hx_mem with ⟨r, hr, rfl⟩
        exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hv_rr_splits hv_nonneg r hr)
      cases rs with
      | nil =>
          simp_all
      | cons r rs' =>
          rcases hshape with ⟨hlen, _⟩ | ⟨hlen, halt⟩
          · lia
          · have hhalt : -1 ≤ r ∧ ListInterlaces ss' (r :: rs') := by
              simpa [hs_eq, ListAlternates] using halt
            have hr_gt_neg_one : -1 < r := hrs_gt_neg_one r (by simp)
            have hr_le_neg_one : r ≤ -1 :=
              listInterlaces_all_ge ss' rs' r hhalt.2 (-1) hminus_mem_tail
            linarith

theorem prec_of_prec_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {u v : ℝ[X]}
    (hd : d = max u.natDegree v.natDegree)
    (hu_rr_ne : u ≠ 0) (hu_rr_splits : u.Splits)
    (hv_rr_ne : v ≠ 0) (hv_rr_splits : v.Splits)
    (h : Prec (fPolynomial d u) (fPolynomial d v))
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    Prec u v := by
  have hud : u.natDegree ≤ d := by simp_all
  have hvd : v.natDegree ≤ d := by simp_all
  by_cases hv_eq : v.natDegree = d
  · by_cases hu_eq : u.natDegree = d
    · exact prec_of_prec_fPolynomial_of_sameDegree_of_isRealRooted_of_hasNonnegCoeffs
        hu_eq hv_eq hu_rr_ne hu_rr_splits hv_rr_ne hv_rr_splits h hu_nonneg hv_nonneg
    · have hu_lt : u.natDegree < d := lt_of_le_of_ne hud hu_eq
      by_cases hu_succ : u.natDegree + 1 = d
      · exact prec_of_prec_fPolynomial_of_succDegree_of_isRealRooted_of_hasNonnegCoeffs
          hu_succ hv_eq hu_rr_ne hu_rr_splits hv_rr_ne hv_rr_splits h hu_nonneg hv_nonneg
      · have hu_two : u.natDegree + 2 ≤ d := by lia
        exact False.elim <|
          not_prec_fPolynomial_of_left_degree_le_sub_two_of_right_full
            hu_two hv_eq hu_rr_ne hu_rr_splits hv_rr_ne hv_rr_splits hu_nonneg hv_nonneg h
  · have hv_lt : v.natDegree < d := lt_of_le_of_ne hvd hv_eq
    have hu_eq : u.natDegree = d := by grind
    exact False.elim <|
      not_prec_fPolynomial_of_right_degree_lt_of_sameDegree_left
        hu_eq hv_lt hu_rr_ne hu_rr_splits hv_rr_ne hv_rr_splits hu_nonneg hv_nonneg h

theorem prec_iff_prec_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {u v : ℝ[X]}
    (hd : d = max u.natDegree v.natDegree)
    (hu_rr_ne : u ≠ 0) (hu_rr_splits : u.Splits)
    (hv_rr_ne : v ≠ 0) (hv_rr_splits : v.Splits)
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    (Prec (fPolynomial d u) (fPolynomial d v) ↔ Prec u v) := by
  constructor
  · intro h
    exact prec_of_prec_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs
      hd hu_rr_ne hu_rr_splits hv_rr_ne hv_rr_splits h hu_nonneg hv_nonneg
  · intro h
    exact prec_fPolynomial_of_prec_of_hasNonnegCoeffs_of_minimal
      hd h hu_nonneg hv_nonneg

/-- If `u ≺ v` and both have nonnegative coefficients, then their
Brändén--Solus `f`-polynomials form a positive-combination real-rooted pair. -/
theorem posComboRealRooted_fPolynomial_of_prec
    {d : ℕ} {u v : ℝ[X]} (h : Prec u v)
    (hud : u.natDegree ≤ d) (hvd : v.natDegree ≤ d)
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    PosComboRealRooted (fPolynomial d u) (fPolynomial d v) := by
  have hu_pos : HasPosLeadingCoeff u := hu_nonneg.pos_leadingCoeff h.1.1
  have hv_pos : HasPosLeadingCoeff v := hv_nonneg.pos_leadingCoeff h.2.1.1
  intro lam μ hlam hμ
  have hcombo_rr : ((C lam * u + C μ * v) ≠ 0 ∧ (C lam * u + C μ * v).Splits) :=
    PosComboRealRooted.of_prec h hu_pos hv_pos hlam hμ
  have hcombo_nonneg : HasNonnegCoeffs (C lam * u + C μ * v) :=
    (nonnegCoeffs_C_mul hlam.le hu_nonneg).add (nonnegCoeffs_C_mul hμ.le hv_nonneg)
  have hcombo_deg : (C lam * u + C μ * v).natDegree ≤ d := by
    have hud' : (C lam * u).natDegree ≤ d := by
      rw [Polynomial.natDegree_C_mul hlam.ne']
      lia
    have hvd' : (C μ * v).natDegree ≤ d := by
      rw [Polynomial.natDegree_C_mul hμ.ne']
      lia
    simpa using Polynomial.natDegree_add_le_of_le hud' hvd'
  simpa [fPolynomial_add, fPolynomial_C_mul] using
    isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs
      hcombo_deg hcombo_rr.1 hcombo_rr.2 hcombo_nonneg


end RealRooted
