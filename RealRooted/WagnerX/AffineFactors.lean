import RealRooted.WagnerX.NonnegativeRoots

/-!
# Wagner-X affine and common-factor transport
-/

open Polynomial Filter

noncomputable section

namespace RealRooted

theorem prec_mul_X_sub_C_both_of_roots_le {f g : ℝ[X]} (r : ℝ) (h : Prec f g)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r) :
    Prec ((X - C r) * f) ((X - C r) * g) := by
  set f' := f.comp (X + C r)
  set g' := g.comp (X + C r)
  have hfg' : Prec f' g' := by simpa [f', g'] using (prec_comp_X_add_C_iff (f := f) (g := g) r).2 h
  have hf'_nonpos : ∀ s ∈ f'.roots, s ≤ 0 := by
    intro s hs
    simp only [f', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    simp_all
  have hg'_nonpos : ∀ s ∈ g'.roots, s ≤ 0 := by
    intro s hs
    simp only [g', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    simp_all
  have hX' : Prec (X * f') (X * g') :=
    prec_mul_X_both_of_roots_nonpos hfg' hf'_nonpos hg'_nonpos
  have htranslated :
      Prec (((X - C r) * f).comp (X + C r)) (((X - C r) * g).comp (X + C r)) := by
    simpa [f', g', mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg,
      comp_assoc, add_assoc, add_left_comm, add_comm] using hX'
  exact (prec_comp_X_add_C_iff (f := (X - C r) * f) (g := (X - C r) * g) r).1 htranslated

theorem prec_of_prec_mul_X_sub_C_both_of_roots_le {f g : ℝ[X]} (r : ℝ)
    (h : Prec ((X - C r) * f) ((X - C r) * g))
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r) :
    Prec f g := by
  set f' := f.comp (X + C r)
  set g' := g.comp (X + C r)
  have htranslated :
      Prec (((X - C r) * f).comp (X + C r)) (((X - C r) * g).comp (X + C r)) := by
    simpa using (prec_comp_X_add_C_iff (f := (X - C r) * f) (g := (X - C r) * g) r).2 h
  have hf'_nonpos : ∀ s ∈ f'.roots, s ≤ 0 := by
    intro s hs
    simp only [f', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    simp_all
  have hg'_nonpos : ∀ s ∈ g'.roots, s ≤ 0 := by
    intro s hs
    simp only [g', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    simp_all
  have hfg' : Prec f' g' := by
    have hX' : Prec (X * f') (X * g') := by
      simpa [f', g', mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg,
        comp_assoc, add_assoc, add_left_comm, add_comm] using htranslated
    exact prec_of_prec_mul_X_both_of_roots_nonpos hX' hf'_nonpos hg'_nonpos
  exact (prec_comp_X_add_C_iff (f := f) (g := g) r).1 (by lia)

theorem prec_iff_prec_mul_X_sub_C_both_of_roots_le {f g : ℝ[X]} (r : ℝ)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r) :
    Prec f g ↔ Prec ((X - C r) * f) ((X - C r) * g) :=
  ⟨fun h => prec_mul_X_sub_C_both_of_roots_le r h hf_le hg_le,
    fun h => prec_of_prec_mul_X_sub_C_both_of_roots_le r h hf_le hg_le⟩

theorem prec_mul_X_sub_C_both {f g : ℝ[X]} (r : ℝ) (h : Prec f g) :
    Prec ((X - C r) * f) ((X - C r) * g) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  refine ⟨isRealRooted_mul (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hf.1 hf.2,
    isRealRooted_mul (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hg.1 hg.2,
    ss.orderedInsert (· ≤ ·) r, rs.orderedInsert (· ≤ ·) r,
    hss.orderedInsert _ _, hrs.orderedInsert _ _, ?_, ?_, ?_⟩
  · have hinsert :
        (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) =
          ({r} : Multiset ℝ) + (↑ss : Multiset ℝ) := by
        calc
          (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ↑(r :: ss) :=
            Multiset.coe_eq_coe.mpr (List.perm_orderedInsert (r := (· ≤ ·)) r ss)
          _ = ({r} : Multiset ℝ) + (↑ss : Multiset ℝ) := by simp
    have hroots :
        ({r} : Multiset ℝ) + (↑ss : Multiset ℝ) = ((X - C r) * f).roots := by
      rw [hss_eq]
      simpa [roots_X_sub_C] using (roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hf.1)).symm
    lia
  · have hinsert :
        (↑(rs.orderedInsert (· ≤ ·) r) : Multiset ℝ) =
          ({r} : Multiset ℝ) + (↑rs : Multiset ℝ) := by
        calc
          (↑(rs.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ↑(r :: rs) :=
            Multiset.coe_eq_coe.mpr (List.perm_orderedInsert (r := (· ≤ ·)) r rs)
          _ = ({r} : Multiset ℝ) + (↑rs : Multiset ℝ) := by simp
    have hroots :
        ({r} : Multiset ℝ) + (↑rs : Multiset ℝ) = ((X - C r) * g).roots := by
      rw [hrs_eq]
      simpa [roots_X_sub_C] using (roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hg.1)).symm
    lia
  · rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
    · refine Or.inl ⟨?_, listInterlaces_orderedInsert hlen hint r⟩
      rw [List.orderedInsert_length (r := (· ≤ ·)) ss r,
        List.orderedInsert_length (r := (· ≤ ·)) rs r]
      lia
    · exact Or.inr ⟨by
        rw [List.orderedInsert_length (r := (· ≤ ·)) ss r,
          List.orderedInsert_length (r := (· ≤ ·)) rs r]
        lia,
        listAlternates_orderedInsert hlen halt r⟩

theorem prec_of_prec_mul_X_sub_C_both {f g : ℝ[X]} (r : ℝ)
    (h : Prec ((X - C r) * f) ((X - C r) * g)) :
    Prec f g := by
  rcases h with ⟨hXf, hXg, ss_mul, rs_mul, hss_mul, hrs_mul, hss_mul_eq, hrs_mul_eq, hcase⟩
  have hf0 : f ≠ 0 := right_ne_zero_of_mul hXf.1
  have hg0 : g ≠ 0 := right_ne_zero_of_mul hXg.1
  have hf : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_dvd hXf.1 hXf.2 hf0 (dvd_mul_left f _)
  have hg : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_dvd hXg.1 hXg.2 hg0 (dvd_mul_left g _)
  set ss := f.roots.sort (· ≤ ·)
  set rs := g.roots.sort (· ≤ ·)
  have hss_eq : (↑ss : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_eq : (↑rs : Multiset ℝ) = g.roots := Multiset.sort_eq ..
  have hss_sorted : ss.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hss_insert_eq :
      (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ((X - C r) * f).roots := by
    rw [show (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) =
        ({r} : Multiset ℝ) + (↑ss : Multiset ℝ) by
          calc
            (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ↑(r :: ss) :=
              Multiset.coe_eq_coe.mpr (List.perm_orderedInsert (r := (· ≤ ·)) r ss)
            _ = ({r} : Multiset ℝ) + (↑ss : Multiset ℝ) := by simp]
    rw [hss_eq]
    symm
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hf.1), roots_X_sub_C]
  have hrs_insert_eq :
      (↑(rs.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ((X - C r) * g).roots := by
    rw [show (↑(rs.orderedInsert (· ≤ ·) r) : Multiset ℝ) =
        ({r} : Multiset ℝ) + (↑rs : Multiset ℝ) by
          calc
            (↑(rs.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ↑(r :: rs) :=
              Multiset.coe_eq_coe.mpr (List.perm_orderedInsert (r := (· ≤ ·)) r rs)
            _ = ({r} : Multiset ℝ) + (↑rs : Multiset ℝ) := by simp]
    rw [hrs_eq]
    symm
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hg.1), roots_X_sub_C]
  have hss_mul_is : ss_mul = ss.orderedInsert (· ≤ ·) r :=
    List.Perm.eq_of_pairwise' hss_mul (hss_sorted.orderedInsert _ _)
      (Multiset.coe_eq_coe.mp (hss_mul_eq.trans hss_insert_eq.symm))
  have hrs_mul_is : rs_mul = rs.orderedInsert (· ≤ ·) r :=
    List.Perm.eq_of_pairwise' hrs_mul (hrs_sorted.orderedInsert _ _)
      (Multiset.coe_eq_coe.mp (hrs_mul_eq.trans hrs_insert_eq.symm))
  refine ⟨hf, hg, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, ?_⟩
  rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · rw [hss_mul_is, hrs_mul_is] at hint hlen
    have hlen' : ss.length + 1 = rs.length := by
      simp only [List.orderedInsert_length] at hlen
      lia
    exact Or.inl ⟨hlen', listInterlaces_of_orderedInsert r hlen' hss_sorted hrs_sorted hint⟩
  · rw [hss_mul_is, hrs_mul_is] at halt hlen
    have hlen' : ss.length = rs.length := by
      simp only [List.orderedInsert_length] at hlen
      lia
    exact Or.inr ⟨hlen', listAlternates_of_orderedInsert r hlen' hss_sorted hrs_sorted halt⟩

theorem prec_mul_common_factor {d f g : ℝ[X]} (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    (h : Prec f g) :
    Prec (d * f) (d * g) := by
  have hprod : Prec (((d.roots.map fun a => X - C a).prod) * f)
      (((d.roots.map fun a => X - C a).prod) * g) := by
    induction d.roots using Multiset.induction_on with
    | empty =>
        simp_all
    | @cons a s ih =>
        simpa [Multiset.map_cons, Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using
          prec_mul_X_sub_C_both a ih
  have hlc0 : d.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hd_ne
  have hscaled :
      Prec ((C d.leadingCoeff * (d.roots.map fun a => X - C a).prod) * f)
        ((C d.leadingCoeff * (d.roots.map fun a => X - C a).prod) * g) := by
    have hleft := prec_C_mul_left hprod hlc0
    have hboth := prec_C_mul_right hleft hlc0
    simpa [mul_assoc, mul_left_comm, mul_comm] using hboth
  simpa [C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_of_splits hd_splits), mul_assoc]
    using hscaled

theorem prec_iff_prec_mul_X_sub_C_of_roots_le {f g : ℝ[X]} (r : ℝ)
    (hf : f.Splits) (hg : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Prec f g ↔ Prec g ((X - C r) * f) := by
  set f' := f.comp (X + C r)
  set g' := g.comp (X + C r)
  have hf' : f' ≠ 0 ∧ f'.Splits := by
    simpa [f'] using isRealRooted_comp_X_add_C hf_pos.ne_zero hf r
  have hg' : g' ≠ 0 ∧ g'.Splits := by
    simpa [g'] using isRealRooted_comp_X_add_C hg_pos.ne_zero hg r
  have hf'_pos : HasPosLeadingCoeff f' := by simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by simpa [g'] using hg_pos.comp_X_add_C r
  have hf'_nonpos : ∀ s ∈ f'.roots, s ≤ 0 := by
    intro s hs
    simp only [f', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    simp_all
  have hg'_nonpos : ∀ s ∈ g'.roots, s ≤ 0 := by
    intro s hs
    simp only [g', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    simp_all
  have hdeg' : f'.natDegree + 1 = g'.natDegree := by simpa [f', g', natDegree_comp] using hdeg
  have hshift :
      Prec f' g' ↔ Prec g' (X * f') :=
    prec_iff_prec_mul_X_of_roots_nonpos hf'.2 hg'.2 hf'_pos hg'_pos hf'_nonpos hg'_nonpos hdeg'
  constructor
  · intro hfg
    have hfg' : Prec f' g' := by
      simpa [f', g'] using (prec_comp_X_add_C_iff (f := f) (g := g) r).2 hfg
    have hgxf' : Prec g' (X * f') := hshift.mp hfg'
    have htranslated : Prec g' (((X - C r) * f).comp (X + C r)) := by
      simpa [f', g', mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg,
        comp_assoc, add_assoc, add_left_comm, add_comm] using hgxf'
    exact (prec_comp_X_add_C_iff (f := g) (g := (X - C r) * f) r).1 htranslated
  · intro hgf
    have hgf' : Prec g' (((X - C r) * f).comp (X + C r)) := by
      simpa [g'] using (prec_comp_X_add_C_iff (f := g) (g := (X - C r) * f) r).2 hgf
    have hgxf' : Prec g' (X * f') := by
      simpa [f', g', mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg,
        comp_assoc, add_assoc, add_left_comm, add_comm] using hgf'
    have hfg' : Prec f' g' := hshift.mpr hgxf'
    exact (prec_comp_X_add_C_iff (f := f) (g := g) r).1 (by lia)

end RealRooted
