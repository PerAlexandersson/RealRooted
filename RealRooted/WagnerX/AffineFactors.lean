import RealRooted.WagnerX.NonnegativeRoots

/-!
# Wagner-X affine and common-factor transport
-/

open Polynomial Filter

noncomputable section

namespace RealRooted

private lemma roots_comp_X_add_C_nonpos_of_le {p : ℝ[X]} {r : ℝ}
    (h : ∀ s ∈ p.roots, s ≤ r) : ∀ s ∈ (p.comp (X + C r)).roots, s ≤ 0 := by
  intro s hs
  rw [roots_comp_X_add_C] at hs
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
  exact sub_nonpos.mpr (h t ht)

private lemma mul_X_sub_C_comp_X_add_C (p : ℝ[X]) (r : ℝ) :
    ((X - C r) * p).comp (X + C r) = X * p.comp (X + C r) := by
  simp only [mul_comp, sub_comp, X_comp, C_comp]
  ring

private lemma coe_orderedInsert_eq_roots_mul_X_sub_C {p : ℝ[X]} (hp : p ≠ 0)
    {ss : List ℝ} (hss : (↑ss : Multiset ℝ) = p.roots) (r : ℝ) :
    (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ((X - C r) * p).roots := by
  have hinsert :
      (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ({r} : Multiset ℝ) + ↑ss := by
    calc
      (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ↑(r :: ss) :=
        Multiset.coe_eq_coe.mpr (List.perm_orderedInsert (r := (· ≤ ·)) r ss)
      _ = ({r} : Multiset ℝ) + ↑ss := by simp
  have hroots : ({r} : Multiset ℝ) + ↑ss = ((X - C r) * p).roots := by
    rw [hss]
    simpa [roots_X_sub_C] using (roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hp)).symm
  exact hinsert.trans hroots

/-- Multiplying both polynomials by the same affine factor preserves strict
interlacing when all original roots lie to its left. -/
theorem StrictInterl.mul_X_sub_C_both_of_roots_le {f g : ℝ[X]}
    (h : StrictInterl f g) (r : ℝ)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r) :
    StrictInterl ((X - C r) * f) ((X - C r) * g) := by
  set f' := f.comp (X + C r)
  set g' := g.comp (X + C r)
  have hfg' : StrictInterl f' g' := by
    simpa [f', g'] using (StrictInterl.comp_X_add_C_iff (f := f) (g := g) r).2 h
  have hX' : StrictInterl (X * f') (X * g') :=
    hfg'.mul_X_both_of_roots_nonpos
      (by simpa [f'] using roots_comp_X_add_C_nonpos_of_le hf_le)
      (by simpa [g'] using roots_comp_X_add_C_nonpos_of_le hg_le)
  exact
    (StrictInterl.comp_X_add_C_iff (f := (X - C r) * f) (g := (X - C r) * g) r).1
      (by simpa [f', g', mul_X_sub_C_comp_X_add_C] using hX')

/-- Multiplying both polynomials by the same affine factor preserves strict
interlacing. -/
theorem StrictInterl.mul_X_sub_C_both {f g : ℝ[X]} (h : StrictInterl f g) (r : ℝ) :
    StrictInterl ((X - C r) * f) ((X - C r) * g) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  refine ⟨isRealRooted_mul (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hf.1 hf.2,
    isRealRooted_mul (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hg.1 hg.2,
    ss.orderedInsert (· ≤ ·) r, rs.orderedInsert (· ≤ ·) r,
    hss.orderedInsert _ _, hrs.orderedInsert _ _, ?_, ?_, ?_⟩
  · exact coe_orderedInsert_eq_roots_mul_X_sub_C hf.1 hss_eq r
  · exact coe_orderedInsert_eq_roots_mul_X_sub_C hg.1 hrs_eq r
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

/-- Cancelling a common affine factor preserves strict interlacing. -/
theorem StrictInterl.of_mul_X_sub_C_both {f g : ℝ[X]} {r : ℝ}
    (h : StrictInterl ((X - C r) * f) ((X - C r) * g)) :
    StrictInterl f g := by
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
      (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ((X - C r) * f).roots :=
    coe_orderedInsert_eq_roots_mul_X_sub_C hf.1 hss_eq r
  have hrs_insert_eq :
      (↑(rs.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ((X - C r) * g).roots :=
    coe_orderedInsert_eq_roots_mul_X_sub_C hg.1 hrs_eq r
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

/-- Multiplication by a common nonzero real-rooted factor preserves strict
interlacing. -/
theorem StrictInterl.mul_common_factor {d f g : ℝ[X]} (h : StrictInterl f g)
    (hd_ne : d ≠ 0) (hd_splits : d.Splits) :
    StrictInterl (d * f) (d * g) := by
  have hprod : StrictInterl (((d.roots.map fun a => X - C a).prod) * f)
      (((d.roots.map fun a => X - C a).prod) * g) := by
    induction d.roots using Multiset.induction_on with
    | empty =>
        simp_all
    | @cons a s ih =>
        simpa [Multiset.map_cons, Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using
          ih.mul_X_sub_C_both a
  have hlc0 : d.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hd_ne
  have hscaled :
      StrictInterl ((C d.leadingCoeff * (d.roots.map fun a => X - C a).prod) * f)
        ((C d.leadingCoeff * (d.roots.map fun a => X - C a).prod) * g) := by
    have hleft := StrictInterl.C_mul_left hprod hlc0
    have hboth := StrictInterl.C_mul_right hleft hlc0
    simpa [mul_assoc, mul_left_comm, mul_comm] using hboth
  simpa [C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_of_splits hd_splits), mul_assoc]
    using hscaled

theorem strictInterl_iff_strictInterl_mul_X_sub_C_of_roots_le {f g : ℝ[X]} (r : ℝ)
    (hf : f.Splits) (hg : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    StrictInterl f g ↔ StrictInterl g ((X - C r) * f) := by
  set f' := f.comp (X + C r)
  set g' := g.comp (X + C r)
  have hf' : f' ≠ 0 ∧ f'.Splits := by
    simpa [f'] using isRealRooted_comp_X_add_C hf_pos.ne_zero hf r
  have hg' : g' ≠ 0 ∧ g'.Splits := by
    simpa [g'] using isRealRooted_comp_X_add_C hg_pos.ne_zero hg r
  have hf'_pos : HasPosLeadingCoeff f' := by simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by simpa [g'] using hg_pos.comp_X_add_C r
  have hf'_nonpos : ∀ s ∈ f'.roots, s ≤ 0 := by
    simpa [f'] using roots_comp_X_add_C_nonpos_of_le hf_le
  have hg'_nonpos : ∀ s ∈ g'.roots, s ≤ 0 := by
    simpa [g'] using roots_comp_X_add_C_nonpos_of_le hg_le
  have hdeg' : f'.natDegree + 1 = g'.natDegree := by simpa [f', g', natDegree_comp] using hdeg
  have hshift :
      StrictInterl f' g' ↔ StrictInterl g' (X * f') :=
    strictInterl_iff_strictInterl_mul_X_of_roots_nonpos
      hf'.2 hg'.2 hf'_pos hg'_pos hf'_nonpos hg'_nonpos hdeg'
  calc
    StrictInterl f g ↔ StrictInterl f' g' :=
      (StrictInterl.comp_X_add_C_iff (f := f) (g := g) r).symm
    _ ↔ StrictInterl g' (X * f') := hshift
    _ ↔ StrictInterl g ((X - C r) * f) := by
      have htranslate :=
        StrictInterl.comp_X_add_C_iff (f := g) (g := (X - C r) * f) r
      rw [mul_X_sub_C_comp_X_add_C] at htranslate
      simpa [f', g'] using htranslate

/-- Same-degree affine shift: if `f ≪ g` have the same degree, positive leading
coefficients, and all roots at most `r`, then `g ≪ (X - r) f`. -/
lemma StrictInterl.mul_X_sub_C_of_sameDegree_of_roots_le {f g : ℝ[X]}
    (h : StrictInterl f g) (r : ℝ)
    (hdeg : f.natDegree = g.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r) :
    StrictInterl g ((X - C r) * f) := by
  set f' := f.comp (X + C r)
  set g' := g.comp (X + C r)
  have hf'_pos : HasPosLeadingCoeff f' := by simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by simpa [g'] using hg_pos.comp_X_add_C r
  have hf'_nonpos : ∀ s ∈ f'.roots, s ≤ 0 := by
    simpa [f'] using roots_comp_X_add_C_nonpos_of_le hf_le
  have hg'_nonpos : ∀ s ∈ g'.roots, s ≤ 0 := by
    simpa [g'] using roots_comp_X_add_C_nonpos_of_le hg_le
  have hdeg' : f'.natDegree = g'.natDegree := by simpa [f', g', natDegree_comp] using hdeg
  have hfg' : StrictInterl f' g' := by
    simpa [f', g'] using (StrictInterl.comp_X_add_C_iff (f := f) (g := g) r).2 h
  have hgxf' : StrictInterl g' (X * f') :=
    strictInterl_sameDegree_to_strictInterl_mul_X_of_roots_nonpos
      hfg' hdeg' hf'_nonpos hg'_nonpos
  exact
    (StrictInterl.comp_X_add_C_iff (f := g) (g := (X - C r) * f) r).1
      (by
        rw [mul_X_sub_C_comp_X_add_C]
        simpa [f', g'] using hgxf')

/-- Converse of `StrictInterl.mul_X_sub_C_of_sameDegree_of_roots_le`. -/
lemma StrictInterl.of_mul_X_sub_C_of_sameDegree_of_roots_le {f g : ℝ[X]} {r : ℝ}
    (h : StrictInterl g ((X - C r) * f))
    (hdeg : f.natDegree = g.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r) :
    StrictInterl f g := by
  set f' := f.comp (X + C r)
  set g' := g.comp (X + C r)
  have hf'_pos : HasPosLeadingCoeff f' := by simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by simpa [g'] using hg_pos.comp_X_add_C r
  have hf'_nonpos : ∀ s ∈ f'.roots, s ≤ 0 := by
    simpa [f'] using roots_comp_X_add_C_nonpos_of_le hf_le
  have hg'_nonpos : ∀ s ∈ g'.roots, s ≤ 0 := by
    simpa [g'] using roots_comp_X_add_C_nonpos_of_le hg_le
  have hdeg' : f'.natDegree = g'.natDegree := by simpa [f', g', natDegree_comp] using hdeg
  have hgxf' : StrictInterl g' (X * f') := by
    have htranslate :=
      (StrictInterl.comp_X_add_C_iff (f := g) (g := (X - C r) * f) r).2 h
    rw [mul_X_sub_C_comp_X_add_C] at htranslate
    simpa [f', g'] using htranslate
  have hfg' : StrictInterl f' g' :=
    strictInterl_of_strictInterl_mul_X_of_sameDegree_of_roots_nonpos hgxf' hdeg' hf'_nonpos
  exact (StrictInterl.comp_X_add_C_iff (f := f) (g := g) r).1 hfg'

end RealRooted
