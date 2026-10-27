module

import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Linear
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Wagner-X affine and common-factor transport
-/

public section

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
  simpa [C_leadingCoeff_mul_prod_multiset_X_sub_C
    (Polynomial.splits_iff_card_roots.mp hd_splits), mul_assoc] using hscaled

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
