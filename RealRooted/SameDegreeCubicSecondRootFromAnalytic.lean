import RealRooted.SameDegreeCubicRootCount
import RealRooted.SameDegreeCountFromAnalytic
import RealRooted.LiuOppositeSigns

/-!
# The cubic second-root bound from analytic root counts

This downstream module closes the cubic second-root leaf without using the
discriminant-pencil placeholders.  The no-common-root case is the strict-upper
root-count argument of Chudnovsky--Seymour Lemma 3.4.  If the cubics have a
common root, a putative failure forces that root to be the only root on the
opposite side of the gap; cancelling it reduces to the checked quadratic
separation obstruction.
-/

open Polynomial

namespace RealRooted

open LiuOppositeSigns

/-- Cancelling a common linear factor preserves positive-combination
real-rootedness. -/
theorem PosComboRealRooted.deleteRootFactor_commonRoot
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g) {z : ℝ}
    (hfz : f.IsRoot z) (hgz : g.IsRoot z) :
    PosComboRealRooted (deleteRootFactor f z) (deleteRootFactor g z) := by
  intro lam mu hlam hmu
  have hcombo := hfg hlam hmu
  have hfactor :
      C lam * f + C mu * g =
        (X - C z) *
          (C lam * deleteRootFactor f z + C mu * deleteRootFactor g z) := by
    calc
      C lam * f + C mu * g =
          C lam * ((X - C z) * deleteRootFactor f z) +
            C mu * ((X - C z) * deleteRootFactor g z) := by
        rw [factor_deleteRootFactor_of_isRoot hfz,
          factor_deleteRootFactor_of_isRoot hgz]
      _ = (X - C z) *
          (C lam * deleteRootFactor f z + C mu * deleteRootFactor g z) := by
        ring
  constructor
  · intro hzero
    apply hcombo.1
    rw [hfactor, hzero, mul_zero]
  · rw [hfactor] at hcombo
    exact
      (splits_mul_iff_right (X_sub_C_ne_zero z) (.X_sub_C z)).mp hcombo.2

private lemma roots_deleteRootFactor_eq_erase
    {f : ℝ[X]} (hf_ne : f ≠ 0) {z : ℝ} (hz : f.IsRoot z) :
    (deleteRootFactor f z).roots = f.roots.erase z := by
  classical
  rw [roots_eq_singleton_add_roots_deleteRootFactor_of_isRoot hf_ne hz]
  simp

/-- Root count of a three-element multiset strictly above a threshold. -/
private theorem card_filter_lt_triple (a b c x : ℝ) :
    (({a, b, c} : Multiset ℝ).filter (x < ·)).card =
      (if x < a then 1 else 0) + (if x < b then 1 else 0) +
        (if x < c then 1 else 0) := by
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton]
  split_ifs <;> simp_all [Multiset.card_cons]

/-- The cubic second-root inequalities follow from the analytic
Chudnovsky--Seymour root-count theorem. -/
theorem cubicSecondRootBound_from_analytic : CubicSecondRootBoundStatement := by
  classical
  intro f g hf_pos hg_pos hf hg hfdeg hgdeg hpc a b c p q r hab hbc hpq hqr hfroots hgroots
  have hdeg : g.natDegree = f.natDegree := by simp [hfdeg, hgdeg]
  by_cases hno : ∀ z, f.IsRoot z → ¬ g.IsRoot z
  · constructor
    · by_contra haq
      have hqa : q < a := lt_of_not_ge haq
      have har : a ≤ r := by
        by_contra har
        have hra : r < a := lt_of_not_ge har
        exact not_posComboRealRooted_cubic_separated
          hf_pos hg_pos hf hg hfdeg hgdeg hpc r a hra
          (fun z hz ↦ by
            rw [hgroots] at hz
            simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
            grind)
          (fun z hz ↦ by
            rw [hfroots] at hz
            simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
            grind)
      let x : ℝ := (q + a) / 2
      have hqx : q < x := by grind
      have hxa : x < a := by grind
      have hxr : x < r := lt_of_lt_of_le hxa har
      have hxp : ¬ x < p := by grind
      have hxq : ¬ x < q := by grind
      have hxb : x < b := lt_of_lt_of_le hxa hab
      have hxc : x < c := lt_of_lt_of_le hxb hbc
      have hxf : ¬ f.IsRoot x := by
        intro hx
        have hxmem : x ∈ f.roots := (Polynomial.mem_roots hf_pos.ne_zero).mpr hx
        rw [hfroots] at hxmem
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hxmem
        grind
      have hxg : ¬ g.IsRoot x := by
        intro hx
        have hxmem : x ∈ g.roots := (Polynomial.mem_roots hg_pos.ne_zero).mpr hx
        rw [hgroots] at hxmem
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hxmem
        grind
      have hcount :=
        sameDegree_rootCountAbove_bounds_of_posCombo_noCommon
          hf_pos hg_pos hpc hdeg hno x hxf hxg
      rw [hfroots, hgroots, card_filter_lt_triple, card_filter_lt_triple] at hcount
      grind
    · by_contra hbr
      have hrb : r < b := lt_of_not_ge hbr
      by_cases hra : r < a
      · let x : ℝ := (r + a) / 2
        have hrx : r < x := by grind
        have hxa : x < a := by grind
        have hxp : ¬ x < p := by grind
        have hxq : ¬ x < q := by grind
        have hxr : ¬ x < r := by grind
        have hxb : x < b := lt_of_lt_of_le hxa hab
        have hxc : x < c := lt_of_lt_of_le hxb hbc
        have hxf : ¬ f.IsRoot x := by
          intro hx
          have hxmem : x ∈ f.roots := (Polynomial.mem_roots hf_pos.ne_zero).mpr hx
          rw [hfroots] at hxmem
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hxmem
          grind
        have hxg : ¬ g.IsRoot x := by
          intro hx
          have hxmem : x ∈ g.roots := (Polynomial.mem_roots hg_pos.ne_zero).mpr hx
          rw [hgroots] at hxmem
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hxmem
          grind
        have hcount :=
          sameDegree_rootCountAbove_bounds_of_posCombo_noCommon
            hf_pos hg_pos hpc hdeg hno x hxf hxg
        rw [hfroots, hgroots, card_filter_lt_triple, card_filter_lt_triple] at hcount
        grind
      · have har : a ≤ r := le_of_not_gt hra
        let x : ℝ := (r + b) / 2
        have hrx : r < x := by grind
        have hxb : x < b := by grind
        have hxa : ¬ x < a := by grind
        have hxp : ¬ x < p := by grind
        have hxq : ¬ x < q := by grind
        have hxr : ¬ x < r := by grind
        have hxc : x < c := lt_of_lt_of_le hxb hbc
        have hxf : ¬ f.IsRoot x := by
          intro hx
          have hxmem : x ∈ f.roots := (Polynomial.mem_roots hf_pos.ne_zero).mpr hx
          rw [hfroots] at hxmem
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hxmem
          grind
        have hxg : ¬ g.IsRoot x := by
          intro hx
          have hxmem : x ∈ g.roots := (Polynomial.mem_roots hg_pos.ne_zero).mpr hx
          rw [hgroots] at hxmem
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hxmem
          grind
        have hcount :=
          sameDegree_rootCountAbove_bounds_of_posCombo_noCommon
            hf_pos hg_pos hpc hdeg hno x hxf hxg
        rw [hfroots, hgroots, card_filter_lt_triple, card_filter_lt_triple] at hcount
        grind
  · push Not at hno
    obtain ⟨z, hfz, hgz⟩ := hno
    have hz_f_mem : z = a ∨ z = b ∨ z = c := by
      have hzmem : z ∈ f.roots := (Polynomial.mem_roots hf_pos.ne_zero).mpr hfz
      rw [hfroots] at hzmem
      simpa only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] using hzmem
    have hz_g_mem : z = p ∨ z = q ∨ z = r := by
      have hzmem : z ∈ g.roots := (Polynomial.mem_roots hg_pos.ne_zero).mpr hgz
      rw [hgroots] at hzmem
      simpa only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] using hzmem
    have hfq_pos : HasPosLeadingCoeff (deleteRootFactor f z) := by
      simpa [HasPosLeadingCoeff,
        leadingCoeff_deleteRootFactor_of_isRoot hf_pos.ne_zero hfz] using hf_pos
    have hgq_pos : HasPosLeadingCoeff (deleteRootFactor g z) := by
      simpa [HasPosLeadingCoeff,
        leadingCoeff_deleteRootFactor_of_isRoot hg_pos.ne_zero hgz] using hg_pos
    have hfq_split : (deleteRootFactor f z).Splits :=
      deleteRootFactor_splits_of_isRoot hf hfz
    have hgq_split : (deleteRootFactor g z).Splits :=
      deleteRootFactor_splits_of_isRoot hg hgz
    have hfq_deg : (deleteRootFactor f z).natDegree = 2 := by rw [natDegree_deleteRootFactor, hfdeg]
    have hgq_deg : (deleteRootFactor g z).natDegree = 2 := by rw [natDegree_deleteRootFactor, hgdeg]
    have hpcq :
        PosComboRealRooted (deleteRootFactor f z) (deleteRootFactor g z) :=
      hpc.deleteRootFactor_commonRoot hfz hgz
    constructor
    · by_contra haq
      have hqa : q < a := lt_of_not_ge haq
      have hz_eq_r : z = r := by grind
      have hgq_roots : (deleteRootFactor g z).roots = {p, q} := by
        rw [roots_deleteRootFactor_eq_erase hg_pos.ne_zero hgz, hgroots, hz_eq_r]
        simp [show p ≠ r by grind, show q ≠ r by grind]
      have hfq_ge : ∀ s ∈ (deleteRootFactor f z).roots, a ≤ s := by
        intro s hs
        rw [roots_deleteRootFactor_eq_erase hf_pos.ne_zero hfz] at hs
        have hs_mem := Multiset.mem_of_mem_erase hs
        rw [hfroots] at hs_mem
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs_mem
        rcases hs_mem with rfl | rfl | rfl
        · exact le_rfl
        · exact hab
        · exact hab.trans hbc
      have hgq_le : ∀ s ∈ (deleteRootFactor g z).roots, s ≤ q := by
        intro s hs
        rw [hgq_roots] at hs
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · exact hpq
        · exact le_rfl
      exact not_posComboRealRooted_quadratic_separated
        hfq_pos hgq_pos hfq_deg hgq_deg hfq_split hgq_split q a hqa
        hgq_le hfq_ge hpcq
    · by_contra hbr
      have hrb : r < b := lt_of_not_ge hbr
      have hz_le_r : z ≤ r := by
        rcases hz_g_mem with rfl | rfl | rfl
        · exact hpq.trans hqr
        · exact hqr
        · exact le_rfl
      have hz_eq_a : z = a := by
        rcases hz_f_mem with hza | hzb | hzc
        · exact hza
        · exfalso
          exact hbr (by simpa [hzb] using hz_le_r)
        · exfalso
          have hc_le_r : c ≤ r := by simpa [hzc] using hz_le_r
          exact hbr (hbc.trans hc_le_r)
      have hfq_roots : (deleteRootFactor f z).roots = {b, c} := by
        rw [roots_deleteRootFactor_eq_erase hf_pos.ne_zero hfz, hfroots, hz_eq_a]
        simp
      have hfq_ge : ∀ s ∈ (deleteRootFactor f z).roots, b ≤ s := by
        intro s hs
        rw [hfq_roots] at hs
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · exact le_rfl
        · exact hbc
      have hgq_le : ∀ s ∈ (deleteRootFactor g z).roots, s ≤ r := by
        intro s hs
        rw [roots_deleteRootFactor_eq_erase hg_pos.ne_zero hgz] at hs
        have hs_mem := Multiset.mem_of_mem_erase hs
        rw [hgroots] at hs_mem
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs_mem
        rcases hs_mem with rfl | rfl | rfl
        · exact hpq.trans hqr
        · exact hqr
        · exact le_rfl
      exact not_posComboRealRooted_quadratic_separated
        hfq_pos hgq_pos hfq_deg hgq_deg hfq_split hgq_split r b hrb
        hgq_le hfq_ge hpcq

end RealRooted
