import RealRooted.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Multiset.Sort
import RealRooted.Derivative.Algebra

open Polynomial Set

noncomputable section

namespace RealRooted

/-! ## Rolle's theorem for polynomials -/

theorem exists_root_derivative_between {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) :
    ∃ c, a < c ∧ c < b ∧ p.derivative.IsRoot c := by
  have hcont : ContinuousOn (fun x => p.eval x) (Icc a b) :=
    p.continuous.continuousOn
  have hfab : p.eval a = p.eval b := by simp_all
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x :=
    fun x _ => p.hasDerivAt x
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_zero hab hcont hfab hderiv
  exact ⟨c, hc_mem.1, hc_mem.2, hc_eq⟩

theorem isRoot_derivative_of_rootMultiplicity_ge_two {p : ℝ[X]} {r : ℝ}
    (hm : 2 ≤ p.rootMultiplicity r) :
    p.derivative.IsRoot r := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hm
  have hdvd : (X - C r) ^ 2 ∣ p := (le_rootMultiplicity_iff hp0).mp hm
  have hdvd' : (X - C r) ^ (2 - 1) ∣ p.derivative :=
    pow_sub_one_dvd_derivative_of_pow_dvd hdvd
  simp only [Nat.reduceSubDiff, pow_one] at hdvd'
  exact dvd_iff_isRoot.mp hdvd'

/-- Extract two ordered distinct elements from a nodup multiset with cardinality
at least two. -/
private lemma exists_pair_mem_lt_of_one_lt_card {m : Multiset ℝ}
    (hcard : 1 < m.card) (hnodup : m.Nodup) :
    ∃ r₁ r₂, r₁ ∈ m ∧ r₂ ∈ m ∧ r₁ < r₂ := by
  have hm_pos : 0 < m.card := Nat.zero_lt_of_lt hcard
  obtain ⟨r₁, hr₁⟩ := Multiset.card_pos_iff_exists_mem.mp hm_pos
  have hm_erase_pos : 0 < (m.erase r₁).card := by
    simpa [Multiset.card_erase_of_mem hr₁] using Nat.sub_pos_of_lt hcard
  obtain ⟨r₂, hr₂erase⟩ := Multiset.card_pos_iff_exists_mem.mp hm_erase_pos
  have hr₂ : r₂ ∈ m := Multiset.mem_of_mem_erase hr₂erase
  have hr₁r₂ : r₁ ≠ r₂ := by
    intro h
    subst h
    exact hnodup.notMem_erase hr₂erase
  cases lt_or_gt_of_ne hr₁r₂ with
  | inl hlt => exact ⟨r₁, r₂, hr₁, hr₂, hlt⟩
  | inr hgt => exact ⟨r₂, r₁, hr₂, hr₁, hgt⟩

private lemma exists_isRoot_derivative_of_one_lt_card_roots_filter
    {p : ℝ[X]} {q : ℝ → Prop} [DecidablePred q]
    (hcard : 1 < (p.roots.filter q).card)
    (hle : (∀ x, q x → ¬ p.derivative.IsRoot x) →
      (p.roots.filter q).card ≤ 1) :
    ∃ x, q x ∧ p.derivative.IsRoot x := by
  by_contra h
  exact (Nat.not_le.mpr hcard) (hle fun x hxq hroot => h ⟨x, hxq, hroot⟩)

/-! ## Root-count transfer from `p` to its derivative

Applied, statement-shaped lemmas: whenever an interval carries more than one
root of `p` with multiplicity, Rolle's theorem forces at least one root of
`p.derivative` in the same interval.
-/

private lemma one_le_card_roots_filter_derivative_of_exists
    {p : ℝ[X]} {q : ℝ → Prop} [DecidablePred q]
    (hcard : 1 < (p.roots.filter q).card)
    (hexists : ∃ x, q x ∧ p.derivative.IsRoot x) :
    1 ≤ (p.derivative.roots.filter q).card := by
  have hle : (p.roots.filter q).card ≤ p.natDegree :=
    le_trans (Multiset.card_le_card (Multiset.filter_le _ p.roots))
      (Polynomial.card_roots' p)
  have hderiv_ne : p.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  obtain ⟨x, hxq, hroot⟩ := hexists
  have hx_mem : x ∈ p.derivative.roots.filter q :=
    Multiset.mem_filter.mpr ⟨Polynomial.mem_roots'.mpr ⟨hderiv_ne, hroot⟩, hxq⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx_mem⟩

end RealRooted
