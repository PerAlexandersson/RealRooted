import RealRooted.SameDegreeDerivative
import RealRooted.SameDegreeQuadraticRootCount

/-!
# Degree-three same-degree root-count helpers

This module records elementary cubic root-list helpers for the degree-three
same-degree Chudnovsky--Seymour route.
-/

open Polynomial

namespace RealRooted

/-- A split real cubic factors through an ordered triple of real roots. -/
theorem exists_roots_triple_of_splits_natDegree_three {f : ℝ[X]}
    (hf : f.Splits) (hdeg : f.natDegree = 3) :
    ∃ a b c : ℝ, a ≤ b ∧ b ≤ c ∧ f.roots = {a, b, c} ∧
      f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_len : rs.length = 3 := by
    simp [rs, card_roots_of_splits hf, hdeg]
  obtain ⟨a, b, c, hrs⟩ := List.length_eq_three.mp hrs_len
  have hrs_sorted : rs.Pairwise (· ≤ ·) := by
    simp [rs]
  have hsorted : ([a, b, c] : List ℝ).Pairwise (· ≤ ·) := by
    simpa [hrs] using hrs_sorted
  have hab : a ≤ b := by
    simpa using (List.pairwise_cons.1 hsorted).1 b (by simp)
  have hbc : b ≤ c := by
    have htail := (List.pairwise_cons.1 hsorted).2
    simpa using (List.pairwise_cons.1 htail).1 c (by simp)
  have hcoe : f.roots = {a, b, c} := by
    have hse : (↑rs : Multiset ℝ) = f.roots := by
      simp [rs]
    rw [hrs] at hse
    rw [← hse]
    rfl
  refine ⟨a, b, c, hab, hbc, hcoe, ?_⟩
  rw [Polynomial.Splits.eq_prod_roots hf, hcoe]
  simp [Multiset.map_cons, Multiset.prod_cons, mul_assoc]

/-- Root count of a three-element multiset below a threshold, as a sum of
indicators. -/
theorem card_filter_le_triple (a b c x : ℝ) :
    (({a, b, c} : Multiset ℝ).filter (· ≤ x)).card =
      (if a ≤ x then 1 else 0) + (if b ≤ x then 1 else 0) +
        (if c ≤ x then 1 else 0) := by
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton]
  split_ifs
  all_goals
    simp_all [Multiset.card_cons]

/-- Two split quadratics with positive leading coefficients whose roots are
separated by a gap cannot form a positive-combination real-rooted pair. -/
theorem not_posComboRealRooted_quadratic_separated
    {q1 q2 : ℝ[X]} (h1 : HasPosLeadingCoeff q1) (h2 : HasPosLeadingCoeff q2)
    (hd1 : q1.natDegree = 2) (hd2 : q2.natDegree = 2)
    (hs1 : q1.Splits) (hs2 : q2.Splits)
    (z1 z2 : ℝ) (hz : z1 < z2)
    (hq2le : ∀ r ∈ q2.roots, r ≤ z1) (hq1ge : ∀ r ∈ q1.roots, z2 ≤ r) :
    ¬ PosComboRealRooted q1 q2 := by
  intro hpc
  obtain ⟨a, b, hab, hq1roots, hq1fac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hs1 hd1
  obtain ⟨c, d, hcd, hq2roots, hq2fac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hs2 hd2
  have ha : z2 ≤ a := hq1ge a (by rw [hq1roots]; simp)
  have hd : d ≤ z1 := hq2le d (by rw [hq2roots]; simp)
  have hsep : d < a := lt_of_le_of_lt hd (lt_of_lt_of_le hz ha)
  rw [hq1fac, hq2fac] at hpc
  exact not_posComboRealRooted_pos_scaled_quadratic_roots_separated
    h1 h2 hab hcd hsep hpc

/-- A positive-combination real-rooted same-degree cubic pair with positive
leading coefficients cannot be fully separated by a strict gap. -/
theorem not_posComboRealRooted_cubic_separated
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hfs : f.Splits) (hgs : g.Splits)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 3)
    (hfg : PosComboRealRooted f g)
    (z1 z2 : ℝ) (hz : z1 < z2)
    (hgle : ∀ r ∈ g.roots, r ≤ z1) (hfge : ∀ r ∈ f.roots, z2 ≤ r) :
    False := by
  have hderpc : PosComboRealRooted f.derivative g.derivative :=
    posComboRealRooted_derivative hf hg (by rw [hgdeg, hfdeg])
      (by rw [hfdeg]; norm_num) hfg
  have hf'deg : f.derivative.natDegree = 2 := by
    rw [f.natDegree_derivative, hfdeg]
  have hg'deg : g.derivative.natDegree = 2 := by
    rw [g.natDegree_derivative, hgdeg]
  have hf'splits : f.derivative.Splits := by
    rcases derivative_eq_zero_or_ne_zero_and_splits hfs with h | h
    · rw [h] at hf'deg
      simp at hf'deg
    · exact h.2
  have hg'splits : g.derivative.Splits := by
    rcases derivative_eq_zero_or_ne_zero_and_splits hgs with h | h
    · rw [h] at hg'deg
      simp at hg'deg
    · exact h.2
  have hf'pos : HasPosLeadingCoeff f.derivative := by
    exact hf.derivative (by rw [hfdeg]; norm_num)
  have hg'pos : HasPosLeadingCoeff g.derivative := by
    exact hg.derivative (by rw [hgdeg]; norm_num)
  have hg'le : ∀ r ∈ g.derivative.roots, r ≤ z1 :=
    roots_le_of_prec_right
      (derivative_interlaces hgs (by rw [hgdeg]; norm_num)).toPrec hgle
  have hf'ge : ∀ r ∈ f.derivative.roots, z2 ≤ r :=
    le_roots_derivative_of_le_roots hfs (by rw [hfdeg]; norm_num) hfge
  exact not_posComboRealRooted_quadratic_separated
    hf'pos hg'pos hf'deg hg'deg hf'splits hg'splits z1 z2 hz hg'le hf'ge hderpc

end RealRooted
