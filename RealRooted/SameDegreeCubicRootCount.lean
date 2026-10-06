import RealRooted.SameDegreeDerivative
import RealRooted.SameDegreeQuadraticRootCount
import RealRooted.CubicDiscriminant

/-!
# Degree-three same-degree root-count helpers

This module records elementary cubic and quartic root-list helpers for
low-degree root-count routes.
-/

open Polynomial

namespace RealRooted

/-- A split real cubic factors through an ordered triple of real roots. -/
theorem exists_roots_triple_of_splits_natDegree_three {f : ℝ[X]}
    (hf : f.Splits) (hdeg : f.natDegree = 3) :
    ∃ a b c : ℝ, a ≤ b ∧ b ≤ c ∧ f.roots = {a, b, c} ∧
      f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_len : rs.length = 3 := by simp [rs, card_roots_of_splits hf, hdeg]
  obtain ⟨a, b, c, hrs⟩ := List.length_eq_three.mp hrs_len
  have hrs_sorted : rs.Pairwise (· ≤ ·) := by simp [rs]
  have hsorted : ([a, b, c] : List ℝ).Pairwise (· ≤ ·) := by simp_all
  have hab : a ≤ b := by grind
  have hbc : b ≤ c := by simp_all
  have hcoe : f.roots = {a, b, c} := by
    have hse : (↑rs : Multiset ℝ) = f.roots := by simp [rs]
    rw [hrs] at hse
    rw [← hse]
    rfl
  refine ⟨a, b, c, hab, hbc, hcoe, ?_⟩
  rw [Polynomial.Splits.eq_prod_roots hf, hcoe]
  simp [Multiset.map_cons, Multiset.prod_cons, mul_assoc]

/-- Recover the leading-coefficient factorisation of a split cubic from a
specified triple of roots. -/
theorem eq_C_leadingCoeff_mul_prod_three
    {f : ℝ[X]} (hf : f.Splits) (a b c : ℝ) (hr : f.roots = {a, b, c}) :
    f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) := by
  rw [Polynomial.Splits.eq_prod_roots hf, hr]
  simp [Multiset.map_cons, Multiset.prod_cons, mul_assoc]

/-- A split real quartic factors through an ordered quadruple of real roots. -/
theorem exists_roots_quadruple_of_splits_natDegree_four {f : ℝ[X]}
    (hf : f.Splits) (hdeg : f.natDegree = 4) :
    ∃ a b c d : ℝ, a ≤ b ∧ b ≤ c ∧ c ≤ d ∧
      f.roots = {a, b, c, d} ∧
        f = C f.leadingCoeff *
          ((X - C a) * (X - C b) * (X - C c) * (X - C d)) := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_len : rs.length = 4 := by simp [rs, card_roots_of_splits hf, hdeg]
  obtain ⟨a, b, c, d, hrs⟩ := List.length_eq_four.mp hrs_len
  have hrs_sorted : rs.Pairwise (· ≤ ·) := by simp [rs]
  have hsorted : ([a, b, c, d] : List ℝ).Pairwise (· ≤ ·) := by simpa [hrs] using hrs_sorted
  have hab : a ≤ b := by simpa using (List.pairwise_cons.1 hsorted).1 b (by simp)
  have hbc : b ≤ c := by
    have htail := (List.pairwise_cons.1 hsorted).2
    simpa using (List.pairwise_cons.1 htail).1 c (by simp)
  have hcd : c ≤ d := by
    have htail := (List.pairwise_cons.1 hsorted).2
    have htail2 := (List.pairwise_cons.1 htail).2
    simpa using (List.pairwise_cons.1 htail2).1 d (by simp)
  have hcoe : f.roots = {a, b, c, d} := by
    have hse : (↑rs : Multiset ℝ) = f.roots := by simp [rs]
    rw [hrs] at hse
    rw [← hse]
    rfl
  refine ⟨a, b, c, d, hab, hbc, hcd, hcoe, ?_⟩
  rw [Polynomial.Splits.eq_prod_roots hf, hcoe]
  simp [Multiset.map_cons, Multiset.prod_cons, mul_assoc]

/-- Evaluation of the monic cubic root pencil `F + sG`. -/
theorem eval_monicCubicPencil (a b c p q r s x : ℝ) :
    ((X - C a) * (X - C b) * (X - C c)
      + C s * ((X - C p) * (X - C q) * (X - C r))).eval x =
      (x - a) * (x - b) * (x - c) + s * ((x - p) * (x - q) * (x - r)) := by
  simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]

/-- Coefficient form of the monic cubic root pencil. -/
theorem monicCubicPencil_eq (a b c p q r s : ℝ) :
    (X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r)) =
      C (1 + s) * X ^ 3
        + C (-((a + b + c) + s * (p + q + r))) * X ^ 2
        + C ((a * b + b * c + c * a) + s * (p * q + q * r + r * p)) * X
        + C (-(a * b * c + s * (p * q * r))) := by grind

/-- Root count of a three-element multiset below a threshold, as a sum of
indicators. -/
theorem card_filter_le_triple (a b c x : ℝ) :
    (({a, b, c} : Multiset ℝ).filter (· ≤ x)).card =
      (if a ≤ x then 1 else 0) + (if b ≤ x then 1 else 0) +
        (if c ≤ x then 1 else 0) := by
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton]
  split_ifs <;> simp_all [Multiset.card_cons]

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
    hfg.derivative hf hg (by simp_all) (by simp_all)
  have hf'deg : f.derivative.natDegree = 2 := by simp_all
  have hg'deg : g.derivative.natDegree = 2 := by simp_all
  have hf'splits : f.derivative.Splits := by
    rcases derivative_eq_zero_or_ne_zero_and_splits hfs with h | h <;> simp_all
  have hg'splits : g.derivative.Splits := by
    rcases derivative_eq_zero_or_ne_zero_and_splits hgs with h | h <;> simp_all
  have hf'pos : HasPosLeadingCoeff f.derivative :=
    hf.derivative (by simp_all)
  have hg'pos : HasPosLeadingCoeff g.derivative :=
    hg.derivative (by simp_all)
  have hg'le : ∀ r ∈ g.derivative.roots, r ≤ z1 :=
    (derivative_interlaces hgs (by simp_all)).toStrictInterl.roots_le_of_right
      hgle
  have hf'ge : ∀ r ∈ f.derivative.roots, z2 ≤ r :=
    le_roots_derivative_of_le_roots hfs (by simp_all) hfge
  exact not_posComboRealRooted_quadratic_separated
    hf'pos hg'pos hf'deg hg'deg hf'splits hg'splits z1 z2 hz hg'le hf'ge hderpc

/-- Degree-three same-degree root-count bound.

For two split real cubics with positive leading coefficients forming a
positive-combination real-rooted pair, the two lower-threshold root-count
functions differ by at most two at every threshold. -/
theorem sameDegree_cubic_rootCount_le_two
    {f g : ℝ[X]}
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 3)
    (hf : f.Splits) (hg : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hpc : PosComboRealRooted f g) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 2 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 := by
  intro x
  obtain ⟨a, b, c, hab, hbc, hfroots, _⟩ :=
    exists_roots_triple_of_splits_natDegree_three hf hfdeg
  obtain ⟨p, q, r, hpq, hqr, hgroots, _⟩ :=
    exists_roots_triple_of_splits_natDegree_three hg hgdeg
  have hfmem : ∀ s ∈ f.roots, s = a ∨ s = b ∨ s = c := by
    intro s hs
    rw [hfroots] at hs
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs
    grind
  have hgmem : ∀ s ∈ g.roots, s = p ∨ s = q ∨ s = r := by
    intro s hs
    rw [hgroots] at hs
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs
    grind
  have hno1 : ¬ (c ≤ x ∧ x < p) := by
    rintro ⟨hcx, hxp⟩
    exact not_posComboRealRooted_cubic_separated (f := g) (g := f)
      hg_pos hf_pos hg hf hgdeg hfdeg hpc.comm x p hxp
      (fun s hs ↦ by grind)
      (fun s hs ↦ by grind)
  have hno2 : ¬ (r ≤ x ∧ x < a) := by
    rintro ⟨hrx, hxa⟩
    exact not_posComboRealRooted_cubic_separated (f := f) (g := g)
      hf_pos hg_pos hf hg hfdeg hgdeg hpc x a hxa
      (fun s hs ↦ by grind)
      (fun s hs ↦ by grind)
  rw [hfroots, hgroots, card_filter_le_triple, card_filter_le_triple]
  grind

end RealRooted
