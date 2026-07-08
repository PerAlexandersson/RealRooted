import RealRooted.SameDegreeQuadraticObstruction

/-!
# Degree-two same-degree root-count bridge

This module discharges the degree-two base case of the same-degree root-count
leaf of the Chudnovsky--Seymour common-interleaver machinery (issue #41), using
the separated-root obstruction from `RealRooted.SameDegreeQuadraticObstruction`.
It is #41-only support unless a future direct #42 pass names this exact
degree-two base case as its remaining gap.

The same-degree root-count leaf asks: for a positive-combination real-rooted
same-degree pair `f, g`, the two threshold root-count functions
`x ↦ (f.roots.filter (· ≤ x)).card` and
`x ↦ (g.roots.filter (· ≤ x)).card` differ by at most one at every threshold
`x`.

Here we prove this in the base case `natDegree = 2`. The core steps are:

* every split real quadratic factors through its root multiset;
* a strictly positive constant scaling preserves splitting, so the
  positive-combination hypothesis on `f, g` descends to the monic pencil
  `(X - a) * (X - b) + t * (X - c) * (X - d)` for every `t > 0`;
* by the obstruction, that pencil splitting for all `t > 0` forbids the roots
  of one quadratic from lying entirely on one side of the roots of the other;
* a finite case analysis on the thresholds yields the root-count bound.
-/

open Polynomial

namespace RealRooted

/-- Multiplying by a nonzero constant preserves and reflects splitting. -/
theorem splits_C_mul_iff {A : ℝ} (hA : A ≠ 0) (p : ℝ[X]) :
    (C A * p).Splits ↔ p.Splits := by
  refine ⟨fun h => ?_, fun h => h.C_mul A⟩
  have h' := h.C_mul A⁻¹
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hA, C_1, one_mul] at h'

/-- A split real quadratic factors through an ordered pair of real roots. -/
theorem exists_roots_pair_of_splits_natDegree_two {f : ℝ[X]}
    (hf : f.Splits) (hdeg : f.natDegree = 2) :
    ∃ a b : ℝ, a ≤ b ∧ f.roots = {a, b} ∧
      f = C f.leadingCoeff * ((X - C a) * (X - C b)) := by
  have hcard : f.roots.card = 2 := (splits_iff_card_roots.1 hf).trans hdeg
  obtain ⟨u, v, huv⟩ := Multiset.card_eq_two.1 hcard
  have hfac : ∀ p q : ℝ, f.roots = {p, q} →
      f = C f.leadingCoeff * ((X - C p) * (X - C q)) := by
    intro p q hpq
    rw [Polynomial.Splits.eq_prod_roots hf, hpq]
    simp [Multiset.map_cons, Multiset.prod_cons]
  have hswap : f.roots = {v, u} := huv.trans (Multiset.cons_swap ..)
  rcases le_total u v with h | h
  · exact ⟨u, v, h, huv, hfac u v huv⟩
  · exact ⟨v, u, h, hswap, hfac v u hswap⟩

/-- Root count of a two-element multiset below a threshold, as a sum of
indicators. -/
theorem card_filter_le_pair (a b x : ℝ) :
    (({a, b} : Multiset ℝ).filter (· ≤ x)).card
      = (if a ≤ x then 1 else 0) + (if b ≤ x then 1 else 0) := by
  split_ifs <;> simp_all +decide [Multiset.filter_singleton]

/-- The positive-combination splitting hypothesis on the two quadratics
`f = A * (X - a) * (X - b)` and `g = B * (X - c) * (X - d)`, with positive
`A` and `B`, descends to the monic pencil
`(X - a) * (X - b) + t * (X - c) * (X - d)` for every `t > 0`. -/
theorem monic_pencil_splits_of_posCombo
    {a b c d A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hpc : ∀ {lam μ : ℝ}, 0 < lam → 0 < μ →
      (C lam * (C A * ((X - C a) * (X - C b)))
        + C μ * (C B * ((X - C c) * (X - C d)))).Splits) :
    ∀ t : ℝ, 0 < t →
      ((X - C a) * (X - C b) + C t * ((X - C c) * (X - C d))).Splits := by
  intro t ht
  have hcombo := hpc (lam := 1) (μ := t * A / B) one_pos (by positivity)
  have key : C (1 : ℝ) * (C A * ((X - C a) * (X - C b)))
        + C (t * A / B) * (C B * ((X - C c) * (X - C d)))
      = C A * ((X - C a) * (X - C b) + C t * ((X - C c) * (X - C d))) := by
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X, one_mul]
    field_simp
  rw [key] at hcombo
  exact (splits_C_mul_iff hA.ne' _).1 hcombo

/-- If the monic pencil `(X - a) * (X - b) + t * (X - c) * (X - d)` splits for
every `t > 0`, with `a ≤ b` and `c ≤ d`, then the roots are not separated:
neither pair lies entirely below the other. -/
theorem not_separated_of_monic_pencil_splits
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hsplit : ∀ t : ℝ, 0 < t →
      ((X - C a) * (X - C b) + C t * ((X - C c) * (X - C d))).Splits) :
    ¬ d < a ∧ ¬ b < c := by
  constructor
  · contrapose! hsplit
    convert exists_pos_combo_not_splits_of_quadratic_roots_separated hab hcd hsplit using 1
  · have h_contra : ∀ t : ℝ, 0 < t →
        ((X - C c) * (X - C d) + C t * ((X - C a) * (X - C b))).Splits := by
      intro t ht
      have key : (X - C c) * (X - C d) + C t * ((X - C a) * (X - C b))
          = C t * ((X - C a) * (X - C b)
              + C (1 / t) * ((X - C c) * (X - C d))) := by
        apply Polynomial.funext
        intro x
        simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
        field_simp
        ring
      rw [key]
      exact (splits_C_mul_iff (show t ≠ 0 by linarith) _).2
        (hsplit (1 / t) (one_div_pos.mpr ht))
    contrapose! h_contra
    convert exists_pos_combo_not_splits_of_quadratic_roots_separated hcd hab h_contra using 1

/-- Finite case analysis: for ordered pairs `a ≤ b`, `c ≤ d` that are not
separated, the indicator root counts below any threshold differ by at most one,
in both directions. -/
theorem count_pair_diff_le_one
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (h1 : ¬ d < a) (h2 : ¬ b < c)
    (x : ℝ) :
    (((if a ≤ x then 1 else 0) + (if b ≤ x then 1 else 0) : ℤ)
        - ((if c ≤ x then 1 else 0) + (if d ≤ x then 1 else 0)) ≤ 1) ∧
    (((if c ≤ x then 1 else 0) + (if d ≤ x then 1 else 0) : ℤ)
        - ((if a ≤ x then 1 else 0) + (if b ≤ x then 1 else 0)) ≤ 1) := by
  grind

/-- Root-order interleaving for a positive-combination real-rooted split
quadratic pair with positive leading coefficients.

Given the roots `{a, b}` (`a ≤ b`) of `f` and `{c, d}` (`c ≤ d`) of `g`, with
`f` and `g` forming a `PosComboRealRooted` pair, neither root pair lies entirely
below the other: `a ≤ d` and `c ≤ b`. -/
theorem posComboRealRooted_quadratic_roots_interleave
    {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits)
    (hfl : 0 < f.leadingCoeff) (hgl : 0 < g.leadingCoeff)
    (hpc : PosComboRealRooted f g)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hfroots : f.roots = {a, b}) (hgroots : g.roots = {c, d}) :
    a ≤ d ∧ c ≤ b := by
  have hffac : f = C f.leadingCoeff * ((X - C a) * (X - C b)) := by
    rw [Polynomial.Splits.eq_prod_roots hf, hfroots]
    simp [Multiset.map_cons, Multiset.prod_cons]
  have hgfac : g = C g.leadingCoeff * ((X - C c) * (X - C d)) := by
    rw [Polynomial.Splits.eq_prod_roots hg, hgroots]
    simp [Multiset.map_cons, Multiset.prod_cons]
  have hpc' : ∀ {lam μ : ℝ}, 0 < lam → 0 < μ →
      (C lam * (C f.leadingCoeff * ((X - C a) * (X - C b)))
        + C μ * (C g.leadingCoeff * ((X - C c) * (X - C d)))).Splits :=
    fun {lam μ} hl hm => hffac ▸ hgfac ▸ (hpc hl hm).2
  have hpencil := monic_pencil_splits_of_posCombo hfl hgl hpc'
  obtain ⟨h1, h2⟩ := not_separated_of_monic_pencil_splits hab hcd hpencil
  exact ⟨not_lt.mp h1, not_lt.mp h2⟩

/-- Degree-two same-degree root-count bound.

For two split real quadratics `f, g` with positive leading coefficients, such
that every strictly positive linear combination `C lam * f + C μ * g` splits,
the two threshold root-count functions differ by at most one at every
threshold. This is the base case `natDegree = 2` of the same-degree root-count
leaf of milestone B1 (issue #41). -/
theorem sameDegree_quadratic_rootCount_le_one
    {f g : ℝ[X]}
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 2)
    (hf : f.Splits) (hg : g.Splits)
    (hfl : 0 < f.leadingCoeff) (hgl : 0 < g.leadingCoeff)
    (hpc : ∀ {lam μ : ℝ}, 0 < lam → 0 < μ →
      (C lam * f + C μ * g).Splits) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  intro x
  obtain ⟨a, b, hab, hfroots, hffac⟩ := exists_roots_pair_of_splits_natDegree_two hf hfdeg
  obtain ⟨c, d, hcd, hgroots, hgfac⟩ := exists_roots_pair_of_splits_natDegree_two hg hgdeg
  have hpc' : ∀ {lam μ : ℝ}, 0 < lam → 0 < μ →
      (C lam * (C f.leadingCoeff * ((X - C a) * (X - C b)))
        + C μ * (C g.leadingCoeff * ((X - C c) * (X - C d)))).Splits :=
    fun {lam μ} hl hm => hffac ▸ hgfac ▸ hpc hl hm
  have hpencil := monic_pencil_splits_of_posCombo hfl hgl hpc'
  obtain ⟨h1, h2⟩ := not_separated_of_monic_pencil_splits hab hcd hpencil
  rw [hfroots, hgroots, card_filter_le_pair, card_filter_le_pair]
  push_cast
  exact count_pair_diff_le_one hab hcd h1 h2 x

end RealRooted
