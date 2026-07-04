module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic

public section

noncomputable section

namespace Polynomial

/-- Sign of a product `prod (x - r)` over a multiset of reals, provided none of
the factors vanish.  The product is positive exactly when an even number of
terms lie strictly above `x`. -/
private lemma prod_map_sub_pos_iff_even {x : ℝ} :
    ∀ {s : Multiset ℝ}, (∀ r ∈ s, r ≠ x) →
      (0 < (s.map (fun r => x - r)).prod ↔ Even (s.filter (x < ·)).card) := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
      intro _
      simp
  | cons a t ih =>
      intro hmem
      have ha : a ≠ x := hmem a (Multiset.mem_cons_self a t)
      have htmem : ∀ r ∈ t, r ≠ x := fun r hr => hmem r (Multiset.mem_cons_of_mem hr)
      have hPne : (t.map (fun r => x - r)).prod ≠ 0 := by
        intro hz
        rw [Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
        obtain ⟨r, hr, hrz⟩ := hz
        exact htmem r hr (by linarith [sub_eq_zero.mp hrz])
      set P := (t.map (fun r => x - r)).prod
      rw [Multiset.map_cons, Multiset.prod_cons]
      rcases lt_or_gt_of_ne ha with hlt | hgt
      · have hxa : 0 < x - a := by linarith
        have hnot : ¬ x < a := by linarith
        rw [Multiset.filter_cons_of_neg _ hnot, mul_pos_iff_of_pos_left hxa, ih htmem]
      · have hxa : x - a < 0 := by linarith
        rw [Multiset.filter_cons_of_pos _ hgt, Multiset.card_cons, Nat.even_add_one]
        have hprod : (0 < (x - a) * P) ↔ P < 0 := by
          constructor
          · intro h
            nlinarith
          · intro h
            nlinarith
        rw [hprod]
        have hPlt : P < 0 ↔ ¬ 0 < P := by
          constructor
          · intro h
            linarith
          · intro hnotpos
            rcases lt_trichotomy P 0 with hneg | hzero | hpos
            · exact hneg
            · exact absurd hzero hPne
            · exact absurd hpos hnotpos
        rw [hPlt, ih htmem]

/-- Sign of a splitting polynomial at a non-root, counted by roots strictly
above the point. -/
theorem Splits.eval_pos_iff_even_card_roots_gt
    {p : ℝ[X]} (hp : p.Splits) (hlc : 0 < p.leadingCoeff)
    {x : ℝ} (hx : ¬ p.IsRoot x) :
    (0 < p.eval x ↔ Even (p.roots.filter (x < ·)).card) := by
  have hp_ne : p ≠ 0 :=
    leadingCoeff_ne_zero.mp (ne_of_gt hlc)
  have hmem : ∀ r ∈ p.roots, r ≠ x := by
    intro r hr hrx
    exact hx (hrx ▸ ((Polynomial.mem_roots hp_ne).mp hr))
  rw [hp.eval_eq_prod_roots x, mul_pos_iff_of_pos_left hlc]
  exact prod_map_sub_pos_iff_even hmem

/-- Negative sign of a splitting polynomial at a non-root, counted by roots
strictly above the point. -/
theorem Splits.eval_neg_iff_odd_card_roots_gt
    {p : ℝ[X]} (hp : p.Splits) (hlc : 0 < p.leadingCoeff)
    {x : ℝ} (hx : ¬ p.IsRoot x) :
    (p.eval x < 0 ↔ Odd (p.roots.filter (x < ·)).card) := by
  let n := (p.roots.filter (x < ·)).card
  have hpos : 0 < p.eval x ↔ Even n :=
    hp.eval_pos_iff_even_card_roots_gt hlc hx
  have hne : p.eval x ≠ 0 := by
    exact fun h => hx (by simpa [Polynomial.IsRoot.def] using h)
  constructor
  · intro hneg
    rw [← Nat.not_even_iff_odd]
    intro heven
    have hpos_eval : 0 < p.eval x := hpos.mpr heven
    linarith
  · intro hodd
    rw [← Nat.not_even_iff_odd] at hodd
    have hnot_pos : ¬ 0 < p.eval x := by
      intro hpos_eval
      exact hodd (hpos.mp hpos_eval)
    exact lt_of_le_of_ne (le_of_not_gt hnot_pos) hne

end Polynomial
