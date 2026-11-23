module

public import RealRooted.Hermite.Poulain
import RealRooted.SimpleRoots
public import RealRooted.IteratedDerivativeShift
import RealRooted.Hermite.PoulainSymbolInterlacing

/-!
# Multiplicity descent for finite differential symbols

A real-rooted symbol with nonzero constant coefficient preserves degree.
Every multiple output root gains one unit of multiplicity in the input for
each linear symbol factor. Consequently a symbol of degree at least `d - 1`
makes every nonzero real-rooted degree-`d` input simple-real-rooted.

This is the finite-polynomial multiplicity argument underlying Lemma 4.2 of
Craven and Csordas, *Differential operators of infinite order and the
distribution of zeros of entire functions* (1994). The nonzero constant term
excludes annihilation and is explicit here.
-/

public section

open Polynomial

namespace RealRooted.HermitePoulain

/-- A nonzero real symbol root gives an invertible scalar times a derivative shift. -/
theorem applyAsDifferentialOperator_X_sub_C {r : ℝ} (hr : r ≠ 0) (p : ℝ[X]) :
    applyAsDifferentialOperator (X - C r) p = C (-r) * tDeriv r⁻¹ p := by
  rw [sub_eq_add_neg, ← map_neg, applyAsDifferentialOperator_X_add_C, tDeriv]
  rw [mul_sub, ← mul_assoc, ← C_mul]
  simp [hr]
  ring

/-- Products of nonzero real symbol factors preserve splitting and trace
multiple roots backward through every factor. -/
private theorem root_product_operator_data (s : Multiset ℝ)
    (hs : ∀ r ∈ s, r ≠ 0) {p : ℝ[X]} (hp0 : p ≠ 0) (hp : p.Splits) :
    let F := applyAsDifferentialOperator (s.map (fun r => X - C r)).prod p
    F ≠ 0 ∧ F.Splits ∧ ∀ x, 2 ≤ F.rootMultiplicity x →
      p.rootMultiplicity x = F.rootMultiplicity x + s.card := by
  induction s using Multiset.induction_on with
  | empty => simp [hp0, hp]
  | @cons r s ih =>
      have hr : r ≠ 0 := hs r (by simp)
      have htail : ∀ u ∈ s, u ≠ 0 := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
      obtain ⟨hF0, hFs, hFm⟩ := ih htail
      simp only [Multiset.map_cons, Multiset.prod_cons, applyAsDifferentialOperator_mul,
        applyAsDifferentialOperator_X_sub_C hr]
      refine ⟨mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr hr)) (tDeriv_ne_zero hF0),
        (splits_tDeriv_all hFs).C_mul _, ?_⟩
      intro x hm
      rw [rootMultiplicity_C_mul (neg_ne_zero.mpr hr)] at hm ⊢
      have hback := rootMultiplicity_eq_succ_of_tDeriv_ge_two_of_ne (inv_ne_zero hr) hFs hm
      have hlarge : 2 ≤
          (applyAsDifferentialOperator (s.map (fun r => X - C r)).prod p).rootMultiplicity x := by
        lia
      have hprev := hFm x hlarge
      simp only [Multiset.card_cons]
      lia

/-- A multiple root of a differential image gains the symbol degree in
multiplicity when traced back to the splitting input. -/
theorem rootMultiplicity_operator_eq_add_natDegree {q p : ℝ[X]}
    (hq : q.Splits) (hq0 : q.coeff 0 ≠ 0) (hp0 : p ≠ 0) (hp : p.Splits)
    {x : ℝ} (hm : 2 ≤ (applyAsDifferentialOperator q p).rootMultiplicity x) :
    p.rootMultiplicity x = (applyAsDifferentialOperator q p).rootMultiplicity x + q.natDegree := by
  have hqne : q ≠ 0 := by intro hz; simp [hz] at hq0
  have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hqne
  have hroots : ∀ r ∈ q.roots, r ≠ 0 := by
    intro r hr hz
    subst r
    apply hq0
    rw [coeff_zero_eq_eval_zero]
    exact (mem_roots hqne).mp hr
  have heq : applyAsDifferentialOperator q p =
      C q.leadingCoeff *
        applyAsDifferentialOperator (q.roots.map (fun r => X - C r)).prod p := by
    conv_lhs => rw [hq.eq_prod_roots]
    exact applyAsDifferentialOperator_C_mul _ _ _
  rw [heq, rootMultiplicity_C_mul hlc] at hm ⊢
  rw [hq.natDegree_eq_card_roots]
  exact (root_product_operator_data q.roots hroots hp0 hp).2.2 x hm

/-- A real-rooted symbol with nonzero constant term and sufficiently many
roots makes every nonzero split input simple-real-rooted. -/
theorem isSimpleRealRooted_applyAsDifferentialOperator {q p : ℝ[X]}
    (hq : q.Splits) (hq0 : q.coeff 0 ≠ 0) (hp0 : p ≠ 0) (hp : p.Splits)
    (hdegree : p.natDegree - 1 ≤ q.natDegree) :
    IsSimpleRealRooted (applyAsDifferentialOperator q p) := by
  have hqne : q ≠ 0 := by intro hz; simp [hz] at hq0
  have hF0 : applyAsDifferentialOperator q p ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    rw [leadingCoeff_applyAsDifferentialOperator hq0 hp0]
    exact mul_ne_zero hq0 (leadingCoeff_ne_zero.mpr hp0)
  refine ⟨hF0, (applyAsDifferentialOperator_eq_zero_or_splits
    ⟨hqne, hq⟩ ⟨hp0, hp⟩).resolve_left hF0, ?_⟩
  intro x hx
  have hpos := (rootMultiplicity_pos hF0).mpr hx
  by_contra hnot
  have hm : 2 ≤ (applyAsDifferentialOperator q p).rootMultiplicity x := by lia
  have hback := rootMultiplicity_operator_eq_add_natDegree hq hq0 hp0 hp hm
  have hbound := rootMultiplicity_le_natDegree p x
  lia

end RealRooted.HermitePoulain
