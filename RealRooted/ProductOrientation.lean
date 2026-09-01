import RealRooted.ObreschkoffConverse
import RealRooted.WagnerRightSum

/-!
# Selecting a same-degree proper-position orientation by an endpoint product

Obreschkoff's converse turns a real-rooted full pencil into the alternative
`Prec f g ∨ Prec g f`.  For polynomials with nonnegative coefficients, all
roots are nonpositive, so the product of the negated roots selects the
orientation.  Via
`p.eval 0 = p.leadingCoeff * ∏ r ∈ p.roots, (-r)`, this gives the
coefficient-level strict inequality used below.

Positive-combination compatibility is deliberately not enough here.  For
example, the monic quadratics with roots `[-4,-1]` and `[-3,-2]` have
real-rooted nonnegative combinations, but neither polynomial is in proper
position with the other.

This sequence-independent orientation criterion was first used in
`ProofsOeis.ProductOrientation`.
-/

open Polynomial

noncomputable section

namespace RealRooted

private lemma prod_le_prod_of_forall₂_of_nonneg :
    ∀ {xs ys : List ℝ},
      List.Forall₂ (fun x y : ℝ => x ≤ y) xs ys →
      (∀ x ∈ xs, 0 ≤ x) → (∀ y ∈ ys, 0 ≤ y) →
      xs.prod ≤ ys.prod
  | [], [], _, _, _ => by simp
  | x :: xs, y :: ys, hxy, hx, hy => by
      simp only [List.forall₂_cons] at hxy
      simp only [List.prod_cons]
      apply mul_le_mul hxy.1
        (prod_le_prod_of_forall₂_of_nonneg hxy.2 (by simp_all) (by simp_all))
        (List.prod_nonneg (by simp_all)) (hy y (by simp))

private lemma forall₂_map_zero_sub_rev :
    ∀ {xs ys : List ℝ},
      List.Forall₂ (fun x y : ℝ => x ≤ y) xs ys →
      List.Forall₂ (fun x y : ℝ => x ≤ y)
        (ys.map (0 - ·)) (xs.map (0 - ·))
  | [], [], _ => by simp
  | x :: xs, y :: ys, h => by
      simp only [List.forall₂_cons] at h
      exact List.Forall₂.cons (by simp_all)
        (forall₂_map_zero_sub_rev h.2)

/-- For same-degree nonnegative-coefficient polynomials, proper position
orders the normalized values at zero. -/
lemma eval_cross_le_of_prec_sameDegree_of_nonneg
    {f g : ℝ[X]}
    (hprec : Prec f g) (hdeg : f.natDegree = g.natDegree)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    g.eval 0 * f.leadingCoeff ≤ f.eval 0 * g.leadingCoeff := by
  rcases hprec with ⟨hf, hg, ss, rs, _hss_sorted, _hrs_sorted,
    hss_eq, hrs_eq, hshape⟩
  have hlen_ss : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hlen_rs : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  have halt : ListAlternates ss rs := by simp_all
  have hpair : List.Forall₂ (fun x y : ℝ ↦ x ≤ y) ss rs :=
    listAlternates_forall₂_le halt
  have hpair_neg :
      List.Forall₂ (fun x y : ℝ => x ≤ y)
        (rs.map (0 - ·)) (ss.map (0 - ·)) :=
    forall₂_map_zero_sub_rev hpair
  have hrs_nonneg : ∀ x ∈ rs.map (0 - ·), 0 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hrroot : r ∈ g.roots := by
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr hr
    have := roots_nonpos_of_hasNonnegCoeffs hgnn r hrroot
    linarith
  have hss_nonneg : ∀ x ∈ ss.map (0 - ·), 0 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hrroot : r ∈ f.roots := by
      rw [← hss_eq]
      exact Multiset.mem_coe.mpr hr
    have := roots_nonpos_of_hasNonnegCoeffs hfnn r hrroot
    linarith
  have hprod : (rs.map (0 - ·)).prod ≤ (ss.map (0 - ·)).prod :=
    prod_le_prod_of_forall₂_of_nonneg hpair_neg hrs_nonneg hss_nonneg
  have hflc : 0 < f.leadingCoeff := hfnn.pos_leadingCoeff hf.1
  have hglc : 0 < g.leadingCoeff := hgnn.pos_leadingCoeff hg.1
  rw [eval_eq_leadingCoeff_mul_prod_sub hf.2 0,
    eval_eq_leadingCoeff_mul_prod_sub hg.2 0, ← hss_eq, ← hrs_eq]
  simp only [Multiset.map_coe, Multiset.prod_coe]
  nlinarith [mul_le_mul_of_nonneg_left hprod (le_of_lt (mul_pos hflc hglc))]

/-- A strict normalized endpoint comparison selects the forward branch of
Obreschkoff's same-degree orientation alternative. -/
theorem prec_of_allComboRealRooted_of_sameDegree_of_nonneg_of_eval_cross_gt
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree = g.natDegree)
    (hcross : g.eval 0 * f.leadingCoeff <
      f.eval 0 * g.leadingCoeff) :
    Prec f g := by
  rcases prec_of_allComboRealRooted hf0 (hall.isRealRooted_left hf0).2
      hg0 (hall.isRealRooted_right hg0).2 hall (Or.inr hdeg) with hfg | hgf
  · grind
  · have hle := eval_cross_le_of_prec_sameDegree_of_nonneg
      hgf hdeg.symm hgnn hfnn
    linarith

end RealRooted
