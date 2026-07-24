import RealRooted.CoefficientShape
import RealRooted.QuadraticRoot

/-!
# Newton inequalities for splitting real cubics

This file records the two coefficient-wise Newton inequalities for a real
cubic polynomial that splits over `ℝ`.  The coefficient proofs use the existing
Vieta helper for negated roots and the elementary-symmetric Newton inequality
from `NewtonAux`.

These are the exact-degree-three analogues of the degree-two discriminant lemma
`four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_natDegree_two` in
`RealRooted.MultiplierSequence`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The two elementary-symmetric Newton inequalities for three real numbers. -/
theorem newton_symm_three (a b c : ℝ) :
    3 * (a * b + a * c + b * c) ≤ (a + b + c) ^ 2 ∧
      3 * ((a + b + c) * (a * b * c)) ≤ (a * b + a * c + b * c) ^ 2 := by
  constructor
  · nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  · nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c),
      sq_nonneg (a * c - b * c)]

/-- Newton's first coefficient inequality for a real cubic that splits:
`3 * coeff 0 * coeff 2 ≤ coeff 1 ^ 2`. -/
theorem three_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_natDegree_three
    {p : ℝ[X]} (hdeg : p.natDegree = 3) (hs : p.Splits) :
    3 * (p.coeff 0 * p.coeff 2) ≤ p.coeff 1 ^ 2 := by
  set t := p.roots.map Neg.neg with ht
  have htcard : Multiset.card t = 3 := by
    rw [ht, Multiset.card_map, ← hs.natDegree_eq_card_roots, hdeg]
  have hnewton := NewtonAux.newton_esymm_ineq t (n := 3) (m := 2) htcard
    (by norm_num) (by norm_num)
  have hc0 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 0) (by
    rw [hdeg]
    norm_num)
  have hc1 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 1) (by
    rw [hdeg]
    norm_num)
  have hc2 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 2) (by
    rw [hdeg]
    norm_num)
  rw [hdeg] at hc0 hc1 hc2
  rw [← ht] at hc0 hc1 hc2
  norm_num at hnewton hc0 hc1 hc2 ⊢
  rw [hc0, hc1, hc2]
  nlinarith [hnewton, sq_nonneg p.leadingCoeff]

/-- Newton's second coefficient inequality for a real cubic that splits:
`3 * coeff 1 * coeff 3 ≤ coeff 2 ^ 2`. -/
theorem three_mul_coeff_one_mul_coeff_three_le_coeff_two_sq_of_splits_natDegree_three
    {p : ℝ[X]} (hdeg : p.natDegree = 3) (hs : p.Splits) :
    3 * (p.coeff 1 * p.coeff 3) ≤ p.coeff 2 ^ 2 := by
  set t := p.roots.map Neg.neg with ht
  have htcard : Multiset.card t = 3 := by
    rw [ht, Multiset.card_map, ← hs.natDegree_eq_card_roots, hdeg]
  have hnewton := NewtonAux.newton_esymm_ineq t (n := 3) (m := 1) htcard
    (by norm_num) (by norm_num)
  have hc1 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 1) (by
    rw [hdeg]
    norm_num)
  have hc2 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 2) (by
    rw [hdeg]
    norm_num)
  have hc3 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 3) (by
    rw [hdeg])
  rw [hdeg] at hc1 hc2 hc3
  rw [← ht] at hc1 hc2 hc3
  norm_num at hnewton hc1 hc2 hc3 ⊢
  rw [hc1, hc2, hc3]
  nlinarith [hnewton, sq_nonneg p.leadingCoeff]

/-- Newton's adjacent coefficient inequalities for a real polynomial of degree
at most three that is zero or splits. -/
theorem three_mul_coeff_newton_of_natDegree_le_three
    {p : ℝ[X]} (hdeg : p.natDegree ≤ 3) (hs : p = 0 ∨ p.Splits) :
    3 * (p.coeff 0 * p.coeff 2) ≤ p.coeff 1 ^ 2 ∧
      3 * (p.coeff 1 * p.coeff 3) ≤ p.coeff 2 ^ 2 := by
  rcases hs with rfl | hsplits
  · simp
  by_cases h3 : p.natDegree = 3
  · exact
      ⟨three_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_natDegree_three
          h3 hsplits,
        three_mul_coeff_one_mul_coeff_three_le_coeff_two_sq_of_splits_natDegree_three
          h3 hsplits⟩
  · have hle2 : p.natDegree ≤ 2 := Nat.lt_succ_iff.mp (lt_of_le_of_ne hdeg h3)
    have hc3 : p.coeff 3 = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle2 (by norm_num))
    refine ⟨?_, ?_⟩
    · by_cases h2 : p.natDegree = 2
      · have hquad := quadratic_disc_coeff_le_of_splits_natDegree_two h2 hsplits
        nlinarith [hquad, sq_nonneg (p.coeff 1)]
      · have hle1 : p.natDegree ≤ 1 :=
          Nat.lt_succ_iff.mp (lt_of_le_of_ne hle2 h2)
        have hc2 : p.coeff 2 = 0 :=
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle1 (by norm_num))
        rw [hc2]
        nlinarith [sq_nonneg (p.coeff 1)]
    · rw [hc3]
      nlinarith [sq_nonneg (p.coeff 2)]

/-- Jensen-normalized cubic log-concavity from splitting of a polynomial whose
coefficients are the binomially weighted `gᵢ`. -/
theorem jensen_three_logConcave_of_natDegree_le_three
    {p : ℝ[X]} {g0 g1 g2 g3 : ℝ}
    (hdeg : p.natDegree ≤ 3) (hs : p = 0 ∨ p.Splits)
    (h0 : p.coeff 0 = g0) (h1 : p.coeff 1 = 3 * g1)
    (h2 : p.coeff 2 = 3 * g2) (h3 : p.coeff 3 = g3) :
    g0 * g2 ≤ g1 ^ 2 ∧ g1 * g3 ≤ g2 ^ 2 := by
  obtain ⟨hleft, hright⟩ := three_mul_coeff_newton_of_natDegree_le_three hdeg hs
  rw [h0, h1, h2] at hleft
  rw [h1, h2, h3] at hright
  exact ⟨by nlinarith [hleft], by nlinarith [hright]⟩

end RealRooted
