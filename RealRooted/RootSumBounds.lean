import RealRooted.Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic

/-!
# Root-Sum Bounds

Small support lemmas relating the sum of a finite multiset of reals to its
cardinality.  These are intended for the issue #42 left-escape argument: if a
root multiset has sum below `(card : ℝ) * A`, then some root lies below `A`.
-/

open Polynomial

namespace Multiset

/-- If every element of a finite real multiset is at least `A`, then
`(s.card : ℝ) * A` bounds the sum from below. -/
private theorem card_mul_le_sum_of_forall_le {s : Multiset ℝ} {A : ℝ}
    (h : ∀ r ∈ s, A ≤ r) :
    (s.card : ℝ) * A ≤ s.sum := by
  simpa [nsmul_eq_mul] using Multiset.card_nsmul_le_sum h

/-- If the sum of a finite real multiset is strictly less than `(s.card : ℝ) * A`,
then some element is strictly below `A`. -/
private theorem exists_lt_of_sum_lt_card_mul {s : Multiset ℝ} {A : ℝ}
    (h : s.sum < (s.card : ℝ) * A) :
    ∃ r ∈ s, r < A := by
  by_contra hcon
  have hle : ∀ r ∈ s, A ≤ r := fun r hr =>
    not_lt.mp fun hlt => hcon ⟨r, hr, hlt⟩
  exact not_lt.mpr (card_mul_le_sum_of_forall_le hle) h

end Multiset

namespace Polynomial

/-- Vieta's root-sum formula in division form.  This is a direct consequence of
`Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff`. -/
private theorem Splits.roots_sum_eq_neg_nextCoeff_div_leadingCoeff {p : ℝ[X]}
    (hp : p.Splits) (hlc : p.leadingCoeff ≠ 0) :
    p.roots.sum = -p.nextCoeff / p.leadingCoeff := by
  have hnext : p.nextCoeff = -p.leadingCoeff * p.roots.sum :=
    hp.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  simp_all


/-- In the degree-jump-by-one case, the next coefficient of `f + C μ * g` is
the leading coefficient of `f` plus the scaled next-highest coefficient of
`g`. -/
private theorem nextCoeff_add_C_mul_of_natDegree_succ {f g : ℝ[X]} {μ : ℝ}
    (hμ : μ ≠ 0) (hdeg : g.natDegree = f.natDegree + 1) :
    (f + C μ * g).nextCoeff =
      f.leadingCoeff + μ * g.coeff f.natDegree := by
  have hlt : f.natDegree < g.natDegree := by lia
  have hsum_deg := natDegree_add_C_mul_of_natDegree_lt hμ hlt
  have hsum_pos : 0 < (f + C μ * g).natDegree := by simp [hsum_deg, hdeg]
  rw [nextCoeff_of_natDegree_pos hsum_pos, hsum_deg, hdeg, Nat.add_sub_cancel,
    coeff_add, coeff_C_mul, leadingCoeff]

end Polynomial

namespace RealRooted

/-- The elementary estimate behind the issue #42 left-escape argument.  If
`a` and `b` are positive, then
`-(a + μ * c) / (μ * b)` is below any fixed real bound for all sufficiently
small positive `μ`. -/
private theorem neg_add_mul_div_mul_eventually_lt {a b c B : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ →
      - (a + μ * c) / (μ * b) < B := by
  let δ₁ : ℝ := a / (2 * (|c| + 1))
  let δ₂ : ℝ := a / (4 * (|B| * b + 1))
  have hδ₁ : 0 < δ₁ := by
    dsimp [δ₁]
    positivity
  have hδ₂ : 0 < δ₂ := by
    dsimp [δ₂]
    positivity
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro μ hμ hμδ
  have hμδ₁ : μ < δ₁ := lt_of_lt_of_le hμδ (min_le_left _ _)
  have hμδ₂ : μ < δ₂ := lt_of_lt_of_le hμδ (min_le_right _ _)
  have hden₁ : 0 < 2 * (|c| + 1) := by positivity
  have hden₂ : 0 < 4 * (|B| * b + 1) := by positivity
  have hmul₁ : μ * (2 * (|c| + 1)) < a := by
    dsimp [δ₁] at hμδ₁
    rwa [lt_div_iff₀ hden₁] at hμδ₁
  have hmul₂ : μ * (4 * (|B| * b + 1)) < a := by
    dsimp [δ₂] at hμδ₂
    rwa [lt_div_iff₀ hden₂] at hμδ₂
  have : |μ * c| < a / 2 := by grind
  have : - (a + μ * c) < -a / 2 := by grind
  have : |B| * (μ * b) < a / 4 := by grind
  have hB_lower : -a / 4 < B * (μ * b) := by
    have hBneg : -|B| ≤ B := neg_abs_le B
    have hprod_nonneg : 0 ≤ μ * b := by positivity
    have hle : -(|B| * (μ * b)) ≤ B * (μ * b) := by
      nlinarith [mul_le_mul_of_nonneg_right hBneg hprod_nonneg]
    nlinarith
  have htarget : - (a + μ * c) < B * (μ * b) := by nlinarith
  have hden : 0 < μ * b := by positivity
  rwa [div_lt_iff₀ hden]

/-- For a positive-leading succ-degree pair, the root sum of `f + C μ * g`
eventually lies below `(natDegree : ℝ) * A` as `μ → 0+`. -/
private theorem roots_sum_lt_natDegree_mul_of_succDegree_add_right_small
    {f g : ℝ[X]} (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree + 1) (A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ →
      (f + C μ * g).Splits →
        (f + C μ * g).roots.sum < ((f + C μ * g).natDegree : ℝ) * A := by
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    neg_add_mul_div_mul_eventually_lt (a := f.leadingCoeff) (b := g.leadingCoeff)
      (c := g.coeff f.natDegree) (B := (g.natDegree : ℝ) * A) hf_pos hg_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro μ hμ hμδ hp_split
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ
  have hlt : f.natDegree < g.natDegree := by lia
  have hnat := Polynomial.natDegree_add_C_mul_of_natDegree_lt hμ_ne hlt
  have hlc : (f + C μ * g).leadingCoeff = μ * g.leadingCoeff :=
    Polynomial.leadingCoeff_add_C_mul_of_natDegree_lt hμ_ne hlt
  have hnext : (f + C μ * g).nextCoeff =
      f.leadingCoeff + μ * g.coeff f.natDegree :=
    Polynomial.nextCoeff_add_C_mul_of_natDegree_succ hμ_ne hdeg
  have hlc_ne : (f + C μ * g).leadingCoeff ≠ 0 := by grind
  have hsum := hp_split.roots_sum_eq_neg_nextCoeff_div_leadingCoeff hlc_ne
  simp_all

/-- Polynomial-root form: if the sum of the roots of `p` is strictly less than
`(p.roots.card : ℝ) * A`, then `p` has a root strictly below `A`. -/
private theorem exists_root_lt_of_roots_sum_lt_card_mul {p : ℝ[X]} {A : ℝ}
    (h : p.roots.sum < (p.roots.card : ℝ) * A) :
    ∃ r : ℝ, r ∈ p.roots ∧ r < A :=
  Multiset.exists_lt_of_sum_lt_card_mul h

/-- Split-polynomial form: if `p` splits and the sum of its roots is strictly
less than `(p.natDegree : ℝ) * A`, then `p` has a root strictly below `A`. -/
private theorem exists_root_lt_of_roots_sum_lt_natDegree_mul {p : ℝ[X]} {A : ℝ}
    (hp : p.Splits) (h : p.roots.sum < (p.natDegree : ℝ) * A) :
    ∃ r : ℝ, r ∈ p.roots ∧ r < A :=
  exists_root_lt_of_roots_sum_lt_card_mul <| by
    simpa [hp.natDegree_eq_card_roots.symm] using h

/-- In a positive-leading succ-degree pencil `f + C μ * g`, some root is below
any fixed bound `A` for all sufficiently small positive `μ`, assuming the
pencil member splits. -/
theorem exists_root_lt_of_succDegree_add_right_small
    {f g : ℝ[X]} (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree + 1) (A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ →
      (f + C μ * g).Splits →
        ∃ r : ℝ, r ∈ (f + C μ * g).roots ∧ r < A := by
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    roots_sum_lt_natDegree_mul_of_succDegree_add_right_small hf_pos hg_pos hdeg A
  exact ⟨δ, hδ_pos, fun μ hμ hμδ hp_split =>
    exists_root_lt_of_roots_sum_lt_natDegree_mul hp_split (hδ μ hμ hμδ hp_split)⟩

end RealRooted
