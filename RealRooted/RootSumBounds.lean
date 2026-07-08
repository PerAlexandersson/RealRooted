import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Real.Basic
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
theorem card_mul_le_sum_of_forall_le {s : Multiset ℝ} {A : ℝ}
    (h : ∀ r ∈ s, A ≤ r) :
    (s.card : ℝ) * A ≤ s.sum := by
  have hns : s.card • A ≤ s.sum := Multiset.card_nsmul_le_sum h
  rwa [nsmul_eq_mul] at hns

/-- If the sum of a finite real multiset is strictly less than `(s.card : ℝ) * A`,
then some element is strictly below `A`. -/
theorem exists_lt_of_sum_lt_card_mul {s : Multiset ℝ} {A : ℝ}
    (h : s.sum < (s.card : ℝ) * A) :
    ∃ r ∈ s, r < A := by
  by_contra hcon
  have hle : ∀ r ∈ s, A ≤ r := by
    intro r hr
    have : ¬ r < A := by
      intro hlt
      exact hcon ⟨r, hr, hlt⟩
    exact not_lt.mp this
  exact not_lt.mpr (card_mul_le_sum_of_forall_le hle) h

end Multiset

namespace Polynomial

/-- Vieta's root-sum formula in division form.  This is a direct consequence of
`Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff`. -/
theorem Splits.roots_sum_eq_neg_nextCoeff_div_leadingCoeff {p : ℝ[X]}
    (hp : p.Splits) (hlc : p.leadingCoeff ≠ 0) :
    p.roots.sum = -p.nextCoeff / p.leadingCoeff := by
  have hnext : p.nextCoeff = -p.leadingCoeff * p.roots.sum :=
    hp.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  field_simp [hlc]
  nlinarith

/-- If `g` has strictly larger degree than `f`, then `f + C μ * g` has the
same degree as `g`, provided `μ ≠ 0`. -/
theorem natDegree_add_C_mul_of_natDegree_lt {f g : ℝ[X]} {μ : ℝ}
    (hμ : μ ≠ 0) (hdeg : f.natDegree < g.natDegree) :
    (f + C μ * g).natDegree = g.natDegree := by
  have hμg_deg : (C μ * g).natDegree = g.natDegree :=
    natDegree_C_mul (p := g) hμ
  have hlt : f.natDegree < (C μ * g).natDegree := by
    rw [hμg_deg]
    exact hdeg
  rw [natDegree_add_eq_right_of_natDegree_lt hlt, hμg_deg]

/-- If `g` has strictly larger degree than `f`, then the leading coefficient of
`f + C μ * g` is the scaled leading coefficient of `g`. -/
theorem leadingCoeff_add_C_mul_of_natDegree_lt {f g : ℝ[X]} {μ : ℝ}
    (hμ : μ ≠ 0) (hdeg : f.natDegree < g.natDegree) :
    (f + C μ * g).leadingCoeff = μ * g.leadingCoeff := by
  have hsum_deg := natDegree_add_C_mul_of_natDegree_lt hμ hdeg
  rw [leadingCoeff, hsum_deg, coeff_add, coeff_C_mul]
  have hf_coeff : f.coeff g.natDegree = 0 := coeff_eq_zero_of_natDegree_lt hdeg
  rw [hf_coeff, zero_add]
  rfl

/-- In the degree-jump-by-one case, the next coefficient of `f + C μ * g` is
the leading coefficient of `f` plus the scaled next-highest coefficient of
`g`. -/
theorem nextCoeff_add_C_mul_of_natDegree_succ {f g : ℝ[X]} {μ : ℝ}
    (hμ : μ ≠ 0) (hdeg : g.natDegree = f.natDegree + 1) :
    (f + C μ * g).nextCoeff =
      f.leadingCoeff + μ * g.coeff f.natDegree := by
  have hlt : f.natDegree < g.natDegree := by lia
  have hsum_deg := natDegree_add_C_mul_of_natDegree_lt hμ hlt
  have hsum_pos : 0 < (f + C μ * g).natDegree := by
    rw [hsum_deg, hdeg]
    exact Nat.succ_pos _
  rw [nextCoeff_of_natDegree_pos hsum_pos, hsum_deg, hdeg, Nat.add_sub_cancel,
    coeff_add, coeff_C_mul, leadingCoeff]

/-- If `g` has strictly larger degree than `f`, then
`C (1 - β) * f + C β * g` has the same degree as `g`, provided `β ≠ 0`. -/
theorem natDegree_closedSegment_of_natDegree_lt {f g : ℝ[X]} {β : ℝ}
    (hβ : β ≠ 0) (hdeg : f.natDegree < g.natDegree) :
    (C (1 - β) * f + C β * g).natDegree = g.natDegree := by
  refine natDegree_add_C_mul_of_natDegree_lt (f := C (1 - β) * f) hβ ?_
  exact (natDegree_C_mul_le (1 - β) f).trans_lt hdeg

/-- If `g` has strictly larger degree than `f`, then the leading coefficient of
`C (1 - β) * f + C β * g` is the scaled leading coefficient of `g`. -/
theorem leadingCoeff_closedSegment_of_natDegree_lt {f g : ℝ[X]} {β : ℝ}
    (hβ : β ≠ 0) (hdeg : f.natDegree < g.natDegree) :
    (C (1 - β) * f + C β * g).leadingCoeff = β * g.leadingCoeff := by
  exact leadingCoeff_add_C_mul_of_natDegree_lt (f := C (1 - β) * f) hβ
    ((natDegree_C_mul_le (1 - β) f).trans_lt hdeg)

/-- In the degree-jump-by-one case, the next coefficient of the closed-segment
member is the scaled leading coefficient of `f` plus the scaled next-highest
coefficient of `g`. -/
theorem nextCoeff_closedSegment_of_natDegree_succ {f g : ℝ[X]} {β : ℝ}
    (hβ : β ≠ 0) (hdeg : g.natDegree = f.natDegree + 1) :
    (C (1 - β) * f + C β * g).nextCoeff =
      (1 - β) * f.leadingCoeff + β * g.coeff f.natDegree := by
  have hlt : f.natDegree < g.natDegree := by
    rw [hdeg]
    exact Nat.lt_succ_self _
  have hsum_deg := natDegree_closedSegment_of_natDegree_lt hβ hlt
  have hsum_pos : 0 < (C (1 - β) * f + C β * g).natDegree := by
    rw [hsum_deg, hdeg]
    exact Nat.succ_pos _
  rw [nextCoeff_of_natDegree_pos hsum_pos, hsum_deg, hdeg, Nat.add_sub_cancel,
    coeff_add, coeff_C_mul, coeff_C_mul, leadingCoeff]

end Polynomial

namespace RealRooted

/-- The elementary estimate behind the issue #42 left-escape argument.  If
`a` and `b` are positive, then
`-(a + μ * c) / (μ * b)` is below any fixed real bound for all sufficiently
small positive `μ`. -/
theorem neg_add_mul_div_mul_eventually_lt {a b c B : ℝ} (ha : 0 < a)
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
  have hc_small : |μ * c| < a / 2 := by
    rw [abs_mul, abs_of_pos hμ]
    have hc_nonneg : 0 ≤ |c| := abs_nonneg c
    nlinarith
  have hnum : - (a + μ * c) < -a / 2 := by
    have hlow : -(a / 2) < μ * c := (abs_lt.mp hc_small).1
    nlinarith
  have hBsmall : |B| * (μ * b) < a / 4 := by
    have hB_nonneg : 0 ≤ |B| := abs_nonneg B
    nlinarith
  have hB_lower : -a / 4 < B * (μ * b) := by
    have hBneg : -|B| ≤ B := neg_abs_le B
    have hprod_nonneg : 0 ≤ μ * b := by positivity
    have hle : -(|B| * (μ * b)) ≤ B * (μ * b) := by
      nlinarith [mul_le_mul_of_nonneg_right hBneg hprod_nonneg]
    nlinarith
  have htarget : - (a + μ * c) < B * (μ * b) := by
    nlinarith
  have hden : 0 < μ * b := by positivity
  rwa [div_lt_iff₀ hden]

/-- For a positive-leading succ-degree pair, the root sum of `f + C μ * g`
eventually lies below `(natDegree : ℝ) * A` as `μ → 0+`. -/
theorem roots_sum_lt_natDegree_mul_of_succDegree_add_right_small
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
  have hlc_ne : (f + C μ * g).leadingCoeff ≠ 0 := by
    rw [hlc]
    exact ne_of_gt (mul_pos hμ hg_pos)
  have hsum := hp_split.roots_sum_eq_neg_nextCoeff_div_leadingCoeff hlc_ne
  calc
    (f + C μ * g).roots.sum =
        -((f + C μ * g).nextCoeff) / (f + C μ * g).leadingCoeff := hsum
    _ = - (f.leadingCoeff + μ * g.coeff f.natDegree) /
        (μ * g.leadingCoeff) := by
      rw [hnext, hlc]
    _ < (g.natDegree : ℝ) * A := hδ μ hμ hμδ
    _ = ((f + C μ * g).natDegree : ℝ) * A := by rw [hnat]

/-- Closed-segment form of
`roots_sum_lt_natDegree_mul_of_succDegree_add_right_small`: for a
positive-leading succ-degree pair, the root sum of
`C (1 - β) * f + C β * g` eventually lies below `(natDegree : ℝ) * A` as
`β → 0+`. -/
theorem roots_sum_lt_natDegree_mul_of_succDegree_closedSegment_left_small
    {f g : ℝ[X]} (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree + 1) (A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ β : ℝ, 0 < β → β < δ →
      (C (1 - β) * f + C β * g).Splits →
        (C (1 - β) * f + C β * g).roots.sum <
          ((C (1 - β) * f + C β * g).natDegree : ℝ) * A := by
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    neg_add_mul_div_mul_eventually_lt (a := f.leadingCoeff) (b := g.leadingCoeff)
      (c := g.coeff f.natDegree - f.leadingCoeff) (B := (g.natDegree : ℝ) * A)
      hf_pos hg_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro β hβ hβδ hp_split
  have hβ_ne : β ≠ 0 := ne_of_gt hβ
  have hlt : f.natDegree < g.natDegree := by
    rw [hdeg]
    exact Nat.lt_succ_self _
  have hnat := Polynomial.natDegree_closedSegment_of_natDegree_lt hβ_ne hlt
  have hlc : (C (1 - β) * f + C β * g).leadingCoeff =
      β * g.leadingCoeff :=
    Polynomial.leadingCoeff_closedSegment_of_natDegree_lt hβ_ne hlt
  have hnext : (C (1 - β) * f + C β * g).nextCoeff =
      (1 - β) * f.leadingCoeff + β * g.coeff f.natDegree :=
    Polynomial.nextCoeff_closedSegment_of_natDegree_succ hβ_ne hdeg
  have hlc_ne : (C (1 - β) * f + C β * g).leadingCoeff ≠ 0 := by
    rw [hlc]
    exact ne_of_gt (mul_pos hβ hg_pos)
  have hsum := hp_split.roots_sum_eq_neg_nextCoeff_div_leadingCoeff hlc_ne
  calc
    (C (1 - β) * f + C β * g).roots.sum =
        -((C (1 - β) * f + C β * g).nextCoeff) /
          (C (1 - β) * f + C β * g).leadingCoeff := hsum
    _ = - (f.leadingCoeff + β * (g.coeff f.natDegree - f.leadingCoeff)) /
        (β * g.leadingCoeff) := by
      rw [hnext, hlc]
      ring
    _ < (g.natDegree : ℝ) * A := hδ β hβ hβδ
    _ = ((C (1 - β) * f + C β * g).natDegree : ℝ) * A := by rw [hnat]

/-- Polynomial-root form: if the sum of the roots of `p` is strictly less than
`(p.roots.card : ℝ) * A`, then `p` has a root strictly below `A`. -/
theorem exists_root_lt_of_roots_sum_lt_card_mul {p : ℝ[X]} {A : ℝ}
    (h : p.roots.sum < (p.roots.card : ℝ) * A) :
    ∃ r : ℝ, r ∈ p.roots ∧ r < A := by
  obtain ⟨r, hr, hlt⟩ := Multiset.exists_lt_of_sum_lt_card_mul h
  exact ⟨r, hr, hlt⟩

/-- Split-polynomial form: if `p` splits and the sum of its roots is strictly
less than `(p.natDegree : ℝ) * A`, then `p` has a root strictly below `A`. -/
theorem exists_root_lt_of_roots_sum_lt_natDegree_mul {p : ℝ[X]} {A : ℝ}
    (hp : p.Splits) (h : p.roots.sum < (p.natDegree : ℝ) * A) :
    ∃ r : ℝ, r ∈ p.roots ∧ r < A := by
  have hcard : p.roots.card = p.natDegree := hp.natDegree_eq_card_roots.symm
  apply exists_root_lt_of_roots_sum_lt_card_mul
  rw [hcard]
  exact h

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
  refine ⟨δ, hδ_pos, ?_⟩
  intro μ hμ hμδ hp_split
  exact exists_root_lt_of_roots_sum_lt_natDegree_mul hp_split (hδ μ hμ hμδ hp_split)

/-- In a positive-leading succ-degree closed segment
`C (1 - β) * f + C β * g`, some root is below any fixed bound `A` for all
sufficiently small positive `β`, assuming the segment member splits. -/
theorem exists_root_lt_of_succDegree_closedSegment_left_small
    {f g : ℝ[X]} (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree + 1) (A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ β : ℝ, 0 < β → β < δ →
      (C (1 - β) * f + C β * g).Splits →
        ∃ r : ℝ, r ∈ (C (1 - β) * f + C β * g).roots ∧ r < A := by
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    roots_sum_lt_natDegree_mul_of_succDegree_closedSegment_left_small hf_pos
      hg_pos hdeg A
  refine ⟨δ, hδ_pos, ?_⟩
  intro β hβ hβδ hp_split
  exact exists_root_lt_of_roots_sum_lt_natDegree_mul hp_split (hδ β hβ hβδ hp_split)

end RealRooted
