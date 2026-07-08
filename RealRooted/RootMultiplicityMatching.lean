import RealRooted.RootCountFinite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Multiplicity-Preserving Root Matching

This file contains the finite matching step for the issue #42
small-positive-parameter route.  It turns local lower counts in disjoint
neighborhoods of the roots of `f` into one global proximity matching
submultiset.
-/

open scoped BigOperators

namespace Multiset

/--
Choose a positive radius, smaller than a prescribed one, whose doubled balls
around distinct values of a finite real multiset are disjoint.
-/
theorem exists_pos_lt_and_two_mul_le_abs_sub_toFinset
    (s : Multiset ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < ρ ∧
      ∀ a ∈ s.toFinset, ∀ b ∈ s.toFinset, a ≠ b → 2 * ε ≤ |a - b| := by
  classical
  suffices hfin : ∀ S : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧ ε < ρ ∧
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 2 * ε ≤ |a - b| by
    exact hfin s.toFinset
  intro S
  induction S using Finset.induction with
  | empty =>
      refine ⟨ρ / 2, by positivity, by linarith, ?_⟩
      simp
  | insert a S ha ih =>
      obtain ⟨ε₁, hε₁_pos, _, hsep₁⟩ := ih
      obtain ⟨η, hη_pos, hη⟩ :=
        exists_pos_le_abs_sub_of_forall_mem_ne S.val a fun r hr hra =>
          ha (by simpa [hra] using hr)
      let ε : ℝ := min ε₁ (min (η / 2) (ρ / 2))
      refine ⟨ε, ?_, ?_, ?_⟩
      · exact lt_min hε₁_pos (lt_min (by positivity) (by positivity))
      · have hερ₂ : ε ≤ ρ / 2 :=
          le_trans (min_le_right ε₁ (min (η / 2) (ρ / 2)))
            (min_le_right (η / 2) (ρ / 2))
        linarith
      · intro b hb c hc hbc
        have hεη : 2 * ε ≤ η := by
          have : ε ≤ η / 2 :=
            le_trans (min_le_right ε₁ (min (η / 2) (ρ / 2)))
              (min_le_left (η / 2) (ρ / 2))
          linarith
        have hεε₁ : 2 * ε ≤ 2 * ε₁ := by
          have : ε ≤ ε₁ := min_le_left ε₁ (min (η / 2) (ρ / 2))
          linarith
        rw [Finset.mem_insert] at hb hc
        rcases hb with rfl | hb <;> rcases hc with rfl | hc
        · contradiction
        · exact le_trans hεη (by simpa [abs_sub_comm] using hη c (by simpa using hc))
        · exact le_trans hεη (hη b (by simpa using hb))
        · exact le_trans hεε₁ (hsep₁ b hb c hc hbc)

/-- `Multiset.Rel` is preserved under finite sums indexed by a `Finset`. -/
theorem rel_sum_of_forall {α β ι : Type*} {r : α → β → Prop} {s : Finset ι}
    {f : ι → Multiset α} {g : ι → Multiset β}
    (h : ∀ i ∈ s, Multiset.Rel r (f i) (g i)) :
    Multiset.Rel r (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact Multiset.Rel.zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/--
Assemble local repeated-root clusters into one global proximity matching.

For each distinct source value `r`, the cluster `cluster r` has exactly
`s.count r` target roots, all within `δ` of `r`; the summed clusters must be a
submultiset of the ambient target multiset `t`.
-/
theorem exists_rel_le_of_clusters
    {s t : Multiset ℝ} {δ : ℝ} (cluster : ℝ → Multiset ℝ)
    (hcard : ∀ r ∈ s.toFinset, (cluster r).card = s.count r)
    (hball : ∀ r ∈ s.toFinset, ∀ q ∈ cluster r, |q - r| < δ)
    (hsum : (∑ r ∈ s.toFinset, cluster r) ≤ t) :
    ∃ u, u ≤ t ∧ Multiset.Rel (fun r q => |q - r| < δ) s u := by
  classical
  refine ⟨∑ r ∈ s.toFinset, cluster r, hsum, ?_⟩
  have hrel : Multiset.Rel (fun r q => |q - r| < δ)
      (∑ r ∈ s.toFinset, s.count r • ({r} : Multiset ℝ))
      (∑ r ∈ s.toFinset, cluster r) := by
    refine rel_sum_of_forall ?_
    intro r hr
    rw [Multiset.nsmul_singleton]
    refine rel_abs_sub_lt_of_repeated_left
      (fun x hx => Multiset.eq_of_mem_replicate hx) (hball r hr) ?_
    rw [Multiset.card_replicate]
    exact (hcard r hr).symm
  rwa [Multiset.toFinset_sum_count_nsmul_eq s] at hrel

/-- A point cannot lie in two `δ`-balls whose centers are `2δ`-separated. -/
theorem not_mem_ball_of_mem_ball_of_separated {a b q δ : ℝ}
    (hsep : 2 * δ ≤ |a - b|) (hqa : |q - a| < δ) :
    ¬ |q - b| < δ := by
  cases abs_cases (a - b) <;>
    cases abs_cases (q - a) <;>
    cases abs_cases (q - b) <;>
    linarith

/--
Under `2δ`-separation of the centers, the `δ`-balls carved from `t` sum to a
submultiset of `t`.
-/
theorem sum_filter_ball_le {s t : Multiset ℝ} {δ : ℝ}
    (hsep : ∀ a ∈ s.toFinset, ∀ b ∈ s.toFinset, a ≠ b → 2 * δ ≤ |a - b|) :
    (∑ a ∈ s.toFinset, t.filter (fun q => |q - a| < δ)) ≤ t := by
  classical
  refine Multiset.le_iff_count.mpr fun q => ?_
  have hcount_sum :
      Multiset.count q (∑ a ∈ s.toFinset, t.filter (fun q => |q - a| < δ)) =
        ∑ a ∈ s.toFinset, if |q - a| < δ then Multiset.count q t else 0 := by
    induction s.toFinset using Finset.induction with
    | empty =>
        simp
    | insert a A ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.count_add, ih]
        simp [Multiset.count_filter]
  rw [hcount_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul]
  have hcard_le : (s.toFinset.filter (fun a => |q - a| < δ)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    exact not_mem_ball_of_mem_ball_of_separated
      (hsep a ha.1 b hb.1 hab) ha.2 hb.2
  calc
    (s.toFinset.filter (fun a => |q - a| < δ)).card * Multiset.count q t
        ≤ 1 * Multiset.count q t :=
      Nat.mul_le_mul_right _ hcard_le
    _ = Multiset.count q t := one_mul _

/--
Global count-to-matching form.

If distinct source values are `2δ`-separated and every `δ`-ball in the target
contains at least the corresponding source multiplicity, then the source
multiset matches a submultiset of the target by `|q - r| < δ`.
-/
theorem exists_rel_le_of_forall_le_count {s t : Multiset ℝ} {δ : ℝ}
    (hsep : ∀ a ∈ s.toFinset, ∀ b ∈ s.toFinset, a ≠ b → 2 * δ ≤ |a - b|)
    (hcount : ∀ a ∈ s.toFinset,
      s.count a ≤ (t.filter (fun q => |q - a| < δ)).card) :
    ∃ u, u ≤ t ∧ Multiset.Rel (fun r q => |q - r| < δ) s u := by
  classical
  let cluster : ℝ → Multiset ℝ := fun a =>
    if h : a ∈ s.toFinset then
      Classical.choose <|
        exists_le_card_eq_of_le_card (t.filter (fun q => |q - a| < δ))
          (hcount a h)
    else 0
  have hcluster : ∀ a (ha : a ∈ s.toFinset),
      cluster a ≤ t.filter (fun q => |q - a| < δ) ∧
        (cluster a).card = s.count a := by
    intro a ha
    have hchoose := Classical.choose_spec <|
      exists_le_card_eq_of_le_card (t.filter (fun q => |q - a| < δ))
        (hcount a ha)
    have ha' : a ∈ s := by simpa using ha
    simpa [cluster, ha, ha'] using hchoose
  refine exists_rel_le_of_clusters cluster (fun a ha => (hcluster a ha).2) ?_ ?_
  · intro a ha q hq
    exact (Multiset.mem_filter.mp (Multiset.mem_of_le (hcluster a ha).1 hq)).2
  · refine le_trans (Finset.sum_le_sum fun a ha => (hcluster a ha).1) ?_
    exact sum_filter_ball_le hsep

/--
Finite local-count bridge for same-cardinality perturbations.

If every source root, counted with multiplicity, has enough target roots in a
small disjoint ball and the two multisets have the same total cardinality, then
the strict-upper count across a separated threshold is unchanged.
-/
theorem card_filter_gt_eq_of_forall_le_count_and_card_eq
    {s t : Multiset ℝ} {x δ : ℝ}
    (hsep_centers : ∀ a ∈ s.toFinset, ∀ b ∈ s.toFinset,
      a ≠ b → 2 * δ ≤ |a - b|)
    (hsep_x : ∀ r ∈ s, δ ≤ |r - x|)
    (hcount : ∀ a ∈ s.toFinset,
      s.count a ≤ (t.filter (fun q => |q - a| < δ)).card)
    (hcard : t.card = s.card) :
    (t.filter (fun q => x < q)).card = (s.filter (fun r => x < r)).card := by
  obtain ⟨u, hu, hRel⟩ :=
    exists_rel_le_of_forall_le_count hsep_centers hcount
  have hu_card : u.card = t.card := by
    rw [hcard, Multiset.card_eq_card_of_rel hRel]
  have hut : u = t := Multiset.eq_of_le_of_card_le hu hu_card.ge
  rw [hut] at hRel
  have hgt : (s.filter (fun r => x < r)).card ≤
      (t.filter (fun q => x < q)).card :=
    card_filter_gt_le_of_rel_abs_sub_lt hsep_x hRel
  have hle : (s.filter (fun r => r ≤ x)).card ≤
      (t.filter (fun q => q ≤ x)).card :=
    card_filter_le_le_of_rel_abs_sub_lt hsep_x hRel
  have hsum : (s.filter (fun r => r ≤ x)).card +
        (s.filter (fun r => x < r)).card =
      (t.filter (fun q => q ≤ x)).card +
        (t.filter (fun q => x < q)).card := by
    rw [card_filter_le_add_card_filter_gt s x,
      card_filter_le_add_card_filter_gt t x, hcard]
  exact Nat.le_antisymm (by lia) hgt

end Multiset
