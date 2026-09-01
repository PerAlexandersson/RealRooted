import RealRooted.RootCounting.Finite
import RealRooted.RootCounting.Threshold.Basic

/-!
# Anchoring thresholded root counts

Independent roots below a threshold bound its count; combined with the parity
chain this turns a lower bound into an exact index count.
-/

namespace RealRooted.RootCounting

open Polynomial

/-- Roots above a threshold and distinct roots at or below it fit within the degree. -/
theorem card_add_le {K : Type*} [Field K] [LinearOrder K] {p : K[X]} (hp : p ≠ 0)
    (hcard : Multiset.card p.roots = p.natDegree)
    {s : K} {S : Finset K} (hS : ∀ x ∈ S, p.IsRoot x)
    (hdisj : ∀ x ∈ S, ¬ (-s < x)) :
    Multiset.card (rootsAbove p s) + S.card ≤ p.natDegree := by
  classical
  have hle : rootsAbove p s + S.val ≤ p.roots := by
    refine Multiset.le_iff_count.mpr (fun x => ?_)
    rw [Multiset.count_add, rootsAbove, Multiset.count_filter]
    by_cases hx : -s < x
    · rw [if_pos hx]
      have hxS : x ∉ S.val := by
        intro hmem
        exact hdisj x (by simpa using hmem) hx
      rw [Multiset.count_eq_zero_of_notMem hxS]
      lia
    · rw [if_neg hx]
      by_cases hxS : x ∈ S
      · have h₁ : Multiset.count x S.val = 1 :=
          Multiset.count_eq_one_of_mem S.nodup (by simpa using hxS)
        have h₂ : 1 ≤ Multiset.count x p.roots :=
          Multiset.count_pos.mpr ((mem_roots hp).mpr (hS x hxS))
        lia
      · have h₁ : Multiset.count x S.val = 0 :=
          Multiset.count_eq_zero_of_notMem (by simpa using hxS)
        lia
  have hcard_le := Multiset.card_le_card hle
  rw [Multiset.card_add, hcard] at hcard_le
  simpa using hcard_le

/-- A parity chain and a final cardinality bound determine every preceding count. -/
theorem count_eq_index {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {p : K[X]} (s : ℕ → K) (hmono : ∀ i, s i ≤ s (i + 1))
    (hpar : ∀ i, (-1 : K) ^ (Multiset.card (rootsAbove p (s i))) = (-1 : K) ^ i)
    {J : ℕ} (hJ : Multiset.card (rootsAbove p (s J)) ≤ J) (j : ℕ) (hj : j ≤ J) :
    Multiset.card (rootsAbove p (s j)) = j := by
  refine index_eq (N := fun i => Multiset.card (rootsAbove p (s i)))
    (fun i => ?_) (fun i _ => card_ge_index s hmono hpar i) hJ j hj
  have hne : (-1 : K) ^ (Multiset.card (rootsAbove p (s i)))
      ≠ (-1 : K) ^ (Multiset.card (rootsAbove p (s (i + 1)))) := by
    rw [hpar i, hpar (i + 1)]
    exact neg_one_pow_ne_succ i
  exact card_lt_of_parity_ne (hmono i) hne

end RealRooted.RootCounting
