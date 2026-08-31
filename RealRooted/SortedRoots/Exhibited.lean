import RealRooted.Basic
import RealRooted.RootCounting.Finite
import RealRooted.SortedRoots

/-!
# Exhibited sorted roots

Generic bridges from an explicitly indexed increasing root family to the
sorted negative-root-magnitude sequence.
-/

namespace RealRooted.SortedRoots

open Polynomial

noncomputable section

/-- An increasing exhibited family of `n` roots saturates the root-cardinality
bound. -/
theorem card_roots_eq_natDegree_of_exhibited {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree = n) (hp : p ≠ 0) {x : ℕ → ℝ}
    (hmono : ∀ i j : ℕ, i < j → j < n → x i < x j)
    (hroot : ∀ i, i < n → p.IsRoot (-(x i))) :
    Multiset.card p.roots = p.natDegree := by
  classical
  set S : Finset ℝ := (Finset.range n).image fun i => -(x i) with hS
  have hinj : Set.InjOn (fun i => -(x i)) (Finset.range n) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    simp only [neg_inj] at hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hij (ne_of_lt (hmono i j h hj))
    · exact absurd hij.symm (ne_of_lt (hmono j i h hi))
  have hcard : S.card = n := by
    rw [hS, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : S ⊆ p.roots.toFinset := by
    intro y hy
    rw [hS, Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Finset.mem_range] at hi
    exact Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (hroot i hi))
  have h1 : n ≤ p.roots.toFinset.card := hcard ▸ Finset.card_le_card hsub
  have h2 : p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
  have h3 : Multiset.card p.roots ≤ p.natDegree := Polynomial.card_roots' p
  lia

/-- The sorted negative-root magnitudes agree with an explicitly exhibited
strictly increasing family of all roots. -/
theorem splits_and_rootSeq_eq_of_exhibited {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree = n) (hp : p ≠ 0) {x : ℕ → ℝ}
    (hmono : ∀ i j : ℕ, i < j → j < n → x i < x j)
    (hroot : ∀ i, i < n → p.IsRoot (-(x i))) :
    p.Splits ∧ ∀ i, i < n → rootSeq p i = x i := by
  classical
  have hcard := card_roots_eq_natDegree_of_exhibited hdeg hp hmono hroot
  have hsp : p.Splits := splits_of_card_roots (by lia)
  refine ⟨hsp, ?_⟩
  have hlen : (rootMags p).length = n := by
    rw [rootMags_length, hcard, hdeg]
  have hnd : p.roots.Nodup := by
    refine RootCounting.roots_nodup_of_card_roots hcard
      (s := (Finset.range n).image fun i => -(x i)) ?_ hp ?_
    · intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      rw [Finset.mem_range] at hi
      exact hroot i hi
    · rw [Finset.card_image_of_injOn, Finset.card_range, hdeg]
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      simp only [neg_inj] at hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact absurd hij (ne_of_lt (hmono i j h hj))
      · exact absurd hij.symm (ne_of_lt (hmono j i h hi))
  set T : Finset ℝ := (rootMags p).toFinset with hT
  have hTcard : T.card = n := by
    rw [hT, List.toFinset_card_of_nodup (rootMags_nodup p hnd), hlen]
  have hxmem : ∀ i : Fin n, x (i : ℕ) ∈ T := by
    intro i
    rw [hT, List.mem_toFinset, rootMags, Multiset.mem_sort, Multiset.mem_map]
    exact ⟨-(x (i : ℕ)), (mem_roots hp).mpr (hroot i i.isLt), by ring⟩
  have hrmem : ∀ i : Fin n, rootSeq p (i : ℕ) ∈ T := by
    intro i
    rw [hT, List.mem_toFinset]
    have hrootSeq := rootSeq_eq_getElem p (by rw [hlen]; exact i.isLt)
    rw [hrootSeq]
    exact List.getElem_mem _
  have hxmono : StrictMono fun i : Fin n => x (i : ℕ) := by
    intro i j hij
    exact hmono i j hij j.isLt
  have hrmono : StrictMono fun i : Fin n => rootSeq p (i : ℕ) := by
    intro i j hij
    exact rootSeq_lt p hnd hij (by rw [hlen]; exact j.isLt)
  have h1 := Finset.orderEmbOfFin_unique (s := T) hTcard hxmem hxmono
  have h2 := Finset.orderEmbOfFin_unique (s := T) hTcard hrmem hrmono
  intro i hi
  have h := congrFun (h2.trans h1.symm) ⟨i, hi⟩
  simpa using h

end
end RealRooted.SortedRoots
