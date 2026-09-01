import RealRooted.Mathlib.Data.List.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.List.GetD
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Real.Basic

/-!
# Sorted negative-root magnitudes

A finite increasing sequence obtained by sorting the negations of a real
polynomial's roots.
-/

namespace RealRooted.SortedRoots

open Polynomial

noncomputable section

def rootMags (p : ℝ[X]) : List ℝ := (p.roots.map (fun r => -r)).sort (· ≤ ·)

/-- The `j`-th smallest root magnitude (junk value `0` past the end). -/
def rootSeq (p : ℝ[X]) (j : ℕ) : ℝ := (rootMags p).getD j 0

theorem rootMags_length (p : ℝ[X]) :
    (rootMags p).length = Multiset.card p.roots := by
  rw [rootMags, Multiset.length_sort, Multiset.card_map]

theorem mem_rootMags (p : ℝ[X]) {x : ℝ} : x ∈ rootMags p ↔ -x ∈ p.roots := by
  rw [rootMags, Multiset.mem_sort, Multiset.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    simpa using hr
  · intro h
    exact ⟨-x, h, by ring⟩

/-- Every listed magnitude is positive, when the roots are negative. -/
theorem rootMags_pos (p : ℝ[X]) (hneg : ∀ r ∈ p.roots, r < 0) {x : ℝ}
    (hx : x ∈ rootMags p) : 0 < x := by
  have hmem := (mem_rootMags p).mp hx
  have := hneg _ hmem
  linarith

theorem rootMags_sortedLE (p : ℝ[X]) : (rootMags p).SortedLE := by
  exact List.Pairwise.sortedLE (Multiset.pairwise_sort (p.roots.map (fun r => -r)) (· ≤ ·))

theorem rootMags_nodup (p : ℝ[X]) (hnd : p.roots.Nodup) : (rootMags p).Nodup := by
  have hmap : (p.roots.map (fun r : ℝ => -r)).Nodup :=
    hnd.map (fun a b h => by linarith [h])
  have hcoe : ((rootMags p : List ℝ) : Multiset ℝ) = p.roots.map (fun r => -r) :=
    Multiset.sort_eq _ _
  rw [← Multiset.coe_nodup, hcoe]
  exact hmap

theorem rootMags_sortedLT (p : ℝ[X]) (hnd : p.roots.Nodup) : (rootMags p).SortedLT :=
  (rootMags_sortedLE p).sortedLT_of_nodup (rootMags_nodup p hnd)

/-- Reading off an in-range index. -/
theorem rootSeq_eq_getElem (p : ℝ[X]) {j : ℕ} (hj : j < (rootMags p).length) :
    rootSeq p j = (rootMags p)[j] := by
  rw [rootSeq, List.getD_eq_getElem _ _ hj]

/-- **The sequence is positive on its range.** -/
theorem rootSeq_pos (p : ℝ[X]) (hneg : ∀ r ∈ p.roots, r < 0) {j : ℕ}
    (hj : j < (rootMags p).length) : 0 < rootSeq p j := by
  rw [rootSeq_eq_getElem p hj]
  exact rootMags_pos p hneg (List.getElem_mem hj)

/-- **The sequence is strictly increasing on its range.** -/
theorem rootSeq_lt (p : ℝ[X]) (hnd : p.roots.Nodup) {i j : ℕ}
    (hij : i < j) (hj : j < (rootMags p).length) :
    rootSeq p i < rootSeq p j := by
  have hi : i < (rootMags p).length := lt_trans hij hj
  rw [rootSeq_eq_getElem p hi, rootSeq_eq_getElem p hj]
  have hmono := List.sortedLT_iff_strictMono_get.mp (rootMags_sortedLT p hnd)
  exact hmono (show (⟨i, hi⟩ : Fin _) < ⟨j, hj⟩ from hij)


/-! ### The amplitude as a product over roots

`j ↦ -(rootSeq p j)` is a bijection from the indices onto the roots, so the
index product `AmplitudeMonotone.amp` is the product over the roots that
`RootAmplitude` speaks about. -/

theorem rootSeq_mem (p : ℝ[X]) {j : ℕ} (hj : j < (rootMags p).length) :
    -(rootSeq p j) ∈ p.roots := by
  rw [rootSeq_eq_getElem p hj]
  exact (mem_rootMags p).mp (List.getElem_mem hj)

theorem rootSeq_injOn (p : ℝ[X]) (hnd : p.roots.Nodup) {i j : ℕ}
    (hi : i < (rootMags p).length) (hj : j < (rootMags p).length)
    (h : rootSeq p i = rootSeq p j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_ge i j with hlt | hge
  · have := rootSeq_lt p hnd hlt hj
    linarith
  · have hlt : j < i := by lia
    have := rootSeq_lt p hnd hlt hi
    linarith

/-! ### From the root multiset to an indexed product -/

/-- The product over the root multiset, reindexed along the sorted magnitudes. -/
theorem prod_roots_eq_range {M : Type*} [CommMonoid M] (p : Polynomial ℝ) (g : ℝ → M) :
    (p.roots.map (fun ξ => g (-ξ))).prod
      = ∏ i ∈ Finset.range (rootMags p).length, g (rootSeq p i) := by
  have h1 : p.roots.map (fun ξ => g (-ξ)) = (p.roots.map (fun ξ => -ξ)).map g := by
    rw [Multiset.map_map]
    rfl
  have h2 : (p.roots.map (fun ξ => -ξ)) = ((rootMags p : List ℝ) : Multiset ℝ) := by
    rw [rootMags, Multiset.sort_eq]
  rw [h1, h2]
  have h3 : (((rootMags p : List ℝ) : Multiset ℝ).map g).prod
      = ((rootMags p).map g).prod := rfl
  rw [h3, List.prod_map_eq_prod_range_getD (a₀ := 0)]
  rfl

end

end RealRooted.SortedRoots
