import RealRooted.RootAmplitude.Finite
import RealRooted.SortedRoots

/-!
# Amplitude bridges for sorted root magnitudes

This file adds only the polynomial-amplitude consequences missing from the
canonical `SortedRoots.rootMags` and `SortedRoots.rootSeq` API.
-/

open Polynomial

namespace RealRooted.RootAmplitude

noncomputable section

/-- Strict increase of the canonical sorted magnitude sequence implies that
all polynomial roots are simple. -/
theorem roots_nodup_of_rootSeq_lt {p : ℝ[X]}
    (hstrict : ∀ i j, i < j → j < (SortedRoots.rootMags p).length →
      SortedRoots.rootSeq p i < SortedRoots.rootSeq p j) :
    p.roots.Nodup := by
  have hpair : (SortedRoots.rootMags p).Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa only [← SortedRoots.rootSeq_eq_getElem p hi,
      ← SortedRoots.rootSeq_eq_getElem p hj] using hstrict i j hij hj
  have hlist : (SortedRoots.rootMags p).Nodup :=
    hpair.imp fun hab => ne_of_lt hab
  have hcoe : ((SortedRoots.rootMags p : List ℝ) : Multiset ℝ)
      = p.roots.map (fun r => -r) := by
    rw [SortedRoots.rootMags, Multiset.sort_eq]
  have hmap : (p.roots.map (fun r : ℝ => -r)).Nodup := by
    rw [← hcoe, Multiset.coe_nodup]
    exact hlist
  exact (Multiset.nodup_map_iff_of_injective neg_injective).mp hmap

/-- The canonical finite amplitude is the corresponding product over all
other polynomial roots. -/
theorem amp_rootSeq_eq_prod_roots {p : ℝ[X]} (hnd : p.roots.Nodup)
    {k : ℕ} (hk : k < (SortedRoots.rootMags p).length) :
    amp (SortedRoots.rootSeq p) (SortedRoots.rootMags p).length k
      = ∏ r ∈ p.roots.toFinset.erase (-SortedRoots.rootSeq p k),
          |1 - (-SortedRoots.rootSeq p k) / r| := by
  classical
  unfold amp
  refine Finset.prod_bij (fun j _ => -SortedRoots.rootSeq p j) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_erase, Finset.mem_range] at hj
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro heq
      exact hj.1 (SortedRoots.rootSeq_injOn p hnd hj.2 hk (neg_inj.mp heq))
    · exact Multiset.mem_toFinset.mpr (SortedRoots.rootSeq_mem p hj.2)
  · intro a ha b hb hab
    rw [Finset.mem_erase, Finset.mem_range] at ha hb
    exact SortedRoots.rootSeq_injOn p hnd ha.2 hb.2 (neg_inj.mp hab)
  · intro r hr
    rw [Finset.mem_erase, Multiset.mem_toFinset] at hr
    have hmem : -r ∈ SortedRoots.rootMags p :=
      (SortedRoots.mem_rootMags p).mpr (by simpa using hr.2)
    obtain ⟨j, hj, hvalue⟩ := List.getElem_of_mem hmem
    refine ⟨j, ?_, ?_⟩
    · refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr hj⟩
      intro hjk
      subst hjk
      exact hr.1 (by rw [SortedRoots.rootSeq_eq_getElem p hj, hvalue]; ring)
    · rw [SortedRoots.rootSeq_eq_getElem p hj, hvalue]
      ring
  · intro j hj
    rw [Finset.mem_erase, Finset.mem_range] at hj
    congr 1
    rw [neg_div_neg_eq]

end

end RealRooted.RootAmplitude
