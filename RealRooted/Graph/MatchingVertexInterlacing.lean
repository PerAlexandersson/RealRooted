import RealRooted.Mathlib.Combinatorics.SimpleGraph.MatchingPolyOn
import RealRooted.GarloffWagner.KreinExpansion
import RealRooted.LiuWang.General
import RealRooted.WeightedSum

/-!
# Vertex-deletion interlacing for matching polynomials

For a finite vertex set `S` of a simple graph and `v ∈ S`, the matching polynomial of
`G[S - v]` interlaces that of `G[S]` (Heilmann–Lieb; Godsil).  In particular every
matching polynomial `μ_S(x) = ∑_M (-1)^|M| x^(|S| - 2|M|)` is real-rooted.

The proof is by strong induction on `S` using the vertex recurrence
`μ_S = x μ_{S - v} - ∑_{u ∼ v} μ_{S - v - u}`
(`SimpleGraph.matchingPolyOn_eq_X_mul_sub`).  By induction each `μ_{S - v - u}` interlaces
`μ_{S - v}`, hence so does their sum (`StrictInterl.sum_right`), and the three-term step
`LiuWang.strictInterl_mul_add_mul_of_eval_nonpos` gives `μ_{S - v} ≪ μ_S`.

## References

* O. J. Heilmann, E. H. Lieb, *Theory of monomer-dimer systems*, Comm. Math. Phys. 25 (1972).
* C. D. Godsil, *Algebraic Combinatorics*, Chapman & Hall (1993), Chapter 6.
-/

open Polynomial

namespace RealRooted

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A sum of monic polynomials of degree `d` over a nonempty index set has degree `d` and
positive leading coefficient. -/
private theorem natDegree_sum_monic {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {d : ℕ}
    {f : ι → ℝ[X]} (hf : ∀ i ∈ s, (f i).Monic) (hd : ∀ i ∈ s, (f i).natDegree = d) :
    (∑ i ∈ s, f i).natDegree = d ∧ HasPosLeadingCoeff (∑ i ∈ s, f i) := by
  have hcoeff : (∑ i ∈ s, f i).coeff d = s.card := by
    rw [finsetSum_coeff, Finset.sum_congr rfl fun i hi =>
      (show (f i).coeff d = 1 by rw [← hd i hi]; exact (hf i hi).coeff_natDegree)]
    simp
  have hle : (∑ i ∈ s, f i).natDegree ≤ d :=
    natDegree_sum_le_of_forall_le s f fun i hi => (hd i hi).le
  have hpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hdeg : (∑ i ∈ s, f i).natDegree = d :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hcoeff]; exact hpos.ne'))
  refine ⟨hdeg, ?_⟩
  rw [HasPosLeadingCoeff, leadingCoeff, hdeg, hcoeff]
  exact hpos

/-- **Vertex-deletion interlacing** (Heilmann–Lieb, Godsil): for `v ∈ S`, the matching
polynomial of `G[S - v]` interlaces the matching polynomial of `G[S]`. -/
theorem interlaces_matchingPolyOn_erase (S : Finset V) {v : V} (hv : v ∈ S) :
    Interlaces (G.matchingPolyOn (S.erase v)) (G.matchingPolyOn S) := by
  induction S using Finset.strongInduction generalizing v with
  | H S ih =>
  set T := S.erase v with hT
  have hTS : T ⊂ S := Finset.erase_ssubset hv
  have hcardS : T.card + 1 = S.card := Finset.card_erase_add_one hv
  have hdegT : (G.matchingPolyOn T).natDegree = T.card := G.natDegree_matchingPolyOn T
  have hdegS : (G.matchingPolyOn S).natDegree = S.card := G.natDegree_matchingPolyOn S
  have hsplitsT : (G.matchingPolyOn T).Splits := by
    rcases T.eq_empty_or_nonempty with h | ⟨w, hw⟩
    · rw [h, G.matchingPolyOn_empty]
      exact Splits.one
    · exact (ih T hTS hw).1.2
  have hrec := G.matchingPolyOn_eq_X_mul_sub hv
  rw [← hT] at hrec
  set N := T.filter (G.Adj v)
  rcases N.eq_empty_or_nonempty with hN | hN
  · rw [hN, Finset.sum_empty, sub_zero] at hrec
    have h := strictInterl_self_X_sub_C_mul (G.monic_matchingPolyOn T).ne_zero hsplitsT 0
    rw [map_zero, sub_zero, ← hrec] at h
    exact h.toInterlaces (by rw [hdegT, hdegS, hcardS])
  -- the neighbour terms all interlace `μ_T`, hence so does their sum
  have hmem : ∀ u ∈ N, u ∈ T := fun u hu => (Finset.mem_filter.mp hu).1
  have hsum := natDegree_sum_monic hN (f := fun u => G.matchingPolyOn (T.erase u))
    (d := T.card - 1) (fun u _ => G.monic_matchingPolyOn _) fun u hu => by
      rw [G.natDegree_matchingPolyOn, Finset.card_erase_of_mem (hmem u hu)]
  have hint : StrictInterl (∑ u ∈ N, G.matchingPolyOn (T.erase u)) (G.matchingPolyOn T) := by
    rw [← Finset.sum_map_toList]
    refine StrictInterl.sum_right _ _ (fun p hp => ?_) (fun p hp => ?_) (by simpa using hN.ne_empty)
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp
      exact (ih T hTS (hmem u (Finset.mem_toList.mp hu))).toStrictInterl
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp
      rw [HasPosLeadingCoeff, (G.monic_matchingPolyOn _).leadingCoeff]
      exact zero_lt_one
  have hstep := LiuWang.strictInterl_mul_add_mul_of_eval_nonpos (a := X) (b := C (-1)) hint
    hsum.2 (by
      rw [C_neg, C_1, neg_one_mul, ← sub_eq_add_neg, ← hrec, HasPosLeadingCoeff,
        (G.monic_matchingPolyOn S).leadingCoeff]
      exact zero_lt_one)
    (by rw [C_neg, C_1, neg_one_mul, ← sub_eq_add_neg, ← hrec, hdegT, hdegS]; lia)
    (by rw [C_neg, C_1, neg_one_mul, ← sub_eq_add_neg, ← hrec, hdegT, hdegS]; lia)
    (fun r _ => by simp)
  rw [C_neg, C_1, neg_one_mul, ← sub_eq_add_neg, ← hrec] at hstep
  exact hstep.toInterlaces (by rw [hdegT, hdegS, hcardS])

/-- **Heilmann–Lieb**: the matching polynomial of every induced subgraph is real-rooted. -/
theorem splits_matchingPolyOn (S : Finset V) : (G.matchingPolyOn S).Splits := by
  rcases S.eq_empty_or_nonempty with h | ⟨v, hv⟩
  · rw [h, G.matchingPolyOn_empty]
    exact Splits.one
  · exact (interlaces_matchingPolyOn_erase G S hv).1.2

end RealRooted
