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

/-! ### The Heilmann–Lieb root bound -/

/-- The signed matching polynomial has the parity of `|S|`. -/
theorem eval_neg_matchingPolyOn (S : Finset V) (x : ℝ) :
    (G.matchingPolyOn S).eval (-x) = (-1) ^ S.card * (G.matchingPolyOn S).eval x := by
  rw [SimpleGraph.matchingPolyOn, eval_finsetSum, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun M hM => ?_
  have h2 := G.two_mul_card_le_of_mem_matchingsOn hM
  set k := S.card - 2 * M.card
  have hS : S.card = k + 2 * M.card := by lia
  simp only [eval_mul, eval_pow, eval_neg, eval_one, eval_X]
  rw [hS, neg_pow x k, pow_add, pow_mul]
  norm_num
  ring

/-- One step of the Heilmann–Lieb ratio estimate: if every `μ_{S-v-u}` with `u ∼ v` is at
most `μ_{S-v}(x) / t`, then `μ_S(x) ≥ μ_{S-v}(x) (x - d/t)` where `d` is the degree of `v`. -/
private theorem eval_matchingPolyOn_ge {S : Finset V} {v : V} (hv : v ∈ S) {x t : ℝ}
    (ht : 0 < t)
    (hu : ∀ u ∈ (S.erase v).filter (G.Adj v),
      t * (G.matchingPolyOn ((S.erase v).erase u)).eval x ≤
        (G.matchingPolyOn (S.erase v)).eval x) :
    (G.matchingPolyOn (S.erase v)).eval x *
        (x - ((S.erase v).filter (G.Adj v)).card / t) ≤
      (G.matchingPolyOn S).eval x := by
  rw [G.matchingPolyOn_eq_X_mul_sub hv, eval_sub, eval_mul, eval_X, eval_finsetSum]
  have hsum : ∑ u ∈ (S.erase v).filter (G.Adj v),
      (G.matchingPolyOn ((S.erase v).erase u)).eval x ≤
        ((S.erase v).filter (G.Adj v)).card * ((G.matchingPolyOn (S.erase v)).eval x / t) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun u hu' => by
      rw [le_div_iff₀ ht, mul_comm]
      exact hu u hu'
  have hring : (G.matchingPolyOn (S.erase v)).eval x *
        (x - ((S.erase v).filter (G.Adj v)).card / t) =
      x * (G.matchingPolyOn (S.erase v)).eval x -
        ((S.erase v).filter (G.Adj v)).card * ((G.matchingPolyOn (S.erase v)).eval x / t) := by
    ring
  linarith

/-- The Heilmann–Lieb ratio induction.  Suppose every vertex of `S` has at most `Δ` neighbours
in `S`, `t > 0`, `t² = Δ - 1` and `x > 2t`.  Then `μ_S(x) > 0`, and `t μ_{S-v}(x) ≤ μ_S(x)`
whenever `v` has at most `Δ - 1` neighbours in `S - v`. -/
private theorem matchingPolyOn_ratio {Δ : ℕ} {t x : ℝ} (ht : 0 < t)
    (htΔ : t ^ 2 = (Δ : ℝ) - 1) (hx : 2 * t < x) (S : Finset V)
    (hS : ∀ w ∈ S, (S.filter (G.Adj w)).card ≤ Δ) :
    0 < (G.matchingPolyOn S).eval x ∧
      ∀ v ∈ S, ((S.erase v).filter (G.Adj v)).card ≤ Δ - 1 →
        t * (G.matchingPolyOn (S.erase v)).eval x ≤ (G.matchingPolyOn S).eval x := by
  have hΔ2 : (2 : ℝ) ≤ Δ := by
    have : 1 < Δ := by exact_mod_cast (show (1 : ℝ) < Δ by nlinarith)
    exact_mod_cast this
  induction S using Finset.strongInduction with
  | H S ih =>
  -- the estimate for a single vertex
  have key : ∀ v ∈ S, 0 < (G.matchingPolyOn (S.erase v)).eval x ∧
      (G.matchingPolyOn (S.erase v)).eval x *
          (x - ((S.erase v).filter (G.Adj v)).card / t) ≤ (G.matchingPolyOn S).eval x := by
    intro v hv
    have hT := ih (S.erase v) (Finset.erase_ssubset hv) fun w hw =>
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset v S))).trans
        (hS w (Finset.mem_of_mem_erase hw))
    refine ⟨hT.1, eval_matchingPolyOn_ge G hv ht fun u hu => hT.2 u ?_ ?_⟩
    · exact (Finset.mem_filter.mp hu).1
    · obtain ⟨huT, hvu⟩ := Finset.mem_filter.mp hu
      have huS := Finset.mem_of_mem_erase huT
      have hsub : ((S.erase v).erase u).filter (G.Adj u) ⊆ (S.filter (G.Adj u)).erase v := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_erase] at hw ⊢
        exact ⟨hw.1.2.1, hw.1.2.2, hw.2⟩
      have hvmem : v ∈ S.filter (G.Adj u) := Finset.mem_filter.mpr ⟨hv, hvu.symm⟩
      have := (Finset.card_le_card hsub).trans_eq (Finset.card_erase_of_mem hvmem)
      have := hS u huS
      lia
  have hpos : 0 < (G.matchingPolyOn S).eval x := by
    rcases S.eq_empty_or_nonempty with h | ⟨v, hv⟩
    · simp [h, G.matchingPolyOn_empty]
    obtain ⟨hT, hge⟩ := key v hv
    have hd : (((S.erase v).filter (G.Adj v)).card : ℝ) ≤ Δ := by
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.erase_subset v S))).trans (hS v hv)
    have : 0 < x - ((S.erase v).filter (G.Adj v)).card / t := by
      rw [sub_pos, div_lt_iff₀ ht]
      nlinarith
    exact (mul_pos hT this).trans_le hge
  refine ⟨hpos, fun v hv hdeg => ?_⟩
  obtain ⟨hT, hge⟩ := key v hv
  have hd : (((S.erase v).filter (G.Adj v)).card : ℝ) ≤ Δ - 1 := by
    have : ((S.erase v).filter (G.Adj v)).card + 1 ≤ Δ := by
      have : 2 ≤ Δ := by exact_mod_cast hΔ2
      lia
    have : (((S.erase v).filter (G.Adj v)).card : ℝ) + 1 ≤ Δ := by exact_mod_cast this
    linarith
  have : t ≤ x - ((S.erase v).filter (G.Adj v)).card / t := by
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ ht]
    nlinarith
  calc t * (G.matchingPolyOn (S.erase v)).eval x
      = (G.matchingPolyOn (S.erase v)).eval x * t := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left this hT.le
    _ ≤ _ := hge

/-- **Heilmann–Lieb root bound**: if every vertex of `S` has at most `Δ ≥ 2` neighbours in
`S`, every root `r` of the matching polynomial of `G[S]` satisfies `|r| ≤ 2 √(Δ - 1)`. -/
theorem abs_le_of_isRoot_matchingPolyOn {Δ : ℕ} (hΔ : 2 ≤ Δ) (S : Finset V)
    (hS : ∀ w ∈ S, (S.filter (G.Adj w)).card ≤ Δ) {r : ℝ}
    (hr : (G.matchingPolyOn S).IsRoot r) : |r| ≤ 2 * Real.sqrt (Δ - 1) := by
  set t := Real.sqrt (Δ - 1)
  have hΔ' : (1 : ℝ) < Δ := by exact_mod_cast hΔ
  have ht : 0 < t := Real.sqrt_pos.mpr (by linarith)
  have htΔ : t ^ 2 = (Δ : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hpos : ∀ x, 2 * t < x → (G.matchingPolyOn S).eval x ≠ 0 := fun x hx =>
    (matchingPolyOn_ratio G ht htΔ hx S hS).1.ne'
  rw [abs_le]
  constructor
  · by_contra h
    apply hpos (-r) (by linarith)
    rw [eval_neg_matchingPolyOn, hr.eq_zero, mul_zero]
  · by_contra h
    exact hpos r (by linarith) hr.eq_zero

end RealRooted
