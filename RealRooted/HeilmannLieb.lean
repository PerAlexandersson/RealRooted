import RealRooted.ChudnovskySeymour
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Heilmann--Lieb graph interface

This file starts the graph-facing route from Chudnovsky--Seymour to
Heilmann--Lieb. The polynomial Chudnovsky--Seymour package in this repository is
an interlacing engine for finite families of polynomials; the remaining graph
work is to connect claw-free graph independence polynomials to that engine.

We add the graph polynomial definitions, prove that line graphs are claw-free,
and record the final matching-generating corollary as a theorem conditional on
the graph-form Chudnovsky--Seymour statement for independence polynomials of
claw-free graphs.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

/-- Independence-generating polynomial of a finite simple graph. -/
def indepPoly {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact ∑ s ∈ (Finset.univ.powerset.filter fun s : Finset V =>
      G.IsIndepSet (s : Set V)),
    (X : ℝ[X]) ^ s.card

/-- Independent subsets of a fixed finite vertex support. -/
def indepSetsOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Finset V) :=
  S.powerset.filter fun s : Finset V => G.IsIndepSet (s : Set V)

/-- Support-restricted independence polynomial. -/
def indepPolyOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℝ[X] :=
  ∑ s ∈ indepSetsOn G S, (X : ℝ[X]) ^ s.card

/-- Weighted support-restricted independence polynomial.  The unweighted
version is the specialization where every vertex has weight `1`. -/
def weightedIndepPolyOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (wt : V → ℝ) : ℝ[X] :=
  ∑ s ∈ indepSetsOn G S, (∏ v ∈ s, C (wt v)) * (X : ℝ[X]) ^ s.card

/-- Weighted independence polynomial of a finite graph. -/
def weightedIndepPoly {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (wt : V → ℝ) : ℝ[X] :=
  weightedIndepPolyOn G Finset.univ wt

/-- The weighted support-restricted definition recovers the global weighted
independence polynomial on the full vertex set. -/
theorem weightedIndepPoly_eq_weightedIndepPolyOn_univ
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ) :
    weightedIndepPoly G wt = weightedIndepPolyOn G Finset.univ wt := by
  rfl

/-- The weighted support-restricted independence polynomial with all weights
equal to `1` is the unweighted support-restricted independence polynomial. -/
theorem weightedIndepPolyOn_one {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    weightedIndepPolyOn G S (fun _ ↦ 1) = indepPolyOn G S := by
  unfold weightedIndepPolyOn indepPolyOn
  simp

/-- The empty independent set gives the constant coefficient of the weighted
support-restricted independence polynomial. -/
theorem weightedIndepPolyOn_coeff_zero {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (wt : V → ℝ) :
    (weightedIndepPolyOn G S wt).coeff 0 = 1 := by
  classical
  rw [weightedIndepPolyOn, Polynomial.finsetSum_coeff, Finset.sum_eq_single ∅]
  · simp
  · intro s hs hne
    have : s.card ≠ 0 := by simp_all
    have hnot : ¬ s.card ≤ 0 := by simp_all
    rw [Polynomial.coeff_mul_X_pow', if_neg hnot]
  · intro hnot
    simp [indepSetsOn] at hnot

/-- Weighted support-restricted independence polynomials are nonzero. -/
theorem weightedIndepPolyOn_ne_zero {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (wt : V → ℝ) :
    weightedIndepPolyOn G S wt ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) h
  simp [weightedIndepPolyOn_coeff_zero] at hcoeff

/-- Weighted support-restricted independence polynomials have nonnegative
coefficients when all vertex weights on the support are nonnegative. -/
theorem weightedIndepPolyOn_hasNonnegCoeffs {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {wt : V → ℝ}
    (hwt : ∀ v ∈ S, 0 ≤ wt v) :
    HasNonnegCoeffs (weightedIndepPolyOn G S wt) := by
  classical
  have hprod :
      ∀ t : Finset V, t ⊆ S → HasNonnegCoeffs (∏ v ∈ t, C (wt v)) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _hsub
      simp [hasNonnegCoeffs_one]
    · intro v t hv ih hsub
      rw [Finset.prod_insert hv]
      have hv_nonneg : HasNonnegCoeffs (C (wt v)) := by
        simpa using nonnegCoeffs_C_mul (hwt v (hsub (Finset.mem_insert_self v t)))
          hasNonnegCoeffs_one
      have hsub_t : t ⊆ S := fun w hw => hsub (Finset.mem_insert.mpr (Or.inr hw))
      exact hv_nonneg.mul (ih hsub_t)
  intro n
  rw [weightedIndepPolyOn, Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun t ht => by
    have hsub : t ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    exact ((hprod t hsub).mul (hasNonnegCoeffs_X.pow t.card)) n

/-- Weighted support-restricted independence polynomials have positive leading
coefficient under nonnegative weights on the support. -/
theorem weightedIndepPolyOn_hasPosLeadingCoeff {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {wt : V → ℝ}
    (hwt : ∀ v ∈ S, 0 ≤ wt v) :
    HasPosLeadingCoeff (weightedIndepPolyOn G S wt) :=
  (weightedIndepPolyOn_hasNonnegCoeffs G hwt).pos_leadingCoeff
    (weightedIndepPolyOn_ne_zero G S wt)

/-- The weighted independence polynomial on the empty support is `1`. -/
theorem weightedIndepPolyOn_empty {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ) :
    weightedIndepPolyOn G (∅ : Finset V) wt = 1 := by
  rw [weightedIndepPolyOn]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro s hs hne
    have hs' : s = ∅ ∧ G.IsIndepSet (s : Set V) := by simpa [indepSetsOn] using hs
    simp_all
  · intro hnot
    simp [indepSetsOn] at hnot

/-- The weighted independence polynomial on the empty support splits. -/
theorem weightedIndepPolyOn_empty_splits {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ) :
    (weightedIndepPolyOn G (∅ : Finset V) wt).Splits := by
  rw [weightedIndepPolyOn_empty]
  simp

/-- Support-restricted independence polynomials are nonzero. -/
theorem indepPolyOn_ne_zero {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    indepPolyOn G S ≠ 0 := by
  simpa [weightedIndepPolyOn_one] using
    (weightedIndepPolyOn_ne_zero G S fun _ => 1)

/-- Support-restricted independence polynomials have nonnegative coefficients. -/
theorem indepPolyOn_hasNonnegCoeffs {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    HasNonnegCoeffs (indepPolyOn G S) := by
  simpa [weightedIndepPolyOn_one] using
    (weightedIndepPolyOn_hasNonnegCoeffs (G := G) (S := S) (wt := fun _ ↦ 1)
      (by simp))

/-- Support-restricted independence polynomials have positive leading coefficient. -/
theorem indepPolyOn_hasPosLeadingCoeff {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    HasPosLeadingCoeff (indepPolyOn G S) :=
  (indepPolyOn_hasNonnegCoeffs G S).pos_leadingCoeff (indepPolyOn_ne_zero G S)

/-- The empty support has independence polynomial `1`. -/
theorem indepPolyOn_empty {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    indepPolyOn G (∅ : Finset V) = 1 := by
  rw [indepPolyOn]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro s hs hne
    have hs' : s = ∅ ∧ G.IsIndepSet (s : Set V) := by simpa [indepSetsOn] using hs
    simp_all
  · intro hnot
    simp [indepSetsOn] at hnot

/-- The empty support independence polynomial splits. -/
theorem indepPolyOn_empty_splits {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    (indepPolyOn G (∅ : Finset V)).Splits := by
  rw [indepPolyOn_empty]
  simp

private theorem compatible_self_X_mul_of_splits {p : ℝ[X]} (hp : p.Splits) :
    Compatible p (X * p) := by
  intro α β _hα _hβ
  have hlin : (C α + C β * X : ℝ[X]).Splits := by
    by_cases hβ0 : β = 0
    · simp [hβ0]
    · have hβα : β * (α / β) = α := by grind
      have : (C α + C β * X : ℝ[X]) = C β * (X + C (α / β)) := by grind
      simp_all
  have hsum : C α * p + C β * (X * p) = (C α + C β * X) * p := by ring
  have : (C α * p + C β * (X * p)).Splits := by simp_all
  grind

/-- If a weighted support-restricted independence polynomial is real-rooted,
then it is compatible with its `X`-multiple. -/
theorem compatible_weightedIndepPolyOn_X_mul_self_of_splits
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (wt : V → ℝ) (hS : (weightedIndepPolyOn G S wt).Splits) :
    Compatible (weightedIndepPolyOn G S wt)
      (X * weightedIndepPolyOn G S wt) :=
  compatible_self_X_mul_of_splits hS

/-- If a support-restricted independence polynomial is real-rooted, then it is
compatible with its `X`-multiple. -/
theorem compatible_indepPolyOn_X_mul_self_of_splits {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hS : (indepPolyOn G S).Splits) :
    Compatible (indepPolyOn G S) (X * indepPolyOn G S) :=
  compatible_self_X_mul_of_splits hS

private theorem compatible_self_of_splits {p : ℝ[X]} (hp_ne : p ≠ 0) (hp : p.Splits) :
    Compatible p p := by
  intro α β _hα _hβ
  have hsum : C α * p + C β * p = C (α + β) * p := by grind
  by_cases hzero : α + β = 0
  · simp_all
  · right
    rw [hsum]
    exact isRealRooted_C_mul hp_ne hp hzero

private theorem compatible_X_mul_of_compatible {f g : ℝ[X]} (h : Compatible f g) :
    Compatible (X * f) (X * g) := by
  intro α β hα hβ
  have hsum : C α * (X * f) + C β * (X * g) =
      X * (C α * f + C β * g) := by
    ring
  rcases h α β hα hβ with hzero | hrr <;> simp_all

private theorem splits_add_of_compatible {p q : ℝ[X]} (h : Compatible p q)
    (hadd : p + q ≠ 0) : (p + q).Splits := by
  have hcombo := h 1 1 zero_le_one zero_le_one
  simp_all

private theorem splits_add_C_mul_of_compatible {p q : ℝ[X]} (h : Compatible p q)
    {r : ℝ} (hr : 0 ≤ r) (hadd : p + C r * q ≠ 0) :
    (p + C r * q).Splits := by
  have hcombo := h 1 r zero_le_one hr
  simp_all

/-- The support-restricted definition recovers `indepPoly` on the full vertex set. -/
theorem indepPoly_eq_indepPolyOn_univ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    indepPoly G = indepPolyOn G Finset.univ := by
  unfold indepPoly indepPolyOn indepSetsOn
  grind

/-- Claw-free graph: no vertex has three pairwise non-adjacent neighbors. -/
def ClawFree {V : Type u} (G : _root_.SimpleGraph V) : Prop :=
  ∀ v : V, ∀ s : Finset V, (∀ w ∈ s, G.Adj v w) → ¬ G.IsNIndepSet 3 s

/-- Induced subgraphs of claw-free graphs are claw-free. -/
theorem ClawFree.induce {V : Type u} {G : _root_.SimpleGraph V}
    (hG : ClawFree G) (s : Set V) : ClawFree (G.induce s) := by
  intro v t hneigh hind
  let t' : Finset V := t.map ⟨Subtype.val, Subtype.val_injective⟩
  have ht'_neigh : ∀ w ∈ t', G.Adj v w := by
    intro w hw
    rcases Finset.mem_map.mp hw with ⟨x, hx, rfl⟩
    simp_all
  have ht'_ind : G.IsNIndepSet 3 t' := by
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hne hadj
      rcases Finset.mem_map.mp ha with ⟨a', ha', rfl⟩
      rcases Finset.mem_map.mp hb with ⟨b', hb', hb_eq⟩
      subst hb_eq
      exact hind.isIndepSet ha' hb' (fun h => hne (congrArg Subtype.val h)) hadj
    · rw [Finset.card_map]
      exact hind.card_eq
  exact hG v t' ht'_neigh ht'_ind

private theorem ClawFree.adj_of_forced_triangle {V : Type u}
    {G : _root_.SimpleGraph V} (hG : ClawFree G)
    {z a b c : V} (hza : G.Adj z a) (hzb : G.Adj z b) (hzc : G.Adj z c)
    (hab : ¬ G.Adj a b) (hac : ¬ G.Adj a c)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (hbc_ne : b ≠ c) : G.Adj b c := by
  classical
  by_contra hbc
  have hneigh : ∀ w ∈ ({a, b, c} : Finset V), G.Adj z w := by simp_all
  have hind : G.IsNIndepSet 3 ({a, b, c} : Finset V) := by
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.isIndepSet_iff]
      intro x hx y hy hne hadj
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · simp_all
      · simp_all
      · simp_all
      · exact hab hadj.symm
      · simp_all
      · simp_all
      · exact hac hadj.symm
      · exact hbc hadj.symm
      · simp_all
    · simp [hab_ne, hac_ne, hbc_ne]
  exact hG z {a, b, c} hneigh hind

/-- Neighbors of a vertex inside a finite support. -/
def neighborSetOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : Finset V :=
  S.filter fun w => G.Adj v w

/-- Closed neighborhood of a vertex inside a finite support. -/
def closedNeighborSetOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : Finset V :=
  S.filter fun w => w = v ∨ G.Adj v w

/-- Common closed neighborhood of two vertices inside a finite support. -/
def commonClosedNeighborSetOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) : Finset V :=
  closedNeighborSetOn G S u ∩ closedNeighborSetOn G S v

/-- The common closed neighborhood inside `S` is a sub-support of `S`. -/
theorem commonClosedNeighborSetOn_subset {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) :
    commonClosedNeighborSetOn G S u v ⊆ S := by
  intro w hw
  exact (Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).1

/-- Neighbors of a vertex in a finite support, excluding a clique. -/
def neighborOutsideCliqueOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) (v : V) : Finset V :=
  neighborSetOn G S v \ K

/-- A support-level version of the simplicial clique condition from
Chudnovsky--Seymour. -/
def IsSimplicialCliqueOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) : Prop :=
  K ⊆ S ∧ G.IsClique (K : Set V) ∧
    ∀ v ∈ K, G.IsClique (neighborOutsideCliqueOn G S K v : Set V)

/-- The empty clique is simplicial on every finite support. -/
theorem isSimplicialCliqueOn_empty {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    IsSimplicialCliqueOn G S ∅ := by
  simp [IsSimplicialCliqueOn]

/-- Chudnovsky--Seymour Lemma 2.6 graph ingredient, in finite-support form.
After deleting the common closed neighborhood of adjacent vertices `u` and `v`,
the remaining neighbors of `u` form a simplicial clique.  The corresponding
statement for `v` follows by symmetry. -/
theorem ClawFree.neighborSetOn_sdiff_commonClosedNeighbor_simplicial
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} {u v : V} (huv : G.Adj u v) :
    IsSimplicialCliqueOn G (S \ commonClosedNeighborSetOn G S u v)
      (neighborSetOn G (S \ commonClosedNeighborSetOn G S u v) u) := by
  classical
  let H := S \ commonClosedNeighborSetOn G S u v
  let K := neighborSetOn G H u
  change IsSimplicialCliqueOn G H K
  have hu_not_H : u ∉ H := by
    intro huH
    have huH' := Finset.mem_sdiff.mp huH
    have huS : u ∈ S := huH'.1
    have huCommon : u ∈ commonClosedNeighborSetOn G S u v := by
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨huS, Or.inl rfl⟩,
          Finset.mem_filter.mpr ⟨huS, Or.inr huv.symm⟩⟩
    simp_all
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).1
  · intro x hx y hy hxy
    have hxK := Finset.mem_filter.mp hx
    have hyK := Finset.mem_filter.mp hy
    have hxH' := Finset.mem_sdiff.mp hxK.1
    have hyH' := Finset.mem_sdiff.mp hyK.1
    have hxClosedU : x ∈ closedNeighborSetOn G S u := by
      exact Finset.mem_filter.mpr ⟨hxH'.1, Or.inr hxK.2⟩
    have hyClosedU : y ∈ closedNeighborSetOn G S u := by
      exact Finset.mem_filter.mpr ⟨hyH'.1, Or.inr hyK.2⟩
    have hx_not_closed_v : x ∉ closedNeighborSetOn G S v := by
      intro hxClosedV
      exact hxH'.2 (Finset.mem_inter.mpr ⟨hxClosedU, hxClosedV⟩)
    have hy_not_closed_v : y ∉ closedNeighborSetOn G S v := by
      intro hyClosedV
      exact hyH'.2 (Finset.mem_inter.mpr ⟨hyClosedU, hyClosedV⟩)
    have hvx_not : ¬ G.Adj v x := by
      intro hvx
      exact hx_not_closed_v (Finset.mem_filter.mpr ⟨hxH'.1, Or.inr hvx⟩)
    have hvy_not : ¬ G.Adj v y := by
      intro hvy
      exact hy_not_closed_v (Finset.mem_filter.mpr ⟨hyH'.1, Or.inr hvy⟩)
    have hvx_ne : v ≠ x := by
      intro hvx
      exact hx_not_closed_v (Finset.mem_filter.mpr ⟨hxH'.1, Or.inl hvx.symm⟩)
    have hvy_ne : v ≠ y := by
      intro hvy
      exact hy_not_closed_v (Finset.mem_filter.mpr ⟨hyH'.1, Or.inl hvy.symm⟩)
    exact hG.adj_of_forced_triangle huv hxK.2 hyK.2 hvx_not hvy_not
      hvx_ne hvy_ne hxy
  · intro n hn x hx y hy hxy
    have hnK := Finset.mem_filter.mp hn
    have hxOut := Finset.mem_sdiff.mp hx
    have hyOut := Finset.mem_sdiff.mp hy
    have hxN := Finset.mem_filter.mp hxOut.1
    have hyN := Finset.mem_filter.mp hyOut.1
    have hux_not : ¬ G.Adj u x := by
      intro hux
      exact hxOut.2 (Finset.mem_filter.mpr ⟨hxN.1, hux⟩)
    have huy_not : ¬ G.Adj u y := by
      intro huy
      exact hyOut.2 (Finset.mem_filter.mpr ⟨hyN.1, huy⟩)
    have hux_ne : u ≠ x := by grind
    have huy_ne : u ≠ y := by grind
    exact hG.adj_of_forced_triangle hnK.2.symm hxN.2 hyN.2 hux_not huy_not
      hux_ne huy_ne hxy

/-- Symmetric version of
`ClawFree.neighborSetOn_sdiff_commonClosedNeighbor_simplicial`. -/
theorem ClawFree.neighborSetOn_sdiff_commonClosedNeighbor_simplicial_right
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} {u v : V} (huv : G.Adj u v) :
    IsSimplicialCliqueOn G (S \ commonClosedNeighborSetOn G S u v)
      (neighborSetOn G (S \ commonClosedNeighborSetOn G S u v) v) := by
  simpa [commonClosedNeighborSetOn, inter_comm] using
    hG.neighborSetOn_sdiff_commonClosedNeighbor_simplicial (S := S) huv.symm

/-- Removing an arbitrary set of vertices preserves a support-level simplicial
clique after subtracting the same vertices from the clique. -/
theorem IsSimplicialCliqueOn.sdiff_right {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] {S K : Finset V}
    (hK : IsSimplicialCliqueOn G S K) (L : Finset V) :
    IsSimplicialCliqueOn G (S \ L) (K \ L) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_sdiff.mpr ⟨hK.1 (Finset.mem_sdiff.mp hx).1,
      (Finset.mem_sdiff.mp hx).2⟩
  · exact hK.2.1.subset fun _x hx => (Finset.mem_sdiff.mp hx).1
  · intro v hv
    have hvK : v ∈ K := (Finset.mem_sdiff.mp hv).1
    exact (hK.2.2 v hvK).subset fun x hx => by
      have hx' := Finset.mem_sdiff.mp hx
      have hxN := Finset.mem_filter.mp hx'.1
      have hxSL := Finset.mem_sdiff.mp hxN.1
      have hx_notK : x ∉ K := by simp_all
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨hxSL.1, hxN.2⟩, hx_notK⟩

/-- Chudnovsky--Seymour Lemma 2.4, in finite-support form.  In a claw-free
graph, deleting a simplicial clique leaves each outside-neighbor set as a
simplicial clique in the remaining support. -/
theorem ClawFree.simplicialClique_neighborOutside {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S K : Finset V} (hK : IsSimplicialCliqueOn G S K) {k : V} (hk : k ∈ K) :
    IsSimplicialCliqueOn G (S \ K) (neighborOutsideCliqueOn G S K k) := by
  classical
  refine ⟨?_, hK.2.2 k hk, ?_⟩
  · intro n hn
    have hn' := Finset.mem_sdiff.mp hn
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hn'.1).1, hn'.2⟩
  · intro n hn x hx y hy hxy
    by_contra hnot
    have hnL := Finset.mem_sdiff.mp hn
    have hnN := Finset.mem_filter.mp hnL.1
    have hkn : G.Adj k n := hnN.2
    have hx' : x ∈ neighborOutsideCliqueOn G (S \ K) (neighborOutsideCliqueOn G S K k) n := by grind
    have hy' : y ∈ neighborOutsideCliqueOn G (S \ K) (neighborOutsideCliqueOn G S K k) n := by grind
    have hxL := Finset.mem_sdiff.mp hx'
    have hyL := Finset.mem_sdiff.mp hy'
    have hxN := Finset.mem_filter.mp hxL.1
    have hyN := Finset.mem_filter.mp hyL.1
    have hxSdiff := Finset.mem_sdiff.mp hxN.1
    have hySdiff := Finset.mem_sdiff.mp hyN.1
    have hkx_not : ¬ G.Adj k x := by
      intro hkx
      exact hxL.2 (Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨hxSdiff.1, hkx⟩, hxSdiff.2⟩)
    have hky_not : ¬ G.Adj k y := by
      intro hky
      exact hyL.2 (Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨hySdiff.1, hky⟩, hySdiff.2⟩)
    have hneigh : ∀ w ∈ ({k, x, y} : Finset V), G.Adj n w := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hkn.symm
      · simp_all
      · simp_all
    have hxk : x ≠ k := fun hxk ↦ hxSdiff.2 (by simp_all)
    have hyk : y ≠ k := fun hyk ↦ hySdiff.2 (by simp_all)
    have hind : G.IsNIndepSet 3 ({k, x, y} : Finset V) := by
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.isIndepSet_iff]
        intro a ha b hb hne hadj
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · simp_all
        · simp_all
        · simp_all
        · exact hkx_not hadj.symm
        · simp_all
        · simp_all
        · exact hky_not hadj.symm
        · exact hnot hadj.symm
        · simp_all
      · simp [hxk.symm, hyk.symm, hxy]
    exact hG n {k, x, y} hneigh hind

/-- Inserting a new vertex preserves independence exactly when the old set was
independent and every old vertex is non-adjacent to the new one. -/
theorem isIndepSet_insert_iff {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {v : V} {s : Finset V} (hv : v ∉ s) :
    G.IsIndepSet ((insert v s : Finset V) : Set V) ↔
      G.IsIndepSet (s : Set V) ∧ ∀ w ∈ s, ¬ G.Adj v w := by
  constructor
  · intro h
    constructor
    · intro a ha b hb hne hadj
      exact h (by simp [ha]) (by simp [hb]) hne hadj
    · intro w hw hadj
      exact h (by simp) (by simp [hw]) (fun hvw => hv (by simp_all)) hadj
  · rintro ⟨hind, hnonadj⟩ a ha b hb hne hadj
    simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · grind
    · rcases hb with rfl | hb
      · exact hnonadj a ha hadj.symm
      · exact hind ha hb hne hadj

/-- Independent sets on `insert v S` split into those avoiding `v` and those
containing `v`.  In the latter case the remaining vertices must lie in the
non-neighbor support. -/
theorem indepSetsOn_insert {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hv : v ∉ S) :
    indepSetsOn G (insert v S) =
      indepSetsOn G S ∪
        (indepSetsOn G (S.filter fun w => ¬ G.Adj v w)).image (insert v) := by
  ext t
  simp only [indepSetsOn, Finset.mem_filter, Finset.mem_powerset, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨htsub, htind⟩
    by_cases hvt : v ∈ t
    · refine Or.inr ?_
      refine ⟨t.erase v, ?_, ?_⟩
      · have hsubS : t.erase v ⊆ S := by grind
        have hnotadj : ∀ w ∈ t.erase v, ¬ G.Adj v w := by
          intro w hw
          have hne : v ∉ t.erase v := Finset.notMem_erase v t
          have ht_eq : insert v (t.erase v) = t := Finset.insert_erase hvt
          have htind' : G.IsIndepSet ((insert v (t.erase v) : Finset V) : Set V) := by simp_all
          exact ((isIndepSet_insert_iff hne).mp htind').2 w hw
        exact ⟨fun w hw ↦ Finset.mem_filter.mpr ⟨hsubS hw, hnotadj w hw⟩,
          ((isIndepSet_insert_iff (Finset.notMem_erase v t)).mp
            (by simp_all)).1⟩
      · simp_all
    · grind
  · rintro (hleft | hright)
    · grind
    · rcases hright with ⟨u, hu, htu⟩
      subst htu
      have hvu : v ∉ u := fun h ↦ hv (Finset.mem_filter.mp (hu.1 h)).1
      refine ⟨?_, ?_⟩
      · grind
      · exact (isIndepSet_insert_iff hvu).mpr
          ⟨hu.2, fun w hw ↦ (Finset.mem_filter.mp (hu.1 hw)).2⟩

/-- Vertex insertion recurrence for weighted support-restricted independence
polynomials.  Varying the weight of the inserted vertex is the graph-side
source of the nonnegative linear combinations used in the compatibility
argument. -/
theorem weightedIndepPolyOn_insert {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    {S : Finset V} {v : V} (hv : v ∉ S) :
    weightedIndepPolyOn G (insert v S) wt =
      weightedIndepPolyOn G S wt +
        C (wt v) * X * weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt := by
  unfold weightedIndepPolyOn
  rw [indepSetsOn_insert G hv]
  have hdisj : Disjoint (indepSetsOn G S)
      ((indepSetsOn G (S.filter fun w => ¬ G.Adj v w)).image (insert v)) := by
    rw [Finset.disjoint_left]
    intro t ht htimg
    have hvt_not : v ∉ t :=
      Finset.notMem_of_mem_powerset_of_notMem (Finset.mem_filter.mp ht).1 hv
    grind
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    have hsub : u ⊆ S.filter fun w ↦ ¬ G.Adj v w :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
    grind
  · intro u hu w hw h
    have hsubu : u ⊆ S.filter fun x ↦ ¬ G.Adj v x :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
    have hsubw : w ⊆ S.filter fun x => ¬ G.Adj v x :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hw).1
    have hvu : v ∉ u := fun hmem => hv (Finset.mem_filter.mp (hsubu hmem)).1
    have hvw : v ∉ w := fun hmem => hv (Finset.mem_filter.mp (hsubw hmem)).1
    have herase := congrArg (fun t : Finset V => t.erase v) h
    simpa [Finset.erase_insert hvu, Finset.erase_insert hvw] using herase

/-- The weighted support-restricted independence polynomial only depends on
the weights on its support. -/
theorem weightedIndepPolyOn_congr {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {S : Finset V}
    {wt wt' : V → ℝ} (hwt : ∀ v ∈ S, wt v = wt' v) :
    weightedIndepPolyOn G S wt = weightedIndepPolyOn G S wt' := by
  unfold weightedIndepPolyOn
  apply Finset.sum_congr rfl
  intro t ht
  have hsub : t ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  have hprod : (∏ v ∈ t, C (wt v)) = (∏ v ∈ t, C (wt' v)) := by
    apply Finset.prod_congr rfl
    grind
  simp_all

/-- In the weighted insertion recurrence, the inserted vertex weight can be
chosen independently of the old weights on the two smaller supports. -/
theorem weightedIndepPolyOn_insert_update {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    {S : Finset V} {v : V} (hv : v ∉ S) (a : ℝ) :
    weightedIndepPolyOn G (insert v S) (Function.update wt v a) =
      weightedIndepPolyOn G S wt +
        C a * X * weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt := by
  rw [weightedIndepPolyOn_insert G (Function.update wt v a) hv]
  have hS : weightedIndepPolyOn G S (Function.update wt v a) =
      weightedIndepPolyOn G S wt := by
    apply weightedIndepPolyOn_congr
    grind
  have hN : weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w)
      (Function.update wt v a) =
        weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt := by
    apply weightedIndepPolyOn_congr
    grind
  simp [hS, hN]

/-- Weighted insertion supplies the two-term compatibility input for the
Chudnovsky--Seymour engine: nonnegative combinations of the old support
polynomial and the `X`-shifted non-neighbor support are obtained by changing
the inserted vertex weight and then scaling. -/
theorem compatible_weightedIndepPolyOn_X_mul_of_insert_splits
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    {S : Finset V} {v : V} (hv : v ∉ S)
    (hN : (weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt).Splits)
    (hinsert : ∀ a : ℝ, 0 ≤ a →
      (weightedIndepPolyOn G (insert v S) (Function.update wt v a)).Splits) :
    Compatible (weightedIndepPolyOn G S wt)
      (X * weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt) := by
  intro α β hα hβ
  by_cases hα0 : α = 0
  · by_cases hβ0 : β = 0
    · simp_all
    · have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
      have :
          (X * weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt) ≠ 0 ∧
            (X * weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt).Splits :=
        isRealRooted_X_mul
          (weightedIndepPolyOn_ne_zero G (S.filter fun w ↦ ¬ G.Adj v w) wt) hN
      simp_all
  · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    have hbase_ne :
        weightedIndepPolyOn G (insert v S) (Function.update wt v (β / α)) ≠ 0 :=
      weightedIndepPolyOn_ne_zero G (insert v S) (Function.update wt v (β / α))
    have hbase_split :
        (weightedIndepPolyOn G (insert v S) (Function.update wt v (β / α))).Splits :=
      hinsert (β / α) (div_nonneg hβ hαpos.le)
    have := isRealRooted_C_mul hbase_ne hbase_split hαpos.ne'
    have hrec := weightedIndepPolyOn_insert_update G wt hv (β / α)
    have :
        C α * weightedIndepPolyOn G (insert v S) (Function.update wt v (β / α)) =
          C α * weightedIndepPolyOn G S wt +
            C β * (X * weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt) := by
      rw [hrec, mul_add]
      congr 1
      calc
        C α * (C (β / α) * X *
            weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt) =
            (C α * C (β / α)) * X *
              weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt := by grind
        _ = C (α * (β / α)) * X *
              weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt := by simp
        _ = C β * X *
              weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt := by grind
        _ = C β *
              (X * weightedIndepPolyOn G (S.filter fun w ↦ ¬ G.Adj v w) wt) := by grind
    grind

/-- Vertex insertion recurrence for the support-restricted independence
polynomial. -/
theorem indepPolyOn_insert {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hv : v ∉ S) :
    indepPolyOn G (insert v S) =
      indepPolyOn G S + X * indepPolyOn G (S.filter fun w => ¬ G.Adj v w) := by
  simpa [weightedIndepPolyOn_one] using
    (weightedIndepPolyOn_insert (G := G) (wt := fun _ => 1) hv)

/-- The support left after deleting the closed neighborhood of `v`, relative to
a finite ambient support. -/
def deleteClosedNeighborSupport {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : Finset V :=
  (S.erase v).filter fun w => ¬ G.Adj v w

/-- Closed-neighborhood deletion leaves a sub-support of the original support. -/
theorem deleteClosedNeighborSupport_subset {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    deleteClosedNeighborSupport G S v ⊆ S := by
  intro w hw
  exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1

/-- Closed-neighborhood deletion is contained in the support with the vertex
itself erased. -/
theorem deleteClosedNeighborSupport_subset_erase {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    deleteClosedNeighborSupport G S v ⊆ S.erase v := by
  intro w hw
  exact (Finset.mem_filter.mp hw).1

/-- Vertex-deletion recurrence for the weighted support-restricted
independence polynomial. -/
theorem weightedIndepPolyOn_erase {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    {S : Finset V} {v : V} (hv : v ∈ S) :
    weightedIndepPolyOn G S wt =
      weightedIndepPolyOn G (S.erase v) wt +
        C (wt v) * X *
          weightedIndepPolyOn G (deleteClosedNeighborSupport G S v) wt := by
  have h := weightedIndepPolyOn_insert
    (G := G) (wt := wt) (S := S.erase v) (v := v)
    (Finset.notMem_erase v S)
  simpa [deleteClosedNeighborSupport, Finset.insert_erase hv] using h

/-- Vertex-deletion recurrence for the support-restricted independence
polynomial. -/
theorem indepPolyOn_erase {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hv : v ∈ S) :
    indepPolyOn G S =
      indepPolyOn G (S.erase v) +
        X * indepPolyOn G (deleteClosedNeighborSupport G S v) := by
  have h := indepPolyOn_insert
    (G := G) (S := S.erase v) (v := v) (Finset.notMem_erase v S)
  simpa [deleteClosedNeighborSupport, Finset.insert_erase hv] using h

/-- If `v` has no neighbors in `S.erase v`, then deleting the closed
neighborhood of `v` only erases `v`. -/
theorem deleteClosedNeighborSupport_eq_erase_of_neighborSetOn_empty
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hneighbor : neighborSetOn G (S.erase v) v = ∅) :
    deleteClosedNeighborSupport G S v = S.erase v := by
  ext w
  constructor
  · intro hw
    exact (Finset.mem_filter.mp hw).1
  · intro hw
    refine Finset.mem_filter.mpr ⟨hw, ?_⟩
    intro hvw
    have hwNeighbor : w ∈ neighborSetOn G (S.erase v) v :=
      Finset.mem_filter.mpr ⟨hw, hvw⟩
    simp [hneighbor] at hwNeighbor

/-- The no-neighbor case of Chudnovsky--Seymour Lemma 2.6.  If `v` is isolated
inside `S`, then the vertex-deletion summands are just a polynomial and its
`X`-multiple. -/
theorem compatible_erase_X_mul_deleteClosedNeighborSupport_of_no_neighbors
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hneighbor : neighborSetOn G (S.erase v) v = ∅)
    (hSplit : (indepPolyOn G (S.erase v)).Splits) :
    Compatible (indepPolyOn G (S.erase v))
      (X * indepPolyOn G (deleteClosedNeighborSupport G S v)) := by
  rw [deleteClosedNeighborSupport_eq_erase_of_neighborSetOn_empty G hneighbor]
  exact compatible_indepPolyOn_X_mul_self_of_splits G (S.erase v) hSplit

/-- Weighted no-neighbor case of the vertex-deletion compatibility lemma. -/
theorem compatible_weightedIndepPolyOn_erase_X_mul_deleteClosedNeighborSupport_of_no_neighbors
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    {S : Finset V} {v : V} (hneighbor : neighborSetOn G (S.erase v) v = ∅)
    (hSplit : (weightedIndepPolyOn G (S.erase v) wt).Splits) :
    Compatible (weightedIndepPolyOn G (S.erase v) wt)
      (X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S v) wt) := by
  rw [deleteClosedNeighborSupport_eq_erase_of_neighborSetOn_empty G hneighbor]
  exact compatible_weightedIndepPolyOn_X_mul_self_of_splits
    G (S.erase v) wt hSplit

/-- If `u` is adjacent to `v`, then erasing `v` before deleting the closed
neighborhood of `u` does not change the deletion support. -/
theorem deleteClosedNeighborSupport_erase_eq_of_adj {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {u v : V} (huv : G.Adj u v) :
    deleteClosedNeighborSupport G (S.erase v) u =
      deleteClosedNeighborSupport G S u := by
  ext w
  by_cases hwv : w = v
  · subst w
    simp [deleteClosedNeighborSupport, huv]
  · simp [deleteClosedNeighborSupport, hwv]

/-- Deleting the remaining neighbors of `u` after removing the common closed
neighborhood of adjacent `u` and `v` is the same support as deleting the closed
neighborhood of `u` from the original support. -/
theorem sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {u v : V} (huv : G.Adj u v) :
    (S \ commonClosedNeighborSetOn G S u v) \
        neighborSetOn G (S \ commonClosedNeighborSetOn G S u v) u =
      deleteClosedNeighborSupport G S u := by
  ext w
  constructor
  · intro hw
    have hw' := Finset.mem_sdiff.mp hw
    have hwH' := Finset.mem_sdiff.mp hw'.1
    have hwu : w ≠ u := by
      intro hwu
      have hwCommon : w ∈ commonClosedNeighborSetOn G S u v := by
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_filter.mpr ⟨hwH'.1, Or.inl hwu⟩,
            Finset.mem_filter.mpr ⟨hwH'.1, Or.inr (hwu ▸ huv.symm)⟩⟩
      simp_all
    have hnotAdj : ¬ G.Adj u w := by
      intro huw
      exact hw'.2 (Finset.mem_filter.mpr ⟨hw'.1, huw⟩)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hwu, hwH'.1⟩, hnotAdj⟩
  · intro hwDel
    have hwFilter := Finset.mem_filter.mp hwDel
    have hwErase := Finset.mem_erase.mp hwFilter.1
    have hwS : w ∈ S := hwErase.2
    have hwu : w ≠ u := hwErase.1
    have hnotAdj : ¬ G.Adj u w := hwFilter.2
    have hwNotCommon : w ∉ commonClosedNeighborSetOn G S u v := by
      intro hwCommon
      have hwClosedU := (Finset.mem_inter.mp hwCommon).1
      rcases (Finset.mem_filter.mp hwClosedU).2 with hwu' | huw <;> simp_all
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hwS, hwNotCommon⟩, ?_⟩
    intro hwNeighbor
    exact hnotAdj (Finset.mem_filter.mp hwNeighbor).2

/-- Symmetric version of
`sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport`. -/
theorem sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport_right
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {u v : V} (huv : G.Adj u v) :
    (S \ commonClosedNeighborSetOn G S u v) \
        neighborSetOn G (S \ commonClosedNeighborSetOn G S u v) v =
      deleteClosedNeighborSupport G S v := by
  simpa [commonClosedNeighborSetOn, inter_comm] using
    sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport
      G (S := S) huv.symm

/-- For a vertex in a clique, deleting its closed neighborhood from the ambient
support is the same as first deleting the clique, then deleting the outside
neighbors of that vertex. -/
theorem deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S K : Finset V} {k : V} (hK : G.IsClique (K : Set V))
    (hKS : K ⊆ S) (hk : k ∈ K) :
    deleteClosedNeighborSupport G S k =
      (S \ K) \ neighborOutsideCliqueOn G S K k := by
  ext w
  by_cases hwS : w ∈ S
  · by_cases hwK : w ∈ K
    · by_cases hwk : w = k
      · subst w
        simp [deleteClosedNeighborSupport, neighborOutsideCliqueOn, neighborSetOn, hk]
      · have hkw : G.Adj k w :=
          hK (by grind) (by grind) (fun h ↦ hwk h.symm)
        simp [deleteClosedNeighborSupport, neighborOutsideCliqueOn, neighborSetOn,
          hwS, hwK, hwk, hkw]
    · by_cases hAdj : G.Adj k w
      · simp [deleteClosedNeighborSupport, neighborOutsideCliqueOn, neighborSetOn,
          hwS, hwK, hAdj]
      · have hwk : w ≠ k := fun h ↦ hwK (by simp_all)
        simp [deleteClosedNeighborSupport, neighborOutsideCliqueOn, neighborSetOn,
          hwS, hwK, hAdj, hwk]
  · have hwK : w ∉ K := fun h ↦ hwS (hKS h)
    simp [deleteClosedNeighborSupport, neighborOutsideCliqueOn, neighborSetOn, hwS, hwK]

/-- If `v` is adjacent to a clique vertex `x`, then removing `v` from the
ambient support does not change the support left after deleting the closed
neighborhood of `x`. -/
theorem deleteClosedNeighborSupport_erase_eq_of_clique {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S K : Finset V} {v x : V}
    (hK : G.IsClique ((insert v K : Finset V) : Set V))
    (hvK : v ∉ K) (hx : x ∈ K) :
    deleteClosedNeighborSupport G (S.erase v) x =
      deleteClosedNeighborSupport G S x := by
  ext w
  by_cases hwv : w = v
  · subst w
    have hx_ne : x ≠ v := fun hxv ↦ hvK (by simp_all)
    have hxv_adj : G.Adj x v := hK (by simp [hx]) (by simp) hx_ne
    simp [deleteClosedNeighborSupport, hxv_adj]
  · simp [deleteClosedNeighborSupport, hwv]

/-- Chudnovsky--Seymour's clique deletion expansion, in finite-support form.
An independent set can meet a clique in at most one vertex, so the independence
polynomial splits into the sets avoiding the clique and the sets containing a
specified clique vertex. -/
theorem indepPolyOn_sdiff_clique {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S) :
    indepPolyOn G S =
      indepPolyOn G (S \ K) +
        ∑ v ∈ K, X * indepPolyOn G (deleteClosedNeighborSupport G S v) := by
  classical
  revert S hK
  refine Finset.induction_on K ?_ ?_
  · simp
  · intro v K hvK ih S hK hKS
    have hvS : v ∈ S := hKS (Finset.mem_insert_self v K)
    have hK_old : G.IsClique (K : Set V) := by simp_all
    have hKS_old : K ⊆ S.erase v := by
      intro w hw
      refine Finset.mem_erase.mpr ⟨?_, hKS (Finset.mem_insert.mpr (Or.inr hw))⟩
      exact fun hwv ↦ hvK (by simp_all)
    rw [indepPolyOn_erase G hvS, ih (S.erase v) hK_old hKS_old]
    have hsdiff : S.erase v \ K = S \ insert v K := by
      ext w
      by_cases hwv : w = v <;> simp [Finset.mem_sdiff, hwv]
    rw [hsdiff, Finset.sum_insert hvK]
    have hsum :
        (∑ x ∈ K, X * indepPolyOn G (deleteClosedNeighborSupport G (S.erase v) x)) =
          ∑ x ∈ K, X * indepPolyOn G (deleteClosedNeighborSupport G S x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [deleteClosedNeighborSupport_erase_eq_of_clique G hK hvK hx]
    rw [hsum]
    ring_nf

/-- Weighted clique-deletion expansion.  The weight of a chosen clique vertex
appears as the scalar on its closed-neighborhood deletion term. -/
theorem weightedIndepPolyOn_sdiff_clique {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S) :
    weightedIndepPolyOn G S wt =
      weightedIndepPolyOn G (S \ K) wt +
        ∑ v ∈ K, C (wt v) * X *
          weightedIndepPolyOn G (deleteClosedNeighborSupport G S v) wt := by
  classical
  revert S hK
  refine Finset.induction_on K ?_ ?_
  · simp
  · intro v K hvK ih S hK hKS
    have hvS : v ∈ S := hKS (Finset.mem_insert_self v K)
    have hK_old : G.IsClique (K : Set V) := by simp_all
    have hKS_old : K ⊆ S.erase v := by
      intro w hw
      refine Finset.mem_erase.mpr ⟨?_, hKS (Finset.mem_insert.mpr (Or.inr hw))⟩
      exact fun hwv ↦ hvK (by simp_all)
    rw [weightedIndepPolyOn_erase G wt hvS,
      ih (S.erase v) hK_old hKS_old]
    have hsdiff : S.erase v \ K = S \ insert v K := by
      ext w
      by_cases hwv : w = v <;> simp [Finset.mem_sdiff, hwv]
    rw [hsdiff, Finset.sum_insert hvK]
    have hsum :
        (∑ x ∈ K, C (wt x) * X *
            weightedIndepPolyOn G
              (deleteClosedNeighborSupport G (S.erase v) x) wt) =
          ∑ x ∈ K, C (wt x) * X *
            weightedIndepPolyOn G (deleteClosedNeighborSupport G S x) wt := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [deleteClosedNeighborSupport_erase_eq_of_clique G hK hvK hx]
    rw [hsum]
    have hsum_swap :
        (∑ x ∈ K, C (wt x) * X *
            weightedIndepPolyOn G (deleteClosedNeighborSupport G S x) wt) =
          ∑ x ∈ K, X * C (wt x) *
            weightedIndepPolyOn G (deleteClosedNeighborSupport G S x) wt := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [mul_comm (C (wt x)) X]
    rw [hsum_swap]
    ring

/-- The weighted clique-deletion family, before the vertex weights are applied
as coefficients in a `weightedSum`. -/
def weightedCliqueDeletionFamily {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) : List ℝ[X] :=
  weightedIndepPolyOn G (S \ K) wt ::
    K.toList.map fun v =>
      X * weightedIndepPolyOn G (deleteClosedNeighborSupport G S v) wt

/-- The actual weighted combination associated with clique deletion. -/
def weightedCliqueDeletionExpansion {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) : List (ℝ × ℝ[X]) :=
  (1, weightedIndepPolyOn G (S \ K) wt) ::
    K.toList.map fun v =>
      (wt v, X * weightedIndepPolyOn G (deleteClosedNeighborSupport G S v) wt)

/-- Forgetting the scalar coefficients in the clique-deletion combination
recovers its polynomial family. -/
theorem weightedCliqueDeletionExpansion_map_snd
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) :
    (weightedCliqueDeletionExpansion G wt S K).map Prod.snd =
      weightedCliqueDeletionFamily G wt S K := by
  simp [weightedCliqueDeletionExpansion, weightedCliqueDeletionFamily]

/-- The weighted sum of the clique-deletion combination is the original
weighted independence polynomial. -/
theorem weightedCliqueDeletionExpansion_weightedSum
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S) :
    weightedSum (weightedCliqueDeletionExpansion G wt S K) =
      weightedIndepPolyOn G S wt := by
  classical
  have htail :
      weightedSum (K.toList.map fun v =>
          (wt v, X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G S v) wt)) =
        ∑ v ∈ K, C (wt v) * X *
          weightedIndepPolyOn G (deleteClosedNeighborSupport G S v) wt := by
    have hlist : ∀ l : List V,
        weightedSum (l.map fun v =>
            (wt v, X * weightedIndepPolyOn G
              (deleteClosedNeighborSupport G S v) wt)) =
          (l.map fun v => C (wt v) * X *
            weightedIndepPolyOn G
              (deleteClosedNeighborSupport G S v) wt).sum := by
      intro l
      induction l with
      | nil => simp
      | cons v l ih => simp [ih, mul_assoc]
    rw [hlist]
    simp
  unfold weightedCliqueDeletionExpansion
  rw [weightedSum_cons, htail]
  simpa using (weightedIndepPolyOn_sdiff_clique G wt S K hK hKS).symm

/-- The finite family in the clique-deletion expansion of `indepPolyOn G S`. -/
def cliqueDeletionFamily {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) : List ℝ[X] :=
  indepPolyOn G (S \ K) ::
    K.toList.map fun v => X * indepPolyOn G (deleteClosedNeighborSupport G S v)

/-- The list form of the clique-deletion expansion. -/
theorem cliqueDeletionFamily_sum {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S) :
    (cliqueDeletionFamily G S K).sum = indepPolyOn G S := by
  have hsum :
      (K.toList.map fun v =>
          X * indepPolyOn G (deleteClosedNeighborSupport G S v)).sum =
        ∑ v ∈ K, X * indepPolyOn G (deleteClosedNeighborSupport G S v) := by
    simp
  simp [cliqueDeletionFamily, hsum, indepPolyOn_sdiff_clique G S K hK hKS]

private theorem compatible_add_C_mul_left_of_pairwiseCompatible_three
    {a b c : ℝ[X]} {r : ℝ} (hr : 0 ≤ r)
    (ha : a ≠ 0 ∧ a.Splits) (hb : b ≠ 0 ∧ b.Splits) (hc : c ≠ 0 ∧ c.Splits)
    (hapos : HasPosLeadingCoeff a) (hbpos : HasPosLeadingCoeff b)
    (hcpos : HasPosLeadingCoeff c) (hann : HasNonnegCoeffs a)
    (hbnn : HasNonnegCoeffs b) (hcnn : HasNonnegCoeffs c)
    (hab : Compatible a b) (hac : Compatible a c) (hbc : Compatible b c) :
    Compatible (a + C r * b) c := by
  let fs : List ℝ[X] := [a, b, c]
  have hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits := by
    intro f hf
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> simp_all
  have hpos : ∀ f ∈ fs, HasPosLeadingCoeff f := by
    intro f hf
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact hapos
    · exact hbpos
    · exact hcpos
  have hnn : ∀ f ∈ fs, HasNonnegCoeffs f := by
    intro f hf
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact hann
    · exact hbnn
    · exact hcnn
  have hpair : PairwiseCompatible fs := by
    apply pairwiseCompatible_of_forall_mem
    intro f hf g hg
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hf hg
    rcases hf with rfl | rfl | rfl <;> rcases hg with rfl | rfl | rfl
    · exact compatible_self_of_splits ha.1 ha.2
    · exact hab
    · exact hac
    · exact hab.comm
    · exact compatible_self_of_splits hb.1 hb.2
    · exact hbc
    · exact hac.comm
    · exact hbc.comm
    · exact compatible_self_of_splits hc.1 hc.2
  have hfam : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      (fs := fs) hrr hpos hnn).1 hpair
  intro α β hα hβ
  let ws : List (ℝ × ℝ[X]) := [(α, a), (α * r, b), (β, c)]
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hap
    rcases hap with rfl | rfl | rfl <;> simp [fs]
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hap
    rcases hap with rfl | rfl | rfl
    · exact hα
    · exact mul_nonneg hα hr
    · exact hβ
  have hsum : weightedSum ws = C α * (a + C r * b) + C β * c := by
    simp only [ws, weightedSum_cons, weightedSum_nil]
    rw [map_mul]
    ring
  simpa [hsum] using hfam ws hmem hnonneg

private theorem compatible_add_left_of_pairwiseCompatible_three {a b c : ℝ[X]}
    (ha : a ≠ 0 ∧ a.Splits) (hb : b ≠ 0 ∧ b.Splits) (hc : c ≠ 0 ∧ c.Splits)
    (hapos : HasPosLeadingCoeff a) (hbpos : HasPosLeadingCoeff b)
    (hcpos : HasPosLeadingCoeff c) (hann : HasNonnegCoeffs a)
    (hbnn : HasNonnegCoeffs b) (hcnn : HasNonnegCoeffs c)
    (hab : Compatible a b) (hac : Compatible a c) (hbc : Compatible b c) :
    Compatible (a + b) c := by
  simpa using compatible_add_C_mul_left_of_pairwiseCompatible_three
    (r := 1) zero_le_one ha hb hc hapos hbpos hcpos hann hbnn hcnn hab hac hbc

/-- Pairwise compatibility of the clique-deletion family follows from the two
compatibility obligations appearing in Chudnovsky--Seymour Lemma 2.5. -/
theorem cliqueDeletionFamily_pairwiseCompatible_of_compatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S K : Finset V)
    (hbase : (indepPolyOn G (S \ K)).Splits)
    (hbase_del : ∀ v ∈ K,
      Compatible (indepPolyOn G (S \ K))
        (X * indepPolyOn G (deleteClosedNeighborSupport G S v)))
    (hdel_pair : ∀ u ∈ K, ∀ v ∈ K,
      Compatible (indepPolyOn G (deleteClosedNeighborSupport G S u))
        (indepPolyOn G (deleteClosedNeighborSupport G S v))) :
    PairwiseCompatible (cliqueDeletionFamily G S K) := by
  apply pairwiseCompatible_of_forall_mem
  intro f hf g hg
  simp only [cliqueDeletionFamily, List.mem_cons, List.mem_map] at hf hg
  rcases hf with rfl | ⟨u, huList, rfl⟩
  · rcases hg with rfl | ⟨v, hvList, rfl⟩
    · exact compatible_self_of_splits (indepPolyOn_ne_zero G (S \ K)) hbase
    · simp_all
  · rcases hg with rfl | ⟨v, hvList, rfl⟩
    · exact (hbase_del u (Finset.mem_toList.mp huList)).comm
    · exact compatible_X_mul_of_compatible
        (hdel_pair u (Finset.mem_toList.mp huList) v (Finset.mem_toList.mp hvList))

/-- Pairwise compatibility of the weighted clique-deletion family follows
from the same two recursive compatibility obligations as in the unweighted
case. -/
theorem weightedCliqueDeletionFamily_pairwiseCompatible_of_compatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V)
    (hbase : (weightedIndepPolyOn G (S \ K) wt).Splits)
    (hbase_del : ∀ v ∈ K,
      Compatible (weightedIndepPolyOn G (S \ K) wt)
        (X * weightedIndepPolyOn G
          (deleteClosedNeighborSupport G S v) wt))
    (hdel_pair : ∀ u ∈ K, ∀ v ∈ K,
      Compatible
        (weightedIndepPolyOn G (deleteClosedNeighborSupport G S u) wt)
        (weightedIndepPolyOn G (deleteClosedNeighborSupport G S v) wt)) :
    PairwiseCompatible (weightedCliqueDeletionFamily G wt S K) := by
  apply pairwiseCompatible_of_forall_mem
  intro f hf g hg
  simp only [weightedCliqueDeletionFamily, List.mem_cons, List.mem_map] at hf hg
  rcases hf with rfl | ⟨u, huList, rfl⟩
  · rcases hg with rfl | ⟨v, hvList, rfl⟩
    · exact compatible_self_of_splits
        (weightedIndepPolyOn_ne_zero G (S \ K) wt) hbase
    · exact hbase_del v (Finset.mem_toList.mp hvList)
  · rcases hg with rfl | ⟨v, hvList, rfl⟩
    · exact (hbase_del u (Finset.mem_toList.mp huList)).comm
    · exact compatible_X_mul_of_compatible
        (hdel_pair u (Finset.mem_toList.mp huList)
          v (Finset.mem_toList.mp hvList))

/-- Pairwise compatibility of the clique-deletion family can be proved on the
recursive supports produced by the outside-neighbor cliques. -/
theorem cliqueDeletionFamily_pairwiseCompatible_of_neighborOutside_compatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {S K : Finset V}
    (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S)
    (hbase : (indepPolyOn G (S \ K)).Splits)
    (hbase_neighbor : ∀ v ∈ K,
      Compatible (indepPolyOn G (S \ K))
        (X * indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)))
    (hneighbor_pair : ∀ u ∈ K, ∀ v ∈ K,
      Compatible (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K u))
        (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v))) :
    PairwiseCompatible (cliqueDeletionFamily G S K) := by
  apply cliqueDeletionFamily_pairwiseCompatible_of_compatible G S K hbase
  · intro v hv
    have hsupport :=
      deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G hK hKS hv
    simp_all
  · intro u hu v hv
    have huSupport :=
      deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G hK hKS hu
    have hvSupport :=
      deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G hK hKS hv
    simp_all

/-- The finite family used to prove compatibility of `I(S)` with
`X * I(S \ K)` in Chudnovsky--Seymour Lemma 2.5.2. -/
def cliqueDeletionCompatibilityFamily {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) : List ℝ[X] :=
  X * indepPolyOn G (S \ K) :: cliqueDeletionFamily G S K

/-- The finite family used to prove compatibility of `I(S \ K)` and
`I(S \ L)` in Chudnovsky--Seymour Lemma 2.5.1. -/
def cliquePairDeletionFamily {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K L : Finset V) : List ℝ[X] :=
  indepPolyOn G (S \ (K ∪ L)) ::
    (((K \ L).toList.map fun v =>
      X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)) ++
    ((L \ K).toList.map fun v =>
      X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)))

/-- The weighted family used to prove compatibility of `I_w(S)` with
`X * I_w(S \ K)`. Vertex weights are applied later as scalar coefficients. -/
def weightedCliqueDeletionCompatibilityFamily
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) : List ℝ[X] :=
  X * weightedIndepPolyOn G (S \ K) wt ::
    weightedCliqueDeletionFamily G wt S K

/-- The weighted family used to prove compatibility of `I_w(S \ K)` and
`I_w(S \ L)`. Vertex weights are applied later as scalar coefficients. -/
def weightedCliquePairDeletionFamily {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K L : Finset V) : List ℝ[X] :=
  weightedIndepPolyOn G (S \ (K ∪ L)) wt ::
    (((K \ L).toList.map fun v =>
      X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G (S \ L) v) wt) ++
    ((L \ K).toList.map fun v =>
      X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G (S \ K) v) wt))

/-- Pairwise compatibility of the weighted extended clique-deletion family
follows from the same recursive compatibility hypotheses as in the unweighted
case. -/
theorem weightedCliqueDeletionCompatibilityFamily_pairwiseCompatible_of_neighborOutside_compatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    {S K : Finset V} (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S)
    (hbase : (weightedIndepPolyOn G (S \ K) wt).Splits)
    (hbase_neighbor_x : ∀ v ∈ K,
      Compatible (weightedIndepPolyOn G (S \ K) wt)
        (X * weightedIndepPolyOn G
          ((S \ K) \ neighborOutsideCliqueOn G S K v) wt))
    (hbase_neighbor : ∀ v ∈ K,
      Compatible (weightedIndepPolyOn G (S \ K) wt)
        (weightedIndepPolyOn G
          ((S \ K) \ neighborOutsideCliqueOn G S K v) wt))
    (hneighbor_pair : ∀ u ∈ K, ∀ v ∈ K,
      Compatible
        (weightedIndepPolyOn G
          ((S \ K) \ neighborOutsideCliqueOn G S K u) wt)
        (weightedIndepPolyOn G
          ((S \ K) \ neighborOutsideCliqueOn G S K v) wt)) :
    PairwiseCompatible
      (weightedCliqueDeletionCompatibilityFamily G wt S K) := by
  apply pairwiseCompatible_of_forall_mem
  intro f hf g hg
  simp only [weightedCliqueDeletionCompatibilityFamily,
    weightedCliqueDeletionFamily, List.mem_cons, List.mem_map] at hf hg
  rcases hf with rfl | rfl | ⟨u, huList, rfl⟩
  · rcases hg with rfl | rfl | ⟨v, hvList, rfl⟩
    · exact compatible_self_of_splits
        (isRealRooted_X_mul
          (weightedIndepPolyOn_ne_zero G (S \ K) wt) hbase).1
        (isRealRooted_X_mul
          (weightedIndepPolyOn_ne_zero G (S \ K) wt) hbase).2
    · exact
        (compatible_weightedIndepPolyOn_X_mul_self_of_splits
          G (S \ K) wt hbase).comm
    · have hvK : v ∈ K := Finset.mem_toList.mp hvList
      have hvSupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G hK hKS hvK
      simpa [hvSupport] using
        compatible_X_mul_of_compatible (hbase_neighbor v hvK)
  · rcases hg with rfl | rfl | ⟨v, hvList, rfl⟩
    · exact compatible_weightedIndepPolyOn_X_mul_self_of_splits
        G (S \ K) wt hbase
    · exact compatible_self_of_splits
        (weightedIndepPolyOn_ne_zero G (S \ K) wt) hbase
    · have hvK : v ∈ K := Finset.mem_toList.mp hvList
      have hvSupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G hK hKS hvK
      simp_all
  · have huK : u ∈ K := Finset.mem_toList.mp huList
    have huSupport :=
      deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
        G hK hKS huK
    rcases hg with rfl | rfl | ⟨v, hvList, rfl⟩
    · simpa [huSupport] using
        (compatible_X_mul_of_compatible (hbase_neighbor u huK)).comm
    · simpa [huSupport] using (hbase_neighbor_x u huK).comm
    · have hvK : v ∈ K := Finset.mem_toList.mp hvList
      have hvSupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G hK hKS hvK
      simpa [huSupport, hvSupport] using
        compatible_X_mul_of_compatible (hneighbor_pair u huK v hvK)

/-- Pairwise compatibility of the extended clique-deletion family follows from
the recursive compatibility hypotheses in Chudnovsky--Seymour Lemma 2.5. -/
theorem cliqueDeletionCompatibilityFamily_pairwiseCompatible_of_neighborOutside_compatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {S K : Finset V}
    (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S)
    (hbase : (indepPolyOn G (S \ K)).Splits)
    (hbase_neighbor_x : ∀ v ∈ K,
      Compatible (indepPolyOn G (S \ K))
        (X * indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)))
    (hbase_neighbor : ∀ v ∈ K,
      Compatible (indepPolyOn G (S \ K))
        (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)))
    (hneighbor_pair : ∀ u ∈ K, ∀ v ∈ K,
      Compatible (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K u))
        (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v))) :
    PairwiseCompatible (cliqueDeletionCompatibilityFamily G S K) := by
  apply pairwiseCompatible_of_forall_mem
  intro f hf g hg
  simp only [cliqueDeletionCompatibilityFamily, cliqueDeletionFamily, List.mem_cons,
    List.mem_map] at hf hg
  rcases hf with rfl | rfl | ⟨u, huList, rfl⟩
  · rcases hg with rfl | rfl | ⟨v, hvList, rfl⟩
    · exact compatible_self_of_splits
        (isRealRooted_X_mul (indepPolyOn_ne_zero G (S \ K)) hbase).1
        (isRealRooted_X_mul (indepPolyOn_ne_zero G (S \ K)) hbase).2
    · exact (compatible_indepPolyOn_X_mul_self_of_splits G (S \ K) hbase).comm
    · have hvK : v ∈ K := Finset.mem_toList.mp hvList
      have hvSupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G hK hKS hvK
      simpa [hvSupport] using compatible_X_mul_of_compatible (hbase_neighbor v hvK)
  · rcases hg with rfl | rfl | ⟨v, hvList, rfl⟩
    · exact compatible_indepPolyOn_X_mul_self_of_splits G (S \ K) hbase
    · exact compatible_self_of_splits (indepPolyOn_ne_zero G (S \ K)) hbase
    · have hvK : v ∈ K := Finset.mem_toList.mp hvList
      have hvSupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G hK hKS hvK
      simp_all
  · have huK : u ∈ K := Finset.mem_toList.mp huList
    have huSupport :=
      deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G hK hKS huK
    rcases hg with rfl | rfl | ⟨v, hvList, rfl⟩
    · simpa [huSupport] using
        (compatible_X_mul_of_compatible (hbase_neighbor u huK)).comm
    · simpa [huSupport] using (hbase_neighbor_x u huK).comm
    · have hvK : v ∈ K := Finset.mem_toList.mp hvList
      have hvSupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G hK hKS hvK
      simpa [huSupport, hvSupport] using
        compatible_X_mul_of_compatible (hneighbor_pair u huK v hvK)

/-- If the clique-deletion family is pairwise compatible, then the support
independence polynomial splits. This is the Chudnovsky--Seymour engine applied
to the finite family from Lemma 2.3. -/
theorem indepPolyOn_splits_of_cliqueDeletion_pairwiseCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S)
    (hbase : (indepPolyOn G (S \ K)).Splits)
    (hdel : ∀ v ∈ K, (indepPolyOn G (deleteClosedNeighborSupport G S v)).Splits)
    (hpair : PairwiseCompatible (cliqueDeletionFamily G S K)) :
    (indepPolyOn G S).Splits := by
  let fs := cliqueDeletionFamily G S K
  have hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits := by
    intro f hf
    change f ∈ cliqueDeletionFamily G S K at hf
    simp only [cliqueDeletionFamily, List.mem_cons, List.mem_map] at hf
    rcases hf with rfl | ⟨v, hvK, rfl⟩
    · exact ⟨indepPolyOn_ne_zero G (S \ K), hbase⟩
    · exact isRealRooted_X_mul
        (indepPolyOn_ne_zero G (deleteClosedNeighborSupport G S v))
        (hdel v (Finset.mem_toList.mp hvK))
  have hpos : ∀ f ∈ fs, HasPosLeadingCoeff f := by
    intro f hf
    change f ∈ cliqueDeletionFamily G S K at hf
    simp only [cliqueDeletionFamily, List.mem_cons, List.mem_map] at hf
    rcases hf with rfl | ⟨v, _hvK, rfl⟩
    · exact indepPolyOn_hasPosLeadingCoeff G (S \ K)
    · exact (indepPolyOn_hasPosLeadingCoeff G
        (deleteClosedNeighborSupport G S v)).X_mul
  have hnn : ∀ f ∈ fs, HasNonnegCoeffs f := by
    intro f hf
    change f ∈ cliqueDeletionFamily G S K at hf
    simp only [cliqueDeletionFamily, List.mem_cons, List.mem_map] at hf
    rcases hf with rfl | ⟨v, _hvK, rfl⟩
    · exact indepPolyOn_hasNonnegCoeffs G (S \ K)
    · exact (indepPolyOn_hasNonnegCoeffs G
        (deleteClosedNeighborSupport G S v)).X_mul
  have hfam : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      (fs := fs) hrr hpos hnn).1 hpair
  have hweighted := hfam (fs.map fun p ↦ ((1 : ℝ), p)) (by
    simp) (by
    simp)
  have hsum : weightedSum (fs.map fun p ↦ ((1 : ℝ), p)) = indepPolyOn G S := by
    rw [weightedSum_map_one]
    exact cliqueDeletionFamily_sum G S K hK hKS
  rw [hsum] at hweighted
  rcases hweighted with hzero | ⟨_, hsplits⟩
  · simp_all
  · exact hsplits

/-- The clique-deletion family also assembles the compatibility of `I(S)` with
`X * I(S \ K)` once the one-extra-term family is pairwise compatible. -/
theorem compatible_indepPolyOn_X_mul_sdiff_of_cliqueDeletion_pairwiseCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S)
    (hbase : (indepPolyOn G (S \ K)).Splits)
    (hdel : ∀ v ∈ K, (indepPolyOn G (deleteClosedNeighborSupport G S v)).Splits)
    (hpair : PairwiseCompatible (cliqueDeletionCompatibilityFamily G S K)) :
    Compatible (indepPolyOn G S) (X * indepPolyOn G (S \ K)) := by
  let fs := cliqueDeletionCompatibilityFamily G S K
  have hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits := by
    intro f hf
    change f ∈ cliqueDeletionCompatibilityFamily G S K at hf
    simp only [cliqueDeletionCompatibilityFamily, List.mem_cons, cliqueDeletionFamily,
      List.mem_map] at hf
    rcases hf with rfl | htail
    · exact isRealRooted_X_mul (indepPolyOn_ne_zero G (S \ K)) hbase
    · rcases htail with rfl | ⟨v, hvK, rfl⟩
      · exact ⟨indepPolyOn_ne_zero G (S \ K), hbase⟩
      · exact isRealRooted_X_mul
          (indepPolyOn_ne_zero G (deleteClosedNeighborSupport G S v))
          (hdel v (Finset.mem_toList.mp hvK))
  have hpos : ∀ f ∈ fs, HasPosLeadingCoeff f := by
    intro f hf
    change f ∈ cliqueDeletionCompatibilityFamily G S K at hf
    simp only [cliqueDeletionCompatibilityFamily, List.mem_cons, cliqueDeletionFamily,
      List.mem_map] at hf
    rcases hf with rfl | htail
    · exact (indepPolyOn_hasPosLeadingCoeff G (S \ K)).X_mul
    · rcases htail with rfl | ⟨v, _hvK, rfl⟩
      · exact indepPolyOn_hasPosLeadingCoeff G (S \ K)
      · exact (indepPolyOn_hasPosLeadingCoeff G
          (deleteClosedNeighborSupport G S v)).X_mul
  have hnn : ∀ f ∈ fs, HasNonnegCoeffs f := by
    intro f hf
    change f ∈ cliqueDeletionCompatibilityFamily G S K at hf
    simp only [cliqueDeletionCompatibilityFamily, List.mem_cons, cliqueDeletionFamily,
      List.mem_map] at hf
    rcases hf with rfl | htail
    · exact (indepPolyOn_hasNonnegCoeffs G (S \ K)).X_mul
    · rcases htail with rfl | ⟨v, _hvK, rfl⟩
      · exact indepPolyOn_hasNonnegCoeffs G (S \ K)
      · exact (indepPolyOn_hasNonnegCoeffs G
          (deleteClosedNeighborSupport G S v)).X_mul
  have hfam : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      (fs := fs) hrr hpos hnn).1 hpair
  intro α β hα hβ
  let ws : List (ℝ × ℝ[X]) :=
    (β, X * indepPolyOn G (S \ K)) ::
      (cliqueDeletionFamily G S K).map fun p => (α, p)
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_cons, List.mem_map] at hap
    rcases hap with rfl | ⟨p, hp, rfl⟩
    · simp [fs, cliqueDeletionCompatibilityFamily]
    · simp [fs, cliqueDeletionCompatibilityFamily, hp]
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_cons, List.mem_map] at hap
    rcases hap with rfl | ⟨_p, _hp, rfl⟩
    · exact hβ
    · exact hα
  have hsum : weightedSum ws =
      C α * indepPolyOn G S + C β * (X * indepPolyOn G (S \ K)) := by
    simp only [ws, weightedSum_cons]
    rw [weightedSum_map_const α (cliqueDeletionFamily G S K)]
    rw [cliqueDeletionFamily_sum G S K hK hKS]
    ring
  simpa [hsum] using hfam ws hmem hnonneg

/-- The weighted clique-deletion family assembles compatibility of `I_w(S)`
with `X * I_w(S \ K)`. -/
theorem compatible_weightedIndepPolyOn_X_mul_sdiff_of_cliqueDeletion_pairwiseCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K : Finset V) (hK : G.IsClique (K : Set V)) (hKS : K ⊆ S)
    (hwt : ∀ v ∈ S, 0 ≤ wt v)
    (hbase : (weightedIndepPolyOn G (S \ K) wt).Splits)
    (hdel : ∀ v ∈ K,
      (weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S v) wt).Splits)
    (hpair : PairwiseCompatible
      (weightedCliqueDeletionCompatibilityFamily G wt S K)) :
    Compatible (weightedIndepPolyOn G S wt)
      (X * weightedIndepPolyOn G (S \ K) wt) := by
  let fs := weightedCliqueDeletionCompatibilityFamily G wt S K
  have hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits := by
    intro f hf
    change f ∈ weightedCliqueDeletionCompatibilityFamily G wt S K at hf
    simp only [weightedCliqueDeletionCompatibilityFamily, List.mem_cons,
      weightedCliqueDeletionFamily, List.mem_map] at hf
    rcases hf with rfl | rfl | ⟨v, hvK, rfl⟩
    · exact isRealRooted_X_mul
        (weightedIndepPolyOn_ne_zero G (S \ K) wt) hbase
    · exact ⟨weightedIndepPolyOn_ne_zero G (S \ K) wt, hbase⟩
    · exact isRealRooted_X_mul
        (weightedIndepPolyOn_ne_zero G
          (deleteClosedNeighborSupport G S v) wt)
        (hdel v (Finset.mem_toList.mp hvK))
  have hpos : ∀ f ∈ fs, HasPosLeadingCoeff f := by
    intro f hf
    change f ∈ weightedCliqueDeletionCompatibilityFamily G wt S K at hf
    simp only [weightedCliqueDeletionCompatibilityFamily, List.mem_cons,
      weightedCliqueDeletionFamily, List.mem_map] at hf
    rcases hf with rfl | rfl | ⟨v, _hvK, rfl⟩
    · exact (weightedIndepPolyOn_hasPosLeadingCoeff G
        (fun v hv => hwt v (Finset.mem_sdiff.mp hv).1)).X_mul
    · exact weightedIndepPolyOn_hasPosLeadingCoeff G
        (fun v hv => hwt v (Finset.mem_sdiff.mp hv).1)
    · exact (weightedIndepPolyOn_hasPosLeadingCoeff G
        (fun w hw => hwt w (deleteClosedNeighborSupport_subset G S v hw))).X_mul
  have hnn : ∀ f ∈ fs, HasNonnegCoeffs f := by
    intro f hf
    change f ∈ weightedCliqueDeletionCompatibilityFamily G wt S K at hf
    simp only [weightedCliqueDeletionCompatibilityFamily, List.mem_cons,
      weightedCliqueDeletionFamily, List.mem_map] at hf
    rcases hf with rfl | rfl | ⟨v, _hvK, rfl⟩
    · exact (weightedIndepPolyOn_hasNonnegCoeffs G
        (fun v hv => hwt v (Finset.mem_sdiff.mp hv).1)).X_mul
    · exact weightedIndepPolyOn_hasNonnegCoeffs G
        (fun v hv => hwt v (Finset.mem_sdiff.mp hv).1)
    · exact (weightedIndepPolyOn_hasNonnegCoeffs G
        (fun w hw => hwt w (deleteClosedNeighborSupport_subset G S v hw))).X_mul
  have hfam : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      (fs := fs) hrr hpos hnn).1 hpair
  intro α β hα hβ
  let expansion := weightedCliqueDeletionExpansion G wt S K
  let ws : List (ℝ × ℝ[X]) :=
    (β, X * weightedIndepPolyOn G (S \ K) wt) ::
      expansion.map fun ap => (α * ap.1, ap.2)
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_cons, List.mem_map] at hap
    rcases hap with rfl | ⟨bp, hbp, rfl⟩
    · simp [fs, weightedCliqueDeletionCompatibilityFamily]
    · change bp.2 ∈ weightedCliqueDeletionCompatibilityFamily G wt S K
      simp only [expansion, weightedCliqueDeletionExpansion,
        List.mem_cons, List.mem_map] at hbp
      rcases hbp with rfl | ⟨v, hv, rfl⟩
      · simp [weightedCliqueDeletionCompatibilityFamily,
          weightedCliqueDeletionFamily]
      · simp only [weightedCliqueDeletionCompatibilityFamily,
          weightedCliqueDeletionFamily, List.mem_cons, List.mem_map]
        exact Or.inr (Or.inr ⟨v, hv, rfl⟩)
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_cons, List.mem_map] at hap
    rcases hap with rfl | ⟨bp, hbp, rfl⟩
    · exact hβ
    · simp only [expansion, weightedCliqueDeletionExpansion,
        List.mem_cons, List.mem_map] at hbp
      rcases hbp with rfl | ⟨v, hv, rfl⟩
      · simpa using hα
      · exact mul_nonneg hα (hwt v (hKS (Finset.mem_toList.mp hv)))
  have hsum : weightedSum ws =
      C α * weightedIndepPolyOn G S wt +
        C β * (X * weightedIndepPolyOn G (S \ K) wt) := by
    simp only [ws, weightedSum_cons]
    rw [weightedSum_map_mul_left α expansion]
    rw [weightedCliqueDeletionExpansion_weightedSum G wt S K hK hKS]
    ring
  simpa [hsum] using hfam ws hmem hnonneg

/-- A pairwise-compatible weighted pair-deletion family assembles
compatibility of the two simplicial-clique deletion polynomials. -/
theorem compatible_weightedIndepPolyOn_sdiff_pair_of_pairDeletion_pairwiseCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ)
    (S K L : Finset V) (hK : G.IsClique (K : Set V))
    (hL : G.IsClique (L : Set V)) (hKS : K ⊆ S) (hLS : L ⊆ S)
    (hwt : ∀ v ∈ S, 0 ≤ wt v)
    (hbase : (weightedIndepPolyOn G (S \ (K ∪ L)) wt).Splits)
    (hKdel : ∀ v ∈ K \ L,
      (weightedIndepPolyOn G
        (deleteClosedNeighborSupport G (S \ L) v) wt).Splits)
    (hLdel : ∀ v ∈ L \ K,
      (weightedIndepPolyOn G
        (deleteClosedNeighborSupport G (S \ K) v) wt).Splits)
    (hpair : PairwiseCompatible
      (weightedCliquePairDeletionFamily G wt S K L)) :
    Compatible (weightedIndepPolyOn G (S \ K) wt)
      (weightedIndepPolyOn G (S \ L) wt) := by
  classical
  let fs := weightedCliquePairDeletionFamily G wt S K L
  have hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits := by
    intro f hf
    change f ∈ weightedCliquePairDeletionFamily G wt S K L at hf
    simp only [weightedCliquePairDeletionFamily, List.mem_cons,
      List.mem_append, List.mem_map] at hf
    rcases hf with rfl | htail
    · exact ⟨weightedIndepPolyOn_ne_zero G (S \ (K ∪ L)) wt, hbase⟩
    · rcases htail with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩
      · exact isRealRooted_X_mul
          (weightedIndepPolyOn_ne_zero G
            (deleteClosedNeighborSupport G (S \ L) v) wt)
          (hKdel v (Finset.mem_toList.mp hvList))
      · exact isRealRooted_X_mul
          (weightedIndepPolyOn_ne_zero G
            (deleteClosedNeighborSupport G (S \ K) v) wt)
          (hLdel v (Finset.mem_toList.mp hvList))
  have hpos : ∀ f ∈ fs, HasPosLeadingCoeff f := by
    intro f hf
    change f ∈ weightedCliquePairDeletionFamily G wt S K L at hf
    simp only [weightedCliquePairDeletionFamily, List.mem_cons,
      List.mem_append, List.mem_map] at hf
    rcases hf with rfl | htail
    · exact weightedIndepPolyOn_hasPosLeadingCoeff G
        (fun v hv => hwt v (Finset.mem_sdiff.mp hv).1)
    · rcases htail with ⟨v, _hvList, rfl⟩ | ⟨v, _hvList, rfl⟩
      · exact (weightedIndepPolyOn_hasPosLeadingCoeff G
          (fun w hw => hwt w ((Finset.mem_sdiff.mp
            (deleteClosedNeighborSupport_subset G (S \ L) v hw)).1))).X_mul
      · exact (weightedIndepPolyOn_hasPosLeadingCoeff G
          (fun w hw => hwt w ((Finset.mem_sdiff.mp
            (deleteClosedNeighborSupport_subset G (S \ K) v hw)).1))).X_mul
  have hnn : ∀ f ∈ fs, HasNonnegCoeffs f := by
    intro f hf
    change f ∈ weightedCliquePairDeletionFamily G wt S K L at hf
    simp only [weightedCliquePairDeletionFamily, List.mem_cons,
      List.mem_append, List.mem_map] at hf
    rcases hf with rfl | htail
    · exact weightedIndepPolyOn_hasNonnegCoeffs G
        (fun v hv => hwt v (Finset.mem_sdiff.mp hv).1)
    · rcases htail with ⟨v, _hvList, rfl⟩ | ⟨v, _hvList, rfl⟩
      · exact (weightedIndepPolyOn_hasNonnegCoeffs G
          (fun w hw => hwt w ((Finset.mem_sdiff.mp
            (deleteClosedNeighborSupport_subset G (S \ L) v hw)).1))).X_mul
      · exact (weightedIndepPolyOn_hasNonnegCoeffs G
          (fun w hw => hwt w ((Finset.mem_sdiff.mp
            (deleteClosedNeighborSupport_subset G (S \ K) v hw)).1))).X_mul
  have hfam : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      (fs := fs) hrr hpos hnn).1 hpair
  have hK_support : (S \ L) \ (K \ L) = S \ (K ∪ L) :=
    by simp [sdiff_sdiff, union_comm]
  have hL_support : (S \ K) \ (L \ K) = S \ (K ∪ L) :=
    by simp [sdiff_sdiff]
  have hK' : G.IsClique ((K \ L : Finset V) : Set V) :=
    hK.subset fun _ hx => (Finset.mem_sdiff.mp hx).1
  have hL' : G.IsClique ((L \ K : Finset V) : Set V) :=
    hL.subset fun _ hx => (Finset.mem_sdiff.mp hx).1
  have hKS' : K \ L ⊆ S \ L := by
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨hKS (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
  have hLS' : L \ K ⊆ S \ K := by
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨hLS (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
  intro α β hα hβ
  let leftExpansion :=
    weightedCliqueDeletionExpansion G wt (S \ K) (L \ K)
  let rightExpansion :=
    weightedCliqueDeletionExpansion G wt (S \ L) (K \ L)
  let ws : List (ℝ × ℝ[X]) :=
    (leftExpansion.map fun ap => (α * ap.1, ap.2)) ++
      (rightExpansion.map fun ap => (β * ap.1, ap.2))
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_append, List.mem_map] at hap
    rcases hap with ⟨bp, hbp, rfl⟩ | ⟨bp, hbp, rfl⟩
    · change bp.2 ∈ weightedCliquePairDeletionFamily G wt S K L
      simp only [leftExpansion, weightedCliqueDeletionExpansion,
        List.mem_cons, List.mem_map] at hbp
      rcases hbp with rfl | ⟨v, hv, rfl⟩
      · simp only [weightedCliquePairDeletionFamily, List.mem_cons]
        exact Or.inl (by rw [hL_support])
      · simp only [weightedCliquePairDeletionFamily, List.mem_cons,
          List.mem_append, List.mem_map]
        exact Or.inr (Or.inr ⟨v, hv, rfl⟩)
    · change bp.2 ∈ weightedCliquePairDeletionFamily G wt S K L
      simp only [rightExpansion, weightedCliqueDeletionExpansion,
        List.mem_cons, List.mem_map] at hbp
      rcases hbp with rfl | ⟨v, hv, rfl⟩
      · simp only [weightedCliquePairDeletionFamily, List.mem_cons]
        exact Or.inl (by rw [hK_support])
      · simp only [weightedCliquePairDeletionFamily, List.mem_cons,
          List.mem_append, List.mem_map]
        exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_append, List.mem_map] at hap
    rcases hap with ⟨bp, hbp, rfl⟩ | ⟨bp, hbp, rfl⟩
    · simp only [leftExpansion, weightedCliqueDeletionExpansion,
        List.mem_cons, List.mem_map] at hbp
      rcases hbp with rfl | ⟨v, hv, rfl⟩
      · simpa using hα
      · exact mul_nonneg hα
          (hwt v (hLS (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).1))
    · simp only [rightExpansion, weightedCliqueDeletionExpansion,
        List.mem_cons, List.mem_map] at hbp
      rcases hbp with rfl | ⟨v, hv, rfl⟩
      · simpa using hβ
      · exact mul_nonneg hβ
          (hwt v (hKS (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).1))
  have hsum : weightedSum ws =
      C α * weightedIndepPolyOn G (S \ K) wt +
        C β * weightedIndepPolyOn G (S \ L) wt := by
    simp only [ws]
    rw [weightedSum_append]
    rw [weightedSum_map_mul_left α leftExpansion,
      weightedSum_map_mul_left β rightExpansion]
    rw [weightedCliqueDeletionExpansion_weightedSum G wt
      (S \ K) (L \ K) hL' hLS']
    rw [weightedCliqueDeletionExpansion_weightedSum G wt
      (S \ L) (K \ L) hK' hKS']
  simpa [hsum] using hfam ws hmem hnonneg

/-- If the pair-deletion family is pairwise compatible, then the two
simplicial-clique deletion polynomials are compatible.  This is the finite
family assembly for Chudnovsky--Seymour Lemma 2.5.1. -/
theorem compatible_indepPolyOn_sdiff_pair_of_pairDeletion_pairwiseCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S K L : Finset V) (hK : G.IsClique (K : Set V))
    (hL : G.IsClique (L : Set V)) (hKS : K ⊆ S) (hLS : L ⊆ S)
    (hbase : (indepPolyOn G (S \ (K ∪ L))).Splits)
    (hKdel : ∀ v ∈ K \ L,
      (indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)).Splits)
    (hLdel : ∀ v ∈ L \ K,
      (indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)).Splits)
    (hpair : PairwiseCompatible (cliquePairDeletionFamily G S K L)) :
    Compatible (indepPolyOn G (S \ K)) (indepPolyOn G (S \ L)) := by
  classical
  let base := indepPolyOn G (S \ (K ∪ L))
  let kTerms : List ℝ[X] :=
    (K \ L).toList.map fun v =>
      X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)
  let lTerms : List ℝ[X] :=
    (L \ K).toList.map fun v =>
      X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)
  let fs := cliquePairDeletionFamily G S K L
  have hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits := by
    intro f hf
    change f ∈ cliquePairDeletionFamily G S K L at hf
    simp only [cliquePairDeletionFamily, List.mem_cons, List.mem_append,
      List.mem_map] at hf
    rcases hf with rfl | htail
    · exact ⟨indepPolyOn_ne_zero G (S \ (K ∪ L)), hbase⟩
    · rcases htail with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩
      · exact isRealRooted_X_mul
          (indepPolyOn_ne_zero G (deleteClosedNeighborSupport G (S \ L) v))
          (hKdel v (Finset.mem_toList.mp hvList))
      · exact isRealRooted_X_mul
          (indepPolyOn_ne_zero G (deleteClosedNeighborSupport G (S \ K) v))
          (hLdel v (Finset.mem_toList.mp hvList))
  have hpos : ∀ f ∈ fs, HasPosLeadingCoeff f := by
    intro f hf
    change f ∈ cliquePairDeletionFamily G S K L at hf
    simp only [cliquePairDeletionFamily, List.mem_cons, List.mem_append,
      List.mem_map] at hf
    rcases hf with rfl | htail
    · exact indepPolyOn_hasPosLeadingCoeff G (S \ (K ∪ L))
    · rcases htail with ⟨v, _hvList, rfl⟩ | ⟨v, _hvList, rfl⟩
      · exact (indepPolyOn_hasPosLeadingCoeff G
          (deleteClosedNeighborSupport G (S \ L) v)).X_mul
      · exact (indepPolyOn_hasPosLeadingCoeff G
          (deleteClosedNeighborSupport G (S \ K) v)).X_mul
  have hnn : ∀ f ∈ fs, HasNonnegCoeffs f := by
    intro f hf
    change f ∈ cliquePairDeletionFamily G S K L at hf
    simp only [cliquePairDeletionFamily, List.mem_cons, List.mem_append,
      List.mem_map] at hf
    rcases hf with rfl | htail
    · exact indepPolyOn_hasNonnegCoeffs G (S \ (K ∪ L))
    · rcases htail with ⟨v, _hvList, rfl⟩ | ⟨v, _hvList, rfl⟩
      · exact (indepPolyOn_hasNonnegCoeffs G
          (deleteClosedNeighborSupport G (S \ L) v)).X_mul
      · exact (indepPolyOn_hasNonnegCoeffs G
          (deleteClosedNeighborSupport G (S \ K) v)).X_mul
  have hfam : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      (fs := fs) hrr hpos hnn).1 hpair
  have hK_support : (S \ L) \ (K \ L) = S \ (K ∪ L) :=
    by simp [sdiff_sdiff, union_comm]
  have hL_support : (S \ K) \ (L \ K) = S \ (K ∪ L) :=
    by simp [sdiff_sdiff]
  have hK_terms :
      kTerms.sum =
        ∑ v ∈ K \ L, X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v) := by
    rw [Finset.sum_eq_multiset_sum]
    simp [kTerms, Finset.toList]
  have hL_terms :
      lTerms.sum =
        ∑ v ∈ L \ K, X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v) := by
    rw [Finset.sum_eq_multiset_sum]
    simp [lTerms, Finset.toList]
  have hKsum : indepPolyOn G (S \ L) = base + kTerms.sum := by
    have hK' : G.IsClique ((K \ L : Finset V) : Set V) :=
      hK.subset fun _ hx => (Finset.mem_sdiff.mp hx).1
    have hKS' : K \ L ⊆ S \ L := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hKS (Finset.mem_sdiff.mp hx).1,
        (Finset.mem_sdiff.mp hx).2⟩
    have h := indepPolyOn_sdiff_clique G (S \ L) (K \ L) hK' hKS'
    rw [hK_support, ← hK_terms] at h
    simpa [base] using h
  have hLsum : indepPolyOn G (S \ K) = base + lTerms.sum := by
    have hL' : G.IsClique ((L \ K : Finset V) : Set V) :=
      hL.subset fun _ hx => (Finset.mem_sdiff.mp hx).1
    have hLS' : L \ K ⊆ S \ K := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hLS (Finset.mem_sdiff.mp hx).1,
        (Finset.mem_sdiff.mp hx).2⟩
    have h := indepPolyOn_sdiff_clique G (S \ K) (L \ K) hL' hLS'
    rw [hL_support, ← hL_terms] at h
    simpa [base] using h
  intro α β hα hβ
  let ws : List (ℝ × ℝ[X]) :=
    (α + β, base) ::
      ((kTerms.map fun p => (β, p)) ++
      (lTerms.map fun p => (α, p)))
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_cons, List.mem_append, List.mem_map] at hap
    change ap.2 ∈ cliquePairDeletionFamily G S K L
    simp only [cliquePairDeletionFamily, List.mem_cons, List.mem_append, List.mem_map]
    rcases hap with rfl | htail
    · exact Or.inl rfl
    · rcases htail with hKterm | hLterm
      · rcases hKterm with ⟨p, hp, rfl⟩
        rcases List.mem_map.mp hp with ⟨v, hvList, rfl⟩
        exact Or.inr (Or.inl ⟨v, hvList, rfl⟩)
      · rcases hLterm with ⟨p, hp, rfl⟩
        rcases List.mem_map.mp hp with ⟨v, hvList, rfl⟩
        exact Or.inr (Or.inr ⟨v, hvList, rfl⟩)
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_cons, List.mem_append, List.mem_map] at hap
    rcases hap with rfl | htail
    · exact add_nonneg hα hβ
    · rcases htail with hKterm | hLterm
      · rcases hKterm with ⟨_p, _hp, rfl⟩
        exact hβ
      · rcases hLterm with ⟨_p, _hp, rfl⟩
        exact hα
  have hsum : weightedSum ws =
      C α * indepPolyOn G (S \ K) + C β * indepPolyOn G (S \ L) := by
    simp only [ws, weightedSum_cons]
    rw [weightedSum_append]
    rw [weightedSum_map_const β kTerms, weightedSum_map_const α lTerms]
    rw [hKsum, hLsum]
    rw [C_add, add_mul]
    ring
  simpa [hsum] using hfam ws hmem hnonneg

/-- On a support `S`, all support-restricted independence polynomials on
subsupports of `S` split. -/
def SupportIndepPolySplits {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ T : Finset V, T ⊆ S → (indepPolyOn G T).Splits

/-- Pair-compatibility invariant from Chudnovsky--Seymour Lemma 2.5.1 on a
finite support. -/
def SupportSimplicialPairCompatible {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ {K L : Finset V}, IsSimplicialCliqueOn G S K → IsSimplicialCliqueOn G S L →
    Compatible (indepPolyOn G (S \ K)) (indepPolyOn G (S \ L))

/-- Self/shift compatibility invariant from Chudnovsky--Seymour Lemma 2.5.2 on
finite supports. -/
def SupportSimplicialXCompatible {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ {K : Finset V}, IsSimplicialCliqueOn G S K →
    Compatible (indepPolyOn G S) (X * indepPolyOn G (S \ K))

/-- Vertex-deletion compatibility invariant from Chudnovsky--Seymour Lemma 2.6
on a finite support. -/
def SupportVertexDeletionCompatible {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ {v : V}, v ∈ S →
    Compatible (indepPolyOn G (S.erase v))
      (X * indepPolyOn G (deleteClosedNeighborSupport G S v))

/-- On a support `S`, all weighted support-restricted independence polynomials
on subsupports of `S` split. -/
def WeightedSupportIndepPolySplits {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (wt : V → ℝ) (S : Finset V) : Prop :=
  ∀ T : Finset V, T ⊆ S → (weightedIndepPolyOn G T wt).Splits

/-- Weighted pair-compatibility invariant on a finite support. -/
def WeightedSupportSimplicialPairCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (wt : V → ℝ) (S : Finset V) : Prop :=
  ∀ {K L : Finset V},
    IsSimplicialCliqueOn G S K → IsSimplicialCliqueOn G S L →
      Compatible (weightedIndepPolyOn G (S \ K) wt)
        (weightedIndepPolyOn G (S \ L) wt)

/-- Weighted self/shift compatibility invariant on a finite support. -/
def WeightedSupportSimplicialXCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (wt : V → ℝ) (S : Finset V) : Prop :=
  ∀ {K : Finset V}, IsSimplicialCliqueOn G S K →
    Compatible (weightedIndepPolyOn G S wt)
      (X * weightedIndepPolyOn G (S \ K) wt)

/-- Weighted vertex-deletion compatibility invariant on a finite support. -/
def WeightedSupportVertexDeletionCompatible
    {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (wt : V → ℝ) (S : Finset V) : Prop :=
  ∀ {v : V}, v ∈ S →
    Compatible (weightedIndepPolyOn G (S.erase v) wt)
      (X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S v) wt)

/-- The pair of closed-neighborhood deletion terms appearing in
Chudnovsky--Seymour Lemma 2.6 is compatible once Lemma 2.5.1 is available on
the support obtained by deleting the common closed neighborhood of adjacent
vertices. -/
theorem compatible_X_mul_deleteClosedNeighborSupport_pair_of_commonClosedNeighbor
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} {u v : V} (huv : G.Adj u v)
    (hPair : SupportSimplicialPairCompatible G
      (S \ commonClosedNeighborSetOn G S u v)) :
    Compatible
      (X * indepPolyOn G (deleteClosedNeighborSupport G S u))
      (X * indepPolyOn G (deleteClosedNeighborSupport G S v)) := by
  let H := S \ commonClosedNeighborSetOn G S u v
  have hKu : IsSimplicialCliqueOn G H (neighborSetOn G H u) :=
    hG.neighborSetOn_sdiff_commonClosedNeighbor_simplicial huv
  have hKv : IsSimplicialCliqueOn G H (neighborSetOn G H v) :=
    hG.neighborSetOn_sdiff_commonClosedNeighbor_simplicial_right huv
  have hp := hPair hKu hKv
  have huSupport :
      H \ neighborSetOn G H u = deleteClosedNeighborSupport G S u := by
    exact sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport
      G huv
  have hvSupport :
      H \ neighborSetOn G H v = deleteClosedNeighborSupport G S v := by
    exact sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport_right
      G huv
  simpa [H, huSupport, hvSupport] using compatible_X_mul_of_compatible hp

/-- Weighted version of the common-closed-neighborhood compatibility bridge. -/
theorem compatible_weighted_deleteClosedNeighborSupport_pair_of_commonClosedNeighbor
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (wt : V → ℝ) {S : Finset V} {u v : V} (huv : G.Adj u v)
    (hPair : WeightedSupportSimplicialPairCompatible G wt
      (S \ commonClosedNeighborSetOn G S u v)) :
    Compatible
      (X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S u) wt)
      (X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S v) wt) := by
  let H := S \ commonClosedNeighborSetOn G S u v
  have hKu : IsSimplicialCliqueOn G H (neighborSetOn G H u) :=
    hG.neighborSetOn_sdiff_commonClosedNeighbor_simplicial huv
  have hKv : IsSimplicialCliqueOn G H (neighborSetOn G H v) :=
    hG.neighborSetOn_sdiff_commonClosedNeighbor_simplicial_right huv
  have hp := hPair hKu hKv
  have huSupport :
      H \ neighborSetOn G H u = deleteClosedNeighborSupport G S u := by
    exact
      sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport
        G huv
  have hvSupport :
      H \ neighborSetOn G H v = deleteClosedNeighborSupport G S v := by
    exact
      sdiff_commonClosedNeighbor_sdiff_neighborSetOn_eq_deleteClosedNeighborSupport_right
        G huv
  simpa [H, huSupport, hvSupport] using compatible_X_mul_of_compatible hp

/-- The adjacent-neighbor case of Chudnovsky--Seymour Lemma 2.6.  Expanding
`I(S.erase v)` at an adjacent vertex `u` reduces compatibility with
`X * I(S \ N[v])` to the two smaller vertex-deletion compatibility inputs and
the Lemma 2.5.1 common-closed-neighborhood bridge. -/
theorem compatible_erase_X_mul_deleteClosedNeighborSupport_of_adjacent
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} {u v : V} (huS : u ∈ S.erase v) (huv : G.Adj u v)
    (hBaseSplit : (indepPolyOn G ((S.erase v).erase u)).Splits)
    (hDelUSplit : (indepPolyOn G (deleteClosedNeighborSupport G S u)).Splits)
    (hDelVSplit : (indepPolyOn G (deleteClosedNeighborSupport G S v)).Splits)
    (hBaseDelU : Compatible (indepPolyOn G ((S.erase v).erase u))
      (X * indepPolyOn G (deleteClosedNeighborSupport G S u)))
    (hBaseDelV : Compatible (indepPolyOn G ((S.erase v).erase u))
      (X * indepPolyOn G (deleteClosedNeighborSupport G S v)))
    (hPair : SupportSimplicialPairCompatible G
      (S \ commonClosedNeighborSetOn G S u v)) :
    Compatible (indepPolyOn G (S.erase v))
      (X * indepPolyOn G (deleteClosedNeighborSupport G S v)) := by
  let A := indepPolyOn G ((S.erase v).erase u)
  let B := X * indepPolyOn G (deleteClosedNeighborSupport G S u)
  let C := X * indepPolyOn G (deleteClosedNeighborSupport G S v)
  have hrec : indepPolyOn G (S.erase v) = A + B := by
    have h := indepPolyOn_erase (G := G) (S := S.erase v) (v := u) huS
    have hsupport :
        deleteClosedNeighborSupport G (S.erase v) u =
          deleteClosedNeighborSupport G S u :=
      deleteClosedNeighborSupport_erase_eq_of_adj G huv
    simpa [A, B, hsupport] using h
  have hA : A ≠ 0 ∧ A.Splits := by exact ⟨indepPolyOn_ne_zero G ((S.erase v).erase u), hBaseSplit⟩
  have hB : B ≠ 0 ∧ B.Splits := by
    dsimp [B]
    exact isRealRooted_X_mul
      (indepPolyOn_ne_zero G (deleteClosedNeighborSupport G S u)) hDelUSplit
  have hC : C ≠ 0 ∧ C.Splits := by
    dsimp [C]
    exact isRealRooted_X_mul
      (indepPolyOn_ne_zero G (deleteClosedNeighborSupport G S v)) hDelVSplit
  have hApos : HasPosLeadingCoeff A := by
    dsimp [A]
    exact indepPolyOn_hasPosLeadingCoeff G ((S.erase v).erase u)
  have hBpos : HasPosLeadingCoeff B := by
    dsimp [B]
    exact (indepPolyOn_hasPosLeadingCoeff G (deleteClosedNeighborSupport G S u)).X_mul
  have hCpos : HasPosLeadingCoeff C := by
    dsimp [C]
    exact (indepPolyOn_hasPosLeadingCoeff G (deleteClosedNeighborSupport G S v)).X_mul
  have hAnn : HasNonnegCoeffs A := by
    dsimp [A]
    exact indepPolyOn_hasNonnegCoeffs G ((S.erase v).erase u)
  have hBnn : HasNonnegCoeffs B := by
    dsimp [B]
    exact (indepPolyOn_hasNonnegCoeffs G (deleteClosedNeighborSupport G S u)).X_mul
  have hCnn : HasNonnegCoeffs C := by
    dsimp [C]
    exact (indepPolyOn_hasNonnegCoeffs G (deleteClosedNeighborSupport G S v)).X_mul
  have hBC : Compatible B C := by
    simpa [B, C] using
      compatible_X_mul_deleteClosedNeighborSupport_pair_of_commonClosedNeighbor hG huv hPair
  have hABC : Compatible (A + B) C :=
    compatible_add_left_of_pairwiseCompatible_three
      hA hB hC hApos hBpos hCpos hAnn hBnn hCnn
      (by simpa [A, B] using hBaseDelU)
      (by simpa [A, C] using hBaseDelV)
      hBC
  simpa [hrec, A, B, C] using hABC

/-- Weighted adjacent-neighbor case of the vertex-deletion compatibility
lemma. The recurrence coefficient is the weight of the expanded vertex. -/
theorem compatible_weighted_erase_X_mul_deleteClosedNeighborSupport_of_adjacent
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (wt : V → ℝ) {S : Finset V} {u v : V}
    (hwt : ∀ w ∈ S, 0 ≤ wt w) (huS : u ∈ S.erase v) (huv : G.Adj u v)
    (hBaseSplit :
      (weightedIndepPolyOn G ((S.erase v).erase u) wt).Splits)
    (hDelUSplit :
      (weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S u) wt).Splits)
    (hDelVSplit :
      (weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S v) wt).Splits)
    (hBaseDelU :
      Compatible (weightedIndepPolyOn G ((S.erase v).erase u) wt)
        (X * weightedIndepPolyOn G
          (deleteClosedNeighborSupport G S u) wt))
    (hBaseDelV :
      Compatible (weightedIndepPolyOn G ((S.erase v).erase u) wt)
        (X * weightedIndepPolyOn G
          (deleteClosedNeighborSupport G S v) wt))
    (hPair : WeightedSupportSimplicialPairCompatible G wt
      (S \ commonClosedNeighborSetOn G S u v)) :
    Compatible (weightedIndepPolyOn G (S.erase v) wt)
      (X * weightedIndepPolyOn G
        (deleteClosedNeighborSupport G S v) wt) := by
  let A := weightedIndepPolyOn G ((S.erase v).erase u) wt
  let B := X * weightedIndepPolyOn G
    (deleteClosedNeighborSupport G S u) wt
  let C := X * weightedIndepPolyOn G
    (deleteClosedNeighborSupport G S v) wt
  have hrec :
      weightedIndepPolyOn G (S.erase v) wt =
        A + Polynomial.C (wt u) * B := by
    have h := weightedIndepPolyOn_erase
      (G := G) (wt := wt) (S := S.erase v) (v := u) huS
    have hsupport :
        deleteClosedNeighborSupport G (S.erase v) u =
          deleteClosedNeighborSupport G S u :=
      deleteClosedNeighborSupport_erase_eq_of_adj G huv
    simpa [A, B, hsupport, mul_assoc] using h
  have hA : A ≠ 0 ∧ A.Splits := by
    exact ⟨weightedIndepPolyOn_ne_zero G ((S.erase v).erase u) wt,
      hBaseSplit⟩
  have hB : B ≠ 0 ∧ B.Splits := by
    dsimp [B]
    exact isRealRooted_X_mul
      (weightedIndepPolyOn_ne_zero G
        (deleteClosedNeighborSupport G S u) wt) hDelUSplit
  have hC : C ≠ 0 ∧ C.Splits := by
    dsimp [C]
    exact isRealRooted_X_mul
      (weightedIndepPolyOn_ne_zero G
        (deleteClosedNeighborSupport G S v) wt) hDelVSplit
  have hApos : HasPosLeadingCoeff A := by
    dsimp [A]
    exact weightedIndepPolyOn_hasPosLeadingCoeff G fun w hw =>
      hwt w (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))
  have hBpos : HasPosLeadingCoeff B := by
    dsimp [B]
    exact (weightedIndepPolyOn_hasPosLeadingCoeff G fun w hw =>
      hwt w (deleteClosedNeighborSupport_subset G S u hw)).X_mul
  have hCpos : HasPosLeadingCoeff C := by
    dsimp [C]
    exact (weightedIndepPolyOn_hasPosLeadingCoeff G fun w hw =>
      hwt w (deleteClosedNeighborSupport_subset G S v hw)).X_mul
  have hAnn : HasNonnegCoeffs A := by
    dsimp [A]
    exact weightedIndepPolyOn_hasNonnegCoeffs G fun w hw =>
      hwt w (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))
  have hBnn : HasNonnegCoeffs B := by
    dsimp [B]
    exact (weightedIndepPolyOn_hasNonnegCoeffs G fun w hw =>
      hwt w (deleteClosedNeighborSupport_subset G S u hw)).X_mul
  have hCnn : HasNonnegCoeffs C := by
    dsimp [C]
    exact (weightedIndepPolyOn_hasNonnegCoeffs G fun w hw =>
      hwt w (deleteClosedNeighborSupport_subset G S v hw)).X_mul
  have hBC : Compatible B C := by
    simpa [B, C] using
      compatible_weighted_deleteClosedNeighborSupport_pair_of_commonClosedNeighbor
        hG wt huv hPair
  have hABC : Compatible (A + Polynomial.C (wt u) * B) C :=
    compatible_add_C_mul_left_of_pairwiseCompatible_three
      (r := wt u) (hwt u (Finset.mem_of_mem_erase huS))
      hA hB hC hApos hBpos hCpos hAnn hBnn hCnn
      (by simpa [A, B] using hBaseDelU)
      (by simpa [A, C] using hBaseDelV)
      hBC
  simpa [hrec, A, B, C] using hABC

/-- Chudnovsky--Seymour Lemma 2.6, as a support-level induction step.  The
compatibility of the two vertex-deletion summands for `v ∈ S` follows from the
same invariant on smaller supports and Lemma 2.5.1 on the common-closed-
neighborhood deletion support. -/
theorem supportVertexDeletionCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} (hSplitSmall : ∀ T : Finset V, T.card < S.card →
      (indepPolyOn G T).Splits)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialPairCompatible G T)
    (hVertexSmall : ∀ T : Finset V, T.card < S.card →
      SupportVertexDeletionCompatible G T) :
    SupportVertexDeletionCompatible G S := by
  intro v hvS
  let N := neighborSetOn G (S.erase v) v
  by_cases hN_empty : N = ∅
  · exact compatible_erase_X_mul_deleteClosedNeighborSupport_of_no_neighbors
      G hN_empty (hSplitSmall (S.erase v) (Finset.card_erase_lt_of_mem hvS))
  · have hN_nonempty : N.Nonempty := Finset.nonempty_iff_ne_empty.mpr hN_empty
    rcases hN_nonempty with ⟨u, huN⟩
    have huN' := Finset.mem_filter.mp huN
    have huS_erase_v : u ∈ S.erase v := huN'.1
    have huv_vu : G.Adj v u := huN'.2
    have huv : G.Adj u v := huv_vu.symm
    have huS : u ∈ S := Finset.mem_of_mem_erase huS_erase_v
    have hv_ne_u : v ≠ u := fun h => (Finset.mem_erase.mp huS_erase_v).1 h.symm
    have hvS_erase_u : v ∈ S.erase u :=
      Finset.mem_erase.mpr ⟨hv_ne_u, hvS⟩
    have hEraseVSmall : (S.erase v).card < S.card :=
      Finset.card_erase_lt_of_mem hvS
    have hEraseUSmall : (S.erase u).card < S.card :=
      Finset.card_erase_lt_of_mem huS
    have hBaseSplit : (indepPolyOn G ((S.erase v).erase u)).Splits := by
      exact hSplitSmall ((S.erase v).erase u) <|
        lt_of_le_of_lt (Finset.card_le_card (Finset.erase_subset u (S.erase v)))
          hEraseVSmall
    have hDelUSplit :
        (indepPolyOn G (deleteClosedNeighborSupport G S u)).Splits :=
      hSplitSmall (deleteClosedNeighborSupport G S u) <|
        lt_of_le_of_lt
          (Finset.card_le_card (deleteClosedNeighborSupport_subset_erase G S u))
          hEraseUSmall
    have hDelVSplit :
        (indepPolyOn G (deleteClosedNeighborSupport G S v)).Splits :=
      hSplitSmall (deleteClosedNeighborSupport G S v) <|
        lt_of_le_of_lt
          (Finset.card_le_card (deleteClosedNeighborSupport_subset_erase G S v))
          hEraseVSmall
    have hBaseDelU : Compatible (indepPolyOn G ((S.erase v).erase u))
        (X * indepPolyOn G (deleteClosedNeighborSupport G S u)) := by
      have h := hVertexSmall (S.erase v) hEraseVSmall huS_erase_v
      have hsupport :
          deleteClosedNeighborSupport G (S.erase v) u =
            deleteClosedNeighborSupport G S u :=
        deleteClosedNeighborSupport_erase_eq_of_adj G huv
      simp_all
    have hBaseDelV : Compatible (indepPolyOn G ((S.erase v).erase u))
        (X * indepPolyOn G (deleteClosedNeighborSupport G S v)) := by
      have h := hVertexSmall (S.erase u) hEraseUSmall hvS_erase_u
      have herase : (S.erase u).erase v = (S.erase v).erase u := by
        ext w
        by_cases hwv : w = v <;> by_cases hwu : w = u <;>
          simp [Finset.mem_erase, hwv, hwu]
      have hsupport :
          deleteClosedNeighborSupport G (S.erase u) v =
            deleteClosedNeighborSupport G S v :=
        deleteClosedNeighborSupport_erase_eq_of_adj G huv_vu
      simp_all
    have hCommonSub : commonClosedNeighborSetOn G S u v ⊆ S :=
      commonClosedNeighborSetOn_subset G S u v
    have huCommon : u ∈ commonClosedNeighborSetOn G S u v := by
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨huS, Or.inl rfl⟩,
          Finset.mem_filter.mpr ⟨huS, Or.inr huv.symm⟩⟩
    have hCommonNonempty : (commonClosedNeighborSetOn G S u v).Nonempty :=
      ⟨u, huCommon⟩
    have hCommonSmall :
        (S \ commonClosedNeighborSetOn G S u v).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hCommonSub hCommonNonempty)
    exact compatible_erase_X_mul_deleteClosedNeighborSupport_of_adjacent hG
      huS_erase_v huv hBaseSplit hDelUSplit hDelVSplit hBaseDelU hBaseDelV
      (hPairSmall (S \ commonClosedNeighborSetOn G S u v) hCommonSmall)

/-- Weighted support-level vertex-deletion compatibility induction step. -/
theorem weightedSupportVertexDeletionCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (wt : V → ℝ) {S : Finset V} (hwt : ∀ v ∈ S, 0 ≤ wt v)
    (hSplitSmall : ∀ T : Finset V, T.card < S.card →
      (weightedIndepPolyOn G T wt).Splits)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      WeightedSupportSimplicialPairCompatible G wt T)
    (hVertexSmall : ∀ T : Finset V, T.card < S.card →
      WeightedSupportVertexDeletionCompatible G wt T) :
    WeightedSupportVertexDeletionCompatible G wt S := by
  intro v hvS
  let N := neighborSetOn G (S.erase v) v
  by_cases hN_empty : N = ∅
  · exact
      compatible_weightedIndepPolyOn_erase_X_mul_deleteClosedNeighborSupport_of_no_neighbors
        G wt hN_empty
        (hSplitSmall (S.erase v) (Finset.card_erase_lt_of_mem hvS))
  · have hN_nonempty : N.Nonempty := Finset.nonempty_iff_ne_empty.mpr hN_empty
    rcases hN_nonempty with ⟨u, huN⟩
    have huN' := Finset.mem_filter.mp huN
    have huS_erase_v : u ∈ S.erase v := huN'.1
    have huv_vu : G.Adj v u := huN'.2
    have huv : G.Adj u v := huv_vu.symm
    have huS : u ∈ S := Finset.mem_of_mem_erase huS_erase_v
    have hv_ne_u : v ≠ u := fun h =>
      (Finset.mem_erase.mp huS_erase_v).1 h.symm
    have hvS_erase_u : v ∈ S.erase u :=
      Finset.mem_erase.mpr ⟨hv_ne_u, hvS⟩
    have hEraseVSmall : (S.erase v).card < S.card :=
      Finset.card_erase_lt_of_mem hvS
    have hEraseUSmall : (S.erase u).card < S.card :=
      Finset.card_erase_lt_of_mem huS
    have hBaseSplit :
        (weightedIndepPolyOn G ((S.erase v).erase u) wt).Splits := by
      exact hSplitSmall ((S.erase v).erase u) <|
        lt_of_le_of_lt
          (Finset.card_le_card (Finset.erase_subset u (S.erase v)))
          hEraseVSmall
    have hDelUSplit :
        (weightedIndepPolyOn G
          (deleteClosedNeighborSupport G S u) wt).Splits :=
      hSplitSmall (deleteClosedNeighborSupport G S u) <|
        lt_of_le_of_lt
          (Finset.card_le_card
            (deleteClosedNeighborSupport_subset_erase G S u))
          hEraseUSmall
    have hDelVSplit :
        (weightedIndepPolyOn G
          (deleteClosedNeighborSupport G S v) wt).Splits :=
      hSplitSmall (deleteClosedNeighborSupport G S v) <|
        lt_of_le_of_lt
          (Finset.card_le_card
            (deleteClosedNeighborSupport_subset_erase G S v))
          hEraseVSmall
    have hBaseDelU :
        Compatible (weightedIndepPolyOn G ((S.erase v).erase u) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G S u) wt) := by
      have h := hVertexSmall (S.erase v) hEraseVSmall huS_erase_v
      have hsupport :
          deleteClosedNeighborSupport G (S.erase v) u =
            deleteClosedNeighborSupport G S u :=
        deleteClosedNeighborSupport_erase_eq_of_adj G huv
      simp_all
    have hBaseDelV :
        Compatible (weightedIndepPolyOn G ((S.erase v).erase u) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G S v) wt) := by
      have h := hVertexSmall (S.erase u) hEraseUSmall hvS_erase_u
      have herase : (S.erase u).erase v = (S.erase v).erase u := by
        ext w
        by_cases hwv : w = v <;> by_cases hwu : w = u <;>
          simp [Finset.mem_erase, hwv, hwu]
      have hsupport :
          deleteClosedNeighborSupport G (S.erase u) v =
            deleteClosedNeighborSupport G S v :=
        deleteClosedNeighborSupport_erase_eq_of_adj G huv_vu
      simp_all
    have hCommonSub : commonClosedNeighborSetOn G S u v ⊆ S :=
      commonClosedNeighborSetOn_subset G S u v
    have huCommon : u ∈ commonClosedNeighborSetOn G S u v := by
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨huS, Or.inl rfl⟩,
          Finset.mem_filter.mpr ⟨huS, Or.inr huv.symm⟩⟩
    have hCommonNonempty :
        (commonClosedNeighborSetOn G S u v).Nonempty :=
      ⟨u, huCommon⟩
    have hCommonSmall :
        (S \ commonClosedNeighborSetOn G S u v).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hCommonSub hCommonNonempty)
    exact
      compatible_weighted_erase_X_mul_deleteClosedNeighborSupport_of_adjacent
        hG wt hwt huS_erase_v huv hBaseSplit hDelUSplit hDelVSplit
        hBaseDelU hBaseDelV
        (hPairSmall (S \ commonClosedNeighborSetOn G S u v) hCommonSmall)

/-- Chudnovsky--Seymour Lemma 2.5.1, as a support-level induction step.  The
new content is that compatibility of `I(S \ K)` and `I(S \ L)` follows from
the two smaller-support compatibility invariants on `S \ (K ∪ L)`. -/
theorem supportSimplicialPairCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} (hSplit : SupportIndepPolySplits G S)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialPairCompatible G T)
    (hXSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialXCompatible G T) :
    SupportSimplicialPairCompatible G S := by
  intro K L hK hL
  have hUnionSub : K ∪ L ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxL
    · exact hK.1 hxK
    · exact hL.1 hxL
  by_cases hUnion_empty : K ∪ L = ∅
  · have hK_empty : K = ∅ := by simp_all
    have hL_empty : L = ∅ := by simp_all
    have hS : (indepPolyOn G S).Splits := hSplit S Subset.rfl
    simpa [hK_empty, hL_empty] using
      compatible_self_of_splits (indepPolyOn_ne_zero G S) hS
  · have hUnion_nonempty : (K ∪ L).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hUnion_empty
    have hsmall : (S \ (K ∪ L)).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hUnionSub hUnion_nonempty)
    have hbase : (indepPolyOn G (S \ (K ∪ L))).Splits :=
      hSplit (S \ (K ∪ L)) sdiff_subset
    have hK_support : (S \ L) \ (K \ L) = S \ (K ∪ L) :=
      by simp [sdiff_sdiff, union_comm]
    have hL_support : (S \ K) \ (L \ K) = S \ (K ∪ L) :=
      by simp [sdiff_sdiff]
    have hK_simp : IsSimplicialCliqueOn G (S \ L) (K \ L) :=
      hK.sdiff_right L
    have hL_simp : IsSimplicialCliqueOn G (S \ K) (L \ K) :=
      hL.sdiff_right K
    have hK_neighbor_simp : ∀ v ∈ K \ L,
        IsSimplicialCliqueOn G (S \ (K ∪ L))
          (neighborOutsideCliqueOn G (S \ L) (K \ L) v) := by
      intro v hv
      simpa [hK_support] using hG.simplicialClique_neighborOutside hK_simp hv
    have hL_neighbor_simp : ∀ v ∈ L \ K,
        IsSimplicialCliqueOn G (S \ (K ∪ L))
          (neighborOutsideCliqueOn G (S \ K) (L \ K) v) := by
      intro v hv
      simpa [hL_support] using hG.simplicialClique_neighborOutside hL_simp hv
    have hK_delete_support : ∀ v ∈ K \ L,
        deleteClosedNeighborSupport G (S \ L) v =
          (S \ (K ∪ L)) \ neighborOutsideCliqueOn G (S \ L) (K \ L) v := by
      intro v hv
      have h := deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
        G hK_simp.2.1 hK_simp.1 hv
      simp_all
    have hL_delete_support : ∀ v ∈ L \ K,
        deleteClosedNeighborSupport G (S \ K) v =
          (S \ (K ∪ L)) \ neighborOutsideCliqueOn G (S \ K) (L \ K) v := by
      intro v hv
      have h := deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
        G hL_simp.2.1 hL_simp.1 hv
      simp_all
    have hKdel : ∀ v ∈ K \ L,
        (indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)).Splits := by
      intro v hv
      have hsub : deleteClosedNeighborSupport G (S \ L) v ⊆ S := by
        intro w hw
        simp_all
      exact hSplit (deleteClosedNeighborSupport G (S \ L) v) hsub
    have hLdel : ∀ v ∈ L \ K,
        (indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)).Splits := by
      intro v hv
      have hsub : deleteClosedNeighborSupport G (S \ K) v ⊆ S := by
        intro w hw
        simp_all
      exact hSplit (deleteClosedNeighborSupport G (S \ K) v) hsub
    have hbase_k_x : ∀ v ∈ K \ L,
        Compatible (indepPolyOn G (S \ (K ∪ L)))
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)) := by
      intro v hv
      have hx := hXSmall (S \ (K ∪ L)) hsmall (hK_neighbor_simp v hv)
      simp_all
    have hbase_l_x : ∀ v ∈ L \ K,
        Compatible (indepPolyOn G (S \ (K ∪ L)))
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)) := by
      intro v hv
      have hx := hXSmall (S \ (K ∪ L)) hsmall (hL_neighbor_simp v hv)
      simp_all
    have hK_pair_x : ∀ u ∈ K \ L, ∀ v ∈ K \ L,
        Compatible
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) u))
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)) := by
      intro u hu v hv
      have hp := (hPairSmall (S \ (K ∪ L)) hsmall)
        (hK_neighbor_simp u hu) (hK_neighbor_simp v hv)
      simpa [hK_delete_support u hu, hK_delete_support v hv] using
        compatible_X_mul_of_compatible hp
    have hL_pair_x : ∀ u ∈ L \ K, ∀ v ∈ L \ K,
        Compatible
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) u))
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)) := by
      intro u hu v hv
      have hp := (hPairSmall (S \ (K ∪ L)) hsmall)
        (hL_neighbor_simp u hu) (hL_neighbor_simp v hv)
      simpa [hL_delete_support u hu, hL_delete_support v hv] using
        compatible_X_mul_of_compatible hp
    have hKL_pair_x : ∀ u ∈ K \ L, ∀ v ∈ L \ K,
        Compatible
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) u))
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)) := by
      intro u hu v hv
      have hp := (hPairSmall (S \ (K ∪ L)) hsmall)
        (hK_neighbor_simp u hu) (hL_neighbor_simp v hv)
      simpa [hK_delete_support u hu, hL_delete_support v hv] using
        compatible_X_mul_of_compatible hp
    have hpair : PairwiseCompatible (cliquePairDeletionFamily G S K L) := by
      apply pairwiseCompatible_of_forall_mem
      intro f hf g hg
      simp only [cliquePairDeletionFamily, List.mem_cons, List.mem_append,
        List.mem_map] at hf hg
      rcases hf with rfl | htailF
      · rcases hg with rfl | htailG
        · exact compatible_self_of_splits
            (indepPolyOn_ne_zero G (S \ (K ∪ L))) hbase
        · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩ <;> simp_all
      · rcases htailF with ⟨u, huList, rfl⟩ | ⟨u, huList, rfl⟩
        · have hu : u ∈ K \ L := Finset.mem_toList.mp huList
          rcases hg with rfl | htailG
          · exact (hbase_k_x u hu).comm
          · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩ <;> simp_all
        · have hu : u ∈ L \ K := Finset.mem_toList.mp huList
          rcases hg with rfl | htailG
          · exact (hbase_l_x u hu).comm
          · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩
            · exact (hKL_pair_x v (Finset.mem_toList.mp hvList) u hu).comm
            · simp_all
    exact compatible_indepPolyOn_sdiff_pair_of_pairDeletion_pairwiseCompatible
      G S K L hK.2.1 hL.2.1 hK.1 hL.1 hbase hKdel hLdel hpair

/-- Weighted support-level simplicial-pair compatibility induction step. -/
theorem weightedSupportSimplicialPairCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (wt : V → ℝ) {S : Finset V} (hwt : ∀ v ∈ S, 0 ≤ wt v)
    (hSplit : WeightedSupportIndepPolySplits G wt S)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      WeightedSupportSimplicialPairCompatible G wt T)
    (hXSmall : ∀ T : Finset V, T.card < S.card →
      WeightedSupportSimplicialXCompatible G wt T) :
    WeightedSupportSimplicialPairCompatible G wt S := by
  intro K L hK hL
  have hUnionSub : K ∪ L ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxL
    · exact hK.1 hxK
    · exact hL.1 hxL
  by_cases hUnion_empty : K ∪ L = ∅
  · have hK_empty : K = ∅ := by simp_all
    have hL_empty : L = ∅ := by simp_all
    have hS : (weightedIndepPolyOn G S wt).Splits :=
      hSplit S Subset.rfl
    simpa [hK_empty, hL_empty] using
      compatible_self_of_splits (weightedIndepPolyOn_ne_zero G S wt) hS
  · have hUnion_nonempty : (K ∪ L).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hUnion_empty
    have hsmall : (S \ (K ∪ L)).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hUnionSub hUnion_nonempty)
    have hbase :
        (weightedIndepPolyOn G (S \ (K ∪ L)) wt).Splits :=
      hSplit (S \ (K ∪ L)) sdiff_subset
    have hK_support : (S \ L) \ (K \ L) = S \ (K ∪ L) :=
      by simp [sdiff_sdiff, union_comm]
    have hL_support : (S \ K) \ (L \ K) = S \ (K ∪ L) :=
      by simp [sdiff_sdiff]
    have hK_simp : IsSimplicialCliqueOn G (S \ L) (K \ L) :=
      hK.sdiff_right L
    have hL_simp : IsSimplicialCliqueOn G (S \ K) (L \ K) :=
      hL.sdiff_right K
    have hK_neighbor_simp : ∀ v ∈ K \ L,
        IsSimplicialCliqueOn G (S \ (K ∪ L))
          (neighborOutsideCliqueOn G (S \ L) (K \ L) v) := by
      intro v hv
      simpa [hK_support] using
        hG.simplicialClique_neighborOutside hK_simp hv
    have hL_neighbor_simp : ∀ v ∈ L \ K,
        IsSimplicialCliqueOn G (S \ (K ∪ L))
          (neighborOutsideCliqueOn G (S \ K) (L \ K) v) := by
      intro v hv
      simpa [hL_support] using
        hG.simplicialClique_neighborOutside hL_simp hv
    have hK_delete_support : ∀ v ∈ K \ L,
        deleteClosedNeighborSupport G (S \ L) v =
          (S \ (K ∪ L)) \
            neighborOutsideCliqueOn G (S \ L) (K \ L) v := by
      intro v hv
      have h :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G hK_simp.2.1 hK_simp.1 hv
      simp_all
    have hL_delete_support : ∀ v ∈ L \ K,
        deleteClosedNeighborSupport G (S \ K) v =
          (S \ (K ∪ L)) \
            neighborOutsideCliqueOn G (S \ K) (L \ K) v := by
      intro v hv
      have h :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G hL_simp.2.1 hL_simp.1 hv
      simp_all
    have hKdel : ∀ v ∈ K \ L,
        (weightedIndepPolyOn G
          (deleteClosedNeighborSupport G (S \ L) v) wt).Splits := by
      intro v hv
      have hsub : deleteClosedNeighborSupport G (S \ L) v ⊆ S := by
        intro w hw
        simp_all
      exact hSplit (deleteClosedNeighborSupport G (S \ L) v) hsub
    have hLdel : ∀ v ∈ L \ K,
        (weightedIndepPolyOn G
          (deleteClosedNeighborSupport G (S \ K) v) wt).Splits := by
      intro v hv
      have hsub : deleteClosedNeighborSupport G (S \ K) v ⊆ S := by
        intro w hw
        simp_all
      exact hSplit (deleteClosedNeighborSupport G (S \ K) v) hsub
    have hbase_k_x : ∀ v ∈ K \ L,
        Compatible (weightedIndepPolyOn G (S \ (K ∪ L)) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ L) v) wt) := by
      intro v hv
      have hx := hXSmall (S \ (K ∪ L)) hsmall
        (hK_neighbor_simp v hv)
      simp_all
    have hbase_l_x : ∀ v ∈ L \ K,
        Compatible (weightedIndepPolyOn G (S \ (K ∪ L)) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ K) v) wt) := by
      intro v hv
      have hx := hXSmall (S \ (K ∪ L)) hsmall
        (hL_neighbor_simp v hv)
      simp_all
    have hK_pair_x : ∀ u ∈ K \ L, ∀ v ∈ K \ L,
        Compatible
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ L) u) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ L) v) wt) := by
      intro u hu v hv
      have hp := (hPairSmall (S \ (K ∪ L)) hsmall)
        (hK_neighbor_simp u hu) (hK_neighbor_simp v hv)
      simpa [hK_delete_support u hu, hK_delete_support v hv] using
        compatible_X_mul_of_compatible hp
    have hL_pair_x : ∀ u ∈ L \ K, ∀ v ∈ L \ K,
        Compatible
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ K) u) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ K) v) wt) := by
      intro u hu v hv
      have hp := (hPairSmall (S \ (K ∪ L)) hsmall)
        (hL_neighbor_simp u hu) (hL_neighbor_simp v hv)
      simpa [hL_delete_support u hu, hL_delete_support v hv] using
        compatible_X_mul_of_compatible hp
    have hKL_pair_x : ∀ u ∈ K \ L, ∀ v ∈ L \ K,
        Compatible
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ L) u) wt)
          (X * weightedIndepPolyOn G
            (deleteClosedNeighborSupport G (S \ K) v) wt) := by
      intro u hu v hv
      have hp := (hPairSmall (S \ (K ∪ L)) hsmall)
        (hK_neighbor_simp u hu) (hL_neighbor_simp v hv)
      simpa [hK_delete_support u hu, hL_delete_support v hv] using
        compatible_X_mul_of_compatible hp
    have hpair : PairwiseCompatible
        (weightedCliquePairDeletionFamily G wt S K L) := by
      apply pairwiseCompatible_of_forall_mem
      intro f hf g hg
      simp only [weightedCliquePairDeletionFamily, List.mem_cons,
        List.mem_append, List.mem_map] at hf hg
      rcases hf with rfl | htailF
      · rcases hg with rfl | htailG
        · exact compatible_self_of_splits
            (weightedIndepPolyOn_ne_zero G (S \ (K ∪ L)) wt) hbase
        · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩ <;>
            simp_all
      · rcases htailF with ⟨u, huList, rfl⟩ | ⟨u, huList, rfl⟩
        · have hu : u ∈ K \ L := Finset.mem_toList.mp huList
          rcases hg with rfl | htailG
          · exact (hbase_k_x u hu).comm
          · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩ <;>
              simp_all
        · have hu : u ∈ L \ K := Finset.mem_toList.mp huList
          rcases hg with rfl | htailG
          · exact (hbase_l_x u hu).comm
          · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩
            · exact (hKL_pair_x v (Finset.mem_toList.mp hvList) u hu).comm
            · simp_all
    exact
      compatible_weightedIndepPolyOn_sdiff_pair_of_pairDeletion_pairwiseCompatible
        G wt S K L hK.2.1 hL.2.1 hK.1 hL.1 hwt hbase hKdel hLdel hpair

/-- Chudnovsky--Seymour Lemma 2.5.2, as a support-level induction step.  The
new content is that the compatibility of `I(S)` with `X * I(S \ K)` follows
from the two smaller-support compatibility invariants on `S \ K`. -/
theorem supportSimplicialXCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    {S : Finset V} (hSplit : SupportIndepPolySplits G S)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialPairCompatible G T)
    (hXSmall : ∀ T : Finset V, T.card < S.card →
      SupportSimplicialXCompatible G T) :
    SupportSimplicialXCompatible G S := by
  intro K hK
  by_cases hK_empty : K = ∅
  · subst hK_empty
    have hS : (indepPolyOn G S).Splits := hSplit S Subset.rfl
    simpa using compatible_indepPolyOn_X_mul_self_of_splits G S hS
  · have hK_nonempty : K.Nonempty := Finset.nonempty_iff_ne_empty.mpr hK_empty
    have hsmall : (S \ K).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hK.1 hK_nonempty)
    have hbase : (indepPolyOn G (S \ K)).Splits := hSplit (S \ K) sdiff_subset
    have hneighbor_simp : ∀ v ∈ K,
        IsSimplicialCliqueOn G (S \ K) (neighborOutsideCliqueOn G S K v) := by
      intro v hv
      exact hG.simplicialClique_neighborOutside hK hv
    have hbase_neighbor_x : ∀ v ∈ K,
        Compatible (indepPolyOn G (S \ K))
          (X * indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)) := by
      intro v hv
      exact hXSmall (S \ K) hsmall (hneighbor_simp v hv)
    have hbase_neighbor : ∀ v ∈ K,
        Compatible (indepPolyOn G (S \ K))
          (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)) := by
      intro v hv
      simpa using (hPairSmall (S \ K) hsmall)
        (isSimplicialCliqueOn_empty G (S \ K)) (hneighbor_simp v hv)
    have hneighbor_pair : ∀ u ∈ K, ∀ v ∈ K,
        Compatible (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K u))
          (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)) := by
      intro u hu v hv
      exact (hPairSmall (S \ K) hsmall) (hneighbor_simp u hu) (hneighbor_simp v hv)
    have hpair : PairwiseCompatible (cliqueDeletionCompatibilityFamily G S K) :=
      cliqueDeletionCompatibilityFamily_pairwiseCompatible_of_neighborOutside_compatible
        G hK.2.1 hK.1 hbase hbase_neighbor_x hbase_neighbor hneighbor_pair
    have hdel : ∀ v ∈ K,
        (indepPolyOn G (deleteClosedNeighborSupport G S v)).Splits := by
      intro v hv
      have hsupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G hK.2.1 hK.1 hv
      have hsub : (S \ K) \ neighborOutsideCliqueOn G S K v ⊆ S := by
        intro w hw
        simp_all
      simpa [hsupport] using hSplit ((S \ K) \ neighborOutsideCliqueOn G S K v) hsub
    exact compatible_indepPolyOn_X_mul_sdiff_of_cliqueDeletion_pairwiseCompatible
      G S K hK.2.1 hK.1 hbase hdel hpair

/-- Weighted support-level simplicial self/shift compatibility induction
step. -/
theorem weightedSupportSimplicialXCompatible_of_smaller
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (wt : V → ℝ) {S : Finset V} (hwt : ∀ v ∈ S, 0 ≤ wt v)
    (hSplit : WeightedSupportIndepPolySplits G wt S)
    (hPairSmall : ∀ T : Finset V, T.card < S.card →
      WeightedSupportSimplicialPairCompatible G wt T)
    (hXSmall : ∀ T : Finset V, T.card < S.card →
      WeightedSupportSimplicialXCompatible G wt T) :
    WeightedSupportSimplicialXCompatible G wt S := by
  intro K hK
  by_cases hK_empty : K = ∅
  · subst hK_empty
    have hS : (weightedIndepPolyOn G S wt).Splits :=
      hSplit S Subset.rfl
    simpa using
      compatible_weightedIndepPolyOn_X_mul_self_of_splits G S wt hS
  · have hK_nonempty : K.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hK_empty
    have hsmall : (S \ K).card < S.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hK.1 hK_nonempty)
    have hbase : (weightedIndepPolyOn G (S \ K) wt).Splits :=
      hSplit (S \ K) sdiff_subset
    have hneighbor_simp : ∀ v ∈ K,
        IsSimplicialCliqueOn G (S \ K)
          (neighborOutsideCliqueOn G S K v) := by
      intro v hv
      exact hG.simplicialClique_neighborOutside hK hv
    have hbase_neighbor_x : ∀ v ∈ K,
        Compatible (weightedIndepPolyOn G (S \ K) wt)
          (X * weightedIndepPolyOn G
            ((S \ K) \ neighborOutsideCliqueOn G S K v) wt) := by
      intro v hv
      exact hXSmall (S \ K) hsmall (hneighbor_simp v hv)
    have hbase_neighbor : ∀ v ∈ K,
        Compatible (weightedIndepPolyOn G (S \ K) wt)
          (weightedIndepPolyOn G
            ((S \ K) \ neighborOutsideCliqueOn G S K v) wt) := by
      intro v hv
      simpa using (hPairSmall (S \ K) hsmall)
        (isSimplicialCliqueOn_empty G (S \ K)) (hneighbor_simp v hv)
    have hneighbor_pair : ∀ u ∈ K, ∀ v ∈ K,
        Compatible
          (weightedIndepPolyOn G
            ((S \ K) \ neighborOutsideCliqueOn G S K u) wt)
          (weightedIndepPolyOn G
            ((S \ K) \ neighborOutsideCliqueOn G S K v) wt) := by
      intro u hu v hv
      exact (hPairSmall (S \ K) hsmall)
        (hneighbor_simp u hu) (hneighbor_simp v hv)
    have hpair : PairwiseCompatible
        (weightedCliqueDeletionCompatibilityFamily G wt S K) :=
      weightedCliqueDeletionCompatibilityFamily_pairwiseCompatible_of_neighborOutside_compatible
        G wt hK.2.1 hK.1 hbase hbase_neighbor_x hbase_neighbor
          hneighbor_pair
    have hdel : ∀ v ∈ K,
        (weightedIndepPolyOn G
          (deleteClosedNeighborSupport G S v) wt).Splits := by
      intro v hv
      have hsupport :=
        deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
          G hK.2.1 hK.1 hv
      have hsub :
          (S \ K) \ neighborOutsideCliqueOn G S K v ⊆ S := by
        intro w hw
        simp_all
      simpa [hsupport] using
        hSplit ((S \ K) \ neighborOutsideCliqueOn G S K v) hsub
    exact
      compatible_weightedIndepPolyOn_X_mul_sdiff_of_cliqueDeletion_pairwiseCompatible
        G wt S K hK.2.1 hK.1 hwt hbase hdel hpair

/-- Support-level Chudnovsky--Seymour theorem for claw-free graphs: every
support-restricted independence polynomial is real-rooted. -/
theorem supportIndepPoly_splits_of_clawFree
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G) :
    ∀ S : Finset V, (indepPolyOn G S).Splits := by
  classical
  have hmain : ∀ n : ℕ, ∀ S : Finset V, S.card = n →
      SupportIndepPolySplits G S ∧
        SupportSimplicialPairCompatible G S ∧
          SupportSimplicialXCompatible G S ∧
            SupportVertexDeletionCompatible G S := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih S hcard
    have hSplitSmall : ∀ T : Finset V, T.card < S.card →
        (indepPolyOn G T).Splits := by
      intro T hT
      have hTn : T.card < n := by simp_all
      exact (ih T.card hTn T rfl).1 T Subset.rfl
    have hPairSmall : ∀ T : Finset V, T.card < S.card →
        SupportSimplicialPairCompatible G T := by
      intro T hT
      have hTn : T.card < n := by simp_all
      intro K L hK hL
      exact (ih T.card hTn T rfl).2.1 hK hL
    have hXSmall : ∀ T : Finset V, T.card < S.card →
        SupportSimplicialXCompatible G T := by
      intro T hT
      have hTn : T.card < n := by simp_all
      intro K hK
      exact (ih T.card hTn T rfl).2.2.1 hK
    have hVertexSmall : ∀ T : Finset V, T.card < S.card →
        SupportVertexDeletionCompatible G T := by
      intro T hT
      have hTn : T.card < n := by simp_all
      intro v hv
      exact (ih T.card hTn T rfl).2.2.2 hv
    have hVertex : SupportVertexDeletionCompatible G S :=
      supportVertexDeletionCompatible_of_smaller hG hSplitSmall hPairSmall hVertexSmall
    have hSplitSelf : (indepPolyOn G S).Splits := by
      by_cases hS_empty : S = ∅
      · subst hS_empty
        exact indepPolyOn_empty_splits G
      · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
        rcases hS_nonempty with ⟨v, hvS⟩
        have hsum_ne :
            indepPolyOn G (S.erase v) +
              X * indepPolyOn G (deleteClosedNeighborSupport G S v) ≠ 0 := by
          intro hzero
          exact indepPolyOn_ne_zero G S (by
            rw [indepPolyOn_erase G hvS]
            simp_all)
        have hsum_splits :=
          splits_add_of_compatible (hVertex hvS) hsum_ne
        rw [indepPolyOn_erase G hvS]
        exact hsum_splits
    have hSplit : SupportIndepPolySplits G S := by
      intro T hTS
      by_cases hTS_eq : T = S
      · simp_all
      · have hproper : T ⊂ S :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hTS_eq⟩
        exact hSplitSmall T (Finset.card_lt_card hproper)
    have hPair : SupportSimplicialPairCompatible G S :=
      supportSimplicialPairCompatible_of_smaller hG hSplit hPairSmall hXSmall
    have hX : SupportSimplicialXCompatible G S :=
      supportSimplicialXCompatible_of_smaller hG hSplit hPairSmall hXSmall
    simp_all
  intro S
  exact (hmain S.card S rfl).1 S Subset.rfl

/-- Weighted support-level Chudnovsky--Seymour theorem: nonnegative vertex
weights preserve real-rootedness of independence polynomials of claw-free
graphs. -/
theorem weightedSupportIndepPoly_splits_of_clawFree
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (wt : V → ℝ) (hwt : ∀ v, 0 ≤ wt v) :
    ∀ S : Finset V, (weightedIndepPolyOn G S wt).Splits := by
  classical
  have hmain : ∀ n : ℕ, ∀ S : Finset V, S.card = n →
      WeightedSupportIndepPolySplits G wt S ∧
        WeightedSupportSimplicialPairCompatible G wt S ∧
          WeightedSupportSimplicialXCompatible G wt S ∧
            WeightedSupportVertexDeletionCompatible G wt S := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih S hcard
    have hSplitSmall : ∀ T : Finset V, T.card < S.card →
        (weightedIndepPolyOn G T wt).Splits := by
      intro T hT
      have hTn : T.card < n := by simp_all
      exact (ih T.card hTn T rfl).1 T Subset.rfl
    have hPairSmall : ∀ T : Finset V, T.card < S.card →
        WeightedSupportSimplicialPairCompatible G wt T := by
      intro T hT
      have hTn : T.card < n := by simp_all
      intro K L hK hL
      exact (ih T.card hTn T rfl).2.1 hK hL
    have hXSmall : ∀ T : Finset V, T.card < S.card →
        WeightedSupportSimplicialXCompatible G wt T := by
      intro T hT
      have hTn : T.card < n := by simp_all
      intro K hK
      exact (ih T.card hTn T rfl).2.2.1 hK
    have hVertexSmall : ∀ T : Finset V, T.card < S.card →
        WeightedSupportVertexDeletionCompatible G wt T := by
      intro T hT
      have hTn : T.card < n := by simp_all
      intro v hv
      exact (ih T.card hTn T rfl).2.2.2 hv
    have hVertex : WeightedSupportVertexDeletionCompatible G wt S :=
      weightedSupportVertexDeletionCompatible_of_smaller
        hG wt (fun v _hv => hwt v) hSplitSmall hPairSmall hVertexSmall
    have hSplitSelf : (weightedIndepPolyOn G S wt).Splits := by
      by_cases hS_empty : S = ∅
      · subst hS_empty
        exact weightedIndepPolyOn_empty_splits G wt
      · have hS_nonempty : S.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hS_empty
        rcases hS_nonempty with ⟨v, hvS⟩
        have hsum_ne :
            weightedIndepPolyOn G (S.erase v) wt +
              C (wt v) *
                (X * weightedIndepPolyOn G
                  (deleteClosedNeighborSupport G S v) wt) ≠ 0 := by
          intro hzero
          exact weightedIndepPolyOn_ne_zero G S wt (by
            rw [weightedIndepPolyOn_erase G wt hvS]
            simpa [mul_assoc] using hzero)
        have hsum_splits :=
          splits_add_C_mul_of_compatible
            (hVertex hvS) (r := wt v) (hwt v) hsum_ne
        rw [weightedIndepPolyOn_erase G wt hvS]
        simpa [mul_assoc] using hsum_splits
    have hSplit : WeightedSupportIndepPolySplits G wt S := by
      intro T hTS
      by_cases hTS_eq : T = S
      · simp_all
      · have hproper : T ⊂ S :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hTS_eq⟩
        exact hSplitSmall T (Finset.card_lt_card hproper)
    have hPair : WeightedSupportSimplicialPairCompatible G wt S :=
      weightedSupportSimplicialPairCompatible_of_smaller
        hG wt (fun v _hv => hwt v) hSplit hPairSmall hXSmall
    have hX : WeightedSupportSimplicialXCompatible G wt S :=
      weightedSupportSimplicialXCompatible_of_smaller
        hG wt (fun v _hv => hwt v) hSplit hPairSmall hXSmall
    simp_all
  intro S
  exact (hmain S.card S rfl).1 S Subset.rfl

/-- Weighted Chudnovsky--Seymour theorem for finite claw-free graphs. -/
theorem clawFree_weightedIndepPoly_splits
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    (hG : ClawFree G) (wt : V → ℝ) (hwt : ∀ v, 0 ≤ wt v) :
    (weightedIndepPoly G wt).Splits := by
  rw [weightedIndepPoly_eq_weightedIndepPolyOn_univ]
  exact weightedSupportIndepPoly_splits_of_clawFree hG wt hwt Finset.univ

/-- The support-restricted independence polynomial is the ordinary independence
polynomial of the induced graph on that support. -/
theorem indepPolyOn_univ_induce_finset {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    indepPolyOn (G.induce (S : Set V)) Finset.univ = indepPolyOn G S := by
  classical
  let lift : Finset V → Finset {x // x ∈ (S : Set V)} := fun t =>
    S.attach.filter fun x => (x : V) ∈ t
  have hmap_lift : ∀ {t : Finset V}, t ⊆ S → (lift t).image Subtype.val = t := by
    intro t hsub
    ext x
    by_cases hxt : x ∈ t
    · simp [lift, hxt, hsub hxt]
    · simp [lift, hxt]
  have hlift_indep : ∀ {t : Finset V}, t ⊆ S →
      ((G.induce (S : Set V)).IsIndepSet ((lift t) : Set {x // x ∈ (S : Set V)}) ↔
        G.IsIndepSet (t : Set V)) := by
    intro t hsub
    constructor
    · intro hind a ha b hb hne hadj
      have ha_fin : a ∈ t := by simpa using ha
      have hb_fin : b ∈ t := by simpa using hb
      have ha' : (⟨a, hsub ha_fin⟩ : {x // x ∈ (S : Set V)}) ∈ lift t := by simp [lift, ha_fin]
      have hb' : (⟨b, hsub hb_fin⟩ : {x // x ∈ (S : Set V)}) ∈ lift t := by simp [lift, hb_fin]
      exact hind ha' hb' (fun h => hne (congrArg Subtype.val h)) hadj
    · intro hind a ha b hb hne hadj
      have ha_fin : a ∈ lift t := by simpa using ha
      have hb_fin : b ∈ lift t := by simpa using hb
      exact hind (by simpa [lift] using (Finset.mem_filter.mp ha_fin).2)
        (by simpa [lift] using (Finset.mem_filter.mp hb_fin).2)
        (fun h => hne (Subtype.ext h)) hadj
  unfold indepPolyOn indepSetsOn
  refine Finset.sum_bij (fun t _ => t.image Subtype.val) ?_ ?_ ?_ ?_
  · intro t ht
    have ht' := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_powerset.mpr fun x hx ↦ by
        rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
        simp
    · intro a ha b hb hne hadj
      rcases Finset.mem_image.mp ha with ⟨a', ha', rfl⟩
      rcases Finset.mem_image.mp hb with ⟨b', hb', hb_eq⟩
      subst hb_eq
      exact ht'.2 ha' hb' (fun h => hne (congrArg Subtype.val h)) hadj
  · intro _t _ht _u _hu h
    exact Finset.image_injective Subtype.val_injective h
  · intro t ht
    have ht' := Finset.mem_filter.mp ht
    have hsub : t ⊆ S := Finset.mem_powerset.mp ht'.1
    refine ⟨lift t, ?_, hmap_lift hsub⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (fun _x _hx ↦ by simp), (hlift_indep hsub).mpr ht'.2⟩
  · intro t _ht
    rw [Finset.card_image_of_injOn]
    simp

/-- Ordinary independence polynomials of induced graphs recover the
support-restricted independence polynomial. -/
theorem indepPoly_induce_finset {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    indepPoly (G.induce (S : Set V)) = indepPolyOn G S := by
  classical
  rw [indepPoly_eq_indepPolyOn_univ]
  exact indepPolyOn_univ_induce_finset G S

/-- Vertex insertion recurrence for independence polynomials of induced
subgraphs. -/
theorem indepPoly_induce_insert {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {v : V} (hv : v ∉ S) :
    indepPoly (G.induce ((insert v S : Finset V) : Set V)) =
      indepPoly (G.induce (S : Set V)) +
        X * indepPoly (G.induce ((S.filter fun w => ¬ G.Adj v w) : Set V)) := by
  rw [indepPoly_induce_finset G (insert v S),
    indepPoly_induce_finset G S,
    indepPoly_induce_finset G (S.filter fun w => ¬ G.Adj v w),
    indepPolyOn_insert G hv]

/-- A finite set of edges is a matching if distinct edges do not share a vertex. -/
def IsMatchingEdgeFinset {V : Type u} (G : _root_.SimpleGraph V)
    (M : Finset G.edgeSet) : Prop :=
  ∀ ⦃e₁ : G.edgeSet⦄, e₁ ∈ M → ∀ ⦃e₂ : G.edgeSet⦄, e₂ ∈ M →
    e₁ ≠ e₂ → ¬ (((e₁ : Sym2 V) ∩ (e₂ : Sym2 V) : Set V).Nonempty)

/-- Edge-set matchings are exactly independent sets in the line graph. -/
theorem isMatchingEdgeFinset_iff_lineGraph_isIndepSet {V : Type u}
    (G : _root_.SimpleGraph V) (M : Finset G.edgeSet) :
    IsMatchingEdgeFinset G M ↔ G.lineGraph.IsIndepSet (M : Set G.edgeSet) := by
  constructor
  · intro h e₁ he₁ e₂ he₂ hne hadj
    exact h he₁ he₂ hne hadj.2
  · intro h e₁ he₁ e₂ he₂ hne hnonempty
    exact h he₁ he₂ hne ⟨hne, hnonempty⟩

/-- Matching-generating polynomial, represented as the independence polynomial
of the line graph. -/
def matchingGeneratingPolynomial {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact indepPoly G.lineGraph

/-- Weighted matching-generating polynomial, represented as the weighted
independence polynomial of the line graph. -/
def weightedMatchingGeneratingPolynomial
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ) : ℝ[X] := by
  classical
  exact weightedIndepPoly G.lineGraph wt

/-- Intrinsic matching-generating polynomial as a sum over finite matchings of
edge sets. -/
def matchingPolynomialByEdges {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact ∑ M ∈ (Finset.univ.filter fun M : Finset G.edgeSet =>
      IsMatchingEdgeFinset G M),
    (X : ℝ[X]) ^ M.card

/-- Intrinsic weighted matching-generating polynomial as a sum over finite
matchings of edge sets. -/
def weightedMatchingPolynomialByEdges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ) : ℝ[X] := by
  classical
  exact ∑ M ∈ (Finset.univ.filter fun M : Finset G.edgeSet =>
      IsMatchingEdgeFinset G M),
    (∏ e ∈ M, C (wt e)) * (X : ℝ[X]) ^ M.card

/-- Total weight of the size-`k` edge matchings of a graph. -/
def weightedMatchingNumber
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ) (k : ℕ) : ℝ := by
  classical
  exact ∑ M ∈ (Finset.univ.filter fun M : Finset G.edgeSet ↦
      IsMatchingEdgeFinset G M),
    if M.card = k then ∏ e ∈ M, wt e else 0

/-- Coefficients of the intrinsic weighted matching polynomial are weighted
matching numbers. -/
theorem coeff_weightedMatchingPolynomialByEdges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ) (k : ℕ) :
    (weightedMatchingPolynomialByEdges G wt).coeff k =
      weightedMatchingNumber G wt k := by
  classical
  rw [weightedMatchingPolynomialByEdges, weightedMatchingNumber]
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro M hM
  have hprod : (∏ e ∈ M, C (wt e)) = C (∏ e ∈ M, wt e) := by simp only [map_prod]
  rw [hprod, coeff_C_mul]
  simp [coeff_X_pow, eq_comm]

/-- The intrinsic edge-matching polynomial agrees with the line-graph
independence-polynomial definition. -/
theorem matchingPolynomialByEdges_eq_matchingGeneratingPolynomial
    {V : Type u} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    matchingPolynomialByEdges G = matchingGeneratingPolynomial G := by
  classical
  simp [matchingPolynomialByEdges, matchingGeneratingPolynomial, indepPoly,
    isMatchingEdgeFinset_iff_lineGraph_isIndepSet]

/-- The intrinsic weighted edge-matching polynomial agrees with the weighted
line-graph independence-polynomial definition. -/
theorem weightedMatchingPolynomialByEdges_eq_weightedMatchingGeneratingPolynomial
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ) :
    weightedMatchingPolynomialByEdges G wt =
      weightedMatchingGeneratingPolynomial G wt := by
  classical
  simp [weightedMatchingPolynomialByEdges,
    weightedMatchingGeneratingPolynomial, weightedIndepPoly,
    weightedIndepPolyOn, indepSetsOn,
    isMatchingEdgeFinset_iff_lineGraph_isIndepSet]

/-- The empty independent set gives the constant coefficient of the
independence polynomial. -/
theorem indepPoly_coeff_zero {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : (indepPoly G).coeff 0 = 1 := by
  classical
  rw [indepPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single ∅]
  · simp
  · intro s hs hne
    have hs_nonzero : s.card ≠ 0 := by simp_all
    have hzero : ¬ 0 = s.card := fun h ↦ hs_nonzero h.symm
    simp [Polynomial.coeff_X_pow, hzero]
  · simp

/-- Independence polynomials are nonzero. -/
theorem indepPoly_ne_zero {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : indepPoly G ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) h
  simp [indepPoly_coeff_zero] at hcoeff

/-- Independence polynomials have nonnegative coefficients by construction. -/
theorem indepPoly_hasNonnegCoeffs {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    HasNonnegCoeffs (indepPoly G) := by
  classical
  intro n
  rw [indepPoly, Polynomial.finsetSum_coeff]
  simp

/-- Independence polynomials have positive leading coefficient. -/
theorem indepPoly_hasPosLeadingCoeff {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : HasPosLeadingCoeff (indepPoly G) :=
  (indepPoly_hasNonnegCoeffs G).pos_leadingCoeff (indepPoly_ne_zero G)

/-- Line graphs are claw-free.

If three distinct neighbors of an edge in the line graph were pairwise
nonadjacent, choosing for each neighbor a shared endpoint with the original edge
would inject three vertices into the two endpoints of the original edge. -/
theorem lineGraph_clawFree {V : Type u} (G : _root_.SimpleGraph V) :
    ClawFree G.lineGraph := by
  classical
  intro v s hneigh hind
  have hs_card : Fintype.card {w // w ∈ s} = s.card := by simp
  have hv_card :
      Fintype.card {x // x ∈ (v : Sym2 V).toFinset} =
        (v : Sym2 V).toFinset.card := by simp
  have hshared : ∀ w : {w // w ∈ s},
      ∃ x : V, x ∈ (v : Sym2 V) ∧ x ∈ ((w.val : G.edgeSet) : Sym2 V) := by
    intro w
    exact (_root_.SimpleGraph.lineGraph_adj_iff_exists.mp (hneigh w.val w.property)).2
  let φ : {w // w ∈ s} → {x // x ∈ (v : Sym2 V).toFinset} := fun w =>
    ⟨Classical.choose (hshared w), by
      rw [Sym2.mem_toFinset]
      exact (Classical.choose_spec (hshared w)).1⟩
  have hφ_edge : ∀ w : {w // w ∈ s}, (φ w : V) ∈ ((w.val : G.edgeSet) : Sym2 V) := by
    intro w
    exact (Classical.choose_spec (hshared w)).2
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    by_contra hval_ne
    have hcommon : (φ a : V) ∈ ((b.val : G.edgeSet) : Sym2 V) := by simp_all
    have hadj : G.lineGraph.Adj a.val b.val := by
      rw [_root_.SimpleGraph.lineGraph_adj_iff_exists]
      exact ⟨hval_ne, ⟨(φ a : V), hφ_edge a, hcommon⟩⟩
    exact hind.isIndepSet a.property b.property hval_ne hadj
  have hcard_le_endpoints : s.card ≤ (v : Sym2 V).toFinset.card := by
    rw [← hs_card, ← hv_card]
    exact Fintype.card_le_of_injective φ hφ_inj
  have hv_not_diag : ¬ (v : Sym2 V).IsDiag :=
    G.not_isDiag_of_mem_edgeSet v.property
  have hcard_le_two : s.card ≤ 2 := by
    simpa [Sym2.card_toFinset_of_not_isDiag (v : Sym2 V) hv_not_diag] using
      hcard_le_endpoints
  rw [hind.card_eq] at hcard_le_two
  simp_all

/-- Graph-form Chudnovsky--Seymour statement still needed for #52.

This is the real graph-theoretic leaf: it should be proved by the usual
claw-free deletion/compatibility induction, using the polynomial
Chudnovsky--Seymour interlacing engine from `RealRooted.ChudnovskySeymour`. -/
def ClawFreeIndepPolySplitsStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V), ClawFree G → (indepPoly G).Splits

/-- Chudnovsky--Seymour graph theorem: finite claw-free graph independence
polynomials are real-rooted. -/
theorem clawFree_indepPoly_splits : ClawFreeIndepPolySplitsStatement.{u} := by
  intro V _hfinite _hdec G hG
  classical
  rw [indepPoly_eq_indepPolyOn_univ]
  exact supportIndepPoly_splits_of_clawFree hG Finset.univ

/-- Conditional Heilmann--Lieb matching-generating corollary.

Once the graph-form Chudnovsky--Seymour statement is proved, the matching
polynomial route is immediate from the definition as the independence polynomial
of the line graph and from `lineGraph_clawFree`. -/
theorem matchingGeneratingPolynomial_splits_of_clawFreeIndepPolySplits
    (hcs : ClawFreeIndepPolySplitsStatement.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    (matchingGeneratingPolynomial G).Splits := by
  classical
  exact hcs (G := G.lineGraph) (lineGraph_clawFree G)

/-- Heilmann--Lieb theorem for the matching-generating polynomial. -/
theorem matchingGeneratingPolynomial_splits
    {V : Type u} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    (matchingGeneratingPolynomial G).Splits :=
  matchingGeneratingPolynomial_splits_of_clawFreeIndepPolySplits
    clawFree_indepPoly_splits G

/-- Heilmann--Lieb theorem for the intrinsic edge-matching polynomial. -/
theorem matchingPolynomialByEdges_splits
    {V : Type u} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    (matchingPolynomialByEdges G).Splits := by
  rw [matchingPolynomialByEdges_eq_matchingGeneratingPolynomial]
  exact matchingGeneratingPolynomial_splits G

/-- Weighted Heilmann--Lieb theorem for the line-graph matching polynomial. -/
theorem weightedMatchingGeneratingPolynomial_splits
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) :
    (weightedMatchingGeneratingPolynomial G wt).Splits := by
  classical
  exact clawFree_weightedIndepPoly_splits
    (G := G.lineGraph) (lineGraph_clawFree G) wt hwt

/-- Weighted Heilmann--Lieb theorem for the intrinsic edge-matching
polynomial. -/
theorem weightedMatchingPolynomialByEdges_splits
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) :
    (weightedMatchingPolynomialByEdges G wt).Splits := by
  rw [weightedMatchingPolynomialByEdges_eq_weightedMatchingGeneratingPolynomial]
  exact weightedMatchingGeneratingPolynomial_splits G wt hwt

/-- The intrinsic weighted matching polynomial is PF for nonnegative edge
weights. -/
theorem weightedMatchingPolynomialByEdges_isPFPolynomial
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) :
    IsPFPolynomial (weightedMatchingPolynomialByEdges G wt) := by
  apply IsPFPolynomial.of_realRooted_nonneg
  · intro k
    rw [coeff_weightedMatchingPolynomialByEdges, weightedMatchingNumber]
    apply Finset.sum_nonneg
    intro M hM
    split_ifs
    · apply Finset.prod_nonneg
      intro e he
      exact hwt e
    · positivity
  · exact weightedMatchingPolynomialByEdges_splits G wt hwt

end Graph
end RealRooted
