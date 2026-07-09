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

/-- The weighted support-restricted independence polynomial with all weights
equal to `1` is the unweighted support-restricted independence polynomial. -/
theorem weightedIndepPolyOn_one {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    weightedIndepPolyOn G S (fun _ => 1) = indepPolyOn G S := by
  unfold weightedIndepPolyOn indepPolyOn
  apply Finset.sum_congr rfl
  intro s _hs
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
    have hs_nonzero : s.card ≠ 0 := by
      rwa [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]
    have hnot : ¬ s.card ≤ 0 := by
      simpa [Nat.pos_iff_ne_zero] using Nat.pos_of_ne_zero hs_nonzero
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
    (weightedIndepPolyOn_hasNonnegCoeffs (G := G) (S := S) (wt := fun _ => 1)
      (by intro _ _; norm_num))

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
    have hs' : s = ∅ ∧ G.IsIndepSet (s : Set V) := by
      simpa [indepSetsOn] using hs
    exact False.elim (hne hs'.1)
  · intro hnot
    simp [indepSetsOn] at hnot

/-- The empty support independence polynomial splits. -/
theorem indepPolyOn_empty_splits {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    (indepPolyOn G (∅ : Finset V)).Splits := by
  rw [indepPolyOn_empty]
  exact Polynomial.Splits.one

private theorem compatible_self_X_mul_of_splits {p : ℝ[X]} (hp : p.Splits) :
    Compatible p (X * p) := by
  intro α β _hα _hβ
  have hlin : (C α + C β * X : ℝ[X]).Splits := by
    by_cases hβ0 : β = 0
    · simp [hβ0]
    · have hβα : β * (α / β) = α := by field_simp [hβ0]
      have hfactor : (C α + C β * X : ℝ[X]) = C β * (X + C (α / β)) := by
        rw [mul_add, ← C_mul, hβα]
        ring
      rw [hfactor]
      exact (Polynomial.Splits.C β).mul <| by
        simp
  have hsum : C α * p + C β * (X * p) = (C α + C β * X) * p := by
    ring
  have hsplit : (C α * p + C β * (X * p)).Splits := by
    rw [hsum]
    exact hlin.mul hp
  by_cases hzero : C α * p + C β * (X * p) = 0
  · exact Or.inl hzero
  · exact Or.inr ⟨hzero, hsplit⟩

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
  have hsum : C α * p + C β * p = C (α + β) * p := by
    rw [← add_mul, ← C_add]
  by_cases hzero : α + β = 0
  · left
    rw [hsum, hzero]
    simp
  · right
    rw [hsum]
    exact isRealRooted_C_mul hp_ne hp hzero

private theorem compatible_X_mul_of_compatible {f g : ℝ[X]} (h : Compatible f g) :
    Compatible (X * f) (X * g) := by
  intro α β hα hβ
  have hsum : C α * (X * f) + C β * (X * g) =
      X * (C α * f + C β * g) := by
    ring
  rcases h α β hα hβ with hzero | hrr
  · left
    rw [hsum, hzero]
    simp
  · right
    rw [hsum]
    exact isRealRooted_X_mul hrr.1 hrr.2

/-- The support-restricted definition recovers `indepPoly` on the full vertex set. -/
theorem indepPoly_eq_indepPolyOn_univ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    indepPoly G = indepPolyOn G Finset.univ := by
  unfold indepPoly indepPolyOn indepSetsOn
  apply Finset.sum_congr
  · ext s
    simp
  · intro s hs
    rfl

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
    exact hneigh x hx
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

/-- Neighbors of a vertex inside a finite support. -/
def neighborSetOn {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : Finset V :=
  S.filter fun w => G.Adj v w

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
      have hx_notK : x ∉ K := by
        intro hxK
        exact hx'.2 (Finset.mem_sdiff.mpr ⟨hxK, hxSL.2⟩)
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
    have hx' : x ∈ neighborOutsideCliqueOn G (S \ K) (neighborOutsideCliqueOn G S K k) n := by
      simpa using hx
    have hy' : y ∈ neighborOutsideCliqueOn G (S \ K) (neighborOutsideCliqueOn G S K k) n := by
      simpa using hy
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
      · exact hxN.2
      · exact hyN.2
    have hxk : x ≠ k := fun hxk => hxSdiff.2 (by simpa [hxk] using hk)
    have hyk : y ≠ k := fun hyk => hySdiff.2 (by simpa [hyk] using hk)
    have hind : G.IsNIndepSet 3 ({k, x, y} : Finset V) := by
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.isIndepSet_iff]
        intro a ha b hb hne hadj
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · exact hne rfl
        · exact hkx_not hadj
        · exact hky_not hadj
        · exact hkx_not hadj.symm
        · exact hne rfl
        · exact hnot hadj
        · exact hky_not hadj.symm
        · exact hnot hadj.symm
        · exact hne rfl
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
      exact h (by simp) (by simp [hw]) (fun hvw => hv (by simpa [hvw] using hw)) hadj
  · rintro ⟨hind, hnonadj⟩ a ha b hb hne hadj
    simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact hne rfl
      · exact hnonadj b hb hadj
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
      · have hsubS : t.erase v ⊆ S := by
          intro w hw
          have hwt : w ∈ t := Finset.mem_of_mem_erase hw
          have hwins : w = v ∨ w ∈ S := Finset.mem_insert.mp (htsub hwt)
          rcases hwins with hwv | hS
          · have hv_mem_erase : v ∈ t.erase v := by
              exact hwv ▸ hw
            exact False.elim (Finset.notMem_erase v t hv_mem_erase)
          · exact hS
        have hnotadj : ∀ w ∈ t.erase v, ¬ G.Adj v w := by
          intro w hw
          have hne : v ∉ t.erase v := Finset.notMem_erase v t
          have ht_eq : insert v (t.erase v) = t := Finset.insert_erase hvt
          have htind' : G.IsIndepSet ((insert v (t.erase v) : Finset V) : Set V) := by
            simpa [ht_eq] using htind
          exact ((isIndepSet_insert_iff hne).mp htind').2 w hw
        exact ⟨fun w hw => Finset.mem_filter.mpr ⟨hsubS hw, hnotadj w hw⟩,
          ((isIndepSet_insert_iff (Finset.notMem_erase v t)).mp
            (by simpa [Finset.insert_erase hvt] using htind)).1⟩
      · exact Finset.insert_erase hvt
    · refine Or.inl ?_
      exact ⟨fun w hw => by
        rcases Finset.mem_insert.mp (htsub hw) with hwv | hS
        · exact False.elim (hvt (by simpa [hwv] using hw))
        · exact hS, htind⟩
  · rintro (hleft | hright)
    · exact ⟨fun w hw => Finset.mem_insert.mpr (Or.inr (hleft.1 hw)), hleft.2⟩
    · rcases hright with ⟨u, hu, htu⟩
      subst htu
      have hvu : v ∉ u := fun h => hv (Finset.mem_filter.mp (hu.1 h)).1
      refine ⟨?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with hwv | hwu
        · rw [hwv]
          exact Finset.mem_insert_self v S
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mp (hu.1 hwu)).1)
      · exact (isIndepSet_insert_iff hvu).mpr
          ⟨hu.2, fun w hw => (Finset.mem_filter.mp (hu.1 hw)).2⟩

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
    rcases Finset.mem_image.mp htimg with ⟨u, _hu, rfl⟩
    exact hvt_not (Finset.mem_insert_self v u)
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    have hsub : u ⊆ S.filter fun w => ¬ G.Adj v w :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
    have hvu : v ∉ u := fun h => hv (Finset.mem_filter.mp (hsub h)).1
    rw [Finset.card_insert_of_notMem hvu, Finset.prod_insert hvu]
    ring_nf
  · intro u hu w hw h
    have hsubu : u ⊆ S.filter fun x => ¬ G.Adj v x :=
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
    intro v hv
    simp [hwt v (hsub hv)]
  rw [hprod]

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
    intro w hw
    have hne : w ≠ v := fun h => hv (by simpa [h] using hw)
    simp [Function.update_of_ne hne]
  have hN : weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w)
      (Function.update wt v a) =
        weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt := by
    apply weightedIndepPolyOn_congr
    intro w hw
    have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
    have hne : w ≠ v := fun h => hv (by simpa [h] using hwS)
    simp [Function.update_of_ne hne]
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
    · left
      simp [hα0, hβ0]
    · right
      have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
      have hXN :
          (X * weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt) ≠ 0 ∧
            (X * weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt).Splits :=
        isRealRooted_X_mul
          (weightedIndepPolyOn_ne_zero G (S.filter fun w => ¬ G.Adj v w) wt) hN
      simpa [hα0] using isRealRooted_C_mul hXN.1 hXN.2 hβpos.ne'
  · right
    have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    have hbase_ne :
        weightedIndepPolyOn G (insert v S) (Function.update wt v (β / α)) ≠ 0 :=
      weightedIndepPolyOn_ne_zero G (insert v S) (Function.update wt v (β / α))
    have hbase_split :
        (weightedIndepPolyOn G (insert v S) (Function.update wt v (β / α))).Splits :=
      hinsert (β / α) (div_nonneg hβ hαpos.le)
    have hscaled := isRealRooted_C_mul hbase_ne hbase_split hαpos.ne'
    have hrec := weightedIndepPolyOn_insert_update G wt hv (β / α)
    have htarget :
        C α * weightedIndepPolyOn G (insert v S) (Function.update wt v (β / α)) =
          C α * weightedIndepPolyOn G S wt +
            C β * (X * weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt) := by
      rw [hrec, mul_add]
      congr 1
      calc
        C α * (C (β / α) * X *
            weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt) =
            (C α * C (β / α)) * X *
              weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt := by
          noncomm_ring
        _ = C (α * (β / α)) * X *
              weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt := by
          rw [C_mul]
        _ = C β * X *
              weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt := by
          have hαβ : α * (β / α) = β := by
            field_simp [hα0]
          rw [hαβ]
        _ = C β *
              (X * weightedIndepPolyOn G (S.filter fun w => ¬ G.Adj v w) wt) := by
          rw [mul_assoc]
    simpa [htarget] using hscaled

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
          hK (by simpa using hk) (by simpa using hwK) (fun h => hwk h.symm)
        simp [deleteClosedNeighborSupport, neighborOutsideCliqueOn, neighborSetOn,
          hwS, hwK, hwk, hkw]
    · by_cases hAdj : G.Adj k w
      · simp [deleteClosedNeighborSupport, neighborOutsideCliqueOn, neighborSetOn,
          hwS, hwK, hAdj]
      · have hwk : w ≠ k := fun h => hwK (by simpa [h] using hk)
        simp [deleteClosedNeighborSupport, neighborOutsideCliqueOn, neighborSetOn,
          hwS, hwK, hAdj, hwk]
  · have hwK : w ∉ K := fun h => hwS (hKS h)
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
    have hx_ne : x ≠ v := fun hxv => hvK (by simpa [hxv] using hx)
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
  · intro S _hK _hKS
    simp
  · intro v K hvK ih S hK hKS
    have hvS : v ∈ S := hKS (Finset.mem_insert_self v K)
    have hK_old : G.IsClique (K : Set V) := by
      exact hK.subset fun w hw => by simp [hw]
    have hKS_old : K ⊆ S.erase v := by
      intro w hw
      refine Finset.mem_erase.mpr ⟨?_, hKS (Finset.mem_insert.mpr (Or.inr hw))⟩
      exact fun hwv => hvK (by simpa [hwv] using hw)
    have hrec_single : indepPolyOn G S =
        indepPolyOn G (S.erase v) +
          X * indepPolyOn G (deleteClosedNeighborSupport G S v) := by
      have h := indepPolyOn_insert
        (G := G) (S := S.erase v) (v := v) (Finset.notMem_erase v S)
      simpa [deleteClosedNeighborSupport, Finset.insert_erase hvS] using h
    rw [hrec_single, ih (S.erase v) hK_old hKS_old]
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
    rw [Finset.sum_eq_multiset_sum]
    simp [Finset.toList]
  simp [cliqueDeletionFamily, hsum, indepPolyOn_sdiff_clique G S K hK hKS]

private theorem weightedSum_map_const (a : ℝ) :
    ∀ fs : List ℝ[X], weightedSum (fs.map fun p => (a, p)) = C a * fs.sum
  | [] => by simp
  | p :: fs => by
      simp [weightedSum_map_const a fs, mul_add]

private theorem weightedSum_append :
    ∀ l m : List (ℝ × ℝ[X]), weightedSum (l ++ m) = weightedSum l + weightedSum m
  | [], m => by simp
  | (a, p) :: l, m => by
      simp [weightedSum_append l m, add_assoc]

private theorem sdiff_right_sdiff_eq_sdiff_union {V : Type u} [DecidableEq V]
    (S K L : Finset V) : (S \ L) \ (K \ L) = S \ (K ∪ L) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨⟨hxS, hxL⟩, hxKL⟩
    exact ⟨hxS, fun hx => by
      rcases hx with hxK | hxL'
      · exact hxKL ⟨hxK, hxL⟩
      · exact hxL hxL'⟩
  · rintro ⟨hxS, hxKL⟩
    exact ⟨⟨hxS, fun hxL => hxKL (Or.inr hxL)⟩,
      fun hxK => hxKL (Or.inl hxK.1)⟩

private theorem sdiff_left_sdiff_eq_sdiff_union {V : Type u} [DecidableEq V]
    (S K L : Finset V) : (S \ K) \ (L \ K) = S \ (K ∪ L) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨⟨hxS, hxK⟩, hxLK⟩
    exact ⟨hxS, fun hx => by
      rcases hx with hxK' | hxL
      · exact hxK hxK'
      · exact hxLK ⟨hxL, hxK⟩⟩
  · rintro ⟨hxS, hxKL⟩
    exact ⟨⟨hxS, fun hxK => hxKL (Or.inl hxK)⟩,
      fun hxL => hxKL (Or.inr hxL.1)⟩

private theorem pairwiseCompatible_of_forall_mem {fs : List ℝ[X]}
    (h : ∀ f ∈ fs, ∀ g ∈ fs, Compatible f g) : PairwiseCompatible fs := by
  intro i j _hij
  exact h (fs.get i) (List.get_mem fs i) (fs.get j) (List.get_mem fs j)

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
    · exact hbase_del v (Finset.mem_toList.mp hvList)
  · rcases hg with rfl | ⟨v, hvList, rfl⟩
    · exact (hbase_del u (Finset.mem_toList.mp huList)).comm
    · exact compatible_X_mul_of_compatible
        (hdel_pair u (Finset.mem_toList.mp huList) v (Finset.mem_toList.mp hvList))

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
    simpa [hsupport] using hbase_neighbor v hv
  · intro u hu v hv
    have huSupport :=
      deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G hK hKS hu
    have hvSupport :=
      deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique G hK hKS hv
    simpa [huSupport, hvSupport] using hneighbor_pair u hu v hv

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
      simpa [hvSupport] using hbase_neighbor_x v hvK
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
  have hweighted := hfam (fs.map fun p => ((1 : ℝ), p)) (by
    intro ap hap
    rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
    exact hp) (by
    intro ap hap
    rcases List.mem_map.mp hap with ⟨p, _hp, rfl⟩
    norm_num)
  have hsum : weightedSum (fs.map fun p => ((1 : ℝ), p)) = indepPolyOn G S := by
    rw [weightedSum_map_one]
    exact cliqueDeletionFamily_sum G S K hK hKS
  rw [hsum] at hweighted
  rcases hweighted with hzero | ⟨_, hsplits⟩
  · exact False.elim (indepPolyOn_ne_zero G S hzero)
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
    sdiff_right_sdiff_eq_sdiff_union S K L
  have hL_support : (S \ K) \ (L \ K) = S \ (K ∪ L) :=
    sdiff_left_sdiff_eq_sdiff_union S K L
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

/-- Every nonempty finite support admits a nonempty simplicial clique.  This is
the graph-theoretic existence input still needed to finish the graph-form
Chudnovsky--Seymour theorem. -/
def SupportSimplicialCliqueExists {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ {S : Finset V}, S.Nonempty → ∃ K : Finset V,
    K.Nonempty ∧ IsSimplicialCliqueOn G S K

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
  · have hK_empty : K = ∅ := by
      ext x
      constructor
      · intro hx
        have hxUnion : x ∈ K ∪ L := Finset.mem_union.mpr (Or.inl hx)
        simp [hUnion_empty] at hxUnion
      · simp
    have hL_empty : L = ∅ := by
      ext x
      constructor
      · intro hx
        have hxUnion : x ∈ K ∪ L := Finset.mem_union.mpr (Or.inr hx)
        simp [hUnion_empty] at hxUnion
      · simp
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
      sdiff_right_sdiff_eq_sdiff_union S K L
    have hL_support : (S \ K) \ (L \ K) = S \ (K ∪ L) :=
      sdiff_left_sdiff_eq_sdiff_union S K L
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
      simpa [hK_support] using h
    have hL_delete_support : ∀ v ∈ L \ K,
        deleteClosedNeighborSupport G (S \ K) v =
          (S \ (K ∪ L)) \ neighborOutsideCliqueOn G (S \ K) (L \ K) v := by
      intro v hv
      have h := deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
        G hL_simp.2.1 hL_simp.1 hv
      simpa [hL_support] using h
    have hKdel : ∀ v ∈ K \ L,
        (indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)).Splits := by
      intro v hv
      have hsub : deleteClosedNeighborSupport G (S \ L) v ⊆ S := by
        intro w hw
        exact (Finset.mem_sdiff.mp
          (Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1)).1
      exact hSplit (deleteClosedNeighborSupport G (S \ L) v) hsub
    have hLdel : ∀ v ∈ L \ K,
        (indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)).Splits := by
      intro v hv
      have hsub : deleteClosedNeighborSupport G (S \ K) v ⊆ S := by
        intro w hw
        exact (Finset.mem_sdiff.mp
          (Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1)).1
      exact hSplit (deleteClosedNeighborSupport G (S \ K) v) hsub
    have hbase_k_x : ∀ v ∈ K \ L,
        Compatible (indepPolyOn G (S \ (K ∪ L)))
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ L) v)) := by
      intro v hv
      have hx := hXSmall (S \ (K ∪ L)) hsmall (hK_neighbor_simp v hv)
      simpa [hK_delete_support v hv] using hx
    have hbase_l_x : ∀ v ∈ L \ K,
        Compatible (indepPolyOn G (S \ (K ∪ L)))
          (X * indepPolyOn G (deleteClosedNeighborSupport G (S \ K) v)) := by
      intro v hv
      have hx := hXSmall (S \ (K ∪ L)) hsmall (hL_neighbor_simp v hv)
      simpa [hL_delete_support v hv] using hx
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
        · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩
          · exact hbase_k_x v (Finset.mem_toList.mp hvList)
          · exact hbase_l_x v (Finset.mem_toList.mp hvList)
      · rcases htailF with ⟨u, huList, rfl⟩ | ⟨u, huList, rfl⟩
        · have hu : u ∈ K \ L := Finset.mem_toList.mp huList
          rcases hg with rfl | htailG
          · exact (hbase_k_x u hu).comm
          · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩
            · exact hK_pair_x u hu v (Finset.mem_toList.mp hvList)
            · exact hKL_pair_x u hu v (Finset.mem_toList.mp hvList)
        · have hu : u ∈ L \ K := Finset.mem_toList.mp huList
          rcases hg with rfl | htailG
          · exact (hbase_l_x u hu).comm
          · rcases htailG with ⟨v, hvList, rfl⟩ | ⟨v, hvList, rfl⟩
            · exact (hKL_pair_x v (Finset.mem_toList.mp hvList) u hu).comm
            · exact hL_pair_x u hu v (Finset.mem_toList.mp hvList)
    exact compatible_indepPolyOn_sdiff_pair_of_pairDeletion_pairwiseCompatible
      G S K L hK.2.1 hL.2.1 hK.1 hL.1 hbase hKdel hLdel hpair

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
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hw).1).1
      simpa [hsupport] using hSplit ((S \ K) \ neighborOutsideCliqueOn G S K v) hsub
    exact compatible_indepPolyOn_X_mul_sdiff_of_cliqueDeletion_pairwiseCompatible
      G S K hK.2.1 hK.1 hbase hdel hpair

/-- The support-level claw-free independence-polynomial theorem, conditional
only on the graph-theoretic existence of nonempty simplicial cliques on
nonempty finite supports.  This is the simultaneous induction assembly after
Chudnovsky--Seymour Lemma 2.5. -/
theorem supportIndepPoly_splits_of_simplicialCliqueExists
    {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (hG : ClawFree G)
    (hexists : SupportSimplicialCliqueExists G) :
    ∀ S : Finset V, (indepPolyOn G S).Splits := by
  classical
  have hmain : ∀ n : ℕ, ∀ S : Finset V, S.card = n →
      SupportIndepPolySplits G S ∧
        SupportSimplicialPairCompatible G S ∧
          SupportSimplicialXCompatible G S := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih S hcard
    have hPairSmall : ∀ T : Finset V, T.card < S.card →
        SupportSimplicialPairCompatible G T := by
      intro T hT
      have hTn : T.card < n := by simpa [hcard] using hT
      intro K L hK hL
      exact (ih T.card hTn T rfl).2.1 hK hL
    have hXSmall : ∀ T : Finset V, T.card < S.card →
        SupportSimplicialXCompatible G T := by
      intro T hT
      have hTn : T.card < n := by simpa [hcard] using hT
      intro K hK
      exact (ih T.card hTn T rfl).2.2 hK
    have hSplitSelf : (indepPolyOn G S).Splits := by
      by_cases hS_empty : S = ∅
      · subst hS_empty
        exact indepPolyOn_empty_splits G
      · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
        rcases hexists hS_nonempty with ⟨K, hK_nonempty, hK⟩
        have hsmall : (S \ K).card < S.card :=
          Finset.card_lt_card (Finset.sdiff_ssubset hK.1 hK_nonempty)
        have hsmalln : (S \ K).card < n := by simpa [hcard] using hsmall
        have hrec := ih (S \ K).card hsmalln (S \ K) rfl
        have hbase : (indepPolyOn G (S \ K)).Splits :=
          hrec.1 (S \ K) Subset.rfl
        have hneighbor_simp : ∀ v ∈ K,
            IsSimplicialCliqueOn G (S \ K)
              (neighborOutsideCliqueOn G S K v) := by
          intro v hv
          exact hG.simplicialClique_neighborOutside hK hv
        have hbase_neighbor : ∀ v ∈ K,
            Compatible (indepPolyOn G (S \ K))
              (X * indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)) := by
          intro v hv
          exact hrec.2.2 (hneighbor_simp v hv)
        have hneighbor_pair : ∀ u ∈ K, ∀ v ∈ K,
            Compatible
              (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K u))
              (indepPolyOn G ((S \ K) \ neighborOutsideCliqueOn G S K v)) := by
          intro u hu v hv
          exact hrec.2.1 (hneighbor_simp u hu) (hneighbor_simp v hv)
        have hpair : PairwiseCompatible (cliqueDeletionFamily G S K) :=
          cliqueDeletionFamily_pairwiseCompatible_of_neighborOutside_compatible
            G hK.2.1 hK.1 hbase hbase_neighbor hneighbor_pair
        have hdel : ∀ v ∈ K,
            (indepPolyOn G (deleteClosedNeighborSupport G S v)).Splits := by
          intro v hv
          have hsupport :=
            deleteClosedNeighborSupport_eq_sdiff_neighborOutsideCliqueOn_of_clique
              G hK.2.1 hK.1 hv
          have hsub :
              (S \ K) \ neighborOutsideCliqueOn G S K v ⊆ S \ K := by
            intro w hw
            exact (Finset.mem_sdiff.mp hw).1
          simpa [hsupport] using
            hrec.1 ((S \ K) \ neighborOutsideCliqueOn G S K v) hsub
        exact indepPolyOn_splits_of_cliqueDeletion_pairwiseCompatible
          G S K hK.2.1 hK.1 hbase hdel hpair
    have hSplit : SupportIndepPolySplits G S := by
      intro T hTS
      by_cases hTS_eq : T = S
      · subst hTS_eq
        exact hSplitSelf
      · have hproper : T ⊂ S :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hTS_eq⟩
        have hTsmall : T.card < S.card := Finset.card_lt_card hproper
        have hTn : T.card < n := by simpa [hcard] using hTsmall
        exact (ih T.card hTn T rfl).1 T Subset.rfl
    have hPair : SupportSimplicialPairCompatible G S :=
      supportSimplicialPairCompatible_of_smaller hG hSplit hPairSmall hXSmall
    have hX : SupportSimplicialXCompatible G S :=
      supportSimplicialXCompatible_of_smaller hG hSplit hPairSmall hXSmall
    exact ⟨hSplit, hPair, hX⟩
  intro S
  exact (hmain S.card S rfl).1 S Subset.rfl

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
      have ha' : (⟨a, hsub ha_fin⟩ : {x // x ∈ (S : Set V)}) ∈ lift t := by
        simp [lift, ha_fin]
      have hb' : (⟨b, hsub hb_fin⟩ : {x // x ∈ (S : Set V)}) ∈ lift t := by
        simp [lift, hb_fin]
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
    · exact Finset.mem_powerset.mpr fun x hx => by
        rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
        exact a.property
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
      ⟨Finset.mem_powerset.mpr (fun _x _hx => by simp), (hlift_indep hsub).mpr ht'.2⟩
  · intro t _ht
    rw [Finset.card_image_of_injOn]
    exact fun a _ b _ h => Subtype.ext h

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

/-- Intrinsic matching-generating polynomial as a sum over finite matchings of
edge sets. -/
def matchingPolynomialByEdges {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℝ[X] := by
  classical
  exact ∑ M ∈ (Finset.univ.filter fun M : Finset G.edgeSet =>
      IsMatchingEdgeFinset G M),
    (X : ℝ[X]) ^ M.card

/-- The intrinsic edge-matching polynomial agrees with the line-graph
independence-polynomial definition. -/
theorem matchingPolynomialByEdges_eq_matchingGeneratingPolynomial
    {V : Type u} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    matchingPolynomialByEdges G = matchingGeneratingPolynomial G := by
  classical
  simp [matchingPolynomialByEdges, matchingGeneratingPolynomial, indepPoly,
    isMatchingEdgeFinset_iff_lineGraph_isIndepSet]

/-- The empty independent set gives the constant coefficient of the
independence polynomial. -/
theorem indepPoly_coeff_zero {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : (indepPoly G).coeff 0 = 1 := by
  classical
  rw [indepPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single ∅]
  · simp
  · intro s hs hne
    have hs_nonzero : s.card ≠ 0 := by
      rwa [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]
    have hzero : ¬ 0 = s.card := fun h => hs_nonzero h.symm
    simp [Polynomial.coeff_X_pow, hzero]
  · intro hnot
    simp at hnot

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
  exact Finset.sum_nonneg fun s _ => by
    by_cases hs : n = s.card
    · simp [Polynomial.coeff_X_pow, hs]
    · simp [Polynomial.coeff_X_pow, hs]

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
  have hs_card : Fintype.card {w // w ∈ s} = s.card := by
    rw [← Finset.card_univ, Finset.univ_eq_attach, Finset.card_attach]
  have hv_card :
      Fintype.card {x // x ∈ (v : Sym2 V).toFinset} =
        (v : Sym2 V).toFinset.card := by
    rw [← Finset.card_univ, Finset.univ_eq_attach, Finset.card_attach]
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
    have hcommon : (φ a : V) ∈ ((b.val : G.edgeSet) : Sym2 V) := by
      have hb := hφ_edge b
      have hval : (φ a : V) = (φ b : V) := congrArg Subtype.val hab
      rwa [hval]
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
  norm_num at hcard_le_two

/-- Graph-form Chudnovsky--Seymour statement still needed for #52.

This is the real graph-theoretic leaf: it should be proved by the usual
claw-free deletion/compatibility induction, using the polynomial
Chudnovsky--Seymour interlacing engine from `RealRooted.ChudnovskySeymour`. -/
def ClawFreeIndepPolySplitsStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V), ClawFree G → (indepPoly G).Splits

/-- The remaining graph-theoretic existence statement needed to finish the
support-level induction for all finite claw-free graphs. -/
def ClawFreeSupportSimplicialCliqueExistsStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : _root_.SimpleGraph V) [DecidableRel G.Adj],
    ClawFree G → SupportSimplicialCliqueExists G

/-- The graph-form Chudnovsky--Seymour statement follows from the support-level
induction once every nonempty finite support in a claw-free graph has a
nonempty simplicial clique. -/
theorem clawFreeIndepPolySplits_of_supportSimplicialCliqueExists
    (hexists : ClawFreeSupportSimplicialCliqueExistsStatement.{u}) :
    ClawFreeIndepPolySplitsStatement.{u} := by
  intro V _hfinite _hdec G hG
  classical
  rw [indepPoly_eq_indepPolyOn_univ]
  exact supportIndepPoly_splits_of_simplicialCliqueExists hG
    (hexists G hG) Finset.univ

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

end Graph
end RealRooted
