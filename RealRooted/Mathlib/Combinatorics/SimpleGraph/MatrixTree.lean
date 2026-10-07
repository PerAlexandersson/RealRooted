import RealRooted.Mathlib.LinearAlgebra.Matrix.CauchyBinet
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The weighted matrix-tree theorem

We prove Kirchhoff's weighted matrix-tree theorem for a finite simple graph `G` on a vertex type
`V`, with edge weights `w : Sym2 V → R` in a commutative ring `R`.

## Main definitions

* `Sym2.orientedIncMatrix R V`: an oriented incidence matrix `V × Sym2 V`, using an arbitrary
  ordered representative of each unordered pair.
* `SimpleGraph.weightedLapMatrix G w`: the weighted Laplacian.
* `SimpleGraph.spanningTrees G`: the spanning trees of `G`, as finsets of edges.

## Main results

* `SimpleGraph.weightedLapMatrix_eq_mul`: `L = B * diagonal w * Bᵀ`.
* `Sym2.sq_det_orientedIncMatrix_submatrix`: a maximal minor of the reduced incidence matrix
  squares to `1` exactly on connected edge sets, and to `0` otherwise.
* `SimpleGraph.det_weightedLapMatrix_submatrix`: the weighted matrix-tree theorem.
* `SimpleGraph.det_lapMatrix_submatrix`: the unweighted matrix-tree theorem for `lapMatrix`.

## Proof outline

The reduced Laplacian factors as `C * diagonal w' * Cᵀ`, where `C` is the oriented incidence
matrix with the row of the root deleted and `w'` is `w` restricted to edges.  Cauchy–Binet
expands its determinant as a sum over `(|V| - 1)`-sets `S` of pairs.  Over `ℤ`, the minor of
`C` at `S` has absolute value at most one (total unimodularity) and is nonzero exactly when `S`
spans a connected graph (kernel argument), so its square is the indicator of connectivity.
Finally, a connected edge set with `|V| - 1` edges is a spanning tree.
-/

open Finset Matrix

namespace Sym2

variable (R V : Type*) [Ring R] [DecidableEq V]

/-- The oriented incidence matrix of all unordered pairs: the column of `e : Sym2 V` has `1` at
the first and `-1` at the second vertex of a fixed (arbitrary) ordered representative of `e`.
Columns of diagonal pairs vanish. -/
noncomputable def orientedIncMatrix : Matrix V (Sym2 V) R := fun v e =>
  (if v = (Quot.out e).1 then 1 else 0) - (if v = (Quot.out e).2 then 1 else 0)

variable {R V}

theorem orientedIncMatrix_mul_orientedIncMatrix (i j : V) {e : Sym2 V} (he : ¬ e.IsDiag) :
    orientedIncMatrix R V i e * orientedIncMatrix R V j e =
      if i = j then (if i ∈ e then 1 else 0) else (if e = s(i, j) then -1 else 0) := by
  rcases hq : Quot.out e with ⟨a, b⟩
  have he' : e = s(a, b) := by rw [← Quot.out_eq e, hq]
  simp only [orientedIncMatrix, hq]
  subst he'
  rw [mk_isDiag_iff] at he
  split_ifs <;> grind

end Sym2

namespace SimpleGraph

variable {V R : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The weighted Laplacian of `G` with edge weights `w : Sym2 V → R`: the diagonal entry at `i`
is the total weight of the edges at `i`, and the entry at `i ≠ j` is `-w s(i, j)` if `i` and
`j` are adjacent and `0` otherwise. -/
def weightedLapMatrix [AddCommGroup R] (w : Sym2 V → R) : Matrix V V R := fun i j =>
  if i = j then ∑ k ∈ G.neighborFinset i, w s(i, k) else if G.Adj i j then -w s(i, j) else 0

private theorem sum_edge_weight_mem [AddCommGroup R] (w : Sym2 V → R) (i : V) :
    ∑ e : Sym2 V, (if e ∈ G.edgeSet ∧ i ∈ e then w e else 0) =
      ∑ k ∈ G.neighborFinset i, w s(i, k) := by
  rw [← sum_filter, ← sum_image (f := w) (g := fun k => s(i, k))
    (fun _ _ _ _ h => Sym2.congr_right.mp h)]
  refine sum_congr ?_ fun _ _ => rfl
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_filter, mem_univ, true_and, mem_edgeSet, Sym2.mem_iff, mem_image,
      mem_neighborFinset]
    constructor
    · rintro ⟨h, rfl | rfl⟩
      · exact ⟨b, h, rfl⟩
      · exact ⟨a, h.symm, Sym2.eq_swap⟩
    · rintro ⟨k, hk, he⟩
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hk, Or.inl rfl⟩
      · exact ⟨hk.symm, Or.inr rfl⟩

/-- The weighted Laplacian factors as `B * diagonal w' * Bᵀ`, where `B` is the oriented
incidence matrix and `w'` is `w` restricted to the edges of `G`. -/
theorem weightedLapMatrix_eq_mul [CommRing R] (w : Sym2 V → R) :
    G.weightedLapMatrix w = Sym2.orientedIncMatrix R V *
      diagonal (fun e => if e ∈ G.edgeSet then w e else 0) * (Sym2.orientedIncMatrix R V)ᵀ := by
  ext i j
  have key : ∀ e : Sym2 V, Sym2.orientedIncMatrix R V i e *
      (if e ∈ G.edgeSet then w e else 0) * Sym2.orientedIncMatrix R V j e =
      if e ∈ G.edgeSet then w e *
        (if i = j then (if i ∈ e then 1 else 0) else (if e = s(i, j) then -1 else 0)) else 0 := by
    intro e
    by_cases he : e ∈ G.edgeSet
    · simp only [he, ↓reduceIte]
      rw [mul_comm _ (w e), mul_assoc,
        Sym2.orientedIncMatrix_mul_orientedIncMatrix i j (G.not_isDiag_of_mem_edgeSet he)]
    · simp [he]
  rw [mul_apply]
  simp only [mul_diagonal, transpose_apply, key]
  unfold weightedLapMatrix
  split_ifs with hij hadj
  · subst hij
    rw [← sum_edge_weight_mem]
    refine sum_congr rfl fun e _ => ?_
    by_cases h1 : e ∈ G.edgeSet <;> by_cases h2 : i ∈ e <;> simp [h1, h2]
  · rw [sum_eq_single s(i, j) (fun e _ he => by simp [he]) (by simp)]
    simp [hadj]
  · refine (sum_eq_zero fun e _ => ?_).symm
    by_cases he : e = s(i, j)
    · simp [he, hadj]
    · simp [he]

end SimpleGraph

namespace Sym2

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem out_eq_or {e : Sym2 V} {a b : V} (h : e = s(a, b)) :
    ((Quot.out e).1 = a ∧ (Quot.out e).2 = b) ∨ ((Quot.out e).1 = b ∧ (Quot.out e).2 = a) :=
  Sym2.eq_iff.mp (h ▸ Quot.out_eq e)

private theorem vecMul_submatrix_val {R : Type*} [CommRing R] {r : V} (y : V → R)
    (hy : y r = 0)
    (f : {v // v ≠ r} → Sym2 V) (j : {v // v ≠ r}) :
    ((fun i : {v // v ≠ r} => y i) ᵥ* (orientedIncMatrix R V).submatrix Subtype.val f) j =
      y (Quot.out (f j)).1 - y (Quot.out (f j)).2 := by
  have hsum : ∑ i : {v // v ≠ r}, y i * orientedIncMatrix R V i (f j) =
      ∑ x, y x * orientedIncMatrix R V x (f j) := by
    rw [← sum_subtype (univ.erase r) (p := fun x => x ≠ r) (by simp)
      (fun x => y x * orientedIncMatrix R V x (f j)), sum_erase _ (by simp [hy])]
  simp only [vecMul, dotProduct, submatrix_apply, hsum]
  simp [orientedIncMatrix, mul_sub, sum_sub_distrib]

/-- A square minor of the oriented incidence matrix, with the row of `r` deleted, is nonzero
iff the selected edges form a connected spanning graph. -/
theorem det_orientedIncMatrix_submatrix_ne_zero_iff (r : V) (f : {v // v ≠ r} → Sym2 V) :
    ((orientedIncMatrix ℤ V).submatrix Subtype.val f).det ≠ 0 ↔
      (SimpleGraph.fromEdgeSet (Set.range f)).Connected := by
  set H := SimpleGraph.fromEdgeSet (Set.range f)
  rw [Ne, ← exists_vecMul_eq_zero_iff]
  constructor
  · intro h
    by_contra hc
    obtain ⟨x, hx⟩ : ∃ x, ¬ H.Reachable r x := by
      by_contra hall
      push Not at hall
      exact hc ((H.connected_iff_exists_forall_reachable).mpr ⟨r, hall⟩)
    have hxr : x ≠ r := fun h => hx (h ▸ SimpleGraph.Reachable.refl _)
    let y : V → ℤ := fun z => if H.Reachable x z then 1 else 0
    have hyr : y r = 0 := by simp [y, show ¬ H.Reachable x r from fun h => hx h.symm]
    refine h ⟨fun i => y i, fun h0 => by simpa [y] using congrFun h0 ⟨x, hxr⟩, ?_⟩
    funext j
    rw [vecMul_submatrix_val y hyr, Pi.zero_apply, sub_eq_zero]
    by_cases hab : (Quot.out (f j)).1 = (Quot.out (f j)).2
    · rw [hab]
    · have hadj : H.Adj (Quot.out (f j)).1 (Quot.out (f j)).2 :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨j, (Quot.out_eq (f j)).symm⟩, hab⟩
      have hiff : H.Reachable x (Quot.out (f j)).1 ↔ H.Reachable x (Quot.out (f j)).2 :=
        ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.reachable.symm⟩
      simp only [y, hiff]
  · rintro hconn ⟨v, hv0, hv⟩
    let y : V → ℤ := fun z => if h : z = r then 0 else v ⟨z, h⟩
    have hyv : (fun i : {v // v ≠ r} => y i) = v := funext fun i => by simp [y, i.2]
    have hadj : ∀ a b, H.Adj a b → y a = y b := by
      intro a b hab
      obtain ⟨⟨j, hj⟩, -⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hab
      have hcol := congrFun hv j
      rw [← hyv, vecMul_submatrix_val y (by simp [y]), Pi.zero_apply, sub_eq_zero] at hcol
      rcases out_eq_or hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2, hcol]
      · rw [← h1, ← h2, hcol]
    have hreach : ∀ z, Relation.ReflTransGen H.Adj r z → y z = y r := by
      intro z hz
      induction hz with
      | refl => rfl
      | tail _ hbc ih => exact (hadj _ _ hbc).symm.trans ih
    refine hv0 (hyv ▸ funext fun i => ?_)
    simpa [y, i.2] using
      hreach i ((SimpleGraph.reachable_iff_reflTransGen _ _).mp (hconn.preconnected r i))

end Sym2

namespace Sym2

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem orientedIncMatrix_eq_one {x : V} {e : Sym2 V}
    (h : orientedIncMatrix ℤ V x e = 1) : x = (Quot.out e).1 := by
  grind [orientedIncMatrix]

omit [Fintype V] in
private theorem orientedIncMatrix_eq_neg_one {x : V} {e : Sym2 V}
    (h : orientedIncMatrix ℤ V x e = -1) : x = (Quot.out e).2 := by
  grind [orientedIncMatrix]

omit [Fintype V] in
private theorem abs_orientedIncMatrix_le_one (x : V) (e : Sym2 V) :
    |orientedIncMatrix ℤ V x e| ≤ 1 := by
  grind [orientedIncMatrix]

/-- The square of a square minor of the integer oriented incidence matrix with the row of `r`
deleted is `1` if the selected edges form a connected spanning graph and `0` otherwise. -/
theorem sq_det_orientedIncMatrix_submatrix (r : V) (f : {v // v ≠ r} → Sym2 V) :
    ((orientedIncMatrix ℤ V).submatrix Subtype.val f).det ^ 2 =
      if (SimpleGraph.fromEdgeSet (Set.range f)).Connected then 1 else 0 := by
  have habs := abs_le.mp (abs_det_le_one_of_col ((orientedIncMatrix ℤ V).submatrix Subtype.val f)
    (fun _ _ => abs_orientedIncMatrix_le_one _ _)
    (fun _ _ _ h h' => Subtype.ext
      ((orientedIncMatrix_eq_one h).trans (orientedIncMatrix_eq_one h').symm))
    (fun _ _ _ h h' => Subtype.ext
      ((orientedIncMatrix_eq_neg_one h).trans (orientedIncMatrix_eq_neg_one h').symm)))
  split_ifs with hc
  · have hne := (det_orientedIncMatrix_submatrix_ne_zero_iff r f).mpr hc
    rcases (by lia : ((orientedIncMatrix ℤ V).submatrix Subtype.val f).det = 1 ∨
      ((orientedIncMatrix ℤ V).submatrix Subtype.val f).det = -1) with h | h <;> simp [h]
  · rw [not_ne_iff.mp (mt (det_orientedIncMatrix_submatrix_ne_zero_iff r f).mp hc)]
    simp

end Sym2

namespace SimpleGraph

variable {V R : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open Classical in
/-- The spanning trees of `G`, as finsets of edges `T ⊆ G.edgeFinset` whose edge graph
`fromEdgeSet T` is a tree on all of `V`. -/
noncomputable def spanningTrees : Finset (Finset (Sym2 V)) :=
  G.edgeFinset.powerset.filter fun T => (fromEdgeSet (T : Set (Sym2 V))).IsTree

omit [DecidableEq V] in
theorem mem_spanningTrees {T : Finset (Sym2 V)} :
    T ∈ G.spanningTrees ↔ T ⊆ G.edgeFinset ∧ (fromEdgeSet (T : Set (Sym2 V))).IsTree := by
  simp [spanningTrees]

private theorem isTree_fromEdgeSet_iff {T : Finset (Sym2 V)} (hT : T ⊆ G.edgeFinset) (r : V) :
    (fromEdgeSet (T : Set (Sym2 V))).IsTree ↔
      (fromEdgeSet (T : Set (Sym2 V))).Connected ∧ T.card = Fintype.card {v // v ≠ r} := by
  have hE : (fromEdgeSet (T : Set (Sym2 V))).edgeSet = T := by
    rw [edgeSet_fromEdgeSet, sdiff_eq_left]
    exact Set.disjoint_left.mpr fun e he hd =>
      G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (hT he)) (Sym2.mem_diagSet.mp hd)
  have hpos := Fintype.card_pos_iff.mpr ⟨r⟩
  rw [isTree_iff_connected_and_card, hE, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Nat.card_eq_fintype_card]
  simp only [ne_eq, Fintype.card_subtype_compl, Fintype.card_unique]
  exact and_congr_right fun _ => ⟨fun h => by lia, fun h => by lia⟩

/-- **Kirchhoff's weighted matrix-tree theorem.** For a finite simple graph `G` with edge
weights `w` in a commutative ring and any vertex `r`, the determinant of the weighted Laplacian
with row and column `r` deleted is the sum over all spanning trees `T` of `∏ e ∈ T, w e`. -/
theorem det_weightedLapMatrix_submatrix [CommRing R] (w : Sym2 V → R) (r : V) :
    ((G.weightedLapMatrix w).submatrix (Subtype.val : {v // v ≠ r} → V) Subtype.val).det =
      ∑ T ∈ G.spanningTrees, ∏ e ∈ T, w e := by
  set d : Sym2 V → R := fun e => if e ∈ G.edgeSet then w e else 0
  set C : Matrix {v // v ≠ r} (Sym2 V) R :=
    (Sym2.orientedIncMatrix R V).submatrix Subtype.val id
  have hL : (G.weightedLapMatrix w).submatrix Subtype.val Subtype.val =
      C * (diagonal d * Cᵀ) := by
    rw [weightedLapMatrix_eq_mul, Matrix.mul_assoc]
    rfl
  let e : (S : {S : Finset (Sym2 V) // S.card = Fintype.card {v // v ≠ r}}) →
      {v // v ≠ r} ≃ S.1 := fun S => Fintype.equivOfCardEq (by simp [S.2])
  have hterm : ∀ S, (C.submatrix id (fun i => (e S i : Sym2 V))).det *
      ((diagonal d * Cᵀ).submatrix (fun i => (e S i : Sym2 V)) id).det =
      (if (fromEdgeSet (S.1 : Set (Sym2 V))).Connected then 1 else 0) * ∏ x ∈ S.1, d x := by
    intro S
    have hrange : Set.range (fun i => (e S i : Sym2 V)) = S.1 := by
      ext x
      simp only [Set.mem_range, Finset.mem_coe]
      exact ⟨fun ⟨i, hi⟩ => hi ▸ (e S i).2, fun hx => ⟨(e S).symm ⟨x, hx⟩, by simp⟩⟩
    have hcast : C.submatrix id (fun i => (e S i : Sym2 V)) = (Int.castRingHom R).mapMatrix
        ((Sym2.orientedIncMatrix ℤ V).submatrix Subtype.val (fun i => (e S i : Sym2 V))) := by
      ext i j
      simp [C, Sym2.orientedIncMatrix]
    have hdiag : (diagonal d * Cᵀ).submatrix (fun i => (e S i : Sym2 V)) id =
        diagonal (fun i => d (e S i)) * (C.submatrix id (fun i => (e S i : Sym2 V)))ᵀ := by
      ext i j
      simp [diagonal_mul]
    have hprod : ∏ i, d (e S i) = ∏ x ∈ S.1, d x := by
      rw [Equiv.prod_comp (e S) (fun x => d x), prod_coe_sort S.1 d]
    rw [hdiag, det_mul, det_diagonal, det_transpose, hprod, hcast, ← RingHom.map_det,
      mul_left_comm, ← map_mul, ← sq, Sym2.sq_det_orientedIncMatrix_submatrix]
    simp only [hrange]
    split_ifs <;> simp
  rw [hL, det_mul_eq_sum_minors C _ e]
  simp_rw [hterm]
  rw [← sum_subtype (univ.filter fun S : Finset (Sym2 V) => S.card = Fintype.card {v // v ≠ r})
      (by simp) (fun S => (if (fromEdgeSet (S : Set (Sym2 V))).Connected then 1 else 0) *
        ∏ x ∈ S, d x),
    sum_filter, ← Fintype.sum_ite_mem G.spanningTrees]
  refine sum_congr rfl fun S _ => ?_
  by_cases hS : S ⊆ G.edgeFinset
  · have hprod : ∏ x ∈ S, d x = ∏ x ∈ S, w x :=
      prod_congr rfl fun x hx => by simp [d, mem_edgeFinset.mp (hS hx)]
    simp only [hprod, mem_spanningTrees, isTree_fromEdgeSet_iff G hS r]
    by_cases hc : (fromEdgeSet (S : Set (Sym2 V))).Connected <;>
      by_cases hcard : S.card = Fintype.card {v // v ≠ r} <;> simp [hS, hc, hcard]
  · obtain ⟨x, hx, hxE⟩ := not_subset.mp hS
    have hzero : ∏ x ∈ S, d x = 0 := prod_eq_zero hx (by simp [d, mem_edgeFinset.not.mp hxE])
    simp [hzero, mem_spanningTrees, hS]

end SimpleGraph

namespace SimpleGraph

variable {V R : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- With unit weights, the weighted Laplacian is Mathlib's `SimpleGraph.lapMatrix`. -/
theorem weightedLapMatrix_one [AddCommGroupWithOne R] :
    G.weightedLapMatrix (fun _ => (1 : R)) = G.lapMatrix R := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [weightedLapMatrix, lapMatrix, degMatrix]
  · by_cases hadj : G.Adj i j <;> simp [weightedLapMatrix, lapMatrix, degMatrix, hij, hadj]

/-- **Kirchhoff's matrix-tree theorem.** Any cofactor of the Laplacian of a finite simple graph
counts its spanning trees. -/
theorem det_lapMatrix_submatrix [CommRing R] (r : V) :
    ((G.lapMatrix R).submatrix (Subtype.val : {v // v ≠ r} → V) Subtype.val).det =
      G.spanningTrees.card := by
  rw [← weightedLapMatrix_one, det_weightedLapMatrix_submatrix]
  simp

end SimpleGraph
