import RealRooted.Mathlib.Combinatorics.SimpleGraph.MatrixTree
import RealRooted.DeterminantalStability

/-!
# Spanning-tree polynomials are real stable

The spanning-tree (Kirchhoff) polynomial `∑_T ∏_{e ∈ T} x_e` of a finite graph is the
determinant of the reduced Laplacian with edge weights `x_e`
(`SimpleGraph.det_weightedLapMatrix_submatrix`), which is the linear pencil
`∑_e x_e b_e b_eᵀ` in the positive semidefinite rank-one matrices `b_e b_eᵀ` built from the
oriented incidence vectors.  By the Borcea–Brändén determinantal theorem
(`mvRealStable_realDetPencil`) it is real stable whenever the graph has a spanning tree.

## References

* Y.-B. Choe, J. G. Oxley, A. D. Sokal, D. G. Wagner, *Homogeneous multivariate polynomials
  with the half-plane property*, Adv. in Appl. Math. 32 (2004), 88–187, Theorem 1.1.
* J. Borcea, P. Brändén, *Applications of stable polynomials to mixed determinants*,
  Duke Math. J. 143 (2008).
-/

open MvPolynomial Matrix

noncomputable section

namespace RealRooted

variable {V : Type*} [DecidableEq V]

private theorem orientedIncMatrix_map (v : V) (e : Sym2 V) :
    Sym2.orientedIncMatrix (MvPolynomial (Sym2 V) ℝ) V v e =
      C (Sym2.orientedIncMatrix ℝ V v e) := by
  simp only [Sym2.orientedIncMatrix, map_sub, apply_ite C, map_one, map_zero]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The rank-one matrix `b_e b_eᵀ` of an edge `e` on the vertices other than `r`, where `b_e`
is the oriented incidence vector; zero for non-edges. -/
def edgePencilMatrix (r : V) (e : Sym2 V) : Matrix {v // v ≠ r} {v // v ≠ r} ℝ :=
  if e ∈ G.edgeSet then
    vecMulVec (fun i => Sym2.orientedIncMatrix ℝ V i.1 e)
      (fun i => Sym2.orientedIncMatrix ℝ V i.1 e)
  else 0

theorem posSemidef_edgePencilMatrix [Finite V] (r : V) (e : Sym2 V) :
    (edgePencilMatrix G r e).PosSemidef := by
  have := Fintype.ofFinite V
  unfold edgePencilMatrix
  split_ifs
  · simpa using posSemidef_vecMulVec_self_star fun i : {v // v ≠ r} =>
      Sym2.orientedIncMatrix ℝ V i.1 e
  · exact PosSemidef.zero

variable [Fintype V]

/-- The spanning-tree polynomial `∑_T ∏_{e ∈ T} x_e` of a finite graph. -/
def spanningTreePoly : MvPolynomial (Sym2 V) ℝ :=
  ∑ T ∈ G.spanningTrees, ∏ e ∈ T, X e

/-- The spanning-tree polynomial is the determinantal pencil `det (∑_e x_e b_e b_eᵀ)` on the
vertices other than `r` (the weighted matrix-tree theorem). -/
theorem spanningTreePoly_eq_realDetPencil (r : V) :
    spanningTreePoly G = realDetPencil 0 (edgePencilMatrix G r) := by
  rw [spanningTreePoly, ← G.det_weightedLapMatrix_submatrix (fun e => X e) r, realDetPencil]
  congr 1
  funext i j
  rw [submatrix_apply, G.weightedLapMatrix_eq_mul, mul_apply]
  simp only [mul_diagonal, transpose_apply, Matrix.zero_apply, map_zero, zero_add,
    orientedIncMatrix_map, edgePencilMatrix]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp [vecMulVec_apply]
  ring

omit [DecidableEq V] in
/-- Evaluating the spanning-tree polynomial at the all-ones point counts spanning trees. -/
theorem eval_one_spanningTreePoly :
    eval 1 (spanningTreePoly G) = G.spanningTrees.card := by
  simp [spanningTreePoly, map_sum]

omit [DecidableEq V] in
/-- **Spanning-tree polynomials are real stable** (Choe–Oxley–Sokal–Wagner): if `G` has a
spanning tree, its spanning-tree polynomial is real stable. -/
theorem mvRealStable_spanningTreePoly (hG : G.spanningTrees.Nonempty) :
    MvRealStable (spanningTreePoly G) := by
  classical
  obtain ⟨r⟩ : Nonempty V := by
    obtain ⟨T, hT⟩ := hG
    exact ((G.mem_spanningTrees.mp hT).2.connected).nonempty
  rw [spanningTreePoly_eq_realDetPencil G r]
  refine mvRealStable_realDetPencil 0 _ isHermitian_zero (posSemidef_edgePencilMatrix G r) ?_
  rw [← spanningTreePoly_eq_realDetPencil G r]
  intro h
  have h0 : spanningTreePoly G = 0 :=
    map_injective _ Complex.ofReal_injective (by simpa [complexifyMv] using h)
  have h1 := eval_one_spanningTreePoly G
  rw [h0, map_zero] at h1
  exact (Nat.cast_ne_zero.mpr hG.card_pos.ne') h1.symm

end RealRooted
