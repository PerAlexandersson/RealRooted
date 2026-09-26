import RealRooted.HeilmannLieb
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Weighted rook polynomials

This file formalizes the ordinary nonattacking-rook model on an arbitrary
finite rectangular board.  It is separate from the non-nesting rook model in
`RealRooted.GeneralizedSnakePosets`.

A matrix position is identified with an edge of the complete bipartite graph.
Under this identification, nonattacking rook placements are exactly graph
matchings, and their weighted generating polynomials agree term by term.
Weighted Heilmann--Lieb therefore gives Nijenhuis's real-rootedness theorem.

The positive-coefficient convention uses `X ^ k`; Nijenhuis's signed
normalization uses `(-X) ^ k`.  Both are exposed explicitly below.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Rook

universe u v

variable {Row : Type u} {Column : Type v}

/-- The complete-bipartite edge associated with a matrix position. -/
private def bipartiteEdge (x : Row × Column) :
    (_root_.completeBipartiteGraph Row Column).edgeSet :=
  ⟨s(.inl x.1, .inr x.2), by
    simp [_root_.SimpleGraph.mem_edgeSet]⟩

/-- Matrix positions are canonically equivalent to the edges of the complete
bipartite graph on the row and column types. -/
def completeBipartiteEdgeEquiv :
    Row × Column ≃ (_root_.completeBipartiteGraph Row Column).edgeSet :=
  Equiv.ofBijective bipartiteEdge
    ⟨by
      intro x y h
      have h' :
          (bipartiteEdge x : Sym2 (Row ⊕ Column)) =
            (bipartiteEdge y : Sym2 (Row ⊕ Column)) :=
        congrArg Subtype.val h
      simp only [bipartiteEdge, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Sum.inl.injEq, Sum.inr.injEq, Prod.swap_prod_mk, reduceCtorEq,
        and_self, or_false] at h'
      exact Prod.ext h'.1 h'.2,
    by
      intro e
      have he : (e : Sym2 (Row ⊕ Column)) ∈
          Set.range (fun x : Row × Column ↦
            s(Sum.inl x.1, Sum.inr x.2)) := by
        rw [← _root_.SimpleGraph.edgeSet_completeBipartiteGraph]
        exact e.property
      rcases he with ⟨x, hx⟩
      refine ⟨x, Subtype.ext ?_⟩
      simpa [bipartiteEdge] using hx⟩

@[simp]
theorem completeBipartiteEdgeEquiv_apply (x : Row × Column) :
    (completeBipartiteEdgeEquiv x : Sym2 (Row ⊕ Column)) =
      s(Sum.inl x.1, Sum.inr x.2) :=
  rfl

/-- A finite set of matrix positions is a nonattacking rook placement when
distinct positions have distinct rows and distinct columns. -/
def IsRookPlacement (P : Finset (Row × Column)) : Prop :=
  ∀ ⦃x⦄, x ∈ P → ∀ ⦃y⦄, y ∈ P → x ≠ y →
    x.1 ≠ y.1 ∧ x.2 ≠ y.2

/-- Nonattacking rook placements are exactly edge matchings in the complete
bipartite graph. -/
theorem isRookPlacement_iff_isMatching (P : Finset (Row × Column)) :
    IsRookPlacement P ↔
      Graph.IsMatchingEdgeFinset (_root_.completeBipartiteGraph Row Column)
        (P.map completeBipartiteEdgeEquiv.toEmbedding) := by
  classical
  constructor
  · intro h e₁ he₁ e₂ he₂ hne hcommon
    rcases Finset.mem_map.mp he₁ with ⟨x, hx, rfl⟩
    rcases Finset.mem_map.mp he₂ with ⟨y, hy, rfl⟩
    have hxy : x ≠ y :=
      fun hxy ↦ hne (congrArg completeBipartiteEdgeEquiv hxy)
    have hdistinct := h hx hy hxy
    have hshared : x.1 = y.1 ∨ x.2 = y.2 := by
      simpa [Set.Nonempty] using hcommon
    exact hshared.elim hdistinct.1 hdistinct.2
  · intro h x hx y hy hxy
    have hne :
        completeBipartiteEdgeEquiv x ≠ completeBipartiteEdgeEquiv y :=
      fun heq ↦ hxy (completeBipartiteEdgeEquiv.injective heq)
    have hxmap :
        completeBipartiteEdgeEquiv x ∈
          P.map completeBipartiteEdgeEquiv.toEmbedding :=
      Finset.mem_map.mpr ⟨x, hx, rfl⟩
    have hymap :
        completeBipartiteEdgeEquiv y ∈
          P.map completeBipartiteEdgeEquiv.toEmbedding :=
      Finset.mem_map.mpr ⟨y, hy, rfl⟩
    constructor
    · intro hrow
      apply h hxmap hymap hne
      simp [Set.Nonempty, hrow]
    · intro hcol
      apply h hxmap hymap hne
      simp [Set.Nonempty, hcol]

/-- The weighted rook polynomial of a finite matrix.  A placement contributes
the product of its matrix entries times `X` to the number of its rooks. -/
def weightedRookPolynomial [Fintype Row] [Fintype Column]
    [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) : ℝ[X] := by
  classical
  exact ∑ P ∈ (Finset.univ.filter fun P : Finset (Row × Column) ↦
      IsRookPlacement P),
    (∏ x ∈ P, C (A x.1 x.2)) * X ^ P.card

/-- Transfer matrix weights to the corresponding complete-bipartite edges. -/
def matrixEdgeWeight (A : Row → Column → ℝ)
    (e : (_root_.completeBipartiteGraph Row Column).edgeSet) : ℝ :=
  A (completeBipartiteEdgeEquiv.symm e).1
    (completeBipartiteEdgeEquiv.symm e).2

@[simp]
theorem matrixEdgeWeight_apply (A : Row → Column → ℝ)
    (x : Row × Column) :
    matrixEdgeWeight A (completeBipartiteEdgeEquiv x) = A x.1 x.2 := by
  simp [matrixEdgeWeight]

/-- Exact weighted identity between the rook polynomial of a matrix and the
matching polynomial of its complete bipartite row-column graph. -/
theorem weightedRookPolynomial_eq_weightedMatchingPolynomialByEdges
    [Fintype Row] [Fintype Column] [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) :
    weightedRookPolynomial A =
      Graph.weightedMatchingPolynomialByEdges
        (_root_.completeBipartiteGraph Row Column) (matrixEdgeWeight A) := by
  classical
  rw [weightedRookPolynomial, Graph.weightedMatchingPolynomialByEdges]
  apply Finset.sum_equiv (Equiv.finsetCongr completeBipartiteEdgeEquiv)
  · intro P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.finsetCongr_apply]
    exact isRookPlacement_iff_isMatching P
  · intro P _hP
    simp

/-- Nijenhuis's signed normalization, in which a placement of size `k`
contributes a factor `(-X)^k`. -/
def nijenhuisRookPolynomial [Fintype Row] [Fintype Column]
    [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) : ℝ[X] :=
  (weightedRookPolynomial A).comp (-X)

/-- The signed normalization multiplies the coefficient in degree `k` by
`(-1)^k`. -/
theorem coeff_nijenhuisRookPolynomial [Fintype Row] [Fintype Column]
    [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) (k : ℕ) :
    (nijenhuisRookPolynomial A).coeff k =
      (-1 : ℝ) ^ k * (weightedRookPolynomial A).coeff k := by
  rw [nijenhuisRookPolynomial,
    show (-X : ℝ[X]) = C (-1) * X by simp,
    Polynomial.comp_C_mul_X_coeff]
  ring

/-- The positive-convention weighted rook polynomial is a Pólya-frequency
polynomial when every matrix entry is nonnegative. -/
theorem weightedRookPolynomial_isPFPolynomial [Fintype Row] [Fintype Column]
    [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) (hA : ∀ r c, 0 ≤ A r c) :
    IsPFPolynomial (weightedRookPolynomial A) := by
  rw [weightedRookPolynomial_eq_weightedMatchingPolynomialByEdges]
  apply Graph.weightedMatchingPolynomialByEdges_isPFPolynomial
  intro e
  exact hA _ _

/-- Nijenhuis's weighted rook polynomial in the positive convention has only
real roots. -/
theorem weightedRookPolynomial_splits [Fintype Row] [Fintype Column]
    [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) (hA : ∀ r c, 0 ≤ A r c) :
    (weightedRookPolynomial A).Splits := by
  rw [weightedRookPolynomial_eq_weightedMatchingPolynomialByEdges]
  apply Graph.weightedMatchingPolynomialByEdges_splits
  intro e
  exact hA _ _

/-- Nijenhuis's signed normalization has only real roots. -/
theorem nijenhuisRookPolynomial_splits [Fintype Row] [Fintype Column]
    [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) (hA : ∀ r c, 0 ≤ A r c) :
    (nijenhuisRookPolynomial A).Splits :=
  (weightedRookPolynomial_splits A hA).comp_neg_X

/-- The roots in Nijenhuis's signed normalization are nonnegative. -/
theorem nijenhuisRookPolynomial_roots_nonneg
    [Fintype Row] [Fintype Column] [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) (hA : ∀ r c, 0 ≤ A r c) :
    ∀ z ∈ (nijenhuisRookPolynomial A).roots, 0 ≤ z := by
  intro z hz
  rw [nijenhuisRookPolynomial, Polynomial.roots_comp_neg_X] at hz
  rcases Multiset.mem_map.mp hz with ⟨r, hr, rfl⟩
  exact neg_nonneg.mpr
    ((weightedRookPolynomial_isPFPolynomial A hA).roots_nonpos r hr)

/-- The ordinary rook polynomial of a finite board, obtained by giving its
cells weight one and all other matrix positions weight zero. -/
def rookPolynomial [Fintype Row] [Fintype Column]
    [DecidableEq Row] [DecidableEq Column]
    (B : Finset (Row × Column)) : ℝ[X] :=
  weightedRookPolynomial fun r c ↦ if (r, c) ∈ B then 1 else 0

/-- Every ordinary rook polynomial is a Pólya-frequency polynomial. -/
theorem rookPolynomial_isPFPolynomial [Fintype Row] [Fintype Column]
    [DecidableEq Row] [DecidableEq Column]
    (B : Finset (Row × Column)) :
    IsPFPolynomial (rookPolynomial B) := by
  apply weightedRookPolynomial_isPFPolynomial
  intro r c
  positivity

/-- Every ordinary rook polynomial has only real roots. -/
theorem rookPolynomial_splits [Fintype Row] [Fintype Column]
    [DecidableEq Row] [DecidableEq Column]
    (B : Finset (Row × Column)) :
    (rookPolynomial B).Splits :=
  weightedRookPolynomial_splits _ (by intro r c; positivity)

/-- Exact one-cell check for the weighted definition. -/
theorem weightedRookPolynomial_one_by_one (a : ℝ) :
    weightedRookPolynomial (fun _ : Fin 1 ↦ fun _ : Fin 1 ↦ a) =
      1 + C a * X := by
  classical
  have huniv :
      (Finset.univ : Finset (Finset (Fin 1 × Fin 1))) =
        {∅, {(0, 0)}} := by decide
  rw [weightedRookPolynomial, huniv]
  simp [IsRookPlacement]

end Rook
end RealRooted
