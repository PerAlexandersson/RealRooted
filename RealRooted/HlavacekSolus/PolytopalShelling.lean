module

import RealRooted.HlavacekSolus.Shelling
public import RealRooted.InterlacingSequenceBasic

/-!
# Polytopal shellings and interlacing

This file formalizes the finite graded-face content of Lemma 2.3 and Theorem 3.1 of
M. Hlavacek and L. Solus, "Subdivisions of shellable complexes", *J. Combin. Theory
Ser. A* (2021), arXiv:2003.07328.

A `PolytopalFaceData` records the faces and their ranks.  A `PolytopalShelling` records the
ordered, pairwise-disjoint relative pieces induced on a subdivision by a shelling, together
with their coverage of all subdivided faces.  This is the lightest abstraction used in the
paper's proof: the geometric subdivision axioms and the recursive boundary-shelling data are
responsible for producing such a decomposition, but neither enters the h-polynomial identity
or the interlacing argument once the decomposition is available.

The main results are `polytopalHPolynomial_eq_sum_relativePieces` and the two permutation
criteria `isRealRooted_polytopalHPolynomial_of_perm_interlacingNonneg` and
`isRealRooted_polytopalHPolynomial_of_perm_interlacing`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted
namespace HlavacekSolus

variable {α : Type*} [DecidableEq α]

/-- The finite graded-face data needed to form a polytopal h-polynomial.

The rank is one more than geometric dimension, so the empty face has rank zero.  Incidence,
intersection, and realization data are deliberately omitted because Theorem 3.1 uses them only
to obtain the relative-piece partition recorded by `PolytopalShelling`.
-/
structure PolytopalFaceData (α : Type*) [DecidableEq α] where
  /-- The faces of the subdivided polytopal complex. -/
  faces : Finset α
  /-- The rank of a face, equal to one more than its geometric dimension. -/
  rank : α → ℕ

/-- The number of faces of rank `k` in a finite set of graded faces. -/
def polytopalFaceCount (rank : α → ℕ) (faces : Finset α) (k : ℕ) : ℕ :=
  (faces.filter fun F => rank F = k).card

/-- The h-polynomial of graded face data with ambient rank `d`.

This is the expanded form of `(1-X)^d f(X/(1-X))`; using the expanded form avoids rational
functions and agrees with the convention in Section 2 of Hlavacek--Solus.
-/
def polytopalHPolynomial (d : ℕ) (rank : α → ℕ) (faces : Finset α) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C (polytopalFaceCount rank faces k : ℝ) * X ^ k * (1 - X) ^ (d - k)

/-- The ordered relative-piece decomposition induced by a polytopal shelling.

For a shelling `(F₁, ..., Fₛ)` of a base complex and a subdivision `C'`, the intended `i`-th
entry is `C'|_{Fᵢ} \ (⋃_{j<i} C'|_{Fⱼ})`.  The fields retain exactly the disjointness and
coverage consequences used in Lemma 2.3 and Theorem 3.1 of Hlavacek--Solus.
-/
structure PolytopalShelling (C : PolytopalFaceData α) where
  /-- The relative face sets, in shelling order. -/
  relativePieces : List (Finset α)
  /-- Distinct relative pieces have disjoint face sets. -/
  pairwise_disjoint : relativePieces.Pairwise Disjoint
  /-- Every subdivided face belongs to exactly the union of the relative pieces. -/
  covers : ∀ F, F ∈ C.faces ↔ ∃ R ∈ relativePieces, F ∈ R

/-- The h-polynomials of the relative pieces, in shelling order. -/
def polytopalRelativeHPolynomials (d : ℕ) (C : PolytopalFaceData α)
    (sh : PolytopalShelling C) : List ℝ[X] :=
  sh.relativePieces.map (polytopalHPolynomial d C.rank)

private lemma polytopalFaceCount_union_disjoint {rank : α → ℕ} {A B : Finset α}
    (h : Disjoint A B) (k : ℕ) :
    polytopalFaceCount rank (A ∪ B) k =
      polytopalFaceCount rank A k + polytopalFaceCount rank B k := by
  unfold polytopalFaceCount
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter h

private lemma polytopalHPolynomial_union_disjoint {rank : α → ℕ} {A B : Finset α}
    (h : Disjoint A B) (d : ℕ) :
    polytopalHPolynomial d rank (A ∪ B) =
      polytopalHPolynomial d rank A + polytopalHPolynomial d rank B := by
  unfold polytopalHPolynomial
  simp only [polytopalFaceCount_union_disjoint h, Nat.cast_add, C_add, add_mul,
    Finset.sum_add_distrib]

private lemma mem_unionList_iff_polytopal {pieces : List (Finset α)} {F : α} :
    F ∈ unionList pieces ↔ ∃ R ∈ pieces, F ∈ R := by
  induction pieces with
  | nil => simp [unionList]
  | cons R pieces ih => simp [unionList, ih]

private lemma polytopalHPolynomial_unionList_of_pairwise_disjoint
    (d : ℕ) (rank : α → ℕ) (pieces : List (Finset α))
    (hpieces : pieces.Pairwise Disjoint) :
    polytopalHPolynomial d rank (unionList pieces) =
      (pieces.map (polytopalHPolynomial d rank)).sum := by
  induction pieces with
  | nil => simp [unionList, polytopalHPolynomial, polytopalFaceCount]
  | cons R pieces ih =>
      have hdisj : Disjoint R (unionList pieces) := by
        rw [Finset.disjoint_left]
        intro F hFR hFU
        rcases mem_unionList_iff_polytopal.mp hFU with ⟨S, hS, hFS⟩
        exact (Finset.disjoint_left.mp ((List.pairwise_cons.mp hpieces).1 S hS)) hFR hFS
      rw [unionList, polytopalHPolynomial_union_disjoint hdisj,
        ih (List.pairwise_cons.mp hpieces).2]
      simp

/-- The h-polynomial is the sum of the h-polynomials of the relative shelling pieces.

This is the graded-face form of Lemma 2.3 and equation (3.1) of Hlavacek--Solus.
-/
theorem polytopalHPolynomial_eq_sum_relativePieces
    (d : ℕ) (C : PolytopalFaceData α) (sh : PolytopalShelling C) :
    polytopalHPolynomial d C.rank C.faces =
      (polytopalRelativeHPolynomials d C sh).sum := by
  have hunion : unionList sh.relativePieces = C.faces := by
    ext F
    rw [mem_unionList_iff_polytopal]
    exact (sh.covers F).symm
  rw [← hunion]
  exact polytopalHPolynomial_unionList_of_pairwise_disjoint
    d C.rank sh.relativePieces sh.pairwise_disjoint

/-- The polytopal shelling criterion for a permuted nonnegative interlacing sequence.

This is Theorem 3.1 of Hlavacek--Solus after the geometric and boundary-shelling hypotheses
have supplied the relative-piece decomposition represented by `PolytopalShelling`.
-/
theorem isRealRooted_polytopalHPolynomial_of_perm_interlacingNonneg
    (d : ℕ) (C : PolytopalFaceData α) (sh : PolytopalShelling C)
    {ordered : List ℝ[X]}
    (hperm : ordered.Perm (polytopalRelativeHPolynomials d C sh))
    (hseq : IsInterlacingSeqNonneg ordered)
    (hpoly_ne : polytopalHPolynomial d C.rank C.faces ≠ 0) :
    polytopalHPolynomial d C.rank C.faces ≠ 0 ∧
      (polytopalHPolynomial d C.rank C.faces).Splits := by
  rw [polytopalHPolynomial_eq_sum_relativePieces d C sh] at hpoly_ne ⊢
  have hordered_ne : (ordered.sum : ℝ[X]) ≠ 0 := by
    intro hzero
    apply hpoly_ne
    rw [← hperm.sum_eq, hzero]
  have hreal := isRealRooted_sum_of_isInterlacingSeqNonneg hseq hordered_ne
  rwa [hperm.sum_eq] at hreal

/-- The polytopal shelling criterion for a permuted bare interlacing sequence.

The explicit real-rootedness and positive-leading-coefficient assumptions are needed for the
repository's bare `IsInterlacingSeq` predicate, which is vacuous for singleton lists.
-/
theorem isRealRooted_polytopalHPolynomial_of_perm_interlacing
    (d : ℕ) (C : PolytopalFaceData α) (sh : PolytopalShelling C)
    {ordered : List ℝ[X]}
    (hperm : ordered.Perm (polytopalRelativeHPolynomials d C sh))
    (hseq : IsInterlacingSeq ordered)
    (hreal : ∀ p ∈ ordered, p ≠ 0 ∧ p.Splits)
    (hpos : ∀ p ∈ ordered, HasPosLeadingCoeff p)
    (hpoly_ne : polytopalHPolynomial d C.rank C.faces ≠ 0) :
    polytopalHPolynomial d C.rank C.faces ≠ 0 ∧
      (polytopalHPolynomial d C.rank C.faces).Splits := by
  rw [polytopalHPolynomial_eq_sum_relativePieces d C sh] at hpoly_ne ⊢
  have hpieces_ne : polytopalRelativeHPolynomials d C sh ≠ [] := by
    intro hnil
    apply hpoly_ne
    rw [hnil]
    simp
  exact isRealRooted_of_perm_sum_of_isInterlacingSeq
    hperm hseq hreal hpos hpieces_ne

/-- The nonnegative interlacing criterion when the shelling order itself interlaces. -/
theorem isRealRooted_polytopalHPolynomial_of_interlacingNonneg
    (d : ℕ) (C : PolytopalFaceData α) (sh : PolytopalShelling C)
    (hseq : IsInterlacingSeqNonneg (polytopalRelativeHPolynomials d C sh))
    (hpoly_ne : polytopalHPolynomial d C.rank C.faces ≠ 0) :
    polytopalHPolynomial d C.rank C.faces ≠ 0 ∧
      (polytopalHPolynomial d C.rank C.faces).Splits :=
  isRealRooted_polytopalHPolynomial_of_perm_interlacingNonneg
    d C sh .rfl hseq hpoly_ne

/-- A two-face rank-zero complex, used as a concrete decomposition example. -/
def twoPointPolytopalFaceData : PolytopalFaceData (Fin 2) where
  faces := Finset.univ
  rank := fun _ => 0

/-- The two singleton relative pieces of `twoPointPolytopalFaceData`. -/
def twoPointPolytopalShelling : PolytopalShelling twoPointPolytopalFaceData where
  relativePieces := [{0}, {1}]
  pairwise_disjoint := by decide
  covers := by
    intro F
    fin_cases F <;> simp [twoPointPolytopalFaceData]

/-- The h-polynomial of the two rank-zero faces is the constant polynomial `2`. -/
theorem twoPoint_hPolynomial :
    polytopalHPolynomial 0 twoPointPolytopalFaceData.rank
      twoPointPolytopalFaceData.faces = C 2 := by
  norm_num [polytopalHPolynomial, polytopalFaceCount, twoPointPolytopalFaceData]
  rw [C_ofNat]

/-- The two relative pieces have constant h-polynomial `1`. -/
theorem twoPoint_relativeHPolynomials :
    polytopalRelativeHPolynomials 0 twoPointPolytopalFaceData
      twoPointPolytopalShelling = [1, 1] := by
  norm_num [polytopalRelativeHPolynomials, polytopalHPolynomial,
    polytopalFaceCount, twoPointPolytopalFaceData, twoPointPolytopalShelling]

/-- The shelling criterion proves real-rootedness for the two-point example. -/
theorem twoPoint_isRealRooted :
    polytopalHPolynomial 0 twoPointPolytopalFaceData.rank
        twoPointPolytopalFaceData.faces ≠ 0 ∧
      (polytopalHPolynomial 0 twoPointPolytopalFaceData.rank
        twoPointPolytopalFaceData.faces).Splits := by
  apply isRealRooted_polytopalHPolynomial_of_interlacingNonneg
  · rw [twoPoint_relativeHPolynomials]
    refine ⟨?_, ?_⟩
    · intro p hp
      have hp_one : p = 1 := by simpa using hp
      subst p
      exact ⟨by simp, hasNonnegCoeffs_one⟩
    · rw [isInterlacingSeq_iff_pairwise]
      simpa using StrictInterl.refl (f := (1 : ℝ[X])) (by simp) (by simp)
  · rw [twoPoint_hPolynomial]
    exact C_ne_zero.mpr (by norm_num)

/-- The two-point example satisfies the relative-piece h-polynomial decomposition. -/
theorem twoPoint_hPolynomial_eq_sum :
    polytopalHPolynomial 0 twoPointPolytopalFaceData.rank
      twoPointPolytopalFaceData.faces =
      (polytopalRelativeHPolynomials 0 twoPointPolytopalFaceData
        twoPointPolytopalShelling).sum :=
  polytopalHPolynomial_eq_sum_relativePieces
    0 twoPointPolytopalFaceData twoPointPolytopalShelling

end HlavacekSolus
end RealRooted
