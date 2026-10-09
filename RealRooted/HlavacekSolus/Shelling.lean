import RealRooted.ChudnovskySeymour.Core

/-!
# Shellings and interlacing for simplicial subdivisions

This file formalizes the finite combinatorial part of M. Hlavacek and L. Solus,
"Subdivisions of shellable complexes", *J. Combin. Theory Ser. A* (2021),
arXiv:2003.07328.  We use the f- and h-polynomial conventions of Section 2:
the coefficient of X^k in f is f_{k-1}, including f_{-1} for the empty face,
and h(C, X) = (1 - X)^d f(C, X / (1 - X)), with the dimension parameter d
explicit.  The decomposition is the finite form of Lemma 2.3, and the
real-rootedness criterion is the algebraic content of Theorem 3.1, using the
shelling and relative-piece data from Definition 3.1 and equation (3.1).

## Boundary

The paper's topological definition of subdivision also includes geometric
realization, carrier compatibility with the relative interiors of faces, and
ball and boundary-subdivision conditions.  None of those clauses is encoded
here: this file uses only finite face sets, a carrier map, restriction by
carrier inclusion, and coverage of each subdivided face by a base facet.
The partition and h-polynomial identity use only those finite consequences,
so the omitted topological clauses are not needed for the criterion.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace HlavacekSolus

/-!
Stage 1 for Hlavacek--Solus, "Subdivisions of Shellable Complexes".

The shelling decomposition has coefficient one on every relative piece.  Thus
the algebraic target is the ordinary sum of the piece polynomials; there is no
degree shift, power of `X`, or other coefficient in this aggregation lemma.
-/

/-- A nonnegative interlacing family aggregates to a real-rooted ordinary sum.

This is the unit-weight specialization of
`IsInterlacingSeqNonneg.weightedSum_isPFPolynomial`.  The explicit nonzero
hypothesis is needed because the library's real-rootedness convention excludes
the zero polynomial.
-/
theorem isRealRooted_sum_of_isInterlacingSeqNonneg
    {pieces : List ℝ[X]} (hpieces : IsInterlacingSeqNonneg pieces)
    (hsum : pieces.sum ≠ 0) :
    pieces.sum ≠ 0 ∧ pieces.sum.Splits := by
  have hpf : IsPFPolynomial (weightedSum (pieces.map fun p => (1, p))) :=
    hpieces.weightedSum_isPFPolynomial
      (pieces.map fun p => (1, p)) (by simp) (by simp)
  rw [weightedSum_map_one] at hpf
  exact hpf.ne_zero_and_splits hsum

private lemma sumCompatibleLeft_of_isInterlacingSeq
    {head : ℝ[X]} {tail : List ℝ[X]}
    (hseq : IsInterlacingSeq (head :: tail))
    (hpos : ∀ p ∈ head :: tail, HasPosLeadingCoeff p)
    (htail : tail ≠ []) :
    SumCompatibleLeft head tail := by
  induction tail with
  | nil => exact (htail rfl).elim
  | cons p tail ih =>
      have hpair : (head :: p :: tail).Pairwise StrictInterl :=
        isInterlacingSeq_iff_pairwise.mp hseq
      have hhead : StrictInterl head p := (List.pairwise_cons.mp hpair).1 p (by simp)
      have hpos_p : HasPosLeadingCoeff p := hpos p (by simp)
      by_cases htail_nil : tail = []
      · subst tail
        exact SumCompatibleLeft.singleton hhead hpos_p
      · have hseq_tail : IsInterlacingSeq (head :: tail) := by
          rw [isInterlacingSeq_iff_pairwise]
          grind
        exact SumCompatibleLeft.cons hhead hpos_p
          (ih hseq_tail (fun q hq => hpos q (by simp only [List.mem_cons]; grind)) htail_nil)

/-- The paper-facing aggregation lemma for a strict interlacing sequence.

The singleton case needs an explicit real-rootedness hypothesis because the
repository's bare `IsInterlacingSeq` predicate is vacuous on singleton lists.
No coefficient nonnegativity is required here; the positive leading
coefficients are the coefficients used by Wagner's addition theorem.
-/
theorem isRealRooted_sum_of_isInterlacingSeq
    {pieces : List ℝ[X]} (hseq : IsInterlacingSeq pieces)
    (hreal : ∀ p ∈ pieces, p ≠ 0 ∧ p.Splits)
    (hpos : ∀ p ∈ pieces, HasPosLeadingCoeff p)
    (hne : pieces ≠ []) :
    pieces.sum ≠ 0 ∧ pieces.sum.Splits := by
  cases pieces with
  | nil => exact (hne rfl).elim
  | cons head tail =>
      by_cases htail_nil : tail = []
      · subst tail
        simpa using hreal head (by simp)
      · have hcomp : SumCompatibleLeft head tail :=
          sumCompatibleLeft_of_isInterlacingSeq hseq hpos htail_nil
        have hhead_pos : HasPosLeadingCoeff head := hpos head (by simp)
        have hsum_pos : HasPosLeadingCoeff tail.sum :=
          SumCompatibleLeft.hasPosLeadingCoeff_sum hcomp
        have hrr := hcomp.toStrictInterl.isRealRooted_pos_combo
          hhead_pos hsum_pos (a := (1 : ℝ)) (b := (1 : ℝ)) (by norm_num) (by norm_num)
        simpa [List.sum_cons] using hrr

/-- Permutation form of the paper-facing aggregation lemma. -/
theorem isRealRooted_of_perm_sum_of_isInterlacingSeq
    {pieces ordered : List ℝ[X]} (hperm : ordered.Perm pieces)
    (hseq : IsInterlacingSeq ordered)
    (hreal : ∀ p ∈ ordered, p ≠ 0 ∧ p.Splits)
    (hpos : ∀ p ∈ ordered, HasPosLeadingCoeff p)
    (hne : pieces ≠ []) :
    pieces.sum ≠ 0 ∧ pieces.sum.Splits := by
  have hordered_ne : ordered ≠ [] := by
    intro hnil
    subst ordered
    exact hne (by simpa using hperm)
  have hordered_rr := isRealRooted_sum_of_isInterlacingSeq hseq hreal hpos hordered_ne
  rw [hperm.sum_eq] at hordered_rr
  exact hordered_rr


variable {U α : Type*} [DecidableEq U] [DecidableEq α]
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- A finite abstract simplicial complex, including its empty face. -/
structure SimplicialComplex (U : Type*) [Fintype U] [DecidableEq U] where
  faces : Finset (Finset U)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {F G : Finset U}, G ∈ faces → F ⊆ G → F ∈ faces

/-- The face set of a finite abstract relative complex `C \ D`.

The fields record the ambient and removed face sets and their inclusion.  The
relative face set is their set difference; this is the finite combinatorial
form of the paper's relative complex convention.
-/
structure RelativeComplex (U : Type*) [DecidableEq U] where
  ambient : Finset (Finset U)
  removed : Finset (Finset U)
  removed_subset : removed ⊆ ambient

variable {Base : SimplicialComplex V} {Subdivided : SimplicialComplex W}

/-- The finite face set of a relative complex. -/
def RelativeComplex.faces (R : RelativeComplex U) : Finset (Finset U) :=
  R.ambient \ R.removed

/-- The number of faces of cardinality `k`, with `k = 0` representing the
    empty face. -/
def faceCount (faces : Finset (Finset U)) (k : ℕ) : ℕ :=
  (faces.filter (fun F => F.card = k)).card

/-- The paper's f-polynomial, with coefficient `f_{k-1}` at `X^k` and the
    empty-face coefficient at `k = 0`.  The dimension parameter is explicit. -/
def fPolynomial (d : ℕ) (faces : Finset (Finset U)) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1), C (faceCount faces k : ℝ) * X ^ k

/-- The paper's h-polynomial in expanded form:
    `(1-X)^d f(X/(1-X)) = ∑ k f_k X^k (1-X)^(d-k)`. -/
def hPolynomial (d : ℕ) (faces : Finset (Finset U)) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C (faceCount faces k : ℝ) * X ^ k * (1 - X) ^ (d - k)

/-- The f-polynomial of a relative complex is the paper's difference
    `f(C \ D) = f(C) - f(D)`. -/
def relativeFPolynomial (d : ℕ) (R : RelativeComplex U) : ℝ[X] :=
  fPolynomial d R.ambient - fPolynomial d R.removed

/-- The h-polynomial of a relative complex, represented by its relative face
    set.  Under `D ⊆ C`, this equals the difference of the two h-polynomials. -/
def relativeHPolynomial (d : ℕ) (R : RelativeComplex U) : ℝ[X] :=
  hPolynomial d R.faces

private lemma faceCount_union_disjoint {A B : Finset (Finset U)} (h : Disjoint A B) (k : ℕ) :
    faceCount (A ∪ B) k = faceCount A k + faceCount B k := by
  classical
  unfold faceCount
  rw [Finset.filter_union]
  rw [Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter h

private lemma fPolynomial_union_disjoint {A B : Finset (Finset U)} (h : Disjoint A B) (d : ℕ) :
    fPolynomial d (A ∪ B) = fPolynomial d A + fPolynomial d B := by
  classical
  unfold fPolynomial
  simp only [faceCount_union_disjoint h, Nat.cast_add, C_add, add_mul,
    Finset.sum_add_distrib]

private lemma hPolynomial_union_disjoint {A B : Finset (Finset U)} (h : Disjoint A B) (d : ℕ) :
    hPolynomial d (A ∪ B) = hPolynomial d A + hPolynomial d B := by
  classical
  unfold hPolynomial
  simp only [faceCount_union_disjoint h, Nat.cast_add, C_add, add_mul,
    Finset.sum_add_distrib]

/-- The relative h-polynomial is the difference of ambient h-polynomials. -/
lemma relativeHPolynomial_eq_sub {R : RelativeComplex U} (d : ℕ) :
    relativeHPolynomial d R = hPolynomial d R.ambient - hPolynomial d R.removed := by
  classical
  have hdisj : Disjoint R.faces R.removed := by
    rw [Finset.disjoint_left]
    intro F hF hFr
    exact (Finset.mem_sdiff.mp hF).2 hFr
  have hunion : R.faces ∪ R.removed = R.ambient := by
    ext F
    simp only [Finset.mem_union, RelativeComplex.faces, Finset.mem_sdiff]
    constructor
    · intro hF
      rcases hF with ⟨hF, _⟩ | hF
      · exact hF
      · exact R.removed_subset hF
    · intro hF
      by_cases hFr : F ∈ R.removed
      · exact Or.inr hFr
      · exact Or.inl ⟨hF, hFr⟩
  have hadd := hPolynomial_union_disjoint hdisj d
  rw [hunion] at hadd
  exact eq_sub_of_add_eq hadd.symm

/-- Restriction of a subdivided face set to a face `F` of the base complex.
    The omitted geometric realization, relative-interior carrier condition,
    ball condition, and boundary-subdivision condition from the paper are not
    represented.  The finite partition identity below needs only the carrier
    test and facet coverage. -/
structure Subdivision (Base : SimplicialComplex V) (Subdivided : SimplicialComplex W) where
  carrier : Finset W → Finset V
  carrier_mem : ∀ {Q : Finset W}, Q ∈ Subdivided.faces → carrier Q ∈ Base.faces
  covered_by_facet : ∀ {Q : Finset W}, Q ∈ Subdivided.faces →
    ∃ F ∈ Base.faces, F ∈ Base.faces.filter (fun G =>
      ∀ H ∈ Base.faces, G ⊆ H → H = G) ∧ carrier Q ⊆ F

/-- The faces of a subdivision whose carriers lie in a specified base face. -/
def restrictionFaces (sub : Subdivision Base Subdivided)
    (F : Finset V) : Finset (Finset W) :=
  Subdivided.faces.filter (fun Q => sub.carrier Q ⊆ F)

/-- The codimension-one faces of a finite face. -/
def boundaryFacets (F : Finset V) : Finset (Finset V) :=
  F.powerset.filter (fun G => G.card + 1 = F.card)

private def boundaryFaces (F : Finset V) : Finset (Finset V) :=
  F.powerset.erase F

private def unionList : List (Finset α) → Finset α
  | [] => ∅
  | S :: Ss => S ∪ unionList Ss

private lemma mem_unionList_iff {Ss : List (Finset α)} {a : α} :
    a ∈ unionList Ss ↔ ∃ S ∈ Ss, a ∈ S := by
  induction Ss with
  | nil => simp [unionList]
  | cons S Ss ih =>
      simp only [unionList, Finset.mem_union]
      rw [ih]
      constructor
      · rintro (hS | ⟨T, hT, haT⟩)
        · exact ⟨S, by simp, hS⟩
        · exact ⟨T, by simp [hT], haT⟩
      · rintro ⟨T, hT, haT⟩
        have hT' : T = S ∨ T ∈ Ss := by simpa using hT
        rcases hT' with hTS | hT
        · exact Or.inl (hTS ▸ haT)
        · exact Or.inr ⟨T, hT, haT⟩

private def greedyPieces (prior : Finset α) : List (Finset α) → List (Finset α)
  | [] => []
  | S :: Ss => (S \ prior) :: greedyPieces (prior ∪ S) Ss

private lemma unionList_greedyPieces (prior : Finset α) (Ss : List (Finset α)) :
    unionList (greedyPieces prior Ss) = unionList Ss \ prior := by
  induction Ss generalizing prior with
  | nil => simp [greedyPieces, unionList]
  | cons S Ss ih =>
      simp only [greedyPieces, unionList]
      rw [ih]
      ext a
      simp only [Finset.mem_union, Finset.mem_sdiff]
      grind

private lemma greedyPieces_disjoint_prior (prior : Finset α) (Ss : List (Finset α)) :
    ∀ T ∈ greedyPieces prior Ss, Disjoint T prior := by
  induction Ss generalizing prior with
  | nil => simp [greedyPieces]
  | cons S Ss ih =>
      intro T hT
      simp only [greedyPieces, List.mem_cons] at hT
      rcases hT with rfl | hT
      · rw [Finset.disjoint_left]
        intro a haS haP
        exact (Finset.mem_sdiff.mp haS).2 haP
      · have h := ih (prior := prior ∪ S) T hT
        exact h.mono_right (Finset.subset_union_left)

private lemma greedyPieces_pairwise (prior : Finset α) (Ss : List (Finset α)) :
    (greedyPieces prior Ss).Pairwise Disjoint := by
  induction Ss generalizing prior with
  | nil => simp [greedyPieces]
  | cons S Ss ih =>
      simp only [greedyPieces, List.pairwise_cons]
      constructor
      · intro T hT
        have h := greedyPieces_disjoint_prior (prior := prior ∪ S) Ss T hT
        rw [Finset.disjoint_left]
        intro a haS haT
        exact (Finset.disjoint_left.mp h) haT (by simp_all)
      · exact ih (prior := prior ∪ S)

private lemma hPolynomial_unionList_of_pairwise_disjoint
    (d : ℕ) (Ss : List (Finset (Finset U)))
    (hSs : Ss.Pairwise Disjoint) :
    hPolynomial d (unionList Ss) = (Ss.map (hPolynomial d)).sum := by
  induction Ss with
  | nil => simp [unionList, hPolynomial, faceCount]
  | cons S Ss ih =>
      have hdisj : Disjoint S (unionList Ss) := by
        rw [Finset.disjoint_left]
        intro a haS haU
        rcases (mem_unionList_iff.mp haU) with ⟨T, hT, haT⟩
        exact (Finset.disjoint_left.mp ((List.pairwise_cons.mp hSs).1 T hT)) haS haT
      rw [unionList, hPolynomial_union_disjoint hdisj, ih (List.pairwise_cons.mp hSs).2]
      simp

private def priorIntersectionFaces (faces : Finset (Finset V))
    (order : List (Finset V)) (i : Fin order.length) : Finset (Finset V) :=
  faces.filter (fun G => G ⊆ order.get i ∧
    ∃ k : Fin order.length, k < i ∧ G ⊆ order.get k)

private def boundaryPrefixFaces (order : List (Finset V)) (r : ℕ) : Finset (Finset V) :=
  (order.take r).foldl (fun acc F => acc ∪ F.powerset) ∅

/-- Recursive paper-style shelling data for a finite facet set.

The successor constructor contains the paper's two boundary clauses: the first
facet has a shelling of its boundary, and every previous-facet intersection is
an initial segment of a boundary shelling. -/
inductive ShellingData : ℕ → Finset (Finset V) → Finset (Finset V) →
    List (Finset V) → Prop
  | zero {faces facets : Finset (Finset V)} {order : List (Finset V)}
      (nodup : order.Nodup)
      (facets_mem : ∀ F, F ∈ facets ↔ F ∈ order) :
      ShellingData 0 faces facets order
  | succ {d : ℕ} {faces facets : Finset (Finset V)} {head : Finset V}
      {tail : List (Finset V)}
      (nodup : (head :: tail).Nodup)
      (facets_mem : ∀ F, F ∈ facets ↔ F ∈ head :: tail)
      (first_order : List (Finset V))
      (first_boundary : ShellingData d (boundaryFaces head)
        (boundaryFacets head) first_order)
      (prefix_order : Fin (tail.length + 1) → List (Finset V))
      (prefix_r : Fin (tail.length + 1) → ℕ)
      (prefix_boundary : ∀ i,
        ShellingData d (boundaryFaces ((head :: tail).get i))
          (boundaryFacets ((head :: tail).get i)) (prefix_order i))
      (prefix_nonempty : ∀ i, 0 < i →
        (priorIntersectionFaces faces (head :: tail) i).Nonempty)
      (prefix_length : ∀ i, prefix_r i ≤ (prefix_order i).length)
      (prefix_eq : ∀ i,
        priorIntersectionFaces faces (head :: tail) i =
          boundaryPrefixFaces (prefix_order i) (prefix_r i)) :
      ShellingData (d + 1) faces facets (head :: tail)

/-- A shelling order with the paper's facet coverage and boundary-prefix data.

The stages-2--4 identity below uses only `nodup` and `facets_mem`; the
facet dimension and recursive boundary fields are retained so the theorem has
an honest shelling hypothesis, but are not needed by the finite partition
argument. -/
structure Shelling (Base : SimplicialComplex V) (d : ℕ) where
  order : List (Finset V)
  nodup : order.Nodup
  facets_mem : ∀ F, F ∈ Base.faces.filter (fun G =>
    ∀ H ∈ Base.faces, G ⊆ H → H = G) ↔ F ∈ order
  facet_card : ∀ F, F ∈ Base.faces.filter (fun G =>
    ∀ H ∈ Base.faces, G ⊆ H → H = G) → F.card = d + 1
  data : ShellingData d
    Base.faces (Base.faces.filter (fun G =>
      ∀ H ∈ Base.faces, G ⊆ H → H = G)) order

/-- The list of subdivision restrictions indexed by a proposed facet order. -/
def shellingRestrictions (sub : Subdivision Base Subdivided)
    (order : List (Finset V)) : List (Finset (Finset W)) :=
  order.map (restrictionFaces sub)

/-- The relative shelling pieces
    `C'|_{F_i} \ ⋃_{k<i} C'|_{F_k}`.  `greedyPieces` carries the accumulated
    previous restriction union, so this definition is independent of any
    shelling boundary clause. -/
def relativePieceFaces (sub : Subdivision Base Subdivided)
    (order : List (Finset V)) : List (Finset (Finset W)) :=
  greedyPieces ∅ (shellingRestrictions sub order)

private lemma unionList_shellingRestrictions (sub : Subdivision Base Subdivided)
    (sh : Shelling Base d) :
    unionList (shellingRestrictions sub sh.order) = Subdivided.faces := by
  classical
  ext Q
  constructor
  · intro hQ
    rcases (mem_unionList_iff.mp hQ) with ⟨R, hR, hQR⟩
    simp only [shellingRestrictions, List.mem_map] at hR
    rcases hR with ⟨F, hF, rfl⟩
    exact (Finset.mem_filter.mp hQR).1
  · intro hQ
    obtain ⟨F, hF, hfacet, hcarrier⟩ := sub.covered_by_facet hQ
    have hfacet' := (Finset.mem_filter.mp hfacet).2
    have horder : F ∈ sh.order :=
      (sh.facets_mem F).mp (Finset.mem_filter.mpr ⟨hF, hfacet'⟩)
    apply mem_unionList_iff.mpr
    refine ⟨restrictionFaces sub F, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨F, horder, rfl⟩
    · simp [restrictionFaces, hQ, hcarrier]

/-- The relative pieces partition all faces of the subdivided complex. -/
theorem relativePieceFaces_partition (sub : Subdivision Base Subdivided)
    (sh : Shelling Base d) :
    unionList (relativePieceFaces sub sh.order) = Subdivided.faces ∧
      (relativePieceFaces sub sh.order).Pairwise Disjoint := by
  have hunion := unionList_shellingRestrictions sub sh
  constructor
  · simpa [relativePieceFaces, unionList_greedyPieces] using hunion
  · exact greedyPieces_pairwise ∅ (shellingRestrictions sub sh.order)

/-- The h-polynomials of the relative pieces in shelling order. -/
def relativePieceHPolynomials (d : ℕ) (sub : Subdivision Base Subdivided)
    (sh : Shelling Base d) : List ℝ[X] :=
  (relativePieceFaces sub sh.order).map (hPolynomial d)

/-- The h-polynomial is the sum of the h-polynomials of the relative pieces. -/
theorem hPolynomial_eq_sum_relativePieces
    (sub : Subdivision Base Subdivided) (sh : Shelling Base d) :
    hPolynomial d Subdivided.faces = (relativePieceHPolynomials d sub sh).sum := by
  have hpart := relativePieceFaces_partition sub sh
  rw [← hpart.1]
  exact hPolynomial_unionList_of_pairwise_disjoint d _ hpart.2

/-- A nonnegative interlacing shelling criterion for the h-polynomial. -/
theorem isRealRooted_hPolynomial_of_perm_isInterlacingSeqNonneg
    (sub : Subdivision Base Subdivided) (sh : Shelling Base d)
    {ordered : List ℝ[X]}
    (hperm : ordered.Perm (relativePieceHPolynomials d sub sh))
    (hseq : IsInterlacingSeqNonneg ordered)
    (hpoly_ne : hPolynomial d Subdivided.faces ≠ 0) :
    hPolynomial d Subdivided.faces ≠ 0 ∧
      (hPolynomial d Subdivided.faces).Splits := by
  rw [hPolynomial_eq_sum_relativePieces sub sh] at hpoly_ne ⊢
  have hpieces_ne : relativePieceHPolynomials d sub sh ≠ [] := by
    intro hnil
    apply hpoly_ne
    rw [hnil]
    simp
  have hordered_ne : (ordered.sum : ℝ[X]) ≠ 0 := by
    intro hzero
    apply hpoly_ne
    rw [← hperm.sum_eq, hzero]
  have hrr := isRealRooted_sum_of_isInterlacingSeqNonneg hseq hordered_ne
  rw [hperm.sum_eq] at hrr
  exact hrr

/-- A bare interlacing shelling criterion with real-rooted pieces. -/
theorem isRealRooted_hPolynomial_of_perm_isInterlacingSeq
    (sub : Subdivision Base Subdivided) (sh : Shelling Base d)
    {ordered : List ℝ[X]}
    (hperm : ordered.Perm (relativePieceHPolynomials d sub sh))
    (hseq : IsInterlacingSeq ordered)
    (hreal : ∀ p ∈ ordered, p ≠ 0 ∧ p.Splits)
    (hpos : ∀ p ∈ ordered, HasPosLeadingCoeff p)
    (hpoly_ne : hPolynomial d Subdivided.faces ≠ 0) :
    hPolynomial d Subdivided.faces ≠ 0 ∧
      (hPolynomial d Subdivided.faces).Splits := by
  rw [hPolynomial_eq_sum_relativePieces sub sh] at hpoly_ne ⊢
  have hpieces_ne : relativePieceHPolynomials d sub sh ≠ [] := by
    intro hnil
    apply hpoly_ne
    rw [hnil]
    simp
  exact isRealRooted_of_perm_sum_of_isInterlacingSeq
    hperm hseq hreal hpos hpieces_ne

example : insert ∅ (∅ : Finset (Finset (Fin 2))) = {∅} := by decide

example : faceCount (Finset.univ.powerset : Finset (Finset (Fin 2))) 2 = 1 := by
  decide

example :
    unionList (greedyPieces ∅
      ([({∅} : Finset (Finset (Fin 2))), {∅, {0}}])) = {∅, {0}} := by
  decide

example :
    let C : SimplicialComplex (Fin 1) :=
      { faces := {∅, {0}}
        empty_mem := by decide
        down_closed := by decide }
    let sub : Subdivision C C :=
      { carrier := fun _ => ∅
        carrier_mem := by
          intro Q _hQ
          decide
        covered_by_facet := by
          intro Q _hQ
          refine ⟨{0}, by decide, by decide, by simp⟩ }
    restrictionFaces sub {0} = {∅, {0}} := by
  decide

end HlavacekSolus
end RealRooted
