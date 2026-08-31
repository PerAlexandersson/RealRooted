import RealRooted.RankTwoMatching.DisjointEquiv

open Polynomial

noncomputable section

namespace RealRooted.Graph.RankTwoInternal

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The total `a`/`b` weight of two disjoint size-`k` vertex sets. -/
def disjointSelectionWeight (a b : V → ℝ) (k : ℕ) : ℝ := by
  classical
  exact
    ∑ A ∈ (Finset.univ.filter fun A : Finset V ↦ A.card = k),
      ∑ B ∈ (Finset.univ.filter fun B : Finset V ↦ B.card = k ∧ Disjoint A B),
        (∏ i ∈ A, a i) * ∏ j ∈ B, b j

def sizeKMatchings (k : ℕ) :
    Finset (Finset (_root_.SimpleGraph.completeGraph V).edgeSet) := by
  classical
  exact Finset.univ.filter fun M ↦
    IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M ∧ M.card = k

theorem weightedMatchingNumber_eq_sum_sizeK (a b : V → ℝ) (k : ℕ) :
    weightedMatchingNumber (_root_.SimpleGraph.completeGraph V)
        (completeGraphRankTwoWeight a b) k =
      ∑ M ∈ sizeKMatchings k,
        ∏ e ∈ M, completeGraphRankTwoWeight a b e := by
  classical
  simp only [weightedMatchingNumber, sizeKMatchings, Finset.sum_filter]
  simp only [SimpleGraph.completeGraph_eq_top]
  apply Finset.sum_bij (fun M _ ↦ M)
  · simp
  · intro M _ N _ hMN
    exact hMN
  · intro M _
    exact ⟨M, by simp, rfl⟩
  · intro M _
    by_cases hm : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M
    · by_cases hc : M.card = k <;> simp [hm, hc]
    · simp [hm]

def orientedMatchingWeightSum (a b : V → ℝ) (k : ℕ) : ℝ :=
  ∑ M ∈ sizeKMatchings k,
    ∑ o ∈ M.pi (fun e ↦ e.1.toFinset),
      ∏ e ∈ M.attach, edgeOrientationWeight a b e.1 (o e.1 e.2)

theorem weightedMatchingNumber_eq_orientedMatchingWeightSum
    (a b : V → ℝ) (k : ℕ) :
    weightedMatchingNumber (_root_.SimpleGraph.completeGraph V)
        (completeGraphRankTwoWeight a b) k =
      orientedMatchingWeightSum a b k := by
  rw [weightedMatchingNumber_eq_sum_sizeK]
  apply Finset.sum_congr rfl
  intro M hM
  exact prod_completeGraphRankTwoWeight_eq_sum_orientations a b M

def disjointEquivWeightSum (a b : V → ℝ) (k : ℕ) : ℝ :=
  ∑ A ∈ (Finset.univ.filter fun A : Finset V ↦ A.card = k),
    ∑ B ∈ (Finset.univ.filter fun B : Finset V ↦ B.card = k ∧ Disjoint A B),
      ∑ _f : A ≃ B, (∏ i ∈ A, a i) * ∏ j ∈ B, b j

abbrev OrientedKMatching (k : ℕ) :=
  Σ M : {M // M ∈ sizeKMatchings (V := V) k},
    ∀ e : M.1, {i : V // i ∈ e.1.1}

abbrev DisjointEquivIndex (k : ℕ) :=
  Σ A : {A : Finset V //
      A ∈ (Finset.univ.filter fun A : Finset V ↦ A.card = k)},
    Σ B : {B : Finset V //
        B ∈ (Finset.univ.filter fun B : Finset V ↦
          B.card = k ∧ Disjoint A.1 B)},
      A.1 ≃ B.1

def orientedKMatching_mem
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    ∀ e (he : e ∈ x.1.1), (x.2 ⟨e, he⟩).1 ∈ e.1 := by
  intro e he
  exact (x.2 ⟨e, he⟩).2

def orientedKMatchingOrientation
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    ∀ e, e ∈ x.1.1 → V :=
  fun e he ↦ (x.2 ⟨e, he⟩).1

def orientedKMatching_isMatching
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) x.1.1 := by
  classical
  exact (Finset.mem_filter.mp x.1.2).2.1

def orientedKMatching_card
    {k : ℕ} (x : OrientedKMatching (V := V) k) : x.1.1.card = k := by
  classical
  exact (Finset.mem_filter.mp x.1.2).2.2

def orientedMatchingToDisjointEquiv
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    DisjointEquivIndex (V := V) k := by
  let hM := orientedKMatching_isMatching x
  let ho := orientedKMatching_mem x
  let o := orientedKMatchingOrientation x
  let A := orientationLeftVertices o
  let B := orientationRightVertices o ho
  refine ⟨⟨A, ?_⟩, ⟨⟨B, ?_⟩, orientationVertexEquiv hM o ho⟩⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      (orientationLeftVertices_card hM o ho).trans
        (orientedKMatching_card x)⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      ⟨(orientationRightVertices_card hM o ho).trans
          (orientedKMatching_card x),
        orientationVertices_disjoint hM o ho⟩⟩

def disjointEquivToOrientedMatching
    {k : ℕ} (y : DisjointEquivIndex (V := V) k) :
    OrientedKMatching (V := V) k := by
  classical
  let A := y.1.1
  let B := y.2.1.1
  have hAcard : A.card = k := (Finset.mem_filter.mp y.1.2).2
  have hBcard : B.card = k := (Finset.mem_filter.mp y.2.1.2).2.1
  have hAB : Disjoint A B := (Finset.mem_filter.mp y.2.1.2).2.2
  let M := matchingOfDisjointEquiv hAB y.2.2
  let o := orientationOfDisjointEquiv hAB y.2.2
  refine ⟨⟨M, ?_⟩, ?_⟩
  · rw [sizeKMatchings, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, matchingOfDisjointEquiv_isMatching hAB y.2.2,
      (matchingOfDisjointEquiv_card hAB y.2.2).trans hAcard⟩
  · intro e
    exact ⟨o e.1 e.2,
      orientationOfDisjointEquiv_mem hAB y.2.2 e.1 e.2⟩

@[simp]
theorem orientedMatchingToDisjointEquiv_left
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    (orientedMatchingToDisjointEquiv x).1.1 =
      orientationLeftVertices (orientedKMatchingOrientation x) := by
  rfl

@[simp]
theorem orientedMatchingToDisjointEquiv_right
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    (orientedMatchingToDisjointEquiv x).2.1.1 =
      orientationRightVertices (orientedKMatchingOrientation x)
        (orientedKMatching_mem x) := by
  rfl

@[simp]
theorem disjointEquivToOrientedMatching_edges
    {k : ℕ} (y : DisjointEquivIndex (V := V) k) :
    (disjointEquivToOrientedMatching y).1.1 =
      matchingOfDisjointEquiv
        (Finset.mem_filter.mp y.2.1.2).2.2 y.2.2 := by
  rfl

omit [Fintype V] in
theorem orientationOf_orientationVertexEquiv_eq
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1)
    (e : (_root_.SimpleGraph.completeGraph V).edgeSet)
    (he : e ∈ M)
    (he' : e ∈ matchingOfDisjointEquiv
      (orientationVertices_disjoint hM o ho)
      (orientationVertexEquiv hM o ho)) :
    orientationOfDisjointEquiv
        (orientationVertices_disjoint hM o ho)
        (orientationVertexEquiv hM o ho) e he' = o e he := by
  let hdisj := orientationVertices_disjoint hM o ho
  let f := orientationVertexEquiv hM o ho
  let x := orientationOfDisjointEquiv hdisj f e he'
  have hxA : x ∈ orientationLeftVertices o := by
    exact ((edgeIndexEquiv hdisj f).symm ⟨e, he'⟩).2
  have hxedge : x ∈ e.1 :=
    orientationOfDisjointEquiv_mem hdisj f e he'
  have hspec : s(o e he, Sym2.Mem.other' (ho e he)) = e.1 :=
    Sym2.other_spec' (ho e he)
  rw [← hspec] at hxedge
  simp only [Sym2.mem_iff] at hxedge
  rcases hxedge with hx | hx
  · exact hx
  · exfalso
    have hxB : x ∈ orientationRightVertices o ho := by
      rw [orientationRightVertices, Finset.mem_image]
      exact ⟨⟨e, he⟩, by simp, hx.symm⟩
    exact (Finset.disjoint_left.mp hdisj hxA) hxB

theorem disjointEquivToOrientedMatching_orientedMatchingToDisjointEquiv
    {k : ℕ} (x : OrientedKMatching (V := V) k) :
    disjointEquivToOrientedMatching
        (orientedMatchingToDisjointEquiv x) = x := by
  have hfirst :
      (disjointEquivToOrientedMatching
        (orientedMatchingToDisjointEquiv x)).1 = x.1 := by
    apply Subtype.ext
    exact matchingOf_orientationVertexEquiv
      (orientedKMatching_isMatching x) (orientedKMatchingOrientation x)
        (orientedKMatching_mem x)
  apply Sigma.ext hfirst
  have hEdges :
      (disjointEquivToOrientedMatching
        (orientedMatchingToDisjointEquiv x)).1.1 = x.1.1 :=
    congrArg Subtype.val hfirst
  have hmemPred :
      (fun e ↦ e ∈ (disjointEquivToOrientedMatching
        (orientedMatchingToDisjointEquiv x)).1.1) ≍
      (fun e ↦ e ∈ x.1.1) := by
    apply heq_of_eq
    funext e
    rw [hEdges]
  apply Function.hfunext
  · exact congrArg (fun M ↦ {e // e ∈ M.1}) hfirst
  · intro e e' hee
    have heval : e.1 = e'.1 := eq_of_heq
      ((Subtype.heq_iff_coe_heq rfl hmemPred).mp hee)
    have houtPred :
        (fun i : V ↦ i ∈ e.1.1) ≍ (fun i : V ↦ i ∈ e'.1.1) := by
      apply heq_of_eq
      rw [heval]
    apply (Subtype.heq_iff_coe_heq rfl houtPred).mpr
    apply heq_of_eq
    have heSource : e.1 ∈ x.1.1 := by
      rw [heval]
      exact e'.2
    have heSourceSubtype : (⟨e.1, heSource⟩ : x.1.1) = e' :=
      Subtype.ext heval
    rw [← heSourceSubtype]
    apply orientationOf_orientationVertexEquiv_eq

theorem disjointEquivIndex_ext
    {k : ℕ} {x y : DisjointEquivIndex (V := V) k}
    (hA : x.1.1 = y.1.1)
    (hB : x.2.1.1 = y.2.1.1)
    (hf : ∀ (i : x.1.1) (j : y.1.1), i.1 = j.1 →
      (x.2.2 i).1 = (y.2.2 j).1) : x = y := by
  rcases x with ⟨⟨A, hAx⟩, ⟨⟨B, hBx⟩, f⟩⟩
  rcases y with ⟨⟨A', hAy⟩, ⟨⟨B', hBy⟩, g⟩⟩
  dsimp only at hA hB hf ⊢
  subst A'
  subst B'
  have hAp : hAx = hAy := Subsingleton.elim _ _
  cases hAp
  have hBp : hBx = hBy := Subsingleton.elim _ _
  cases hBp
  have hfg : f = g := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact hf i i rfl
  cases hfg
  rfl

omit [Fintype V] in
theorem orientationVertexEquiv_ofDisjointEquiv_val
    {A B : Finset V} (hAB : Disjoint A B) (f : A ≃ B)
    (i : orientationLeftVertices (orientationOfDisjointEquiv hAB f))
    (j : A) (hij : i.1 = j.1) :
    ((orientationVertexEquiv
      (matchingOfDisjointEquiv_isMatching hAB f)
      (orientationOfDisjointEquiv hAB f)
      (orientationOfDisjointEquiv_mem hAB f)) i).1 = (f j).1 := by
  let M := matchingOfDisjointEquiv hAB f
  let o := orientationOfDisjointEquiv hAB f
  let hM := matchingOfDisjointEquiv_isMatching hAB f
  let ho := orientationOfDisjointEquiv_mem hAB f
  let e : M := (orientationLeftEquiv hM o ho).symm i
  have heleft : o e.1 e.2 = i.1 := by
    exact congrArg Subtype.val
      ((orientationLeftEquiv hM o ho).apply_symm_apply i)
  have hedgeIndex : ((edgeIndexEquiv hAB f).symm e).1 = j.1 := by exact heleft.trans hij
  change Sym2.Mem.other' (ho e.1 e.2) = (f j).1
  rw [other_orientationOfDisjointEquiv hAB f e.1 e.2]
  exact congrArg Subtype.val (congrArg f (Subtype.ext hedgeIndex))

theorem orientedMatchingToDisjointEquiv_disjointEquivToOrientedMatching
    {k : ℕ} (y : DisjointEquivIndex (V := V) k) :
    orientedMatchingToDisjointEquiv
        (disjointEquivToOrientedMatching y) = y := by
  rcases y with ⟨⟨A, hA⟩, ⟨⟨B, hB⟩, f⟩⟩
  let hAB : Disjoint A B := (Finset.mem_filter.mp hB).2.2
  have hleft : orientationLeftVertices
      (orientationOfDisjointEquiv hAB f) = A :=
    orientationLeftVertices_ofDisjointEquiv hAB f
  have hright : orientationRightVertices
      (orientationOfDisjointEquiv hAB f)
      (orientationOfDisjointEquiv_mem hAB f) = B :=
    orientationRightVertices_ofDisjointEquiv hAB f
  apply disjointEquivIndex_ext hleft hright
  intro i j hij
  apply orientationVertexEquiv_ofDisjointEquiv_val hAB f
  exact hij

def orientedKMatchingEquivDisjointEquiv (k : ℕ) :
    OrientedKMatching (V := V) k ≃ DisjointEquivIndex (V := V) k where
  toFun := orientedMatchingToDisjointEquiv
  invFun := disjointEquivToOrientedMatching
  left_inv := disjointEquivToOrientedMatching_orientedMatchingToDisjointEquiv
  right_inv := orientedMatchingToDisjointEquiv_disjointEquivToOrientedMatching

abbrev PiOrientationIndex
    (M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet) :=
  {o // o ∈ M.pi (fun e ↦ e.1.toFinset)}

def piOrientationEquiv
    (M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet) :
    PiOrientationIndex M ≃ (∀ e : M, {i : V // i ∈ e.1.1}) where
  toFun o e := ⟨o.1 e.1 e.2,
    Sym2.mem_toFinset.mp (Finset.mem_pi.mp o.2 e.1 e.2)⟩
  invFun q := ⟨fun e he ↦ (q ⟨e, he⟩).1, by
    rw [Finset.mem_pi]
    intro e he
    exact Sym2.mem_toFinset.mpr (q ⟨e, he⟩).2⟩
  left_inv o := by
    apply Subtype.ext
    funext e he
    rfl
  right_inv q := by
    funext e
    apply Subtype.ext
    rfl

abbrev PiOrientedKMatching (k : ℕ) :=
  Σ M : {M // M ∈ sizeKMatchings (V := V) k}, PiOrientationIndex M.1

def piOrientedKMatchingEquiv (k : ℕ) :
    PiOrientedKMatching (V := V) k ≃ OrientedKMatching (V := V) k :=
  Equiv.sigmaCongrRight fun M ↦ piOrientationEquiv M.1

def piOrientedKMatchingWeight (a b : V → ℝ) {k : ℕ}
    (x : PiOrientedKMatching (V := V) k) : ℝ :=
  ∏ e ∈ x.1.1.attach,
    edgeOrientationWeight a b e.1 (x.2.1 e.1 e.2)

def orientedKMatchingWeight (a b : V → ℝ) {k : ℕ}
    (x : OrientedKMatching (V := V) k) : ℝ :=
  ∏ e ∈ x.1.1.attach,
    edgeOrientationWeight a b e.1
      (orientedKMatchingOrientation x e.1 e.2)

def disjointEquivIndexWeight (a b : V → ℝ) {k : ℕ}
    (y : DisjointEquivIndex (V := V) k) : ℝ :=
  (∏ i ∈ y.1.1, a i) * ∏ j ∈ y.2.1.1, b j

theorem piOrientedKMatchingEquiv_weight
    (a b : V → ℝ) {k : ℕ} (x : PiOrientedKMatching (V := V) k) :
    piOrientedKMatchingWeight a b x =
      orientedKMatchingWeight a b (piOrientedKMatchingEquiv k x) := by
  rfl

theorem orientedKMatchingEquivDisjointEquiv_weight
    (a b : V → ℝ) {k : ℕ} (x : OrientedKMatching (V := V) k) :
    orientedKMatchingWeight a b x =
      disjointEquivIndexWeight a b
        (orientedKMatchingEquivDisjointEquiv k x) := by
  exact orientationWeightProduct a b (orientedKMatching_isMatching x)
    (orientedKMatchingOrientation x) (orientedKMatching_mem x)

theorem orientedMatchingWeightSum_eq_piOrientedKMatching_sum
    (a b : V → ℝ) (k : ℕ) :
    orientedMatchingWeightSum a b k =
      ∑ x : PiOrientedKMatching (V := V) k,
        piOrientedKMatchingWeight a b x := by
  classical
  unfold orientedMatchingWeightSum
  rw [Finset.sum_subtype (sizeKMatchings k) (fun _ ↦ Iff.rfl)]
  · rw [Fintype.sum_sigma]
    apply Fintype.sum_congr
    intro M
    rw [Finset.sum_subtype
      (M.1.pi (fun e ↦ e.1.toFinset)) (fun _ ↦ Iff.rfl)]
    rfl

theorem disjointEquivWeightSum_eq_disjointEquivIndex_sum
    (a b : V → ℝ) (k : ℕ) :
    disjointEquivWeightSum a b k =
      ∑ y : DisjointEquivIndex (V := V) k,
        disjointEquivIndexWeight a b y := by
  classical
  unfold disjointEquivWeightSum
  rw [Finset.sum_subtype
    ((Finset.univ : Finset (Finset V)).filter fun A ↦ A.card = k)
    (fun _ ↦ Iff.rfl)]
  · rw [Fintype.sum_sigma]
    apply Fintype.sum_congr
    intro A
    rw [Finset.sum_subtype
      ((Finset.univ : Finset (Finset V)).filter fun B ↦
        B.card = k ∧ Disjoint A.1 B) (fun _ ↦ Iff.rfl)]
    · rw [Fintype.sum_sigma]
      rfl

theorem orientedMatchingWeightSum_eq_disjointEquivWeightSum
    (a b : V → ℝ) (k : ℕ) :
    orientedMatchingWeightSum a b k = disjointEquivWeightSum a b k := by
  rw [orientedMatchingWeightSum_eq_piOrientedKMatching_sum,
    disjointEquivWeightSum_eq_disjointEquivIndex_sum]
  calc
    (∑ x : PiOrientedKMatching (V := V) k,
        piOrientedKMatchingWeight a b x) =
        ∑ x : OrientedKMatching (V := V) k,
          orientedKMatchingWeight a b x := by
      apply Fintype.sum_equiv (piOrientedKMatchingEquiv k)
      intro x
      exact piOrientedKMatchingEquiv_weight a b x
    _ = ∑ y : DisjointEquivIndex (V := V) k,
          disjointEquivIndexWeight a b y := by
      apply Fintype.sum_equiv (orientedKMatchingEquivDisjointEquiv k)
      intro x
      exact orientedKMatchingEquivDisjointEquiv_weight a b x

theorem disjointEquivWeightSum_eq_factorial_mul
    (a b : V → ℝ) (k : ℕ) :
    disjointEquivWeightSum a b k =
      (k.factorial : ℝ) * disjointSelectionWeight a b k := by
  classical
  simp only [disjointEquivWeightSum, disjointSelectionWeight]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have hAcard : A.card = k := Finset.mem_filter.mp hA |>.2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hAB : Disjoint A B := (Finset.mem_filter.mp hB).2.2
  have hBcard : B.card = k := (Finset.mem_filter.mp hB).2.1
  have f : A ≃ B := Fintype.equivOfCardEq (by simp [hAcard, hBcard])
  rw [sum_finsetEquiv_const A B f, hAcard]

theorem disjointSelectionWeight_eq_disjointSubsetWeight
    (a b : V → ℝ) (k : ℕ) :
    disjointSelectionWeight a b k =
      RankTwoMatchingModel.disjointSubsetWeight a b k := by
  classical
  letI : DecidableEq V := Classical.decEq V
  simp only [disjointSelectionWeight,
    RankTwoMatchingModel.disjointSubsetWeight,
    Finset.powersetCard_eq_filter]
  rw [Finset.powerset_univ]
  have hsets (B : Finset V) :
      ((Finset.univ \ B).powerset.filter fun A : Finset V ↦ A.card = k) =
        (Finset.univ.filter fun A : Finset V ↦
          A.card = k ∧ Disjoint A B) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ,
      true_and]
    constructor
    · intro h
      exact ⟨h.2, Finset.disjoint_left.mpr fun x hxA hxB ↦
        (Finset.mem_sdiff.mp (h.1 hxA)).2 hxB⟩
    · intro h
      refine ⟨?_, h.1⟩
      intro x hxA
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ x, Finset.disjoint_left.mp h.2 hxA⟩
  simp_rw [hsets]
  simp_rw [Finset.mul_sum]
  simp only [Finset.sum_filter]
  have hite (p : Prop) [Decidable p] (f : Finset V → ℝ) :
      (if p then ∑ B, f B else 0) = ∑ B, if p then f B else 0 := by
    by_cases hp : p <;> simp [hp]
  simp_rw [hite]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro A
  by_cases hA : A.card = k
  · simp only [hA, ↓reduceIte]
    apply Fintype.sum_congr
    intro B
    by_cases hB : B.card = k
    · by_cases hAB : Disjoint A B
      · simp [hB, hAB.symm, mul_comm]
      · have hBA : ¬ Disjoint B A := by simpa [disjoint_comm] using hAB
        simp [hB, hBA]
    · simp [hB]
  · simp [hA]

end RealRooted.Graph.RankTwoInternal
