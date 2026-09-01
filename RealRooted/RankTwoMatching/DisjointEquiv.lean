import RealRooted.RankTwoMatching.Orientation

open Polynomial

noncomputable section

namespace RealRooted.Graph.RankTwoInternal

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem ne_of_finset_disjoint {A B : Finset V} (hAB : Disjoint A B)
    {i j : V} (hi : i ∈ A) (hj : j ∈ B) : i ≠ j := by
  intro hij
  subst j
  exact (Finset.disjoint_left.mp hAB hi) hj

def edgeOfDisjointEquiv {A B : Finset V} (hAB : Disjoint A B)
    (f : A ≃ B) (i : A) :
    (_root_.SimpleGraph.completeGraph V).edgeSet :=
  ⟨s(i.1, (f i).1), by
    simpa using ne_of_finset_disjoint hAB i.2 (f i).2⟩

omit [Fintype V] [DecidableEq V] in
theorem edgeOfDisjointEquiv_injective {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B) :
    Function.Injective (edgeOfDisjointEquiv hAB f) := by
  intro i j hij
  have hs := congrArg (fun e => e.1) hij
  change s(i.1, (f i).1) = s(j.1, (f j).1) at hs
  rw [Sym2.eq_iff] at hs
  rcases hs with hs | hs
  · exact Subtype.ext hs.1
  · exact (ne_of_finset_disjoint hAB i.2 (f j).2 hs.1).elim

def matchingOfDisjointEquiv {A B : Finset V} (hAB : Disjoint A B)
    (f : A ≃ B) :
    Finset (_root_.SimpleGraph.completeGraph V).edgeSet :=
  Finset.univ.image (edgeOfDisjointEquiv hAB f)

omit [Fintype V] in
theorem matchingOfDisjointEquiv_card {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B) :
    (matchingOfDisjointEquiv hAB f).card = A.card := by
  exact (Finset.card_image_of_injective Finset.univ
    (edgeOfDisjointEquiv_injective hAB f)).trans (by simp)

omit [Fintype V] in
theorem matchingOfDisjointEquiv_isMatching {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B) :
    IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V)
      (matchingOfDisjointEquiv hAB f) := by
  intro e he e' he' hne hshare
  rw [matchingOfDisjointEquiv, Finset.mem_image] at he he'
  obtain ⟨i, hi, rfl⟩ := he
  obtain ⟨j, hj, rfl⟩ := he'
  rcases hshare with ⟨x, hx⟩
  change (x ∈ s(i.1, (f i).1)) ∧ (x ∈ s(j.1, (f j).1)) at hx
  simp only [Sym2.mem_iff] at hx
  rcases hx with ⟨hil | hir, hjl | hjr⟩
  · apply hne
    apply Subtype.ext
    have hij : i = j := Subtype.ext (hil.symm.trans hjl)
    subst j
    rfl
  · exact ne_of_finset_disjoint hAB i.2 (f j).2 (hil.symm.trans hjr)
  · exact ne_of_finset_disjoint hAB j.2 (f i).2 (hjl.symm.trans hir)
  · apply hne
    apply Subtype.ext
    have hfij : f i = f j := Subtype.ext (hir.symm.trans hjr)
    have hij : i = j := f.injective hfij
    subst j
    rfl

omit [Fintype V] in
theorem matchingOf_orientationVertexEquiv
    {M : Finset (_root_.SimpleGraph.completeGraph V).edgeSet}
    (hM : IsMatchingEdgeFinset (_root_.SimpleGraph.completeGraph V) M)
    (o : ∀ e, e ∈ M → V)
    (ho : ∀ e (he : e ∈ M), o e he ∈ e.1) :
    matchingOfDisjointEquiv (orientationVertices_disjoint hM o ho)
        (orientationVertexEquiv hM o ho) = M := by
  ext e
  constructor
  · intro he
    rw [matchingOfDisjointEquiv, Finset.mem_image] at he
    obtain ⟨i, hi, hei⟩ := he
    let m : M := (orientationLeftEquiv hM o ho).symm i
    have hmleft : (orientationLeftEquiv hM o ho) m = i := by simp [m]
    have heval : e.1 = m.1.1 := by
      rw [← hei]
      apply Sym2.ext
      intro x
      simp only [edgeOfDisjointEquiv, Sym2.mem_iff]
      have hright :
          (orientationVertexEquiv hM o ho i).1 =
            Sym2.Mem.other' (ho m.1 m.2) := by
        change ((orientationRightEquiv hM o ho)
          ((orientationLeftEquiv hM o ho).symm i)).1 = _
        rfl
      have hleft : i.1 = o m.1 m.2 := by
        rw [← hmleft]
        rfl
      rw [hleft, hright]
      have hspec :
          s(o m.1 m.2, Sym2.Mem.other' (ho m.1 m.2)) = m.1.1 :=
        Sym2.other_spec' (ho m.1 m.2)
      constructor
      · intro hx
        rw [← hspec]
        simpa only [Sym2.mem_iff] using hx
      · intro hx
        rw [← hspec] at hx
        simpa only [Sym2.mem_iff] using hx
    have : e = m.1 := Subtype.ext heval
    rw [this]
    exact m.2
  · intro he
    rw [matchingOfDisjointEquiv, Finset.mem_image]
    let m : M := ⟨e, he⟩
    let i : orientationLeftVertices o := (orientationLeftEquiv hM o ho) m
    refine ⟨i, by simp, ?_⟩
    apply Subtype.ext
    change s(i.1, ((orientationVertexEquiv hM o ho) i).1) = e.1
    have hleft : i.1 = o e he := rfl
    have hright : ((orientationVertexEquiv hM o ho) i).1 =
        Sym2.Mem.other' (ho e he) := by
      change ((orientationRightEquiv hM o ho)
        ((orientationLeftEquiv hM o ho).symm
          ((orientationLeftEquiv hM o ho) m))).1 = _
      rw [Equiv.symm_apply_apply]
      rfl
    rw [hleft, hright, Sym2.other_spec' (ho e he)]

def edgeIndexEquiv {A B : Finset V} (hAB : Disjoint A B)
    (f : A ≃ B) : A ≃ matchingOfDisjointEquiv hAB f :=
  Equiv.ofBijective
    (fun i : A ↦ ⟨edgeOfDisjointEquiv hAB f i, by
      rw [matchingOfDisjointEquiv, Finset.mem_image]
      exact ⟨i, by simp, rfl⟩⟩)
    ⟨fun i j hij ↦ edgeOfDisjointEquiv_injective hAB f
        (congrArg Subtype.val hij),
      fun e ↦ by
        have he : e.1 ∈ Finset.univ.image (edgeOfDisjointEquiv hAB f) := e.2
        rw [Finset.mem_image] at he
        obtain ⟨i, hi, hie⟩ := he
        exact ⟨i, Subtype.ext hie⟩⟩

def orientationOfDisjointEquiv {A B : Finset V} (hAB : Disjoint A B)
    (f : A ≃ B) (e : (_root_.SimpleGraph.completeGraph V).edgeSet)
    (he : e ∈ matchingOfDisjointEquiv hAB f) : V :=
  ((edgeIndexEquiv hAB f).symm ⟨e, he⟩).1

omit [Fintype V] in
theorem orientationOfDisjointEquiv_mem {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B)
    (e : (_root_.SimpleGraph.completeGraph V).edgeSet)
    (he : e ∈ matchingOfDisjointEquiv hAB f) :
    orientationOfDisjointEquiv hAB f e he ∈ e.1 := by
  let i : A := (edgeIndexEquiv hAB f).symm ⟨e, he⟩
  have hei : edgeOfDisjointEquiv hAB f i = e := by
    exact congrArg Subtype.val ((edgeIndexEquiv hAB f).apply_symm_apply ⟨e, he⟩)
  change i.1 ∈ e.1
  have hi : i.1 ∈ (edgeOfDisjointEquiv hAB f i).1 := Sym2.mem_mk_left _ _
  simpa only [hei] using hi

omit [Fintype V] in
theorem orientationLeftVertices_ofDisjointEquiv {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B) :
    orientationLeftVertices (orientationOfDisjointEquiv hAB f) = A := by
  ext x
  constructor
  · intro hx
    rw [orientationLeftVertices, Finset.mem_image] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact ((edgeIndexEquiv hAB f).symm e).2
  · intro hx
    rw [orientationLeftVertices, Finset.mem_image]
    let i : A := ⟨x, hx⟩
    let e : matchingOfDisjointEquiv hAB f := edgeIndexEquiv hAB f i
    refine ⟨e, by simp, ?_⟩
    change ((edgeIndexEquiv hAB f).symm e).1 = x
    rw [show e = edgeIndexEquiv hAB f i from rfl,
      (edgeIndexEquiv hAB f).symm_apply_apply]

omit [Fintype V] in
theorem other_orientationOfDisjointEquiv {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B)
    (e : (_root_.SimpleGraph.completeGraph V).edgeSet)
    (he : e ∈ matchingOfDisjointEquiv hAB f) :
    Sym2.Mem.other' (orientationOfDisjointEquiv_mem hAB f e he) =
      (f ((edgeIndexEquiv hAB f).symm ⟨e, he⟩)).1 := by
  let i : A := (edgeIndexEquiv hAB f).symm ⟨e, he⟩
  have hei : edgeOfDisjointEquiv hAB f i = e := by
    exact congrArg Subtype.val ((edgeIndexEquiv hAB f).apply_symm_apply ⟨e, he⟩)
  have hs := Sym2.other_spec' (orientationOfDisjointEquiv_mem hAB f e he)
  change s(i.1, Sym2.Mem.other' (orientationOfDisjointEquiv_mem hAB f e he)) = e.1 at hs
  apply Sym2.congr_right.mp
  exact hs.trans (congrArg Subtype.val hei).symm

omit [Fintype V] in
theorem orientationRightVertices_ofDisjointEquiv {A B : Finset V}
    (hAB : Disjoint A B) (f : A ≃ B) :
    orientationRightVertices (orientationOfDisjointEquiv hAB f)
        (orientationOfDisjointEquiv_mem hAB f) = B := by
  ext x
  constructor
  · intro hx
    rw [orientationRightVertices, Finset.mem_image] at hx
    obtain ⟨e, he, hex⟩ := hx
    rw [other_orientationOfDisjointEquiv hAB f e.1 e.2] at hex
    exact hex ▸ (f ((edgeIndexEquiv hAB f).symm e)).2
  · intro hx
    rw [orientationRightVertices, Finset.mem_image]
    let j : B := ⟨x, hx⟩
    let i : A := f.symm j
    let e : matchingOfDisjointEquiv hAB f := edgeIndexEquiv hAB f i
    refine ⟨e, by simp, ?_⟩
    rw [other_orientationOfDisjointEquiv hAB f e.1 e.2]
    change (f ((edgeIndexEquiv hAB f).symm e)).1 = x
    rw [show e = edgeIndexEquiv hAB f i from rfl,
      (edgeIndexEquiv hAB f).symm_apply_apply]
    exact congrArg Subtype.val (f.apply_symm_apply j)

omit [Fintype V] in
theorem card_finsetEquiv (A B : Finset V) (f : A ≃ B) :
    Fintype.card (A ≃ B) = A.card.factorial := by
  calc
    Fintype.card (A ≃ B) = Fintype.card (Equiv.Perm A) :=
      (Fintype.card_congr (Equiv.equivCongr (Equiv.refl A) f)).symm
    _ = (Fintype.card A).factorial := Fintype.card_perm
    _ = A.card.factorial := by simp

omit [Fintype V] in
theorem sum_finsetEquiv_const (A B : Finset V) (f : A ≃ B) (w : ℝ) :
    ∑ _g : A ≃ B, w = (A.card.factorial : ℝ) * w := by
  rw [Finset.sum_const, Finset.card_univ, card_finsetEquiv A B f]
  simp

end RealRooted.Graph.RankTwoInternal
