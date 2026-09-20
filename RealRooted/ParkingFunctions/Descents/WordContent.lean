import RealRooted.ParkingFunctions.Descents.Basic
import Mathlib.Data.Finsupp.Multiset

/-!
# Content of finite words

This neutral module records alphabet relabeling, literal word content, and the
finite fibers of words with prescribed content.  It is independent of parking
conditions and Smirnov restrictions.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- Relabel every value of a finite word by an alphabet equivalence. -/
def relabelWord {n m : ℕ} (e : Equiv.Perm (Fin m))
    (w : Fin n → Fin m) : Fin n → Fin m :=
  fun i => e (w i)

/-- The literal multiset of values occurring in a finite word. -/
def wordContent {n m : ℕ} (w : Fin n → Fin m) : Multiset (Fin m) :=
  Multiset.map w Finset.univ.val

@[simp]
theorem card_wordContent {n m : ℕ} (w : Fin n → Fin m) :
    (wordContent w).card = n := by
  simp [wordContent]

/-- The exponent vector recording the multiplicity of every letter in a
word. -/
def wordExponent {n m : ℕ} (w : Fin n → Fin m) : Fin m →₀ ℕ :=
  ∑ i, Finsupp.single (w i) 1

/-- The exponent vector and value-multiset presentations of content agree. -/
theorem wordExponent_eq_toFinsupp_wordContent {n m : ℕ}
    (w : Fin n → Fin m) :
    wordExponent w = (wordContent w).toFinsupp := by
  classical
  ext a
  unfold wordExponent wordContent
  simp only [Multiset.toFinsupp_apply]
  rw [Multiset.count_map]
  have hfilter :
      Multiset.filter (fun i => a = w i) Finset.univ.val =
        (Finset.univ.filter fun i => a = w i).val := rfl
  rw [hfilter]
  change (∑ i, Finsupp.single (w i) 1) a =
    (Finset.univ.filter fun i => a = w i).card
  rw [Finset.card_filter]
  change (Finsupp.applyAddHom a) (∑ i, Finsupp.single (w i) 1) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : w i = a
  · subst a
    simp
  · simp [Ne.symm h]

@[simp]
theorem wordContent_relabelWord {n m : ℕ} (e : Equiv.Perm (Fin m))
    (w : Fin n → Fin m) :
    wordContent (relabelWord e w) = (wordContent w).map e := by
  simp only [wordContent, Multiset.map_map]
  rfl

/-- Mapping a word-content multiset by an alphabet permutation maps its
multiplicity vector along the same permutation. -/
theorem toFinsupp_map_equiv {m : ℕ} (μ : Multiset (Fin m))
    (e : Equiv.Perm (Fin m)) :
    (μ.map e).toFinsupp = Finsupp.mapDomain e μ.toFinsupp := by
  apply Multiset.toFinsupp_eq_iff.mpr
  simpa using Finsupp.toMultiset_map μ.toFinsupp e

@[simp]
theorem relabelWord_symm_relabelWord {n m : ℕ} (e : Equiv.Perm (Fin m))
    (w : Fin n → Fin m) :
    relabelWord e.symm (relabelWord e w) = w := by
  funext i
  simp [relabelWord]

/-- The literal finite fiber of words with prescribed labeled content. -/
def contentFiber {n m : ℕ} (μ : Multiset (Fin m)) :
    Finset (Fin n → Fin m) := by
  classical
  exact Finset.univ.filter fun w => wordContent w = μ

@[simp]
theorem mem_contentFiber_iff {n m : ℕ} {μ : Multiset (Fin m)}
    {w : Fin n → Fin m} :
    w ∈ contentFiber μ ↔ wordContent w = μ := by
  simp [contentFiber]

/-- Relabeling transports a labeled content fiber to the correspondingly
relabelled content fiber. -/
def contentFiberRelabelEquiv {n m : ℕ} (e : Equiv.Perm (Fin m))
    (μ : Multiset (Fin m)) :
    {w : Fin n → Fin m // wordContent w = μ} ≃
      {w : Fin n → Fin m // wordContent w = μ.map e} :=
  (Equiv.piCongrRight fun _ => e).subtypeEquiv fun w => by
    change wordContent w = μ ↔ wordContent (relabelWord e w) = μ.map e
    rw [wordContent_relabelWord]
    exact (Multiset.map_injective e.injective).eq_iff.symm

/-- Two contents have the same multiplicity type when they differ only by a
permutation of alphabet labels. -/
def HasContentType {n m : ℕ} (μ : Multiset (Fin m))
    (w : Fin n → Fin m) : Prop :=
  ∃ e : Equiv.Perm (Fin m), wordContent w = μ.map e

/-- Relabeling a word preserves its multiplicity type. -/
theorem HasContentType.relabelWord {n m : ℕ} {μ : Multiset (Fin m)}
    {w : Fin n → Fin m} (e : Equiv.Perm (Fin m))
    (h : HasContentType μ w) :
    HasContentType μ (relabelWord e w) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ.trans e, ?_⟩
  rw [wordContent_relabelWord, hσ, Multiset.map_map]
  rfl

/-- Multiplicity type is invariant under an arbitrary alphabet relabeling. -/
theorem hasContentType_relabelWord_iff {n m : ℕ}
    (μ : Multiset (Fin m)) (e : Equiv.Perm (Fin m))
    (w : Fin n → Fin m) :
    HasContentType μ (relabelWord e w) ↔ HasContentType μ w := by
  constructor
  · intro h
    have h' := h.relabelWord e.symm
    simpa only [relabelWord_symm_relabelWord] using h'
  · exact HasContentType.relabelWord e

/-- Alphabet relabeling preserves the complete equality pattern of a word. -/
theorem relabelWord_eq_iff {n m : ℕ} (e : Equiv.Perm (Fin m))
    (w : Fin n → Fin m) (i j : Fin n) :
    relabelWord e w i = relabelWord e w j ↔ w i = w j := by
  exact e.injective.eq_iff

end

end RealRooted.ParkingFunctions
