import RealRooted.ParkingFunctions.Descents.Basic

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
theorem wordContent_relabelWord {n m : ℕ} (e : Equiv.Perm (Fin m))
    (w : Fin n → Fin m) :
    wordContent (relabelWord e w) = (wordContent w).map e := by
  simp [wordContent, relabelWord, Function.comp_def]

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
