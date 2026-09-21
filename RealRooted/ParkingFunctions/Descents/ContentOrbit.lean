import RealRooted.Mathlib.Data.Fintype.Card
import RealRooted.ParkingFunctions.Descents.PollakTransfer
import RealRooted.ParkingFunctions.Descents.Tieless

/-!
# Content orbits for parking and Smirnov words

The literal content of a finite word is its multiset of values.  Its content
type is the orbit of that multiset under permutations of the alphabet, so it
remembers multiplicities but not the labels carrying them.  This file proves
that cyclic value shift preserves content type and the Smirnov condition, then
combines those invariants with Pollak's unique parking shift to obtain the
integral fixed-content-type cardinality factor.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- Cyclic value shift transports a labeled content fiber to the fiber of the
cyclically shifted content. -/
def contentFiberCyclicValueShiftEquiv {n : ℕ} (c : Fin (n + 1))
    (μ : Multiset (Fin (n + 1))) :
    {w : Fin n → Fin (n + 1) // wordContent w = μ} ≃
      {w : Fin n → Fin (n + 1) // wordContent w = μ.map (finCycle c)} :=
  contentFiberRelabelEquiv (finCycle c) μ

/-- Alphabet relabeling preserves the Smirnov condition. -/
theorem isSmirnovWord_relabelWord_iff {n m : ℕ}
    (e : Equiv.Perm (Fin m)) (w : Fin n → Fin m) :
    BrandenVecchi.IsSmirnovWord n (relabelWord e w) ↔
      BrandenVecchi.IsSmirnovWord n w := by
  cases n with
  | zero => simp [BrandenVecchi.IsSmirnovWord]
  | succ n =>
      simp only [BrandenVecchi.IsSmirnovWord, ne_eq,
        relabelWord_eq_iff]

/-- Cyclic value shift rotates the literal labeled content. -/
theorem wordContent_cyclicValueShift {n : ℕ} (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) :
    wordContent (cyclicValueShift c w) = (wordContent w).map (finCycle c) := by
  rw [cyclicValueShift_eq_relabelWord, wordContent_relabelWord]

/-- Cyclic value shift preserves multiplicity type. -/
theorem hasContentType_cyclicValueShift_iff {n : ℕ}
    (μ : Multiset (Fin (n + 1))) (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) :
    HasContentType μ (cyclicValueShift c w) ↔ HasContentType μ w := by
  rw [cyclicValueShift_eq_relabelWord, hasContentType_relabelWord_iff]

/-- Cyclic value shift preserves the Smirnov condition. -/
theorem isSmirnovWord_cyclicValueShift_iff {n : ℕ}
    (c : Fin (n + 1)) (w : Fin n → Fin (n + 1)) :
    BrandenVecchi.IsSmirnovWord n (cyclicValueShift c w) ↔
      BrandenVecchi.IsSmirnovWord n w := by
  rw [cyclicValueShift_eq_relabelWord, isSmirnovWord_relabelWord_iff]

/-- A cyclic-invariant word property cuts out a finite type on which every
word still has a unique cyclic shift satisfying the parking condition. -/
theorem card_cyclicInvariant_words_eq_succ_mul_card_parking {n : ℕ}
    (Q : (Fin n → Fin (n + 1)) → Prop) [DecidablePred Q]
    [DecidablePred (fun w => Q w ∧ IsParkingWord w)]
    (hQ : ∀ c w, Q (cyclicValueShift c w) ↔ Q w) :
    Fintype.card {w : Fin n → Fin (n + 1) // Q w} =
      (n + 1) * Fintype.card
        {w : Fin n → Fin (n + 1) // Q w ∧ IsParkingWord w} := by
  classical
  let W := {w : Fin n → Fin (n + 1) // Q w}
  let act : Fin (n + 1) → W ≃ W := fun c =>
    (cyclicValueShiftEquiv n c).subtypeEquiv fun w => (hQ c w).symm
  have hunique : ∀ w : W, ∃! c : Fin (n + 1),
      IsParkingWord (act c w).val := by
    intro w
    change ∃! c : Fin (n + 1), IsParkingWord (cyclicValueShift c w.val)
    exact existsUnique_isParkingWord_cyclicValueShift w.val
  have hcard :=
    Fintype.card_eq_card_mul_card_subtype_of_existsUnique_equiv
      W (Fin (n + 1)) act (fun w => IsParkingWord w.val) hunique
  calc
    Fintype.card W = (n + 1) * Fintype.card
        {w : W // IsParkingWord w.val} := by
      simpa only [Fintype.card_fin] using hcard
    _ = (n + 1) * Fintype.card
        {w : Fin n → Fin (n + 1) // Q w ∧ IsParkingWord w} := by
      congr 1
      exact Fintype.card_congr
        (Equiv.subtypeSubtypeEquivSubtypeInter Q IsParkingWord)

/-- Words of prescribed multiplicity type that are also Smirnov words. -/
def contentTypeSmirnovWords {n : ℕ} (μ : Multiset (Fin (n + 1))) :
    Finset (Fin n → Fin (n + 1)) := by
  classical
  exact Finset.univ.filter fun w =>
    HasContentType μ w ∧ BrandenVecchi.IsSmirnovWord n w

@[simp]
theorem mem_contentTypeSmirnovWords_iff {n : ℕ}
    {μ : Multiset (Fin (n + 1))} {w : Fin n → Fin (n + 1)} :
    w ∈ contentTypeSmirnovWords μ ↔
      HasContentType μ w ∧ BrandenVecchi.IsSmirnovWord n w := by
  simp [contentTypeSmirnovWords]

/-- The parking members of a fixed-multiplicity-type Smirnov family. -/
def parkingContentTypeSmirnovWords {n : ℕ}
    (μ : Multiset (Fin (n + 1))) : Finset (Fin n → Fin (n + 1)) := by
  classical
  exact (contentTypeSmirnovWords μ).filter IsParkingWord

@[simp]
theorem mem_parkingContentTypeSmirnovWords_iff {n : ℕ}
    {μ : Multiset (Fin (n + 1))} {w : Fin n → Fin (n + 1)} :
    w ∈ parkingContentTypeSmirnovWords μ ↔
      (HasContentType μ w ∧ BrandenVecchi.IsSmirnovWord n w) ∧
        IsParkingWord w := by
  simp [parkingContentTypeSmirnovWords]

/-- In positive length, the parking side of a fixed-type Smirnov family is
exactly its intersection with the literal embedded parking family. -/
theorem mem_parkingContentTypeSmirnovWords_iff_embedded {n : ℕ}
    {μ : Multiset (Fin (n + 2))} {w : Fin (n + 1) → Fin (n + 2)} :
    w ∈ parkingContentTypeSmirnovWords μ ↔
      w ∈ contentTypeSmirnovWords μ ∧ w ∈ embeddedParkingFunctions n := by
  rw [mem_parkingContentTypeSmirnovWords_iff,
    mem_contentTypeSmirnovWords_iff,
    mem_embeddedParkingFunctions_iff_isParkingWord]

/-- Fixed multiplicity type and the Smirnov condition are jointly invariant
under cyclic value shift. -/
theorem contentTypeSmirnov_cyclicValueShift_iff {n : ℕ}
    (μ : Multiset (Fin (n + 1))) (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) :
    (HasContentType μ (cyclicValueShift c w) ∧
        BrandenVecchi.IsSmirnovWord n (cyclicValueShift c w)) ↔
      HasContentType μ w ∧ BrandenVecchi.IsSmirnovWord n w := by
  exact and_congr (hasContentType_cyclicValueShift_iff μ c w)
    (isSmirnovWord_cyclicValueShift_iff c w)

/-- Pollak's cyclic action gives the exact integral factor `n + 1` within
every fixed multiplicity type of Smirnov words. -/
theorem card_contentTypeSmirnov_eq_succ_mul_card_parking {n : ℕ}
    (μ : Multiset (Fin (n + 1))) :
    Nat.card
        {w : Fin n → Fin (n + 1) //
          HasContentType μ w ∧ BrandenVecchi.IsSmirnovWord n w} =
      (n + 1) * Nat.card
        {w : Fin n → Fin (n + 1) //
          (HasContentType μ w ∧ BrandenVecchi.IsSmirnovWord n w) ∧
            IsParkingWord w} := by
  classical
  simpa only [Nat.card_eq_fintype_card] using
    card_cyclicInvariant_words_eq_succ_mul_card_parking
      (fun w => HasContentType μ w ∧ BrandenVecchi.IsSmirnovWord n w)
      (contentTypeSmirnov_cyclicValueShift_iff μ)

/-- Finset form of the fixed-multiplicity-type orbit count. -/
theorem card_contentTypeSmirnovWords_eq_succ_mul_card_parking {n : ℕ}
    (μ : Multiset (Fin (n + 1))) :
    (contentTypeSmirnovWords μ).card =
      (n + 1) * (parkingContentTypeSmirnovWords μ).card := by
  classical
  have hleft :
      Nat.card
          {w : Fin n → Fin (n + 1) //
            HasContentType μ w ∧ BrandenVecchi.IsSmirnovWord n w} =
        (contentTypeSmirnovWords μ).card := by
    let := Fintype.subtype (contentTypeSmirnovWords μ)
      (fun _ => mem_contentTypeSmirnovWords_iff)
    rw [@Nat.card_eq_fintype_card _ this]
    exact Fintype.subtype_card (contentTypeSmirnovWords μ)
      (fun _ => mem_contentTypeSmirnovWords_iff)
  have hright :
      Nat.card
          {w : Fin n → Fin (n + 1) //
            (HasContentType μ w ∧ BrandenVecchi.IsSmirnovWord n w) ∧
              IsParkingWord w} =
        (parkingContentTypeSmirnovWords μ).card := by
    let := Fintype.subtype (parkingContentTypeSmirnovWords μ)
      (fun _ => mem_parkingContentTypeSmirnovWords_iff)
    rw [@Nat.card_eq_fintype_card _ this]
    exact Fintype.subtype_card (parkingContentTypeSmirnovWords μ)
      (fun _ => mem_parkingContentTypeSmirnovWords_iff)
  calc
    (contentTypeSmirnovWords μ).card = Nat.card
        {w : Fin n → Fin (n + 1) //
          HasContentType μ w ∧ BrandenVecchi.IsSmirnovWord n w} := hleft.symm
    _ = (n + 1) * Nat.card
        {w : Fin n → Fin (n + 1) //
          (HasContentType μ w ∧ BrandenVecchi.IsSmirnovWord n w) ∧
            IsParkingWord w} :=
      card_contentTypeSmirnov_eq_succ_mul_card_parking μ
    _ = (n + 1) * (parkingContentTypeSmirnovWords μ).card := by rw [hright]

/-- The empty word is the unique Smirnov word of empty content type. -/
@[simp]
theorem card_contentTypeSmirnovWords_zero :
    (contentTypeSmirnovWords
      (n := 0) (0 : Multiset (Fin 1))).card = 1 := by
  simp [contentTypeSmirnovWords, HasContentType, wordContent,
    BrandenVecchi.IsSmirnovWord]

/-- The empty word is also the unique parking member of its content type. -/
@[simp]
theorem card_parkingContentTypeSmirnovWords_zero :
    (parkingContentTypeSmirnovWords
      (n := 0) (0 : Multiset (Fin 1))).card = 1 := by
  simp [parkingContentTypeSmirnovWords, contentTypeSmirnovWords,
    HasContentType, wordContent, BrandenVecchi.IsSmirnovWord,
    Finset.filter_singleton, IsParkingWord]

end

end RealRooted.ParkingFunctions
