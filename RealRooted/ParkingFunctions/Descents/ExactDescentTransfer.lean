import RealRooted.ParkingFunctions.Descents.ExactDescent
import RealRooted.ParkingFunctions.Descents.OrdinaryTransfer

/-!
# Exact descent-set Pollak transfer

This module transfers arbitrary descent-set weights, and hence exact
descent-set cardinalities, from words to ordinary parking functions.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- A sum of a descent-set weight over a fixed content fiber is invariant
under relabeling the content. -/
theorem sum_fixedContentWords_descentSetWeight_map_equiv
    {M : Type*} [AddCommMonoid M] {n m : ℕ}
    (weight : Finset (Fin n) → M) (μ : Multiset (Fin m))
    (e : Equiv.Perm (Fin m)) :
    (∑ w ∈ fixedContentWords (n := n + 1) (μ.map e),
        weight (descentSet w)) =
      ∑ w ∈ fixedContentWords (n := n + 1) μ,
        weight (descentSet w) := by
  classical
  have hsum (ν : Multiset (Fin m)) :
      (∑ w ∈ fixedContentWords (n := n + 1) ν,
          weight (descentSet w)) =
        ∑ S : Finset (Fin n),
          (((fixedContentWords (n := n + 1) ν).filter fun w =>
            descentSet w = S).card) • weight S := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := fixedContentWords (n := n + 1) ν)
      (t := Finset.univ) (g := descentSet)
      (fun _ _ => Finset.mem_univ _)
      (fun w => weight (descentSet w))]
    apply Finset.sum_congr rfl
    intro S _
    apply Finset.sum_eq_card_nsmul
    intro w hw
    rw [(Finset.mem_filter.mp hw).2]
  rw [hsum, hsum]
  apply Finset.sum_congr rfl
  intro S _
  rw [card_fixedContentWords_descentSet_map_equiv μ e S]

/-- Relabeling a fixed content fiber reindexes a descent-set weight sum. -/
theorem sum_fixedContentWords_descentSetWeight_relabelWord
    {M : Type*} [AddCommMonoid M] {n m : ℕ}
    (weight : Finset (Fin n) → M) (μ : Multiset (Fin m))
    (e : Equiv.Perm (Fin m)) :
    (∑ w ∈ fixedContentWords (n := n + 1) μ,
        weight (descentSet (relabelWord e w))) =
      ∑ w ∈ fixedContentWords (n := n + 1) (μ.map e),
        weight (descentSet w) := by
  classical
  apply Finset.sum_bij (fun w _ => relabelWord e w)
  · intro w hw
    rw [mem_fixedContentWords_iff] at hw ⊢
    rw [wordContent_relabelWord, hw]
  · intro w₁ _ w₂ _ h
    funext i
    exact e.injective (congrFun h i)
  · intro w hw
    refine ⟨relabelWord e.symm w, ?_, ?_⟩
    · rw [mem_fixedContentWords_iff] at hw ⊢
      rw [wordContent_relabelWord, hw, Multiset.map_map]
      simp
    · funext i
      exact e.apply_symm_apply (w i)
  · intro w _
    rfl

/-- The aggregate descent-set weight of parking words is invariant under any
alphabet relabeling. -/
theorem sum_parkingWords_descentSetWeight_relabelWord
    {M : Type*} [AddCommMonoid M] (n : ℕ)
    (weight : Finset (Fin n) → M) (e : Equiv.Perm (Fin (n + 2))) :
    (∑ w ∈ parkingWords (n + 1),
        weight (descentSet (relabelWord e w))) =
      ∑ w ∈ parkingWords (n + 1), weight (descentSet w) := by
  classical
  have hpartition :
      (∑ μ ∈ parkingWordContents (n + 1),
          ∑ w ∈ fixedContentWords (n := n + 1) μ,
            weight (descentSet w)) =
        ∑ w ∈ parkingWords (n + 1), weight (descentSet w) := by
    unfold parkingWordContents
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun w hw => Finset.mem_image_of_mem wordContent hw)]
    apply Finset.sum_congr rfl
    intro μ hμ
    rw [parkingWords_filter_wordContent_eq μ hμ]
  rw [← hpartition]
  unfold parkingWordContents
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun w hw => Finset.mem_image_of_mem wordContent hw)]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [parkingWords_filter_wordContent_eq μ hμ]
  calc
    (∑ w ∈ fixedContentWords (n := n + 1) μ,
        weight (descentSet (relabelWord e w))) =
        ∑ w ∈ fixedContentWords (n := n + 1) (μ.map e),
          weight (descentSet w) :=
      sum_fixedContentWords_descentSetWeight_relabelWord weight μ e
    _ = ∑ w ∈ fixedContentWords (n := n + 1) μ,
        weight (descentSet w) :=
      sum_fixedContentWords_descentSetWeight_map_equiv weight μ e

/-- Reindexing a relabel-preimage gives the parking-word descent-set weight
sum. -/
theorem sum_words_filter_isParkingWord_relabelWord_descentSetWeight
    {M : Type*} [AddCommMonoid M] (n : ℕ)
    (weight : Finset (Fin n) → M) (e : Equiv.Perm (Fin (n + 2))) :
    (∑ w ∈ parkingWordRelabelPreimage n e,
        weight (descentSet w)) =
      ∑ w ∈ parkingWords (n + 1), weight (descentSet w) := by
  classical
  unfold parkingWordRelabelPreimage
  calc
    (∑ w ∈ (Finset.univ : Finset (Fin (n + 1) → Fin (n + 2))).filter
        (fun w => IsParkingWord (relabelWord e w)),
        weight (descentSet w)) =
      ∑ w ∈ parkingWords (n + 1),
        weight (descentSet (relabelWord e.symm w)) := by
      apply Finset.sum_bij (fun w _ => relabelWord e w)
      · intro w hw
        rw [Finset.mem_filter] at hw
        rw [mem_parkingWords_iff]
        exact hw.2
      · intro w₁ _ w₂ _ h
        funext i
        exact e.injective (congrFun h i)
      · intro w hw
        refine ⟨relabelWord e.symm w, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hundo : relabelWord e (relabelWord e.symm w) = w := by
            funext i
            exact e.apply_symm_apply (w i)
          rw [hundo]
          exact mem_parkingWords_iff.mp hw
        · funext i
          exact e.apply_symm_apply (w i)
      · intro w _
        congr 2
        exact (relabelWord_symm_relabelWord e w).symm
    _ = ∑ w ∈ parkingWords (n + 1), weight (descentSet w) :=
      sum_parkingWords_descentSetWeight_relabelWord n weight e.symm

/-- Pollak's unique cyclic shift transfers every descent-set weight from all
positive-length words to parking words. -/
theorem wordDescentSetWeightSum_succ_eq_succ_nsmul_parkingWordSum
    {M : Type*} [AddCommMonoid M] (n : ℕ)
    (weight : Finset (Fin n) → M) :
    (∑ w : Fin (n + 1) → Fin (n + 2), weight (descentSet w)) =
      (n + 2) •
        ∑ w ∈ parkingWords (n + 1), weight (descentSet w) := by
  classical
  apply sum_eq_succ_nsmul_of_cyclicValueShift_filter_sum
    (Finset.univ : Finset (Fin (n + 1) → Fin (n + 2)))
    (fun w => weight (descentSet w))
    (∑ w ∈ parkingWords (n + 1), weight (descentSet w))
  intro c
  unfold cyclicParkingPreimage
  change
    (∑ w ∈ (Finset.univ : Finset (Fin (n + 1) → Fin (n + 2))).filter
        (fun w => IsParkingWord (relabelWord (finCycle c) w)),
      weight (descentSet w)) = _
  exact sum_words_filter_isParkingWord_relabelWord_descentSetWeight
    n weight (finCycle c)

/-- Embedding ordinary parking functions in the extra alphabet preserves any
descent-set weight sum. -/
theorem sum_parkingWords_descentSetWeight_eq_parkingFunctions
    {M : Type*} [AddCommMonoid M] (n : ℕ)
    (weight : Finset (Fin n) → M) :
    (∑ w ∈ parkingWords (n + 1), weight (descentSet w)) =
      ∑ w ∈ parkingFunctions (n + 1), weight (descentSet w) := by
  classical
  symm
  apply Finset.sum_bij (fun w _ => parkingWordEmbed w)
  · intro w hw
    rw [mem_parkingWords_iff]
    exact mem_embeddedParkingFunctions_iff_isParkingWord.mp
      (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  · intro w₁ _ w₂ _ h
    exact parkingWordEmbed_injective h
  · intro w hw
    have hw' : w ∈ embeddedParkingFunctions n :=
      mem_embeddedParkingFunctions_iff_isParkingWord.mpr
        (mem_parkingWords_iff.mp hw)
    rw [embeddedParkingFunctions, Finset.mem_image] at hw'
    obtain ⟨v, hv, hvw⟩ := hw'
    exact ⟨v, hv, hvw⟩
  · intro w _
    rw [descentSet_parkingWordEmbed]

/-- Exact positive-length transfer for every descent-set weight. -/
theorem succ_nsmul_parkingDescentSetWeightSum_eq_wordSum
    {M : Type*} [AddCommMonoid M] (n : ℕ)
    (weight : Finset (Fin n) → M) :
    (n + 2) • (∑ w ∈ parkingFunctions (n + 1),
        weight (descentSet w)) =
      ∑ w : Fin (n + 1) → Fin (n + 2), weight (descentSet w) := by
  rw [← sum_parkingWords_descentSetWeight_eq_parkingFunctions]
  exact (wordDescentSetWeightSum_succ_eq_succ_nsmul_parkingWordSum
    n weight).symm

/-- Pollak transfer for every finite word length, including the empty word. -/
theorem sum_wordDescentSetWeight_words_eq_succ_nsmul_parkingFunctions
    {M : Type*} [AddCommMonoid M] (n : ℕ) :
    ∀ weight : Finset (Fin (n - 1)) → M,
      (∑ w : Fin n → Fin (n + 1), weight (wordDescentSet w)) =
        (n + 1) • ∑ w ∈ parkingFunctions n,
          weight (wordDescentSet w) := by
  cases n with
  | zero =>
      intro weight
      simp [parkingFunctions, IsParkingFunction]
  | succ n =>
      simp only [wordDescentSet]
      intro weight
      exact (succ_nsmul_parkingDescentSetWeightSum_eq_wordSum n weight).symm

/-- Exact positive-length descent-set cardinality transfer. -/
theorem succ_mul_card_parkingFunctions_descentSet_eq_card_words
    (n : ℕ) (S : Finset (Fin n)) :
    (n + 2) * ((parkingFunctions (n + 1)).filter fun w =>
      descentSet w = S).card =
    ((Finset.univ : Finset (Fin (n + 1) → Fin (n + 2))).filter fun w =>
      descentSet w = S).card := by
  rw [Finset.card_filter, Finset.card_filter]
  have h := succ_nsmul_parkingDescentSetWeightSum_eq_wordSum n
    (fun T => if T = S then 1 else 0)
  rw [Nat.nsmul_eq_mul] at h
  exact h

/-- Exact descent-set cardinality transfer for every finite word length. -/
theorem succ_mul_card_parkingFunctions_wordDescentSet_eq_card_words
    (n : ℕ) (S : Finset (Fin (n - 1))) :
    (n + 1) * ((parkingFunctions n).filter fun w =>
      wordDescentSet w = S).card =
    ((Finset.univ : Finset (Fin n → Fin (n + 1))).filter fun w =>
      wordDescentSet w = S).card := by
  rw [Finset.card_filter, Finset.card_filter]
  have h := (sum_wordDescentSetWeight_words_eq_succ_nsmul_parkingFunctions n
    (fun T => if T = S then 1 else 0)).symm
  rw [Nat.nsmul_eq_mul] at h
  exact h

/-- In length zero, both the ordinary parking family and the full word family
contain only the empty word. -/
@[simp]
theorem card_parkingFunctions_zero_eq_card_words :
    (parkingFunctions 0).card =
      (Finset.univ : Finset (Fin 0 → Fin 1)).card := by
  simp [parkingFunctions, IsParkingFunction]

end

end RealRooted.ParkingFunctions
