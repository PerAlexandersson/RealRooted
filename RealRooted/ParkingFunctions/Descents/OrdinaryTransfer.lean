import RealRooted.ParkingFunctions.Descents.ContentSymmetry
import RealRooted.ParkingFunctions.Descents.LiteralRecurrence
import RealRooted.ParkingFunctions.Descents.Pollak

/-!
# Integral ordinary parking-function transfer

This module combines Pollak's unique cyclic shift with the checked symmetry
of ordinary fixed-content descent polynomials. It obtains an exact integral
identity between parking-function descents and all-word descents, then derives
real-rootedness from the literal word recurrence. No chain-sorting theorem is
used.
-/

open Polynomial

namespace RealRooted.ParkingFunctions

noncomputable section

/-- The extra-alphabet parking words of length `n`. -/
def parkingWords (n : ℕ) : Finset (Fin n → Fin (n + 1)) := by
  classical
  exact Finset.univ.filter IsParkingWord

@[simp]
theorem mem_parkingWords_iff {n : ℕ} {w : Fin n → Fin (n + 1)} :
    w ∈ parkingWords n ↔ IsParkingWord w := by
  simp [parkingWords]

/-- Integral descent enumerator of ordinary parking functions. -/
noncomputable def parkingDescentPolynomialInt : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 =>
      descentGeneratingPolynomial (R := ℤ) (parkingFunctions (n + 1))

/-- Integral literal descent enumerator of all finite words. -/
noncomputable def literalWordDescentPolynomialInt (m : ℕ) : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 =>
      descentGeneratingPolynomial (R := ℤ)
        (Finset.univ : Finset (Fin (n + 1) → Fin m))

@[simp]
theorem parkingDescentPolynomialInt_zero :
    parkingDescentPolynomialInt 0 = 1 := rfl

@[simp]
theorem literalWordDescentPolynomialInt_zero (m : ℕ) :
    literalWordDescentPolynomialInt m 0 = 1 := rfl

/-- Contents occurring among parking words. -/
def parkingWordContents (n : ℕ) : Finset (Multiset (Fin (n + 1))) := by
  classical
  exact (parkingWords n).image wordContent

@[simp]
theorem mem_parkingWordContents_iff {n : ℕ}
    {μ : Multiset (Fin (n + 1))} :
    μ ∈ parkingWordContents n ↔
      ∃ w ∈ parkingWords n, wordContent w = μ := by
  simp [parkingWordContents]

/-- Parking removes no words from a represented literal content fiber. -/
theorem parkingWords_filter_wordContent_eq {n : ℕ}
    (μ : Multiset (Fin (n + 1))) (hμ : μ ∈ parkingWordContents n) :
    (parkingWords n).filter (fun w => wordContent w = μ) =
      fixedContentWords μ := by
  classical
  obtain ⟨v, hv, hvμ⟩ := mem_parkingWordContents_iff.mp hμ
  ext w
  rw [Finset.mem_filter, mem_parkingWords_iff, mem_fixedContentWords_iff]
  constructor
  · rintro ⟨_, hcontent⟩
    exact hcontent
  · intro hcontent
    refine ⟨?_, hcontent⟩
    apply (isParkingWord_iff_of_multiset_eq (hcontent.trans hvμ.symm)).2
    exact mem_parkingWords_iff.mp hv

/-- Relabeling a literal content fiber transports its complete descent sum. -/
theorem sum_fixedContentWords_relabelWord {n m : ℕ}
    (μ : Multiset (Fin m)) (e : Equiv.Perm (Fin m)) :
    (∑ w ∈ fixedContentWords (n := n + 1) μ,
        (X : ℤ[X]) ^ descentNumber (relabelWord e w)) =
      fixedContentWordDescentPolynomial (n := n + 1) (μ.map e) := by
  classical
  unfold fixedContentWordDescentPolynomial
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

/-- The complete parking-word sum is the sum of its represented fibers. -/
theorem sum_fixedContentWordDescentPolynomial_parkingWordContents (n : ℕ) :
    (∑ μ ∈ parkingWordContents (n + 1),
        fixedContentWordDescentPolynomial (n := n + 1) μ) =
      ∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ descentNumber w := by
  classical
  unfold parkingWordContents
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun w hw => Finset.mem_image_of_mem wordContent hw)]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [parkingWords_filter_wordContent_eq μ hμ]
  rfl

/-- Aggregate parking-word descents are invariant under alphabet relabeling. -/
theorem sum_parkingWords_relabelWord (n : ℕ)
    (e : Equiv.Perm (Fin (n + 2))) :
    (∑ w ∈ parkingWords (n + 1),
        (X : ℤ[X]) ^ descentNumber (relabelWord e w)) =
      ∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ descentNumber w := by
  classical
  rw [← sum_fixedContentWordDescentPolynomial_parkingWordContents n]
  unfold parkingWordContents
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun w hw => Finset.mem_image_of_mem wordContent hw)]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [parkingWords_filter_wordContent_eq μ hμ]
  calc
    (∑ w ∈ fixedContentWords (n := n + 1) μ,
        (X : ℤ[X]) ^ descentNumber (relabelWord e w)) =
        fixedContentWordDescentPolynomial (n := n + 1) (μ.map e) :=
      sum_fixedContentWords_relabelWord μ e
    _ = fixedContentWordDescentPolynomial (n := n + 1) μ :=
      fixedContentWordDescentPolynomial_map_equiv μ e

/-- All positive-length words whose relabeling by `e` is parking. -/
def parkingWordRelabelPreimage (n : ℕ)
    (e : Equiv.Perm (Fin (n + 2))) : Finset (Fin (n + 1) → Fin (n + 2)) := by
  classical
  exact Finset.univ.filter fun w => IsParkingWord (relabelWord e w)

/-- Reindexing the relabel-preimage produces the parking-word sum. -/
theorem sum_words_filter_isParkingWord_relabelWord (n : ℕ)
    (e : Equiv.Perm (Fin (n + 2))) :
    (∑ w ∈ parkingWordRelabelPreimage n e,
        (X : ℤ[X]) ^ descentNumber w) =
      ∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ descentNumber w := by
  classical
  unfold parkingWordRelabelPreimage
  calc
    (∑ w ∈ (Finset.univ : Finset (Fin (n + 1) → Fin (n + 2))).filter
        (fun w => IsParkingWord (relabelWord e w)),
        (X : ℤ[X]) ^ descentNumber w) =
      ∑ w ∈ parkingWords (n + 1),
        (X : ℤ[X]) ^ descentNumber (relabelWord e.symm w) := by
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
    _ = ∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ descentNumber w :=
      sum_parkingWords_relabelWord n e.symm

/-- Pollak's unique shift upgrades the cardinality factor to the full
integral descent polynomial in positive length. -/
theorem wordDescentSum_succ_eq_succ_nsmul_parkingWordDescentSum (n : ℕ) :
    (∑ w : Fin (n + 1) → Fin (n + 2), (X : ℤ[X]) ^ descentNumber w) =
      (n + 2) •
        ∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ descentNumber w := by
  classical
  have hone (w : Fin (n + 1) → Fin (n + 2)) :
      (∑ c : Fin (n + 2),
          if IsParkingWord (relabelWord (finCycle c) w) then
            (X : ℤ[X]) ^ descentNumber w else 0) =
        (X : ℤ[X]) ^ descentNumber w := by
    have hu : ∃! c : Fin (n + 2),
        IsParkingWord (relabelWord (finCycle c) w) := by
      change ∃! c : Fin (n + 2), IsParkingWord (cyclicValueShift c w)
      exact existsUnique_isParkingWord_cyclicValueShift w
    obtain ⟨c, hc, hunique⟩ := hu
    rw [Finset.sum_eq_single c]
    · simp [hc]
    · intro d _ hdc
      have hn : ¬IsParkingWord (relabelWord (finCycle d) w) := by
        intro hdparking
        exact hdc (hunique d hdparking)
      simp [hn]
    · simp
  calc
    (∑ w : Fin (n + 1) → Fin (n + 2), (X : ℤ[X]) ^ descentNumber w) =
      ∑ w : Fin (n + 1) → Fin (n + 2),
        ∑ c : Fin (n + 2),
          if IsParkingWord (relabelWord (finCycle c) w) then
            (X : ℤ[X]) ^ descentNumber w else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      exact (hone w).symm
    _ = ∑ c : Fin (n + 2),
        ∑ w : Fin (n + 1) → Fin (n + 2),
          if IsParkingWord (relabelWord (finCycle c) w) then
            (X : ℤ[X]) ^ descentNumber w else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ c : Fin (n + 2),
        ∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ descentNumber w := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.sum_filter]
      exact sum_words_filter_isParkingWord_relabelWord n (finCycle c)
    _ = (n + 2) •
        ∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ descentNumber w := by
      simp

/-- The extra-alphabet parking-word descent sum is the ordinary integral
parking-function enumerator in positive length. -/
theorem parkingWordDescentSum_succ_eq_parkingDescentPolynomialInt (n : ℕ) :
    (∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ descentNumber w) =
      parkingDescentPolynomialInt (n + 1) := by
  unfold parkingDescentPolynomialInt
  unfold descentGeneratingPolynomial
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
    congr 2

/-- Exact integral ordinary parking-to-all-words transfer. -/
theorem succ_nsmul_parkingDescentPolynomialInt_eq_literalWordDescentPolynomialInt
    (n : ℕ) :
    (n + 1) • parkingDescentPolynomialInt n =
      literalWordDescentPolynomialInt (n + 1) n := by
  cases n with
  | zero => simp [parkingDescentPolynomialInt, literalWordDescentPolynomialInt]
  | succ n =>
      rw [literalWordDescentPolynomialInt,
        ← parkingWordDescentSum_succ_eq_parkingDescentPolynomialInt]
      exact (wordDescentSum_succ_eq_succ_nsmul_parkingWordDescentSum n).symm

/-- Casting an integral descent-generating polynomial to the reals commutes
with the finite sum. -/
theorem map_descentGeneratingPolynomial_int {n : ℕ} {α : Type*}
    [LT α] [DecidableRel (fun a b : α => a < b)]
    (words : Finset (Fin (n + 1) → α)) :
    (descentGeneratingPolynomial (R := ℤ) words).map
        (Int.castRingHom ℝ) =
      descentGeneratingPolynomial (R := ℝ) words := by
  classical
  unfold descentGeneratingPolynomial
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp

/-- Casting the integral literal enumerator recovers the existing real one. -/
theorem map_literalWordDescentPolynomialInt (m n : ℕ) :
    (literalWordDescentPolynomialInt m n).map (Int.castRingHom ℝ) =
      literalWordDescentPolynomial m n := by
  cases n with
  | zero => simp [literalWordDescentPolynomialInt, literalWordDescentPolynomial]
  | succ n =>
      exact map_descentGeneratingPolynomial_int Finset.univ

/-- Casting the integral parking enumerator recovers the existing real one. -/
theorem map_parkingDescentPolynomialInt (n : ℕ) :
    (parkingDescentPolynomialInt n).map (Int.castRingHom ℝ) =
      parkingDescentPolynomial n := by
  cases n with
  | zero => simp [parkingDescentPolynomialInt, parkingDescentPolynomial]
  | succ n =>
      exact map_descentGeneratingPolynomial_int (parkingFunctions (n + 1))

/-- Real-coefficient form of the integral transfer. -/
theorem succ_nsmul_map_parkingDescentPolynomialInt_eq_literalWord (n : ℕ) :
    (n + 1) • (parkingDescentPolynomialInt n).map (Int.castRingHom ℝ) =
      literalWordDescentPolynomial (n + 1) n := by
  have h := congrArg (fun p : ℤ[X] => p.map (Int.castRingHom ℝ))
    (succ_nsmul_parkingDescentPolynomialInt_eq_literalWordDescentPolynomialInt n)
  simpa [map_literalWordDescentPolynomialInt] using h

/-- The existing real parking enumerator satisfies the same exact transfer. -/
theorem succ_nsmul_parkingDescentPolynomial_eq_literalWord (n : ℕ) :
    (n + 1) • parkingDescentPolynomial n =
      literalWordDescentPolynomial (n + 1) n := by
  rw [← map_parkingDescentPolynomialInt]
  exact succ_nsmul_map_parkingDescentPolynomialInt_eq_literalWord n

/-- The real ordinary parking descent polynomial splits. -/
theorem map_parkingDescentPolynomialInt_splits (n : ℕ) :
    ((parkingDescentPolynomialInt n).map (Int.castRingHom ℝ)).Splits := by
  let p := (parkingDescentPolynomialInt n).map (Int.castRingHom ℝ)
  have heq : C (n + 1 : ℝ) * p = literalWordDescentPolynomial (n + 1) n := by
    simpa [p, nsmul_eq_mul] using
      succ_nsmul_map_parkingDescentPolynomialInt_eq_literalWord n
  have hscaled : (C (n + 1 : ℝ) * p).Splits := by
    rw [heq]
    exact literalWordDescentPolynomial_splits (n + 1) (Nat.succ_pos _) n
  exact (Polynomial.splits_mul_iff_right
    (C_ne_zero.mpr (by positivity))
    (Polynomial.Splits.C (n + 1 : ℝ))).mp hscaled

/-- The ordinary parking-function descent polynomial is real-rooted. -/
theorem parkingDescentPolynomial_splits (n : ℕ) :
    (parkingDescentPolynomial n).Splits := by
  rw [← map_parkingDescentPolynomialInt]
  exact map_parkingDescentPolynomialInt_splits n

end

end RealRooted.ParkingFunctions
