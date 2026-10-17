import RealRooted.ParkingFunctions.Descents.ContentSymmetry
import RealRooted.ParkingFunctions.Descents.LiteralRecurrence
import RealRooted.ParkingFunctions.Descents.PollakTransfer

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

open ParkingFunction (IsParkingFunction parkingFunctions mem_parkingFunctions_iff
  isParkingFunction_iff_prefix)

noncomputable section

/-- Integral descent enumerator of ordinary parking functions. -/
noncomputable def parkingDescentPolynomialInt : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 =>
      (parkingFunctions (n + 1)).genPoly fun w => (List.ofFn w).descentCount

/-- Integral literal descent enumerator of all finite words. -/
noncomputable def literalWordDescentPolynomialInt (m : ℕ) : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 =>
      (Finset.univ : Finset (Fin (n + 1) → Fin m)).genPoly
        fun w => (List.ofFn w).descentCount

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
        (X : ℤ[X]) ^ (List.ofFn (relabelWord e w)).descentCount) =
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
      ∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ (List.ofFn w).descentCount := by
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
        (X : ℤ[X]) ^ (List.ofFn (relabelWord e w)).descentCount) =
      ∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ (List.ofFn w).descentCount := by
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
        (X : ℤ[X]) ^ (List.ofFn (relabelWord e w)).descentCount) =
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
        (X : ℤ[X]) ^ (List.ofFn w).descentCount) =
      ∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ (List.ofFn w).descentCount := by
  classical
  unfold parkingWordRelabelPreimage
  calc
    (∑ w ∈ (Finset.univ : Finset (Fin (n + 1) → Fin (n + 2))).filter
        (fun w => IsParkingWord (relabelWord e w)),
        (X : ℤ[X]) ^ (List.ofFn w).descentCount) =
      ∑ w ∈ parkingWords (n + 1),
        (X : ℤ[X]) ^ (List.ofFn (relabelWord e.symm w)).descentCount := by
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
        rw [relabelWord_symm_relabelWord]
    _ = ∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ (List.ofFn w).descentCount :=
      sum_parkingWords_relabelWord n e.symm

/-- Pollak's unique shift upgrades the cardinality factor to the full
integral descent polynomial in positive length. -/
theorem wordDescentSum_succ_eq_succ_nsmul_parkingWordDescentSum (n : ℕ) :
    (∑ w : Fin (n + 1) → Fin (n + 2), (X : ℤ[X]) ^ (List.ofFn w).descentCount) =
      (n + 2) •
        ∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ (List.ofFn w).descentCount := by
  classical
  apply sum_eq_succ_nsmul_of_cyclicValueShift_filter_sum
    (Finset.univ : Finset (Fin (n + 1) → Fin (n + 2)))
    (fun w => (X : ℤ[X]) ^ (List.ofFn w).descentCount)
    (∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ (List.ofFn w).descentCount)
  intro c
  unfold cyclicParkingPreimage
  change
    (∑ w ∈ (Finset.univ : Finset (Fin (n + 1) → Fin (n + 2))).filter
        (fun w => IsParkingWord (relabelWord (finCycle c) w)),
      (X : ℤ[X]) ^ (List.ofFn w).descentCount) = _
  exact sum_words_filter_isParkingWord_relabelWord n (finCycle c)

/-- The extra-alphabet parking-word descent sum is the ordinary integral
parking-function enumerator in positive length. -/
theorem parkingWordDescentSum_succ_eq_parkingDescentPolynomialInt (n : ℕ) :
    (∑ w ∈ parkingWords (n + 1), (X : ℤ[X]) ^ (List.ofFn w).descentCount) =
      parkingDescentPolynomialInt (n + 1) := by
  unfold parkingDescentPolynomialInt
  unfold Finset.genPoly
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
    beta_reduce
    rw [descentCount_parkingWordEmbed]

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

/-- Casting the integral literal enumerator recovers the existing real one. -/
theorem map_literalWordDescentPolynomialInt (m n : ℕ) :
    (literalWordDescentPolynomialInt m n).map (Int.castRingHom ℝ) =
      literalWordDescentPolynomial m n := by
  cases n with
  | zero => simp [literalWordDescentPolynomialInt, literalWordDescentPolynomial]
  | succ n =>
      exact Finset.map_genPoly _ _ _

/-- Casting the integral parking enumerator recovers the existing real one. -/
theorem map_parkingDescentPolynomialInt (n : ℕ) :
    (parkingDescentPolynomialInt n).map (Int.castRingHom ℝ) =
      parkingDescentPolynomial n := by
  cases n with
  | zero => simp [parkingDescentPolynomialInt, parkingDescentPolynomial]
  | succ n =>
      exact Finset.map_genPoly _ _ _

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
