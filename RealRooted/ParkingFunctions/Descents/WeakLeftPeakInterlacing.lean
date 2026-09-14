import RealRooted.ParkingFunctions.Descents.WeakLeftPeakNDCutPreservation

/-!
# Weak-left-peak interlacing and parking-function real-rootedness

The structural N/D cut invariant is iterated over word length.  Its ordered
P/Q projection gives the terminal interlacing family, while compatibility of
the same finite family proves splitness of the aggregate word enumerator.  The
checked integral Pollak transfer then gives the parking-function result.
-/

open Polynomial

namespace RealRooted.ParkingFunctions

noncomputable section

/-- Every rank of the fixed-alphabet terminal recurrence satisfies the full
structural cut invariant. -/
theorem terminalND_orderedNDCutCompatible (m r : ℕ) :
    OrderedNDCutCompatible (terminalNonDescentReal m r)
      (terminalDescentReal m r) := by
  induction r with
  | zero => exact terminalND_orderedNDCutCompatible_zero m
  | succ r ih => exact terminalND_orderedNDCutCompatible_succ m r ih

/-- The terminal pair mixes occur in the strict order `reverse P ++ Q`. -/
theorem terminalPQOrderReal_interlacing (m r : ℕ) :
    IsInterlacingSeqNonneg (terminalPQOrderReal m r) := by
  change IsInterlacingSeqNonneg
    ((List.ofFn
        (ndCutP (terminalNonDescentReal m r) (terminalDescentReal m r))).reverse ++
      List.ofFn
        (ndCutQ (terminalNonDescentReal m r) (terminalDescentReal m r)))
  exact (terminalND_orderedNDCutCompatible m r).cutCompatible.pqInterlacing

/-- Casting the terminal decomposition gives the exact real aggregate. -/
theorem map_literalWordWeakLeftPeakPolynomialIntOfAlphabet_succ_succ
    (m r : ℕ) :
    (literalWordWeakLeftPeakPolynomialIntOfAlphabet m (r + 2)).map
        (Int.castRingHom ℝ) =
      ∑ j : Fin m, terminalPairMixReal m r j := by
  rw [literalWordWeakLeftPeakPolynomialIntOfAlphabet_succ_succ,
    Polynomial.map_sum]
  apply Fintype.sum_congr
  intro j
  simp [terminalPairMixReal, terminalNonDescentReal, terminalDescentReal]

private theorem sum_terminalPairMixReal_splits
    (m : ℕ) (hm : 0 < m) (r : ℕ) :
    (∑ j : Fin m, terminalPairMixReal m r j).Splits := by
  let ws : List (ℝ × ℝ[X]) :=
    List.ofFn fun j : Fin m ↦ ((1 : ℝ), terminalPairMixReal m r j)
  have hinv := terminalND_orderedNDCutCompatible m r
  have hmem : ∀ ap ∈ ws,
      ap.2 ∈
        List.ofFn
            (ndCutP (terminalNonDescentReal m r) (terminalDescentReal m r)) ++
          List.ofFn
            (ndCutQ (terminalNonDescentReal m r) (terminalDescentReal m r)) := by
    intro ap hap
    rcases List.mem_ofFn.mp hap with ⟨j, rfl⟩
    simp [ndCutP, terminalPairMixReal]
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    rcases List.mem_ofFn.mp hap with ⟨j, rfl⟩
    simp
  have hpos : ∀ ap ∈ ws, HasPosLeadingCoeff ap.2 := by
    intro ap hap
    rcases List.mem_ofFn.mp hap with ⟨j, rfl⟩
    simpa [ndCutP, terminalPairMixReal] using hinv.cutCompatible.p_pos j
  have hex : ∃ ap ∈ ws, 0 < ap.1 := by
    let j : Fin m := ⟨0, hm⟩
    refine ⟨((1 : ℝ), terminalPairMixReal m r j), ?_, by positivity⟩
    exact List.mem_ofFn.mpr ⟨j, by simp⟩
  have hsum_pos : HasPosLeadingCoeff (weightedSum ws) :=
    hasPosLeadingCoeff_weightedSum ws hnonneg hpos hex
  rcases hinv.cutCompatible.familyCompatible_pq ws hmem hnonneg with hzero | hrr
  · exact False.elim (hsum_pos.ne_zero hzero)
  · simpa [ws, weightedSum_ofFn] using hrr.2

/-- On a nonempty finite alphabet, the real cast of every literal-word
weak-left-peak enumerator splits, including the empty and one-letter words. -/
theorem map_literalWordWeakLeftPeakPolynomialIntOfAlphabet_splits
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    ((literalWordWeakLeftPeakPolynomialIntOfAlphabet m n).map
      (Int.castRingHom ℝ)).Splits := by
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero =>
          simpa using Polynomial.Splits.C (R := ℝ) (m : ℝ)
      | succ r =>
          rw [map_literalWordWeakLeftPeakPolynomialIntOfAlphabet_succ_succ]
          exact sum_terminalPairMixReal_splits m hm r

/-- The diagonal all-word enumerator used by the Pollak transfer splits. -/
theorem map_literalWordWeakLeftPeakPolynomialInt_splits (n : ℕ) :
    ((literalWordWeakLeftPeakPolynomialInt n).map
      (Int.castRingHom ℝ)).Splits := by
  rw [literalWordWeakLeftPeakPolynomialInt_eq_ofAlphabet]
  exact map_literalWordWeakLeftPeakPolynomialIntOfAlphabet_splits
    (n + 1) (Nat.succ_pos n) n

/-- Real-coefficient form of the exact integral weak-left-peak transfer. -/
theorem succ_nsmul_map_parkingWeakLeftPeakPolynomialInt_eq_literalWord
    (n : ℕ) :
    (n + 1) •
        (parkingWeakLeftPeakPolynomialInt n).map (Int.castRingHom ℝ) =
      (literalWordWeakLeftPeakPolynomialInt n).map (Int.castRingHom ℝ) := by
  have h := congrArg (fun p : ℤ[X] ↦ p.map (Int.castRingHom ℝ))
    (succ_nsmul_parkingWeakLeftPeakPolynomialInt_eq_literalWord n)
  simpa using h

/-- The real cast of the ordinary parking-function weak-left-peak enumerator
splits for every size. -/
theorem map_parkingWeakLeftPeakPolynomialInt_splits (n : ℕ) :
    ((parkingWeakLeftPeakPolynomialInt n).map
      (Int.castRingHom ℝ)).Splits := by
  let p := (parkingWeakLeftPeakPolynomialInt n).map (Int.castRingHom ℝ)
  have heq : C (n + 1 : ℝ) * p =
      (literalWordWeakLeftPeakPolynomialInt n).map (Int.castRingHom ℝ) := by
    simpa [p, nsmul_eq_mul] using
      succ_nsmul_map_parkingWeakLeftPeakPolynomialInt_eq_literalWord n
  have hscaled : (C (n + 1 : ℝ) * p).Splits := by
    rw [heq]
    exact map_literalWordWeakLeftPeakPolynomialInt_splits n
  exact (Polynomial.splits_mul_iff_right
    (C_ne_zero.mpr (by positivity))
    (Polynomial.Splits.C (n + 1 : ℝ))).mp hscaled

end

end RealRooted.ParkingFunctions
