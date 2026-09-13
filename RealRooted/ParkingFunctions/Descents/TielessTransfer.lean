import RealRooted.BrandenVecchi.SmirnovInterlacing
import RealRooted.ParkingFunctions.Descents.ContentSymmetry
import RealRooted.ParkingFunctions.Descents.Pollak

/-!
# Integral tieless parking-to-Smirnov transfer

This file assembles the literal parking embedding, Pollak's cyclic action,
and fixed-content Smirnov symmetry.  The cyclic action does not preserve
descents pointwise; fixed-content symmetry supplies exactly the aggregate
invariance needed for the integral factor.
-/

open Polynomial

namespace RealRooted.ParkingFunctions

noncomputable section

/-- The Smirnov words that satisfy the extra-alphabet parking condition. -/
def parkingSmirnovWords (n : ℕ) : Finset (Fin n → Fin (n + 1)) := by
  classical
  exact (BrandenVecchi.smirnovWords (n + 1) n).filter IsParkingWord

@[simp]
theorem mem_parkingSmirnovWords_iff {n : ℕ}
    {w : Fin n → Fin (n + 1)} :
    w ∈ parkingSmirnovWords n ↔
      BrandenVecchi.IsSmirnovWord n w ∧ IsParkingWord w := by
  simp [parkingSmirnovWords]

/-- The labeled contents represented by parking Smirnov words. -/
def parkingSmirnovContents (n : ℕ) : Finset (Multiset (Fin (n + 1))) := by
  classical
  exact (parkingSmirnovWords n).image wordContent

@[simp]
theorem mem_parkingSmirnovContents_iff {n : ℕ}
    {μ : Multiset (Fin (n + 1))} :
    μ ∈ parkingSmirnovContents n ↔
      ∃ w ∈ parkingSmirnovWords n, wordContent w = μ := by
  simp [parkingSmirnovContents]

/-- Relabeling a fixed content fiber transports its complete descent sum to
the correspondingly relabeled content fiber. -/
theorem sum_fixedContentSmirnovWords_relabelWord {n m : ℕ}
    (μ : Multiset (Fin m)) (e : Equiv.Perm (Fin m)) :
    (∑ w ∈ fixedContentSmirnovWords (n := n) μ,
        X ^ BrandenVecchi.smirnovDescentNumber (relabelWord e w)) =
      fixedContentSmirnovPolynomial (n := n) (μ.map e) := by
  classical
  unfold fixedContentSmirnovPolynomial
  apply Finset.sum_bij (fun w _ => relabelWord e w)
  · intro w hw
    rw [mem_fixedContentSmirnovWords_iff] at hw ⊢
    exact ⟨(isSmirnovWord_relabelWord_iff e w).2 hw.1, by
      rw [wordContent_relabelWord, hw.2]⟩
  · intro w₁ hw₁ w₂ hw₂ h
    funext i
    exact e.injective (congrFun h i)
  · intro w hw
    refine ⟨relabelWord e.symm w, ?_, ?_⟩
    · rw [mem_fixedContentSmirnovWords_iff] at hw ⊢
      exact ⟨(isSmirnovWord_relabelWord_iff e.symm w).2 hw.1, by
        rw [wordContent_relabelWord, hw.2, Multiset.map_map]
        simp⟩
    · funext i
      exact e.apply_symm_apply (w i)
  · intro w hw
    rfl

/-- Within a represented parking content, the parking restriction removes no
Smirnov words because the parking condition depends only on content. -/
theorem parkingSmirnovWords_filter_wordContent_eq {n : ℕ}
    (μ : Multiset (Fin (n + 1))) (hμ : μ ∈ parkingSmirnovContents n) :
    (parkingSmirnovWords n).filter (fun w => wordContent w = μ) =
      fixedContentSmirnovWords μ := by
  classical
  obtain ⟨v, hv, hvμ⟩ := mem_parkingSmirnovContents_iff.mp hμ
  ext w
  rw [Finset.mem_filter, mem_parkingSmirnovWords_iff,
    mem_fixedContentSmirnovWords_iff]
  constructor
  · rintro ⟨⟨hsmirnov, _⟩, hcontent⟩
    exact ⟨hsmirnov, hcontent⟩
  · rintro ⟨hsmirnov, hcontent⟩
    refine ⟨⟨hsmirnov, ?_⟩, hcontent⟩
    apply (isParkingWord_iff_of_multiset_eq
      (hcontent.trans hvμ.symm)).2
    exact (mem_parkingSmirnovWords_iff.mp hv).2

/-- The parking Smirnov descent sum is the sum of its represented labeled
content fibers. -/
theorem sum_fixedContentSmirnovPolynomial_parkingSmirnovContents (n : ℕ) :
    (∑ μ ∈ parkingSmirnovContents n,
        fixedContentSmirnovPolynomial (n := n) μ) =
      ∑ w ∈ parkingSmirnovWords n,
        X ^ BrandenVecchi.smirnovDescentNumber w := by
  classical
  unfold parkingSmirnovContents
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun w hw => Finset.mem_image_of_mem wordContent hw)]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [parkingSmirnovWords_filter_wordContent_eq μ hμ]
  rfl

/-- Aggregate descents on parking Smirnov words are invariant under an
arbitrary alphabet relabeling. -/
theorem sum_parkingSmirnovWords_relabelWord {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) :
    (∑ w ∈ parkingSmirnovWords n,
        (X : ℤ[X]) ^
          BrandenVecchi.smirnovDescentNumber (relabelWord e w)) =
      ∑ w ∈ parkingSmirnovWords n,
        X ^ BrandenVecchi.smirnovDescentNumber w := by
  classical
  rw [← sum_fixedContentSmirnovPolynomial_parkingSmirnovContents n]
  unfold parkingSmirnovContents
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun w hw => Finset.mem_image_of_mem wordContent hw)]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [parkingSmirnovWords_filter_wordContent_eq μ hμ]
  calc
    (∑ w ∈ fixedContentSmirnovWords (n := n) μ,
        (X : ℤ[X]) ^
          BrandenVecchi.smirnovDescentNumber (relabelWord e w)) =
      fixedContentSmirnovPolynomial (n := n) (μ.map e) :=
        sum_fixedContentSmirnovWords_relabelWord μ e
    _ = fixedContentSmirnovPolynomial (n := n) μ :=
      fixedContentSmirnovPolynomial_map_equiv μ e

/-- Smirnov words whose image under one alphabet relabeling is parking. -/
def parkingSmirnovRelabelPreimage {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) : Finset (Fin n → Fin (n + 1)) := by
  classical
  exact (BrandenVecchi.smirnovWords (n + 1) n).filter fun w =>
    IsParkingWord (relabelWord e w)

/-- Reindexing all Smirnov words by a relabeling turns the condition that the
relabeling is parking into the parking Smirnov family.  Fixed-content
symmetry removes the inverse relabeling from the descent weight. -/
theorem sum_smirnovWords_filter_isParkingWord_relabelWord {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) :
    (∑ w ∈ parkingSmirnovRelabelPreimage e,
        (X : ℤ[X]) ^ BrandenVecchi.smirnovDescentNumber w) =
      ∑ w ∈ parkingSmirnovWords n,
        X ^ BrandenVecchi.smirnovDescentNumber w := by
  classical
  unfold parkingSmirnovRelabelPreimage
  calc
    (∑ w ∈ (BrandenVecchi.smirnovWords (n + 1) n).filter
          (fun w => IsParkingWord (relabelWord e w)),
        (X : ℤ[X]) ^ BrandenVecchi.smirnovDescentNumber w) =
      ∑ w ∈ parkingSmirnovWords n,
        X ^ BrandenVecchi.smirnovDescentNumber (relabelWord e.symm w) := by
      apply Finset.sum_bij (fun w _ => relabelWord e w)
      · intro w hw
        rw [Finset.mem_filter] at hw
        rw [mem_parkingSmirnovWords_iff]
        exact ⟨(isSmirnovWord_relabelWord_iff e w).2
          (BrandenVecchi.mem_smirnovWords_iff.mp hw.1), hw.2⟩
      · intro w₁ hw₁ w₂ hw₂ h
        funext i
        exact e.injective (congrFun h i)
      · intro w hw
        refine ⟨relabelWord e.symm w, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨BrandenVecchi.mem_smirnovWords_iff.mpr
            ((isSmirnovWord_relabelWord_iff e.symm w).2
              (mem_parkingSmirnovWords_iff.mp hw).1), ?_⟩
          have hundo : relabelWord e (relabelWord e.symm w) = w := by
            funext i
            exact e.apply_symm_apply (w i)
          rw [hundo]
          exact (mem_parkingSmirnovWords_iff.mp hw).2
        · funext i
          exact e.apply_symm_apply (w i)
      · intro w hw
        congr 2
        exact (relabelWord_symm_relabelWord e w).symm
    _ = ∑ w ∈ parkingSmirnovWords n,
        X ^ BrandenVecchi.smirnovDescentNumber w :=
      sum_parkingSmirnovWords_relabelWord e.symm

/-- Pollak's unique successful cyclic shift, combined with fixed-content
symmetry, upgrades the cardinality factor to the complete integral descent
polynomial. -/
theorem smirnovDescentSum_eq_succ_nsmul_parkingSmirnovDescentSum
    (n : ℕ) :
    (∑ w ∈ BrandenVecchi.smirnovWords (n + 1) n,
        (X : ℤ[X]) ^ BrandenVecchi.smirnovDescentNumber w) =
      (n + 1) • ∑ w ∈ parkingSmirnovWords n,
        X ^ BrandenVecchi.smirnovDescentNumber w := by
  classical
  have hone (w : Fin n → Fin (n + 1)) :
      (∑ c : Fin (n + 1),
          if IsParkingWord (relabelWord (finCycle c) w) then
            (X : ℤ[X]) ^ BrandenVecchi.smirnovDescentNumber w else 0) =
        X ^ BrandenVecchi.smirnovDescentNumber w := by
    have hu : ∃! c : Fin (n + 1),
        IsParkingWord (relabelWord (finCycle c) w) := by
      simpa only [← cyclicValueShift_eq_relabelWord] using
        existsUnique_isParkingWord_cyclicValueShift w
    obtain ⟨c, hc, hunique⟩ := hu
    rw [Finset.sum_eq_single c]
    · simp [hc]
    · intro d hd hdc
      have hn : ¬IsParkingWord (relabelWord (finCycle d) w) := by
        intro hdparking
        exact hdc (hunique d hdparking)
      simp [hn]
    · simp
  calc
    (∑ w ∈ BrandenVecchi.smirnovWords (n + 1) n,
        (X : ℤ[X]) ^ BrandenVecchi.smirnovDescentNumber w) =
      ∑ w ∈ BrandenVecchi.smirnovWords (n + 1) n,
        ∑ c : Fin (n + 1),
          if IsParkingWord (relabelWord (finCycle c) w) then
            X ^ BrandenVecchi.smirnovDescentNumber w else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      exact (hone w).symm
    _ = ∑ c : Fin (n + 1),
        ∑ w ∈ BrandenVecchi.smirnovWords (n + 1) n,
          if IsParkingWord (relabelWord (finCycle c) w) then
            X ^ BrandenVecchi.smirnovDescentNumber w else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ c : Fin (n + 1),
        ∑ w ∈ parkingSmirnovWords n,
          X ^ BrandenVecchi.smirnovDescentNumber w := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [← Finset.sum_filter]
      exact sum_smirnovWords_filter_isParkingWord_relabelWord (finCycle c)
    _ = (n + 1) • ∑ w ∈ parkingSmirnovWords n,
        X ^ BrandenVecchi.smirnovDescentNumber w := by
      simp

/-- The embedded parking Smirnov sum is exactly the literal tieless parking
descent polynomial, including the empty-word boundary. -/
theorem parkingSmirnovDescentSum_eq_tielessParkingDescentPolynomial
    (n : ℕ) :
    (∑ w ∈ parkingSmirnovWords n,
        (X : ℤ[X]) ^ BrandenVecchi.smirnovDescentNumber w) =
      tielessParkingDescentPolynomial n := by
  cases n with
  | zero =>
      simp [parkingSmirnovWords, BrandenVecchi.smirnovWords,
        BrandenVecchi.IsSmirnovWord, IsParkingWord,
        BrandenVecchi.smirnovDescentNumber]
  | succ n =>
      rw [tielessParkingDescentPolynomial]
      unfold descentGeneratingPolynomial
      symm
      apply Finset.sum_bij (fun w _ => parkingWordEmbed w)
      · intro w hw
        rw [mem_parkingSmirnovWords_iff]
        have hembed := parkingWordEmbed_conditions_of_mem hw
        exact ⟨BrandenVecchi.mem_smirnovWords_iff.mp hembed.2,
          hembed.1⟩
      · intro w₁ hw₁ w₂ hw₂ h
        exact parkingWordEmbed_injective h
      · intro w hw
        have hw' := mem_parkingSmirnovWords_iff.mp hw
        have hembedded : w ∈ embeddedParkingFunctions n :=
          mem_embeddedParkingFunctions_iff_isParkingWord.mpr hw'.2
        rw [embeddedParkingFunctions, Finset.mem_image] at hembedded
        obtain ⟨v, hv, hvw⟩ := hembedded
        refine ⟨v, ?_, hvw⟩
        rw [mem_tielessParkingFunctions_iff_embed, hvw]
        exact ⟨hw'.2, BrandenVecchi.mem_smirnovWords_iff.mpr hw'.1⟩
      · intro w hw
        exact (descentMonomial_parkingWordEmbed (R := ℤ) w).symm

/-- The all-one weighted polynomial is the literal integral Smirnov descent
sum. -/
theorem weightedSmirnovPolynomial_one_eq_smirnovDescentSum (n : ℕ) :
    BrandenVecchi.weightedSmirnovPolynomial
        (R := ℤ) (fun _ : Fin (n + 1) => 1) n =
      ∑ w ∈ BrandenVecchi.smirnovWords (n + 1) n,
        X ^ BrandenVecchi.smirnovDescentNumber w := by
  classical
  unfold BrandenVecchi.weightedSmirnovPolynomial
    BrandenVecchi.smirnovWordWeight
  apply Finset.sum_congr rfl
  intro w hw
  simp

/-- Integral tieless parking-to-Smirnov transfer.  The factor `n + 1` is
natural-number scalar multiplication, so no division is hidden. -/
theorem succ_nsmul_tielessParkingDescentPolynomial_eq_weightedSmirnov
    (n : ℕ) :
    (n + 1) • tielessParkingDescentPolynomial n =
      BrandenVecchi.weightedSmirnovPolynomial
        (R := ℤ) (fun _ : Fin (n + 1) => 1) n := by
  rw [weightedSmirnovPolynomial_one_eq_smirnovDescentSum,
    smirnovDescentSum_eq_succ_nsmul_parkingSmirnovDescentSum,
    parkingSmirnovDescentSum_eq_tielessParkingDescentPolynomial]

/-- The integral transfer identifies the scaled tieless parking enumerator
with the finite elementary-Toeplitz Chow polynomial. -/
theorem succ_nsmul_tielessParkingDescentPolynomial_eq_chowPolynomial
    (n : ℕ) :
    (n + 1) • tielessParkingDescentPolynomial n =
      BrandenVecchi.chowPolynomial
        (BrandenVecchi.finiteElementaryToeplitz
          (R := ℤ) (fun _ : Fin (n + 1) => 1)) n := by
  calc
    (n + 1) • tielessParkingDescentPolynomial n =
        BrandenVecchi.weightedSmirnovPolynomial
          (R := ℤ) (fun _ : Fin (n + 1) => 1) n :=
      succ_nsmul_tielessParkingDescentPolynomial_eq_weightedSmirnov n
    _ = BrandenVecchi.chowPolynomial
        (BrandenVecchi.finiteElementaryToeplitz
          (R := ℤ) (fun _ : Fin (n + 1) => 1)) n :=
      BrandenVecchi.weightedSmirnovPolynomial_eq_chowPolynomial _ _

/-- Real-coefficient form of the integral transfer. -/
theorem succ_nsmul_map_tielessParkingDescentPolynomial_eq_smirnov
    (n : ℕ) :
    (n + 1) •
        (tielessParkingDescentPolynomial n).map (Int.castRingHom ℝ) =
      BrandenVecchi.smirnovDescentPolynomial (n + 1) n := by
  have h := congrArg (fun p : ℤ[X] => p.map (Int.castRingHom ℝ))
    (succ_nsmul_tielessParkingDescentPolynomial_eq_weightedSmirnov n)
  simpa [BrandenVecchi.smirnovDescentPolynomial,
    BrandenVecchi.map_weightedSmirnovPolynomial] using h

/-- Leander's Smirnov interlacing theorem therefore gives real-rootedness of
the real-coefficient tieless parking descent polynomial. -/
theorem map_tielessParkingDescentPolynomial_splits (n : ℕ) :
    ((tielessParkingDescentPolynomial n).map
      (Int.castRingHom ℝ)).Splits := by
  let p := (tielessParkingDescentPolynomial n).map (Int.castRingHom ℝ)
  have heq : C (n + 1 : ℝ) * p =
      BrandenVecchi.smirnovDescentPolynomial (n + 1) n := by
    simpa [p, nsmul_eq_mul] using
      succ_nsmul_map_tielessParkingDescentPolynomial_eq_smirnov n
  have hscaled : (C (n + 1 : ℝ) * p).Splits := by
    rw [heq]
    exact BrandenVecchi.smirnovDescentPolynomial_splits (n + 1) n
  exact (Polynomial.splits_mul_iff_right (C_ne_zero.mpr (by positivity))
    (Polynomial.Splits.C (n + 1 : ℝ))).mp hscaled

end

end RealRooted.ParkingFunctions
