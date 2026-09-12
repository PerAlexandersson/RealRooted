import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIReverse
import RealRooted.MultiplierSequence.Sign

/-!
# Signed Type-I Pólya--Schur classification

This file packages the classical global-sign and alternating-sign conventions
around the sign-sensitive Type-I Laguerre--Pólya class.
-/

noncomputable section

namespace RealRooted

/-- A function is signed Type-I when it, its global negation, its reflection
at zero, or the negation of that reflection is Type-I Laguerre--Pólya. -/
def IsLaguerrePolyaTypeISigned (f : ℂ → ℂ) : Prop :=
  (IsLaguerrePolyaTypeI f ∨ IsLaguerrePolyaTypeI (fun z => -f z)) ∨
    (IsLaguerrePolyaTypeI (fun z => f (-z)) ∨
      IsLaguerrePolyaTypeI (fun z => -f (-z)))

/-- Full signed Pólya--Schur classification for an exponential generating
series with a positive radius of convergence. -/
theorem isMultiplierSequence_iff_isLaguerrePolyaTypeISigned_complexExpGeneratingFunction
    {gamma : ℕ → ℝ}
    (hpositive : ∃ R : NNReal, 0 < R ∧
      Summable (fun k => ‖gamma k‖ * (R : ℝ) ^ k / k.factorial)) :
    IsMultiplierSequence gamma ↔
      IsLaguerrePolyaTypeISigned (complexExpGeneratingFunction gamma) := by
  let gammaNeg := fun k => -gamma k
  let gammaAlt := fun k => (-1 : ℝ) ^ k * gamma k
  let gammaNegAlt := fun k => -((-1 : ℝ) ^ k * gamma k)
  have hpositiveNeg : ∃ R : NNReal, 0 < R ∧
      Summable (fun k => ‖gammaNeg k‖ * (R : ℝ) ^ k / k.factorial) := by
    rcases hpositive with ⟨R, hR, hsum⟩
    exact ⟨R, hR, by simpa [gammaNeg] using hsum⟩
  have hpositiveAlt : ∃ R : NNReal, 0 < R ∧
      Summable (fun k => ‖gammaAlt k‖ * (R : ℝ) ^ k / k.factorial) := by
    rcases hpositive with ⟨R, hR, hsum⟩
    exact ⟨R, hR, by simpa [gammaAlt, norm_mul] using hsum⟩
  have hpositiveNegAlt : ∃ R : NNReal, 0 < R ∧
      Summable (fun k => ‖gammaNegAlt k‖ * (R : ℝ) ^ k / k.factorial) := by
    rcases hpositiveAlt with ⟨R, hR, hsum⟩
    exact ⟨R, hR, by simpa [gammaNegAlt, gammaAlt] using hsum⟩
  have hegfNeg : complexExpGeneratingFunction gammaNeg =
      fun z => -complexExpGeneratingFunction gamma z := by
    simpa [gammaNeg] using complexExpGeneratingFunction_const_mul (-1) gamma
  have hegfAlt : complexExpGeneratingFunction gammaAlt =
      fun z => complexExpGeneratingFunction gamma (-z) := by
    simpa [gammaAlt] using complexExpGeneratingFunction_alternating gamma
  have hegfNegAlt : complexExpGeneratingFunction gammaNegAlt =
      fun z => -complexExpGeneratingFunction gamma (-z) := by
    calc
      complexExpGeneratingFunction gammaNegAlt =
          fun z => (-1 : ℂ) * complexExpGeneratingFunction gammaAlt z := by
        simpa [gammaNegAlt, gammaAlt] using
          complexExpGeneratingFunction_const_mul (-1) gammaAlt
      _ = fun z => -complexExpGeneratingFunction gamma (-z) := by
        rw [hegfAlt]
        simp
  constructor
  · intro hgamma
    unfold IsLaguerrePolyaTypeISigned
    rcases hgamma.exists_pf_sign_normalization with hpf | hpf
    · rcases hpf with hpf | hpf
      · exact Or.inl (Or.inl
          ((isPFMultiplierSequence_iff_isLaguerrePolyaTypeI_complexExpGeneratingFunction
            hpositive).mp hpf))
      · left
        right
        rw [← hegfNeg]
        exact
          (isPFMultiplierSequence_iff_isLaguerrePolyaTypeI_complexExpGeneratingFunction
            hpositiveNeg).mp hpf
    · rcases hpf with hpf | hpf
      · right
        left
        rw [← hegfAlt]
        exact
          (isPFMultiplierSequence_iff_isLaguerrePolyaTypeI_complexExpGeneratingFunction
            hpositiveAlt).mp hpf
      · right
        right
        rw [← hegfNegAlt]
        exact
          (isPFMultiplierSequence_iff_isLaguerrePolyaTypeI_complexExpGeneratingFunction
            hpositiveNegAlt).mp hpf
  · intro hsigned
    unfold IsLaguerrePolyaTypeISigned at hsigned
    rcases hsigned with (htype | htype) | htype | htype
    · have hpf :=
        (isPFMultiplierSequence_iff_isLaguerrePolyaTypeI_complexExpGeneratingFunction
          hpositive).mpr htype
      exact (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp hpf).1
    · have hpf : IsPFMultiplierSequence gammaNeg :=
        (isPFMultiplierSequence_iff_isLaguerrePolyaTypeI_complexExpGeneratingFunction
          hpositiveNeg).mpr (by rw [hegfNeg]; exact htype)
      have hmult := (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp hpf).1
      simpa [gammaNeg] using hmult.const_mul (-1)
    · have hpf : IsPFMultiplierSequence gammaAlt :=
        (isPFMultiplierSequence_iff_isLaguerrePolyaTypeI_complexExpGeneratingFunction
          hpositiveAlt).mpr (by rw [hegfAlt]; exact htype)
      have hmult := (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp hpf).1
      have halt := hmult.alternating
      have hseq : (fun k => (-1 : ℝ) ^ k * gammaAlt k) = gamma := by
        funext k
        dsimp only [gammaAlt]
        calc
          (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * gamma k) =
              (-1 : ℝ) ^ (k + k) * gamma k := by rw [pow_add, mul_assoc]
          _ = gamma k := by rw [← two_mul, pow_mul]; norm_num
      rw [hseq] at halt
      exact halt
    · have hpf : IsPFMultiplierSequence gammaNegAlt :=
        (isPFMultiplierSequence_iff_isLaguerrePolyaTypeI_complexExpGeneratingFunction
          hpositiveNegAlt).mpr (by rw [hegfNegAlt]; exact htype)
      have hmult := (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp hpf).1
      have hmultAlt : IsMultiplierSequence gammaAlt := by
        simpa [gammaNegAlt, gammaAlt] using hmult.const_mul (-1)
      have halt := hmultAlt.alternating
      have hseq : (fun k => (-1 : ℝ) ^ k * gammaAlt k) = gamma := by
        funext k
        dsimp only [gammaAlt]
        calc
          (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * gamma k) =
              (-1 : ℝ) ^ (k + k) * gamma k := by rw [pow_add, mul_assoc]
          _ = gamma k := by rw [← two_mul, pow_mul]; norm_num
      rw [hseq] at halt
      exact halt

end RealRooted
