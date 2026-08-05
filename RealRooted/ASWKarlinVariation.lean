import RealRooted.ASWKarlinMatrix
import RealRooted.ASWKarlinSineBounds
import RealRooted.ASWKarlinThreshold
import RealRooted.ASWKarlinVectors
import RealRooted.Mathlib.LinearAlgebra.Matrix.KernelSignVariation

/-!
# Variation-diminishing input for Karlin's sector proof

This file isolates the sign-variation bookkeeping used by the remaining
classical sign-regular variation-diminishing ingredient in the forward
Aissen--Schoenberg--Whitney theorem.
-/

noncomputable section

namespace RealRooted

/-- The sign-variation lower-bound property needed for the one-block Karlin
coefficient-window matrix.

This is stated as a property rather than as a consequence of arbitrary
rectangular total nonnegativity and surjectivity: that more general statement
is false. -/
def AswKarlinKernelSignVariationLowerBound
    (degree order : ℕ) (u : ℕ → ℝ) : Prop :=
  Matrix.KernelSignVariationLowerBound (aswKarlinMatrix u degree order 1) order

/-- The zero-free repeated-matrix kernel sign-variation lower-bound property.

Unlike `Matrix.KernelSignVariationLowerBound`, this only quantifies over
kernel vectors whose coordinates are all nonzero.  This zero-free restriction
is essential for the repeated Karlin matrices used in the classical
variation-diminishing route. -/
def AswKarlinRepeatedZeroFreeKernelSignVariationLowerBound
    (degree order blocks : ℕ) (u : ℕ → ℝ) : Prop :=
  ∀ {v : Fin (blocks * (degree + order - 1) + 1) → ℝ},
    (aswKarlinMatrix u degree order blocks).mulVec v = 0 →
    (∀ j, v j ≠ 0) →
    blocks * order ≤ Fin.signVariations v

/-- Specialized classical input needed for the one-block Karlin
coefficient-window matrix.

The hypotheses are exactly the checked data produced from a positive-endpoint
PF polynomial: the full Pólya-frequency property and finite support through
`degree`.  The full PF hypothesis is essential; one-block total
nonnegativity plus full row rank is too weak. -/
def AswKarlinKernelSignVariationClassicalInputStatement : Prop :=
  ∀ {u : ℕ → ℝ} {degree order : ℕ},
    0 < degree →
    0 < order →
    0 < u 0 →
    0 < u degree →
    (∀ k, degree < k → u k = 0) →
    IsPolyaFreqSeq u →
    AswKarlinKernelSignVariationLowerBound degree order u

/-- Specialized classical input for zero-free kernel vectors in the repeated
Karlin coefficient-window matrices.

This is the remaining classical variation-diminishing boundary in the phased
route.  It is deliberately weaker than the false arbitrary-kernel repeated
matrix predicate. -/
def AswKarlinRepeatedZeroFreeKernelSignVariationClassicalInputStatement :
    Prop :=
  ∀ {u : ℕ → ℝ} {degree order blocks : ℕ},
    0 < degree →
    0 < order →
    0 < blocks →
    0 < u 0 →
    0 < u degree →
    (∀ k, degree < k → u k = 0) →
    IsPolyaFreqSeq u →
    AswKarlinRepeatedZeroFreeKernelSignVariationLowerBound
      degree order blocks u

/-- Checked reduction from the specialized classical input to the PF one-block
Karlin coefficient-window kernel lower bound. -/
theorem IsPolyaFreqSeq.aswKarlinKernelSignVariationLowerBound_of_classicalInput
    {u : ℕ → ℝ} (hpf : IsPolyaFreqSeq u)
    (hclassical : AswKarlinKernelSignVariationClassicalInputStatement)
    (degree order : ℕ) (hdegree : 0 < degree) (horder : 0 < order)
    (hconst : 0 < u 0) (hlead : 0 < u degree)
    (hsupport : ∀ k, degree < k → u k = 0) :
    AswKarlinKernelSignVariationLowerBound degree order u := by
  exact hclassical hdegree horder hconst hlead hsupport hpf

/-- Remaining classical sign-regular zero-free kernel lower bound for repeated
PF coefficient windows.

This is the only non-elementary input in the current phased Karlin sector
route.  It matches the zero-free vectors produced by phase selection and avoids
the false arbitrary-kernel repeated-matrix statement. -/
theorem aswKarlinRepeatedZeroFreeKernelSignVariationClassicalInput :
    AswKarlinRepeatedZeroFreeKernelSignVariationClassicalInputStatement := by
  intro u degree order blocks hdegree horder hblocks hconst hlead hsupport hpf v
    hker hzeroFree
  -- Remaining classical step: Karlin's variation-diminishing theorem for the
  -- repeated Toeplitz coefficient-window matrix, restricted to zero-free
  -- kernel vectors.
  sorry

/-- Repeated phased-sine contradiction for nonnegative angles.

If every zero-avoiding phase satisfies the repeated Karlin lower bound, then
the angle cannot lie below Karlin's sector threshold. -/
theorem aswSectorThreshold_le_of_repeated_phasedSine_bounds_of_nonneg
    {degree order blocks : ℕ} {θ : ℝ}
    (hdegree : 0 < degree) (horder : 0 < order) (hblocks : 0 < blocks)
    (hθ0 : 0 ≤ θ)
    (hlower : ∀ {phase : ℝ},
      AswKarlinPhaseAvoidsZeros phase θ degree order blocks →
        blocks * order ≤
          Fin.signVariations
            (aswKarlinPhasedSineVector phase θ degree order blocks)) :
    aswSectorThreshold degree order ≤ θ := by
  by_contra hnot
  have hθ_lt : θ < aswSectorThreshold degree order := lt_of_not_ge hnot
  have hmargin :
      ((blocks * (degree + order - 1) : ℕ) : ℝ) * θ <
        ((blocks * order : ℕ) : ℝ) * Real.pi :=
    aswSectorThreshold_repeated_last_angle_lt_order_pi
      hdegree horder hblocks hθ_lt
  obtain ⟨phase, havoid, hphase0, hlast⟩ :=
    exists_phase_avoidsZeros_aswKarlin_with_last_lt_order_pi
      (θ := θ) (degree := degree) (order := order) (blocks := blocks) hmargin
  have hlower_phase :
      blocks * order ≤
        Fin.signVariations
          (aswKarlinPhasedSineVector phase θ degree order blocks) :=
    hlower havoid
  have hupper :
      Fin.signVariations
          (aswKarlinPhasedSineVector phase θ degree order blocks) <
        blocks * order :=
    signVariations_aswKarlinPhasedSineVector_lt_of_last_le_order_pi
      hblocks horder hphase0 hθ0 hlast.le
  exact (not_lt_of_ge hlower_phase) hupper

/-- The final sector inequality follows once the two sign-variation bounds are
available: a lower bound from the full-row-rank TN kernel theorem and an upper
bound for the sampled sine vector inside the forbidden sector. -/
theorem aswSectorThreshold_le_of_signVariation_bounds
    {degree order : ℕ} {θ : ℝ}
    {v : Fin (1 * (degree + order - 1) + 1) → ℝ}
    (hsign : Fin.signVariations v =
      Fin.signVariations (aswKarlinSineVector θ degree order 1))
    (hkerLower : order ≤ Fin.signVariations v)
    (hsineUpper : θ < aswSectorThreshold degree order →
      Fin.signVariations (aswKarlinSineVector θ degree order 1) < order) :
    aswSectorThreshold degree order ≤ θ := by
  by_contra hnot
  have hlt : θ < aswSectorThreshold degree order := lt_of_not_ge hnot
  have hlower_sine :
      order ≤ Fin.signVariations (aswKarlinSineVector θ degree order 1) := by
    simpa [hsign] using hkerLower
  exact (not_lt_of_ge hlower_sine) (hsineUpper hlt)

/-- Nonnegative-angle form of the sign-variation contradiction used in
Karlin's sector proof. -/
theorem aswSectorThreshold_le_of_karlin_sine_kernel_of_nonneg
    {degree order : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    {v : Fin (1 * (degree + order - 1) + 1) → ℝ}
    (hsign : Fin.signVariations v =
      Fin.signVariations (aswKarlinSineVector θ degree order 1))
    (hkerLower : order ≤ Fin.signVariations v)
    (hsineUpper : ∀ {φ : ℝ}, 0 ≤ φ →
      φ < aswSectorThreshold degree order →
      Fin.signVariations (aswKarlinSineVector φ degree order 1) < order) :
    aswSectorThreshold degree order ≤ θ := by
  exact aswSectorThreshold_le_of_signVariation_bounds hsign hkerLower
    (hsineUpper hθ)

/-- Karlin's variation-diminishing kernel criterion specialized to the
one-block sine vector.  The sign-variation count is invariant under negating
the sampled sine vector, so the hard leaf is the nonnegative-angle form. -/
theorem aswSectorThreshold_le_abs_arg_of_karlin_sine_kernel
    {degree order : ℕ} {θ : ℝ}
    {v : Fin (1 * (degree + order - 1) + 1) → ℝ}
    (hsign : Fin.signVariations v =
      Fin.signVariations (aswKarlinSineVector θ degree order 1))
    (hkerLower : order ≤ Fin.signVariations v)
    (hsineUpper : ∀ {φ : ℝ}, 0 ≤ φ →
      φ < aswSectorThreshold degree order →
      Fin.signVariations (aswKarlinSineVector φ degree order 1) < order) :
    aswSectorThreshold degree order ≤ |θ| := by
  by_cases hθ : 0 ≤ θ
  · rw [abs_of_nonneg hθ]
    exact aswSectorThreshold_le_of_karlin_sine_kernel_of_nonneg hθ hsign
      hkerLower hsineUpper
  · have hθneg : 0 ≤ -θ := by linarith
    have hsign_neg :
        Fin.signVariations v =
          Fin.signVariations (aswKarlinSineVector (-θ) degree order 1) :=
      hsign.trans (signVariations_aswKarlinSineVector_neg θ degree order 1).symm
    rw [abs_of_neg (lt_of_not_ge hθ)]
    exact aswSectorThreshold_le_of_karlin_sine_kernel_of_nonneg hθneg hsign_neg
      hkerLower hsineUpper

/-- Karlin's sector contradiction assembled directly from the one-block
coefficient-window matrix kernel hypotheses. -/
theorem aswSectorThreshold_le_abs_arg_of_karlin_matrix_kernel
    {degree order : ℕ} {u : ℕ → ℝ} {θ : ℝ}
    {v : Fin (1 * (degree + order - 1) + 1) → ℝ}
    (hkernelLower : AswKarlinKernelSignVariationLowerBound degree order u)
    (hker : (aswKarlinMatrix u degree order 1).mulVec v = 0)
    (hvec_ne : v ≠ 0)
    (hsign : Fin.signVariations v =
      Fin.signVariations (aswKarlinSineVector θ degree order 1))
    (hsineUpper : ∀ {φ : ℝ}, 0 ≤ φ →
      φ < aswSectorThreshold degree order →
      Fin.signVariations (aswKarlinSineVector φ degree order 1) < order) :
    aswSectorThreshold degree order ≤ |θ| := by
  have hkerLower : order ≤ Fin.signVariations v :=
    hkernelLower.apply hker hvec_ne
  exact aswSectorThreshold_le_abs_arg_of_karlin_sine_kernel hsign hkerLower
    hsineUpper

/-- Karlin's sector contradiction assembled from the one-block matrix kernel
hypotheses and the proved threshold sine bound. -/
theorem aswSectorThreshold_le_abs_arg_of_karlin_matrix_kernel_of_threshold
    {degree order : ℕ} {u : ℕ → ℝ} {θ : ℝ}
    {v : Fin (1 * (degree + order - 1) + 1) → ℝ}
    (hdegree : 0 < degree) (horder : 0 < order)
    (hkernelLower : AswKarlinKernelSignVariationLowerBound degree order u)
    (hker : (aswKarlinMatrix u degree order 1).mulVec v = 0)
    (hvec_ne : v ≠ 0)
    (hsign : Fin.signVariations v =
      Fin.signVariations (aswKarlinSineVector θ degree order 1)) :
    aswSectorThreshold degree order ≤ |θ| := by
  apply aswSectorThreshold_le_abs_arg_of_karlin_matrix_kernel
    hkernelLower hker hvec_ne hsign
  intro φ hφ0 hφ
  exact signVariations_aswKarlinSineVector_lt_of_lt_threshold
    hdegree horder hφ0 hφ

end RealRooted
