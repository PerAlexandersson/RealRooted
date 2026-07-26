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

/-- Classical sign-regular kernel lower bound for a PF one-block Karlin
coefficient-window matrix.

This is the only remaining non-elementary input in the current Karlin sector
proof.  It should eventually be proved from the specialized sign-regular
variation-diminishing theorem for a full-row-rank totally nonnegative Toeplitz
window matrix. -/
theorem IsPolyaFreqSeq.aswKarlinKernelSignVariationLowerBound
    {u : ℕ → ℝ} (hpf : IsPolyaFreqSeq u) (degree order : ℕ)
    (hdegree : 0 < degree) (horder : 0 < order) (hconst : 0 < u 0)
    (hlead : 0 < u degree) (hsupport : ∀ k, degree < k → u k = 0) :
    AswKarlinKernelSignVariationLowerBound degree order u := by
  intro v hker hvec_ne
  have htn :
      (aswKarlinMatrix u degree order 1).IsTotallyNonnegRect :=
    hpf.aswKarlinMatrix_isTotallyNonnegRect degree order 1
  have hsurj :
      Function.Surjective (aswKarlinMatrix u degree order 1).mulVec :=
    aswKarlinMatrix_mulVec_surjective (u := u) degree order 1
      hdegree horder hconst
  -- Remaining classical step: use the PF-derived `htn`, `hsurj`, the support
  -- data `hlead`/`hsupport`, `hker`, and `hvec_ne` to prove the kernel
  -- sign-variation lower bound.
  sorry

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
