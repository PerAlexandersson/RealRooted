import RealRooted.AissenSchoenbergWhitney

/-!
# Aissen--Schoenberg--Whitney challenge entry point

This module exposes the proved reverse theorem and the remaining forward ASW
interfaces without requiring a contributor to navigate the full Toeplitz API.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace Challenges
namespace AissenSchoenbergWhitney

/-- Challenge-facing alias for the proved reverse ASW theorem. -/
theorem reverseTheorem {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p)
    (hsplits : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    IsPolyaFreqSeq (fun n ↦ p.coeff n) :=
  aissenSchoenbergWhitney_reverse hpnn hsplits hroots

/-- Challenge-facing alias for the PF-limit closure used in the current #42
endpoint route. -/
theorem pfSeq_of_forall_pos_add_C_mul_splits {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p)
    (hqnn : HasNonnegCoeffs q)
    (hfamily : ∀ {μ : ℝ}, 0 < μ → (p + C μ * q).Splits) :
    IsPolyaFreqSeq (fun n ↦ p.coeff n) :=
  IsPolyaFreqSeq.of_forall_pos_add_C_mul_splits hpnn hqnn hfamily

/-- Challenge-facing low-degree forward ASW splitting theorem. -/
theorem splits_of_pfCoeff_of_natDegree_le_two {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq (fun n ↦ p.coeff n))
    (hdeg : p.natDegree ≤ 2) :
    p.Splits :=
  splits_of_isPolyaFreqSeq_coeff_of_natDegree_le_two hpf hdeg

/-- Challenge-facing alias: PF coefficients already rule out positive real
roots. -/
theorem rootsNonpos_of_pfCoeff {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq (fun n ↦ p.coeff n)) :
    ∀ r ∈ p.roots, r ≤ 0 :=
  roots_nonpos_of_IsPolyaFreqSeq_coeff hpf

/-- The splitting-only target implies the full forward target. -/
theorem forwardTarget_of_splitsTarget :
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits) →
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0) :=
  aissenSchoenbergWhitneyForward_of_splits

/-- The full forward target implies the splitting-only target. -/
theorem splitsTarget_of_forwardTarget :
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0) →
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits) :=
  aissenSchoenbergWhitneyForwardSplits_of_forward

/-- The full forward target is equivalent to the splitting-only target. -/
theorem forwardTarget_iff_splitsTarget :
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0) ↔
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits) :=
  aissenSchoenbergWhitneyForward_iff_splits

/-- The zero-aware target implies the splitting-only target. -/
theorem splitsTarget_of_forwardOrZeroTarget :
    (∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) →
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits) :=
  aissenSchoenbergWhitneyForwardSplits_of_orZero

/-- The splitting-only target implies the zero-aware target. -/
theorem forwardOrZeroTarget_of_splitsTarget :
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits) →
    (∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) :=
  aissenSchoenbergWhitneyForwardOrZero_of_splits

/-- The zero-aware target is equivalent to the splitting-only target. -/
theorem forwardOrZeroTarget_iff_splitsTarget :
    (∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) ↔
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits) :=
  aissenSchoenbergWhitneyForwardOrZero_iff_splits

/-- The no-extra-nonnegativity target implies the splitting-only target. -/
theorem splitsTarget_of_forwardNoNonnegTarget :
    (∀ {p : ℝ[X]}, p ≠ 0 → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p ≠ 0 ∧ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) →
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits) :=
  aissenSchoenbergWhitneyForwardSplits_of_noNonneg

/-- The splitting-only target implies the no-extra-nonnegativity target. -/
theorem forwardNoNonnegTarget_of_splitsTarget :
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits) →
    (∀ {p : ℝ[X]}, p ≠ 0 → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p ≠ 0 ∧ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) :=
  aissenSchoenbergWhitneyForwardNoNonneg_of_splits

/-- The no-extra-nonnegativity target is equivalent to the splitting-only
target. -/
theorem forwardNoNonnegTarget_iff_splitsTarget :
    (∀ {p : ℝ[X]}, p ≠ 0 → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p ≠ 0 ∧ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) ↔
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits) :=
  aissenSchoenbergWhitneyForwardNoNonneg_iff_splits

/-- The strict and no-extra-nonnegativity forward targets are equivalent. -/
theorem forwardTarget_iff_noNonnegTarget :
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0) ↔
    (∀ {p : ℝ[X]}, p ≠ 0 → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p ≠ 0 ∧ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) :=
  aissenSchoenbergWhitneyForward_iff_noNonneg

/-- The strict and zero-aware forward targets are equivalent. -/
theorem forwardTarget_iff_orZeroTarget :
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0) ↔
    (∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) :=
  aissenSchoenbergWhitneyForward_iff_orZero

end AissenSchoenbergWhitney
end Challenges
end RealRooted
