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

/-- The strict forward Aissen--Schoenberg--Whitney target. -/
abbrev forwardTarget : Prop :=
  aissenSchoenbergWhitneyForwardStatement

/-- The zero-aware forward Aissen--Schoenberg--Whitney target. -/
abbrev forwardOrZeroTarget : Prop :=
  aissenSchoenbergWhitneyForwardOrZeroStatement

/-- The splitting-only forward ASW target.  The root-location conjunct follows
from PF coefficient nonnegativity. -/
abbrev forwardSplitsTarget : Prop :=
  aissenSchoenbergWhitneyForwardSplitsStatement

/-- The forward target with PF-sequence nonnegativity used directly. -/
abbrev forwardNoNonnegTarget : Prop :=
  aissenSchoenbergWhitneyForwardNoNonnegStatement

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

/-- Challenge-facing alias: PF coefficients already rule out positive real
roots. -/
theorem rootsNonpos_of_pfCoeff {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq (fun n ↦ p.coeff n)) :
    ∀ r ∈ p.roots, r ≤ 0 :=
  roots_nonpos_of_IsPolyaFreqSeq_coeff hpf

/-- The splitting-only target implies the full forward target. -/
theorem forwardTarget_of_splitsTarget
    (h : forwardSplitsTarget) :
    forwardTarget :=
  aissenSchoenbergWhitneyForward_of_splits h

/-- The full forward target implies the splitting-only target. -/
theorem splitsTarget_of_forwardTarget
    (h : forwardTarget) :
    forwardSplitsTarget :=
  aissenSchoenbergWhitneyForwardSplits_of_forward h

/-- The full forward target is equivalent to the splitting-only target. -/
theorem forwardTarget_iff_splitsTarget :
    forwardTarget ↔ forwardSplitsTarget :=
  aissenSchoenbergWhitneyForward_iff_splits

/-- The zero-aware target implies the splitting-only target. -/
theorem splitsTarget_of_forwardOrZeroTarget
    (h : forwardOrZeroTarget) :
    forwardSplitsTarget :=
  aissenSchoenbergWhitneyForwardSplits_of_orZero h

/-- The splitting-only target implies the zero-aware target. -/
theorem forwardOrZeroTarget_of_splitsTarget
    (h : forwardSplitsTarget) :
    forwardOrZeroTarget :=
  aissenSchoenbergWhitneyForwardOrZero_of_splits h

/-- The zero-aware target is equivalent to the splitting-only target. -/
theorem forwardOrZeroTarget_iff_splitsTarget :
    forwardOrZeroTarget ↔ forwardSplitsTarget :=
  aissenSchoenbergWhitneyForwardOrZero_iff_splits

/-- The no-extra-nonnegativity target implies the splitting-only target. -/
theorem splitsTarget_of_forwardNoNonnegTarget
    (h : forwardNoNonnegTarget) :
    forwardSplitsTarget :=
  aissenSchoenbergWhitneyForwardSplits_of_noNonneg h

/-- The splitting-only target implies the no-extra-nonnegativity target. -/
theorem forwardNoNonnegTarget_of_splitsTarget
    (h : forwardSplitsTarget) :
    forwardNoNonnegTarget :=
  aissenSchoenbergWhitneyForwardNoNonneg_of_splits h

/-- The no-extra-nonnegativity target is equivalent to the splitting-only
target. -/
theorem forwardNoNonnegTarget_iff_splitsTarget :
    forwardNoNonnegTarget ↔ forwardSplitsTarget :=
  aissenSchoenbergWhitneyForwardNoNonneg_iff_splits

/-- The strict and no-extra-nonnegativity forward targets are equivalent. -/
theorem forwardTarget_iff_noNonnegTarget :
    forwardTarget ↔ forwardNoNonnegTarget :=
  aissenSchoenbergWhitneyForward_iff_noNonneg

/-- The strict and zero-aware forward targets are equivalent. -/
theorem forwardTarget_iff_orZeroTarget :
    forwardTarget ↔ forwardOrZeroTarget :=
  aissenSchoenbergWhitneyForward_iff_orZero

end AissenSchoenbergWhitney
end Challenges
end RealRooted
