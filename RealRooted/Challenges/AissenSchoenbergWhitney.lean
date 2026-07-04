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
