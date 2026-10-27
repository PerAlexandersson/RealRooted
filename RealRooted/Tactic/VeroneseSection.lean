module

public import RealRooted.VeroneseSection

/-!
# Veronese-section tactic frontends

Thin wrappers for the fixed-section Veronese APIs in
`RealRooted.VeroneseSection`.
-/

public section

open Polynomial

namespace RealRooted

/-- Positive section moduli preserve nonnegative coefficients pointwise under the Veronese
section operation. -/
theorem hasNonnegCoeffs_veroneseSectionPolynomial_sequence
    {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hr : ∀ n : Nat, 0 < r n) :
    ∀ n : Nat, HasNonnegCoeffs (veroneseSectionPolynomial (r n) (k n) (P n)) :=
  fun n => hasNonnegCoeffs_veroneseSectionPolynomial (hr n) (hnn n)

/-- For positive moduli and section indices below their moduli, Veronese sections preserve the
Pólya-frequency property pointwise. -/
theorem isPolyaFreqSeq_veroneseSectionPolynomial_coeff_sequence
    {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hpf : ∀ n : Nat, IsPolyaFreqSeq (P n).coeff)
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat, IsPolyaFreqSeq (veroneseSectionPolynomial (r n) (k n) (P n)).coeff :=
  fun n => isPolyaFreqSeq_veroneseSectionPolynomial_coeff (hpf n) (hr n) (hk n)

/-- For positive moduli and valid section indices, the Veronese section of each
Pólya-frequency coefficient sequence is zero or splits. -/
theorem veroneseSectionPolynomial_sequence_zero_or_splits_of_pf
    {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hpf : ∀ n : Nat, IsPolyaFreqSeq (P n).coeff)
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat,
      veroneseSectionPolynomial (r n) (k n) (P n) = 0 ∨
        (veroneseSectionPolynomial (r n) (k n) (P n)).Splits := fun n =>
  splits_veroneseSectionPolynomial_of_pf (hpf n) (hr n) (hk n)

/-- For positive moduli and valid section indices, Veronese sections of splitting polynomials
with nonnegative coefficients are zero or split. -/
theorem veroneseSectionPolynomial_sequence_zero_or_splits_of_nonneg
    {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hsplits : ∀ n : Nat, (P n).Splits)
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat,
      veroneseSectionPolynomial (r n) (k n) (P n) = 0 ∨
        (veroneseSectionPolynomial (r n) (k n) (P n)).Splits := fun n =>
  splits_veroneseSectionPolynomial_of_splits_nonneg
    (hnn n) (hsplits n) (hr n) (hk n)

namespace Tactic

end Tactic
end RealRooted
