import RealRooted.Tactic.GammaRealRoots
import RealRooted.Tactic.VeroneseSection

/-!
# OEIS gamma and Veronese router regression examples

Gamma-real-rootedness and Veronese-section certificate routing tests.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic


/-- Gamma-transform row-family real-rootedness exposed through the OEIS facade. -/
example {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, (Γ n).natDegree ≤ d n / 2)
    (hne : ∀ n : Nat, Γ n ≠ 0)
    (hsplits : ∀ n : Nat, (Γ n).Splits)
    (hnn : ∀ n : Nat, HasNonnegCoeffs (Γ n)) :
    ∀ n : Nat, gammaTransform (d n) (Γ n) ≠ 0 ∧
      (gammaTransform (d n) (Γ n)).Splits := by
  rr_gamma_transform_sequence_realrooted_nonneg using
    gamma_degree := hdeg,
    gamma_nonzero := hne,
    gamma_splits := hsplits,
    gamma_nonneg := hnn

/-- Gamma row-family bridge exposed through the OEIS facade. -/
example {d : Nat → Nat} {P Γ : Nat → ℝ[X]}
    (hγdeg : ∀ n : Nat, (Γ n).natDegree ≤ d n / 2)
    (hpdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hsym : ∀ n : Nat, IdTransform (d n) (P n) = P n)
    (hexp : ∀ n : Nat, IsGammaExpansion (d n) (P n) (Γ n)) :
    ∀ n : Nat,
      (((Γ n ≠ 0 ∧ (Γ n).Splits) ∧ HasRootsNonpos (Γ n)) ↔
        ((P n ≠ 0 ∧ (P n).Splits) ∧ HasRootsNonpos (P n))) := by
  rr_gamma_sequence_realrooted_iff using
    gamma_degree := hγdeg,
    polynomial_degree := hpdeg,
    symmetric := hsym,
    expansion := hexp

/-- Veronese-section row-family PF exit exposed through the OEIS facade. -/
example {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hpf : ∀ n : Nat, IsPolyaFreqSeq (P n).coeff)
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat,
      IsPolyaFreqSeq (veroneseSectionPolynomial (r n) (k n) (P n)).coeff := by
  rr_veronese_section_sequence_pf_coeff using
    pf_coeff := hpf,
    r_pos := hr,
    k_lt_r := hk

/-- Veronese pair-section row-family `Prec` exit exposed through the OEIS facade. -/
example {r i j : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (hij : ∀ n : Nat, i n < j n)
    (hj : ∀ n : Nat, j n < 2 * r n) :
    ∀ n : Nat, Prec
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (i n))
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (j n)) := by
  rr_veronese_pair_sequence_prec using
    prec_to_full := hPrecToFull,
    full_to_prec := hFullToPrec,
    prec := hpq,
    r_pos := hr,
    index_lt := hij,
    right_lt_bound := hj


end Tactic
end RealRooted
