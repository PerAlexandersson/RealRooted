module

public import RealRooted.SymmetricDecomposition
import RealRooted.SymmetricDecomposition.FPolynomialInterlacing
import RealRooted.SymmetricDecomposition.Theorem26
public import RealRooted.SymmetricDecomposition.FPolynomial
public import RealRooted.ObreschkoffContinuity

/-!
# Symmetric-decomposition tactic frontends

Thin wrappers for the Branden--Solus `fPolynomial` transport API in
`RealRooted.SymmetricDecomposition`.
-/

public section

open Polynomial

namespace RealRooted

/-- Certificate-shaped frontend for real-rootedness preservation under `fPolynomial`. -/
theorem isRealRooted_fPolynomial_of_isRealRooted_cert
    {d : Nat} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d)
    (hp : p ≠ 0 ∧ p.Splits)
    (hpnn : HasNonnegCoeffs p) :
    (fPolynomial d p) ≠ 0 ∧ (fPolynomial d p).Splits :=
  isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hpdeg hp.1 hp.2 hpnn

/-- Certificate-shaped frontend for pulling real-rootedness back through `fPolynomial`. -/
theorem isRealRooted_of_fPolynomial_isRealRooted_cert
    {d : Nat} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d)
    (hfp : (fPolynomial d p) ≠ 0 ∧ (fPolynomial d p).Splits)
    (hpnn : HasNonnegCoeffs p) :
    p ≠ 0 ∧ p.Splits :=
  isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs hpdeg hfp.1 hfp.2 hpnn

/-- Forward `StrictInterl` transport through `fPolynomial` in any ambient degree. -/
theorem strictInterl_fPolynomial_of_strictInterl
    {d : Nat} {u v : ℝ[X]}
    (hud : u.natDegree ≤ d)
    (hvd : v.natDegree ≤ d)
    (hu_nonneg : HasNonnegCoeffs u)
    (hv_nonneg : HasNonnegCoeffs v)
    (h : StrictInterl u v) :
    StrictInterl (fPolynomial d u) (fPolynomial d v) :=
  (strictInterlFPolynomialTransport hud hvd hu_nonneg hv_nonneg).mpr h

/-- Backward `StrictInterl` transport through `fPolynomial` in any ambient degree. -/
theorem strictInterl_of_strictInterl_fPolynomial
    {d : Nat} {u v : ℝ[X]}
    (hud : u.natDegree ≤ d)
    (hvd : v.natDegree ≤ d)
    (hu_nonneg : HasNonnegCoeffs u)
    (hv_nonneg : HasNonnegCoeffs v)
    (h : StrictInterl (fPolynomial d u) (fPolynomial d v)) :
    StrictInterl u v :=
  (strictInterlFPolynomialTransport hud hvd hu_nonneg hv_nonneg).mp h

/-- Pointwise forward transport of nonzero splitting polynomials with nonnegative coefficients
through `fPolynomial`, under the stated ambient-degree bounds. -/
theorem isRealRooted_fPolynomial_sequence_of_isRealRooted_cert
    {d : Nat → Nat} {P : Nat → ℝ[X]}
    (hdeg : ∀ i : Nat, (P i).natDegree ≤ d i)
    (hrr : ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits)
    (hnn : ∀ i : Nat, HasNonnegCoeffs (P i)) :
    ∀ i : Nat, fPolynomial (d i) (P i) ≠ 0 ∧
      (fPolynomial (d i) (P i)).Splits := fun i =>
  isRealRooted_fPolynomial_of_isRealRooted_cert (hdeg i) (hrr i) (hnn i)

/-- Pointwise reverse transport of nonzero splitting polynomials with nonnegative coefficients
through `fPolynomial`, under the stated ambient-degree bounds. -/
theorem isRealRooted_of_fPolynomial_sequence_isRealRooted_cert
    {d : Nat → Nat} {P : Nat → ℝ[X]}
    (hdeg : ∀ i : Nat, (P i).natDegree ≤ d i)
    (hfPrr : ∀ i : Nat, fPolynomial (d i) (P i) ≠ 0 ∧
      (fPolynomial (d i) (P i)).Splits)
    (hnn : ∀ i : Nat, HasNonnegCoeffs (P i)) :
    ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits := fun i =>
  isRealRooted_of_fPolynomial_isRealRooted_cert (hdeg i) (hfPrr i) (hnn i)

/-- Pointwise forward transport of strict interlacing through `fPolynomial`, assuming
nonnegative coefficients and the stated ambient-degree bounds for both sequences. -/
theorem strictInterl_fPolynomial_sequence_of_strictInterl
    {d : Nat → Nat} {U V : Nat → ℝ[X]}
    (hud : ∀ i : Nat, (U i).natDegree ≤ d i)
    (hvd : ∀ i : Nat, (V i).natDegree ≤ d i)
    (hu_nonneg : ∀ i : Nat, HasNonnegCoeffs (U i))
    (hv_nonneg : ∀ i : Nat, HasNonnegCoeffs (V i))
    (hstrictInterl : ∀ i : Nat, StrictInterl (U i) (V i)) :
    ∀ i : Nat, StrictInterl (fPolynomial (d i) (U i)) (fPolynomial (d i) (V i)) :=
  fun i => strictInterl_fPolynomial_of_strictInterl (hud i) (hvd i)
    (hu_nonneg i) (hv_nonneg i) (hstrictInterl i)

/-- Pointwise reverse transport of strict interlacing through `fPolynomial`, assuming
nonnegative coefficients and the stated ambient-degree bounds for both sequences. -/
theorem strictInterl_of_strictInterl_fPolynomial_sequence
    {d : Nat → Nat} {U V : Nat → ℝ[X]}
    (hud : ∀ i : Nat, (U i).natDegree ≤ d i)
    (hvd : ∀ i : Nat, (V i).natDegree ≤ d i)
    (hu_nonneg : ∀ i : Nat, HasNonnegCoeffs (U i))
    (hv_nonneg : ∀ i : Nat, HasNonnegCoeffs (V i))
    (hstrictInterl : ∀ i : Nat,
      StrictInterl (fPolynomial (d i) (U i)) (fPolynomial (d i) (V i))) :
    ∀ i : Nat, StrictInterl (U i) (V i) := fun i =>
  strictInterl_of_strictInterl_fPolynomial (hud i) (hvd i)
    (hu_nonneg i) (hv_nonneg i) (hstrictInterl i)

/-- Pointwise positive-combination real-rootedness after `fPolynomial`, assuming strict
interlacing, nonnegative coefficients, and the stated ambient-degree bounds. -/
theorem posComboRealRooted_fPolynomial_sequence_of_strictInterl
    {d : Nat → Nat} {U V : Nat → ℝ[X]}
    (hstrictInterl : ∀ i : Nat, StrictInterl (U i) (V i))
    (hud : ∀ i : Nat, (U i).natDegree ≤ d i)
    (hvd : ∀ i : Nat, (V i).natDegree ≤ d i)
    (hu_nonneg : ∀ i : Nat, HasNonnegCoeffs (U i))
    (hv_nonneg : ∀ i : Nat, HasNonnegCoeffs (V i)) :
    ∀ i : Nat, PosComboRealRooted (fPolynomial (d i) (U i))
      (fPolynomial (d i) (V i)) := fun i =>
  posComboRealRooted_fPolynomial_of_strictInterl (hstrictInterl i) (hud i) (hvd i)
    (hu_nonneg i) (hv_nonneg i)

namespace Tactic

end Tactic
end RealRooted
namespace RealRooted

end RealRooted
