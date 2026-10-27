module

public import RealRooted.MagnitudeDominated

/-!
# Magnitude-dominated lag tactic frontends

Thin wrappers for magnitude-dominated Ma-Wang / generalized Liu-Wang
interlacing certificates.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- Pointwise successor-degree form of magnitude-dominated strict interlacing, assuming the
interlacing, leading-coefficient, degree, and root-sign hypotheses at every index. -/
theorem magnitude_dominated_sequence_succ
    {F G1 G2 A B1 B2 : Nat → ℝ[X]}
    (hinter : ∀ i : Nat, Interlaces (G1 i) (F i))
    (hinterpos : ∀ i : Nat, HasPosLeadingCoeff (G1 i))
    (htargetpos : ∀ i : Nat,
      HasPosLeadingCoeff (A i * F i + B1 i * G1 i + B2 i * G2 i))
    (hdeg : ∀ i : Nat,
      (A i * F i + B1 i * G1 i + B2 i * G2 i).natDegree =
        (F i).natDegree + 1)
    (hcert : ∀ i : Nat, ∀ r, (F i).IsRoot r →
      (B1 i).eval r * ((G1 i).eval r) ^ 2 +
        (B2 i).eval r * ((G2 i).eval r * (G1 i).eval r) < 0) :
    ∀ i : Nat, StrictInterl (F i) (A i * F i + B1 i * G1 i + B2 i * G2 i) := fun i =>
  RealRooted.strictInterl_of_magnitude_dominated_succ
    (hinter i) (hinterpos i) (htargetpos i) (hdeg i) (hcert i)

/-- Pointwise equal-degree form of magnitude-dominated strict interlacing, assuming the
interlacing, leading-coefficient, degree, and root-sign hypotheses at every index. -/
theorem magnitude_dominated_sequence_same
    {F G1 G2 A B1 B2 : Nat → ℝ[X]}
    (hinter : ∀ i : Nat, Interlaces (G1 i) (F i))
    (hinterpos : ∀ i : Nat, HasPosLeadingCoeff (G1 i))
    (htargetpos : ∀ i : Nat,
      HasPosLeadingCoeff (A i * F i + B1 i * G1 i + B2 i * G2 i))
    (hdeg : ∀ i : Nat,
      (A i * F i + B1 i * G1 i + B2 i * G2 i).natDegree =
        (F i).natDegree)
    (hcert : ∀ i : Nat, ∀ r, (F i).IsRoot r →
      (B1 i).eval r * ((G1 i).eval r) ^ 2 +
        (B2 i).eval r * ((G2 i).eval r * (G1 i).eval r) < 0) :
    ∀ i : Nat, StrictInterl (F i) (A i * F i + B1 i * G1 i + B2 i * G2 i) := fun i =>
  RealRooted.strictInterl_of_magnitude_dominated_same
    (hinter i) (hinterpos i) (htargetpos i) (hdeg i) (hcert i)

/-- Pointwise magnitude-dominated strict interlacing when the target degree lies between the
base degree and its successor and the root-sign inequality holds at every index. -/
theorem magnitude_dominated_sequence
    {F G1 G2 A B1 B2 : Nat → ℝ[X]}
    (hinter : ∀ i : Nat, Interlaces (G1 i) (F i))
    (hinterpos : ∀ i : Nat, HasPosLeadingCoeff (G1 i))
    (htargetpos : ∀ i : Nat,
      HasPosLeadingCoeff (A i * F i + B1 i * G1 i + B2 i * G2 i))
    (hdeglo : ∀ i : Nat,
      (F i).natDegree ≤ (A i * F i + B1 i * G1 i + B2 i * G2 i).natDegree)
    (hdeghi : ∀ i : Nat,
      (A i * F i + B1 i * G1 i + B2 i * G2 i).natDegree ≤
        (F i).natDegree + 1)
    (hcert : ∀ i : Nat, ∀ r, (F i).IsRoot r →
      (B1 i).eval r * ((G1 i).eval r) ^ 2 +
        (B2 i).eval r * ((G2 i).eval r * (G1 i).eval r) < 0) :
    ∀ i : Nat, StrictInterl (F i) (A i * F i + B1 i * G1 i + B2 i * G2 i) := fun i =>
  RealRooted.strictInterl_of_magnitude_dominated
    (hinter i) (hinterpos i) (htargetpos i) (hdeglo i) (hdeghi i) (hcert i)

/-- A pointwise negative head term remains negative after adding a second term whose absolute
value is strictly smaller. -/
theorem magnitude_sequence_cert_of_abs_dominated
    {B1 G1 B2 G2 : Nat → ℝ[X]}
    (hhead : ∀ i : Nat, ∀ r,
      (B1 i).eval r * ((G1 i).eval r) ^ 2 < 0)
    (hdom : ∀ i : Nat, ∀ r,
      |(B2 i).eval r * ((G2 i).eval r * (G1 i).eval r)| <
        |(B1 i).eval r * ((G1 i).eval r) ^ 2|) :
    ∀ i : Nat, ∀ r,
      (B1 i).eval r * ((G1 i).eval r) ^ 2 +
        (B2 i).eval r * ((G2 i).eval r * (G1 i).eval r) < 0 := fun i r =>
  RealRooted.magnitude_cert_of_abs_dominated (hhead i r) (hdom i r)

end Tactic
end RealRooted
