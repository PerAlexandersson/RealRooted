module

public import RealRooted.IteratedDerivativeShift

/-!
# Iterated derivative-shift family lemmas

Pointwise lifts of `tDeriv` and `iterateTDeriv` preservation facts to families
indexed by natural numbers.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- Pointwise derivative shifts preserve positive leading coefficients. -/
theorem tDeriv_sequence_pos_lc {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasPosLeadingCoeff (P i)) :
    ∀ i : Nat, HasPosLeadingCoeff (tDeriv (eps i) (P i)) := fun i =>
  RealRooted.HasPosLeadingCoeff.tDeriv (hP i)

/-- Pointwise derivative shifts preserve nonzeroness. -/
theorem tDeriv_sequence_ne_zero {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, P i ≠ 0) :
    ∀ i : Nat, tDeriv (eps i) (P i) ≠ 0 := fun i =>
  RealRooted.tDeriv_ne_zero (hP i)

/-- Positive pointwise derivative shifts preserve splitness. -/
theorem tDeriv_sequence_splits {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (heps : ∀ i : Nat, 0 < eps i)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, (tDeriv (eps i) (P i)).Splits := fun i =>
  RealRooted.splits_tDeriv (heps i) (hP i)

/-- A positive pointwise derivative shift of a nonzero split polynomial
strictly interlaces it on the right. -/
theorem tDeriv_sequence_strictInterl {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (heps : ∀ i : Nat, 0 < eps i)
    (hP0 : ∀ i : Nat, P i ≠ 0)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, StrictInterl (P i) (tDeriv (eps i) (P i)) := fun i =>
  RealRooted.strictInterl_tDeriv (heps i) (hP0 i) (hP i)

/-- Pointwise iterated derivative shifts preserve nonzeroness. -/
theorem iterateTDeriv_sequence_ne_zero
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} (K : Nat → ℕ)
    (hP : ∀ i : Nat, P i ≠ 0) :
    ∀ i : Nat, iterateTDeriv (eps i) (K i) (P i) ≠ 0 := fun i =>
  RealRooted.iterateTDeriv_ne_zero (hP i)

/-- Positive pointwise iterated derivative shifts preserve splitness. -/
theorem iterateTDeriv_sequence_splits
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} (K : Nat → ℕ)
    (heps : ∀ i : Nat, 0 < eps i)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, (iterateTDeriv (eps i) (K i) (P i)).Splits := fun i =>
  RealRooted.splits_iterateTDeriv (heps i) (hP i)

/-- Consecutive positive pointwise derivative-shift iterates of a nonzero split
polynomial are strictly interlacing. -/
theorem iterateTDeriv_sequence_strictInterl_succ
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} (K : Nat → ℕ)
    (heps : ∀ i : Nat, 0 < eps i)
    (hP0 : ∀ i : Nat, P i ≠ 0)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat,
      StrictInterl (iterateTDeriv (eps i) (K i) (P i))
        (iterateTDeriv (eps i) (K i + 1) (P i)) := fun i =>
  RealRooted.strictInterl_iterateTDeriv_succ (heps i) (hP0 i) (hP i)

/-- Pointwise iterated derivative shifts preserve degree. -/
theorem iterateTDeriv_sequence_natDegree
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat, (iterateTDeriv (eps i) (K i) (P i)).natDegree = (P i).natDegree :=
  fun i => RealRooted.natDegree_iterateTDeriv (eps i) (P i) (K i)

/-- Pointwise iterated derivative shifts preserve leading coefficients. -/
theorem iterateTDeriv_sequence_leadingCoeff
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat,
      (iterateTDeriv (eps i) (K i) (P i)).leadingCoeff = (P i).leadingCoeff :=
  fun i => RealRooted.leadingCoeff_iterateTDeriv (eps i) (P i) (K i)

/-- Pointwise iterated derivative shifts preserve positive leading
coefficients. -/
theorem iterateTDeriv_sequence_pos_lc
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} (K : Nat → ℕ)
    (hP : ∀ i : Nat, HasPosLeadingCoeff (P i)) :
    ∀ i : Nat, HasPosLeadingCoeff (iterateTDeriv (eps i) (K i) (P i)) := fun i =>
  RealRooted.hasPosLeadingCoeff_iterateTDeriv.mpr (hP i)

/-- Pointwise iterated derivative shifts preserve monicity. -/
theorem iterateTDeriv_sequence_monic
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} (K : Nat → ℕ)
    (hP : ∀ i : Nat, (P i).Monic) :
    ∀ i : Nat, (iterateTDeriv (eps i) (K i) (P i)).Monic := fun i =>
  RealRooted.monic_iterateTDeriv (hP i)

/-- Pointwise derivative shifts are additive. -/
theorem tDeriv_sequence_add {eps : Nat → ℝ} {P Q : Nat → ℝ[X]} :
    ∀ i : Nat,
      tDeriv (eps i) (P i + Q i) =
        tDeriv (eps i) (P i) + tDeriv (eps i) (Q i) := fun i =>
  RealRooted.tDeriv_add (eps i) (P i) (Q i)

/-- Pointwise derivative shifts commute with scalar multiplication. -/
theorem tDeriv_sequence_C_mul
    {eps c : Nat → ℝ} {P : Nat → ℝ[X]} :
    ∀ i : Nat,
      tDeriv (eps i) (C (c i) * P i) =
        C (c i) * tDeriv (eps i) (P i) := fun i =>
  RealRooted.tDeriv_C_mul (eps i) (c i) (P i)

/-- Pointwise iterated derivative shifts are additive. -/
theorem iterateTDeriv_sequence_add
    {eps : Nat → ℝ} {P Q : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat,
      iterateTDeriv (eps i) (K i) (P i + Q i) =
        iterateTDeriv (eps i) (K i) (P i) +
          iterateTDeriv (eps i) (K i) (Q i) := fun i =>
  RealRooted.iterateTDeriv_add (eps i) (K i) (P i) (Q i)

/-- Pointwise iterated derivative shifts commute with scalar multiplication. -/
theorem iterateTDeriv_sequence_C_mul
    {eps c : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat,
      iterateTDeriv (eps i) (K i) (C (c i) * P i) =
        C (c i) * iterateTDeriv (eps i) (K i) (P i) := fun i =>
  RealRooted.iterateTDeriv_C_mul (eps i) (c i) (K i) (P i)

/-- Pointwise derivative shifts commute with differentiation. -/
theorem derivative_tDeriv_sequence {eps : Nat → ℝ} {P : Nat → ℝ[X]} :
    ∀ i : Nat,
      (tDeriv (eps i) (P i)).derivative =
        tDeriv (eps i) (P i).derivative := fun i =>
  RealRooted.derivative_tDeriv (eps i) (P i)

/-- Pointwise derivative shifts commute with iterated differentiation. -/
theorem iterate_derivative_tDeriv_sequence
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat,
      (Polynomial.derivative^[K i]) (tDeriv (eps i) (P i)) =
        tDeriv (eps i) ((Polynomial.derivative^[K i]) (P i)) := fun i =>
  RealRooted.iterate_derivative_tDeriv (eps i) (K i) (P i)

/-- Pointwise iterated derivative shifts commute with iterated
differentiation. -/
theorem iterate_derivative_iterateTDeriv_sequence
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K L : Nat → ℕ} :
    ∀ i : Nat,
      (Polynomial.derivative^[K i]) (iterateTDeriv (eps i) (L i) (P i)) =
        iterateTDeriv (eps i) (L i) ((Polynomial.derivative^[K i]) (P i)) :=
  fun i =>
    RealRooted.iterate_derivative_iterateTDeriv (eps i) (L i) (K i) (P i)

end Tactic
end RealRooted

