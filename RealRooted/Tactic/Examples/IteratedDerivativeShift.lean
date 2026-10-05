import RealRooted.Tactic.IteratedDerivativeShift

open Polynomial

namespace RealRooted
namespace Tactic

example {eps : ℝ} {p : ℝ[X]} (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (tDeriv eps p) := by
  rr_TDeriv_pos_lc using pos_lc := hp

example {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasPosLeadingCoeff (P i)) :
    ∀ i : Nat, HasPosLeadingCoeff (tDeriv (eps i) (P i)) := by
  rr_TDeriv_sequence_pos_lc using pos_lc := hP

example {eps : ℝ} {p : ℝ[X]} (hp0 : p ≠ 0) :
    tDeriv eps p ≠ 0 := by
  rr_TDeriv_ne_zero using nonzero := hp0

example {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (hP0 : ∀ i : Nat, P i ≠ 0) :
    ∀ i : Nat, tDeriv (eps i) (P i) ≠ 0 := by
  rr_TDeriv_sequence_ne_zero using nonzero := hP0

example {eps : ℝ} {p : ℝ[X]} (heps : 0 < eps) (hp : p.Splits) :
    (tDeriv eps p).Splits := by
  rr_TDeriv_splits using eps_pos := heps, splits := hp

example {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (heps : ∀ i : Nat, 0 < eps i)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, (tDeriv (eps i) (P i)).Splits := by
  rr_TDeriv_sequence_splits using eps_pos := heps, splits := hP

example {eps : ℝ} {p : ℝ[X]} (heps : 0 < eps) (hp0 : p ≠ 0)
    (hp : p.Splits) :
    StrictInterl p (tDeriv eps p) := by
  rr_TDeriv_strict_interl using eps_pos := heps, nonzero := hp0, splits := hp

example {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (heps : ∀ i : Nat, 0 < eps i)
    (hP0 : ∀ i : Nat, P i ≠ 0)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, StrictInterl (P i) (tDeriv (eps i) (P i)) := by
  rr_TDeriv_sequence_strict_interl using
    eps_pos := heps,
    nonzero := hP0,
    splits := hP

example {eps : ℝ} {p : ℝ[X]} {k : ℕ} (hp0 : p ≠ 0) :
    iterateTDeriv eps k p ≠ 0 := by
  rr_iterateTDeriv_ne_zero using nonzero := hp0

example {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ}
    (hP0 : ∀ i : Nat, P i ≠ 0) :
    ∀ i : Nat, iterateTDeriv (eps i) (K i) (P i) ≠ 0 := by
  rr_iterateTDeriv_sequence_ne_zero using nonzero := hP0, index := K

example {eps : ℝ} {p : ℝ[X]} {k : ℕ} (heps : 0 < eps) (hp : p.Splits) :
    (iterateTDeriv eps k p).Splits := by
  rr_iterateTDeriv_splits using eps_pos := heps, splits := hp

example {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ}
    (heps : ∀ i : Nat, 0 < eps i)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, (iterateTDeriv (eps i) (K i) (P i)).Splits := by
  rr_iterateTDeriv_sequence_splits using
    eps_pos := heps,
    splits := hP,
    index := K

example {eps : ℝ} {p : ℝ[X]} {n : ℕ} (heps : 0 < eps) (hp0 : p ≠ 0)
    (hp : p.Splits) :
    StrictInterl (iterateTDeriv eps n p) (iterateTDeriv eps (n + 1) p) := by
  rr_iterateTDeriv_strict_interl_succ using eps_pos := heps, nonzero := hp0, splits := hp

example {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ}
    (heps : ∀ i : Nat, 0 < eps i)
    (hP0 : ∀ i : Nat, P i ≠ 0)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat,
      StrictInterl (iterateTDeriv (eps i) (K i) (P i))
        (iterateTDeriv (eps i) (K i + 1) (P i)) := by
  rr_iterateTDeriv_sequence_strict_interl_succ using
    eps_pos := heps,
    nonzero := hP0,
    splits := hP,
    index := K

example {eps : ℝ} {p : ℝ[X]} {k : ℕ} :
    (iterateTDeriv eps k p).natDegree = p.natDegree := by
  rr_iterateTDeriv_natDegree

example {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat, (iterateTDeriv (eps i) (K i) (P i)).natDegree = (P i).natDegree := by
  rr_iterateTDeriv_sequence_natDegree

example {eps : ℝ} {p : ℝ[X]} {k : ℕ} :
    (iterateTDeriv eps k p).leadingCoeff = p.leadingCoeff := by
  rr_iterateTDeriv_leadingCoeff

example {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat,
      (iterateTDeriv (eps i) (K i) (P i)).leadingCoeff = (P i).leadingCoeff := by
  rr_iterateTDeriv_sequence_leadingCoeff

example {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ}
    (hP : ∀ i : Nat, HasPosLeadingCoeff (P i)) :
    ∀ i : Nat, HasPosLeadingCoeff (iterateTDeriv (eps i) (K i) (P i)) := by
  rr_iterateTDeriv_sequence_pos_lc using pos_lc := hP, index := K

example {eps : ℝ} {p : ℝ[X]} {k : ℕ} (hp : p.Monic) :
    (iterateTDeriv eps k p).Monic := by
  rr_iterateTDeriv_monic using monic := hp

example {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ}
    (hP : ∀ i : Nat, (P i).Monic) :
    ∀ i : Nat, (iterateTDeriv (eps i) (K i) (P i)).Monic := by
  rr_iterateTDeriv_sequence_monic using monic := hP, index := K

example (eps : ℝ) (p q : ℝ[X]) :
    tDeriv eps (p + q) = tDeriv eps p + tDeriv eps q := by
  rr_TDeriv_add

example {eps : Nat → ℝ} {P Q : Nat → ℝ[X]} :
    ∀ i : Nat,
      tDeriv (eps i) (P i + Q i) =
        tDeriv (eps i) (P i) + tDeriv (eps i) (Q i) := by
  rr_TDeriv_sequence_add

example (eps c : ℝ) (p : ℝ[X]) :
    tDeriv eps (C c * p) = C c * tDeriv eps p := by
  rr_TDeriv_C_mul

example {eps c : Nat → ℝ} {P : Nat → ℝ[X]} :
    ∀ i : Nat,
      tDeriv (eps i) (C (c i) * P i) =
        C (c i) * tDeriv (eps i) (P i) := by
  rr_TDeriv_sequence_C_mul

example (eps : ℝ) (n : ℕ) (p q : ℝ[X]) :
    iterateTDeriv eps n (p + q) = iterateTDeriv eps n p + iterateTDeriv eps n q := by
  rr_iterateTDeriv_add

example {eps : Nat → ℝ} {P Q : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat,
      iterateTDeriv (eps i) (K i) (P i + Q i) =
        iterateTDeriv (eps i) (K i) (P i) +
          iterateTDeriv (eps i) (K i) (Q i) := by
  rr_iterateTDeriv_sequence_add

example (eps c : ℝ) (n : ℕ) (p : ℝ[X]) :
    iterateTDeriv eps n (C c * p) = C c * iterateTDeriv eps n p := by
  rr_iterateTDeriv_C_mul

example {eps c : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat,
      iterateTDeriv (eps i) (K i) (C (c i) * P i) =
        C (c i) * iterateTDeriv (eps i) (K i) (P i) := by
  rr_iterateTDeriv_sequence_C_mul

example (eps : ℝ) (p : ℝ[X]) :
    (tDeriv eps p).derivative = tDeriv eps p.derivative := by
  rr_derivative_TDeriv

example {eps : Nat → ℝ} {P : Nat → ℝ[X]} :
    ∀ i : Nat,
      (tDeriv (eps i) (P i)).derivative =
        tDeriv (eps i) (P i).derivative := by
  rr_derivative_TDeriv_sequence

example (eps : ℝ) (k : ℕ) (p : ℝ[X]) :
    (derivative^[k]) (tDeriv eps p) = tDeriv eps ((derivative^[k]) p) := by
  rr_iterate_derivative_TDeriv

example {eps : Nat → ℝ} {K : Nat → ℕ} {P : Nat → ℝ[X]} :
    ∀ i : Nat,
      (derivative^[K i]) (tDeriv (eps i) (P i)) =
        tDeriv (eps i) ((derivative^[K i]) (P i)) := by
  rr_iterate_derivative_TDeriv_sequence

example (eps : ℝ) (n k : ℕ) (p : ℝ[X]) :
    (derivative^[k]) (iterateTDeriv eps n p) =
      iterateTDeriv eps n ((derivative^[k]) p) := by
  rr_iterate_derivative_iterateTDeriv

example {eps : Nat → ℝ} {K L : Nat → ℕ} {P : Nat → ℝ[X]} :
    ∀ i : Nat,
      (derivative^[K i]) (iterateTDeriv (eps i) (L i) (P i)) =
        iterateTDeriv (eps i) (L i) ((derivative^[K i]) (P i)) := by
  rr_iterate_derivative_iterateTDeriv_sequence

end Tactic
end RealRooted
