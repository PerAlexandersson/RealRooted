import RealRooted.IteratedDerivativeShift

/-!
# Iterated derivative-shift tactic frontends

Thin wrappers for `TDeriv` and `iterateTDeriv` preservation facts.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem TDeriv_sequence_pos_lc {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasPosLeadingCoeff (P i)) :
    ∀ i : Nat, HasPosLeadingCoeff (TDeriv (eps i) (P i)) := fun i =>
  RealRooted.HasPosLeadingCoeff.TDeriv (hP i)

theorem TDeriv_sequence_ne_zero {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, P i ≠ 0) :
    ∀ i : Nat, TDeriv (eps i) (P i) ≠ 0 := fun i =>
  RealRooted.TDeriv_ne_zero (hP i)

theorem TDeriv_sequence_splits {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (heps : ∀ i : Nat, 0 < eps i)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, (TDeriv (eps i) (P i)).Splits := fun i =>
  RealRooted.splits_tderiv (heps i) (hP i)

theorem TDeriv_sequence_prec {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (heps : ∀ i : Nat, 0 < eps i)
    (hP0 : ∀ i : Nat, P i ≠ 0)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, Prec (P i) (TDeriv (eps i) (P i)) := fun i =>
  RealRooted.prec_TDeriv (heps i) (hP0 i) (hP i)

theorem iterateTDeriv_sequence_ne_zero
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} (K : Nat → ℕ)
    (hP : ∀ i : Nat, P i ≠ 0) :
    ∀ i : Nat, iterateTDeriv (eps i) (K i) (P i) ≠ 0 := fun i =>
  RealRooted.iterateTDeriv_ne_zero (hP i)

theorem iterateTDeriv_sequence_splits
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} (K : Nat → ℕ)
    (heps : ∀ i : Nat, 0 < eps i)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, (iterateTDeriv (eps i) (K i) (P i)).Splits := fun i =>
  RealRooted.splits_iterateTDeriv (heps i) (hP i)

theorem iterateTDeriv_sequence_prec_succ
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} (K : Nat → ℕ)
    (heps : ∀ i : Nat, 0 < eps i)
    (hP0 : ∀ i : Nat, P i ≠ 0)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat,
      Prec (iterateTDeriv (eps i) (K i) (P i))
        (iterateTDeriv (eps i) (K i + 1) (P i)) := fun i =>
  RealRooted.prec_iterateTDeriv_succ (heps i) (hP0 i) (hP i)

theorem iterateTDeriv_sequence_natDegree
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat, (iterateTDeriv (eps i) (K i) (P i)).natDegree = (P i).natDegree :=
  fun i => RealRooted.natDegree_iterateTDeriv (eps i) (P i) (K i)

theorem iterateTDeriv_sequence_leadingCoeff
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat,
      (iterateTDeriv (eps i) (K i) (P i)).leadingCoeff = (P i).leadingCoeff :=
  fun i => RealRooted.leadingCoeff_iterateTDeriv (eps i) (P i) (K i)

theorem iterateTDeriv_sequence_pos_lc
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} (K : Nat → ℕ)
    (hP : ∀ i : Nat, HasPosLeadingCoeff (P i)) :
    ∀ i : Nat, HasPosLeadingCoeff (iterateTDeriv (eps i) (K i) (P i)) := fun i =>
  RealRooted.hasPosLeadingCoeff_iterateTDeriv.mpr (hP i)

theorem iterateTDeriv_sequence_monic
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} (K : Nat → ℕ)
    (hP : ∀ i : Nat, (P i).Monic) :
    ∀ i : Nat, (iterateTDeriv (eps i) (K i) (P i)).Monic := fun i =>
  RealRooted.monic_iterateTDeriv (hP i)

theorem TDeriv_sequence_add {eps : Nat → ℝ} {P Q : Nat → ℝ[X]} :
    ∀ i : Nat,
      TDeriv (eps i) (P i + Q i) =
        TDeriv (eps i) (P i) + TDeriv (eps i) (Q i) := fun i =>
  RealRooted.TDeriv_add (eps i) (P i) (Q i)

theorem TDeriv_sequence_C_mul
    {eps c : Nat → ℝ} {P : Nat → ℝ[X]} :
    ∀ i : Nat,
      TDeriv (eps i) (C (c i) * P i) =
        C (c i) * TDeriv (eps i) (P i) := fun i =>
  RealRooted.TDeriv_C_mul (eps i) (c i) (P i)

theorem iterateTDeriv_sequence_add
    {eps : Nat → ℝ} {P Q : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat,
      iterateTDeriv (eps i) (K i) (P i + Q i) =
        iterateTDeriv (eps i) (K i) (P i) +
          iterateTDeriv (eps i) (K i) (Q i) := fun i =>
  RealRooted.iterateTDeriv_add (eps i) (K i) (P i) (Q i)

theorem iterateTDeriv_sequence_C_mul
    {eps c : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat,
      iterateTDeriv (eps i) (K i) (C (c i) * P i) =
        C (c i) * iterateTDeriv (eps i) (K i) (P i) := fun i =>
  RealRooted.iterateTDeriv_C_mul (eps i) (c i) (K i) (P i)

theorem derivative_TDeriv_sequence {eps : Nat → ℝ} {P : Nat → ℝ[X]} :
    ∀ i : Nat,
      (TDeriv (eps i) (P i)).derivative =
        TDeriv (eps i) (P i).derivative := fun i =>
  RealRooted.derivative_TDeriv (eps i) (P i)

theorem iterate_derivative_TDeriv_sequence
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat,
      (Polynomial.derivative^[K i]) (TDeriv (eps i) (P i)) =
        TDeriv (eps i) ((Polynomial.derivative^[K i]) (P i)) := fun i =>
  RealRooted.iterate_derivative_TDeriv (eps i) (K i) (P i)

theorem iterate_derivative_iterateTDeriv_sequence
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K L : Nat → ℕ} :
    ∀ i : Nat,
      (Polynomial.derivative^[K i]) (iterateTDeriv (eps i) (L i) (P i)) =
        iterateTDeriv (eps i) (L i) ((Polynomial.derivative^[K i]) (P i)) :=
  fun i =>
    RealRooted.iterate_derivative_iterateTDeriv (eps i) (L i) (K i) (P i)

syntax (name := rr_TDeriv_pos_lc_named)
  "rr_TDeriv_pos_lc" " using " "pos_lc" ":=" term :
  tactic

syntax (name := rr_TDeriv_sequence_pos_lc_named)
  "rr_TDeriv_sequence_pos_lc" " using " "pos_lc" ":=" term :
  tactic

syntax (name := rr_TDeriv_ne_zero_named)
  "rr_TDeriv_ne_zero" " using " "nonzero" ":=" term :
  tactic

syntax (name := rr_TDeriv_sequence_ne_zero_named)
  "rr_TDeriv_sequence_ne_zero" " using " "nonzero" ":=" term :
  tactic

syntax (name := rr_TDeriv_splits_named)
  "rr_TDeriv_splits" " using "
    "eps_pos" ":=" term ","
    "splits" ":=" term :
  tactic

syntax (name := rr_TDeriv_sequence_splits_named)
  "rr_TDeriv_sequence_splits" " using "
    "eps_pos" ":=" term ","
    "splits" ":=" term :
  tactic

syntax (name := rr_TDeriv_prec_named)
  "rr_TDeriv_prec" " using "
    "eps_pos" ":=" term ","
    "nonzero" ":=" term ","
    "splits" ":=" term :
  tactic

syntax (name := rr_TDeriv_sequence_prec_named)
  "rr_TDeriv_sequence_prec" " using "
    "eps_pos" ":=" term ","
    "nonzero" ":=" term ","
    "splits" ":=" term :
  tactic

syntax (name := rr_iterateTDeriv_ne_zero_named)
  "rr_iterateTDeriv_ne_zero" " using " "nonzero" ":=" term :
  tactic

syntax (name := rr_iterateTDeriv_sequence_ne_zero_named)
  "rr_iterateTDeriv_sequence_ne_zero" " using "
    "nonzero" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_iterateTDeriv_splits_named)
  "rr_iterateTDeriv_splits" " using "
    "eps_pos" ":=" term ","
    "splits" ":=" term :
  tactic

syntax (name := rr_iterateTDeriv_sequence_splits_named)
  "rr_iterateTDeriv_sequence_splits" " using "
    "eps_pos" ":=" term ","
    "splits" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_iterateTDeriv_prec_succ_named)
  "rr_iterateTDeriv_prec_succ" " using "
    "eps_pos" ":=" term ","
    "nonzero" ":=" term ","
    "splits" ":=" term :
  tactic

syntax (name := rr_iterateTDeriv_sequence_prec_succ_named)
  "rr_iterateTDeriv_sequence_prec_succ" " using "
    "eps_pos" ":=" term ","
    "nonzero" ":=" term ","
    "splits" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_iterateTDeriv_natDegree_named)
  "rr_iterateTDeriv_natDegree" :
  tactic

syntax (name := rr_iterateTDeriv_sequence_natDegree_named)
  "rr_iterateTDeriv_sequence_natDegree" :
  tactic

syntax (name := rr_iterateTDeriv_leadingCoeff_named)
  "rr_iterateTDeriv_leadingCoeff" :
  tactic

syntax (name := rr_iterateTDeriv_sequence_leadingCoeff_named)
  "rr_iterateTDeriv_sequence_leadingCoeff" :
  tactic

syntax (name := rr_iterateTDeriv_sequence_pos_lc_named)
  "rr_iterateTDeriv_sequence_pos_lc" " using "
    "pos_lc" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_iterateTDeriv_monic_named)
  "rr_iterateTDeriv_monic" " using " "monic" ":=" term :
  tactic

syntax (name := rr_iterateTDeriv_sequence_monic_named)
  "rr_iterateTDeriv_sequence_monic" " using "
    "monic" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_TDeriv_add_named)
  "rr_TDeriv_add" :
  tactic

syntax (name := rr_TDeriv_sequence_add_named)
  "rr_TDeriv_sequence_add" :
  tactic

syntax (name := rr_TDeriv_C_mul_named)
  "rr_TDeriv_C_mul" :
  tactic

syntax (name := rr_TDeriv_sequence_C_mul_named)
  "rr_TDeriv_sequence_C_mul" :
  tactic

syntax (name := rr_iterateTDeriv_add_named)
  "rr_iterateTDeriv_add" :
  tactic

syntax (name := rr_iterateTDeriv_sequence_add_named)
  "rr_iterateTDeriv_sequence_add" :
  tactic

syntax (name := rr_iterateTDeriv_C_mul_named)
  "rr_iterateTDeriv_C_mul" :
  tactic

syntax (name := rr_iterateTDeriv_sequence_C_mul_named)
  "rr_iterateTDeriv_sequence_C_mul" :
  tactic

syntax (name := rr_derivative_TDeriv_named)
  "rr_derivative_TDeriv" :
  tactic

syntax (name := rr_derivative_TDeriv_sequence_named)
  "rr_derivative_TDeriv_sequence" :
  tactic

syntax (name := rr_iterate_derivative_TDeriv_named)
  "rr_iterate_derivative_TDeriv" :
  tactic

syntax (name := rr_iterate_derivative_TDeriv_sequence_named)
  "rr_iterate_derivative_TDeriv_sequence" :
  tactic

syntax (name := rr_iterate_derivative_iterateTDeriv_named)
  "rr_iterate_derivative_iterateTDeriv" :
  tactic

syntax (name := rr_iterate_derivative_iterateTDeriv_sequence_named)
  "rr_iterate_derivative_iterateTDeriv_sequence" :
  tactic

macro_rules
  | `(tactic| rr_TDeriv_pos_lc using pos_lc := $hp:term) =>
      `(tactic| exact RealRooted.HasPosLeadingCoeff.TDeriv $hp)
  | `(tactic| rr_TDeriv_sequence_pos_lc using pos_lc := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.TDeriv_sequence_pos_lc $hp)
  | `(tactic| rr_TDeriv_ne_zero using nonzero := $hp:term) =>
      `(tactic| exact RealRooted.TDeriv_ne_zero $hp)
  | `(tactic| rr_TDeriv_sequence_ne_zero using nonzero := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.TDeriv_sequence_ne_zero $hp)
  | `(tactic|
      rr_TDeriv_splits using
        eps_pos := $heps:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.splits_tderiv $heps $hp)
  | `(tactic|
      rr_TDeriv_sequence_splits using
        eps_pos := $heps:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.TDeriv_sequence_splits $heps $hp)
  | `(tactic|
      rr_TDeriv_prec using
        eps_pos := $heps:term,
        nonzero := $hp0:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.prec_TDeriv $heps $hp0 $hp)
  | `(tactic|
      rr_TDeriv_sequence_prec using
        eps_pos := $heps:term,
        nonzero := $hp0:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.TDeriv_sequence_prec $heps $hp0 $hp)
  | `(tactic| rr_iterateTDeriv_ne_zero using nonzero := $hp:term) =>
      `(tactic| exact RealRooted.iterateTDeriv_ne_zero $hp)
  | `(tactic|
      rr_iterateTDeriv_sequence_ne_zero using
        nonzero := $hp:term,
        index := $k:term) =>
      `(tactic| exact RealRooted.Tactic.iterateTDeriv_sequence_ne_zero $k $hp)
  | `(tactic|
      rr_iterateTDeriv_splits using
        eps_pos := $heps:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.splits_iterateTDeriv $heps $hp)
  | `(tactic|
      rr_iterateTDeriv_sequence_splits using
        eps_pos := $heps:term,
        splits := $hp:term,
        index := $k:term) =>
      `(tactic| exact RealRooted.Tactic.iterateTDeriv_sequence_splits
          $k $heps $hp)
  | `(tactic|
      rr_iterateTDeriv_prec_succ using
        eps_pos := $heps:term,
        nonzero := $hp0:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.prec_iterateTDeriv_succ $heps $hp0 $hp)
  | `(tactic|
      rr_iterateTDeriv_sequence_prec_succ using
        eps_pos := $heps:term,
        nonzero := $hp0:term,
        splits := $hp:term,
        index := $k:term) =>
      `(tactic| exact RealRooted.Tactic.iterateTDeriv_sequence_prec_succ
          $k $heps $hp0 $hp)
  | `(tactic| rr_iterateTDeriv_natDegree) =>
      `(tactic| exact RealRooted.natDegree_iterateTDeriv _ _ _)
  | `(tactic| rr_iterateTDeriv_sequence_natDegree) =>
      `(tactic| exact RealRooted.Tactic.iterateTDeriv_sequence_natDegree)
  | `(tactic| rr_iterateTDeriv_leadingCoeff) =>
      `(tactic| exact RealRooted.leadingCoeff_iterateTDeriv _ _ _)
  | `(tactic| rr_iterateTDeriv_sequence_leadingCoeff) =>
      `(tactic| exact RealRooted.Tactic.iterateTDeriv_sequence_leadingCoeff)
  | `(tactic|
      rr_iterateTDeriv_sequence_pos_lc using
        pos_lc := $hp:term,
        index := $k:term) =>
      `(tactic| exact RealRooted.Tactic.iterateTDeriv_sequence_pos_lc $k $hp)
  | `(tactic| rr_iterateTDeriv_monic using monic := $hp:term) =>
      `(tactic| exact RealRooted.monic_iterateTDeriv $hp)
  | `(tactic|
      rr_iterateTDeriv_sequence_monic using
        monic := $hp:term,
        index := $k:term) =>
      `(tactic| exact RealRooted.Tactic.iterateTDeriv_sequence_monic $k $hp)
  | `(tactic| rr_TDeriv_add) =>
      `(tactic| exact RealRooted.TDeriv_add _ _ _)
  | `(tactic| rr_TDeriv_sequence_add) =>
      `(tactic| exact RealRooted.Tactic.TDeriv_sequence_add)
  | `(tactic| rr_TDeriv_C_mul) =>
      `(tactic| exact RealRooted.TDeriv_C_mul _ _ _)
  | `(tactic| rr_TDeriv_sequence_C_mul) =>
      `(tactic| exact RealRooted.Tactic.TDeriv_sequence_C_mul)
  | `(tactic| rr_iterateTDeriv_add) =>
      `(tactic| exact RealRooted.iterateTDeriv_add _ _ _ _)
  | `(tactic| rr_iterateTDeriv_sequence_add) =>
      `(tactic| exact RealRooted.Tactic.iterateTDeriv_sequence_add)
  | `(tactic| rr_iterateTDeriv_C_mul) =>
      `(tactic| exact RealRooted.iterateTDeriv_C_mul _ _ _ _)
  | `(tactic| rr_iterateTDeriv_sequence_C_mul) =>
      `(tactic| exact RealRooted.Tactic.iterateTDeriv_sequence_C_mul)
  | `(tactic| rr_derivative_TDeriv) =>
      `(tactic| exact RealRooted.derivative_TDeriv _ _)
  | `(tactic| rr_derivative_TDeriv_sequence) =>
      `(tactic| exact RealRooted.Tactic.derivative_TDeriv_sequence)
  | `(tactic| rr_iterate_derivative_TDeriv) =>
      `(tactic| exact RealRooted.iterate_derivative_TDeriv _ _ _)
  | `(tactic| rr_iterate_derivative_TDeriv_sequence) =>
      `(tactic| exact RealRooted.Tactic.iterate_derivative_TDeriv_sequence)
  | `(tactic| rr_iterate_derivative_iterateTDeriv) =>
      `(tactic| exact RealRooted.iterate_derivative_iterateTDeriv _ _ _ _)
  | `(tactic| rr_iterate_derivative_iterateTDeriv_sequence) =>
      `(tactic|
        exact RealRooted.Tactic.iterate_derivative_iterateTDeriv_sequence)

end Tactic
end RealRooted
