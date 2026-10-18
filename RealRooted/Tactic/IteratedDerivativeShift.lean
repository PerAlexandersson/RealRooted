import RealRooted.IteratedDerivativeShift

/-!
# Iterated derivative-shift tactic frontends

Thin wrappers for `tDeriv` and `iterateTDeriv` preservation facts.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem tDeriv_sequence_pos_lc {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasPosLeadingCoeff (P i)) :
    ∀ i : Nat, HasPosLeadingCoeff (tDeriv (eps i) (P i)) := fun i =>
  RealRooted.HasPosLeadingCoeff.tDeriv (hP i)

theorem tDeriv_sequence_ne_zero {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, P i ≠ 0) :
    ∀ i : Nat, tDeriv (eps i) (P i) ≠ 0 := fun i =>
  RealRooted.tDeriv_ne_zero (hP i)

theorem tDeriv_sequence_splits {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (heps : ∀ i : Nat, 0 < eps i)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, (tDeriv (eps i) (P i)).Splits := fun i =>
  RealRooted.splits_tDeriv (heps i) (hP i)

theorem tDeriv_sequence_strictInterl {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (heps : ∀ i : Nat, 0 < eps i)
    (hP0 : ∀ i : Nat, P i ≠ 0)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat, StrictInterl (P i) (tDeriv (eps i) (P i)) := fun i =>
  RealRooted.strictInterl_tDeriv (heps i) (hP0 i) (hP i)

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

theorem iterateTDeriv_sequence_strictInterl_succ
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} (K : Nat → ℕ)
    (heps : ∀ i : Nat, 0 < eps i)
    (hP0 : ∀ i : Nat, P i ≠ 0)
    (hP : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat,
      StrictInterl (iterateTDeriv (eps i) (K i) (P i))
        (iterateTDeriv (eps i) (K i + 1) (P i)) := fun i =>
  RealRooted.strictInterl_iterateTDeriv_succ (heps i) (hP0 i) (hP i)

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

theorem tDeriv_sequence_add {eps : Nat → ℝ} {P Q : Nat → ℝ[X]} :
    ∀ i : Nat,
      tDeriv (eps i) (P i + Q i) =
        tDeriv (eps i) (P i) + tDeriv (eps i) (Q i) := fun i =>
  RealRooted.tDeriv_add (eps i) (P i) (Q i)

theorem tDeriv_sequence_C_mul
    {eps c : Nat → ℝ} {P : Nat → ℝ[X]} :
    ∀ i : Nat,
      tDeriv (eps i) (C (c i) * P i) =
        C (c i) * tDeriv (eps i) (P i) := fun i =>
  RealRooted.tDeriv_C_mul (eps i) (c i) (P i)

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

theorem derivative_tDeriv_sequence {eps : Nat → ℝ} {P : Nat → ℝ[X]} :
    ∀ i : Nat,
      (tDeriv (eps i) (P i)).derivative =
        tDeriv (eps i) (P i).derivative := fun i =>
  RealRooted.derivative_tDeriv (eps i) (P i)

theorem iterate_derivative_tDeriv_sequence
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K : Nat → ℕ} :
    ∀ i : Nat,
      (Polynomial.derivative^[K i]) (tDeriv (eps i) (P i)) =
        tDeriv (eps i) ((Polynomial.derivative^[K i]) (P i)) := fun i =>
  RealRooted.iterate_derivative_tDeriv (eps i) (K i) (P i)

theorem iterate_derivative_iterateTDeriv_sequence
    {eps : Nat → ℝ} {P : Nat → ℝ[X]} {K L : Nat → ℕ} :
    ∀ i : Nat,
      (Polynomial.derivative^[K i]) (iterateTDeriv (eps i) (L i) (P i)) =
        iterateTDeriv (eps i) (L i) ((Polynomial.derivative^[K i]) (P i)) :=
  fun i =>
    RealRooted.iterate_derivative_iterateTDeriv (eps i) (L i) (K i) (P i)

/-- Closes `HasPosLeadingCoeff (tDeriv eps p)` from `pos_lc : HasPosLeadingCoeff p`, where
`tDeriv eps p = p - C eps * p.derivative`. -/
syntax (name := rr_TDeriv_pos_lc_named)
  "rr_TDeriv_pos_lc" " using " "pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_TDeriv_pos_lc`: the same certificate for every index `i`. -/
syntax (name := rr_TDeriv_sequence_pos_lc_named)
  "rr_TDeriv_sequence_pos_lc" " using " "pos_lc" ":=" term :
  tactic

/-- Closes `tDeriv eps p ≠ 0` from `nonzero : p ≠ 0`. -/
syntax (name := rr_TDeriv_ne_zero_named)
  "rr_TDeriv_ne_zero" " using " "nonzero" ":=" term :
  tactic

/-- Sequence form of `rr_TDeriv_ne_zero`: the same certificate for every index `i`. -/
syntax (name := rr_TDeriv_sequence_ne_zero_named)
  "rr_TDeriv_sequence_ne_zero" " using " "nonzero" ":=" term :
  tactic

/-- Closes `(tDeriv eps p).Splits` from `eps_pos : 0 < eps` and `splits : p.Splits`. -/
syntax (name := rr_TDeriv_splits_named)
  "rr_TDeriv_splits" " using "
    "eps_pos" ":=" term ","
    "splits" ":=" term :
  tactic

/-- Sequence form of `rr_TDeriv_splits`: the same certificate for every index `i`. -/
syntax (name := rr_TDeriv_sequence_splits_named)
  "rr_TDeriv_sequence_splits" " using "
    "eps_pos" ":=" term ","
    "splits" ":=" term :
  tactic

/-- Closes `StrictInterl p (tDeriv eps p)` from `eps_pos : 0 < eps`, `nonzero : p ≠ 0` and
`splits : p.Splits`. -/
syntax (name := rr_TDeriv_strict_interl_named)
  "rr_TDeriv_strict_interl" " using "
    "eps_pos" ":=" term ","
    "nonzero" ":=" term ","
    "splits" ":=" term :
  tactic

/-- Sequence form of `rr_TDeriv_strict_interl`: the same certificate for every index `i`. -/
syntax (name := rr_TDeriv_sequence_strict_interl_named)
  "rr_TDeriv_sequence_strict_interl" " using "
    "eps_pos" ":=" term ","
    "nonzero" ":=" term ","
    "splits" ":=" term :
  tactic

/-- Closes `iterateTDeriv eps k p ≠ 0` from `nonzero : p ≠ 0`, where `iterateTDeriv eps k` is the
`k`-fold iterate of `tDeriv eps`. -/
syntax (name := rr_iterateTDeriv_ne_zero_named)
  "rr_iterateTDeriv_ne_zero" " using " "nonzero" ":=" term :
  tactic

/-- Sequence form of `rr_iterateTDeriv_ne_zero`: the same certificate for every index `i`. The
argument `index` is the sequence `K` of iteration counts. -/
syntax (name := rr_iterateTDeriv_sequence_ne_zero_named)
  "rr_iterateTDeriv_sequence_ne_zero" " using "
    "nonzero" ":=" term ","
    "index" ":=" term :
  tactic

/-- Closes `(iterateTDeriv eps k p).Splits` from `eps_pos : 0 < eps` and `splits : p.Splits`. -/
syntax (name := rr_iterateTDeriv_splits_named)
  "rr_iterateTDeriv_splits" " using "
    "eps_pos" ":=" term ","
    "splits" ":=" term :
  tactic

/-- Sequence form of `rr_iterateTDeriv_splits`: the same certificate for every index `i`. The
argument `index` is the sequence `K` of iteration counts. -/
syntax (name := rr_iterateTDeriv_sequence_splits_named)
  "rr_iterateTDeriv_sequence_splits" " using "
    "eps_pos" ":=" term ","
    "splits" ":=" term ","
    "index" ":=" term :
  tactic

/-- Closes `StrictInterl (iterateTDeriv eps k p) (iterateTDeriv eps (k + 1) p)` from
`eps_pos : 0 < eps`, `nonzero : p ≠ 0` and `splits : p.Splits`. -/
syntax (name := rr_iterateTDeriv_strict_interl_succ_named)
  "rr_iterateTDeriv_strict_interl_succ" " using "
    "eps_pos" ":=" term ","
    "nonzero" ":=" term ","
    "splits" ":=" term :
  tactic

/-- Sequence form of `rr_iterateTDeriv_strict_interl_succ`: the same certificate for every index
`i`. The argument `index` is the sequence `K` of iteration counts. -/
syntax (name := rr_iterateTDeriv_sequence_strict_interl_succ_named)
  "rr_iterateTDeriv_sequence_strict_interl_succ" " using "
    "eps_pos" ":=" term ","
    "nonzero" ":=" term ","
    "splits" ":=" term ","
    "index" ":=" term :
  tactic

/-- Closes `(iterateTDeriv eps k p).natDegree = p.natDegree`: iterating `tDeriv` preserves the
degree. -/
syntax (name := rr_iterateTDeriv_natDegree_named)
  "rr_iterateTDeriv_natDegree" :
  tactic

/-- Sequence form of `rr_iterateTDeriv_natDegree`: the same certificate for every index `i`. -/
syntax (name := rr_iterateTDeriv_sequence_natDegree_named)
  "rr_iterateTDeriv_sequence_natDegree" :
  tactic

/-- Closes `(iterateTDeriv eps k p).leadingCoeff = p.leadingCoeff`: iterating `tDeriv` preserves the
leading coefficient. -/
syntax (name := rr_iterateTDeriv_leadingCoeff_named)
  "rr_iterateTDeriv_leadingCoeff" :
  tactic

/-- Sequence form of `rr_iterateTDeriv_leadingCoeff`: the same certificate for every index `i`. -/
syntax (name := rr_iterateTDeriv_sequence_leadingCoeff_named)
  "rr_iterateTDeriv_sequence_leadingCoeff" :
  tactic

/-- Closes `∀ i, HasPosLeadingCoeff (iterateTDeriv (eps i) (K i) (P i))` from
`pos_lc : ∀ i, HasPosLeadingCoeff (P i)`. The argument `index` is the sequence `K` of iteration
counts. -/
syntax (name := rr_iterateTDeriv_sequence_pos_lc_named)
  "rr_iterateTDeriv_sequence_pos_lc" " using "
    "pos_lc" ":=" term ","
    "index" ":=" term :
  tactic

/-- Closes `(iterateTDeriv eps k p).Monic` from `monic : p.Monic`. -/
syntax (name := rr_iterateTDeriv_monic_named)
  "rr_iterateTDeriv_monic" " using " "monic" ":=" term :
  tactic

/-- Sequence form of `rr_iterateTDeriv_monic`: the same certificate for every index `i`. The
argument `index` is the sequence `K` of iteration counts. -/
syntax (name := rr_iterateTDeriv_sequence_monic_named)
  "rr_iterateTDeriv_sequence_monic" " using "
    "monic" ":=" term ","
    "index" ":=" term :
  tactic

/-- Closes `tDeriv eps (p + q) = tDeriv eps p + tDeriv eps q`: `tDeriv` is additive. -/
syntax (name := rr_TDeriv_add_named)
  "rr_TDeriv_add" :
  tactic

/-- Sequence form of `rr_TDeriv_add`: the same certificate for every index `i`. -/
syntax (name := rr_TDeriv_sequence_add_named)
  "rr_TDeriv_sequence_add" :
  tactic

/-- Closes `tDeriv eps (C c * p) = C c * tDeriv eps p`: `tDeriv` commutes with scalar
multiplication. -/
syntax (name := rr_TDeriv_C_mul_named)
  "rr_TDeriv_C_mul" :
  tactic

/-- Sequence form of `rr_TDeriv_C_mul`: the same certificate for every index `i`. -/
syntax (name := rr_TDeriv_sequence_C_mul_named)
  "rr_TDeriv_sequence_C_mul" :
  tactic

/-- Closes `iterateTDeriv eps k (p + q) = iterateTDeriv eps k p + iterateTDeriv eps k q`:
`iterateTDeriv` is additive. -/
syntax (name := rr_iterateTDeriv_add_named)
  "rr_iterateTDeriv_add" :
  tactic

/-- Sequence form of `rr_iterateTDeriv_add`: the same certificate for every index `i`. -/
syntax (name := rr_iterateTDeriv_sequence_add_named)
  "rr_iterateTDeriv_sequence_add" :
  tactic

/-- Closes `iterateTDeriv eps k (C c * p) = C c * iterateTDeriv eps k p`: `iterateTDeriv` commutes
with scalar multiplication. -/
syntax (name := rr_iterateTDeriv_C_mul_named)
  "rr_iterateTDeriv_C_mul" :
  tactic

/-- Sequence form of `rr_iterateTDeriv_C_mul`: the same certificate for every index `i`. -/
syntax (name := rr_iterateTDeriv_sequence_C_mul_named)
  "rr_iterateTDeriv_sequence_C_mul" :
  tactic

/-- Closes `(tDeriv eps p).derivative = tDeriv eps p.derivative`: the derivative commutes with
`tDeriv`. -/
syntax (name := rr_derivative_TDeriv_named)
  "rr_derivative_TDeriv" :
  tactic

/-- Sequence form of `rr_derivative_TDeriv`: the same certificate for every index `i`. -/
syntax (name := rr_derivative_TDeriv_sequence_named)
  "rr_derivative_TDeriv_sequence" :
  tactic

/-- Closes `(Polynomial.derivative^[k]) (tDeriv eps p) = tDeriv eps ((Polynomial.derivative^[k])
p)`: iterated derivatives commute with `tDeriv`. -/
syntax (name := rr_iterate_derivative_TDeriv_named)
  "rr_iterate_derivative_TDeriv" :
  tactic

/-- Sequence form of `rr_iterate_derivative_TDeriv`: the same certificate for every index `i`. -/
syntax (name := rr_iterate_derivative_TDeriv_sequence_named)
  "rr_iterate_derivative_TDeriv_sequence" :
  tactic

/-- Closes `(Polynomial.derivative^[k]) (iterateTDeriv eps l p) = iterateTDeriv eps l
((Polynomial.derivative^[k]) p)`: iterated derivatives commute with `iterateTDeriv`. -/
syntax (name := rr_iterate_derivative_iterateTDeriv_named)
  "rr_iterate_derivative_iterateTDeriv" :
  tactic

/-- Sequence form of `rr_iterate_derivative_iterateTDeriv`: the same certificate for every index
`i`. -/
syntax (name := rr_iterate_derivative_iterateTDeriv_sequence_named)
  "rr_iterate_derivative_iterateTDeriv_sequence" :
  tactic

macro_rules
  | `(tactic| rr_TDeriv_pos_lc using pos_lc := $hp:term) =>
      `(tactic| exact RealRooted.HasPosLeadingCoeff.tDeriv $hp)
  | `(tactic| rr_TDeriv_sequence_pos_lc using pos_lc := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.tDeriv_sequence_pos_lc $hp)
  | `(tactic| rr_TDeriv_ne_zero using nonzero := $hp:term) =>
      `(tactic| exact RealRooted.tDeriv_ne_zero $hp)
  | `(tactic| rr_TDeriv_sequence_ne_zero using nonzero := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.tDeriv_sequence_ne_zero $hp)
  | `(tactic|
      rr_TDeriv_splits using
        eps_pos := $heps:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.splits_tDeriv $heps $hp)
  | `(tactic|
      rr_TDeriv_sequence_splits using
        eps_pos := $heps:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.tDeriv_sequence_splits $heps $hp)
  | `(tactic|
      rr_TDeriv_strict_interl using
        eps_pos := $heps:term,
        nonzero := $hp0:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.strictInterl_tDeriv $heps $hp0 $hp)
  | `(tactic|
      rr_TDeriv_sequence_strict_interl using
        eps_pos := $heps:term,
        nonzero := $hp0:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.Tactic.tDeriv_sequence_strictInterl $heps $hp0 $hp)
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
      rr_iterateTDeriv_strict_interl_succ using
        eps_pos := $heps:term,
        nonzero := $hp0:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.strictInterl_iterateTDeriv_succ $heps $hp0 $hp)
  | `(tactic|
      rr_iterateTDeriv_sequence_strict_interl_succ using
        eps_pos := $heps:term,
        nonzero := $hp0:term,
        splits := $hp:term,
        index := $k:term) =>
      `(tactic| exact RealRooted.Tactic.iterateTDeriv_sequence_strictInterl_succ
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
      `(tactic| exact RealRooted.tDeriv_add _ _ _)
  | `(tactic| rr_TDeriv_sequence_add) =>
      `(tactic| exact RealRooted.Tactic.tDeriv_sequence_add)
  | `(tactic| rr_TDeriv_C_mul) =>
      `(tactic| exact RealRooted.tDeriv_C_mul _ _ _)
  | `(tactic| rr_TDeriv_sequence_C_mul) =>
      `(tactic| exact RealRooted.Tactic.tDeriv_sequence_C_mul)
  | `(tactic| rr_iterateTDeriv_add) =>
      `(tactic| exact RealRooted.iterateTDeriv_add _ _ _ _)
  | `(tactic| rr_iterateTDeriv_sequence_add) =>
      `(tactic| exact RealRooted.Tactic.iterateTDeriv_sequence_add)
  | `(tactic| rr_iterateTDeriv_C_mul) =>
      `(tactic| exact RealRooted.iterateTDeriv_C_mul _ _ _ _)
  | `(tactic| rr_iterateTDeriv_sequence_C_mul) =>
      `(tactic| exact RealRooted.Tactic.iterateTDeriv_sequence_C_mul)
  | `(tactic| rr_derivative_TDeriv) =>
      `(tactic| exact RealRooted.derivative_tDeriv _ _)
  | `(tactic| rr_derivative_TDeriv_sequence) =>
      `(tactic| exact RealRooted.Tactic.derivative_tDeriv_sequence)
  | `(tactic| rr_iterate_derivative_TDeriv) =>
      `(tactic| exact RealRooted.iterate_derivative_tDeriv _ _ _)
  | `(tactic| rr_iterate_derivative_TDeriv_sequence) =>
      `(tactic| exact RealRooted.Tactic.iterate_derivative_tDeriv_sequence)
  | `(tactic| rr_iterate_derivative_iterateTDeriv) =>
      `(tactic| exact RealRooted.iterate_derivative_iterateTDeriv _ _ _ _)
  | `(tactic| rr_iterate_derivative_iterateTDeriv_sequence) =>
      `(tactic|
        exact RealRooted.Tactic.iterate_derivative_iterateTDeriv_sequence)

end Tactic
end RealRooted
namespace RealRooted
namespace Tactic

end Tactic
end RealRooted
