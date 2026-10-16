module

public import RealRooted.GammaRealRoots

/-!
# Gamma-real-rootedness tactic frontends

Thin wrappers for gamma transforms and the gamma-polynomial
real-rootedness/nonpositive-root bridge.
-/

public section

open Polynomial

namespace RealRooted

theorem isRealRooted_gammaTransform_sequence_of_nonneg
    {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hdeg : ∀ i : Nat, (Γ i).natDegree ≤ d i / 2)
    (hne : ∀ i : Nat, Γ i ≠ 0)
    (hsplits : ∀ i : Nat, (Γ i).Splits)
    (hnn : ∀ i : Nat, HasNonnegCoeffs (Γ i)) :
    ∀ i : Nat, gammaTransform (d i) (Γ i) ≠ 0 ∧
      (gammaTransform (d i) (Γ i)).Splits := fun i =>
  isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
    (hdeg i) (hne i) (hsplits i) (hnn i)

theorem hasRootsNonpos_gammaTransform_sequence_of_nonneg
    {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hnn : ∀ i : Nat, HasNonnegCoeffs (Γ i)) :
    ∀ i : Nat, HasRootsNonpos (gammaTransform (d i) (Γ i)) := fun i =>
  hasRootsNonpos_gammaTransform_of_hasNonnegCoeffs (hnn i)

theorem gammaTransform_sequence_realrooted_and_roots_nonpos_of_roots_nonpos
    {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hdeg : ∀ i : Nat, (Γ i).natDegree ≤ d i / 2)
    (hne : ∀ i : Nat, Γ i ≠ 0)
    (hsplits : ∀ i : Nat, (Γ i).Splits)
    (hnp : ∀ i : Nat, HasRootsNonpos (Γ i)) :
    ∀ i : Nat,
      (gammaTransform (d i) (Γ i) ≠ 0 ∧
        (gammaTransform (d i) (Γ i)).Splits) ∧
        HasRootsNonpos (gammaTransform (d i) (Γ i)) := fun i =>
  isRealRooted_and_hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasRootsNonpos
    (hdeg i) (hne i) (hsplits i) (hnp i)

theorem gammaTransform_sequence_backward_of_natDegree_le
    {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hdeg : ∀ i : Nat, (Γ i).natDegree ≤ d i / 2)
    (hne : ∀ i : Nat, gammaTransform (d i) (Γ i) ≠ 0)
    (hsplits : ∀ i : Nat, (gammaTransform (d i) (Γ i)).Splits)
    (hnp : ∀ i : Nat, HasRootsNonpos (gammaTransform (d i) (Γ i))) :
    ∀ i : Nat, (Γ i ≠ 0 ∧ (Γ i).Splits) ∧ HasRootsNonpos (Γ i) := fun i =>
  isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
    (hdeg i) (hne i) (hsplits i) (hnp i)

theorem gammaTransform_sequence_backward_minimal
    {Γ : Nat → ℝ[X]}
    (hne : ∀ i : Nat, gammaTransform (2 * (Γ i).natDegree) (Γ i) ≠ 0)
    (hsplits : ∀ i : Nat, (gammaTransform (2 * (Γ i).natDegree) (Γ i)).Splits)
    (hnp : ∀ i : Nat,
      HasRootsNonpos (gammaTransform (2 * (Γ i).natDegree) (Γ i))) :
    ∀ i : Nat, (Γ i ≠ 0 ∧ (Γ i).Splits) ∧ HasRootsNonpos (Γ i) := fun i =>
  isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
    (hne i) (hsplits i) (hnp i)

theorem IsGammaExpansion.isRealRooted_and_hasRootsNonpos_iff_sequence
    {d : Nat → Nat} {P Γ : Nat → ℝ[X]}
    (hγdeg : ∀ i : Nat, (Γ i).natDegree ≤ d i / 2)
    (hexp : ∀ i : Nat, IsGammaExpansion (d i) (P i) (Γ i)) :
    ∀ i : Nat,
      (((Γ i ≠ 0 ∧ (Γ i).Splits) ∧ HasRootsNonpos (Γ i)) ↔
        ((P i ≠ 0 ∧ (P i).Splits) ∧ HasRootsNonpos (P i))) := fun i =>
  (hexp i).isRealRooted_and_hasRootsNonpos_iff (hγdeg i)

namespace Tactic

/-- Closes `gammaTransform d (γ + δ) = gammaTransform d γ + gammaTransform d δ`: the gamma transform
is additive. -/
syntax (name := rr_gamma_transform_add_named)
  "rr_gamma_transform_add" :
  tactic

/-- Closes `gammaTransform d (C a * γ) = C a * gammaTransform d γ`: the gamma transform commutes
with scalar multiplication. -/
syntax (name := rr_gamma_transform_C_mul_named)
  "rr_gamma_transform_C_mul" :
  tactic

/-- Closes `gammaTransform d (monomial n a) = if n ≤ d / 2 then C a * gammaBasisTerm d n else 0`,
the gamma transform of a monomial. -/
syntax (name := rr_gamma_transform_monomial_named)
  "rr_gamma_transform_monomial" :
  tactic

/-- Closes `idTransform d (gammaTransform d γ) = gammaTransform d γ`: the gamma transform is fixed
by `idTransform` in the same ambient degree `d`. -/
syntax (name := rr_gamma_transform_fixed_named)
  "rr_gamma_transform_fixed" :
  tactic

/-- Closes `HasNonnegCoeffs (gammaBasisTerm d i)`: each gamma basis term
`X ^ i * (X + 1) ^ (d - 2 * i)` has nonnegative coefficients. -/
syntax (name := rr_gamma_basis_nonneg_named)
  "rr_gamma_basis_nonneg" :
  tactic

/-- Closes `HasNonnegCoeffs (gammaTransform d γ)` from `nonneg : HasNonnegCoeffs γ`. -/
syntax (name := rr_gamma_transform_nonneg_named)
  "rr_gamma_transform_nonneg" " using " "nonneg" ":=" term :
  tactic

/-- Closes `(gammaTransform d γ).natDegree ≤ d`. -/
syntax (name := rr_gamma_transform_natDegree_le_named)
  "rr_gamma_transform_natDegree_le" :
  tactic

/-- Closes `γ = δ` from `transform_eq : gammaTransform d γ = gammaTransform d δ`, where
`left_degree : γ.natDegree ≤ d / 2` and `right_degree : δ.natDegree ≤ d / 2`. -/
syntax (name := rr_gamma_transform_injective_named)
  "rr_gamma_transform_injective" " using "
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "transform_eq" ":=" term :
  tactic

/-- Closes `gammaTransform d γ = 0 ↔ γ = 0` from `gamma_degree : γ.natDegree ≤ d / 2`. -/
syntax (name := rr_gamma_transform_zero_iff_named)
  "rr_gamma_transform_zero_iff" " using " "gamma_degree" ":=" term :
  tactic

/-- Closes `gammaTransform (d + 2) (X * γ) = X * gammaTransform d γ`. -/
syntax (name := rr_gamma_transform_X_mul_two_named)
  "rr_gamma_transform_X_mul_two" :
  tactic

/-- Closes `gammaTransform (d + 2) γ = (X + 1) ^ 2 * gammaTransform d γ` from
`gamma_degree : γ.natDegree ≤ d / 2`. -/
syntax (name := rr_gamma_transform_pad_two_named)
  "rr_gamma_transform_pad_two" " using " "gamma_degree" ":=" term :
  tactic

/-- Closes `gammaTransform (2 * m + 1) γ = (X + 1) * gammaTransform (2 * m) γ`. -/
syntax (name := rr_gamma_transform_odd_named)
  "rr_gamma_transform_odd" :
  tactic

/-- Closes `gammaTransform d γ ≠ 0 ∧ (gammaTransform d γ).Splits` from
`gamma_degree : γ.natDegree ≤ d / 2`, `gamma_nonzero : γ ≠ 0`, `gamma_splits : γ.Splits` and
`gamma_nonneg : HasNonnegCoeffs γ`. -/
syntax (name := rr_gamma_transform_realrooted_nonneg_named)
  "rr_gamma_transform_realrooted_nonneg" " using "
    "gamma_degree" ":=" term ","
    "gamma_nonzero" ":=" term ","
    "gamma_splits" ":=" term ","
    "gamma_nonneg" ":=" term :
  tactic

/-- Closes `HasRootsNonpos (gammaTransform d γ)` from `gamma_nonneg : HasNonnegCoeffs γ`. -/
syntax (name := rr_gamma_transform_roots_nonpos_nonneg_named)
  "rr_gamma_transform_roots_nonpos_nonneg" " using "
    "gamma_nonneg" ":=" term :
  tactic

/-- Closes the conjunction of `gammaTransform d γ ≠ 0 ∧ (gammaTransform d γ).Splits` and
`HasRootsNonpos (gammaTransform d γ)` from `gamma_degree : γ.natDegree ≤ d / 2`,
`gamma_nonzero : γ ≠ 0`, `gamma_splits : γ.Splits` and `gamma_roots_nonpos : HasRootsNonpos γ`. -/
syntax (name := rr_gamma_transform_realrooted_nonpos_named)
  "rr_gamma_transform_realrooted_nonpos" " using "
    "gamma_degree" ":=" term ","
    "gamma_nonzero" ":=" term ","
    "gamma_splits" ":=" term ","
    "gamma_roots_nonpos" ":=" term :
  tactic

/-- Closes `(γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ` from the corresponding facts `transform_nonzero`,
`transform_splits` and `transform_roots_nonpos` for `gammaTransform (2 * γ.natDegree) γ`, the
transform in the minimal even ambient degree. -/
syntax (name := rr_gamma_transform_backward_minimal_named)
  "rr_gamma_transform_backward_minimal" " using "
    "transform_nonzero" ":=" term ","
    "transform_splits" ":=" term ","
    "transform_roots_nonpos" ":=" term :
  tactic

/-- Closes `(γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ` from `gamma_degree : γ.natDegree ≤ d / 2` and the
facts `transform_nonzero`, `transform_splits` and `transform_roots_nonpos` for `gammaTransform d γ`.
-/
syntax (name := rr_gamma_transform_backward_named)
  "rr_gamma_transform_backward" " using "
    "gamma_degree" ":=" term ","
    "transform_nonzero" ":=" term ","
    "transform_splits" ":=" term ","
    "transform_roots_nonpos" ":=" term :
  tactic

/-- Closes `((γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ) ↔ ((p ≠ 0 ∧ p.Splits) ∧ HasRootsNonpos p)` from
`gamma_degree : γ.natDegree ≤ d / 2` and `expansion : IsGammaExpansion d p γ`. -/
syntax (name := rr_gamma_realrooted_iff_named)
  "rr_gamma_realrooted_iff" " using "
    "gamma_degree" ":=" term ","
    "expansion" ":=" term :
  tactic

/-- Sequence form of `rr_gamma_transform_realrooted_nonneg`: the same certificate for every index
`i`. -/
syntax (name := rr_gamma_transform_sequence_realrooted_nonneg_named)
  "rr_gamma_transform_sequence_realrooted_nonneg" " using "
    "gamma_degree" ":=" term ","
    "gamma_nonzero" ":=" term ","
    "gamma_splits" ":=" term ","
    "gamma_nonneg" ":=" term :
  tactic

/-- Sequence form of `rr_gamma_transform_roots_nonpos_nonneg`: the same certificate for every index
`i`. -/
syntax (name := rr_gamma_transform_sequence_roots_nonpos_nonneg_named)
  "rr_gamma_transform_sequence_roots_nonpos_nonneg" " using "
    "gamma_nonneg" ":=" term :
  tactic

/-- Sequence form of `rr_gamma_transform_realrooted_nonpos`: the same certificate for every index
`i`. -/
syntax (name := rr_gamma_transform_sequence_realrooted_nonpos_named)
  "rr_gamma_transform_sequence_realrooted_nonpos" " using "
    "gamma_degree" ":=" term ","
    "gamma_nonzero" ":=" term ","
    "gamma_splits" ":=" term ","
    "gamma_roots_nonpos" ":=" term :
  tactic

/-- Sequence form of `rr_gamma_transform_backward_minimal`: the same certificate for every index
`i`. -/
syntax (name := rr_gamma_transform_sequence_backward_minimal_named)
  "rr_gamma_transform_sequence_backward_minimal" " using "
    "transform_nonzero" ":=" term ","
    "transform_splits" ":=" term ","
    "transform_roots_nonpos" ":=" term :
  tactic

/-- Sequence form of `rr_gamma_transform_backward`: the same certificate for every index `i`. -/
syntax (name := rr_gamma_transform_sequence_backward_named)
  "rr_gamma_transform_sequence_backward" " using "
    "gamma_degree" ":=" term ","
    "transform_nonzero" ":=" term ","
    "transform_splits" ":=" term ","
    "transform_roots_nonpos" ":=" term :
  tactic

/-- Sequence form of `rr_gamma_realrooted_iff`: the same certificate for every index `i`. -/
syntax (name := rr_gamma_sequence_realrooted_iff_named)
  "rr_gamma_sequence_realrooted_iff" " using "
    "gamma_degree" ":=" term ","
    "expansion" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_gamma_transform_add) =>
      `(tactic| exact RealRooted.gammaTransform_add _ _ _)
  | `(tactic| rr_gamma_transform_C_mul) =>
      `(tactic| exact RealRooted.gammaTransform_C_mul _ _ _)
  | `(tactic| rr_gamma_transform_monomial) =>
      `(tactic| exact RealRooted.gammaTransform_monomial _ _ _)
  | `(tactic| rr_gamma_transform_fixed) =>
      `(tactic| exact RealRooted.gammaTransform_fixed _ _)
  | `(tactic| rr_gamma_basis_nonneg) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_gammaBasisTerm _ _)
  | `(tactic| rr_gamma_transform_nonneg using nonneg := $hγ:term) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_gammaTransform $hγ)
  | `(tactic| rr_gamma_transform_natDegree_le) =>
      `(tactic| exact RealRooted.natDegree_gammaTransform_le _ _)
  | `(tactic|
      rr_gamma_transform_injective using
        left_degree := $hγ:term,
        right_degree := $hδ:term,
        transform_eq := $hEq:term) =>
      `(tactic| exact RealRooted.gammaTransform_injective_of_natDegree_le $hγ $hδ $hEq)
  | `(tactic| rr_gamma_transform_zero_iff using gamma_degree := $hγ:term) =>
      `(tactic| exact RealRooted.gammaTransform_eq_zero_iff_of_natDegree_le $hγ)
  | `(tactic| rr_gamma_transform_X_mul_two) =>
      `(tactic| exact RealRooted.gammaTransform_X_mul_two _ _)
  | `(tactic| rr_gamma_transform_pad_two using gamma_degree := $hγ:term) =>
      `(tactic| exact RealRooted.gammaTransform_pad_two $hγ)
  | `(tactic| rr_gamma_transform_odd) =>
      `(tactic| exact RealRooted.gammaTransform_odd _ _)
  | `(tactic|
      rr_gamma_transform_realrooted_nonneg using
        gamma_degree := $hdeg:term,
        gamma_nonzero := $hne:term,
        gamma_splits := $hsplits:term,
        gamma_nonneg := $hnn:term) =>
      `(tactic|
        exact
          RealRooted.isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
            $hdeg $hne $hsplits $hnn)
  | `(tactic|
      rr_gamma_transform_roots_nonpos_nonneg using
        gamma_nonneg := $hnn:term) =>
      `(tactic|
        exact
          RealRooted.hasRootsNonpos_gammaTransform_of_hasNonnegCoeffs $hnn)
  | `(tactic|
      rr_gamma_transform_realrooted_nonpos using
        gamma_degree := $hdeg:term,
        gamma_nonzero := $hne:term,
        gamma_splits := $hsplits:term,
        gamma_roots_nonpos := $hnp:term) =>
      `(tactic|
        exact
          isRealRooted_and_hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasRootsNonpos
            $hdeg $hne $hsplits $hnp)
  | `(tactic|
      rr_gamma_transform_backward_minimal using
        transform_nonzero := $hne:term,
        transform_splits := $hsplits:term,
        transform_roots_nonpos := $hnp:term) =>
      `(tactic|
        exact
          RealRooted.isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
            $hne $hsplits $hnp)
  | `(tactic|
      rr_gamma_transform_backward using
        gamma_degree := $hdeg:term,
        transform_nonzero := $hne:term,
        transform_splits := $hsplits:term,
        transform_roots_nonpos := $hnp:term) =>
      `(tactic|
        exact
          RealRooted.isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
            $hdeg $hne $hsplits $hnp)
  | `(tactic|
      rr_gamma_realrooted_iff using
        gamma_degree := $hγdeg:term,
        expansion := $hexp:term) =>
      `(tactic|
        exact RealRooted.IsGammaExpansion.isRealRooted_and_hasRootsNonpos_iff $hγdeg $hexp)
  | `(tactic|
      rr_gamma_transform_sequence_realrooted_nonneg using
        gamma_degree := $hdeg:term,
        gamma_nonzero := $hne:term,
        gamma_splits := $hsplits:term,
        gamma_nonneg := $hnn:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_gammaTransform_sequence_of_nonneg
          $hdeg $hne $hsplits $hnn)
  | `(tactic|
      rr_gamma_transform_sequence_roots_nonpos_nonneg using
        gamma_nonneg := $hnn:term) =>
      `(tactic|
        exact RealRooted.hasRootsNonpos_gammaTransform_sequence_of_nonneg
          $hnn)
  | `(tactic|
      rr_gamma_transform_sequence_realrooted_nonpos using
        gamma_degree := $hdeg:term,
        gamma_nonzero := $hne:term,
        gamma_splits := $hsplits:term,
        gamma_roots_nonpos := $hnp:term) =>
      `(tactic|
        exact
          RealRooted.gammaTransform_sequence_realrooted_and_roots_nonpos_of_roots_nonpos
            $hdeg $hne $hsplits $hnp)
  | `(tactic|
      rr_gamma_transform_sequence_backward_minimal using
        transform_nonzero := $hne:term,
        transform_splits := $hsplits:term,
        transform_roots_nonpos := $hnp:term) =>
      `(tactic|
        exact RealRooted.gammaTransform_sequence_backward_minimal
          $hne $hsplits $hnp)
  | `(tactic|
      rr_gamma_transform_sequence_backward using
        gamma_degree := $hdeg:term,
        transform_nonzero := $hne:term,
        transform_splits := $hsplits:term,
        transform_roots_nonpos := $hnp:term) =>
      `(tactic|
        exact RealRooted.gammaTransform_sequence_backward_of_natDegree_le
          $hdeg $hne $hsplits $hnp)
  | `(tactic|
      rr_gamma_sequence_realrooted_iff using
        gamma_degree := $hγdeg:term,
        expansion := $hexp:term) =>
      `(tactic|
        exact RealRooted.IsGammaExpansion.isRealRooted_and_hasRootsNonpos_iff_sequence
          $hγdeg $hexp)

end Tactic
end RealRooted
