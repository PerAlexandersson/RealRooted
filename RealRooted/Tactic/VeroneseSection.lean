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

theorem hasNonnegCoeffs_veroneseSectionPolynomial_sequence
    {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hr : ∀ n : Nat, 0 < r n) :
    ∀ n : Nat, HasNonnegCoeffs (veroneseSectionPolynomial (r n) (k n) (P n)) :=
  fun n => hasNonnegCoeffs_veroneseSectionPolynomial (hr n) (hnn n)

theorem isPolyaFreqSeq_veroneseSectionPolynomial_coeff_sequence
    {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hpf : ∀ n : Nat, IsPolyaFreqSeq (P n).coeff)
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat, IsPolyaFreqSeq (veroneseSectionPolynomial (r n) (k n) (P n)).coeff :=
  fun n => isPolyaFreqSeq_veroneseSectionPolynomial_coeff (hpf n) (hr n) (hk n)

theorem veroneseSectionPolynomial_sequence_zero_or_splits_of_pf
    {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hpf : ∀ n : Nat, IsPolyaFreqSeq (P n).coeff)
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat,
      veroneseSectionPolynomial (r n) (k n) (P n) = 0 ∨
        (veroneseSectionPolynomial (r n) (k n) (P n)).Splits := fun n =>
  splits_veroneseSectionPolynomial_of_pf (hpf n) (hr n) (hk n)

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

/-- Closes `HasNonnegCoeffs (veroneseSectionPolynomial r k P)` from `nonneg : HasNonnegCoeffs P`
and `r_pos : 0 < r`. -/
syntax (name := rr_veronese_section_nonneg_named)
  "rr_veronese_section_nonneg" " using "
    "nonneg" ":=" term ","
    "r_pos" ":=" term :
  tactic

/-- Closes `IsPolyaFreqSeq (veroneseSectionPolynomial r k P).coeff` from
`pf_coeff : IsPolyaFreqSeq P.coeff`, `r_pos : 0 < r` and `k_lt_r : k < r`. -/
syntax (name := rr_veronese_section_pf_coeff_named)
  "rr_veronese_section_pf_coeff" " using "
    "pf_coeff" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

/-- Closes `veroneseSectionPolynomial r k P = 0 ∨ (veroneseSectionPolynomial r k P).Splits` from
`pf_coeff : IsPolyaFreqSeq P.coeff`, `r_pos` and `k_lt_r`. -/
syntax (name := rr_veronese_section_splits_pf_named)
  "rr_veronese_section_splits_pf" " using "
    "pf_coeff" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

/-- Closes `veroneseSectionPolynomial r k P = 0 ∨ (veroneseSectionPolynomial r k P).Splits` from
`nonneg : HasNonnegCoeffs P`, `splits : P.Splits`, `r_pos` and `k_lt_r`. -/
syntax (name := rr_veronese_section_splits_nonneg_named)
  "rr_veronese_section_splits_nonneg" " using "
    "nonneg" ":=" term ","
    "splits" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

/-- Sequence form of `rr_veronese_section_nonneg`: the same certificate for every index `n`. -/
syntax (name := rr_veronese_section_sequence_nonneg_named)
  "rr_veronese_section_sequence_nonneg" " using "
    "nonneg" ":=" term ","
    "r_pos" ":=" term :
  tactic

/-- Sequence form of `rr_veronese_section_pf_coeff`: the same certificate for every index `n`. -/
syntax (name := rr_veronese_section_sequence_pf_coeff_named)
  "rr_veronese_section_sequence_pf_coeff" " using "
    "pf_coeff" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

/-- Sequence form of `rr_veronese_section_splits_pf`: the same certificate for every index `n`. -/
syntax (name := rr_veronese_section_sequence_splits_pf_named)
  "rr_veronese_section_sequence_splits_pf" " using "
    "pf_coeff" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

/-- Sequence form of
`rr_veronese_section_splits_nonneg`: the same certificate for every index `n`. -/
syntax (name := rr_veronese_section_sequence_splits_nonneg_named)
  "rr_veronese_section_sequence_splits_nonneg" " using "
    "nonneg" ":=" term ","
    "splits" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_veronese_section_nonneg using
        nonneg := $hp:term,
        r_pos := $hr:term) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_veroneseSectionPolynomial $hr $hp)
  | `(tactic|
      rr_veronese_section_pf_coeff using
        pf_coeff := $hp:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact RealRooted.isPolyaFreqSeq_veroneseSectionPolynomial_coeff
          $hp $hr $hk)
  | `(tactic|
      rr_veronese_section_splits_pf using
        pf_coeff := $hp:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact RealRooted.splits_veroneseSectionPolynomial_of_pf $hp $hr $hk)
  | `(tactic|
      rr_veronese_section_splits_nonneg using
        nonneg := $hpnn:term,
        splits := $hsplits:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact
          RealRooted.splits_veroneseSectionPolynomial_of_splits_nonneg
            $hpnn $hsplits $hr $hk)
  | `(tactic|
      rr_veronese_section_sequence_nonneg using
        nonneg := $hp:term,
        r_pos := $hr:term) =>
      `(tactic|
        exact RealRooted.hasNonnegCoeffs_veroneseSectionPolynomial_sequence
          $hp $hr)
  | `(tactic|
      rr_veronese_section_sequence_pf_coeff using
        pf_coeff := $hp:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact RealRooted.isPolyaFreqSeq_veroneseSectionPolynomial_coeff_sequence
          $hp $hr $hk)
  | `(tactic|
      rr_veronese_section_sequence_splits_pf using
        pf_coeff := $hp:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact RealRooted.veroneseSectionPolynomial_sequence_zero_or_splits_of_pf $hp $hr $hk)
  | `(tactic|
      rr_veronese_section_sequence_splits_nonneg using
        nonneg := $hpnn:term,
        splits := $hsplits:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact
          RealRooted.veroneseSectionPolynomial_sequence_zero_or_splits_of_nonneg
            $hpnn $hsplits $hr $hk)

end Tactic
end RealRooted
