import RealRooted.VeroneseSection

/-!
# Veronese-section tactic frontends

Thin wrappers for the fixed-section and pairwise Veronese APIs in
`RealRooted.VeroneseSection`.  Bridge theorems such as the Lace-to-polynomial
steps remain explicit supplied certificates.
-/

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
  fun n => IsPolyaFreqSeq_veroneseSectionPolynomial_coeff (hpf n) (hr n) (hk n)

theorem veroneseSectionPolynomial_sequence_zero_or_splits_of_pf
    {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hpf : ∀ n : Nat, IsPolyaFreqSeq (P n).coeff)
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat,
      veroneseSectionPolynomial (r n) (k n) (P n) = 0 ∨
        (veroneseSectionPolynomial (r n) (k n) (P n)).Splits := fun n =>
  veroneseSectionPolynomial_eq_zero_or_isRealRooted_of_pf (hpf n) (hr n) (hk n)

theorem veroneseSectionPolynomial_sequence_zero_or_splits_of_nonneg
    {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hsplits : ∀ n : Nat, (P n).Splits)
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat,
      veroneseSectionPolynomial (r n) (k n) (P n) = 0 ∨
        (veroneseSectionPolynomial (r n) (k n) (P n)).Splits := fun n =>
  veroneseSectionPolynomial_eq_zero_or_isRealRooted_of_realRooted_nonneg
    (hnn n) (hsplits n) (hr n) (hk n)

theorem prec0_veroneseSectionPolynomial_sequence_of_prec
    {r k : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat, Prec0
      (veroneseSectionPolynomial (r n) (k n) (P n))
      (veroneseSectionPolynomial (r n) (k n) (Q n)) := fun n =>
  prec0_veroneseSectionPolynomial_of_prec
    hPrecToFull hFullToPrec0 (hpq n) (hr n) (hk n)

theorem prec_veroneseSectionPolynomial_sequence_of_prec
    {r k : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat, Prec
      (veroneseSectionPolynomial (r n) (k n) (P n))
      (veroneseSectionPolynomial (r n) (k n) (Q n)) := fun n =>
  prec_veroneseSectionPolynomial_of_prec
    hPrecToFull hFullToPrec (hpq n) (hr n) (hk n)

theorem prec0_veronesePairSectionPolynomial_sequence_of_prec
    {r i j : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (hij : ∀ n : Nat, i n < j n)
    (hj : ∀ n : Nat, j n < 2 * r n) :
    ∀ n : Nat, Prec0
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (i n))
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (j n)) := fun n =>
  prec0_veronesePairSectionPolynomial_of_prec
    hPrecToFull hFullToPrec0 (hpq n) (hr n) (hij n) (hj n)

theorem prec_veronesePairSectionPolynomial_sequence_of_prec
    {r i j : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (hij : ∀ n : Nat, i n < j n)
    (hj : ∀ n : Nat, j n < 2 * r n) :
    ∀ n : Nat, Prec
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (i n))
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (j n)) := fun n =>
  prec_veronesePairSectionPolynomial_of_prec
    hPrecToFull hFullToPrec (hpq n) (hr n) (hij n) (hj n)

theorem prec0_veronesePairSectionPolynomial_fin_sequence_of_prec
    {r : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (i j : ∀ n : Nat, Fin (2 * r n))
    (hij : ∀ n : Nat, i n < j n) :
    ∀ n : Nat, Prec0
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (i n))
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (j n)) := fun n =>
  prec0_veronesePairSectionPolynomial_fin_of_prec
    hPrecToFull hFullToPrec0 (hpq n) (hr n) (i n) (j n) (hij n)

theorem prec_veronesePairSectionPolynomial_fin_sequence_of_prec
    {r : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (i j : ∀ n : Nat, Fin (2 * r n))
    (hij : ∀ n : Nat, i n < j n) :
    ∀ n : Nat, Prec
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (i n))
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (j n)) := fun n =>
  prec_veronesePairSectionPolynomial_fin_of_prec
    hPrecToFull hFullToPrec (hpq n) (hr n) (i n) (j n) (hij n)

namespace Tactic

syntax (name := rr_veronese_section_nonneg_named)
  "rr_veronese_section_nonneg" " using "
    "nonneg" ":=" term ","
    "r_pos" ":=" term :
  tactic

syntax (name := rr_veronese_section_pf_coeff_named)
  "rr_veronese_section_pf_coeff" " using "
    "pf_coeff" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

syntax (name := rr_veronese_section_splits_pf_named)
  "rr_veronese_section_splits_pf" " using "
    "pf_coeff" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

syntax (name := rr_veronese_section_splits_nonneg_named)
  "rr_veronese_section_splits_nonneg" " using "
    "nonneg" ":=" term ","
    "splits" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

syntax (name := rr_veronese_section_prec0_named)
  "rr_veronese_section_prec0" " using "
    "prec_to_full" ":=" term ","
    "full_to_prec0" ":=" term ","
    "prec" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

syntax (name := rr_veronese_section_prec_named)
  "rr_veronese_section_prec" " using "
    "prec_to_full" ":=" term ","
    "full_to_prec" ":=" term ","
    "prec" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

syntax (name := rr_veronese_pair_prec0_named)
  "rr_veronese_pair_prec0" " using "
    "prec_to_full" ":=" term ","
    "full_to_prec0" ":=" term ","
    "prec" ":=" term ","
    "r_pos" ":=" term ","
    "index_lt" ":=" term ","
    "right_lt_bound" ":=" term :
  tactic

syntax (name := rr_veronese_pair_prec_named)
  "rr_veronese_pair_prec" " using "
    "prec_to_full" ":=" term ","
    "full_to_prec" ":=" term ","
    "prec" ":=" term ","
    "r_pos" ":=" term ","
    "index_lt" ":=" term ","
    "right_lt_bound" ":=" term :
  tactic

syntax (name := rr_veronese_pair_fin_prec0_named)
  "rr_veronese_pair_fin_prec0" " using "
    "prec_to_full" ":=" term ","
    "full_to_prec0" ":=" term ","
    "prec" ":=" term ","
    "r_pos" ":=" term ","
    "left" ":=" term ","
    "right" ":=" term ","
    "index_lt" ":=" term :
  tactic

syntax (name := rr_veronese_pair_fin_prec_named)
  "rr_veronese_pair_fin_prec" " using "
    "prec_to_full" ":=" term ","
    "full_to_prec" ":=" term ","
    "prec" ":=" term ","
    "r_pos" ":=" term ","
    "left" ":=" term ","
    "right" ":=" term ","
    "index_lt" ":=" term :
  tactic

syntax (name := rr_veronese_section_sequence_nonneg_named)
  "rr_veronese_section_sequence_nonneg" " using "
    "nonneg" ":=" term ","
    "r_pos" ":=" term :
  tactic

syntax (name := rr_veronese_section_sequence_pf_coeff_named)
  "rr_veronese_section_sequence_pf_coeff" " using "
    "pf_coeff" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

syntax (name := rr_veronese_section_sequence_splits_pf_named)
  "rr_veronese_section_sequence_splits_pf" " using "
    "pf_coeff" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

syntax (name := rr_veronese_section_sequence_splits_nonneg_named)
  "rr_veronese_section_sequence_splits_nonneg" " using "
    "nonneg" ":=" term ","
    "splits" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

syntax (name := rr_veronese_section_sequence_prec0_named)
  "rr_veronese_section_sequence_prec0" " using "
    "prec_to_full" ":=" term ","
    "full_to_prec0" ":=" term ","
    "prec" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

syntax (name := rr_veronese_section_sequence_prec_named)
  "rr_veronese_section_sequence_prec" " using "
    "prec_to_full" ":=" term ","
    "full_to_prec" ":=" term ","
    "prec" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

syntax (name := rr_veronese_pair_sequence_prec0_named)
  "rr_veronese_pair_sequence_prec0" " using "
    "prec_to_full" ":=" term ","
    "full_to_prec0" ":=" term ","
    "prec" ":=" term ","
    "r_pos" ":=" term ","
    "index_lt" ":=" term ","
    "right_lt_bound" ":=" term :
  tactic

syntax (name := rr_veronese_pair_sequence_prec_named)
  "rr_veronese_pair_sequence_prec" " using "
    "prec_to_full" ":=" term ","
    "full_to_prec" ":=" term ","
    "prec" ":=" term ","
    "r_pos" ":=" term ","
    "index_lt" ":=" term ","
    "right_lt_bound" ":=" term :
  tactic

syntax (name := rr_veronese_pair_fin_sequence_prec0_named)
  "rr_veronese_pair_fin_sequence_prec0" " using "
    "prec_to_full" ":=" term ","
    "full_to_prec0" ":=" term ","
    "prec" ":=" term ","
    "r_pos" ":=" term ","
    "left" ":=" term ","
    "right" ":=" term ","
    "index_lt" ":=" term :
  tactic

syntax (name := rr_veronese_pair_fin_sequence_prec_named)
  "rr_veronese_pair_fin_sequence_prec" " using "
    "prec_to_full" ":=" term ","
    "full_to_prec" ":=" term ","
    "prec" ":=" term ","
    "r_pos" ":=" term ","
    "left" ":=" term ","
    "right" ":=" term ","
    "index_lt" ":=" term :
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
        exact RealRooted.IsPolyaFreqSeq_veroneseSectionPolynomial_coeff
          $hp $hr $hk)
  | `(tactic|
      rr_veronese_section_splits_pf using
        pf_coeff := $hp:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact RealRooted.veroneseSectionPolynomial_eq_zero_or_isRealRooted_of_pf $hp $hr $hk)
  | `(tactic|
      rr_veronese_section_splits_nonneg using
        nonneg := $hpnn:term,
        splits := $hsplits:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact
          RealRooted.veroneseSectionPolynomial_eq_zero_or_isRealRooted_of_realRooted_nonneg
            $hpnn $hsplits $hr $hk)
  | `(tactic|
      rr_veronese_section_prec0 using
        prec_to_full := $hPrecToFull:term,
        full_to_prec0 := $hFullToPrec0:term,
        prec := $hpq:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact RealRooted.prec0_veroneseSectionPolynomial_of_prec
          $hPrecToFull $hFullToPrec0 $hpq $hr $hk)
  | `(tactic|
      rr_veronese_section_prec using
        prec_to_full := $hPrecToFull:term,
        full_to_prec := $hFullToPrec:term,
        prec := $hpq:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact RealRooted.prec_veroneseSectionPolynomial_of_prec
          $hPrecToFull $hFullToPrec $hpq $hr $hk)
  | `(tactic|
      rr_veronese_pair_prec0 using
        prec_to_full := $hPrecToFull:term,
        full_to_prec0 := $hFullToPrec0:term,
        prec := $hpq:term,
        r_pos := $hr:term,
        index_lt := $hij:term,
        right_lt_bound := $hj:term) =>
      `(tactic|
        exact RealRooted.prec0_veronesePairSectionPolynomial_of_prec
          $hPrecToFull $hFullToPrec0 $hpq $hr $hij $hj)
  | `(tactic|
      rr_veronese_pair_prec using
        prec_to_full := $hPrecToFull:term,
        full_to_prec := $hFullToPrec:term,
        prec := $hpq:term,
        r_pos := $hr:term,
        index_lt := $hij:term,
        right_lt_bound := $hj:term) =>
      `(tactic|
        exact RealRooted.prec_veronesePairSectionPolynomial_of_prec
          $hPrecToFull $hFullToPrec $hpq $hr $hij $hj)
  | `(tactic|
      rr_veronese_pair_fin_prec0 using
        prec_to_full := $hPrecToFull:term,
        full_to_prec0 := $hFullToPrec0:term,
        prec := $hpq:term,
        r_pos := $hr:term,
        left := $i:term,
        right := $j:term,
        index_lt := $hij:term) =>
      `(tactic|
        exact RealRooted.prec0_veronesePairSectionPolynomial_fin_of_prec
          $hPrecToFull $hFullToPrec0 $hpq $hr $i $j $hij)
  | `(tactic|
      rr_veronese_pair_fin_prec using
        prec_to_full := $hPrecToFull:term,
        full_to_prec := $hFullToPrec:term,
        prec := $hpq:term,
        r_pos := $hr:term,
        left := $i:term,
        right := $j:term,
        index_lt := $hij:term) =>
      `(tactic|
        exact RealRooted.prec_veronesePairSectionPolynomial_fin_of_prec
          $hPrecToFull $hFullToPrec $hpq $hr $i $j $hij)
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
  | `(tactic|
      rr_veronese_section_sequence_prec0 using
        prec_to_full := $hPrecToFull:term,
        full_to_prec0 := $hFullToPrec0:term,
        prec := $hpq:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact RealRooted.prec0_veroneseSectionPolynomial_sequence_of_prec
          $hPrecToFull $hFullToPrec0 $hpq $hr $hk)
  | `(tactic|
      rr_veronese_section_sequence_prec using
        prec_to_full := $hPrecToFull:term,
        full_to_prec := $hFullToPrec:term,
        prec := $hpq:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact RealRooted.prec_veroneseSectionPolynomial_sequence_of_prec
          $hPrecToFull $hFullToPrec $hpq $hr $hk)
  | `(tactic|
      rr_veronese_pair_sequence_prec0 using
        prec_to_full := $hPrecToFull:term,
        full_to_prec0 := $hFullToPrec0:term,
        prec := $hpq:term,
        r_pos := $hr:term,
        index_lt := $hij:term,
        right_lt_bound := $hj:term) =>
      `(tactic|
        exact RealRooted.prec0_veronesePairSectionPolynomial_sequence_of_prec
          $hPrecToFull $hFullToPrec0 $hpq $hr $hij $hj)
  | `(tactic|
      rr_veronese_pair_sequence_prec using
        prec_to_full := $hPrecToFull:term,
        full_to_prec := $hFullToPrec:term,
        prec := $hpq:term,
        r_pos := $hr:term,
        index_lt := $hij:term,
        right_lt_bound := $hj:term) =>
      `(tactic|
        exact RealRooted.prec_veronesePairSectionPolynomial_sequence_of_prec
          $hPrecToFull $hFullToPrec $hpq $hr $hij $hj)
  | `(tactic|
      rr_veronese_pair_fin_sequence_prec0 using
        prec_to_full := $hPrecToFull:term,
        full_to_prec0 := $hFullToPrec0:term,
        prec := $hpq:term,
        r_pos := $hr:term,
        left := $i:term,
        right := $j:term,
        index_lt := $hij:term) =>
      `(tactic|
        exact RealRooted.prec0_veronesePairSectionPolynomial_fin_sequence_of_prec
          $hPrecToFull $hFullToPrec0 $hpq $hr $i $j $hij)
  | `(tactic|
      rr_veronese_pair_fin_sequence_prec using
        prec_to_full := $hPrecToFull:term,
        full_to_prec := $hFullToPrec:term,
        prec := $hpq:term,
        r_pos := $hr:term,
        left := $i:term,
        right := $j:term,
        index_lt := $hij:term) =>
      `(tactic|
        exact RealRooted.prec_veronesePairSectionPolynomial_fin_sequence_of_prec
          $hPrecToFull $hFullToPrec $hpq $hr $i $j $hij)

end Tactic
end RealRooted
