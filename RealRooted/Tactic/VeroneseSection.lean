import RealRooted.VeroneseSection

/-!
# Veronese-section tactic frontends

Thin wrappers for the fixed-section and pairwise Veronese APIs in
`RealRooted.VeroneseSection`.  Bridge theorems such as the Lace-to-polynomial
steps remain explicit supplied certificates.
-/

open Polynomial

namespace RealRooted
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
    "asw" ":=" term ","
    "pf_coeff" ":=" term ","
    "r_pos" ":=" term ","
    "k_lt_r" ":=" term :
  tactic

syntax (name := rr_veronese_section_splits_nonneg_named)
  "rr_veronese_section_splits_nonneg" " using "
    "asw" ":=" term ","
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
        asw := $hASW:term,
        pf_coeff := $hp:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact RealRooted.veroneseSectionPolynomial_eq_zero_or_isRealRooted_of_pf
          $hASW $hp $hr $hk)
  | `(tactic|
      rr_veronese_section_splits_nonneg using
        asw := $hASW:term,
        nonneg := $hpnn:term,
        splits := $hsplits:term,
        r_pos := $hr:term,
        k_lt_r := $hk:term) =>
      `(tactic|
        exact
          RealRooted.veroneseSectionPolynomial_eq_zero_or_isRealRooted_of_realRooted_nonneg
            $hASW $hpnn $hsplits $hr $hk)
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

end Tactic
end RealRooted
