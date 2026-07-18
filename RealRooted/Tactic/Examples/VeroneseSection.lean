import RealRooted.Tactic.VeroneseSection

open Polynomial

namespace RealRooted
namespace Tactic

example {r k : ℕ} {p : ℝ[X]} (hp : HasNonnegCoeffs p) (hr : 0 < r) :
    HasNonnegCoeffs (veroneseSectionPolynomial r k p) := by
  rr_veronese_section_nonneg using nonneg := hp, r_pos := hr

example {r k : ℕ} {p : ℝ[X]} (hp : IsPolyaFreqSeq p.coeff)
    (hr : 0 < r) (hk : k < r) :
    IsPolyaFreqSeq (veroneseSectionPolynomial r k p).coeff := by
  rr_veronese_section_pf_coeff using pf_coeff := hp, r_pos := hr, k_lt_r := hk

example {r k : ℕ} {p : ℝ[X]} (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hp : IsPolyaFreqSeq p.coeff) (hr : 0 < r) (hk : k < r) :
    veroneseSectionPolynomial r k p = 0 ∨
      (veroneseSectionPolynomial r k p).Splits := by
  rr_veronese_section_splits_pf using
    asw := hASW,
    pf_coeff := hp,
    r_pos := hr,
    k_lt_r := hk

example {r k : ℕ} {p : ℝ[X]} (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hpnn : HasNonnegCoeffs p) (hsplits : p.Splits)
    (hr : 0 < r) (hk : k < r) :
    veroneseSectionPolynomial r k p = 0 ∨
      (veroneseSectionPolynomial r k p).Splits := by
  rr_veronese_section_splits_nonneg using
    asw := hASW,
    nonneg := hpnn,
    splits := hsplits,
    r_pos := hr,
    k_lt_r := hk

example {p q : ℝ[X]} {r k : ℕ}
    (hPrecToFull : PrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpq : Prec p q) (hr : 0 < r) (hk : k < r) :
    Prec0 (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) := by
  rr_veronese_section_prec0 using
    prec_to_full := hPrecToFull,
    full_to_prec0 := hFullToPrec0,
    prec := hpq,
    r_pos := hr,
    k_lt_r := hk

example {p q : ℝ[X]} {r k : ℕ}
    (hPrecToFull : PrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : Prec p q) (hr : 0 < r) (hk : k < r) :
    Prec (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) := by
  rr_veronese_section_prec using
    prec_to_full := hPrecToFull,
    full_to_prec := hFullToPrec,
    prec := hpq,
    r_pos := hr,
    k_lt_r := hk

example {p q : ℝ[X]} {r i j : ℕ}
    (hPrecToFull : PrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpq : Prec p q) (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    Prec0 (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) := by
  rr_veronese_pair_prec0 using
    prec_to_full := hPrecToFull,
    full_to_prec0 := hFullToPrec0,
    prec := hpq,
    r_pos := hr,
    index_lt := hij,
    right_lt_bound := hj

example {p q : ℝ[X]} {r i j : ℕ}
    (hPrecToFull : PrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : Prec p q) (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    Prec (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) := by
  rr_veronese_pair_prec using
    prec_to_full := hPrecToFull,
    full_to_prec := hFullToPrec,
    prec := hpq,
    r_pos := hr,
    index_lt := hij,
    right_lt_bound := hj

example {p q : ℝ[X]} {r : ℕ}
    (hPrecToFull : PrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpq : Prec p q) (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec0 (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) := by
  rr_veronese_pair_fin_prec0 using
    prec_to_full := hPrecToFull,
    full_to_prec0 := hFullToPrec0,
    prec := hpq,
    r_pos := hr,
    left := i,
    right := j,
    index_lt := hij

example {p q : ℝ[X]} {r : ℕ}
    (hPrecToFull : PrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : Prec p q) (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) := by
  rr_veronese_pair_fin_prec using
    prec_to_full := hPrecToFull,
    full_to_prec := hFullToPrec,
    prec := hpq,
    r_pos := hr,
    left := i,
    right := j,
    index_lt := hij

end Tactic
end RealRooted
