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

example {r k : ℕ} {p : ℝ[X]}
    (hp : IsPolyaFreqSeq p.coeff) (hr : 0 < r) (hk : k < r) :
    veroneseSectionPolynomial r k p = 0 ∨
      (veroneseSectionPolynomial r k p).Splits := by
  rr_veronese_section_splits_pf using
    pf_coeff := hp,
    r_pos := hr,
    k_lt_r := hk

example {r k : ℕ} {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hsplits : p.Splits)
    (hr : 0 < r) (hk : k < r) :
    veroneseSectionPolynomial r k p = 0 ∨
      (veroneseSectionPolynomial r k p).Splits := by
  rr_veronese_section_splits_nonneg using
    nonneg := hpnn,
    splits := hsplits,
    r_pos := hr,
    k_lt_r := hk

example {p q : ℝ[X]} {r k : ℕ}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
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
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
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
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
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
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
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
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
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
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
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

example {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hr : ∀ n : Nat, 0 < r n) :
    ∀ n : Nat, HasNonnegCoeffs (veroneseSectionPolynomial (r n) (k n) (P n)) := by
  rr_veronese_section_sequence_nonneg using
    nonneg := hnn,
    r_pos := hr

example {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hpf : ∀ n : Nat, IsPolyaFreqSeq (P n).coeff)
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat,
      IsPolyaFreqSeq (veroneseSectionPolynomial (r n) (k n) (P n)).coeff := by
  rr_veronese_section_sequence_pf_coeff using
    pf_coeff := hpf,
    r_pos := hr,
    k_lt_r := hk

example {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hpf : ∀ n : Nat, IsPolyaFreqSeq (P n).coeff)
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat,
      veroneseSectionPolynomial (r n) (k n) (P n) = 0 ∨
        (veroneseSectionPolynomial (r n) (k n) (P n)).Splits := by
  rr_veronese_section_sequence_splits_pf using
    pf_coeff := hpf,
    r_pos := hr,
    k_lt_r := hk

example {r k : Nat → Nat} {P : Nat → ℝ[X]}
    (hnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hsplits : ∀ n : Nat, (P n).Splits)
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat,
      veroneseSectionPolynomial (r n) (k n) (P n) = 0 ∨
        (veroneseSectionPolynomial (r n) (k n) (P n)).Splits := by
  rr_veronese_section_sequence_splits_nonneg using
    nonneg := hnn,
    splits := hsplits,
    r_pos := hr,
    k_lt_r := hk

example {r k : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat, Prec0
      (veroneseSectionPolynomial (r n) (k n) (P n))
      (veroneseSectionPolynomial (r n) (k n) (Q n)) := by
  rr_veronese_section_sequence_prec0 using
    prec_to_full := hPrecToFull,
    full_to_prec0 := hFullToPrec0,
    prec := hpq,
    r_pos := hr,
    k_lt_r := hk

example {r k : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (hk : ∀ n : Nat, k n < r n) :
    ∀ n : Nat, Prec
      (veroneseSectionPolynomial (r n) (k n) (P n))
      (veroneseSectionPolynomial (r n) (k n) (Q n)) := by
  rr_veronese_section_sequence_prec using
    prec_to_full := hPrecToFull,
    full_to_prec := hFullToPrec,
    prec := hpq,
    r_pos := hr,
    k_lt_r := hk

example {r i j : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (hij : ∀ n : Nat, i n < j n)
    (hj : ∀ n : Nat, j n < 2 * r n) :
    ∀ n : Nat, Prec0
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (i n))
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (j n)) := by
  rr_veronese_pair_sequence_prec0 using
    prec_to_full := hPrecToFull,
    full_to_prec0 := hFullToPrec0,
    prec := hpq,
    r_pos := hr,
    index_lt := hij,
    right_lt_bound := hj

example {r i j : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (hij : ∀ n : Nat, i n < j n)
    (hj : ∀ n : Nat, j n < 2 * r n) :
    ∀ n : Nat, Prec
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (i n))
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (j n)) := by
  rr_veronese_pair_sequence_prec using
    prec_to_full := hPrecToFull,
    full_to_prec := hFullToPrec,
    prec := hpq,
    r_pos := hr,
    index_lt := hij,
    right_lt_bound := hj

example {r : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (i j : ∀ n : Nat, Fin (2 * r n))
    (hij : ∀ n : Nat, i n < j n) :
    ∀ n : Nat, Prec0
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (i n))
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (j n)) := by
  rr_veronese_pair_fin_sequence_prec0 using
    prec_to_full := hPrecToFull,
    full_to_prec0 := hFullToPrec0,
    prec := hpq,
    r_pos := hr,
    left := i,
    right := j,
    index_lt := hij

example {r : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hPrecToFull : LegacyPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : ∀ n : Nat, Prec (P n) (Q n))
    (hr : ∀ n : Nat, 0 < r n)
    (i j : ∀ n : Nat, Fin (2 * r n))
    (hij : ∀ n : Nat, i n < j n) :
    ∀ n : Nat, Prec
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (i n))
      (veronesePairSectionPolynomial (r n) (P n) (Q n) (j n)) := by
  rr_veronese_pair_fin_sequence_prec using
    prec_to_full := hPrecToFull,
    full_to_prec := hFullToPrec,
    prec := hpq,
    r_pos := hr,
    left := i,
    right := j,
    index_lt := hij

end Tactic
end RealRooted
