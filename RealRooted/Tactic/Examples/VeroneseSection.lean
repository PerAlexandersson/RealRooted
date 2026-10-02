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

end Tactic
end RealRooted
