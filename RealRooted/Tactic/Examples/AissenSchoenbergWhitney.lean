import RealRooted.Tactic.AissenSchoenbergWhitney

open Polynomial

namespace RealRooted
namespace Tactic

example {p : ℝ[X]} (hpf : IsPolyaFreqSeq p.coeff) :
    p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  rr_asw_forward using pf_coeff := hpf

example {p : ℝ[X]} (hpf : IsPolyaFreqSeq p.coeff) :
    p.Splits := by
  rr_asw_splits using pf_coeff := hpf

example {p : ℝ[X]} (hpf : IsPolyaFreqSeq p.coeff) :
    (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  rr_asw_forward_or_zero using pf_coeff := hpf

example {p : ℝ[X]}
    (hp0 : p ≠ 0)
    (hpf : IsPolyaFreqSeq p.coeff) :
    (p ≠ 0 ∧ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  rr_asw_forward_nonzero using
    nonzero := hp0,
    pf_coeff := hpf

example {p : ℝ[X]} (hpf : IsPolyaFreqSeq p.coeff) :
    IsPFPolynomial p := by
  rr_asw_pf_polynomial using pf_coeff := hpf

end Tactic
end RealRooted
