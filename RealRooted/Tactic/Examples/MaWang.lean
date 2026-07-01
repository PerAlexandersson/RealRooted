import RealRooted.Tactic.MaWang

/-!
# `rr_ma_wang` examples

Abstract smoke tests for the Ma-Wang dispatcher tactics.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign :
      ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_ma_wang using
    hf, hdegf, hdeg_lo, hdeg_hi, hF_pos, hf_pos, hroot_sign

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign :
      ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_ma_wang_same using
    hf, hdegf, hdeg, hF_pos, hf_pos, hroot_sign

example {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign :
      ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  rr_ma_wang_succ using
    hf, hdegf, hdeg, hF_pos, hf_pos, hroot_sign

end Tactic
end RealRooted
