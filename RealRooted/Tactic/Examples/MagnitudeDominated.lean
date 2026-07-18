import RealRooted.Tactic.MagnitudeDominated

open Polynomial

namespace RealRooted
namespace Tactic

example {f g1 g2 a b1 b2 : ℝ[X]}
    (hg1f : Interlaces g1 f)
    (hg1_pos : HasPosLeadingCoeff g1)
    (hF_pos : HasPosLeadingCoeff (a * f + b1 * g1 + b2 * g2))
    (hdeg : (a * f + b1 * g1 + b2 * g2).natDegree = f.natDegree + 1)
    (hcert : ∀ r, f.IsRoot r →
      b1.eval r * (g1.eval r) ^ 2 + b2.eval r * (g2.eval r * g1.eval r) < 0) :
    Prec f (a * f + b1 * g1 + b2 * g2) := by
  rr_magnitude_dominated_succ using
    interlaces := hg1f,
    interlacer_pos_lc := hg1_pos,
    target_pos_lc := hF_pos,
    degree := hdeg,
    certificate := hcert

example {f g1 g2 a b1 b2 : ℝ[X]}
    (hg1f : Interlaces g1 f)
    (hg1_pos : HasPosLeadingCoeff g1)
    (hF_pos : HasPosLeadingCoeff (a * f + b1 * g1 + b2 * g2))
    (hdeg : (a * f + b1 * g1 + b2 * g2).natDegree = f.natDegree)
    (hcert : ∀ r, f.IsRoot r →
      b1.eval r * (g1.eval r) ^ 2 + b2.eval r * (g2.eval r * g1.eval r) < 0) :
    Prec f (a * f + b1 * g1 + b2 * g2) := by
  rr_magnitude_dominated_same using
    interlaces := hg1f,
    interlacer_pos_lc := hg1_pos,
    target_pos_lc := hF_pos,
    degree := hdeg,
    certificate := hcert

example {f g1 g2 a b1 b2 : ℝ[X]}
    (hg1f : Interlaces g1 f)
    (hg1_pos : HasPosLeadingCoeff g1)
    (hF_pos : HasPosLeadingCoeff (a * f + b1 * g1 + b2 * g2))
    (hdeg_lo : f.natDegree ≤ (a * f + b1 * g1 + b2 * g2).natDegree)
    (hdeg_hi : (a * f + b1 * g1 + b2 * g2).natDegree ≤ f.natDegree + 1)
    (hcert : ∀ r, f.IsRoot r →
      b1.eval r * (g1.eval r) ^ 2 + b2.eval r * (g2.eval r * g1.eval r) < 0) :
    Prec f (a * f + b1 * g1 + b2 * g2) := by
  rr_magnitude_dominated using
    interlaces := hg1f,
    interlacer_pos_lc := hg1_pos,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    certificate := hcert

example {b1 g1 b2 g2 : ℝ[X]} {r : ℝ}
    (hhead : b1.eval r * (g1.eval r) ^ 2 < 0)
    (hdom : |b2.eval r * (g2.eval r * g1.eval r)| <
      |b1.eval r * (g1.eval r) ^ 2|) :
    b1.eval r * (g1.eval r) ^ 2 + b2.eval r * (g2.eval r * g1.eval r) < 0 := by
  rr_magnitude_cert_abs_dominated using head_negative := hhead, domination := hdom

end Tactic
end RealRooted
