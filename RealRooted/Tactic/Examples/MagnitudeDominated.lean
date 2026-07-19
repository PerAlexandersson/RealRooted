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

example {F G1 G2 A B1 B2 : Nat → ℝ[X]}
    (hG1F : ∀ n : Nat, Interlaces (G1 n) (F n))
    (hG1_pos : ∀ n : Nat, HasPosLeadingCoeff (G1 n))
    (hF_pos : ∀ n : Nat,
      HasPosLeadingCoeff (A n * F n + B1 n * G1 n + B2 n * G2 n))
    (hdeg : ∀ n : Nat,
      (A n * F n + B1 n * G1 n + B2 n * G2 n).natDegree =
        (F n).natDegree + 1)
    (hcert : ∀ n : Nat, ∀ r, (F n).IsRoot r →
      (B1 n).eval r * ((G1 n).eval r) ^ 2 +
        (B2 n).eval r * ((G2 n).eval r * (G1 n).eval r) < 0) :
    ∀ n : Nat, Prec (F n) (A n * F n + B1 n * G1 n + B2 n * G2 n) := by
  rr_magnitude_dominated_sequence_succ using
    interlaces := hG1F,
    interlacer_pos_lc := hG1_pos,
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

example {F G1 G2 A B1 B2 : Nat → ℝ[X]}
    (hG1F : ∀ n : Nat, Interlaces (G1 n) (F n))
    (hG1_pos : ∀ n : Nat, HasPosLeadingCoeff (G1 n))
    (hF_pos : ∀ n : Nat,
      HasPosLeadingCoeff (A n * F n + B1 n * G1 n + B2 n * G2 n))
    (hdeg : ∀ n : Nat,
      (A n * F n + B1 n * G1 n + B2 n * G2 n).natDegree =
        (F n).natDegree)
    (hcert : ∀ n : Nat, ∀ r, (F n).IsRoot r →
      (B1 n).eval r * ((G1 n).eval r) ^ 2 +
        (B2 n).eval r * ((G2 n).eval r * (G1 n).eval r) < 0) :
    ∀ n : Nat, Prec (F n) (A n * F n + B1 n * G1 n + B2 n * G2 n) := by
  rr_magnitude_dominated_sequence_same using
    interlaces := hG1F,
    interlacer_pos_lc := hG1_pos,
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

example {F G1 G2 A B1 B2 : Nat → ℝ[X]}
    (hG1F : ∀ n : Nat, Interlaces (G1 n) (F n))
    (hG1_pos : ∀ n : Nat, HasPosLeadingCoeff (G1 n))
    (hF_pos : ∀ n : Nat,
      HasPosLeadingCoeff (A n * F n + B1 n * G1 n + B2 n * G2 n))
    (hdeg_lo : ∀ n : Nat,
      (F n).natDegree ≤ (A n * F n + B1 n * G1 n + B2 n * G2 n).natDegree)
    (hdeg_hi : ∀ n : Nat,
      (A n * F n + B1 n * G1 n + B2 n * G2 n).natDegree ≤
        (F n).natDegree + 1)
    (hcert : ∀ n : Nat, ∀ r, (F n).IsRoot r →
      (B1 n).eval r * ((G1 n).eval r) ^ 2 +
        (B2 n).eval r * ((G2 n).eval r * (G1 n).eval r) < 0) :
    ∀ n : Nat, Prec (F n) (A n * F n + B1 n * G1 n + B2 n * G2 n) := by
  rr_magnitude_dominated_sequence using
    interlaces := hG1F,
    interlacer_pos_lc := hG1_pos,
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

example {B1 G1 B2 G2 : Nat → ℝ[X]}
    (hhead : ∀ n : Nat, ∀ r,
      (B1 n).eval r * ((G1 n).eval r) ^ 2 < 0)
    (hdom : ∀ n : Nat, ∀ r,
      |(B2 n).eval r * ((G2 n).eval r * (G1 n).eval r)| <
        |(B1 n).eval r * ((G1 n).eval r) ^ 2|) :
    ∀ n : Nat, ∀ r,
      (B1 n).eval r * ((G1 n).eval r) ^ 2 +
        (B2 n).eval r * ((G2 n).eval r * (G1 n).eval r) < 0 := by
  rr_magnitude_sequence_cert_abs_dominated using
    head_negative := hhead,
    domination := hdom

end Tactic
end RealRooted
