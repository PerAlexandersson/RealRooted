import RealRooted.Tactic.Linear

/-!
# Linear-polynomial tactic examples

Small regression examples for degree-one real-rootedness and interlacing.
-/

open Polynomial

namespace RealRooted
namespace Tactic

@[rr_degree] theorem rr_linear_X_add_two_degree_smoke :
    (X + C (2 : ℝ) : ℝ[X]).natDegree = 1 := by
  compute_degree!

example (r : ℝ) :
    (X - C r : ℝ[X]) ≠ 0 ∧ (X - C r : ℝ[X]).Splits := by
  rr_X_sub_C_realrooted using
    root := r

example {p : ℝ[X]} (hdeg : p.natDegree = 1) :
    p ≠ 0 ∧ p.Splits := by
  rr_degree_one_realrooted using
    degree := hdeg

example :
    (X + C (2 : ℝ) : ℝ[X]) ≠ 0 ∧ (X + C (2 : ℝ) : ℝ[X]).Splits := by
  rr_degree_one_realrooted

example {p : ℝ[X]} (hne : p ≠ 0) (hdeg : p.natDegree ≤ 1) :
    p ≠ 0 ∧ p.Splits := by
  rr_natDegree_le_one_realrooted using
    nonzero := hne,
    degree := hdeg

example {p : ℝ[X]} (hdeg : p.natDegree = 1) :
    Interlaces (1 : ℝ[X]) p := by
  rr_interlaces_one_linear using
    degree := hdeg

example :
    Interlaces (1 : ℝ[X]) (X + C (2 : ℝ) : ℝ[X]) := by
  rr_interlaces_one_linear

example {p : ℝ[X]} {c : ℝ} (hc : c ≠ 0) (hdeg : p.natDegree = 1) :
    Interlaces (C c) p := by
  rr_interlaces_C_linear using
    scalar_ne := hc,
    degree := hdeg

example :
    Interlaces (C (3 : ℝ)) (X + C (2 : ℝ) : ℝ[X]) := by
  rr_interlaces_C_linear using
    scalar_ne := (by norm_num : (3 : ℝ) ≠ 0)

example {f g : ℝ[X]} {a : ℝ} (hfg : Prec f g) (ha : a ≠ 0) :
    Prec (C a * f) g := by
  rr_prec_C_mul_left using
    prec := hfg,
    scalar_ne := ha

example {f g : ℝ[X]} {a : ℝ} (hfg : Prec f g) (ha : a ≠ 0) :
    Prec f (C a * g) := by
  rr_prec_C_mul_right using
    prec := hfg,
    scalar_ne := ha

example {f g : ℝ[X]} {a b : ℝ} (hfg : Prec f g) (ha : a ≠ 0) (hb : b ≠ 0) :
    Prec (C a * f) (C b * g) := by
  rr_prec_C_mul_both using
    prec := hfg,
    left_ne := ha,
    right_ne := hb

example {f g : ℝ[X]} {n : Nat} (hfg : Prec f g) :
    Prec (C ((n : ℝ) + 1) * f) g := by
  rr_prec_C_mul_left using
    prec := hfg

example {f g : ℝ[X]} {n : Nat} (hfg : Prec f g) :
    Prec (C ((n : ℝ) + 1) * f) (C ((n : ℝ) + 2) * g) := by
  rr_prec_C_mul_both using
    prec := hfg

example {f g : ℝ[X]} {a b : ℝ} (hfg : Prec f g) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdeg : (C a * f).natDegree + 1 = (C b * g).natDegree) :
    Interlaces (C a * f) (C b * g) := by
  have hscaled : Prec (C a * f) (C b * g) := by
    rr_prec_C_mul_both using
      prec := hfg,
      left_ne := ha,
      right_ne := hb
  rr_interlaces using hscaled

example {p : ℝ[X]} {a : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) (ha : a ≠ 0) :
    C a * p ≠ 0 ∧ (C a * p).Splits := by
  rr_C_mul_realrooted using
    realrooted := hp,
    scalar_ne := ha

example {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    X * p ≠ 0 ∧ (X * p).Splits := by
  rr_X_mul_realrooted using
    realrooted := hp

end Tactic
end RealRooted
