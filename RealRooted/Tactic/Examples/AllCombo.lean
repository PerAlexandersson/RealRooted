import RealRooted.Tactic.AllCombo

open Polynomial

namespace RealRooted
namespace Tactic

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) (a b : ℝ) :
    (C a * f + C b * g).Splits := by
  rr_all_combo_splits using all_combo := hall, left_scalar := a, right_scalar := b

example {f g p : ℝ[X]} {a b : ℝ}
    (hall : AllComboRealRooted f g)
    (hp : p = C a * f + C b * g) :
    p.Splits := by
  rr_all_combo_splits_of_eq_combo using all_combo := hall, eq_combo := hp

example {f g p : ℝ[X]} {a b : ℝ}
    (hall : AllComboRealRooted f g)
    (hp : p = C a * f + C b * g)
    (hp0 : p ≠ 0) :
    p ≠ 0 ∧ p.Splits := by
  rr_all_combo_ne_zero_and_splits_of_eq_combo using
    all_combo := hall,
    eq_combo := hp,
    nonzero := hp0

example {F G P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hP : ∀ i : Nat, P i = C (a i) * F i + C (b i) * G i) :
    ∀ i : Nat, (P i).Splits := by
  rr_all_combo_sequence_splits_of_eq_combo using all_combo := hall, eq_combo := hP

example {F G P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hP : ∀ i : Nat, P i = C (a i) * F i + C (b i) * G i)
    (hP0 : ∀ i : Nat, P i ≠ 0) :
    ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits := by
  rr_all_combo_sequence_ne_zero_and_splits_of_eq_combo using
    all_combo := hall,
    eq_combo := hP,
    nonzero := hP0

example {f g p q : ℝ[X]} {a b c d : ℝ}
    (hall : AllComboRealRooted f g)
    (hp : p = C a * f + C b * g)
    (hq : q = C c * f + C d * g) :
    AllComboRealRooted p q := by
  rr_all_combo_linear_recombination using
    all_combo := hall,
    left_eq_combo := hp,
    right_eq_combo := hq

example {F G P Q : Nat → ℝ[X]} {a b c d : Nat → ℝ}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hP : ∀ i : Nat, P i = C (a i) * F i + C (b i) * G i)
    (hQ : ∀ i : Nat, Q i = C (c i) * F i + C (d i) * G i) :
    ∀ i : Nat, AllComboRealRooted (P i) (Q i) := by
  rr_all_combo_sequence_linear_recombination using
    all_combo := hall,
    left_eq_combo := hP,
    right_eq_combo := hQ

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) (hf0 : f ≠ 0) :
    f ≠ 0 ∧ f.Splits := by
  rr_all_combo_left_realrooted using all_combo := hall, nonzero := hf0

example {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hF0 : ∀ i : Nat, F i ≠ 0) :
    ∀ i : Nat, F i ≠ 0 ∧ (F i).Splits := by
  rr_all_combo_sequence_left_realrooted using all_combo := hall, nonzero := hF0

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    f.Splits := by
  rr_all_combo_left_splits using all_combo := hall

example {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, (F i).Splits := by
  rr_all_combo_sequence_left_splits using all_combo := hall

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) (hg0 : g ≠ 0) :
    g ≠ 0 ∧ g.Splits := by
  rr_all_combo_right_realrooted using all_combo := hall, nonzero := hg0

example {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hG0 : ∀ i : Nat, G i ≠ 0) :
    ∀ i : Nat, G i ≠ 0 ∧ (G i).Splits := by
  rr_all_combo_sequence_right_realrooted using all_combo := hall, nonzero := hG0

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    g.Splits := by
  rr_all_combo_right_splits using all_combo := hall

example {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, (G i).Splits := by
  rr_all_combo_sequence_right_splits using all_combo := hall

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted g f := by
  rr_all_combo_comm using all_combo := hall

example {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (G i) (F i) := by
  rr_all_combo_sequence_comm using all_combo := hall

example {f g : ℝ[X]} {c : ℝ} (hall : AllComboRealRooted f g) :
    AllComboRealRooted (C c * f) g := by
  rr_all_combo_C_mul_left using all_combo := hall

example {F G : Nat → ℝ[X]} {c : Nat → ℝ}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (C (c i) * F i) (G i) := by
  rr_all_combo_sequence_C_mul_left using scalar := c, all_combo := hall

example {f g : ℝ[X]} {c : ℝ} (hall : AllComboRealRooted f g) :
    AllComboRealRooted f (C c * g) := by
  rr_all_combo_C_mul_right using all_combo := hall

example {F G : Nat → ℝ[X]} {c : Nat → ℝ}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (F i) (C (c i) * G i) := by
  rr_all_combo_sequence_C_mul_right using scalar := c, all_combo := hall

example {d f g : ℝ[X]} (hall : AllComboRealRooted f g) (hd : d.Splits) :
    AllComboRealRooted (d * f) (d * g) := by
  rr_all_combo_mul_common_factor using all_combo := hall, factor_splits := hd

example {D F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hD : ∀ i : Nat, (D i).Splits) :
    ∀ i : Nat, AllComboRealRooted (D i * F i) (D i * G i) := by
  rr_all_combo_sequence_mul_common_factor using
    all_combo := hall,
    factor_splits := hD

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted f.derivative g.derivative := by
  rr_all_combo_derivative using all_combo := hall

example {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, AllComboRealRooted (F i).derivative (G i).derivative := by
  rr_all_combo_sequence_derivative using all_combo := hall

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) (n : ℕ) :
    AllComboRealRooted ((Polynomial.derivative^[n]) f)
      ((Polynomial.derivative^[n]) g) := by
  rr_all_combo_iterate_derivative using all_combo := hall, index := n

example {F G : Nat → ℝ[X]} {K : Nat → ℕ}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat,
      AllComboRealRooted ((Polynomial.derivative^[K i]) (F i))
        ((Polynomial.derivative^[K i]) (G i)) := by
  rr_all_combo_sequence_iterate_derivative using all_combo := hall, index := K

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) {eps : ℝ}
    (heps : 0 < eps) (n : ℕ) :
    AllComboRealRooted (iterateTDeriv eps n f) (iterateTDeriv eps n g) := by
  rr_all_combo_iterateTDeriv using all_combo := hall, eps_pos := heps, index := n

example {F G : Nat → ℝ[X]} {eps : Nat → ℝ} {K : Nat → ℕ}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (heps : ∀ i : Nat, 0 < eps i) :
    ∀ i : Nat,
      AllComboRealRooted (iterateTDeriv (eps i) (K i) (F i))
        (iterateTDeriv (eps i) (K i) (G i)) := by
  rr_all_combo_sequence_iterateTDeriv using
    all_combo := hall,
    eps_pos := heps,
    index := K

example {f g : ℝ[X]} (hall : AllComboRealRooted f g)
    (hne : ∀ {lam μ : ℝ}, 0 < lam → 0 < μ → C lam * f + C μ * g ≠ 0) :
    PosComboRealRooted f g := by
  rr_all_combo_to_pos_combo using all_combo := hall, positive_combos_ne_zero := hne

example {f g : ℝ[X]} (hall : AllComboRealRooted f g)
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : f.natDegree = g.natDegree) :
    PosComboRealRooted f g := by
  rr_all_combo_to_pos_combo_sameDegree using
    all_combo := hall,
    left_pos_lc := hf,
    right_pos_lc := hg,
    degree_eq := hdeg

example {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (F i).natDegree = (G i).natDegree) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := by
  rr_all_combo_sequence_to_pos_combo_sameDegree using
    all_combo := hall,
    left_pos_lc := hF,
    right_pos_lc := hG,
    degree_eq := hdeg

example {f g : ℝ[X]} (hall : AllComboRealRooted f g)
    (hg : HasPosLeadingCoeff g) (hdeg : f.natDegree < g.natDegree) :
    PosComboRealRooted f g := by
  rr_all_combo_to_pos_combo_natDegree_lt using
    all_combo := hall,
    right_pos_lc := hg,
    degree_lt := hdeg

example {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hG : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (F i).natDegree < (G i).natDegree) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := by
  rr_all_combo_sequence_to_pos_combo_natDegree_lt using
    all_combo := hall,
    right_pos_lc := hG,
    degree_lt := hdeg

example {f g : ℝ[X]} (hall : AllComboRealRooted f g)
    (hf : HasPosLeadingCoeff f) (hdeg : g.natDegree < f.natDegree) :
    PosComboRealRooted f g := by
  rr_all_combo_to_pos_combo_natDegree_gt using
    all_combo := hall,
    left_pos_lc := hf,
    degree_gt := hdeg

example {F G : Nat → ℝ[X]}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hF : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hdeg : ∀ i : Nat, (G i).natDegree < (F i).natDegree) :
    ∀ i : Nat, PosComboRealRooted (F i) (G i) := by
  rr_all_combo_sequence_to_pos_combo_natDegree_gt using
    all_combo := hall,
    left_pos_lc := hF,
    degree_gt := hdeg

end Tactic
end RealRooted
