import RealRooted.Tactic.AllCombo

open Polynomial

namespace RealRooted
namespace Tactic

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) (a b : ℝ) :
    (C a * f + C b * g).Splits := by
  rr_all_combo_splits using all_combo := hall, left_scalar := a, right_scalar := b

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) (hf0 : f ≠ 0) :
    f ≠ 0 ∧ f.Splits := by
  rr_all_combo_left_realrooted using all_combo := hall, nonzero := hf0

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) (hg0 : g ≠ 0) :
    g ≠ 0 ∧ g.Splits := by
  rr_all_combo_right_realrooted using all_combo := hall, nonzero := hg0

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted g f := by
  rr_all_combo_comm using all_combo := hall

example {f g : ℝ[X]} {c : ℝ} (hall : AllComboRealRooted f g) :
    AllComboRealRooted (C c * f) g := by
  rr_all_combo_C_mul_left using all_combo := hall

example {f g : ℝ[X]} {c : ℝ} (hall : AllComboRealRooted f g) :
    AllComboRealRooted f (C c * g) := by
  rr_all_combo_C_mul_right using all_combo := hall

example {d f g : ℝ[X]} (hall : AllComboRealRooted f g) (hd : d.Splits) :
    AllComboRealRooted (d * f) (d * g) := by
  rr_all_combo_mul_common_factor using all_combo := hall, factor_splits := hd

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted f.derivative g.derivative := by
  rr_all_combo_derivative using all_combo := hall

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) (n : ℕ) :
    AllComboRealRooted ((Polynomial.derivative^[n]) f)
      ((Polynomial.derivative^[n]) g) := by
  rr_all_combo_iterate_derivative using all_combo := hall, index := n

example {f g : ℝ[X]} (hall : AllComboRealRooted f g) {eps : ℝ}
    (heps : 0 < eps) (n : ℕ) :
    AllComboRealRooted (iterateTDeriv eps n f) (iterateTDeriv eps n g) := by
  rr_all_combo_iterateTDeriv using all_combo := hall, eps_pos := heps, index := n

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

example {f g : ℝ[X]} (hall : AllComboRealRooted f g)
    (hg : HasPosLeadingCoeff g) (hdeg : f.natDegree < g.natDegree) :
    PosComboRealRooted f g := by
  rr_all_combo_to_pos_combo_natDegree_lt using
    all_combo := hall,
    right_pos_lc := hg,
    degree_lt := hdeg

example {f g : ℝ[X]} (hall : AllComboRealRooted f g)
    (hf : HasPosLeadingCoeff f) (hdeg : g.natDegree < f.natDegree) :
    PosComboRealRooted f g := by
  rr_all_combo_to_pos_combo_natDegree_gt using
    all_combo := hall,
    left_pos_lc := hf,
    degree_gt := hdeg

end Tactic
end RealRooted
