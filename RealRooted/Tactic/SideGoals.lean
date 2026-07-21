import RealRooted.Derivative
import RealRooted.WagnerX
import RealRooted.Tactic.Attr
import Mathlib.Tactic

/-!
# Side-goal tactic

The tactic

```lean
rr_side
```

tries the small, stable automation steps that repeatedly occur after applying
a recurrence-preservation theorem.

Initial scope:

- polynomial evaluation simplification;
- recurrence and degree rewrites from explicit certificates;
- arithmetic by `norm_num`, `positivity`, `lia`, and `nlinarith`;
- polynomial identities by `ring` or `ring_nf`;
- final local cleanup by `simp_all` and `grind`.

This tactic should fail clearly when a mathematical certificate is missing.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_side_nonneg) "rr_side_nonneg" : tactic
syntax (name := rr_side_pos) "rr_side_pos" : tactic
syntax (name := rr_side_ne) "rr_side_ne" : tactic
syntax (name := rr_side_nonneg_seq) "rr_side_nonneg_seq" : tactic
syntax (name := rr_side_pos_seq) "rr_side_pos_seq" : tactic
syntax (name := rr_side_ne_seq) "rr_side_ne_seq" : tactic
syntax (name := rr_positivity_seq) "rr_positivity_seq" : tactic
syntax (name := rr_coeff_simp) "rr_coeff_simp" : tactic
syntax (name := rr_coeff) "rr_coeff" : tactic
syntax (name := rr_nonneg_coeffs) "rr_nonneg_coeffs" : tactic
syntax (name := rr_nonneg_coeffs_using_one)
  "rr_nonneg_coeffs" " using " term : tactic
syntax (name := rr_nonneg_coeffs_using_two)
  "rr_nonneg_coeffs" " using " term "," term : tactic
syntax (name := rr_nonneg_coeffs_using_three)
  "rr_nonneg_coeffs" " using " term "," term "," term : tactic
syntax (name := rr_nonneg_coeffs_zero) "rr_nonneg_coeffs_zero" : tactic
syntax (name := rr_nonneg_coeffs_one) "rr_nonneg_coeffs_one" : tactic
syntax (name := rr_nonneg_coeffs_C)
  "rr_nonneg_coeffs_C" " using " "scalar_nonneg" ":=" term : tactic
syntax (name := rr_nonneg_coeffs_X) "rr_nonneg_coeffs_X" : tactic
syntax (name := rr_nonneg_coeffs_X_add_C)
  "rr_nonneg_coeffs_X_add_C" " using " "scalar_nonneg" ":=" term : tactic
syntax (name := rr_nonneg_coeffs_X_sub_C)
  "rr_nonneg_coeffs_X_sub_C" " using " "root_nonpos" ":=" term : tactic
syntax (name := rr_nonneg_coeffs_C_mul)
  "rr_nonneg_coeffs_C_mul" " using "
    "scalar_nonneg" ":=" term "," "poly_nonneg" ":=" term : tactic
syntax (name := rr_nonneg_coeffs_X_mul)
  "rr_nonneg_coeffs_X_mul" " using " "poly_nonneg" ":=" term : tactic
syntax (name := rr_nonneg_coeffs_add)
  "rr_nonneg_coeffs_add" " using " "left" ":=" term "," "right" ":=" term : tactic
syntax (name := rr_nonneg_coeffs_mul)
  "rr_nonneg_coeffs_mul" " using " "left" ":=" term "," "right" ":=" term : tactic
syntax (name := rr_nonneg_coeffs_pow)
  "rr_nonneg_coeffs_pow" " using " "poly_nonneg" ":=" term "," "exponent" ":=" term :
    tactic
syntax (name := rr_pos_lc_auto) "rr_pos_lc" : tactic
syntax (name := rr_pos_lc_one) "rr_pos_lc_one" : tactic
syntax (name := rr_pos_lc_from_nonneg)
  "rr_pos_lc" " using " "nonneg" ":=" term "," "nonzero" ":=" term : tactic
syntax (name := rr_pos_lc_from_nonzero)
  "rr_pos_lc" " using " "nonzero" ":=" term : tactic
syntax (name := rr_pos_lc_C_mul)
  "rr_pos_lc_C_mul" " using " "scalar_pos" ":=" term "," "pos_lc" ":=" term : tactic
syntax (name := rr_pos_lc_mul)
  "rr_pos_lc_mul" " using " "left" ":=" term "," "right" ":=" term : tactic
syntax (name := rr_pos_lc_X_mul)
  "rr_pos_lc_X_mul" " using " "pos_lc" ":=" term : tactic
syntax (name := rr_close_side) "rr_close_side" : tactic
syntax (name := rr_side) "rr_side" : tactic
syntax (name := rr_refine_then) "rr_refine_then " term " with " tactic : tactic
syntax (name := rr_recurrence_simpa)
  "rr_recurrence_simpa" " using "
    "recurrence" ":=" term ","
    "certificate" ":=" term :
  tactic
syntax (name := rr_recurrence_degree)
  "rr_recurrence_degree" " using "
    "recurrence" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_positivity_term) "rr_positivity_term" : term
syntax (name := rr_side_pos_term) "rr_side_pos_term" : term
syntax (name := rr_positivity_seq_term) "rr_positivity_seq_term" : term
syntax (name := rr_side_nonneg_seq_term) "rr_side_nonneg_seq_term" : term
syntax (name := rr_side_ne_seq_term) "rr_side_ne_seq_term" : term

macro_rules
  | `(tactic| rr_refine_then $h:term with $tac:tactic) =>
      `(tactic| refine $h <;> $tac)
  | `(tactic| rr_recurrence_simpa using recurrence := $hrec:term, certificate := $h:term) =>
      `(tactic| simpa [← $hrec] using $h)
  | `(tactic| rr_recurrence_degree using recurrence := $hrec:term, degree := $hdeg:term) =>
      `(tactic|
        rw [← $hrec];
        have rr_recurrence_degree_h := $hdeg;
        lia)
  | `(tactic| rr_side_nonneg) =>
      `(tactic|
        first
          | assumption
          | exact_mod_cast (by assumption)
          | (guard_target =~ 0 ≤ (((_ : Nat) : _));
             exact Nat.cast_nonneg _)
          | exact sub_nonneg.mpr (by exact_mod_cast (by assumption))
          | exact sub_nonneg.mpr (by exact_mod_cast (by lia))
          | exact div_nonneg (by positivity) (by
              first
                | exact sub_nonneg.mpr (by exact_mod_cast (by lia))
                | positivity
                | norm_num
                | nlinarith)
          | positivity
          | norm_num
          | nlinarith)
  | `(tactic| rr_side_pos) =>
      `(tactic|
        first
          | assumption
          | exact_mod_cast (by assumption)
          | exact sub_pos.mpr (by exact_mod_cast (by lia))
          | positivity
          | norm_num
          | nlinarith)
  | `(tactic| rr_side_ne) =>
      `(tactic|
        first
          | assumption
          | exact_mod_cast (by assumption)
          | apply Nat.cast_ne_zero_of_pos
            rr_close_side
          | apply Nat.cast_choose_ne_zero
            rr_close_side
          | apply neg_ne_zero.mpr
            exact ne_of_gt rr_side_pos_term
          | apply pow_ne_zero
            rr_side_ne
          | (guard_target =~ ((_ : ℝ) / (_ : ℝ)) ≠ 0;
             exact div_ne_zero (by rr_side_ne) (by rr_side_ne))
          | (guard_target =~ ((_ : ℂ) / (_ : ℂ)) ≠ 0;
             exact div_ne_zero (by rr_side_ne) (by rr_side_ne))
          | (guard_target =~ ((_ : ℝ)⁻¹) ≠ 0;
             exact inv_ne_zero (by rr_side_ne))
          | (guard_target =~ ((_ : ℂ)⁻¹) ≠ 0;
             exact inv_ne_zero (by rr_side_ne))
          | positivity
          | norm_num
          | exact ne_of_gt rr_side_pos_term
          | apply ne_of_gt
            positivity
          | apply ne_of_lt
            nlinarith)
  | `(tactic| rr_side_nonneg_seq) =>
      `(tactic| intro n <;> rr_side_nonneg)
  | `(tactic| rr_side_pos_seq) =>
      `(tactic| intro n <;> rr_side_pos)
  | `(tactic| rr_side_ne_seq) =>
      `(tactic| intro n <;> rr_side_ne)
  | `(tactic| rr_positivity_seq) =>
      `(tactic| intro n <;> positivity)
  | `(tactic| rr_coeff_simp) =>
      `(tactic|
        simp (discharger := decide) only [
          Polynomial.coeff_add,
          Polynomial.coeff_sub,
          Polynomial.coeff_neg,
          Polynomial.coeff_smul,
          Polynomial.coeff_C_mul,
          Polynomial.coeff_mul_C,
          Polynomial.coeff_natCast_mul,
          Polynomial.coeff_mul_natCast,
          Polynomial.coeff_ofNat_mul,
          Polynomial.coeff_mul_ofNat,
          Polynomial.coeff_intCast_mul,
          Polynomial.coeff_mul_intCast,
          Polynomial.coeff_C,
          Polynomial.coeff_X,
          Polynomial.coeff_X_pow,
          Polynomial.coeff_X_pow_self,
          Polynomial.coeff_X_mul,
          Polynomial.coeff_X_mul_zero,
          Polynomial.coeff_mul_X,
          Polynomial.coeff_mul_X_zero,
          Polynomial.coeff_derivative,
          Polynomial.coeff_one,
          Polynomial.coeff_zero,
          Polynomial.C_add,
          Polynomial.C_sub,
          Polynomial.C_neg,
          Polynomial.C_mul,
          Polynomial.C_1,
          Polynomial.C_0,
          Polynomial.C_ofNat,
          add_zero,
          zero_add,
          sub_zero,
          zero_sub,
          one_mul,
          mul_one,
          zero_mul,
          mul_zero,
          neg_zero,
          Nat.succ_ne_zero,
          Nat.succ.injEq])
  | `(tactic| rr_coeff) =>
      `(tactic|
        (rr_coeff_simp
          <;> try norm_num
          <;> try ring_nf
          <;> try rr_coeff_simp
          <;> try norm_num
          <;> try ring_nf))
  | `(tactic| rr_nonneg_coeffs_zero) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_zero)
  | `(tactic| rr_nonneg_coeffs_one) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_one)
  | `(tactic| rr_nonneg_coeffs_C using scalar_nonneg := $ha:term) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_C $ha)
  | `(tactic| rr_nonneg_coeffs_X) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_X)
  | `(tactic| rr_nonneg_coeffs_X_add_C using scalar_nonneg := $ha:term) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_X_add_C $ha)
  | `(tactic| rr_nonneg_coeffs_X_sub_C using root_nonpos := $hr:term) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_X_sub_C $hr)
  | `(tactic|
      rr_nonneg_coeffs_C_mul using scalar_nonneg := $ha:term, poly_nonneg := $hp:term) =>
      `(tactic|
        first
          | exact RealRooted.nonnegCoeffs_C_mul $ha $hp
          | simpa [mul_comm] using RealRooted.nonnegCoeffs_C_mul $ha $hp)
  | `(tactic| rr_nonneg_coeffs_X_mul using poly_nonneg := $hp:term) =>
      `(tactic|
        first
          | exact RealRooted.HasNonnegCoeffs.X_mul $hp
          | simpa [mul_comm] using RealRooted.HasNonnegCoeffs.X_mul $hp)
  | `(tactic| rr_nonneg_coeffs_add using left := $hp:term, right := $hq:term) =>
      `(tactic|
        first
          | exact RealRooted.HasNonnegCoeffs.add $hp $hq
          | simpa [add_comm] using RealRooted.HasNonnegCoeffs.add $hq $hp)
  | `(tactic| rr_nonneg_coeffs_mul using left := $hp:term, right := $hq:term) =>
      `(tactic|
        first
          | exact RealRooted.HasNonnegCoeffs.mul $hp $hq
          | simpa [mul_comm] using RealRooted.HasNonnegCoeffs.mul $hq $hp)
  | `(tactic|
      rr_nonneg_coeffs_pow using poly_nonneg := $hp:term, exponent := $n:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.pow $hp $n)
  | `(tactic| rr_nonneg_coeffs using $h:term) =>
      `(tactic|
        have rr_nonneg_coeffs_h := ($h);
        rr_nonneg_coeffs)
  | `(tactic| rr_nonneg_coeffs using $h1:term, $h2:term) =>
      `(tactic|
        have rr_nonneg_coeffs_h1 := ($h1);
        have rr_nonneg_coeffs_h2 := ($h2);
        rr_nonneg_coeffs)
  | `(tactic| rr_nonneg_coeffs using $h1:term, $h2:term, $h3:term) =>
      `(tactic|
        have rr_nonneg_coeffs_h1 := ($h1);
        have rr_nonneg_coeffs_h2 := ($h2);
        have rr_nonneg_coeffs_h3 := ($h3);
        rr_nonneg_coeffs)
  | `(tactic| rr_nonneg_coeffs) =>
      `(tactic|
        first
          | assumption
          | exact RealRooted.hasNonnegCoeffs_zero
          | exact RealRooted.hasNonnegCoeffs_one
          | exact RealRooted.hasNonnegCoeffs_X
          | apply RealRooted.hasNonnegCoeffs_C
            rr_side_nonneg
          | apply RealRooted.hasNonnegCoeffs_X_add_C
            rr_side_nonneg
          | apply RealRooted.hasNonnegCoeffs_X_sub_C
            rr_close_side
          | apply RealRooted.HasNonnegCoeffs.derivative
            rr_nonneg_coeffs
          | apply RealRooted.nonnegCoeffs_C_mul
            · rr_side_nonneg
            · rr_nonneg_coeffs
          | apply RealRooted.HasNonnegCoeffs.X_mul
            rr_nonneg_coeffs
          | apply RealRooted.HasNonnegCoeffs.add <;> rr_nonneg_coeffs
          | apply RealRooted.HasNonnegCoeffs.mul <;> rr_nonneg_coeffs
          | apply RealRooted.HasNonnegCoeffs.pow
            rr_nonneg_coeffs)
  | `(tactic| rr_pos_lc_one) =>
      `(tactic| exact RealRooted.hasPosLeadingCoeff_one)
  | `(tactic| rr_pos_lc using nonneg := $hnn:term, nonzero := $hp0:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.pos_leadingCoeff $hnn $hp0)
  | `(tactic| rr_pos_lc using nonzero := $hp0:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.pos_leadingCoeff (by rr_nonneg_coeffs) $hp0)
  | `(tactic| rr_pos_lc_C_mul using scalar_pos := $ha:term, pos_lc := $hp:term) =>
      `(tactic|
        first
          | exact RealRooted.hasPosLeadingCoeff_C_mul $ha $hp
          | simpa [mul_comm] using RealRooted.hasPosLeadingCoeff_C_mul $ha $hp)
  | `(tactic| rr_pos_lc_mul using left := $hp:term, right := $hq:term) =>
      `(tactic|
        first
          | exact RealRooted.HasPosLeadingCoeff.mul $hp $hq
          | simpa [mul_comm] using RealRooted.HasPosLeadingCoeff.mul $hq $hp)
  | `(tactic| rr_pos_lc_X_mul using pos_lc := $hp:term) =>
      `(tactic|
        first
          | exact RealRooted.HasPosLeadingCoeff.X_mul $hp
          | simpa [mul_comm] using RealRooted.HasPosLeadingCoeff.X_mul $hp)
  | `(tactic| rr_pos_lc) =>
      `(tactic|
        first
          | assumption
          | exact RealRooted.hasPosLeadingCoeff_one
          | apply RealRooted.hasPosLeadingCoeff_C_mul
            · rr_side_pos
            · rr_pos_lc
          | apply RealRooted.HasPosLeadingCoeff.X_mul
            rr_pos_lc
          | apply RealRooted.HasPosLeadingCoeff.derivative
            · rr_pos_lc
            · rr_close_side
          | apply RealRooted.HasPosLeadingCoeff.mul <;> rr_pos_lc
          | exact RealRooted.hasPosLeadingCoeff_add_of_natDegree_lt_left
              (by assumption) (by rr_pos_lc)
          | exact RealRooted.hasPosLeadingCoeff_add_of_natDegree_lt_right
              (by assumption) (by rr_pos_lc)
          | exact RealRooted.hasPosLeadingCoeff_add_of_same_natDegree
              (by assumption) (by rr_pos_lc) (by rr_pos_lc)
          | apply RealRooted.HasNonnegCoeffs.pos_leadingCoeff
            · rr_nonneg_coeffs
            · rr_close_side
          | unfold RealRooted.HasPosLeadingCoeff
            simp <;> try rr_side_pos)
  | `(tactic| rr_close_side) =>
      `(tactic|
        first
          | assumption
          | exact_mod_cast (by assumption)
          | positivity <;> done
          | norm_num <;> done
          | rr_coeff <;> done
          | ring_nf <;> done
          | ring <;> done
          | lia
          | nlinarith
          | simp_all [
              Polynomial.eval_add,
              Polynomial.eval_sub,
              Polynomial.eval_mul,
              Polynomial.eval_pow,
              Polynomial.eval_C,
              Polynomial.eval_X] <;> done
          | grind)
  | `(tactic| rr_side) =>
      `(tactic|
        first
          | positivity
          | norm_num
          | rr_coeff
          | ring_nf
          | ring
          | lia
          | nlinarith
          | simp_all [
              Polynomial.eval_add,
              Polynomial.eval_sub,
              Polynomial.eval_mul,
              Polynomial.eval_pow,
              Polynomial.eval_C,
              Polynomial.eval_X]
          | grind)
  | `(rr_positivity_term) =>
      `(by positivity)
  | `(rr_side_pos_term) =>
      `(by rr_side_pos)
  | `(rr_positivity_seq_term) =>
      `(by rr_positivity_seq)
  | `(rr_side_nonneg_seq_term) =>
      `(by rr_side_nonneg_seq)
  | `(rr_side_ne_seq_term) =>
      `(by rr_side_ne_seq)

end Tactic
end RealRooted
