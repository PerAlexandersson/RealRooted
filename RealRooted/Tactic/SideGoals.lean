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
syntax (name := rr_coeff) "rr_coeff" : tactic
syntax (name := rr_side) "rr_side" : tactic
syntax (name := rr_refine_then) "rr_refine_then " term " with " tactic : tactic

syntax (name := rr_positivity_term) "rr_positivity_term" : term
syntax (name := rr_side_pos_term) "rr_side_pos_term" : term
syntax (name := rr_positivity_seq_term) "rr_positivity_seq_term" : term
syntax (name := rr_side_nonneg_seq_term) "rr_side_nonneg_seq_term" : term
syntax (name := rr_side_ne_seq_term) "rr_side_ne_seq_term" : term

macro_rules
  | `(tactic| rr_refine_then $h:term with $tac:tactic) =>
      `(tactic| refine $h <;> $tac)
  | `(tactic| rr_side_nonneg) =>
      `(tactic|
        first
          | assumption
          | exact_mod_cast (by assumption)
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
          | apply neg_ne_zero.mpr
            exact ne_of_gt rr_side_pos_term
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
  | `(tactic| rr_coeff) =>
      `(tactic|
        (simp (discharger := decide) only [
            Polynomial.coeff_add,
            Polynomial.coeff_sub,
            Polynomial.coeff_neg,
            Polynomial.coeff_smul,
            Polynomial.coeff_C_mul,
            Polynomial.coeff_mul_C,
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
            Nat.succ.injEq]
          <;> try norm_num
          <;> try ring_nf))
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
