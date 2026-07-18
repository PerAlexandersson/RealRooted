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
syntax (name := rr_side) "rr_side" : tactic

syntax (name := rr_positivity_term) "rr_positivity_term" : term
syntax (name := rr_side_pos_term) "rr_side_pos_term" : term
syntax (name := rr_positivity_seq_term) "rr_positivity_seq_term" : term
syntax (name := rr_side_nonneg_seq_term) "rr_side_nonneg_seq_term" : term
syntax (name := rr_side_ne_seq_term) "rr_side_ne_seq_term" : term

macro_rules
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
  | `(tactic| rr_side) =>
      `(tactic|
        first
          | positivity
          | norm_num
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
