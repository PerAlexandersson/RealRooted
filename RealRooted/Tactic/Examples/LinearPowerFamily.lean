import RealRooted.LinearPowerFamily
import RealRooted.Tactic.Finish

/-!
# Linear-power family tactic examples

Small OEIS-agnostic regression examples for the fixed linear-factor backend.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example (n : Nat) :
    Interlaces ((C (2 : ℝ) + C 3 * X) ^ n)
      ((C (2 : ℝ) + C 3 * X) ^ (n + 1)) := by
  exact interlaces_linear_pow 2 3 (by norm_num) n

example {A : Nat → ℝ[X]}
    (h0 : A 0 = C (1 : ℝ))
    (h1 : A 1 = C (2 : ℝ) + C 3 * X)
    (hstep : ∀ n, A (n + 2) = (C (5 : ℝ) + C 7 * X) * A (n + 1))
    (n : Nat) :
    Interlaces (A n) (A (n + 1)) := by
  exact linear_tail_sequence_interlaces
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    h0 h1 hstep n

example {A : Nat → ℝ[X]}
    (h0 : A 0 = C (1 : ℝ))
    (h1 : A 1 = C (2 : ℝ) + C 3 * X)
    (hstep : ∀ n, A (n + 2) = (C (5 : ℝ) * X) * A (n + 1))
    (n : Nat) :
    Interlaces (A n) (A (n + 1)) := by
  exact monomial_tail_sequence_interlaces
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) h0 h1 hstep n

example {A : Nat → ℝ[X]}
    (h0 : A 0 = C (1 : ℝ))
    (h1 : A 1 = C (2 : ℝ) + C 3 * X)
    (hstep : ∀ n, A (n + 2) = (C (5 : ℝ) + C 7 * X) * A (n + 1))
    (n : Nat) :
    A n ≠ 0 ∧ (A n).Splits := by
  have hprec : ∀ n : Nat, Prec (A n) (A (n + 1)) := fun n =>
    (linear_tail_sequence_interlaces
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      h0 h1 hstep n).toPrec
  exact isRealRooted_of_prec_chain (hprec 0) hprec n

end Tactic
end RealRooted
