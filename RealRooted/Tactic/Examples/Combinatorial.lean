import RealRooted.CombinatorialExamples.Touchard
import RealRooted.Tactic.Finish

/-!
# Combinatorial tactic examples

Regression tests against existing combinatorial polynomial families.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example (n : Nat) :
    Interlaces (touchard n) (touchard (n + 1)) := by
  have hdeg : (touchard n).natDegree + 1 = (touchard (n + 1)).natDegree := by
    simp [natDegree_touchard]
  rr_finish using prec_touchard_succ n, hdeg

example (n : Nat) : touchard (n + 1) ≠ 0 := by rr_finish using prec_touchard_succ n

example (n : Nat) : (touchard (n + 1)).Splits := by rr_finish using prec_touchard_succ n

example (n : Nat) :
    touchard (n + 1) ≠ 0 ∧ (touchard (n + 1)).Splits := by
  rr_finish using prec_touchard_succ n

end Tactic
end RealRooted
