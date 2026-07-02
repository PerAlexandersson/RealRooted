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
  rr_interlaces using prec_touchard_succ n, hdeg

example (n : Nat) : touchard (n + 1) ≠ 0 := by
  have hprec : Prec (touchard n) (touchard (n + 1)) := prec_touchard_succ n
  rr_finish

example (n : Nat) : (touchard (n + 1)).Splits := by
  have hprec : Prec (touchard n) (touchard (n + 1)) := prec_touchard_succ n
  rr_finish

example (n : Nat) :
    touchard (n + 1) ≠ 0 ∧ (touchard (n + 1)).Splits := by
  have hprec : Prec (touchard n) (touchard (n + 1)) := prec_touchard_succ n
  rr_finish

end Tactic
end RealRooted
