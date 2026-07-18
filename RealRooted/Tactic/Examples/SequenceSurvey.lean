import RealRooted.CombinatorialExamples
import RealRooted.Tactic.Finish

/-!
# Sequence survey for tactic development

Representative checks against the currently formalized combinatorial sequence
families.  These examples document what the tactic layer can already consume:
once a family-specific `Prec` or `Interlaces` certificate is available, the
short proof tail should be automatic.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example (n : Nat) :
    Interlaces (touchard n) (touchard (n + 1)) := by
  have hdeg : (touchard n).natDegree + 1 = (touchard (n + 1)).natDegree := by
    simp [natDegree_touchard]
  rr_finish using prec_touchard_succ n, hdeg

example (n : Nat) :
    stirlingPermutations (n + 1) ≠ 0 ∧ (stirlingPermutations (n + 1)).Splits := by
  rr_finish using prec_stirlingPermutations_succ n

example (n : Nat) :
    Interlaces (typeBEulerian n) (typeBEulerian (n + 1)) := by
  have hdeg : (typeBEulerian n).natDegree + 1 = (typeBEulerian (n + 1)).natDegree := by
    simp [natDegree_typeBEulerian]
  rr_finish using prec_typeBEulerian_succ n, hdeg

example (c m n : Nat) :
    coloredSetPartitions c m (n + 1) ≠ 0 ∧
      (coloredSetPartitions c m (n + 1)).Splits := by
  rr_finish using prec_coloredSetPartitions_succ c m n

example (n : Nat) :
    typeBSetPartitions (n + 1) ≠ 0 ∧ (typeBSetPartitions (n + 1)).Splits := by
  rr_finish using prec_coloredSetPartitions_succ 1 2 n

example (n : Nat) :
    eulerianTilde (n + 1) ≠ 0 ∧ (eulerianTilde (n + 1)).Splits := by
  rr_finish using prec_eulerianTilde_succ n

example (n : Nat) :
    motzkin (n + 1) ≠ 0 ∧ (motzkin (n + 1)).Splits := by
  rr_finish using prec_motzkin_succ n

example (n : Nat) :
    simsun (n + 1) ≠ 0 ∧ (simsun (n + 1)).Splits := by
  rr_finish using prec_simsun_succ n

example (n : Nat) (hn : 2 ≤ n) :
    singletonFreeSetPartitions (n + 1) ≠ 0 ∧
      (singletonFreeSetPartitions (n + 1)).Splits := by
  rr_finish using prec_singletonFreeSetPartitions_succ n hn

example (n : Nat) (hn : 2 ≤ n) :
    sturmDerangementsExc (n + 1) ≠ 0 ∧ (sturmDerangementsExc (n + 1)).Splits := by
  rr_finish using prec_sturmDerangementsExc_succ n hn

example (n : Nat) (hn : 1 ≤ n)
    (hnonneg : ∀ m : Nat, HasNonnegCoeffs (narayanaQuot m)) :
    Interlaces (narayanaQuot n) (narayanaQuot (n + 1)) := by
  have hprec : Prec (narayanaQuot n) (narayanaQuot (n + 1)) :=
    prec_narayanaQuot_succ_of_nonnegCoeffs n hn hnonneg
  have hdeg :
      (narayanaQuot n).natDegree + 1 = (narayanaQuot (n + 1)).natDegree := by
    rw [natDegree_narayanaQuot (n + 1) (by lia), natDegree_narayanaQuot n hn]
    lia
  rr_finish using hprec, hdeg

example (n : Nat) (hn : 1 ≤ n)
    (hnonneg : ∀ m : Nat, HasNonnegCoeffs (narayanaQuot m)) :
    narayana (n + 1) ≠ 0 ∧ (narayana (n + 1)).Splits := by
  rr_finish using interlaces_narayana_succ_of_nonnegCoeffs n hn hnonneg

example (m j : Nat) (hj : j < m) :
    oneDescentGamma 1 m j ≠ 0 ∧ (oneDescentGamma 1 m j).Splits := by
  rr_finish using oneDescent_prec_gamma_one_adjacent_chain m j hj

example (m : Nat) (hm : 0 < m) :
    oneDescentQ 1 m ≠ 0 ∧ (oneDescentQ 1 m).Splits := by
  rr_finish using oneDescent_prec_gamma_one_terminal_chain m hm

end Tactic
end RealRooted
