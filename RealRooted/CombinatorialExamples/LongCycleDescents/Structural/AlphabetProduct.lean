/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Counting
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetTransform
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic

/-!
# Rational alphabet polynomials from the proved necklace model

We identify the finite multiset product with the original permutation alphabet
polynomial by its positive integer evaluations.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

noncomputable section

open Polynomial Finset
open scoped ArithmeticFunction.Moebius

namespace RealRooted.LongCycleDescents.Structural

open Necklace Words

/-- The rational primitive-necklace polynomial. -/
def necklacePolynomial (j : ℕ) : ℚ[X] :=
  C ((j : ℚ)⁻¹) * ∑ d ∈ j.divisors, C (μ d : ℚ) * X ^ (j / d)

/-- The multiset profile alphabet polynomial, with its genuine cutoff. -/
def cycleAlphabet (n k : ℕ) : ℚ[X] :=
  ∑ p : PositiveLengthProfile n k, ∏ i : Fin n,
    Ring.multichoose (necklacePolynomial (i.val + 1)) (p.val i).val

/-- Primitive-necklace evaluation is the already proved integer Möbius count. -/
theorem necklacePolynomial_eval_nat {j : ℕ} (hj : 0 < j) (q : ℕ) :
    (necklacePolynomial j).eval (q : ℚ) = (Fintype.card (PrimitiveNecklace j q) : ℚ) := by
  simp only [necklacePolynomial, eval_mul, eval_C, eval_finsetSum, eval_pow, eval_X]
  have h : (j : ℚ) * (Fintype.card (PrimitiveNecklace j q) : ℚ) =
      ∑ d ∈ j.divisors, (μ d : ℚ) * (q : ℚ) ^ (j / d) := by
    exact_mod_cast card_primitiveNecklace_mul hj q
  rw [← h, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hj.ne'), one_mul]

private theorem multichoose_natCast (q b : ℕ) :
    Ring.multichoose (q : ℚ) b = (Nat.multichoose q b : ℚ) := by
  cases b with
  | zero => simp
  | succ b =>
    rw [Ring.multichoose_eq, Nat.multichoose_eq]
    have he : (q : ℚ) + (b + 1 : ℕ) - 1 = ((q + (b + 1) - 1 : ℕ) : ℚ) := by
      rw [show q + (b + 1) - 1 = q + b by lia]
      push_cast
      ring
    rw [he, Ring.choose_natCast]

/-- The rational product evaluates to the actual necklace-content cardinality. -/
theorem cycleAlphabet_eval_nat (n k q : ℕ) :
    (cycleAlphabet n k).eval (q : ℚ) = (Nat.card (NecklaceContent n q k) : ℚ) := by
  rw [card_necklaceContent_eq_positive_sum]
  push_cast
  simp only [cycleAlphabet, eval_finsetSum]
  apply sum_congr rfl
  intro p _
  rw [eval_prod]
  apply prod_congr rfl
  intro i _
  change (evalRingHom (q : ℚ)) (Ring.multichoose _ _) = _
  rw [Ring.map_multichoose]
  change Ring.multichoose ((necklacePolynomial (i.val + 1)).eval (q : ℚ)) _ = _
  rw [necklacePolynomial_eval_nat (Nat.succ_pos _), multichoose_natCast]

/-- The rational product is faithfully the original permutation alphabet polynomial. -/
theorem map_cycleAlphabet {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (cycleAlphabet n k).map (Rat.castHom ℝ) = descentAlphabetPolynomial n k := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun q : ℕ => ((q + 1 : ℕ) : ℝ)) := by
    intro a b h
    exact Nat.succ.inj (Nat.cast_injective h)
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨q, rfl⟩
  change ((cycleAlphabet n k).map (Rat.castHom ℝ)).eval ((q + 1 : ℕ) : ℝ) =
    (descentAlphabetPolynomial n k).eval ((q + 1 : ℕ) : ℝ)
  rw [descentAlphabetPolynomial_eval_nat _ _ _ (Nat.succ_pos _)]
  have he := cycleAlphabet_eval_nat n k (q + 1)
  have hc := letters_eq_necklace_content hn (q + 1) k
  rw [hc]
  have hm : ((cycleAlphabet n k).map (Rat.castHom ℝ)).eval ((q + 1 : ℕ) : ℝ) =
      (((cycleAlphabet n k).eval ((q + 1 : ℕ) : ℚ) : ℚ) : ℝ) := by
    rw [eval_map]
    simpa using (eval₂_at_apply (p := cycleAlphabet n k) (Rat.castHom ℝ) ((q + 1 : ℕ) : ℚ))
  rw [hm, he]
  norm_cast

end RealRooted.LongCycleDescents.Structural
