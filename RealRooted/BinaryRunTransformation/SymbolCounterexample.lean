import RealRooted.BinaryRunTransformation.Interlacing
import RealRooted.BorceaBranden.UnivariateFiniteSymbol

/-!
# The rank-three binary-run transform does not preserve stability

The rank-three binary-run transform `J_3 : u^m ↦ J_{3,m}` satisfies the monomial-chain
interlacing hypotheses (`strictInterl_binaryRunTransform`), so it preserves oriented interlacing
of nonnegative-coefficient inputs, equivalently nonnegative stable pencils.  It does not preserve
unrestricted bivariate real stability: applied in the first variable to the real stable
polynomial `(t + z)^3` it gives its Borcea--Brändén symbol
`S(t, z) = z^3 + 3 t z^2 + (2 t + t^2) z + t`, which vanishes at `t = z = (-1 + 2i)/5`.
So preservation of stable pencils lies strictly between real-rootedness preservation and
stability preservation.
-/

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted

/-- The rank-three binary-run symbol in variables `t = X 0` and `z = X 1`. -/
def binaryRunSymbolThree : MvPolynomial (Fin 2) ℝ :=
  let t := MvPolynomial.X (0 : Fin 2)
  let z := MvPolynomial.X (1 : Fin 2)
  z ^ 3 + 3 * t * z ^ 2 + (2 * t + t ^ 2) * z + t

/-- The result of applying `binaryRunTransformLinearMap 3` in the first
variable to `(t + z)^3`, represented by the repository's finite symbol. -/
def binaryRunFirstVariableOutputThree : MvPolynomial (Fin 2) ℝ :=
  BorceaBranden.finiteAlgebraicSymbol 3 (binaryRunTransformLinearMap 3)

/-- The rank-three finite symbol expands to the stated polynomial `S(t,z)`. -/
theorem binaryRunFirstVariableOutputThree_eq_binaryRunSymbolThree :
    binaryRunFirstVariableOutputThree = binaryRunSymbolThree := by
  have h2 : (3 : MvPolynomial (Fin 2) ℝ) * MvPolynomial.C (2 / 3) = 2 := by
    rw [← map_ofNat MvPolynomial.C 3, ← MvPolynomial.C_mul, ← map_ofNat MvPolynomial.C 2]
    norm_num
  have h3 : (3 : MvPolynomial (Fin 2) ℝ) * MvPolynomial.C 3⁻¹ = 1 := by
    rw [← map_ofNat MvPolynomial.C 3, ← MvPolynomial.C_mul]
    norm_num
  simp only [binaryRunFirstVariableOutputThree, BorceaBranden.finiteAlgebraicSymbol,
    Nat.reduceAdd, map_natCast, BorceaBranden.polynomialInFirstMv, Fin.isValue,
    binaryRunTransformLinearMap_apply, binaryRunTransform_X_pow, binaryRunPolynomial,
    Nat.one_le_ofNat, Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton, tsub_self,
    Nat.choose_zero_right, Nat.cast_one, Nat.choose_one_right, one_mul, Nat.add_one_sub_one,
    Finset.sum_range_succ, Finset.range_one, ↓reduceIte, eval₂_one, mul_one, tsub_zero,
    Nat.cast_ofNat, one_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self,
    CharP.cast_eq_zero, Nat.choose_succ_self_right, zero_mul, zero_div, monomial_zero_right,
    add_zero, Nat.choose_zero_succ, Nat.choose_self, eval₂_monomial, MvPolynomial.C_1, pow_one,
    Nat.reduceSub, one_div, Nat.choose_succ_self, mul_zero, eval₂_add, div_one, pow_zero,
    binaryRunSymbolThree]
  rw [Nat.choose_eq_zero_of_lt (by norm_num : 1 < 3)]
  linear_combination (MvPolynomial.X 0 * MvPolynomial.X 1) * h2 +
    (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1) * h3

/-- The upper-half-plane witness used to disprove stability of the symbol. -/
def binaryRunWitnessThree : ℂ := (-1 + 2 * Complex.I) / 5

/-- The witness has positive imaginary part. -/
theorem im_pos_binaryRunWitnessThree : 0 < binaryRunWitnessThree.im := by
  norm_num [binaryRunWitnessThree]

/-- At the witness, the symbol evaluates to `w * (5 * w^2 + 2 * w + 1)`. -/
theorem binaryRunSymbolThree_eval_witness_factor :
    MvPolynomial.eval (fun _ : Fin 2 => binaryRunWitnessThree)
        (complexifyMv binaryRunSymbolThree) =
      binaryRunWitnessThree *
        (5 * binaryRunWitnessThree ^ 2 + 2 * binaryRunWitnessThree + 1) := by
  have hEval :
      MvPolynomial.eval (fun _ : Fin 2 => binaryRunWitnessThree)
          (complexifyMv binaryRunSymbolThree) =
        binaryRunWitnessThree ^ 3 +
          3 * binaryRunWitnessThree * binaryRunWitnessThree ^ 2 +
          (2 * binaryRunWitnessThree + binaryRunWitnessThree ^ 2) *
            binaryRunWitnessThree + binaryRunWitnessThree := by
    simp [binaryRunSymbolThree, complexifyMv]
  rw [hEval]
  ring

/-- The symbol vanishes at the upper-half-plane witness. -/
theorem binaryRunSymbolThree_eval_witness :
    MvPolynomial.eval (fun _ : Fin 2 => binaryRunWitnessThree)
        (complexifyMv binaryRunSymbolThree) = 0 := by
  rw [binaryRunSymbolThree_eval_witness_factor]
  have hpoly : 5 * binaryRunWitnessThree ^ 2 +
      2 * binaryRunWitnessThree + 1 = 0 := by
    rw [binaryRunWitnessThree]
    ring_nf
    simp [pow_two, Complex.I_mul_I]
  rw [hpoly, mul_zero]

/-- The rank-three binary-run symbol is not multivariate real stable. -/
theorem not_mvRealStable_binaryRunSymbolThree :
    ¬ MvRealStable binaryRunSymbolThree := by
  intro h
  have hz := h (fun _ : Fin 2 => binaryRunWitnessThree)
  have hupper : ∀ i : Fin 2,
      binaryRunWitnessThree ∈ (fun z : ℂ => {w | 0 < w.im}) i := by
    intro i
    fin_cases i <;> exact im_pos_binaryRunWitnessThree
  exact (hz hupper) binaryRunSymbolThree_eval_witness

/-- The finite-symbol output of the first-variable `J_3` action is not stable. -/
theorem not_mvRealStable_binaryRunFirstVariableOutputThree :
    ¬ MvRealStable binaryRunFirstVariableOutputThree := by
  rw [binaryRunFirstVariableOutputThree_eq_binaryRunSymbolThree]
  exact not_mvRealStable_binaryRunSymbolThree

/-- The stable input `(t + z)^3` and its nonstable rank-three output. -/
theorem binaryRunTransformThree_counterexample :
    MvRealStable
        ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ 3) ∧
      ¬ MvRealStable binaryRunFirstVariableOutputThree := by
  have hlinear : MvRealStable
      (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) :=
    MvRealStable.X_add_X 0 1
  refine ⟨?_, not_mvRealStable_binaryRunFirstVariableOutputThree⟩
  simpa [pow_succ, mul_assoc] using hlinear.mul (hlinear.mul hlinear)

end RealRooted
