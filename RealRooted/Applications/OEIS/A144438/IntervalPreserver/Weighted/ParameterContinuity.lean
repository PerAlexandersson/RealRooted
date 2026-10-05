import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.ContactCalculus

/-!
# Continuity of the weighted unequal-parameter family

The coefficients of the input product, its weighted image, and its companion
vary continuously with all labeled input-root parameters.  We also package
joint continuity in the parameters and the evaluation variable.
-/

open Polynomial Topology

noncomputable section

namespace RealRooted.Applications.OEIS

theorem continuous_weightedDecoParameterInput_coeff
    {I : Type*}
    (s : Finset I) (k : ℕ) :
    Continuous fun a : I → ℝ => (weightedDecoParameterInput s a).coeff k := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
      simp only [weightedDecoParameterInput, Finset.prod_empty]
      fun_prop
  | @insert i s hi ih =>
      rw [show (fun a : I → ℝ =>
          (weightedDecoParameterInput (insert i s) a).coeff k) =
          fun a => ((X + C (a i)) * weightedDecoParameterInput s a).coeff k by
        funext a
        simp only [weightedDecoParameterInput, Finset.prod_insert hi]]
      cases k with
      | zero =>
          simp only [add_mul, coeff_add, coeff_X_mul_zero, coeff_C_mul]
          convert (continuous_apply i).mul (ih 0) using 1
          ext a
          simp only [Pi.mul_apply, zero_add]
      | succ k =>
          simp only [add_mul, coeff_add, coeff_X_mul, coeff_C_mul]
          exact (ih k).add ((continuous_apply i).mul (ih (k + 1)))

private theorem continuous_coeff_basisTransform_of_degree_le
    {T : Type*} [TopologicalSpace T] (B : ℕ → ℝ[X])
    (p : T → ℝ[X]) (N k : ℕ)
    (hdegree : ∀ t, (p t).natDegree ≤ N)
    (hcoeff : ∀ i, Continuous fun t => (p t).coeff i) :
    Continuous fun t => (Polynomial.basisTransform B (p t)).coeff k := by
  rw [show (fun t => (Polynomial.basisTransform B (p t)).coeff k) =
      fun t => ∑ i ∈ Finset.range (N + 1),
        (p t).coeff i * (B i).coeff k by
    funext t
    rw [Polynomial.coeff_basisTransform]
    exact (p t).sum_over_range'
      (f := fun i c => c * (B i).coeff k) (fun _ => by simp) (N + 1)
      ((hdegree t).trans_lt (Nat.lt_succ_self N))]
  exact continuous_finsetSum _ fun i _ => (hcoeff i).mul_const _

theorem continuous_weightedDecoParameterImage_coeff
    {I : Type*}
    (w : ℝ) (s : Finset I) (k : ℕ) :
    Continuous fun a : I → ℝ =>
      (weightedDecoParameterImage w s a).coeff k := by
  apply continuous_coeff_basisTransform_of_degree_le
    (weightedDecoEulerian w) (fun a => weightedDecoParameterInput s a) s.card k
  · intro a
    rw [weightedDecoParameterInput_natDegree]
  · exact continuous_weightedDecoParameterInput_coeff s

theorem continuous_weightedDecoParameterCompanion_coeff
    {I : Type*}
    (w : ℝ) (s : Finset I) (k : ℕ) :
    Continuous fun a : I → ℝ =>
      (weightedDecoParameterCompanion w s a).coeff k := by
  apply continuous_coeff_basisTransform_of_degree_le
    (weightedDecoCompanionBasis w)
    (fun a => weightedDecoParameterInput s a) s.card k
  · intro a
    rw [weightedDecoParameterInput_natDegree]
  · exact continuous_weightedDecoParameterInput_coeff s

theorem weightedDecoParameterCompanion_natDegree_le
    {I : Type*} (w : ℝ) (s : Finset I) (a : I → ℝ) :
    (weightedDecoParameterCompanion w s a).natDegree ≤ s.card := by
  unfold weightedDecoParameterCompanion weightedDecoCompanionTransform
  calc
    (Polynomial.basisTransform (weightedDecoCompanionBasis w)
        (weightedDecoParameterInput s a)).natDegree ≤
        (weightedDecoParameterInput s a).natDegree :=
      Polynomial.basisTransform_natDegree_le_of_natDegree_le
        (fun n => (weightedDecoCompanionBasis_natDegree_le w n).trans
          (Nat.sub_le n 1)) _
    _ = s.card := weightedDecoParameterInput_natDegree s a

theorem continuous_weightedDecoParameterImage_eval_prod
    {I : Type*}
    (w : ℝ) (s : Finset I) :
    Continuous fun z : (I → ℝ) × ℝ =>
      (weightedDecoParameterImage w s z.1).eval z.2 := by
  apply Polynomial.continuous_eval_of_continuous_coeff
    (fun z : (I → ℝ) × ℝ => weightedDecoParameterImage w s z.1)
    (N := s.card)
  · intro z
    rw [weightedDecoParameterImage_natDegree]
  · intro k
    exact (continuous_weightedDecoParameterImage_coeff w s k).comp continuous_fst
  · exact continuous_snd

theorem continuous_weightedDecoParameterImage_derivative_eval_prod
    {I : Type*}
    (w : ℝ) (s : Finset I) :
    Continuous fun z : (I → ℝ) × ℝ =>
      (weightedDecoParameterImage w s z.1).derivative.eval z.2 := by
  apply Polynomial.continuous_eval_of_continuous_coeff
    (fun z : (I → ℝ) × ℝ =>
      (weightedDecoParameterImage w s z.1).derivative)
    (N := s.card)
  · intro z
    calc
      (weightedDecoParameterImage w s z.1).derivative.natDegree ≤
          (weightedDecoParameterImage w s z.1).natDegree - 1 :=
        Polynomial.natDegree_derivative_le _
      _ ≤ (weightedDecoParameterImage w s z.1).natDegree := Nat.sub_le _ _
      _ = s.card := weightedDecoParameterImage_natDegree w s z.1
  · intro k
    simp only [coeff_derivative]
    exact ((continuous_weightedDecoParameterImage_coeff w s (k + 1)).comp
      continuous_fst).mul_const _
  · exact continuous_snd

theorem continuous_weightedDecoParameterCompanion_eval_prod
    {I : Type*}
    (w : ℝ) (s : Finset I) :
    Continuous fun z : (I → ℝ) × ℝ =>
      (weightedDecoParameterCompanion w s z.1).eval z.2 := by
  apply Polynomial.continuous_eval_of_continuous_coeff
    (fun z : (I → ℝ) × ℝ => weightedDecoParameterCompanion w s z.1)
    (N := s.card)
  · exact fun z => weightedDecoParameterCompanion_natDegree_le w s z.1
  · intro k
    exact (continuous_weightedDecoParameterCompanion_coeff w s k).comp
      continuous_fst
  · exact continuous_snd

end RealRooted.Applications.OEIS
