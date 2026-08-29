import RealRooted.ParkingFunctions.ToricContribution.DiagonalCollapse

/-!
# Root data for the finite toric-contribution offsets

This file transfers the open-interval root package for a triangle diagonal
across its factor `1-X`.  The resulting polynomial has one additional simple
root at the right endpoint and all other roots in the open unit interval.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace ParkingFunctions
namespace ToricContribution

/-- A polynomial has exactly `n` simple roots in `(0,1]`, including the right
endpoint, and does not vanish at the left endpoint. -/
structure RightClosedIntervalRootData (p : ℝ[X]) (n : ℕ) : Prop where
  natDegree_eq : p.natDegree = n
  eval_zero_ne : p.eval 0 ≠ 0
  eval_one_eq_zero : p.eval 1 = 0
  splits : p.Splits
  roots_mem_Ioc : ∀ r ∈ p.roots, r ∈ Set.Ioc (0 : ℝ) 1
  eval_derivative_ne_zero : ∀ r, p.IsRoot r → p.derivative.eval r ≠ 0

/-- Multiplication by `1-X`, followed by a nonzero rescaling, adjoins one
simple root at the right endpoint to an open-interval root package. -/
theorem rightClosedIntervalRootData_of_one_sub_X_mul_eq_C_mul
    {f p : ℝ[X]} {n : ℕ} {s : ℝ}
    (hf : IntervalRootData f n) (hs : s ≠ 0)
    (heq : (1 - X) * f = C s * p) :
    RightClosedIntervalRootData p (n + 1) := by
  have hf_ne : f ≠ 0 := by
    intro hzero
    apply hf.eval_zero_ne
    simp [hzero]
  have hp_eval_zero : p.eval 0 ≠ 0 := by
    intro hpzero
    have hzero := congrArg (Polynomial.eval 0) heq
    simp only [eval_mul, eval_sub, eval_one, eval_X, sub_zero, one_mul,
      eval_C, hpzero, mul_zero] at hzero
    exact hf.eval_zero_ne hzero
  have hp_ne : p ≠ 0 := by
    intro hzero
    apply hp_eval_zero
    simp [hzero]
  have hone_sub_ne : (1 - X : ℝ[X]) ≠ 0 := by
    intro hzero
    have h := congrArg (Polynomial.eval 0) hzero
    norm_num at h
  have hone_sub_degree : (1 - X : ℝ[X]).natDegree = 1 := by
    rw [show (1 - X : ℝ[X]) = -(X - 1) by ring, Polynomial.natDegree_neg]
    simpa using (Polynomial.natDegree_X_sub_C (R := ℝ) 1)
  have hone_sub_splits : (1 - X : ℝ[X]).Splits := by
    have hlinear : (X - 1 : ℝ[X]).Splits := by
      simpa using (Polynomial.Splits.X_sub_C (1 : ℝ))
    rw [show (1 - X : ℝ[X]) = -(X - 1) by ring]
    exact hlinear.neg
  have hproduct_splits : ((1 - X) * f).Splits :=
    hone_sub_splits.mul hf.splits
  have hp_splits : p.Splits := by
    have hscaled : (C s * p).Splits := by rwa [← heq]
    have hinv := hscaled.C_mul s⁻¹
    simpa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hs] using hinv
  have hp_eval_one : p.eval 1 = 0 := by
    have hone := congrArg (Polynomial.eval 1) heq
    simp only [eval_mul, eval_sub, eval_one, eval_X, sub_self, zero_mul,
      eval_C] at hone
    exact (mul_eq_zero.mp hone.symm).resolve_left hs
  refine ⟨?_, hp_eval_zero, hp_eval_one, hp_splits, ?_, ?_⟩
  · rw [← Polynomial.natDegree_C_mul hs, ← heq,
      Polynomial.natDegree_mul hone_sub_ne hf_ne, hone_sub_degree,
      hf.natDegree_eq]
    exact Nat.add_comm 1 n
  · intro r hr
    have hrp : p.IsRoot r := (mem_roots hp_ne).mp hr
    rw [IsRoot.def] at hrp
    have hroot := congrArg (Polynomial.eval r) heq
    rw [eval_mul, eval_sub, eval_one, eval_X, eval_mul, eval_C, hrp,
      mul_zero] at hroot
    rcases mul_eq_zero.mp hroot with hrOne | hrf
    · have hrEq : r = 1 := by linarith
      rw [hrEq]
      exact ⟨by norm_num, le_rfl⟩
    · have hrfRoot : f.IsRoot r := hrf
      have hri := hf.roots_mem_Ioo r ((mem_roots hf_ne).mpr hrfRoot)
      exact ⟨hri.1, hri.2.le⟩
  · intro r hrp
    rw [IsRoot.def] at hrp
    have hroot := congrArg (Polynomial.eval r) heq
    rw [eval_mul, eval_sub, eval_one, eval_X, eval_mul, eval_C, hrp,
      mul_zero] at hroot
    have hproduct_derivative_ne : ((1 - X) * f).derivative.eval r ≠ 0 := by
      rcases mul_eq_zero.mp hroot with hrOne | hrf
      · have hrEq : r = 1 := by linarith
        have hfOne : f.eval 1 ≠ 0 := by
          intro hfOneZero
          have hfOneRoot : f.IsRoot 1 := hfOneZero
          have hi := hf.roots_mem_Ioo 1 ((mem_roots hf_ne).mpr hfOneRoot)
          exact (lt_irrefl 1 hi.2)
        rw [hrEq]
        simp only [derivative_mul, derivative_sub, derivative_one,
          derivative_X, zero_sub, eval_add, eval_mul, eval_neg, eval_one,
          eval_sub, eval_X, sub_self, zero_mul, add_zero]
        exact mul_ne_zero (by norm_num) hfOne
      · have hrfRoot : f.IsRoot r := hrf
        have hri := hf.roots_mem_Ioo r ((mem_roots hf_ne).mpr hrfRoot)
        have honeSub : 1 - r ≠ 0 := sub_ne_zero.mpr hri.2.ne'
        have hfder := hf.eval_derivative_ne_zero r hrfRoot
        simp only [derivative_mul, eval_add, eval_mul, hrf, mul_zero, zero_add]
        simpa [sub_eq_add_neg] using mul_ne_zero honeSub hfder
    have hderivative := congrArg derivative heq
    simp only [derivative_C_mul] at hderivative
    have heval := congrArg (Polynomial.eval r) hderivative
    simp only [eval_mul, eval_C] at heval
    intro hzero
    apply hproduct_derivative_ne
    rw [heval, hzero, mul_zero]

/-- For every nonexceptional offset, `R_d` has degree `m`, a simple right
endpoint root, and all remaining roots in the open unit interval. -/
theorem rPolynomial_rightClosedIntervalRootData
    (m ε d : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) :
    RightClosedIntervalRootData (rPolynomial m ε d) m := by
  let f := triangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) d d
  let s := realRisingFactorial ((ε : ℝ) + 1 / 2) d *
    ((d.factorial : ℝ) * jCoeff m ε d)
  have hf : IntervalRootData f (m - 1) := by
    have hdata := jPolynomial_triangleFamily_intervalRootData
      m ε d d hm hd le_rfl
    dsimp only [f]
    convert hdata using 1
    lia
  have hs : s ≠ 0 := by
    have hrising : 0 < realRisingFactorial ((ε : ℝ) + 1 / 2) d := by
      apply realRisingFactorial_pos
      positivity
    have hderivative :=
      negOnePow_mul_iterate_derivative_jPolynomial_eval_zero_pos m ε d hm hd
    rw [iterate_derivative_jPolynomial_eval_zero m ε d (by lia)] at hderivative
    have hcoefficient : (d.factorial : ℝ) * jCoeff m ε d ≠ 0 :=
      right_ne_zero_of_mul (ne_of_gt hderivative)
    exact mul_ne_zero hrising.ne' hcoefficient
  have heq : (1 - X) * f = C s * rPolynomial m ε d := by
    exact one_sub_X_mul_triangleFamily_diagonal_eq_C_mul_rPolynomial
      m ε d hm hd
  have hdata := rightClosedIntervalRootData_of_one_sub_X_mul_eq_C_mul hf hs heq
  convert hdata using 1
  lia

end ToricContribution
end ParkingFunctions
end RealRooted
