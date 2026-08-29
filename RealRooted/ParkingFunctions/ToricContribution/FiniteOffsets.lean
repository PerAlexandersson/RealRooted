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

/-- If a split polynomial has positive value at zero and all roots are
positive, multiplying it by `(-1)^n` makes its leading coefficient positive. -/
theorem IntervalRootData.hasPosLeadingCoeff_negOnePow_mul
    {p : ℝ[X]} {n : ℕ} (hp : IntervalRootData p n) (hpZero : 0 < p.eval 0) :
    HasPosLeadingCoeff (C ((-1 : ℝ) ^ n) * p) := by
  have hprod : 0 < p.roots.prod := by
    apply Multiset.prod_pos
    intro r hr
    exact (hp.roots_mem_Ioo r hr).1
  have hcoeff := hp.splits.coeff_zero_eq_leadingCoeff_mul_prod_roots
  rw [coeff_zero_eq_eval_zero, hp.natDegree_eq] at hcoeff
  have hfactor : 0 < (-1 : ℝ) ^ n * p.leadingCoeff := by
    rw [show (-1 : ℝ) ^ n * p.leadingCoeff = p.eval 0 / p.roots.prod by
      rw [hcoeff]
      field_simp [hprod.ne']]
    exact div_pos hpZero hprod
  rw [HasPosLeadingCoeff, Polynomial.leadingCoeff_C_mul_of_isUnit
    (isUnit_iff_ne_zero.mpr (pow_ne_zero n (by norm_num)))]
  exact hfactor

/-- The interval-insertion proper-position theorem without a leading-sign
hypothesis, using positive orientation at zero to normalize the input. -/
theorem IntervalRootData.prec_neg_insertionOperator
    {p : ℝ[X]} {n : ℕ} (hp : IntervalRootData p n) (hpZero : 0 < p.eval 0)
    (a b : ℝ) (hn : 2 ≤ n) (hb : 0 < b) :
    Prec p (-ToricContribution.insertionOperator a b p) := by
  let sign : ℝ := (-1 : ℝ) ^ n
  have hsign : sign ≠ 0 := pow_ne_zero n (by norm_num)
  have hscaledData : IntervalRootData (C sign * p) n := hp.C_mul hsign
  have hscaledPos : HasPosLeadingCoeff (C sign * p) := by
    exact hp.hasPosLeadingCoeff_negOnePow_mul hpZero
  have hprec :
      Prec (C sign * p)
        (-ToricContribution.insertionOperator a b (C sign * p)) := by
    apply ToricContribution.prec_neg_insertionOperator a b
      hscaledData.splits hscaledPos
      (by rw [hscaledData.natDegree_eq]; exact hn)
      (fun r hr => hscaledData.roots_mem_Ioo r
        ((mem_roots hscaledPos.ne_zero).mpr hr))
      hscaledData.eval_derivative_ne_zero hb
  have hoperator :
      -ToricContribution.insertionOperator a b (C sign * p) =
        C sign * (-ToricContribution.insertionOperator a b p) := by
    rw [insertionOperator_C_mul]
    ring
  rw [hoperator] at hprec
  have hleft := prec_C_mul_left hprec (inv_ne_zero hsign)
  rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hsign, C_1,
    one_mul] at hleft
  have hboth := prec_C_mul_right hleft (inv_ne_zero hsign)
  rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hsign, C_1,
    one_mul] at hboth
  exact hboth

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

/-- Above the two low-degree boundary cases, the next signed diagonal lies
strictly before the current signed diagonal in proper-position order. This is
the polynomial form of the directed gap comparison in the last Darboux
square. -/
theorem consecutive_signedTriangleFamily_prec
    (m ε d : ℕ) (hm : 4 ≤ m) (hd : d ≤ m - 2) :
    Prec
      (signedTriangleFamily ((ε : ℝ) + 1 / 2)
        (jPolynomial m ε) (d + 1) (d + 1))
      (C ((((m - 1 : ℕ) : ℝ) - d) *
          ((m - 1 : ℕ) + d + ε + 3)) *
        signedTriangleFamily ((ε : ℝ) + 1 / 2)
          (jPolynomial m ε) d d) := by
  let a : ℝ := ε + 1 / 2 + d
  let b : ℝ := ε + 1 / 2 + d + 2
  let eigenvalue : ℝ :=
    (((m - 1 : ℕ) : ℝ) - d) * ((m - 1 : ℕ) + d + ε + 3)
  let H := signedTriangleFamily ((ε : ℝ) + 1 / 2)
    (jPolynomial m ε) (d + 1) d
  let A := signedTriangleFamily ((ε : ℝ) + 1 / 2)
    (jPolynomial m ε) d d
  let B := signedTriangleFamily ((ε : ℝ) + 1 / 2)
    (jPolynomial m ε) (d + 1) (d + 1)
  let signH : ℝ := (-1 : ℝ) ^ (m - 2)
  let signAB : ℝ := (-1 : ℝ) ^ (m - 1)
  let Hpos : ℝ[X] := C signH * H
  let Apos : ℝ[X] := C signAB * (C eigenvalue * A)
  let Bpos : ℝ[X] := C signAB * B
  have hmPos : 0 < m := by lia
  have hdRow : d ≤ m - 1 := by lia
  have hdNext : d + 1 ≤ m - 1 := by lia
  have hHData : IntervalRootData H (m - 2) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε (d + 1) d hmPos hdNext (by lia)
    dsimp only [H]
    convert hdata using 1
    lia
  have hAData : IntervalRootData A (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε d d hmPos hdRow le_rfl
    dsimp only [A]
    convert hdata using 1
    lia
  have hBData : IntervalRootData B (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε (d + 1) (d + 1) hmPos hdNext le_rfl
    dsimp only [B]
    convert hdata using 1
    lia
  have hHEval : 0 < H.eval 0 := by
    exact signedTriangleFamily_eval_zero_pos m ε (d + 1) d hmPos hdNext
  have hAEval : 0 < A.eval 0 := by
    exact signedTriangleFamily_eval_zero_pos m ε d d hmPos hdRow
  have hBEval : 0 < B.eval 0 := by
    exact signedTriangleFamily_eval_zero_pos m ε (d + 1) (d + 1) hmPos hdNext
  have heigenvalue : 0 < eigenvalue := by
    have hfirst : 0 < (((m - 1 : ℕ) : ℝ) - d) := by
      have hnat : 0 < m - 1 - d := by lia
      rw [← Nat.cast_sub hdRow]
      exact_mod_cast hnat
    have hsecond : 0 < (((m - 1 : ℕ) : ℝ) + d + ε + 3) := by positivity
    exact mul_pos hfirst hsecond
  have hsignH : signH ≠ 0 := pow_ne_zero (m - 2) (by norm_num)
  have hsignAB : signAB ≠ 0 := pow_ne_zero (m - 1) (by norm_num)
  have hsignRelation : signAB = -signH := by
    dsimp only [signAB, signH]
    rw [show m - 1 = (m - 2) + 1 by lia, pow_succ]
    ring
  have hHposData : IntervalRootData Hpos (m - 2) := hHData.C_mul hsignH
  have hBposData : IntervalRootData Bpos (m - 1) := hBData.C_mul hsignAB
  have hAposData : IntervalRootData Apos (m - 1) := by
    exact (hAData.C_mul heigenvalue.ne').C_mul hsignAB
  have hHLeading : HasPosLeadingCoeff Hpos := by
    exact hHData.hasPosLeadingCoeff_negOnePow_mul hHEval
  have hBLeading : HasPosLeadingCoeff Bpos := by
    exact hBData.hasPosLeadingCoeff_negOnePow_mul hBEval
  have hALeading : HasPosLeadingCoeff Apos := by
    apply (hAData.C_mul heigenvalue.ne').hasPosLeadingCoeff_negOnePow_mul
    simp only [eval_mul, eval_C]
    exact mul_pos heigenvalue hAEval
  have hhorizontal : B = insertionOperator a b H := by
    dsimp only [B, H, a, b, signedTriangleFamily]
    rw [triangleFamily_succ]
    have hparameter :
        (ε : ℝ) + 1 / 2 + ((d + 1 : ℕ) : ℝ) + 1 =
          (ε : ℝ) + 1 / 2 + (d : ℝ) + 2 := by
      push_cast
      ring
    rw [hparameter, insertionOperator_C_mul]
  have hBposOperator : Bpos = -insertionOperator a b Hpos := by
    dsimp only [Bpos, Hpos]
    rw [insertionOperator_C_mul, ← hhorizontal, hsignRelation]
    apply Polynomial.funext
    intro x
    simp only [eval_neg, eval_mul, eval_C]
    ring
  have hHBPrec : Prec Hpos Bpos := by
    rw [hBposOperator]
    apply ToricContribution.prec_neg_insertionOperator a b
      hHposData.splits hHLeading
    · rw [hHposData.natDegree_eq]
      lia
    · intro r hr
      exact hHposData.roots_mem_Ioo r
        ((mem_roots hHLeading.ne_zero).mpr hr)
    · exact hHposData.eval_derivative_ne_zero
    · dsimp only [b]
      positivity
  have hHBInterlaces : Interlaces Hpos Bpos := by
    apply hHBPrec.toInterlaces
    rw [hHposData.natDegree_eq, hBposData.natDegree_eq]
    lia
  have hnoCommon : ∀ r, Bpos.IsRoot r → ¬Hpos.IsRoot r := by
    intro r hrB hrH
    have hMroot : (insertionOperator a b Hpos).IsRoot r := by
      rw [hBposOperator, IsRoot.def] at hrB
      rw [IsRoot.def]
      simpa using hrB
    exact insertionOperator_no_common_root a b
      (fun x hx => hHposData.roots_mem_Ioo x
        ((mem_roots hHLeading.ne_zero).mpr hx))
      hHposData.eval_derivative_ne_zero r hrH hMroot
  have hcombination :
      Apos = 1 * Bpos + (-(C (3 / 2 : ℝ) * (1 - X))) * Hpos := by
    have hscaled := congrArg (C signAB * ·)
      (signedTriangleFamily_diagonal_relation m ε d)
    dsimp only [Apos, Bpos, Hpos, A, B, H, eigenvalue]
    rw [hsignRelation] at hscaled ⊢
    simp only [map_neg, map_mul] at hscaled ⊢
    linear_combination hscaled
  have hcombinationLeading :
      HasPosLeadingCoeff
        (1 * Bpos + (-(C (3 / 2 : ℝ) * (1 - X))) * Hpos) := by
    rw [← hcombination]
    exact hALeading
  have hcombinationDegree :
      (1 * Bpos + (-(C (3 / 2 : ℝ) * (1 - X))) * Hpos).natDegree =
        Bpos.natDegree := by
    rw [← hcombination, hAposData.natDegree_eq, hBposData.natDegree_eq]
  have hcoefficientNeg :
      ∀ r, Bpos.IsRoot r → (-(C (3 / 2 : ℝ) * (1 - X))).eval r < 0 := by
    intro r hr
    have hri := hBposData.roots_mem_Ioo r
      ((mem_roots hBLeading.ne_zero).mpr hr)
    have hone : 0 < 1 - r := sub_pos.mpr hri.2
    simp only [eval_neg, eval_mul, eval_C, eval_sub, eval_one, eval_X]
    norm_num
    nlinarith
  have hprecPos := prec_of_interlaces_evalCoeff_neg_same
    hHBInterlaces hHLeading hcombinationLeading hcombinationDegree
    hnoCommon hcoefficientNeg
  rw [← hcombination] at hprecPos
  have hleft := prec_C_mul_left hprecPos (inv_ne_zero hsignAB)
  rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hsignAB,
    C_1, one_mul] at hleft
  have hboth := prec_C_mul_right hleft (inv_ne_zero hsignAB)
  rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hsignAB,
    C_1, one_mul] at hboth
  exact hboth

end ToricContribution
end ParkingFunctions
end RealRooted
