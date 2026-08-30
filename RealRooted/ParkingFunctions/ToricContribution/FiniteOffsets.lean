import RealRooted.JacobiParameterInterlacing
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

/-- The `i`th root of a polynomial, in increasing order. The default value is
irrelevant when the polynomial has the expected degree and splits. -/
noncomputable def orderedRoot (p : ℝ[X]) (n : ℕ) (i : Fin n) : ℝ :=
  (p.roots.sort (· ≤ ·)).getD i 0

theorem IntervalRootData.roots_sort_length
    {p : ℝ[X]} {n : ℕ} (hp : IntervalRootData p n) :
    (p.roots.sort (· ≤ ·)).length = n := by
  rw [Multiset.length_sort, card_roots_of_splits hp.splits,
    hp.natDegree_eq]

theorem IntervalRootData.orderedRoot_isRoot
    {p : ℝ[X]} {n : ℕ} (hp : IntervalRootData p n) (i : Fin n) :
    p.IsRoot (orderedRoot p n i) := by
  have hi : i.val < (p.roots.sort (· ≤ ·)).length := by
    rw [hp.roots_sort_length]
    exact i.isLt
  rw [orderedRoot, List.getD_eq_getElem _ _ hi]
  apply Polynomial.isRoot_of_mem_roots
  exact (Multiset.mem_sort _).mp (List.getElem_mem ..)

theorem IntervalRootData.strictMono_orderedRoot
    {p : ℝ[X]} {n : ℕ} (hp : IntervalRootData p n) :
    StrictMono (orderedRoot p n) := by
  have hsorted : (p.roots.sort (· ≤ ·)).SortedLE := by
    simpa using (Multiset.pairwise_sort (s := p.roots) (r := (· ≤ ·))).sortedLE
  have hnodup : (p.roots.sort (· ≤ ·)).Nodup := by
    apply Multiset.coe_nodup.mp
    simpa using Polynomial.roots_nodup_of_splits_and_simple
      (fun r hr hderivative => hp.eval_derivative_ne_zero r hr hderivative)
  have hstrict := hsorted.sortedLT_of_nodup hnodup
  intro i j hij
  have hi : i.val < (p.roots.sort (· ≤ ·)).length := by
    rw [hp.roots_sort_length]
    exact i.isLt
  have hj : j.val < (p.roots.sort (· ≤ ·)).length := by
    rw [hp.roots_sort_length]
    exact j.isLt
  change (p.roots.sort (· ≤ ·)).getD i 0 <
    (p.roots.sort (· ≤ ·)).getD j 0
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  exact hstrict.getElem_lt_getElem_of_lt hij

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
    (a b : ℝ) (hb : 0 < b) :
    Prec p (-ToricContribution.insertionOperator a b p) := by
  by_cases hn : n = 0
  · have hpDegree : p.natDegree = 0 := hp.natDegree_eq.trans hn
    have hpNe : p ≠ 0 := by
      intro hpEq
      simp [hpEq] at hpZero
    have houtputDegree :
        (-ToricContribution.insertionOperator a b p).natDegree = 1 := by
      rw [natDegree_neg]
      exact natDegree_insertionOperator_of_natDegree_zero
        a b hpDegree hpZero.ne' hb.ne'
    have houtputNe : -ToricContribution.insertionOperator a b p ≠ 0 := by
      intro houtputEq
      simp [houtputEq] at houtputDegree
    have houtputSplits :
        (-ToricContribution.insertionOperator a b p).Splits := by
      simpa using insertionOperator_splits_of_natDegree_zero
        a b hpDegree hpZero.ne' hb.ne'
    exact prec_degree_zero_right_of_degree_one hpNe hp.splits
      houtputNe houtputSplits hpDegree houtputDegree
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
      (by rw [hscaledData.natDegree_eq]; exact Nat.one_le_iff_ne_zero.mpr hn)
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

/-- The diagonal-collapse normalization is positive after applying the signed
triangle convention. -/
theorem exists_one_sub_X_mul_signedTriangleFamily_diagonal_eq_C_mul_rPolynomial
    (m ε d : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) :
    ∃ k : ℝ, 0 < k ∧
      (1 - X) * signedTriangleFamily ((ε : ℝ) + 1 / 2)
          (jPolynomial m ε) d d =
        C k * rPolynomial m ε d := by
  let sign : ℝ := (-1 : ℝ) ^ d
  let rising : ℝ := realRisingFactorial ((ε : ℝ) + 1 / 2) d
  let coefficient : ℝ := (d.factorial : ℝ) * jCoeff m ε d
  let k : ℝ := sign * (rising * coefficient)
  have hrising : 0 < rising := by
    apply realRisingFactorial_pos
    positivity
  have hcoefficient : 0 < sign * coefficient := by
    have hderivative :=
      negOnePow_mul_iterate_derivative_jPolynomial_eval_zero_pos m ε d hm hd
    rw [iterate_derivative_jPolynomial_eval_zero m ε d (by lia)] at hderivative
    exact hderivative
  have hk : 0 < k := by
    dsimp only [k]
    nlinarith [mul_pos hrising hcoefficient]
  have hcollapse :=
    one_sub_X_mul_triangleFamily_diagonal_eq_C_mul_rPolynomial m ε d hm hd
  refine ⟨k, hk, ?_⟩
  rw [signedTriangleFamily]
  calc
    (1 - X) * (C sign *
        triangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) d d) =
        C sign * ((1 - X) *
          triangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε) d d) := by ring
    _ = C sign *
        (C (rising * coefficient) * rPolynomial m ε d) := by
      simpa only [sign, rising, coefficient] using
        congrArg (C sign * ·) hcollapse
    _ = C k * rPolynomial m ε d := by
      simp only [← mul_assoc, ← C_mul, k]

/-- The `i`th increasing root of the signed diagonal at offset `d`. -/
noncomputable def signedDiagonalRoot
    (m ε d : ℕ) (i : Fin (m - 1)) : ℝ :=
  orderedRoot
    (signedTriangleFamily ((ε : ℝ) + 1 / 2)
      (jPolynomial m ε) d d) (m - 1) i

/-- The `i`th increasing root of the Jacobi interlacer `J`. -/
noncomputable def jPolynomialRoot
    (m ε : ℕ) (i : Fin (m - 1)) : ℝ :=
  orderedRoot (jPolynomial m ε) (m - 1) i

/-- The next signed diagonal lies strictly before the current signed diagonal
in proper-position order. This is the polynomial form of the directed gap
comparison in the last Darboux square. -/
theorem consecutive_signedTriangleFamily_prec
    (m ε d : ℕ) (hm : 2 ≤ m) (hd : d ≤ m - 2) :
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
    have hraw := hHData.prec_neg_insertionOperator hHEval a b (by
      dsimp only [b]
      positivity)
    have hleft := prec_C_mul_left hraw hsignH
    have hboth := prec_C_mul_right hleft hsignH
    dsimp only [Hpos]
    rw [insertionOperator_C_mul]
    simpa only [mul_neg] using hboth
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

/-- The consecutive signed-diagonal comparison is strict: adjacent
diagonals have no common root. -/
theorem consecutive_signedTriangleFamily_strictPrec
    (m ε d : ℕ) (hm : 2 ≤ m) (hd : d ≤ m - 2) :
    StrictPrecSameDegree
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
  have hm_pos : 0 < m := by lia
  have hd_row : d ≤ m - 1 := by lia
  have hd_next : d + 1 ≤ m - 1 := by lia
  have hH_data : IntervalRootData H (m - 2) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε (d + 1) d hm_pos hd_next (by lia)
    dsimp only [H]
    convert hdata using 1
    lia
  have hA_data : IntervalRootData A (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε d d hm_pos hd_row le_rfl
    dsimp only [A]
    convert hdata using 1
    lia
  have hB_data : IntervalRootData B (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε (d + 1) (d + 1) hm_pos hd_next le_rfl
    dsimp only [B]
    convert hdata using 1
    lia
  have heigenvalue : 0 < eigenvalue := by
    have hfirst : 0 < (((m - 1 : ℕ) : ℝ) - d) := by
      rw [← Nat.cast_sub hd_row]
      exact_mod_cast (by lia : 0 < m - 1 - d)
    have hsecond : 0 < (((m - 1 : ℕ) : ℝ) + d + ε + 3) := by
      positivity
    exact mul_pos hfirst hsecond
  have hhorizontal : B = insertionOperator a b H := by
    dsimp only [B, H, a, b, signedTriangleFamily]
    rw [triangleFamily_succ]
    have hparameter :
        (ε : ℝ) + 1 / 2 + ((d + 1 : ℕ) : ℝ) + 1 =
          (ε : ℝ) + 1 / 2 + (d : ℝ) + 2 := by
      push_cast
      ring
    rw [hparameter, insertionOperator_C_mul]
  apply StrictPrecSameDegree.of_prec_of_no_common
    (consecutive_signedTriangleFamily_prec m ε d hm hd)
  · change B.natDegree = (C eigenvalue * A).natDegree
    rw [hB_data.natDegree_eq, natDegree_C_mul heigenvalue.ne',
      hA_data.natDegree_eq]
  · intro r hrB hr_scaledA
    have hrA : A.IsRoot r := by
      rw [Polynomial.IsRoot.def] at hr_scaledA ⊢
      simp only [eval_mul, eval_C] at hr_scaledA
      exact (mul_eq_zero.mp hr_scaledA).resolve_left heigenvalue.ne'
    have hrI := hB_data.roots_mem_Ioo r (by
      have hB_ne : B ≠ 0 := by
        intro hzero
        apply hB_data.eval_zero_ne
        simp [hzero]
      exact (mem_roots hB_ne).mpr hrB)
    have hrelation := congrArg (Polynomial.eval r)
      (signedTriangleFamily_diagonal_relation m ε d)
    have hAeval : A.eval r = 0 := hrA
    have hBeval : B.eval r = 0 := hrB
    change (C eigenvalue * A - B).eval r =
      (C (3 / 2 : ℝ) * (1 - X) * H).eval r at hrelation
    simp only [eval_sub, eval_mul, eval_C, hAeval, hBeval, mul_zero,
      sub_self, eval_one, eval_X] at hrelation
    have hfactor : (3 / 2 : ℝ) * (1 - r) ≠ 0 := by
      apply mul_ne_zero
      · norm_num
      · exact sub_ne_zero.mpr hrI.2.ne'
    have hrH : H.IsRoot r := by
      rw [Polynomial.IsRoot.def]
      exact (mul_eq_zero.mp hrelation.symm).resolve_left hfactor
    have hr_insert : (insertionOperator a b H).IsRoot r := by
      rw [← hhorizontal]
      exact hrB
    exact insertionOperator_no_common_root a b
      (fun x hx => hH_data.roots_mem_Ioo x (by
        have hH_ne : H ≠ 0 := by
          intro hzero
          apply hH_data.eval_zero_ne
          simp [hzero]
        exact (mem_roots hH_ne).mpr hx))
      hH_data.eval_derivative_ne_zero r hrH hr_insert

/-- The strict adjacent-diagonal comparison written as increasing indexed
root inequalities. -/
theorem consecutive_signedDiagonalRoot_interlacing
    (m ε d : ℕ) (hm : 2 ≤ m) (hd : d ≤ m - 2) :
    (∀ i : Fin (m - 1),
      signedDiagonalRoot m ε (d + 1) i < signedDiagonalRoot m ε d i) ∧
    ∀ (i j : Fin (m - 1)), i < j →
      signedDiagonalRoot m ε d i < signedDiagonalRoot m ε (d + 1) j := by
  let eigenvalue : ℝ :=
    (((m - 1 : ℕ) : ℝ) - d) * ((m - 1 : ℕ) + d + ε + 3)
  let A := signedTriangleFamily ((ε : ℝ) + 1 / 2)
    (jPolynomial m ε) d d
  let B := signedTriangleFamily ((ε : ℝ) + 1 / 2)
    (jPolynomial m ε) (d + 1) (d + 1)
  have hm_pos : 0 < m := by lia
  have hd_row : d ≤ m - 1 := by lia
  have hd_next : d + 1 ≤ m - 1 := by lia
  have hA_data : IntervalRootData A (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε d d hm_pos hd_row le_rfl
    dsimp only [A]
    convert hdata using 1
    lia
  have hB_data : IntervalRootData B (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε (d + 1) (d + 1) hm_pos hd_next le_rfl
    dsimp only [B]
    convert hdata using 1
    lia
  have heigenvalue : 0 < eigenvalue := by
    have hfirst : 0 < (((m - 1 : ℕ) : ℝ) - d) := by
      rw [← Nat.cast_sub hd_row]
      exact_mod_cast (by lia : 0 < m - 1 - d)
    have hsecond : 0 < (((m - 1 : ℕ) : ℝ) + d + ε + 3) := by
      positivity
    exact mul_pos hfirst hsecond
  have hstrict := consecutive_signedTriangleFamily_strictPrec m ε d hm hd
  have hq_degree : (C eigenvalue * A).natDegree = m - 1 := by
    rw [natDegree_C_mul heigenvalue.ne', hA_data.natDegree_eq]
  have hB_roots : ∀ i : Fin (m - 1),
      B.IsRoot (signedDiagonalRoot m ε (d + 1) i) := by
    intro i
    exact hB_data.orderedRoot_isRoot i
  have hA_roots : ∀ i : Fin (m - 1),
      (C eigenvalue * A).IsRoot (signedDiagonalRoot m ε d i) := by
    intro i
    rw [Polynomial.IsRoot.def]
    simp only [eval_mul, eval_C]
    rw [show A.eval (signedDiagonalRoot m ε d i) = 0 by
      exact hA_data.orderedRoot_isRoot i]
    exact mul_zero _
  have hinter := hstrict.interlacing_fin hq_degree
    (signedDiagonalRoot m ε (d + 1)) hB_roots
    hB_data.strictMono_orderedRoot
    (signedDiagonalRoot m ε d) hA_roots hA_data.strictMono_orderedRoot
  exact hinter

/-- The terminal signed diagonal strictly interleaves the Jacobi interlacer.
This transports the all-degree fractional Jacobi comparison through the
positive normalizations of the two polynomial models. -/
theorem signedTriangleFamily_terminal_strictPrec_jPolynomial
    (m ε : ℕ) (hm : 0 < m) :
    StrictPrecSameDegree
      (signedTriangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε)
        (m - 1) (m - 1))
      (jPolynomial m ε) := by
  have hε : 0 ≤ (ε : ℝ) := Nat.cast_nonneg ε
  have hα : -1 < (ε : ℝ) - 1 / 2 := by linarith
  have hupper : -1 < (ε : ℝ) + 1 := by linarith
  have hprec := shiftedJacobiMonic_prec_three_halves (m - 1) ε
  have hno : ∀ r,
      (shiftedJacobiMonic (m - 1) ((ε : ℝ) - 1 / 2) 1).IsRoot r →
      ¬(shiftedJacobiMonic (m - 1) ((ε : ℝ) + 1) 1).IsRoot r := by
    intro r hr hroot
    apply shiftedJacobiMonic_noCommonRoot_alpha_add (m - 1) hα
      (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (3 / 2 : ℝ) ≤ 2) r hr
    convert hroot using 1
    ring_nf
  have hstrict_monic :
      StrictPrecSameDegree
        (shiftedJacobiMonic (m - 1) ((ε : ℝ) - 1 / 2) 1)
        (shiftedJacobiMonic (m - 1) ((ε : ℝ) + 1) 1) := by
    apply StrictPrecSameDegree.of_prec_of_no_common hprec
    · rw [natDegree_shiftedJacobiMonic (m - 1) hα (by norm_num),
        natDegree_shiftedJacobiMonic (m - 1) hupper (by norm_num)]
    · exact hno
  let u : ℝ := (((-1 : ℝ) ^ (m - 1) *
    Ring.choose ((m - 1 : ℕ) + ((ε : ℝ) - 1 / 2) + 1 +
      ((m - 1 : ℕ) : ℝ))
      (m - 1))⁻¹)
  let v : ℝ := (((-1 : ℝ) ^ (m - 1) *
    Ring.choose ((m - 1 : ℕ) + ((ε : ℝ) + 1) + 1 +
      ((m - 1 : ℕ) : ℝ))
      (m - 1))⁻¹)
  have hu : u ≠ 0 := by
    intro hu_zero
    have hne := shiftedJacobiMonic_ne_zero (m - 1) hα
      (by norm_num : (-1 : ℝ) < 1)
    apply hne
    rw [shiftedJacobiMonic]
    change C u * shiftedJacobi (m - 1) ((ε : ℝ) - 1 / 2) 1 = 0
    rw [hu_zero, C_0, zero_mul]
  have hv : v ≠ 0 := by
    intro hv_zero
    have hne := shiftedJacobiMonic_ne_zero (m - 1) hupper
      (by norm_num : (-1 : ℝ) < 1)
    apply hne
    rw [shiftedJacobiMonic]
    change C v * shiftedJacobi (m - 1) ((ε : ℝ) + 1) 1 = 0
    rw [hv_zero, C_0, zero_mul]
  have hstrict_shifted :
      StrictPrecSameDegree
        (shiftedJacobi (m - 1) ((ε : ℝ) - 1 / 2) 1)
        (shiftedJacobi (m - 1) ((ε : ℝ) + 1) 1) := by
    apply (StrictPrecSameDegree.C_mul_C_mul_iff hu hv).mp
    simpa only [shiftedJacobiMonic, u, v] using hstrict_monic
  obtain ⟨k, hk, hterminal⟩ :=
    exists_signedTriangleFamily_terminal_eq_C_mul_shiftedJacobi m ε hm
  let scale : ℝ := Ring.choose (((m - 1 : ℕ) : ℝ) + (ε + 1)) (m - 1)
  have hscale : 0 < scale := by
    apply Polynomial.ring_choose_pos
    linarith
  have hJ := C_mul_jPolynomial_eq_shiftedJacobi m ε hm
  have hJ_scaled : jPolynomial m ε =
      C scale⁻¹ * shiftedJacobi (m - 1) ((ε : ℝ) + 1) 1 := by
    calc
      jPolynomial m ε = C 1 * jPolynomial m ε := by rw [C_1, one_mul]
      _ = C (scale⁻¹ * scale) * jPolynomial m ε := by
        rw [inv_mul_cancel₀ hscale.ne']
      _ = C scale⁻¹ * (C scale * jPolynomial m ε) := by
        rw [C_mul, mul_assoc]
      _ = C scale⁻¹ * shiftedJacobi (m - 1) ((ε : ℝ) + 1) 1 := by
        simpa only [scale] using congrArg (C scale⁻¹ * ·) hJ
  have hscaled := hstrict_shifted.C_mul_C_mul hk.ne'
    (inv_ne_zero hscale.ne')
  rw [← hterminal, ← hJ_scaled] at hscaled
  exact hscaled

/-- The fractional Jacobi endpoint comparison in the indexed root notation
of the finite-offset triangle. -/
theorem signedDiagonalRoot_terminal_interlacing_jPolynomialRoot
    (m ε : ℕ) (hm : 0 < m) :
    (∀ i : Fin (m - 1),
      signedDiagonalRoot m ε (m - 1) i < jPolynomialRoot m ε i) ∧
    ∀ (i j : Fin (m - 1)), i < j →
      jPolynomialRoot m ε i < signedDiagonalRoot m ε (m - 1) j := by
  let T := signedTriangleFamily ((ε : ℝ) + 1 / 2)
    (jPolynomial m ε) (m - 1) (m - 1)
  have hT_data : IntervalRootData T (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε (m - 1) (m - 1) hm le_rfl le_rfl
    dsimp only [T]
    convert hdata using 1
    lia
  have hJ_data : IntervalRootData (jPolynomial m ε) (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε 0 0 hm (by lia) le_rfl
    simpa [signedTriangleFamily] using hdata
  have hstrict := signedTriangleFamily_terminal_strictPrec_jPolynomial m ε hm
  have hinter := hstrict.interlacing_fin hJ_data.natDegree_eq
    (signedDiagonalRoot m ε (m - 1))
    (fun i => hT_data.orderedRoot_isRoot i)
    hT_data.strictMono_orderedRoot
    (jPolynomialRoot m ε)
    (fun i => hJ_data.orderedRoot_isRoot i)
    hJ_data.strictMono_orderedRoot
  exact hinter

private theorem signedDiagonalRoot_le_of_le
    (m ε d e : ℕ) (hm : 2 ≤ m) (hde : d ≤ e) (he : e ≤ m - 1)
    (i : Fin (m - 1)) :
    signedDiagonalRoot m ε e i ≤ signedDiagonalRoot m ε d i := by
  induction e generalizing d with
  | zero =>
      have hd : d = 0 := by lia
      subst d
      exact le_rfl
  | succ e ih =>
      by_cases hd : d = e + 1
      · subst d
        exact le_rfl
      · have hde' : d ≤ e := by lia
        have he' : e ≤ m - 2 := by lia
        exact ((consecutive_signedDiagonalRoot_interlacing m ε e hm he').1 i).le.trans
          (ih d hde' (by lia))

/-- Every nonzero nonexceptional diagonal has its roots in the exact gaps of
the Jacobi interlacer. The proof uses fixed-index chains through the adjacent
Darboux inequalities; it does not invoke transitivity of interlacing. -/
theorem signedDiagonalRoot_interlacing_jPolynomialRoot
    (m ε d : ℕ) (hm : 0 < m) (hd_pos : 0 < d) (hd : d ≤ m - 1) :
    (∀ i : Fin (m - 1),
      signedDiagonalRoot m ε d i < jPolynomialRoot m ε i) ∧
    ∀ (i j : Fin (m - 1)), i < j →
      jPolynomialRoot m ε i < signedDiagonalRoot m ε d j := by
  have hm_two : 2 ≤ m := by lia
  have hzero : ∀ i : Fin (m - 1),
      signedDiagonalRoot m ε 0 i = jPolynomialRoot m ε i := by
    intro i
    simp [signedDiagonalRoot, jPolynomialRoot, signedTriangleFamily]
  have hfirst := consecutive_signedDiagonalRoot_interlacing m ε 0 hm_two (by lia)
  have hterminal :=
    signedDiagonalRoot_terminal_interlacing_jPolynomialRoot m ε hm
  constructor
  · intro i
    have hchain : signedDiagonalRoot m ε d i ≤
        signedDiagonalRoot m ε 1 i :=
      signedDiagonalRoot_le_of_le m ε 1 d hm_two (by lia) hd i
    rw [← hzero i]
    exact lt_of_le_of_lt hchain (hfirst.1 i)
  · intro i j hij
    have hchain : signedDiagonalRoot m ε (m - 1) j ≤
        signedDiagonalRoot m ε d j :=
      signedDiagonalRoot_le_of_le m ε d (m - 1) hm_two hd le_rfl j
    exact (hterminal.2 i j hij).trans_le hchain

/-- At every Jacobi node, a nonzero nonexceptional signed diagonal has the
same derivative-oriented sign as the Jacobi interlacer. -/
theorem signedTriangleFamily_eval_mul_jPolynomial_derivative_pos
    (m ε d : ℕ) (hm : 0 < m) (hd_pos : 0 < d) (hd : d ≤ m - 1)
    (i : Fin (m - 1)) :
    0 < (signedTriangleFamily ((ε : ℝ) + 1 / 2)
          (jPolynomial m ε) d d).eval (jPolynomialRoot m ε i) *
        (jPolynomial m ε).derivative.eval (jPolynomialRoot m ε i) := by
  let S := signedTriangleFamily ((ε : ℝ) + 1 / 2)
    (jPolynomial m ε) d d
  let s : Fin (m - 1) → ℝ := signedDiagonalRoot m ε d
  let r : Fin (m - 1) → ℝ := jPolynomialRoot m ε
  have hS_data : IntervalRootData S (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε d d hm hd le_rfl
    dsimp only [S]
    convert hdata using 1
    lia
  have hJ_data : IntervalRootData (jPolynomial m ε) (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε 0 0 hm (by lia) le_rfl
    simpa [signedTriangleFamily] using hdata
  have hS_ne : S ≠ 0 := by
    intro hzero
    apply hS_data.eval_zero_ne
    simp [hzero]
  have hJ_ne : jPolynomial m ε ≠ 0 := by
    intro hzero
    apply hJ_data.eval_zero_ne
    simp [hzero]
  have hS_eq : S = C S.leadingCoeff *
      ∏ j : Fin (m - 1), (X - C (s j)) := by
    apply Polynomial.splits_eq_C_mul_prod hS_ne hS_data.natDegree_eq
      s (fun j => hS_data.orderedRoot_isRoot j)
    exact hS_data.strictMono_orderedRoot.injective
  have hJ_eq : jPolynomial m ε = C (jPolynomial m ε).leadingCoeff *
      ∏ j : Fin (m - 1), (X - C (r j)) := by
    apply Polynomial.splits_eq_C_mul_prod hJ_ne hJ_data.natDegree_eq
      r (fun j => hJ_data.orderedRoot_isRoot j)
    exact hJ_data.strictMono_orderedRoot.injective
  obtain ⟨hleft, hright⟩ :=
    signedDiagonalRoot_interlacing_jPolynomialRoot m ε d hm hd_pos hd
  have hprod := StrictMono.prod_sub_mul_prod_sub_pos_of_interlacing
    s r hJ_data.strictMono_orderedRoot hleft hright i
  let sign : ℝ := (-1 : ℝ) ^ (m - 1)
  have hS_zero : 0 < S.eval 0 := by
    exact signedTriangleFamily_diagonal_eval_zero_pos m ε d hm hd
  have hJ_zero : 0 < (jPolynomial m ε).eval 0 := by
    rw [jPolynomial_eval_zero m ε hm]
    norm_num
  have hS_leading := hS_data.hasPosLeadingCoeff_negOnePow_mul hS_zero
  have hJ_leading := hJ_data.hasPosLeadingCoeff_negOnePow_mul hJ_zero
  have hS_lead : 0 < sign * S.leadingCoeff := by
    rw [HasPosLeadingCoeff,
      Polynomial.leadingCoeff_C_mul_of_isUnit
        (isUnit_iff_ne_zero.mpr (pow_ne_zero (m - 1) (by norm_num)))] at hS_leading
    exact hS_leading
  have hJ_lead : 0 < sign * (jPolynomial m ε).leadingCoeff := by
    rw [HasPosLeadingCoeff,
      Polynomial.leadingCoeff_C_mul_of_isUnit
        (isUnit_iff_ne_zero.mpr (pow_ne_zero (m - 1) (by norm_num)))] at hJ_leading
    exact hJ_leading
  have hsign_sq : sign * sign = 1 := by
    dsimp only [sign]
    rw [← pow_two, ← pow_mul]
    simp
  have hleading : 0 < S.leadingCoeff * (jPolynomial m ε).leadingCoeff := by
    nlinarith [mul_pos hS_lead hJ_lead]
  have hevalS : S.eval (r i) =
      S.leadingCoeff * ∏ j : Fin (m - 1), (r i - s j) := by
    calc
      S.eval (r i) =
          (C S.leadingCoeff * ∏ j : Fin (m - 1), (X - C (s j))).eval
            (r i) := congrArg (Polynomial.eval (r i)) hS_eq
      _ = S.leadingCoeff * ∏ j : Fin (m - 1), (r i - s j) := by
        simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  have hevalJ : (jPolynomial m ε).derivative.eval (r i) =
      (jPolynomial m ε).leadingCoeff *
        ∏ j ∈ Finset.univ.erase i, (r i - r j) := by
    calc
      (jPolynomial m ε).derivative.eval (r i) =
          (C (jPolynomial m ε).leadingCoeff *
            ∏ j : Fin (m - 1), (X - C (r j))).derivative.eval (r i) :=
        congrArg (fun p : ℝ[X] => p.derivative.eval (r i)) hJ_eq
      _ = (jPolynomial m ε).leadingCoeff *
          ∏ j ∈ Finset.univ.erase i, (r i - r j) :=
        Polynomial.eval_derivative_C_mul_prod_X_sub_C_univ_at_root
          (jPolynomial m ε).leadingCoeff r i
  have heval :
      S.eval (r i) * (jPolynomial m ε).derivative.eval (r i) =
        (S.leadingCoeff * (jPolynomial m ε).leadingCoeff) *
          ((∏ j : Fin (m - 1), (r i - s j)) *
            ∏ j ∈ Finset.univ.erase i, (r i - r j)) := by
    rw [hevalS, hevalJ]
    ring
  change 0 < S.eval (r i) * (jPolynomial m ε).derivative.eval (r i)
  rw [heval]
  exact mul_pos hleading hprod

/-- The finite toric-contribution polynomial has the desired positive node
sign at every root of `J`, for every nonexceptional offset. -/
theorem rPolynomial_eval_mul_jPolynomial_derivative_pos
    (m ε d : ℕ) (hm : 0 < m) (hd_pos : 0 < d) (hd : d ≤ m - 1)
    (i : Fin (m - 1)) :
    0 < (rPolynomial m ε d).eval (jPolynomialRoot m ε i) *
      (jPolynomial m ε).derivative.eval (jPolynomialRoot m ε i) := by
  let S := signedTriangleFamily ((ε : ℝ) + 1 / 2)
    (jPolynomial m ε) d d
  let x := jPolynomialRoot m ε i
  obtain ⟨k, hk, hcollapse⟩ :=
    exists_one_sub_X_mul_signedTriangleFamily_diagonal_eq_C_mul_rPolynomial
      m ε d hm hd
  have hJ_data : IntervalRootData (jPolynomial m ε) (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε 0 0 hm (by lia) le_rfl
    simpa [signedTriangleFamily] using hdata
  have hxI := hJ_data.roots_mem_Ioo x (by
    have hJ_ne : jPolynomial m ε ≠ 0 := by
      intro hzero
      apply hJ_data.eval_zero_ne
      simp [hzero]
    exact (mem_roots hJ_ne).mpr (hJ_data.orderedRoot_isRoot i))
  have hsign := signedTriangleFamily_eval_mul_jPolynomial_derivative_pos
    m ε d hm hd_pos hd i
  have heval := congrArg (Polynomial.eval x) hcollapse
  change ((1 - X) * S).eval x =
    (C k * rPolynomial m ε d).eval x at heval
  simp only [eval_mul, eval_sub, eval_one, eval_X, eval_C] at heval
  have hpositive : 0 < k *
      ((rPolynomial m ε d).eval x *
        (jPolynomial m ε).derivative.eval x) := by
    calc
      k * ((rPolynomial m ε d).eval x *
          (jPolynomial m ε).derivative.eval x) =
          (k * (rPolynomial m ε d).eval x) *
            (jPolynomial m ε).derivative.eval x := by ring
      _ = ((1 - x) * S.eval x) *
          (jPolynomial m ε).derivative.eval x := by rw [heval]
      _ =
          (1 - x) * (S.eval x *
            (jPolynomial m ε).derivative.eval x) := by ring
      _ > 0 := mul_pos (sub_pos.mpr hxI.2) hsign
  rcases mul_pos_iff.mp hpositive with h | h
  · exact h.2
  · linarith

/-- The finite toric-contribution polynomial has the desired positive sign at
every root of `J`, without choosing an ordering index in the statement. -/
theorem rPolynomial_eval_mul_jPolynomial_derivative_pos_of_isRoot
    (m ε d : ℕ) (hm : 0 < m) (hd_pos : 0 < d) (hd : d ≤ m - 1)
    {x : ℝ} (hx : (jPolynomial m ε).IsRoot x) :
    0 < (rPolynomial m ε d).eval x *
      (jPolynomial m ε).derivative.eval x := by
  have hJ_data : IntervalRootData (jPolynomial m ε) (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε 0 0 hm (by lia) le_rfl
    simpa [signedTriangleFamily] using hdata
  have hJ_ne : jPolynomial m ε ≠ 0 := by
    intro hzero
    apply hJ_data.eval_zero_ne
    simp [hzero]
  obtain ⟨i, hi⟩ := exists_index_eq_of_mem_roots
    (jPolynomialRoot m ε) hJ_data.strictMono_orderedRoot
    (fun i => hJ_data.orderedRoot_isRoot i) hJ_ne hJ_data.natDegree_eq.le
    x ((mem_roots hJ_ne).mpr hx)
  rw [← hi]
  exact rPolynomial_eval_mul_jPolynomial_derivative_pos
    m ε d hm hd_pos hd i

end ToricContribution
end ParkingFunctions
end RealRooted
