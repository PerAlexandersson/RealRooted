module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.RankOneUpdate

/-!
# Expectations of rank-one determinant updates

The determinant `det (M - u uᵀ)` is affine in the rank-one matrix `u uᵀ`, so its expectation
over a finite distribution of vectors `u` equals `(1 - ∂ₜ) det (M + t A) |_{t=0}` with
`A = E[u uᵀ]`.  This is the one-variable step of Marcus–Spielman–Srivastava, Theorem 4.1.
-/

public section

open Polynomial

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

private theorem det_add_vecMulVec_trace (M : Matrix n n R) (u w : n → R) :
    (M + vecMulVec u w).det = M.det + (M.adjugate * vecMulVec u w).trace := by
  rw [Matrix.det_add_vecMulVec]
  congr 1
  simp only [trace, diag_apply, mul_apply, vecMulVec_apply, mulVec, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem eval_zero_det_mapC (M : Matrix n n R) :
    ((M.map C).det).eval 0 = M.det := by
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext
  simp

private theorem eval_zero_adjugate (N : Matrix n n R[X]) (M : Matrix n n R)
    (hN : N.map (eval 0) = M) (i j : n) : (N.adjugate i j).eval 0 = M.adjugate i j := by
  have h := RingHom.map_adjugate (evalRingHom (0 : R)) N
  have h2 : (evalRingHom (0 : R)).mapMatrix N = M := by
    rw [← hN]
    rfl
  rw [h2] at h
  rw [← h]
  rfl

private theorem derivative_det_rankOne_sum {ι : Type*} (s : Finset ι) (u w : ι → n → R)
    (M : Matrix n n R) :
    (derivative (M.map C + (X : R[X]) •
      (∑ k ∈ s, vecMulVec (u k) (w k)).map C).det).eval 0 =
      ∑ k ∈ s, (M.adjugate * vecMulVec (u k) (w k)).trace := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (M.map C).det = C M.det := (RingHom.map_det C M).symm
    simp [h0]
  | insert c s hc ih =>
    set N := M.map C + (X : R[X]) • (∑ k ∈ s, vecMulVec (u k) (w k)).map C with hNdef
    have hrewrite : M.map C + (X : R[X]) •
        (∑ k ∈ insert c s, vecMulVec (u k) (w k)).map C =
        N + vecMulVec ((X : R[X]) • (fun a => C (u c a))) (fun b => C (w c b)) := by
      refine Matrix.ext fun a b => ?_
      simp [hNdef, Finset.sum_insert hc, vecMulVec_apply, Matrix.sum_apply]
      ring
    rw [hrewrite, det_add_vecMulVec_trace, smul_vecMulVec, Matrix.mul_smul, trace_smul,
      smul_eq_mul, derivative_add, eval_add, ih, derivative_mul, derivative_X, one_mul,
      eval_add, eval_mul, eval_X, zero_mul, add_zero, Finset.sum_insert hc, add_comm]
    congr 1
    have hN : N.map (eval 0) = M := by
      ext a b
      simp [hNdef]
    simp only [trace, diag_apply, mul_apply, vecMulVec_apply, eval_finsetSum, eval_mul, eval_C,
      eval_zero_adjugate N M hN]

/-- Evaluating the derivative of a determinant pencil at zero gives its adjugate trace. -/
theorem eval_derivative_det_add_X_smul (M A : Matrix n n R) :
    (derivative (M.map C + (X : R[X]) • A.map C).det).eval 0 =
      (M.adjugate * A).trace := by
  have hA : A = ∑ k : n × n,
      vecMulVec (Pi.single k.1 (A k.1 k.2)) (Pi.single k.2 1) := by
    ext a b
    simp [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply, Fintype.sum_prod_type]
  rw [hA, derivative_det_rankOne_sum, ← trace_sum, ← Finset.mul_sum]

/-- A rank-one determinant pencil specializes to the determinant minus the adjugate trace. -/
theorem eval_one_sub_derivative_det_add_X_smul (M A : Matrix n n R) :
    (((M.map C + (X : R[X]) • A.map C).det : R[X]) -
      derivative ((M.map C + (X : R[X]) • A.map C).det)).eval 0 =
      M.det - (M.adjugate * A).trace := by
  rw [eval_sub, eval_derivative_det_add_X_smul, eval_det_add_X_smul, eval_zero_det_mapC]

omit [Fintype n] [DecidableEq n] in
private theorem map_vecMulVec {S : Type*} [CommRing S] (f : S →+* R) (u w : n → S) :
    (vecMulVec u w).map f = vecMulVec (fun a => f (u a)) (fun b => f (w b)) := by
  ext a b
  simp [vecMulVec_apply]

private theorem det_sub_vecMulVec_trace (M : Matrix n n R) (u : n → R) :
    (M - vecMulVec u u).det = M.det - (M.adjugate * vecMulVec u u).trace := by
  rw [sub_eq_add_neg, ← neg_vecMulVec, det_add_vecMulVec_trace, neg_vecMulVec, Matrix.mul_neg,
    trace_neg, ← sub_eq_add_neg]

/-- The expected determinant after a rank-one update depends only on the second moment. -/
theorem expected_det_sub_vecMulVec {S : Type*} [CommRing S] (f : S →+* R) {ι : Type*}
    [Fintype ι] (M : Matrix n n R) (v : ι → n → S) (p : ι → S) (hp : ∑ j, p j = 1) :
    ∑ j, f (p j) * (M - (vecMulVec (v j) (v j)).map f).det =
      M.det - (M.adjugate * (∑ j, p j • vecMulVec (v j) (v j)).map f).trace := by
  simp only [map_vecMulVec, det_sub_vecMulVec_trace, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← map_sum, hp, map_one, one_mul]
  congr 1
  have hsecondMoment : (∑ j, p j • vecMulVec (v j) (v j)).map f =
      ∑ j, f (p j) • vecMulVec (fun a => f (v j a)) (fun b => f (v j b)) := by
    ext a b
    simp [Matrix.sum_apply, vecMulVec_apply, map_sum]
  rw [hsecondMoment, Finset.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, trace_smul, smul_eq_mul]

end Matrix
