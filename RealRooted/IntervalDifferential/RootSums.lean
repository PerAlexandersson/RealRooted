/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.Certificates
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Root-sum inequalities for the centered zigzag transfer

For a product of real linear factors, the second Laguerre expression is a
sum of squares of the one-root cofactors. Cauchy--Schwarz then proves the
Appendix C.2 inequality for `zigzagK`. A separate linear-factor identity
gives strict positivity of `zigzagJ` inside the root interval.
-/

@[expose] public noncomputable section

namespace RealRooted.IntervalDifferential

open Polynomial

/-- The monic product with the listed real roots, including multiplicity. -/
private def zigzagRootProduct (roots : List ℝ) : ℝ[X] :=
  (roots.map (fun r => X - C r)).prod

/-- The list of cofactor polynomials obtained by deleting one listed root. -/
private def zigzagRootCofactors : List ℝ → List ℝ[X]
  | [] => []
  | r :: roots => zigzagRootProduct roots ::
      (zigzagRootCofactors roots).map (fun p => (X - C r) * p)

private theorem zigzagRootCofactors_length (roots : List ℝ) :
    (zigzagRootCofactors roots).length = roots.length := by
  induction roots with
  | nil => simp [zigzagRootCofactors]
  | cons r roots ih => simp [zigzagRootCofactors, ih]

/-- The weighted cofactor sum that represents `zigzagJ`. -/
private def zigzagRootJSum : List ℝ → ℝ[X]
  | [] => 0
  | r :: roots => C (1 - r ^ 2) * zigzagRootProduct roots ^ 2 +
      (X - C r) ^ 2 * zigzagRootJSum roots

/-- The derivative of a listed-root product is the sum of its one-root
cofactors. -/
private theorem zigzagRootProduct_derivative (roots : List ℝ) :
    (zigzagRootProduct roots).derivative = (zigzagRootCofactors roots).sum := by
  induction roots with
  | nil => simp [zigzagRootProduct, zigzagRootCofactors]
  | cons r roots ih =>
    change ((X - C r) * zigzagRootProduct roots).derivative =
      zigzagRootProduct roots +
        ((zigzagRootCofactors roots).map (fun p => (X - C r) * p)).sum
    rw [derivative_mul, derivative_X_sub_C, one_mul]
    rw [ih, List.sum_map_mul_left]
    simp only [List.map_id']

/-- Laguerre's identity for a product of real linear factors. -/
private theorem zigzagRootProduct_laguerre (roots : List ℝ) :
    (zigzagRootProduct roots).derivative ^ 2 -
        zigzagRootProduct roots * (zigzagRootProduct roots).derivative.derivative =
      ((zigzagRootCofactors roots).map (fun p => p ^ 2)).sum := by
  induction roots with
  | nil => simp [zigzagRootProduct, zigzagRootCofactors]
  | cons r roots ih =>
    let v : ℝ[X] := X - C r
    let F : ℝ[X] := zigzagRootProduct roots
    have hder : (v * F).derivative = F + v * F.derivative := by
      simp [v, derivative_mul]
    have hv : v.derivative = 1 := by simp [v]
    have hderder : (v * F).derivative.derivative =
        C 2 * F.derivative + v * F.derivative.derivative := by
      rw [hder, derivative_add, derivative_mul, hv]
      norm_num [Polynomial.C_ofNat]
      ring
    have hmap :
        ((zigzagRootCofactors roots).map (fun p => (v * p) ^ 2)).sum =
          v ^ 2 * ((zigzagRootCofactors roots).map (fun p => p ^ 2)).sum := by
      simp only [mul_pow, List.sum_map_mul_left]
    change (v * F).derivative ^ 2 - (v * F) * (v * F).derivative.derivative =
      ((zigzagRootProduct roots ::
        (zigzagRootCofactors roots).map (fun p => v * p)).map (fun p => p ^ 2)).sum
    have ihF : F.derivative ^ 2 - F * F.derivative.derivative =
        ((zigzagRootCofactors roots).map (fun p => p ^ 2)).sum := by
      simpa [F] using ih
    rw [hderder, hder]
    simp only [List.map_cons, List.sum_cons]
    calc
      (F + v * F.derivative) ^ 2 -
          v * F * (C 2 * F.derivative + v * F.derivative.derivative) =
        F ^ 2 + v ^ 2 * (F.derivative ^ 2 - F * F.derivative.derivative) := by
          norm_num [Polynomial.C_ofNat]
          ring
      _ = F ^ 2 + v ^ 2 *
          ((zigzagRootCofactors roots).map (fun p => p ^ 2)).sum := by
          rw [ihF]
      _ = F ^ 2 +
          ((zigzagRootCofactors roots).map (fun p => (v * p) ^ 2)).sum := by
          rw [← hmap]
      _ = F ^ 2 +
          (((zigzagRootCofactors roots).map (fun p => v * p)).map
            (fun p => p ^ 2)).sum := by
          congr 1
          simp only [List.map_map, Function.comp_def]
      _ = zigzagRootProduct roots ^ 2 +
          (((zigzagRootCofactors roots).map (fun p => v * p)).map
            (fun p => p ^ 2)).sum := by
          rfl

/-- The finite-list Cauchy--Schwarz remainder is nonnegative. -/
private theorem zigzag_list_cauchy_remainder (values : List ℝ) :
    0 ≤ (values.length : ℝ) * (values.map (fun x => x ^ 2)).sum -
      values.sum ^ 2 := by
  apply sub_nonneg.mpr
  simpa using Multiset.sq_sum_le_card_mul_sum_sq (Multiset.ofList values)

/-- `zigzagJ` obeys the factor-insertion identity from Appendix C.2. -/
theorem zigzagJ_linear_factor (d : ℕ) (r : ℝ) (F : ℝ[X]) :
    zigzagJ (d + 1) ((X - C r) * F) =
      (X - C r) ^ 2 * zigzagJ d F + C (1 - r ^ 2) * F ^ 2 := by
  simp [zigzagJ, derivative_mul, Nat.cast_add,
    Nat.cast_one, Polynomial.C_ofNat]
  ring

/-- `zigzagJ` on a listed-root product is its positive weighted cofactor
sum. -/
private theorem zigzagJ_rootProduct_eq (roots : List ℝ) :
    zigzagJ roots.length (zigzagRootProduct roots) = zigzagRootJSum roots := by
  induction roots with
  | nil => simp [zigzagJ, zigzagRootProduct, zigzagRootJSum]
  | cons r roots ih =>
    change zigzagJ (roots.length + 1) ((X - C r) * zigzagRootProduct roots) =
      zigzagRootJSum (r :: roots)
    rw [zigzagJ_linear_factor, ih]
    simp only [zigzagRootJSum, map_sub, map_one, map_pow]
    ring_nf

/-- The root-sum expression for `zigzagJ` is nonnegative when all listed roots
belong to `(-1,1)`. -/
private theorem zigzagRootJSum_eval_nonneg (roots : List ℝ)
    (hroots : ∀ r ∈ roots, -1 < r ∧ r < 1) (x : ℝ) :
    0 ≤ (zigzagRootJSum roots).eval x := by
  induction roots with
  | nil => simp [zigzagRootJSum]
  | cons r roots ih =>
    have hr := hroots r (by simp)
    have htail : ∀ t ∈ roots, -1 < t ∧ t < 1 := by
      intro t ht
      exact hroots t (List.mem_cons_of_mem r ht)
    have hrootsum := ih htail
    simp only [zigzagRootJSum, eval_add, eval_mul, eval_C, eval_pow,
      eval_sub, eval_X]
    exact add_nonneg (mul_nonneg (by nlinarith [sq_nonneg r]) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) hrootsum)

/-- Away from the roots, the same root-sum is strictly positive. -/
private theorem zigzagRootJSum_eval_pos_of_eval_ne_zero (roots : List ℝ)
    (hroots : ∀ r ∈ roots, -1 < r ∧ r < 1) (x : ℝ)
    (hnil : roots ≠ []) (hx : (zigzagRootProduct roots).eval x ≠ 0) :
    0 < (zigzagRootJSum roots).eval x := by
  cases roots with
  | nil => contradiction
  | cons r roots =>
    have hr := hroots r (by simp)
    have htail : ∀ t ∈ roots, -1 < t ∧ t < 1 := by
      intro t ht
      exact hroots t (List.mem_cons_of_mem r ht)
    have hrootsum := zigzagRootJSum_eval_nonneg roots htail x
    have hprod : (x - r) * (zigzagRootProduct roots).eval x ≠ 0 := by
      simpa [zigzagRootProduct, eval_mul, eval_sub, eval_C, eval_X] using hx
    have hF : (zigzagRootProduct roots).eval x ≠ 0 :=
      (mul_ne_zero_iff.mp hprod).2
    have hweight : 0 < 1 - r ^ 2 := by nlinarith [sq_nonneg r]
    simp only [zigzagRootJSum, eval_add, eval_mul, eval_C, eval_pow,
      eval_sub, eval_X]
    have hfirst : 0 < (1 - r ^ 2) * (zigzagRootProduct roots).eval x ^ 2 :=
      mul_pos hweight (sq_pos_of_ne_zero hF)
    exact add_pos_of_pos_of_nonneg hfirst
      (mul_nonneg (sq_nonneg _) hrootsum)

/-- Scaling a polynomial scales `zigzagJ` by the square of the scalar. -/
theorem zigzagJ_scale (d : ℕ) (c : ℝ) (F : ℝ[X]) :
    zigzagJ d (C c * F) = C (c ^ 2) * zigzagJ d F := by
  simp [zigzagJ]
  ring

/-- Scaling a polynomial scales `zigzagK` by the square of the scalar. -/
theorem zigzagK_scale (d : ℕ) (c : ℝ) (F : ℝ[X]) :
    zigzagK d (C c * F) = C (c ^ 2) * zigzagK d F := by
  simp [zigzagK]
  ring

private theorem zigzagRootProduct_toList (roots : Multiset ℝ) :
    zigzagRootProduct roots.toList = (roots.map (fun r => X - C r)).prod := by
  exact Multiset.prod_map_toList roots (fun r => X - C r)

/-- For a split polynomial, `zigzagJ` is strictly positive at every point
which is not a root, provided all roots lie in `(-1,1)` and the degree is
positive. -/
theorem zigzagJ_eval_pos_of_splits (F : ℝ[X])
    (hF : F.Splits) (hdeg : 0 < F.natDegree)
    (hroots : ∀ r ∈ F.roots, -1 < r ∧ r < 1) (x : ℝ)
    (hx : F.eval x ≠ 0) :
    0 < (zigzagJ F.natDegree F).eval x := by
  let roots : List ℝ := F.roots.toList
  have hlength : roots.length = F.natDegree := by
    dsimp [roots]
    rw [Multiset.length_toList, hF.natDegree_eq_card_roots]
  have hfactor : F = C F.leadingCoeff * zigzagRootProduct roots := by
    dsimp [roots]
    calc
      F = C F.leadingCoeff * (F.roots.map (fun r => X - C r)).prod := hF.eq_prod_roots
      _ = C F.leadingCoeff * zigzagRootProduct F.roots.toList := by
        rw [zigzagRootProduct_toList]
  have hlc : F.leadingCoeff ≠ 0 := by
    apply leadingCoeff_ne_zero.mpr
    exact ne_zero_of_natDegree_gt hdeg
  have hnonempty : roots ≠ [] := by
    intro hempty
    change F.roots.toList = [] at hempty
    have hcard : F.natDegree = F.roots.card := hF.natDegree_eq_card_roots
    have hcard0 : F.roots.card = 0 := by
      simpa [hempty] using (Multiset.length_toList F.roots).symm
    rw [hcard0] at hcard
    lia
  have hrootsList : ∀ r ∈ roots, -1 < r ∧ r < 1 := by
    intro r hr
    dsimp [roots] at hr
    exact hroots r (by simpa using hr)
  have hprod : (zigzagRootProduct roots).eval x ≠ 0 := by
    have hEval := congrArg (fun p : ℝ[X] => p.eval x) hfactor
    simp only [eval_mul, eval_C] at hEval
    intro hzero
    rw [hzero, mul_zero] at hEval
    exact hx hEval
  rw [← hlength, hfactor, zigzagJ_scale, zigzagJ_rootProduct_eq]
  have hpos := zigzagRootJSum_eval_pos_of_eval_ne_zero roots
    hrootsList x hnonempty hprod
  have hsq : 0 < F.leadingCoeff ^ 2 := sq_pos_of_ne_zero hlc
  simp only [eval_mul, eval_C]
  exact mul_pos hsq hpos

/-- `zigzagK` is nonnegative for every split real polynomial. -/
theorem zigzagK_eval_nonneg_of_splits (F : ℝ[X]) (hF : F.Splits) (x : ℝ) :
    0 ≤ (zigzagK F.natDegree F).eval x := by
  let roots : List ℝ := F.roots.toList
  have hlength : roots.length = F.natDegree := by
    dsimp [roots]
    rw [Multiset.length_toList, hF.natDegree_eq_card_roots]
  have hfactor : F = C F.leadingCoeff * zigzagRootProduct roots := by
    dsimp [roots]
    calc
      F = C F.leadingCoeff * (F.roots.map (fun r => X - C r)).prod := hF.eq_prod_roots
      _ = C F.leadingCoeff * zigzagRootProduct F.roots.toList := by
        rw [zigzagRootProduct_toList]
  rw [← hlength, hfactor, zigzagK_scale]
  have hder : (zigzagRootProduct roots).derivative.eval x =
      ((zigzagRootCofactors roots).map (fun p : ℝ[X] => p.eval x)).sum := by
    rw [zigzagRootProduct_derivative]
    exact eval_listSum (zigzagRootCofactors roots) x
  have hlag := congrArg (fun p : ℝ[X] => p.eval x)
    (zigzagRootProduct_laguerre roots)
  simp only [eval_sub, eval_mul, eval_pow, eval_listSum] at hlag
  let values := (zigzagRootCofactors roots).map (fun p : ℝ[X] => p.eval x)
  have hlag' :
      ((zigzagRootProduct roots).derivative.eval x) ^ 2 -
          (zigzagRootProduct roots).eval x *
            (zigzagRootProduct roots).derivative.derivative.eval x =
        (values.map (fun y => y ^ 2)).sum := by
    simpa [values, List.map_map, Function.comp_def, eval_pow] using hlag
  have hder' : (zigzagRootProduct roots).derivative.eval x = values.sum := by
    simpa [values] using hder
  have hvalues : values.length = roots.length := by
    simp only [values, List.length_map]
    exact zigzagRootCofactors_length roots
  have hk : (zigzagK roots.length (zigzagRootProduct roots)).eval x =
      (values.length : ℝ) * (values.map (fun y => y ^ 2)).sum - values.sum ^ 2 := by
    have hsecond :
        (zigzagRootProduct roots).eval x *
          (zigzagRootProduct roots).derivative.derivative.eval x =
          ((zigzagRootProduct roots).derivative.eval x) ^ 2 -
            (values.map (fun y => y ^ 2)).sum := by
      linarith [hlag']
    simp only [zigzagK, eval_sub, eval_mul, eval_C, eval_pow]
    rw [hder']
    have hsecond' : (roots.length : ℝ) *
        (zigzagRootProduct roots).eval x *
          (zigzagRootProduct roots).derivative.derivative.eval x =
        (roots.length : ℝ) *
          (values.sum ^ 2 - (values.map (fun y => y ^ 2)).sum) := by
      calc
        _ = (roots.length : ℝ) *
            ((zigzagRootProduct roots).eval x *
              (zigzagRootProduct roots).derivative.derivative.eval x) := by
                rw [mul_assoc]
        _ = _ := by rw [hsecond, hder']
    rw [hsecond', ← hvalues]
    ring
  have hnonneg := zigzag_list_cauchy_remainder values
  have hbase : 0 ≤
      (zigzagK roots.length (zigzagRootProduct roots)).eval x := by
    rw [hk]
    exact hnonneg
  simp only [eval_mul, eval_C]
  exact mul_nonneg (sq_nonneg _) hbase

end RealRooted.IntervalDifferential
