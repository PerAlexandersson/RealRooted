module

public import RealRooted.DerivativeProduct.Associative
public import RealRooted.RootLocation.Basic
import RealRooted.DerivativeProduct.KernelSufficiency
import RealRooted.RootLocation.DerivativeSigns
import Mathlib.Tactic

/-!
# Root intervals are stable under the diamond product

Let `G` be rooted in `[-1, 0]` and `R` rooted in `[A, B]` with `A ≤ -1` and `B ≥ 0`.  Then the
diamond product `G ⋄ R = ∑ k, [X (X + 1)] ^ k / (k!) ^ 2 * G ^ (k) * R ^ (k)` is rooted in
`[A, B]` (`RealRooted.betaProduct_one_isRealRootedIn_Icc`).

Real-rootedness is Brändén's theorem (`betaProduct_isRealRootedIn_univ`).  For the location,
outside `[A, B]` the weight `X (X + 1)` is positive and all the derivatives of `G` and `R` have
the sign dictated by the leading coefficients (`RealRooted.RootLocation.DerivativeSigns`), so all
the summands have the same sign and the `k = 0` summand is nonzero.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- **Sign-coherent derivative products do not vanish.**  If the coefficients `c k` are
nonnegative with `c 0 = 1`, the weight is nonnegative at `x`, and after multiplication by a
fixed `s` all the products `G ^ (k) (x) * R ^ (k) (x)` are nonnegative and the one with
`k = 0` is positive, then `(G ⋆ R) (x) ≠ 0`. -/
theorem eval_derivProduct_ne_zero {w : ℝ[X]} {c : ℕ → ℝ} {G R : ℝ[X]} {x s : ℝ}
    (hc0 : c 0 = 1) (hc : ∀ k, 0 ≤ c k) (hw : 0 ≤ w.eval x)
    (hsign : ∀ k, 0 ≤ s * ((derivative^[k] G).eval x * (derivative^[k] R).eval x))
    (h0 : 0 < s * (G.eval x * R.eval x)) : (derivProduct w c G R).eval x ≠ 0 := by
  intro h
  have hsum : s * (derivProduct w c G R).eval x = ∑ k ∈ Finset.range (G.natDegree + 1),
      c k * (w.eval x) ^ k * (s * ((derivative^[k] G).eval x * (derivative^[k] R).eval x)) := by
    simp only [derivProduct, eval_finsetSum, eval_mul, eval_C, eval_pow, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [h, mul_zero, Finset.sum_range_succ'] at hsum
  have hnn : 0 ≤ ∑ k ∈ Finset.range G.natDegree,
      c (k + 1) * (w.eval x) ^ (k + 1) *
        (s * ((derivative^[k + 1] G).eval x * (derivative^[k + 1] R).eval x)) :=
    Finset.sum_nonneg fun k _ ↦ mul_nonneg (mul_nonneg (hc _) (pow_nonneg hw _)) (hsign _)
  simp only [hc0, pow_zero, one_mul, Function.iterate_zero, id] at hsum
  linarith

private theorem eval_ne_zero_of_isRealRootedIn_Icc {S : Set ℝ} {q : ℝ[X]}
    (hq : IsRealRootedIn S q) {x : ℝ} (hx : x ∉ S) : q.eval x ≠ 0 := fun h ↦
  hx (hq.mem_of_isRoot h)

/-- The diamond product of a polynomial rooted in `[-1, 0]` and one with all roots at most `B`
does not vanish to the right of `B`, where `B ≥ 0`. -/
private theorem eval_betaProduct_one_ne_zero_of_lt {G R : ℝ[X]} {B x : ℝ}
    (hG : IsRealRootedIn (Icc (-1) 0) G) (hR : IsRealRootedIn (Iic B) R) (hB : 0 ≤ B)
    (hx : B < x) : (betaProduct 1 G R).eval x ≠ 0 := by
  have hxpos : 0 < x := hB.trans_lt hx
  have hG' : IsRealRootedIn (Iic x) G := hG.mono fun r hr ↦ by
    simp only [mem_Icc] at hr
    simp only [mem_Iic]
    linarith [hr.2]
  have hR' : IsRealRootedIn (Iic x) R := hR.mono fun r hr ↦ by simp only [mem_Iic] at hr ⊢; linarith
  have hlcG : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hG.ne_zero
  have hlcR : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR.ne_zero
  have hGx : G.eval x ≠ 0 := eval_ne_zero_of_isRealRootedIn_Icc hG (by simp [hxpos])
  have hRx : R.eval x ≠ 0 :=
    eval_ne_zero_of_isRealRootedIn_Icc hR (by simp only [mem_Iic, not_le]; exact hx)
  refine eval_derivProduct_ne_zero (s := G.leadingCoeff * R.leadingCoeff) (betaCoeff_zero 1)
    (betaCoeff_nonneg one_pos) (by simp only [eval_mul, eval_X, eval_add, eval_one]; positivity)
    (fun k ↦ ?_) ?_
  · have h1 := hG'.leadingCoeff_mul_eval_iterate_derivative_nonneg k
    have h2 := hR'.leadingCoeff_mul_eval_iterate_derivative_nonneg k
    nlinarith [mul_nonneg h1 h2]
  · have h1 := hG'.leadingCoeff_mul_eval_iterate_derivative_nonneg 0
    have h2 := hR'.leadingCoeff_mul_eval_iterate_derivative_nonneg 0
    simp only [Function.iterate_zero, id] at h1 h2
    have h1' : 0 < G.leadingCoeff * G.eval x := lt_of_le_of_ne h1 (Ne.symm (mul_ne_zero hlcG hGx))
    have h2' : 0 < R.leadingCoeff * R.eval x := lt_of_le_of_ne h2 (Ne.symm (mul_ne_zero hlcR hRx))
    nlinarith [mul_pos h1' h2']

/-- The diamond product of a polynomial rooted in `[-1, 0]` and one with all roots at least `A`
does not vanish to the left of `A`, where `A ≤ -1`. -/
private theorem eval_betaProduct_one_ne_zero_of_gt {G R : ℝ[X]} {A x : ℝ}
    (hG : IsRealRootedIn (Icc (-1) 0) G) (hR : IsRealRootedIn (Ici A) R) (hA : A ≤ -1)
    (hx : x < A) : (betaProduct 1 G R).eval x ≠ 0 := by
  have hxneg : x < -1 := hx.trans_le hA
  have hG' : IsRealRootedIn (Ici x) G := hG.mono fun r hr ↦ by
    simp only [mem_Icc] at hr; simp only [mem_Ici]; linarith [hr.1]
  have hR' : IsRealRootedIn (Ici x) R := hR.mono fun r hr ↦ by
    simp only [mem_Ici] at hr ⊢; linarith
  have hlcG : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hG.ne_zero
  have hlcR : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR.ne_zero
  have hGx : G.eval x ≠ 0 :=
    eval_ne_zero_of_isRealRootedIn_Icc hG (by
      simp only [mem_Icc, not_and, not_le]
      intro h
      linarith)
  have hRx : R.eval x ≠ 0 :=
    eval_ne_zero_of_isRealRootedIn_Icc hR (by simp only [mem_Ici, not_le]; exact hx)
  have key : ∀ k : ℕ, ∀ a b : ℝ,
      (-1 : ℝ) ^ (G.natDegree + R.natDegree) * (G.leadingCoeff * R.leadingCoeff) * (a * b) =
        ((-1) ^ (G.natDegree + k) * G.leadingCoeff * a) *
          ((-1) ^ (R.natDegree + k) * R.leadingCoeff * b) := fun k a b ↦ by
    have h : ((-1 : ℝ) ^ k) * ((-1) ^ k) = 1 := by rw [← mul_pow]; norm_num
    rw [pow_add, pow_add, pow_add]
    linear_combination (-((-1 : ℝ) ^ G.natDegree * (-1) ^ R.natDegree * G.leadingCoeff *
      R.leadingCoeff * a * b)) * h
  refine eval_derivProduct_ne_zero
    (s := (-1 : ℝ) ^ (G.natDegree + R.natDegree) * (G.leadingCoeff * R.leadingCoeff))
    (betaCoeff_zero 1) (betaCoeff_nonneg one_pos)
    (by simp only [eval_mul, eval_X, eval_add, eval_one]; nlinarith) (fun k ↦ ?_) ?_
  · rw [key]
    exact mul_nonneg (hG'.negOnePow_mul_eval_iterate_derivative_nonneg k)
      (hR'.negOnePow_mul_eval_iterate_derivative_nonneg k)
  · rw [key 0]
    have h1 := hG'.negOnePow_mul_eval_iterate_derivative_nonneg 0
    have h2 := hR'.negOnePow_mul_eval_iterate_derivative_nonneg 0
    simp only [Function.iterate_zero, id, add_zero] at h1 h2 ⊢
    have hne1 : (-1 : ℝ) ^ G.natDegree * G.leadingCoeff * G.eval x ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hlcG) hGx
    have hne2 : (-1 : ℝ) ^ R.natDegree * R.leadingCoeff * R.eval x ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hlcR) hRx
    exact mul_pos (lt_of_le_of_ne h1 (Ne.symm hne1)) (lt_of_le_of_ne h2 (Ne.symm hne2))

/-- **Root intervals are stable under the diamond product.**  If `G` is rooted in `[-1, 0]` and
`R` is rooted in `[A, B]` with `A ≤ -1` and `0 ≤ B`, then the diamond product `G ⋄ R` is rooted
in `[A, B]`.  Real-rootedness is Brändén's theorem (`betaProduct_isRealRootedIn_univ`). -/
theorem betaProduct_one_isRealRootedIn_Icc {A B : ℝ} (hA : A ≤ -1) (hB : 0 ≤ B) {G R : ℝ[X]}
    (hG : IsRealRootedIn (Icc (-1) 0) G) (hR : IsRealRootedIn (Icc A B) R) :
    IsRealRootedIn (Icc A B) (betaProduct 1 G R) := by
  have huniv := betaProduct_isRealRootedIn_univ one_pos hG (hR.mono (subset_univ _))
  refine ⟨huniv.ne_zero, huniv.splits, fun x hx ↦ ?_⟩
  have hroot : (betaProduct 1 G R).eval x = 0 := (mem_roots huniv.ne_zero).1 hx
  by_contra hxn
  simp only [mem_Icc, not_and, not_le] at hxn
  by_cases hxA : A ≤ x
  · exact eval_betaProduct_one_ne_zero_of_lt hG (hR.mono fun r hr ↦ hr.2) hB (hxn hxA) hroot
  · exact eval_betaProduct_one_ne_zero_of_gt hG (hR.mono fun r hr ↦ hr.1) hA
      (lt_of_not_ge hxA) hroot

end RealRooted
