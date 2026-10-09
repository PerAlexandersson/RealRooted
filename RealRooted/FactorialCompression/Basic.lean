import RealRooted.Basic.Coefficients
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Factorial compression: definitions and coefficient formulas

The common Schur--Szegő kernel `commonKernel r`, the level-`ℓ` factorial compression of a
polynomial, the adjacent differential step `nextPolynomial`, and the degree-changing kernel
`kernel N ℓ a`, together with the exact coefficient formulas, positivity and degree facts that
do not involve roots.

The construction is due to Zhanhe Zhang (*Factorial compression and strict interlacing*,
SSRN 7510941); the proofs below are ported from the draft of Zhang's formalization.  The root
geometry lives in `RealRooted/FactorialCompression/CommonKernel.lean` and `Kernel.lean`.
-/

open Polynomial

namespace RealRooted.FactorialCompression

/-- The common Schur--Szegő kernel `h_r = ∑ⱼ r! / (j! (r - 2j)!) xʲ` of Zhang (SSRN 7510941). -/
noncomputable def commonKernel (r : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (r / 2 + 1),
    C ((r.factorial : ℝ) / ((j.factorial : ℝ) * ((r - 2 * j).factorial : ℝ))) * X ^ j

/-- The multiplier `(N - k)! / (N + ℓ - 2k)!` on `2k ≤ N + ℓ` (and `0` otherwise) of the
level-`ℓ` factorial compression of Zhang (SSRN 7510941). -/
noncomputable def multiplier (N ℓ k : ℕ) : ℝ :=
  if 2 * k ≤ N + ℓ then ((N - k).factorial : ℝ) / ((N + ℓ - 2 * k).factorial : ℝ) else 0

/-- The level-`ℓ` factorial compression `∑_{k ≤ N} μ_{N,ℓ,k} pₖ xᵏ` of a polynomial `p`
(Zhang, SSRN 7510941). -/
noncomputable def compression (N ℓ : ℕ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (N + 1), C (multiplier N ℓ k * p.coeff k) * X ^ k

/-- The adjacent differential step `(x + a) p + x p'` (Zhang, SSRN 7510941). -/
noncomputable def nextPolynomial (a : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (X + C a) * p + X * p.derivative

/-- The scalar `α = 1/4 + a (N + 1) / (m (m + 1))`, `m = N + ℓ`, in the kernel `kernel N ℓ a`. -/
noncomputable def kernelAlpha (N ℓ : ℕ) (a : ℝ) : ℝ :=
  1 / 4 + a * ((N : ℝ) + 1) / (((N + ℓ : ℕ) : ℝ) * (((N + ℓ : ℕ) : ℝ) + 1))

/-- The scalar `β = (N - ℓ + 1)(1/2 + a / (m + 1))`, `m = N + ℓ`, in the kernel
`kernel N ℓ a`. -/
noncomputable def kernelBeta (N ℓ : ℕ) (a : ℝ) : ℝ :=
  ((N : ℝ) - (ℓ : ℝ) + 1) * (1 / 2 + a / (((N + ℓ : ℕ) : ℝ) + 1))

/-- The degree-changing kernel `K_{N,ℓ,a} = α h_m + (β x - 1/4) h_{m-1}`, `m = N + ℓ`
(Zhang, SSRN 7510941). -/
noncomputable def kernel (N ℓ : ℕ) (a : ℝ) : ℝ[X] :=
  C (kernelAlpha N ℓ a) * commonKernel (N + ℓ) +
    (C (kernelBeta N ℓ a) * X - C (1 / 4 : ℝ)) * commonKernel (N + ℓ - 1)

/-! ### Coefficients of the common kernel -/

/-- The coefficients of the common kernel `h_r`. -/
theorem coeff_commonKernel (r k : ℕ) :
    (commonKernel r).coeff k = if 2 * k ≤ r then
      (r.factorial : ℝ) / ((k.factorial : ℝ) * ((r - 2 * k).factorial : ℝ)) else 0 := by
  classical
  have hi : k ≤ r / 2 ↔ 2 * k ≤ r := by lia
  simp [commonKernel, finsetSum_coeff, coeff_C_mul, coeff_X_pow, hi]

/-- A coefficient lowering identity for the common kernel, with the zero boundary included. -/
theorem mul_coeff_commonKernel_succ (r k : ℕ) :
    ((r : ℝ) + 1 - 2 * (k : ℝ)) * (commonKernel (r + 1)).coeff k =
      ((r : ℝ) + 1) * (commonKernel r).coeff k := by
  by_cases hk : 2 * k ≤ r
  · have hk' : 2 * k ≤ r + 1 := by lia
    have hi : r + 1 - 2 * k = (r - 2 * k) + 1 := by lia
    have hc : ((r - 2 * k : ℕ) : ℝ) + 1 = (r : ℝ) + 1 - 2 * (k : ℝ) := by
      have he : r = (r - 2 * k) + 2 * k := by lia
      have heq := congrArg (fun n : ℕ => (n : ℝ)) he
      push_cast at heq
      linarith
    rw [coeff_commonKernel, ite_eq_left hk', coeff_commonKernel, ite_eq_left hk, hi]
    simp only [Nat.factorial_succ]
    push_cast
    rw [hc]
    have hd : ((r - 2 * k).factorial : ℝ) ≠ 0 := by positivity
    have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
    have ha : (r : ℝ) + 1 - 2 * (k : ℝ) ≠ 0 := by
      rw [← hc]
      positivity
    field_simp
  · by_cases hk' : 2 * k ≤ r + 1
    · have he : 2 * k = r + 1 := by lia
      have hc : (r : ℝ) + 1 - 2 * (k : ℝ) = 0 := by
        have := congrArg (fun n : ℕ => (n : ℝ)) he
        push_cast at this
        linarith
      simp [coeff_commonKernel, hk, hk', hc]
    · simp [coeff_commonKernel, hk, hk']

/-- The coefficient shift identity relating `h_{r+2}` and `h_r`. -/
theorem mul_coeff_commonKernel_add_two_succ (r k : ℕ) :
    ((k : ℝ) + 1) * (commonKernel (r + 2)).coeff (k + 1) =
      ((r : ℝ) + 2) * ((r : ℝ) + 1) * (commonKernel r).coeff k := by
  have hi : 2 * (k + 1) ≤ r + 2 ↔ 2 * k ≤ r := by lia
  by_cases hk : 2 * k ≤ r
  · have hd : r + 2 - 2 * (k + 1) = r - 2 * k := by lia
    rw [coeff_commonKernel, ite_eq_left (hi.mpr hk), coeff_commonKernel, ite_eq_left hk, hd]
    simp only [show r + 2 = (r + 1) + 1 by lia, Nat.factorial_succ]
    push_cast
    have hdne : ((r - 2 * k).factorial : ℝ) ≠ 0 := by positivity
    have hkne : (k.factorial : ℝ) ≠ 0 := by positivity
    have hkn : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · simp [coeff_commonKernel, hk, hi]

/-- The constant coefficient of the common kernel is `1`. -/
@[simp] theorem coeff_commonKernel_zero (r : ℕ) : (commonKernel r).coeff 0 = 1 := by
  rw [coeff_commonKernel]
  simp only [mul_zero, Nat.zero_le, ite_true, Nat.factorial_zero, Nat.cast_one,
    one_mul, Nat.sub_zero]
  exact div_self (by positivity)

/-- Every supported coefficient of the common kernel is strictly positive. -/
theorem coeff_commonKernel_pos {r k : ℕ} (hk : 2 * k ≤ r) : 0 < (commonKernel r).coeff k := by
  rw [coeff_commonKernel, ite_eq_left hk]
  positivity

/-- The common kernel has nonnegative coefficients. -/
theorem hasNonnegCoeffs_commonKernel (r : ℕ) : HasNonnegCoeffs (commonKernel r) := by
  intro k
  rw [coeff_commonKernel]
  split <;> positivity

/-- The common kernel is nonzero. -/
theorem commonKernel_ne_zero (r : ℕ) : commonKernel r ≠ 0 := by
  intro heq
  have hz := coeff_commonKernel_zero r
  simp [heq] at hz

/-- The common kernel has a positive leading coefficient. -/
theorem hasPosLeadingCoeff_commonKernel (r : ℕ) : HasPosLeadingCoeff (commonKernel r) :=
  (hasNonnegCoeffs_commonKernel r).pos_leadingCoeff (commonKernel_ne_zero r)

/-- The degree of the common kernel `h_r` is `⌊r / 2⌋`. -/
theorem natDegree_commonKernel (r : ℕ) : (commonKernel r).natDegree = r / 2 := by
  apply Nat.le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_commonKernel, ite_eq_right (by lia)]
  · apply le_natDegree_of_ne_zero
    exact ne_of_gt (coeff_commonKernel_pos (r := r) (k := r / 2) (by lia))

/-! ### Coefficients of the compression and of the kernel -/

/-- The coefficients of the level-`ℓ` factorial compression. -/
theorem coeff_compression (N ℓ k : ℕ) (p : ℝ[X]) :
    (compression N ℓ p).coeff k = if k ≤ N then multiplier N ℓ k * p.coeff k else 0 := by
  classical
  unfold compression
  simp_rw [C_mul_X_pow_eq_monomial]
  rw [finsetSum_coeff]
  by_cases hk : k ≤ N
  · simp [coeff_monomial, hk]
  · simp [coeff_monomial, Nat.not_lt.mpr (Nat.succ_le_of_lt (Nat.lt_of_not_le hk)), hk]

/-- Scalar identity needed for the exact kernel coefficient calculation. -/
private theorem kernel_coefficient_bracket (N ℓ : ℕ) (a t : ℝ) (hN : N ≠ 0) :
    (kernelAlpha N ℓ a * ((N + ℓ : ℕ) : ℝ) -
        (1 / 4 : ℝ) * (((N + ℓ : ℕ) : ℝ) - 2 * t)) *
        (((N + ℓ : ℕ) : ℝ) + 1 - 2 * t) + kernelBeta N ℓ a * t =
      ((N : ℝ) + 1 - t) * (a + t) := by
  have hm : ((N + ℓ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show N + ℓ ≠ 0 by lia)
  have hm1 : ((N + ℓ : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  unfold kernelAlpha kernelBeta
  field_simp
  push_cast
  ring

/-- Division-free coefficient identity, valid at every parity endpoint and outside the support,
without any sign assumption on `a`. -/
private theorem coeff_kernel_normalized (N ℓ : ℕ) (a : ℝ) (k : ℕ) (hN : N ≠ 0) :
    (((N + ℓ : ℕ) : ℝ) * (((N + ℓ : ℕ) : ℝ) + 1)) * (kernel N ℓ a).coeff k =
      ((N : ℝ) + 1 - (k : ℝ)) * (a + (k : ℝ)) * (commonKernel (N + ℓ + 1)).coeff k := by
  have hm1 : N + ℓ - 1 + 1 = N + ℓ := by lia
  have hm2 : N + ℓ - 1 + 2 = N + ℓ + 1 := by lia
  have hmcast : ((N + ℓ - 1 : ℕ) : ℝ) + 1 = ((N + ℓ : ℕ) : ℝ) := by
    exact_mod_cast hm1
  have hmcast2 : ((N + ℓ - 1 : ℕ) : ℝ) + 2 = ((N + ℓ : ℕ) : ℝ) + 1 := by
    linarith [hmcast]
  cases k with
  | zero =>
      have hm : ((N + ℓ : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show N + ℓ ≠ 0 by lia)
      have hmpos : ((N + ℓ : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      simp only [kernel, sub_mul, mul_assoc, coeff_add, coeff_sub, coeff_C_mul,
        coeff_X_mul_zero, coeff_commonKernel_zero, Nat.cast_zero, sub_zero, add_zero, mul_one]
      unfold kernelAlpha
      field_simp
      ring
  | succ k =>
      have hs1 := mul_coeff_commonKernel_succ (N + ℓ) (k + 1)
      have hs0 := mul_coeff_commonKernel_succ (N + ℓ - 1) (k + 1)
      have hshift := mul_coeff_commonKernel_add_two_succ (N + ℓ - 1) k
      rw [hm1, hmcast] at hs0
      rw [hm2, hmcast, hmcast2] at hshift
      have hbr := kernel_coefficient_bracket N ℓ a ((k : ℝ) + 1) hN
      simp only [kernel, sub_mul, mul_assoc, coeff_add, coeff_sub,
        coeff_C_mul, coeff_X_mul]
      push_cast at hs1 hs0 hshift hbr ⊢
      linear_combination
        -(kernelAlpha N ℓ a * ((N : ℝ) + (ℓ : ℝ)) -
          (1 / 4 : ℝ) * ((N : ℝ) + (ℓ : ℝ) - 2 * ((k : ℝ) + 1))) * hs1 +
        (1 / 4 : ℝ) * ((N : ℝ) + (ℓ : ℝ) + 1) * hs0 -
        kernelBeta N ℓ a * hshift + (commonKernel (N + ℓ + 1)).coeff (k + 1) * hbr

/-- The exact all-index coefficient formula for the degree-changing kernel. -/
theorem coeff_kernel (N ℓ : ℕ) (a : ℝ) (k : ℕ) (hN : N ≠ 0) :
    (kernel N ℓ a).coeff k =
      if 2 * k ≤ N + ℓ + 1 then
        ((N + ℓ - 1).factorial : ℝ) /
          ((k.factorial : ℝ) * ((N + ℓ + 1 - 2 * k).factorial : ℝ)) *
            ((N : ℝ) + 1 - (k : ℝ)) * (a + (k : ℝ))
      else 0 := by
  have hn := coeff_kernel_normalized N ℓ a k hN
  have hm : ((N + ℓ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show N + ℓ ≠ 0 by lia)
  have hm1 : ((N + ℓ : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  have hKnorm : (kernel N ℓ a).coeff k =
      (((N : ℝ) + 1 - (k : ℝ)) * (a + (k : ℝ)) * (commonKernel (N + ℓ + 1)).coeff k) /
        (((N + ℓ : ℕ) : ℝ) * (((N + ℓ : ℕ) : ℝ) + 1)) := by
    apply (eq_div_iff (mul_ne_zero hm hm1)).mpr
    simpa only [mul_comm] using hn
  by_cases hguard : 2 * k ≤ N + ℓ + 1
  · rw [ite_eq_left hguard, hKnorm, coeff_commonKernel, ite_eq_left hguard]
    have hpred : (N + ℓ) * (N + ℓ - 1).factorial = (N + ℓ).factorial :=
      Nat.mul_factorial_pred (by lia)
    have hpredcast := congrArg (fun n : ℕ => (n : ℝ)) hpred
    push_cast at hpredcast
    have hsuc : ((N + ℓ + 1).factorial : ℝ) =
        (((N + ℓ : ℕ) : ℝ) + 1) * ((N + ℓ).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      rfl
    rw [hsuc, ← hpredcast]
    have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
    have hden : ((N + ℓ + 1 - 2 * k).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  · rw [ite_eq_right hguard]
    rw [coeff_commonKernel, ite_eq_right hguard] at hn
    exact (mul_eq_zero.mp (by simpa using hn)).resolve_left (mul_ne_zero hm hm1)

/-- The coefficients of the degree-changing kernel on its support `2k ≤ N + ℓ + 1`. -/
theorem coeff_kernel_of_le (N ℓ : ℕ) (a : ℝ) (k : ℕ) (hN : N ≠ 0) (hguard : 2 * k ≤ N + ℓ + 1) :
    (kernel N ℓ a).coeff k =
      ((N + ℓ - 1).factorial : ℝ) /
        ((k.factorial : ℝ) * ((N + ℓ + 1 - 2 * k).factorial : ℝ)) *
          ((N : ℝ) + 1 - (k : ℝ)) * (a + (k : ℝ)) := by
  rw [coeff_kernel N ℓ a k hN, ite_eq_left hguard]

/-- For `ℓ = 1` and `a = (N + 2) / 2` the kernel is
`3/4 h_{N+1} + (N x - 1/4) h_N`. -/
theorem kernel_one_eq (N : ℕ) :
    kernel N 1 (((N : ℝ) + 2) / 2) =
      C (3 / 4 : ℝ) * commonKernel (N + 1) + (C (N : ℝ) * X - C (1 / 4 : ℝ)) * commonKernel N := by
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  have hN2 : (N : ℝ) + 2 ≠ 0 := by positivity
  have hα : kernelAlpha N 1 (((N : ℝ) + 2) / 2) = 3 / 4 := by
    unfold kernelAlpha
    push_cast
    field_simp
    ring
  have hβ : kernelBeta N 1 (((N : ℝ) + 2) / 2) = N := by
    unfold kernelBeta
    push_cast
    field_simp
    ring
  simp only [kernel, hα, hβ, Nat.add_sub_cancel]

end RealRooted.FactorialCompression
