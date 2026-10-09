import RealRooted.FactorialCompression.CommonKernel
import RealRooted.Hadamard.SchurSzegoStrict

/-!
# Factorial compression as a Schur--Szegő composition

For arbitrary `p` the level-`ℓ` factorial compression `T^{(ℓ)}_N p` is a scalar multiple of the
Schur--Szegő composition `schurSzegoComp N (commonKernel (N + ℓ)) p` (the multiplier `p` stands
on the right, as in `RealRooted/Hadamard/SchurSzegoStrict.lean`).  For `p` of degree at most `N`
the compression of the adjacent differential step `nextPolynomial a p` is, up to a scalar, the
composition of `p` with `kernel N ℓ a`, plus `X` times the composition of `p` with
`commonKernel (N + ℓ - 1)`.  No sign hypothesis on `p` is needed for any of these identities.
The derivative identity of the common kernel passes through the composition via the Euler
operator.

The construction is due to Zhanhe Zhang (*Factorial compression and strict interlacing*,
SSRN 7510941); the proofs are ported from the draft of Zhang's formalization.
-/

open Polynomial

namespace RealRooted.FactorialCompression

/-- Binomial/factorial normalization of the multiplier, including absent coefficients. -/
private theorem choose_mul_multiplier (N ℓ k : ℕ) (hk : k ≤ N) :
    (Nat.choose N k : ℝ) * multiplier N ℓ k =
      (N.factorial : ℝ) / ((N + ℓ).factorial : ℝ) * (commonKernel (N + ℓ)).coeff k := by
  by_cases hguard : 2 * k ≤ N + ℓ
  · have hfac : (Nat.choose N k : ℝ) * (k.factorial : ℝ) * ((N - k).factorial : ℝ) =
        (N.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
    rw [multiplier, ite_eq_left hguard, coeff_commonKernel, ite_eq_left hguard]
    have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
    have hmfac : ((N + ℓ).factorial : ℝ) ≠ 0 := by positivity
    have hden : ((N + ℓ - 2 * k).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith [hfac]
  · simp only [multiplier, coeff_commonKernel, hguard, ite_false, mul_zero]

/-- The factorial compression is a scalar multiple of the Schur--Szegő composition of the common
kernel `h_{N+ℓ}` with `p`; no sign hypothesis on `p` is needed. -/
theorem compression_eq_schurSzegoComp (N ℓ : ℕ) (p : ℝ[X]) :
    compression N ℓ p =
      C ((N.factorial : ℝ) / ((N + ℓ).factorial : ℝ)) *
        schurSzegoComp N (commonKernel (N + ℓ)) p := by
  ext k
  rw [coeff_compression, coeff_C_mul, coeff_schurSzegoComp]
  by_cases hk : k ≤ N
  · rw [ite_eq_left hk, ite_eq_left hk]
    have hchoose : (Nat.choose N k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk).ne'
    have hmu : multiplier N ℓ k =
        (((N.factorial : ℝ) / ((N + ℓ).factorial : ℝ)) *
          (commonKernel (N + ℓ)).coeff k) / (Nat.choose N k : ℝ) := by
      apply (eq_div_iff hchoose).mpr
      simpa only [mul_comm] using choose_mul_multiplier N ℓ k hk
    rw [hmu]
    ring
  · simp only [hk, ite_false, mul_zero]

/-- Normalization of the shifted multiplier. -/
private theorem choose_mul_multiplier_shift (N ℓ k : ℕ) (hN : N ≠ 0) (hk : k ≤ N) :
    (Nat.choose N k : ℝ) * multiplier (N + 1) ℓ (k + 1) =
      (N.factorial : ℝ) / ((N + ℓ - 1).factorial : ℝ) *
        (commonKernel (N + ℓ - 1)).coeff k := by
  have hguard : 2 * (k + 1) ≤ N + 1 + ℓ ↔ 2 * k ≤ N + ℓ - 1 := by lia
  by_cases hsupport : 2 * k ≤ N + ℓ - 1
  · have hi : N + 1 - (k + 1) = N - k := by lia
    have hi2 : N + 1 + ℓ - 2 * (k + 1) = N + ℓ - 1 - 2 * k := by lia
    rw [multiplier, ite_eq_left (hguard.mpr hsupport), hi, hi2,
      coeff_commonKernel, ite_eq_left hsupport, Nat.cast_choose ℝ hk]
    have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
    have hNfac : ((N - k).factorial : ℝ) ≠ 0 := by positivity
    have hmfac : ((N + ℓ - 1).factorial : ℝ) ≠ 0 := by positivity
    have hden : ((N + ℓ - 1 - 2 * k).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · simp only [multiplier, coeff_commonKernel, hguard, hsupport, ite_false, mul_zero]

/-- Compression of `X * p` at level `ℓ` and size `N + 1` is `X` times the composition of the
shifted common kernel `h_{N+ℓ-1}` with `p`. -/
theorem compression_X_mul (N ℓ : ℕ) (p : ℝ[X]) (hN : N ≠ 0) :
    compression (N + 1) ℓ (X * p) =
      C ((N.factorial : ℝ) / ((N + ℓ - 1).factorial : ℝ)) *
        (X * schurSzegoComp N (commonKernel (N + ℓ - 1)) p) := by
  ext k
  cases k with
  | zero => simp only [coeff_compression, coeff_C_mul, coeff_X_mul_zero,
      mul_zero, ite_self]
  | succ k =>
      rw [coeff_compression, coeff_C_mul, coeff_X_mul, coeff_X_mul, coeff_schurSzegoComp]
      have hbound : k + 1 ≤ N + 1 ↔ k ≤ N := by lia
      by_cases hk : k ≤ N
      · rw [ite_eq_left (hbound.mpr hk), ite_eq_left hk]
        have hchoose : (Nat.choose N k : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos hk).ne'
        have hmu : multiplier (N + 1) ℓ (k + 1) =
            (((N.factorial : ℝ) / ((N + ℓ - 1).factorial : ℝ)) *
              (commonKernel (N + ℓ - 1)).coeff k) / (Nat.choose N k : ℝ) := by
          apply (eq_div_iff hchoose).mpr
          simpa only [mul_comm] using choose_mul_multiplier_shift N ℓ k hN hk
        rw [hmu]
        ring
      · simp only [hbound, hk, ite_false, mul_zero]

/-- Normalization of the unshifted kernel coefficients. -/
private theorem coeff_kernel_mul_multiplier (N ℓ : ℕ) (a : ℝ) (k : ℕ) (hN : N ≠ 0)
    (hk : k ≤ N) :
    ((N.factorial : ℝ) / ((N + ℓ - 1).factorial : ℝ)) * (kernel N ℓ a).coeff k =
      (Nat.choose N k : ℝ) * (a + (k : ℝ)) * multiplier (N + 1) ℓ k := by
  have hi : N + 1 + ℓ = N + ℓ + 1 := by lia
  by_cases hguard : 2 * k ≤ N + ℓ + 1
  · rw [coeff_kernel N ℓ a k hN, ite_eq_left hguard, multiplier, hi, ite_eq_left hguard,
      Nat.cast_choose ℝ hk]
    have hindex : N + 1 - k = (N - k) + 1 := by lia
    have hcast : ((N - k : ℕ) : ℝ) + 1 = (N : ℝ) + 1 - (k : ℝ) := by
      rw [Nat.cast_sub hk]
      ring
    rw [hindex, Nat.factorial_succ]
    push_cast
    rw [hcast]
    have hprev : ((N + ℓ - 1).factorial : ℝ) ≠ 0 := by positivity
    have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
    have hNfac : ((N - k).factorial : ℝ) ≠ 0 := by positivity
    have hden : ((N + ℓ + 1 - 2 * k).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · rw [coeff_kernel N ℓ a k hN, ite_eq_right hguard, multiplier, hi, ite_eq_right hguard,
      mul_zero, mul_zero]

/-- The coefficients of `nextPolynomial a p` in terms of those of `X * p` and `p`. -/
theorem coeff_nextPolynomial (a : ℝ) (p : ℝ[X]) (k : ℕ) :
    (nextPolynomial a p).coeff k = (X * p).coeff k + (a + (k : ℝ)) * p.coeff k := by
  cases k with
  | zero => simp only [nextPolynomial, coeff_add, coeff_X_mul_zero, zero_add,
      add_mul, coeff_C_mul, Nat.cast_zero, add_zero]
  | succ k =>
      simp only [nextPolynomial, add_mul, coeff_add, coeff_X_mul, coeff_C_mul, coeff_derivative,
        Nat.cast_add, Nat.cast_one]
      ring

/-- **Exact identity for the compressed adjacent differential step** (Lemma 4.2 of Zhang, SSRN
7510941).  For every real `a`, every `ℓ`, `N ≠ 0` and every `p` of degree at most `N` (no sign or
root hypothesis),
`T^{(ℓ)}_{N+1} ((x + a) p + x p') = N! / (N + ℓ - 1)! * (p ∘ₙ K_{N,ℓ,a} + x (p ∘ₙ h_{N+ℓ-1}))`,
where `∘ₙ` is `schurSzegoComp N` with the multiplier `p` on the right. -/
theorem compression_nextPolynomial (N ℓ : ℕ) (a : ℝ) (p : ℝ[X]) (hN : N ≠ 0)
    (hp : p.natDegree ≤ N) :
    compression (N + 1) ℓ (nextPolynomial a p) =
      C ((N.factorial : ℝ) / ((N + ℓ - 1).factorial : ℝ)) *
        (schurSzegoComp N (kernel N ℓ a) p +
          X * schurSzegoComp N (commonKernel (N + ℓ - 1)) p) := by
  have hshift := compression_X_mul N ℓ p hN
  ext k
  have hcshift := congrArg (fun q : ℝ[X] => q.coeff k) hshift
  rw [coeff_C_mul] at hcshift
  rw [coeff_compression, coeff_nextPolynomial, coeff_C_mul, coeff_add, coeff_schurSzegoComp]
  simp only [mul_add]
  rw [← hcshift, coeff_compression]
  by_cases hk : k ≤ N
  · have hk1 : k ≤ N + 1 := by lia
    simp only [ite_eq_left hk1, ite_eq_left hk]
    have hchoose : (Nat.choose N k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk).ne'
    have hK := coeff_kernel_mul_multiplier N ℓ a k hN hk
    field_simp at hK ⊢
    linear_combination -p.coeff k * hK
  · have hpk : p.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (lt_of_not_ge hk))
    have hk1 : ¬ k ≤ N := hk
    simp only [hk1, ite_false, hpk, mul_zero, add_zero, zero_add]

/-- The derivative identity `h_r = h_{r+1} - 2 / (r + 1) * x h_{r+1}'` of the common kernel
passes through Schur--Szegő composition with any `p` (Euler operator commutation). -/
theorem schurSzegoComp_commonKernel_eq_sub_derivative (N r : ℕ) (p : ℝ[X]) :
    schurSzegoComp N (commonKernel r) p =
      schurSzegoComp N (commonKernel (r + 1)) p -
        C (2 / ((r : ℝ) + 1)) * (X * (schurSzegoComp N (commonKernel (r + 1)) p).derivative) := by
  have hpencil : commonKernel (r + 1) - C (2 / ((r : ℝ) + 1)) * theta (commonKernel (r + 1)) =
      C 1 * commonKernel (r + 1) + C (-(2 / ((r : ℝ) + 1))) * theta (commonKernel (r + 1)) := by
    rw [C_1, C_neg]
    ring
  have hX : X * (schurSzegoComp N (commonKernel (r + 1)) p).derivative =
      theta (schurSzegoComp N (commonKernel (r + 1)) p) := rfl
  rw [commonKernel_eq_sub_derivative r]
  change schurSzegoComp N (commonKernel (r + 1) - C (2 / ((r : ℝ) + 1)) * theta
      (commonKernel (r + 1))) p = _
  rw [hpencil, schurSzegoComp_C_mul_add_left, hX, ← schurSzegoComp_theta_left, C_1, C_neg]
  ring

/-! ### The level `ℓ = 1` forms -/

/-- The level-one compression `T_N p = (N + 1)⁻¹ * (h_{N+1} ∘ₙ p)`. -/
theorem compression_one_eq_schurSzegoComp (N : ℕ) (p : ℝ[X]) :
    compression N 1 p = C (1 / ((N : ℝ) + 1)) * schurSzegoComp N (commonKernel (N + 1)) p := by
  rw [compression_eq_schurSzegoComp, Nat.factorial_succ]
  congr 2
  push_cast
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The level-one form of the compressed adjacent step with the shift `a = (N + 2) / 2`:
`T_{N+1} ((x + (N+2)/2) p + x p') = p ∘ₙ (3/4 h_{N+1} + (N x - 1/4) h_N) + x (p ∘ₙ h_N)`
for `N ≠ 0` and `p` of degree at most `N`. -/
theorem compression_one_nextPolynomial (N : ℕ) (p : ℝ[X]) (hN : N ≠ 0) (hp : p.natDegree ≤ N) :
    compression (N + 1) 1 (nextPolynomial (((N : ℝ) + 2) / 2) p) =
      schurSzegoComp N
          (C (3 / 4 : ℝ) * commonKernel (N + 1) + (C (N : ℝ) * X - C (1 / 4 : ℝ)) * commonKernel N)
          p +
        X * schurSzegoComp N (commonKernel N) p := by
  have hN' : (N.factorial : ℝ) ≠ 0 := by positivity
  rw [compression_nextPolynomial N 1 _ p hN hp, kernel_one_eq, Nat.add_sub_cancel,
    div_self hN', C_1, one_mul]

end RealRooted.FactorialCompression
