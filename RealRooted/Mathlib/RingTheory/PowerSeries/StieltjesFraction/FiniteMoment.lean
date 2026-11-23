/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentChristoffelLocal
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentSeriesLocal
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.EulerTermination

/-!
# Finite-rank moment data give a terminating Stieltjes fraction

Let `N` and `M` be the unshifted and shifted moment ranks, respectively.
When `M ≤ N ≤ M+1`, the first zero numerator has index `N+M-1`.
The proof uses only positive finite Hankel forms and the actual vanishing
pairings of the full-rank nodal polynomials. The origin-only case `M = 0`
is included. This is the terminating case of Sokal’s formal moment criterion,
Proposition 7 on p. 5 of the published hypergeometric-function paper.
-/

public section

open PowerSeries
open scoped PowerSeries

namespace Polynomial

/-- Interleave the two norm-ratio families in their Euler–Gauss order. -/
private noncomputable def momentEulerNumerator (μ : ℕ → ℝ) (k : ℕ) : ℝ :=
  Sum.elim (momentStieltjesEven μ) (momentStieltjesOdd μ)
    (Equiv.natSumNatEquivNat.symm k)

/-- Interleave the unshifted and shifted orthogonal series. -/
private noncomputable def momentEulerPair (μ : ℕ → ℝ) (k : ℕ) : ℝ⟦X⟧ :=
  Sum.elim (momentOrthogonalSeries μ)
    (momentOrthogonalSeries (fun k => μ (k + 1)))
    (Equiv.natSumNatEquivNat.symm k)

/-- Prepend the constant unit series to the paired orthogonal series. -/
private noncomputable def momentEulerFamily (μ : ℕ → ℝ) : ℕ → ℝ⟦X⟧
  | 0 => 1
  | k + 1 => momentEulerPair μ k

/-- Even positions recover the unshifted norm ratio. -/
private theorem momentEulerNumerator_even (μ : ℕ → ℝ) (n : ℕ) :
    momentEulerNumerator μ (2 * n) = momentStieltjesEven μ n := by
  rw [show 2 * n = Equiv.natSumNatEquivNat (Sum.inl n) by simp]
  simp only [momentEulerNumerator, Equiv.symm_apply_apply, Sum.elim_inl]

/-- Odd positions recover the shifted norm ratio. -/
private theorem momentEulerNumerator_odd (μ : ℕ → ℝ) (n : ℕ) :
    momentEulerNumerator μ (2 * n + 1) = momentStieltjesOdd μ n := by
  rw [show 2 * n + 1 = Equiv.natSumNatEquivNat (Sum.inr n) by simp]
  simp only [momentEulerNumerator, Equiv.symm_apply_apply, Sum.elim_inr]

/-- Even positions recover the original orthogonal series. -/
private theorem momentEulerPair_even (μ : ℕ → ℝ) (n : ℕ) :
    momentEulerPair μ (2 * n) = momentOrthogonalSeries μ n := by
  rw [show 2 * n = Equiv.natSumNatEquivNat (Sum.inl n) by simp]
  simp only [momentEulerPair, Equiv.symm_apply_apply, Sum.elim_inl]

/-- Odd positions recover the shifted orthogonal series. -/
private theorem momentEulerPair_odd (μ : ℕ → ℝ) (n : ℕ) :
    momentEulerPair μ (2 * n + 1) =
      momentOrthogonalSeries (fun k => μ (k + 1)) n := by
  rw [show 2 * n + 1 = Equiv.natSumNatEquivNat (Sum.inr n) by simp]
  simp only [momentEulerPair, Equiv.symm_apply_apply, Sum.elim_inr]

/-- A vanishing shifted pairing at degree zero makes the moment series constant. -/
private theorem mk_eq_C_of_shift_pairing_zero (μ : ℕ → ℝ)
    (hzero : ∀ p : ℝ[X], momentPairing (fun k => μ (k + 1)) p
      (monicMomentPolynomial (fun k => μ (k + 1)) 0) = 0) :
    PowerSeries.mk μ = PowerSeries.C (μ 0) := by
  have hm (k : ℕ) : μ (k + 1) = 0 := by
    simpa only [monicMomentPolynomial_zero, momentPairing, mul_one,
      momentFunctional_X_pow] using hzero (X ^ k)
  ext k
  cases k with
  | zero => simp only [PowerSeries.coeff_mk, PowerSeries.coeff_zero_C]
  | succ k => simp only [PowerSeries.coeff_mk, PowerSeries.coeff_succ_C, hm]

/-- Local Christoffel identities give the Euler–Gauss recurrence before the
first vanishing numerator. -/
private theorem momentEulerFamily_sub_of_lt (μ : ℕ → ℝ) (N M : ℕ)
    (hMN : M ≤ N) (hNM : N ≤ M + 1)
    (hu : ∀ n < N, 0 < momentNormSq μ n)
    (hv : ∀ n < M, 0 < momentNormSq (fun k => μ (k + 1)) n)
    (hd : ∀ n ≤ N, IsUnit (momentHankelMatrix μ n).det)
    (hs : ∀ n ≤ M, IsUnit (momentHankelMatrix (fun k => μ (k + 1)) n).det)
    (hm0 : μ 0 ≠ 0) (hm1 : μ 1 ≠ 0) (k : ℕ) (hk : k < N + M - 1) :
    momentEulerFamily μ (k + 1) - momentEulerFamily μ k =
      PowerSeries.C (momentEulerNumerator μ k) * PowerSeries.X *
        momentEulerFamily μ (k + 2) := by
  let E := momentOrthogonalSeries μ
  let O := momentOrthogonalSeries (fun k => μ (k + 1))
  let a := momentEulerNumerator μ
  let H := momentEulerPair μ
  have haeven (n : ℕ) : a (2 * n) = momentStieltjesEven μ n :=
    momentEulerNumerator_even μ n
  have haodd (n : ℕ) : a (2 * n + 1) = momentStieltjesOdd μ n :=
    momentEulerNumerator_odd μ n
  have hHeven (n : ℕ) : H (2 * n) = momentOrthogonalSeries μ n :=
    momentEulerPair_even μ n
  have hHodd (n : ℕ) : H (2 * n + 1) =
      momentOrthogonalSeries (fun k => μ (k + 1)) n := momentEulerPair_odd μ n
  have ha0 : a 0 = momentStieltjesEven μ 0 := by simpa only [Nat.mul_zero] using haeven 0
  have hH0 : H 0 = E 0 := by simpa only [Nat.mul_zero] using hHeven 0
  have hH1 : H 1 = O 0 := by simpa only [Nat.mul_zero, Nat.zero_add] using hHodd 0
  cases k with
  | zero =>
      change H 0 - 1 = PowerSeries.C (a 0) * PowerSeries.X * H 1
      rw [hH0, hH1, ha0]
      exact momentOrthogonalSeries_zero_sub_one_of_ne_zero μ hm0 hm1
  | succ k =>
      obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
      · have hnN : n + 1 < N := by lia
        have hnM : n < M := by lia
        have hpoly := X_mul_monicMomentPolynomial_shift_of_isUnit μ n
          (hd n (by lia)) (hd (n + 1) (by lia)) (hs n (by lia)) (hu n (by lia)).ne'
        have hstep := momentOrthogonalSeries_shift_sub_of_identity μ n hpoly
          (hd (n + 1) (by lia)) (hu n (by lia)).ne' (hv n hnM).ne'
          (hu (n + 1) hnN).ne'
        change H (2 * n + 1) - H (2 * n) =
          PowerSeries.C (a (2 * n + 1)) * PowerSeries.X * H (2 * n + 2)
        rw [show 2 * n + 2 = 2 * (n + 1) by ring,
          hHeven, hHodd, haodd, hHeven]
        exact hstep
      · have hnN : n + 1 < N := by lia
        have hnM : n + 1 < M := by lia
        have hpoly := monicMomentPolynomial_eq_shift_add_of_isUnit μ n
          (hd (n + 1) (by lia)) (hs n (by lia)) (hs (n + 1) (by lia))
          (hv n (by lia)).ne'
        have hstep := momentOrthogonalSeries_succ_sub_of_identity μ n hpoly
          (hs (n + 1) (by lia)) (hu (n + 1) hnN).ne' (hv n (by lia)).ne'
          (hv (n + 1) hnM).ne'
        change H (2 * n + 2) - H (2 * n + 1) =
          PowerSeries.C (a (2 * n + 2)) * PowerSeries.X * H (2 * n + 3)
        rw [show 2 * n + 2 = 2 * (n + 1) by ring,
          show 2 * n + 3 = 2 * (n + 1) + 1 by ring, hHeven, hHodd, haeven, hHodd]
        exact hstep

/-- The full-rank vanishing pairing identifies the final two Euler–Gauss
series, in both possible rank configurations. -/
private theorem momentEulerFamily_terminal (μ : ℕ → ℝ) (N M : ℕ)
    (hMN : M ≤ N) (hNM : N ≤ M + 1) (hM : M ≠ 0)
    (hu : ∀ n < N, 0 < momentNormSq μ n)
    (hv : ∀ n < M, 0 < momentNormSq (fun k => μ (k + 1)) n)
    (hd : ∀ n ≤ N, IsUnit (momentHankelMatrix μ n).det)
    (hs : ∀ n ≤ M, IsUnit (momentHankelMatrix (fun k => μ (k + 1)) n).det)
    (hzero : ∀ p : ℝ[X], momentPairing μ p (monicMomentPolynomial μ N) = 0)
    (hzeroShift : ∀ p : ℝ[X], momentPairing (fun k => μ (k + 1)) p
      (monicMomentPolynomial (fun k => μ (k + 1)) M) = 0) :
    momentEulerFamily μ (N + M - 1 + 1) = momentEulerFamily μ (N + M - 1) := by
  let H := momentEulerPair μ
  have hHeven (n : ℕ) : H (2 * n) = momentOrthogonalSeries μ n :=
    momentEulerPair_even μ n
  have hHodd (n : ℕ) : H (2 * n + 1) =
      momentOrthogonalSeries (fun k => μ (k + 1)) n := momentEulerPair_odd μ n
  by_cases heq : N = M
  · subst N
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM
    rw [show (n + 1) + (n + 1) - 1 = 2 * n + 1 by lia]
    change H (2 * n + 1) = H (2 * n)
    rw [hHodd, hHeven]
    apply momentOrthogonalSeries_shift_eq_of_pairing_zero μ n
    · exact X_mul_monicMomentPolynomial_shift_of_isUnit μ n
        (hd n (by lia)) (hd (n + 1) (by lia)) (hs n (by lia)) (hu n (by lia)).ne'
    · exact hzero
    · exact (hu n (by lia)).ne'
    · exact (hv n (by lia)).ne'
  · have heq : N = M + 1 := by lia
    subst N
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM
    rw [show (n + 1 + 1) + (n + 1) - 1 = 2 * (n + 1) by lia]
    change H (2 * (n + 1)) = H (2 * n + 1)
    rw [hHeven, hHodd]
    apply momentOrthogonalSeries_succ_eq_of_pairing_zero μ n
    · exact monicMomentPolynomial_eq_shift_add_of_isUnit μ n
        (hd (n + 1) (by lia)) (hs n (by lia)) (hs (n + 1) (by lia))
        (hv n (by lia)).ne'
    · exact hzeroShift
    · exact (hu (n + 1) (by lia)).ne'
    · exact (hv n (by lia)).ne'

/-- Every numerator before the exact finite-rank boundary is a positive
ratio of orthogonal norms. -/
private theorem momentEulerNumerator_pos_of_lt (μ : ℕ → ℝ) (N M : ℕ)
    (hMN : M ≤ N) (hNM : N ≤ M + 1)
    (hu : ∀ n < N, 0 < momentNormSq μ n)
    (hv : ∀ n < M, 0 < momentNormSq (fun k => μ (k + 1)) n)
    (k : ℕ) (hk : k < N + M - 1) : 0 < momentEulerNumerator μ k := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [momentEulerNumerator_even]
    exact div_pos (hv n (by lia)) (hu n (by lia))
  · rw [momentEulerNumerator_odd]
    exact div_pos (hu (n + 1) (by lia)) (hv n (by lia))

/-- Positive finite moment forms and their exact vanishing boundary give a
Stieltjes fraction positive before `N+M-1` and identically zero thereafter. -/
theorem exists_stieltjesTail_of_finite_hankel (μ : ℕ → ℝ) (N M : ℕ)
    (hN : 0 < N) (hMN : M ≤ N) (hNM : N ≤ M + 1)
    (hpos : ∀ n ≤ N, (momentHankelMatrix μ n).PosDef)
    (hshift : ∀ n ≤ M, (momentHankelMatrix (fun k => μ (k + 1)) n).PosDef)
    (hzero : ∀ p : ℝ[X], momentPairing μ p (monicMomentPolynomial μ N) = 0)
    (hzeroShift : ∀ p : ℝ[X], momentPairing (fun k => μ (k + 1)) p
      (monicMomentPolynomial (fun k => μ (k + 1)) M) = 0) :
    0 < μ 0 ∧ ∃ a : ℕ → ℝ,
      (∀ k < N + M - 1, 0 < a k) ∧ (∀ k, N + M - 1 ≤ k → a k = 0) ∧
      PowerSeries.mk μ = PowerSeries.C (μ 0) * stieltjesTail a 0 := by
  have hu (n : ℕ) (hn : n < N) : 0 < momentNormSq μ n :=
    momentNormSq_pos μ n (hpos (n + 1) (by lia))
  have hv (n : ℕ) (hn : n < M) : 0 < momentNormSq (fun k => μ (k + 1)) n :=
    momentNormSq_pos _ n (hshift (n + 1) (by lia))
  have hd (n : ℕ) (hn : n ≤ N) : IsUnit (momentHankelMatrix μ n).det :=
    isUnit_iff_ne_zero.mpr (hpos n hn).det_pos.ne'
  have hs (n : ℕ) (hn : n ≤ M) :
      IsUnit (momentHankelMatrix (fun k => μ (k + 1)) n).det :=
    isUnit_iff_ne_zero.mpr (hshift n hn).det_pos.ne'
  have hm0 : 0 < μ 0 := by simpa only [momentNormSq_zero] using hu 0 hN
  refine ⟨hm0, ?_⟩
  by_cases hM : M = 0
  · have hlength : N + M - 1 = 0 := by lia
    refine ⟨fun _ => 0, ?_, fun _ _ => rfl, ?_⟩
    · intro k hk
      lia
    · rw [stieltjesTail_eq_one_of_zero (a := fun _ : ℕ => (0 : ℝ)) (s := 0) rfl,
        mul_one]
      exact mk_eq_C_of_shift_pairing_zero μ (by simpa only [hM] using hzeroShift)
  have hm1 : μ 1 ≠ 0 := by
    simpa only [momentNormSq_zero, Nat.zero_add] using (hv 0 (Nat.pos_of_ne_zero hM)).ne'
  let a := momentEulerNumerator μ
  let G := momentEulerFamily μ
  let b : ℕ → ℝ := fun k => if k < N + M - 1 then a k else 0
  have hG1 : G 1 = momentOrthogonalSeries μ 0 := by
    change momentEulerPair μ 0 = momentOrthogonalSeries μ 0
    simpa only [Nat.mul_zero] using momentEulerPair_even μ 0
  have hseries : momentOrthogonalSeries μ 0 = stieltjesTail b 0 := by
    apply hG1.symm.trans
    exact eq_stieltjesTail_of_eulerGauss_terminated (a := a) (G := G)
      (N + M - 1) rfl
      (momentEulerFamily_sub_of_lt μ N M hMN hNM hu hv hd hs hm0.ne' hm1)
      (momentEulerFamily_terminal μ N M hMN hNM hM hu hv hd hs hzero hzeroShift)
  refine ⟨b, ?_, ?_, ?_⟩
  · intro k hk
    rw [show b k = a k from ite_eq_left hk]
    exact momentEulerNumerator_pos_of_lt μ N M hMN hNM hu hv k hk
  · intro k hk
    exact ite_eq_right (by lia)
  · rw [← hseries]
    ext k
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
      coeff_momentOrthogonalSeries_zero]
    field_simp [hm0.ne']

end Polynomial
