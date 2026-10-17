/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import RealRooted.EulerOperator.Polar.ProperPosition
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Adjacent polar Euler operators

This file gives algebraic identities for changing the ambient degree of
`polarTheta` and proves that adjacent polar operators preserve a tight strict
interlacing pair in the PF cone.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Raising the ambient degree of `polarTheta` by one adds the input. -/
theorem polarTheta_succ (N : ℕ) (p : ℝ[X]) :
    polarTheta (N + 1) p = p + polarTheta N p := by
  simp [polarTheta, theta]
  ring

/-- `polarTheta` moves through a left factor of `X` while dropping its
ambient degree by one. -/
theorem polarTheta_succ_X_mul (N : ℕ) (p : ℝ[X]) :
    polarTheta (N + 1) (X * p) = X * polarTheta N p := by
  ext k
  cases k with
  | zero => simp [coeff_polarTheta]
  | succ k =>
      simp only [coeff_polarTheta, coeff_X_mul]
      push_cast
      ring

/-- Reversal preserves the orientation of a strict PF pair whose degrees
differ by one, provided neither polynomial has zero constant coefficient. -/
theorem strictInterl_reverse_of_pf_of_natDegree_add_one
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : StrictInterl p q)
    (hdeg : p.natDegree + 1 = q.natDegree)
    (hpconst : p.coeff 0 ≠ 0) (hqconst : q.coeff 0 ≠ 0) :
    StrictInterl p.reverse q.reverse := by
  have hqXp : StrictInterl q (X * p) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg hpq
      hp.hasNonnegCoeffs hq.hasNonnegCoeffs
  let N := q.natDegree
  have hp0 : p ≠ 0 := hpq.1.1
  have hq0 : q ≠ 0 := hpq.2.1.1
  have hXpdeg : (X * p).natDegree = N := by
    rw [natDegree_mul X_ne_zero hp0, natDegree_X]
    grind
  have hqdeg : q.natDegree = N := rfl
  have hRq : reflect N q = q.reverse := by
    rw [DegreeDropReversal.reflect_eq_X_pow_mul_reverse q hqdeg.le]
    simp [hqdeg]
  have hRXp : reflect N (X * p) = p.reverse := by
    rw [DegreeDropReversal.reflect_eq_X_pow_mul_reverse
      (X * p) hXpdeg.le]
    rw [hXpdeg, Nat.sub_self, pow_zero, one_mul,
      Polynomial.reverse_X_mul]
  have hall : AllComboRealRooted q.reverse p.reverse := by
    intro a b
    have hs := allComboRealRooted_of_strictInterl hqXp a b
    have hcomboDeg :
        (C a * q + C b * (X * p)).natDegree ≤ N :=
      (natDegree_add_le _ _).trans
        (max_le
          ((natDegree_C_mul_le a q).trans hqdeg.le)
          ((natDegree_C_mul_le b (X * p)).trans hXpdeg.le))
    have hreflect :
        reflect N (C a * q + C b * (X * p)) =
          C a * q.reverse + C b * p.reverse := by
      simp_all
    rw [← hreflect]
    exact DegreeDropReversal.splits_reflect_of_splits hs hcomboDeg
  have hprev0 : p.reverse ≠ 0 := by simp [hp0]
  have hqrev0 : q.reverse ≠ 0 := by simp [hq0]
  have hprevSplits : p.reverse.Splits :=
    DegreeDropReversal.splits_reverse hpq.1.2
  have hqrevSplits : q.reverse.Splits :=
    DegreeDropReversal.splits_reverse hpq.2.1.2
  have hptrail : p.natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hpconst)
  have hqtrail : q.natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hqconst)
  have hprevdeg : p.reverse.natDegree = p.natDegree := by
    rw [Polynomial.reverse_natDegree, hptrail]
    simp
  have hqrevdeg : q.reverse.natDegree = q.natDegree := by
    rw [Polynomial.reverse_natDegree, hqtrail]
    simp
  rcases strictInterl_of_allComboRealRooted hprev0 hprevSplits
      hqrev0 hqrevSplits (AllComboRealRooted.comm hall)
      (Or.inl (by simp_all)) with hforward | hreverse
  · exact hforward
  · exfalso
    have hle := StrictInterl.natDegree_le hreverse
    rw [hprevdeg, hqrevdeg] at hle
    lia

/-- Applying adjacent tight polar operators preserves a strict PF pair of
consecutive degrees. -/
theorem strictInterl_polarTheta_adjacent
    {N : ℕ} {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : StrictInterl p q)
    (hpdeg : p.natDegree = N) (hqdeg : q.natDegree = N + 1)
    (hpconst : p.coeff 0 ≠ 0) (hqconst : q.coeff 0 ≠ 0) :
    StrictInterl (polarTheta (N + 1) p) (polarTheta (N + 2) q) := by
  have hrev : StrictInterl p.reverse q.reverse :=
    strictInterl_reverse_of_pf_of_natDegree_add_one hp hq hpq
      (by simp_all) hpconst hqconst
  have hprevPF : IsPFPolynomial p.reverse := hp.reverse
  have hqrevPF : IsPFPolynomial q.reverse := hq.reverse
  have hXrev : StrictInterl (X * p.reverse) (X * q.reverse) :=
    StrictInterl.mul_X_both_of_roots_nonpos hrev
      hprevPF.roots_nonpos hqrevPF.roots_nonpos
  let P := X * p.reverse
  let Q := X * q.reverse
  have hPdeg : P.natDegree = N + 1 := by
    dsimp [P]
    rw [natDegree_mul X_ne_zero (by simp [hpq.1.1]),
      natDegree_X, Polynomial.reverse_natDegree,
      Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hpconst), hpdeg]
    lia
  have hQdeg : Q.natDegree = N + 2 := by
    dsimp [Q]
    rw [natDegree_mul X_ne_zero (by simp [hpq.2.1.1]),
      natDegree_X, Polynomial.reverse_natDegree,
      Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hqconst), hqdeg]
    lia
  have hPderdeg : P.derivative.natDegree = N := by simp_all
  have hQderdeg : Q.derivative.natDegree = N + 1 := by simp_all
  have hPderconst : P.derivative.coeff 0 ≠ 0 := by
    dsimp [P]
    rw [coeff_derivative, coeff_X_mul]
    simpa [leadingCoeff, hpdeg] using
      Polynomial.leadingCoeff_ne_zero.mpr hpq.1.1
  have hQderconst : Q.derivative.coeff 0 ≠ 0 := by
    dsimp [Q]
    rw [coeff_derivative, coeff_X_mul]
    simpa [leadingCoeff, hqdeg] using
      Polynomial.leadingCoeff_ne_zero.mpr hpq.2.1.1
  have hPder0 : P.derivative ≠ 0 := by simp_all
  have hQder0 : Q.derivative ≠ 0 := by simp_all
  have hder0 : Interl P.derivative Q.derivative :=
    derivativePreservesInterl hXrev.toInterl
  have hder : StrictInterl P.derivative Q.derivative := by
    rcases hder0 with hzero | hzero | hstrict
    · simp_all
    · simp_all
    · exact hstrict
  have hPderpf : IsPFPolynomial P.derivative := hprevPF.X_mul.derivative
  have hQderpf : IsPFPolynomial Q.derivative := hqrevPF.X_mul.derivative
  have hrevder : StrictInterl P.derivative.reverse Q.derivative.reverse :=
    strictInterl_reverse_of_pf_of_natDegree_add_one
      hPderpf hQderpf hder (by simp_all) hPderconst hQderconst
  have hPin : reciprocalShift (N + 1) p = P := by
    rw [reciprocalShift_eq_X_pow_mul_reverse (by simp_all)]
    simp [P, hpdeg]
  have hQin : reciprocalShift (N + 2) q = Q := by
    rw [reciprocalShift_eq_X_pow_mul_reverse (by simp_all)]
    simp [Q, hqdeg]
  rw [polarTheta_eq_reciprocalShift_derivative_reciprocalShift
      (N + 1) p (by simp_all),
    polarTheta_eq_reciprocalShift_derivative_reciprocalShift
      (N + 2) q (by simp_all), hPin, hQin]
  change StrictInterl (reflect N P.derivative)
    (reflect (N + 1) Q.derivative)
  rw [DegreeDropReversal.reflect_eq_X_pow_mul_reverse
      P.derivative hPderdeg.le,
    DegreeDropReversal.reflect_eq_X_pow_mul_reverse
      Q.derivative hQderdeg.le,
    hPderdeg, hQderdeg]
  simpa using hrevder

end RealRooted
