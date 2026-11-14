module

public import RealRooted.BasisTransform.AppellRigidity

import Mathlib.Analysis.Polynomial.Basic
import RealRooted.InterlacingSequence.NonnegativeShift
import RealRooted.Mathlib.Algebra.Polynomial.Taylor

/-!
# Translation rigidity of Appell basis transforms

This file characterizes the zero quadratic coefficient case of a
root-preserving monic basis transform.  It also makes the locally finite
differential-operator expansion available as a public theorem.
-/

public section

open Filter Finset Polynomial

noncomputable section

namespace RealRooted

/-- An Appell expansion can be extended to any larger finite differential
sum when the basis and differential coefficients have the expected degrees. -/
theorem eq_sum_of_isAppellExpansion_of_natDegree_le
    {P Q : ℕ → ℝ[X]} (hPQ : IsAppellExpansion P Q)
    (hPdeg : ∀ n, (P n).natDegree = n)
    (hQdeg : ∀ k, (Q k).natDegree ≤ k / 2) {n N : ℕ} (hn : n ≤ N) :
    P n = ∑ k ∈ range (N + 1),
      C (n.descFactorial k : ℝ) * (X ^ (n - k) * Q k) := by
  ext i
  by_cases hi : i ≤ n
  · have hcoeff := coeff_eq_sum_descFactorial_of_isAppellExpansion hPQ
      (j := n - i) (Nat.sub_le n i)
    rw [Nat.sub_sub_self hi] at hcoeff
    rw [hcoeff, finsetSum_coeff]
    have hsubset : Icc (n - i) n ⊆ range (N + 1) := by
      intro k hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        ((Finset.mem_Icc.mp hk).2.trans hn))
    rw [← Finset.sum_subset hsubset]
    · apply Finset.sum_congr rfl
      intro k hk
      have hbounds := Finset.mem_Icc.mp hk
      rw [coeff_C_mul, coeff_X_pow_mul', ite_eq_left]
      · congr 2
        lia
      · lia
    · intro k hkrange hkIcc
      by_cases hkn : k ≤ n
      · have hklt : k < n - i := lt_of_not_ge fun hkge =>
          hkIcc (Finset.mem_Icc.mpr ⟨hkge, hkn⟩)
        rw [coeff_C_mul, coeff_X_pow_mul', ite_eq_right]
        · simp
        · lia
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by lia)]
        simp
  · have hni : n < i := lt_of_not_ge hi
    rw [coeff_eq_zero_of_natDegree_lt (by simpa [hPdeg n] using hni),
      finsetSum_coeff]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hkn : k ≤ n
    · apply coeff_eq_zero_of_natDegree_lt
      calc
        (C (n.descFactorial k : ℝ) * (X ^ (n - k) * Q k)).natDegree ≤
            (X ^ (n - k) * Q k).natDegree := natDegree_C_mul_le _ _
        _ ≤ (X ^ (n - k)).natDegree + (Q k).natDegree := natDegree_mul_le
        _ ≤ (n - k) + k / 2 := by
          rw [natDegree_X_pow]
          exact Nat.add_le_add_left (hQdeg k) (n - k)
        _ ≤ n := by lia
        _ < i := hni
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by lia)]
      simp

/-- An Appell expansion evaluates the associated basis transform as the
locally finite differential operator with coefficients `Q`. -/
theorem _root_.RealRooted.IsAppellExpansion.basisTransform_eq_sum_iterate_derivative
    {P Q : ℕ → ℝ[X]} (hPQ : IsAppellExpansion P Q)
    (hPdeg : ∀ n, (P n).natDegree = n)
    (hQdeg : ∀ k, (Q k).natDegree ≤ k / 2)
    {p : ℝ[X]} {N : ℕ} (hp : p.natDegree ≤ N) :
    basisTransform P p =
      ∑ k ∈ range (N + 1), Q k * derivative^[k] p := by
  have hpsum := p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hp)
  conv_lhs => rw [hpsum]
  rw [basisTransform_finset_sum]
  simp only [basisTransform_C_mul_X_pow]
  calc
    _ = ∑ n ∈ range (N + 1), ∑ k ∈ range (N + 1),
        C (p.coeff n) *
          (C (n.descFactorial k : ℝ) * (X ^ (n - k) * Q k)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [eq_sum_of_isAppellExpansion_of_natDegree_le hPQ hPdeg hQdeg
        (Nat.le_of_lt_succ (Finset.mem_range.mp hn)), Finset.mul_sum]
    _ = ∑ k ∈ range (N + 1), Q k * derivative^[k] p := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      conv_rhs => rw [hpsum]
      rw [iterate_derivative_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul]
      ring

private theorem natDegree_eq_zero_of_sq_eval_neg_le_const
    {q : ℝ[X]} {C : ℝ}
    (hbound : ∀ r : ℝ, 0 ≤ r → (q.eval (-r)) ^ 2 ≤ C) :
    q.natDegree = 0 := by
  have hbounded : IsBoundedUnder (· ≤ ·) atBot (|q.eval ·|) := by
    refine ⟨|C| + 1, eventually_map.mpr ?_⟩
    filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
    have hsq := hbound (-x) (by linarith)
    have hsq' : (q.eval x) ^ 2 ≤ C := by simpa using hsq
    have habs : |q.eval x| ≤ (q.eval x) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|q.eval x| - 1), sq_abs (q.eval x)]
    nlinarith [hsq'.trans (le_abs_self C)]
  exact natDegree_eq_zero_iff_degree_le_zero.mpr
    ((Polynomial.isBoundedUnder_abs_atBot_iff q).mp hbounded)

private theorem shiftedPowerImage_eq_of_commutes_translation
    {P : ℕ → ℝ[X]}
    (hcomm : ∀ (r : ℝ) (p : ℝ[X]),
      basisTransform P (p.comp (X + C r)) =
        (basisTransform P p).comp (X + C r))
    (k : ℕ) (r : ℝ) :
    shiftedPowerImage P k r = P k := by
  rw [shiftedPowerImage_eq]
  have hpow : ((X + C r) ^ k : ℝ[X]) = (X ^ k).comp (X + C r) := by
    simp
  rw [hpow, hcomm, basisTransform_X_pow, comp_assoc]
  simp [sub_eq_add_neg]

/-- The canonical Appell coefficients are constant exactly when the basis
transform commutes with every translation. -/
theorem _root_.RealRooted.AppellCoefficient.forall_natDegree_eq_zero_iff_commutes_translation
    (P : ℕ → ℝ[X]) (hPdeg : ∀ n, (P n).natDegree = n)
    (hQdeg : ∀ k, (appellCoefficient P k).natDegree ≤ k / 2) :
    (∀ k, (appellCoefficient P k).natDegree = 0) ↔
      ∀ (r : ℝ) (p : ℝ[X]),
        basisTransform P (p.comp (X + C r)) =
          (basisTransform P p).comp (X + C r) := by
  constructor
  · intro hconstant r p
    rw [RealRooted.IsAppellExpansion.basisTransform_eq_sum_iterate_derivative
        (isAppellExpansion_appellCoefficient P) hPdeg hQdeg
        (p := p.comp (X + C r)) (N := p.natDegree) (by
          rw [← taylor_apply, natDegree_taylor]),
      RealRooted.IsAppellExpansion.basisTransform_eq_sum_iterate_derivative
        (isAppellExpansion_appellCoefficient P) hPdeg hQdeg (p := p)
        (N := p.natDegree) le_rfl]
    rw [Polynomial.sum_comp]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_comp]
    have hiter := Polynomial.taylor_iterate_derivative r p k
    simp only [taylor_apply] at hiter
    rw [← hiter]
    have hC := eq_C_of_natDegree_eq_zero (hconstant k)
    rw [hC]
    simp
  · intro hcomm k
    apply eq_C_coeff_zero_iff_natDegree_eq_zero.mp
    apply Polynomial.funext
    intro x
    simp only [eval_C]
    have hfactorial : (k.factorial : ℝ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hfactorial
    have heval (r : ℝ) :
        (k.factorial : ℝ) * (appellCoefficient P k).eval (-r) =
          (P k).eval 0 := by
      rw [← eval_zero_shiftedPowerImage,
        shiftedPowerImage_eq_of_commutes_translation hcomm]
    calc
      (k.factorial : ℝ) * (appellCoefficient P k).eval x =
          (k.factorial : ℝ) * (appellCoefficient P k).eval (-(-x)) := by ring_nf
      _ = (P k).eval 0 := heval (-x)
      _ = (k.factorial : ℝ) * (appellCoefficient P k).eval (-0) :=
        (heval 0).symm
      _ = (k.factorial : ℝ) * (appellCoefficient P k).coeff 0 := by
        rw [neg_zero, ← coeff_zero_eq_eval_zero]

private theorem basisTransform_derivative_commutes_of_basis_derivative
    {P : ℕ → ℝ[X]}
    (hP : ∀ n, (P n).derivative = C (n : ℝ) * P (n - 1))
    (p : ℝ[X]) :
    (basisTransform P p).derivative = basisTransform P p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [basisTransform_add, derivative_add, hp, hq]
  | monomial n a =>
      rw [basisTransform_monomial, derivative_C_mul, hP]
      cases n with
      | zero => simp
      | succ n =>
          rw [derivative_monomial, basisTransform_monomial]
          simp only [Nat.succ_sub_one]
          push_cast
          rw [C_mul]
          ring

private theorem derivative_appellCoefficient_eq_zero_of_basis_derivative
    {P : ℕ → ℝ[X]}
    (hPdeg : ∀ n, (P n).natDegree = n)
    (hQdeg : ∀ k, (appellCoefficient P k).natDegree ≤ k / 2)
    (hP : ∀ n, (P n).derivative = C (n : ℝ) * P (n - 1)) :
    ∀ n, (appellCoefficient P n).derivative = 0 := by
  let Q := appellCoefficient P
  have hcomm := basisTransform_derivative_commutes_of_basis_derivative hP
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hexpand :=
        RealRooted.IsAppellExpansion.basisTransform_eq_sum_iterate_derivative
          (isAppellExpansion_appellCoefficient P) hPdeg hQdeg
          (p := X ^ n) (N := n) (by simp)
      have hexpandDer :=
        RealRooted.IsAppellExpansion.basisTransform_eq_sum_iterate_derivative
          (isAppellExpansion_appellCoefficient P) hPdeg hQdeg
          (p := (X ^ n).derivative) (N := n)
          (calc
            (X ^ n).derivative.natDegree ≤ (X ^ n).natDegree - 1 :=
              natDegree_derivative_le (X ^ n)
            _ ≤ (X ^ n).natDegree := Nat.sub_le _ _
            _ = n := natDegree_X_pow n)
      have hsum :
          ∑ k ∈ range (n + 1),
              (Q k).derivative * derivative^[k] (X ^ n) = 0 := by
        calc
          _ = (∑ k ∈ range (n + 1),
                derivative (Q k * derivative^[k] (X ^ n))) -
              ∑ k ∈ range (n + 1),
                Q k * derivative^[k] ((X ^ n).derivative) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro k hk
              rw [derivative_mul]
              have hiter :
                  derivative (derivative^[k] (X ^ n : ℝ[X])) =
                    derivative^[k] ((X ^ n : ℝ[X]).derivative) := by
                rw [← Function.iterate_succ_apply derivative,
                  ← Function.iterate_succ_apply' derivative]
              have hcancel :
                  Q k * derivative (derivative^[k] (X ^ n)) =
                    Q k * derivative^[k] ((X ^ n).derivative) :=
                congrArg (Q k * ·) hiter
              linear_combination -hcancel
          _ = derivative (basisTransform P (X ^ n)) -
              basisTransform P ((X ^ n).derivative) := by
              rw [hexpand, hexpandDer, derivative_sum]
          _ = 0 := by rw [hcomm]; simp
      rw [Finset.sum_eq_single n] at hsum
      · rw [iterate_derivative_X_pow_eq_C_mul] at hsum
        have hfac : C (n.factorial : ℝ) ≠ 0 :=
          C_ne_zero.mpr (by positivity)
        have hprod : (Q n).derivative * C (n.factorial : ℝ) = 0 := by
          simpa only [Nat.descFactorial_self, Nat.sub_self, pow_zero,
            mul_one] using hsum
        exact (mul_eq_zero.mp hprod).resolve_right hfac
      · intro k hk hkn
        have hkn' : k < n := by
          have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          lia
        rw [ih k hkn', zero_mul]
      · simp

/-- The canonical Appell coefficients are constant exactly when the basis
polynomials satisfy the Appell derivative recurrence. -/
theorem forall_appellCoefficient_natDegree_eq_zero_iff_derivative
    (P : ℕ → ℝ[X]) (hPdeg : ∀ n, (P n).natDegree = n)
    (hQdeg : ∀ k, (appellCoefficient P k).natDegree ≤ k / 2) :
    (∀ k, (appellCoefficient P k).natDegree = 0) ↔
      ∀ n, (P n).derivative = C (n : ℝ) * P (n - 1) := by
  constructor
  · intro hconstant n
    have hcomm (p : ℝ[X]) :
        (basisTransform P p).derivative = basisTransform P p.derivative := by
      rw [RealRooted.IsAppellExpansion.basisTransform_eq_sum_iterate_derivative
          (isAppellExpansion_appellCoefficient P) hPdeg hQdeg (p := p)
          (N := p.natDegree) le_rfl,
        RealRooted.IsAppellExpansion.basisTransform_eq_sum_iterate_derivative
          (isAppellExpansion_appellCoefficient P) hPdeg hQdeg
          (p := p.derivative) (N := p.natDegree)
          ((natDegree_derivative_le (p := p)).trans (Nat.sub_le _ _))]
      rw [derivative_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [derivative_mul, (derivative_eq_zero.mpr (hconstant k)), zero_mul, zero_add]
      rw [← Function.iterate_succ_apply derivative,
        ← Function.iterate_succ_apply' derivative]
    have hmonomial := hcomm (X ^ n)
    rw [basisTransform_X_pow, derivative_X_pow] at hmonomial
    rw [basisTransform_C_mul_X_pow] at hmonomial
    exact hmonomial
  · intro hP n
    exact derivative_eq_zero.mp
      (derivative_appellCoefficient_eq_zero_of_basis_derivative hPdeg hQdeg hP n)

private theorem appellCoefficient_natDegree_eq_zero_of_quadraticCoefficient_eq_zero
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits)
    (hbeta : 2 * (appellCoefficient P 2).coeff 1 = 0) :
    ∀ k, (appellCoefficient P k).natDegree = 0 := by
  have hQdeg := appellCoefficient_natDegree_le hPdeg hPmonic hpres
  have hfirst {n : ℕ} (hn : 1 ≤ n) :
      (P n).coeff (n - 1) = (appellCoefficient P 1).coeff 0 * n := by
    rw [coeff_sub_one_eq_linear_add_choose
      (isAppellExpansion_appellCoefficient P) hQdeg hn, hbeta, zero_mul, add_zero]
  intro k
  by_cases hk : 2 ≤ k
  · let q := C (k.factorial : ℝ) * appellCoefficient P k
    let A := (P k).coeff (k - 1) ^ 2 - 2 * (P k).coeff (k - 2)
    have hslope :
        k * (P (k - 1)).coeff (k - 2) -
          (k - 1) * (P k).coeff (k - 1) = 0 := by
      have hprev := hfirst (n := k - 1) (by lia)
      have hcurr := hfirst (n := k) (by lia)
      rw [show k - 2 = k - 1 - 1 by lia, hprev, hcurr]
      rw [Nat.cast_sub (by lia : 1 ≤ k)]
      ring
    have hbound : ∀ r : ℝ, 0 ≤ r → (q.eval (-r)) ^ 2 ≤ A ^ k := by
      intro r hr
      have hsplits : (shiftedPowerImage P k r).Splits := by
        have hinput : ((X + C r) ^ k : ℝ[X]).Splits :=
          (Polynomial.Splits.X_add_C r).pow k
        have hroots : ∀ x ∈ ((X + C r) ^ k : ℝ[X]).roots, x ≤ 0 := by
          intro x hx
          rw [roots_pow, roots_X_add_C] at hx
          have hx' : x = -r :=
            Multiset.mem_singleton.mp (Multiset.mem_nsmul.mp hx).2
          linarith
        exact (splits_shiftedPowerImage_iff P k r).2 (hpres _ hinput hroots)
      have hroot := eval_zero_sq_le_coeff_sq_sub_two_mul_pow
        (shiftedPowerImage_monic hPdeg hPmonic k r)
        (shiftedPowerImage_natDegree hPdeg hPmonic k r) hk hsplits
      rw [eval_zero_shiftedPowerImage,
        coeff_shiftedPowerImage_sub_one hPdeg hPmonic (by lia) r,
        coeff_shiftedPowerImage_sub_two hPdeg hPmonic hk r, hslope,
        zero_mul, add_zero] at hroot
      simpa only [q, A, eval_mul, eval_C] using hroot
    have hqzero := natDegree_eq_zero_of_sq_eval_neg_le_const hbound
    have hfactorial : (k.factorial : ℝ) ≠ 0 := by positivity
    simpa only [q, natDegree_C_mul hfactorial] using hqzero
  · have hk' : k ≤ 1 := by lia
    have hkhalf : k / 2 = 0 := Nat.div_eq_of_lt (by lia)
    exact Nat.eq_zero_of_le_zero ((hQdeg k).trans_eq hkhalf)

/-- Under nonpositive-root preservation, the canonical quadratic coefficient
vanishes exactly when every differential coefficient is constant. -/
theorem two_mul_coeff_one_appellCoefficient_two_eq_zero_iff
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits) :
    2 * (appellCoefficient P 2).coeff 1 = 0 ↔
      ∀ k, (appellCoefficient P k).natDegree = 0 := by
  constructor
  · exact appellCoefficient_natDegree_eq_zero_of_quadraticCoefficient_eq_zero
      hPdeg hPmonic hpres
  · intro hconstant
    have hcoeff : (appellCoefficient P 2).coeff 1 = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hconstant 2]; norm_num)
    rw [hcoeff, mul_zero]

/-- For a root-preserving monic basis, vanishing of the canonical quadratic
coefficient, constant differential coefficients, translation commutation,
and the Appell derivative recurrence are equivalent. -/
theorem appellTranslationRigidity_equivalences
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits) :
    let beta := 2 * (appellCoefficient P 2).coeff 1
    (beta = 0 ↔ ∀ k, (appellCoefficient P k).natDegree = 0) ∧
      (beta = 0 ↔ ∀ (r : ℝ) (p : ℝ[X]),
        basisTransform P (p.comp (X + C r)) =
          (basisTransform P p).comp (X + C r)) ∧
      (beta = 0 ↔ ∀ n,
        (P n).derivative = C (n : ℝ) * P (n - 1)) := by
  dsimp only
  have hbeta := two_mul_coeff_one_appellCoefficient_two_eq_zero_iff
    hPdeg hPmonic hpres
  exact ⟨hbeta,
    hbeta.trans (RealRooted.AppellCoefficient.forall_natDegree_eq_zero_iff_commutes_translation
      P hPdeg (appellCoefficient_natDegree_le hPdeg hPmonic hpres)),
    hbeta.trans (forall_appellCoefficient_natDegree_eq_zero_iff_derivative
      P hPdeg (appellCoefficient_natDegree_le hPdeg hPmonic hpres))⟩

/-- In the zero-quadratic-coefficient case, a monic basis transform that
preserves split inputs with nonpositive roots preserves every split input. -/
theorem basisTransform_splits_of_quadraticCoefficient_eq_zero
    {P : ℕ → ℝ[X]} (hPdeg : ∀ n, (P n).natDegree = n)
    (hPmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits)
    (hbeta : 2 * (appellCoefficient P 2).coeff 1 = 0)
    {p : ℝ[X]} (hp : p.Splits) :
    (basisTransform P p).Splits := by
  have hconstant :=
    appellCoefficient_natDegree_eq_zero_of_quadraticCoefficient_eq_zero
      hPdeg hPmonic hpres hbeta
  have hcomm :=
    (RealRooted.AppellCoefficient.forall_natDegree_eq_zero_iff_commutes_translation
      P hPdeg (appellCoefficient_natDegree_le hPdeg hPmonic hpres)).mp hconstant
  obtain ⟨r, hr⟩ := exists_root_upper_bound p
  have hshiftSplits : (p.comp (X + C r)).Splits := hp.comp_X_add_C r
  have hshiftRoots : ∀ x ∈ (p.comp (X + C r)).roots, x ≤ 0 := by
    intro x hx
    rw [roots_comp_X_add_C] at hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    linarith [hr y hy]
  have hout := hpres (p.comp (X + C r)) hshiftSplits hshiftRoots
  rw [hcomm] at hout
  have hback := hout.comp_X_add_C (-r)
  simpa [comp_assoc] using hback

end RealRooted
