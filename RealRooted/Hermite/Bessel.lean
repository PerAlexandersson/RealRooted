import RealRooted.Hermite.Poulain
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real

/-!
# The Bessel differential transform

We prove that the finite action of the Bessel symbol `J₀(2D)` preserves
real-rootedness.  The proof approximates the symbol by Laguerre polynomials,
uses Hermite--Poulain for every approximant, and passes to the limit through
the closedness of real-rooted polynomials of bounded degree.
-/

open Finset Polynomial Filter Topology

noncomputable section

namespace RealRooted.HermitePoulain

private theorem splits_derivative_sub {p : ℝ[X]} (hp : p.Splits) (r : ℝ) :
    (derivative p - C r * p).Splits := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hs := differential_operator_preserves_real_rooted
    (f := X + C (-r)) (g := p)
    ⟨(monic_X_add_C (-r)).ne_zero, Splits.X_add_C (-r)⟩ ⟨hp0, hp⟩
  rw [applyAsDifferentialOperator_X_add_C] at hs
  have heq : derivative p + C (-r) * p = derivative p - C r * p := by
    simp only [map_neg]
    ring
  rcases hs with hs | hs
  · rw [heq] at hs
    rw [hs]
    exact Splits.zero
  · rwa [heq] at hs

private def laguerreApproximation (M : ℕ) : ℝ[X] :=
  ∑ k ∈ range (M + 1),
    C ((-1 : ℝ) ^ k * (M.choose k : ℝ) / (k.factorial : ℝ)) * X ^ k

private theorem laguerreApproximation_coeff (M k : ℕ) :
    (laguerreApproximation M).coeff k =
      (-1 : ℝ) ^ k * (M.choose k : ℝ) / (k.factorial : ℝ) := by
  simp only [laguerreApproximation, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro hk
    simp at hk
    simp [Nat.choose_eq_zero_of_lt (by lia : M < k)]

private theorem laguerreApproximation_eval_pos (M : ℕ) {t : ℝ} (ht : t ≤ 0) :
    0 < (laguerreApproximation M).eval t := by
  simp only [laguerreApproximation, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [Finset.sum_range_succ']
  apply add_pos_of_nonneg_of_pos
  · apply Finset.sum_nonneg
    intro k _
    have heq :
        (-1 : ℝ) ^ (k + 1) * (M.choose (k + 1) : ℝ) /
            ((k + 1).factorial : ℝ) * t ^ (k + 1) =
          (-t) ^ (k + 1) *
            ((M.choose (k + 1) : ℝ) / ((k + 1).factorial : ℝ)) := by
      rw [neg_pow]
      ring
    rw [heq]
    have : 0 ≤ -t := by linarith
    positivity
  · simp

private theorem laguerreApproximation_eq_aeval (M : ℕ) :
    C (M.factorial : ℝ) * laguerreApproximation M =
      (aeval (derivative : Module.End ℝ ℝ[X]) ((X - C (1 : ℝ)) ^ M) :
        Module.End ℝ ℝ[X]) (X ^ M) := by
  have hdeg : ((X - C (1 : ℝ)) ^ M).natDegree < M + 1 := by
    rw [natDegree_pow, natDegree_X_sub_C]
    lia
  rw [aeval_eq_sum_range' hdeg]
  ext k
  simp only [coeff_C_mul, laguerreApproximation_coeff, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply, Module.End.pow_apply,
    iterate_derivative_X_pow_eq_smul, finsetSum_coeff, coeff_smul, smul_eq_mul,
    sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow, coeff_X_pow]
  rcases le_or_gt k M with hk | hk
  · rw [Finset.sum_eq_single (M - k)]
    · have hfactorial := Nat.factorial_mul_descFactorial (Nat.sub_le M k)
      rw [Nat.sub_sub_self hk] at hfactorial
      rw [Nat.sub_sub_self hk, Nat.choose_symm hk, ite_eq_left rfl]
      have hkf : (k.factorial : ℝ) ≠ 0 := by positivity
      rw [← hfactorial]
      push_cast
      field_simp
    · intro b hb hne
      rw [Finset.mem_range] at hb
      rw [ite_eq_right (by lia)]
      simp
    · intro h
      simp at h
  · rw [Nat.choose_eq_zero_of_lt hk]
    simp only [Nat.cast_zero, mul_zero, zero_div]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_range] at hx
    rw [ite_eq_right (by lia)]
    simp

private theorem laguerreApproximation_splits (M : ℕ) :
    (laguerreApproximation M).Splits := by
  have hsymbol : ((X - C (1 : ℝ)) ^ M).Splits := (Splits.X_sub_C 1).pow M
  have hinput : (X ^ M : ℝ[X]).Splits := Splits.X_pow M
  have hpres := differential_operator_preserves_real_rooted
    ⟨((monic_X_sub_C 1).pow M).ne_zero, hsymbol⟩ ⟨by simp, hinput⟩
  have haeval :
      (aeval (derivative : Module.End ℝ ℝ[X]) ((X - C (1 : ℝ)) ^ M) :
        Module.End ℝ ℝ[X]) (X ^ M) =
        applyAsDifferentialOperator ((X - C 1) ^ M) (X ^ M) := by
    rw [applyAsDifferentialOperator_eq_sum_range (N := M + 1) (by
      rw [natDegree_pow, natDegree_X_sub_C]
      lia)]
    rw [aeval_eq_sum_range' (n := M + 1) (by
      rw [natDegree_pow, natDegree_X_sub_C]
      lia)]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      Module.End.pow_apply, smul_eq_C_mul]
  rw [← haeval, ← laguerreApproximation_eq_aeval] at hpres
  rcases hpres with hzero | hsplit
  · have hfactorial : (M.factorial : ℝ) ≠ 0 := by positivity
    have : laguerreApproximation M = 0 := by
      apply (mul_left_cancel₀ (C_ne_zero.mpr hfactorial))
      simpa using hzero
    rw [this]
    exact Splits.zero
  · have h := hsplit.C_mul (1 / (M.factorial : ℝ))
    rw [← mul_assoc, ← C_mul] at h
    have hfactorial : (M.factorial : ℝ) ≠ 0 := by positivity
    rwa [one_div_mul_cancel hfactorial, C_1, one_mul] at h

private theorem laguerreApproximation_roots_nonneg (M : ℕ) :
    ∀ r ∈ (laguerreApproximation M).roots, 0 ≤ r := by
  intro r hr
  by_contra h
  have hroot := (mem_roots'.mp hr).2
  have hpos := laguerreApproximation_eval_pos M (le_of_lt (not_le.mp h))
  rw [hroot.eq_zero] at hpos
  exact lt_irrefl _ hpos

/-- The constant-coefficient operator `c D²`. -/
def sqDifferentialOperator (c : ℝ) : Module.End ℝ ℝ[X] :=
  c • ((derivative : Module.End ℝ ℝ[X]) * derivative)

private theorem sqDifferentialOperator_pow_apply (c : ℝ) (k : ℕ) (p : ℝ[X]) :
    ((sqDifferentialOperator c) ^ k) p =
      C (c ^ k) * derivative^[2 * k] p := by
  rw [sqDifferentialOperator, _root_.smul_pow, LinearMap.smul_apply, ← sq, ← pow_mul,
    Module.End.pow_apply, smul_eq_C_mul, mul_comm 2 k]

private theorem aeval_sqDifferentialOperator_apply
    (L : ℝ[X]) (c : ℝ) {p : ℝ[X]} {N : ℕ} (hN : p.natDegree < 2 * N) :
    (aeval (sqDifferentialOperator c) L : Module.End ℝ ℝ[X]) p =
      ∑ k ∈ range N, C (L.coeff k * c ^ k) * derivative^[2 * k] p := by
  have hB : L.natDegree < L.natDegree + 1 + N := by lia
  rw [aeval_eq_sum_range' hB, LinearMap.coe_sum, Finset.sum_apply]
  simp only [LinearMap.smul_apply, sqDifferentialOperator_pow_apply, smul_eq_C_mul,
    ← mul_assoc, ← C_mul]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp at hk ⊢
    lia
  · intro k _ hk
    simp at hk
    rw [iterate_derivative_eq_zero (by lia), mul_zero]

private theorem splits_sq_sub {q : ℝ[X]} (hq : q.Splits) {c a : ℝ}
    (hc : 0 < c) (ha : 0 ≤ a) :
    (c • derivative (derivative q) - a • q).Splits := by
  set s := Real.sqrt (a / c)
  have hs : c * s ^ 2 = a := by
    rw [Real.sq_sqrt (div_nonneg ha hc.le)]
    field_simp
  have h := splits_derivative_sub (splits_derivative_sub hq (-s)) s
  have heq :
      c • derivative (derivative q) - a • q =
        C c * (derivative (derivative q - C (-s) * q) -
          C s * (derivative q - C (-s) * q)) := by
    simp only [derivative_sub, derivative_mul, derivative_C, smul_eq_C_mul,
      ← hs, map_mul, map_pow, map_neg]
    ring
  rw [heq]
  exact h.C_mul c

private theorem aeval_sqDifferentialOperator_prod_splits
    (s : Multiset ℝ) (hr : ∀ r ∈ s, 0 ≤ r) {c : ℝ} (hc : 0 < c)
    {p : ℝ[X]} (hp : p.Splits) :
    ((aeval (sqDifferentialOperator c) (s.map (X - C ·)).prod :
      Module.End ℝ ℝ[X]) p).Splits := by
  induction s using Multiset.induction_on with
  | empty => simpa using hp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_apply]
    have h := splits_sq_sub
      (ih (fun r hr' => hr r (Multiset.mem_cons_of_mem hr'))) hc
      (hr a (Multiset.mem_cons_self _ _))
    simpa [sqDifferentialOperator, Module.algebraMap_end_apply] using h

/-- If `L` has only nonnegative real roots, then the Laguerre--Pólya operator
`L(c D²)` preserves real-rootedness for `c > 0`.

The proof was found by Aristotle (Harmonic). -/
theorem aeval_sqDifferentialOperator_splits {L : ℝ[X]} (hL : L.Splits)
    (hr : ∀ r ∈ L.roots, 0 ≤ r) {c : ℝ} (hc : 0 < c)
    {p : ℝ[X]} (hp : p.Splits) :
    ((aeval (sqDifferentialOperator c) L : Module.End ℝ ℝ[X]) p).Splits := by
  rw [hL.eq_prod_roots, map_mul, aeval_C, Module.End.mul_apply,
    Module.algebraMap_end_apply, smul_eq_C_mul]
  exact (aeval_sqDifferentialOperator_prod_splits _ hr hc hp).C_mul _

private theorem tendsto_descFactorial_div_pow (k : ℕ) :
    Tendsto (fun M : ℕ => (M.descFactorial k : ℝ) / (M : ℝ) ^ k)
      atTop (nhds 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : Tendsto (fun M : ℕ => 1 - (k : ℝ) / M) atTop (nhds 1) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ)).const_sub 1
    have h2 := h1.mul ih
    rw [one_mul] at h2
    apply h2.congr'
    filter_upwards [eventually_gt_atTop k] with M hM
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hM.le, pow_succ]
    have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    field_simp

private theorem tendsto_choose_div_pow (k : ℕ) :
    Tendsto (fun M : ℕ => (M.choose k : ℝ) / (M : ℝ) ^ k)
      atTop (nhds (1 / k.factorial)) := by
  have h := (tendsto_descFactorial_div_pow k).div_const (k.factorial : ℝ)
  apply h.congr
  intro M
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The finite action of the Bessel symbol
`J₀(2D) = ∑ k, (-1)^k D^(2*k)/(k!)²` on a polynomial. -/
def besselDifferentialTransform (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (p.natDegree / 2 + 1),
    C ((-1 : ℝ) ^ k / (Nat.factorial k : ℝ) ^ 2) * derivative^[2 * k] p

/-- The Bessel differential transform `J₀(2D)` sends every real-rooted
real polynomial to a real-rooted polynomial, by Laguerre--Pólya approximation.

The proof was found by Aristotle (Harmonic). -/
theorem besselDifferentialTransform_splits {p : ℝ[X]} (hp : p.Splits) :
    (besselDifferentialTransform p).Splits := by
  by_cases hp0 : p = 0
  · subst hp0
    simp [besselDifferentialTransform]
  set n := p.natDegree with hn
  set N := n / 2 + 1 with hNdef
  have hN : n < 2 * N := by lia
  set b : ℕ → ℝ := fun k => (-1 : ℝ) ^ k / (Nat.factorial k : ℝ) ^ 2 with hb
  set a : ℕ → ℕ → ℝ := fun M k =>
    (laguerreApproximation M).coeff k * (1 / (M : ℝ)) ^ k with ha
  set G : (ℕ → ℝ) → ℝ[X] := fun f =>
    ∑ k ∈ range N, C (f k) * derivative^[2 * k] p with hG
  have hB : besselDifferentialTransform p = G b := rfl
  have hA : ∀ M : ℕ,
      (aeval (sqDifferentialOperator (1 / (M : ℝ))) (laguerreApproximation M) :
        Module.End ℝ ℝ[X]) p = G (a M) :=
    fun M => aeval_sqDifferentialOperator_apply _ _ hN
  have hconv : ∀ k, Tendsto (fun M => a M k) atTop (nhds (b k)) := by
    intro k
    have h := (tendsto_choose_div_pow k).const_mul
      ((-1 : ℝ) ^ k / k.factorial)
    convert h using 1
    · ext M
      simp only [ha, laguerreApproximation_coeff, one_div_pow]
      ring
    · congr 1
      change (-1 : ℝ) ^ k / (k.factorial : ℝ) ^ 2 = _
      ring
  have hGdeg : ∀ f, (G f).natDegree ≤ n := by
    intro f
    apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_iterate_derivative _ _).trans (by lia))
  have hGeval : ∀ f (z : ℂ), ((G f).map Complex.ofRealHom).eval z =
      ∑ k ∈ range N,
        (f k : ℂ) * ((derivative^[2 * k] p).map Complex.ofRealHom).eval z := by
    intro f z
    simp [hG, Polynomial.map_sum, eval_finsetSum]
  rw [hB]
  rcases Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le
      (p := fun M => G (a M)) (p₀ := G b) (fun M => hGdeg (a M)) (by
        intro M
        by_cases hM : M = 0
        · subst M
          right
          rw [← hA]
          simpa [laguerreApproximation, sqDifferentialOperator] using hp
        · right
          rw [← hA]
          exact aeval_sqDifferentialOperator_splits
            (laguerreApproximation_splits M)
            (laguerreApproximation_roots_nonneg M) (by positivity) hp) (by
        intro z
        simp only [hGeval]
        refine tendsto_finsetSum _ fun k _ => ?_
        exact ((Complex.continuous_ofReal.tendsto _).comp (hconv k)).mul_const _)
      with hzero | hsplit
  · rw [hzero]
    exact Splits.zero
  · exact hsplit

end RealRooted.HermitePoulain
