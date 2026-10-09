import RealRooted.CombinatorialExamples.MultisetEulerianNarayana
import RealRooted.MaWang.Strong

/-!
# The gamma operator for multiset Eulerian--Narayana polynomials

Zhang--Zhao (arXiv:2610.00966), Lemma 3.2: for `a > 0` the gamma operator
`Φ_{d,a} Γ = Γ + (z(1 - 4z)Γ' + 2dzΓ)/a` preserves simple negative zeros
(`simpleNegRooted_gammaOperator`).  The degree rises by one exactly when `d` is odd; for
even `d` the top coefficient of `z(1 - 4z)Γ' + 2dzΓ` cancels.  The sign/interlacing core
(`strictInterl_gammaOperatorNumerator`) is stated separately from the coefficient bookkeeping.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace Applications
namespace MultisetEulerianNarayana

/-- The numerator of `Φ_{d,a} Γ = Γ + D_d Γ / a`. -/
def gammaOperatorNumerator (d : ℕ) (a : ℝ) (f : ℝ[X]) : ℝ[X] :=
  C a * f + X * (1 - C 4 * X) * f.derivative + C (2 * (d : ℝ)) * X * f

/-- The gamma operator `Φ_{d,a}` from Zhang--Zhao, equation (20). -/
def gammaOperator (d : ℕ) (a : ℝ) (f : ℝ[X]) : ℝ[X] :=
  C a⁻¹ * gammaOperatorNumerator d a f

private theorem coeff_gammaOperatorNumerator (d : ℕ) (a : ℝ) (f : ℝ[X]) (k : ℕ) :
    (gammaOperatorNumerator d a f).coeff k =
      (a + (k : ℝ)) * f.coeff k +
        if k = 0 then 0 else
          (2 * (d : ℝ) - 4 * (k : ℝ) + 4) * f.coeff (k - 1) := by
  unfold gammaOperatorNumerator
  by_cases hk : k = 0
  · subst k
    simp [coeff_add]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hpoly :
        C a * f + X * (1 - C 4 * X) * f.derivative + C (2 * (d : ℝ)) * X * f =
          C a * f + (X * f.derivative - C 4 * (X ^ 2 * f.derivative)) +
            C (2 * (d : ℝ)) * (X * f) := by ring
    rw [hpoly]
    simp only [coeff_add, coeff_sub, coeff_C_mul]
    have hXder : (X * f.derivative).coeff k = f.derivative.coeff (k - 1) := by
      rw [show k = (k - 1) + 1 by lia, coeff_X_mul]
      simp only [Nat.sub_add_cancel hkpos]
    have hXf : (X * f).coeff k = f.coeff (k - 1) := by
      rw [show k = (k - 1) + 1 by lia, coeff_X_mul]
      simp only [Nat.sub_add_cancel hkpos]
    have hXtwo : (X ^ 2 * f.derivative).coeff k =
        (k - 1 : ℝ) * f.coeff (k - 1) := by
      rw [coeff_X_pow_mul']
      by_cases hk2 : 2 ≤ k
      · simp only [ite_eq_left hk2, coeff_derivative]
        have hidx : k - 2 + 1 = k - 1 := by lia
        rw [hidx]
        have hkcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
          rw [Nat.cast_sub (by lia)]
          norm_num
        rw [hkcast]
        ring
      · simp only [ite_eq_right hk2]
        have hkone : k = 1 := by lia
        subst k
        simp
    rw [hXder, hXtwo, hXf, coeff_derivative]
    simp only [ite_eq_right hk, Nat.sub_add_cancel hkpos]
    have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by lia)]
      norm_num
    rw [hkcast]
    ring

private theorem gammaOperatorNumerator_hasNonnegCoeffs
    {d m : ℕ} {a : ℝ} {f : ℝ[X]} (hf : SimpleNegRooted f m)
    (hd : 2 * m ≤ d) (ha : 0 < a) :
    HasNonnegCoeffs (gammaOperatorNumerator d a f) := by
  intro k
  rw [coeff_gammaOperatorNumerator]
  by_cases hk : k = 0
  · subst k
    simpa using (mul_nonneg ha.le (hf.nonneg 0))
  · simp only [ite_eq_right hk]
    by_cases hkm : k ≤ m + 1
    · have hkcast : (k : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hkm
      have hdm : 2 * (m : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have hcoef : 0 ≤ 2 * (d : ℝ) - 4 * (k : ℝ) + 4 := by
        nlinarith
      exact add_nonneg (mul_nonneg (by positivity) (hf.nonneg k))
        (mul_nonneg hcoef (hf.nonneg (k - 1)))
    · have hkgt : m + 1 < k := Nat.lt_of_not_ge hkm
      have hkdeg : m < k := by lia
      have hkdeg' : m < k - 1 := by lia
      rw [coeff_eq_zero_of_natDegree_lt (by simpa [hf.natDegree_eq] using hkdeg),
        coeff_eq_zero_of_natDegree_lt (by simpa [hf.natDegree_eq] using hkdeg')]
      simp

private theorem gammaOperatorNumerator_coeff_top_even
    {m : ℕ} {a : ℝ} {f : ℝ[X]} (hf : SimpleNegRooted f m) (ha : 0 < a) :
    0 < (gammaOperatorNumerator (2 * m) a f).coeff m := by
  rw [coeff_gammaOperatorNumerator]
  by_cases hm : m = 0
  · subst m
    simpa using (mul_pos ha hf.coeff_zero_pos)
  · simp only [ite_eq_right hm]
    have htop : f.coeff m = f.leadingCoeff := by
      simp [leadingCoeff, hf.natDegree_eq]
    rw [htop]
    have hprev : 0 ≤ f.coeff (m - 1) := hf.nonneg (m - 1)
    have hlc : 0 < f.leadingCoeff := hf.pos
    push_cast
    have hfirst : 0 < (a + (m : ℝ)) * f.leadingCoeff := by positivity
    have hsecond : 0 ≤ (4 : ℝ) * f.coeff (m - 1) := by positivity
    nlinarith

private theorem gammaOperatorNumerator_coeff_top_odd
    {m : ℕ} {a : ℝ} {f : ℝ[X]} (hf : SimpleNegRooted f m) (ha : 0 < a) :
    0 < (gammaOperatorNumerator (2 * m + 1) a f).coeff (m + 1) := by
  rw [coeff_gammaOperatorNumerator]
  have htop : f.coeff m = f.leadingCoeff := by
    simp [leadingCoeff, hf.natDegree_eq]
  have hzero : f.coeff (m + 1) = 0 := by
    exact coeff_eq_zero_of_natDegree_lt (by rw [hf.natDegree_eq]; lia)
  rw [hzero, show m + 1 - 1 = m by lia, htop]
  have hlc : 0 < f.leadingCoeff := hf.pos
  push_cast
  have hfirst : 0 ≤ (a + (m + 1 : ℝ)) * 0 := by positivity
  have hsecond : 0 < (2 : ℝ) * f.leadingCoeff := by positivity
  nlinarith

private theorem gammaOperatorNumerator_coeff_even_next
    {m : ℕ} {a : ℝ} {f : ℝ[X]} (hf : SimpleNegRooted f m) :
    (gammaOperatorNumerator (2 * m) a f).coeff (m + 1) = 0 := by
  rw [coeff_gammaOperatorNumerator]
  have hzero : f.coeff (m + 1) = 0 := by
    exact coeff_eq_zero_of_natDegree_lt (by rw [hf.natDegree_eq]; lia)
  rw [hzero, show m + 1 - 1 = m by lia]
  have htop : f.coeff m = f.leadingCoeff := by
    simp [leadingCoeff, hf.natDegree_eq]
  rw [htop]
  push_cast
  ring

private theorem gammaOperatorNumerator_natDegree_even
    {m : ℕ} {a : ℝ} {f : ℝ[X]} (hf : SimpleNegRooted f m) (ha : 0 < a) :
    (gammaOperatorNumerator (2 * m) a f).natDegree = m := by
  have htop := gammaOperatorNumerator_coeff_top_even hf ha
  apply Nat.le_antisymm
  · apply (natDegree_le_iff_coeff_eq_zero).mpr
    intro k hk
    rw [coeff_gammaOperatorNumerator]
    have hkm : m + 1 ≤ k := by lia
    have hk0 : k ≠ 0 := by lia
    simp only [ite_eq_right hk0]
    have hfzero : f.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simpa [hf.natDegree_eq] using hk
    by_cases heq : k = m + 1
    · subst k
      rw [hfzero]
      push_cast
      ring
    · have hkgt : m + 1 < k := lt_of_le_of_ne hkm (Ne.symm heq)
      have hfprev : f.coeff (k - 1) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        simpa [hf.natDegree_eq] using (show m < k - 1 by lia)
      rw [hfzero, hfprev]
      ring
  · exact le_natDegree_of_ne_zero htop.ne'

private theorem gammaOperatorNumerator_natDegree_odd
    {m : ℕ} {a : ℝ} {f : ℝ[X]} (hf : SimpleNegRooted f m) (ha : 0 < a) :
    (gammaOperatorNumerator (2 * m + 1) a f).natDegree = m + 1 := by
  have htop := gammaOperatorNumerator_coeff_top_odd hf ha
  apply Nat.le_antisymm
  · apply (natDegree_le_iff_coeff_eq_zero).mpr
    intro k hk
    rw [coeff_gammaOperatorNumerator]
    have hk0 : k ≠ 0 := by lia
    simp only [ite_eq_right hk0]
    have hfzero : f.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simpa [hf.natDegree_eq] using (show m < k by lia)
    have hfprev : f.coeff (k - 1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simpa [hf.natDegree_eq] using (show m < k - 1 by lia)
    rw [hfzero, hfprev]
    ring
  · exact le_natDegree_of_ne_zero htop.ne'

private theorem gammaOperatorNumerator_natDegree
    {d m : ℕ} {a : ℝ} {f : ℝ[X]} (hf : SimpleNegRooted f m) (ha : 0 < a)
    (hd : d = 2 * m ∨ d = 2 * m + 1) :
    (gammaOperatorNumerator d a f).natDegree = m ∨
      (gammaOperatorNumerator d a f).natDegree = m + 1 := by
  rcases hd with rfl | rfl
  · exact Or.inl (gammaOperatorNumerator_natDegree_even hf ha)
  · exact Or.inr (gammaOperatorNumerator_natDegree_odd hf ha)

/-- At an input root, the numerator evaluates to the derivative term. -/
theorem gammaOperatorNumerator_eval_of_isRoot
    {d : ℕ} {a : ℝ} {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) :
    (gammaOperatorNumerator d a f).eval r =
      (X * (1 - C 4 * X) : ℝ[X]).eval r * f.derivative.eval r := by
  simp only [gammaOperatorNumerator, eval_add, eval_mul]
  rw [hr.eq_zero]
  ring

/-- The numerator has the strict Liu--Wang sign at every negative simple root. -/
theorem gammaOperatorNumerator_eval_mul_derivative_neg
    {d : ℕ} {a : ℝ} {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r)
    (hrneg : r < 0) (hregular : f.derivative.eval r ≠ 0) :
    (gammaOperatorNumerator d a f).eval r * f.derivative.eval r < 0 := by
  rw [gammaOperatorNumerator_eval_of_isRoot hr]
  have hfactor : (X * (1 - C 4 * X) : ℝ[X]).eval r < 0 := by
    simp only [eval_mul, eval_X, eval_sub, eval_one, eval_C]
    nlinarith
  have hsq : 0 < f.derivative.eval r * f.derivative.eval r := by
    simpa only [pow_two] using (sq_pos_iff.mpr hregular)
  rw [mul_assoc]
  exact mul_neg_of_neg_of_pos hfactor hsq

/-- Strict interlacing and negativity for a gamma numerator under the sign-side
conditions of Zhang--Zhao's Lemma 3.2. -/
theorem strictInterl_gammaOperatorNumerator
    {d m : ℕ} {a : ℝ} {f : ℝ[X]}
    (hm : f.natDegree = m) (hmpos : m ≠ 0)
    (hf : SimpleNegRooted f m)
    (hg : HasNonnegCoeffs (gammaOperatorNumerator d a f))
    (hg0 : 0 < (gammaOperatorNumerator d a f).coeff 0)
    (hdeg : (gammaOperatorNumerator d a f).natDegree = m ∨
      (gammaOperatorNumerator d a f).natDegree = m + 1) :
    StrictInterl f (gammaOperatorNumerator d a f) ∧
      (∀ r, f.IsRoot r → ¬(gammaOperatorNumerator d a f).IsRoot r) ∧
      ∀ r ∈ (gammaOperatorNumerator d a f).roots, r < 0 := by
  have hsign : ∀ r, f.IsRoot r →
      (gammaOperatorNumerator d a f).eval r * f.derivative.eval r < 0 := by
    intro r hr
    exact gammaOperatorNumerator_eval_mul_derivative_neg hr
      (hf.isRoot_neg hr) (hf.simple.eval_derivative_ne_zero hr)
  have hdeg' : (gammaOperatorNumerator d a f).natDegree = f.natDegree ∨
      (gammaOperatorNumerator d a f).natDegree = f.natDegree + 1 := by
    simpa [hm] using hdeg
  exact strictInterl_and_noCommonRoot_of_eval_mul_derivative_neg hf.splits hf.pos
    (by simpa [hm] using hmpos) hg hg0 hdeg' hsign

/-- The nonconstant part of Lemma 3.2, including the scalar normalization from
the numerator to `Φ_{d,a}`. -/
theorem simpleNegRooted_gammaOperator_of_coeff_degree
    {d m q : ℕ} {a : ℝ} {f : ℝ[X]}
    (hm : f.natDegree = m) (hmpos : m ≠ 0) (ha : 0 < a)
    (hf : SimpleNegRooted f m)
    (hg : HasNonnegCoeffs (gammaOperatorNumerator d a f))
    (hg0 : 0 < (gammaOperatorNumerator d a f).coeff 0)
    (hdeg : (gammaOperatorNumerator d a f).natDegree = q)
    (hq : q = m ∨ q = m + 1) :
    SimpleNegRooted (gammaOperator d a f) q := by
  have hsign : ∀ r, f.IsRoot r →
      (gammaOperatorNumerator d a f).eval r * f.derivative.eval r < 0 := by
    intro r hr
    exact gammaOperatorNumerator_eval_mul_derivative_neg hr
      (hf.isRoot_neg hr) (hf.simple.eval_derivative_ne_zero hr)
  have hdeg' : (gammaOperatorNumerator d a f).natDegree = f.natDegree ∨
      (gammaOperatorNumerator d a f).natDegree = f.natDegree + 1 := by
    simpa [hdeg, hm] using hq
  have hroot := strictInterl_and_noCommonRoot_of_eval_mul_derivative_neg
    hf.splits hf.pos (by simpa [hm] using hmpos) hg hg0 hdeg' hsign
  have hgne : gammaOperatorNumerator d a f ≠ 0 := by
    intro hzero
    have h := hg0
    rw [hzero] at h
    simp at h
  have hno : ∀ r, ¬(f.IsRoot r ∧
      (gammaOperatorNumerator d a f).IsRoot r) := by
    intro r hr
    exact hroot.2.1 r hr.1 hr.2
  have hsimple : HasSimpleRoots (gammaOperatorNumerator d a f) :=
    (hroot.1.hasSimpleRoots_of_no_common_root hno).2
  have hbase : SimpleNegRooted (gammaOperatorNumerator d a f) q := by
    refine ⟨hdeg, hg.pos_leadingCoeff hgne, hg, hg0, hroot.1.2.1.2, hsimple⟩
  simpa only [gammaOperator] using hbase.C_mul (inv_pos.mpr ha)

/-- The gamma operator preserves simple negative zeros for a nonconstant input;
the two alternatives record the exact even/odd output degree. -/
theorem simpleNegRooted_gammaOperator_of_pos_natDegree
    {d m : ℕ} {a : ℝ} {f : ℝ[X]} (hmpos : m ≠ 0) (ha : 0 < a)
    (hf : SimpleNegRooted f m) (hd : d = 2 * m ∨ d = 2 * m + 1) :
    (d = 2 * m ∧ SimpleNegRooted (gammaOperator d a f) m) ∨
      (d = 2 * m + 1 ∧ SimpleNegRooted (gammaOperator d a f) (m + 1)) := by
  rcases hd with rfl | rfl
  · have hnonneg : HasNonnegCoeffs (gammaOperatorNumerator (2 * m) a f) := by
      apply gammaOperatorNumerator_hasNonnegCoeffs hf
      · lia
      · exact ha
    have hzero : 0 < (gammaOperatorNumerator (2 * m) a f).coeff 0 := by
      rw [coeff_gammaOperatorNumerator]
      simpa using (mul_pos ha hf.coeff_zero_pos)
    exact Or.inl ⟨rfl, simpleNegRooted_gammaOperator_of_coeff_degree
      hf.natDegree_eq hmpos ha hf hnonneg hzero
      (gammaOperatorNumerator_natDegree_even hf ha) (Or.inl rfl)⟩
  · have hnonneg : HasNonnegCoeffs (gammaOperatorNumerator (2 * m + 1) a f) := by
      apply gammaOperatorNumerator_hasNonnegCoeffs hf
      · lia
      · exact ha
    have hzero : 0 < (gammaOperatorNumerator (2 * m + 1) a f).coeff 0 := by
      rw [coeff_gammaOperatorNumerator]
      simpa using (mul_pos ha hf.coeff_zero_pos)
    exact Or.inr ⟨rfl, simpleNegRooted_gammaOperator_of_coeff_degree
      hf.natDegree_eq hmpos ha hf hnonneg hzero
      (gammaOperatorNumerator_natDegree_odd hf ha) (Or.inr rfl)⟩

private theorem simpleNegRooted_gammaOperator_zero
    {d : ℕ} {a : ℝ} {f : ℝ[X]} (ha : 0 < a) (hf : SimpleNegRooted f 0)
    (hd : d = 0 ∨ d = 1) :
    (d = 0 ∧ SimpleNegRooted (gammaOperator d a f) 0) ∨
      (d = 1 ∧ SimpleNegRooted (gammaOperator d a f) 1) := by
  have hf_eq : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hf.natDegree_eq
  have hc : 0 < f.coeff 0 := hf.coeff_zero_pos
  rcases hd with rfl | rfl
  · left
    constructor
    · rfl
    have hop : gammaOperator 0 a f = f := by
      rw [hf_eq]
      simp only [gammaOperator, gammaOperatorNumerator, derivative_C, mul_zero,
        Nat.cast_zero, C_0, zero_mul, add_zero]
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ ha.ne', C_1, one_mul]
    rw [hop]
    exact hf
  · right
    constructor
    · rfl
    let b : ℝ := 2 * a⁻¹
    have hb : 0 < b := by
      dsimp [b]
      positivity
    let p : ℝ[X] := 1 + C b * X
    have hp_eq : p = C b * (X + C b⁻¹) := by
      dsimp [p]
      rw [mul_add, ← C_mul]
      have hbinv : b * b⁻¹ = 1 := by exact mul_inv_cancel₀ hb.ne'
      rw [hbinv, C_1]
      ring
    have hpdeg : p.natDegree = 1 := by
      rw [hp_eq, natDegree_C_mul hb.ne', natDegree_X_add_C]
    have hprr : p ≠ 0 ∧ p.Splits := isRealRooted_of_degree_one hpdeg
    have hpsimple : HasSimpleRoots p :=
      hasSimpleRoots_of_natDegree_le_one hprr.1 hpdeg.le
    have hppos : HasPosLeadingCoeff p := by
      rw [hp_eq]
      exact hasPosLeadingCoeff_C_mul hb (hasPosLeadingCoeff_X_add_C _)
    have hpnn : HasNonnegCoeffs p := by
      rw [hp_eq]
      exact nonnegCoeffs_C_mul hb.le (hasNonnegCoeffs_X_add_C (by positivity))
    have hp0 : 0 < p.coeff 0 := by
      simp [p]
    have hbase : SimpleNegRooted p 1 :=
      ⟨hpdeg, hppos, hpnn, hp0, hprr.2, hpsimple⟩
    have hop : gammaOperator 1 a f = C (f.coeff 0) * p := by
      rw [hf_eq]
      dsimp [p, b, gammaOperator, gammaOperatorNumerator]
      simp only [coeff_C_zero, derivative_C, mul_zero, Nat.cast_one, mul_one,
        add_zero]
      rw [mul_add]
      calc
        C a⁻¹ * (C a * C (f.coeff 0)) +
            C a⁻¹ * (C 2 * X * C (f.coeff 0)) =
            C (f.coeff 0) + C (a⁻¹ * 2) * X * C (f.coeff 0) := by
          rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ ha.ne', C_1, one_mul]
          rw [show C a⁻¹ * (C 2 * X * C (f.coeff 0)) =
            (C a⁻¹ * C 2) * X * C (f.coeff 0) by ring]
          rw [← C_mul]
        _ = C (f.coeff 0) * (1 + C (2 * a⁻¹) * X) := by
          rw [mul_add, mul_one]
          rw [show C (f.coeff 0) * (C (2 * a⁻¹) * X) =
            C (2 * a⁻¹) * X * C (f.coeff 0) by ring]
          rw [mul_comm a⁻¹ 2]
    rw [hop]
    exact hbase.C_mul hc

/-- Lemma 3.2: `Φ_{d,a}` preserves simple negative zeros, with its exact
even/odd output degree, including constant inputs. -/
theorem simpleNegRooted_gammaOperator
    {d m : ℕ} {a : ℝ} {f : ℝ[X]} (ha : 0 < a)
    (hf : SimpleNegRooted f m) (hd : d = 2 * m ∨ d = 2 * m + 1) :
    (d = 2 * m ∧ SimpleNegRooted (gammaOperator d a f) m) ∨
      (d = 2 * m + 1 ∧ SimpleNegRooted (gammaOperator d a f) (m + 1)) := by
  rcases hd with rfl | rfl
  · by_cases hm : m = 0
    · subst m
      exact simpleNegRooted_gammaOperator_zero ha hf (Or.inl rfl)
    · exact simpleNegRooted_gammaOperator_of_pos_natDegree hm ha hf (Or.inl rfl)
  · by_cases hm : m = 0
    · subst m
      exact simpleNegRooted_gammaOperator_zero ha hf (Or.inr rfl)
    · exact simpleNegRooted_gammaOperator_of_pos_natDegree hm ha hf (Or.inr rfl)

end MultisetEulerianNarayana
end Applications
end RealRooted
