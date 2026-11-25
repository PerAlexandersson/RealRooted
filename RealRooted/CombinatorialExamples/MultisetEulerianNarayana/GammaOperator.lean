module

public import RealRooted.CombinatorialExamples.MultisetEulerianNarayana
import RealRooted.MaWang.Strong
import RealRooted.DerivativeRecurrence.Interlacing
public import RealRooted.EulerOperator.Darboux.NegativeRoots
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Linear

/-!
# The gamma operator for multiset Eulerian--Narayana polynomials

Zhang--Zhao (arXiv:2610.00966), Lemma 3.2: for `a > 0` the gamma operator
`Φ_{d,a} Γ = Γ + (z(1 - 4z)Γ' + 2dzΓ)/a` preserves simple negative zeros
(`simpleNegRooted_gammaOperator`).  The degree rises by one exactly when `d` is odd; for
even `d` the top coefficient of `z(1 - 4z)Γ' + 2dzΓ` cancels.  The sign/interlacing core
(`strictInterl_gammaOperatorNumerator`) is stated separately from the coefficient bookkeeping.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted
namespace MultisetEulerianNarayana

/-- The numerator of `Φ_{d,a} Γ = Γ + D_d Γ / a`. -/
def gammaOperatorNumerator (d : ℕ) (a : ℝ) (f : ℝ[X]) : ℝ[X] :=
  C a * f + X * (1 - C 4 * X) * f.derivative + C (2 * (d : ℝ)) * X * f

/-- The gamma operator `Φ_{d,a}` from Zhang--Zhao, equation (20). -/
def gammaOperator (d : ℕ) (a : ℝ) (f : ℝ[X]) : ℝ[X] :=
  C a⁻¹ * gammaOperatorNumerator d a f

/-- The numerator is a quadratic-derivative step in the generic coefficient API. -/
private lemma gammaOperatorNumerator_eq (d : ℕ) (a : ℝ) (f : ℝ[X]) :
    gammaOperatorNumerator d a f =
      (C 1 * X + C (-4) * X ^ 2) * f.derivative +
        (C a + C (2 * (d : ℝ)) * X) * f := by
  simp only [gammaOperatorNumerator, map_one, map_neg, map_ofNat]
  ring

private theorem gammaOperatorNumerator_hasNonnegCoeffs
    {d m : ℕ} {a : ℝ} {f : ℝ[X]} (hf : SimpleNegRooted f m)
    (hd : 2 * m ≤ d) (ha : 0 < a) :
    HasNonnegCoeffs (gammaOperatorNumerator d a f) := by
  rw [gammaOperatorNumerator_eq, add_comm]
  apply hasNonnegCoeffs_mul_add_mul_derivative hf.natDegree_eq.le (by simp) ?_ hf.nonneg
  intro i j hj
  have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
  have hd' : 2 * (m : ℝ) ≤ d := by exact_mod_cast hd
  simp only [coeff_add, coeff_C_mul, coeff_X, coeff_X_pow, coeff_C]
  rcases i with _ | _ | i
  · norm_num
    positivity
  · norm_num
    linarith
  · simp

private theorem gammaOperatorNumerator_natDegree_even
    {m : ℕ} {a : ℝ} {f : ℝ[X]} (hf : SimpleNegRooted f m) (ha : 0 < a) :
    (gammaOperatorNumerator (2 * m) a f).natDegree = m := by
  rw [gammaOperatorNumerator_eq]
  apply (derivativeRecurrence_natDegree_eq_and_leadingCoeff_pos_step_of_cancel
    (m := 1) (by norm_num) (by compute_degree) (by compute_degree)
    hf.nonneg hf.natDegree_eq hf.pos ?_).1
  right
  simp only [coeff_add, coeff_C_mul, coeff_X, coeff_X_pow, coeff_C]
  norm_num
  exact ⟨by ring, by positivity⟩

private theorem gammaOperatorNumerator_natDegree_odd
    {m : ℕ} {a : ℝ} {f : ℝ[X]} (hf : SimpleNegRooted f m) :
    (gammaOperatorNumerator (2 * m + 1) a f).natDegree = m + 1 := by
  rw [gammaOperatorNumerator_eq]
  apply (derivativeRecurrence_natDegree_eq_and_leadingCoeff_pos_step_of_cancel
    (m := 1) (by norm_num) (by compute_degree) (by compute_degree)
    hf.nonneg hf.natDegree_eq hf.pos ?_).1
  left
  simp only [coeff_add, coeff_C_mul, coeff_X, coeff_X_pow, coeff_C]
  norm_num
  linarith

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
  have hroot := strictInterl_gammaOperatorNumerator hm hmpos hf hg hg0
    (by simpa only [hdeg] using hq)
  have hgne : gammaOperatorNumerator d a f ≠ 0 := by
    intro hzero
    simp [hzero] at hg0
  have hsimple := (hroot.1.hasSimpleRoots_of_no_common_root
    (fun r hr => hroot.2.1 r hr.1 hr.2)).2
  have hbase : SimpleNegRooted (gammaOperatorNumerator d a f) q :=
    ⟨hdeg, hg.pos_leadingCoeff hgne, hg, hg0, hroot.1.2.1.2, hsimple⟩
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
      simpa [gammaOperatorNumerator] using mul_pos ha hf.coeff_zero_pos
    exact Or.inl ⟨rfl, simpleNegRooted_gammaOperator_of_coeff_degree
      hf.natDegree_eq hmpos ha hf hnonneg hzero
      (gammaOperatorNumerator_natDegree_even hf ha) (Or.inl rfl)⟩
  · have hnonneg : HasNonnegCoeffs (gammaOperatorNumerator (2 * m + 1) a f) := by
      apply gammaOperatorNumerator_hasNonnegCoeffs hf
      · lia
      · exact ha
    have hzero : 0 < (gammaOperatorNumerator (2 * m + 1) a f).coeff 0 := by
      simpa [gammaOperatorNumerator] using mul_pos ha hf.coeff_zero_pos
    exact Or.inr ⟨rfl, simpleNegRooted_gammaOperator_of_coeff_degree
      hf.natDegree_eq hmpos ha hf hnonneg hzero
      (gammaOperatorNumerator_natDegree_odd hf) (Or.inr rfl)⟩

private theorem simpleNegRooted_gammaOperator_zero
    {d : ℕ} {a : ℝ} {f : ℝ[X]} (ha : 0 < a) (hf : SimpleNegRooted f 0)
    (hd : d = 0 ∨ d = 1) :
    (d = 0 ∧ SimpleNegRooted (gammaOperator d a f) 0) ∨
      (d = 1 ∧ SimpleNegRooted (gammaOperator d a f) 1) := by
  have hnonneg := gammaOperatorNumerator_hasNonnegCoeffs hf (by lia : 2 * 0 ≤ d) ha
  have hzero : 0 < (gammaOperatorNumerator d a f).coeff 0 := by
    simpa [gammaOperatorNumerator] using mul_pos ha hf.coeff_zero_pos
  have hne : gammaOperatorNumerator d a f ≠ 0 := by
    intro hzero'
    simp [hzero'] at hzero
  have hbase (q : ℕ) (hq : q ≤ 1)
      (hdeg : (gammaOperatorNumerator d a f).natDegree = q) :
      SimpleNegRooted (gammaOperator d a f) q := by
    have hnum : SimpleNegRooted (gammaOperatorNumerator d a f) q :=
      ⟨hdeg, hnonneg.pos_leadingCoeff hne, hnonneg, hzero,
        Splits.of_natDegree_le_one (hdeg.le.trans hq),
        hasSimpleRoots_of_natDegree_le_one hne (hdeg.le.trans hq)⟩
    simpa only [gammaOperator] using hnum.C_mul (inv_pos.mpr ha)
  rcases hd with rfl | rfl
  · exact Or.inl ⟨rfl, hbase 0 (by lia) (gammaOperatorNumerator_natDegree_even (m := 0) hf ha)⟩
  · exact Or.inr ⟨rfl, hbase 1 (by lia) (gammaOperatorNumerator_natDegree_odd (m := 0) hf)⟩

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
end RealRooted
