module

public import RealRooted.ExponentialRows.SubstitutionRows
public import RealRooted.PFPolynomial
import RealRooted.ExponentialRows.SubstitutionPolynomialKernel
import RealRooted.ExponentialRows.SubstitutionPolynomialPreserver
import RealRooted.ExponentialRows.SubstitutionFactor
import RealRooted.ExponentialRows.Substitution
import RealRooted.ExponentialRows.SubstitutionComposition
import Mathlib.Tactic

/-!
# PF polynomial substitutions of marked block series

For every PF polynomial `P`, substitution `B ↦ P(B) - P(0)` preserves
real-rooted exponential rows and every directed weak input-row interlacing.
The unmarked series is arbitrary and fixed. Zero parameters, zero outer
polynomials, and vanishing rows are included.

Source: unpublished manuscript, *Degree-raising substitutions for exponential rows*,
Theorem 1, RealRooted issue #2415:
https://github.com/PerAlexandersson/RealRooted/issues/2415#issuecomment-7141592218.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- Removing the constant coefficient of a polynomial gives a substitutable
formal series, independently of any sign condition. -/
private theorem polynomial_sub_constantCoeff (P : ℝ[X]) :
    PowerSeries.constantCoeff ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ) = 0 := by
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coe,
    coeff_sub, coeff_C_zero, sub_self]

/-- Removing a PF polynomial's constant term leaves nonnegative coefficients. -/
private theorem polynomial_sub_coeff_nonneg {P : ℝ[X]} (hP : IsPFPolynomial P) (n : ℕ) :
    0 ≤ PowerSeries.coeff n ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ) := by
  rw [coeff_coe, coeff_sub, coeff_C]
  split_ifs with hn
  · subst n
    rw [sub_self]
  · simpa only [sub_zero] using hP.hasNonnegCoeffs n

/-- A PF outer symbol induces a PF-preserving kernel operator, together with
all its positive-constant single-factor interlacing edges. -/
private theorem polynomial_kernel_preserver {P : ℝ[X]} (hP : IsPFPolynomial P) (hPne : P ≠ 0) :
    (∀ {p}, IsPFPolynomial p →
      IsPFPolynomial (exponentialSubstitution
        ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ) p)) ∧
    (∀ {p}, IsPFPolynomial p → 0 < p.coeff 0 → ∀ r : ℝ, 0 < r →
      StrictInterl
        (exponentialSubstitution ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ) p)
        (exponentialSubstitution ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ)
          ((X + C r) * p))) := by
  exact isPFPolynomial_map_and_strictInterl_of_polynomial_rule _ hP hPne
    (fun _ hp => hasNonnegCoeffs_exponentialSubstitution (polynomial_sub_constantCoeff P)
      (polynomial_sub_coeff_nonneg hP) hp)
    (coeff_zero_exponentialSubstitution (polynomial_sub_constantCoeff P))
    (exponentialSubstitution_one (polynomial_sub_constantCoeff P))
    (natDegree_exponentialSubstitution_le (polynomial_sub_constantCoeff P))
    exponentialSubstitution_applyDifferential exponentialSubstitution_X_mul_polynomial

/-- For every PF polynomial `P`, the exponential kernel of `P - P(0)`
preserves all PF polynomials. -/
theorem isPFPolynomial_exponentialSubstitution_polynomial {P : ℝ[X]}
    (hP : IsPFPolynomial P) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (exponentialSubstitution
      ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ) p) := by
  by_cases hPne : P = 0
  · subst P
    simpa only [coeff_zero, map_zero, sub_zero, Polynomial.coe_zero] using
      isPFPolynomial_exponentialSubstitution (P := (0 : PowerSeries ℝ))
        (by simp) (a := 0) (b := 0) (l := 0) (by simp)
        le_rfl le_rfl le_rfl hp
  · exact (polynomial_kernel_preserver hP hPne).1 hp

/-- PF polynomial outer symbols preserve every directed weak PF interlacing,
including roots at zero and vanishing outputs. -/
theorem interl_exponentialSubstitution_polynomial {P : ℝ[X]}
    (hP : IsPFPolynomial P) {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfg : Interl f g) :
    Interl
      (exponentialSubstitution ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ) f)
      (exponentialSubstitution ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ) g) := by
  by_cases hPne : P = 0
  · subst P
    simpa only [coeff_zero, map_zero, sub_zero, Polynomial.coe_zero] using
      interl_exponentialSubstitution (P := (0 : PowerSeries ℝ))
        (by simp) (a := 0) (b := 0) (l := 0) (by simp)
        le_rfl le_rfl le_rfl hf hg hfg
  · exact interl_map_of_pos_constant_factor _
      (fun _ hp => hasNonnegCoeffs_exponentialSubstitution (polynomial_sub_constantCoeff P)
        (polynomial_sub_coeff_nonneg hP) hp)
      (coeff_zero_exponentialSubstitution (polynomial_sub_constantCoeff P))
      (natDegree_exponentialSubstitution_le (polynomial_sub_constantCoeff P))
      (fun hp _ => isPFPolynomial_exponentialSubstitution_polynomial hP hp)
      (fun hp hp0 _ => (polynomial_kernel_preserver hP hPne).2 hp hp0)
      hf hg (le_max_left f.natDegree g.natDegree) (le_max_right f.natDegree g.natDegree) hfg

/-- Formal substitution of the polynomial's zero-constant part is literal
polynomial evaluation minus its constant coefficient. -/
private theorem subst_polynomial_sub_constant {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (P : ℝ[X]) :
    ((P - C (P.coeff 0) : ℝ[X]) : PowerSeries ℝ).subst B =
      Polynomial.aeval B P - PowerSeries.C (P.coeff 0) := by
  rw [PowerSeries.subst_coe (PowerSeries.HasSubst.of_constantCoeff_zero' hB),
    map_sub, aeval_C]
  rfl

/-- Substitution `B ↦ P(B) - P(0)` for any nonnegative, nonpositive-rooted
outer polynomial preserves splitting of each exponential row. -/
theorem insertionRow_splits_polynomial_subst {A B : PowerSeries ℝ} {P : ℝ[X]}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hP : IsPFPolynomial P)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (n : ℕ) (hrow : (insertionRow (affineBlockWeights A B) n).Splits) :
    (insertionRow (affineBlockWeights A
      (Polynomial.aeval B P - PowerSeries.C (P.coeff 0))) n).Splits := by
  rw [← subst_polynomial_sub_constant hB,
    ← exponentialSubstitution_insertionRow hA hB (polynomial_sub_constantCoeff P)]
  exact (isPFPolynomial_exponentialSubstitution_polynomial hP
    (IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_insertionRow_affineBlockWeights hAnn hBnn n) hrow)).splits

/-- Every directed weak interlacing between input exponential rows survives
substitution by a PF polynomial after subtracting its constant coefficient. -/
theorem insertionRow_interl_polynomial_subst {A B : PowerSeries ℝ} {P : ℝ[X]}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hP : IsPFPolynomial P)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    {m n : ℕ} (hm : (insertionRow (affineBlockWeights A B) m).Splits)
    (hn : (insertionRow (affineBlockWeights A B) n).Splits)
    (hinterl : Interl (insertionRow (affineBlockWeights A B) m)
      (insertionRow (affineBlockWeights A B) n)) :
    Interl (insertionRow (affineBlockWeights A
      (Polynomial.aeval B P - PowerSeries.C (P.coeff 0))) m)
      (insertionRow (affineBlockWeights A
        (Polynomial.aeval B P - PowerSeries.C (P.coeff 0))) n) := by
  rw [← subst_polynomial_sub_constant hB,
    ← exponentialSubstitution_insertionRow hA hB (polynomial_sub_constantCoeff P),
    ← exponentialSubstitution_insertionRow hA hB (polynomial_sub_constantCoeff P)]
  exact interl_exponentialSubstitution_polynomial hP
    (IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_insertionRow_affineBlockWeights hAnn hBnn m) hm)
    (IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_insertionRow_affineBlockWeights hAnn hBnn n) hn) hinterl

/-- With unmarked singleton weight one, a PF outer polynomial preserves
nonzero real-rootedness of every row, with no positive-parameter assumption. -/
theorem insertionRow_isRealRooted_polynomial_subst {B : PowerSeries ℝ} {P : ℝ[X]}
    (hB : PowerSeries.constantCoeff B = 0) (hP : IsPFPolynomial P)
    (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (n : ℕ) (hrow : (insertionRow (affineBlockWeights PowerSeries.X B) n).Splits) :
    insertionRow (affineBlockWeights PowerSeries.X
      (Polynomial.aeval B P - PowerSeries.C (P.coeff 0))) n ≠ 0 ∧
      (insertionRow (affineBlockWeights PowerSeries.X
        (Polynomial.aeval B P - PowerSeries.C (P.coeff 0))) n).Splits := by
  have hPB : PowerSeries.constantCoeff
      (Polynomial.aeval B P - PowerSeries.C (P.coeff 0)) = 0 := by
    rw [← subst_polynomial_sub_constant hB, PowerSeries.constantCoeff_eq,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero hB]
    exact polynomial_sub_constantCoeff P
  refine ⟨insertionRow_affine_X_ne_zero hPB n, ?_⟩
  apply insertionRow_splits_polynomial_subst PowerSeries.constantCoeff_X hB hP _ hBnn n hrow
  intro r
  rw [PowerSeries.coeff_X]
  split_ifs <;> positivity

/-- Every positive integer power of an admissible nonnegative marked series
preserves splitting of each exponential row. -/
theorem insertionRow_splits_pow {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (n : ℕ) (hrow : (insertionRow (affineBlockWeights A B) n).Splits)
    {k : ℕ} (hk : k ≠ 0) :
    (insertionRow (affineBlockWeights A (B ^ k)) n).Splits := by
  have hc : (X ^ k : ℝ[X]).coeff 0 = 0 := by
    simp only [coeff_X_pow, ite_eq_right (Ne.symm hk)]
  simpa only [map_pow, aeval_X, hc, map_zero, sub_zero] using
    insertionRow_splits_polynomial_subst hA hB (isPFPolynomial_X_pow k) hAnn hBnn n hrow

/-- Every positive integer power of the marked series preserves every
directed weak input-row interlacing, including vanishing rows. -/
theorem insertionRow_interl_pow {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    {m n : ℕ} (hm : (insertionRow (affineBlockWeights A B) m).Splits)
    (hn : (insertionRow (affineBlockWeights A B) n).Splits)
    (hinterl : Interl (insertionRow (affineBlockWeights A B) m)
      (insertionRow (affineBlockWeights A B) n)) {k : ℕ} (hk : k ≠ 0) :
    Interl (insertionRow (affineBlockWeights A (B ^ k)) m)
      (insertionRow (affineBlockWeights A (B ^ k)) n) := by
  have hc : (X ^ k : ℝ[X]).coeff 0 = 0 := by
    simp only [coeff_X_pow, ite_eq_right (Ne.symm hk)]
  simpa only [map_pow, aeval_X, hc, map_zero, sub_zero] using
    insertionRow_interl_polynomial_subst hA hB (isPFPolynomial_X_pow k)
      hAnn hBnn hm hn hinterl

end RealRooted.ExponentialRows
