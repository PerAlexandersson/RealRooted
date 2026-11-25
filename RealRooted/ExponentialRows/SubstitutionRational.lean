module

public import RealRooted.ExponentialRows.SubstitutionRows
public import RealRooted.PFPolynomial
import RealRooted.ExponentialRows.SubstitutionComposition
import RealRooted.ExponentialRows.SubstitutionRationalKernel
import RealRooted.ExponentialRows.SubstitutionRationalPreserver
import Mathlib.Tactic

/-!
# Rational-ODE substitution closure of exponential rows

If `(1 - d x) Φ' = a + b x + λ Φ` and all four parameters are nonnegative,
substitution of `Φ(B)` preserves every real-rooted exponential row and every
directed weak interlacing between input rows. The unmarked series is arbitrary
and fixed. Zero parameters and zero rows are included.

Source: unpublished manuscript, *Degree-raising substitutions for exponential rows*,
Theorem 2, RealRooted issue #2415, round-4 comment:
https://github.com/PerAlexandersson/RealRooted/issues/2415#issuecomment-7141592218.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- Rational-ODE exponential substitution preserves every PF polynomial. -/
theorem isPFPolynomial_exponentialSubstitution_of_rational_ode
    {P : PowerSeries ℝ} {a b l d : ℝ}
    (hP : PowerSeries.constantCoeff P = 0)
    (hode : (1 - PowerSeries.C d * PowerSeries.X) * PowerSeries.derivative P =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * P)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l) (hd : 0 ≤ d)
    {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (exponentialSubstitution P p) := by
  apply isPFPolynomial_map_of_rational_substitution_rule (exponentialSubstitution P) hb hl hd
  · intro q hq
    exact hasNonnegCoeffs_exponentialSubstitution hP
      (coeff_nonneg_of_rational_substitution_ode hP hode ha hb hl hd) hq
  · exact coeff_zero_exponentialSubstitution hP
  · exact exponentialSubstitution_one hP
  · exact exponentialSubstitution_linear_mul_of_rational_ode hP hode
  · exact hp

/-- Rational-ODE substitution preserves every directed weak PF interlacing,
including vanishing images. -/
theorem interl_exponentialSubstitution_of_rational_ode
    {P : PowerSeries ℝ} {a b l d : ℝ}
    (hP : PowerSeries.constantCoeff P = 0)
    (hode : (1 - PowerSeries.C d * PowerSeries.X) * PowerSeries.derivative P =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * P)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l) (hd : 0 ≤ d)
    {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfg : Interl f g) :
    Interl (exponentialSubstitution P f) (exponentialSubstitution P g) := by
  apply interl_map_of_rational_substitution_rule (exponentialSubstitution P) hb hl hd
  · intro q hq
    exact hasNonnegCoeffs_exponentialSubstitution hP
      (coeff_nonneg_of_rational_substitution_ode hP hode ha hb hl hd) hq
  · exact coeff_zero_exponentialSubstitution hP
  · exact exponentialSubstitution_one hP
  · exact exponentialSubstitution_linear_mul_of_rational_ode hP hode
  · exact natDegree_exponentialSubstitution_le hP
  · exact hf
  · exact hg
  · exact hfg

/-- The four-parameter rational ODE preserves splitting of each exponential
row for arbitrary nonnegative unmarked and marked series. -/
theorem insertionRow_splits_subst_of_rational_ode
    {A B P : PowerSeries ℝ} {a b l d : ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hP : PowerSeries.constantCoeff P = 0)
    (hode : (1 - PowerSeries.C d * PowerSeries.X) * PowerSeries.derivative P =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * P)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l) (hd : 0 ≤ d)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (n : ℕ) (hrow : (insertionRow (affineBlockWeights A B) n).Splits) :
    (insertionRow (affineBlockWeights A (P.subst B)) n).Splits := by
  rw [← exponentialSubstitution_insertionRow hA hB hP]
  exact (isPFPolynomial_exponentialSubstitution_of_rational_ode hP hode ha hb hl hd
    (IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_insertionRow_affineBlockWeights hAnn hBnn n) hrow)).splits

/-- Every directed weak interlacing between exponential rows survives a
four-parameter rational-ODE substitution of the marked series. -/
theorem insertionRow_interl_subst_of_rational_ode
    {A B P : PowerSeries ℝ} {a b l d : ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hP : PowerSeries.constantCoeff P = 0)
    (hode : (1 - PowerSeries.C d * PowerSeries.X) * PowerSeries.derivative P =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * P)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l) (hd : 0 ≤ d)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    {m n : ℕ}
    (hm : (insertionRow (affineBlockWeights A B) m).Splits)
    (hn : (insertionRow (affineBlockWeights A B) n).Splits)
    (hinterl : Interl (insertionRow (affineBlockWeights A B) m)
      (insertionRow (affineBlockWeights A B) n)) :
    Interl (insertionRow (affineBlockWeights A (P.subst B)) m)
      (insertionRow (affineBlockWeights A (P.subst B)) n) := by
  rw [← exponentialSubstitution_insertionRow hA hB hP,
    ← exponentialSubstitution_insertionRow hA hB hP]
  exact interl_exponentialSubstitution_of_rational_ode hP hode ha hb hl hd
    (IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_insertionRow_affineBlockWeights hAnn hBnn m) hm)
    (IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_insertionRow_affineBlockWeights hAnn hBnn n) hn) hinterl


/-- With the original unmarked singleton series `A = z`, rational-ODE
substitution preserves nonzero real-rootedness, with no extra assumption on
constant coefficients or on positive parameter values. -/
theorem insertionRow_isRealRooted_subst_of_rational_ode
    {B P : PowerSeries ℝ} {a b l d : ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (hP : PowerSeries.constantCoeff P = 0)
    (hode : (1 - PowerSeries.C d * PowerSeries.X) * PowerSeries.derivative P =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * P)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l) (hd : 0 ≤ d)
    (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (n : ℕ) (hrow : (insertionRow (affineBlockWeights PowerSeries.X B) n).Splits) :
    insertionRow (affineBlockWeights PowerSeries.X (P.subst B)) n ≠ 0 ∧
      (insertionRow (affineBlockWeights PowerSeries.X (P.subst B)) n).Splits := by
  have hPB : PowerSeries.constantCoeff (P.subst B) = 0 := by
    rw [PowerSeries.constantCoeff_eq,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero hB]
    exact hP
  refine ⟨insertionRow_affine_X_ne_zero hPB n, ?_⟩
  apply insertionRow_splits_subst_of_rational_ode PowerSeries.constantCoeff_X hB hP hode
    ha hb hl hd _ hBnn n hrow
  intro r
  rw [PowerSeries.coeff_X]
  split_ifs <;> positivity

end RealRooted.ExponentialRows
