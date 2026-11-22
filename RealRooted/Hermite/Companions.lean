module

public import RealRooted.Hermite.FiniteTransfer
public import Mathlib.RingTheory.Polynomial.Pochhammer
import RealRooted.MultiplierSequence.InvPochhammer
import RealRooted.MultiplierSequence.PolyaSchur
import RealRooted.Mathlib.Algebra.Polynomial.Reverse

/-!
# Weighted Hermite companions

A finite multiplier sequence can be applied to the reflected Jensen input
before the Hermite transform. This includes the reciprocal-factorial companion
following Corollary 3.8 of Cormac O'Sullivan, *Zeros of Jensen polynomials and
asymptotics for the Riemann xi function*, https://arxiv.org/abs/2007.13582.
Reciprocal rising factorials give a further parameterized family.
-/

@[expose] public section

open Polynomial

namespace RealRooted

/-- A Hermite Jensen polynomial with a weight on the Hermite index. -/
noncomputable def hermiteCompanion (d : ℕ) (gamma weight : ℕ → ℝ) : ℝ[X] :=
  hermiteJensenPolynomial d (fun k => gamma k * weight (d - k))

/-- The reciprocal-factorial Hermite companion. -/
noncomputable def hermiteFactorialPolynomial (d : ℕ) (gamma : ℕ → ℝ) : ℝ[X] :=
  hermiteCompanion d gamma (fun k => (k.factorial : ℝ)⁻¹)

/-- The reciprocal rising-factorial Hermite companion with parameter `a`. -/
noncomputable def hermitePochhammerPolynomial (d : ℕ) (gamma : ℕ → ℝ) (a : ℝ) : ℝ[X] :=
  hermiteCompanion d gamma (fun k => ((ascPochhammer ℝ k).eval a)⁻¹)

/-- The degree-zero companion is the product of the initial coefficients. -/
@[simp] theorem hermiteCompanion_zero (gamma weight : ℕ → ℝ) :
    hermiteCompanion 0 gamma weight = C (gamma 0 * weight 0) := by
  simp [hermiteCompanion, hermiteJensenPolynomial]

/-- Reflection turns a weight on the Hermite index into an ordinary diagonal operator. -/
theorem reflect_jensenPolynomial_weight (d : ℕ) (gamma weight : ℕ → ℝ) :
    reflect d (jensenPolynomial d (fun k => gamma k * weight (d - k))) =
      diagonalOperator weight (reflect d (jensenPolynomial d gamma)) := by
  ext k
  simp only [coeff_diagonalOperator, coeff_reflect]
  by_cases hk : k ≤ d
  · rw [revAt_le hk]
    simp [coeff_jensenPolynomial, Nat.sub_sub_self hk]
    ring
  · rw [revAt_eq_self_of_lt (lt_of_not_ge hk)]
    simp [coeff_jensenPolynomial, hk]

/-- A weighted companion is a diagonal operator followed by the Hermite transform. -/
theorem hermiteCompanion_eq_basisTransform (d : ℕ) (gamma weight : ℕ → ℝ) :
    hermiteCompanion d gamma weight =
      basisTransform hermitePhysicists
        (diagonalOperator weight (reflect d (jensenPolynomial d gamma))) := by
  rw [hermiteCompanion, hermiteJensenPolynomial_eq_basisTransform,
    reflect_jensenPolynomial_weight]

/-- Finite multiplier weights preserve splitting of the Hermite companion,
including zero inputs and weights with zero entries. -/
theorem hermiteCompanion_splits {d : ℕ} {gamma weight : ℕ → ℝ}
    (hweight : IsFiniteMultiplierSequence d weight)
    (hp : (jensenPolynomial d gamma).Splits) :
    (hermiteCompanion d gamma weight).Splits := by
  rw [hermiteCompanion_eq_basisTransform]
  apply splits_hermiteBasisTransform
  have hdeg : (reflect d (jensenPolynomial d gamma)).natDegree ≤ d :=
    natDegree_reflect_le.trans (max_eq_left (natDegree_jensenPolynomial_le d gamma)).le
  rcases hweight hdeg (hp.reflect (natDegree_jensenPolynomial_le d gamma)) with hz | hs
  · simp [hz]
  · exact hs

/-- A weighted companion is simple-real-rooted whenever its transformed
input is nonzero and the finite multiplier hypothesis holds. -/
theorem isSimpleRealRooted_hermiteCompanion {d : ℕ} {gamma weight : ℕ → ℝ}
    (hweight : IsFiniteMultiplierSequence d weight)
    (hp : (jensenPolynomial d gamma).Splits)
    (hne : diagonalOperator weight (reflect d (jensenPolynomial d gamma)) ≠ 0) :
    IsSimpleRealRooted (hermiteCompanion d gamma weight) := by
  rw [hermiteCompanion_eq_basisTransform]
  apply isSimpleRealRooted_hermiteBasisTransform _ hne
  have hdeg : (reflect d (jensenPolynomial d gamma)).natDegree ≤ d :=
    natDegree_reflect_le.trans (max_eq_left (natDegree_jensenPolynomial_le d gamma)).le
  exact (hweight hdeg (hp.reflect (natDegree_jensenPolynomial_le d gamma))).resolve_left hne

/-- Weights nonzero through the relevant degree cannot annihilate a nonzero input. -/
theorem isSimpleRealRooted_hermiteCompanion_of_nonzero
    {d : ℕ} {gamma weight : ℕ → ℝ} (hweight : IsFiniteMultiplierSequence d weight)
    (hp : (jensenPolynomial d gamma).Splits) (hp0 : jensenPolynomial d gamma ≠ 0)
    (hw0 : ∀ k ≤ d, weight k ≠ 0) :
    IsSimpleRealRooted (hermiteCompanion d gamma weight) := by
  apply isSimpleRealRooted_hermiteCompanion hweight hp
  intro hz
  apply hp0
  apply (reflect_eq_zero_iff (N := d)).mp
  ext k
  by_cases hk : k ≤ d
  · have h := congrArg (fun p : ℝ[X] => p.coeff k) hz
    simpa only [coeff_diagonalOperator, coeff_zero, mul_eq_zero,
      hw0 k hk, false_or] using h
  · have hdeg : (reflect d (jensenPolynomial d gamma)).natDegree ≤ d :=
      natDegree_reflect_le.trans (max_eq_left (natDegree_jensenPolynomial_le d gamma)).le
    rw [coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (lt_of_not_ge hk)), coeff_zero]

/-- Nonzero top weight and initial coefficient suffice for simple real roots;
other entries of the finite multiplier sequence may vanish. -/
theorem isSimpleRealRooted_hermiteCompanion_of_coeff_zero
    {d : ℕ} {gamma weight : ℕ → ℝ} (hweight : IsFiniteMultiplierSequence d weight)
    (hp : (jensenPolynomial d gamma).Splits) (hgamma : gamma 0 ≠ 0)
    (hw : weight d ≠ 0) : IsSimpleRealRooted (hermiteCompanion d gamma weight) := by
  apply isSimpleRealRooted_hermiteCompanion hweight hp
  intro hz
  have h := congrArg (fun p : ℝ[X] => p.coeff d) hz
  simp only [coeff_diagonalOperator, coeff_reflect, revAt_le le_rfl, Nat.sub_self,
    coeff_jensenPolynomial, Nat.zero_le, ite_true, Nat.choose_zero_right,
    Nat.cast_one, one_mul, coeff_zero] at h
  exact mul_ne_zero hw hgamma h

/-- Nonvanishing of the leading weighted coefficient makes the degree exact. -/
theorem natDegree_hermiteCompanion {d : ℕ} {gamma weight : ℕ → ℝ}
    (hgamma : gamma 0 ≠ 0) (hweight : weight d ≠ 0) :
    (hermiteCompanion d gamma weight).natDegree = d :=
  natDegree_hermiteJensenPolynomial (by simpa using mul_ne_zero hgamma hweight)

/-- The leading coefficient of a degree-exact weighted companion. -/
theorem leadingCoeff_hermiteCompanion {d : ℕ} {gamma weight : ℕ → ℝ}
    (hgamma : gamma 0 ≠ 0) (hweight : weight d ≠ 0) :
    (hermiteCompanion d gamma weight).leadingCoeff = gamma 0 * weight d * 2 ^ d := by
  simpa [hermiteCompanion] using leadingCoeff_hermiteJensenPolynomial (d := d)
    (gamma := fun k => gamma k * weight (d - k)) (by simpa using mul_ne_zero hgamma hweight)

/-- The factorial companion is exactly the finite sum with denominator `(d-k)!`. -/
theorem hermiteFactorialPolynomial_eq_sum (d : ℕ) (gamma : ℕ → ℝ) :
    hermiteFactorialPolynomial d gamma =
      ∑ k ∈ Finset.range (d + 1),
        C ((d.choose k : ℝ) * gamma k / (d - k).factorial) * hermitePhysicists (d - k) := by
  simp only [hermiteFactorialPolynomial, hermiteCompanion, hermiteJensenPolynomial,
    div_eq_mul_inv, mul_assoc]

/-- Parameter one recovers the reciprocal-factorial companion. -/
@[simp] theorem hermitePochhammerPolynomial_one (d : ℕ) (gamma : ℕ → ℝ) :
    hermitePochhammerPolynomial d gamma 1 = hermiteFactorialPolynomial d gamma := by
  simp [hermitePochhammerPolynomial, hermiteFactorialPolynomial, ascPochhammer_eval_one]

/-- The reciprocal-factorial companion preserves splitting at a fixed degree. -/
theorem hermiteFactorialPolynomial_splits {d : ℕ} {gamma : ℕ → ℝ}
    (hp : (jensenPolynomial d gamma).Splits) :
    (hermiteFactorialPolynomial d gamma).Splits :=
  hermiteCompanion_splits (isMultiplierSequence_inv_factorial.finite d) hp

/-- A nonzero split Jensen input gives a factorial companion with simple real roots. -/
theorem isSimpleRealRooted_hermiteFactorialPolynomial {d : ℕ} {gamma : ℕ → ℝ}
    (hp : (jensenPolynomial d gamma).Splits) (hp0 : jensenPolynomial d gamma ≠ 0) :
    IsSimpleRealRooted (hermiteFactorialPolynomial d gamma) :=
  isSimpleRealRooted_hermiteCompanion_of_nonzero
    (isMultiplierSequence_inv_factorial.finite d) hp hp0 (fun k _ => by positivity)

/-- Positive rising-factorial parameters give a finite splitting-preserving companion. -/
theorem hermitePochhammerPolynomial_splits {d : ℕ} {gamma : ℕ → ℝ} {a : ℝ}
    (ha : 0 < a) (hp : (jensenPolynomial d gamma).Splits) :
    (hermitePochhammerPolynomial d gamma a).Splits :=
  hermiteCompanion_splits
    ((isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp
      (isPFMultiplierSequence_inv_ascPochhammer ha)).1.finite d) hp

/-- Positive rising-factorial parameters give simple roots for every nonzero split input. -/
theorem isSimpleRealRooted_hermitePochhammerPolynomial {d : ℕ} {gamma : ℕ → ℝ} {a : ℝ}
    (ha : 0 < a) (hp : (jensenPolynomial d gamma).Splits)
    (hp0 : jensenPolynomial d gamma ≠ 0) :
    IsSimpleRealRooted (hermitePochhammerPolynomial d gamma a) :=
  isSimpleRealRooted_hermiteCompanion_of_nonzero
    ((isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp
      (isPFMultiplierSequence_inv_ascPochhammer ha)).1.finite d) hp hp0
    (fun k _ => inv_ne_zero (ascPochhammer_pos k a ha).ne')

end RealRooted
