module

public import RealRooted.BasisTransform.PolynomialSemigroups

/-!
# Classification of monic ray semigroups

This file supplies the semigroup law for the algebraic ray maps and begins the
finite nilpotent logarithm API used to recognize embeddings into those maps.
-/

public section

open Finset Polynomial

noncomputable section

namespace RealRooted

private theorem raySemigroupTransform_basis_add (a b s t : ℝ) (n : ℕ) :
    raySemigroupTransform a b s (raySemigroupBasis a b t n) =
      raySemigroupBasis a b (s + t) n := by
  induction n with
  | zero =>
      change raySemigroupTransform a b s 1 = 1
      rw [show (1 : ℝ[X]) = X ^ 0 by simp, raySemigroupTransform_X_pow]
      rfl
  | succ n ih =>
      rw [raySemigroupBasis_succ, raySemigroupTransform_add]
      rw [show (X + C (t * (a + b * n))) * raySemigroupBasis a b t n =
          X * raySemigroupBasis a b t n +
            (t * (a + b * n)) • raySemigroupBasis a b t n by
        rw [Polynomial.smul_eq_C_mul]
        simp only [map_mul, map_add, map_natCast]
        ring]
      rw [raySemigroupTransform_add, raySemigroupTransform_smul,
        raySemigroupTransform_X_mul, ih]
      rw [show C (b * t) * X * (raySemigroupBasis a b t n).derivative =
          (b * t) • (X * (raySemigroupBasis a b t n).derivative) by
        rw [Polynomial.smul_eq_C_mul]
        ring]
      rw [raySemigroupTransform_smul, raySemigroupTransform_X_mul_derivative, ih]
      rw [raySemigroupBasis_succ]
      have heuler := raySemigroupBasis_differential a b (s + t) n
      simp only [map_mul, map_add, map_natCast] at heuler ⊢
      linear_combination -(C b * C s) * heuler

/-- The algebraic ray transforms form an additive one-parameter semigroup. -/
theorem raySemigroupTransform_add_time (a b s t : ℝ) (p : ℝ[X]) :
    raySemigroupTransform a b (s + t) p =
      raySemigroupTransform a b s (raySemigroupTransform a b t p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [raySemigroupTransform_add, raySemigroupTransform_add,
        raySemigroupTransform_add, hp, hq]
  | monomial n c =>
      rw [raySemigroupTransform, Polynomial.basisTransform_monomial]
      rw [show raySemigroupTransform a b t (monomial n c) =
          C c * raySemigroupBasis a b t n by
        rw [raySemigroupTransform, Polynomial.basisTransform_monomial]]
      rw [show C c * raySemigroupBasis a b t n = c • raySemigroupBasis a b t n by
        rw [Polynomial.smul_eq_C_mul], raySemigroupTransform_smul]
      rw [raySemigroupTransform_basis_add]

/-- Time zero is the identity ray transform. -/
@[simp] theorem raySemigroupTransform_time_zero (a b : ℝ) (p : ℝ[X]) :
    raySemigroupTransform a b 0 p = p := by
  have hbasis : ∀ n, raySemigroupBasis a b 0 n = X ^ n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [raySemigroupBasis_succ, ih]
        simp [pow_succ']
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [raySemigroupTransform_add, hp, hq]
  | monomial n c =>
      rw [raySemigroupTransform, Polynomial.basisTransform_monomial]
      rw [hbasis, Polynomial.C_mul_X_pow_eq_monomial]

private theorem raySemigroupBasis_one (a b t : ℝ) :
    raySemigroupBasis a b t 1 = X + C (t * a) := by
  rw [show 1 = 0 + 1 by rfl, raySemigroupBasis_succ]
  simp

private theorem raySemigroupBasis_two (a b t : ℝ) :
    raySemigroupBasis a b t 2 =
      X ^ 2 + C (2 * t * (a + b)) * X + C (t ^ 2 * a * (a + b)) := by
  rw [show 2 = 1 + 1 by rfl, raySemigroupBasis_succ, raySemigroupBasis_one]
  simp only [Nat.cast_one, mul_one, derivative_add, derivative_X, derivative_C,
    add_zero]
  simp only [map_mul, map_add, map_ofNat]
  rw [map_pow]
  ring

private theorem raySemigroupTransform_shifted_square (a b t r : ℝ) :
    raySemigroupTransform a b t ((X + C r) ^ 2) =
      X ^ 2 + C (2 * (r + t * (a + b))) * X +
        C (r ^ 2 + 2 * r * t * a + t ^ 2 * a * (a + b)) := by
  rw [show (X + C r) ^ 2 = X ^ 2 + (2 * r) • X + (r ^ 2) • 1 by
    simp only [Polynomial.smul_eq_C_mul, map_mul, map_ofNat, map_pow]
    ring]
  rw [raySemigroupTransform_add, raySemigroupTransform_add,
    raySemigroupTransform_smul, raySemigroupTransform_smul]
  rw [raySemigroupTransform_X_pow, raySemigroupBasis_two]
  rw [show (1 : ℝ[X]) = X ^ 0 by simp, raySemigroupTransform_X_pow,
    raySemigroupBasis_zero]
  have hX : raySemigroupTransform a b t X = X + C (t * a) := by
    rw [show (X : ℝ[X]) = X ^ 1 by simp, raySemigroupTransform_X_pow,
      raySemigroupBasis_one]
    simp
  rw [hX]
  simp only [map_mul, map_add, map_ofNat, map_pow]
  ring

/-- The algebraic ray semigroup preserves every PF polynomial at every
nonnegative time exactly when both generator parameters are nonnegative. -/
theorem _root_.RealRooted.RaySemigroup.forall_isPFPolynomial_iff (a b : ℝ) :
    (∀ t, 0 ≤ t → ∀ {p : ℝ[X]}, IsPFPolynomial p →
      IsPFPolynomial (raySemigroupTransform a b t p)) ↔
      0 ≤ a ∧ 0 ≤ b := by
  constructor
  · intro hpres
    have hlinear := hpres 1 zero_le_one isPFPolynomial_X
    have ha : 0 ≤ a := by
      have hcoeff := hlinear.hasNonnegCoeffs 0
      rw [show (X : ℝ[X]) = X ^ 1 by simp, raySemigroupTransform_X_pow,
        raySemigroupBasis_one] at hcoeff
      simpa using hcoeff
    refine ⟨ha, ?_⟩
    by_contra hb
    have hbneg : b < 0 := lt_of_not_ge hb
    let r := |a + b| + 1
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hfactor : 0 < 2 * r + (a + b) := by
      dsimp [r]
      have habs : -(a + b) ≤ |a + b| := neg_le_abs (a + b)
      linarith
    have hin : IsPFPolynomial ((X + C r) ^ 2) :=
      (isPFPolynomial_X_add_C hr).pow 2
    have hout := hpres 1 zero_le_one hin
    have hformula := raySemigroupTransform_shifted_square a b 1 r
    simp only [one_mul, one_pow] at hformula
    rw [hformula] at hout
    have hdisc :
        discrim (1 : ℝ) (2 * (r + (a + b)))
          (r ^ 2 + 2 * r * a + a * (a + b)) < 0 := by
      rw [show discrim (1 : ℝ) (2 * (r + (a + b)))
          (r ^ 2 + 2 * r * a + a * (a + b)) =
          4 * b * (2 * r + (a + b)) by simp [discrim]; ring]
      exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hbneg) hfactor
    have hne :
        X ^ 2 + C (2 * (r + (a + b))) * X +
            C (r ^ 2 + 2 * r * 1 * a + a * (a + b)) ≠ 0 := by
      intro hzero
      have htop :
          (X ^ 2 + C (2 * (r + (a + b))) * X +
            C (r ^ 2 + 2 * r * 1 * a + a * (a + b))).coeff 2 = 1 := by
        simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow,
          Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
        norm_num
      have hcoeff := congrArg (fun p : ℝ[X] ↦ p.coeff 2) hzero
      rw [htop] at hcoeff
      simp at hcoeff
    apply quadraticPoly_not_splits_of_discrim_neg one_ne_zero hdisc
    simpa using (hout.ne_zero_and_splits hne).2
  · rintro ⟨ha, hb⟩ t ht p hp
    exact raySemigroupTransform_isPFPolynomial ha hb ht hp

/-! ## Finite logarithms and powers -/

/-- The degree-`N` nilpotent logarithm of an endomorphism. -/
def finiteEndomorphismLog (N : ℕ) (T : Module.End ℝ ℝ[X]) : Module.End ℝ ℝ[X] :=
  ∑ j ∈ Icc 1 N, ((-1 : ℝ) ^ (j + 1) / (j : ℝ)) • (T - 1) ^ j

/-- The degree-`N` truncated exponential of an endomorphism. -/
def finiteEndomorphismExp (N : ℕ) (t : ℝ)
    (L : Module.End ℝ ℝ[X]) : Module.End ℝ ℝ[X] :=
  ∑ j ∈ range (N + 1), (t ^ j / (j.factorial : ℝ)) • L ^ j

/-- The finite real power obtained by exponentiating the nilpotent logarithm. -/
def finiteEndomorphismPower (N : ℕ) (t : ℝ)
    (T : Module.End ℝ ℝ[X]) : Module.End ℝ ℝ[X] :=
  finiteEndomorphismExp N t (finiteEndomorphismLog N T)

/-- Evaluation formula for the finite logarithm. -/
theorem finiteEndomorphismLog_apply (N : ℕ) (T : Module.End ℝ ℝ[X])
    (p : ℝ[X]) :
    finiteEndomorphismLog N T p =
      ∑ j ∈ Icc 1 N,
        C ((-1 : ℝ) ^ (j + 1) / (j : ℝ)) * ((T - 1) ^ j) p := by
  simp [finiteEndomorphismLog, Polynomial.smul_eq_C_mul]

/-- Evaluation formula for the finite exponential. -/
theorem finiteEndomorphismExp_apply (N : ℕ) (t : ℝ)
    (L : Module.End ℝ ℝ[X]) (p : ℝ[X]) :
    finiteEndomorphismExp N t L p =
      ∑ j ∈ range (N + 1), C (t ^ j / (j.factorial : ℝ)) * (L ^ j) p := by
  simp [finiteEndomorphismExp, Polynomial.smul_eq_C_mul]

/-- Evaluation formula for the finite real power. -/
theorem finiteEndomorphismPower_apply (N : ℕ) (t : ℝ)
    (T : Module.End ℝ ℝ[X]) (p : ℝ[X]) :
    finiteEndomorphismPower N t T p =
      ∑ j ∈ range (N + 1),
        C (t ^ j / (j.factorial : ℝ)) * ((finiteEndomorphismLog N T) ^ j) p := by
  exact finiteEndomorphismExp_apply N t (finiteEndomorphismLog N T) p

/-- The degree-two finite logarithm is `U - U²/2`, where `U = T - I`. -/
theorem finiteEndomorphismLog_two_apply (T : Module.End ℝ ℝ[X]) (p : ℝ[X]) :
    finiteEndomorphismLog 2 T p =
      (T - 1) p - C (1 / 2 : ℝ) *
        (((T - 1) ^ 2 : Module.End ℝ ℝ[X]) p) := by
  rw [finiteEndomorphismLog_apply]
  norm_num [Finset.sum_Icc_succ_top]
  ring

/-- The degree-two finite exponential is `I + tL + t²L²/2`. -/
theorem finiteEndomorphismExp_two_apply (t : ℝ) (L : Module.End ℝ ℝ[X])
    (p : ℝ[X]) :
    finiteEndomorphismExp 2 t L p =
      p + C t * L p + C (t ^ 2 / 2) * ((L ^ 2 : Module.End ℝ ℝ[X]) p) := by
  rw [finiteEndomorphismExp_apply]
  norm_num [Finset.sum_range_succ]

/-- The ray transform bundled as a polynomial endomorphism. -/
def raySemigroupEnd (a b t : ℝ) : Module.End ℝ ℝ[X] :=
  Polynomial.basisTransformₗ (raySemigroupBasis a b t)

/-- The bundled ray transform evaluates to `raySemigroupTransform`. -/
@[simp] theorem raySemigroupEnd_apply (a b t : ℝ) (p : ℝ[X]) :
    raySemigroupEnd a b t p = raySemigroupTransform a b t p := by
  rw [raySemigroupEnd, Polynomial.basisTransformₗ_apply, raySemigroupTransform]

/-- Bundled form of the additive ray-semigroup law. -/
theorem raySemigroupEnd_add_time (a b s t : ℝ) :
    raySemigroupEnd a b (s + t) = raySemigroupEnd a b s * raySemigroupEnd a b t := by
  apply LinearMap.ext
  intro p
  rw [Module.End.mul_apply]
  simp only [raySemigroupEnd_apply]
  exact raySemigroupTransform_add_time a b s t p

/-- The bundled ray semigroup starts at the identity. -/
@[simp] theorem raySemigroupEnd_time_zero (a b : ℝ) :
    raySemigroupEnd a b 0 = 1 := by
  apply LinearMap.ext
  intro p
  rw [Module.End.one_apply, raySemigroupEnd_apply]
  exact raySemigroupTransform_time_zero a b p

private theorem raySemigroupTransform_X (a b t : ℝ) :
    raySemigroupTransform a b t X = X + C (t * a) := by
  rw [show (X : ℝ[X]) = X ^ 1 by simp, raySemigroupTransform_X_pow,
    raySemigroupBasis_one]
  simp

private theorem raySemigroupTransform_C (a b t c : ℝ) :
    raySemigroupTransform a b t (C c) = C c := by
  rw [raySemigroupTransform, Polynomial.basisTransform_C]
  simp [raySemigroupBasis_zero]

private theorem raySemigroupTransform_X_sq (a b t : ℝ) :
    raySemigroupTransform a b t (X ^ 2) =
      X ^ 2 + C (2 * t * (a + b)) * X + C (t ^ 2 * a * (a + b)) := by
  rw [raySemigroupTransform_X_pow, raySemigroupBasis_two]

private theorem finiteEndomorphismLog_raySemigroupEnd_C (a b c : ℝ) :
    finiteEndomorphismLog 2 (raySemigroupEnd a b 1) (C c) = 0 := by
  let U := raySemigroupEnd a b 1 - 1
  have hU : U (C c) = 0 := by
    simp only [U, LinearMap.sub_apply, Module.End.one_apply, raySemigroupEnd_apply]
    rw [raySemigroupTransform_C]
    simp
  rw [finiteEndomorphismLog_two_apply]
  change U (C c) - C (1 / 2 : ℝ) * ((U ^ 2 : Module.End ℝ ℝ[X]) (C c)) = 0
  rw [pow_two, Module.End.mul_apply, hU, map_zero]
  simp

/-- On the two-dimensional truncation, the finite logarithm recovers the
constant derivative parameter from the image of `X`. -/
theorem finiteEndomorphismLog_raySemigroupEnd_X (a b : ℝ) :
    finiteEndomorphismLog 2 (raySemigroupEnd a b 1) X = C a := by
  let U := raySemigroupEnd a b 1 - 1
  have hU : U X = C a := by
    simp only [U, LinearMap.sub_apply, Module.End.one_apply, raySemigroupEnd_apply]
    rw [raySemigroupTransform_X]
    simp
  have hUtwo : (U ^ 2 : Module.End ℝ ℝ[X]) X = 0 := by
    rw [pow_two, Module.End.mul_apply, hU]
    simp only [U, LinearMap.sub_apply, Module.End.one_apply, raySemigroupEnd_apply]
    rw [raySemigroupTransform_C]
    simp
  rw [finiteEndomorphismLog_two_apply]
  change U X - C (1 / 2 : ℝ) * ((U ^ 2 : Module.End ℝ ℝ[X]) X) = C a
  rw [hU, hUtwo]
  simp

/-- On the two-dimensional truncation, the finite logarithm recovers the
`X D²` parameter from the image of `X²`. -/
theorem finiteEndomorphismLog_raySemigroupEnd_X_sq (a b : ℝ) :
    finiteEndomorphismLog 2 (raySemigroupEnd a b 1) (X ^ 2) =
      C (2 * (a + b)) * X := by
  let U := raySemigroupEnd a b 1 - 1
  have hU : U (X ^ 2) = C (2 * (a + b)) * X + C (a * (a + b)) := by
    simp only [U, LinearMap.sub_apply, Module.End.one_apply, raySemigroupEnd_apply]
    rw [raySemigroupTransform_X_sq]
    simp only [one_mul, one_pow, map_mul, map_add, map_ofNat, map_one]
    ring
  have hUtwo :
      (U ^ 2 : Module.End ℝ ℝ[X]) (X ^ 2) = C (2 * a * (a + b)) := by
    rw [pow_two, Module.End.mul_apply, hU]
    simp only [U, LinearMap.sub_apply, Module.End.one_apply, raySemigroupEnd_apply]
    rw [show C (2 * (a + b)) * X = (2 * (a + b)) • X by
      rw [Polynomial.smul_eq_C_mul]]
    rw [show C (a * (a + b)) = (a * (a + b)) • (1 : ℝ[X]) by
      rw [Polynomial.smul_eq_C_mul]
      simp]
    rw [raySemigroupTransform_add, raySemigroupTransform_smul,
      raySemigroupTransform_smul, raySemigroupTransform_X]
    rw [show (1 : ℝ[X]) = X ^ 0 by simp, raySemigroupTransform_X_pow]
    simp only [raySemigroupBasis_zero, one_mul, map_mul, map_add, map_ofNat,
      Polynomial.smul_eq_C_mul]
    ring
  rw [finiteEndomorphismLog_two_apply]
  change U (X ^ 2) - C (1 / 2 : ℝ) *
      ((U ^ 2 : Module.End ℝ ℝ[X]) (X ^ 2)) = C (2 * (a + b)) * X
  rw [hU, hUtwo]
  have hconst :
      C (1 / 2 : ℝ) * C (2 * a * (a + b)) = C (a * (a + b)) := by
    rw [← map_mul]
    congr 1
    ring
  rw [hconst]
  ring

/-- The finite power of the time-one ray map fixes constants, as does every
ray-semigroup time. -/
theorem finiteEndomorphismPower_raySemigroupEnd_C (a b t c : ℝ) :
    finiteEndomorphismPower 2 t (raySemigroupEnd a b 1) (C c) =
      raySemigroupTransform a b t (C c) := by
  let L := finiteEndomorphismLog 2 (raySemigroupEnd a b 1)
  have hL : L (C c) = 0 := finiteEndomorphismLog_raySemigroupEnd_C a b c
  have hLtwo : (L ^ 2 : Module.End ℝ ℝ[X]) (C c) = 0 := by
    rw [pow_two, Module.End.mul_apply, hL, map_zero]
  rw [finiteEndomorphismPower, finiteEndomorphismExp_two_apply]
  change C c + C t * L (C c) + C (t ^ 2 / 2) *
      ((L ^ 2 : Module.End ℝ ℝ[X]) (C c)) = _
  rw [hL, hLtwo, raySemigroupTransform_C]
  simp

/-- The finite power of the time-one ray map agrees with the ray semigroup on
the linear monomial. -/
theorem finiteEndomorphismPower_raySemigroupEnd_X (a b t : ℝ) :
    finiteEndomorphismPower 2 t (raySemigroupEnd a b 1) X =
      raySemigroupTransform a b t X := by
  let L := finiteEndomorphismLog 2 (raySemigroupEnd a b 1)
  have hL : L X = C a := finiteEndomorphismLog_raySemigroupEnd_X a b
  have hLtwo : (L ^ 2 : Module.End ℝ ℝ[X]) X = 0 := by
    rw [pow_two, Module.End.mul_apply, hL]
    exact finiteEndomorphismLog_raySemigroupEnd_C a b a
  rw [finiteEndomorphismPower, finiteEndomorphismExp_two_apply]
  change X + C t * L X + C (t ^ 2 / 2) * ((L ^ 2 : Module.End ℝ ℝ[X]) X) = _
  rw [hL, hLtwo, raySemigroupTransform_X]
  simp only [mul_zero, add_zero, ← map_mul]

/-- The finite power of the time-one ray map agrees with the ray semigroup on
the quadratic monomial. -/
theorem finiteEndomorphismPower_raySemigroupEnd_X_sq (a b t : ℝ) :
    finiteEndomorphismPower 2 t (raySemigroupEnd a b 1) (X ^ 2) =
      raySemigroupTransform a b t (X ^ 2) := by
  let L := finiteEndomorphismLog 2 (raySemigroupEnd a b 1)
  have hLX : L X = C a := finiteEndomorphismLog_raySemigroupEnd_X a b
  have hL : L (X ^ 2) = C (2 * (a + b)) * X :=
    finiteEndomorphismLog_raySemigroupEnd_X_sq a b
  have hLtwo :
      (L ^ 2 : Module.End ℝ ℝ[X]) (X ^ 2) = C (2 * a * (a + b)) := by
    rw [pow_two, Module.End.mul_apply, hL]
    rw [show C (2 * (a + b)) * X = (2 * (a + b)) • X by
      rw [Polynomial.smul_eq_C_mul], LinearMap.map_smul, hLX]
    simp only [Polynomial.smul_eq_C_mul, ← map_mul]
    congr 1
    ring
  rw [finiteEndomorphismPower, finiteEndomorphismExp_two_apply]
  change X ^ 2 + C t * L (X ^ 2) + C (t ^ 2 / 2) *
      ((L ^ 2 : Module.End ℝ ℝ[X]) (X ^ 2)) = _
  rw [hL, hLtwo, raySemigroupTransform_X_sq]
  have hconst : C (t ^ 2 / 2) * C (2 * a * (a + b)) =
      C (t ^ 2 * a * (a + b)) := by
    rw [← map_mul]
    congr 1
    ring
  rw [hconst]
  have hx : C t * C (2 * (a + b)) = C (2 * t * (a + b)) := by
    rw [← map_mul]
    congr 1
    ring
  rw [← mul_assoc, hx]

/-- The two coefficients prescribed in the finite logarithm criterion recover
the two ray-generator parameters. -/
theorem finiteEndomorphismLog_raySemigroupEnd_parameters (a b : ℝ) :
    (finiteEndomorphismLog 2 (raySemigroupEnd a b 1) X).coeff 0 = a ∧
      (finiteEndomorphismLog 2 (raySemigroupEnd a b 1) (X ^ 2)).coeff 1 / 2 -
          (finiteEndomorphismLog 2 (raySemigroupEnd a b 1) X).coeff 0 = b := by
  rw [finiteEndomorphismLog_raySemigroupEnd_X,
    finiteEndomorphismLog_raySemigroupEnd_X_sq]
  constructor
  · simp
  · simp

/-- Logarithmic recognition of the PF-preserving members of the algebraic ray
semigroup family.  The degree-two finite logarithm already detects both
generator parameters. -/
theorem _root_.RealRooted.RaySemigroup.forall_isPFPolynomial_iff_finiteLog (a b : ℝ) :
    (∀ t, 0 ≤ t → ∀ {p : ℝ[X]}, IsPFPolynomial p →
      IsPFPolynomial (raySemigroupTransform a b t p)) ↔
      0 ≤ (finiteEndomorphismLog 2 (raySemigroupEnd a b 1) X).coeff 0 ∧
        0 ≤ (finiteEndomorphismLog 2
            (raySemigroupEnd a b 1) (X ^ 2)).coeff 1 / 2 -
          (finiteEndomorphismLog 2 (raySemigroupEnd a b 1) X).coeff 0 := by
  rw [RealRooted.RaySemigroup.forall_isPFPolynomial_iff,
    finiteEndomorphismLog_raySemigroupEnd_X,
    finiteEndomorphismLog_raySemigroupEnd_X_sq]
  simp only [coeff_C_zero, coeff_C_mul, coeff_X, ite_true]
  constructor <;> rintro ⟨ha, hb⟩ <;> refine ⟨ha, ?_⟩ <;> linarith

end RealRooted
