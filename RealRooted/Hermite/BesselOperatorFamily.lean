module

import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization.CoefficientExtraction
public import RealRooted.HermiteBiehler.Basic
import RealRooted.QuadraticRoot

/-!
# The finite Bessel operator family

This file defines the finite differential operators with coefficients
`(-lambda)^k / (k! (k+r)!)`, proves their exact degree and coefficient behavior,
and gives the finite proof of their real-rootedness-preserving characterization.
-/

public section

open Finset Polynomial

namespace RealRooted

noncomputable section

/-- The finite differential operator
`sum_k (-lambda)^k D^(2*k+r) / (k! (k+r)!)` on real polynomials. -/
def besselOperator (lambda : ℝ) (r : ℕ) (f : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (f.natDegree + 1),
    C ((-lambda) ^ k /
      ((k.factorial : ℝ) * ((k + r).factorial : ℝ))) *
        derivative^[2 * k + r] f

/-- The coefficient of the finite Bessel operator at a specified degree. -/
theorem coeff_besselOperator (lambda : ℝ) (r : ℕ) (f : ℝ[X]) (q : ℕ) :
    (besselOperator lambda r f).coeff q =
      ∑ k ∈ range (f.natDegree + 1),
        ((-lambda) ^ k /
          ((k.factorial : ℝ) * ((k + r).factorial : ℝ))) *
            ((q + (2 * k + r)).descFactorial (2 * k + r) : ℝ) *
              f.coeff (q + (2 * k + r)) := by
  simp [besselOperator, Polynomial.coeff_iterate_derivative, nsmul_eq_mul,
    mul_assoc]

/-- Applying a finite Bessel operator to the zero polynomial gives zero. -/
@[simp] theorem besselOperator_zero (lambda : ℝ) (r : ℕ) :
    besselOperator lambda r 0 = 0 := by
  simp [besselOperator]

/-- The `r`th finite Bessel operator lowers natural degree by at least `r`. -/
theorem natDegree_besselOperator_le (lambda : ℝ) (r : ℕ) (f : ℝ[X]) :
    (besselOperator lambda r f).natDegree ≤ f.natDegree - r := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro q hq
  rw [coeff_besselOperator]
  apply sum_eq_zero
  intro k hk
  rw [f.coeff_eq_zero_of_natDegree_lt (by lia), mul_zero]

/-- The coefficient in the highest possible output degree is the expected
binomial multiple of the input leading coefficient. -/
theorem coeff_besselOperator_natDegree_sub (lambda : ℝ) (r : ℕ) (f : ℝ[X])
    (hr : r ≤ f.natDegree) :
    (besselOperator lambda r f).coeff (f.natDegree - r) =
      (f.natDegree.choose r : ℝ) * f.leadingCoeff := by
  rw [coeff_besselOperator]
  rw [sum_eq_single 0]
  · norm_num [Nat.sub_add_cancel hr, Nat.descFactorial_eq_factorial_mul_choose,
      coeff_natDegree]
    have hfac : (r.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    simp
  · intro k hk hk0
    rw [f.coeff_eq_zero_of_natDegree_lt (by lia), mul_zero]
  · simp

/-- A nonzero polynomial of degree at least `r` loses exactly `r` degrees under
the `r`th finite Bessel operator. -/
theorem natDegree_besselOperator (lambda : ℝ) (r : ℕ) (f : ℝ[X])
    (hf : f ≠ 0) (hr : r ≤ f.natDegree) :
    (besselOperator lambda r f).natDegree = f.natDegree - r := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_besselOperator_le lambda r f)
  rw [coeff_besselOperator_natDegree_sub lambda r f hr]
  exact mul_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.choose_ne_zero_iff.mpr hr))
    (leadingCoeff_ne_zero.mpr hf)

/-- The leading coefficient of a nonzero finite Bessel output is the binomial
multiple `choose (degree f) r` of the input leading coefficient. -/
theorem leadingCoeff_besselOperator (lambda : ℝ) (r : ℕ) (f : ℝ[X])
    (hf : f ≠ 0) (hr : r ≤ f.natDegree) :
    (besselOperator lambda r f).leadingCoeff =
      (f.natDegree.choose r : ℝ) * f.leadingCoeff := by
  rw [leadingCoeff, natDegree_besselOperator lambda r f hf hr,
    coeff_besselOperator_natDegree_sub lambda r f hr]

/-- The `r`th finite Bessel operator vanishes when `r` exceeds the input
degree. -/
theorem besselOperator_eq_zero_of_natDegree_lt (lambda : ℝ) (r : ℕ)
    (f : ℝ[X]) (hr : f.natDegree < r) : besselOperator lambda r f = 0 := by
  simp only [besselOperator]
  apply sum_eq_zero
  intro k hk
  rw [iterate_derivative_eq_zero (by lia), mul_zero]

/-- A nonzero input of degree at least `r` has nonzero finite Bessel output. -/
theorem besselOperator_ne_zero (lambda : ℝ) (r : ℕ) (f : ℝ[X])
    (hf : f ≠ 0) (hr : r ≤ f.natDegree) :
    besselOperator lambda r f ≠ 0 := by
  apply leadingCoeff_ne_zero.mp
  rw [leadingCoeff_besselOperator lambda r f hf hr]
  exact mul_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.choose_ne_zero_iff.mpr hr))
    (leadingCoeff_ne_zero.mpr hf)

/-- For a nonzero input, the finite Bessel output vanishes exactly when `r`
exceeds the input degree. -/
theorem besselOperator_eq_zero_iff_natDegree_lt (lambda : ℝ) (r : ℕ)
    (f : ℝ[X]) (hf : f ≠ 0) :
    besselOperator lambda r f = 0 ↔ f.natDegree < r := by
  constructor
  · intro hzero
    by_contra hnot
    exact besselOperator_ne_zero lambda r f hf (by lia) hzero
  · exact besselOperator_eq_zero_of_natDegree_lt lambda r f

/-- The denominator-cleared auxiliary polynomial
`sum_m f_m t^(N-m) (x*t+t^2-lambda)^m`, with `t` indexed by `none` and `x`
indexed by `some ()`. -/
def besselAuxiliary (N : ℕ) (lambda : ℝ) (f : ℝ[X]) :
    MvPolynomial (Option Unit) ℂ :=
  ∑ m ∈ range (N + 1),
    MvPolynomial.C (f.coeff m : ℂ) * MvPolynomial.X none ^ (N - m) *
      (MvPolynomial.X (some ()) * MvPolynomial.X none +
        MvPolynomial.X none ^ 2 - MvPolynomial.C (lambda : ℂ)) ^ m

/-- Evaluation of the finite Bessel auxiliary polynomial in its defining
coefficient form. -/
theorem eval_besselAuxiliary (N : ℕ) (lambda : ℝ) (f : ℝ[X])
    (z : Option Unit → ℂ) :
    MvPolynomial.eval z (besselAuxiliary N lambda f) =
      ∑ m ∈ range (N + 1),
        (f.coeff m : ℂ) * z none ^ (N - m) *
          (z (some ()) * z none + z none ^ 2 - lambda) ^ m := by
  simp [besselAuxiliary]

/-- Away from `t = 0`, the auxiliary polynomial equals
`t^N f(x+t-lambda/t)`. -/
theorem eval_besselAuxiliary_eq_pow_mul (N : ℕ) (lambda : ℝ) (f : ℝ[X])
    (hN : f.natDegree ≤ N) (z : Option Unit → ℂ) (hz : z none ≠ 0) :
    MvPolynomial.eval z (besselAuxiliary N lambda f) =
      z none ^ N *
        (complexify f).eval
          (z (some ()) + z none - (lambda : ℂ) / z none) := by
  rw [eval_besselAuxiliary, Polynomial.eval_eq_sum_range' (n := N + 1)]
  · rw [Finset.mul_sum]
    apply sum_congr rfl
    intro m hm
    rw [complexify, Polynomial.coeff_map]
    have hmN : m ≤ N := by simp at hm; lia
    have hfactor :
        z (some ()) * z none + z none ^ 2 - (lambda : ℂ) =
          z none * (z (some ()) + z none - (lambda : ℂ) / z none) := by
      field_simp
    rw [hfactor, mul_pow]
    calc
      _ = (f.coeff m : ℂ) * (z none ^ (N - m) * z none ^ m) *
          (z (some ()) + z none - (lambda : ℂ) / z none) ^ m := by ring
      _ = _ := by
        rw [← pow_add, Nat.sub_add_cancel hmN]
        simp only [Complex.ofRealHom_eq_coe]
        ring
  · rw [complexify,
      Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective]
    lia

/-- For nonnegative parameter, the denominator-cleared auxiliary of a nonzero
split polynomial is upper-half-plane stable. -/
theorem mvUpperHalfPlaneStable_besselAuxiliary (N : ℕ) {lambda : ℝ}
    {f : ℝ[X]} (hlambda : 0 ≤ lambda) (hf : f ≠ 0) (hsplits : f.Splits)
    (hN : f.natDegree ≤ N) :
    MvUpperHalfPlaneStable (besselAuxiliary N lambda f) := by
  intro z hz
  have ht : 0 < (z none).im := hz none
  have ht0 : z none ≠ 0 := fun hzero => by simp [hzero] at ht
  rw [eval_besselAuxiliary_eq_pow_mul N lambda f hN z ht0]
  apply mul_ne_zero (pow_ne_zero N ht0)
  apply eval_complexify_ne_zero_of_splits_of_im_pos hsplits hf
  rw [Complex.sub_im, Complex.add_im, Complex.div_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div]
  have hnorm : 0 < Complex.normSq (z none) := Complex.normSq_pos.mpr ht0
  have hterm :
      0 ≤ lambda * (z none).im / Complex.normSq (z none) :=
    div_nonneg (mul_nonneg hlambda ht.le) hnorm.le
  have hx : 0 < (z (some ())).im := hz (some ())
  linarith

/-- Every distinguished-variable coefficient of a finite Bessel auxiliary is
zero or upper-half-plane stable. -/
theorem besselAuxiliary_coeff_zero_or (N r : ℕ) {lambda : ℝ} {f : ℝ[X]}
    (hlambda : 0 ≤ lambda) (hf : f ≠ 0) (hsplits : f.Splits)
    (hN : f.natDegree ≤ N) :
    MvUpperHalfPlaneStableOrZero
      ((MvPolynomial.optionEquivLeft ℂ Unit
        (besselAuxiliary N lambda f)).coeff (N + r)) :=
  MvUpperHalfPlaneStable.optionEquivLeft_coeff_zero_or_of_finite
    (mvUpperHalfPlaneStable_besselAuxiliary N hlambda hf hsplits hN) (N + r)

private def besselAuxiliaryPolynomial (N : ℕ) (lambda : ℝ) (f : ℝ[X]) :
    Polynomial ℂ[X] :=
  (MvPolynomial.optionEquivLeft ℂ Unit (besselAuxiliary N lambda f)).map
    (MvPolynomial.eval₂Hom C fun _ ↦ X)

private theorem besselAuxiliaryPolynomial_eq (N : ℕ) (lambda : ℝ) (f : ℝ[X]) :
    besselAuxiliaryPolynomial N lambda f =
      ∑ m ∈ range (N + 1),
        C (C (f.coeff m : ℂ)) * X ^ (N - m) *
          (C X * X + X ^ 2 - C (C (lambda : ℂ))) ^ m := by
  rw [besselAuxiliaryPolynomial, besselAuxiliary, map_sum, Polynomial.map_sum]
  simp

private theorem coeff_auxiliary_monomial (N m r : ℕ) (lambda : ℝ)
    (hm : m ≤ N) :
    (X ^ (N - m) *
        (C X * X + X ^ 2 - C (C (lambda : ℂ))) ^ m : Polynomial ℂ[X]).coeff
          (N + r) =
      ∑ k ∈ range (m + 1),
        C (((-lambda : ℂ) ^ k) * (m.choose k : ℂ)) *
          X ^ (m - k - (k + r)) * C ((m - k).choose (k + r) : ℂ) := by
  have hinner :
      (C X * X + X ^ 2 - C (C (lambda : ℂ)) : Polynomial ℂ[X]) =
        C (C (-lambda : ℂ)) + X * (X + C X) := by
    simp only [map_neg]
    ring
  rw [hinner, add_pow, Finset.mul_sum]
  rw [finsetSum_coeff]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by simp at hk; lia
  have hkN : k ≤ N := hkm.trans hm
  have hexp : N - m + (m - k) = N - k := by lia
  have hterm :
      X ^ (N - m) *
          (C (C (-lambda : ℂ)) ^ k * (X * (X + C X)) ^ (m - k) *
            (m.choose k : Polynomial ℂ[X])) =
        X ^ (N - k) *
          (C (C (-lambda : ℂ) ^ k) * (X + C X) ^ (m - k) *
            (m.choose k : Polynomial ℂ[X])) := by
    rw [mul_pow, ← C_pow]
    calc
      _ = C (C (-lambda : ℂ) ^ k) *
          (X ^ (N - m) * X ^ (m - k)) * (X + C X) ^ (m - k) *
            (m.choose k : Polynomial ℂ[X]) := by ring
      _ = _ := by rw [← pow_add, hexp]; ring
  rw [hterm, coeff_X_pow_mul']
  simp only [show N - k ≤ N + r by lia, ite_true]
  rw [show N + r - (N - k) = k + r by lia]
  rw [coeff_mul_natCast, coeff_C_mul, coeff_X_add_C_pow]
  rw [← C_pow]
  have hpow : (-lambda : ℂ) ^ k = ((-lambda) ^ k : ℝ) := by norm_cast
  rw [hpow]
  rw [map_mul]
  simp only [C_eq_natCast]
  ring

private theorem cast_choose_mul_choose (m k r : ℕ) :
    (m.choose k : ℂ) * ((m - k).choose (k + r) : ℂ) =
      (m.descFactorial (2 * k + r) : ℂ) /
        ((k.factorial : ℂ) * ((k + r).factorial : ℂ)) := by
  by_cases h : 2 * k + r ≤ m
  · have hk : k ≤ m := by lia
    have hsub : 2 * k + r - k = k + r := by lia
    have hchoose := Nat.choose_mul (n := m) (k := 2 * k + r) (s := k) (by lia)
    have hfactor := Nat.choose_mul_factorial_mul_factorial
      (n := 2 * k + r) (k := k) (by lia)
    rw [hsub] at hchoose hfactor
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    have hkfac : (k.factorial : ℂ) ≠ 0 := by
      exact_mod_cast k.factorial_ne_zero
    have hkrfac : ((k + r).factorial : ℂ) ≠ 0 := by
      exact_mod_cast (k + r).factorial_ne_zero
    field_simp
    exact_mod_cast (show
      m.choose k * (m - k).choose (k + r) * k.factorial * (k + r).factorial =
        (2 * k + r).factorial * m.choose (2 * k + r) by
      calc
        _ = (m.choose k * (m - k).choose (k + r)) *
            (k.factorial * (k + r).factorial) := by ring
        _ = (m.choose (2 * k + r) * (2 * k + r).choose k) *
            (k.factorial * (k + r).factorial) := by rw [hchoose]
        _ = m.choose (2 * k + r) *
            ((2 * k + r).choose k * k.factorial * (k + r).factorial) := by ring
        _ = _ := by rw [hfactor]; ring)
  · have hlt : m < 2 * k + r := by lia
    have hchoose : m - k < k + r := by lia
    rw [Nat.choose_eq_zero_of_lt hchoose,
      Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
    simp

private def complexBesselOperatorBound (N : ℕ) (lambda : ℝ) (r : ℕ)
    (p : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ range (N + 1),
    C ((-lambda : ℂ) ^ k /
      ((k.factorial : ℂ) * ((k + r).factorial : ℂ))) *
        derivative^[2 * k + r] p

private theorem coeff_auxiliary_monomial_eq_bound (N m r : ℕ) (lambda : ℝ)
    (hm : m ≤ N) :
    (X ^ (N - m) *
        (C X * X + X ^ 2 - C (C (lambda : ℂ))) ^ m : Polynomial ℂ[X]).coeff
          (N + r) =
      complexBesselOperatorBound N lambda r (X ^ m) := by
  rw [coeff_auxiliary_monomial N m r lambda hm]
  unfold complexBesselOperatorBound
  have hsum :
      ∑ k ∈ range (m + 1),
          C (((-lambda : ℂ) ^ k) * (m.choose k : ℂ)) *
            X ^ (m - k - (k + r)) * C ((m - k).choose (k + r) : ℂ) =
        ∑ k ∈ range (N + 1),
          C (((-lambda : ℂ) ^ k) * (m.choose k : ℂ)) *
            X ^ (m - k - (k + r)) * C ((m - k).choose (k + r) : ℂ) := by
    apply Finset.sum_subset (range_subset_range.2 (by lia))
    intro k hkN hkm
    have hmk : m < k := by simp at hkm; lia
    rw [Nat.choose_eq_zero_of_lt hmk]
    simp
  rw [hsum]
  apply sum_congr rfl
  intro k hk
  rw [iterate_derivative_X_pow_eq_C_mul]
  rw [show m - k - (k + r) = m - (2 * k + r) by lia]
  calc
    _ = C ((-lambda : ℂ) ^ k *
          ((m.choose k : ℂ) * ((m - k).choose (k + r) : ℂ))) *
        X ^ (m - (2 * k + r)) := by
          simp only [map_mul]
          ring
    _ = _ := by
      rw [cast_choose_mul_choose]
      have hscalar :
          (-lambda : ℂ) ^ k *
              ((m.descFactorial (2 * k + r) : ℂ) /
                ((k.factorial : ℂ) * ((k + r).factorial : ℂ))) =
            ((-lambda : ℂ) ^ k /
                ((k.factorial : ℂ) * ((k + r).factorial : ℂ))) *
              (m.descFactorial (2 * k + r) : ℂ) := by
        ring
      rw [hscalar, map_mul]
      ring

private theorem coeff_besselAuxiliaryPolynomial_eq_bound (N r : ℕ)
    (lambda : ℝ) (f : ℝ[X]) (hN : f.natDegree ≤ N) :
    (besselAuxiliaryPolynomial N lambda f).coeff (N + r) =
      complexBesselOperatorBound N lambda r (complexify f) := by
  have hfcomplex :
      complexify f =
        ∑ m ∈ range (N + 1), C (f.coeff m : ℂ) * X ^ m := by
    have hf : f = ∑ m ∈ range (N + 1), C (f.coeff m) * X ^ m :=
      f.as_sum_range_C_mul_X_pow' (n := N + 1) (by lia)
    calc
      complexify f = f.map Complex.ofRealHom := rfl
      _ = (∑ m ∈ range (N + 1), C (f.coeff m) * X ^ m).map
          Complex.ofRealHom := congrArg (Polynomial.map Complex.ofRealHom) hf
      _ = _ := by rw [Polynomial.map_sum]; simp
  rw [besselAuxiliaryPolynomial_eq, finsetSum_coeff]
  calc
    _ = ∑ m ∈ range (N + 1),
        C (f.coeff m : ℂ) * complexBesselOperatorBound N lambda r (X ^ m) := by
      apply sum_congr rfl
      intro m hm
      rw [mul_assoc, coeff_C_mul]
      rw [coeff_auxiliary_monomial_eq_bound N m r lambda (by simp at hm; lia)]
    _ = complexBesselOperatorBound N lambda r
        (∑ m ∈ range (N + 1), C (f.coeff m : ℂ) * X ^ m) := by
      unfold complexBesselOperatorBound
      simp_rw [Finset.mul_sum, iterate_derivative_sum, iterate_derivative_C_mul]
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro m hm
      ring
    _ = _ := by rw [← hfcomplex]

private theorem complexBesselOperatorBound_eq_complexify (N r : ℕ)
    (lambda : ℝ) (f : ℝ[X]) (hN : f.natDegree ≤ N) :
    complexBesselOperatorBound N lambda r (complexify f) =
      complexify (besselOperator lambda r f) := by
  have hmap :
      complexify (besselOperator lambda r f) =
        ∑ k ∈ range (f.natDegree + 1),
          C ((-lambda : ℂ) ^ k /
            ((k.factorial : ℂ) * ((k + r).factorial : ℂ))) *
              derivative^[2 * k + r] (complexify f) := by
    rw [complexify, besselOperator, Polynomial.map_sum]
    apply sum_congr rfl
    intro k hk
    simp only [Polynomial.map_mul, Polynomial.map_C]
    rw [show complexify f = f.map Complex.ofRealHom by rfl]
    rw [iterate_derivative_map]
    congr 2
    norm_cast
  rw [hmap]
  unfold complexBesselOperatorBound
  symm
  apply Finset.sum_subset (range_subset_range.2 (by lia))
  intro k hkN hk
  have hdegree : (complexify f).natDegree < 2 * k + r := by
    rw [complexify,
      Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective]
    simp at hk
    lia
  rw [iterate_derivative_eq_zero hdegree, mul_zero]

/-- The coefficient of `t^(N+r)` in the denominator-cleared auxiliary is the
complexification of the finite Bessel operator. -/
theorem besselAuxiliary_coeff (N r : ℕ) (lambda : ℝ) (f : ℝ[X])
    (hN : f.natDegree ≤ N) :
    (MvPolynomial.uniqueAlgEquiv ℂ Unit)
        ((MvPolynomial.optionEquivLeft ℂ Unit
          (besselAuxiliary N lambda f)).coeff (N + r)) =
      complexify (besselOperator lambda r f) := by
  rw [← complexBesselOperatorBound_eq_complexify N r lambda f hN]
  rw [← coeff_besselAuxiliaryPolynomial_eq_bound N r lambda f hN]
  rw [besselAuxiliaryPolynomial, Polynomial.coeff_map]
  rfl

private theorem isUpperHalfPlaneStable_uniqueAlgEquiv_unit
    {P : MvPolynomial Unit ℂ} (hP : MvUpperHalfPlaneStable P) :
    IsUpperHalfPlaneStable ((MvPolynomial.uniqueAlgEquiv ℂ Unit) P) := by
  intro z hz
  have h := hP (fun _ ↦ z) (fun _ ↦ hz)
  change ((MvPolynomial.uniqueAlgEquiv ℂ Unit) P).eval₂ (RingHom.id ℂ) z ≠ 0
  rw [MvPolynomial.eval₂_uniqueAlgEquiv
    (f := P) (φ := RingHom.id ℂ) (a := fun _ : Unit ↦ z)]
  exact h

/-- For nonnegative parameter, the finite Bessel output is zero or its
complexification is upper-half-plane stable. -/
theorem besselOperator_eq_zero_or_isUpperHalfPlaneStable_complexify
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (r : ℕ) {f : ℝ[X]}
    (hf : f.Splits) :
    besselOperator lambda r f = 0 ∨
      IsUpperHalfPlaneStable (complexify (besselOperator lambda r f)) := by
  by_cases hf0 : f = 0
  · exact Or.inl (by rw [hf0, besselOperator_zero])
  have hcoeff := besselAuxiliary_coeff_zero_or f.natDegree r hlambda hf0 hf le_rfl
  rcases hcoeff with hzero | hstable
  · left
    apply (Polynomial.map_eq_zero_iff (f := Complex.ofRealHom)
      Complex.ofReal_injective).mp
    change complexify (besselOperator lambda r f) = 0
    rw [← besselAuxiliary_coeff f.natDegree r lambda f le_rfl, hzero]
    simp
  · right
    rw [← besselAuxiliary_coeff f.natDegree r lambda f le_rfl]
    exact isUpperHalfPlaneStable_uniqueAlgEquiv_unit hstable

/-- For nonnegative parameter, every finite Bessel operator preserves real
rootedness, with the zero polynomial included in Mathlib's `Splits` predicate. -/
theorem besselOperator_splits {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (r : ℕ) {f : ℝ[X]} (hf : f.Splits) :
    (besselOperator lambda r f).Splits := by
  rcases besselOperator_eq_zero_or_isUpperHalfPlaneStable_complexify
      hlambda r hf with hzero | hstable
  · rw [hzero]
    exact Polynomial.Splits.zero
  · exact hstable.splits_complexify

private theorem coeff_zero_besselOperator_X_pow_add_two_pos {lambda : ℝ}
    (hlambda : lambda < 0) (r : ℕ) :
    0 < (besselOperator lambda r (X ^ (r + 2))).coeff 0 := by
  rw [coeff_besselOperator]
  rw [sum_eq_single 1]
  · simp only [zero_add]
    rw [coeff_X_pow]
    rw [ite_eq_left (by lia)]
    norm_num only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul]
    have hdescNat : 0 < (2 + r).descFactorial (2 + r) := by
      simp [Nat.add_comm]
    have hdescReal : 0 < ((2 + r).descFactorial (2 + r) : ℝ) := by
      exact_mod_cast hdescNat
    have hfactorial : 0 < ((1 + r).factorial : ℝ) := by positivity
    have hneg : 0 < -lambda := neg_pos.mpr hlambda
    positivity
  · intro k hk hk1
    rw [coeff_X_pow]
    split_ifs with heq
    · exfalso
      have : k = 1 := by lia
      exact hk1 this
    · simp
  · simp

private theorem coeff_one_besselOperator_X_pow_add_two (lambda : ℝ) (r : ℕ) :
    (besselOperator lambda r (X ^ (r + 2))).coeff 1 = 0 := by
  rw [coeff_besselOperator]
  apply sum_eq_zero
  intro k hk
  rw [coeff_X_pow]
  split_ifs with heq
  · exfalso
    lia
  · simp

private theorem coeff_two_besselOperator_X_pow_add_two_pos (lambda : ℝ) (r : ℕ) :
    0 < (besselOperator lambda r (X ^ (r + 2))).coeff 2 := by
  have hr : r ≤ (X ^ (r + 2) : ℝ[X]).natDegree := by simp
  have htop := coeff_besselOperator_natDegree_sub lambda r (X ^ (r + 2)) hr
  rw [show (X ^ (r + 2) : ℝ[X]).natDegree - r = 2 by simp] at htop
  rw [htop]
  simp only [natDegree_X_pow, leadingCoeff_X_pow, mul_one, Nat.cast_pos]
  exact Nat.choose_pos (by lia)

/-- The finite Bessel operator preserves every split real polynomial exactly
for nonnegative values of the parameter. -/
theorem nonneg_iff_forall_besselOperator_splits (lambda : ℝ) (r : ℕ) :
    0 ≤ lambda ↔
      ∀ f : ℝ[X], f.Splits → (besselOperator lambda r f).Splits := by
  constructor
  · intro hlambda f hf
    exact besselOperator_splits hlambda r hf
  · intro hpreserves
    by_contra hlambda
    have hnegative : lambda < 0 := lt_of_not_ge hlambda
    let p := besselOperator lambda r (X ^ (r + 2))
    have hpdeg : p.natDegree = 2 := by
      dsimp [p]
      rw [natDegree_besselOperator lambda r (X ^ (r + 2)) (by simp) (by simp)]
      simp
    have hpsplits : p.Splits :=
      hpreserves (X ^ (r + 2)) (Polynomial.Splits.X_pow (r + 2))
    have hdisc := quadratic_disc_coeff_le_of_splits_natDegree_two hpdeg hpsplits
    have hp0 : 0 < p.coeff 0 :=
      coeff_zero_besselOperator_X_pow_add_two_pos hnegative r
    have hp1 : p.coeff 1 = 0 := coeff_one_besselOperator_X_pow_add_two lambda r
    have hp2 : 0 < p.coeff 2 := coeff_two_besselOperator_X_pow_add_two_pos lambda r
    rw [hp1] at hdisc
    nlinarith

end

end RealRooted
