module

import RealRooted.Favard
public import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Bernstein
import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Roots
public import RealRooted.Transforms.BrandenE.Inverse
public import RealRooted.Transforms.BrandenE.WeightedSum
import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Algebra
public import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Basic

/-!
# The Delannoy family and Brändén's E transform

The inverse image under Brändén's `E` transform of the doubled Pascal power
is a normalized Delannoy polynomial.  Its roots lie on the vertical line of
real part `-1 / 2`.  The Cayley transform then gives a coefficient certificate
in the ambient Bernstein basis.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

private lemma brandenEPreimage_twoPascal_recurrence (n : ℕ) :
    C ((n + 2 : ℕ) : ℝ) *
        brandenEPreimage (R := ℝ) ((1 + C 2 * X) ^ (n + 2)) =
      (C 2 * X + 1) *
          brandenEPreimage (R := ℝ) ((1 + C 2 * X) ^ (n + 1)) +
        C ((n + 1 : ℕ) : ℝ) *
          brandenEPreimage (R := ℝ) ((1 + C 2 * X) ^ n) := by
  apply brandenE_injective (R := ℝ)
  rw [show C ((n + 2 : ℕ) : ℝ) *
        brandenEPreimage (R := ℝ) ((1 + C 2 * X) ^ (n + 2)) =
      ((n + 2 : ℕ) : ℝ) •
        brandenEPreimage (R := ℝ) ((1 + C 2 * X) ^ (n + 2)) by
      rw [Polynomial.smul_eq_C_mul],
    brandenE_smul, brandenE_preimage]
  have hfirst : (C 2 * X + 1) *
          brandenEPreimage (R := ℝ) ((1 + C 2 * X) ^ (n + 1)) =
        (2 : ℝ) •
            (X * brandenEPreimage (R := ℝ) ((1 + C 2 * X) ^ (n + 1))) +
          brandenEPreimage (R := ℝ) ((1 + C 2 * X) ^ (n + 1)) := by
    rw [Polynomial.smul_eq_C_mul]
    ring
  have hsecond : C ((n + 1 : ℕ) : ℝ) *
          brandenEPreimage (R := ℝ) ((1 + C 2 * X) ^ n) =
        ((n + 1 : ℕ) : ℝ) •
          brandenEPreimage (R := ℝ) ((1 + C 2 * X) ^ n) := by
    rw [Polynomial.smul_eq_C_mul]
  rw [hfirst, hsecond]
  simp only [brandenE_add, brandenE_smul, brandenE_X_mul,
    brandenE_preimage]
  simp only [Polynomial.derivative_pow, derivative_add, derivative_one,
    derivative_mul, derivative_C, derivative_X, zero_add, zero_mul,
    mul_one]
  push_cast
  norm_num [map_ofNat, map_add, map_mul]
  ring

/-- The inverse Brändén image of the doubled Pascal powers. -/
def brandenDelannoy (n : ℕ) : ℝ[X] :=
  brandenEPreimage (R := ℝ) ((1 + C 2 * X) ^ n)

@[simp] theorem brandenDelannoy_zero : brandenDelannoy 0 = 1 := by
  apply brandenE_injective (R := ℝ)
  rw [brandenDelannoy, brandenE_preimage]
  rw [show (1 : ℝ[X]) = X ^ 0 by simp, brandenE_X_pow]
  simp

@[simp] theorem brandenDelannoy_one : brandenDelannoy 1 = 1 + C 2 * X := by
  apply brandenE_injective (R := ℝ)
  rw [brandenDelannoy, brandenE_preimage, pow_one,
    brandenE_add, brandenE_C_mul]
  rw [show (1 : ℝ[X]) = X ^ 0 by simp, brandenE_X_pow]
  rw [show (X : ℝ[X]) = X ^ 1 by simp, brandenE_X_pow]
  simp [orderedBellPolynomial]

theorem brandenDelannoy_recurrence (n : ℕ) :
    C ((n + 2 : ℕ) : ℝ) * brandenDelannoy (n + 2) =
      (C 2 * X + 1) * brandenDelannoy (n + 1) +
        C ((n + 1 : ℕ) : ℝ) * brandenDelannoy n :=
  brandenEPreimage_twoPascal_recurrence n

/-- Monic normalization of the rotated Delannoy polynomial. -/
def delannoyFavard : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => X * delannoyFavard (n + 1) -
      C ((((n + 1 : ℕ) : ℝ) ^ 2) / 4) * delannoyFavard n

private lemma delannoyFavard_recurrence :
    SatisfiesFavardRecurrence delannoyFavard (fun _ => 0)
      (fun n => ((n : ℝ) ^ 2) / 4) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [delannoyFavard]
  · intro n
    simp only [delannoyFavard]
    simp

private lemma delannoyFavard_beta_pos (n : ℕ) :
    0 < ((((n + 1 : ℕ) : ℝ) ^ 2) / 4) := by
  positivity

theorem delannoyFavard_strictInterl (n : ℕ) :
    StrictInterl (delannoyFavard n) (delannoyFavard (n + 1)) :=
  favardInterlacing delannoyFavard_recurrence delannoyFavard_beta_pos n

theorem delannoyFavard_splits (n : ℕ) :
    (delannoyFavard n).Splits :=
  (isRealRooted_of_favard delannoyFavard_recurrence
    delannoyFavard_beta_pos n).2

theorem delannoyFavard_ne_zero (n : ℕ) : delannoyFavard n ≠ 0 :=
  (isRealRooted_of_favard delannoyFavard_recurrence
    delannoyFavard_beta_pos n).1

private theorem delannoyFavard_monic_natDegree : ∀ n : ℕ,
    (delannoyFavard n).Monic ∧ (delannoyFavard n).natDegree = n
  | 0 => by simp [delannoyFavard]
  | 1 => by simp [delannoyFavard]
  | n + 2 => by
      rw [delannoyFavard]
      have ih0 := delannoyFavard_monic_natDegree n
      have ih1 := delannoyFavard_monic_natDegree (n + 1)
      have hleft : (X * delannoyFavard (n + 1)).Monic := monic_X.mul ih1.1
      have hlt :
          (C ((((n + 1 : ℕ) : ℝ) ^ 2) / 4) * delannoyFavard n).natDegree <
            (X * delannoyFavard (n + 1)).natDegree := by
        refine (natDegree_C_mul_le _ _).trans_lt ?_
        rw [ih0.2, natDegree_mul monic_X.ne_zero ih1.1.ne_zero,
          natDegree_X, ih1.2]
        lia
      have hmonic := hleft.sub_of_left (degree_lt_degree hlt)
      exact ⟨hmonic, by
        rw [natDegree_sub_eq_left_of_natDegree_lt hlt,
          natDegree_mul monic_X.ne_zero ih1.1.ne_zero,
          natDegree_X, ih1.2]
        lia⟩

theorem delannoyFavard_monic (n : ℕ) : (delannoyFavard n).Monic :=
  (delannoyFavard_monic_natDegree n).1

theorem delannoyFavard_natDegree (n : ℕ) :
    (delannoyFavard n).natDegree = n :=
  (delannoyFavard_monic_natDegree n).2

/-- Factorial normalization of the real Delannoy Favard family. -/
def delannoyNormalized (n : ℕ) : ℝ[X] :=
  C (((2 : ℝ) ^ n) / (Nat.factorial n : ℝ)) * delannoyFavard n

@[simp] theorem delannoyNormalized_zero : delannoyNormalized 0 = 1 := by
  simp [delannoyNormalized, delannoyFavard]

@[simp] theorem delannoyNormalized_one : delannoyNormalized 1 = C 2 * X := by
  simp [delannoyNormalized, delannoyFavard]

theorem delannoyNormalized_recurrence (n : ℕ) :
    C ((n + 2 : ℕ) : ℝ) * delannoyNormalized (n + 2) =
      C 2 * X * delannoyNormalized (n + 1) -
        C ((n + 1 : ℕ) : ℝ) * delannoyNormalized n := by
  rw [delannoyNormalized, delannoyNormalized, delannoyNormalized,
    delannoyFavard]
  have hn1 : (Nat.factorial (n + 1) : ℝ) ≠ 0 := by positivity
  have hn2 : (Nat.factorial (n + 2) : ℝ) ≠ 0 := by positivity
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  grind

/-- Delannoy polynomials rotated onto the vertical line `re z = -1 / 2`. -/
def delannoyVertical (n : ℕ) : ℂ[X] :=
  C (Complex.I ^ n) *
    (delannoyNormalized n).map Complex.ofRealHom |>.comp
      (C (-Complex.I) * (X + C (1 / 2 : ℂ)))

@[simp] theorem delannoyVertical_zero : delannoyVertical 0 = 1 := by
  simp [delannoyVertical]

@[simp] theorem delannoyVertical_one : delannoyVertical 1 = 1 + C 2 * X := by
  apply Polynomial.funext
  intro z
  simp [delannoyVertical]
  ring_nf
  simp

theorem delannoyVertical_recurrence (n : ℕ) :
    C ((n + 2 : ℕ) : ℂ) * delannoyVertical (n + 2) =
      (C 2 * X + 1) * delannoyVertical (n + 1) +
        C ((n + 1 : ℕ) : ℂ) * delannoyVertical n := by
  rw [delannoyVertical, delannoyVertical, delannoyVertical]
  apply Polynomial.funext
  intro z
  have hz := congrArg
    (fun p : ℝ[X] => p.eval₂ Complex.ofRealHom
      (-Complex.I * (z + (1 / 2 : ℂ))))
    (delannoyNormalized_recurrence n)
  simp at hz
  simp only [Nat.cast_add, Nat.cast_ofNat, map_add, map_natCast, map_pow, map_neg, one_div,
    neg_mul, mul_comp, pow_comp, C_comp, eval_mul, eval_add, eval_natCast, eval_C, eval_pow,
    eval_comp, eval_neg, eval_X, Nat.cast_one, map_one, eval_one]
  simp only [eval_map] at ⊢
  rw [pow_add, pow_add]
  ring_nf at hz ⊢
  rw [Complex.I_sq]
  grind

theorem delannoyNormalized_splits (n : ℕ) :
    (delannoyNormalized n).Splits := by
  rw [delannoyNormalized]
  exact (Polynomial.Splits.C _).mul (delannoyFavard_splits n)

theorem delannoyNormalized_ne_zero (n : ℕ) :
    delannoyNormalized n ≠ 0 := by
  rw [delannoyNormalized]
  exact mul_ne_zero
    (by simp only [ne_eq, map_eq_zero, div_eq_zero_iff, pow_eq_zero_iff',
      OfNat.ofNat_ne_zero, false_and, Nat.cast_eq_zero, false_or]; positivity)
    (delannoyFavard_ne_zero n)

/-- Every root of `delannoyVertical n` has real part `-1 / 2`. -/
theorem delannoyVertical_root_re (n : ℕ) {z : ℂ}
    (hz : z ∈ (delannoyVertical n).roots) : z.re = -1 / 2 := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hscale : Complex.I ^ n ≠ 0 := pow_ne_zero _ hI
  rw [delannoyVertical, Polynomial.mul_comp, Polynomial.C_comp,
    roots_C_mul _ hscale] at hz
  have hq :
      (C (-Complex.I) * (X + C (1 / 2 : ℂ)) : ℂ[X]) =
        C (-Complex.I) * X + C (-Complex.I * (1 / 2 : ℂ)) := by
    grind
  rw [hq, roots_comp_C_mul_X_add_C _ _ _
    (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hI))] at hz
  rcases Multiset.mem_map.mp hz with ⟨w, hw, rfl⟩
  have hmaproots := (delannoyNormalized_splits n).roots_map_of_injective
    (i := Complex.ofRealHom) Complex.ofReal_injective
  rw [hmaproots] at hw
  rcases Multiset.mem_map.mp hw with ⟨r, _, rfl⟩
  have hinv : Ring.inverse (-Complex.I) = Complex.I := by simp
  rw [hinv]
  simp
  ring

theorem delannoyVertical_splits (n : ℕ) :
    (delannoyVertical n).Splits := by
  rw [delannoyVertical]
  apply Polynomial.Splits.comp_of_natDegree_le_one
  · exact (Polynomial.Splits.C _).mul
      ((delannoyNormalized_splits n).map Complex.ofRealHom)
  · compute_degree!

theorem delannoyNormalized_natDegree (n : ℕ) :
    (delannoyNormalized n).natDegree = n := by
  rw [delannoyNormalized, natDegree_C_mul]
  · exact delannoyFavard_natDegree n
  · exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)

theorem delannoyVertical_natDegree (n : ℕ) :
    (delannoyVertical n).natDegree = n := by
  rw [delannoyVertical, natDegree_comp,
    natDegree_C_mul (pow_ne_zero _ Complex.I_ne_zero),
    natDegree_map_eq_of_injective Complex.ofReal_injective,
    delannoyNormalized_natDegree]
  have hinner :
      (C (-Complex.I) * (X + C (1 / 2 : ℂ)) : ℂ[X]).natDegree = 1 := by
    compute_degree!
  simp_all

theorem delannoyVertical_ne_zero (n : ℕ) : delannoyVertical n ≠ 0 := by
  intro hzero
  have hdegree := delannoyVertical_natDegree n
  cases n with
  | zero => simp_all
  | succ n => simp_all

theorem delannoyVertical_coeff_zero : ∀ n : ℕ,
    (delannoyVertical n).coeff 0 = 1 := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih_succ =>
      have h := congrArg (Polynomial.eval (0 : ℂ))
        (delannoyVertical_recurrence n)
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_one] at h
      have ih_eval : (delannoyVertical n).eval 0 = 1 := by
        rw [← coeff_zero_eq_eval_zero]
        exact ih
      have ih_succ_eval : (delannoyVertical (n + 1)).eval 0 = 1 := by
        rw [← coeff_zero_eq_eval_zero]
        exact ih_succ
      rw [ih_eval, ih_succ_eval] at h
      rw [coeff_zero_eq_eval_zero]
      push_cast at h
      norm_num at h
      apply mul_left_cancel₀
        (show ((n : ℂ) + 2) ≠ 0 by
          exact_mod_cast (by lia : (n : ℕ) + 2 ≠ 0))
      grind

/-- The Brändén preimage agrees with the vertical-line Delannoy family. -/
theorem map_brandenDelannoy_eq_delannoyVertical : ∀ n : ℕ,
    (brandenDelannoy n).map Complex.ofRealHom = delannoyVertical n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih_succ =>
      have hreal := congrArg (Polynomial.map Complex.ofRealHom)
        (brandenDelannoy_recurrence n)
      have hreal' :
          C ((n + 2 : ℕ) : ℂ) *
              (brandenDelannoy (n + 2)).map Complex.ofRealHom =
            (C 2 * X + 1) *
                (brandenDelannoy (n + 1)).map Complex.ofRealHom +
              C ((n + 1 : ℕ) : ℂ) *
                (brandenDelannoy n).map Complex.ofRealHom := by
        simpa using hreal
      have hcomplex := delannoyVertical_recurrence n
      apply mul_left_cancel₀
        (show C ((n + 2 : ℕ) : ℂ) ≠ 0 by
          rw [Polynomial.C_ne_zero]
          exact_mod_cast (by lia : (n + 2 : ℕ) ≠ 0))
      simp_all

/-- Cayley transform of the real Delannoy preimage. -/
def delannoyCayley (n : ℕ) : ℝ[X] :=
  Polynomial.cayleyTransform n (brandenDelannoy n)

theorem map_delannoyCayley (n : ℕ) :
    (delannoyCayley n).map Complex.ofRealHom =
      Polynomial.cayleyTransform n (delannoyVertical n) := by
  rw [delannoyCayley, Polynomial.map_cayleyTransform,
    map_brandenDelannoy_eq_delannoyVertical]

theorem brandenDelannoy_natDegree (n : ℕ) :
    (brandenDelannoy n).natDegree = n := by
  have hmap := natDegree_map_eq_of_injective
    (f := Complex.ofRealHom) Complex.ofReal_injective (brandenDelannoy n)
  rw [map_brandenDelannoy_eq_delannoyVertical,
    delannoyVertical_natDegree] at hmap
  grind

theorem delannoyCayley_natDegree (n : ℕ) :
    (delannoyCayley n).natDegree = n := by
  have hmap := natDegree_map_eq_of_injective
    (f := Complex.ofRealHom) Complex.ofReal_injective (delannoyCayley n)
  rw [map_delannoyCayley,
    Polynomial.cayleyTransform_natDegree (delannoyVertical_ne_zero n)
      (delannoyVertical_splits n) (delannoyVertical_natDegree n)
      (fun _ hr => delannoyVertical_root_re n hr)] at hmap
  grind

theorem delannoyCayley_coeff_zero (n : ℕ) :
    (delannoyCayley n).coeff 0 = 1 := by
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff 0)
    (map_delannoyCayley n)
  rw [Polynomial.coeff_map,
    Polynomial.cayleyTransform_coeff_zero (delannoyVertical_splits n)
      (delannoyVertical_natDegree n),
    delannoyVertical_coeff_zero] at hcoeff
  exact Complex.ofReal_injective hcoeff

/-- Every Cayley coefficient is bounded by the corresponding Pascal entry. -/
theorem abs_delannoyCayley_coeff_le_choose (n k : ℕ) :
    |(delannoyCayley n).coeff k| ≤ Nat.choose n k := by
  have hbound := Polynomial.norm_coeff_cayleyTransform_le_choose
    (delannoyVertical_ne_zero n) (delannoyVertical_splits n)
    (delannoyVertical_natDegree n)
    (fun _ hr => delannoyVertical_root_re n hr)
    (by rw [delannoyVertical_coeff_zero]; norm_num) (k := k)
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff k)
    (map_delannoyCayley n)
  rw [Polynomial.coeff_map] at hcoeff
  rw [← hcoeff] at hbound
  simpa using hbound

/-- Nonnegative Bernstein-basis weight supplied by the Delannoy certificate. -/
def delannoyPascalWeight (n k : ℕ) : ℝ :=
  Nat.choose n k + (delannoyCayley n).coeff k

theorem delannoyPascalWeight_nonneg (n k : ℕ) :
    0 ≤ delannoyPascalWeight n k := by
  have hbound := (abs_le.mp (abs_delannoyCayley_coeff_le_choose n k)).1
  simp only [delannoyPascalWeight]
  linarith

theorem delannoyPascalWeight_zero_pos (n : ℕ) :
    0 < delannoyPascalWeight n 0 := by
  rw [delannoyPascalWeight, delannoyCayley_coeff_zero]
  simp

private lemma cayleyTransform_brandenBasisWeightedInput
    (n : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hkn : ∀ k ∈ s, k ≤ n) :
    Polynomial.cayleyTransform n (brandenBasisWeightedInput n s a) =
      ∑ k ∈ s, C (a k) * X ^ k := by
  rw [brandenBasisWeightedInput, Polynomial.cayleyTransform_finset_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.cayleyTransform_C_mul]
  congr 1
  simpa [brandenBinomialBasis, add_comm] using
    Polynomial.cayleyTransform_binomialBasisRaw (K := ℝ) (hkn k hk)

private lemma cayleyTransform_twoPascal_add_delannoy (n : ℕ) :
    Polynomial.cayleyTransform n
        ((1 + C 2 * X) ^ n + brandenDelannoy n) =
      ∑ k ∈ Finset.range (n + 1),
        C (delannoyPascalWeight n k) * X ^ k := by
  rw [Polynomial.cayleyTransform_add, Polynomial.cayleyTransform_twoPascal]
  change (1 + X : ℝ[X]) ^ n + delannoyCayley n = _
  rw [((1 + X : ℝ[X]) ^ n).as_sum_range_C_mul_X_pow'
      (n := n + 1) (by
        rw [show (1 + X : ℝ[X]) = X + C 1 by simp [add_comm],
          natDegree_pow_X_add_C]
        lia),
    (delannoyCayley n).as_sum_range_C_mul_X_pow'
      (n := n + 1) (by rw [delannoyCayley_natDegree]; lia),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Polynomial.coeff_one_add_X_pow, delannoyPascalWeight]
  grind

private lemma brandenBasisWeightedInput_natDegree_le
    (n : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hkn : ∀ k ∈ s, k ≤ n) :
    (brandenBasisWeightedInput n s a).natDegree ≤ n := by
  rw [brandenBasisWeightedInput]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_C_mul_le _ _).trans
    (Polynomial.natDegree_mul_le.trans (by
      simp only [natDegree_X_pow]
      have hpow : ((X + 1 : ℝ[X]) ^ (n - k)).natDegree = n - k := by
        rw [show (X + 1 : ℝ[X]) = X + C 1 by simp,
          natDegree_pow_X_add_C]
      simp_all))

private theorem cayleyTransformReal_injective_on_natDegree_le (n : ℕ)
    {p q : ℝ[X]} (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree ≤ n)
    (heq : Polynomial.cayleyTransform n p =
      Polynomial.cayleyTransform n q) : p = q := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  apply Polynomial.cayleyTransform_injective_on_natDegree_le n
  · simpa using hpdeg
  · simpa using hqdeg
  · rw [← Polynomial.map_cayleyTransform,
      ← Polynomial.map_cayleyTransform, heq]

/-- The doubled Pascal power plus its Delannoy preimage has nonnegative
coordinates in Brändén's ambient binomial basis. -/
theorem twoPascal_add_brandenDelannoy_eq_weightedInput (n : ℕ) :
    (1 + C 2 * X) ^ n + brandenDelannoy n =
      brandenBasisWeightedInput n (Finset.range (n + 1))
        (delannoyPascalWeight n) := by
  apply cayleyTransformReal_injective_on_natDegree_le n
  · exact (natDegree_add_le _ _).trans (max_le (by compute_degree!)
      (brandenDelannoy_natDegree n).le)
  · exact brandenBasisWeightedInput_natDegree_le n _ _ (by simp)
  · rw [cayleyTransform_twoPascal_add_delannoy,
      cayleyTransform_brandenBasisWeightedInput]
    simp

end RealRooted
