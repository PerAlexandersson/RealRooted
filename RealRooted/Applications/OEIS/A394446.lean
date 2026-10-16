module

public import RealRooted.GammaTransform.Derivative
public import RealRooted.CombinatorialExamples.Narayana
public import RealRooted.GammaTransform.Preservation
public import RealRooted.NarayanaTransformation.Endpoints

/-!
# OEIS A394446

The rows of A394446 grow in degree by two.  We identify them with the gamma transforms
`gammaTransform (2 * n) (narayanaPolynomial 1 n)` of the Narayana polynomials, through a
lowering identity for `narayanaPolynomial 1` and the Euler-derivative formula for gamma
transforms, and deduce that every row splits.
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted.Applications.OEIS.A394446

private lemma narayanaTransformCoeff_one_eq (n k : ℕ) :
    narayanaTransformCoeff 1 n k =
      (Nat.choose n k : ℝ) * (Nat.choose (n + 1) k : ℝ) / (k + 1) := by
  simp [narayanaTransformCoeff, add_comm]

private lemma narayanaTransformCoeff_one_lower_interior
    (n k : ℕ) (hk : k < n) :
    ((n : ℝ) + 1 - 2 * ((k : ℝ) + 1)) *
        narayanaTransformCoeff 1 (n + 1) (k + 1) =
      ((n : ℝ) + 1) *
        (narayanaTransformCoeff 1 n (k + 1) -
          narayanaTransformCoeff 1 n k) := by
  have h1 := Nat.choose_succ_right_eq n k
  have h2 := Nat.choose_succ_right_eq (n + 1) k
  have h3 := Nat.add_one_mul_choose_eq n k
  have h4 := Nat.add_one_mul_choose_eq (n + 1) k
  have c1 : (Nat.choose n (k + 1) : ℝ) =
      (Nat.choose n k : ℝ) * ((n : ℝ) - k) / (k + 1) := by
    rw [eq_div_iff (by positivity)]
    have h := congrArg (fun m : ℕ ↦ (m : ℝ)) h1
    push_cast [Nat.cast_sub hk.le] at h
    linarith
  have c2 : (Nat.choose (n + 1) (k + 1) : ℝ) =
      (Nat.choose (n + 1) k : ℝ) * ((n : ℝ) + 1 - k) /
        (k + 1) := by
    rw [eq_div_iff (by positivity)]
    have h := congrArg (fun m : ℕ ↦ (m : ℝ)) h2
    push_cast [Nat.cast_sub (by lia : k ≤ n + 1)] at h
    linarith
  have c3 : (Nat.choose (n + 1) (k + 1) : ℝ) =
      ((n : ℝ) + 1) * (Nat.choose n k : ℝ) / (k + 1) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast h3.symm
  have c4 : (Nat.choose (n + 2) (k + 1) : ℝ) =
      ((n : ℝ) + 2) * (Nat.choose (n + 1) k : ℝ) / (k + 1) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast h4.symm
  rw [narayanaTransformCoeff_one_eq, narayanaTransformCoeff_one_eq,
    narayanaTransformCoeff_one_eq]
  push_cast
  rw [c1, c4]
  nth_rewrite 2 [c2]
  rw [c3]
  field_simp
  ring

private lemma coeff_narayanaPolynomial_one_lower (n k : ℕ) :
    ((n : ℝ) + 1 - 2 * (k + 1)) *
        (narayanaPolynomial 1 (n + 1)).coeff (k + 1) =
      ((n : ℝ) + 1) *
        ((narayanaPolynomial 1 n).coeff (k + 1) -
          (narayanaPolynomial 1 n).coeff k) := by
  rcases lt_trichotomy k n with hk | rfl | hk
  · rw [coeff_narayanaPolynomial_of_le (by lia),
      coeff_narayanaPolynomial_of_le (by lia),
      coeff_narayanaPolynomial_of_le (by lia)]
    simpa only [Nat.cast_add, Nat.cast_one] using
      narayanaTransformCoeff_one_lower_interior n k hk
  · rw [coeff_narayanaPolynomial_of_le le_rfl,
      coeff_narayanaPolynomial_of_lt (Nat.lt_succ_self k),
      coeff_narayanaPolynomial_of_le le_rfl]
    norm_num [narayanaTransformCoeff, Nat.choose_self,
      Nat.choose_succ_self_right]
    have hadd_succ : 1 + (k + 1) = (k + 1) + 1 := by lia
    rw [hadd_succ, Nat.choose_succ_self_right]
    have hadd : 1 + k = k + 1 := by lia
    rw [hadd, Nat.choose_succ_self_right]
    field_simp
    push_cast
    ring
  · rw [coeff_narayanaPolynomial_of_lt (by lia : n + 1 < k + 1),
      coeff_narayanaPolynomial_of_lt (by lia : n < k + 1),
      coeff_narayanaPolynomial_of_lt hk]
    ring

/-- The ordinary Narayana rows satisfy their derivative lowering relation. -/
theorem narayanaPolynomial_one_lowering (n : ℕ) :
    C ((n : ℝ) + 1) * narayanaPolynomial 1 (n + 1) -
        C 2 * X * (narayanaPolynomial 1 (n + 1)).derivative =
      C ((n : ℝ) + 1) * (1 - X) * narayanaPolynomial 1 n := by
  ext k
  have hleft : C 2 * X * (narayanaPolynomial 1 (n + 1)).derivative =
      C 2 * (X * (narayanaPolynomial 1 (n + 1)).derivative) := by ring
  have hright : C ((n : ℝ) + 1) * (1 - X) * narayanaPolynomial 1 n =
      C ((n : ℝ) + 1) * narayanaPolynomial 1 n -
        C ((n : ℝ) + 1) * (X * narayanaPolynomial 1 n) := by ring
  rw [hleft, hright]
  simp only [coeff_sub, coeff_C_mul]
  rcases k with _ | k
  · simp
  · simp only [coeff_X_mul, coeff_derivative]
    linear_combination coeff_narayanaPolynomial_one_lower n k

/-- The initial nonconstant A394446 row. -/
def initialPolynomial : ℝ[X] := 1 + 3 * X + X ^ 2

/-- The quadratic factor in the lag term of the A394446 recurrence. -/
def quadraticFactor : ℝ[X] := 1 + X + X ^ 2

/-- The row polynomial of [OEIS A394446](https://oeis.org/A394446). -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => initialPolynomial
  | n + 2 =>
      C (((2 * n : ℝ) + 5) / ((n : ℝ) + 4)) * initialPolynomial *
          polynomial (n + 1) -
        C (((n : ℝ) + 1) / ((n : ℝ) + 4)) * quadraticFactor ^ 2 * polynomial n

private lemma gammaTransform_one_add_X_mul (n : ℕ) :
    gammaTransform (2 * (n + 2))
        ((1 + X) * narayanaPolynomial 1 (n + 1)) =
      initialPolynomial * gammaTransform (2 * (n + 1))
        (narayanaPolynomial 1 (n + 1)) := by
  have hdeg : (narayanaPolynomial 1 (n + 1)).natDegree ≤
      (2 * (n + 1)) / 2 := by
    rw [natDegree_narayanaPolynomial]
    lia
  have hambient : 2 * (n + 2) = 2 * (n + 1) + 2 := by lia
  have hexpand : (1 + X) * narayanaPolynomial 1 (n + 1) =
      narayanaPolynomial 1 (n + 1) +
        X * narayanaPolynomial 1 (n + 1) := by ring
  rw [hexpand]
  rw [gammaTransform_add, hambient, gammaTransform_pad_two hdeg,
    gammaTransform_X_mul_two]
  simp only [initialPolynomial]
  ring

private lemma gammaTransform_one_sub_X_sq_mul (n : ℕ) :
    gammaTransform (2 * (n + 2))
        ((1 - X) ^ 2 * narayanaPolynomial 1 n) =
      quadraticFactor ^ 2 * gammaTransform (2 * n) (narayanaPolynomial 1 n) := by
  have hdeg : (narayanaPolynomial 1 n).natDegree ≤ (2 * n) / 2 := by
    rw [natDegree_narayanaPolynomial]
    simp
  have hambient : 2 * (n + 2) = 2 * n + 2 * 2 := by lia
  have hexpand : (1 - X) ^ 2 * narayanaPolynomial 1 n =
      narayanaPolynomial 1 n - C 2 * (X * narayanaPolynomial 1 n) +
        X * (X * narayanaPolynomial 1 n) := by
      norm_num [map_ofNat]
      ring
  rw [hexpand]
  rw [gammaTransform_add, gammaTransform_sub, gammaTransform_C_mul]
  rw [hambient, gammaTransform_add_two_mul (2 * n) 2 hdeg]
  have hambient' : 2 * n + 2 * 2 = (2 * n + 2) + 2 := by lia
  rw [hambient']
  rw [gammaTransform_X_mul_two (2 * n + 2)
    (X * narayanaPolynomial 1 n)]
  rw [gammaTransform_X_mul_two (2 * n) (narayanaPolynomial 1 n)]
  rw [gammaTransform_X_mul_two (2 * n + 2) (narayanaPolynomial 1 n)]
  rw [gammaTransform_pad_two hdeg]
  simp only [quadraticFactor]
  norm_num [map_ofNat]
  ring

private lemma gammaTransform_narayanaPolynomial_pure_recurrence (n : ℕ) :
    C ((n : ℝ) + 4) *
        gammaTransform (2 * (n + 2)) (narayanaPolynomial 1 (n + 2)) =
      C ((2 * n : ℝ) + 5) * initialPolynomial *
          gammaTransform (2 * (n + 1)) (narayanaPolynomial 1 (n + 1)) -
        C ((n : ℝ) + 1) * quadraticFactor ^ 2 *
          gammaTransform (2 * n) (narayanaPolynomial 1 n) := by
  have h := congrArg (gammaTransform (2 * (n + 2)))
    (narayanaPolynomial_pure_rec 1 n)
  rw [gammaTransform_C_mul, gammaTransform_sub, gammaTransform_C_mul,
    gammaTransform_C_mul, gammaTransform_one_add_X_mul,
    gammaTransform_one_sub_X_sq_mul] at h
  norm_num only [Nat.cast_one] at h
  ring_nf at h ⊢
  exact h

/-- Each A394446 row is the even gamma transform of the ordinary Narayana row. -/
theorem polynomial_eq_gammaTransform (n : ℕ) :
    polynomial n = gammaTransform (2 * n) (narayanaPolynomial 1 n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [polynomial, gammaTransform]
  | one =>
      change initialPolynomial = gammaTransform 2 (narayanaPolynomial 1 1)
      rw [narayanaPolynomial_one]
      simp only [initialPolynomial]
      norm_num [gammaTransform, gammaBasisTerm, Finset.sum_range_succ,
        coeff_add, coeff_X, coeff_one]
      ring
  | more n ih ih_succ =>
      rw [polynomial, ih, ih_succ]
      have hrec := gammaTransform_narayanaPolynomial_pure_recurrence n
      have hden : (C ((n : ℝ) + 4) : ℝ[X]) ≠ 0 :=
        C_ne_zero.mpr (by positivity)
      have ha : C ((n : ℝ) + 4) *
          C (((2 * n : ℝ) + 5) / ((n : ℝ) + 4)) =
          C ((2 * n : ℝ) + 5) := by
        rw [← map_mul]
        congr 1
        field_simp
      have hb : C ((n : ℝ) + 4) *
          C (((n : ℝ) + 1) / ((n : ℝ) + 4)) =
          C ((n : ℝ) + 1) := by
        rw [← map_mul]
        congr 1
        field_simp
      apply mul_left_cancel₀ hden
      calc
        C ((n : ℝ) + 4) *
            (C (((2 * n : ℝ) + 5) / ((n : ℝ) + 4)) * initialPolynomial *
                gammaTransform (2 * (n + 1)) (narayanaPolynomial 1 (n + 1)) -
              C (((n : ℝ) + 1) / ((n : ℝ) + 4)) * quadraticFactor ^ 2 *
                gammaTransform (2 * n) (narayanaPolynomial 1 n)) =
            (C ((n : ℝ) + 4) *
                C (((2 * n : ℝ) + 5) / ((n : ℝ) + 4))) * initialPolynomial *
                gammaTransform (2 * (n + 1)) (narayanaPolynomial 1 (n + 1)) -
              (C ((n : ℝ) + 4) *
                C (((n : ℝ) + 1) / ((n : ℝ) + 4))) * quadraticFactor ^ 2 *
                gammaTransform (2 * n) (narayanaPolynomial 1 n) := by ring
        _ = C ((2 * n : ℝ) + 5) * initialPolynomial *
                gammaTransform (2 * (n + 1)) (narayanaPolynomial 1 (n + 1)) -
              C ((n : ℝ) + 1) * quadraticFactor ^ 2 *
                gammaTransform (2 * n) (narayanaPolynomial 1 n) := by
            rw [ha, hb]
        _ = C ((n : ℝ) + 4) *
            gammaTransform (2 * (n + 2)) (narayanaPolynomial 1 (n + 2)) :=
          hrec.symm

private theorem polynomial_lowering (n : ℕ) :
    C 2 * X * (X + 1) * (polynomial (n + 1)).derivative =
      C ((n : ℝ) + 1) *
        ((C 3 * X + 1) * polynomial (n + 1) +
          (X - 1) * quadraticFactor * polynomial n) := by
  let gamma := narayanaPolynomial 1 (n + 1)
  let delta := narayanaPolynomial 1 n
  have hdelta : delta.natDegree ≤ (2 * n) / 2 := by
    dsimp only [delta]
    rw [natDegree_narayanaPolynomial]
    simp
  have hsource :
      C ((n : ℝ) + 1) * gamma - C 2 * (X * gamma.derivative) =
        C ((n : ℝ) + 1) * (delta - X * delta) := by
    dsimp only [gamma, delta]
    calc
      C ((n : ℝ) + 1) * narayanaPolynomial 1 (n + 1) -
          C 2 * (X * (narayanaPolynomial 1 (n + 1)).derivative) =
          C ((n : ℝ) + 1) * narayanaPolynomial 1 (n + 1) -
            C 2 * X * (narayanaPolynomial 1 (n + 1)).derivative := by ring
      _ = C ((n : ℝ) + 1) * (1 - X) * narayanaPolynomial 1 n :=
        narayanaPolynomial_one_lowering n
      _ = C ((n : ℝ) + 1) *
          (narayanaPolynomial 1 n - X * narayanaPolynomial 1 n) := by ring
  have htransform := congrArg (gammaTransform (2 * (n + 1))) hsource
  rw [gammaTransform_sub, gammaTransform_C_mul, gammaTransform_C_mul,
    gammaTransform_C_mul, gammaTransform_sub] at htransform
  have hambient : 2 * (n + 1) = 2 * n + 2 := by lia
  rw [hambient, gammaTransform_pad_two hdelta,
    gammaTransform_X_mul_two (2 * n) delta] at htransform
  have heuler := gammaTransform_euler_derivative (2 * (n + 1)) gamma
  dsimp only [gamma, delta] at htransform heuler
  rw [← hambient] at htransform
  rw [← polynomial_eq_gammaTransform (n + 1),
    ← polynomial_eq_gammaTransform n] at htransform
  rw [← polynomial_eq_gammaTransform (n + 1)] at heuler
  dsimp only [quadraticFactor]
  norm_num [map_ofNat] at htransform heuler ⊢
  linear_combination 2 * heuler - (1 - X) * htransform

private theorem polynomial_derivative_recurrence_num (n : ℕ) :
    C ((n : ℝ) + 4) * polynomial (n + 2) =
      (-C 4 * X - C 6 * X ^ 2 - C 2 * X ^ 3) *
          (polynomial (n + 1)).derivative +
        (C ((4 * n : ℝ) + 7) + C ((13 * n : ℝ) + 22) * X +
          C ((5 * n : ℝ) + 8) * X ^ 2) * polynomial (n + 1) -
        C (3 * ((n : ℝ) + 1)) * quadraticFactor * polynomial n := by
  have hpure := gammaTransform_narayanaPolynomial_pure_recurrence n
  rw [← polynomial_eq_gammaTransform (n + 2),
    ← polynomial_eq_gammaTransform (n + 1),
    ← polynomial_eq_gammaTransform n] at hpure
  have hlower := polynomial_lowering n
  dsimp only [initialPolynomial, quadraticFactor] at hpure hlower ⊢
  norm_num [map_ofNat] at hpure hlower ⊢
  linear_combination hpure + (X + 2) * hlower

/-- The derivative recurrence for the A394446 rows. -/
theorem polynomial_add_two (n : ℕ) :
    polynomial (n + 2) =
      (C (-4 / ((n : ℝ) + 4)) * X +
          C (-6 / ((n : ℝ) + 4)) * X ^ 2 +
          C (-2 / ((n : ℝ) + 4)) * X ^ 3) *
          (polynomial (n + 1)).derivative +
        (C (((4 * n : ℝ) + 7) / ((n : ℝ) + 4)) +
          C (((13 * n : ℝ) + 22) / ((n : ℝ) + 4)) * X +
          C (((5 * n : ℝ) + 8) / ((n : ℝ) + 4)) * X ^ 2) *
          polynomial (n + 1) +
        C ((-3 * ((n : ℝ) + 1)) / ((n : ℝ) + 4)) * quadraticFactor *
          polynomial n := by
  have hden : (C ((n : ℝ) + 4) : ℝ[X]) ≠ 0 :=
    C_ne_zero.mpr (by positivity)
  have hC (a : ℝ) :
      C (a / ((n : ℝ) + 4)) =
        C (1 / ((n : ℝ) + 4)) * C a := by
    rw [← map_mul]
    congr 1
    ring
  have hinv : C ((n : ℝ) + 4) * C (1 / ((n : ℝ) + 4)) =
      (1 : ℝ[X]) := by
    rw [← map_mul]
    field_simp
    norm_num
  apply mul_left_cancel₀ hden
  rw [polynomial_derivative_recurrence_num]
  dsimp only [quadraticFactor]
  rw [hC (-4), hC (-6), hC (-2), hC ((4 * n : ℝ) + 7),
    hC ((13 * n : ℝ) + 22), hC ((5 * n : ℝ) + 8),
    hC (-3 * ((n : ℝ) + 1))]
  calc
    (-C 4 * X - C 6 * X ^ 2 - C 2 * X ^ 3) *
          (polynomial (n + 1)).derivative +
        (C ((4 * n : ℝ) + 7) + C ((13 * n : ℝ) + 22) * X +
          C ((5 * n : ℝ) + 8) * X ^ 2) * polynomial (n + 1) -
        C (3 * ((n : ℝ) + 1)) * (1 + X + X ^ 2) * polynomial n =
        (C ((n : ℝ) + 4) * C (1 / ((n : ℝ) + 4))) *
          ((-C 4 * X - C 6 * X ^ 2 - C 2 * X ^ 3) *
              (polynomial (n + 1)).derivative +
            (C ((4 * n : ℝ) + 7) + C ((13 * n : ℝ) + 22) * X +
              C ((5 * n : ℝ) + 8) * X ^ 2) * polynomial (n + 1) -
            C (3 * ((n : ℝ) + 1)) * (1 + X + X ^ 2) * polynomial n) := by
        rw [hinv, one_mul]
    _ = C ((n : ℝ) + 4) *
        ((C (1 / ((n : ℝ) + 4)) * C (-4) * X +
            C (1 / ((n : ℝ) + 4)) * C (-6) * X ^ 2 +
            C (1 / ((n : ℝ) + 4)) * C (-2) * X ^ 3) *
              (polynomial (n + 1)).derivative +
          (C (1 / ((n : ℝ) + 4)) * C ((4 * n : ℝ) + 7) +
            C (1 / ((n : ℝ) + 4)) * C ((13 * n : ℝ) + 22) * X +
            C (1 / ((n : ℝ) + 4)) * C ((5 * n : ℝ) + 8) * X ^ 2) *
              polynomial (n + 1) +
          C (1 / ((n : ℝ) + 4)) * C (-3 * ((n : ℝ) + 1)) *
              (1 + X + X ^ 2) * polynomial n) := by
        norm_num [map_ofNat]
        ring

/-- Every A394446 row polynomial is real-rooted. -/
theorem splits_polynomial (n : ℕ) : (polynomial n).Splits := by
  rw [polynomial_eq_gammaTransform]
  exact (isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
    (by rw [natDegree_narayanaPolynomial]; lia)
    (narayanaPolynomial_ne_zero 1 n)
    (splits_narayanaPolynomial 1 n)
    (hasNonnegCoeffs_narayanaPolynomial 1 n)).2

end RealRooted.Applications.OEIS.A394446
