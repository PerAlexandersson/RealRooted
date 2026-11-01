module

public import RealRooted.CombinatorialExamples.PathPowerClique
import RealRooted.DerivativeRecurrence.Interlacing
import RealRooted.MaWang.Weak.DerivativeSign
import RealRooted.Mathlib.Algebra.Polynomial.Derivative

/-!
# Degree-controlled derivative images of path polynomials

We package the first-order differential operator
`f ↦ (1 + N X) f - c X² f'` and apply it to weighted path-matching
polynomials.  The degree constraint `c * degree f ≤ N` is exactly what
makes every output coefficient nonnegative.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The degree-controlled derivative image
`(1 + N X) f - c X² f'`. -/
@[expose]
def degreeControlledDerivativeImage (N c : ℝ) (f : ℝ[X]) : ℝ[X] :=
  (1 + C N * X) * f - C c * X ^ 2 * f.derivative

/-- The coefficient of a degree-controlled derivative image. -/
@[simp]
theorem coeff_degreeControlledDerivativeImage_succ (N c : ℝ) (f : ℝ[X]) (k : ℕ) :
    (degreeControlledDerivativeImage N c f).coeff (k + 1) =
      f.coeff (k + 1) + (N - c * (k : ℝ)) * f.coeff k := by
  rw [show degreeControlledDerivativeImage N c f =
        (C 0 * X + C (-c) * X ^ 2) * f.derivative +
          (C 1 + C N * X) * f by
    unfold degreeControlledDerivativeImage
    rw [map_zero, map_neg, map_one]
    ring]
  rw [Polynomial.coeff_quadratic_derivative_add_linear_mul_succ]
  ring

/-- A degree-controlled derivative image of a nonzero PF polynomial is PF and
is preceded by its input in directed proper position. -/
theorem IsPFPolynomial.degreeControlledDerivativeImage_isPF_and_strictInterl
    {f : ℝ[X]} {N c : ℝ} (hf : IsPFPolynomial f) (hf0 : f ≠ 0)
    (hc : 0 ≤ c) (hN : c * f.natDegree ≤ N) :
    IsPFPolynomial (degreeControlledDerivativeImage N c f) ∧
      StrictInterl f (degreeControlledDerivativeImage N c f) := by
  let Q := degreeControlledDerivativeImage N c f
  have hfpos : HasPosLeadingCoeff f := hf.hasNonnegCoeffs.pos_leadingCoeff hf0
  have hQnn : HasNonnegCoeffs Q := by
    intro k
    rcases k with _ | k
    · change 0 ≤ (degreeControlledDerivativeImage N c f).coeff 0
      rw [coeff_zero_eq_eval_zero]
      simp only [degreeControlledDerivativeImage, eval_sub, eval_mul, eval_add, eval_one,
        eval_C, eval_X, mul_zero, add_zero, one_mul, eval_pow]
      norm_num
      simpa [coeff_zero_eq_eval_zero] using hf.hasNonnegCoeffs 0
    · rw [show Q.coeff (k + 1) =
          f.coeff (k + 1) + (N - c * (k : ℝ)) * f.coeff k by
        exact coeff_degreeControlledDerivativeImage_succ N c f k]
      by_cases hk : k ≤ f.natDegree
      · have hcast : (k : ℝ) ≤ f.natDegree := by exact_mod_cast hk
        exact add_nonneg (hf.hasNonnegCoeffs (k + 1))
          (mul_nonneg (by nlinarith) (hf.hasNonnegCoeffs k))
      · have hz : f.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
        rw [hz, mul_zero, add_zero]
        exact hf.hasNonnegCoeffs (k + 1)
  have hdegpos :
      (Q.natDegree = f.natDegree ∨ Q.natDegree = f.natDegree + 1) ∧
        HasPosLeadingCoeff Q := by
    let A : ℝ[X] := C 0 * X + C (-c) * X ^ 2
    let B : ℝ[X] := C (1 : ℝ) + C N * X
    have hA : A.natDegree ≤ 2 := by
      dsimp [A]
      compute_degree
    have hB : B.natDegree ≤ 1 := by
      dsimp [B]
      compute_degree
    have hAQ : A * f.derivative + B * f = Q := by
      simp [A, B, Q, degreeControlledDerivativeImage]
      ring
    by_cases ht : c * f.natDegree < N
    · have h := derivativeRecurrence_natDegree_eq_and_leadingCoeff_pos_step_of_cancel
          (f := f) (A := A) (B := B)
          (d := f.natDegree) (d' := f.natDegree + 1) (m := 1)
          (by norm_num) hA hB hf.hasNonnegCoeffs rfl hfpos
          (Or.inl ⟨by simp [A, B, coeff_one]; nlinarith, rfl⟩)
      rw [hAQ] at h
      exact ⟨Or.inr h.1, h.2⟩
    · have heq : c * f.natDegree = N := by nlinarith
      have h := derivativeRecurrence_natDegree_eq_and_leadingCoeff_pos_step_of_cancel
          (f := f) (A := A) (B := B)
          (d := f.natDegree) (d' := f.natDegree) (m := 1)
          (by norm_num) hA hB hf.hasNonnegCoeffs rfl hfpos
          (Or.inr ⟨by simp [A, B, coeff_one, heq], by simp, by simp [A, hc],
            by simp [A, B, coeff_one]⟩)
      rw [hAQ] at h
      exact ⟨Or.inl h.1, h.2⟩
  have hQpos : HasPosLeadingCoeff Q := hdegpos.2
  have hinter : StrictInterl f Q := by
    by_cases hdeg0 : f.natDegree = 0
    · apply StrictInterl.of_natDegree_eq_zero_left hf0 hdeg0 hQpos.ne_zero
      rcases hdegpos.1 with hdeg | hdeg <;> lia
    · apply derivativeRecurrence_strictInterl_step
        (f := f) (Q := Q) (A := -C c * X ^ 2) (B := 1 + C N * X)
      · simp [Q, degreeControlledDerivativeImage, sub_eq_add_neg]
        ring
      · exact (hf.ne_zero_and_splits hf0).2
      · exact hdeg0
      · exact hfpos
      · exact hQpos
      · rcases hdegpos.1 with hdeg | hdeg <;> lia
      · rcases hdegpos.1 with hdeg | hdeg <;> lia
      · intro r _
        simp only [neg_mul, eval_neg, eval_mul, eval_C, eval_pow, eval_X,
          Left.neg_nonpos_iff]
        positivity
  exact ⟨IsPFPolynomial.of_realRooted_nonneg hQnn hinter.2.1.2, hinter⟩

/-- The weighted path-matching polynomial
`Σ k, choose (n - k) k * v^k * X^k`. -/
@[expose]
def weightedPathPolynomial (v : ℝ) (n : ℕ) : ℝ[X] :=
  (pathPowerCliquePolynomial 2 n).comp (C v * X)

/-- Coefficients of the weighted path-matching polynomial. -/
@[simp]
theorem coeff_weightedPathPolynomial (v : ℝ) (n k : ℕ) :
    (weightedPathPolynomial v n).coeff k = ((n - k).choose k : ℕ) * v ^ k := by
  rw [weightedPathPolynomial, Polynomial.comp_C_mul_X_coeff,
    coeff_pathPowerCliquePolynomial]
  norm_num

/-- The weighted path rows start with the constant polynomial one. -/
@[simp]
theorem weightedPathPolynomial_zero (v : ℝ) : weightedPathPolynomial v 0 = 1 := by
  norm_num [weightedPathPolynomial, pathPowerCliquePolynomial, Finset.sum_range_succ]

/-- The second weighted path row is also the constant polynomial one. -/
@[simp]
theorem weightedPathPolynomial_one (v : ℝ) : weightedPathPolynomial v 1 = 1 := by
  norm_num [weightedPathPolynomial, pathPowerCliquePolynomial, Finset.sum_range_succ]

/-- Weighted path-matching polynomials satisfy their ordinary second-order recurrence. -/
theorem weightedPathPolynomial_add_two (v : ℝ) (n : ℕ) :
    weightedPathPolynomial v (n + 2) =
      weightedPathPolynomial v (n + 1) + C v * X * weightedPathPolynomial v n := by
  have h := congrArg (fun p : ℝ[X] ↦ p.comp (C v * X))
    (pathPowerCliquePolynomial_add_lag 2 n (by norm_num))
  simpa [weightedPathPolynomial, Polynomial.add_comp, Polynomial.mul_comp] using h

/-- A positive edge weight gives the expected degree `⌊n / 2⌋`. -/
theorem weightedPathPolynomial_natDegree (v : ℝ) (n : ℕ) (hv : 0 < v) :
    (weightedPathPolynomial v n).natDegree = n / 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_weightedPathPolynomial, Nat.choose_eq_zero_of_lt]
    · simp
    · lia
  · rw [coeff_weightedPathPolynomial]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by lia)))
      (pow_ne_zero _ hv.ne')

/-- Positive weighted path-matching polynomials are PF. -/
theorem isPFPolynomial_weightedPathPolynomial (v : ℝ) (n : ℕ) (hv : 0 < v) :
    IsPFPolynomial (weightedPathPolynomial v n) := by
  unfold weightedPathPolynomial
  simpa using (isPFPolynomial_pathPowerCliquePolynomial 2 n).comp_C_mul_X_add_C hv le_rfl

/-- The derivative image of the `n`th weighted path row with affine parameter `a n + b`. -/
@[expose]
def pathDerivativeImage (a b c v : ℝ) (n : ℕ) : ℝ[X] :=
  degreeControlledDerivativeImage (a * n + b) c (weightedPathPolynomial v n)

/-- In the parameter region `b ≥ 0`, `2a ≥ c`, every path derivative image is PF
and is preceded by its path row in directed proper position. -/
theorem pathDerivativeImage_isPF_and_strictInterl
    {a b c v : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) (hac : c ≤ 2 * a)
    (hv : 0 < v) (n : ℕ) :
    IsPFPolynomial (pathDerivativeImage a b c v n) ∧
      StrictInterl (weightedPathPolynomial v n) (pathDerivativeImage a b c v n) := by
  have hpf := isPFPolynomial_weightedPathPolynomial v n hv
  apply hpf.degreeControlledDerivativeImage_isPF_and_strictInterl
  · exact hpf.ne_zero_and_splits (by
      intro hzero
      have := congrArg (fun p : ℝ[X] ↦ p.coeff 0) hzero
      simp at this) |>.1
  · exact hc
  · rw [weightedPathPolynomial_natDegree v n hv]
    have ha : 0 ≤ a := by nlinarith
    have hhalfNat : 2 * (n / 2) ≤ n := by
      simpa [mul_comm] using Nat.div_mul_le_self n 2
    have hhalf : (2 : ℝ) * (n / 2 : ℕ) ≤ n := by exact_mod_cast hhalfNat
    nlinarith [mul_nonneg ha (Nat.cast_nonneg n)]

/-- Every affine-parameter path derivative family satisfies the common
fourth-order recurrence, without sign restrictions on its parameters. -/
theorem pathDerivativeImage_add_four (a b c v : ℝ) (n : ℕ) :
    pathDerivativeImage a b c v (n + 4) =
      2 * pathDerivativeImage a b c v (n + 3) +
        (2 * C v * X - 1) * pathDerivativeImage a b c v (n + 2) -
          2 * C v * X * pathDerivativeImage a b c v (n + 1) -
            C (v ^ 2) * X ^ 2 * pathDerivativeImage a b c v n := by
  simp only [pathDerivativeImage, degreeControlledDerivativeImage]
  rw [show n + 4 = (n + 2) + 2 by lia,
    weightedPathPolynomial_add_two v (n + 2)]
  rw [show n + 3 = (n + 1) + 2 by lia,
    weightedPathPolynomial_add_two v (n + 1)]
  rw [show n + 2 = n + 2 by rfl, weightedPathPolynomial_add_two v n]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X, zero_mul, zero_add]
  push_cast
  simp only [map_add, map_mul, map_pow, map_natCast, map_ofNat]
  norm_num
  ring

/-- The first coefficient beyond the degree of an even path row detects the
sharp inequality `c ≤ 2a`. -/
theorem coeff_pathDerivativeImage_even_top (a b c v : ℝ) (m : ℕ) :
    (pathDerivativeImage a b c v (2 * m)).coeff (m + 1) =
      ((2 * a - c) * m + b) * v ^ m := by
  rw [pathDerivativeImage, coeff_degreeControlledDerivativeImage_succ,
    coeff_weightedPathPolynomial, coeff_weightedPathPolynomial]
  have hz : (2 * m - (m + 1)).choose (m + 1) = 0 :=
    Nat.choose_eq_zero_of_lt (by lia)
  have ho : (2 * m - m).choose m = 1 := by
    rw [show 2 * m - m = m by lia, Nat.choose_self]
  rw [hz, ho]
  norm_num only [Nat.cast_zero, Nat.cast_one, zero_mul, zero_add, one_mul]
  push_cast
  ring

/-- For positive path weight and nonnegative derivative parameter, every path
derivative image is PF exactly in the region `b ≥ 0`, `c ≤ 2a`. -/
theorem forall_pathDerivativeImage_isPF_iff
    {a b c v : ℝ} (hc : 0 ≤ c) (hv : 0 < v) :
    (∀ n, IsPFPolynomial (pathDerivativeImage a b c v n)) ↔
      0 ≤ b ∧ c ≤ 2 * a := by
  constructor
  · intro h
    have hbcoeff := (h 0).hasNonnegCoeffs 1
    rw [show 1 = 0 + 1 by rfl, coeff_pathDerivativeImage_even_top a b c v 0] at hbcoeff
    norm_num at hbcoeff
    refine ⟨hbcoeff, ?_⟩
    by_contra hac
    have hdelta : 0 < c - 2 * a := by linarith
    obtain ⟨m : ℕ, hm⟩ := exists_nat_gt (b / (c - 2 * a))
    have hneg : (2 * a - c) * (m : ℝ) + b < 0 := by
      have hmul := (div_lt_iff₀ hdelta).mp hm
      nlinarith
    have hnonneg := (h (2 * m)).hasNonnegCoeffs (m + 1)
    rw [coeff_pathDerivativeImage_even_top] at hnonneg
    nlinarith [pow_pos hv m]
  · rintro ⟨hb, hac⟩ n
    exact (pathDerivativeImage_isPF_and_strictInterl hc hb hac hv n).1

/-- With zero edge weight, every weighted path row is the constant one. -/
@[simp]
theorem weightedPathPolynomial_zero_weight (n : ℕ) : weightedPathPolynomial 0 n = 1 := by
  ext k
  rw [coeff_weightedPathPolynomial]
  rcases k with _ | k <;> simp [Polynomial.coeff_one]

/-- At zero edge weight the derivative parameter disappears. -/
@[simp]
theorem pathDerivativeImage_zero_weight (a b c : ℝ) (n : ℕ) :
    pathDerivativeImage a b c 0 n = 1 + C (a * n + b) * X := by
  simp [pathDerivativeImage, degreeControlledDerivativeImage]

/-- At zero edge weight, every path derivative image is PF exactly when
`a` and `b` are nonnegative; the derivative parameter is irrelevant. -/
theorem forall_pathDerivativeImage_zero_weight_isPF_iff (a b c : ℝ) :
    (∀ n, IsPFPolynomial (pathDerivativeImage a b c 0 n)) ↔ 0 ≤ a ∧ 0 ≤ b := by
  constructor
  · intro h
    have hb : 0 ≤ b := by
      simpa [Polynomial.coeff_one] using (h 0).hasNonnegCoeffs 1
    refine ⟨?_, hb⟩
    by_contra ha
    have hapos : 0 < -a := by linarith
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (b / (-a))
    have hneg : a * (n : ℝ) + b < 0 := by
      have hmul := (div_lt_iff₀ hapos).mp hn
      nlinarith
    have hcoeff : 0 ≤ a * (n : ℝ) + b := by
      simpa [Polynomial.coeff_one] using (h n).hasNonnegCoeffs 1
    linarith
  · rintro ⟨ha, hb⟩ n
    rw [pathDerivativeImage_zero_weight]
    apply IsPFPolynomial.of_realRooted_nonneg
    · exact hasNonnegCoeffs_one.add
        ((hasNonnegCoeffs_C (by positivity)).mul hasNonnegCoeffs_X)
    · exact Polynomial.Splits.of_natDegree_le_one (by compute_degree)

/-- The weighted path row at index two. -/
private theorem weightedPathPolynomial_two (v : ℝ) :
    weightedPathPolynomial v 2 = 1 + C v * X := by
  norm_num [weightedPathPolynomial, pathPowerCliquePolynomial, Finset.sum_range_succ]

/-- The weighted path row at index three. -/
private theorem weightedPathPolynomial_three (v : ℝ) :
    weightedPathPolynomial v 3 = 1 + C (2 * v) * X := by
  norm_num [weightedPathPolynomial, pathPowerCliquePolynomial, Finset.sum_range_succ]
  simp only [Polynomial.C_ofNat]
  ring

/-- The zeroth initial row of the path derivative family. -/
@[simp]
theorem pathDerivativeImage_zero (a b c v : ℝ) :
    pathDerivativeImage a b c v 0 = 1 + C b * X := by
  simp [pathDerivativeImage, degreeControlledDerivativeImage]

/-- The first initial row of the path derivative family. -/
@[simp]
theorem pathDerivativeImage_one (a b c v : ℝ) :
    pathDerivativeImage a b c v 1 = 1 + C (a + b) * X := by
  simp [pathDerivativeImage, degreeControlledDerivativeImage]

/-- The second initial row of the path derivative family. -/
@[simp]
theorem pathDerivativeImage_two (a b c v : ℝ) :
    pathDerivativeImage a b c v 2 =
      1 + C (v + 2 * a + b) * X + C ((2 * a + b - c) * v) * X ^ 2 := by
  rw [pathDerivativeImage, degreeControlledDerivativeImage, weightedPathPolynomial_two]
  simp only [derivative_one, derivative_mul, derivative_C, derivative_X, zero_add, zero_mul,
    map_add, map_mul, map_sub, map_ofNat]
  rw [map_natCast C 2]
  ring

/-- The third initial row of the path derivative family. -/
@[simp]
theorem pathDerivativeImage_three (a b c v : ℝ) :
    pathDerivativeImage a b c v 3 =
      1 + C (2 * v + 3 * a + b) * X + C (2 * v * (3 * a + b - c)) * X ^ 2 := by
  rw [pathDerivativeImage, degreeControlledDerivativeImage, weightedPathPolynomial_three]
  simp only [derivative_one, derivative_mul, derivative_C, derivative_X, zero_add, zero_mul,
    mul_zero, map_add, map_mul, map_sub, map_ofNat, Polynomial.derivative_ofNat]
  rw [map_natCast C 3]
  ring

/-- A polynomial sequence with the four displayed seeds and the common
fourth-order recurrence is the corresponding path derivative family. -/
theorem eq_pathDerivativeImage_of_seeds_and_recurrence
    {P : ℕ → ℝ[X]} (a b c v : ℝ)
    (h0 : P 0 = 1 + C b * X)
    (h1 : P 1 = 1 + C (a + b) * X)
    (h2 : P 2 =
      1 + C (v + 2 * a + b) * X + C ((2 * a + b - c) * v) * X ^ 2)
    (h3 : P 3 =
      1 + C (2 * v + 3 * a + b) * X + C (2 * v * (3 * a + b - c)) * X ^ 2)
    (hrec : ∀ n,
      P (n + 4) = 2 * P (n + 3) + (2 * C v * X - 1) * P (n + 2) -
        2 * C v * X * P (n + 1) - C (v ^ 2) * X ^ 2 * P n) :
    P = pathDerivativeImage a b c v := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa using h0
    | 1 => simpa using h1
    | 2 => simpa using h2
    | 3 => simpa using h3
    | k + 4 =>
        rw [hrec, pathDerivativeImage_add_four, ih (k + 3) (by lia),
          ih (k + 2) (by lia), ih (k + 1) (by lia), ih k (by lia)]

end RealRooted
