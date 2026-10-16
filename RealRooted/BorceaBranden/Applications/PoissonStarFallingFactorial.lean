module

public import RealRooted.BorceaBranden.Applications.UnivariatePoissonStar
public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform

/-!
# Remaining finite consequences of the univariate Poisson product

We prove that `star_c` with a nonnegative parameter and an affine left factor preserves
Pólya-frequency polynomials and interlaces its input, and we introduce the step-`c`
falling-factorial transform, which conjugates the affine Poisson recurrence to ordinary
multiplication (issue #1494).
-/

@[expose] public section

open Polynomial
open scoped BigOperators

namespace RealRooted.Poisson

noncomputable section

private theorem derivative_interl_self {p : ℝ[X]} (hp : IsPFPolynomial p) :
    Interl p.derivative p := by
  by_cases hp0 : p = 0
  · rw [hp0, derivative_zero]
    exact interl_zero_left 0
  have hps := hp.ne_zero_and_splits hp0
  by_cases hdeg0 : p.natDegree = 0
  · rw [Polynomial.derivative_eq_zero.mpr hdeg0]
    exact interl_zero_left p
  by_cases hdeg1 : p.natDegree = 1
  · have hder_ne : p.derivative ≠ 0 :=
      Polynomial.derivative_ne_zero.mpr hdeg0
    have hder_deg0 : p.derivative.natDegree = 0 := by
      rw [p.natDegree_derivative, hdeg1]
    exact
      (StrictInterl.of_degree_zero_right_of_degree_one hder_ne
        (Polynomial.Splits.of_natDegree_eq_zero hder_deg0) hp0 hps.2
        hder_deg0 hdeg1).toInterl
  · exact (derivative_interlaces_of_natDegree_ne_zero hps.2 hdeg0).toStrictInterl.toInterl

private def affinePFStep (r : ℝ) (D F : ℝ[X]) : ℝ[X] :=
  (X + C r) * F + X * D

private theorem affinePFStep_isPF {D F : ℝ[X]} {r : ℝ}
    (hr : 0 ≤ r) (hDF : Interl D F)
    (hD : IsPFPolynomial D) (hF : IsPFPolynomial F) :
    IsPFPolynomial (affinePFStep r D F) := by
  have hX : Interl F (X * D) :=
    interl_mul_X_of_interl hDF hD.hasNonnegCoeffs hF.hasNonnegCoeffs
  have hXF : Interl F (X * F) :=
    interl_mul_X_of_interl hF.interl_self hF.hasNonnegCoeffs hF.hasNonnegCoeffs
  have hcomboX : Interl F (X * D + X * F) := by
    simpa using interl_nonneg_combo_right_of_common_left_of_nonneg hX hXF
      hD.X_mul.hasNonnegCoeffs hF.X_mul.hasNonnegCoeffs zero_le_one zero_le_one
  have hcomboXnn : HasNonnegCoeffs (X * D + X * F) :=
    hD.X_mul.hasNonnegCoeffs.add hF.X_mul.hasNonnegCoeffs
  have hcombo : Interl F ((X * D + X * F) + C r * F) := by
    simpa using interl_nonneg_combo_right_of_common_left_of_nonneg hcomboX
      hF.interl_self hcomboXnn hF.hasNonnegCoeffs zero_le_one hr
  have hinterl : Interl F (affinePFStep r D F) := by
    unfold affinePFStep
    convert hcombo using 1
    ring
  have hnn : HasNonnegCoeffs (affinePFStep r D F) := by
    unfold affinePFStep
    exact ((isPFPolynomial_X_add_C hr).mul hF).hasNonnegCoeffs.add
      hD.X_mul.hasNonnegCoeffs
  by_cases hF0 : F = 0
  · rw [affinePFStep, hF0, mul_zero, zero_add]
    exact hD.X_mul
  rcases hinterl with hleft0 | hright0 | hstrict
  · exact (hF0 hleft0).elim
  · simpa [hright0] using IsPFPolynomial.zero
  · exact IsPFPolynomial.of_realRooted_nonneg hnn hstrict.2.1.2

/-- A nonnegative affine fixed factor preserves the PF cone when the Poisson
parameter is nonnegative. -/
theorem preservesPF_affine_of_nonneg {c a b : ℝ} (hc : 0 ≤ c)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    PreservesPF c (C a + C b * X) := by
  intro f hf
  by_cases hb0 : b = 0
  · subst b
    simpa using preservesPF_constant c a ha f hf
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  let D : ℝ[X] := C c * f.derivative
  have hD : IsPFPolynomial D :=
    (IsPFPolynomial.of_C_nonneg hc).mul hf.derivative
  have hDf : Interl D f := by
    exact (derivative_interl_self hf).C_mul_left_of_nonneg hc
  have hstep : IsPFPolynomial (affinePFStep (a / b) D f) :=
    affinePFStep_isPF (div_nonneg ha hb) hDf hD hf
  have hscale : IsPFPolynomial (C b * affinePFStep (a / b) D f) :=
    (IsPFPolynomial.of_C_nonneg hb).mul hstep
  have hratio : C b * C (a / b) = (C a : ℝ[X]) := by
    rw [← map_mul]
    congr 1
    field_simp
  have heq : starC c (C a + C b * X) f =
      C b * affinePFStep (a / b) D f := by
    rw [starC_linear_factor_left]
    dsimp [D, affinePFStep]
    calc
      (C a + C b * X) * f + C (c * b) * X * f.derivative =
          (C b * C (a / b)) * f + C b * X * f +
            C b * X * (C c * f.derivative) := by
              rw [hratio]
              simp only [map_mul]
              ring
      _ = C b * ((X + C (a / b)) * f + X * (C c * f.derivative)) := by
        ring
  rw [heq]
  exact hscale

/-- A PF polynomial precedes its image under a nonnegative affine Poisson
factor. -/
theorem interl_starC_affine_self_of_nonneg {c a b : ℝ} (hc : 0 ≤ c)
    (ha : 0 ≤ a) (hb : 0 ≤ b) {f : ℝ[X]} (hf : IsPFPolynomial f) :
    Interl f (starC c (C a + C b * X) f) := by
  let D : ℝ[X] := C c * f.derivative
  have hD : IsPFPolynomial D :=
    (IsPFPolynomial.of_C_nonneg hc).mul hf.derivative
  have hDf : Interl D f :=
    (derivative_interl_self hf).C_mul_left_of_nonneg hc
  have hXD : Interl f (X * D) :=
    interl_mul_X_of_interl hDf hD.hasNonnegCoeffs hf.hasNonnegCoeffs
  have hXF : Interl f (X * f) :=
    interl_mul_X_of_interl hf.interl_self hf.hasNonnegCoeffs hf.hasNonnegCoeffs
  have hsum : Interl f (X * D + X * f) := by
    simpa using interl_nonneg_combo_right_of_common_left_of_nonneg hXD hXF
      hD.X_mul.hasNonnegCoeffs hf.X_mul.hasNonnegCoeffs zero_le_one zero_le_one
  have hsumnn : HasNonnegCoeffs (X * D + X * f) :=
    hD.X_mul.hasNonnegCoeffs.add hf.X_mul.hasNonnegCoeffs
  have hcombo : Interl f (C b * (X * D + X * f) + C a * f) :=
    interl_nonneg_combo_right_of_common_left_of_nonneg hsum hf.interl_self
      hsumnn hf.hasNonnegCoeffs hb ha
  rw [starC_linear_factor_left]
  convert hcombo using 1
  dsimp [D]
  simp only [map_mul]
  ring

/-- The step-`c` falling-factorial polynomial
`X (X-c) ... (X-(n-1)c)`. -/
def stepFallingFactorial (c : ℝ) (n : ℕ) : ℝ[X] :=
  ∏ k ∈ Finset.range n, (X - C (c * k))

/-- Appending the last factor gives the successor recurrence for the
step-`c` falling factorial. -/
theorem stepFallingFactorial_succ (c : ℝ) (n : ℕ) :
    stepFallingFactorial c (n + 1) =
      (X - C (c * n)) * stepFallingFactorial c n := by
  simp only [stepFallingFactorial, Finset.prod_range_succ]
  ring

/-- Every step-`c` falling factorial is monic. -/
theorem stepFallingFactorial_monic (c : ℝ) (n : ℕ) :
    (stepFallingFactorial c n).Monic := by
  unfold stepFallingFactorial
  exact monic_prod_of_monic _ _ fun k _ => monic_X_sub_C _

/-- The `n`th step-`c` falling factorial has degree exactly `n`. -/
theorem natDegree_stepFallingFactorial (c : ℝ) (n : ℕ) :
    (stepFallingFactorial c n).natDegree = n := by
  unfold stepFallingFactorial
  rw [natDegree_prod_of_monic _ _ fun k _ => monic_X_sub_C _]
  calc
    ∑ k ∈ Finset.range n, (X - C (c * k)).natDegree =
        ∑ _k ∈ Finset.range n, 1 := by
          apply Finset.sum_congr rfl
          intro k hk
          exact natDegree_X_sub_C _
    _ = n := by simp

/-- The step-`c` falling-factorial basis transform. -/
def fallingFactorialTransform (c : ℝ) (p : ℝ[X]) : ℝ[X] :=
  Polynomial.basisTransform (stepFallingFactorial c) p

/-- The falling-factorial transform is additive. -/
theorem fallingFactorialTransform_add (c : ℝ) (p q : ℝ[X]) :
    fallingFactorialTransform c (p + q) =
      fallingFactorialTransform c p + fallingFactorialTransform c q := by
  exact Polynomial.basisTransform_add (stepFallingFactorial c) p q

/-- The falling-factorial transform commutes with real scalar multiplication. -/
theorem fallingFactorialTransform_C_mul (c a : ℝ) (p : ℝ[X]) :
    fallingFactorialTransform c (C a * p) =
      C a * fallingFactorialTransform c p := by
  rw [show C a * p = a • p by rw [Polynomial.smul_eq_C_mul]]
  exact Polynomial.basisTransform_smul (stepFallingFactorial c) a p

/-- The falling-factorial transform sends `X^n` to the `n`th step-`c`
falling factorial. -/
@[simp] theorem fallingFactorialTransform_X_pow (c : ℝ) (n : ℕ) :
    fallingFactorialTransform c (X ^ n) = stepFallingFactorial c n := by
  exact Polynomial.basisTransform_X_pow (stepFallingFactorial c) n

/-- The step-`c` falling-factorial transform is injective. -/
theorem fallingFactorialTransform_injective (c : ℝ) :
    Function.Injective (fallingFactorialTransform c) := by
  apply Polynomial.basisTransform_injective_of_natDegree_eq
  · exact natDegree_stepFallingFactorial c
  · intro n
    exact (stepFallingFactorial_monic c n).ne_zero

/-- Multiplication by `X` before the falling-factorial transform satisfies
the triangular step-`c` recurrence. -/
theorem fallingFactorialTransform_X_mul (c : ℝ) (p : ℝ[X]) :
    fallingFactorialTransform c (X * p) =
      X * fallingFactorialTransform c p -
        C c * fallingFactorialTransform c (X * p.derivative) := by
  have hsucc : ∀ n : ℕ, stepFallingFactorial c (n + 1) =
      X * stepFallingFactorial c n +
        C (-c) * (C (n : ℝ) * stepFallingFactorial c n) +
          0 * (stepFallingFactorial c n).derivative := by
    intro n
    rw [stepFallingFactorial_succ]
    simp only [map_mul, map_neg, zero_mul, add_zero]
    ring
  simpa only [fallingFactorialTransform, C_neg, neg_mul, zero_mul, add_zero,
    sub_eq_add_neg]
    using Polynomial.basisTransform_X_mul_of_succ_index_derivative
      (stepFallingFactorial c) X (C (-c)) 0 hsucc p

/-- The falling-factorial transform conjugates Poisson multiplication by `X`
to ordinary multiplication by `X`. -/
theorem fallingFactorialTransform_starC_X (c : ℝ) (p : ℝ[X]) :
    fallingFactorialTransform c (starC c X p) =
      X * fallingFactorialTransform c p := by
  rw [starC_comm, starC_X_right]
  rw [show X * (p + C c * p.derivative) =
      X * p + C c * (X * p.derivative) by ring]
  rw [fallingFactorialTransform_add, fallingFactorialTransform_X_mul,
    fallingFactorialTransform_C_mul]
  ring

/-- The falling-factorial transform turns Poisson multiplication by an affine
factor into ordinary multiplication by that factor. -/
theorem fallingFactorialTransform_starC_affine (c a b : ℝ) (p : ℝ[X]) :
    fallingFactorialTransform c (starC c (C a + C b * X) p) =
      (C a + C b * X) * fallingFactorialTransform c p := by
  rw [starC_add_left, fallingFactorialTransform_add]
  rw [show C a = C a * 1 by simp, starC_C_mul_left, starC_one_left]
  rw [starC_C_mul_left, fallingFactorialTransform_C_mul,
    fallingFactorialTransform_C_mul, fallingFactorialTransform_starC_X]
  ring

/-- Every row of a nonnegative affine Poisson recurrence is PF, and each row
precedes its successor. -/
theorem isPFPolynomial_and_interl_of_poisson_affine_recurrence
    {c : ℝ} {a b : ℕ → ℝ} {P : ℕ → ℝ[X]}
    (hc : 0 ≤ c) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hP0 : IsPFPolynomial (P 0))
    (hrec : ∀ n, P (n + 1) =
      (C (a n) + C (b n) * X) * P n +
        C (c * b n) * X * (P n).derivative) (n : ℕ) :
    IsPFPolynomial (P n) ∧ Interl (P n) (P (n + 1)) := by
  have hpf : ∀ m, IsPFPolynomial (P m) := by
    intro m
    induction m with
    | zero => exact hP0
    | succ m ih =>
        rw [hrec m, ← starC_linear_factor_left]
        exact preservesPF_affine_of_nonneg hc (ha m) (hb m) (P m) ih
  exact ⟨hpf n, by
    rw [hrec n, ← starC_linear_factor_left]
    exact interl_starC_affine_self_of_nonneg hc (ha n) (hb n) (hpf n)⟩

/-- The falling-factorial transform turns a nonnegative affine Poisson
recurrence into the ordinary product of its affine factors.  The algebraic
identity itself does not require sign assumptions. -/
theorem fallingFactorialTransform_poisson_affine_recurrence
    {c : ℝ} {a b : ℕ → ℝ} {P : ℕ → ℝ[X]}
    (hP0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C (a n) + C (b n) * X) * P n +
        C (c * b n) * X * (P n).derivative) (n : ℕ) :
    fallingFactorialTransform c (P n) =
      ∏ k ∈ Finset.range n, (C (a k) + C (b k) * X) := by
  induction n with
  | zero =>
      rw [hP0]
      simpa only [pow_zero, stepFallingFactorial, Finset.range_zero,
        Finset.prod_empty]
        using fallingFactorialTransform_X_pow c 0
  | succ n ih =>
      rw [hrec n, ← starC_linear_factor_left,
        fallingFactorialTransform_starC_affine, ih, Finset.prod_range_succ]
      ring


/-! ## Full multiplicativity and associativity -/

/-- The falling-factorial transform fixes the constant polynomial one. -/
theorem fallingFactorialTransform_one (c : ℝ) :
    fallingFactorialTransform c 1 = 1 := by
  simpa only [pow_zero, stepFallingFactorial, Finset.range_zero, Finset.prod_empty]
    using fallingFactorialTransform_X_pow c 0

private theorem shift_coeff (c : ℝ) (k : ℕ) :
    C (c ^ (k + 1) / ((k + 1).factorial : ℝ)) * C ((k + 1 : ℕ) : ℝ) =
      C c * C (c ^ k / (k.factorial : ℝ)) := by
  rw [← C_mul, ← C_mul]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Leibniz rule for `starC` in the left factor. -/
theorem starC_X_mul_left (c : ℝ) (f g : ℝ[X]) :
    starC c (X * f) g = X * starC c f g + C c * X * starC c f g.derivative := by
  obtain ⟨M, hM⟩ : ∃ M, M = f.natDegree + 1 := ⟨_, rfl⟩
  have hXf : (X * f).natDegree < M + 1 :=
    natDegree_mul_le.trans_lt (by rw [natDegree_X]; lia)
  rw [starC_eq_sum_range hXf, starC_eq_sum_range (N := M + 1) (by lia),
    starC_eq_sum_range (N := M) (by lia), Finset.mul_sum, Finset.mul_sum,
    Finset.sum_range_succ', Finset.sum_range_succ', add_right_comm,
    ← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm X f, iterate_derivative_mul_X, nsmul_eq_mul,
      Nat.add_sub_cancel, ← map_natCast C (k + 1)]
    simp only [Function.iterate_succ_apply]
    have h := shift_coeff c k
    linear_combination (X ^ (k + 1) * (derivative^[k]) f *
      (derivative^[k]) (derivative g)) * h
  · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_one,
      Function.iterate_zero_apply]
    ring

/-- Derivative of a Poisson product. -/
theorem derivative_starC (c : ℝ) (f g : ℝ[X]) :
    derivative (starC c f g) =
      starC c f.derivative g + starC c f g.derivative +
        C c * starC c f.derivative g.derivative := by
  obtain ⟨M, hM⟩ : ∃ M, M = f.natDegree + 1 := ⟨_, rfl⟩
  have hf' : f.derivative.natDegree < M :=
    (natDegree_derivative_le f).trans_lt (by lia)
  rw [starC_eq_sum_range (N := M + 1) (by lia),
    starC_eq_sum_range (N := M + 1) (hf'.trans (by lia)),
    starC_eq_sum_range (N := M + 1) (by lia),
    starC_eq_sum_range (N := M) hf', derivative_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_range_succ', Finset.sum_range_succ',
    add_right_comm, ← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    simp only [derivative_mul, derivative_C, derivative_X_pow, zero_mul, zero_add,
      Nat.add_sub_cancel, ← Function.iterate_succ_apply' derivative,
      Function.iterate_succ_apply]
    have h := shift_coeff c k
    linear_combination (X ^ k * (derivative^[k]) (derivative f) *
      (derivative^[k]) (derivative g)) * h
  · simp only [derivative_mul, pow_zero, derivative_one,
      Nat.factorial_zero, Nat.cast_one, div_one, map_one,
      Function.iterate_zero_apply]
    ring

/-- Inductive step: multiplicativity passes from `f` to `X * f` whenever
`X f' = r f` (true for monomials). -/
private theorem fallingFactorialTransform_starC_X_mul (c r : ℝ) {f : ℝ[X]}
    (hXf' : X * f.derivative = C r * f)
    (ih : ∀ g, fallingFactorialTransform c (starC c f g) =
      fallingFactorialTransform c f * fallingFactorialTransform c g) (g : ℝ[X]) :
    fallingFactorialTransform c (starC c (X * f) g) =
      fallingFactorialTransform c (X * f) * fallingFactorialTransform c g := by
  -- `X (f ⋆ g)' = (X f') ⋆ g + X (f ⋆ g')`
  have hkey : X * derivative (starC c f g) =
      starC c (X * f.derivative) g + X * starC c f g.derivative := by
    rw [derivative_starC, starC_X_mul_left]
    ring
  have hT : fallingFactorialTransform c (X * starC c f g.derivative) =
      fallingFactorialTransform c (X * derivative (starC c f g)) -
        fallingFactorialTransform c (starC c (X * f.derivative) g) := by
    rw [hkey, fallingFactorialTransform_add]; ring
  rw [starC_X_mul_left, fallingFactorialTransform_add, mul_assoc,
    fallingFactorialTransform_C_mul, fallingFactorialTransform_X_mul, hT,
    fallingFactorialTransform_X_mul c f, hXf', starC_C_mul_left c r f g,
    fallingFactorialTransform_C_mul, fallingFactorialTransform_C_mul, ih]
  ring

/-- The falling-factorial transform is multiplicative for `starC`. -/
theorem fallingFactorialTransform_starC (c : ℝ) (f g : ℝ[X]) :
    fallingFactorialTransform c (starC c f g) =
      fallingFactorialTransform c f * fallingFactorialTransform c g := by
  induction f using Polynomial.induction_on generalizing g with
  | C a =>
      rw [← mul_one (C a), starC_C_mul_left, starC_one_left,
        fallingFactorialTransform_C_mul, fallingFactorialTransform_C_mul,
        fallingFactorialTransform_one, mul_one]
  | add p q hp hq =>
      rw [starC_add_left, fallingFactorialTransform_add, fallingFactorialTransform_add,
        hp, hq, add_mul]
  | monomial n a ih =>
      have hXf' : X * (C a * X ^ n).derivative = C (n : ℝ) * (C a * X ^ n) := by
        rw [derivative_C_mul, derivative_X_pow]
        cases n with
        | zero => simp
        | succ n => rw [Nat.add_sub_cancel]; ring
      rw [show C a * X ^ (n + 1) = X * (C a * X ^ n) by ring]
      exact fallingFactorialTransform_starC_X_mul c n hXf' ih g

/-- Associativity of `starC`, by injectivity of the falling-factorial transform. -/
theorem starC_assoc (c : ℝ) (f g h : ℝ[X]) :
    starC c (starC c f g) h = starC c f (starC c g h) := by
  apply fallingFactorialTransform_injective c
  simp only [fallingFactorialTransform_starC, mul_assoc]
end

end RealRooted.Poisson
