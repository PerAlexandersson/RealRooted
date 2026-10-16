module

public import RealRooted.HermiteBiehler.Basic
public import RealRooted.OperatorPreservesInterlacing
public import RealRooted.PFPolynomial
public import RealRooted.QuadraticRoot

/-!
# The univariate Poisson star product

For real polynomials `f` and `g` and a real parameter `c`, this file defines

`f ⋆[c] g = ∑ j, c^j X^j / j! * f^(j) * g^(j)`.

The intended library home is
`RealRooted/BorceaBranden/Applications/UnivariatePoissonStar.lean`.  The API below records
linearity, the affine-input formula, the sharp quadratic obstruction, stability of the signed
Weyl symbol under the root-sign condition, exact affine-factor tests, and the boundary cases
of the PF classification established here.
-/

@[expose] public noncomputable section

open Polynomial
open scoped BigOperators

namespace RealRooted.Poisson

/-- The univariate Poisson product with real parameter `c`.

The sum is truncated at the degree of the left input.  Terms beyond the degree of the right
input vanish automatically. -/
def starC (c : ℝ) (f g : ℝ[X]) : ℝ[X] :=
  ∑ j ∈ Finset.range (f.natDegree + 1),
    C (c ^ j / (j.factorial : ℝ)) * X ^ j *
      (derivative^[j]) f * (derivative^[j]) g

/-- The defining sum for `starC` may be enlarged beyond the degree of its left input. -/
theorem starC_eq_sum_range {c : ℝ} {f : ℝ[X]} {N : ℕ}
    (hfN : f.natDegree < N) (g : ℝ[X]) :
    starC c f g =
      ∑ j ∈ Finset.range N,
        C (c ^ j / (j.factorial : ℝ)) * X ^ j *
          (derivative^[j]) f * (derivative^[j]) g := by
  rw [starC]
  refine Finset.sum_subset (Finset.range_subset_range.mpr ?_) ?_
  · exact Nat.succ_le_iff.mpr hfN
  · intro j hjN hjf
    simp only [Finset.mem_range] at hjN hjf
    have hdeg : f.natDegree < j := by lia
    rw [iterate_derivative_eq_zero hdeg, mul_zero, zero_mul]

/-- The univariate Poisson product is symmetric. -/
theorem starC_comm (c : ℝ) (f g : ℝ[X]) :
    starC c f g = starC c g f := by
  let N := max (f.natDegree + 1) (g.natDegree + 1)
  rw [starC_eq_sum_range (N := N)
      ((Nat.lt_succ_self f.natDegree).trans_le (le_max_left _ _)),
    starC_eq_sum_range (N := N)
      ((Nat.lt_succ_self g.natDegree).trans_le (le_max_right _ _))]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- `starC` is additive in its right input. -/
theorem starC_add_right (c : ℝ) (f g h : ℝ[X]) :
    starC c f (g + h) = starC c f g + starC c f h := by
  simp only [starC, iterate_map_add, mul_add, Finset.sum_add_distrib]

/-- `starC` is additive in its left input. -/
theorem starC_add_left (c : ℝ) (f g h : ℝ[X]) :
    starC c (f + g) h = starC c f h + starC c g h := by
  rw [starC_comm, starC_add_right, starC_comm c h f, starC_comm c h g]

/-- `starC` commutes with multiplication of its right input by a real constant. -/
theorem starC_C_mul_right (c a : ℝ) (f g : ℝ[X]) :
    starC c f (C a * g) = C a * starC c f g := by
  rw [starC, starC, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iterate_derivative_C_mul]
  ring

/-- `starC` commutes with multiplication of its left input by a real constant. -/
theorem starC_C_mul_left (c a : ℝ) (f g : ℝ[X]) :
    starC c (C a * f) g = C a * starC c f g := by
  rw [starC_comm, starC_C_mul_right, starC_comm c g f]

/-- The zero polynomial is a right annihilator for `starC`. -/
@[simp] theorem starC_zero_right (c : ℝ) (f : ℝ[X]) :
    starC c f 0 = 0 := by
  simp only [starC, iterate_map_zero, mul_zero, Finset.sum_const_zero]

/-- The zero polynomial is a left annihilator for `starC`. -/
@[simp] theorem starC_zero_left (c : ℝ) (g : ℝ[X]) :
    starC c 0 g = 0 := by
  rw [starC_comm, starC_zero_right]

/-- The constant polynomial `1` is a right unit for `starC`. -/
@[simp] theorem starC_one_right (c : ℝ) (f : ℝ[X]) :
    starC c f 1 = f := by
  rw [starC, Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    map_one, pow_zero, Function.iterate_zero_apply, one_mul]
  rw [Finset.sum_eq_zero]
  · simp
  · intro j hj
    rw [iterate_derivative_eq_zero (p := (1 : ℝ[X])) (by simp), mul_zero]

/-- The constant polynomial `1` is a left unit for `starC`. -/
@[simp] theorem starC_one_left (c : ℝ) (g : ℝ[X]) :
    starC c 1 g = g := by
  rw [starC_comm, starC_one_right]

/-- Left Poisson multiplication is a real-linear operator. -/
def starCLinearMap (c : ℝ) (f : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := starC c f
  map_add' := starC_add_right c f
  map_smul' a g := by
    rw [smul_eq_C_mul, smul_eq_C_mul, starC_C_mul_right]
    simp only [RingHom.id_apply]

/-- Evaluation of the bundled left-multiplication map is `starC`. -/
@[simp] theorem starCLinearMap_apply (c : ℝ) (f g : ℝ[X]) :
    starCLinearMap c f g = starC c f g :=
  rfl

/-- Applying `starC` to `X` gives the first-order Euler pencil
`X * (f + c f')`. -/
theorem starC_X_right (c : ℝ) (f : ℝ[X]) :
    starC c f X = X * (f + C c * f.derivative) := by
  by_cases hdeg : f.natDegree = 0
  · rw [starC]
    simp only [hdeg, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, map_one, Function.iterate_zero_apply,
      one_mul]
    rw [derivative_eq_zero.mpr hdeg]
    ring
  · obtain ⟨n, hdeg'⟩ := Nat.exists_eq_succ_of_ne_zero hdeg
    rw [starC, hdeg', Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_one,
      Function.iterate_zero_apply, one_mul]
    have htail : (∑ j ∈ Finset.range n,
        C (c ^ (j + 2) / ((j + 2).factorial : ℝ)) * X ^ (j + 2) *
          (derivative^[j + 2]) f * (derivative^[j + 2]) X) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [iterate_derivative_eq_zero (p := (X : ℝ[X])) (by simp), mul_zero]
    rw [htail]
    simp only [zero_add, pow_one, Nat.factorial_one,
      Nat.cast_one, div_one, Function.iterate_one, derivative_X, mul_one]
    ring

/-- Affine right inputs give the explicit first-order formula. -/
theorem starC_affine_right (c a b : ℝ) (f : ℝ[X]) :
    starC c f (C a + C b * X) =
      C a * f + C b * X * (f + C c * f.derivative) := by
  rw [show C a = C a * 1 by simp, starC_add_right,
    starC_C_mul_right, starC_C_mul_right,
    starC_one_right, starC_X_right]
  ring

/-- Affine left inputs act by the first-order Euler operator. -/
theorem starC_affine_left (c a b : ℝ) (g : ℝ[X]) :
    starC c (C a + C b * X) g =
      C a * g + C b * X * (g + C c * g.derivative) := by
  rw [starC_comm, starC_affine_right]

/-- A linear left factor gives the Poisson differential recurrence. -/
theorem starC_linear_factor_left (c a b : ℝ) (g : ℝ[X]) :
    starC c (C a + C b * X) g =
      (C a + C b * X) * g + C (c * b) * X * g.derivative := by
  rw [starC_affine_left]
  simp only [map_mul]
  ring

/-- At parameter zero, the Poisson product is ordinary multiplication. -/
@[simp] theorem starC_zero (f g : ℝ[X]) :
    starC 0 f g = f * g := by
  rw [starC, Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_one,
    Function.iterate_zero_apply, one_mul]
  rw [Finset.sum_eq_zero]
  · ring
  · intro j hj
    simp

/-- Nonnegative inputs remain coefficientwise nonnegative when `c` is nonnegative. -/
theorem starC_nonneg {c : ℝ} (hc : 0 ≤ c) {f g : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g) :
    HasNonnegCoeffs (starC c f g) := by
  unfold starC
  exact hasNonnegCoeffs_finsetSum _ _ fun j _ ↦
    (((hasNonnegCoeffs_C
      (div_nonneg (pow_nonneg hc j) (Nat.cast_nonneg j.factorial))).mul
      (hasNonnegCoeffs_X.pow j)).mul (hf.iterate_derivative j)).mul
      (hg.iterate_derivative j)

/-- The sharp affine obstruction: a root `r` with `c*r > 0` produces a
quadratic factor with negative discriminant. -/
theorem starC_root_obstruction (c r : ℝ) :
    starC c (X - C r) (X - C (r + c)) =
      (X - C r) ^ 2 + C (c * r) := by
  rw [show X - C (r + c) = C (-(r + c)) + C 1 * X by
    simp only [map_add, map_neg, map_one]
    ring]
  rw [starC_affine_right]
  simp only [map_one, derivative_sub, derivative_X, derivative_C, sub_zero]
  simp only [map_add, map_neg, map_mul]
  ring

/-- The quadratic obstruction fails to split precisely in the forbidden
strict-sign regime `0 < c * r`. -/
theorem starC_root_obstruction_not_splits {c r : ℝ} (hcr : 0 < c * r) :
    ¬(starC c (X - C r) (X - C (r + c))).Splits := by
  rw [starC_root_obstruction]
  rw [show (X - C r) ^ 2 + C (c * r) =
      C 1 * X ^ 2 + C (-2 * r) * X + C (r ^ 2 + c * r) by
    simp only [map_add, map_neg, map_mul, map_pow, map_one, map_ofNat]
    ring]
  apply quadraticPoly_not_splits_of_discrim_neg one_ne_zero
  unfold discrim
  nlinarith

/-- A forbidden root already disproves preservation on affine inputs. -/
theorem not_preservesRealRootedOrZero_linear {c r : ℝ} (hcr : 0 < c * r) :
    ¬PreservesRealRootedOrZero (starCLinearMap c (X - C r)) := by
  intro hpres
  have hinput : X - C (r + c) ≠ 0 ∧ (X - C (r + c)).Splits :=
    ⟨X_sub_C_ne_zero _, (isRealRooted_X_sub_C _).2⟩
  have hnot := starC_root_obstruction_not_splits hcr
  rcases hpres (X - C (r + c)) hinput with hzero | hsplits
  · apply hnot
    rw [← starCLinearMap_apply, hzero]
    simp
  · exact hnot hsplits

/-- Preservation on the affine test class.  Since every real affine
polynomial splits, no separate input-splitting hypothesis is needed. -/
def PreservesAffineRealRooted (c : ℝ) (f : ℝ[X]) : Prop :=
  ∀ a b : ℝ, (starC c f (C a + C b * X)).Splits

/-- Exact affine-test classification for a single linear factor: the factor
`X - r` passes every affine input exactly when `c * r ≤ 0`. -/
theorem preservesAffineRealRooted_linear_iff (c r : ℝ) :
    PreservesAffineRealRooted c (X - C r) ↔ c * r ≤ 0 := by
  constructor
  · intro hpres
    by_contra hnot
    have hcr : 0 < c * r := lt_of_not_ge hnot
    have hsplits := hpres (-(r + c)) 1
    have hinput : C (-(r + c)) + C 1 * X = X - C (r + c) := by
      simp only [map_add, map_neg, map_one]
      ring
    rw [hinput] at hsplits
    exact starC_root_obstruction_not_splits hcr hsplits
  · intro hcr a b
    rw [starC_affine_right]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero]
    rw [show C a * (X - C r) + C b * X *
          (X - C r + C c * 1) =
        C b * X ^ 2 + C (a + b * (c - r)) * X + C (-a * r) by
      simp only [map_add, map_sub, map_neg, map_mul]
      ring]
    apply quadraticPoly_splits_of_discrim_nonneg_or_linear
    have hbcr : b ^ 2 * (c * r) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg b) hcr
    unfold discrim
    nlinarith [sq_nonneg (a + b * (c + r))]

/-- The bivariate signed Weyl symbol `f(z(1-cw))` of fixed left Poisson
multiplication. -/
def poissonSignedSymbol (c : ℝ) (f : ℝ[X]) : MvPolynomial (Fin 2) ℂ :=
  (complexify f).eval₂
    (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
    (MvPolynomial.X 0 *
      (1 - MvPolynomial.C (c : ℂ) * MvPolynomial.X 1))

/-- The root-side condition in the exact Poisson preserver classifier. -/
def IsAdmissible (c : ℝ) (f : ℝ[X]) : Prop :=
  f ≠ 0 ∧ f.Splits ∧ ∀ r ∈ f.roots, c * r ≤ 0

/-- Evaluation of the signed Weyl symbol is substitution into
`f(z(1-cw))`. -/
@[simp] theorem eval_poissonSignedSymbol (c : ℝ) (f : ℝ[X])
    (z : Fin 2 → ℂ) :
    MvPolynomial.eval z (poissonSignedSymbol c f) =
      (complexify f).eval (z 0 * (1 - (c : ℂ) * z 1)) := by
  have hC :
      (MvPolynomial.eval z).comp
          (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ) =
        RingHom.id ℂ := by
    ext a
    simp
  simp [poissonSignedSymbol, Polynomial.hom_eval₂, hC]

/-- The signed Weyl symbol is stable when every root of the split fixed
factor satisfies the sharp sign condition `c * r ≤ 0`. -/
theorem poissonSignedSymbol_stable {c : ℝ} {f : ℝ[X]} (hf : f ≠ 0)
    (hfs : f.Splits) (hroot : ∀ r ∈ f.roots, c * r ≤ 0) :
    MvUpperHalfPlaneStable (poissonSignedSymbol c f) := by
  intro z hz
  rw [eval_poissonSignedSymbol, eval_complexify_eq_prod hfs]
  apply mul_ne_zero
  · simp [hf]
  · apply Multiset.prod_ne_zero
    simp only [Multiset.mem_map, not_exists, not_and]
    intro r hr
    have hden : 1 - (c : ℂ) * z 1 ≠ 0 := by
      intro hden_zero
      by_cases hc : c = 0
      · simp [hc] at hden_zero
      · have him := congrArg Complex.im hden_zero
        simp only [Complex.sub_im, Complex.one_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          zero_sub, Complex.zero_im] at him
        exact hc ((mul_eq_zero.mp (neg_eq_zero.mp him)).resolve_right (ne_of_gt (hz 1)))
    intro hzero
    have hmul : z 0 * (1 - (c : ℂ) * z 1) = (r : ℂ) :=
      sub_eq_zero.mp hzero
    have hzdiv : z 0 = (r : ℂ) / (1 - (c : ℂ) * z 1) :=
      (eq_div_iff hden).2 hmul
    have himag :
        ((r : ℂ) / (1 - (c : ℂ) * z 1)).im =
          r * c * (z 1).im /
            Complex.normSq (1 - (c : ℂ) * z 1) := by
      rw [Complex.div_im]
      simp only [Complex.ofReal_im, zero_mul, Complex.ofReal_re,
        Complex.sub_im, Complex.one_im, Complex.mul_im,
        Complex.sub_re, Complex.one_re, Complex.mul_re]
      ring
    have hnorm : 0 < Complex.normSq (1 - (c : ℂ) * z 1) :=
      Complex.normSq_pos.mpr hden
    have hnum : r * c * (z 1).im ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by simpa [mul_comm] using hroot r hr) (hz 1).le
    have hnonpos :
        ((r : ℂ) / (1 - (c : ℂ) * z 1)).im ≤ 0 := by
      rw [himag]
      exact div_nonpos_of_nonpos_of_nonneg hnum hnorm.le
    have hzpos :
        0 < ((r : ℂ) / (1 - (c : ℂ) * z 1)).im := by
      rw [← hzdiv]
      exact hz 0
    exact (not_lt_of_ge hnonpos) hzpos

/-- Admissibility packages exactly the hypotheses needed for signed-symbol
stability. -/
theorem IsAdmissible.poissonSignedSymbol_stable {c : ℝ} {f : ℝ[X]}
    (h : IsAdmissible c f) :
    MvUpperHalfPlaneStable (poissonSignedSymbol c f) :=
  RealRooted.Poisson.poissonSignedSymbol_stable h.1 h.2.1 h.2.2

/-- Preservation of the finite PF cone by fixed left Poisson multiplication. -/
def PreservesPF (c : ℝ) (f : ℝ[X]) : Prop :=
  ∀ g : ℝ[X], IsPFPolynomial g → IsPFPolynomial (starC c f g)

/-- Any fixed factor preserving all PF polynomials is itself PF. -/
theorem isPFPolynomial_of_preservesPF {c : ℝ} {f : ℝ[X]}
    (hpres : PreservesPF c f) : IsPFPolynomial f := by
  simpa using hpres 1 IsPFPolynomial.one

/-- Poisson multiplication by a nonnegative constant preserves every PF
polynomial, for every real parameter. -/
theorem preservesPF_constant (c a : ℝ) (ha : 0 ≤ a) :
    PreservesPF c (C a) := by
  intro g hg
  rw [show C a = C a * 1 by simp, starC_C_mul_left, starC_one_left]
  exact (IsPFPolynomial.of_C_nonneg ha).mul hg

/-- The first negative-parameter PF obstruction is already visible on two
copies of `X`. -/
theorem starC_X_X (c : ℝ) :
    starC c X X = X ^ 2 + C c * X := by
  rw [starC_X_right]
  simp only [derivative_X, mul_one]
  ring

/-- For `c < 0`, left Poisson multiplication by `X` does not preserve the PF
cone. -/
theorem not_preservesPF_X {c : ℝ} (hc : c < 0) :
    ¬PreservesPF c X := by
  intro hpres
  have hcoeff := (hpres X isPFPolynomial_X).hasNonnegCoeffs 1
  rw [starC_X_X] at hcoeff
  have hc_nonneg : 0 ≤ c := by
    simpa [coeff_add, coeff_C_mul, coeff_X_pow] using hcoeff
  exact (not_lt_of_ge hc_nonneg) hc

/-- On a monomial test input, a fixed affine factor has exactly two
potentially nonzero coefficients. -/
theorem starC_affine_X_pow (c a b : ℝ) (N : ℕ) :
    starC c (C a + C b * X) (X ^ N) =
      C b * X ^ (N + 1) + C (a + c * b * N) * X ^ N := by
  rw [starC_linear_factor_left]
  cases N with
  | zero => simp [add_comm]
  | succ N =>
      rw [derivative_X_pow_succ]
      push_cast
      simp only [map_add, map_mul, map_one]
      ring

/-- On a high enough monomial, all derivative terms in `starC` share the
factor `X ^ N`. -/
theorem starC_X_pow_eq_X_pow_mul (c : ℝ) (f : ℝ[X]) (N : ℕ)
    (hN : f.natDegree ≤ N) :
    starC c f (X ^ N) =
      X ^ N * ∑ j ∈ Finset.range (f.natDegree + 1),
        C (c ^ j / (j.factorial : ℝ)) *
          C (N.descFactorial j : ℝ) * (derivative^[j]) f := by
  rw [starC, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjN : j ≤ N := (Nat.le_of_lt_succ hj).trans hN
  rw [iterate_derivative_X_pow_eq_C_mul]
  have hpow : (X : ℝ[X]) ^ j * X ^ (N - j) = X ^ N := by
    rw [← pow_add, Nat.add_sub_of_le hjN]
  calc
    C (c ^ j / (j.factorial : ℝ)) * X ^ j * (derivative^[j]) f *
          (C (N.descFactorial j : ℝ) * X ^ (N - j)) =
        C (c ^ j / (j.factorial : ℝ)) * C (N.descFactorial j : ℝ) *
          (X ^ j * X ^ (N - j)) * (derivative^[j]) f := by ring
    _ = X ^ N * (C (c ^ j / (j.factorial : ℝ)) *
          C (N.descFactorial j : ℝ) * (derivative^[j]) f) := by
      rw [hpow]
      ring

/-- The coefficient just below the top degree on a high monomial test is
`nextCoeff f + c * deg(f) * N * leadingCoeff f`. -/
theorem coeff_starC_X_pow_next (c : ℝ) (f : ℝ[X]) (N : ℕ)
    (hfdeg : f.natDegree ≠ 0) (hN : f.natDegree ≤ N) :
    (starC c f (X ^ N)).coeff (f.natDegree + N - 1) =
      f.nextCoeff + c * f.natDegree * N * f.leadingCoeff := by
  rw [starC_X_pow_eq_X_pow_mul c f N hN]
  rw [show f.natDegree + N - 1 = f.natDegree - 1 + N by lia]
  rw [coeff_X_pow_mul]
  rw [finsetSum_coeff]
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hfdeg
  rw [hd, Finset.sum_range_succ', Finset.sum_range_succ']
  have htail :
      ∑ j ∈ Finset.range d,
        (C (c ^ (j + 1 + 1) / ((j + 1 + 1).factorial : ℝ)) *
          C (N.descFactorial (j + 1 + 1) : ℝ) *
            (derivative^[j + 1 + 1]) f).coeff (d.succ - 1) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [← map_mul, coeff_C_mul, coeff_iterate_derivative]
    rw [f.coeff_eq_zero_of_natDegree_lt (by rw [hd]; lia)]
    simp
  rw [htail, zero_add]
  have hfirst :
      (C c * C (N.descFactorial 1 : ℝ) * (derivative^[1]) f).coeff d =
        c * N * (d + 1) * f.coeff (d + 1) := by
    rw [← map_mul, coeff_C_mul, Function.iterate_one, coeff_derivative]
    simp only [Nat.descFactorial_one]
    ring
  have hzero : (C 1 * C 1 * f).coeff d = f.coeff d := by simp
  norm_num only [Nat.zero_add, pow_zero, pow_one, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, div_one, Nat.descFactorial_zero,
    Function.iterate_zero_apply, Nat.succ_sub_one]
  rw [hfirst, hzero]
  have hlc : f.coeff (d + 1) = f.leadingCoeff := by
    rw [show d + 1 = d.succ by rfl, ← hd]
    exact coeff_natDegree
  simp only [Polynomial.nextCoeff, hd, Nat.succ_ne_zero, ite_false,
    Nat.succ_sub_one]
  rw [hlc]
  push_cast
  ring

/-- For a negative parameter, every affine factor with positive slope fails
to preserve the PF cone: a sufficiently high monomial exposes a negative
coefficient. -/
theorem not_preservesPF_affine_of_neg {c b : ℝ} (hc : c < 0) (hb : 0 < b)
    (a : ℝ) :
    ¬PreservesPF c (C a + C b * X) := by
  intro hpres
  have hden : 0 < -(c * b) := neg_pos.mpr (mul_neg_of_neg_of_pos hc hb)
  obtain ⟨N, hN⟩ := exists_nat_gt (a / (-(c * b)))
  have hscaled := mul_lt_mul_of_pos_right hN hden
  rw [div_mul_cancel₀ a hden.ne'] at hscaled
  have hnegative : a + c * b * N < 0 := by
    nlinarith
  have hpow : IsPFPolynomial ((X : ℝ[X]) ^ N) := isPFPolynomial_X.pow N
  have hcoeff := (hpres (X ^ N) hpow).hasNonnegCoeffs N
  rw [starC_affine_X_pow] at hcoeff
  have hnonneg : 0 ≤ a + c * b * N := by
    rw [coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_pow,
      coeff_X_pow] at hcoeff
    have hne : ¬N = N + 1 := Nat.ne_of_lt (Nat.lt_succ_self N)
    simp only [hne, ite_false, ite_true, mul_zero, zero_add, mul_one] at hcoeff
    exact hcoeff
  exact (not_lt_of_ge hnonneg) hnegative

/-- Exact negative-parameter PF classification: only nonnegative constants
can be fixed left factors preserving every finite PF polynomial. -/
theorem preservesPF_of_neg_iff {c : ℝ} (hc : c < 0) (f : ℝ[X]) :
    PreservesPF c f ↔ ∃ a : ℝ, 0 ≤ a ∧ f = C a := by
  constructor
  · intro hpres
    have hfpf : IsPFPolynomial f := isPFPolynomial_of_preservesPF hpres
    by_cases hdeg : f.natDegree = 0
    · exact ⟨f.coeff 0, hfpf.hasNonnegCoeffs 0,
        eq_C_of_natDegree_eq_zero hdeg⟩
    · exfalso
      have hf0 : f ≠ 0 := by
        intro hzero
        simp [hzero] at hdeg
      have hdegree_pos : 0 < f.natDegree := Nat.pos_of_ne_zero hdeg
      have hlc_pos : 0 < f.leadingCoeff :=
        hfpf.hasNonnegCoeffs.pos_leadingCoeff hf0
      have hnext : 0 ≤ f.nextCoeff := by
        simpa [Polynomial.nextCoeff, hdeg] using
          hfpf.hasNonnegCoeffs (f.natDegree - 1)
      have hscale : c * (f.natDegree : ℝ) * f.leadingCoeff < 0 :=
        mul_neg_of_neg_of_pos
          (mul_neg_of_neg_of_pos hc (Nat.cast_pos.mpr hdegree_pos)) hlc_pos
      have hden : 0 < -(c * (f.natDegree : ℝ) * f.leadingCoeff) :=
        neg_pos.mpr hscale
      let bound : ℝ := max (f.natDegree : ℝ)
        (f.nextCoeff / -(c * (f.natDegree : ℝ) * f.leadingCoeff))
      obtain ⟨N, hN⟩ := exists_nat_gt bound
      have hdegreeN : f.natDegree ≤ N := by
        have hdegreeN_real : (f.natDegree : ℝ) ≤ (N : ℝ) :=
          (le_max_left (f.natDegree : ℝ)
            (f.nextCoeff /
              -(c * (f.natDegree : ℝ) * f.leadingCoeff))).trans hN.le
        exact_mod_cast hdegreeN_real
      have hratio :
          f.nextCoeff / -(c * (f.natDegree : ℝ) * f.leadingCoeff) < N :=
        (le_max_right _ _).trans_lt hN
      have hscaled := mul_lt_mul_of_pos_right hratio hden
      rw [div_mul_cancel₀ f.nextCoeff hden.ne'] at hscaled
      have hnegative :
          f.nextCoeff + c * f.natDegree * N * f.leadingCoeff < 0 := by
        nlinarith
      have hout := (hpres (X ^ N) (isPFPolynomial_X.pow N)).hasNonnegCoeffs
        (f.natDegree + N - 1)
      rw [coeff_starC_X_pow_next c f N hdeg hdegreeN] at hout
      exact (not_lt_of_ge hout) hnegative
  · rintro ⟨a, ha, rfl⟩
    exact preservesPF_constant c a ha

/-- At the boundary parameter `c = 0`, fixed left multiplication preserves
real-rootedness exactly when its nonzero factor splits. -/
theorem preservesRealRootedOrZero_zero_iff {f : ℝ[X]} (hf : f ≠ 0) :
    PreservesRealRootedOrZero (starCLinearMap 0 f) ↔ f.Splits := by
  constructor
  · intro hpres
    rcases hpres 1 ⟨one_ne_zero, by simp⟩ with hzero | hsplits
    · rw [starCLinearMap_apply, starC_one_right] at hzero
      exact (hf hzero).elim
    · simpa using hsplits
  · intro hfs g hg
    right
    rw [starCLinearMap_apply, starC_zero]
    exact hfs.mul hg.2

/-- At `c = 0`, the exact PF-preserver condition is that the fixed factor is
itself PF. -/
theorem preservesPF_zero_iff (f : ℝ[X]) :
    PreservesPF 0 f ↔ IsPFPolynomial f := by
  constructor
  · exact isPFPolynomial_of_preservesPF
  · intro hf g hg
    rw [starC_zero]
    exact hf.mul hg

end RealRooted.Poisson
