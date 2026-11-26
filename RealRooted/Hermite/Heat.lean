module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
public import RealRooted.SimpleRoots
import RealRooted.Derivative.Algebra
public import RealRooted.Hermite.Homogeneous
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatFlow
import RealRooted.ExponentialRows.GaussianSimplicity
import RealRooted.ExponentialRows.QuarticGaussian
import Mathlib.Tactic

/-!
# Finite heat operators

The polynomial operator `gaussianHeat s` is `exp(s D²)`. We reuse the
Laguerre–Pólya theorem and its simplicity refinement, and supply finite-sum
and differentiation APIs. Source: the unpublished heat-operator argument in
https://github.com/PerAlexandersson/RealRooted/issues/2646.
-/

@[expose] public section

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- The finite polynomial heat operator `exp(s D²)`, with signed time `s`. -/
def gaussianHeat (s : ℝ) (p : ℝ[X]) : ℝ[X] :=
  taylorDifferentialOperator (fun z => Complex.exp ((s : ℂ) * z ^ 2)) p

/-- A degree bound can replace the intrinsic truncation of a Taylor differential operator. -/
theorem taylorDifferentialOperator_eq_sum {φ : ℂ → ℂ} (p : ℝ[X]) {N : ℕ}
    (hN : p.natDegree ≤ N) :
    taylorDifferentialOperator φ p = ∑ k ∈ range (N + 1),
      C ((iteratedDeriv k φ 0 / k.factorial).re) * (derivative^[k]) p := by
  apply sum_subset (range_mono (Nat.add_le_add_right hN 1))
  intro k _ hk
  have hlt : p.natDegree < k := by
    simp only [mem_range, not_lt] at hk
    lia
  rw [iterate_derivative_eq_zero hlt, mul_zero]

/-- Taylor differential operators commute with polynomial differentiation. -/
theorem derivative_taylorDifferentialOperator (φ : ℂ → ℂ) (p : ℝ[X]) :
    (taylorDifferentialOperator φ p).derivative =
      taylorDifferentialOperator φ p.derivative := by
  rw [taylorDifferentialOperator_eq_sum p.derivative (N := p.natDegree)
    ((natDegree_derivative_le p).trans (Nat.sub_le _ _))]
  simp only [taylorDifferentialOperator, derivative_sum, derivative_mul, derivative_C,
    zero_mul, zero_add]
  apply sum_congr rfl
  intro k _
  rw [← Function.iterate_succ_apply' (f := (Polynomial.derivative : ℝ[X] → ℝ[X])),
    Function.iterate_succ_apply]

/-- Taylor differential operators commute with multiplication by a scalar. -/
theorem taylorDifferentialOperator_C_mul (φ : ℂ → ℂ) (a : ℝ) (p : ℝ[X]) :
    taylorDifferentialOperator φ (C a * p) = C a * taylorDifferentialOperator φ p := by
  by_cases ha : a = 0
  · simp [ha, taylorDifferentialOperator]
  simp only [taylorDifferentialOperator, natDegree_C_mul ha, iterate_derivative_C_mul,
    mul_sum]
  apply sum_congr rfl
  intro k _
  ring

/-- The heat operator is a finite sum of homogeneous Gaussian moments and derivatives. -/
theorem gaussianHeat_eq_sum (s : ℝ) (p : ℝ[X]) :
    gaussianHeat s p = ∑ k ∈ range (p.natDegree + 1),
      C (hermiteHomogeneous 0 s k / k.factorial) * (derivative^[k]) p := by
  unfold gaussianHeat taylorDifferentialOperator
  apply sum_congr rfl
  intro k _
  rw [iteratedDeriv_exp_mul_sq_zero]
  have hm := map_hermiteHomogeneous Complex.ofRealHom 0 s k
  simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_zero] at hm
  rw [← hm, ← Complex.ofReal_natCast k.factorial, ← Complex.ofReal_div, Complex.ofReal_re]

/-- Heat commutes with differentiation, at every real signed time. -/
theorem derivative_gaussianHeat (s : ℝ) (p : ℝ[X]) :
    (gaussianHeat s p).derivative = gaussianHeat s p.derivative :=
  derivative_taylorDifferentialOperator _ _

/-- A scalar factor pulls out of the heat operator. -/
theorem gaussianHeat_C_mul (s a : ℝ) (p : ℝ[X]) :
    gaussianHeat s (C a * p) = C a * gaussianHeat s p :=
  taylorDifferentialOperator_C_mul _ _ _

/-- Backward heat preserves splitting, including the zero polynomial and time zero. -/
theorem gaussianHeat_splits {s : ℝ} (hs : s ≤ 0) {p : ℝ[X]} (hp : p.Splits) :
    (gaussianHeat s p).Splits := by
  have hφ := isLaguerrePolya_exp_neg_mul_sq (neg_nonneg.mpr hs)
  have h := hφ.taylorDifferentialOperator_splits hp
  simpa only [gaussianHeat, Complex.ofReal_neg, neg_neg] using h

/-- Backward heat preserves simple real-rootedness, including time zero. -/
theorem gaussianHeat_isSimpleRealRooted {s : ℝ} (hs : s ≤ 0) {p : ℝ[X]}
    (hp : IsSimpleRealRooted p) : IsSimpleRealRooted (gaussianHeat s p) := by
  have h := isSimpleRealRooted_taylorDifferentialOperator_exp_neg_mul_sq
    (neg_nonneg.mpr hs) hp
  simpa only [gaussianHeat, Complex.ofReal_neg, neg_neg] using h

/-- Odd Gaussian moments vanish over every commutative ring. -/
theorem hermiteHomogeneous_zero_odd {R : Type*} [CommRing R] (s : R) (j : ℕ) :
    hermiteHomogeneous 0 s (2 * j + 1) = 0 := by
  induction j with
  | zero => simp only [mul_zero, zero_add, hermiteHomogeneous_one]
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by lia,
      hermiteHomogeneous_add_two, zero_mul, zero_add, ih, mul_zero]

/-- Even Gaussian moments have the exponential-series normalization. -/
theorem hermiteHomogeneous_zero_even_div_factorial (s : ℝ) (j : ℕ) :
    hermiteHomogeneous 0 s (2 * j) / (2 * j).factorial = s ^ j / j.factorial := by
  have hm : (j.factorial : ℝ) * hermiteHomogeneous 0 s (2 * j) =
      ((2 * j).factorial : ℝ) * s ^ j := by
    induction j with
    | zero => simp only [mul_zero, hermiteHomogeneous_zero, Nat.factorial_zero,
        Nat.cast_one, one_mul, pow_zero]
    | succ j ih =>
      rw [show 2 * (j + 1) = 2 * j + 2 by lia, hermiteHomogeneous_add_two,
        zero_mul, zero_add, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      rw [pow_succ]
      calc
        _ = (2 * (j + 1) * (2 * j + 1) * s) *
            ((j.factorial : ℝ) * hermiteHomogeneous 0 s (2 * j)) := by ring
        _ = _ := by rw [ih]; ring
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have h₂j : ((2 * j).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * j)
  apply (div_eq_div_iff h₂j hj).mpr
  simpa only [mul_comm] using hm

/-- Pair consecutive summands in a finite even-length sum. -/
private theorem sum_range_double (f : ℕ → ℝ[X]) (N : ℕ) :
    ∑ k ∈ range (2 * N), f k = ∑ j ∈ range N, (f (2 * j) + f (2 * j + 1)) := by
  induction N with
  | zero => simp only [mul_zero, range_zero, sum_empty]
  | succ N ih =>
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by lia,
      sum_range_succ, sum_range_succ, ih, sum_range_succ]
    abel

/-- The finite heat exponential is the usual sum of the even derivatives. -/
theorem gaussianHeat_eq_sum_even (s : ℝ) (p : ℝ[X]) :
    gaussianHeat s p = ∑ j ∈ range (p.natDegree + 1),
      C (s ^ j / j.factorial) * (derivative^[2 * j]) p := by
  rw [gaussianHeat, taylorDifferentialOperator_eq_sum p
    (N := 2 * (p.natDegree + 1) - 1) (by lia),
    show 2 * (p.natDegree + 1) - 1 + 1 = 2 * (p.natDegree + 1) by lia,
    sum_range_double]
  apply sum_congr rfl
  intro j _
  simp only [iteratedDeriv_exp_mul_sq_zero, hermiteHomogeneous_zero_odd, zero_div,
    Complex.zero_re, map_zero, zero_mul, add_zero]
  have hm := map_hermiteHomogeneous Complex.ofRealHom 0 s (2 * j)
  simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_zero] at hm
  rw [← hm, ← Complex.ofReal_natCast (2 * j).factorial, ← Complex.ofReal_div,
    Complex.ofReal_re, hermiteHomogeneous_zero_even_div_factorial]

/-- The finite diagonal `exp(c X D²) p`, with the time variable specialized after acting. -/
def heatDiagonal (c : ℝ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (p.natDegree + 1),
    C ((k.factorial : ℝ)⁻¹) * hermiteHomogeneous 0 (C c * X) k * (derivative^[k]) p

/-- The diagonal polynomial is heat at the frozen time `c t`, evaluated at `t`. -/
theorem eval_heatDiagonal (c t : ℝ) (p : ℝ[X]) :
    (heatDiagonal c p).eval t = (gaussianHeat (c * t) p).eval t := by
  rw [heatDiagonal, gaussianHeat_eq_sum]
  simp only [eval_finsetSum, eval_mul, eval_C]
  apply sum_congr rfl
  intro k _
  have he := map_hermiteHomogeneous (evalRingHom t) 0 (C c * X) k
  simp only [map_zero, coe_evalRingHom, eval_mul, eval_C, eval_X] at he
  rw [he, div_eq_mul_inv]
  ring

/-- The diagonal specialization is a finite sum with polynomial time factors. -/
theorem heatDiagonal_eq_sum_even (c : ℝ) (p : ℝ[X]) :
    heatDiagonal c p = ∑ j ∈ range (p.natDegree + 1),
      C (c ^ j / j.factorial) * X ^ j * (derivative^[2 * j]) p := by
  apply Polynomial.funext
  intro t
  rw [eval_heatDiagonal, gaussianHeat_eq_sum_even]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply sum_congr rfl
  intro j _
  rw [mul_pow, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The Gaussian moment recurrence with the time variable left polynomial. -/
private theorem moment_add_two (c : ℝ) (k : ℕ) :
    hermiteHomogeneous 0 (C c * X) (k + 2) =
      C (2 * (k + 1 : ℝ) * c) * (X * hermiteHomogeneous 0 (C c * X) k) := by
  simp only [hermiteHomogeneous_add_two, zero_mul, zero_add, map_mul, map_ofNat,
    map_add, map_one, map_natCast]
  push_cast
  ring

/-- The Gaussian moment polynomial has degree at most half its index. -/
theorem natDegree_hermiteHomogeneous_zero_C_mul_X (c : ℝ) (k : ℕ) :
    (hermiteHomogeneous 0 (C c * X) k).natDegree ≤ k / 2 := by
  induction k using Nat.twoStepInduction with
  | zero => simp only [hermiteHomogeneous_zero, natDegree_one, Nat.zero_div, le_refl]
  | one => norm_num only [hermiteHomogeneous_one, natDegree_zero]
  | more k ih _ =>
    rw [moment_add_two]
    have hh := natDegree_C_mul_le (2 * (k + 1 : ℝ) * c)
      (X * hermiteHomogeneous 0 (C c * X) k)
    have hl := natDegree_mul_le (p := (X : ℝ[X]))
      (q := hermiteHomogeneous 0 (C c * X) k)
    rw [natDegree_X] at hl
    lia

/-- Every nonconstant differential summand in the diagonal has degree below the input. -/
private theorem heatDiagonal_term_natDegree_lt (c : ℝ) (p : ℝ[X]) {k : ℕ}
    (hk : k ≠ 0) (hkd : k ≤ p.natDegree) :
    (C ((k.factorial : ℝ)⁻¹) * hermiteHomogeneous 0 (C c * X) k *
      (derivative^[k]) p).natDegree < p.natDegree := by
  have hm := natDegree_hermiteHomogeneous_zero_C_mul_X c k
  have hd := natDegree_iterate_derivative p k
  have hmul := natDegree_mul_le (p := C ((k.factorial : ℝ)⁻¹) *
    hermiteHomogeneous 0 (C c * X) k) (q := (derivative^[k]) p)
  have hc := natDegree_C_mul_le ((k.factorial : ℝ)⁻¹)
    (hermiteHomogeneous 0 (C c * X) k)
  lia

/-- Diagonal heat does not increase degree. -/
theorem heatDiagonal_natDegree_le (c : ℝ) (p : ℝ[X]) :
    (heatDiagonal c p).natDegree ≤ p.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  by_cases hk₀ : k = 0
  · subst k
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, map_one,
      hermiteHomogeneous_zero, mul_one, one_mul, Function.iterate_zero_apply, le_refl]
  · exact (heatDiagonal_term_natDegree_lt c p hk₀ (by
      simp only [mem_range] at hk
      lia)).le

/-- The top coefficient is unchanged by diagonal heat. -/
theorem coeff_heatDiagonal_natDegree (c : ℝ) (p : ℝ[X]) :
    (heatDiagonal c p).coeff p.natDegree = p.leadingCoeff := by
  rw [heatDiagonal, finsetSum_coeff, sum_eq_single 0]
  · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, map_one,
      hermiteHomogeneous_zero, mul_one, one_mul, Function.iterate_zero_apply, coeff_natDegree]
  · intro k hk hk₀
    exact coeff_eq_zero_of_natDegree_lt (heatDiagonal_term_natDegree_lt c p hk₀ (by
      simp only [mem_range] at hk
      lia))
  · simp only [mem_range, Nat.zero_lt_succ, not_true_eq_false, false_implies]

/-- Diagonal heat preserves the exact degree of any polynomial. -/
theorem heatDiagonal_natDegree (c : ℝ) (p : ℝ[X]) :
    (heatDiagonal c p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · subst p
    simp [heatDiagonal]
  · exact natDegree_eq_of_le_of_coeff_ne_zero (heatDiagonal_natDegree_le c p)
      (by rw [coeff_heatDiagonal_natDegree]; exact leadingCoeff_ne_zero.mpr hp)

/-- The leading coefficient is unchanged by diagonal heat. -/
theorem heatDiagonal_leadingCoeff (c : ℝ) (p : ℝ[X]) :
    (heatDiagonal c p).leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff, heatDiagonal_natDegree, coeff_heatDiagonal_natDegree]

/-- The constant coefficient is unchanged by diagonal heat. -/
theorem heatDiagonal_coeff_zero (c : ℝ) (p : ℝ[X]) :
    (heatDiagonal c p).coeff 0 = p.coeff 0 := by
  rw [coeff_zero_eq_eval_zero, eval_heatDiagonal, mul_zero, gaussianHeat_eq_sum,
    eval_finsetSum, sum_eq_single 0]
  · simp only [hermiteHomogeneous_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      map_one, Function.iterate_zero_apply, one_mul, coeff_zero_eq_eval_zero]
  · intro k _ hk
    simp only [eval_mul, eval_C, hermiteHomogeneous_zero_right, zero_pow hk, zero_div,
      zero_mul]
  · simp only [mem_range, Nat.zero_lt_succ, not_true_eq_false, false_implies]

/-- At zero time diagonal heat is the identity. -/
@[simp] theorem heatDiagonal_zero (p : ℝ[X]) : heatDiagonal 0 p = p := by
  rw [heatDiagonal, sum_eq_single 0]
  · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, map_one,
      hermiteHomogeneous_zero, mul_one, one_mul, Function.iterate_zero_apply]
  · intro k _ hk
    simp only [map_zero, zero_mul, hermiteHomogeneous_zero_right, zero_pow hk, mul_zero]
  · simp only [mem_range, Nat.zero_lt_succ, not_true_eq_false, false_implies]

/-- Nonnegative time gives nonnegative coefficients to each Gaussian moment polynomial. -/
theorem hasNonnegCoeffs_hermiteHomogeneous_zero_C_mul_X {c : ℝ} (hc : 0 ≤ c) (k : ℕ) :
    HasNonnegCoeffs (hermiteHomogeneous 0 (C c * X) k) := by
  induction k using Nat.twoStepInduction with
  | zero => exact hasNonnegCoeffs_one
  | one => exact hasNonnegCoeffs_zero
  | more k ih _ =>
    rw [hermiteHomogeneous_add_two, zero_mul, zero_add]
    exact (((hasNonnegCoeffs_C (by norm_num : (0 : ℝ) ≤ 2)).mul
      (hasNonnegCoeffs_C (by positivity : (0 : ℝ) ≤ (k + 1 : ℕ)))).mul
        ((hasNonnegCoeffs_C hc).mul hasNonnegCoeffs_X)).mul ih

/-- Diagonal heat at nonnegative times preserves coefficient nonnegativity. -/
theorem HasNonnegCoeffs.heatDiagonal {c : ℝ} (hc : 0 ≤ c) {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) : HasNonnegCoeffs (heatDiagonal c p) := by
  apply hasNonnegCoeffs_finsetSum
  intro k hk
  clear hk
  have hd : HasNonnegCoeffs ((derivative^[k]) p) := by
    induction k with
    | zero => exact hp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.derivative
  exact ((hasNonnegCoeffs_C (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)⁻¹)).mul
    (hasNonnegCoeffs_hermiteHomogeneous_zero_C_mul_X hc k)).mul hd

/-- Every coefficient of a diagonal heat deformation depends continuously on time. -/
theorem continuous_coeff_heatDiagonal (p : ℝ[X]) (i : ℕ) :
    Continuous fun c : ℝ => (heatDiagonal c p).coeff i := by
  have hm (k j : ℕ) : Continuous fun c : ℝ =>
      (hermiteHomogeneous 0 (C c * X) k).coeff j := by
    induction k using Nat.twoStepInduction generalizing j with
    | zero => exact continuous_const
    | one => exact continuous_const
    | more k ih _ =>
      simp only [moment_add_two, coeff_C_mul]
      cases j with
      | zero => simp only [coeff_X_mul_zero, mul_zero]; exact continuous_const
      | succ j =>
        simp only [coeff_X_mul]
        exact ((continuous_const.mul (continuous_const.add continuous_const)).mul
          continuous_id).mul (ih j)
  simp only [heatDiagonal, finsetSum_coeff, coeff_mul]
  apply continuous_finsetSum
  intro k _
  apply continuous_finsetSum
  intro a _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetSum
  intro b _
  exact continuous_const.mul (hm k b.2)

/-- A derivative-linked pair of simple split seeds stays disjoint under frozen backward heat. -/
theorem gaussianHeat_no_common_root_of_derivative {p q : ℝ[X]} {a s : ℝ}
    (hq : IsSimpleRealRooted q) (hder : q.derivative = C a * p) (hs : s ≤ 0) (t : ℝ) :
    ¬ ((gaussianHeat s p).IsRoot t ∧ (gaussianHeat s q).IsRoot t) := by
  rintro ⟨hp, hqroot⟩
  have hne := (gaussianHeat_isSimpleRealRooted hs hq).2.2.eval_derivative_ne_zero hqroot
  rw [derivative_gaussianHeat, hder, gaussianHeat_C_mul, eval_mul, eval_C,
    hp.eq_zero, mul_zero] at hne
  exact hne rfl

/-- For a nonnegative-coefficient input and its simple split antiderivative, the heat
specializations have no common real root at any nonnegative deformation parameter. -/
theorem heatDiagonal_no_common_root_of_derivative {p q : ℝ[X]} {a c : ℝ}
    (hq : IsSimpleRealRooted q) (hder : q.derivative = C a * p)
    (hp : HasNonnegCoeffs p) (hp₀ : p.coeff 0 ≠ 0) (hc : 0 ≤ c) (t : ℝ) :
    ¬ ((heatDiagonal c p).IsRoot t ∧ (heatDiagonal c q).IsRoot t) := by
  rintro ⟨hpt, hqt⟩
  have hc₀ : (heatDiagonal c p).coeff 0 ≠ 0 := by
    rw [heatDiagonal_coeff_zero]
    exact hp₀
  have hpne : heatDiagonal c p ≠ 0 := by
    intro he
    exact hc₀ (by rw [he, coeff_zero])
  have ht := roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne (hp.heatDiagonal hc)
    hc₀ t ((mem_roots hpne).mpr hpt)
  apply gaussianHeat_no_common_root_of_derivative hq hder
    (mul_nonpos_of_nonneg_of_nonpos hc ht.le) t
  simpa only [IsRoot.def, ← eval_heatDiagonal] using And.intro hpt hqt

end RealRooted
