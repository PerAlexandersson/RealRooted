module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import RealRooted.SimpleRoots
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic
import RealRooted.MaWang.Strong

/-!
# The circle criterion for Hessenberg recurrences

We use the monic recurrence associated with a real Laurent symbol with coefficient
one at degree minus one. The circle condition is expressed by nonnegativity of a
finite Chebyshev sum. Source: unpublished manuscript.
-/

@[expose] public section

open Polynomial
open scoped BigOperators
open scoped LaurentPolynomial

noncomputable section

namespace RealRooted.Toeplitz.Circle

private def circleEval (θ : ℝ) : ℝ[T;T⁻¹] →+* ℂ :=
  AddMonoidAlgebra.liftNCRingHom Complex.ofRealHom
    { toFun := fun k : Multiplicative ℤ => Complex.exp ((k.toAdd : ℂ) * θ * Complex.I)
      map_one' := by simp
      map_mul' := by
        intro k l
        change Complex.exp (((k.toAdd + l.toAdd : ℤ) : ℂ) * θ * Complex.I) = _
        rw [Int.cast_add, add_mul, add_mul, Complex.exp_add] }
    (fun _ _ => Commute.all _ _)

private lemma circleEval_monomial (θ a : ℝ) (k : ℤ) :
    circleEval θ (LaurentPolynomial.C a * LaurentPolynomial.T k) =
      a * Complex.exp ((k : ℂ) * θ * Complex.I) := by
  simp [circleEval, ← LaurentPolynomial.single_eq_C_mul_T]

@[fun_prop] private lemma continuous_circleEval (p : ℝ[T;T⁻¹]) :
    Continuous fun θ : ℝ => circleEval θ p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add]
    fun_prop
  | C_mul_T k a => simp_rw [circleEval_monomial]; fun_prop

private lemma integral_cos_int (k : ℤ) :
    (∫ θ : ℝ in 0..Real.pi, Real.cos (k * θ)) =
      if k = 0 then Real.pi else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [ite_eq_right hk,
      intervalIntegral.integral_comp_mul_left _ (Int.cast_ne_zero.mpr hk)]
    simp [integral_cos, Real.sin_int_mul_pi]

private lemma integral_circleEval (p : ℝ[T;T⁻¹]) :
    (∫ θ : ℝ in 0..Real.pi, (circleEval θ p).re) = Real.pi * p.coeff 0 := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Complex.add_re, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    have hp' : Continuous fun θ : ℝ => (circleEval θ p).re := by
      fun_prop
    have hq' : Continuous fun θ : ℝ => (circleEval θ q).re := by
      fun_prop
    rw [intervalIntegral.integral_add (hp'.intervalIntegrable _ _)
      (hq'.intervalIntegrable _ _), hp, hq]
    ring
  | C_mul_T k a =>
    simp_rw [circleEval_monomial, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    have hre (θ : ℝ) : (Complex.exp ((k : ℂ) * θ * Complex.I)).re =
        Real.cos ((k : ℝ) * θ) := by
      rw [← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_re]
    simp_rw [hre]
    rw [intervalIntegral.integral_const_mul, integral_cos_int]
    by_cases hk : k = 0 <;> simp [hk, ← LaurentPolynomial.single_eq_C_mul_T]
    ring

private lemma coeff_zero_nonneg (p : ℝ[T;T⁻¹])
    (hp : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, 0 ≤ (circleEval θ p).re) :
    0 ≤ p.coeff 0 := by
  have hi := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) Real.pi_pos.le hp
  rw [integral_circleEval] at hi
  exact nonneg_of_mul_nonneg_right hi Real.pi_pos

/-- The monic Hessenberg recurrence; the sum omits all negative row indices. -/
def row (b : ℕ →₀ ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X * row b n -
      b.sum fun k a => if k ≤ n then C a * row b (n - k) else 0
termination_by n => n

/-- The initial row is the constant polynomial one. -/
@[simp] theorem row_zero (b : ℕ →₀ ℝ) : row b 0 = 1 := by
  rw [row]

/-- The first row includes the diagonal coefficient of the symbol. -/
@[simp] theorem row_one (b : ℕ →₀ ℝ) : row b 1 = X - C (b 0) := by
  rw [row]
  simp only [row_zero, mul_one, Nat.le_zero, Finsupp.sum, Finset.sum_ite_eq',
    Finsupp.mem_support_iff]
  split_ifs <;> simp_all

/-- The defining recurrence with the negative indices suppressed. -/
theorem row_succ (b : ℕ →₀ ℝ) (n : ℕ) :
    row b (n + 1) = X * row b n -
      b.sum fun k a => if k ≤ n then C a * row b (n - k) else 0 := by
  rw [row]

/-- Every row is monic and has degree equal to its index. -/
theorem row_isMonicOfDegree (b : ℕ →₀ ℝ) (n : ℕ) :
    (row b n).IsMonicOfDegree n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [row_succ]
      have hlead := (Polynomial.isMonicOfDegree_X ℝ).mul (ih n (by lia))
      have hlead' : (X * row b n).IsMonicOfDegree (n + 1) := by
        simpa only [Nat.add_comm] using hlead
      apply hlead'.sub
      apply lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_)
        (Nat.lt_succ_self n)
      intro j hj
      dsimp only
      split_ifs with hjn
      · exact (Polynomial.natDegree_C_mul_le _ _).trans
          (by rw [(ih (n - j) (by lia)).natDegree_eq]; lia)
      · simp

/-- The degree of the row is its index. -/
@[simp] theorem row_natDegree (b : ℕ →₀ ℝ) (n : ℕ) : (row b n).natDegree = n :=
  (row_isMonicOfDegree b n).natDegree_eq

/-- The Chebyshev polynomial controlling the imaginary part on a circle. -/
def circlePolynomial (b : ℕ →₀ ℝ) (R : ℝ) : ℝ[X] :=
  -C R⁻¹ + b.sum fun k a => C (a * R ^ k) * Chebyshev.U ℝ ((k : ℤ) - 1)

/-- The circle hypothesis includes the endpoints of the cosine interval. -/
def CircleNonneg (b : ℕ →₀ ℝ) (R : ℝ) : Prop :=
  ∀ u ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ (circlePolynomial b R).eval u

/-- The scaled Laurent symbol with a real spectral parameter subtracted. -/
def symbol (b : ℕ →₀ ℝ) (R x : ℝ) : ℝ[T;T⁻¹] :=
  LaurentPolynomial.C R⁻¹ * LaurentPolynomial.T (-1) - LaurentPolynomial.C x +
    b.sum fun k a => LaurentPolynomial.C (a * R ^ k) * LaurentPolynomial.T k

private lemma circleEval_invert (p : ℝ[T;T⁻¹]) (θ : ℝ) :
    circleEval θ (LaurentPolynomial.invert p) = star (circleEval θ p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, star_add]
  | C_mul_T k a =>
    rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
      circleEval_monomial, circleEval_monomial]
    simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Int.cast_neg]
    rw [← Complex.exp_conj]
    congr 2
    simp [mul_assoc]

private lemma circleEval_symbol_im (b : ℕ →₀ ℝ) (R x θ : ℝ) :
    (circleEval θ (symbol b R x)).im =
      (circlePolynomial b R).eval (Real.cos θ) * Real.sin θ := by
  have hm (a : ℝ) (k : ℤ) :
      (circleEval θ (LaurentPolynomial.C a * LaurentPolynomial.T k)).im =
        a * Real.sin ((k : ℝ) * θ) := by
    rw [circleEval_monomial, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hc (a : ℝ) : circleEval θ (LaurentPolynomial.C a) = a := by
    simpa using circleEval_monomial θ a 0
  simp only [symbol, map_add, map_sub, hc, Complex.add_im, Complex.sub_im,
    Complex.ofReal_im, sub_zero, Finsupp.sum, map_sum, Complex.im_sum, hm,
    circlePolynomial, Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, add_mul, neg_mul, Finset.sum_mul]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro k hk
    rw [mul_assoc (b k * R ^ k), Chebyshev.U_real_cos]
    congr 2
    push_cast
    ring

private lemma energy_nonneg (b : ℕ →₀ ℝ) (R x : ℝ) (hQ : CircleNonneg b R)
    (g : ℝ[T;T⁻¹]) :
    0 ≤ (-(symbol b R x * g *
      (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) *
        LaurentPolynomial.invert g)).coeff 0 := by
  apply coeff_zero_nonneg
  intro θ hθ
  have him := circleEval_symbol_im b R x θ
  have hq := hQ (Real.cos θ) ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have ht (k : ℤ) : circleEval θ (LaurentPolynomial.T k) =
      Complex.exp ((k : ℂ) * θ * Complex.I) := by
    simpa using circleEval_monomial θ 1 k
  simp only [map_neg, map_mul, map_sub, circleEval_invert, ht]
  have he : Complex.exp (θ * Complex.I) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using Complex.exp_mul_I θ
  have hen : Complex.exp (-θ * Complex.I) =
      (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, neg_mul,
      sub_eq_add_neg, Complex.ofReal_cos, Complex.ofReal_sin]
  simp only [Int.cast_one, Int.cast_neg, one_mul, neg_one_mul, he, hen,
    Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [him]
  convert mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hq)
    (mul_nonneg (add_nonneg (sq_nonneg (circleEval θ g).re)
      (sq_nonneg (circleEval θ g).im)) (sq_nonneg (Real.sin θ))) using 1
  ring

private lemma coeff_skew_mul_invert (S g : ℝ[T;T⁻¹]) :
    (S * (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) *
      LaurentPolynomial.invert g).coeff 0 =
        g.coeff.sum fun j a => (S.coeff (j - 1) - S.coeff (j + 1)) * a := by
  have hi := LaurentPolynomial.invert_apply
    (S * (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) *
      LaurentPolynomial.invert g) 0
  simp only [neg_zero] at hi
  rw [← hi]
  simp only [map_mul, map_sub, LaurentPolynomial.invert_T, neg_neg]
  rw [LaurentPolynomial.involutive_invert g]
  rw [AddMonoidAlgebra.coeff_mul_apply_right]
  simp only [mul_sub, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    LaurentPolynomial.T, AddMonoidAlgebra.coeff_mul_single_apply,
    LaurentPolynomial.invert_apply, mul_one]
  congr 1
  funext j a
  congr 2 <;> congr 1 <;> lia

/-- The finite autocorrelation of the real coefficients of a Laurent polynomial. -/
def correlation (g : ℝ[T;T⁻¹]) (k : ℤ) : ℝ :=
  (g * LaurentPolynomial.invert g).coeff k

private lemma correlation_neg (g : ℝ[T;T⁻¹]) (k : ℤ) :
    correlation g (-k) = correlation g k := by
  rw [correlation, ← LaurentPolynomial.invert_apply, map_mul,
    LaurentPolynomial.involutive_invert g, mul_comm]
  rfl

/-- Autocorrelations are the sums of products of coefficients at a fixed separation. -/
theorem correlation_eq_sum (g : ℝ[T;T⁻¹]) (k : ℤ) :
    correlation g k = g.coeff.sum (fun j a => a * g.coeff (j + k)) := by
  rw [← correlation_neg g k, correlation, AddMonoidAlgebra.coeff_mul_apply_left]
  simp only [LaurentPolynomial.invert_apply]
  congr 1
  funext j a
  congr 2
  lia

/-- The quadratic form associated with the Chebyshev circle polynomial. -/
def quadraticForm (b : ℕ →₀ ℝ) (R : ℝ) (g : ℝ[T;T⁻¹]) : ℝ :=
  -R⁻¹ * (correlation g 0 - correlation g 2) +
    b.sum fun k a => a * R ^ k * (correlation g ((k : ℤ) - 1) -
      correlation g ((k : ℤ) + 1))

/-- A finite constant-term identity: only the two boundary coefficients survive. -/
theorem boundary_identity (S g : ℝ[T;T⁻¹]) (n : ℕ)
    (hg : ∀ j ∈ g.coeff.support, (1 : ℤ) ≤ j ∧ j ≤ n)
    (hS : S.coeff 0 = 1) (hz : ∀ j : ℤ, 1 ≤ j → j ≤ n → S.coeff j = 0) :
    (S * (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) *
      LaurentPolynomial.invert g).coeff 0 =
        g.coeff 1 - S.coeff (n + 1) * g.coeff n := by
  rw [coeff_skew_mul_invert]
  have he : g.coeff.sum (fun j a => (S.coeff (j - 1) - S.coeff (j + 1)) * a) =
      g.coeff.sum (fun j a =>
        (if j = 1 then a else 0) - (if j = n then S.coeff (n + 1) * a else 0)) := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hj1, hjn⟩ := hg j hj
    by_cases h1 : j = 1 <;> by_cases hn : j = n
    · simp_all [sub_mul]
    · have hnext : S.coeff (j + 1) = 0 := hz _ (by lia) (by lia)
      simp_all
    · have hprev : S.coeff (j - 1) = 0 := hz _ (by lia) (by lia)
      simp_all
    · have hprev : S.coeff (j - 1) = 0 := hz _ (by lia) (by lia)
      have hnext : S.coeff (j + 1) = 0 := hz _ (by lia) (by lia)
      simp_all
  rw [he, Finsupp.sum_sub]
  simp only [Finsupp.sum, Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs <;> simp_all

private lemma symbol_mul_coeff (b : ℕ →₀ ℝ) (R x : ℝ) (g : ℝ[T;T⁻¹]) (j : ℤ) :
    (symbol b R x * g).coeff j = R⁻¹ * g.coeff (j + 1) - x * g.coeff j +
      b.sum (fun k a => a * R ^ k * g.coeff (j - k)) := by
  have hm (a : ℝ) (k : ℤ) :
      (LaurentPolynomial.C a * LaurentPolynomial.T k * g).coeff j =
        a * g.coeff (j - k) := by
    rw [← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single_mul_apply]
    congr 2
    lia
  have hc (a : ℝ) : (LaurentPolynomial.C a * g).coeff j = a * g.coeff j := by
    simpa using hm a 0
  simp only [symbol, Finsupp.sum, add_mul, sub_mul, Finset.sum_mul,
    AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub, Finsupp.add_apply,
    Finsupp.sub_apply, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, hm, hc,
    sub_neg_eq_add]

private lemma quadraticForm_eq_coeff (b : ℕ →₀ ℝ) (R x : ℝ) (g : ℝ[T;T⁻¹]) :
    quadraticForm b R g = -(symbol b R x * g *
      (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) *
        LaurentPolynomial.invert g).coeff 0 := by
  have he : symbol b R x * g * (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) *
      LaurentPolynomial.invert g = symbol b R x *
        ((LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) *
          (g * LaurentPolynomial.invert g)) := by ring
  have hc (j : ℤ) : ((LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) *
      (g * LaurentPolynomial.invert g)).coeff j =
        correlation g (j - 1) - correlation g (j + 1) := by
    simp only [sub_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, correlation]
    congr 1 <;> congr 1 <;> lia
  rw [he, symbol_mul_coeff]
  simp only [hc, zero_add, zero_sub]
  have hfirst : correlation g (1 - 1) - correlation g (1 + 1) =
      correlation g 0 - correlation g 2 := by norm_num
  rw [hfirst, correlation_neg g 1, sub_self, mul_zero, sub_zero]
  have hs : b.sum (fun k a => a * R ^ k *
      (correlation g (- (k : ℤ) - 1) - correlation g (-(k : ℤ) + 1))) =
      -b.sum (fun k a => a * R ^ k *
        (correlation g ((k : ℤ) - 1) - correlation g ((k : ℤ) + 1))) := by
    rw [← Finsupp.sum_neg]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only
    rw [show -(k : ℤ) - 1 = -((k : ℤ) + 1) by lia,
      show -(k : ℤ) + 1 = -((k : ℤ) - 1) by lia, correlation_neg, correlation_neg]
    ring
  rw [hs, quadraticForm]
  ring

/-- A nonnegative circle polynomial makes its correlation quadratic form nonnegative. -/
theorem quadraticForm_nonneg (b : ℕ →₀ ℝ) (R : ℝ) (hQ : CircleNonneg b R)
    (g : ℝ[T;T⁻¹]) : 0 ≤ quadraticForm b R g := by
  rw [quadraticForm_eq_coeff b R 0 g]
  simpa only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply] using
    energy_nonneg b R 0 hQ g

private lemma symbol_mul_coeff_succ (b : ℕ →₀ ℝ) (R x : ℝ) (g : ℝ[T;T⁻¹]) (m : ℕ)
    (hneg : ∀ j : ℤ, j ≤ 0 → g.coeff j = 0)
    (hg : ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 →
      g.coeff j = R ^ j * (row b (j - 1)).eval x) :
    (symbol b R x * g).coeff (m + 1) =
      R⁻¹ * g.coeff (m + 2) - R ^ (m + 1) * (row b (m + 1)).eval x := by
  rw [symbol_mul_coeff]
  have hgs : b.sum (fun k a => a * R ^ k * g.coeff ((m : ℤ) + 1 - k)) =
      R ^ (m + 1) * b.sum (fun k a =>
        if k ≤ m then a * (row b (m - k)).eval x else 0) := by
    rw [Finsupp.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only
    by_cases hkm : k ≤ m
    · have hj : (m : ℤ) + 1 - k = (m + 1 - k : ℕ) := by lia
      rw [hj, hg _ (by lia) (by lia), ite_eq_left hkm]
      have hp : R ^ k * R ^ (m + 1 - k) = R ^ (m + 1) := by
        rw [← pow_add, Nat.add_sub_of_le (by lia : k ≤ m + 1)]
      have hi : m + 1 - k - 1 = m - k := by lia
      rw [hi]
      linear_combination (b k * (row b (m - k)).eval x) * hp
    · rw [hneg _ (by lia), ite_eq_right hkm]
      ring
  have hgm : g.coeff ((m : ℤ) + 1) = R ^ (m + 1) * (row b m).eval x := by
    simpa using hg (m + 1) (by lia) (by lia)
  rw [hgs, hgm]
  have hr := congrArg (fun p : ℝ[X] => p.eval x) (row_succ b m)
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Finsupp.sum,
    Polynomial.eval_finsetSum, apply_ite, Polynomial.eval_C, Polynomial.eval_zero] at hr
  rw [show (m : ℤ) + 1 + 1 = (m : ℤ) + 2 by lia]
  rw [hr]
  simp only [Finsupp.sum]
  ring

/-- The finitely supported vector used in the energy identity at a row root. -/
def fundamentalVector (b : ℕ →₀ ℝ) (R x : ℝ) (n : ℕ) : ℝ[T;T⁻¹] :=
  AddMonoidAlgebra.ofCoeff <| Finsupp.onFinset (Finset.Icc (1 : ℤ) n)
    (fun j => if 1 ≤ j ∧ j ≤ n then R ^ j.toNat * (row b (j.toNat - 1)).eval x else 0)
    (by intro j hj; by_contra hn; simp only [Finset.mem_Icc] at hn; simp [hn] at hj)

private lemma fundamentalVector_coeff (b : ℕ →₀ ℝ) (R x : ℝ) (n : ℕ) (j : ℤ) :
    (fundamentalVector b R x n).coeff j =
      if 1 ≤ j ∧ j ≤ n then R ^ j.toNat * (row b (j.toNat - 1)).eval x else 0 := rfl

private lemma fundamentalVector_support (b : ℕ →₀ ℝ) (R x : ℝ) (n : ℕ) :
    ∀ j ∈ (fundamentalVector b R x n).coeff.support, (1 : ℤ) ≤ j ∧ j ≤ n := by
  intro j hj
  by_contra hn
  have hne := Finsupp.mem_support_iff.mp hj
  rw [fundamentalVector_coeff, ite_eq_right hn] at hne
  exact hne rfl

private lemma fundamentalVector_coeff_of_root (b : ℕ →₀ ℝ) (R x : ℝ) (n : ℕ)
    (hx : (row b n).IsRoot x) (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n + 1) :
    (fundamentalVector b R x n).coeff j = R ^ j * (row b (j - 1)).eval x := by
  rw [fundamentalVector_coeff]
  by_cases h : j ≤ n
  · simp [hj, h]
  · have he : j = n + 1 := by lia
    subst j
    simp [hx.eq_zero]

private lemma fundamentalVector_symbol_coeffs (b : ℕ →₀ ℝ) (R x : ℝ) (n : ℕ)
    (hR : R ≠ 0) (hn : 1 ≤ n) (hx : (row b n).IsRoot x) :
    let g := fundamentalVector b R x n;
    let S := symbol b R x * g
    S.coeff 0 = 1 ∧ (∀ j : ℤ, 1 ≤ j → j ≤ n → S.coeff j = 0) ∧
      S.coeff (n + 1) = -R ^ (n + 1) * (row b (n + 1)).eval x := by
  dsimp only
  let g := fundamentalVector b R x n
  have hneg (j : ℤ) (hj : j ≤ 0) : g.coeff j = 0 := by
    rw [fundamentalVector_coeff, ite_eq_right (by lia)]
  have hgs (m : ℕ) (hm : m ≤ n) := symbol_mul_coeff_succ b R x g m hneg
    (fun j hj hjm => fundamentalVector_coeff_of_root b R x n hx j hj (by lia))
  have hg1 : g.coeff 1 = R := by simp [g, fundamentalVector_coeff, hn]
  refine ⟨?_, ?_, ?_⟩
  · rw [symbol_mul_coeff, zero_add, hg1, hneg 0 le_rfl, mul_zero, sub_zero]
    have hs : b.sum (fun k a => a * R ^ k * g.coeff (0 - k)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      dsimp only
      rw [hneg _ (by lia), mul_zero]
    rw [hs, add_zero, inv_mul_cancel₀ hR]
  · intro j hj hjn
    lift j to ℕ using (by lia : 0 ≤ j)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : j ≠ 0)
    rw [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 by lia, hgs m (by lia)]
    have hgv := fundamentalVector_coeff_of_root b R x n hx (m + 2) (by lia) (by lia)
    have hcast : ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 := by lia
    rw [hcast] at hgv
    rw [hgv, show m + 2 - 1 = m + 1 by lia, pow_succ R (m + 1)]
    field_simp
    ring
  · rw [hgs n le_rfl]
    have ht : g.coeff ((n : ℤ) + 2) = 0 := by
      rw [fundamentalVector_coeff, ite_eq_right (by lia)]
    rw [ht]
    ring

/-- The exact circle energy identity at a real zero of a recurrence row. -/
private lemma energy_identity_coeff (b : ℕ →₀ ℝ) (R x : ℝ) (n : ℕ)
    (hR : R ≠ 0) (hn : 1 ≤ n) (hx : (row b n).IsRoot x) :
    let g := fundamentalVector b R x n;
    -R ^ (2 * n + 1) * (row b (n - 1)).eval x * (row b (n + 1)).eval x =
      R - (symbol b R x * g * (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) *
        LaurentPolynomial.invert g).coeff 0 := by
  dsimp only
  obtain ⟨hzero, hinterior, hlast⟩ := fundamentalVector_symbol_coeffs b R x n hR hn hx
  have hi := boundary_identity (symbol b R x * fundamentalVector b R x n)
    (fundamentalVector b R x n) n (fundamentalVector_support b R x n) hzero hinterior
  rw [hlast] at hi
  have hg1 : (fundamentalVector b R x n).coeff 1 = R := by
    simp [fundamentalVector_coeff, hn]
  have hgn : (fundamentalVector b R x n).coeff n =
      R ^ n * (row b (n - 1)).eval x := by
    simp [fundamentalVector_coeff, hn]
  rw [hi, hg1, hgn]
  have hp : R ^ (n + 1) * R ^ n = R ^ (2 * n + 1) := by
    rw [← pow_add]
    congr 1
    lia
  linear_combination -((row b (n - 1)).eval x * (row b (n + 1)).eval x) * hp

/-- The exact correlation energy identity at a real zero of a recurrence row.
Source: unpublished manuscript. -/
theorem energy_identity (b : ℕ →₀ ℝ) (R x : ℝ) (n : ℕ)
    (hR : R ≠ 0) (hn : 1 ≤ n) (hx : (row b n).IsRoot x) :
    -R ^ (2 * n + 1) * (row b (n - 1)).eval x * (row b (n + 1)).eval x =
      R + quadraticForm b R (fundamentalVector b R x n) := by
  rw [quadraticForm_eq_coeff b R x]
  exact energy_identity_coeff b R x n hR hn hx

/-- Opposite signs at successive row roots suffice for simplicity and interlacing.
This is the algebraic induction used after establishing the circle energy estimate. -/
theorem strictInterl_of_root_sign (b : ℕ →₀ ℝ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, (row b (n + 1)).IsRoot x →
      (row b (n + 2)).eval x * (row b n).eval x < 0) (n : ℕ) :
    StrictInterl (row b n) (row b (n + 1)) ∧
      HasSimpleRoots (row b n) ∧ HasSimpleRoots (row b (n + 1)) := by
  have hpos (k : ℕ) : HasPosLeadingCoeff (row b k) := by
    change 0 < (row b k).leadingCoeff
    rw [(row_isMonicOfDegree b k).monic.leadingCoeff]
    exact zero_lt_one
  have hinter : ∀ k : ℕ, Interlaces (row b k) (row b (k + 1)) := by
    intro k
    induction k with
    | zero => simp [Interlaces, ListInterlaces, X_sub_C_ne_zero]
    | succ k ih =>
      exact (MaWang.strictInterl_of_interlaces_eval_mul_neg_succ ih (hpos k)
        (hpos (k + 2)) (by simp) (hsign k)).toInterlaces (by simp)
  have hno : ∀ x : ℝ, ¬ ((row b n).IsRoot x ∧ (row b (n + 1)).IsRoot x) := by
    cases n with
    | zero => simp
    | succ n =>
      intro x hx
      have := hsign n x hx.1
      simp [hx.2.eq_zero] at this
  exact ⟨(hinter n).toStrictInterl,
    ((hinter n).toStrictInterl.hasSimpleRoots_of_no_common_root hno)⟩

/-- The product of the adjacent rows is strictly negative at a row root. -/
theorem eval_mul_neg_of_circleNonneg (b : ℕ →₀ ℝ) (R : ℝ)
    (hR : 0 < R) (hQ : CircleNonneg b R) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : (row b n).IsRoot x) :
    (row b (n + 1)).eval x * (row b (n - 1)).eval x < 0 := by
  have hi := energy_identity b R x n hR.ne' hn hx
  have he := quadraticForm_nonneg b R hQ (fundamentalVector b R x n)
  have hp : R ^ (2 * n + 1) *
      ((row b (n + 1)).eval x * (row b (n - 1)).eval x) < 0 := by
    nlinarith
  exact neg_of_mul_neg_right hp (pow_pos hR _).le

/-- Consecutive rows under the circle condition have no common real root. -/
theorem not_isRoot_succ_of_circleNonneg (b : ℕ →₀ ℝ) (R : ℝ)
    (hR : 0 < R) (hQ : CircleNonneg b R) (n : ℕ) (x : ℝ)
    (hx : (row b n).IsRoot x) : ¬ (row b (n + 1)).IsRoot x := by
  cases n with
  | zero => simp at hx
  | succ n =>
    intro hnext
    have hs := eval_mul_neg_of_circleNonneg b R hR hQ (n + 1) (by lia) x hx
    simp [hnext.eq_zero] at hs

/-- The circle criterion: consecutive rows interlace and have only simple real roots.
Together with monicity and exact degree, this gives exactly `n` distinct real zeros
for the row of index `n`. Source: unpublished manuscript. -/
theorem strictInterl_of_circleNonneg (b : ℕ →₀ ℝ) (R : ℝ)
    (hR : 0 < R) (hQ : CircleNonneg b R) (n : ℕ) :
    StrictInterl (row b n) (row b (n + 1)) ∧
      HasSimpleRoots (row b n) ∧ HasSimpleRoots (row b (n + 1)) := by
  apply strictInterl_of_root_sign
  intro k x hx
  simpa using eval_mul_neg_of_circleNonneg b R hR hQ (k + 1) (by lia) x hx

/-- Every recurrence row has exactly its index many distinct real zeros. -/
theorem roots_card_of_circleNonneg (b : ℕ →₀ ℝ) (R : ℝ)
    (hR : 0 < R) (hQ : CircleNonneg b R) (n : ℕ) :
    (row b n).Splits ∧ (row b n).roots.Nodup ∧ (row b n).roots.card = n := by
  obtain ⟨hi, hs, _⟩ := strictInterl_of_circleNonneg b R hR hQ n
  exact ⟨hi.1.2, hs.roots_nodup, by
    rw [Polynomial.splits_iff_card_roots.mp hi.1.2, row_natDegree]⟩

end RealRooted.Toeplitz.Circle
