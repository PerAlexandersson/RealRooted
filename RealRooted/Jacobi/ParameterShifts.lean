module

public import RealRooted.MultiplierSequence
public import RealRooted.EulerOperator.Shift
public import RealRooted.Jacobi.CoefficientFamily
public import RealRooted.JacobiDeformation.Pochhammer
import RealRooted.MultiplierSequence.ProperPosition
import RealRooted.MultiplierSequence.Laguerre

/-!
# Parameter shifts for the positive-coefficient Jacobi family

This file proves the two integral parameter-shift factorizations for
`jacobiCoefficientPolynomial`. The first uses consecutive shifted Euler
operators; the second uses iterated derivatives. It also characterizes
row-independent polynomials in the Euler operator that map the diagonal
family to an off-diagonal family.

The coefficient family, derivative recurrence, PF property, simple negative
roots, and adjacent interlacing come from `RealRooted.Jacobi.CoefficientFamily`.
-/

public section

open Finset Polynomial

noncomputable section

namespace RealRooted

open JacobiDeformation

/-- Apply consecutive shifted Euler operators with shifts
`a, a + 1, ..., a + r - 1`. -/
@[expose]
def eulerShiftRange (a : ℝ) : ℕ → ℝ[X] → ℝ[X]
  | 0, p => p
  | r + 1, p => eulerShift (a + r) (eulerShiftRange a r p)

/-- An empty consecutive Euler product is the identity. -/
@[simp]
theorem eulerShiftRange_zero (a : ℝ) (p : ℝ[X]) :
    eulerShiftRange a 0 p = p := by
  rfl

/-- Appending one factor applies the next shifted Euler operator. -/
@[simp]
theorem eulerShiftRange_succ (a : ℝ) (r : ℕ) (p : ℝ[X]) :
    eulerShiftRange a (r + 1) p =
      eulerShift (a + r) (eulerShiftRange a r p) := by
  rfl

/-- A consecutive shifted-Euler product multiplies coefficient `k` by the
rising factorial `(k + a)_r`. -/
@[simp]
theorem coeff_eulerShiftRange (a : ℝ) (r : ℕ) (p : ℝ[X]) (k : ℕ) :
    (eulerShiftRange a r p).coeff k =
      risingFactorial ((k : ℝ) + a) r * p.coeff k := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [eulerShiftRange_succ, coeff_eulerShift, ih, risingFactorial_succ]
      ring_nf

/-- Consecutive positive shifted Euler operators preserve directed
interlacing. -/
theorem StrictInterl.eulerShiftRange {f g : ℝ[X]} (h : StrictInterl f g)
    {a : ℝ} (ha : 0 < a) (r : ℕ) :
    StrictInterl (eulerShiftRange a r f) (eulerShiftRange a r g) := by
  induction r with
  | zero => simpa
  | succ r ih =>
      rw [eulerShiftRange_succ, eulerShiftRange_succ]
      apply eulerShift_strictInterl_of_pos (r := a + r)
      · positivity
      · exact ih

/-- Consecutive nonnegative shifted Euler operators preserve the polynomial
Pólya-frequency cone and hence nonpositive real-root location. -/
theorem IsPFPolynomial.eulerShiftRange {p : ℝ[X]} (hp : IsPFPolynomial p)
    {a : ℝ} (ha : 0 ≤ a) (r : ℕ) :
    IsPFPolynomial (eulerShiftRange a r p) := by
  induction r with
  | zero => simpa
  | succ r ih =>
      rw [eulerShiftRange_succ, ← diagonalOperator_natCast_add_eq_eulerShift]
      apply (isPFMultiplierSequence_natCast_add (by positivity)).diagonalOperator_isPF
      exact ih

/-- The polynomial whose value at `k` is the normalized product of the
consecutive Euler multipliers `k + a + 1, ..., k + a + r`. -/
@[expose]
def eulerShiftMultiplierPolynomial (a : ℝ) (r : ℕ) : ℝ[X] :=
  C (risingFactorial (a + 1) r)⁻¹ *
    (ascPochhammer ℝ r).comp (X + C (a + 1))

/-- Evaluation of the normalized Euler-multiplier polynomial is the
corresponding quotient of rising factorials. -/
@[simp]
theorem eval_eulerShiftMultiplierPolynomial (a : ℝ) (r : ℕ) (x : ℝ) :
    (eulerShiftMultiplierPolynomial a r).eval x =
      risingFactorial (x + a + 1) r / risingFactorial (a + 1) r := by
  simp [eulerShiftMultiplierPolynomial, risingFactorial]
  ring_nf

private theorem ring_choose_eq_fallingFactorial_div (x : ℝ) (k : ℕ) :
    Ring.choose x k = fallingFactorial x k / (k.factorial : ℝ) := by
  have hsmeval : (descPochhammer ℤ k).smeval x = fallingFactorial x k := by
    induction k with
    | zero => simp [fallingFactorial]
    | succ k ih =>
        rw [descPochhammer_succ_right, smeval_mul, ih,
          fallingFactorial_succ]
        simp [smeval_natCast]
  rw [Ring.choose_eq_smul]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hsmeval]

/-- The binomial-quotient coefficient used by `jacobiCoefficientPolynomial`
equals its falling-factorial/rising-factorial form. -/
theorem jacobiCoefficient_eq_fallingFactorial_div_risingFactorial
    (n k : ℕ) (a b : ℝ) :
    jacobiCoefficient n k a b =
      (n.choose k : ℝ) * fallingFactorial ((n : ℝ) + b) k /
        risingFactorial (a + 1) k := by
  rw [jacobiCoefficient, ring_choose_eq_fallingFactorial_div,
    ring_choose_eq_fallingFactorial_div]
  rw [risingFactorial_eq_fallingFactorial]
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  congr 2
  ring

private theorem risingFactorial_cross_mul (a : ℝ) (k r : ℕ) :
    risingFactorial (a + 1) k * risingFactorial (a + k + 1) r =
      risingFactorial (a + 1) r * risingFactorial (a + r + 1) k := by
  have hkr := risingFactorial_add (a + 1) k r
  have hrk := risingFactorial_add (a + 1) r k
  rw [show a + 1 + (k : ℝ) = a + k + 1 by ring_nf] at hkr
  rw [show a + 1 + (r : ℝ) = a + r + 1 by ring_nf] at hrk
  rw [Nat.add_comm] at hkr
  exact hkr.symm.trans hrk

/-- Clearing the positive scalar in the upper-parameter Euler factorization:
`E_(a+1) ... E_(a+r) H_n^(a+r,a+r) = (a+1)_r H_n^(a,a+r)`. -/
theorem _root_.RealRooted.JacobiCoefficientPolynomial.eulerShiftRange_diagonal_eq_C_mul
    (a : ℝ) (r n : ℕ) (ha : -1 < a) :
    eulerShiftRange (a + 1) r
        (jacobiCoefficientPolynomial n (a + r) (a + r)) =
      C (risingFactorial (a + 1) r) *
        jacobiCoefficientPolynomial n a (a + r) := by
  ext k
  rw [coeff_eulerShiftRange, coeff_C_mul,
    coeff_jacobiCoefficientPolynomial, coeff_jacobiCoefficientPolynomial]
  by_cases hk : k ≤ n
  · rw [ite_eq_left hk, ite_eq_left hk,
      jacobiCoefficient_eq_fallingFactorial_div_risingFactorial,
      jacobiCoefficient_eq_fallingFactorial_div_risingFactorial]
    have hden₁ : risingFactorial (a + 1) k ≠ 0 :=
      (risingFactorial_pos k (by linarith)).ne'
    have hden₂ : risingFactorial (a + (r : ℝ) + 1) k ≠ 0 :=
      (risingFactorial_pos k (by
        have hr : 0 ≤ (r : ℝ) := by positivity
        linarith)).ne'
    have hcross := risingFactorial_cross_mul a k r
    have hcross' :
        risingFactorial ((k : ℝ) + a + 1) r * risingFactorial (a + 1) k =
          risingFactorial (a + 1) r *
            risingFactorial (a + (r : ℝ) + 1) k := by
      rw [mul_comm]
      simpa only [add_assoc, add_comm, add_left_comm] using hcross
    field_simp
    calc
      risingFactorial ((k : ℝ) + (a + 1)) r * (n.choose k : ℝ) *
            fallingFactorial ((n : ℝ) + (a + r)) k *
              risingFactorial (a + 1) k =
          ((n.choose k : ℝ) *
              fallingFactorial ((n : ℝ) + (a + r)) k) *
            (risingFactorial ((k : ℝ) + a + 1) r *
              risingFactorial (a + 1) k) := by ring_nf
      _ = ((n.choose k : ℝ) *
              fallingFactorial ((n : ℝ) + (a + r)) k) *
            (risingFactorial (a + 1) r *
              risingFactorial (a + (r : ℝ) + 1) k) := by rw [hcross']
      _ = (n.choose k : ℝ) *
            fallingFactorial ((n : ℝ) + (a + r)) k *
              risingFactorial (a + (r : ℝ) + 1) k *
                risingFactorial (a + 1) r := by ring_nf
  · rw [ite_eq_right hk, ite_eq_right hk]
    simp

/-- The upper-parameter Euler factorization in quotient form. -/
theorem jacobiCoefficientPolynomial_eq_C_mul_eulerShiftRange
    (a : ℝ) (r n : ℕ) (ha : -1 < a) :
    jacobiCoefficientPolynomial n a (a + r) =
      C (risingFactorial (a + 1) r)⁻¹ *
        eulerShiftRange (a + 1) r
          (jacobiCoefficientPolynomial n (a + r) (a + r)) := by
  rw [RealRooted.JacobiCoefficientPolynomial.eulerShiftRange_diagonal_eq_C_mul a r n ha]
  rw [← mul_assoc, ← C_mul]
  simp [(risingFactorial_pos r (by linarith : 0 < a + 1)).ne']

/-- A polynomial in the Euler operator is the diagonal operator obtained by
evaluating that polynomial on the nonnegative integers. -/
theorem diagonalOperator_eulerShiftMultiplierPolynomial
    (a : ℝ) (r : ℕ) (p : ℝ[X]) :
    diagonalOperator (fun k ↦ (eulerShiftMultiplierPolynomial a r).eval k) p =
      C (risingFactorial (a + 1) r)⁻¹ * eulerShiftRange (a + 1) r p := by
  ext k
  rw [coeff_diagonalOperator, coeff_C_mul, coeff_eulerShiftRange,
    eval_eulerShiftMultiplierPolynomial]
  ring_nf

private theorem risingFactorial_add_one_succ (x : ℝ) (k : ℕ) :
    risingFactorial (x + 1) (k + 1) =
      (x + 1) * risingFactorial (x + 2) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [risingFactorial_succ (x + 1) (k + 1),
        risingFactorial_succ (x + 2) k, ih]
      push_cast
      ring_nf

/-- Iterating the derivative shift raises the first parameter by the number
of derivatives. The row index is offset so that the output remains row `n`. -/
theorem iterate_derivative_jacobiCoefficientPolynomial
    (a b : ℝ) (r n : ℕ) (ha : -1 < a) :
    (derivative^[r]) (jacobiCoefficientPolynomial (n + r) a b) =
      C (risingFactorial ((n : ℝ) + 1) r *
          risingFactorial ((n : ℝ) + b + 1) r /
            risingFactorial (a + 1) r) *
        jacobiCoefficientPolynomial n (a + r) b := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
      rw [show n + (r + 1) = (n + 1) + r by lia]
      rw [Function.iterate_succ_apply', ih (n + 1)]
      rw [Polynomial.derivative_C_mul,
        derivative_jacobiCoefficientPolynomial n (a := a + r) (b := b) (by
          have hr : 0 ≤ (r : ℝ) := by positivity
          linarith)]
      rw [← mul_assoc, ← C_mul]
      congr 1
      · congr 1
        have hn := risingFactorial_add_one_succ (n : ℝ) r
        have hnb := risingFactorial_add_one_succ ((n : ℝ) + b) r
        have ha0 : risingFactorial (a + 1) r ≠ 0 :=
          (risingFactorial_pos r (by linarith)).ne'
        have har0 : a + (r : ℝ) + 1 ≠ 0 := by
          have hr : 0 ≤ (r : ℝ) := by positivity
          linarith
        have har0' : 1 + a + (r : ℝ) ≠ 0 := by
          have hr : 0 ≤ (r : ℝ) := by positivity
          linarith
        rw [hn, hnb, risingFactorial_succ (a + 1) r]
        field_simp [ha0, har0, har0']
        push_cast
        ring_nf
        field_simp [har0']
        ring_nf
      · apply congrArg (fun x : ℝ ↦ jacobiCoefficientPolynomial n x b)
        push_cast
        ring_nf

/-- The lower-parameter derivative factorization from a diagonal row. -/
theorem jacobiCoefficientPolynomial_eq_C_mul_iterate_derivative
    (b : ℝ) (r n : ℕ) (hb : -1 < b) :
    jacobiCoefficientPolynomial n (b + r) b =
      C (risingFactorial (b + 1) r /
          (risingFactorial ((n : ℝ) + 1) r *
            risingFactorial ((n : ℝ) + b + 1) r)) *
        (derivative^[r]) (jacobiCoefficientPolynomial (n + r) b b) := by
  rw [iterate_derivative_jacobiCoefficientPolynomial b b r n hb]
  rw [← mul_assoc, ← C_mul]
  have hb0 : risingFactorial (b + 1) r ≠ 0 :=
    (risingFactorial_pos r (by linarith)).ne'
  have hn0 : risingFactorial ((n : ℝ) + 1) r ≠ 0 :=
    (risingFactorial_pos r (by positivity)).ne'
  have hnb0 : risingFactorial ((n : ℝ) + b + 1) r ≠ 0 :=
    (risingFactorial_pos r (by
      have hn : 0 ≤ (n : ℝ) := by positivity
      linarith)).ne'
  rw [show
    risingFactorial (b + 1) r /
          (risingFactorial ((n : ℝ) + 1) r *
            risingFactorial ((n : ℝ) + b + 1) r) *
        (risingFactorial ((n : ℝ) + 1) r *
          risingFactorial ((n : ℝ) + b + 1) r /
            risingFactorial (b + 1) r) = 1 by
      field_simp]
  simp

private theorem coeff_jacobiCoefficientPolynomial_self (a b : ℝ) (k : ℕ) :
    (jacobiCoefficientPolynomial k a b).coeff k =
      risingFactorial (b + 1) k / risingFactorial (a + 1) k := by
  rw [coeff_jacobiCoefficientPolynomial, ite_eq_left le_rfl,
    jacobiCoefficient_eq_fallingFactorial_div_risingFactorial]
  rw [Nat.choose_self]
  simp only [Nat.cast_one, one_mul]
  rw [risingFactorial_eq_fallingFactorial (b + 1) k]
  congr 1
  ring_nf

/-- An Euler-multiplier polynomial representing every row is forced at each
nonnegative integer by the top coefficient of that row. -/
theorem _root_.RealRooted.JacobiCoefficientPolynomial.eval_eq_risingFactorial_div
    {a b : ℝ} {p : ℝ[X]} (hb : -1 < b)
    (h : ∀ n, jacobiCoefficientPolynomial n a b =
      diagonalOperator (fun k ↦ p.eval (k : ℝ))
        (jacobiCoefficientPolynomial n b b))
    (k : ℕ) :
    p.eval (k : ℝ) =
      risingFactorial (b + 1) k / risingFactorial (a + 1) k := by
  have hk := congrArg (fun q : ℝ[X] ↦ q.coeff k) (h k)
  rw [coeff_jacobiCoefficientPolynomial_self,
    coeff_diagonalOperator, coeff_jacobiCoefficientPolynomial_self] at hk
  have hb0 : risingFactorial (b + 1) k ≠ 0 :=
    (risingFactorial_pos k (by linarith)).ne'
  rw [div_self hb0, mul_one] at hk
  exact hk.symm

private theorem mul_comp_X_add_C_eq_mul_of_diagonalOperator
    {a b : ℝ} {p : ℝ[X]} (ha : -1 < a) (hb : -1 < b)
    (h : ∀ n, jacobiCoefficientPolynomial n a b =
      diagonalOperator (fun k ↦ p.eval (k : ℝ))
        (jacobiCoefficientPolynomial n b b)) :
    (X + C (a + 1)) * p.comp (X + C 1) = (X + C (b + 1)) * p := by
  apply eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective Nat.cast_injective).mono
  rintro x ⟨k, rfl⟩
  simp only [Set.mem_ofPred_eq, eval_mul, eval_add, eval_X, eval_C, eval_comp]
  rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_num]
  rw [
    RealRooted.JacobiCoefficientPolynomial.eval_eq_risingFactorial_div
      hb h (k + 1),
    RealRooted.JacobiCoefficientPolynomial.eval_eq_risingFactorial_div
      hb h k]
  rw [risingFactorial_succ, risingFactorial_succ]
  have ha0 : risingFactorial (a + 1) k ≠ 0 :=
    (risingFactorial_pos k (by linarith)).ne'
  have hak0 : a + 1 + (k : ℝ) ≠ 0 := by
    have hk : 0 ≤ (k : ℝ) := by positivity
    linarith
  field_simp [ha0, hak0]
  ring_nf

private theorem natDegree_eq_sub_of_mul_comp_X_add_C_eq_mul
    {a b : ℝ} {p : ℝ[X]} (hp0 : p ≠ 0)
    (h : (X + C (a + 1)) * p.comp (X + C 1) =
      (X + C (b + 1)) * p) :
    (p.natDegree : ℝ) = b - a := by
  by_cases hd : p.natDegree = 0
  · have hpC := eq_C_of_natDegree_eq_zero hd
    have hc0 : p.coeff 0 ≠ 0 := by
      intro hc
      apply hp0
      rw [hpC, hc, C_0]
    have he := congrArg (fun q : ℝ[X] ↦ q.eval 0) h
    simp only [eval_mul, eval_add, eval_X, eval_C, eval_comp, zero_add] at he
    rw [hpC] at he
    simp only [eval_C] at he
    have hab : a - b = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hc0
      linear_combination he
    rw [hd]
    norm_num
    linarith
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hd
    have hm' : p.natDegree = m + 1 := by
      simpa only [Nat.succ_eq_add_one] using hm
    have hshift : p.comp (X + C 1) = taylor 1 p := by
      rw [taylor_apply]
    have htop : (taylor 1 p).coeff (m + 1) = p.coeff (m + 1) := by
      rw [← hm', coeff_taylor_natDegree, leadingCoeff]
    have hmid :
        (taylor 1 p).coeff m =
          p.coeff m + ((m : ℝ) + 1) * p.leadingCoeff := by
      rw [taylor_coeff]
      have hdeg : (hasseDeriv m p).natDegree < 2 := by
        have hle := natDegree_hasseDeriv_le p m
        lia
      rw [eval_eq_sum_range' hdeg]
      have h1 : (1 + m).choose m = m + 1 := by
        simp [add_comm]
      have h2 : p.coeff (1 + m) = p.leadingCoeff := by
        rw [add_comm, leadingCoeff, hm']
      simp [Finset.sum_range_succ, hasseDeriv_coeff, h1, h2]
    have h' :
        X * taylor 1 p + C (a + 1) * taylor 1 p =
          X * p + C (b + 1) * p := by
      rw [← hshift]
      calc
        X * p.comp (X + C 1) + C (a + 1) * p.comp (X + C 1) =
            (X + C (a + 1)) * p.comp (X + C 1) := by ring
        _ = (X + C (b + 1)) * p := h
        _ = X * p + C (b + 1) * p := by ring
    have he := congrArg (fun q : ℝ[X] ↦ q.coeff (m + 1)) h'
    rw [coeff_add, coeff_add, coeff_X_mul, coeff_X_mul,
      coeff_C_mul, coeff_C_mul, hmid, htop] at he
    have hlead : p.coeff (m + 1) = p.leadingCoeff := by
      rw [leadingCoeff, hm']
    rw [hlead] at he
    have hscalar : ((m : ℝ) + 1 + a - b) * p.leadingCoeff = 0 := by
      linear_combination he
    have hlead0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
    have hab := (mul_eq_zero.mp hscalar).resolve_right hlead0
    rw [hm']
    push_cast
    linarith

/-- A row-independent polynomial in the Euler operator maps the diagonal
Jacobi coefficient family to parameters `(a, b)` exactly when `b - a` is a
nonnegative integer. -/
theorem exists_diagonalOperator_jacobiCoefficientPolynomial_iff
    {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    (∃ p : ℝ[X], ∀ n,
      jacobiCoefficientPolynomial n a b =
        diagonalOperator (fun k ↦ p.eval (k : ℝ))
          (jacobiCoefficientPolynomial n b b)) ↔
      ∃ r : ℕ, b = a + r := by
  constructor
  · rintro ⟨p, hp⟩
    have hpEval :=
      RealRooted.JacobiCoefficientPolynomial.eval_eq_risingFactorial_div
        hb hp 0
    simp only [risingFactorial_zero, div_one] at hpEval
    have hp0 : p ≠ 0 := by
      intro hpz
      rw [hpz, eval_zero] at hpEval
      exact zero_ne_one hpEval
    have hshift := mul_comp_X_add_C_eq_mul_of_diagonalOperator ha hb hp
    have hdeg := natDegree_eq_sub_of_mul_comp_X_add_C_eq_mul hp0 hshift
    refine ⟨p.natDegree, ?_⟩
    linarith
  · rintro ⟨r, rfl⟩
    refine ⟨eulerShiftMultiplierPolynomial a r, fun n ↦ ?_⟩
    calc
      jacobiCoefficientPolynomial n a (a + r) =
          C (risingFactorial (a + 1) r)⁻¹ *
            eulerShiftRange (a + 1) r
              (jacobiCoefficientPolynomial n (a + r) (a + r)) :=
        jacobiCoefficientPolynomial_eq_C_mul_eulerShiftRange a r n ha
      _ = diagonalOperator
            (fun k ↦ (eulerShiftMultiplierPolynomial a r).eval (k : ℝ))
            (jacobiCoefficientPolynomial n (a + r) (a + r)) :=
        (diagonalOperator_eulerShiftMultiplierPolynomial a r _).symm

/-- Allowing a nonzero scalar depending on the row does not enlarge the
class of row-independent polynomial Euler multipliers. -/
theorem _root_.RealRooted.JacobiCoefficientPolynomial.exists_rowScalar_diagonalOperator_iff
    {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    (∃ (p : ℝ[X]) (c : ℕ → ℝ), p.eval 0 ≠ 0 ∧
      (∀ n, c n ≠ 0) ∧
      ∀ n, jacobiCoefficientPolynomial n a b =
        C (c n) * diagonalOperator (fun k ↦ p.eval (k : ℝ))
          (jacobiCoefficientPolynomial n b b)) ↔
      ∃ r : ℕ, b = a + r := by
  constructor
  · rintro ⟨p, c, hp0, _, h⟩
    have hc : ∀ n, c n = (p.eval 0)⁻¹ := by
      intro n
      have hcoeff := congrArg (fun q : ℝ[X] ↦ q.coeff 0) (h n)
      simp only [jacobiCoefficientPolynomial_coeff_zero, coeff_C_mul,
        coeff_diagonalOperator, Nat.cast_zero, mul_one] at hcoeff
      apply (mul_right_cancel₀ hp0)
      rw [inv_mul_cancel₀ hp0]
      simpa only [mul_comm] using hcoeff.symm
    have hnormalized : ∀ n, jacobiCoefficientPolynomial n a b =
        diagonalOperator
          (fun k ↦ (C (p.eval 0)⁻¹ * p).eval (k : ℝ))
          (jacobiCoefficientPolynomial n b b) := by
      intro n
      rw [h n, hc n]
      ext k
      simp only [coeff_C_mul, coeff_diagonalOperator, eval_mul, eval_C]
      ring
    exact (exists_diagonalOperator_jacobiCoefficientPolynomial_iff ha hb).mp
      ⟨C (p.eval 0)⁻¹ * p, hnormalized⟩
  · intro hr
    obtain ⟨p, hp⟩ :=
      (exists_diagonalOperator_jacobiCoefficientPolynomial_iff ha hb).mpr hr
    refine ⟨p, fun _ ↦ 1, ?_, fun _ ↦ one_ne_zero, ?_⟩
    · have hpEval :=
        RealRooted.JacobiCoefficientPolynomial.eval_eq_risingFactorial_div
          hb hp 0
      simp only [risingFactorial_zero, div_one] at hpEval
      norm_num at hpEval
      rw [hpEval]
      exact one_ne_zero
    · intro n
      simpa using hp n

/-- On an integral upper-parameter shift, the normalized product of linear
Euler multipliers is the unique polynomial in the Euler operator mapping
every diagonal row to the shifted family. -/
theorem _root_.RealRooted.JacobiCoefficientPolynomial.diagonalOperator_iff_eq_multiplierPolynomial
    (a : ℝ) (r : ℕ) (p : ℝ[X]) (ha : -1 < a) :
    (∀ n, jacobiCoefficientPolynomial n a (a + r) =
      diagonalOperator (fun k ↦ p.eval (k : ℝ))
        (jacobiCoefficientPolynomial n (a + r) (a + r))) ↔
      p = eulerShiftMultiplierPolynomial a r := by
  have hb : -1 < a + (r : ℝ) := by
    have hr : 0 ≤ (r : ℝ) := by positivity
    linarith
  have hmodel : ∀ n, jacobiCoefficientPolynomial n a (a + r) =
      diagonalOperator
        (fun k ↦ (eulerShiftMultiplierPolynomial a r).eval (k : ℝ))
        (jacobiCoefficientPolynomial n (a + r) (a + r)) := by
    intro n
    calc
      jacobiCoefficientPolynomial n a (a + r) =
          C (risingFactorial (a + 1) r)⁻¹ *
            eulerShiftRange (a + 1) r
              (jacobiCoefficientPolynomial n (a + r) (a + r)) :=
        jacobiCoefficientPolynomial_eq_C_mul_eulerShiftRange a r n ha
      _ = diagonalOperator
            (fun k ↦ (eulerShiftMultiplierPolynomial a r).eval (k : ℝ))
            (jacobiCoefficientPolynomial n (a + r) (a + r)) :=
        (diagonalOperator_eulerShiftMultiplierPolynomial a r _).symm
  constructor
  · intro hp
    apply eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective Nat.cast_injective).mono
    rintro x ⟨k, rfl⟩
    simp only [Set.mem_ofPred_eq]
    rw [
      RealRooted.JacobiCoefficientPolynomial.eval_eq_risingFactorial_div
        hb hp k,
      RealRooted.JacobiCoefficientPolynomial.eval_eq_risingFactorial_div
        hb hmodel k]
  · rintro rfl
    exact hmodel

end RealRooted
