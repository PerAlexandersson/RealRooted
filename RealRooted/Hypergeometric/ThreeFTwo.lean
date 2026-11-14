module

public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Complex.Basic
public import RealRooted.MatrixInterlacing.ThreeBidiagonalProduction
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real
import RealRooted.Interlacing.ReversalCommonFactor
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Terminating three-over-two hypergeometric polynomials

We use the parameters of H. Lima, *Multiple orthogonal polynomials associated
with branched continued fractions for ratios of hypergeometric series*,
arXiv:2208.03539v2, (6.6) and (8.9), with `r = s = 2` and `λ₁ = 1`, `λ₂ = 2`.
The polynomial here has constant coefficient one; Lima uses its monic multiple.
The upper parameters are `b₁ + m, b₂ + m - 1` in positive even degree `2m`,
and `b₁ + m, b₂ + m` in odd degree `2m + 1`.

We prove the four-term recurrence coefficientwise and identify every monic row
with the characteristic polynomial of Lima's three-bidiagonal production section.
The matrix theorem gives simple positive zeros and strict consecutive interlacing
in the strict range (8.1). A coefficientwise limit gives splitting at the weak
parameter boundary; coefficient alternation excludes nonpositive real zeros.
-/

@[expose] public section

open Polynomial Finset

noncomputable section

namespace RealRooted.Hypergeometric

/-- The first upper parameter in Lima's terminating three-over-two family. -/
def upperOne (b : ℝ) (n : ℕ) : ℝ := b + (n / 2 : ℕ)

/-- The second upper parameter; its unused degree-zero value is set to `b`. -/
def upperTwo (b : ℝ) (n : ℕ) : ℝ := b + ((n - 1) / 2 : ℕ)

/-- The coefficient of the terminating three-over-two series, in binomial form. -/
def threeFTwoCoeff (a₁ a₂ b₁ b₂ : ℝ) (n k : ℕ) : ℝ :=
  (-1) ^ k * (n.choose k : ℝ) *
    (ascPochhammer ℝ k).eval (upperOne b₁ n) *
    (ascPochhammer ℝ k).eval (upperTwo b₂ n) /
    ((ascPochhammer ℝ k).eval a₁ * (ascPochhammer ℝ k).eval a₂)

/-- The finite series `₃F₂(-n, B₁,n, B₂,n; a₁, a₂; X)` with constant term one. -/
def threeFTwo (a₁ a₂ b₁ b₂ : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ range (n + 1), monomial k (threeFTwoCoeff a₁ a₂ b₁ b₂ n k)

/-- The first parameter is `b + m` in even degree. -/
@[simp] theorem upperOne_even (b : ℝ) (m : ℕ) : upperOne b (2 * m) = b + m := by
  simp [upperOne]

/-- The first parameter is `b + m` in odd degree. -/
@[simp] theorem upperOne_odd (b : ℝ) (m : ℕ) : upperOne b (2 * m + 1) = b + m := by
  simp [upperOne, Nat.add_div]

/-- The second parameter is `b + m - 1` in positive even degree. -/
theorem upperTwo_even (b : ℝ) {m : ℕ} (hm : m ≠ 0) :
    upperTwo b (2 * m) = b + m - 1 := by
  have hm' : 1 ≤ m := by lia
  have hdiv : (2 * m - 1) / 2 = m - 1 := by lia
  simp only [upperTwo, hdiv, Nat.cast_sub hm', Nat.cast_one]
  ring

/-- The second parameter is `b + m` in odd degree. -/
@[simp] theorem upperTwo_odd (b : ℝ) (m : ℕ) : upperTwo b (2 * m + 1) = b + m := by
  simp [upperTwo]

/-- Positive base parameters give positive upper parameters in every degree. -/
theorem upperParameters_pos {b₁ b₂ : ℝ} (h₁ : 0 < b₁) (h₂ : 0 < b₂) (n : ℕ) :
    0 < upperOne b₁ n ∧ 0 < upperTwo b₂ n := by
  constructor <;> dsimp [upperOne, upperTwo] <;> positivity

/-- The binomial coefficient formula is the usual finite Pochhammer formula. -/
theorem threeFTwoCoeff_eq_pochhammer (a₁ a₂ b₁ b₂ : ℝ) (n k : ℕ) :
    threeFTwoCoeff a₁ a₂ b₁ b₂ n k =
      (ascPochhammer ℝ k).eval (-(n : ℝ)) *
        (ascPochhammer ℝ k).eval (upperOne b₁ n) *
        (ascPochhammer ℝ k).eval (upperTwo b₂ n) /
        ((ascPochhammer ℝ k).eval a₁ * (ascPochhammer ℝ k).eval a₂ * k.factorial) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  simp only [threeFTwoCoeff]
  field_simp

/-- Coefficients outside the terminating support vanish. -/
theorem threeFTwoCoeff_eq_zero_of_lt {n k : ℕ} (h : n < k) (a₁ a₂ b₁ b₂ : ℝ) :
    threeFTwoCoeff a₁ a₂ b₁ b₂ n k = 0 := by
  simp [threeFTwoCoeff, Nat.choose_eq_zero_of_lt h]

/-- The coefficient formula holds at every natural index, including outside the support. -/
@[simp] theorem coeff_threeFTwo (a₁ a₂ b₁ b₂ : ℝ) (n k : ℕ) :
    (threeFTwo a₁ a₂ b₁ b₂ n).coeff k = threeFTwoCoeff a₁ a₂ b₁ b₂ n k := by
  classical
  by_cases hk : k < n + 1
  · simp [threeFTwo, coeff_monomial, hk]
  · simp [threeFTwo, coeff_monomial, hk,
      threeFTwoCoeff_eq_zero_of_lt (show n < k by lia)]

/-- The zeroth series coefficient is one for all real parameters. -/
@[simp] theorem threeFTwoCoeff_zero (a₁ a₂ b₁ b₂ : ℝ) (n : ℕ) :
    threeFTwoCoeff a₁ a₂ b₁ b₂ n 0 = 1 := by
  simp [threeFTwoCoeff]

/-- The constant coefficient is one for all real parameters. -/
theorem coeff_zero_threeFTwo (a₁ a₂ b₁ b₂ : ℝ) (n : ℕ) :
    (threeFTwo a₁ a₂ b₁ b₂ n).coeff 0 = 1 := by
  simp

/-- The series is never the zero polynomial. -/
theorem threeFTwo_ne_zero (a₁ a₂ b₁ b₂ : ℝ) (n : ℕ) :
    threeFTwo a₁ a₂ b₁ b₂ n ≠ 0 := by
  intro h
  have := congrArg (fun p : ℝ[X] => p.coeff 0) h
  simp [threeFTwoCoeff] at this

/-- Degree zero has value one. -/
@[simp] theorem threeFTwo_zero (a₁ a₂ b₁ b₂ : ℝ) :
    threeFTwo a₁ a₂ b₁ b₂ 0 = 1 := by
  simp [threeFTwo, threeFTwoCoeff]

/-- The terminating series has degree at most its terminating index. -/
theorem natDegree_threeFTwo_le (a₁ a₂ b₁ b₂ : ℝ) (n : ℕ) :
    (threeFTwo a₁ a₂ b₁ b₂ n).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simpa using threeFTwoCoeff_eq_zero_of_lt hk a₁ a₂ b₁ b₂

/-- Alternating coefficients are strictly positive throughout the support. -/
theorem threeFTwoCoeff_alternating_pos {a₁ a₂ b₁ b₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    {n k : ℕ} (hk : k ≤ n) :
    0 < (-1 : ℝ) ^ k * threeFTwoCoeff a₁ a₂ b₁ b₂ n k := by
  have hchoose : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  obtain ⟨hu₁, hu₂⟩ := upperParameters_pos hb₁ hb₂ n
  have hsign : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by
    rw [← mul_pow]
    simp
  dsimp [threeFTwoCoeff]
  rw [mul_div_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, hsign, one_mul]
  simpa only [mul_div_assoc] using div_pos (mul_pos (mul_pos hchoose (ascPochhammer_pos k _ hu₁))
    (ascPochhammer_pos k _ hu₂))
    (mul_pos (ascPochhammer_pos k _ ha₁) (ascPochhammer_pos k _ ha₂))

/-- Positive parameters prevent any loss of degree, including at the weak boundary. -/
theorem natDegree_threeFTwo {a₁ a₂ b₁ b₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (n : ℕ) :
    (threeFTwo a₁ a₂ b₁ b₂ n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_threeFTwo_le _ _ _ _ _)
  rw [coeff_threeFTwo]
  exact right_ne_zero_of_mul (threeFTwoCoeff_alternating_pos ha₁ ha₂ hb₁ hb₂
    (le_refl n)).ne'

/-- The first-order coefficient recurrence, with the terminating factor `k - n`.
It holds at every index, so it also includes the support boundary `k = n`. -/
theorem threeFTwoCoeff_succ {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (b₁ b₂ : ℝ) (n k : ℕ) :
    threeFTwoCoeff a₁ a₂ b₁ b₂ n (k + 1) *
        ((a₁ + k) * (a₂ + k) * (k + 1)) =
      threeFTwoCoeff a₁ a₂ b₁ b₂ n k *
        (((k : ℝ) - n) * (upperOne b₁ n + k) * (upperTwo b₂ n + k)) := by
  rw [threeFTwoCoeff_eq_pochhammer, threeFTwoCoeff_eq_pochhammer]
  simp only [ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have h₁ := (ascPochhammer_pos k a₁ ha₁).ne'
  have h₂ := (ascPochhammer_pos k a₂ ha₂).ne'
  have hs₁ : a₁ + (k : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hs₂ : a₂ + (k : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The constant term and the first-order coefficient recurrence characterize
the polynomial, without a separate degree or support hypothesis. -/
theorem eq_threeFTwo_of_coeff_recurrence {a₁ a₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (b₁ b₂ : ℝ) (n : ℕ) (p : ℝ[X])
    (hzero : p.coeff 0 = 1)
    (hstep : ∀ k : ℕ, p.coeff (k + 1) * ((a₁ + k) * (a₂ + k) * (k + 1)) =
      p.coeff k * (((k : ℝ) - n) * (upperOne b₁ n + k) * (upperTwo b₂ n + k))) :
    p = threeFTwo a₁ a₂ b₁ b₂ n := by
  ext k
  induction k with
  | zero => simpa [threeFTwoCoeff] using hzero
  | succ k ih =>
      have hden : (a₁ + (k : ℝ)) * (a₂ + k) * (k + 1) ≠ 0 := by positivity
      apply mul_right_cancel₀ hden
      rw [hstep, coeff_threeFTwo, threeFTwoCoeff_succ ha₁ ha₂, ih, coeff_threeFTwo]

/-- At a nonpositive argument every summand is nonnegative and the constant
summand is one. No splitting hypothesis is needed. -/
theorem eval_threeFTwo_pos_of_nonpos {a₁ a₂ b₁ b₂ x : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (n : ℕ) (hx : x ≤ 0) : 0 < (threeFTwo a₁ a₂ b₁ b₂ n).eval x := by
  have hterm (k : ℕ) (hk : k ∈ range (n + 1)) :
      0 ≤ threeFTwoCoeff a₁ a₂ b₁ b₂ n k * x ^ k := by
    have hcoeff := (threeFTwoCoeff_alternating_pos ha₁ ha₂ hb₁ hb₂
      (show k ≤ n from Nat.le_of_lt_succ (mem_range.mp hk))).le
    have hpow : 0 ≤ (-x) ^ k := pow_nonneg (neg_nonneg.mpr hx) k
    have heq : threeFTwoCoeff a₁ a₂ b₁ b₂ n k * x ^ k =
        ((-1 : ℝ) ^ k * threeFTwoCoeff a₁ a₂ b₁ b₂ n k) * (-x) ^ k := by
      rw [neg_pow]
      have hs : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; simp
      linear_combination -(threeFTwoCoeff a₁ a₂ b₁ b₂ n k * x ^ k) * hs
    rw [heq]
    exact mul_nonneg hcoeff hpow
  simp only [threeFTwo, eval_finsetSum, eval_monomial]
  apply sum_pos' hterm
  exact ⟨0, mem_range.mpr (by lia), by simp [threeFTwoCoeff]⟩

/-- Every real zero is positive for positive parameters, without using splitting. -/
theorem isRoot_threeFTwo_pos {a₁ a₂ b₁ b₂ x : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (n : ℕ) (hx : (threeFTwo a₁ a₂ b₁ b₂ n).IsRoot x) : 0 < x := by
  by_contra h
  have hpos := eval_threeFTwo_pos_of_nonpos ha₁ ha₂ hb₁ hb₂ n (le_of_not_gt h)
  rw [hx] at hpos
  exact lt_irrefl _ hpos

/-- Lima's monic normalization of the constant-term-one series. -/
def monicThreeFTwo (a₁ a₂ b₁ b₂ : ℝ) (n : ℕ) : ℝ[X] :=
  C (threeFTwoCoeff a₁ a₂ b₁ b₂ n n)⁻¹ * threeFTwo a₁ a₂ b₁ b₂ n

/-- The monic normalization is well defined for positive parameters. -/
theorem monic_monicThreeFTwo {a₁ a₂ b₁ b₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (n : ℕ) :
    (monicThreeFTwo a₁ a₂ b₁ b₂ n).Monic := by
  have hdeg := natDegree_threeFTwo ha₁ ha₂ hb₁ hb₂ n
  have hcoeff := right_ne_zero_of_mul
    (threeFTwoCoeff_alternating_pos ha₁ ha₂ hb₁ hb₂ (le_refl n)).ne'
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [leadingCoeff, hdeg, coeff_threeFTwo, inv_mul_cancel₀ hcoeff]

/-- The scalar in the monic normalization is precisely the prefactor in
Lima (6.6)/(8.9), rather than a change of the polynomial variable. -/
theorem monicThreeFTwo_eq_C_mul {a₁ a₂ b₁ b₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (n : ℕ) :
    monicThreeFTwo a₁ a₂ b₁ b₂ n =
      C ((-1 : ℝ) ^ n * (ascPochhammer ℝ n).eval a₁ *
        (ascPochhammer ℝ n).eval a₂ /
        ((ascPochhammer ℝ n).eval (upperOne b₁ n) *
          (ascPochhammer ℝ n).eval (upperTwo b₂ n))) * threeFTwo a₁ a₂ b₁ b₂ n := by
  obtain ⟨hu₁, hu₂⟩ := upperParameters_pos hb₁ hb₂ n
  have h₁ := (ascPochhammer_pos n a₁ ha₁).ne'
  have h₂ := (ascPochhammer_pos n a₂ ha₂).ne'
  have h₃ := (ascPochhammer_pos n _ hu₁).ne'
  have h₄ := (ascPochhammer_pos n _ hu₂).ne'
  have hs : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  unfold monicThreeFTwo
  congr 2
  apply inv_eq_of_mul_eq_one_right
  simp only [threeFTwoCoeff, Nat.choose_self, Nat.cast_one, mul_one]
  field_simp
  nlinarith [hs]

/-- Every coefficient varies continuously under a simultaneous upper-parameter
shift. The lower parameters, and hence all denominators, stay fixed. -/
theorem continuous_threeFTwoCoeff_shift (a₁ a₂ b₁ b₂ : ℝ) (n k : ℕ) :
    Continuous (fun ε : ℝ => threeFTwoCoeff a₁ a₂ (b₁ + ε) (b₂ + ε) n k) := by
  unfold threeFTwoCoeff upperOne upperTwo
  fun_prop

/-- Complexified evaluations vary continuously under the same shift. -/
theorem continuous_eval_threeFTwo_shift (a₁ a₂ b₁ b₂ : ℝ) (n : ℕ) (z : ℂ) :
    Continuous (fun ε : ℝ =>
      ((threeFTwo a₁ a₂ (b₁ + ε) (b₂ + ε) n).map Complex.ofRealHom).eval z) := by
  simp only [threeFTwo, Polynomial.map_sum, map_monomial, eval_finsetSum, eval_monomial]
  apply continuous_finsetSum
  intro k _
  exact (Complex.continuous_ofReal.comp (continuous_threeFTwoCoeff_shift _ _ _ _ n k)).mul
    continuous_const

/-- Splitting passes to a simultaneous upper-parameter limit. This is a closure
lemma: its splitting premise still has to be supplied by a separate strict-case proof. -/
theorem splits_threeFTwo_of_tendsto_shift (a₁ a₂ b₁ b₂ : ℝ) (n : ℕ)
    (ε : ℕ → ℝ) (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hs : ∀ j, (threeFTwo a₁ a₂ (b₁ + ε j) (b₂ + ε j) n).Splits) :
    (threeFTwo a₁ a₂ b₁ b₂ n).Splits := by
  have hclosed := Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le
    (p₀ := threeFTwo a₁ a₂ b₁ b₂ n)
    (fun j => natDegree_threeFTwo_le a₁ a₂ (b₁ + ε j) (b₂ + ε j) n)
    (fun j => Or.inr (hs j)) (fun z => ?_)
  · exact hclosed.resolve_left (threeFTwo_ne_zero a₁ a₂ b₁ b₂ n)
  · simpa [Function.comp_def] using
      (continuous_eval_threeFTwo_shift a₁ a₂ b₁ b₂ n z).continuousAt.tendsto.comp hε

/-- Splitting for all positive upper-parameter perturbations implies splitting
at the unperturbed parameters. This does not assume simplicity at the limit. -/
theorem splits_threeFTwo_of_pos_shift (a₁ a₂ b₁ b₂ : ℝ) (n : ℕ)
    (hs : ∀ ε : ℝ, 0 < ε → (threeFTwo a₁ a₂ (b₁ + ε) (b₂ + ε) n).Splits) :
    (threeFTwo a₁ a₂ b₁ b₂ n).Splits := by
  apply splits_threeFTwo_of_tendsto_shift a₁ a₂ b₁ b₂ n (fun j => 1 / ((j : ℝ) + 1))
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro j
    exact hs _ (by positivity)

/-- The two-branched weights from Lima (5.13), with `a₃ = 1`. The six residue
classes combine the periods three and two in the shifted parameters of (5.9).
The removable factor `b₂ - 1` is cancelled at index two, so the definition also
covers `b₂ = 1`. Indices zero and one are the zero boundary weights in (6.42). -/
def branchedWeight (a₁ a₂ b₁ b₂ : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => a₁ * a₂ / (b₁ * b₂)
  | j + 3 =>
      let m : ℝ := (j / 6 : ℕ)
      match j % 6 with
      | 0 => (b₁ - a₁ + m) * (2 * m + 1) * (a₂ + 2 * m) /
          ((b₁ + 3 * m + 1) * (b₂ + 3 * m) * (b₁ + 3 * m))
      | 1 => (b₂ - a₂ + m) * (a₁ + 2 * m + 1) * (2 * m + 1) /
          ((b₂ + 3 * m + 1) * (b₁ + 3 * m + 1) * (b₂ + 3 * m))
      | 2 => (b₁ + m) * (a₂ + 2 * m + 1) * (a₁ + 2 * m + 1) /
          ((b₁ + 3 * m + 2) * (b₂ + 3 * m + 1) * (b₁ + 3 * m + 1))
      | 3 => (b₂ - a₁ + m) * (2 * m + 2) * (a₂ + 2 * m + 1) /
          ((b₂ + 3 * m + 2) * (b₁ + 3 * m + 2) * (b₂ + 3 * m + 1))
      | 4 => (b₁ - a₂ + m + 1) * (a₁ + 2 * m + 2) * (2 * m + 2) /
          ((b₁ + 3 * m + 3) * (b₂ + 3 * m + 2) * (b₁ + 3 * m + 2))
      | _ => (b₂ + m) * (a₂ + 2 * m + 2) * (a₁ + 2 * m + 2) /
          ((b₂ + 3 * m + 3) * (b₁ + 3 * m + 3) * (b₂ + 3 * m + 2))

/-- The explicit two-branched weights are nonnegative in Lima's weak range. -/
theorem branchedWeight_nonneg {a₁ a₂ b₁ b₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ - 1 ≤ b₁) (h₃ : a₁ ≤ b₂) (h₄ : a₂ ≤ b₂)
    (j : ℕ) : 0 ≤ branchedWeight a₁ a₂ b₁ b₂ j := by
  have hd₁ : 0 ≤ b₁ - a₁ := sub_nonneg.mpr h₁
  have hd₂ : 0 ≤ b₂ - a₂ := sub_nonneg.mpr h₄
  have hd₃ : 0 ≤ b₂ - a₁ := sub_nonneg.mpr h₃
  have hd₄ : 0 ≤ b₁ - a₂ + 1 := by linarith
  match j with
  | 0 => simp [branchedWeight]
  | 1 => simp [branchedWeight]
  | 2 => dsimp [branchedWeight]; positivity
  | j + 3 =>
      have hd₅ : 0 ≤ b₁ - a₂ + (j / 6 : ℕ) + 1 := by
        linarith [Nat.cast_nonneg (α := ℝ) (j / 6)]
      dsimp only [branchedWeight]
      split <;> positivity

/-- Every non-boundary two-branched weight is positive in Lima's strict range. -/
theorem branchedWeight_pos {a₁ a₂ b₁ b₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (h₁ : a₁ < b₁) (h₂ : a₂ - 1 < b₁) (h₃ : a₁ < b₂) (h₄ : a₂ < b₂)
    {j : ℕ} (hj : 2 ≤ j) : 0 < branchedWeight a₁ a₂ b₁ b₂ j := by
  have hd₁ : 0 < b₁ - a₁ := sub_pos.mpr h₁
  have hd₂ : 0 < b₂ - a₂ := sub_pos.mpr h₄
  have hd₃ : 0 < b₂ - a₁ := sub_pos.mpr h₃
  have hd₄ : 0 < b₁ - a₂ + 1 := by linarith
  match j with
  | 0 => lia
  | 1 => lia
  | 2 => dsimp [branchedWeight]; positivity
  | j + 3 =>
      have hd₅ : 0 < b₁ - a₂ + (j / 6 : ℕ) + 1 := by
        linarith [Nat.cast_nonneg (α := ℝ) (j / 6)]
      dsimp only [branchedWeight]
      split <;> positivity

/-- The finite production section for the explicit weights in Lima (3.7). -/
def production (a₁ a₂ b₁ b₂ : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.twoBranchedProduction (branchedWeight a₁ a₂ b₁ b₂) n

/-- The empty section agrees with the monic degree-zero series. -/
@[simp] theorem monicThreeFTwo_zero (a₁ a₂ b₁ b₂ : ℝ) :
    monicThreeFTwo a₁ a₂ b₁ b₂ 0 = (production a₁ a₂ b₁ b₂ 0).charpoly := by
  simp [monicThreeFTwo, threeFTwoCoeff, production, Matrix.twoBranchedProduction]

/-- The first section agrees with the monic linear series, with the same variable. -/
theorem monicThreeFTwo_one {a₁ a₂ b₁ b₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    monicThreeFTwo a₁ a₂ b₁ b₂ 1 = (production a₁ a₂ b₁ b₂ 1).charpoly := by
  rw [monicThreeFTwo_eq_C_mul ha₁ ha₂ hb₁ hb₂, production, Matrix.twoBranchedProduction,
    Matrix.threeBidiagonalProduction_charpoly_one]
  have h₁ := ha₁.ne'
  have h₂ := ha₂.ne'
  have h₃ := hb₁.ne'
  have h₄ := hb₂.ne'
  ext k
  match k with
  | 0 => simp [threeFTwoCoeff, upperOne, upperTwo, branchedWeight, neg_div]
  | 1 =>
      simp [threeFTwoCoeff, upperOne, upperTwo]
      field_simp
  | k + 2 =>
      simp [threeFTwoCoeff, Nat.choose_eq_zero_of_lt (show 1 < k + 2 by lia),
        coeff_X]

private theorem production_charpoly_two (a₁ a₂ : ℝ) {b₁ b₂ : ℝ}
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    (production a₁ a₂ b₁ b₂ 2).charpoly =
      X ^ 2 - C (2 * (a₁ + 1) * (a₂ + 1) / ((b₁ + 2) * (b₂ + 1))) * X +
        C (a₁ * a₂ * (a₁ + 1) * (a₂ + 1) /
          ((b₁ + 1) * (b₁ + 2) * b₂ * (b₂ + 1))) := by
  have hb₁₀ := hb₁.ne'
  have hb₂₀ := hb₂.ne'
  have hb₁₁ : b₁ + 1 ≠ 0 := by positivity
  have hb₁₂ : b₁ + 2 ≠ 0 := by positivity
  have hb₂₁ : b₂ + 1 ≠ 0 := by positivity
  have hsum : branchedWeight a₁ a₂ b₁ b₂ 2 + branchedWeight a₁ a₂ b₁ b₂ 3 +
      branchedWeight a₁ a₂ b₁ b₂ 4 + branchedWeight a₁ a₂ b₁ b₂ 5 =
      2 * (a₁ + 1) * (a₂ + 1) / ((b₁ + 2) * (b₂ + 1)) := by
    norm_num [branchedWeight]
    field_simp
    ring
  have hprod : branchedWeight a₁ a₂ b₁ b₂ 2 * branchedWeight a₁ a₂ b₁ b₂ 5 =
      a₁ * a₂ * (a₁ + 1) * (a₂ + 1) /
        ((b₁ + 1) * (b₁ + 2) * b₂ * (b₂ + 1)) := by
    norm_num [branchedWeight]
    field_simp
  rw [production, Matrix.twoBranchedProduction,
    Matrix.threeBidiagonalProduction_charpoly_two]
  simp only [Matrix.threeBidiagonalDiag, Matrix.threeBidiagonalSub, one_mul, mul_one]
  rw [← hsum, ← hprod]
  simp only [C_add, C_mul, C_1]
  ring

/-- The second section agrees with the monic quadratic series. Together with
the degree-zero and degree-one identities, this supplies the three startup
identities required by the library's four-term recurrence identification. -/
theorem monicThreeFTwo_two {a₁ a₂ b₁ b₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    monicThreeFTwo a₁ a₂ b₁ b₂ 2 = (production a₁ a₂ b₁ b₂ 2).charpoly := by
  rw [monicThreeFTwo_eq_C_mul ha₁ ha₂ hb₁ hb₂, production_charpoly_two _ _ hb₁ hb₂]
  have h₁ := ha₁.ne'
  have h₂ := ha₂.ne'
  have h₃ : a₁ + 1 ≠ 0 := by positivity
  have h₄ : a₂ + 1 ≠ 0 := by positivity
  have h₅ := hb₁.ne'
  have h₆ := hb₂.ne'
  have h₇ : b₁ + 1 ≠ 0 := by positivity
  have h₈ : b₁ + 2 ≠ 0 := by positivity
  have h₉ : b₂ + 1 ≠ 0 := by positivity
  ext k
  match k with
  | 0 =>
      simp [threeFTwoCoeff, upperOne, upperTwo, ascPochhammer_succ_eval]
      field_simp
      ring
  | 1 =>
      simp [threeFTwoCoeff, upperOne, upperTwo, ascPochhammer_succ_eval]
      field_simp
      ring
  | 2 =>
      simp [threeFTwoCoeff, upperOne, upperTwo, ascPochhammer_succ_eval]
      field_simp
  | k + 3 =>
      simp [threeFTwoCoeff, Nat.choose_eq_zero_of_lt (show 2 < k + 3 by lia)]

/-- Lima's weak parameter inequalities make every finite production section
totally nonnegative, including when some factor weights vanish. -/
theorem isTotallyNonneg_production {a₁ a₂ b₁ b₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ - 1 ≤ b₁) (h₃ : a₁ ≤ b₂) (h₄ : a₂ ≤ b₂)
    (n : ℕ) : (production a₁ a₂ b₁ b₂ n).IsTotallyNonneg := by
  apply Matrix.isTotallyNonneg_threeBidiagonalProduction
  intro i
  have h := branchedWeight_nonneg ha₁ ha₂ hb₁ hb₂ h₁ h₂ h₃ h₄
  exact ⟨by norm_num, h _, by norm_num, h _, h _, by norm_num⟩

/-- In the strict parameter range, consecutive production characteristic
polynomials interlace, have simple disjoint roots, and have positive spectrum.
The equality with `monicThreeFTwo` is proved in `monicThreeFTwo_eq_charpoly`. -/
theorem production_charpoly_strictInterlaces {a₁ a₂ b₁ b₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (h₁ : a₁ < b₁) (h₂ : a₂ - 1 < b₁) (h₃ : a₁ < b₂) (h₄ : a₂ < b₂)
    (n : ℕ) :
    let H := production a₁ a₂ b₁ b₂
    RealRooted.Interlaces (H n).charpoly (H (n + 1)).charpoly ∧
      (∀ x : ℝ, (H (n + 1)).charpoly.IsRoot x →
        (H (n + 1)).charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, (H n).charpoly.IsRoot x → (H n).charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, ¬((H (n + 1)).charpoly.IsRoot x ∧ (H n).charpoly.IsRoot x)) ∧
      ∀ x ∈ (H (n + 1)).charpoly.roots, 0 < x := by
  have hpos := fun (i : ℕ) (hi : 2 ≤ i) =>
    branchedWeight_pos ha₁ ha₂ hb₁ hb₂ h₁ h₂ h₃ h₄ hi
  apply Matrix.threeBidiagonalProduction_charpoly_strictInterlaces
  · intro i
    have h := branchedWeight_nonneg ha₁ ha₂ hb₁ hb₂ h₁.le h₂.le h₃.le h₄.le
    exact ⟨by norm_num, h _, by norm_num, h _, h _, by norm_num⟩
  · intro i
    simpa using hpos (3 * i + 2) (by lia)
  · intro i
    norm_num
  · intro i
    cases i with
    | zero =>
        simp only [Matrix.threeBidiagonalSub, one_mul, mul_one]
        exact mul_pos (add_pos (hpos 3 (by lia)) (hpos 4 (by lia)))
          (hpos 2 (by lia))
    | succ i =>
        simp only [Matrix.threeBidiagonalSub, one_mul, mul_one]
        exact add_pos
          (mul_pos (add_pos (hpos _ (by lia)) (hpos _ (by lia)))
            (hpos _ (by lia)))
          (mul_pos (hpos _ (by lia)) (hpos _ (by lia)))

private abbrev poch (x : ℝ) (k : ℕ) : ℝ := (ascPochhammer ℝ k).eval x

private def term (a c u v : ℝ) (n k : ℕ) : ℝ :=
  ((-1) ^ n * poch a n * poch c n / (poch u n * poch v n)) *
    ((-1) ^ k * (n.choose k : ℝ) * poch u k * poch v k / (poch a k * poch c k))

private def rowRatio (a c u v r k : ℝ) : ℝ :=
  -(r + 1 - k) * (u + r) * (v + r) * (v + r + 1) /
    ((r + 1) * (a + r) * (c + r) * (v + k))

private def mulRatio (a c u v r k : ℝ) : ℝ :=
  k * (a + k - 1) * (c + k - 1) * (u + r) * (v + r) * (v + r + 1) /
    ((r + 1) * (a + r) * (c + r) * (u + k - 1) * (v + k - 1) * (v + k))

private theorem poch_shift {v : ℝ} (hv : v ≠ 0) (k : ℕ) :
    poch (v + 1) k = poch v k * (v + k) / v := by
  apply (eq_div_iff hv).2
  have h := congrArg (fun p : ℝ[X] => p.eval v)
    (ascPochhammer_succ_left (S := ℝ) k)
  simpa [ascPochhammer_succ_eval, mul_comm] using h.symm

private theorem term_symm (a c u v : ℝ) (n k : ℕ) :
    term a c u v n k = term a c v u n k := by
  simp only [term]
  ring

private theorem coeff_monicThreeFTwo {a c b d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hd : 0 < d) (n k : ℕ) :
    (monicThreeFTwo a c b d n).coeff k = term a c (upperOne b n) (upperTwo d n) n k := by
  rw [monicThreeFTwo_eq_C_mul ha hc hb hd, coeff_C_mul, coeff_threeFTwo]
  rfl

private theorem term_step {a c u v : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hu : 0 < u) (hv : 0 < v) (n k : ℕ) :
    term a c u v n k = rowRatio a c u v n k * term a c u (v + 1) (n + 1) k := by
  by_cases hk : k ≤ n + 1
  · have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hchoose : (n.choose k : ℝ) =
        (((n : ℝ) + 1 - k) / (n + 1)) * ((n + 1).choose k : ℝ) := by
      have h := congrArg (fun j : ℕ => (j : ℝ)) (Nat.choose_mul_succ_eq n k)
      push_cast [Nat.cast_sub hk] at h
      apply (mul_right_cancel₀ hn)
      field_simp
      nlinarith [h]
    have hp₁ := (ascPochhammer_pos n a ha).ne'
    have hp₂ := (ascPochhammer_pos n c hc).ne'
    have hp₃ := (ascPochhammer_pos n u hu).ne'
    have hp₄ := (ascPochhammer_pos n v hv).ne'
    have hp₅ := (ascPochhammer_pos k a ha).ne'
    have hp₆ := (ascPochhammer_pos k c hc).ne'
    have hv₀ := hv.ne'
    have hvn : v + (n : ℝ) ≠ 0 := by positivity
    have hunk : u + (n : ℝ) ≠ 0 := by positivity
    have hvnn : v + (n : ℝ) + 1 ≠ 0 := by positivity
    have han : a + (n : ℝ) ≠ 0 := by positivity
    have hcn : c + (n : ℝ) ≠ 0 := by positivity
    have hvk : v + (k : ℝ) ≠ 0 := by positivity
    simp only [term, rowRatio, ascPochhammer_succ_eval, pow_succ, Nat.cast_add,
      Nat.cast_one, poch_shift hv₀, hchoose]
    field_simp
    ring
  · have hk₁ : n < k := by lia
    have hk₂ : n + 1 < k := by lia
    simp [term, Nat.choose_eq_zero_of_lt hk₁, Nat.choose_eq_zero_of_lt hk₂]

private theorem term_mul {a c u v : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hu : 0 < u) (hv : 0 < v) (n k : ℕ) :
    term a c u v n k = mulRatio a c u v n (k + 1) *
      term a c u (v + 1) (n + 1) (k + 1) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hchoose : (n.choose k : ℝ) =
      (((k : ℝ) + 1) / (n + 1)) * ((n + 1).choose (k + 1) : ℝ) := by
    have h := congrArg (fun j : ℕ => (j : ℝ)) (Nat.add_one_mul_choose_eq n k)
    push_cast at h
    apply mul_right_cancel₀ hn
    field_simp
    nlinarith [h]
  have hp₁ := (ascPochhammer_pos n a ha).ne'
  have hp₂ := (ascPochhammer_pos n c hc).ne'
  have hp₃ := (ascPochhammer_pos n u hu).ne'
  have hp₄ := (ascPochhammer_pos n v hv).ne'
  have hp₅ := (ascPochhammer_pos k a ha).ne'
  have hp₆ := (ascPochhammer_pos k c hc).ne'
  have hv₀ := hv.ne'
  have hvn : v + (n : ℝ) ≠ 0 := by positivity
  have hun : u + (n : ℝ) ≠ 0 := by positivity
  have hvnn : v + (n : ℝ) + 1 ≠ 0 := by positivity
  have han : a + (n : ℝ) ≠ 0 := by positivity
  have hcn : c + (n : ℝ) ≠ 0 := by positivity
  have hvk : v + (k : ℝ) ≠ 0 := by positivity
  have huk : u + (k : ℝ) ≠ 0 := by positivity
  have hak : a + (k : ℝ) ≠ 0 := by positivity
  have hck : c + (k : ℝ) ≠ 0 := by positivity
  have hvkk : v + (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [term, mulRatio, ascPochhammer_succ_eval, pow_succ, Nat.cast_add,
    Nat.cast_one, poch_shift hv₀, hchoose]
  simp only [add_sub_assoc]
  field_simp
  ring

private def part (a c u v r : ℝ) : ℕ → ℝ
  | 0 => r * (v - a) * (c + r - 1) / ((v + r) * (u + r - 1) * (v + r - 1))
  | 1 => r * (u - c) * (a + r) / ((u + r) * (v + r) * (u + r - 1))
  | 2 => v * (a + r) * (c + r) / ((v + r + 1) * (u + r) * (v + r))
  | 3 => (u - 1) * (a + r - 1) * (c + r - 1) /
      ((u + r - 1) * (v + r - 1) * (u + r - 2))
  | 4 => (v - c) * (a + r - 1) * (r - 1) /
      ((v + r - 1) * (u + r - 2) * (v + r - 2))
  | _ => (v - 1) * (a + r - 2) * (c + r - 2) /
      ((v + r - 2) * (u + r - 3) * (v + r - 3))

private theorem ratio_identity {a c u v r k : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hu : 1 < u) (hv : 1 < v) (hr : 3 ≤ r) (hk : 0 ≤ k) :
    let W := part a c u v r
    let R₀ := rowRatio a c u v r k
    let R₁ := rowRatio a c v (u - 1) (r - 1) k
    let R₂ := rowRatio a c (u - 1) (v - 1) (r - 2) k
    mulRatio a c u v r k = 1 + R₀ * (W 0 + W 1 + W 2 +
      R₁ * (W 3 * (W 0 + W 1) + W 4 * W 0) + R₁ * R₂ * W 5 * W 4 * W 0) := by
  let W := part a c u v r
  let R₀ := rowRatio a c u v r k
  let R₁ := rowRatio a c v (u - 1) (r - 1) k
  let R₂ := rowRatio a c (u - 1) (v - 1) (r - 2) k
  have hr₀ : r ≠ 0 := by linarith
  have hr₁ : r - 1 ≠ 0 := by linarith
  have hr₂ : r + 1 ≠ 0 := by linarith
  have ha₀ : a + r ≠ 0 := by linarith
  have ha₁ : a + r - 1 ≠ 0 := by linarith
  have ha₂ : a + r - 2 ≠ 0 := by linarith
  have hc₀ : c + r ≠ 0 := by linarith
  have hc₁ : c + r - 1 ≠ 0 := by linarith
  have hc₂ : c + r - 2 ≠ 0 := by linarith
  have hu₀ : u + r ≠ 0 := by linarith
  have hu₁ : u + r - 1 ≠ 0 := by linarith
  have hu₂ : u + r - 2 ≠ 0 := by linarith
  have hu₃ : u + r - 3 ≠ 0 := by linarith
  have hv₀ : v + r ≠ 0 := by linarith
  have hv₁ : v + r - 1 ≠ 0 := by linarith
  have hv₂ : v + r - 2 ≠ 0 := by linarith
  have hv₃ : v + r - 3 ≠ 0 := by linarith
  have hv₄ : v + r + 1 ≠ 0 := by linarith
  have huk : u + k - 1 ≠ 0 := by linarith
  have hvk : v + k - 1 ≠ 0 := by linarith
  have hvk₀ : v + k ≠ 0 := by linarith
  have hR₁ : R₁ = -(r - k) * (v + r - 1) * (u + r - 2) * (u + r - 1) /
      (r * (a + r - 1) * (c + r - 1) * (u + k - 1)) := by
    dsimp [R₁, rowRatio]
    congr 1 <;> ring
  have hR₂ : R₂ = -(r - 1 - k) * (u + r - 3) * (v + r - 3) * (v + r - 2) /
      ((r - 1) * (a + r - 2) * (c + r - 2) * (v + k - 1)) := by
    dsimp [R₂, rowRatio]
    congr 1 <;> ring
  have hC : 1 + R₀ * W 2 = k * (v + r + 1) / ((r + 1) * (v + k)) := by
    dsimp [R₀, W, rowRatio, part]
    field_simp [ha₀, hc₀, hu₀, hv₀, hv₄, hr₂, hvk₀]
    field_simp
    ring
  have hD : 1 + R₁ * W 3 = k * (u + r - 1) / (r * (u + k - 1)) := by
    rw [hR₁]
    dsimp [W, part]
    field_simp
    field_simp
    ring
  have hF : 1 + R₂ * W 5 = k * (v + r - 2) / ((r - 1) * (v + k - 1)) := by
    rw [hR₂]
    dsimp [W, part]
    field_simp
    field_simp
    ring
  have hA : 1 + R₁ * W 3 + R₁ * W 4 * (1 + R₂ * W 5) =
      k * (u + r - 1) * (v + r - 1) * (c + k - 1) /
        (r * (u + k - 1) * (c + r - 1) * (v + k - 1)) := by
    rw [hD, hF, hR₁]
    dsimp [W, part]
    field_simp
    field_simp
    ring
  have hB : 1 + R₀ * W 2 + R₀ * W 1 * (1 + R₁ * W 3) =
      k * (v + r + 1) * (u + r) * (c + k - 1) /
        ((r + 1) * (v + k) * (c + r) * (u + k - 1)) := by
    rw [hC, hD]
    dsimp [R₀, W, rowRatio, part]
    field_simp
    field_simp
    ring
  change mulRatio a c u v r k = _
  calc
    _ = (1 + R₀ * W 2 + R₀ * W 1 * (1 + R₁ * W 3)) +
        R₀ * W 0 * (1 + R₁ * W 3 + R₁ * W 4 * (1 + R₂ * W 5)) := by
      rw [hB, hA]
      dsimp [R₀, W, rowRatio, part, mulRatio]
      field_simp
      field_simp
      ring
    _ = _ := by ring

private theorem term_recurrence {a c u v : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hu : 1 < u) (hv : 1 < v) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    let W := part a c u v (n + 2)
    term a c u (v + 1) (n + 3) k =
      (if k = 0 then 0 else term a c u v (n + 2) (k - 1)) -
        (W 0 + W 1 + W 2) * term a c u v (n + 2) k -
        (W 3 * (W 0 + W 1) + W 4 * W 0) * term a c v (u - 1) (n + 1) k -
        (W 5 * W 4 * W 0) * term a c (u - 1) (v - 1) n k := by
  have hu₀ : 0 < u := by linarith
  have hv₀ : 0 < v := by linarith
  have hu₁ : 0 < u - 1 := sub_pos.mpr hu
  have hv₁ : 0 < v - 1 := sub_pos.mpr hv
  have h₀ := term_step ha hc hu₀ hv₀ (n + 2) k
  have h₁ := term_step ha hc hv₀ hu₁ (n + 1) k
  simp only [sub_add_cancel, Nat.add_assoc] at h₀ h₁
  rw [term_symm a c v u (n + 2) k] at h₁
  have h₂ := term_step ha hc hu₁ hv₁ n k
  simp only [sub_add_cancel] at h₂
  rw [term_symm a c (u - 1) v (n + 1) k] at h₂
  have hs : (if k = 0 then 0 else term a c u v (n + 2) (k - 1)) =
      mulRatio a c u v (n + 2) k * term a c u (v + 1) (n + 3) k := by
    cases k with
    | zero => simp [mulRatio]
    | succ k => simpa using term_mul ha hc hu₀ hv₀ (n + 2) k
  have hi := ratio_identity ha hc hu hv
    (r := (n + 2 : ℕ)) (k := k) (by exact_mod_cast (show 3 ≤ n + 2 by lia))
    (Nat.cast_nonneg k)
  have hn₁ : ((n + 2 : ℕ) : ℝ) - 1 = (n + 1 : ℕ) := by push_cast; ring
  have hn₂ : ((n + 2 : ℕ) : ℝ) - 2 = (n : ℝ) := by push_cast; ring
  dsimp only at hi ⊢
  rw [hn₁, hn₂] at hi
  push_cast at hi h₀ h₁ h₂
  rw [hs, h₂, h₁, h₀]
  linear_combination -(term a c u (v + 1) (n + 3) k) * hi

private def productionPart (α : ℕ → ℝ) (r : ℕ) : ℕ → ℝ
  | 0 => α (3 * r)
  | 1 => α (3 * r + 1)
  | 2 => α (3 * r + 2)
  | 3 => α (3 * r - 1)
  | 4 => α (3 * r - 2)
  | _ => α (3 * r - 4)

private theorem part_even (a c b d : ℝ) (m : ℕ) (j : Fin 6) :
    part a c (b + (m + 2)) (d + (m + 1)) (2 * m + 4) j =
      productionPart (branchedWeight a c b d) (2 * m + 4) j := by
  fin_cases j <;>
    norm_num [part, productionPart, Nat.mul_add, ← Nat.mul_assoc, branchedWeight,
      Nat.add_div, Nat.add_mod] <;> ring

private theorem part_odd (a c b d : ℝ) (m : ℕ) (j : Fin 6) :
    part a c (d + (m + 1)) (b + (m + 1)) (2 * m + 3) j =
      productionPart (branchedWeight a c b d) (2 * m + 3) j := by
  fin_cases j <;>
    norm_num [part, productionPart, Nat.mul_add, ← Nat.mul_assoc, branchedWeight,
      Nat.add_div, Nat.add_mod] <;> ring

private theorem coeff_X_mul_ite (p : ℝ[X]) (k : ℕ) :
    (X * p).coeff k = if k = 0 then 0 else p.coeff (k - 1) := by
  cases k <;> simp

private theorem monic_recurrence_pos {a c b d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hd : 0 < d)
    {n : ℕ} (hn : 1 ≤ n) :
    let P := monicThreeFTwo a c b d
    let W := productionPart (branchedWeight a c b d) (n + 2)
    P (n + 3) = (X - C (W 0 + W 1 + W 2)) * P (n + 2) -
      C (W 3 * (W 0 + W 1) + W 4 * W 0) * P (n + 1) -
      C (W 5 * W 4 * W 0) * P n := by
  dsimp only
  ext k
  simp only [sub_mul, coeff_sub, coeff_C_mul, coeff_X_mul_ite,
    coeff_monicThreeFTwo ha hc hb hd]
  obtain ⟨m, he | ho⟩ := Nat.even_or_odd' (n - 1)
  · have hn' : n = 2 * m + 1 := by lia
    subst n
    have h := term_recurrence ha hc (u := d + (m + 1)) (v := b + (m + 1))
      (by linarith [Nat.cast_nonneg (α := ℝ) m])
      (by linarith [Nat.cast_nonneg (α := ℝ) m]) (n := 2 * m + 1) (by lia) k
    dsimp only at h
    push_cast at h
    simp only [add_assoc] at h
    norm_num only at h
    rw [part_odd a c b d m ⟨0, by decide⟩, part_odd a c b d m ⟨1, by decide⟩,
      part_odd a c b d m ⟨2, by decide⟩, part_odd a c b d m ⟨3, by decide⟩,
      part_odd a c b d m ⟨4, by decide⟩, part_odd a c b d m ⟨5, by decide⟩] at h
    have hshift (x : ℝ) : x + (m + 1) - 1 = x + m := by ring
    rw [hshift d, hshift b] at h
    rw [term_symm a c (d + (m + 1)) (b + (m + 2)) (2 * m + 4) k,
      term_symm a c (d + (m + 1)) (b + (m + 1)) (2 * m + 3) k,
      term_symm a c (d + (m + 1)) (b + (m + 1)) (2 * m + 3) (k - 1),
      term_symm a c (d + m) (b + m) (2 * m + 1) k] at h
    simp only [Nat.add_assoc] at ⊢
    norm_num [upperOne, upperTwo, Nat.add_div] at ⊢
    simpa only [add_assoc, mul_assoc] using h
  · have hn' : n = 2 * m + 2 := by lia
    subst n
    have h := term_recurrence ha hc (u := b + (m + 2)) (v := d + (m + 1))
      (by linarith [Nat.cast_nonneg (α := ℝ) m])
      (by linarith [Nat.cast_nonneg (α := ℝ) m]) (n := 2 * m + 2) (by lia) k
    dsimp only at h
    push_cast at h
    simp only [add_assoc] at h
    norm_num only at h
    rw [part_even a c b d m ⟨0, by decide⟩, part_even a c b d m ⟨1, by decide⟩,
      part_even a c b d m ⟨2, by decide⟩, part_even a c b d m ⟨3, by decide⟩,
      part_even a c b d m ⟨4, by decide⟩, part_even a c b d m ⟨5, by decide⟩] at h
    have hshift₁ : b + (m + 2) - 1 = b + (m + 1) := by ring
    have hshift₂ : d + (m + 1) - 1 = d + m := by ring
    rw [hshift₁, hshift₂,
      term_symm a c (d + (m + 1)) (b + (m + 1)) (2 * m + 3) k] at h
    simp only [Nat.add_assoc] at ⊢
    norm_num [upperOne, upperTwo, Nat.add_div] at ⊢
    simpa only [add_assoc, mul_assoc] using h

private theorem monic_recurrence_zero {a c b d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hd : 0 < d) :
    let P := monicThreeFTwo a c b d
    let W := productionPart (branchedWeight a c b d) 2
    P 3 = (X - C (W 0 + W 1 + W 2)) * P 2 -
      C (W 3 * (W 0 + W 1) + W 4 * W 0) * P 1 - C (W 5 * W 4 * W 0) * P 0 := by
  have hp (x : ℝ) (hx : 0 < x) : x ≠ 0 ∧ x + 1 ≠ 0 ∧ x + 2 ≠ 0 ∧ x + 3 ≠ 0 := by
    exact ⟨by positivity, by positivity, by positivity, by positivity⟩
  obtain ⟨ha₀, ha₁, ha₂, ha₃⟩ := hp a ha
  obtain ⟨hc₀, hc₁, hc₂, hc₃⟩ := hp c hc
  obtain ⟨hb₀, hb₁, hb₂, hb₃⟩ := hp b hb
  obtain ⟨hd₀, hd₁, hd₂, hd₃⟩ := hp d hd
  clear hp
  dsimp only
  ext k
  simp only [sub_mul, coeff_sub, coeff_C_mul, coeff_X_mul_ite,
    coeff_monicThreeFTwo ha hc hb hd]
  by_cases hk : k ≤ 3
  · interval_cases k <;>
      norm_num [term, poch, Nat.choose, productionPart, branchedWeight, upperOne, upperTwo,
        ascPochhammer_succ_eval] <;> field_simp <;> field_simp <;> norm_num <;> ring
  · have hk₀ : k ≠ 0 := by lia
    simp [term, hk₀, Nat.choose_eq_zero_of_lt (show 3 < k by lia),
      Nat.choose_eq_zero_of_lt (show 2 < k by lia),
      Nat.choose_eq_zero_of_lt (show 1 < k by lia),
      Nat.choose_eq_zero_of_lt (show 0 < k by lia),
      Nat.choose_eq_zero_of_lt (show 2 < k - 1 by lia)]

/-- Lima's monic terminating three-over-two polynomial is the characteristic
polynomial of the explicit three-bidiagonal section, in every degree.
This is (6.6), (3.7), and (6.42) of arXiv:2208.03539v2. -/
theorem monicThreeFTwo_eq_charpoly {a c b d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hd : 0 < d) (n : ℕ) :
    monicThreeFTwo a c b d n = (production a c b d n).charpoly := by
  let α := branchedWeight a c b d
  change monicThreeFTwo a c b d n =
    (Matrix.threeBidiagonalProduction (fun _ => 1) (fun i => α (3 * i + 3))
      (fun _ => 1) (fun i => α (3 * i + 4)) (fun i => α (3 * i + 2)) (fun _ => 1) n).charpoly
  apply RealRooted.eq_charpoly_threeBidiagonalProduction_of_recurrence
  · intro i
    norm_num
  · simp [monicThreeFTwo, threeFTwoCoeff]
  · exact (monicThreeFTwo_one ha hc hb hd).trans
      (Matrix.threeBidiagonalProduction_charpoly_one _ _ _ _ _ _)
  · simpa using (monicThreeFTwo_two ha hc hb hd).trans
      (Matrix.threeBidiagonalProduction_charpoly_two _ _ _ _ _ _)
  · intro j
    have h :
        let P := monicThreeFTwo a c b d
        let W := productionPart (branchedWeight a c b d) (j + 2)
        P (j + 3) = (X - C (W 0 + W 1 + W 2)) * P (j + 2) -
          C (W 3 * (W 0 + W 1) + W 4 * W 0) * P (j + 1) -
          C (W 5 * W 4 * W 0) * P j := by
      by_cases hj : j = 0
      · subst j
        exact monic_recurrence_zero ha hc hb hd
      · exact monic_recurrence_pos ha hc hb hd (n := j) (by lia)
    dsimp only at h
    convert h using 1
    norm_num [α, productionPart, Matrix.threeBidiagonalDiag, Matrix.threeBidiagonalSub,
      Nat.mul_add, C_add, C_mul]
    ring

/-- In Lima's strict range, consecutive terminating series split and interlace,
with simple disjoint positive roots (Theorem 8.4 of arXiv:2208.03539v2). -/
theorem threeFTwo_strictInterlaces {a c b d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hd : 0 < d)
    (h₁ : a < b) (h₂ : c - 1 < b) (h₃ : a < d) (h₄ : c < d) (n : ℕ) :
    let H := threeFTwo a c b d
    RealRooted.Interlaces (H n) (H (n + 1)) ∧
      (∀ x : ℝ, (H (n + 1)).IsRoot x → (H (n + 1)).rootMultiplicity x = 1) ∧
      (∀ x : ℝ, (H n).IsRoot x → (H n).rootMultiplicity x = 1) ∧
      (∀ x : ℝ, ¬((H (n + 1)).IsRoot x ∧ (H n).IsRoot x)) ∧
      ∀ x ∈ (H (n + 1)).roots, 0 < x := by
  have hnz (j : ℕ) : threeFTwoCoeff a c b d j j ≠ 0 :=
    right_ne_zero_of_mul (threeFTwoCoeff_alternating_pos ha hc hb hd (le_refl j)).ne'
  have hs (j : ℕ) : C (threeFTwoCoeff a c b d j j) * monicThreeFTwo a c b d j =
      threeFTwo a c b d j := by
    rw [monicThreeFTwo, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (hnz j), C_1, one_mul]
  have hr (j : ℕ) (x : ℝ) : (threeFTwo a c b d j).IsRoot x ↔
      (monicThreeFTwo a c b d j).IsRoot x := by
    rw [← hs j]
    simp only [Polynomial.IsRoot.def, eval_C_mul, mul_eq_zero, hnz j, false_or]
  have h := production_charpoly_strictInterlaces ha hc hb hd h₁ h₂ h₃ h₄ n
  dsimp only at h ⊢
  simp_rw [← monicThreeFTwo_eq_charpoly ha hc hb hd] at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hs] using h.1.C_mul_both (hnz n) (hnz (n + 1))
  · intro x hx
    rw [← hs (n + 1), Polynomial.rootMultiplicity_C_mul (hnz (n + 1))]
    exact h.2.1 x ((hr (n + 1) x).1 hx)
  · intro x hx
    rw [← hs n, Polynomial.rootMultiplicity_C_mul (hnz n)]
    exact h.2.2.1 x ((hr n x).1 hx)
  · intro x hx
    exact h.2.2.2.1 x ⟨(hr (n + 1) x).1 hx.1, (hr n x).1 hx.2⟩
  · intro x hx
    exact isRoot_threeFTwo_pos ha hc hb hd (n + 1)
      ((Polynomial.mem_roots (threeFTwo_ne_zero a c b d (n + 1))).1 hx)

/-- Splitting persists at Lima's weak parameter boundary by positive shifts of
both upper base parameters. No assertion of simple boundary roots is needed. -/
theorem threeFTwo_splits {a c b d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hd : 0 < d)
    (h₁ : a ≤ b) (h₂ : c - 1 ≤ b) (h₃ : a ≤ d) (h₄ : c ≤ d) (n : ℕ) :
    (threeFTwo a c b d n).Splits := by
  apply splits_threeFTwo_of_pos_shift
  intro ε hε
  exact (threeFTwo_strictInterlaces ha hc (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) n).1.2.1.2

end RealRooted.Hypergeometric
