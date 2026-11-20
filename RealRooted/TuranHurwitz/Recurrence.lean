module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Differential recurrence and extended Turán expressions

We use the six parameters of Shi, arXiv:2610.35783v2, Theorem 1.1(i).
The parameters `σ` and `ρ` are zero throughout. Named families below are
defined by their differential recurrences, without combinatorial identifications.
The general stability theorem is proved in `TuranHurwitz.Main`; see RealRooted issue #2600.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- Parameters of the differential recurrence with `σ = ρ = 0`. -/
structure Parameters where
  a₁ : ℝ
  a₂ : ℝ
  b₁ : ℝ
  b₂ : ℝ
  lam : ℝ
  tau : ℝ

/-- The parameter conditions of Theorem 1.1(i). -/
structure Parameters.Admissible (c : Parameters) : Prop where
  a₁_nonneg : 0 ≤ c.a₁
  a₂_nonneg : 0 ≤ c.a₂
  b₁_nonneg : 0 ≤ c.b₁
  b₂_nonneg : 0 ≤ c.b₂
  lam_nonneg : 0 ≤ c.lam
  tau_nonneg : 0 ≤ c.tau
  cross_nonneg : c.a₂ * c.b₁ ≤ c.a₁ * (c.b₁ + c.b₂)
  numerator_pos : 0 < c.b₁ + c.b₂ + c.tau * c.a₂
  slope_pos : 0 < c.a₁ + c.b₁

/-- The shifted variable `x + λ`. -/
@[expose] noncomputable def shiftedVariable (c : Parameters) : ℝ[X] := X + C c.lam

/-- The polynomial sequence in Theorem 1.1(i), in factored form. -/
@[expose] noncomputable def family (c : Parameters) : ℕ → ℝ[X]
  | 0 => 1
  | j + 1 =>
      (C c.a₂ + C (c.b₁ + c.b₂) * shiftedVariable c +
        C (c.tau * j) * shiftedVariable c * (C c.a₁ + C c.b₁ * shiftedVariable c)) *
          family c j +
      shiftedVariable c * (1 - C c.tau * shiftedVariable c) *
        (C c.a₁ + C c.b₁ * shiftedVariable c) * (family c j).derivative

/-- The factorially normalized extended Turán expression, equation (1.1). -/
@[expose] noncomputable def turan (m n : ℕ) (P : ℕ → ℝ[X]) : ℝ[X] :=
  ∑ j ∈ Finset.range (2 * n + 1),
    C ((-1 : ℝ) ^ (n + j) / ((j.factorial : ℝ) * ((2 * n - j).factorial : ℝ))) *
      (P (m + j) * P (m + 2 * n - j))

/-- The recurrence starts with the constant polynomial one. -/
@[simp] theorem family_zero (c : Parameters) : family c 0 = 1 := rfl

/-- The recurrence in expanded form, matching the paper's displayed recurrence. -/
theorem family_succ (c : Parameters) (j : ℕ) :
    family c (j + 1) =
      (C c.a₂ + C (c.b₁ + c.b₂ + c.tau * c.a₁ * j) * shiftedVariable c +
        C (c.tau * c.b₁ * j) * shiftedVariable c ^ 2) * family c j +
      (C c.a₁ * shiftedVariable c + C (c.b₁ - c.tau * c.a₁) * shiftedVariable c ^ 2 -
        C (c.tau * c.b₁) * shiftedVariable c ^ 3) * (family c j).derivative := by
  rw [family]
  simp only [map_add, map_sub, map_mul]
  ring

/-- The recurrence uniquely determines the sequence. -/
theorem family_unique (c : Parameters) (P : ℕ → ℝ[X]) (h0 : P 0 = 1)
    (hrec : ∀ j, P (j + 1) =
      (C c.a₂ + C (c.b₁ + c.b₂) * shiftedVariable c +
        C (c.tau * j) * shiftedVariable c * (C c.a₁ + C c.b₁ * shiftedVariable c)) *
          P j + shiftedVariable c * (1 - C c.tau * shiftedVariable c) *
            (C c.a₁ + C c.b₁ * shiftedVariable c) * (P j).derivative) :
    P = family c := by
  funext j
  induction j with
  | zero => exact h0
  | succ j ih => rw [hrec, ih, family]

/-- The first row is affine, independently of `τ`. -/
@[simp] theorem family_one (c : Parameters) :
    family c 1 = C c.a₂ + C (c.b₁ + c.b₂) * shiftedVariable c := by
  simp [family]

/-- For `n = 0` the same finite sum is the square of the initial row. -/
@[simp] theorem turan_zero (m : ℕ) (P : ℕ → ℝ[X]) : turan m 0 P = P m ^ 2 := by
  simp [turan, pow_two]

/-- The first ordinary Turán expression factors into two affine factors. -/
theorem turan_zero_one (c : Parameters) :
    turan 0 1 (family c) =
      -C (c.b₁ + c.b₂ + c.tau * c.a₂) * shiftedVariable c *
        (C c.a₁ + C c.b₁ * shiftedVariable c) := by
  have hh : C (1 / 2 : ℝ) + C (1 / 2 : ℝ) = (1 : ℝ[X]) := by
    rw [← map_add]
    norm_num
  have hT : turan 0 1 (family c) = family c 1 ^ 2 - family c 2 := by
    norm_num [turan, Finset.sum_range_succ]
    linear_combination -family c 2 * hh
  rw [hT]
  simp [family, shiftedVariable, map_add, map_mul, derivative_mul]
  ring

/-- The first Turán expression has no root to the right of the shifted boundary. -/
theorem aeval_turan_zero_one_ne_zero {c : Parameters} (hc : c.Admissible) (z : ℂ)
    (hz : -c.lam < z.re) : aeval z (turan 0 1 (family c)) ≠ 0 := by
  have hq : 0 < (z + (c.lam : ℂ)).re := by
    simpa using (show 0 < z.re + c.lam by linarith)
  have hq0 : z + (c.lam : ℂ) ≠ 0 := by
    intro heq
    rw [heq] at hq
    exact (lt_irrefl 0) hq
  have hs : (c.b₁ + c.b₂ + c.tau * c.a₂ : ℂ) ≠ 0 := by
    exact_mod_cast hc.numerator_pos.ne'
  have hlin : 0 < ((c.a₁ : ℂ) + (c.b₁ : ℂ) * (z + (c.lam : ℂ))).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    by_cases hb : c.b₁ = 0
    · have := hc.slope_pos
      simp only [hb, zero_mul, add_zero] at this ⊢
      exact this
    · have hbpos := lt_of_le_of_ne hc.b₁_nonneg (Ne.symm hb)
      nlinarith [hc.a₁_nonneg, mul_pos hbpos hq]
  have hlin0 : (c.a₁ : ℂ) + (c.b₁ : ℂ) * (z + (c.lam : ℂ)) ≠ 0 := by
    intro heq
    rw [heq] at hlin
    exact (lt_irrefl 0) hlin
  simpa [turan_zero_one, shiftedVariable] using
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hs) hq0) hlin0

/-- In particular, the first Turán polynomial is nonzero. -/
theorem turan_zero_one_ne_zero {c : Parameters} (hc : c.Admissible) :
    turan 0 1 (family c) ≠ 0 := by
  have hf := aeval_turan_zero_one_ne_zero hc (1 - (c.lam : ℂ)) (by simp)
  intro heq
  simp [heq] at hf

/-- The product inequality forces `a₂ = 0` on the boundary `a₁ = 0`. -/
theorem Parameters.Admissible.a₂_eq_zero {c : Parameters} (hc : c.Admissible)
    (ha : c.a₁ = 0) : c.a₂ = 0 := by
  have hb : 0 < c.b₁ := by linarith [hc.slope_pos]
  have h := hc.cross_nonneg
  rw [ha, zero_mul] at h
  nlinarith [hc.a₂_nonneg]

/-- The exponent in the normalization of the generic parameter case. -/
@[expose] noncomputable def normalizedExponent (c : Parameters) : ℝ :=
  (c.b₁ + c.b₂ + c.tau * c.a₂) / (c.b₁ + c.tau * c.a₁)

/-- The offset in the normalization of the generic parameter case. -/
@[expose] noncomputable def normalizedOffset (c : Parameters) : ℝ :=
  2 * c.a₂ / c.a₁ - normalizedExponent c

/-- The normalized exponent is positive whenever its denominator is positive. -/
theorem normalizedExponent_pos {c : Parameters} (hc : c.Admissible)
    (hb : 0 < c.b₁ + c.tau * c.a₁) : 0 < normalizedExponent c :=
  div_pos hc.numerator_pos hb

/-- The product inequality gives exactly the required normalized offset interval. -/
theorem normalizedOffset_mem_Icc {c : Parameters} (hc : c.Admissible)
    (ha : 0 < c.a₁) (hb : 0 < c.b₁ + c.tau * c.a₁) :
    normalizedOffset c ∈ Set.Icc (-normalizedExponent c) (normalizedExponent c) := by
  have hratio : c.a₂ / c.a₁ ≤ normalizedExponent c := by
    apply (div_le_div_iff₀ ha hb).mpr
    nlinarith [hc.cross_nonneg]
  have hnn : 0 ≤ c.a₂ / c.a₁ := div_nonneg hc.a₂_nonneg ha.le
  dsimp [normalizedOffset]
  rw [mul_div_assoc]
  constructor <;> linarith

/-- At the pole of the fractional change of variable, the derivative term vanishes. -/
theorem eval_family_succ_pole (c : Parameters) (htau : c.tau ≠ 0) (j : ℕ) :
    (family c (j + 1)).eval (1 / c.tau - c.lam) =
      (c.a₂ + (c.b₁ + c.b₂) / c.tau + (j : ℝ) * (c.a₁ + c.b₁ / c.tau)) *
        (family c j).eval (1 / c.tau - c.lam) := by
  rw [family]
  simp only [eval_add, eval_mul, eval_sub, eval_one, eval_C, shiftedVariable, eval_X]
  have hshift : 1 / c.tau - c.lam + c.lam = 1 / c.tau := by ring
  rw [hshift]
  field_simp
  ring

/-- The Bell recurrence `P₀ = 1`, `Pⱼ₊₁ = X (Pⱼ + Pⱼ')`. -/
@[expose] noncomputable def bell : ℕ → ℝ[X] := family ⟨1, 0, 0, 1, 0, 0⟩

/-- Stirling–Whitney–Riordan recurrence (the `τ = 0` specialization). -/
@[expose] noncomputable def stirlingWhitneyRiordan (a₁ a₂ b₁ b₂ lam : ℝ) : ℕ → ℝ[X] :=
  family ⟨a₁, a₂, b₁, b₂, lam, 0⟩

/-- Eulerian recurrence, with the indexing convention of Table 1. -/
@[expose] noncomputable def eulerian : ℕ → ℝ[X] := family ⟨1, 1, 0, 0, 0, 1⟩

/-- Type B Eulerian recurrence. -/
@[expose] noncomputable def typeBEulerian : ℕ → ℝ[X] := family ⟨2, 1, 0, 1, 0, 1⟩

/-- Colored Eulerian recurrence; the theorem's parameter range is `1 ≤ ell`. -/
@[expose] noncomputable def coloredEulerian (ell : ℕ) : ℕ → ℝ[X] :=
  family ⟨ell, 1, 0, (ell : ℝ) - 1, 0, 1⟩

/-- Cycle-weighted Eulerian recurrence; the parameter range is `0 < theta`. -/
@[expose] noncomputable def cycleWeightedEulerian (theta : ℝ) : ℕ → ℝ[X] :=
  family ⟨1, theta, 0, 0, 0, 1⟩

/-- Type A `1/k` Eulerian recurrence; the parameter range is `0 < k`. -/
@[expose] noncomputable def reciprocalEulerian (k : ℝ) : ℕ → ℝ[X] :=
  family ⟨k, 1, 0, 0, 0, 1⟩

/-- Type B `1/k` Eulerian recurrence; the parameter range is `0 < k`. -/
@[expose] noncomputable def reciprocalTypeBEulerian (k : ℝ) : ℕ → ℝ[X] :=
  family ⟨2 * k, 1, 0, 1, 0, 1⟩

/-- The `r` Bell recurrence. -/
@[expose] noncomputable def rBell (r : ℕ) : ℕ → ℝ[X] := family ⟨1, r, 0, 1, 0, 0⟩

/-- The geometric polynomial recurrence. -/
@[expose] noncomputable def geometric : ℕ → ℝ[X] := family ⟨1, 0, 1, 0, 0, 0⟩

/-- The Dowling recurrence; the parameter range is `0 < r`. -/
@[expose] noncomputable def dowling (r : ℝ) : ℕ → ℝ[X] := family ⟨r, 1, 0, 1, 0, 0⟩

/-- The Tanny–geometric recurrence; the parameter range is `1 ≤ r`. -/
@[expose] noncomputable def tannyGeometric (r : ℝ) : ℕ → ℝ[X] :=
  family ⟨r, 1, 1, 0, 0, 0⟩

/-- The Riordan recurrence, with shift `λ = 1`. -/
@[expose] noncomputable def riordan : ℕ → ℝ[X] := family ⟨1, 0, 0, 1, 1, 0⟩

/-- The Bell parameters satisfy the hypotheses of part (i). -/
theorem bell_admissible : (Parameters.mk 1 0 0 1 0 0).Admissible := by
  constructor <;> norm_num

/-- The ordinary Eulerian parameters satisfy the hypotheses. -/
theorem eulerian_admissible : (Parameters.mk 1 1 0 0 0 1).Admissible := by
  constructor <;> norm_num

/-- The type B Eulerian parameters satisfy the hypotheses. -/
theorem typeBEulerian_admissible : (Parameters.mk 2 1 0 1 0 1).Admissible := by
  constructor <;> norm_num

/-- Colored Eulerian parameters satisfy the hypotheses when the number of colors is positive. -/
theorem coloredEulerian_admissible {ell : ℕ} (hell : 1 ≤ ell) :
    (Parameters.mk ell 1 0 ((ell : ℝ) - 1) 0 1).Admissible := by
  have he : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  constructor <;> dsimp <;> nlinarith

/-- Cycle-weighted Eulerian parameters satisfy the hypotheses for positive weight. -/
theorem cycleWeightedEulerian_admissible {theta : ℝ} (htheta : 0 < theta) :
    (Parameters.mk 1 theta 0 0 0 1).Admissible := by
  constructor <;> dsimp <;> linarith

/-- Type A reciprocal Eulerian parameters satisfy the hypotheses for `k > 0`. -/
theorem reciprocalEulerian_admissible {k : ℝ} (hk : 0 < k) :
    (Parameters.mk k 1 0 0 0 1).Admissible := by
  constructor <;> dsimp <;> linarith

/-- Type B reciprocal Eulerian parameters satisfy the hypotheses for `k > 0`. -/
theorem reciprocalTypeBEulerian_admissible {k : ℝ} (hk : 0 < k) :
    (Parameters.mk (2 * k) 1 0 1 0 1).Admissible := by
  constructor <;> dsimp <;> linarith

/-- The `r` Bell parameters satisfy the hypotheses for every natural `r`. -/
theorem rBell_admissible (r : ℕ) : (Parameters.mk 1 r 0 1 0 0).Admissible := by
  constructor <;> dsimp <;> norm_num

/-- The geometric parameters satisfy the hypotheses. -/
theorem geometric_admissible : (Parameters.mk 1 0 1 0 0 0).Admissible := by
  constructor <;> norm_num

/-- Dowling parameters satisfy the hypotheses for `r > 0`. -/
theorem dowling_admissible {r : ℝ} (hr : 0 < r) :
    (Parameters.mk r 1 0 1 0 0).Admissible := by
  constructor <;> dsimp <;> linarith

/-- Tanny–geometric parameters satisfy the hypotheses for `r ≥ 1`. -/
theorem tannyGeometric_admissible {r : ℝ} (hr : 1 ≤ r) :
    (Parameters.mk r 1 1 0 0 0).Admissible := by
  constructor <;> dsimp <;> linarith

/-- The shifted Riordan parameters satisfy the hypotheses. -/
theorem riordan_admissible : (Parameters.mk 1 0 0 1 1 0).Admissible := by
  constructor <;> norm_num

/-- A geometric scaling of sequence values gives a common power in every Turán summand. -/
theorem aeval_turan_scaling (P Q : ℕ → ℝ[X]) (z u s : ℂ)
    (hP : ∀ j, Polynomial.aeval z (P j) = s ^ j * Polynomial.aeval u (Q j)) (m n : ℕ) :
    Polynomial.aeval z (turan m n P) =
      s ^ (2 * m + 2 * n) * Polynomial.aeval u (turan m n Q) := by
  rw [turan, map_sum, turan, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ 2 * n := by simpa using Finset.mem_range.mp hj
  have hpow : s ^ (m + j) * s ^ (m + 2 * n - j) = s ^ (2 * m + 2 * n) := by
    rw [← pow_add]
    congr 1
    lia
  simp only [map_mul, Polynomial.aeval_C]
  rw [hP, hP]
  linear_combination
    ((algebraMap ℝ ℂ)
      ((-1 : ℝ) ^ (n + j) / ((j.factorial : ℝ) * ((2 * n - j).factorial : ℝ))) *
      Polynomial.aeval u (Q (m + j)) * Polynomial.aeval u (Q (m + 2 * n - j))) * hpow

end RealRooted.TuranHurwitz
