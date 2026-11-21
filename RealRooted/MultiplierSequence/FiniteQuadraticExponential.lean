module

public import RealRooted.MultiplierSequence
import RealRooted.MultiplierSequence.FiniteQuadratic
import RealRooted.PFPolynomial.Closure
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Exponentiating finite symmetric quadratic PF multipliers

We exponentiate `k (d - k)` by finite products and coefficientwise closure.
We also classify exponential quadratic weights through degree `d ≥ 2`:
`exp (A k² + B k + C)` preserves PF exactly when `A ≤ 0`.
We also prove that a local Jensen test implies preservation at every nonnegative time.
The quadratic-generator classification is completed in `DiagonalSemigroup`.

Source: the unpublished manuscript proofs in RealRooted issue #2320,
<https://github.com/PerAlexandersson/RealRooted/issues/2320>.
-/

public section

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- The finite symmetric quadratic heat multiplier preserves PF at nonnegative times. -/
theorem isFinitePFMultiplierSequence_exp_symmetric_quadratic
    (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    IsFinitePFMultiplierSequence d (fun k => Real.exp (t * (k : ℝ) * ((d : ℝ) - k))) := by
  intro p hp hdeg
  have hstep (n : ℕ) : IsFinitePFMultiplierSequence d
      (fun k => 1 + (t / (n + 1 : ℕ)) * (k : ℝ) * ((d : ℝ) - k)) := by
    intro q hq hqdeg
    exact hq.diagonalOperator_symmetric_quadratic hqdeg zero_le_one
      (div_nonneg ht (Nat.cast_nonneg _))
  apply IsPFPolynomial.of_coeff_tendsto
    (fun n => IsFinitePFMultiplierSequence.pow (hstep n) (n + 1) hp hdeg)
  intro k
  simp only [coeff_diagonalOperator]
  apply Filter.Tendsto.mul_const
  have hlim := Real.tendsto_one_add_div_pow_exp (t * (k : ℝ) * ((d : ℝ) - k))
  have hshift := (tendsto_add_atTop_iff_nat 1).2 hlim
  simpa only [div_mul_eq_mul_div] using hshift

/-- Exponential diagonal operators satisfy the semigroup law for every real generator. -/
theorem diagonalOperator_exp_add (g : ℕ → ℝ) (s t : ℝ) (p : ℝ[X]) :
    diagonalOperator (fun k => Real.exp ((s + t) * g k)) p =
      diagonalOperator (fun k => Real.exp (s * g k))
        (diagonalOperator (fun k => Real.exp (t * g k)) p) := by
  ext k
  simp [add_mul, Real.exp_add, mul_assoc]

/-- A nonpositive quadratic exponent gives a finite PF multiplier in every degree. -/
theorem isFinitePFMultiplierSequence_exp_quadratic
    (d : ℕ) {A : ℝ} (hA : A ≤ 0) (B C₀ : ℝ) :
    IsFinitePFMultiplierSequence d
      (fun k => Real.exp (A * (k : ℝ) ^ 2 + B * k + C₀)) := by
  intro p hp hdeg
  have hheat := isFinitePFMultiplierSequence_exp_symmetric_quadratic d (neg_nonneg.mpr hA)
    hp hdeg
  have hPF := (hheat.comp_C_mul_X_add_C (Real.exp_pos (B + A * d)) (d := 0) le_rfl).const_mul
    (Real.exp_pos C₀)
  have hweight (k : ℕ) : Real.exp (A * (k : ℝ) ^ 2 + B * k + C₀) =
      Real.exp C₀ * Real.exp (B + A * d) ^ k *
        Real.exp (-A * (k : ℝ) * ((d : ℝ) - k)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  convert hPF using 1
  ext k
  simp only [coeff_diagonalOperator, coeff_C_mul, comp_C_mul_X_coeff, C_0, add_zero]
  rw [hweight]
  ring

/-- Through degree at least two, exponential quadratic PF preservation holds
exactly when the quadratic coefficient of the exponent is nonpositive. -/
theorem isFinitePFMultiplierSequence_exp_quadratic_iff
    {d : ℕ} (hd : 2 ≤ d) (A B C₀ : ℝ) :
    IsFinitePFMultiplierSequence d
      (fun k => Real.exp (A * (k : ℝ) ^ 2 + B * k + C₀)) ↔ A ≤ 0 := by
  refine ⟨fun h => ?_, fun hA => isFinitePFMultiplierSequence_exp_quadratic d hA B C₀⟩
  have hj := isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence (h.mono hd)
  have hlog := hj.coeffLogConcaveUpTo_of_isPF_jensenPolynomial 1 (by norm_num) (by norm_num)
  norm_num at hlog
  have hexp : Real.exp (C₀ + (A * 4 + B * 2 + C₀)) ≤
      Real.exp ((A + B + C₀) + (A + B + C₀)) := by
    simpa only [Real.exp_add, pow_two] using hlog
  have := Real.exp_le_exp.mp hexp
  linarith

/-- In degrees zero and one every exponential quadratic weight preserves PF. -/
theorem isFinitePFMultiplierSequence_exp_quadratic_of_le_one
    {d : ℕ} (hd : d ≤ 1) (A B C₀ : ℝ) :
    IsFinitePFMultiplierSequence d
      (fun k => Real.exp (A * (k : ℝ) ^ 2 + B * k + C₀)) :=
  isFinitePFMultiplierSequence_of_natDegree_le_one hd (fun _ => Real.exp_nonneg _)

/-- Every quadratic generator with nonpositive quadratic coefficient gives a
PF-preserving diagonal semigroup on each finite degree range. -/
theorem isFinitePFMultiplierSequence_exp_mul_quadratic
    (d : ℕ) {A : ℝ} (hA : A ≤ 0) (B C₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IsFinitePFMultiplierSequence d
      (fun k => Real.exp (t * (A * (k : ℝ) ^ 2 + B * k + C₀))) := by
  have h : IsFinitePFMultiplierSequence d
      (fun k => Real.exp ((t * A) * (k : ℝ) ^ 2 + (t * B) * k + t * C₀)) :=
    isFinitePFMultiplierSequence_exp_quadratic d
      (mul_nonpos_of_nonneg_of_nonpos ht hA) (t * B) (t * C₀)
  have heq : (fun k : ℕ => Real.exp (t * (A * (k : ℝ) ^ 2 + B * k + C₀))) =
      (fun k : ℕ => Real.exp ((t * A) * (k : ℝ) ^ 2 + (t * B) * k + t * C₀)) := by
    funext k
    congr 1
    ring
  rw [heq]
  exact @h

/-- If the exponential Jensen polynomials split along positive times tending to
zero, the entire diagonal semigroup preserves PF on the same degree range.
We approximate any time by integer multiples of these times. -/
theorem isFinitePFMultiplierSequence_exp_of_local_jensen
    {d : ℕ} (g : ℕ → ℝ) {τ : ℕ → ℝ} (hpos : ∀ n, 0 < τ n)
    (hτ : Tendsto τ atTop (𝓝 0))
    (hs : ∀ n, (jensenPolynomial d (fun k => Real.exp (τ n * g k))).Splits)
    {t : ℝ} (ht : 0 ≤ t) :
    IsFinitePFMultiplierSequence d (fun k => Real.exp (t * g k)) := by
  let N (n : ℕ) := ⌊t / τ n⌋₊
  have hfloor (n : ℕ) : (N n : ℝ) * τ n ≤ t :=
    (le_div_iff₀ (hpos n)).mp (Nat.floor_le (div_nonneg ht (hpos n).le))
  have hceil (n : ℕ) : t < ((N n : ℝ) + 1) * τ n :=
    (div_lt_iff₀ (hpos n)).mp (Nat.lt_floor_add_one (t / τ n))
  have herror : Tendsto (fun n => t - (N n : ℝ) * τ n) atTop (𝓝 0) :=
    squeeze_zero (fun n => sub_nonneg.mpr (hfloor n))
      (fun n => by linarith [hceil n]) hτ
  have htime : Tendsto (fun n => (N n : ℝ) * τ n) atTop (𝓝 t) := by
    simpa only [sub_sub_cancel, sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t)).sub herror
  have hstep (n : ℕ) : IsFinitePFMultiplierSequence d
      (fun k => Real.exp (τ n * g k)) := by
    apply isFinitePFMultiplierSequence_iff_jensen_isPF.mpr
    exact IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_jensenPolynomial (fun _ => Real.exp_nonneg _)) (hs n)
  intro p hp hdeg
  apply IsPFPolynomial.of_coeff_tendsto
    (fun n => IsFinitePFMultiplierSequence.pow (hstep n) (N n) hp hdeg)
  intro k
  simp only [coeff_diagonalOperator, ← Real.exp_nat_mul]
  apply Filter.Tendsto.mul_const
  simpa only [Function.comp_def, mul_assoc] using (Real.continuous_exp.tendsto (t * g k)).comp
    (htime.mul_const (g k))

/-- A diagonal exponential semigroup preserves PF at every nonnegative time if
and only if its single Jensen family splits along positive times tending to zero.
This local test is valid for arbitrary real generators and every degree bound. -/
theorem forall_isFinitePFMultiplierSequence_exp_iff_local_jensen
    (d : ℕ) (g : ℕ → ℝ) :
    (∀ t : ℝ, 0 ≤ t → IsFinitePFMultiplierSequence d (fun k => Real.exp (t * g k))) ↔
      ∃ τ : ℕ → ℝ, (∀ n, 0 < τ n) ∧ Tendsto τ atTop (𝓝 0) ∧
        ∀ n, (jensenPolynomial d (fun k => Real.exp (τ n * g k))).Splits := by
  constructor
  · intro h
    refine ⟨fun n => 1 / (n + 1 : ℕ), fun n => by positivity,
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))), ?_⟩
    intro n
    exact (isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence
      (h _ (by positivity))).splits
  · rintro ⟨τ, hpos, hτ, hs⟩ t ht
    exact isFinitePFMultiplierSequence_exp_of_local_jensen g hpos hτ hs ht

end RealRooted
