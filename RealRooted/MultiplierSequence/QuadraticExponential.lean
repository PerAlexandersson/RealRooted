module

public import RealRooted.MultiplierSequence.PolyaSchur.Limit
public import RealRooted.PFPolynomial.Closure
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

@[expose] public noncomputable section

open Filter Polynomial Topology

namespace RealRooted

private def fallingTwo (k : ℕ) : ℝ := (k * (k - 1) : ℕ)

private lemma diagonalOperator_one_sub_fallingTwo (s : ℝ) (p : ℝ[X]) :
    diagonalOperator (fun k => 1 - s * fallingTwo k) p =
      p - C s * (X ^ 2 * p.derivative.derivative) := by
  ext k
  rcases k with (_ | _ | k)
  · simp [fallingTwo]
  · simp [fallingTwo, coeff_X_pow_mul']
  · simp [fallingTwo, coeff_X_pow_mul', coeff_derivative]
    ring_nf

private lemma isPFPolynomial_C_mul_X_add_one {c : ℝ} (hc : 0 ≤ c) :
    IsPFPolynomial (C c * X + 1) := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa using IsPFPolynomial.one
  have hfactor : (C c * X + 1 : ℝ[X]) = C c * (X + C c⁻¹) := by
    rw [mul_add, ← C_mul]
    simp [hc.ne']
  rw [hfactor]
  exact (isPFPolynomial_X_add_C (inv_nonneg.mpr hc.le)).const_mul hc

private def truncatedOneStep (d : ℕ) (s : ℝ) (k : ℕ) : ℝ :=
  if k ≤ d then 1 - s * fallingTwo k else 0

private lemma jensenPolynomial_truncatedOneStep (d : ℕ) (s : ℝ) :
    jensenPolynomial d (truncatedOneStep d s) =
      (X + 1) ^ d - C s *
        (X ^ 2 * ((X + 1 : ℝ[X]) ^ d).derivative.derivative) := by
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow,
    ← diagonalOperator_one_sub_fallingTwo]
  ext k
  by_cases hk : k ≤ d
  · simp [truncatedOneStep, hk]
  · have hcoeff : ((X + 1 : ℝ[X]) ^ d).coeff k = 0 := by
      rw [coeff_X_add_one_pow, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hk)]
      exact Nat.cast_zero
    simp only [coeff_diagonalOperator, truncatedOneStep, ite_eq_right hk, hcoeff, mul_zero]

private lemma jensenPolynomial_truncatedOneStep_eq_factor
    {d : ℕ} (hd : 2 ≤ d) (s : ℝ) :
    jensenPolynomial d (truncatedOneStep d s) =
      (X + 1) ^ (d - 2) *
        ((X + 1) ^ 2 - C (s * (d * (d - 1) : ℕ)) * X ^ 2) := by
  rw [jensenPolynomial_truncatedOneStep,
    show (1 : ℝ[X]) = C 1 by rfl, derivative_X_add_C_pow, derivative_mul]
  simp only [derivative_C, zero_mul, zero_add]
  rw [derivative_X_add_C_pow]
  simp only [C_1]
  rw [Nat.sub_sub]
  have hpow : (X + 1 : ℝ[X]) ^ d =
      (X + 1) ^ (d - 2) * (X + 1) ^ 2 := by
    rw [← pow_add]
    congr
    lia
  rw [hpow]
  have hC : C s * C (d : ℝ) * C ((d - 1 : ℕ) : ℝ) =
      C (s * ((d * (d - 1) : ℕ) : ℝ)) := by
    rw [← C_mul, ← C_mul, Nat.cast_mul]
    ring_nf
  calc
    (X + 1) ^ (d - 2) * (X + 1) ^ 2 -
          C s * (X ^ 2 * (C (d : ℝ) *
            (C ((d - 1 : ℕ) : ℝ) * (X + 1) ^ (d - 2)))) =
        (X + 1) ^ (d - 2) * (X + 1) ^ 2 -
          (C s * C (d : ℝ) * C ((d - 1 : ℕ) : ℝ)) *
            X ^ 2 * (X + 1) ^ (d - 2) := by ring_nf
    _ = (X + 1) ^ (d - 2) *
        ((X + 1) ^ 2 - C (s * (d * (d - 1) : ℕ)) * X ^ 2) := by
      rw [hC]
      ring_nf

private lemma isPFPolynomial_jensenPolynomial_truncatedOneStep
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s * (d * (d - 1) : ℕ))
    (hs_one : s * (d * (d - 1) : ℕ) ≤ 1) :
    IsPFPolynomial (jensenPolynomial d (truncatedOneStep d s)) := by
  rcases d with (_ | _ | d)
  · rw [jensenPolynomial_zero]
    simpa [truncatedOneStep, fallingTwo] using IsPFPolynomial.one
  · rw [jensenPolynomial_truncatedOneStep]
    simpa using isPFPolynomial_X_add_one
  · let a : ℝ := s * ((d + 2) * (d + 2 - 1) : ℕ)
    have ha : 0 ≤ a := hs
    have ha_one : a ≤ 1 := hs_one
    have hsqrt : 0 ≤ 1 - Real.sqrt a := by
      rw [sub_nonneg]
      exact Real.sqrt_le_one.mpr ha_one
    have hfactor :
        ((X + 1 : ℝ[X]) ^ 2 - C a * X ^ 2) =
          (C (1 - Real.sqrt a) * X + 1) *
            (C (1 + Real.sqrt a) * X + 1) := by
      have hsqrt_sq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
      have hCa : C a = C (Real.sqrt a) ^ 2 := by
        rw [← map_pow, hsqrt_sq]
      have hCsub : C (1 - Real.sqrt a) = 1 - C (Real.sqrt a) := by
        rw [map_sub, map_one]
      have hCadd : C (1 + Real.sqrt a) = 1 + C (Real.sqrt a) := by
        rw [map_add, map_one]
      rw [hCa, hCsub, hCadd]
      ring_nf
    rw [jensenPolynomial_truncatedOneStep_eq_factor (by lia), hfactor]
    exact (isPFPolynomial_X_add_one.pow d).mul
      ((isPFPolynomial_C_mul_X_add_one hsqrt).mul
        (isPFPolynomial_C_mul_X_add_one (by positivity)))

private lemma fallingTwo_mono {k d : ℕ} (hkd : k ≤ d) :
    fallingTwo k ≤ fallingTwo d := by
  rw [fallingTwo, fallingTwo]
  exact_mod_cast Nat.mul_le_mul hkd (Nat.sub_le_sub_right hkd 1)

private lemma truncatedOneStep_nonneg {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (hs_one : s * fallingTwo d ≤ 1) (k : ℕ) :
    0 ≤ truncatedOneStep d s k := by
  rw [truncatedOneStep]
  split_ifs with hkd
  · have hfall := fallingTwo_mono hkd
    have := mul_le_mul_of_nonneg_left hfall hs
    linarith
  · exact le_rfl

private lemma IsFinitePFMultiplierSequence.pow
    {d : ℕ} {gamma : ℕ → ℝ} (hgamma : IsFinitePFMultiplierSequence d gamma)
    (N : ℕ) : IsFinitePFMultiplierSequence d (fun k => gamma k ^ N) := by
  induction N with
  | zero =>
      intro p hp _
      simpa using hp
  | succ N ih =>
      intro p hp hdeg
      simpa only [pow_succ] using (ih.mul hgamma) hp hdeg

/-- The Gaussian multiplier on falling factorials of order two. -/
def quadraticExponentialMultiplier (t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-t * (k * (k - 1) : ℕ))

/-- The quadratic exponential sequence is a Pólya-frequency multiplier
sequence for every nonnegative time. -/
theorem isPFMultiplierSequence_quadraticExponentialMultiplier
    {t : ℝ} (ht : 0 ≤ t) :
    IsPFMultiplierSequence (quadraticExponentialMultiplier t) := by
  rw [isPFMultiplierSequence_iff_jensenPolynomial_isPF]
  intro d
  obtain ⟨M, hM⟩ := exists_nat_ge (t * fallingTwo d)
  let N : ℕ → ℕ := fun n => n + M + 1
  let gamma : ℕ → ℕ → ℝ := fun n k =>
    truncatedOneStep d (t / N n) k ^ N n
  have hN_pos (n : ℕ) : 0 < N n := by simp [N]
  have hstep_nonneg (n k : ℕ) : 0 ≤ truncatedOneStep d (t / N n) k := by
    apply truncatedOneStep_nonneg (div_nonneg ht (Nat.cast_nonneg _))
    have hMN : (M : ℝ) ≤ N n := by
      dsimp [N]
      push_cast
      linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have hden : (0 : ℝ) < N n := by exact_mod_cast hN_pos n
    apply (div_mul_eq_mul_div _ _ _).trans_le
    exact (div_le_one hden).2 (hM.trans hMN)
  have hgamma_pf (n : ℕ) :
      IsPFPolynomial (jensenPolynomial d (gamma n)) := by
    have hden : (0 : ℝ) < N n := by exact_mod_cast hN_pos n
    have hMN : (M : ℝ) ≤ N n := by
      dsimp [N]
      push_cast
      linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have hJ := isPFPolynomial_jensenPolynomial_truncatedOneStep
      (d := d) (s := t / N n)
      (mul_nonneg (div_nonneg ht hden.le) (by positivity))
      ((div_mul_eq_mul_div _ _ _).trans_le ((div_le_one hden).2 (hM.trans hMN)))
    have hfinite : IsFinitePFMultiplierSequence d
        (truncatedOneStep d (t / N n)) :=
      (isFinitePFMultiplierSequence_iff_jensenPolynomial
        (hstep_nonneg n)).2 hJ
    exact isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence
      (hfinite.pow (N n))
  apply IsPFPolynomial.of_coeff_tendsto hgamma_pf
  intro k
  simp only [coeff_jensenPolynomial]
  by_cases hkd : k ≤ d
  · simp only [ite_eq_left hkd]
    apply tendsto_const_nhds.mul
    have hlim := Real.tendsto_one_add_div_pow_exp (-t * fallingTwo k)
    have hshift := (tendsto_add_atTop_iff_nat (M + 1)).2 hlim
    simpa [gamma, N, truncatedOneStep, hkd, quadraticExponentialMultiplier,
      fallingTwo, sub_eq_add_neg, add_assoc, div_mul_eq_mul_div, neg_div] using hshift
  · simp only [ite_eq_right hkd]
    exact tendsto_const_nhds

theorem quadraticExponentialMultiplier_nonneg {t : ℝ} (k : ℕ) :
    0 ≤ quadraticExponentialMultiplier t k := Real.exp_nonneg _

private lemma diagonalOperator_ne_zero_of_forall_ne_zero
    {gamma : ℕ → ℝ} (hgamma : ∀ k, gamma k ≠ 0)
    {p : ℝ[X]} (hp : p ≠ 0) : diagonalOperator gamma p ≠ 0 := by
  intro hzero
  apply hp
  ext k
  have hcoeff := congrArg (fun q : ℝ[X] => q.coeff k) hzero
  simp only [coeff_diagonalOperator, coeff_zero] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left (hgamma k)

/-- The quadratic exponential diagonal action preserves real-rootedness. -/
theorem splits_diagonalOperator_quadraticExponentialMultiplier
    {t : ℝ} (ht : 0 ≤ t) {p : ℝ[X]} (hp0 : p ≠ 0) (hp : p.Splits) :
    (diagonalOperator (quadraticExponentialMultiplier t) p).Splits := by
  have hmult :=
    (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp
      (isPFMultiplierSequence_quadraticExponentialMultiplier ht)).1
  rcases hmult.diagonalOperator_eq_zero_or_splits hp with hzero | hsplits
  · exact (diagonalOperator_ne_zero_of_forall_ne_zero
      (fun k => Real.exp_ne_zero _) hp0 hzero).elim
  · exact hsplits

end RealRooted
