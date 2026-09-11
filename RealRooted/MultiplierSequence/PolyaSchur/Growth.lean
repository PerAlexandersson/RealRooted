import RealRooted.MultiplierSequence.PolyaSchur
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya

/-!
# Exponential growth of Pólya--Schur multiplier sequences

This analytic-side child derives an all-radius exponential-generating majorant
from the PF multiplier convention when the zeroth coefficient is positive.
Initial-zero and signed conventions remain separate boundaries.
-/

open Polynomial

noncomputable section

namespace RealRooted

private theorem exponential_bound_of_nonneg_logConcave_zero_tail
    {a : ℕ → ℝ} (h0 : 0 < a 0) (hnonneg : ∀ n, 0 ≤ a n)
    (hlog : ∀ n, a n * a (n + 2) ≤ a (n + 1) ^ 2)
    (htail : ∀ ⦃n m⦄, a n = 0 → n ≤ m → a m = 0) (n : ℕ) :
    a n ≤ a 0 * (a 1 / a 0) ^ n := by
  let r : ℝ := a 1 / a 0
  have hr : 0 ≤ r := div_nonneg (hnonneg 1) h0.le
  have hstep : ∀ n, a (n + 1) ≤ r * a n := by
    intro n
    induction n with
    | zero =>
        dsimp [r]
        field_simp
        exact le_rfl
    | succ n ih =>
        by_cases hz : a (n + 1) = 0
        · have htail' : a (n + 2) = 0 := htail hz (by lia)
          simp [hz, htail']
        · have hprevne : a n ≠ 0 := by
            intro hzero
            exact hz (htail hzero (by lia))
          have hprev : 0 < a n :=
            lt_of_le_of_ne (hnonneg _) (Ne.symm hprevne)
          have hmul : a n * a (n + 2) ≤ a n * (r * a (n + 1)) := by
            calc
              a n * a (n + 2) ≤ a (n + 1) ^ 2 := hlog n
              _ ≤ (r * a n) * a (n + 1) := by
                rw [pow_two]
                exact mul_le_mul_of_nonneg_right ih (hnonneg _)
              _ = a n * (r * a (n + 1)) := by ring
          exact le_of_mul_le_mul_left hmul hprev
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        a (n + 1) ≤ r * a n := hstep n
        _ ≤ r * (a 0 * r ^ n) := mul_le_mul_of_nonneg_left ih hr
        _ = a 0 * r ^ (n + 1) := by rw [pow_succ]; ring

/-- A positive initial coefficient and PF multiplier property prevent a later
coefficient zero from being followed by a nonzero coefficient. -/
theorem IsPFMultiplierSequence.coeff_zero_tail_of_coeff_zero_pos
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma)
    (hzero : 0 < gamma 0) {n m : ℕ} (hn : gamma n = 0) (hnm : n ≤ m) :
    gamma m = 0 := by
  by_contra hm
  have hn0 : 0 < n := by
    by_contra hn0
    have : n = 0 := by lia
    subst n
    exact hzero.ne' hn
  have hnm' : n < m := lt_of_le_of_ne hnm (by rintro rfl; exact hm hn)
  let p := jensenPolynomial m gamma
  have htop : p.coeff m ≠ 0 := by
    simp [p, coeff_jensenPolynomial, hm]
  have hp0 : p ≠ 0 := fun hp0 => htop (by simp [hp0])
  have hp : IsPFPolynomial p := by
    simpa [p] using isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence hgamma m
  have hnozero := hasNoInternalCoeffZeros_of_hasNonnegCoeffs_of_eq_zero_or_splits
    hp.hasNonnegCoeffs (Or.inr (hp.ne_zero_and_splits hp0).2)
  have hcoeff0 : p.coeff 0 ≠ 0 := by simp [p, hzero.ne']
  have hdeg : m ≤ p.natDegree := le_natDegree_of_ne_zero htop
  have hcoeffn : p.coeff n ≠ 0 := hnozero 0 n m hn0 hnm' hdeg hcoeff0 htop
  simp [p, coeff_jensenPolynomial, hn] at hcoeffn

/-- A PF multiplier sequence with positive zeroth coefficient has geometric
coefficient growth. -/
theorem IsPFMultiplierSequence.coeff_le_geometric_of_coeff_zero_pos
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma)
    (hzero : 0 < gamma 0) (n : ℕ) :
    gamma n ≤ gamma 0 * (gamma 1 / gamma 0) ^ n := by
  apply exponential_bound_of_nonneg_logConcave_zero_tail hzero hgamma.nonneg hgamma.logConcave
  intro i j hi hij
  exact hgamma.coeff_zero_tail_of_coeff_zero_pos hzero hi hij

/-- A PF multiplier sequence with positive zeroth coefficient satisfies the
all-radius EGF summability hypothesis used by the analytic Jensen limit. -/
theorem IsPFMultiplierSequence.summable_expGenerating_majorant_of_coeff_zero_pos
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma)
    (hzero : 0 < gamma 0) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun k => ‖gamma k‖ * R ^ k / k.factorial) := by
  let r : ℝ := gamma 1 / gamma 0
  have hr : 0 ≤ r := div_nonneg (hgamma.nonneg 1) hzero.le
  refine Summable.of_nonneg_of_le
    (f := fun k => gamma 0 * (r * R) ^ k / k.factorial)
    (fun k => by positivity) (fun k => ?_) ?_
  · rw [Real.norm_of_nonneg (hgamma.nonneg k)]
    have hfactor : 0 ≤ R ^ k / (k.factorial : ℝ) := by positivity
    have hbound := mul_le_mul_of_nonneg_right
      (hgamma.coeff_le_geometric_of_coeff_zero_pos hzero k) hfactor
    change gamma k * R ^ k / (k.factorial : ℝ) ≤
      gamma 0 * (r * R) ^ k / (k.factorial : ℝ)
    calc
      gamma k * R ^ k / (k.factorial : ℝ) =
          gamma k * (R ^ k / (k.factorial : ℝ)) := by ring
      _ ≤ (gamma 0 * r ^ k) * (R ^ k / (k.factorial : ℝ)) := hbound
      _ = gamma 0 * (r * R) ^ k / (k.factorial : ℝ) := by
        rw [mul_pow]
        ring
  · simpa only [mul_div_assoc] using
      (Real.summable_pow_div_factorial (r * R)).mul_left (gamma 0)

/-- A PF multiplier sequence with positive zeroth coefficient has a
Laguerre--Pólya complex exponential-generating function. -/
theorem IsPFMultiplierSequence.isLaguerrePolya_complexExpGeneratingFunction_of_coeff_zero_pos
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma)
    (hzero : 0 < gamma 0) :
    IsLaguerrePolya (complexExpGeneratingFunction gamma) := by
  have hmult := (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp hgamma).1
  exact hmult.isLaguerrePolya_complexExpGeneratingFunction
    (fun R hR => hgamma.summable_expGenerating_majorant_of_coeff_zero_pos hzero R hR)

end RealRooted
