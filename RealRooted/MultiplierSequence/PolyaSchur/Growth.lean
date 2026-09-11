import RealRooted.MultiplierSequence.PolyaSchur
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya

/-!
# Exponential growth of Pólya--Schur multiplier sequences

This analytic-side child derives an all-radius exponential-generating majorant
from the PF multiplier convention and transports the resulting
Laguerre--Pólya witness through the classical alternating-sign convention.
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

/-- Every PF multiplier sequence satisfies the all-radius EGF summability
hypothesis.  A finite initial zero prefix is removed before applying the
positive-initial-coefficient estimate. -/
theorem IsPFMultiplierSequence.summable_expGenerating_majorant
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma)
    (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun k => ‖gamma k‖ * R ^ k / k.factorial) := by
  by_cases hzero : gamma = 0
  · simp [hzero]
  have hexists : ∃ n : ℕ, gamma n ≠ 0 := by
    by_contra h
    push Not at h
    exact hzero (funext h)
  let s := Nat.find hexists
  have hsne : gamma s ≠ 0 := Nat.find_spec hexists
  have hspos : 0 < gamma s :=
    lt_of_le_of_ne (hgamma.nonneg s) (Ne.symm hsne)
  have hshift := hgamma.shift s
  have hspos' : 0 < (fun k => gamma (k + s)) 0 := by simpa using hspos
  have hsum := hshift.summable_expGenerating_majorant_of_coeff_zero_pos hspos' R hR
  apply (summable_nat_add_iff s).mp
  refine Summable.of_nonneg_of_le
    (f := fun n => R ^ s * (‖gamma (n + s)‖ * R ^ n / n.factorial))
    (fun n => by positivity) (fun n => ?_) (hsum.mul_left (R ^ s))
  rw [Real.norm_of_nonneg (hgamma.nonneg (n + s))]
  have hnum : 0 ≤ gamma (n + s) * (R ^ n * R ^ s) :=
    mul_nonneg (hgamma.nonneg _) (mul_nonneg (pow_nonneg hR _) (pow_nonneg hR _))
  have hfacpos : 0 < (n.factorial : ℝ) := by positivity
  have hfacle : (n.factorial : ℝ) ≤ ((n + s).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_add_right n s)
  calc
    gamma (n + s) * R ^ (n + s) / ((n + s).factorial : ℝ) =
        (gamma (n + s) * (R ^ n * R ^ s)) / ((n + s).factorial : ℝ) := by
      rw [pow_add]
    _ ≤ (gamma (n + s) * (R ^ n * R ^ s)) / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_left hnum hfacpos hfacle
    _ = R ^ s * (gamma (n + s) * R ^ n / (n.factorial : ℝ)) := by ring

/-- A PF multiplier sequence with positive zeroth coefficient has a
Laguerre--Pólya complex exponential-generating function. -/
theorem IsPFMultiplierSequence.isLaguerrePolya_complexExpGeneratingFunction_of_coeff_zero_pos
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma)
    (hzero : 0 < gamma 0) :
    IsLaguerrePolya (complexExpGeneratingFunction gamma) := by
  have hmult := (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp hgamma).1
  exact hmult.isLaguerrePolya_complexExpGeneratingFunction
    (fun R hR => hgamma.summable_expGenerating_majorant_of_coeff_zero_pos hzero R hR)

/-- The complex EGF of every PF multiplier sequence is Laguerre--Pólya. -/
theorem IsPFMultiplierSequence.isLaguerrePolya_complexExpGeneratingFunction
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma) :
    IsLaguerrePolya (complexExpGeneratingFunction gamma) := by
  have hmult := (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp hgamma).1
  exact hmult.isLaguerrePolya_complexExpGeneratingFunction
    (fun R hR => hgamma.summable_expGenerating_majorant R hR)

/-- Alternating the signs of a PF multiplier sequence corresponds to
precomposition of its complex EGF by `z ↦ -z`. -/
theorem complexExpGeneratingFunction_alternating (gamma : ℕ → ℝ) :
    complexExpGeneratingFunction (fun k => (-1 : ℝ) ^ k * gamma k) =
      fun z => complexExpGeneratingFunction gamma (-z) := by
  rw [complexExpGeneratingFunction_eq_tsum, complexExpGeneratingFunction_eq_tsum]
  ext z
  apply tsum_congr
  intro k
  push_cast
  rw [neg_pow]
  ring

/-- The alternating-sign convention for a PF multiplier sequence also has a
Laguerre--Pólya complex EGF. -/
theorem IsPFMultiplierSequence.isLaguerrePolya_complexExpGeneratingFunction_alternating
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma) :
    IsLaguerrePolya
      (complexExpGeneratingFunction (fun k => (-1 : ℝ) ^ k * gamma k)) := by
  rw [complexExpGeneratingFunction_alternating]
  simpa using hgamma.isLaguerrePolya_complexExpGeneratingFunction.comp_affine_real (-1) 0

end RealRooted
