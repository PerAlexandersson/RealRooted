module

public import RealRooted.NarayanaInterpolation
public import RealRooted.MaWang.CriticalSign
import RealRooted.GammaTransform.ProperPosition
import RealRooted.Mathlib.Algebra.Polynomial.Coeff
import RealRooted.GammaTransform.StrictLifting
import RealRooted.MaWang.DerivativeStep
import RealRooted.NarayanaTransformation.Recurrences.Identities

/-!
# Continuous Narayana gamma polynomials

This module defines the gamma polynomials of the continuous Narayana
interpolation and proves coefficient formulas, recurrences, interlacing,
and root-location and simplicity results.
-/

public section

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- The coefficient of degree `k` in the continuous Narayana gamma polynomial. -/
def continuousNarayanaGammaCoeff (theta : ℝ) (n k : ℕ) : ℝ :=
  (n.factorial : ℝ) /
    ((n - 2 * k).factorial * k.factorial *
      (ascPochhammer ℝ k).eval (theta + 1))

/-- The gamma polynomial of the degree-`n` continuous Narayana interpolation. -/
def continuousNarayanaGamma (theta : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ range (n / 2 + 1), monomial k (continuousNarayanaGammaCoeff theta n k)

/-- Coefficients inside the defining support have the factorial--Pochhammer formula. -/
@[simp]
theorem coeff_continuousNarayanaGamma (theta : ℝ) (n k : ℕ) :
    (continuousNarayanaGamma theta n).coeff k =
      if k ≤ n / 2 then continuousNarayanaGammaCoeff theta n k else 0 := by
  simpa only [continuousNarayanaGamma, Nat.lt_succ_iff] using
    Polynomial.coeff_sum_range_monomial
      (continuousNarayanaGammaCoeff theta n) (n / 2 + 1) k

/-- The continuous Narayana gamma polynomial has degree at most `floor(n / 2)`. -/
theorem natDegree_continuousNarayanaGamma_le (theta : ℝ) (n : ℕ) :
    (continuousNarayanaGamma theta n).natDegree ≤ n / 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_continuousNarayanaGamma, ite_eq_right (by lia)]

/-- In the parameter range `theta > -1`, every coefficient in the support is positive. -/
theorem continuousNarayanaGammaCoeff_pos {theta : ℝ} (htheta : -1 < theta)
    (n k : ℕ) :
    0 < continuousNarayanaGammaCoeff theta n k := by
  unfold continuousNarayanaGammaCoeff
  exact div_pos (by positivity)
    (mul_pos (mul_pos (by positivity) (by positivity))
      (ascPochhammer_pos k (theta + 1) (by linarith)))

/-- In the parameter range `theta > -1`, the gamma polynomial has nonnegative
coefficients. -/
theorem continuousNarayanaGamma_hasNonnegCoeffs {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) :
    HasNonnegCoeffs (continuousNarayanaGamma theta n) := by
  intro k
  rw [coeff_continuousNarayanaGamma]
  split_ifs with hk
  · exact (continuousNarayanaGammaCoeff_pos htheta n k).le
  · exact le_rfl

/-- The constant coefficient of every continuous Narayana gamma polynomial is one. -/
theorem continuousNarayanaGamma_coeff_zero (theta : ℝ) (n : ℕ) :
    (continuousNarayanaGamma theta n).coeff 0 = 1 := by
  rw [coeff_continuousNarayanaGamma, ite_eq_left (by simp)]
  unfold continuousNarayanaGammaCoeff
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  simp [hn]

/-- In the parameter range `theta > -1`, the gamma polynomial has its expected degree. -/
theorem natDegree_continuousNarayanaGamma {theta : ℝ} (htheta : -1 < theta)
    (n : ℕ) :
    (continuousNarayanaGamma theta n).natDegree = n / 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_continuousNarayanaGamma_le theta n)
  rw [coeff_continuousNarayanaGamma, ite_eq_left le_rfl]
  exact (continuousNarayanaGammaCoeff_pos htheta n (n / 2)).ne'

/-- In the parameter range `theta > -1`, the gamma polynomial has positive
leading coefficient. -/
theorem continuousNarayanaGamma_hasPosLeadingCoeff {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) :
    HasPosLeadingCoeff (continuousNarayanaGamma theta n) :=
  (continuousNarayanaGamma_hasNonnegCoeffs htheta n).pos_leadingCoeff
    (by
      intro h
      have hcoeff := congrArg (fun p : ℝ[X] ↦ p.coeff 0) h
      rw [continuousNarayanaGamma_coeff_zero] at hcoeff
      norm_num at hcoeff)

/-- The existing continuous Narayana polynomial is the gamma transform of the
public continuous gamma polynomial. -/
theorem gammaTransform_continuousNarayanaGamma {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) :
    gammaTransform n (continuousNarayanaGamma theta n) =
      narayanaInterpolation theta n := by
  rw [narayanaInterpolation_eq_sum_gamma htheta]
  unfold gammaTransform continuousNarayanaGamma
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.coeff_sum_range_monomial,
    ite_eq_left (Finset.mem_range.mp hk)]
  simp only [gammaBasisTerm]
  unfold continuousNarayanaGammaCoeff
  ring

private lemma coeff_continuousNarayanaGamma_of_two_mul_le
    (theta : ℝ) {n k : ℕ} (hk : 2 * k ≤ n) :
    (continuousNarayanaGamma theta n).coeff k =
      continuousNarayanaGammaCoeff theta n k := by
  rw [coeff_continuousNarayanaGamma, ite_eq_left (by lia)]

private lemma coeff_continuousNarayanaGamma_of_lt_two_mul
    (theta : ℝ) {n k : ℕ} (hk : n < 2 * k) :
    (continuousNarayanaGamma theta n).coeff k = 0 := by
  rw [coeff_continuousNarayanaGamma, ite_eq_right (by lia)]

private lemma continuousNarayanaGammaCoeff_deriv_rec_core
    {theta : ℝ} (htheta : -1 < theta) {n k : ℕ}
    (hkpos : k ≠ 0) (hk : 2 * k ≤ n) :
    ((n : ℝ) + 2 * theta + 1) *
        (continuousNarayanaGamma theta (n + 1)).coeff k =
      ((n : ℝ) + 2 * theta + 1 + 2 * k) *
          (continuousNarayanaGamma theta n).coeff k +
        (4 * (n : ℝ) + 8 - 8 * k) *
          (continuousNarayanaGamma theta n).coeff (k - 1) := by
  let F : ℝ := (n.factorial : ℝ) /
    (k.factorial * (n - 2 * k + 2).factorial *
      (ascPochhammer ℝ k).eval (theta + 1))
  have hPk_ne : (ascPochhammer ℝ k).eval (theta + 1) ≠ 0 :=
    (ascPochhammer_pos k (theta + 1) (by linarith)).ne'
  have hF1 : (continuousNarayanaGamma theta (n + 1)).coeff k =
      ((n + 1 : ℕ) : ℝ) * ((n - 2 * k + 2 : ℕ) : ℝ) * F := by
    rw [coeff_continuousNarayanaGamma_of_two_mul_le theta (by lia)]
    unfold continuousNarayanaGammaCoeff
    dsimp only [F]
    field_simp [hPk_ne, factorial_cast_ne_zero]
    rw [factorial_succ_cast n]
    rw [show n - 2 * k + 2 = (n + 1 - 2 * k) + 1 by lia,
      factorial_succ_cast (n + 1 - 2 * k)]
    push_cast
    ring
  have hF2 : (continuousNarayanaGamma theta n).coeff k =
      ((n - 2 * k + 2 : ℕ) : ℝ) * ((n - 2 * k + 1 : ℕ) : ℝ) * F := by
    rw [coeff_continuousNarayanaGamma_of_two_mul_le theta hk]
    unfold continuousNarayanaGammaCoeff
    dsimp only [F]
    field_simp [hPk_ne, factorial_cast_ne_zero]
    rw [show n - 2 * k + 2 = (n - 2 * k + 1) + 1 by lia,
      factorial_succ_cast (n - 2 * k + 1),
      show n - 2 * k + 1 = (n - 2 * k) + 1 by lia,
      factorial_succ_cast (n - 2 * k)]
    push_cast
    ring
  have hF3 : (continuousNarayanaGamma theta n).coeff (k - 1) =
      (k : ℝ) * (theta + k) * F := by
    rw [coeff_continuousNarayanaGamma_of_two_mul_le theta (by lia)]
    unfold continuousNarayanaGammaCoeff
    dsimp only [F]
    have hkfac : (k.factorial : ℝ) = k * (k - 1).factorial :=
      factorial_cast_pred hkpos
    have hgap : n - 2 * (k - 1) = n - 2 * k + 2 := by lia
    have hpoch := ascPochhammer_succ_eval (S := ℝ) (k - 1) (theta + 1)
    have hpoch_ne : (ascPochhammer ℝ (k - 1)).eval (theta + 1) ≠ 0 :=
      (ascPochhammer_pos (k - 1) (theta + 1) (by linarith)).ne'
    have htheta_k : theta + (k : ℝ) ≠ 0 := by
      have hk_one : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hkpos)
      linarith
    rw [show k - 1 + 1 = k by lia] at hpoch
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by lia)]
      norm_num
    rw [hgap, hkfac, hpoch, hcast]
    field_simp [hpoch_ne, htheta_k, factorial_cast_ne_zero]
    ring
  rw [hF1, hF2, hF3]
  have hcast : ((n - 2 * k : ℕ) : ℝ) = (n : ℝ) - 2 * k := by
    rw [Nat.cast_sub hk]
    norm_num
  push_cast
  rw [hcast]
  ring

/-- Coefficient form of the differential recurrence for the continuous
Narayana gamma polynomials. -/
theorem coeff_continuousNarayanaGamma_deriv_rec {theta : ℝ}
    (htheta : -1 < theta) (n k : ℕ) (hkpos : k ≠ 0) :
    ((n : ℝ) + 2 * theta + 1) *
        (continuousNarayanaGamma theta (n + 1)).coeff k =
      ((n : ℝ) + 2 * theta + 1 + 2 * k) *
          (continuousNarayanaGamma theta n).coeff k +
        (4 * (n : ℝ) + 8 - 8 * k) *
          (continuousNarayanaGamma theta n).coeff (k - 1) := by
  by_cases hk : 2 * k ≤ n
  · exact continuousNarayanaGammaCoeff_deriv_rec_core htheta hkpos hk
  · by_cases htop : 2 * k ≤ n + 1
    · have heq : 2 * k = n + 1 := by lia
      rw [coeff_continuousNarayanaGamma_of_two_mul_le theta htop,
        coeff_continuousNarayanaGamma_of_lt_two_mul theta (by lia),
        coeff_continuousNarayanaGamma_of_two_mul_le theta (by lia)]
      unfold continuousNarayanaGammaCoeff
      have hgap0 : n + 1 - 2 * k = 0 := by lia
      have hgap1 : n - 2 * (k - 1) = 1 := by lia
      rw [hgap0, hgap1]
      have hpoch := ascPochhammer_succ_eval (S := ℝ) (k - 1) (theta + 1)
      have hpoch_ne : (ascPochhammer ℝ (k - 1)).eval (theta + 1) ≠ 0 :=
        (ascPochhammer_pos (k - 1) (theta + 1) (by linarith)).ne'
      have htheta_k : theta + (k : ℝ) ≠ 0 := by
        have hk_one : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hkpos)
        linarith
      rw [show k - 1 + 1 = k by lia] at hpoch
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by lia)]
        norm_num
      rw [hpoch, hcast, factorial_succ_cast n, factorial_cast_pred hkpos]
      norm_num only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
        mul_zero, add_zero]
      field_simp [hpoch_ne, htheta_k, factorial_cast_ne_zero]
      have heqR := congrArg (fun m : ℕ ↦ (m : ℝ)) heq
      push_cast at heqR ⊢
      have hnR : (n : ℝ) = 2 * (k : ℝ) - 1 := by linarith
      rw [hnR]
      ring
    · rw [coeff_continuousNarayanaGamma_of_lt_two_mul theta (by lia),
        coeff_continuousNarayanaGamma_of_lt_two_mul theta (by lia)]
      by_cases hprev : 2 * (k - 1) ≤ n
      · have heq : 2 * k = n + 2 := by lia
        have heqR := congrArg (fun m : ℕ ↦ (m : ℝ)) heq
        push_cast at heqR
        have hfactor : 4 * (n : ℝ) + 8 - 8 * k = 0 := by linarith
        rw [hfactor]
        ring
      · rw [coeff_continuousNarayanaGamma_of_lt_two_mul theta (by lia)]
        ring

/-- The continuous Narayana gamma polynomials satisfy a first-order
differential recurrence. -/
theorem continuousNarayanaGamma_deriv_rec {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) :
    C ((n : ℝ) + 2 * theta + 1) * continuousNarayanaGamma theta (n + 1) =
      (C ((n : ℝ) + 2 * theta + 1) + C (4 * (n : ℝ)) * X) *
          continuousNarayanaGamma theta n +
        C (2 : ℝ) * X * (1 - C 4 * X) *
          (continuousNarayanaGamma theta n).derivative := by
  rw [show C (2 : ℝ) * X * (1 - C 4 * X) =
      C (2 : ℝ) * X - C 8 * X ^ 2 by
        calc
          C (2 : ℝ) * X * (1 - C 4 * X) =
              C 2 * X - (C 2 * C 4) * (X * X) := by ring
          _ = C 2 * X - C 8 * X ^ 2 := by norm_num [← map_mul, pow_two]]
  ext k
  rw [add_mul, sub_mul, mul_assoc, mul_assoc]
  rcases k with _ | _ | k
  · rw [coeff_C_mul, continuousNarayanaGamma_coeff_zero]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_zero,
      continuousNarayanaGamma_coeff_zero]
    simp [coeff_mul]
  · rw [coeff_C_mul,
      coeff_continuousNarayanaGamma_deriv_rec htheta n 1 one_ne_zero]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul,
      coeff_derivative, sq, mul_assoc, coeff_X_mul_zero]
    ring
  · rw [coeff_C_mul,
      coeff_continuousNarayanaGamma_deriv_rec htheta n (k + 2) (by lia)]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul,
      coeff_derivative, sq, mul_assoc]
    push_cast
    ring

/-- The degree-zero continuous Narayana gamma polynomial is one. -/
@[simp]
theorem continuousNarayanaGamma_zero (theta : ℝ) :
    continuousNarayanaGamma theta 0 = 1 := by
  ext k
  rw [coeff_continuousNarayanaGamma]
  rcases k with _ | k
  · simp [continuousNarayanaGammaCoeff]
  · simp [coeff_one]

/-- The degree-one continuous Narayana gamma polynomial is one. -/
@[simp]
theorem continuousNarayanaGamma_one (theta : ℝ) :
    continuousNarayanaGamma theta 1 = 1 := by
  ext k
  rw [coeff_continuousNarayanaGamma]
  rcases k with _ | k
  · simp [continuousNarayanaGammaCoeff]
  · simp [coeff_one]

/-- Every real root of a continuous Narayana gamma polynomial is strictly
negative in the parameter range `theta > -1`. -/
theorem continuousNarayanaGamma_roots_neg {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) :
    ∀ r ∈ (continuousNarayanaGamma theta n).roots, r < 0 := by
  intro r hr
  refine lt_of_le_of_ne
    (roots_nonpos_of_hasNonnegCoeffs
      (continuousNarayanaGamma_hasNonnegCoeffs htheta n) r hr) fun hrzero ↦ ?_
  have hroot := isRoot_of_mem_roots hr
  subst r
  rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero,
    continuousNarayanaGamma_coeff_zero] at hroot
  norm_num at hroot

/-- Normalized form of the first-order differential recurrence. -/
theorem continuousNarayanaGamma_deriv_rec_normalized {theta : ℝ}
    (htheta : -1 < theta) {n : ℕ} (hn : 1 ≤ n) :
    continuousNarayanaGamma theta (n + 1) =
      (1 + C (4 * (n : ℝ) / ((n : ℝ) + 2 * theta + 1)) * X) *
          continuousNarayanaGamma theta n +
        (C (2 / ((n : ℝ) + 2 * theta + 1)) * X * (1 - C 4 * X)) *
          (continuousNarayanaGamma theta n).derivative := by
  let d : ℝ := (n : ℝ) + 2 * theta + 1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd_pos : 0 < d := by dsimp [d]; linarith
  have hd : d ≠ 0 := hd_pos.ne'
  have hrec := continuousNarayanaGamma_deriv_rec htheta n
  change C d * continuousNarayanaGamma theta (n + 1) = _ at hrec
  calc
    continuousNarayanaGamma theta (n + 1) =
        C d⁻¹ * (C d * continuousNarayanaGamma theta (n + 1)) := by
          rw [← mul_assoc, ← map_mul]
          simp [hd]
    _ = C d⁻¹ *
        ((C d + C (4 * (n : ℝ)) * X) * continuousNarayanaGamma theta n +
          C (2 : ℝ) * X * (1 - C 4 * X) *
            (continuousNarayanaGamma theta n).derivative) := by rw [hrec]
    _ = (1 + C (4 * (n : ℝ) / d) * X) * continuousNarayanaGamma theta n +
        (C (2 / d) * X * (1 - C 4 * X)) *
          (continuousNarayanaGamma theta n).derivative := by
          have hdinv : d⁻¹ * d = 1 := inv_mul_cancel₀ hd
          have hfour : d⁻¹ * (4 * (n : ℝ)) = 4 * n / d := by
            field_simp
          have htwo : d⁻¹ * (2 : ℝ) = 2 / d := by field_simp
          calc
            C d⁻¹ *
                ((C d + C (4 * (n : ℝ)) * X) *
                    continuousNarayanaGamma theta n +
                  C (2 : ℝ) * X * (1 - C 4 * X) *
                    (continuousNarayanaGamma theta n).derivative) =
                (C (d⁻¹ * d) + C (d⁻¹ * (4 * (n : ℝ))) * X) *
                    continuousNarayanaGamma theta n +
                  (C (d⁻¹ * 2) * X * (1 - C 4 * X)) *
                    (continuousNarayanaGamma theta n).derivative := by
                      simp only [map_mul]
                      ring
            _ = _ := by rw [hdinv, hfour, htwo, map_one]

/-- The induction package behind strict interlacing and simplicity. -/
private theorem continuousNarayanaGamma_root_package {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) :
    (continuousNarayanaGamma theta n).Splits ∧
      HasSimpleRoots (continuousNarayanaGamma theta n) ∧
      StrictInterl (continuousNarayanaGamma theta n)
        (continuousNarayanaGamma theta (n + 1)) ∧
      ∀ r, (continuousNarayanaGamma theta n).IsRoot r →
        ¬ (continuousNarayanaGamma theta (n + 1)).IsRoot r := by
  induction n with
  | zero =>
      have hstrict : StrictInterl (1 : ℝ[X]) 1 :=
        StrictInterl.refl (by simp) (by simp)
      refine ⟨by simp, ?_, by simpa using hstrict, ?_⟩
      · simp [HasSimpleRoots]
      · simp [Polynomial.IsRoot.def]
  | succ n ih =>
      let f := continuousNarayanaGamma theta (n + 1)
      let g := continuousNarayanaGamma theta (n + 2)
      let d : ℝ := ((n + 1 : ℕ) : ℝ) + 2 * theta + 1
      let u : ℝ[X] := 1 + C (4 * ((n + 1 : ℕ) : ℝ) / d) * X
      let v : ℝ[X] := C (2 / d) * X * (1 - C 4 * X)
      have hd_pos : 0 < d := by dsimp [d]; push_cast; linarith
      have hf_pos : HasPosLeadingCoeff f := by
        exact continuousNarayanaGamma_hasPosLeadingCoeff htheta (n + 1)
      have hg_pos : HasPosLeadingCoeff g := by
        exact continuousNarayanaGamma_hasPosLeadingCoeff htheta (n + 2)
      have hf_splits : f.Splits := by
        exact (ih.2.2.1).2.1.2
      have hf_simple : HasSimpleRoots f := by
        exact (ih.2.2.1.hasSimpleRoots_of_no_common_root
          (fun r hr ↦ ih.2.2.2 r hr.1 hr.2)).2
      have hrec : g = u * f + v * f.derivative := by
        simpa [f, g, u, v, d, Nat.add_assoc] using
          (continuousNarayanaGamma_deriv_rec_normalized htheta
            (n := n + 1) (by lia))
      have hdeg_lo : f.natDegree ≤ g.natDegree := by
        dsimp [f, g]
        rw [natDegree_continuousNarayanaGamma htheta,
          natDegree_continuousNarayanaGamma htheta]
        lia
      have hdeg_hi : g.natDegree ≤ f.natDegree + 1 := by
        dsimp [f, g]
        rw [natDegree_continuousNarayanaGamma htheta,
          natDegree_continuousNarayanaGamma htheta]
        lia
      have hv_neg {r : ℝ} (hr : f.IsRoot r) : v.eval r < 0 := by
        have hrmem : r ∈ f.roots := (mem_roots hf_pos.ne_zero).2 hr
        have hrneg : r < 0 := by
          exact continuousNarayanaGamma_roots_neg htheta (n + 1) r hrmem
        have hc : 0 < 2 / d := div_pos (by norm_num) hd_pos
        have hcr : 2 / d * r < 0 := mul_neg_of_pos_of_neg hc hrneg
        have hfactor : 0 < 1 - 4 * r := by linarith
        dsimp [v]
        simp only [eval_mul, eval_C, eval_X, eval_sub, eval_one]
        exact mul_neg_of_neg_of_pos hcr hfactor
      have hstrict : StrictInterl f g := by
        rw [hrec]
        exact MaWang.strictInterl_derivative_of_nonpos_of_splits hf_splits
          (by simpa only [hrec] using hdeg_lo)
          (by simpa only [hrec] using hdeg_hi)
          (by simpa only [hrec] using hg_pos) hf_pos
          (fun r hr ↦ (hv_neg hr).le)
      have hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r := by
        intro r hfr hgr
        have heval := congrArg (eval r) hrec
        have hzero : v.eval r * f.derivative.eval r = 0 := by
          rw [hgr.eq_zero, eval_add, eval_mul, eval_mul, hfr.eq_zero,
            mul_zero, zero_add] at heval
          exact heval.symm
        exact (mul_ne_zero (hv_neg hfr).ne
          (hf_simple.eval_derivative_ne_zero hfr)) hzero
      exact ⟨hf_splits, hf_simple, hstrict, hno⟩

/-- Every continuous Narayana gamma polynomial splits over the reals. -/
theorem continuousNarayanaGamma_splits {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) :
    (continuousNarayanaGamma theta n).Splits :=
  (continuousNarayanaGamma_root_package htheta n).1

/-- Every continuous Narayana gamma polynomial has only simple real roots. -/
theorem continuousNarayanaGamma_hasSimpleRoots {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) :
    HasSimpleRoots (continuousNarayanaGamma theta n) :=
  (continuousNarayanaGamma_root_package htheta n).2.1

/-- Consecutive continuous Narayana gamma polynomials interlace. -/
theorem strictInterl_continuousNarayanaGamma_succ {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) :
    StrictInterl (continuousNarayanaGamma theta n)
      (continuousNarayanaGamma theta (n + 1)) :=
  (continuousNarayanaGamma_root_package htheta n).2.2.1

/-- Consecutive continuous Narayana gamma polynomials have no common real root. -/
theorem continuousNarayanaGamma_noCommonRoot_succ {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) (r : ℝ)
    (hr : (continuousNarayanaGamma theta n).IsRoot r) :
    ¬ (continuousNarayanaGamma theta (n + 1)).IsRoot r :=
  (continuousNarayanaGamma_root_package htheta n).2.2.2 r hr

/-- Consecutive continuous Narayana interpolation polynomials interlace. -/
theorem strictInterl_narayanaInterpolation_succ {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) :
    StrictInterl (narayanaInterpolation theta n)
      (narayanaInterpolation theta (n + 1)) := by
  rw [← gammaTransform_continuousNarayanaGamma htheta,
    ← gammaTransform_continuousNarayanaGamma htheta]
  exact
    (strictInterl_gammaTransform_succ_iff
      (natDegree_continuousNarayanaGamma_le theta n)
      (natDegree_continuousNarayanaGamma_le theta (n + 1))
      (continuousNarayanaGamma_hasNonnegCoeffs htheta n)
      (continuousNarayanaGamma_hasNonnegCoeffs htheta (n + 1))
      (by rw [continuousNarayanaGamma_coeff_zero]; norm_num)
      (by rw [continuousNarayanaGamma_coeff_zero]; norm_num)).2
        (strictInterl_continuousNarayanaGamma_succ htheta n)

/-- Strict root data for two consecutive continuous Narayana interpolation
polynomials. -/
private theorem narayanaInterpolation_root_package {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) :
    HasSimpleRoots (narayanaInterpolation theta n) ∧
      HasSimpleRoots (narayanaInterpolation theta (n + 1)) ∧
      StrictInterl (narayanaInterpolation theta n)
        (narayanaInterpolation theta (n + 1)) ∧
      ∀ r, (narayanaInterpolation theta n).IsRoot r →
        ¬ (narayanaInterpolation theta (n + 1)).IsRoot r := by
  cases n with
  | zero =>
      have hstrict := strictInterl_narayanaInterpolation_succ htheta 0
      have hno : ∀ r,
          ¬ ((narayanaInterpolation theta 0).IsRoot r ∧
            (narayanaInterpolation theta 1).IsRoot r) := by
        simp [Polynomial.IsRoot.def]
      have hsimple := hstrict.hasSimpleRoots_of_no_common_root hno
      exact ⟨hsimple.1, hsimple.2, hstrict,
        fun r hr hnext ↦ hno r ⟨hr, hnext⟩⟩
  | succ n =>
      have hlift := GammaTransform.strictInterl_succ_of_no_common
        (n := n + 2) (A := continuousNarayanaGamma theta (n + 1))
        (B := continuousNarayanaGamma theta (n + 2)) (by lia)
        (by rw [natDegree_continuousNarayanaGamma htheta]; lia)
        (by rw [natDegree_continuousNarayanaGamma htheta])
        (continuousNarayanaGamma_hasPosLeadingCoeff htheta (n + 1))
        (continuousNarayanaGamma_hasPosLeadingCoeff htheta (n + 2))
        (continuousNarayanaGamma_roots_neg htheta (n + 1))
        (continuousNarayanaGamma_roots_neg htheta (n + 2))
        (strictInterl_continuousNarayanaGamma_succ htheta (n + 1))
        (fun r hr ↦
          continuousNarayanaGamma_noCommonRoot_succ htheta (n + 1) r hr.1 hr.2)
      have hsimple_left := hlift.2.2.1
      have hsimple_right := hlift.2.2.2.1
      have hstrict := hlift.2.2.2.2.2.2.1
      have hno := hlift.2.2.2.2.2.2.2
      have hidx : n + 2 - 1 = n + 1 := by lia
      rw [hidx, gammaTransform_continuousNarayanaGamma htheta] at hsimple_left
      rw [gammaTransform_continuousNarayanaGamma htheta] at hsimple_right
      rw [hidx, gammaTransform_continuousNarayanaGamma htheta,
        gammaTransform_continuousNarayanaGamma htheta] at hstrict
      rw [hidx, gammaTransform_continuousNarayanaGamma htheta,
        gammaTransform_continuousNarayanaGamma htheta] at hno
      simpa [Nat.add_assoc] using ⟨hsimple_left, hsimple_right, hstrict, hno⟩

/-- Every continuous Narayana interpolation polynomial has only simple roots. -/
theorem narayanaInterpolation_hasSimpleRoots {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) :
    HasSimpleRoots (narayanaInterpolation theta n) :=
  (narayanaInterpolation_root_package htheta n).1

/-- Consecutive continuous Narayana interpolation polynomials have no common
real root. -/
theorem narayanaInterpolation_noCommonRoot_succ {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) (r : ℝ)
    (hr : (narayanaInterpolation theta n).IsRoot r) :
    ¬ (narayanaInterpolation theta (n + 1)).IsRoot r :=
  (narayanaInterpolation_root_package htheta n).2.2.2 r hr

/-- Coefficient identity eliminating the parameter derivative from one row. -/
private theorem coeff_continuousNarayanaGamma_pred {theta : ℝ}
    (htheta : -1 < theta) {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    (n : ℝ) * (continuousNarayanaGamma theta (n - 1)).coeff k =
      ((n : ℝ) - 2 * k) * (continuousNarayanaGamma theta n).coeff k := by
  have hPk_ne : (ascPochhammer ℝ k).eval (theta + 1) ≠ 0 :=
    (ascPochhammer_pos k (theta + 1) (by linarith)).ne'
  by_cases hkpred : 2 * k ≤ n - 1
  · rw [coeff_continuousNarayanaGamma_of_two_mul_le theta hkpred,
      coeff_continuousNarayanaGamma_of_two_mul_le theta (by lia)]
    unfold continuousNarayanaGammaCoeff
    have hgap : n - 2 * k = (n - 1 - 2 * k) + 1 := by lia
    rw [factorial_cast_pred hn, hgap,
      factorial_succ_cast (n - 1 - 2 * k)]
    field_simp [hPk_ne, factorial_cast_ne_zero]
    have hcast : ((n - 1 - 2 * k : ℕ) : ℝ) =
        (n : ℝ) - 1 - 2 * k := by
      rw [Nat.cast_sub (by lia), Nat.cast_sub (by lia)]
      norm_num
    rw [hcast]
    ring
  · by_cases hk : 2 * k ≤ n
    · have heq : 2 * k = n := by lia
      rw [coeff_continuousNarayanaGamma_of_lt_two_mul theta (by lia),
        coeff_continuousNarayanaGamma_of_two_mul_le theta hk]
      have heqR := congrArg (fun m : ℕ ↦ (m : ℝ)) heq
      push_cast at heqR ⊢
      rw [heqR]
      ring
    · rw [coeff_continuousNarayanaGamma_of_lt_two_mul theta (by lia),
        coeff_continuousNarayanaGamma_of_lt_two_mul theta (by lia)]
      ring

/-- The continuous Narayana gamma polynomials have a one-step derivative
representation. -/
theorem continuousNarayanaGamma_pred_deriv_rec {theta : ℝ}
    (htheta : -1 < theta) {n : ℕ} (hn : 1 ≤ n) :
    C (n : ℝ) * continuousNarayanaGamma theta (n - 1) =
      C (n : ℝ) * continuousNarayanaGamma theta n -
        C (2 : ℝ) * X * (continuousNarayanaGamma theta n).derivative := by
  rw [show C (2 : ℝ) * X * (continuousNarayanaGamma theta n).derivative =
      C 2 * (X * (continuousNarayanaGamma theta n).derivative) by ring]
  ext k
  rw [coeff_C_mul, coeff_sub, coeff_C_mul, coeff_C_mul,
    coeff_X_mul_derivative, coeff_continuousNarayanaGamma_pred htheta (by lia)]
  ring

/-- The continuous Narayana gamma polynomials satisfy a pure three-term
recurrence. -/
theorem continuousNarayanaGamma_pure_rec {theta : ℝ}
    (htheta : -1 < theta) (n : ℕ) :
    C ((n : ℝ) + 2 * theta + 2) * continuousNarayanaGamma theta (n + 2) =
      C ((2 * n : ℝ) + 2 * theta + 3) *
          continuousNarayanaGamma theta (n + 1) -
        C ((n : ℝ) + 1) * (1 - C 4 * X) *
          continuousNarayanaGamma theta n := by
  have hrec := continuousNarayanaGamma_deriv_rec htheta (n + 1)
  have hpred := continuousNarayanaGamma_pred_deriv_rec htheta
    (n := n + 1) (by lia)
  push_cast at hrec hpred ⊢
  have hd : (n : ℝ) + 1 + 2 * theta + 1 = n + 2 * theta + 2 := by ring
  rw [hd] at hrec
  have hder :
      C (2 : ℝ) * X * (continuousNarayanaGamma theta (n + 1)).derivative =
        C ((n : ℝ) + 1) * continuousNarayanaGamma theta (n + 1) -
          C ((n : ℝ) + 1) * continuousNarayanaGamma theta n := by
    linear_combination hpred
  have hfour : C (4 * ((n : ℝ) + 1)) = C 4 * C ((n : ℝ) + 1) := by
    rw [← map_mul]
  have hsum : C ((2 : ℝ) * n + 2 * theta + 3) =
      C ((n : ℝ) + 2 * theta + 2) + C ((n : ℝ) + 1) := by
    rw [← map_add]
    congr 1
    ring
  rw [hrec]
  rw [show C (2 : ℝ) * X * (1 - C 4 * X) *
      (continuousNarayanaGamma theta (n + 1)).derivative =
        (1 - C 4 * X) *
          (C 2 * X * (continuousNarayanaGamma theta (n + 1)).derivative) by ring,
    hder]
  rw [hfour, hsum]
  ring

end RealRooted
