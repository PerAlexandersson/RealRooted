module

public import RealRooted.MultiplierSequence.JensenLaguerre
public import Mathlib.RingTheory.Binomial
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Classical Laguerre basis for Jensen transforms

The rising-factorial transform is exactly `d!` times the Laguerre family in
O'Sullivan, *Zeros of Jensen polynomials and asymptotics for the Riemann xi
function*, equation (3.8) and Theorem 3.9, https://arxiv.org/abs/2007.13582.
These algebraic identities hold for every real parameter, including `-1` and `-2`.
-/

public section

open Polynomial
open scoped BigOperators

namespace RealRooted

noncomputable section

private theorem descFactorial_mul_choose_eq_pochhammer
    (d j : ℕ) (hjd : j ≤ d) (alpha : ℝ) :
    (d.descFactorial j : ℝ) * Ring.choose ((d : ℝ) + alpha) j =
      (d.choose j : ℝ) *
        (ascPochhammer ℝ j).eval (alpha + (d - j : ℕ) + 1) := by
  have harg : (d : ℝ) + alpha - j + 1 = alpha + (d - j : ℕ) + 1 := by
    rw [Nat.cast_sub hjd]
    ring
  have hfac : (j.factorial : ℝ) ≠ 0 := by positivity
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
    Ring.choose_eq_smul, descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval, smul_eq_mul, harg]
  field_simp [hfac]

private theorem laguerre_classical_coefficient_factor
    (d k j : ℕ) (hjk : j ≤ k) (hkd : k ≤ d) (alpha : ℝ) :
    (d.descFactorial j : ℝ) * Ring.choose ((d : ℝ) + alpha) j *
        ((d - j).choose (k - j) : ℝ) *
        (ascPochhammer ℝ (d - k)).eval (alpha + (k - j : ℕ) + 1) =
      (d.choose k : ℝ) * (k.choose j : ℝ) *
        (ascPochhammer ℝ (d - (k - j))).eval (alpha + (k - j : ℕ) + 1) := by
  have hjd : j ≤ d := hjk.trans hkd
  rw [descFactorial_mul_choose_eq_pochhammer d j hjd alpha]
  have hchoose :
      (d.choose j : ℝ) * ((d - j).choose (k - j) : ℝ) =
        (d.choose k : ℝ) * (k.choose j : ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := d) (k := k) (s := j) hjk).symm
  have hlength : d - k + j = d - (k - j) := by lia
  have hindices : k - j + (d - k) = d - j := by lia
  have hindicesR := congrArg (fun n : ℕ => (n : ℝ)) hindices
  push_cast at hindicesR
  have hshift :
      (alpha + (k - j : ℕ) + 1) + (d - k : ℕ) =
        alpha + (d - j : ℕ) + 1 := by linarith
  have hpoch :
      (ascPochhammer ℝ (d - k)).eval (alpha + (k - j : ℕ) + 1) *
          (ascPochhammer ℝ j).eval (alpha + (d - j : ℕ) + 1) =
        (ascPochhammer ℝ (d - (k - j))).eval (alpha + (k - j : ℕ) + 1) := by
    have h := congrArg (fun p : ℝ[X] => p.eval (alpha + (k - j : ℕ) + 1))
      (ascPochhammer_mul (S := ℝ) (d - k) j)
    simpa only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast,
      hshift, hlength] using h
  calc
    _ = ((d.choose j : ℝ) * ((d - j).choose (k - j) : ℝ)) *
        ((ascPochhammer ℝ (d - k)).eval (alpha + (k - j : ℕ) + 1) *
          (ascPochhammer ℝ j).eval (alpha + (d - j : ℕ) + 1)) := by ring
    _ = _ := by rw [hchoose, hpoch]

private theorem coeff_laguerreJensenPolynomial_by_input
    (d k : ℕ) (gamma : ℕ → ℝ) (alpha : ℝ) (hk : k ≤ d) :
    (laguerreJensenPolynomial d gamma alpha).coeff k =
      (d.choose k : ℝ) *
        ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℝ) * gamma j * (-1 : ℝ) ^ (k - j) *
            (ascPochhammer ℝ (d - (k - j))).eval (alpha + (k - j : ℕ) + 1) := by
  rw [laguerreJensenPolynomial, coeff_jensenProductPolynomial,
    ite_eq_left hk, binomialConvolution]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [laguerreJensenCoeff]
  ring

/-- The Gamma-free Laguerre Jensen family expanded in the classical-sign
Laguerre basis. This identity holds for every real parameter, including -1 and -2. -/
theorem laguerreJensenPolynomial_eq_laguerre_sum
    (d : ℕ) (gamma : ℕ → ℝ) (alpha : ℝ) :
    laguerreJensenPolynomial d gamma alpha =
      ∑ j ∈ Finset.range (d + 1),
        C ((d.descFactorial j : ℝ) * Ring.choose ((d : ℝ) + alpha) j * gamma j) *
          (X ^ j * (generalizedLaguerre (d - j) alpha).comp (-X)) := by
  let B (j : ℕ) : ℝ[X] :=
    C ((d.descFactorial j : ℝ) * Ring.choose ((d : ℝ) + alpha) j * gamma j) *
      (X ^ j * (generalizedLaguerre (d - j) alpha).comp (-X))
  ext k
  change (laguerreJensenPolynomial d gamma alpha).coeff k =
    (∑ j ∈ Finset.range (d + 1), B j).coeff k
  rw [finsetSum_coeff]
  by_cases hk : k ≤ d
  · rw [coeff_laguerreJensenPolynomial_by_input d k gamma alpha hk, Finset.mul_sum]
    symm
    calc
      ∑ j ∈ Finset.range (d + 1), (B j).coeff k =
          ∑ j ∈ Finset.range (k + 1), (B j).coeff k := by
        symm
        apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hk))
        intro j hjd hjk
        have hkj : k < j := by
          simp only [Finset.mem_range, not_lt] at hjk
          lia
        simp only [B, coeff_C_mul, coeff_X_pow_mul',
          ite_eq_right (Nat.not_le.mpr hkj), mul_zero]
      _ = ∑ j ∈ Finset.range (k + 1),
          (d.choose k : ℝ) *
            ((k.choose j : ℝ) * gamma j * (-1 : ℝ) ^ (k - j) *
              (ascPochhammer ℝ (d - (k - j))).eval
                (alpha + (k - j : ℕ) + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsub : k - j ≤ d - j := by lia
        have hlength : d - j - (k - j) = d - k := by lia
        simp only [B, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hjk,
          coeff_comp_neg_X, coeff_generalizedLaguerre, ite_eq_left hsub, hlength]
        calc
          _ = ((d.descFactorial j : ℝ) * Ring.choose ((d : ℝ) + alpha) j *
              ((d - j).choose (k - j) : ℝ) *
              (ascPochhammer ℝ (d - k)).eval (alpha + (k - j : ℕ) + 1)) *
              gamma j * (-1 : ℝ) ^ (k - j) := by ring
          _ = _ := by
            rw [laguerre_classical_coefficient_factor d k j hjk hk alpha]
            ring
  · rw [coeff_laguerreJensenPolynomial, ite_eq_right hk]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hdk : d < k := Nat.lt_of_not_ge hk
    have hjk : j ≤ k := by lia
    have hsub : ¬ k - j ≤ d - j := by lia
    simp only [B, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hjk,
      coeff_comp_neg_X, coeff_generalizedLaguerre, ite_eq_right hsub,
      zero_mul, mul_zero]

/-- Written with the standard Laguerre normalization, the polynomial is d! Q.
Here `C (m!⁻¹) * (generalizedLaguerre m alpha).comp (-X)` denotes L_m^alpha(X). -/
theorem laguerreJensenPolynomial_eq_factorial_mul
    (d : ℕ) (gamma : ℕ → ℝ) (alpha : ℝ) :
    laguerreJensenPolynomial d gamma alpha =
      C (d.factorial : ℝ) *
        ∑ j ∈ Finset.range (d + 1),
          C (Ring.choose ((d : ℝ) + alpha) j * gamma j) *
            (X ^ j * (C (((d - j).factorial : ℝ)⁻¹) *
              (generalizedLaguerre (d - j) alpha).comp (-X))) := by
  rw [laguerreJensenPolynomial_eq_laguerre_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hf : (((d - j).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hfac := congrArg (fun n : ℕ => (n : ℝ)) (Nat.factorial_mul_descFactorial hjd)
  push_cast at hfac
  have hdesc : (d.descFactorial j : ℝ) =
      (d.factorial : ℝ) * (((d - j).factorial : ℝ)⁻¹) := by
    field_simp [hf]
    nlinarith [hfac]
  rw [hdesc]
  simp only [map_mul]
  ring

end

end RealRooted
