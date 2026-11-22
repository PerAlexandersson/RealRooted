module

public import RealRooted.MultiplierSequence.Infinite
public import RealRooted.MultiplierSequence.JensenProduct
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import RealRooted.MultiplierSequence.BinomialConvolution
import RealRooted.MultiplierSequence.InvPochhammer
import RealRooted.Mathlib.RingTheory.Polynomial.Pochhammer.ReciprocalConvolution
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Gamma normalization of reciprocal-Pochhammer convolution

The finite-product numerator supplies the canceled Gamma ratio at its
removable singularity. For positive parameters whose sum differs from one,
the usual quotient is valid at every index. When the sum is one, its zeroth
value must be defined separately.

These are the precise normalizations of Craven--Csordas (2006), Lemma 3.12
and Theorem 3.14. Mathlib assigns zero to Gamma at its poles, so substituting
that value directly in the uncanceled quotient would lose its constant term.
-/

public section

open Polynomial

namespace RealRooted

/-- Reciprocal Gamma along a positive natural shift is a constant multiple
of a reciprocal rising factorial. -/
private theorem inv_Gamma_add_nat_eq {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (Real.Gamma (a + n))⁻¹ =
      (Real.Gamma a)⁻¹ * ((ascPochhammer ℝ n).eval a)⁻¹ := by
  have h := Real.inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add a n
  have hA := (ascPochhammer_pos n a ha).ne'
  rw [mul_comm] at h
  exact (eq_div_iff hA).mpr h.symm

/-- Reciprocal Gamma evaluated at positive natural shifts gives a PF
multiplier sequence. -/
theorem isPFMultiplierSequence_inv_Gamma_add {a : ℝ} (ha : 0 < a) :
    IsPFMultiplierSequence (fun n => (Real.Gamma (a + n))⁻¹) := by
  simp_rw [inv_Gamma_add_nat_eq ha]
  exact (isPFMultiplierSequence_inv_ascPochhammer ha).const_mul
    (inv_nonneg.mpr (Real.Gamma_pos_of_pos ha).le)

/-- The binomial convolution of reciprocal Gamma values has a pole-free
finite-product numerator, including index zero. -/
theorem binomialConvolution_inv_Gamma_eq {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    binomialConvolution (fun k => (Real.Gamma (a + k))⁻¹)
        (fun k => (Real.Gamma (b + k))⁻¹) n =
      (ascPochhammer ℝ n).eval (a + b + n - 1) /
        (Real.Gamma (a + n) * Real.Gamma (b + n)) := by
  simp_rw [inv_Gamma_add_nat_eq ha, inv_Gamma_add_nat_eq hb]
  rw [binomialConvolution_const_mul, binomialConvolution,
    sum_choose_mul_inv_ascPochhammer n
      (ascPochhammer_pos n a ha).ne' (ascPochhammer_pos n b hb).ne']
  have haeq := Real.Gamma_add_nat_div_Gamma_eq (n := n) a
    (fun k => ne_of_gt (lt_of_le_of_lt (neg_nonpos.mpr (Nat.cast_nonneg k)) ha))
  have hbeq := Real.Gamma_add_nat_div_Gamma_eq (n := n) b
    (fun k => ne_of_gt (lt_of_le_of_lt (neg_nonpos.mpr (Nat.cast_nonneg k)) hb))
  rw [← haeq, ← hbeq]
  field_simp

/-- The canceled Gamma convolution gives a PF multiplier sequence for all
positive parameters, including a parameter sum of one. -/
theorem isPFMultiplierSequence_gammaConvolution {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    IsPFMultiplierSequence (fun n =>
      (ascPochhammer ℝ n).eval (a + b + n - 1) /
        (Real.Gamma (a + n) * Real.Gamma (b + n))) := by
  have h := (isPFMultiplierSequence_inv_Gamma_add ha).binomialConvolution
    (isPFMultiplierSequence_inv_Gamma_add hb)
  convert h using 1
  ext n
  exact (binomialConvolution_inv_Gamma_eq ha hb n).symm

/-- Away from the sole removable pole, the finite-product convolution is the
usual quotient of Gamma values. -/
theorem pochhammer_div_gamma_mul_eq_gamma_ratio {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {n : ℕ} (h : n ≠ 0 ∨ a + b ≠ 1) :
    (ascPochhammer ℝ n).eval (a + b + n - 1) /
        (Real.Gamma (a + n) * Real.Gamma (b + n)) =
      Real.Gamma (2 * n + a + b - 1) /
        (Real.Gamma (a + n) * Real.Gamma (b + n) * Real.Gamma (n + a + b - 1)) := by
  have hpole : ∀ k : ℕ, a + b + n - 1 ≠ -(k : ℝ) := by
    intro k heq
    cases n with
    | zero =>
      have hab : a + b ≠ 1 := h.resolve_left (by simp)
      cases k with
      | zero => simp only [Nat.cast_zero, add_zero, neg_zero] at heq; exact hab (by linarith)
      | succ k => push_cast at heq; have := Nat.cast_nonneg (α := ℝ) k; linarith
    | succ n =>
      push_cast at heq
      have := Nat.cast_nonneg (α := ℝ) n
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
  rw [← Real.Gamma_add_nat_div_Gamma_eq (a + b + n - 1) hpole]
  rw [show a + b + (n : ℝ) - 1 + n = 2 * n + a + b - 1 by ring,
    show a + b + (n : ℝ) - 1 = n + a + b - 1 by ring]
  ring

/-- The ordinary Gamma quotient gives the convolution multiplier sequence
when the positive parameters do not sum to one. -/
theorem isPFMultiplierSequence_gammaRatio {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≠ 1) :
    IsPFMultiplierSequence (fun n =>
      Real.Gamma (2 * n + a + b - 1) /
        (Real.Gamma (a + n) * Real.Gamma (b + n) * Real.Gamma (n + a + b - 1))) := by
  simpa only [pochhammer_div_gamma_mul_eq_gamma_ratio ha hb (Or.inr hab)] using
    isPFMultiplierSequence_gammaConvolution ha hb

/-- The zeroth coefficient of the canceled convolution is the product of
reciprocal Gamma values, also when the parameters sum to one. -/
theorem gammaConvolution_zero (a b : ℝ) :
    (ascPochhammer ℝ 0).eval (a + b + (0 : ℕ) - 1) /
        (Real.Gamma (a + (0 : ℕ)) * Real.Gamma (b + (0 : ℕ))) =
      1 / (Real.Gamma a * Real.Gamma b) := by
  simp

end RealRooted
