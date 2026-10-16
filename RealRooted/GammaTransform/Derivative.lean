module

public import RealRooted.GammaTransform.Basic

/-!
# Euler derivatives of gamma transforms

Linearity of `gammaTransform` under negation and subtraction, and the action of the Euler
operator `X * d/dX` on a gamma transform.
-/

public noncomputable section

open Polynomial

namespace RealRooted

/-- The gamma transform commutes with negation. -/
@[simp] lemma gammaTransform_neg (d : ℕ) (gamma : ℝ[X]) :
    gammaTransform d (-gamma) = -gammaTransform d gamma := by
  have hneg : -gamma = C (-1 : ℝ) * gamma := by simp
  rw [hneg, gammaTransform_C_mul]
  simp

/-- The gamma transform commutes with subtraction. -/
@[simp] lemma gammaTransform_sub (d : ℕ) (gamma delta : ℝ[X]) :
    gammaTransform d (gamma - delta) =
      gammaTransform d gamma - gammaTransform d delta := by
  rw [sub_eq_add_neg, gammaTransform_add, gammaTransform_neg, sub_eq_add_neg]

private lemma gammaBasisTerm_euler_derivative (d i : ℕ) (hi : 2 * i ≤ d) :
    X * (X + 1) * (gammaBasisTerm d i).derivative =
      C (i : ℝ) * (1 - X) * gammaBasisTerm d i +
        C (d : ℝ) * X * gammaBasisTerm d i := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hi
  rcases i with _ | i
  · rcases r with _ | r
    · simp [gammaBasisTerm]
    · simp only [gammaBasisTerm, Nat.add_sub_cancel_left, pow_zero, one_mul,
        derivative_pow, Nat.add_sub_cancel, derivative_add,
        derivative_X, derivative_one, add_zero, mul_one]
      push_cast
      norm_num [map_ofNat, map_natCast]
      rw [pow_succ]
      ring
  · simp only [gammaBasisTerm]
    have hsub : 2 * (i + 1) + r - 2 * (i + 1) = r := by lia
    rw [hsub]
    simp only [derivative_mul, derivative_pow]
    rcases r with _ | r
    · norm_num [map_ofNat, map_natCast]
      ring
    · simp only [Nat.add_sub_cancel, derivative_add, derivative_X,
        derivative_one, add_zero, mul_one]
      push_cast
      norm_num [map_ofNat, map_natCast]
      ring

/-- The Euler derivative of a gamma transform is the transform of the Euler
derivative of its gamma polynomial, plus the ambient-degree term. -/
theorem gammaTransform_euler_derivative (d : ℕ) (gamma : ℝ[X]) :
    X * (X + 1) * (gammaTransform d gamma).derivative =
      (1 - X) * gammaTransform d (X * gamma.derivative) +
        C (d : ℝ) * X * gammaTransform d gamma := by
  have hcoeff (i : ℕ) :
      (X * gamma.derivative).coeff i = (i : ℝ) * gamma.coeff i := by
    rcases i with _ | i
    · simp
    · rw [coeff_X_mul, coeff_derivative]
      push_cast
      ring
  have hmoment : gammaTransform d (X * gamma.derivative) =
      ∑ i ∈ Finset.range (d / 2 + 1),
        C ((i : ℝ) * gamma.coeff i) * gammaBasisTerm d i := by
    unfold gammaTransform
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoeff]
  rw [hmoment]
  unfold gammaTransform
  rw [derivative_sum]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have htwo : 2 * i ≤ d := by
    have hi_le : i ≤ d / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    lia
  calc
    X * (X + 1) * (C (gamma.coeff i) * (gammaBasisTerm d i).derivative) =
        C (gamma.coeff i) *
          (X * (X + 1) * (gammaBasisTerm d i).derivative) := by ring
    _ = C (gamma.coeff i) *
        (C (i : ℝ) * (1 - X) * gammaBasisTerm d i +
          C (d : ℝ) * X * gammaBasisTerm d i) := by
      rw [gammaBasisTerm_euler_derivative d i htwo]
    _ = (1 - X) * (C ((i : ℝ) * gamma.coeff i) * gammaBasisTerm d i) +
        C (d : ℝ) * X * (C (gamma.coeff i) * gammaBasisTerm d i) := by
      rw [map_mul]
      ring

end RealRooted
