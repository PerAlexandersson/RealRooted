import RealRooted.GammaPencil.Basic
import RealRooted.GammaPencil.Invariants
import RealRooted.GammaTransform.Basic

/-!
# Intertwining the Eulerian step and the gamma operator

The gamma transform carries the rank-`m` gamma operator to the differential
step on palindromic polynomials of ambient degree `m`. This is the reusable
algebraic bridge behind lagged gamma recurrences.
-/

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace RealRooted

/-- The rank-`m` Eulerian differential step on the original polynomial. -/
def gammaEulerianStep (m : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  oreAffineDerivativeLinearMap
    (C 1 + C ((m : ℝ) + 1) * X) (X - X ^ 2)

@[simp]
theorem gammaEulerianStep_apply (m : ℕ) (p : ℝ[X]) :
    gammaEulerianStep m p =
      (X - X ^ 2) * p.derivative +
        (C 1 + C ((m : ℝ) + 1) * X) * p := by
  simp [gammaEulerianStep]
  ring

private lemma gammaEulerianStep_basis_zero_succ (r : ℕ) :
    (X - X ^ 2) * derivative ((X + 1 : ℝ[X]) ^ (r + 1)) +
        (C 1 + C (((r + 1 : ℕ) : ℝ) + 1) * X) * (X + 1) ^ (r + 1) =
      C (1 : ℝ) * (X + 1) ^ (r + 2) +
        C (2 * (((r + 1 : ℕ) : ℝ) - 0)) * (X * (X + 1) ^ r) := by
  rw [derivative_pow]
  simp only [Nat.add_sub_cancel, derivative_add, derivative_X, derivative_one,
    add_zero, mul_one]
  rw [show r + 2 = (r + 1) + 1 by lia, pow_succ]
  push_cast
  norm_num [map_ofNat, map_add, map_mul, map_natCast]
  ring

private lemma gammaEulerianStep_basis_top (i : ℕ) :
    (X - X ^ 2) * derivative ((X : ℝ[X]) ^ (i + 1)) +
        (C 1 + C (((2 * (i + 1) : ℕ) : ℝ) + 1) * X) * X ^ (i + 1) =
      C (((i + 1 : ℕ) : ℝ) + 1) * (X ^ (i + 1) * (X + 1)) := by
  rw [derivative_X_pow_succ]
  push_cast
  norm_num [map_ofNat, map_add, map_mul, map_natCast]
  ring

private lemma gammaEulerianStep_basis_middle (i r : ℕ) :
    (X - X ^ 2) *
          derivative ((X : ℝ[X]) ^ (i + 1) * (X + 1) ^ (r + 1)) +
        (C 1 + C (((2 * (i + 1) + (r + 1) : ℕ) : ℝ) + 1) * X) *
          (X ^ (i + 1) * (X + 1) ^ (r + 1)) =
      C (((i + 1 : ℕ) : ℝ) + 1) * (X ^ (i + 1) * (X + 1) ^ (r + 2)) +
        C (2 * (((r + 1 : ℕ) : ℝ))) * (X ^ (i + 2) * (X + 1) ^ r) := by
  rw [derivative_mul, derivative_X_pow_succ, derivative_pow]
  simp only [Nat.add_sub_cancel, derivative_add, derivative_X, derivative_one,
    add_zero, mul_one]
  rw [show r + 2 = (r + 1) + 1 by lia, pow_succ]
  push_cast
  norm_num [map_ofNat, map_add, map_mul, map_natCast]
  ring

/-- One gamma basis vector is carried to the two adjacent basis vectors in
the next ambient degree. -/
theorem gammaEulerianStep_gammaBasisTerm (m i : ℕ) (hi : 2 * i ≤ m) :
    gammaEulerianStep m (gammaBasisTerm m i) =
      C ((i : ℝ) + 1) * gammaBasisTerm (m + 1) i +
        C (2 * ((m : ℝ) - 2 * i)) * gammaBasisTerm (m + 1) (i + 1) := by
  rw [gammaEulerianStep_apply]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hi
  rcases i with _ | i
  · rcases r with _ | r
    · simp [gammaBasisTerm, add_comm]
    · simpa [gammaBasisTerm] using gammaEulerianStep_basis_zero_succ r
  · rcases r with _ | r
    · simpa [gammaBasisTerm] using gammaEulerianStep_basis_top i
    · have hleft :
          2 * (i + 1) + (r + 1) + 1 - 2 * (i + 1) = r + 2 := by lia
      have hright :
          2 * (i + 1) + (r + 1) + 1 - 2 * (i + 1 + 1) = r := by lia
      have hcurrent :
          2 * (i + 1) + (r + 1) - 2 * (i + 1) = r + 1 := by lia
      have hreal :
          ((2 * (i + 1) + (r + 1) : ℕ) : ℝ) - 2 * ((i + 1 : ℕ) : ℝ) =
            ((r + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      simp only [gammaBasisTerm]
      rw [hcurrent, hleft, hright, hreal]
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.add_assoc] using
        gammaEulerianStep_basis_middle i r

private lemma gammaEulerianStep_gammaTransform_sum (m : ℕ) (γ : ℝ[X]) :
    gammaEulerianStep m (gammaTransform m γ) =
      ∑ i ∈ range (m / 2 + 1),
        C (γ.coeff i) *
          (C ((i : ℝ) + 1) * gammaBasisTerm (m + 1) i +
            C (2 * ((m : ℝ) - 2 * i)) * gammaBasisTerm (m + 1) (i + 1)) := by
  unfold gammaTransform
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [← Polynomial.smul_eq_C_mul, LinearMap.map_smul,
    Polynomial.smul_eq_C_mul, gammaEulerianStep_gammaBasisTerm]
  lia

/-- The gamma transform intertwines `gammaOperator m` with the Eulerian
differential step from ambient degree `m` to `m + 1`. -/
theorem gammaEulerianStep_gammaTransform (m : ℕ) (γ : ℝ[X])
    (hγ : γ.natDegree ≤ m / 2) :
    gammaEulerianStep m (gammaTransform m γ) =
      gammaTransform (m + 1) (gammaOperator m γ) := by
  rw [gammaEulerianStep_gammaTransform_sum]
  let A : ℕ → ℝ[X] := fun i =>
    C (γ.coeff i) * C ((i : ℝ) + 1) * gammaBasisTerm (m + 1) i
  let B : ℕ → ℝ[X] := fun i =>
    C (γ.coeff i) * C (2 * ((m : ℝ) - 2 * i)) *
      gammaBasisTerm (m + 1) (i + 1)
  have hsource :
      (∑ i ∈ range (m / 2 + 1),
          C (γ.coeff i) *
            (C ((i : ℝ) + 1) * gammaBasisTerm (m + 1) i +
              C (2 * ((m : ℝ) - 2 * i)) * gammaBasisTerm (m + 1) (i + 1))) =
        ∑ i ∈ range (m / 2 + 1), (A i + B i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [A, B]
    ring
  rw [hsource]
  rcases Nat.mod_two_eq_zero_or_one m with heven | hodd
  · let s := m / 2
    have hm : m = 2 * s := by dsimp [s]; lia
    have hhalf : (m + 1) / 2 = s := by lia
    have hzero :
        C ((gammaOperator m γ).coeff 0) * gammaBasisTerm (m + 1) 0 = A 0 := by
      simp [A]
    have hsucc : ∀ k < s,
        C ((gammaOperator m γ).coeff (k + 1)) *
            gammaBasisTerm (m + 1) (k + 1) = A (k + 1) + B k := by
      intro k hk
      rw [gammaOperator_coeff]
      simp only [A, B, map_add, map_mul]
      push_cast
      norm_num [map_ofNat, map_add, map_mul, map_natCast]
      ring
    have hBtop : B s = 0 := by
      simp [B, hm]
    have htarget :
        (∑ k ∈ range s,
            C ((gammaOperator m γ).coeff (k + 1)) *
              gammaBasisTerm (m + 1) (k + 1)) =
          ∑ k ∈ range s, (A (k + 1) + B k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hsucc k (Finset.mem_range.mp hk)
    have hcombine :
        (∑ k ∈ range s, (A (k + 1) + B k)) + A 0 =
          ∑ i ∈ range (s + 1), (A i + B i) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_range_succ', Finset.sum_range_succ, hBtop, add_zero]
      ring
    symm
    rw [gammaTransform, hhalf, Finset.sum_range_succ', hzero, htarget]
    simpa [s] using hcombine
  · let s := m / 2
    have hm : m = 2 * s + 1 := by dsimp [s]; lia
    have hhalf : (m + 1) / 2 = s + 1 := by lia
    have hzero :
        C ((gammaOperator m γ).coeff 0) * gammaBasisTerm (m + 1) 0 = A 0 := by
      simp [A]
    have hsucc : ∀ k < s + 1,
        C ((gammaOperator m γ).coeff (k + 1)) *
            gammaBasisTerm (m + 1) (k + 1) = A (k + 1) + B k := by
      intro k hk
      rw [gammaOperator_coeff]
      simp only [A, B, map_add, map_mul]
      push_cast
      norm_num [map_ofNat, map_add, map_mul, map_natCast]
      ring
    have hAtop : A (s + 1) = 0 := by
      have hcoeff : γ.coeff (s + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by dsimp [s]; lia)
      simp [A, hcoeff]
    have htarget :
        (∑ k ∈ range (s + 1),
            C ((gammaOperator m γ).coeff (k + 1)) *
              gammaBasisTerm (m + 1) (k + 1)) =
          ∑ k ∈ range (s + 1), (A (k + 1) + B k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hsucc k (Finset.mem_range.mp hk)
    have hcombine :
        (∑ k ∈ range (s + 1), (A (k + 1) + B k)) + A 0 =
          ∑ i ∈ range (s + 1), (A i + B i) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Finset.sum_range_succ (f := fun k => A (k + 1)), hAtop, add_zero]
      rw [Finset.sum_range_succ' A]
      ring
    symm
    rw [gammaTransform, hhalf, Finset.sum_range_succ', hzero, htarget]
    simpa [s] using hcombine

end RealRooted
