module

public import RealRooted.CombinatorialExamples.BigDescents132.Basic
public import RealRooted.Mathlib.RingTheory.PowerSeries.Sqrt
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Generating function for the 132 big-descent recurrence

Let `F = sum_(N >= 1) B_N z^N`, with zero constant coefficient.  The positive recurrence
gives `F = zU + zLF + tzLF^2`, where `U = 1 + z + z^2 + ...` and `L = 1 + tzU`.
After multiplication by `1-z`, this becomes the quadratic identity

`(1 - 2z + (1-t)z^2)F = z + tz(1-(1-t)z)F^2`.

We prove uniqueness over every commutative ring and the normalized square-root form over a
rational algebra.  No division by `t` is used, so all identities retain the specialization
`t = 0`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.BigDescents132

section Semiring

variable {R : Type*} [CommSemiring R]

/-- The nonempty generating series `F = sum_(N >= 1) B_N z^N`. -/
def nonemptySeries : PowerSeries R[X] := PowerSeries.mk fun
  | 0 => 0
  | n + 1 => bigDescentPoly (n + 1)

@[simp]
theorem coeff_nonemptySeries_zero : PowerSeries.coeff 0 (nonemptySeries (R := R)) = 0 := by
  simp [nonemptySeries]

@[simp]
theorem coeff_nonemptySeries_succ (n : ℕ) :
    PowerSeries.coeff (n + 1) (nonemptySeries (R := R)) = bigDescentPoly (n + 1) := by
  simp [nonemptySeries]

private def geometricSeries : PowerSeries R[X] := PowerSeries.mk 1

private def positiveLinearSeries : PowerSeries R[X] :=
  1 + PowerSeries.C X * PowerSeries.X * geometricSeries

private lemma coeff_nonemptySeries_mul_geometric (n : ℕ) :
    PowerSeries.coeff n (nonemptySeries (R := R) * geometricSeries) =
      ∑ i ∈ Finset.range n, bigDescentPoly (i + 1) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ']
  simp only [coeff_nonemptySeries_zero, zero_mul]
  rw [add_zero]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp [geometricSeries]

private lemma coeff_nonemptySeries_sq_succ (n : ℕ) :
    PowerSeries.coeff (n + 1) (nonemptySeries (R := R) ^ 2) =
      ∑ i ∈ Finset.range n,
        bigDescentPoly (i + 1) * bigDescentPoly (n - i) := by
  rw [sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [coeff_nonemptySeries_zero, zero_mul, coeff_nonemptySeries_succ, Nat.sub_self,
    mul_zero, add_zero]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  rw [show n + 1 - (i + 1) = (n - i - 1) + 1 by lia, coeff_nonemptySeries_succ]
  congr 2
  lia

private lemma coeff_nonemptySeries_sq_mul_geometric (n : ℕ) :
    PowerSeries.coeff n (nonemptySeries (R := R) ^ 2 * geometricSeries) =
      ∑ k ∈ Finset.range n, ∑ i ∈ Finset.range k,
        bigDescentPoly (i + 1) * bigDescentPoly (k - i) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ']
  have hzero : PowerSeries.coeff 0 (nonemptySeries (R := R) ^ 2) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
    have hF0 : PowerSeries.constantCoeff (nonemptySeries (R := R)) = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_nonemptySeries_zero]
    simp [hF0]
  simp only [geometricSeries, PowerSeries.coeff_mk, Pi.one_apply, mul_one, hzero]
  rw [add_zero]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [coeff_nonemptySeries_sq_succ]

/-- The positive generating-function equation behind the defining recurrence. -/
private theorem nonemptySeries_positive :
    nonemptySeries (R := R) =
      PowerSeries.X * geometricSeries +
      PowerSeries.X * positiveLinearSeries * nonemptySeries +
      PowerSeries.C X * PowerSeries.X * positiveLinearSeries * nonemptySeries ^ 2 := by
  let F := nonemptySeries (R := R)
  let z : PowerSeries R[X] := PowerSeries.X
  let t : PowerSeries R[X] := PowerSeries.C X
  have hexpand :
      z * geometricSeries + z * positiveLinearSeries * F +
          t * z * positiveLinearSeries * F ^ 2 =
        z * geometricSeries + z * F + t * z ^ 2 * (F * geometricSeries) +
          t * z * F ^ 2 + PowerSeries.C (X ^ 2) * z ^ 2 * (F ^ 2 * geometricSeries) := by
    simp only [positiveLinearSeries, F, z, t]
    rw [map_pow]
    ring
  rw [hexpand]
  refine PowerSeries.ext fun N ↦ ?_
  match N with
  | 0 => simp [F, z, t, geometricSeries, mul_assoc, nonemptySeries]
  | 1 =>
    have hF0 : PowerSeries.constantCoeff (nonemptySeries (R := R)) = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_nonemptySeries_zero]
    rw [map_add, map_add, map_add, map_add, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_succ_X_mul, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow_mul', mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow_mul']
    simp [F, geometricSeries, sq, hF0]
  | n + 2 =>
    rw [map_add, map_add, map_add, map_add, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_succ_X_mul, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow_mul', mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow_mul']
    simp only [F, show 2 ≤ n + 2 by lia, ↓reduceIte, Nat.add_sub_cancel,
      coeff_nonemptySeries_succ, coeff_nonemptySeries_mul_geometric,
      coeff_nonemptySeries_sq_succ, coeff_nonemptySeries_sq_mul_geometric]
    simp only [geometricSeries, PowerSeries.coeff_mk, Pi.one_apply]
    rw [bigDescentPoly_add_two]

end Semiring

section Ring

variable {R : Type*} [CommRing R]

/-- The linear coefficient `A = 1 - 2z + (1-t)z^2` in the quadratic equation. -/
def quadraticLinearSeries : PowerSeries R[X] :=
  1 - 2 * PowerSeries.X + PowerSeries.C (1 - X) * PowerSeries.X ^ 2

/-- The quadratic coefficient `v = tz(1-(1-t)z)`. -/
def quadraticFactor : PowerSeries R[X] :=
  PowerSeries.C X * PowerSeries.X *
    (1 - PowerSeries.C (1 - X) * PowerSeries.X)

/-- The quadratic generating-function identity. -/
theorem nonemptySeries_quadratic :
    quadraticLinearSeries * nonemptySeries (R := R) =
      PowerSeries.X + quadraticFactor * nonemptySeries ^ 2 := by
  let F := nonemptySeries (R := R)
  let U := geometricSeries (R := R)
  let L := positiveLinearSeries (R := R)
  let z : PowerSeries R[X] := PowerSeries.X
  let t : PowerSeries R[X] := PowerSeries.C X
  let s : PowerSeries R[X] := PowerSeries.C (1 - X)
  have hU : U * (1 - z) = 1 := PowerSeries.mk_one_mul_one_sub_eq_one R[X]
  have hts : PowerSeries.C X + s = 1 := by
    dsimp only [s]
    rw [← map_add]
    rw [show X + (1 - X) = (1 : R[X]) by ring, map_one]
  have hL : (1 - z) * L = 1 - s * z := by
    dsimp only [L, positiveLinearSeries, t, s]
    linear_combination (PowerSeries.C X * z) * hU + z * hts
  have hP := nonemptySeries_positive (R := R)
  change F = z * U + z * L * F + t * z * L * F ^ 2 at hP
  change (1 - 2 * z + s * z ^ 2) * F = z + t * z * (1 - s * z) * F ^ 2
  linear_combination (1 - z) * hP + z * hU + z * F * hL + t * z * F ^ 2 * hL

private lemma fixed_point_of_quadratic {G : PowerSeries R[X]}
    (hG : quadraticLinearSeries * G = PowerSeries.X + quadraticFactor * G ^ 2) :
    G = PowerSeries.X + PowerSeries.C 2 * PowerSeries.X * G -
      PowerSeries.C (1 - X) * PowerSeries.X ^ 2 * G +
      PowerSeries.C X * PowerSeries.X * G ^ 2 -
      PowerSeries.C (X * (1 - X)) * PowerSeries.X ^ 2 * G ^ 2 := by
  simp only [quadraticLinearSeries, quadraticFactor] at hG
  simp only [map_ofNat, map_mul]
  linear_combination hG

/-- The quadratic equation has a unique solution; its constant coefficient follows from it. -/
theorem eq_nonemptySeries_of_quadratic {G : PowerSeries R[X]}
    (hG : quadraticLinearSeries * G = PowerSeries.X + quadraticFactor * G ^ 2) :
    G = nonemptySeries := by
  let F := nonemptySeries (R := R)
  have hGF := fixed_point_of_quadratic hG
  have hFF := fixed_point_of_quadratic (nonemptySeries_quadratic (R := R))
  change G = F
  apply PowerSeries.ext
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 =>
      have h := congrArg (PowerSeries.coeff 0) hGF
      simpa [F] using h
    | n + 1 =>
      have hsq : PowerSeries.coeff n (G ^ 2) = PowerSeries.coeff n (F ^ 2) := by
        simp only [sq, PowerSeries.coeff_mul]
        refine Finset.sum_congr rfl fun ij hij ↦ ?_
        have hij' := Finset.mem_antidiagonal.mp hij
        rw [ih ij.1 (by lia), ih ij.2 (by lia)]
      have hsq' : PowerSeries.coeff (n - 1) (G ^ 2) =
          PowerSeries.coeff (n - 1) (F ^ 2) := by
        simp only [sq, PowerSeries.coeff_mul]
        refine Finset.sum_congr rfl fun ij hij ↦ ?_
        have hij' := Finset.mem_antidiagonal.mp hij
        rw [ih ij.1 (by lia), ih ij.2 (by lia)]
      have h1 := congrArg (PowerSeries.coeff (n + 1)) hGF
      have h2 := congrArg (PowerSeries.coeff (n + 1)) hFF
      simp only [map_add, map_sub, mul_assoc, PowerSeries.coeff_X,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_X_pow_mul'] at h1 h2
      rw [← map_sub] at h1 h2
      simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul'] at h1 h2
      by_cases hn : 1 ≤ n
      · simp only [show (2 ≤ n + 1) ↔ (1 ≤ n) by lia, hn, ↓reduceIte] at h1 h2
        rw [show n + 1 - 2 = n - 1 by lia] at h1 h2
        rw [hsq, hsq', ih n (by lia), ih (n - 1) (by lia)] at h1
        exact h1.trans h2.symm
      · simp only [show (2 ≤ n + 1) ↔ (1 ≤ n) by lia, hn, ↓reduceIte] at h1 h2
        rw [hsq, ih n (by lia)] at h1
        exact h1.trans h2.symm

end Ring

section Sqrt

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The quartic discriminant
`D = 1 - 4z + 6(1-t)z^2 - 4(1-t)^2z^3 + (1-t)^2z^4`. -/
def discriminantSeries : PowerSeries R[X] :=
  1 - 4 * PowerSeries.X + PowerSeries.C (6 * (1 - X)) * PowerSeries.X ^ 2 -
    PowerSeries.C (4 * (1 - X) ^ 2) * PowerSeries.X ^ 3 +
    PowerSeries.C ((1 - X) ^ 2) * PowerSeries.X ^ 4

omit [Algebra ℚ R] in
private theorem discriminantSeries_eq :
    discriminantSeries (R := R) =
      quadraticLinearSeries ^ 2 - 4 * quadraticFactor * PowerSeries.X := by
  simp only [discriminantSeries, quadraticLinearSeries, quadraticFactor, map_mul, map_pow,
    map_sub, map_one, map_ofNat]
  ring

/-- The normalized square root selected by its constant coefficient. -/
theorem sqrt_discriminantSeries :
    PowerSeries.sqrt (discriminantSeries (R := R)) =
      quadraticLinearSeries - 2 * quadraticFactor * nonemptySeries := by
  symm
  refine PowerSeries.eq_sqrt_of_sq_eq (by simp [discriminantSeries])
    (by simp [quadraticLinearSeries, quadraticFactor]) ?_
  have hQ := nonemptySeries_quadratic (R := R)
  rw [discriminantSeries_eq]
  linear_combination -4 * quadraticFactor * hQ

/-- The square-root form `(A + sqrt D)F = 2z`. -/
theorem add_sqrt_discriminantSeries_mul_nonemptySeries :
    (quadraticLinearSeries + PowerSeries.sqrt discriminantSeries) *
        nonemptySeries (R := R) = 2 * PowerSeries.X := by
  rw [sqrt_discriminantSeries]
  have hQ := nonemptySeries_quadratic (R := R)
  linear_combination 2 * hQ

end Sqrt

end RealRooted.BigDescents132
