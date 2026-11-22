module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.MultiplierSequence.Geometric
import RealRooted.MultiplierSequence.PolyaSchur.Limit

/-!
# Reciprocal Gamma sampled along positive real steps

For a nonnegative real step and a positive starting value, reciprocal Gamma
samples form a PF multiplier sequence. Euler's finite Gamma approximants
factor into positive affine multipliers and a geometric factor. Their
pointwise limit gives the result without an infinite-product sampling theorem.

This proves the multiplier statement behind Craven--Csordas (2006),
Example 2.7, and Baricz--Singh (2018), Theorem 1 for positive parameters.
-/

public section

open Filter Topology

namespace RealRooted

/-- Euler's reciprocal Gamma approximants separate into a geometric factor
and a finite product of affine factors. -/
private theorem inv_GammaSeq_eq (a b : ℝ) {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    (Real.GammaSeq (a * k + b) N)⁻¹ =
      (Real.exp (-(Real.log N) * b) / N.factorial) *
        (Real.exp (-(Real.log N) * a)) ^ k *
          ∏ j ∈ Finset.range (N + 1), (a * k + (b + j)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [Real.GammaSeq, inv_div, div_eq_mul_inv, mul_inv_rev,
    Real.rpow_def_of_pos hNpos, ← Real.exp_neg, ← Real.exp_nat_mul]
  rw [show -(Real.log N * (a * k + b)) =
    -(Real.log N) * b + k * (-(Real.log N) * a) by ring, Real.exp_add]
  simp only [add_assoc]
  ring

/-- Each nonzero-index reciprocal Gamma approximant is a PF multiplier. -/
private theorem isPFMultiplierSequence_inv_GammaSeq {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) {N : ℕ} (hN : N ≠ 0) :
    IsPFMultiplierSequence (fun k => (Real.GammaSeq (a * k + b) N)⁻¹) := by
  have hprod := IsPFMultiplierSequence.finsetProd (Finset.range (N + 1))
    (fun j k => a * k + (b + j))
    (fun j _ => isPFMultiplierSequence_mul_natCast_add ha (by positivity))
  have hgeom := (isPFMultiplierSequence_pow (Real.exp_pos (-(Real.log N) * a))).mul hprod
  have h := hgeom.const_mul (show 0 ≤ Real.exp (-(Real.log N) * b) / N.factorial by positivity)
  convert h using 1
  ext k
  rw [inv_GammaSeq_eq a b hN]
  ring

/-- Reciprocal Gamma at every nonnegative real step and positive starting
value forms a PF multiplier sequence. A zero step gives a constant sequence. -/
theorem isPFMultiplierSequence_inv_Gamma_mul_add {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) :
    IsPFMultiplierSequence (fun k => (Real.Gamma (a * k + b))⁻¹) := by
  apply isPFMultiplierSequence_of_tendsto
    (gamma := fun N k => (Real.GammaSeq (a * k + b) (N + 1))⁻¹)
    (fun N => isPFMultiplierSequence_inv_GammaSeq ha hb (Nat.succ_ne_zero N))
  intro k
  have hpos : 0 < a * (k : ℝ) + b := by positivity
  exact ((Real.GammaSeq_tendsto_Gamma (a * k + b)).inv₀
    (Real.Gamma_pos_of_pos hpos).ne').comp (tendsto_add_atTop_nat 1)

/-- The positive-step Wright exponential generating function is entire
positive Type-I Laguerre--Pólya, including the exponential at zero step. -/
theorem isLaguerrePolyaTypeI_inv_Gamma_mul_add {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) :
    IsLaguerrePolyaTypeI
      (complexExpGeneratingFunction (fun k => (Real.Gamma (a * k + b))⁻¹)) :=
  IsPFMultiplierSequence.isLaguerrePolyaTypeI_complexExpGeneratingFunction
    (isPFMultiplierSequence_inv_Gamma_mul_add ha hb)

end RealRooted
