module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
public import RealRooted.SimpleRoots
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.Hermite.ExponentialJensenFactor
import RealRooted.Hermite.PoulainExponential

/-!
# Exact multiplicity of the exceptional Jensen zero

The explicit exponential factor has exactly the predicted multiplicity:
the residual sum does not vanish at `-1/a`. For a real-rooted polynomial
symbol nonzero at zero, this gives the exact simple-root degree range,
including the endpoint one degree beyond the symbol degree.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- At the exceptional point, only the leading-coefficient summand survives. -/
private theorem eval_exponential_jensen_residual (q : ℝ[X]) {a : ℝ} (ha : a ≠ 0) (d : ℕ) :
    (∑ k ∈ Finset.range (q.natDegree + 1),
      C (q.coeff k * (d.descFactorial k : ℝ)) *
        (X ^ k * (1 + C a * X) ^ (q.natDegree - k))).eval (-a⁻¹) =
      q.leadingCoeff * (d.descFactorial q.natDegree : ℝ) * (-a⁻¹) ^ q.natDegree := by
  have hz : 1 + a * (-a⁻¹) = 0 := by simp [ha]
  rw [eval_finsetSum, Finset.sum_eq_single q.natDegree]
  · simp only [eval_mul, eval_C, eval_pow, eval_X,
      Nat.sub_self, pow_zero, mul_one, coeff_natDegree]
  · intro k hk hkm
    have hlt : k < q.natDegree := by
      have := Finset.mem_range.mp hk
      lia
    have hn : q.natDegree - k ≠ 0 := by lia
    simp only [eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one,
      hz, zero_pow hn, mul_zero]
  · simp

/-- The exceptional Jensen zero has exactly multiplicity `d - deg q`.
Neither real-rootedness nor a nonzero constant coefficient is required here. -/
theorem rootMultiplicity_jensen_polynomial_exp {q : ℝ[X]} (hq0 : q ≠ 0)
    {a : ℝ} (ha : a ≠ 0) (d : ℕ) (hd : q.natDegree ≤ d) :
    (jensenPolynomial d (fun k =>
      (iteratedDeriv k
        (fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z)) 0).re)).rootMultiplicity
        (-a⁻¹) = d - q.natDegree := by
  let R : ℝ[X] := ∑ k ∈ Finset.range (q.natDegree + 1),
    C (q.coeff k * (d.descFactorial k : ℝ)) *
      (X ^ k * (1 + C a * X) ^ (q.natDegree - k))
  have hRval : R.eval (-a⁻¹) ≠ 0 := by
    rw [show R.eval (-a⁻¹) = _ from eval_exponential_jensen_residual q ha d]
    exact mul_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr hq0)
      (by exact_mod_cast (Nat.descFactorial_pos.mpr hd).ne'))
      (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero ha)))
  have hR : R ≠ 0 := by intro hz; exact hRval (by simp [hz])
  have hlinear : (1 + C a * X : ℝ[X]) = C a * (X - C (-a⁻¹)) := by
    rw [mul_sub, ← C_mul]
    simp [ha, add_comm]
  rw [jensen_polynomial_exp_factor q a d hd]
  change ((1 + C a * X) ^ (d - q.natDegree) * R).rootMultiplicity (-a⁻¹) = _
  rw [hlinear, mul_pow, ← C_pow, mul_assoc,
    rootMultiplicity_C_mul (pow_ne_zero _ ha), mul_comm _ R,
    rootMultiplicity_mul_X_sub_C_pow hR, rootMultiplicity_eq_zero hRval, zero_add]

/-- For a nonzero real exponential slope, the simple-root degree range is
exactly `d ≤ deg q + 1`, strengthening the range stated in Proposition 4.1(2). -/
theorem simple_jensen_polynomial_exp_iff_degree {q : ℝ[X]}
    (hq : q.Splits) (hq0 : q.coeff 0 ≠ 0) {a : ℝ} (ha : a ≠ 0) (d : ℕ) :
    IsSimpleRealRooted (jensenPolynomial d (fun k =>
      (iteratedDeriv k (fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z)) 0).re)) ↔
        d ≤ q.natDegree + 1 := by
  constructor
  · intro hs
    by_contra hnot
    have hd : q.natDegree ≤ d := by lia
    have hqne : q ≠ 0 := by intro hz; simp [hz] at hq0
    have hm := rootMultiplicity_jensen_polynomial_exp hqne ha d hd
    have hroot : (jensenPolynomial d (fun k =>
        (iteratedDeriv k (fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z)) 0).re)).IsRoot
          (-a⁻¹) := (rootMultiplicity_pos hs.1).mp (by rw [hm]; lia)
    have hsimp := hs.2.2 _ hroot
    lia
  · intro hd
    exact simple_jensen_polynomial_exp_of_degree hq hq0 a d (by lia)

end RealRooted
