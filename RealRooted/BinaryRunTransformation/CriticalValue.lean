import RealRooted.BinaryRunTransformation.Coefficients
import RealRooted.HermiteBiehler.StablePencil

/-!
# Critical values in the binary-run deformation

This file develops the signed parity lift `z^n p(-z⁻²)` and uses a stable
polynomial pencil to control the sign of a critical value during a pointing
deformation.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- Polynomial realization of `z^n p(-z⁻²)`. The degree hypotheses below
ensure that the finite sum contains every coefficient of `p`. -/
def signedParityLift (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    C ((-1) ^ k * p.coeff k) * X ^ (n - 2 * k)

/-- Under the natural degree bound, the defining sum may be extended through
all indices `0, ..., n`; every added coefficient vanishes. -/
theorem signedParityLift_eq_sum_range_succ
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n / 2) :
    signedParityLift n p =
      ∑ k ∈ Finset.range (n + 1),
        C ((-1) ^ k * p.coeff k) * X ^ (n - 2 * k) := by
  rw [signedParityLift]
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by lia)) ?_
  rintro k hk hksmall
  simp only [Finset.mem_range] at hk hksmall ⊢
  have hdegree : p.natDegree < k := by lia
  rw [coeff_eq_zero_of_natDegree_lt hdegree]
  simp

theorem coeff_signedParityLift (n : ℕ) (p : ℝ[X]) {k : ℕ}
    (hk : k ≤ n / 2) :
    (signedParityLift n p).coeff (n - 2 * k) =
      (-1) ^ k * p.coeff k := by
  rw [signedParityLift, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single k]
  · rw [coeff_C_mul, coeff_X_pow, ite_eq_left rfl, mul_one]
  · intro j hj hjk
    rw [coeff_C_mul, coeff_X_pow, ite_eq_right, mul_zero]
    simp only [Finset.mem_range] at hj
    lia
  · intro hknot
    exact absurd (Finset.mem_range.mpr (by lia)) hknot

/-- On its natural degree range, the signed parity lift is injective at zero.
-/
theorem signedParityLift_eq_zero_iff
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n / 2) :
    signedParityLift n p = 0 ↔ p = 0 := by
  constructor
  · intro hzero
    apply Polynomial.ext
    intro k
    by_cases hk : k ≤ n / 2
    · have hcoeff := congrArg (fun q : ℝ[X] => q.coeff (n - 2 * k)) hzero
      rw [coeff_signedParityLift n p hk, coeff_zero] at hcoeff
      exact (mul_eq_zero.mp hcoeff).resolve_left (pow_ne_zero _ (by norm_num))
    · rw [coeff_eq_zero_of_natDegree_lt (by lia), coeff_zero]
  · rintro rfl
    simp [signedParityLift]

theorem natDegree_signedParityLift_le (n : ℕ) (p : ℝ[X]) :
    (signedParityLift n p).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
  lia

theorem aeval_signedParityLift {n : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ n / 2) {z : ℂ} (hz : z ≠ 0) :
    (Polynomial.aeval z) (signedParityLift n p) =
      z ^ n * (Polynomial.aeval (-(z ^ 2)⁻¹)) p := by
  rw [signedParityLift, map_sum,
    Polynomial.aeval_eq_sum_range' (n := n / 2 + 1) (by lia),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  have hpow : z ^ n = z ^ (n - 2 * k) * z ^ (2 * k) := by
    rw [← pow_add]
    congr 1
    lia
  have hinv : ((z ^ 2)⁻¹) ^ k = (z ^ (2 * k))⁻¹ := by
    rw [inv_pow, ← pow_mul]
  have hneg : (-(z ^ 2)⁻¹) ^ k =
      (-1) ^ k * (z ^ (2 * k))⁻¹ := by
    rw [neg_pow, hinv]
  rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
    hneg, Complex.real_smul]
  push_cast
  rw [hpow]
  field_simp
  rfl

theorem eval_signedParityLift {n : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ n / 2) {r : ℝ} (hr : r ≠ 0) :
    (signedParityLift n p).eval r =
      r ^ n * p.eval (-(r ^ 2)⁻¹) := by
  change (Polynomial.aeval r) (signedParityLift n p) =
    r ^ n * (Polynomial.aeval (-(r ^ 2)⁻¹)) p
  rw [signedParityLift, map_sum,
    Polynomial.aeval_eq_sum_range' (n := n / 2 + 1) (by lia),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  have hpow : r ^ n = r ^ (n - 2 * k) * r ^ (2 * k) := by
    rw [← pow_add]
    congr 1
    lia
  have hinv : ((r ^ 2)⁻¹) ^ k = (r ^ (2 * k))⁻¹ := by
    rw [inv_pow, ← pow_mul]
  have hneg : (-(r ^ 2)⁻¹) ^ k =
      (-1) ^ k * (r ^ (2 * k))⁻¹ := by
    rw [neg_pow, hinv]
  rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, hneg]
  rw [hpow]
  simp only [Algebra.smul_def, map_mul, map_pow, map_neg, map_one]
  field_simp

theorem coeff_X_mul_derivative (p : ℝ[X]) (k : ℕ) :
    (X * p.derivative).coeff k = (k : ℝ) * p.coeff k := by
  rcases k with _ | k
  · simp
  · rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- Euler identity for the signed parity lift. At a nonzero root of `p`, it
turns the derivative of the lift into the lift of `X p'`. -/
theorem X_mul_derivative_signedParityLift (n : ℕ) (p : ℝ[X]) :
    X * (signedParityLift n p).derivative =
      C (n : ℝ) * signedParityLift n p -
        C 2 * signedParityLift n (X * p.derivative) := by
  simp only [signedParityLift, derivative_sum, derivative_mul,
    derivative_C, zero_mul, zero_add, derivative_X_pow, Finset.mul_sum,
    coeff_X_mul_derivative]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  have hkn : 2 * k ≤ n := by lia
  let c : ℝ := (-1) ^ k * p.coeff k
  let c' : ℝ := (-1) ^ k * ((k : ℝ) * p.coeff k)
  have hscalar : ((n - 2 * k : ℕ) : ℝ) * c =
      (n : ℝ) * c - 2 * c' := by
    rw [Nat.cast_sub hkn]
    push_cast
    dsimp [c, c']
    ring
  have hderiv :
      X * (C c * (C ((n - 2 * k : ℕ) : ℝ) *
        X ^ (n - 2 * k - 1))) =
        C (((n - 2 * k : ℕ) : ℝ) * c) *
          X ^ (n - 2 * k) := by
    by_cases he : n - 2 * k = 0
    · simp [he]
    · have hpow : (X : ℝ[X]) ^ (n - 2 * k) =
          X ^ (n - 2 * k - 1) * X := by
        rw [← pow_succ]
        congr 1
        lia
      rw [hpow]
      calc
        X * (C c * (C ((n - 2 * k : ℕ) : ℝ) *
            X ^ (n - 2 * k - 1))) =
            (C c * C ((n - 2 * k : ℕ) : ℝ)) *
              (X ^ (n - 2 * k - 1) * X) := by ring_nf
        _ = C (c * ((n - 2 * k : ℕ) : ℝ)) *
              (X ^ (n - 2 * k - 1) * X) := by rw [← C_mul]
        _ = C (((n - 2 * k : ℕ) : ℝ) * c) *
              (X ^ (n - 2 * k - 1) * X) := by ring_nf
  change X * (C c * (C ((n - 2 * k : ℕ) : ℝ) *
      X ^ (n - 2 * k - 1))) =
    C (n : ℝ) * (C c * X ^ (n - 2 * k)) -
      C 2 * (C c' * X ^ (n - 2 * k))
  rw [hderiv, hscalar, map_sub, map_mul, map_mul]
  have hc' : C (2 * c') = (C 2 : ℝ[X]) * C c' := by
    rw [← C_mul]
  rw [hc']
  ring

/-- The abstract critical-value inequality behind the pointing deformation.
The degree hypotheses identify the signed parity lifts with
`r^n E(-r⁻²)` and `r^(n-1) q'(-r⁻²)`. -/
theorem criticalValue_sign_of_stablePencil {n : ℕ} (hn : 4 ≤ n)
    {E q : ℝ[X]} {r : ℝ} (hr : 0 < r)
    (hE : E.natDegree ≤ n / 2)
    (hq' : q.derivative.natDegree ≤ (n - 1) / 2)
    (hXq'' : (X * q.derivative.derivative).natDegree ≤ (n - 1) / 2)
    (hcritical : q.derivative.eval (-(r ^ 2)⁻¹) = 0)
    (hstable : IsUpperHalfPlaneStablePencil
      (-(signedParityLift (n - 1) q.derivative))
      (signedParityLift n E)) :
    E.eval (-(r ^ 2)⁻¹) *
      q.derivative.derivative.eval (-(r ^ 2)⁻¹) ≤ 0 := by
  let η : ℝ := -(r ^ 2)⁻¹
  let a := signedParityLift n E
  let b := signedParityLift (n - 1) q.derivative
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hb0 : b.eval r = 0 := by
    rw [show b = signedParityLift (n - 1) q.derivative by rfl,
      eval_signedParityLift hq' hr0, show -(r ^ 2)⁻¹ = η by rfl,
      hcritical, mul_zero]
  have hsign : b.derivative.eval r * a.eval r ≤ 0 :=
    hstable.derivative_mul_nonpos_at_root hb0
  have ha : a.eval r = r ^ n * E.eval η :=
    eval_signedParityLift hE hr0
  have hlift :
      (signedParityLift (n - 1) (X * q.derivative.derivative)).eval r =
        r ^ (n - 1) * (η * q.derivative.derivative.eval η) := by
    rw [eval_signedParityLift hXq'' hr0]
    simp only [eval_mul, eval_X]
    rfl
  have heuler := congrArg (Polynomial.eval r)
    (X_mul_derivative_signedParityLift (n - 1) q.derivative)
  have hrb :
      r * b.derivative.eval r =
        2 * r ^ (n - 3) * q.derivative.derivative.eval η := by
    simp only [eval_mul, eval_X, eval_C, eval_sub] at heuler
    rw [show signedParityLift (n - 1) q.derivative = b by rfl,
      hb0, mul_zero, zero_sub, hlift] at heuler
    have hpow : r ^ (n - 1) = r ^ (n - 3) * r ^ 2 := by
      rw [← pow_add]
      congr 1
      lia
    rw [hpow] at heuler
    dsimp [η] at heuler
    field_simp at heuler
    simpa [η] using heuler
  have hrsign : r * (b.derivative.eval r * a.eval r) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hr.le hsign
  have hfactor :
      r * (b.derivative.eval r * a.eval r) =
        (2 * r ^ (2 * n - 3)) *
          (E.eval η * q.derivative.derivative.eval η) := by
    rw [← mul_assoc, hrb, ha]
    have hexp : (n - 3) + n = 2 * n - 3 := by lia
    calc
      2 * r ^ (n - 3) * q.derivative.derivative.eval η *
          (r ^ n * E.eval η) =
          (2 * (r ^ (n - 3) * r ^ n)) *
            (E.eval η * q.derivative.derivative.eval η) := by ring
      _ = (2 * r ^ (2 * n - 3)) *
            (E.eval η * q.derivative.derivative.eval η) := by
        rw [← pow_add, hexp]
  rw [hfactor] at hrsign
  have hpos : 0 < 2 * r ^ (2 * n - 3) := by positivity
  exact nonpos_of_mul_nonpos_right hrsign hpos

end

end RealRooted
