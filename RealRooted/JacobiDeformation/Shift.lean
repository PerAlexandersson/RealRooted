import RealRooted.JacobiDeformation.Basic
import RealRooted.EulerOperator
import RealRooted.EulerOperator.Polar.RealParameter
import RealRooted.EulerOperator.Polar.Pencil
import RealRooted.SimpleRoots

/-!
# The unit parameter shift of the Jacobi deformation

With `b = m + c + d - 1 + δ`, the Jacobi deformation satisfies the exact
operator identity

`b J_{m,δ+1} = (b + m) J_{m,δ} - X J_{m,δ}'`

(`polynomial_shift_cleared`, and `polynomial_shift` after division by
`b ≠ 0`).  Since `b + m` exceeds the degree `m`, the real polar Euler
operator of `RealRooted.EulerOperator.Polar.RealParameter` preserves PF
polynomials, so every integral increment of `δ` preserves the PF property,
splitness, and strictly negative roots.  For ranks at least two, a simple PF
base also gives strict interlacing and simple roots after each shift.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-! ## The shift identity -/

theorem summand_shift (m i j : ℕ) (δ c d U V : ℝ) :
    ((m : ℝ) + c + d - 1 + δ) * summand m (δ + 1) c d U V i j =
      ((m : ℝ) + c + d - 1 + δ + (i + j : ℕ)) *
        summand m δ c d U V i j := by
  let b : ℝ := (m : ℝ) + c + d - 1 + δ
  let K : ℝ :=
    (m.factorial : ℝ) /
        (((m - i - j).factorial : ℝ) * i.factorial * j.factorial) /
      (risingFactorial c i * risingFactorial d j) * U ^ i * V ^ j
  have hform (ε : ℝ) : summand m ε c d U V i j =
      K * risingFactorial ((m : ℝ) + c + d - 1 + ε) (i + j) := by
    unfold summand
    dsimp [K]
    ring
  rw [hform, hform]
  have hshift := mul_risingFactorial_add_one b (i + j)
  dsimp [b] at hshift ⊢
  rw [show (m : ℝ) + c + d - 1 + (δ + 1) =
      ((m : ℝ) + c + d - 1 + δ) + 1 by ring]
  linear_combination K * hshift

theorem coeff_polynomial_shift (m k : ℕ) (δ c d U V : ℝ) :
    ((m : ℝ) + c + d - 1 + δ) *
        (polynomial m (δ + 1) c d U V).coeff k =
      ((m : ℝ) + c + d - 1 + δ + (m - k : ℕ)) *
        (polynomial m δ c d U V).coeff k := by
  by_cases hk : k ≤ m
  · rw [coeff_polynomial, coeff_polynomial, ite_eq_left hk, ite_eq_left hk,
      Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    have hijsum : ij.1 + ij.2 = m - k :=
      HasAntidiagonal.mem_antidiagonal.mp hij
    simpa [hijsum] using summand_shift m ij.1 ij.2 δ c d U V
  · rw [coeff_polynomial, coeff_polynomial, ite_eq_right hk, ite_eq_right hk]
    ring

/-- The unit shift identity without division by its scalar denominator. -/
theorem polynomial_shift_cleared (m : ℕ) (δ c d U V : ℝ) :
    C ((m : ℝ) + c + d - 1 + δ) * polynomial m (δ + 1) c d U V =
      C ((m : ℝ) + c + d - 1 + δ + m) * polynomial m δ c d U V -
        X * (polynomial m δ c d U V).derivative := by
  rw [show X * (polynomial m δ c d U V).derivative =
      theta (polynomial m δ c d U V) by rfl]
  ext k
  rw [coeff_C_mul, coeff_sub, coeff_C_mul, coeff_theta]
  have hcoeff := coeff_polynomial_shift m k δ c d U V
  by_cases hk : k ≤ m
  · have hcast : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by
      rw [Nat.cast_sub hk]
    rw [hcast] at hcoeff
    linarith
  · have hzero : (polynomial m δ c d U V).coeff k = 0 := by
      rw [coeff_polynomial, ite_eq_right hk]
    have hzero' : (polynomial m (δ + 1) c d U V).coeff k = 0 := by
      rw [coeff_polynomial, ite_eq_right hk]
    rw [hzero, hzero']
    ring

/-- The unit shift identity in quotient form. -/
theorem polynomial_shift (m : ℕ) (δ c d U V : ℝ)
    (hb : (m : ℝ) + c + d - 1 + δ ≠ 0) :
    polynomial m (δ + 1) c d U V =
      C (((m : ℝ) + c + d - 1 + δ)⁻¹) *
        (C ((m : ℝ) + c + d - 1 + δ + m) *
          polynomial m δ c d U V -
            X * (polynomial m δ c d U V).derivative) := by
  rw [← polynomial_shift_cleared]
  symm
  calc
    C (((m : ℝ) + c + d - 1 + δ)⁻¹) *
          (C ((m : ℝ) + c + d - 1 + δ) * polynomial m (δ + 1) c d U V) =
        (C (((m : ℝ) + c + d - 1 + δ)⁻¹) *
          C ((m : ℝ) + c + d - 1 + δ)) * polynomial m (δ + 1) c d U V := by
      rw [mul_assoc]
    _ = C (((m : ℝ) + c + d - 1 + δ)⁻¹ *
          ((m : ℝ) + c + d - 1 + δ)) * polynomial m (δ + 1) c d U V := by
      rw [C_mul]
    _ = polynomial m (δ + 1) c d U V := by
      rw [inv_mul_cancel₀ hb]
      simp

/-! ## Preservation along integral shifts -/

/-- The unit shift identity transports the PF property across one parameter
shift whenever its scalar denominator is positive. -/
theorem isPFPolynomial_polynomial_shift {m : ℕ} {δ c d U V : ℝ}
    (hb : 0 < (m : ℝ) + c + d - 1 + δ)
    (hp : IsPFPolynomial (polynomial m δ c d U V)) :
    IsPFPolynomial (polynomial m (δ + 1) c d U V) := by
  rw [polynomial_shift m δ c d U V hb.ne']
  have ha : (m : ℝ) < (m : ℝ) + c + d - 1 + δ + m := by
    linarith
  have hpolar : IsPFPolynomial
      (C ((m : ℝ) + c + d - 1 + δ + m) * polynomial m δ c d U V -
        theta (polynomial m δ c d U V)) :=
    isPFPolynomial_C_mul_sub_theta ha hp
      (natDegree_polynomial_le m δ c d U V)
  simpa [theta] using hpolar.const_mul (inv_pos.mpr hb)

/-- Iterating the unit shift transports a PF base through every
nonnegative integral parameter increment. -/
theorem isPFPolynomial_polynomial_nat_shift {m : ℕ} {δ c d U V : ℝ}
    (hb : 0 < (m : ℝ) + c + d - 1 + δ)
    (hp : IsPFPolynomial (polynomial m δ c d U V)) (n : ℕ) :
    IsPFPolynomial (polynomial m (δ + n) c d U V) := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
      have hb' : 0 < (m : ℝ) + c + d - 1 + (δ + n) := by
        have hn : (0 : ℝ) ≤ n := by positivity
        linarith
      have hstep := isPFPolynomial_polynomial_shift hb' ih
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hstep

/-- A positive-parameter PF base and the unit shift give split polynomials with
strictly negative roots after every integral parameter shift. -/
theorem polynomial_nat_shift_splits_roots_neg {m : ℕ} {δ c d U V : ℝ}
    (hm : 1 ≤ m) (hδ : 0 ≤ δ) (hc : 0 < c) (hd : 0 < d)
    (hU : 0 < U) (hV : 0 < V)
    (hp : IsPFPolynomial (polynomial m δ c d U V)) (n : ℕ) :
    (polynomial m (δ + n) c d U V).Splits ∧
      ∀ r ∈ (polynomial m (δ + n) c d U V).roots, r < 0 := by
  have hb : 0 < (m : ℝ) + c + d - 1 + δ :=
    base_pos_of_one_le hm hδ hc hd
  have hpf := isPFPolynomial_polynomial_nat_shift hb hp n
  have hne : polynomial m (δ + n) c d U V ≠ 0 :=
    (monic_polynomial m (δ + n) c d U V).ne_zero
  refine ⟨(hpf.ne_zero_and_splits hne).2, ?_⟩
  intro r hr
  have hrle : r ≤ 0 := hpf.roots_nonpos r hr
  have hδn : 0 ≤ δ + (n : ℝ) := by positivity
  have hconst : 0 < (polynomial m (δ + n) c d U V).coeff 0 :=
    coeff_zero_pos_of_pos hm hδn hc hd hU hV
  have hrne : r ≠ 0 := by
    intro hr0
    subst r
    have hroot : (polynomial m (δ + n) c d U V).IsRoot 0 :=
      (mem_roots hne).mp hr
    have hzero : (polynomial m (δ + n) c d U V).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simpa [Polynomial.IsRoot.def] using hroot
    linarith
  exact lt_of_le_of_ne hrle hrne

/-- For ranks at least two, one Jacobi parameter shift strictly interlaces its
simple PF input and again has simple roots. -/
theorem strictInterl_polynomial_shift {m : ℕ} {δ c d U V : ℝ}
    (hm : 2 ≤ m) (hδ : 0 ≤ δ) (hc : 0 < c) (hd : 0 < d)
    (hU : 0 < U) (hV : 0 < V)
    (hp : IsPFPolynomial (polynomial m δ c d U V))
    (hsimple : HasSimpleRoots (polynomial m δ c d U V)) :
    StrictInterl (polynomial m (δ + 1) c d U V)
        (polynomial m δ c d U V) ∧
      HasSimpleRoots (polynomial m (δ + 1) c d U V) := by
  let p : ℝ[X] := polynomial m δ c d U V
  let b : ℝ := (m : ℝ) + c + d - 1 + δ
  have hm1 : 1 ≤ m := by lia
  have hb : 0 < b := by
    dsimp [b]
    exact base_pos_of_one_le hm1 hδ hc hd
  have hpdeg : p.natDegree = m := natDegree_polynomial m δ c d U V
  have hp0 : p ≠ 0 := (monic_polynomial m δ c d U V).ne_zero
  have hconst : 0 < p.coeff 0 :=
    coeff_zero_pos_of_pos hm1 hδ hc hd hU hV
  have hreflect : 2 ≤ (reciprocalShift m p).natDegree := by
    have htop : (reciprocalShift m p).coeff m ≠ 0 := by
      simp [hconst.ne']
    exact hm.trans (le_natDegree_of_ne_zero htop)
  have hpolar : StrictInterl (polarTheta m p) p :=
    strictInterl_polarTheta_self hp hpdeg.le hreflect
  have hpolarPos : HasPosLeadingCoeff (polarTheta m p) :=
    (polarTheta_preserves_pf hp hpdeg.le).hasNonnegCoeffs.pos_leadingCoeff
      hpolar.1.1
  have hpPos : HasPosLeadingCoeff p :=
    hp.hasNonnegCoeffs.pos_leadingCoeff hp0
  have hcombo : StrictInterl (polarTheta m p + C b * p) p := by
    simpa using hpolar.nonneg_combo_right hpolarPos hpPos
      (a := 1) (b := b) zero_le_one hb.le (Or.inl zero_lt_one)
  have hop : C (b + m) * p - theta p = polarTheta m p + C b * p := by
    simp [polarTheta]
    ring
  have hstrict : StrictInterl (polynomial m (δ + 1) c d U V) p := by
    rw [polynomial_shift m δ c d U V (by simpa [b] using hb.ne')]
    change StrictInterl (C b⁻¹ * (C (b + m) * p - theta p)) p
    rw [hop]
    exact StrictInterl.C_mul_left hcombo (inv_ne_zero hb.ne')
  have hrootsneg : ∀ r ∈ p.roots, r < 0 := by
    simpa [p] using
      (polynomial_nat_shift_splits_roots_neg hm1 hδ hc hd hU hV hp 0).2
  have hno : ∀ r : ℝ,
      ¬ ((polynomial m (δ + 1) c d U V).IsRoot r ∧ p.IsRoot r) := by
    intro r hr
    have hp_eval : p.eval r = 0 := hr.2
    have hder_ne : p.derivative.eval r ≠ 0 := hsimple.eval_derivative_ne_zero hr.2
    have hr_mem : r ∈ p.roots := (mem_roots hp0).mpr hr.2
    have hr_ne : r ≠ 0 := ne_of_lt (hrootsneg r hr_mem)
    have heval : (polynomial m (δ + 1) c d U V).eval r =
        -b⁻¹ * r * p.derivative.eval r := by
      rw [polynomial_shift m δ c d U V (by simpa [b] using hb.ne')]
      simp only [eval_mul, eval_C, eval_sub, eval_X]
      change b⁻¹ * ((b + m) * p.eval r - r * p.derivative.eval r) = _
      rw [hp_eval]
      ring
    have hne : -b⁻¹ * r * p.derivative.eval r ≠ 0 :=
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hb.ne')) hr_ne)
        hder_ne
    apply hne
    rw [← heval]
    exact hr.1
  exact ⟨hstrict, (hstrict.hasSimpleRoots_of_no_common_root hno).1⟩

/-- Simple roots persist through every integral Jacobi parameter shift once
the PF base is simple. -/
theorem polynomial_nat_shift_hasSimpleRoots {m : ℕ} {δ c d U V : ℝ}
    (hm : 2 ≤ m) (hδ : 0 ≤ δ) (hc : 0 < c) (hd : 0 < d)
    (hU : 0 < U) (hV : 0 < V)
    (hp : IsPFPolynomial (polynomial m δ c d U V))
    (hsimple : HasSimpleRoots (polynomial m δ c d U V)) (n : ℕ) :
    HasSimpleRoots (polynomial m (δ + n) c d U V) := by
  induction n with
  | zero => simpa using hsimple
  | succ n ih =>
      have hδn : 0 ≤ δ + (n : ℝ) := by positivity
      have hb : 0 < (m : ℝ) + c + d - 1 + δ :=
        base_pos_of_one_le (by lia) hδ hc hd
      have hpf := isPFPolynomial_polynomial_nat_shift hb hp n
      have hstep := strictInterl_polynomial_shift hm hδn hc hd hU hV hpf ih
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hstep.2

end RealRooted.JacobiDeformation
