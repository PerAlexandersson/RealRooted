import RealRooted.Hadamard.Grace
import RealRooted.EulerOperator.Polar.Pencil
import RealRooted.JacobiDeformation.ShiftRecurrence
import RealRooted.SimpleRoots

/-!
# Real polar-shift preservation

This module proves the real-parameter polar-derivative preservation needed to
iterate equation (25).  The proof uses the finite Pólya--Schur theorem with an
explicit Jensen-polynomial factorization, so repeated roots and every degree
boundary are included.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The globally nonnegative truncation of the real polar multiplier
`k ↦ a - k`. -/
def positivePolarMultiplier (a : ℝ) (k : ℕ) : ℝ :=
  max (a - k) 0

theorem positivePolarMultiplier_nonneg (a : ℝ) (k : ℕ) :
    0 ≤ positivePolarMultiplier a k := by
  simp [positivePolarMultiplier]

theorem jensenPolynomial_positivePolarMultiplier {n : ℕ} (hn : 1 ≤ n)
    {a : ℝ} (ha : (n : ℝ) < a) :
    jensenPolynomial n (positivePolarMultiplier a) =
      (X + 1) ^ (n - 1) * (C (a - n) * X + C a) := by
  have hsame :
      jensenPolynomial n (positivePolarMultiplier a) =
        jensenPolynomial n (fun k => a - (k : ℝ)) := by
    ext k
    rw [coeff_jensenPolynomial, coeff_jensenPolynomial]
    by_cases hk : k ≤ n
    · have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
      have hak : 0 ≤ a - (k : ℝ) := by linarith
      simp only [hk, ↓reduceIte]
      rw [positivePolarMultiplier, max_eq_left hak]
    · simp [hk]
  rw [hsame, jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
  have hdiag (p : ℝ[X]) :
      diagonalOperator (fun k => a - (k : ℝ)) p = C a * p - theta p := by
    ext k
    simp [coeff_theta]
    ring
  rw [hdiag]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.add_sub_cancel_left, theta, derivative_pow,
    derivative_add, derivative_X, derivative_one, add_zero, mul_one,
    Nat.cast_add, Nat.cast_one]
  simp only [map_add, map_sub, map_one, map_natCast]
  ring

/-- The real polar multiplier preserves the PF cone through every degree
strictly below `a`. -/
theorem positivePolarMultiplier_isFinitePFMultiplierSequence (n : ℕ)
    {a : ℝ} (ha : (n : ℝ) < a) :
    IsFinitePFMultiplierSequence n (positivePolarMultiplier a) := by
  have hnonneg : ∀ k, 0 ≤ positivePolarMultiplier a k :=
    positivePolarMultiplier_nonneg a
  cases n with
  | zero =>
      intro p hp hpdeg
      exact isFinitePFMultiplierSequence_natDegree_zero
        (gamma := positivePolarMultiplier a) hnonneg hp hpdeg
  | succ n =>
      have hcoef : 0 < a - ((n + 1 : ℕ) : ℝ) := sub_pos.mpr ha
      have hn0 : (0 : ℝ) ≤ (n + 1 : ℕ) := by positivity
      have ha0 : 0 ≤ a := by linarith
      have hlin :
          (C (a - ((n + 1 : ℕ) : ℝ)) * X + C a : ℝ[X]) =
            C (a - ((n + 1 : ℕ) : ℝ)) *
              (X + C (a / (a - ((n + 1 : ℕ) : ℝ)))) := by
        rw [mul_add, ← C_mul]
        congr 1
        field_simp [hcoef.ne']
      have hjensen :
          IsPFPolynomial
            (jensenPolynomial (n + 1) (positivePolarMultiplier a)) := by
        rw [jensenPolynomial_positivePolarMultiplier (by lia) ha, hlin]
        exact (isPFPolynomial_X_add_one.pow n).mul
          ((isPFPolynomial_X_add_C (div_nonneg ha0 hcoef.le)).const_mul hcoef)
      intro p hp hpdeg
      exact isFinitePFMultiplierSequence_of_finiteMultiplierSequence
        (n := n + 1) (gamma := positivePolarMultiplier a) hnonneg
        ((finitePolyaSchur_nonneg hnonneg).2 hjensen) hp hpdeg

/-- On a degree box below `a`, the positive polar multiplier realizes the
real polar derivative `a p - X p'`. -/
theorem diagonalOperator_positivePolarMultiplier_eq {n : ℕ} {a : ℝ}
    (ha : (n : ℝ) < a) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) :
    diagonalOperator (positivePolarMultiplier a) p = C a * p - theta p := by
  ext k
  rw [coeff_diagonalOperator, coeff_sub, coeff_C_mul, coeff_theta]
  by_cases hk : k ≤ n
  · have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    rw [positivePolarMultiplier, max_eq_left (by linarith)]
    ring
  · have hpcoeff : p.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg (lt_of_not_ge hk))
    rw [hpcoeff]
    ring

/-- A real polar derivative preserves the PF cone when its scalar parameter
strictly exceeds the polynomial's degree bound. -/
theorem isPFPolynomial_C_mul_sub_theta {n : ℕ} {a : ℝ}
    (ha : (n : ℝ) < a) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hpdeg : p.natDegree ≤ n) :
    IsPFPolynomial (C a * p - theta p) := by
  rw [← diagonalOperator_positivePolarMultiplier_eq ha hpdeg]
  exact positivePolarMultiplier_isFinitePFMultiplierSequence n ha hp hpdeg

namespace JacobiDeformation

/-- Equation (25) transports the PF property across one unit parameter shift
whenever its scalar denominator is positive. -/
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

/-- Iterating equation (25) transports a checked PF base through every
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

/-- A positive-parameter PF base and equation (25) give split polynomials with
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
    prec_polarTheta_self hp hpdeg.le hreflect
  have hpolarPos : HasPosLeadingCoeff (polarTheta m p) :=
    (polarTheta_preserves_pf hp hpdeg.le).hasNonnegCoeffs.pos_leadingCoeff
      hpolar.1.1
  have hpPos : HasPosLeadingCoeff p :=
    hp.hasNonnegCoeffs.pos_leadingCoeff hp0
  have hcombo : StrictInterl (polarTheta m p + C b * p) p := by
    simpa using prec_nonneg_combo_right hpolar hpolarPos hpPos
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
the checked PF base is simple. -/
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

end JacobiDeformation
end RealRooted
