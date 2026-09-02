import RealRooted.HermiteBiehler.Basic

/-!
# Odd/even polynomial algebra

The polynomial `q(X²) + X * p(X²)`, its coefficient recovery maps,
nonnegativity transport, and degree/parity formulas.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The real polynomial `q(x^2) + x p(x^2)`.

This is the polynomial whose Hurwitz matrix is the two-row Lace matrix for the
odd and even parts in the Athanasiadis--Wagner setup. -/
def oddEvenPolynomial (p q : ℝ[X]) : ℝ[X] :=
  q.comp (X ^ 2) + X * p.comp (X ^ 2)

@[simp] theorem complexify_oddEvenPolynomial (p q : ℝ[X]) :
    complexify (oddEvenPolynomial p q) =
      (complexify q).comp (X ^ 2 : ℂ[X]) +
        X * (complexify p).comp (X ^ 2 : ℂ[X]) := by
  simp [complexify, oddEvenPolynomial, Polynomial.map_comp]

@[simp] theorem eval_complexify_oddEvenPolynomial (p q : ℝ[X]) (z : ℂ) :
    (complexify (oddEvenPolynomial p q)).eval z =
      (complexify q).eval (z ^ 2) + z * (complexify p).eval (z ^ 2) := by
  simp

lemma monomial_comp_X_sq (n : ℕ) (a : ℝ) :
    (Polynomial.monomial n a).comp (X ^ 2 : ℝ[X]) =
      Polynomial.monomial (2 * n) a := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [mul_comp, C_comp, pow_comp, X_comp]
  rw [show (X ^ 2 : ℝ[X]) ^ n = X ^ (2 * n) by rw [pow_mul]]
  rw [Polynomial.C_mul_X_pow_eq_monomial]

@[simp] lemma coeff_comp_X_sq_even (p : ℝ[X]) (n : ℕ) :
    (p.comp (X ^ 2 : ℝ[X])).coeff (2 * n) = p.coeff n := by
  refine Polynomial.induction_on' p ?_ ?_
  · simp_all
  · intro m a
    simp only [monomial_comp_X_sq, Polynomial.coeff_monomial,
      (by lia : 2 * m = 2 * n ↔ m = n)]

@[simp] lemma coeff_comp_X_sq_odd (p : ℝ[X]) (n : ℕ) :
    (p.comp (X ^ 2 : ℝ[X])).coeff (2 * n + 1) = 0 := by
  refine Polynomial.induction_on' p ?_ ?_
  · simp_all
  · intro m a
    simp only [monomial_comp_X_sq, Polynomial.coeff_monomial,
      (by lia : 2 * m = 2 * n + 1 ↔ False), if_false]

@[simp] lemma coeff_X_mul_comp_X_sq_even (p : ℝ[X]) (n : ℕ) :
    (X * p.comp (X ^ 2 : ℝ[X])).coeff (2 * n) = 0 := by
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by lia]
      simp

@[simp] lemma coeff_X_mul_comp_X_sq_odd (p : ℝ[X]) (n : ℕ) :
    (X * p.comp (X ^ 2 : ℝ[X])).coeff (2 * n + 1) = p.coeff n := by
  simp

@[simp] theorem coeff_oddEvenPolynomial_even (p q : ℝ[X]) (n : ℕ) :
    (oddEvenPolynomial p q).coeff (2 * n) = q.coeff n := by
  simp [oddEvenPolynomial]

@[simp] theorem coeff_oddEvenPolynomial_odd (p q : ℝ[X]) (n : ℕ) :
    (oddEvenPolynomial p q).coeff (2 * n + 1) = p.coeff n := by
  simp [oddEvenPolynomial]

/-- The odd/even construction is injective in its two polynomial inputs. -/
theorem oddEvenPolynomial_inj {p q r s : ℝ[X]}
    (h : oddEvenPolynomial p q = oddEvenPolynomial r s) :
    p = r ∧ q = s := by
  constructor
  · ext n
    have hcoeff := congrArg (fun u : ℝ[X] => u.coeff (2 * n + 1)) h
    simpa using hcoeff
  · ext n
    have hcoeff := congrArg (fun u : ℝ[X] => u.coeff (2 * n)) h
    simpa using hcoeff

theorem oddEvenPolynomial_eq_iff {p q r s : ℝ[X]} :
    oddEvenPolynomial p q = oddEvenPolynomial r s ↔ p = r ∧ q = s :=
  ⟨oddEvenPolynomial_inj, fun h => h.1 ▸ h.2 ▸ rfl⟩

@[simp] theorem oddEvenPolynomial_zero_zero :
    oddEvenPolynomial (0 : ℝ[X]) 0 = 0 := by
  simp [oddEvenPolynomial]

@[simp] theorem oddEvenPolynomial_eq_zero_iff {p q : ℝ[X]} :
    oddEvenPolynomial p q = 0 ↔ p = 0 ∧ q = 0 := by
  simpa using
    (oddEvenPolynomial_eq_iff (p := p) (q := q) (r := 0) (s := 0))

theorem oddEvenPolynomial_ne_zero_iff {p q : ℝ[X]} :
    oddEvenPolynomial p q ≠ 0 ↔ p ≠ 0 ∨ q ≠ 0 :=
  (not_congr oddEvenPolynomial_eq_zero_iff).trans not_and_or

theorem hasNonnegCoeffs_oddEvenPolynomial {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (oddEvenPolynomial p q) := fun n => by
  by_cases hmod : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by lia
    rw [hn, coeff_oddEvenPolynomial_even]
    exact hq (n / 2)
  · have hn : n = 2 * (n / 2) + 1 := by lia
    rw [hn, coeff_oddEvenPolynomial_odd]
    exact hp (n / 2)

theorem hasNonnegCoeffs_left_of_oddEvenPolynomial {p q : ℝ[X]}
    (h : HasNonnegCoeffs (oddEvenPolynomial p q)) :
    HasNonnegCoeffs p := fun n => by
  simpa using h (2 * n + 1)

theorem hasNonnegCoeffs_right_of_oddEvenPolynomial {p q : ℝ[X]}
    (h : HasNonnegCoeffs (oddEvenPolynomial p q)) :
    HasNonnegCoeffs q := fun n => by
  simpa using h (2 * n)

/-! ## Degree and parity -/

/-- Composition with `X²` is nonzero-preserving. -/
theorem comp_X_sq_ne_zero {p : ℝ[X]} (hp : p ≠ 0) :
    p.comp (X ^ 2 : ℝ[X]) ≠ 0 := by
  rw [Ne, Polynomial.comp_eq_zero_iff]
  rintro (h | ⟨_, hc⟩)
  · exact hp h
  · have hd :
      (X ^ 2 : ℝ[X]).natDegree = (C ((X ^ 2 : ℝ[X]).coeff 0)).natDegree := by rw [← hc]
    simp at hd

/-- The substitution `X ↦ X²` doubles the degree. -/
theorem natDegree_comp_X_sq (q : ℝ[X]) :
    (q.comp (X ^ 2 : ℝ[X])).natDegree = 2 * q.natDegree := by
  rw [Polynomial.natDegree_comp]
  simp
  ring

/-- Degree of the odd part `x · p(x²)`. -/
theorem natDegree_X_mul_comp_X_sq {p : ℝ[X]} (hp : p ≠ 0) :
    (X * p.comp (X ^ 2 : ℝ[X])).natDegree = 2 * p.natDegree + 1 := by
  rw [Polynomial.natDegree_mul (by simp) (comp_X_sq_ne_zero hp), Polynomial.natDegree_X,
    natDegree_comp_X_sq]
  ring

/-- Degree of the odd/even polynomial `q(x²) + x p(x²)`.

The even and odd summands have opposite-parity degrees, so their leading terms
cannot cancel. -/
theorem natDegree_oddEvenPolynomial {p q : ℝ[X]} (hp : p ≠ 0) :
    (oddEvenPolynomial p q).natDegree =
      max (2 * q.natDegree) (2 * p.natDegree + 1) := by
  have ha : (q.comp (X ^ 2 : ℝ[X])).natDegree = 2 * q.natDegree :=
    natDegree_comp_X_sq q
  have hb : (X * p.comp (X ^ 2 : ℝ[X])).natDegree = 2 * p.natDegree + 1 :=
    natDegree_X_mul_comp_X_sq hp
  unfold oddEvenPolynomial
  rcases lt_or_gt_of_ne (show (q.comp (X ^ 2 : ℝ[X])).natDegree ≠
      (X * p.comp (X ^ 2 : ℝ[X])).natDegree by omega) with h | h
  · rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt h, hb]
    omega
  · rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt h, ha]
    omega

/-- For `p ≠ 0`, the odd/even polynomial has even degree exactly when the even
part has strictly larger degree than the odd input. -/
theorem natDegree_lt_iff_even_natDegree_oddEvenPolynomial {p q : ℝ[X]}
    (hp : p ≠ 0) :
    p.natDegree < q.natDegree ↔ Even (oddEvenPolynomial p q).natDegree := by
  rw [natDegree_oddEvenPolynomial hp]
  constructor
  · intro h
    exact ⟨q.natDegree, by rw [max_eq_left (by lia)]; ring⟩
  · intro h
    by_contra hcon
    have hle := Nat.not_lt.mp hcon
    rw [max_eq_right (by lia)] at h
    rcases h with ⟨k, hk⟩
    lia

end RealRooted
