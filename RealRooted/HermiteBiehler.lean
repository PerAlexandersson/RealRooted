import RealRooted.Basic
import Mathlib.Data.Complex.Basic

open Polynomial

noncomputable section

namespace RealRooted

/-- Complexification of a real polynomial. -/
def complexify (p : ℝ[X]) : ℂ[X] :=
  p.map Complex.ofRealHom

/-- A univariate complex polynomial is upper-half-plane stable if it has no root
with strictly positive imaginary part. -/
def IsUpperHalfPlaneStable (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0

/-- A univariate complex polynomial is right-half-plane stable if it has no
root with strictly positive real part. -/
def IsRightHalfPlaneStable (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, 0 < z.re → p.eval z ≠ 0

/-- Hurwitz stability for a real polynomial in the coefficient-positive
combinatorial convention used here. -/
def IsHurwitzStable (p : ℝ[X]) : Prop :=
  HasNonnegCoeffs p ∧ IsRightHalfPlaneStable (complexify p)

/-- The classical Hermite--Biehler combination `f + i g`. -/
def hermiteBiehlerPolynomial (f g : ℝ[X]) : ℂ[X] :=
  complexify f + C Complex.I * complexify g

@[simp] theorem eval_hermiteBiehlerPolynomial (f g : ℝ[X]) (z : ℂ) :
    (hermiteBiehlerPolynomial f g).eval z =
      (complexify f).eval z + Complex.I * (complexify g).eval z := by
  simp [hermiteBiehlerPolynomial]

/-! ## Odd/even polynomial used by the Hurwitz form -/

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
  rw [complexify_oddEvenPolynomial]
  simp [Polynomial.eval_comp]

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
  · intro p q hp hq
    simp [hp, hq]
  · intro m a
    rw [monomial_comp_X_sq]
    by_cases hmn : m = n
    · subst hmn
      simp
    · have h2 : 2 * m ≠ 2 * n := by lia
      rw [Polynomial.coeff_monomial, Polynomial.coeff_monomial]
      simp [hmn, h2]

@[simp] lemma coeff_comp_X_sq_odd (p : ℝ[X]) (n : ℕ) :
    (p.comp (X ^ 2 : ℝ[X])).coeff (2 * n + 1) = 0 := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    simp [hp, hq]
  · intro m a
    rw [monomial_comp_X_sq]
    have h2 : 2 * m ≠ 2 * n + 1 := by lia
    simp [Polynomial.coeff_monomial, h2]

@[simp] lemma coeff_X_mul_comp_X_sq_even (p : ℝ[X]) (n : ℕ) :
    (X * p.comp (X ^ 2 : ℝ[X])).coeff (2 * n) = 0 := by
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by lia]
      rw [Polynomial.coeff_X_mul, coeff_comp_X_sq_odd]

@[simp] lemma coeff_X_mul_comp_X_sq_odd (p : ℝ[X]) (n : ℕ) :
    (X * p.comp (X ^ 2 : ℝ[X])).coeff (2 * n + 1) = p.coeff n := by
  rw [Polynomial.coeff_X_mul, coeff_comp_X_sq_even]

@[simp] theorem coeff_oddEvenPolynomial_even (p q : ℝ[X]) (n : ℕ) :
    (oddEvenPolynomial p q).coeff (2 * n) = q.coeff n := by
  simp [oddEvenPolynomial]

@[simp] theorem coeff_oddEvenPolynomial_odd (p q : ℝ[X]) (n : ℕ) :
    (oddEvenPolynomial p q).coeff (2 * n + 1) = p.coeff n := by
  simp [oddEvenPolynomial]

theorem hasNonnegCoeffs_oddEvenPolynomial {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (oddEvenPolynomial p q) := by
  intro n
  by_cases hmod : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by
      have hdiv := Nat.div_add_mod n 2
      lia
    rw [hn, coeff_oddEvenPolynomial_even]
    exact hq (n / 2)
  · have hn : n = 2 * (n / 2) + 1 := by
      have hdiv := Nat.div_add_mod n 2
      have hlt : n % 2 < 2 := Nat.mod_lt n (by norm_num)
      lia
    rw [hn, coeff_oddEvenPolynomial_odd]
    exact hp (n / 2)

theorem hasNonnegCoeffs_left_of_oddEvenPolynomial {p q : ℝ[X]}
    (h : HasNonnegCoeffs (oddEvenPolynomial p q)) :
    HasNonnegCoeffs p := by
  intro n
  simpa using h (2 * n + 1)

theorem hasNonnegCoeffs_right_of_oddEvenPolynomial {p q : ℝ[X]}
    (h : HasNonnegCoeffs (oddEvenPolynomial p q)) :
    HasNonnegCoeffs q := by
  intro n
  simpa using h (2 * n)


/-- Sign-normalized forward Hermite--Biehler bridge.

This is the minimal sign-stable form used in downstream plumbing:
positive leading coefficients on both inputs prevent the false counterexample.
-/
def hermiteBiehlerForwardPosStatement : Prop :=
  ∀ {f g : ℝ[X]},
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    Prec g f →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)

/-- Legacy planning stub for the sign-free forward interface.

This exact form is too weak without a sign normalization; see
`not_hermiteBiehlerForwardStatement`. -/
def hermiteBiehlerForwardStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Prec g f →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)

/-- Nonnegative coefficients plus nonzeroness force a positive leading
coefficient.  This is a small normalization helper for bridging to the
sign-normalized Hermite--Biehler route. -/
lemma hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hp0 : p ≠ 0) :
    HasPosLeadingCoeff p := by
  unfold HasPosLeadingCoeff HasNonnegCoeffs at *
  have hlead_ne : p.coeff p.natDegree ≠ 0 := by
    simpa [Polynomial.coeff_natDegree] using (Polynomial.leadingCoeff_ne_zero).2 hp0
  exact lt_of_le_of_ne (hpnn p.natDegree) (by simpa using hlead_ne.symm)

/-- The legacy sign-free statement implies the normalized one as a
specialization. -/
theorem hermiteBiehlerForwardPosStatement_of_forward
    (hHB : hermiteBiehlerForwardStatement) :
    hermiteBiehlerForwardPosStatement := by
  intro f g hf hg hpq
  exact hHB hpq

/-- The current sign-free forward Hermite--Biehler interface is false:
`-1 ≪ X`, but `X - i` has the upper-half-plane root `i`. -/
theorem not_hermiteBiehlerForwardStatement :
    ¬ hermiteBiehlerForwardStatement := by
  intro h
  have hprec : Prec (-(1 : ℝ[X])) (X : ℝ[X]) := by
    have hX : ((X : ℝ[X]) ≠ 0 ∧ (X : ℝ[X]).Splits) := by
      refine ⟨X_ne_zero, ?_⟩
      exact splits_of_card_roots <| by
        rw [roots_X, Multiset.card_singleton, natDegree_X]
    have hneg : ((-(1 : ℝ[X])) ≠ 0 ∧ (-(1 : ℝ[X])).Splits) := by
      refine isRealRooted_of_deg_zero ?_ ?_
      · norm_num
      · simp
    apply Interlaces.toPrec
    refine ⟨hX, hneg, ?_, [0], [], ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp [ListInterlaces]
  exact h (f := X) (g := -(1 : ℝ[X])) hprec Complex.I (by simp)
    (by simp [hermiteBiehlerPolynomial, complexify])

/-- Planning stub for the converse Hermite--Biehler theorem.

The exact orientation hypotheses may still be adjusted, but the target is that
upper-half-plane stability of `f + i g` forces an interlacing relation between
the real and imaginary parts. -/
def hermiteBiehlerConverseStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) →
    Prec g f ∨ Prec f g

/-- Analytic bridge from the Hermite--Biehler stable polynomial `q + i p` to
right-half-plane stability of `q(x^2) + x p(x^2)`.

This isolates the classical conformal-substitution part of the
Hermite--Biehler/Hurwitz route. -/
def HermiteBiehlerStableToHurwitzOddEvenStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) →
    IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q))

/-- Packaging form of the analytic Hermite--Biehler-to-Hurwitz odd/even
bridge, including the coefficient half of `IsHurwitzStable`. -/
theorem isHurwitzStable_oddEvenPolynomial_of_hermiteBiehlerStableToHurwitz
    (h : HermiteBiehlerStableToHurwitzOddEvenStatement) {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsHurwitzStable (oddEvenPolynomial p q) := by
  exact ⟨hasNonnegCoeffs_oddEvenPolynomial hp hq, h hp hq hstable⟩

end RealRooted
