import RealRooted.Basic
import Mathlib.Data.Complex.Basic

open Polynomial

noncomputable section

namespace RealRooted

/-- Complexification of a real polynomial. -/
def complexify (p : ℝ[X]) : ℂ[X] :=
  p.map Complex.ofRealHom

@[simp] theorem complexify_zero :
    complexify 0 = 0 := by
  simp [complexify]

@[simp] theorem complexify_one :
    complexify 1 = 1 := by
  simp [complexify]

@[simp] theorem complexify_C (a : ℝ) :
    complexify (C a) = C (a : ℂ) := by
  simp [complexify]

@[simp] theorem complexify_X :
    complexify X = X := by
  simp [complexify]

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

namespace IsHurwitzStable

theorem hasNonnegCoeffs {p : ℝ[X]} (hp : IsHurwitzStable p) :
    HasNonnegCoeffs p :=
  hp.1

theorem rightHalfPlaneStable {p : ℝ[X]} (hp : IsHurwitzStable p) :
    IsRightHalfPlaneStable (complexify p) :=
  hp.2

end IsHurwitzStable

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
    rw [monomial_comp_X_sq]
    by_cases hmn : m = n
    · simp_all
    · have h2 : 2 * m ≠ 2 * n := by lia
      rw [Polynomial.coeff_monomial, Polynomial.coeff_monomial]
      lia

@[simp] lemma coeff_comp_X_sq_odd (p : ℝ[X]) (n : ℕ) :
    (p.comp (X ^ 2 : ℝ[X])).coeff (2 * n + 1) = 0 := by
  refine Polynomial.induction_on' p ?_ ?_
  · simp_all
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
    oddEvenPolynomial p q = oddEvenPolynomial r s ↔ p = r ∧ q = s := by
  constructor
  · exact oddEvenPolynomial_inj
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem oddEvenPolynomial_zero_zero :
    oddEvenPolynomial (0 : ℝ[X]) 0 = 0 := by
  simp [oddEvenPolynomial]

@[simp] theorem oddEvenPolynomial_eq_zero_iff {p q : ℝ[X]} :
    oddEvenPolynomial p q = 0 ↔ p = 0 ∧ q = 0 := by
  simpa using
    (oddEvenPolynomial_eq_iff (p := p) (q := q) (r := 0) (s := 0))

theorem oddEvenPolynomial_ne_zero_iff {p q : ℝ[X]} :
    oddEvenPolynomial p q ≠ 0 ↔ p ≠ 0 ∨ q ≠ 0 := by
  constructor
  · intro h
    by_cases hp : p = 0
    · right
      exact fun hq => h (by simp [hp, hq])
    · exact Or.inl hp
  · rintro (hp | hq) hzero
    · exact hp (oddEvenPolynomial_eq_zero_iff.mp hzero).1
    · exact hq (oddEvenPolynomial_eq_zero_iff.mp hzero).2

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

/-- Sign-normalized forward Hermite--Biehler bridge: positive leading
coefficients on both inputs prevent the false counterexample, ensuring
upper-half-plane stability. -/
theorem hermiteBiehlerForwardPos {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (h : Prec g f) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) := by
  sorry

/-- Concrete obstruction to a sign-free forward Hermite--Biehler route:
`X - i` has the upper-half-plane root `i`. -/
theorem not_isUpperHalfPlaneStable_hermiteBiehlerPolynomial_X_neg_one :
    ¬ IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (X : ℝ[X]) (-(1 : ℝ[X]))) :=
  fun h => h Complex.I (by simp) (by simp [hermiteBiehlerPolynomial, complexify])

/-- Converse Hermite--Biehler theorem: upper-half-plane stability of `f + i g`
forces an interlacing relation between the real and imaginary parts. -/
theorem hermiteBiehlerConverse {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    Prec g f ∨ Prec f g := by
  sorry

/-- Conformal-substitution bridge from Hermite--Biehler stability to Hurwitz stability. -/
theorem hermiteBiehlerStableToHurwitzOddEven {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (h : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q)) := by
  sorry

/-- Analytic bridge from the Hermite--Biehler stable polynomial `q + i p` to
right-half-plane stability of `q(x^2) + x p(x^2)`.

This isolates the classical conformal-substitution part of the
Hermite--Biehler/Hurwitz route. -/
abbrev HermiteBiehlerStableToHurwitzOddEvenStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) →
    IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q))

/-! ## Reduction of the forward Hermite--Biehler/Hurwitz bridge to a
first-quadrant conformal-substitution interface -/

/-- Conjugation symmetry of the complexification: a real polynomial commutes
with complex conjugation under evaluation. -/
theorem eval_complexify_conj (p : ℝ[X]) (z : ℂ) :
    (complexify p).eval (starRingEnd ℂ z) =
      starRingEnd ℂ ((complexify p).eval z) := by
  have hcomp : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
    ext r
    simp
  rw [complexify, Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂, hcomp]

/-- Value of a complexified real polynomial at a real point. -/
theorem eval_complexify_ofReal (p : ℝ[X]) (t : ℝ) :
    (complexify p).eval (t : ℂ) = ((p.eval t : ℝ) : ℂ) := by
  simpa [complexify] using Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := p) t

/-- First-quadrant form of the forward Hermite--Biehler/Hurwitz conformal
substitution: it suffices to exclude roots of `q(x²) + x p(x²)` in the open
first quadrant `{Re > 0, Im > 0}`. -/
def HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) →
    ∀ z : ℂ, 0 < z.re → 0 < z.im →
      (complexify (oddEvenPolynomial p q)).eval z ≠ 0

/-- Upper-half-plane substitution form of the forward Hermite--Biehler/Hurwitz
bridge: for any upper-half-plane point `w` with a right-half-plane square root
`z`, the Hurwitz combination `q(w) + z·p(w)` is nonzero.

This is the genuinely analytic conformal-substitution core: the quadratic map
`z ↦ z²` sends the open first quadrant onto the open upper half-plane, so this
interface and the first-quadrant interface above carry exactly the same
content. -/
def HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) →
    ∀ ⦃w z : ℂ⦄, 0 < w.im → z ^ 2 = w → 0 < z.re →
      (complexify q).eval w + z * (complexify p).eval w ≠ 0

/-- The first-quadrant interface follows from the upper-half-plane substitution
interface: for `z` in the open first quadrant, `w = z²` lies in the open upper
half-plane and `z` is a right-half-plane square root of `w`. -/
theorem hermiteBiehlerStableToHurwitzOddEvenFirstQuadrant_of_upperHalfSubstitution
    (h : HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement) :
    HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement :=
  fun p q hp hq hstable z hzre hzim => by
  rw [eval_complexify_oddEvenPolynomial]
  have hw : 0 < (z ^ 2).im := by
    rw [pow_two, Complex.mul_im]
    positivity
  exact h hp hq hstable hw rfl hzre

/-- Checked reduction of the forward Hermite--Biehler/Hurwitz odd/even bridge to
its first-quadrant conformal-substitution core.

`HermiteBiehlerStableToHurwitzOddEvenStatement` follows from
`HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement`: the real-axis case
`Im z = 0` is handled by positivity of the nonnegative-coefficient polynomial
`q(x²) + x p(x²)`, and the lower half-plane case `Im z < 0` is reduced to the
first quadrant by complex conjugation. -/
theorem hermiteBiehlerStableToHurwitzOddEven_of_firstQuadrant
    (h : HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement) :
    HermiteBiehlerStableToHurwitzOddEvenStatement := by
  intro p q hp hq hstable z hzre
  -- The odd/even polynomial is nonzero, otherwise the stability hypothesis fails.
  have hfne : oddEvenPolynomial p q ≠ 0 := by
    intro h0
    rw [oddEvenPolynomial_eq_zero_iff] at h0
    obtain ⟨hp0, hq0⟩ := h0
    have hI := hstable Complex.I (by rw [Complex.I_im]; norm_num)
    apply hI
    simp [hermiteBiehlerPolynomial, complexify, hp0, hq0]
  rcases lt_trichotomy z.im 0 with him | him | him
  · -- Lower half-plane: reduce to the first quadrant by conjugation.
    have hconj := eval_complexify_conj (oddEvenPolynomial p q) z
    have hre : 0 < (starRingEnd ℂ z).re := by
      simpa [Complex.conj_re] using hzre
    have hci : 0 < (starRingEnd ℂ z).im := by
      rw [Complex.conj_im]
      linarith
    have hne : (complexify (oddEvenPolynomial p q)).eval (starRingEnd ℂ z) ≠ 0 :=
      h hp hq hstable (starRingEnd ℂ z) hre hci
    intro h0
    apply hne
    rw [hconj, h0, map_zero]
  · -- Real axis: positivity of the nonnegative-coefficient polynomial.
    have hz : z = ((z.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hz, eval_complexify_ofReal]
    have hpos : 0 < (oddEvenPolynomial p q).eval z.re :=
      eval_pos_of_hasNonnegCoeffs (hasNonnegCoeffs_oddEvenPolynomial hp hq) hfne hzre
    simpa using hpos.ne'
  · -- First quadrant: the interface applies directly.
    exact h hp hq hstable z hzre him

/-- Composite reduction: the forward Hermite--Biehler/Hurwitz odd/even bridge
follows from the upper-half-plane substitution interface. -/
theorem hermiteBiehlerStableToHurwitzOddEven_of_upperHalfSubstitution
    (h : HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement) :
    HermiteBiehlerStableToHurwitzOddEvenStatement :=
  hermiteBiehlerStableToHurwitzOddEven_of_firstQuadrant
    (hermiteBiehlerStableToHurwitzOddEvenFirstQuadrant_of_upperHalfSubstitution h)

/-- Packaging form of the analytic Hermite--Biehler-to-Hurwitz odd/even
bridge, including the coefficient half of `IsHurwitzStable`. -/
theorem isHurwitzStable_oddEvenPolynomial_of_hermiteBiehlerStableToHurwitz
    {p q : ℝ[X]} (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsHurwitzStable (oddEvenPolynomial p q) :=
  ⟨hasNonnegCoeffs_oddEvenPolynomial hp hq, hermiteBiehlerStableToHurwitzOddEven hp hq hstable⟩

end RealRooted
