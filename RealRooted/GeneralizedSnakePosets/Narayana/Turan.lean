import RealRooted.GeneralizedSnakePosets.Narayana.JacobiTransport

/-!
# Certificate-free Turan API for modified Narayana polynomials

This module contains the reusable Turan determinant statements and the
hypothesis-taking bridge lemmas for Braun--Jal Lemma 3.4.  Explicit finite
certificates live in `RealRooted.GeneralizedSnakePosets.Narayana.TuranCertificates`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- The Narayana Turan determinant that remains in the shifted Lemma 3.4
route.  The next analytic target is its nonnegativity on nonpositive inputs. -/
def modifiedNarayanaTuran (m : ℕ) (r : ℝ) : ℝ :=
  ((modifiedNarayanaPolynomial m).eval r) ^ 2 -
    (modifiedNarayanaPolynomial (m + 1)).eval r *
      (modifiedNarayanaPolynomial (m - 1)).eval r

/-- The Turan determinant built from the normalized Jacobi transport
polynomials. -/
def jacobi11TransportTuran (m : ℕ) (r : ℝ) : ℝ :=
  ((jacobi11TransportPolynomial m).eval r) ^ 2 -
    (jacobi11TransportPolynomial (m + 1)).eval r *
      (jacobi11TransportPolynomial (m - 1)).eval r

/-- The modified Narayana Turan determinant is the Turan determinant of the
normalized Jacobi transport polynomials. -/
theorem modifiedNarayanaTuran_eq_jacobi11TransportTuran (m : ℕ) (r : ℝ) :
    modifiedNarayanaTuran m r = jacobi11TransportTuran m r := by
  simp [modifiedNarayanaTuran, jacobi11TransportTuran,
    jacobi11TransportPolynomial_eq_modifiedNarayanaPolynomial]

/-- Statement form for the remaining Narayana Turan inequality needed by the
shifted Lemma 3.4 route. -/
def ModifiedNarayanaTuranNonnegOnNonposStatement : Prop :=
  ∀ {m : ℕ} {r : ℝ}, 1 ≤ m → r ≤ 0 → 0 ≤ modifiedNarayanaTuran m r

/-- Bounded statement form for the Narayana Turan inequality.  This records
finite checkpoints while the all-`m` nonpositive-input proof is being built. -/
def ModifiedNarayanaTuranNonnegOnNonposUpToStatement (N : ℕ) : Prop :=
  ∀ {m : ℕ} {r : ℝ}, 1 ≤ m → m ≤ N → r ≤ 0 →
    0 ≤ modifiedNarayanaTuran m r

/-- The all-`m` Turan inequality implies every bounded Turan package. -/
theorem modifiedNarayanaTuranNonnegOnNonposUpTo_of_statement
    (hT : ModifiedNarayanaTuranNonnegOnNonposStatement) (N : ℕ) :
    ModifiedNarayanaTuranNonnegOnNonposUpToStatement N := by
  intro m r hm _hmN hr
  exact hT hm hr

/-- At a root of the shifted Lemma 3.4 left-hand polynomial, the right-hand
polynomial sign test is exactly the negative Narayana Turan determinant. -/
theorem lemma34ModifiedNarayanaShifted_right_eval_mul_prev_eq_neg_turan
    {m : ℕ} {lam mu r : ℝ}
    (hr : (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r =
        -modifiedNarayanaTuran m r := by
  let A := (C lam * X + C mu : ℝ[X]).eval r
  let p₀ := (modifiedNarayanaPolynomial (m - 1)).eval r
  let p₁ := (modifiedNarayanaPolynomial m).eval r
  let p₂ := (modifiedNarayanaPolynomial (m + 1)).eval r
  have hrel : A * p₀ + (p₁ - p₀) = 0 := by
    simpa [Polynomial.IsRoot.def, narayanaDifference, A, p₀, p₁,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul] using hr
  have hrel' : (A - 1) * p₀ = -p₁ := by linarith
  calc
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r
        = (A * p₁ + (p₂ - p₁)) * p₀ := by
            simp [narayanaDifference, A, p₀, p₁, p₂, Polynomial.eval_add,
              Polynomial.eval_sub, Polynomial.eval_mul]
    _ = p₂ * p₀ + ((A - 1) * p₀) * p₁ := by ring
    _ = p₂ * p₀ - p₁ ^ 2 := by rw [hrel']; ring
    _ = -modifiedNarayanaTuran m r := by
        simp [modifiedNarayanaTuran, p₀, p₁, p₂]

/-- A pointwise nonnegative Turan determinant gives the shifted Lemma 3.4
right-hand sign test at a root of the left-hand polynomial. -/
theorem lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_turan
    {m : ℕ} {lam mu r : ℝ}
    (hr : (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r))
    (hT : 0 ≤ modifiedNarayanaTuran m r) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 := by
  rw [lemma34ModifiedNarayanaShifted_right_eval_mul_prev_eq_neg_turan hr]
  linarith

/-- The global nonpositive-input Turan inequality gives the shifted Lemma 3.4
right-hand sign test at roots of the left-hand polynomial. -/
theorem lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_turanNonneg
    {m : ℕ} {lam mu r : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hT : ModifiedNarayanaTuranNonnegOnNonposStatement)
    (hr : (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_turan hr
    (hT hm (lemma34ModifiedNarayanaShifted_left_isRoot_nonpos hm hlam hmu
      (lemma34ModifiedNarayanaShifted_left_ne_zero hm hlam hmu) r hr))

/-- A bounded nonpositive-input Turan package gives the shifted Lemma 3.4
right-hand sign test in that range. -/
theorem
    lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    {N m : ℕ} {lam mu r : ℝ} (hm : 1 ≤ m) (hmN : m ≤ N)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hT : ModifiedNarayanaTuranNonnegOnNonposUpToStatement N)
    (hr : (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_turan hr
    (hT hm hmN (lemma34ModifiedNarayanaShifted_left_isRoot_nonpos hm hlam hmu
      (lemma34ModifiedNarayanaShifted_left_ne_zero hm hlam hmu) r hr))

/-- At a root of the paper-shaped Lemma 3.4 left-hand polynomial, the
right-hand sign test is exactly the negative Narayana Turan determinant. -/
theorem lemma34ModifiedNarayana_right_eval_mul_prev_eq_neg_turan
    {m : ℕ} {lam nu r : ℝ}
    (hr : (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r =
        -modifiedNarayanaTuran m r := by
  let A := (C lam * X + C nu : ℝ[X]).eval r
  let p₀ := (modifiedNarayanaPolynomial (m - 1)).eval r
  let p₁ := (modifiedNarayanaPolynomial m).eval r
  let p₂ := (modifiedNarayanaPolynomial (m + 1)).eval r
  have hrel : A * p₀ + p₁ = 0 := by
    simpa [Polynomial.IsRoot.def, A, p₀, p₁, Polynomial.eval_add,
      Polynomial.eval_mul] using hr
  have hrel' : A * p₀ = -p₁ := by linarith
  calc
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r
        = (A * p₁ + p₂) * p₀ := by
            simp [A, p₀, p₁, p₂, Polynomial.eval_add, Polynomial.eval_mul]
    _ = p₂ * p₀ + (A * p₀) * p₁ := by ring
    _ = p₂ * p₀ - p₁ ^ 2 := by rw [hrel']; ring
    _ = -modifiedNarayanaTuran m r := by
        simp [modifiedNarayanaTuran, p₀, p₁, p₂]

/-- A pointwise nonnegative Turan determinant gives the paper-shaped Lemma 3.4
right-hand sign test at a root of the left-hand polynomial. -/
theorem lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_turan
    {m : ℕ} {lam nu r : ℝ}
    (hr : (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).IsRoot r))
    (hT : 0 ≤ modifiedNarayanaTuran m r) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 := by
  rw [lemma34ModifiedNarayana_right_eval_mul_prev_eq_neg_turan hr]
  linarith

/-- The global nonpositive-input Turan inequality gives the paper-shaped
Lemma 3.4 right-hand sign test at roots of the left-hand polynomial. -/
theorem lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_turanNonneg
    {m : ℕ} {lam nu r : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hT : ModifiedNarayanaTuranNonnegOnNonposStatement)
    (hr : (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_turan hr
    (hT hm (lemma34ModifiedNarayana_left_isRoot_nonpos hm hlam hnu hr))

/-- A bounded nonpositive-input Turan package gives the paper-shaped Lemma 3.4
right-hand sign test in that range. -/
theorem lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    {N m : ℕ} {lam nu r : ℝ} (hm : 1 ≤ m) (hmN : m ≤ N)
    (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hT : ModifiedNarayanaTuranNonnegOnNonposUpToStatement N)
    (hr : (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_turan hr
    (hT hm hmN (lemma34ModifiedNarayana_left_isRoot_nonpos hm hlam hnu hr))

end GeneralizedSnakePosets
end RealRooted
