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

/-- Explicit `m = 1` Narayana Turan determinant. -/
theorem modifiedNarayanaTuran_one (r : ℝ) :
    modifiedNarayanaTuran 1 r = -r := by
  rw [modifiedNarayanaTuran, modifiedNarayanaPolynomial_zero,
    modifiedNarayanaPolynomial_one, modifiedNarayanaPolynomial_eq_coeffPolynomial 2,
    modifiedNarayanaCoeffPolynomial_two]
  norm_num
  ring

/-- Cleared eval form of the three-term recurrence for modified Narayana
polynomials. -/
theorem modifiedNarayanaPolynomial_eval_three_term_rec (j : ℕ) (r : ℝ) :
    ((j : ℝ) + 4) * (modifiedNarayanaPolynomial (j + 2)).eval r =
      ((2 * j : ℝ) + 5) *
          ((1 + r) * (modifiedNarayanaPolynomial (j + 1)).eval r) -
        ((j : ℝ) + 1) *
          ((1 - r) ^ 2 * (modifiedNarayanaPolynomial j).eval r) := by
  simp only [modifiedNarayanaPolynomial]
  rw [narayanaQuot_succ_succ]
  simp [narayanaCoeffA, narayanaCoeffB, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub]
  field_simp [show ((j : ℝ) + 4) ≠ 0 by positivity]
  ring_nf

/-- The modified Narayana Turan determinant satisfies a sum-of-squares
recurrence on the nonpositive-input side. -/
theorem modifiedNarayanaTuran_succ_identity (j : ℕ) (r : ℝ) :
    ((j : ℝ) + 5) * modifiedNarayanaTuran (j + 2) r =
      ((j : ℝ) + 1) * (r - 1) ^ 2 * modifiedNarayanaTuran (j + 1) r +
        ((modifiedNarayanaPolynomial (j + 2)).eval r -
          (1 + r) * (modifiedNarayanaPolynomial (j + 1)).eval r) ^ 2 +
        (-4 * r) * ((modifiedNarayanaPolynomial (j + 1)).eval r) ^ 2 := by
  let p0 := (modifiedNarayanaPolynomial j).eval r
  let p1 := (modifiedNarayanaPolynomial (j + 1)).eval r
  let p2 := (modifiedNarayanaPolynomial (j + 2)).eval r
  let p3 := (modifiedNarayanaPolynomial (j + 2 + 1)).eval r
  have h0 : ((j : ℝ) + 4) * p2 =
      ((2 * j : ℝ) + 5) * ((1 + r) * p1) -
        ((j : ℝ) + 1) * ((1 - r) ^ 2 * p0) := by
    simpa [p0, p1, p2] using
      modifiedNarayanaPolynomial_eval_three_term_rec j r
  have h1 : ((j : ℝ) + 5) * p3 =
      ((2 * j : ℝ) + 7) * ((1 + r) * p2) -
        ((j : ℝ) + 2) * ((1 - r) ^ 2 * p1) := by
    have hraw := modifiedNarayanaPolynomial_eval_three_term_rec (j + 1) r
    dsimp [p1, p2, p3]
    convert hraw using 1 <;> (push_cast; ring_nf)
  change ((j : ℝ) + 5) * (p2 ^ 2 - p3 * p1) =
    ((j : ℝ) + 1) * (r - 1) ^ 2 * (p1 ^ 2 - p2 * p0) +
      (p2 - (1 + r) * p1) ^ 2 + (-4 * r) * p1 ^ 2
  linear_combination (-p1) * h1 + p2 * h0

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

/-- For `r ≠ 1`, the modified Narayana Turan determinant is the
`(r - 1) ^ (2 * m)` rescaling of the Turan determinant of the normalized
Jacobi polynomials at the Braun--Jal change of variables.  This is the bridge
to Gasper's Turan theorem on `[-1, 1]`. -/
theorem modifiedNarayanaTuran_eq_scale_mul_jacobi11NormalizedTuran
    {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr : r ≠ 1) :
    modifiedNarayanaTuran m r =
      (r - 1) ^ (2 * m) *
        (((jacobi11NormalizedPolynomial m).eval
              (jacobi11ChangeOfVariables r)) ^ 2 -
          (jacobi11NormalizedPolynomial (m + 1)).eval
              (jacobi11ChangeOfVariables r) *
            (jacobi11NormalizedPolynomial (m - 1)).eval
              (jacobi11ChangeOfVariables r)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by lia⟩
  have e0 := jacobi11NormalizedPolynomial_transport_eval (n := k) hr
  have e1 := jacobi11NormalizedPolynomial_transport_eval (n := k + 1) hr
  have e2 := jacobi11NormalizedPolynomial_transport_eval (n := k + 1 + 1) hr
  simp only [modifiedNarayanaTuran, Nat.add_sub_cancel,
    ← jacobi11TransportPolynomial_eq_modifiedNarayanaPolynomial]
  rw [← e0, ← e1, ← e2]
  ring

/-- Statement form for the remaining Narayana Turan inequality needed by the
shifted Lemma 3.4 route. -/
def ModifiedNarayanaTuranNonnegOnNonposStatement : Prop :=
  ∀ {m : ℕ} {r : ℝ}, 1 ≤ m → r ≤ 0 → 0 ≤ modifiedNarayanaTuran m r

/-- The normalized Jacobi Turan inequality on `[-1, 1]` gives the modified
Narayana Turan inequality on nonpositive inputs through the Braun--Jal change
of variables. -/
theorem modifiedNarayanaTuranNonnegOnNonpos_of_jacobi11NormalizedTuran
    (hjacobi : ∀ {m : ℕ} {x : ℝ}, 1 ≤ m → x ∈ Set.Icc (-1 : ℝ) 1 →
      0 ≤ ((jacobi11NormalizedPolynomial m).eval x) ^ 2 -
        (jacobi11NormalizedPolynomial (m + 1)).eval x *
          (jacobi11NormalizedPolynomial (m - 1)).eval x) :
    ModifiedNarayanaTuranNonnegOnNonposStatement := by
  intro m r hm hr
  have hr_ne : r ≠ 1 := by linarith
  rw [modifiedNarayanaTuran_eq_scale_mul_jacobi11NormalizedTuran hm hr_ne]
  exact mul_nonneg (jacobi11TuranScale_nonneg m r)
    (hjacobi hm (jacobi11ChangeOfVariables_mem_Icc_of_nonpos hr))

/-- Modified Narayana Turan determinants are nonnegative on nonpositive
inputs. -/
theorem modifiedNarayanaTuran_nonneg_of_nonpos
    {m : ℕ} {r : ℝ} (hm : 1 ≤ m) (hr : r ≤ 0) :
    0 ≤ modifiedNarayanaTuran m r := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by lia⟩
  clear hm
  induction j with
  | zero =>
      rw [modifiedNarayanaTuran_one]
      linarith
  | succ j ih =>
      apply nonneg_of_mul_nonneg_right (a := ((j : ℝ) + 5))
      · rw [modifiedNarayanaTuran_succ_identity]
        exact add_nonneg
          (add_nonneg
            (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg (r - 1))) ih)
            (sq_nonneg _))
          (mul_nonneg (by nlinarith) (sq_nonneg _))
      · positivity

/-- The all-`m` Narayana Turan package needed by the shifted Lemma 3.4 route. -/
theorem modifiedNarayanaTuranNonnegOnNonpos :
    ModifiedNarayanaTuranNonnegOnNonposStatement := by
  intro m r hm hr
  exact modifiedNarayanaTuran_nonneg_of_nonpos hm hr

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
