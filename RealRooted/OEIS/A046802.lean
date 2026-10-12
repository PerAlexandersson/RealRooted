import RealRooted.ThresholdMatrix.HaglundZhang

/-!
# OEIS A046802

The sequence-facing surface of A046802: its rows are the Haglund--Zhang binomial Eulerian
polynomials, and the refined Haglund--Zhang vector is the interlacing certificate.  The
mathematical work lives in `RealRooted.ThresholdMatrix.HaglundZhang`.
-/

open Polynomial

noncomputable section

namespace RealRooted

namespace OEIS

/-- The recurrence-defined A046802 row family, represented by the
Haglund--Zhang binomial Eulerian polynomial.  Agreement with the external OEIS
table is intentionally a separate theorem for the generated sequence file. -/
abbrev A046802 (n : ℕ) : ℝ[X] :=
  HaglundZhang.binomialEulerianPolynomial n

/-- The refined Haglund--Zhang vector used as the interlacing certificate for
`A046802`. -/
abbrev A046802Refined (n : ℕ) : List ℝ[X] :=
  HaglundZhang.binomialRefined n

@[simp] theorem A046802_eq_binomialEulerianPolynomial (n : ℕ) :
    A046802 n = HaglundZhang.binomialEulerianPolynomial n := rfl

@[simp] theorem A046802Refined_eq_binomialRefined (n : ℕ) :
    A046802Refined n = HaglundZhang.binomialRefined n := rfl

@[simp] theorem coeff_zero_A046802 (n : ℕ) :
    (A046802 n).coeff 0 = 1 :=
  HaglundZhang.coeff_zero_binomialEulerianPolynomial n

/-- Interlacing certificate for the Haglund--Zhang refinement behind A046802. -/
theorem A046802_interlaces (n : ℕ) :
    IsInterlacingSeq0Nonneg (A046802Refined n) :=
  HaglundZhang.binomialRefined_interlaces n

/-- Real-rootedness certificate for each nonzero refined polynomial behind A046802. -/
theorem A046802_refined_realRooted (n : ℕ) :
    ∀ f ∈ A046802Refined n, f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  HaglundZhang.binomialRefined_realRooted n

theorem A046802_ne_zero (n : ℕ) :
    A046802 n ≠ 0 :=
  HaglundZhang.binomialEulerianPolynomial_ne_zero n

theorem A046802_realRooted (n : ℕ) :
    A046802 n ≠ 0 ∧ (A046802 n).Splits :=
  HaglundZhang.binomialEulerianPolynomial_realRooted n

end OEIS

end RealRooted
