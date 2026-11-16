module

public import RealRooted.Basic.ProperPosition
public import RealRooted.Basic.Coefficients
import RealRooted.DerivativeRecurrence.Interlacing
import RealRooted.MaWang.DerivativeStep
import RealRooted.ThreeTermRecurrence.Interlacing

/-!
# Strict interlacing of derivative recurrences of half degree

Two consecutive-interlacing theorems for nonnegative derivative recurrences
`Q (n + 1) = A n * (Q n)' + B n * Q n` whose degrees grow by half a degree per step.  The row
tactics apply them in the `degreePattern` and `fTransform` routes.
-/

public section

open Polynomial

namespace RealRooted

/-- Consecutive strict interlacing for a nonnegative derivative-recurrence sequence whose
degree is `(n + 1) / 2`, including the degree-zero initial row. -/
theorem derivativeRecurrence_strictInterl_of_half_degree
    {Q A B : ℕ → ℝ[X]}
    (hrec : ∀ n, Q (n + 1) = A n * (Q n).derivative + B n * Q n)
    (hdeg : ∀ n, (Q n).natDegree = (n + 1) / 2)
    (hpos : ∀ n, 0 < (Q n).leadingCoeff)
    (hnn : ∀ n, HasNonnegCoeffs (Q n))
    (hA : ∀ n r, r ≤ 0 → (A n).eval r ≤ 0) :
    ∀ n, StrictInterl (Q n) (Q (n + 1))
  | 0 =>
      (interlaces_of_natDegree_eq_zero_of_natDegree_eq_one
        (Polynomial.leadingCoeff_ne_zero.mp (hpos 0).ne') (hdeg 0) (hdeg 1)).toStrictInterl
  | n + 1 => by
      refine derivativeRecurrence_strictInterl_step (hrec (n + 1))
        (derivativeRecurrence_strictInterl_of_half_degree hrec hdeg hpos hnn hA n).2.1.2
        (by rw [hdeg]; grind) (hpos (n + 1)) (hpos (n + 2))
        (by rw [hdeg, hdeg]; grind) (by rw [hdeg, hdeg]; grind) ?_
      intro r hr
      apply hA (n + 1) r
      exact roots_nonpos_of_hasNonnegCoeffs (hnn (n + 1)) r
        ((Polynomial.mem_roots
          (Polynomial.leadingCoeff_ne_zero.mp (hpos (n + 1)).ne')).mpr hr)

/-- Consecutive strict interlacing for a nonnegative derivative recurrence of
degree `n / 2`.  The Ma--Wang constant-row branch handles the initial
constant-to-constant step. -/
theorem derivativeRecurrence_strictInterl_of_floor_half_degree
    {Q A B : ℕ → ℝ[X]}
    (hrec : ∀ n, Q (n + 1) = A n * (Q n).derivative + B n * Q n)
    (hdeg : ∀ n, (Q n).natDegree = n / 2)
    (hpos : ∀ n, 0 < (Q n).leadingCoeff)
    (hnn : ∀ n, HasNonnegCoeffs (Q n))
    (hA : ∀ n r, r ≤ 0 → (A n).eval r ≤ 0) :
    ∀ n, StrictInterl (Q n) (Q (n + 1)) := by
  have hstep (n : ℕ) (hs : (Q n).Splits) :
      StrictInterl (Q n) (Q (n + 1)) := by
    have hstrict := MaWang.strictInterl_derivative_of_nonpos_of_splits
      (u := B n) (v := A n) hs
      (by rw [add_comm, ← hrec n, hdeg, hdeg]; grind)
      (by rw [add_comm, ← hrec n, hdeg, hdeg]; grind)
      (by rw [add_comm, ← hrec n]; exact hpos (n + 1)) (hpos n) (by
        intro r hr
        apply hA n r
        exact roots_nonpos_of_hasNonnegCoeffs (hnn n) r
          ((Polynomial.mem_roots
            (Polynomial.leadingCoeff_ne_zero.mp (hpos n).ne')).mpr hr))
    rw [add_comm, ← hrec n] at hstrict
    exact hstrict
  intro n
  induction n with
  | zero =>
      exact hstep 0 (Polynomial.Splits.of_natDegree_eq_zero (by rw [hdeg]))
  | succ n ih => exact hstep (n + 1) ih.2.1.2

end RealRooted
