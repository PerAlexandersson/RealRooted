import RealRooted.Derivative.Interlacing
import RealRooted.NarayanaTransformation.Endpoints
import RealRooted.SimpleRoots

/-!
# Simple roots of generalized Narayana polynomials

Consecutive proper position and the no-common-root recurrence give simple
roots for every generalized Narayana polynomial. Derivative interlacing then
gives the corresponding positive-degree derivative result.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Every generalized Narayana polynomial has simple real roots. -/
theorem narayanaPolynomial_hasSimpleRoots (m n : ℕ) :
    HasSimpleRoots (narayanaPolynomial m n) := by
  cases n with
  | zero => simp [HasSimpleRoots, narayanaPolynomial]
  | succ n =>
      exact ((prec_narayanaPolynomial_succ m n).hasSimpleRoots_of_no_common_root
        (fun r hr ↦ (narayanaPolynomial_no_common_root m (n + 1) r hr.2) hr.1)).1

/-- The derivative of a positive-degree generalized Narayana polynomial has
simple real roots. -/
theorem narayanaPolynomial_derivative_hasSimpleRoots
    (m n : ℕ) (hn : 0 < n) :
    HasSimpleRoots (narayanaPolynomial m n).derivative := by
  rcases n with _ | _ | n
  · simp at hn
  · simp [narayanaPolynomial_one, HasSimpleRoots]
  · have hprec : Prec (narayanaPolynomial m (n + 2)).derivative
        (narayanaPolynomial m (n + 2)) :=
      (derivative_interlaces (splits_narayanaPolynomial m (n + 2))
        (by rw [natDegree_narayanaPolynomial]; lia)).toPrec
    exact (hprec.hasSimpleRoots_of_no_common_root (fun _ hr ↦
      (narayanaPolynomial_hasSimpleRoots m (n + 2)).eval_derivative_ne_zero hr.2 hr.1)).1

end RealRooted
