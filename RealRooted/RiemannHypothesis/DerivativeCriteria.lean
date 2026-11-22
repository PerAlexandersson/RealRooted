module

public import RealRooted.RiemannHypothesis
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Hadamard
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros

/-!
# Real zeros at a fixed xi derivative index

For each fixed `n`, every zero of `Θ⁽ⁿ⁾` is real exactly when all Jensen
polynomials `J_(d,n)` split. Real zeros at index `n` imply real zeros at every
later derivative index. These are Corollaries 3.2 and 3.3 of Cormac O'Sullivan,
*Zeros of Jensen polynomials and asymptotics for the Riemann xi function*,
https://arxiv.org/abs/2007.13582.

The growth and nonvanishing hypotheses are established unconditionally for
every derivative. A single positive derivative index is not asserted to
characterize RH.
-/

public section

open Complex Polynomial
open scoped ComplexConjugate

namespace RealRooted

/-- For each fixed derivative index, real zeros characterize Laguerre--Pólya membership. -/
theorem isLaguerrePolya_iteratedDeriv_riemannXiTheta_iff (n : ℕ) :
    IsLaguerrePolya (iteratedDeriv n riemannXiTheta) ↔
      ∀ z : ℂ, iteratedDeriv n riemannXiTheta z = 0 → z.im = 0 := by
  constructor
  · intro h z hz
    exact h.im_eq_zero_of_eq_zero
      (fun hzero => iteratedDeriv_riemannXiTheta_zero_ne_zero n (congrFun hzero 0)) hz
  · exact isLaguerrePolya_of_orderLE_one (orderLE_iteratedDeriv_riemannXiTheta n)
      (differentiable_iteratedDeriv_riemannXiTheta n)
      (iteratedDeriv_riemannXiTheta_zero_ne_zero n)
      (iteratedDeriv_conj riemannXiTheta_conj n)

/-- O'Sullivan's Corollary 3.2: real zeros at a fixed derivative index are
equivalent to splitting of every Jensen polynomial at that same shift. -/
theorem riemannXiTheta_iteratedDeriv_zeros_iff_splits (n : ℕ) :
    (∀ z : ℂ, iteratedDeriv n riemannXiTheta z = 0 → z.im = 0) ↔
      ∀ d, (riemannXiJensenPolynomial d n).Splits := by
  rw [← isLaguerrePolya_iteratedDeriv_riemannXiTheta_iff]
  apply isLaguerrePolya_iff_jensenPolynomial_splits
    (differentiable_iteratedDeriv_riemannXiTheta n)
  intro k
  simpa only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm] using
    (ofReal_riemannXiCoeff (n + k)).symm

/-- The fixed-shift criterion only needs the positive degrees, as stated in the paper. -/
theorem riemannXiTheta_iteratedDeriv_zeros_iff_pos_splits (n : ℕ) :
    (∀ z : ℂ, iteratedDeriv n riemannXiTheta z = 0 → z.im = 0) ↔
      ∀ d, 0 < d → (riemannXiJensenPolynomial d n).Splits := by
  rw [riemannXiTheta_iteratedDeriv_zeros_iff_splits]
  refine ⟨fun h d _ => h d, fun h d => ?_⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [riemannXiJensenPolynomial, jensenPolynomial_zero]
  · exact h d hd

/-- O'Sullivan's Corollary 3.3: real zeros at one derivative index propagate
to every later index. The statement also includes the equal-index boundary. -/
theorem riemannXiTheta_iteratedDeriv_zeros_mono {n m : ℕ} (hnm : n ≤ m)
    (h : ∀ z : ℂ, iteratedDeriv n riemannXiTheta z = 0 → z.im = 0) :
    ∀ z : ℂ, iteratedDeriv m riemannXiTheta z = 0 → z.im = 0 := by
  apply (isLaguerrePolya_iteratedDeriv_riemannXiTheta_iff m).mp
  have hLP := (isLaguerrePolya_iteratedDeriv_riemannXiTheta_iff n).mpr h
  simpa only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply,
    Nat.sub_add_cancel hnm] using hLP.iterate_deriv (m - n)

end RealRooted
