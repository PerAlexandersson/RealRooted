module

import RealRooted.BorceaBranden.FiniteOrderWeylPreserver
import RealRooted.Mathlib.Algebra.MvPolynomial.PDeriv.ToMvPolynomial
public import RealRooted.HermiteBiehler.Basic
import Mathlib.Tactic

/-!
# Univariate differential operators with stable symbol

A finite-order differential operator `g ↦ ∑ j ≤ m, a j * g ^ (j)` with real polynomial
coefficients `a j` sends every nonzero real-rooted polynomial to zero or to a real-rooted
polynomial as soon as its signed Weyl symbol `∑ j, a j (x) * (-y) ^ j` does not vanish for `x`
and `y` in the open upper half-plane.  This is the univariate case of the finite-order Weyl-symbol
theorem `RealRooted.BorceaBranden.finiteOrderWeylOperator_preserves_stability` (Borcea–Brändén,
*The Lee–Yang and Pólya–Schur programs. I*, Invent. Math. 177 (2009), Theorems 1.3–1.4), and it is
the engine behind the fixed-factor criterion for derivative products.
-/

public section

open Polynomial

namespace RealRooted

noncomputable section

/-- `iteratedPDerivAt` on the image of a univariate polynomial is the iterated derivative. -/
private theorem iteratedPDerivAt_toMvPolynomial (j : ℕ) (p : ℂ[X]) :
    iteratedPDerivAt () j (p.toMvPolynomial ()) = (derivative^[j] p).toMvPolynomial () := by
  rw [← MvPolynomial.iterate_pderiv_toMvPolynomial]
  induction j with
  | zero => rfl
  | succ j ih => rw [iteratedPDerivAt, ih, Function.iterate_succ_apply']

/-- **Stable symbol criterion.**  If the signed Weyl symbol `∑ j, a j (x) * (-y) ^ j` of the
operator `g ↦ ∑ j ≤ m, a j * g ^ (j)` has no zero with `x` and `y` in the open upper half-plane,
then the operator sends a nonzero real-rooted polynomial to zero or to a real-rooted polynomial.
(Finite-order case of Borcea–Brändén, Invent. Math. 177 (2009), Thms 1.3–1.4.) -/
theorem sum_mul_iterate_derivative_eq_zero_or_splits {m : ℕ} (a : Fin (m + 1) → ℝ[X])
    (hsym : ∀ x y : ℂ, 0 < x.im → 0 < y.im →
      ∑ j : Fin (m + 1), (complexify (a j)).eval x * (-y) ^ (j : ℕ) ≠ 0)
    {g : ℝ[X]} (hg0 : g ≠ 0) (hgs : g.Splits) :
    ∑ j : Fin (m + 1), a j * (derivative^[j]) g = 0 ∨
      (∑ j : Fin (m + 1), a j * (derivative^[j]) g).Splits := by
  have hW : MvUpperHalfPlaneStable
      (BorceaBranden.signedWeylSymbol m (fun j ↦ (complexify (a j)).toMvPolynomial ())) := by
    intro z hz
    have h := hsym (z (some ())) (z none) (hz (some ())) (hz none)
    simp only [BorceaBranden.signedWeylSymbol, map_sum, MvPolynomial.eval_mul,
      MvPolynomial.eval_rename, Function.comp_apply, MvPolynomial.eval_C, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, MvPolynomial.eval_toMvPolynomial]
    convert h using 1
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hgStable : MvUpperHalfPlaneStable ((complexify g).toMvPolynomial ()) := by
    intro z hz
    rw [MvPolynomial.eval_toMvPolynomial]
    exact Polynomial.Splits.isUpperHalfPlaneStable_complexify hgs hg0 (z ()) (hz ())
  have hout := BorceaBranden.finiteOrderWeylOperator_preserves_stability () m _ hW hgStable
  have hop : BorceaBranden.finiteOrderWeylOperator () m
      (fun j ↦ (complexify (a j)).toMvPolynomial ()) ((complexify g).toMvPolynomial ()) =
        (complexify (∑ j : Fin (m + 1), a j * (derivative^[j]) g)).toMvPolynomial () := by
    rw [BorceaBranden.finiteOrderWeylOperator]
    change (∑ j : Fin (m + 1), (complexify (a j)).toMvPolynomial () *
      iteratedPDerivAt () (j : ℕ) ((complexify g).toMvPolynomial ())) = _
    simp only [iteratedPDerivAt_toMvPolynomial, complexify, Polynomial.map_sum, map_sum,
      ← map_mul, ← iterate_derivative_map, Polynomial.map_mul]
  rw [hop] at hout
  rcases hout with hzero | hstable
  · left
    have hcomplex : complexify (∑ j : Fin (m + 1), a j * (derivative^[j]) g) = 0 :=
      Polynomial.toMvPolynomial_injective () (by rw [hzero]; simp)
    exact (Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp hcomplex
  · right
    apply IsUpperHalfPlaneStable.splits_complexify
    intro z hz
    have heval := hstable (fun _ : Unit ↦ z) (fun _ ↦ hz)
    simpa only [MvPolynomial.eval_toMvPolynomial] using heval

end

end RealRooted
