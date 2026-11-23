module

public import RealRooted.PFPolynomial
public import RealRooted.LaguerreInequalities.AuxiliaryProduct
import RealRooted.Mathlib.Algebra.Polynomial.PowerRootsProduct
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Ring

/-!
# Generating polynomials for higher-even auxiliary inequalities

For `g = X^n + 1`, the translated product of a splitting polynomial is a
polynomial in `t^n`. Its compressed polynomial has roots `-(x-r)^n`.
For even `n` these roots are nonpositive, with all coefficients nonnegative.
This is the denominator-free form of Cardon's Example 2.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- The polynomial in the compressed translation variable for the auxiliary
`X^n + 1`. The product keeps every real root of the input with multiplicity. -/
@[expose] noncomputable def powerGeneratingPolynomial (n : ℕ) (p : ℝ[X]) (x : ℝ) : ℝ[X] :=
  C (p.leadingCoeff ^ n) * (p.roots.map fun r : ℝ ↦ X + C ((x - r) ^ n)).prod

/-- Even powers give a PF generating polynomial, including zero inputs and
real centers equal to an input root. -/
theorem isPFPolynomial_powerGeneratingPolynomial {n : ℕ} (hn : Even n)
    (p : ℝ[X]) (x : ℝ) : IsPFPolynomial (powerGeneratingPolynomial n p x) := by
  apply (IsPFPolynomial.of_C_nonneg (hn.pow_nonneg p.leadingCoeff)).mul
  induction p.roots using Multiset.induction_on with
  | empty => simpa using IsPFPolynomial.one
  | cons r s ih =>
      simpa using (isPFPolynomial_X_add_C (hn.pow_nonneg (x - r))).mul ih

private theorem eval_powerGeneratingPolynomial (n : ℕ) (p : ℝ[X]) (x : ℝ) (z : ℂ) :
    ((powerGeneratingPolynomial n p x).map ofRealHom).eval z =
      (p.leadingCoeff : ℂ) ^ n *
        (p.roots.map fun r : ℝ ↦ z + ((x : ℂ) - (r : ℂ)) ^ n).prod := by
  simp only [powerGeneratingPolynomial, Polynomial.map_mul, map_C, eval_mul, eval_C,
    ofRealHom_eq_coe, ofReal_pow, Polynomial.map_multiset_prod, eval_multiset_prod,
    Multiset.map_map, Function.comp_apply, Polynomial.map_add, map_X, eval_add, eval_X,
    ofReal_sub]

private theorem auxiliaryProduct_eval_eq {n : ℕ} (hn : n ≠ 0) {p : ℝ[X]}
    (hp : p.Splits) (x : ℝ) (z : ℂ) :
    auxiliaryProduct (X ^ n + 1) (fun w ↦ (p.map ofRealHom).eval w) x z =
      (p.leadingCoeff : ℂ) ^ n *
        (p.roots.map fun r : ℝ ↦ ((x : ℂ) - (r : ℂ)) ^ n + z ^ n).prod := by
  let g : ℂ[X] := X ^ n + 1
  have hcard : g.roots.card = n := by
    rw [← (IsAlgClosed.splits g).natDegree_eq_card_roots]
    simpa only [g, C_1] using
      (natDegree_X_pow_add_C (n := n) (r := (1 : ℂ)))
  have heval (w : ℂ) : (p.map ofRealHom).eval w =
      (p.leadingCoeff : ℂ) * (p.roots.map fun r : ℝ ↦ w - (r : ℂ)).prod := by
    simpa only [leadingCoeff_map, hp.roots_map, Multiset.map_map, Function.comp_def,
      ofRealHom_eq_coe] using (hp.map ofRealHom).eval_eq_prod_roots w
  simp only [auxiliaryProduct, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one]
  change (g.roots.map fun a ↦ (p.map ofRealHom).eval ((x : ℂ) - a * z)).prod = _
  simp_rw [heval]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard,
    Multiset.prod_map_prod_map]
  apply congrArg ((p.leadingCoeff : ℂ) ^ n * ·)
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro r _
  have harg (a : ℂ) : (x : ℂ) - a * z - (r : ℂ) =
      ((x : ℂ) - (r : ℂ)) - a * z := by ring
  simp_rw [harg]
  exact Polynomial.prod_roots_X_pow_add_one_sub_mul hn _ _

/-- The full translated product is obtained by substituting `t^n` into the
compressed generating polynomial. No division by `p(x)` is used. -/
theorem eval_powerGeneratingPolynomial_pow {n : ℕ} (hn : n ≠ 0) {p : ℝ[X]}
    (hp : p.Splits) (x : ℝ) (z : ℂ) :
    ((powerGeneratingPolynomial n p x).map ofRealHom).eval (z ^ n) =
      auxiliaryProduct (X ^ n + 1) (fun w ↦ (p.map ofRealHom).eval w) x z := by
  rw [eval_powerGeneratingPolynomial, auxiliaryProduct_eval_eq hn hp]
  simp only [add_comm]

end RealRooted
