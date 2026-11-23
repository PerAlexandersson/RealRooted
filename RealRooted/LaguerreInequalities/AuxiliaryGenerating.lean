module

public import RealRooted.Basic.Coefficients
public import RealRooted.LaguerreInequalities.AuxiliaryProduct
public import RealRooted.Mathlib.Algebra.Polynomial.MobiusTransform
import RealRooted.Mathlib.Algebra.Polynomial.MobiusTransform.Map
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Generating polynomials for an even nonnegative auxiliary

The homogeneous Möbius transform computes the translated root product without
reciprocals. This is the finite-polynomial step in Cardon's Theorem 2.1.
-/

public section

open Polynomial Complex

namespace RealRooted

private theorem even_natDegree_of_monic {g : ℝ[X]} (hg : g.Monic)
    (he : ∀ k, Odd k → g.coeff k = 0) : Even g.natDegree := by
  rcases Nat.even_or_odd g.natDegree with h | h
  · exact h
  · have hz := he _ h
    rw [coeff_natDegree, hg.leadingCoeff] at hz
    exact (one_ne_zero hz).elim

private theorem hasNonnegCoeffs_auxiliaryFactor {g : ℝ[X]}
    (he : ∀ k, Odd k → g.coeff k = 0) (hc : HasNonnegCoeffs g) (u : ℝ) :
    HasNonnegCoeffs (mobiusTransform g.natDegree 0 u 1 0 g) := by
  rw [mobiusTransform_eq_sum _ _ _ _ _ le_rfl]
  simp only [map_zero, zero_mul, zero_add, map_one, one_mul, add_zero]
  apply hasNonnegCoeffs_finsetSum
  intro k _
  rcases Nat.even_or_odd k with hk | hk
  · rw [← map_pow]
    exact (hasNonnegCoeffs_C (hc k)).mul
      ((hasNonnegCoeffs_C (hk.pow_nonneg u)).mul
        (hasNonnegCoeffs_X.pow (g.natDegree - k)))
  · rw [he k hk, map_zero, zero_mul]
    exact hasNonnegCoeffs_zero

/-- The auxiliary translated-product polynomial of a splitting input,
written using the real roots of the input and homogeneous auxiliary factors. -/
@[expose] noncomputable def auxiliaryGeneratingPolynomial
    (g p : ℝ[X]) (x : ℝ) : ℝ[X] :=
  C (p.leadingCoeff ^ g.natDegree) *
    (p.roots.map fun r : ℝ ↦ mobiusTransform g.natDegree 0 (x - r) 1 0 g).prod

/-- A monic even auxiliary with nonnegative coefficients gives a polynomial
with nonnegative coefficients, including zero inputs and vanishing centers. -/
theorem hasNonnegCoeffs_auxiliaryGeneratingPolynomial {g : ℝ[X]} (hg : g.Monic)
    (he : ∀ k, Odd k → g.coeff k = 0) (hc : HasNonnegCoeffs g) (p : ℝ[X]) (x : ℝ) :
    HasNonnegCoeffs (auxiliaryGeneratingPolynomial g p x) := by
  apply (hasNonnegCoeffs_C ((even_natDegree_of_monic hg he).pow_nonneg p.leadingCoeff)).mul
  induction p.roots using Multiset.induction_on with
  | empty => simpa using hasNonnegCoeffs_one
  | cons r s ih =>
      simpa using (hasNonnegCoeffs_auxiliaryFactor he hc (x - r)).mul ih

private theorem eval_auxiliaryFactor {g : ℝ[X]} (hg : g.Monic) (u : ℝ) (z : ℂ) :
    ((mobiusTransform g.natDegree 0 u 1 0 g).map ofRealHom).eval z =
      ((g.map ofRealHom).roots.map fun a ↦ (u : ℂ) - a * z).prod := by
  rw [map_mobiusTransform]
  rw [mobiusTransform_eq_rootFactorProduct g.natDegree _ _ _ _
    (IsAlgClosed.splits (g.map ofRealHom)) (by simp)]
  simp only [(hg.map ofRealHom).leadingCoeff, ofRealHom_eq_coe, ofReal_zero,
    map_one, one_mul, zero_sub, mul_one, mul_zero, sub_zero,
    eval_multiset_prod, Multiset.map_map, Function.comp_apply, eval_add,
    eval_mul, eval_C, eval_X]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro a _
  ring

/-- The homogeneous generating polynomial is exactly the auxiliary
translated product of the input polynomial. -/
theorem eval_auxiliaryGeneratingPolynomial {g p : ℝ[X]} (hg : g.Monic)
    (hp : p.Splits) (x : ℝ) (z : ℂ) :
    ((auxiliaryGeneratingPolynomial g p x).map ofRealHom).eval z =
      auxiliaryProduct g (fun w ↦ (p.map ofRealHom).eval w) x z := by
  have hcard : (g.map ofRealHom).roots.card = g.natDegree := by
    rw [← (IsAlgClosed.splits (g.map ofRealHom)).natDegree_eq_card_roots]
    simp
  have heval (w : ℂ) : (p.map ofRealHom).eval w =
      (p.leadingCoeff : ℂ) * (p.roots.map fun r : ℝ ↦ w - (r : ℂ)).prod := by
    simpa only [leadingCoeff_map, hp.roots_map, Multiset.map_map, Function.comp_def,
      ofRealHom_eq_coe] using (hp.map ofRealHom).eval_eq_prod_roots w
  simp only [auxiliaryGeneratingPolynomial, Polynomial.map_mul, map_C, eval_mul,
    eval_C, ofRealHom_eq_coe, ofReal_pow, Polynomial.map_multiset_prod,
    eval_multiset_prod, Multiset.map_map, Function.comp_apply, eval_auxiliaryFactor hg,
    auxiliaryProduct]
  simp_rw [heval]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard,
    Multiset.prod_map_prod_map]
  apply congrArg ((p.leadingCoeff : ℂ) ^ g.natDegree * ·)
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro r _
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro a _
  rw [ofReal_sub]
  ring

end RealRooted
