module

public import RealRooted.TuranHurwitz.PairedRoots
public import RealRooted.TuranHurwitz.FiniteRoots
import RealRooted.TuranHurwitz.CoefficientDerivation
import Mathlib.Tactic.Ring

/-!
# Pairing a split polynomial along the formal flow

Factorization includes every root with its multiplicity. The constant factors
recombine into the square of the polynomial evaluated at the fixed parameter.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

local notation "S" => complexTanhSeries

/-- Rescaling commutes with evaluation of a real polynomial in a complex formal series. -/
theorem rescale_aeval_series (a : ℂ) (p : ℝ[X]) (g : PowerSeries ℂ) :
    PowerSeries.rescale a (Polynomial.aeval g p) =
      Polynomial.aeval (PowerSeries.rescale a g) p := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  ext r
  simp [PowerSeries.algebraMap_apply, rescale_constantSeries]

/-- The exponent minus one is the inverse formal unit base. -/
theorem binomial_subst_neg_one (g : PowerSeries ℂ)
    (hg : PowerSeries.constantCoeff g = 0) :
    (PowerSeries.binomialSeries ℝ (-1 : ℝ)).subst g = (1 + g)⁻¹ := by
  have hne : (1 + g) ≠ 0 := by
    intro heq
    have h := congrArg PowerSeries.constantCoeff heq
    simp [hg] at h
  apply mul_left_cancel₀ hne
  have h := binomial_subst_shift (0 : ℝ) g hg
  rw [show (0 : ℝ) - 1 = -1 by ring, PowerSeries.binomialSeries_zero] at h
  rw [PowerSeries.mul_inv_cancel _ (by simp [hg])]
  have hone : (1 : PowerSeries ℝ).subst g = (1 : PowerSeries ℂ) := by
    simpa using subst_C_algebra (1 : ℝ) g
      (PowerSeries.HasSubst.of_constantCoeff_zero' hg)
  rw [hone] at h
  exact h

/-- Negative natural exponents are powers of the inverse formal base. -/
theorem binomial_subst_neg_nat (k : ℕ) (g : PowerSeries ℂ)
    (hg : PowerSeries.constantCoeff g = 0) :
    (PowerSeries.binomialSeries ℝ (-(k : ℝ))).subst g = ((1 + g)⁻¹) ^ k := by
  induction k with
  | zero =>
      simp only [Nat.cast_zero, neg_zero, PowerSeries.binomialSeries_zero, pow_zero]
      simpa using subst_C_algebra (1 : ℝ) g
        (PowerSeries.HasSubst.of_constantCoeff_zero' hg)
  | succ k ih =>
      rw [show -((k + 1 : ℕ) : ℝ) = -(k : ℝ) + (-1) by push_cast; ring,
        ← binomial_subst_add _ _ _ hg, ih, binomial_subst_neg_one g hg, pow_succ]

/-- Finite root factorization evaluated in an arbitrary complex formal series. -/
theorem aeval_series_eq_prod_indexedRoots {p : ℝ[X]} (hs : p.Splits) (g : PowerSeries ℂ) :
    Polynomial.aeval g p = PowerSeries.C (p.leadingCoeff : ℂ) *
      ∏ j ∈ Finset.range p.natDegree, (g - PowerSeries.C (indexedRoots p j : ℂ)) := by
  conv_lhs => rw [eq_prod_indexedRoots hs]
  have hc (r : ℝ) : algebraMap ℝ ℂ r = (r : ℂ) := rfl
  simp only [map_mul, map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    PowerSeries.algebraMap_apply, hc]

/-- Finite root factorization evaluated at the fixed complex parameter. -/
theorem aeval_eq_prod_indexedRoots {p : ℝ[X]} (hs : p.Splits) (u : ℂ) :
    Polynomial.aeval u p = (p.leadingCoeff : ℂ) *
      ∏ j ∈ Finset.range p.natDegree, (u - (indexedRoots p j : ℂ)) := by
  conv_lhs => rw [eq_prod_indexedRoots hs]
  have hc (r : ℝ) : algebraMap ℝ ℂ r = (r : ℂ) := rfl
  simp only [map_mul, map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hc]

/-- Pairing a split polynomial produces the finite product of paired-root kernel factors. -/
theorem polynomial_formalFlow_pair {p : ℝ[X]} (hs : p.Splits) (u : ℂ)
    (hur : ∀ j < p.natDegree, u - (indexedRoots p j : ℂ) ≠ 0) :
    Polynomial.aeval (formalFlow u) p *
        PowerSeries.rescale (-1) (Polynomial.aeval (formalFlow u) p) =
      PowerSeries.C ((Polynomial.aeval u p) ^ 2) *
        (∏ j ∈ Finset.range p.natDegree,
          (1 - PowerSeries.C (pairedParameter u (indexedRoots p j)) * S ^ 2)) *
        (PowerSeries.binomialSeries ℝ (-(p.natDegree : ℝ))).subst
          (-PowerSeries.C (u ^ 2) * S ^ 2) := by
  rw [rescale_aeval_series, aeval_series_eq_prod_indexedRoots hs,
    aeval_series_eq_prod_indexedRoots hs]
  have hprod : (∏ j ∈ Finset.range p.natDegree,
      ((formalFlow u - PowerSeries.C (indexedRoots p j : ℂ)) *
        (PowerSeries.rescale (-1) (formalFlow u) -
          PowerSeries.C (indexedRoots p j : ℂ)))) =
      (∏ j ∈ Finset.range p.natDegree,
        (PowerSeries.C ((u - (indexedRoots p j : ℂ)) ^ 2) *
          (1 - PowerSeries.C (pairedParameter u (indexedRoots p j)) * S ^ 2) *
          (1 - PowerSeries.C (u ^ 2) * S ^ 2)⁻¹)) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact formalFlow_root_pair u _ (hur j (Finset.mem_range.mp hj))
  have hpair : (PowerSeries.C (p.leadingCoeff : ℂ) *
      ∏ j ∈ Finset.range p.natDegree, (formalFlow u -
        PowerSeries.C (indexedRoots p j : ℂ))) *
      (PowerSeries.C (p.leadingCoeff : ℂ) *
      ∏ j ∈ Finset.range p.natDegree, (PowerSeries.rescale (-1) (formalFlow u) -
        PowerSeries.C (indexedRoots p j : ℂ))) =
      PowerSeries.C (p.leadingCoeff : ℂ) ^ 2 *
        ∏ j ∈ Finset.range p.natDegree, ((formalFlow u -
          PowerSeries.C (indexedRoots p j : ℂ)) *
          (PowerSeries.rescale (-1) (formalFlow u) -
            PowerSeries.C (indexedRoots p j : ℂ))) := by
    rw [Finset.prod_mul_distrib]
    ring
  rw [hpair, hprod]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [binomial_subst_neg_nat _ _ (by simp),
    show (1 + -PowerSeries.C (u ^ 2) * S ^ 2) =
      1 - PowerSeries.C (u ^ 2) * S ^ 2 by ring]
  rw [← map_prod, Finset.prod_pow, aeval_eq_prod_indexedRoots hs, mul_pow]
  simp only [map_mul, map_pow]
  ring

end RealRooted.TuranHurwitz
