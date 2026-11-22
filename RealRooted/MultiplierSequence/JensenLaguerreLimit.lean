module

public import RealRooted.MultiplierSequence.JensenLaguerre
import Mathlib.Topology.Algebra.Order.Polynomial
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real
import RealRooted.PFPolynomial.Closure

/-!
# The Laguerre Jensen criterion

Dividing the factorial-normalized Laguerre transform by the parameter to the
degree gives the original Jensen polynomial in the limit. Closedness of real
splitting proves the converse to finite Laguerre transfer. No sign or
nonvanishing hypothesis on the coefficient sequence is required.
-/

public section

open Polynomial Filter Topology

namespace RealRooted

/-- Only the term with no degree loss survives normalization at infinity. -/
private theorem tendsto_laguerrePochhammer_div_pow (d r : ℕ) (hr : r ≤ d) :
    Tendsto (fun alpha : ℝ =>
      (ascPochhammer ℝ (d - r)).eval (alpha + r + 1) / alpha ^ d)
      atTop (𝓝 (if r = 0 then 1 else 0)) := by
  let p : ℝ[X] := (ascPochhammer ℝ (d - r)).comp (X + C ((r : ℝ) + 1))
  have hp : p.Monic := (monic_ascPochhammer (S := ℝ) (d - r)).comp
    (monic_X_add_C _) (by rw [natDegree_X_add_C]; exact one_ne_zero)
  have hdeg : p.natDegree = d - r := by
    simp only [p, natDegree_comp, ascPochhammer_natDegree, natDegree_X_add_C, mul_one]
  by_cases hr0 : r = 0
  · subst r
    have hlim := p.tendsTo_atTop_div_nhds_leadingCoeff
    simp only [hdeg, Nat.sub_zero, hp.leadingCoeff] at hlim
    simpa [p, eval_comp, add_assoc] using hlim
  · have hlt : p.degree < (X ^ d : ℝ[X]).degree := by
      rw [degree_eq_natDegree hp.ne_zero, hdeg, degree_X_pow]
      exact_mod_cast (Nat.sub_lt (by lia) (Nat.pos_of_ne_zero hr0))
    simpa [p, hr0, eval_comp, add_assoc] using
      Polynomial.div_tendsto_atTop_zero_of_degree_lt hlt

/-- The normalized Laguerre coefficients converge to the Jensen coefficients
as the Laguerre parameter tends to positive infinity. -/
theorem tendsto_coeff_laguerreJensenPolynomial_div (d k : ℕ) (gamma : ℕ → ℝ) :
    Tendsto (fun alpha : ℝ =>
      (laguerreJensenPolynomial d gamma alpha).coeff k / alpha ^ d)
      atTop (𝓝 ((jensenPolynomial d gamma).coeff k)) := by
  by_cases hk : k ≤ d
  · have hsum := tendsto_finsetSum (Finset.range (k + 1)) (fun r hr =>
      (tendsto_laguerrePochhammer_div_pow d r
        ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)).trans hk)).const_mul
        ((k.choose r : ℝ) * (-1 : ℝ) ^ r * gamma (k - r)))
    simpa [coeff_laguerreJensenPolynomial, coeff_jensenPolynomial, hk,
      mul_div_assoc, Finset.sum_div] using hsum.const_mul (d.choose k : ℝ)
  · simp only [coeff_laguerreJensenPolynomial, coeff_jensenPolynomial, ite_eq_right hk,
      zero_div]
    exact tendsto_const_nhds

/-- It is enough to test the Laguerre family at nonnegative integer parameters
to recover splitting of the original Jensen polynomial. -/
theorem jensenPolynomial_splits_of_laguerreJensenPolynomial
    {d : ℕ} {gamma : ℕ → ℝ}
    (h : ∀ n : ℕ, (laguerreJensenPolynomial d gamma n).Splits) :
    (jensenPolynomial d gamma).Splits := by
  let q : ℕ → ℝ[X] := fun n =>
    C (((n : ℝ) ^ d)⁻¹) * laguerreJensenPolynomial d gamma n
  have hdeg (n : ℕ) : (q n).natDegree ≤ d :=
    (natDegree_C_mul_le _ _).trans (natDegree_laguerreJensenPolynomial_le d gamma n)
  have hsplit (n : ℕ) : q n = 0 ∨ (q n).Splits := .inr ((h n).C_mul _)
  have hcoeff (k : ℕ) : Tendsto (fun n => (q n).coeff k) atTop
      (𝓝 ((jensenPolynomial d gamma).coeff k)) := by
    simpa [q, coeff_C_mul, div_eq_mul_inv, mul_comm, Function.comp_def] using
      (tendsto_coeff_laguerreJensenPolynomial_div d k gamma).comp
        tendsto_natCast_atTop_atTop
  have heval (z : ℂ) : Tendsto (fun n => ((q n).map Complex.ofRealHom).eval z)
      atTop (𝓝 (((jensenPolynomial d gamma).map Complex.ofRealHom).eval z)) := by
    refine Polynomial.tendsto_eval_of_coeff_tendsto_of_natDegree_le
      (N := d) (fun n => by simpa using hdeg n)
      (by simpa using natDegree_jensenPolynomial_le d gamma) ?_ z
    intro k
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp (hcoeff k)
  rcases Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le
      hdeg hsplit heval with hzero | hreal
  · rw [hzero]
    exact Splits.zero
  · exact hreal

/-- A finite Jensen polynomial splits exactly when all its Laguerre transforms
split throughout the extended parameter range. -/
theorem jensenPolynomial_splits_iff_laguerreJensenPolynomial
    (d : ℕ) (gamma : ℕ → ℝ) :
    (jensenPolynomial d gamma).Splits ↔
      ∀ alpha : ℝ, -2 ≤ alpha → (laguerreJensenPolynomial d gamma alpha).Splits := by
  constructor
  · intro h alpha halpha
    exact laguerreJensenPolynomial_splits h halpha
  · intro h
    exact jensenPolynomial_splits_of_laguerreJensenPolynomial
      (fun n => h n (le_trans (by norm_num) (Nat.cast_nonneg n)))

end RealRooted
