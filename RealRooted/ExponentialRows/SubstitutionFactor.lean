module

public import RealRooted.PFPolynomial
import RealRooted.OperatorInterlacingUpgrade
import RealRooted.PFPolynomial.PreserverClosure
import RealRooted.PFPolynomial.Closure
import RealRooted.JensenPencilContraction
import RealRooted.Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

/-!
# Interlacing upgrade from positive factors

We isolate the bounded-degree, zero-aware extension of the positive-factor
induction used for exponential substitution. This includes degree drops and
vanishing images. Source: unpublished manuscript, degree-raising substitutions,
RealRooted issue #2415, round four.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- Positive translation makes every nonzero PF input image nonzero, so the
linear-factor upgrade applies without a zero-root boundary. -/
private theorem strictInterl_map_comp_X_add_C
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {D : ℕ}
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hmap : ∀ {p}, IsPFPolynomial p → p.natDegree ≤ D → IsPFPolynomial (T p))
    (hfactor : ∀ {p}, IsPFPolynomial p → 0 < p.coeff 0 → p.natDegree < D →
      ∀ r : ℝ, 0 < r → StrictInterl (T p) (T ((X + C r) * p)))
    {f g : ℝ[X]} (hstrict : StrictInterl f g)
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hgdeg : g.natDegree ≤ D)
    (eps : ℝ) (heps : 0 < eps) :
    StrictInterl (T (f.comp (X + C eps))) (T (g.comp (X + C eps))) := by
  classical
  let U : ℝ[X] →ₗ[ℝ] ℝ[X] := T.comp (Polynomial.aeval (X + C eps)).toLinearMap
  have hU (p : ℝ[X]) : U p = T (p.comp (X + C eps)) := by
    simp only [U, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      ← Polynomial.comp_eq_aeval]
  have hUpf {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ D) :
      IsPFPolynomial (U p) ∧ U p ≠ 0 := by
    have htrans := hp.comp_X_add_C_and_coeff_zero_pos hp0 heps
    have hpos : 0 < (U p).coeff 0 := by rw [hU, hTc]; exact htrans.2
    refine ⟨?_, ?_⟩
    · rw [hU]
      exact hmap htrans.1 (by
        simpa only [natDegree_comp, natDegree_X_add_C, mul_one] using hpdeg)
    · intro hz
      simp only [hz, coeff_zero, lt_self_iff_false] at hpos
  apply strictInterl_map_of_pfLinearFactor (T := U) (D := D)
    hstrict hf.hasNonnegCoeffs hg.hasNonnegCoeffs hgdeg
  · intro p hp
    rw [hU]
    apply hTnn
    rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def]
    exact hasNonnegCoeffs_finsetSum _ _ fun n _ =>
      hasNonnegCoeffs_C_mul (hp n) ((hasNonnegCoeffs_X_add_C heps.le).pow n)
  · intro p hp hp0 hpdeg
    exact ⟨(hUpf hp hp0 hpdeg).2, (hUpf hp hp0 hpdeg).1.splits⟩
  · intro p r hp hp0 hr hpdeg
    have ht := hp.comp_X_add_C_and_coeff_zero_pos hp0 heps
    have H := hfactor ht.1 ht.2 (by
      have hpne : p ≠ 0 := hp0
      rw [natDegree_mul (X_add_C_ne_zero r) hpne, natDegree_X_add_C] at hpdeg
      rw [natDegree_comp, natDegree_X_add_C, mul_one]
      lia) (r + eps) (by linarith)
    simpa only [hU, mul_comp, add_comp, X_comp, C_comp, map_add, add_assoc,
      add_left_comm, add_comm] using H

/-- Positive-constant linear-factor edges suffice to preserve directed PF
interlacing through a fixed degree. Translation and bounded-degree limits
include inputs with roots at zero and vanishing images. -/
theorem interl_map_of_pos_constant_factor
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {D : ℕ}
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hTdeg : ∀ p, (T p).natDegree ≤ p.natDegree)
    (hmap : ∀ {p}, IsPFPolynomial p → p.natDegree ≤ D → IsPFPolynomial (T p))
    (hfactor : ∀ {p}, IsPFPolynomial p → 0 < p.coeff 0 → p.natDegree < D →
      ∀ r : ℝ, 0 < r → StrictInterl (T p) (T ((X + C r) * p)))
    {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfdeg : f.natDegree ≤ D) (hgdeg : g.natDegree ≤ D)
    (hfg : Interl f g) : Interl (T f) (T g) := by
  classical
  by_cases hf0 : f = 0
  · simp only [hf0, map_zero]
    exact interl_zero_left _
  by_cases hg0 : g = 0
  · simp only [hg0, map_zero]
    exact interl_zero_right _
  have hstrict := hfg.toStrictInterl_of_ne hf0 hg0
  have heps := strictInterl_map_comp_X_add_C T hTnn hTc hmap hfactor
    hstrict hf hg hgdeg
  let eps : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hepspos (n : ℕ) : 0 < eps n := by dsimp [eps]; positivity
  have hepslim : Filter.Tendsto eps Filter.atTop (nhds 0) := by
    simpa only [eps, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlim (p : ℝ[X]) : ∀ j, Filter.Tendsto
      (fun n => (T (p.comp (X + C (eps n)))).coeff j) Filter.atTop
      (nhds ((T p).coeff j)) := by
    apply tendsto_coeff_linearMap_apply_of_coeff_tendsto T (d := p.natDegree)
    · intro n
      simp only [natDegree_comp, natDegree_X_add_C, mul_one, le_refl]
    · intro j
      simpa only [Function.comp_def, C_0, add_zero, comp_X] using
        (p.continuous_coeff_comp_X_add_C j).tendsto 0 |>.comp hepslim
  apply interl_of_pf_coeff_tendsto_of_natDegree_le (N := max f.natDegree g.natDegree)
    (fun n => hmap (hf.comp_X_add_C_and_coeff_zero_pos hf0 (hepspos n)).1
      (by simpa only [natDegree_comp, natDegree_X_add_C, mul_one] using hfdeg))
    (fun n => hmap (hg.comp_X_add_C_and_coeff_zero_pos hg0 (hepspos n)).1
      (by simpa only [natDegree_comp, natDegree_X_add_C, mul_one] using hgdeg))
    (fun n => (heps _ (hepspos n)).toInterl)
  · intro n
    apply (hTdeg _).trans
    simpa only [natDegree_comp, natDegree_X_add_C, mul_one] using
      (le_max_left f.natDegree g.natDegree)
  · intro n
    apply (hTdeg _).trans
    simpa only [natDegree_comp, natDegree_X_add_C, mul_one] using
      (le_max_right f.natDegree g.natDegree)
  · exact hlim f
  · exact hlim g

end RealRooted.ExponentialRows
