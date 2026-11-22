module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.RootDivision
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros
import TauCeti.Analysis.Analytic.ExtractZeros

/-!
# Removing all zeros of an LP function with finitely many zeros

An LP function nonzero at the origin and with finitely many distinct real
zeros is a real-rooted polynomial times a zero-free LP function. Each zero is
removed with its full analytic multiplicity. No growth bound is imposed.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- Removing a full analytic zero leaves an entire LP cofactor nonzero there. -/
private theorem extract_full_real_zero {f : ℂ → ℂ} (hf : IsLaguerrePolya f)
    (hf0 : f 0 ≠ 0) (r : ℝ) :
    ∃ (m : ℕ) (g : ℂ → ℂ), IsLaguerrePolya g ∧ g 0 ≠ 0 ∧ g r ≠ 0 ∧
      ∀ z, f z = (z - r) ^ m * g z := by
  have ha : AnalyticOnNhd ℂ f Set.univ := hf.analyticOnNhd
  have hfinite : analyticOrderAt f (r : ℂ) ≠ ⊤ :=
    ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ (0 : ℂ)) (Set.mem_univ (r : ℂ))
      (by simp [analyticOrderAt_eq_zero.mpr (.inr hf0)])
  let m := analyticOrderNatAt f (r : ℂ)
  obtain ⟨g, hg, hfg⟩ := ha.exists_eq_prod_pow_smul {(r : ℂ)} (fun _ => m)
    (by simpa [m] using (Nat.cast_analyticOrderNatAt hfinite).le)
  have hfactor (z : ℂ) : f z = (z - r) ^ m * g z := by simpa using hfg z
  have hga : AnalyticAt ℂ g (r : ℂ) := hg _ (Set.mem_univ _)
  have heq : f = (· - (r : ℂ)) ^ m * g := by
    funext z
    simpa only [Pi.mul_apply, Pi.pow_apply] using hfactor z
  have horder : (m : ℕ∞) + analyticOrderAt g (r : ℂ) = m := by
    calc
      _ = analyticOrderAt ((· - (r : ℂ)) ^ m * g) (r : ℂ) := by
        rw [analyticOrderAt_mul (by fun_prop) hga, analyticOrderAt_centeredMonomial]
      _ = analyticOrderAt f (r : ℂ) := by rw [← heq]
      _ = (m : ℕ∞) := by simpa [m] using (Nat.cast_analyticOrderNatAt hfinite).symm
  have hgr : g r ≠ 0 := hga.analyticOrderAt_eq_zero.mp
    (ENat.add_right_injective_of_ne_top (ENat.natCast_ne_top m)
      (horder.trans (add_zero _).symm))
  have hg0 : g 0 ≠ 0 := by
    intro hz
    exact hf0 (by rw [hfactor, hz, mul_zero])
  have hLP : IsLaguerrePolya (fun z => (z - r) ^ m * g z) := by
    rw [show (fun z => (z - r) ^ m * g z) = f from (funext hfactor).symm]
    exact hf
  exact ⟨m, g, hLP.of_sub_pow_mul r m (differentiableOn_univ.mp hg.differentiableOn),
    hg0, hgr, hfactor⟩

/-- Finite zero-set containment suffices for complete extraction. -/
private theorem exists_factor_of_zero_set_subset (s : Finset ℝ) {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hf0 : f 0 ≠ 0)
    (hzeros : ∀ r : ℝ, f r = 0 → r ∈ s) :
    ∃ (q : ℝ[X]) (g : ℂ → ℂ), q.Splits ∧ q.coeff 0 ≠ 0 ∧ IsLaguerrePolya g ∧
      (∀ z, g z ≠ 0) ∧ ∀ z, f z = (q.map ofRealHom).eval z * g z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
      refine ⟨1, f, Splits.one, by simp, hf, ?_, by simp⟩
      intro z hz
      have hfn : f ≠ 0 := fun h => hf0 (by simp [h])
      have him := hf.im_eq_zero_of_eq_zero hfn hz
      have hreal : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
      have hr := hzeros z.re (by rwa [hreal])
      exact Finset.notMem_empty _ hr
  | @insert r s hrs ih =>
      by_cases hr : f r = 0
      · have hr0 : r ≠ 0 := by intro hz; subst r; exact hf0 (by simpa using hr)
        obtain ⟨m, g, hg, hg0, hgr, hfactor⟩ := extract_full_real_zero hf hf0 r
        have hsubset : ∀ u : ℝ, g u = 0 → u ∈ s := by
          intro u hu
          have hfu : f u = 0 := by rw [hfactor, hu, mul_zero]
          rcases Finset.mem_insert.mp (hzeros u hfu) with hur | hus
          · subst u
            exact (hgr hu).elim
          · exact hus
        obtain ⟨q, t, hq, hq0, ht, htnz, hgt⟩ := ih hg hg0 hsubset
        refine ⟨(X - C r) ^ m * q, t, ((Splits.X_sub_C r).pow m).mul hq,
          ?_, ht, htnz, ?_⟩
        · rw [coeff_zero_eq_eval_zero, eval_mul, eval_pow, eval_sub, eval_X, eval_C,
            zero_sub, ← coeff_zero_eq_eval_zero]
          exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hr0)) hq0
        · intro z
          rw [hfactor, hgt]
          simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, mul_assoc]
      · apply ih hf hf0
        intro u hu
        rcases Finset.mem_insert.mp (hzeros u hu) with hur | hus
        · subst u
          exact (hr hu).elim
        · exact hus

/-- An LP function with finitely many distinct real zeros and nonzero initial
value is a real-rooted polynomial times a zero-free LP function. -/
theorem IsLaguerrePolya.exists_polynomial_factor_of_finite_zeros {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hf0 : f 0 ≠ 0)
    (hfin : Set.Finite {r : ℝ | f r = 0}) :
    ∃ (q : ℝ[X]) (g : ℂ → ℂ), q.Splits ∧ q.coeff 0 ≠ 0 ∧ IsLaguerrePolya g ∧
      (∀ z, g z ≠ 0) ∧ ∀ z, f z = (q.map ofRealHom).eval z * g z := by
  classical
  exact exists_factor_of_zero_set_subset hfin.toFinset hf hf0
    (fun r hr => hfin.mem_toFinset.mpr hr)

end RealRooted
