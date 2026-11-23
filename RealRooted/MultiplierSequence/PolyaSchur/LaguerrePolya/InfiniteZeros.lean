module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.RootDivision

/-!
# Polynomial factors from infinitely many LP zeros

An LP function with infinitely many distinct real zeros admits real-rooted
polynomial factors of every prescribed degree, with LP cofactors. No growth
bound or canonical-product representation is required.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- Removing one real zero leaves infinitely many others and a nonzero value at zero. -/
private theorem exists_sub_mul_of_infinite_zeros {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hf0 : f 0 ≠ 0)
    (hinf : Set.Infinite {r : ℝ | f r = 0}) :
    ∃ (r : ℝ) (g : ℂ → ℂ), r ≠ 0 ∧ IsLaguerrePolya g ∧ g 0 ≠ 0 ∧
      Set.Infinite {u : ℝ | g u = 0} ∧ ∀ z, f z = (z - r) * g z := by
  obtain ⟨r, hr⟩ := hinf.nonempty
  have hr0 : r ≠ 0 := by intro hz; subst r; exact hf0 (by simpa using hr)
  let g := dslope f (r : ℂ)
  have hfactor (z : ℂ) : f z = (z - r) * g z := by
    simpa only [smul_eq_mul] using (sub_smul_dslope_of_zero hr z).symm
  have hg0 : g 0 ≠ 0 := by
    intro hzero
    exact hf0 (by rw [hfactor, hzero, mul_zero])
  refine ⟨r, g, hr0, hf.dslope_of_eq_zero hr, hg0, ?_, hfactor⟩
  apply (hinf.sdiff (Set.finite_singleton r)).mono
  intro u hu
  have hur : u ≠ r := by simpa using hu.2
  have hne : (u : ℂ) - r ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hur)
  have hprod : ((u : ℂ) - r) * g u = 0 := by rw [← hfactor]; exact hu.1
  exact (mul_eq_zero.mp hprod).resolve_left hne

/-- Infinitely many real LP zeros supply polynomial factors of any exact
degree, with LP cofactors and both factors nonzero at the origin. -/
theorem IsLaguerrePolya.exists_polynomial_factor_of_infinite_zeros {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hf0 : f 0 ≠ 0)
    (hinf : Set.Infinite {r : ℝ | f r = 0}) (N : ℕ) :
    ∃ (q : ℝ[X]) (g : ℂ → ℂ), q.Splits ∧ q.coeff 0 ≠ 0 ∧ q.natDegree = N ∧
      IsLaguerrePolya g ∧ g 0 ≠ 0 ∧ ∀ z, f z = (q.map ofRealHom).eval z * g z := by
  induction N generalizing f with
  | zero =>
      exact ⟨1, f, Splits.one, by simp, by simp, hf, hf0, by simp⟩
  | succ N ih =>
      obtain ⟨r, g, hr, hg, hg0, hginf, hfactor⟩ :=
        exists_sub_mul_of_infinite_zeros hf hf0 hinf
      obtain ⟨q, t, hq, hq0, hdegree, ht, ht0, hgt⟩ := ih hg hg0 hginf
      have hqne : q ≠ 0 := by intro hz; simp [hz] at hq0
      refine ⟨(X - C r) * q, t, (Splits.X_sub_C r).mul hq, ?_, ?_, ht, ht0, ?_⟩
      · rw [coeff_zero_eq_eval_zero, eval_mul, eval_sub, eval_X, eval_C,
          zero_sub, ← coeff_zero_eq_eval_zero]
        exact mul_ne_zero (neg_ne_zero.mpr hr) hq0
      · rw [natDegree_mul (X_sub_C_ne_zero r) hqne, natDegree_X_sub_C, hdegree]
        lia
      · intro z
        rw [hfactor, hgt]
        simp [Polynomial.map_mul, Polynomial.map_sub, mul_assoc]

end RealRooted
