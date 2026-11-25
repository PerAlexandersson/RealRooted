module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatFlow
public import RealRooted.SimpleRoots
import RealRooted.CriticalValueContinuation
import RealRooted.IteratedDerivativeShift
import Mathlib.Tactic

/-!
# Scalar perturbations and simplicity under backward heat

Two opposite vertical shifts of a polynomial detect repeated real roots by
the strict Laguerre inequality. We apply this criterion to Taylor differential
operators with unit constant symbol, including backward heat at every time.
The argument generalizes the scalar perturbation proof for Schur–Szegő composition.

Source: the unpublished quartic-row argument in RealRooted issue #2649,
https://github.com/PerAlexandersson/RealRooted/issues/2649.
-/

public section

open Polynomial Filter Topology Finset

namespace RealRooted

/-- Small scalar shifts of a simple split polynomial continue to split. -/
theorem IsSimpleRealRooted.eventually_splits_add_C {p : ℝ[X]} (hp : IsSimpleRealRooted p) :
    ∀ᶠ u : ℝ in 𝓝 0, (p + C u).Splits := by
  by_cases hd : p.natDegree = 0
  · exact .of_forall fun u => Splits.of_natDegree_le_one (by simp [hd])
  obtain ⟨_, _, h⟩ := exists_eventually_polynomial_root_branches (fun u : ℝ => p + C u)
    (t := 0) (D := p.natDegree) hd (.of_forall fun _ => natDegree_add_C)
    (by simpa using hp.2.1) (by simpa using hp.2.2) (by
      intro x _
      simp only [eval_add, eval_C]
      exact (((Polynomial.contDiff_aeval p 1).comp contDiff_snd).add contDiff_fst).contDiffAt)
  exact h.mono fun _ hu => hu.1

/-- Two opposite nonzero scalar shifts that split exclude a repeated root at the midpoint. -/
theorem hasSimpleRoots_of_splits_add_C_of_splits_sub_C {p : ℝ[X]} (hp : p ≠ 0)
    {v : ℝ} (hv : v ≠ 0) (hpos : (p + C v).Splits) (hneg : (p + C (-v)).Splits) :
    HasSimpleRoots p := by
  by_cases hd : p.natDegree ≤ 1
  · exact hasSimpleRoots_of_natDegree_le_one hp hd
  intro r hr
  by_contra hm
  have hval : p.eval r = 0 := hr
  have hder : p.derivative.eval r = 0 :=
    ((one_lt_rootMultiplicity_iff_isRoot hp).1 (by
      have := (rootMultiplicity_pos hp).2 hr
      lia)).2
  have h₁ := deriv2_mul_lt_deriv_sq_at_non_root hpos (by rw [natDegree_add_C]; lia)
    (by rw [eval_add, eval_C, hval, zero_add]; exact hv)
  have h₂ := deriv2_mul_lt_deriv_sq_at_non_root hneg (by rw [natDegree_add_C]; lia)
    (by rw [eval_add, eval_C, hval, zero_add]; exact neg_ne_zero.mpr hv)
  simp only [derivative_add, derivative_C, add_zero, hder, eval_add, eval_C, hval, zero_add,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_neg] at h₁ h₂
  linarith

/-- A Taylor differential operator with normalized symbol commutes with scalar shifts. -/
theorem taylorDifferentialOperator_add_C {φ : ℂ → ℂ} (hφ : φ 0 = 1) (p : ℝ[X]) (v : ℝ) :
    taylorDifferentialOperator φ (p + C v) = taylorDifferentialOperator φ p + C v := by
  simp only [taylorDifferentialOperator, natDegree_add_C, sum_range_succ', iterate_map_add,
    iterate_derivative_C (Nat.succ_pos _), add_zero, Function.iterate_zero_apply,
    iteratedDeriv_zero, hφ, Nat.factorial_zero, Nat.cast_one, div_one, Complex.one_re,
    map_one, one_mul]
  abel

/-- The top coefficient is fixed by every Taylor differential operator with normalized symbol. -/
theorem coeff_taylorDifferentialOperator_natDegree {φ : ℂ → ℂ} (hφ : φ 0 = 1) (p : ℝ[X]) :
    (taylorDifferentialOperator φ p).coeff p.natDegree = p.leadingCoeff := by
  have h (k : ℕ) : (derivative^[k] (derivative p)).coeff p.natDegree = 0 := by
    rw [← Function.iterate_succ_apply, coeff_iterate_derivative,
      coeff_eq_zero_of_natDegree_lt (by lia), smul_zero]
  simp [taylorDifferentialOperator, sum_range_succ', h, hφ]

/-- Normalized Laguerre–Pólya differential operators preserve simple real-rootedness. -/
theorem IsLaguerrePolya.isSimpleRealRooted_taylorDifferentialOperator {φ : ℂ → ℂ}
    (hφ : IsLaguerrePolya φ) (h₀ : φ 0 = 1) {p : ℝ[X]} (hp : IsSimpleRealRooted p) :
    IsSimpleRealRooted (taylorDifferentialOperator φ p) := by
  have hne : taylorDifferentialOperator φ p ≠ 0 := by
    intro he
    have hh := coeff_taylorDifferentialOperator_natDegree h₀ p
    rw [he, coeff_zero] at hh
    exact (leadingCoeff_ne_zero.mpr hp.1) hh.symm
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp hp.eventually_splits_add_C
  have hs (u : ℝ) (hu : |u| < δ) : (taylorDifferentialOperator φ p + C u).Splits := by
    rw [← taylorDifferentialOperator_add_C h₀]
    exact hφ.taylorDifferentialOperator_splits (hb (by simpa [Real.dist_eq] using hu))
  have hhalf := half_pos hδ
  refine ⟨hne, hφ.taylorDifferentialOperator_splits hp.2.1,
    hasSimpleRoots_of_splits_add_C_of_splits_sub_C hne hhalf.ne' ?_ ?_⟩
  · exact hs _ (by simpa [abs_of_pos hhalf] using half_lt_self hδ)
  · exact hs _ (by simpa [abs_of_pos hhalf] using half_lt_self hδ)

/-- Backward heat preserves simplicity of all the real zeros, including at time zero. -/
theorem isSimpleRealRooted_taylorDifferentialOperator_exp_neg_mul_sq {h : ℝ} (hh : 0 ≤ h)
    {p : ℝ[X]} (hp : IsSimpleRealRooted p) :
    IsSimpleRealRooted (taylorDifferentialOperator (fun z => Complex.exp (-(h : ℂ) * z ^ 2)) p) :=
  (isLaguerrePolya_exp_neg_mul_sq hh).isSimpleRealRooted_taylorDifferentialOperator (by simp) hp

end RealRooted
