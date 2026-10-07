import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Examples

/-!
# The heat flow preserves real-rootedness

If `f` is a Laguerre–Pólya function of type I (a limit of polynomials with nonpositive roots),
then `z ↦ f (-a z²)` is a Laguerre–Pólya function for `a ≥ 0`: substituting `-a X²` into a
polynomial with nonpositive roots gives a real-rooted polynomial.  With `f = exp` this shows
that `exp (-a z²)` is in the Laguerre–Pólya class, so the heat operator `e^{-a D²}` maps
real-rooted polynomials to real-rooted polynomials (Pólya; see also Craven–Csordas).
-/

open Polynomial Filter Topology

noncomputable section

namespace RealRooted

/-- Substituting `-a X²` (with `a > 0`) into a polynomial whose roots are all `≤ 0` gives a
real-rooted polynomial. -/
theorem splits_comp_neg_C_mul_X_sq {p : ℝ[X]} (hp : p.Splits) (hroots : ∀ r ∈ p.roots, r ≤ 0)
    {a : ℝ} (ha : 0 < a) : (p.comp (C (-a) * X ^ 2)).Splits := by
  rw [hp.eq_prod_roots, mul_comp, C_comp, multiset_prod_comp, Multiset.map_map]
  refine (Splits.C _).mul (Splits.multisetProd fun q hq => ?_)
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
  set s := Real.sqrt (-r / a)
  have hs : a * s ^ 2 = -r := by
    rw [Real.sq_sqrt (div_nonneg (neg_nonneg.mpr (hroots r hr)) ha.le)]
    field_simp
  have hfac : (X - C r).comp (C (-a) * X ^ 2) = C (-a) * ((X - C s) * (X + C s)) := by
    have hr' : C r = -(C a * C s ^ 2) := by
      rw [← map_pow, ← map_mul, ← map_neg, hs, neg_neg]
    rw [sub_comp, X_comp, C_comp, hr', map_neg]
    ring
  rw [Function.comp_apply, hfac]
  exact (Splits.C _).mul ((Splits.of_natDegree_le_one (by compute_degree!)).mul
    (Splits.of_natDegree_le_one (by compute_degree!)))

/-- If `f` is Laguerre–Pólya of type I and `a ≥ 0`, then `z ↦ f (-a z²)` is Laguerre–Pólya. -/
theorem IsLaguerrePolyaTypeI.isLaguerrePolya_comp_neg_mul_sq {f : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) {a : ℝ} (ha : 0 ≤ a) :
    IsLaguerrePolya fun z => f (-(a : ℂ) * z ^ 2) := by
  obtain ⟨p, hp, hconv⟩ := hf
  refine ⟨fun n => (p n).comp (C (-a) * X ^ 2), fun n => ?_, ?_⟩
  · rcases hp n with ⟨-, h0 | hs, hroots⟩
    · left; simp [h0]
    rcases ha.lt_or_eq with ha | rfl
    · exact Or.inr (splits_comp_neg_C_mul_X_sq hs hroots ha)
    · right
      simp
  · have := hconv.comp (fun z : ℂ => -(a : ℂ) * z ^ 2) (by fun_prop)
    refine this.congr fun n z => ?_
    simp [Function.comp_apply, Polynomial.eval_map, map_comp]

/-- `exp (-a z²)` is a Laguerre–Pólya function for `a ≥ 0`. -/
theorem isLaguerrePolya_exp_neg_mul_sq {a : ℝ} (ha : 0 ≤ a) :
    IsLaguerrePolya fun z => Complex.exp (-(a : ℂ) * z ^ 2) :=
  isLaguerrePolyaTypeI_exp.isLaguerrePolya_comp_neg_mul_sq ha

/-- **The heat flow preserves real-rootedness**: `e^{-a D²}` maps real-rooted polynomials to
real-rooted polynomials (or zero) for `a ≥ 0`. -/
theorem taylorDifferentialOperator_exp_neg_mul_sq_eq_zero_or_splits {a : ℝ} (ha : 0 ≤ a)
    {g : ℝ[X]} (hg : g.Splits) :
    taylorDifferentialOperator (fun z => Complex.exp (-(a : ℂ) * z ^ 2)) g = 0 ∨
      (taylorDifferentialOperator (fun z => Complex.exp (-(a : ℂ) * z ^ 2)) g).Splits :=
  (isLaguerrePolya_exp_neg_mul_sq ha).taylorDifferentialOperator_eq_zero_or_splits hg

end RealRooted
