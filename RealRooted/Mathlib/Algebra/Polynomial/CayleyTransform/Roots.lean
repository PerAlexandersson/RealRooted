import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Algebra
import RealRooted.Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Root geometry of the finite-degree Cayley transform

Transport from the vertical line of real part minus one half to the unit circle,
with the resulting degree, leading-coefficient, and coefficient estimates.
-/

open Polynomial

noncomputable section

namespace Polynomial

private lemma one_add_ne_zero_of_re_eq_neg_half {r : ℂ}
    (hr : r.re = -1 / 2) : 1 + r ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp at hre
  linarith

/-- Cayley homogenization sends every root on `re z = -1/2` to a root on
the unit circle. -/
theorem cayleyTransform_root_norm_eq_one
    {p : ℂ[X]} {n : ℕ} (hp0 : p ≠ 0) (hp : p.Splits)
    (hdeg : p.natDegree = n)
    (hline : ∀ r ∈ p.roots, r.re = -1 / 2)
    {z : ℂ} (hz : z ∈ (cayleyTransform n p).roots) :
    ‖z‖ = 1 := by
  rw [cayleyTransform_eq_rootFactorProduct hp hdeg,
    roots_C_mul _ (leadingCoeff_ne_zero.mpr hp0)] at hz
  let factors : Multiset ℂ[X] :=
    p.roots.map (fun r => (1 + C r) * X - C r)
  have hfactors : 0 ∉ factors := by
    intro hzero
    rcases Multiset.mem_map.mp hzero with ⟨r, hr, heq⟩
    simp_all
  rw [show p.roots.map (fun r => (1 + C r) * X - C r) = factors from rfl,
    roots_multiset_prod factors hfactors] at hz
  rcases Multiset.mem_bind.mp hz with ⟨f, hf, hzf⟩
  rcases Multiset.mem_map.mp hf with ⟨r, hr, rfl⟩
  have hden := one_add_ne_zero_of_re_eq_neg_half (hline r hr)
  rw [show (1 + C r) * X - C r = C (1 + r) * X - C r by
    simp, roots_C_mul_X_sub_C r hden] at hzf
  have hzform : z = (1 + r)⁻¹ * r := by simpa using hzf
  rw [hzform, norm_mul, norm_inv]
  have hnorm : ‖r‖ = ‖1 + r‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    grind
  simp_all

theorem cayleyTransform_splits
    {p : ℂ[X]} {n : ℕ} (hp : p.Splits) (hdeg : p.natDegree = n) :
    (cayleyTransform n p).Splits := by
  rw [cayleyTransform_eq_rootFactorProduct hp hdeg]
  apply (Polynomial.Splits.C _).mul
  apply Polynomial.Splits.multisetProd
  intro f hf
  rcases Multiset.mem_map.mp hf with ⟨r, _, rfl⟩
  exact Polynomial.Splits.of_natDegree_le_one (by compute_degree!)

theorem cayleyTransform_coeff_zero
    {p : ℂ[X]} {n : ℕ} (hp : p.Splits) (hdeg : p.natDegree = n) :
    (cayleyTransform n p).coeff 0 = p.coeff 0 := by
  rw [cayleyTransform_eq_rootFactorProduct hp hdeg]
  rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero,
    eval_mul, eval_C, eval_multiset_prod]
  rw [hp.eval_eq_prod_roots]
  simp

theorem cayleyTransform_natDegree
    {p : ℂ[X]} {n : ℕ} (hp0 : p ≠ 0) (hp : p.Splits)
    (hdeg : p.natDegree = n)
    (hline : ∀ r ∈ p.roots, r.re = -1 / 2) :
    (cayleyTransform n p).natDegree = n := by
  rw [cayleyTransform_eq_rootFactorProduct hp hdeg,
    natDegree_C_mul (leadingCoeff_ne_zero.mpr hp0)]
  let factors : Multiset ℂ[X] :=
    p.roots.map (fun r => (1 + C r) * X - C r)
  have hfactors : 0 ∉ factors := by
    intro hzero
    rcases Multiset.mem_map.mp hzero with ⟨r, hr, heq⟩
    have hcoeff := congrArg (fun q : ℂ[X] ↦ q.coeff 1) heq
    have hden := one_add_ne_zero_of_re_eq_neg_half (hline r hr)
    simp at hcoeff
    simp_all
  rw [show p.roots.map (fun r ↦ (1 + C r) * X - C r) = factors from rfl,
    natDegree_multiset_prod factors hfactors]
  have hdegrees : factors.map Polynomial.natDegree = p.roots.map (fun _ ↦ 1) := by
    simp only [factors, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro r hr
    dsimp
    have hden := one_add_ne_zero_of_re_eq_neg_half (hline r hr)
    compute_degree!
  rw [hdegrees]
  simp [← hp.natDegree_eq_card_roots, hdeg]

/-- Unit-circle roots and a unit constant coefficient force the Cayley
homogenization to have unit-norm leading coefficient. -/
theorem cayleyTransform_leadingCoeff_norm_eq_one
    {p : ℂ[X]} {n : ℕ} (hp0 : p ≠ 0) (hp : p.Splits)
    (hdeg : p.natDegree = n)
    (hline : ∀ r ∈ p.roots, r.re = -1 / 2)
    (hconst : ‖p.coeff 0‖ = 1) :
    ‖(cayleyTransform n p).leadingCoeff‖ = 1 := by
  let q := cayleyTransform n p
  have hqsplit : q.Splits := cayleyTransform_splits hp hdeg
  have hqdeg : q.natDegree = n :=
    cayleyTransform_natDegree hp0 hp hdeg hline
  have hqroot : ∀ z ∈ q.roots, ‖z‖ = 1 := by
    intro z hz
    exact cayleyTransform_root_norm_eq_one hp0 hp hdeg hline hz
  have hprod : ‖q.roots.prod‖ = 1 := by
    let normHom : ℂ →* ℝ :=
      { toFun := norm
        map_one' := norm_one
        map_mul' := norm_mul }
    change normHom q.roots.prod = 1
    rw [map_multiset_prod]
    apply Multiset.prod_eq_one
    intro a ha
    rcases Multiset.mem_map.mp ha with ⟨z, hz, rfl⟩
    exact hqroot z hz
  have hformula := hqsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots
  have hqconst : ‖q.coeff 0‖ = 1 := by
    rw [cayleyTransform_coeff_zero hp hdeg]
    simp_all
  rw [hformula, norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, hprod, mul_one] at hqconst
  grind

/-- Coefficient bound obtained by transporting a vertical-line polynomial to
the unit circle and applying the Mahler/Vieta estimate. -/
theorem norm_coeff_cayleyTransform_le_choose
    {p : ℂ[X]} {n k : ℕ} (hp0 : p ≠ 0) (hp : p.Splits)
    (hdeg : p.natDegree = n)
    (hline : ∀ r ∈ p.roots, r.re = -1 / 2)
    (hconst : ‖p.coeff 0‖ = 1) :
    ‖(cayleyTransform n p).coeff k‖ ≤ Nat.choose n k := by
  apply norm_coeff_le_choose_of_leadingCoeff_norm_one_of_roots_norm_le_one
    (cayleyTransform_leadingCoeff_norm_eq_one hp0 hp hdeg hline hconst)
    (cayleyTransform_natDegree hp0 hp hdeg hline)
  intro z hz
  exact (cayleyTransform_root_norm_eq_one hp0 hp hdeg hline hz).le


end Polynomial
