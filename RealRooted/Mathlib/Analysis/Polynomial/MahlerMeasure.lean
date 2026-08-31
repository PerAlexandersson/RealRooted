import Mathlib.Analysis.Polynomial.MahlerMeasure

/-!
# Coefficient bounds from the Mahler measure

Upstream-shaped consequences of the standard coefficient/Mahler-measure
estimate for complex polynomials whose roots lie in the closed unit disk.
-/

open Polynomial

noncomputable section

namespace Polynomial

theorem norm_coeff_le_choose_of_monic_of_roots_norm_le_one
    {p : ℂ[X]} {n k : ℕ} (hp : p.Monic)
    (hdeg : p.natDegree = n)
    (hroots : ∀ z ∈ p.roots, ‖z‖ ≤ 1) :
    ‖p.coeff k‖ ≤ Nat.choose n k := by
  have hmeasure : p.mahlerMeasure = 1 := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hp.leadingCoeff]
    simp only [norm_one, one_mul]
    apply Multiset.prod_eq_one
    simp_all
  have hbound := norm_coeff_le_choose_mul_mahlerMeasure k p
  simp_all

theorem norm_coeff_le_choose_of_leadingCoeff_norm_one_of_roots_norm_le_one
    {p : ℂ[X]} {n k : ℕ} (hlead : ‖p.leadingCoeff‖ = 1)
    (hdeg : p.natDegree = n)
    (hroots : ∀ z ∈ p.roots, ‖z‖ ≤ 1) :
    ‖p.coeff k‖ ≤ Nat.choose n k := by
  have hmeasure : p.mahlerMeasure = 1 := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hlead, one_mul]
    apply Multiset.prod_eq_one
    simp_all
  have hbound := norm_coeff_le_choose_mul_mahlerMeasure k p
  simp_all

end Polynomial
