import RealRooted.Hadamard.FiniteReflection
import RealRooted.MultiplierSequence.PolyaSchur.Factorial

/-!
# Schur's factorial product theorem

Human statement: https://www.symmetricfunctions.com/realRooted.htm#hadamardProductTheorems,
the theorem of Schur after the Liu--Mao Hadamard results.  The distinct-zeros
refinement stated there is not formalized here.

If `f = ∑ aₖ xᵏ` is real-rooted and `g = ∑ bₖ xᵏ` is real-rooted with all zeros
of one sign, then `∑ k! aₖ bₖ xᵏ` is zero or real-rooted (I. Schur, 1914; see
also P. Brändén, "On linear transformations preserving the Pólya frequency
property", Thm. 1).

For a PF polynomial `g`, the factorial-weighted sequence `k! bₖ` is a
multiplier sequence by the finite Pólya--Schur theorem.  The remaining sign
patterns follow by negating `g` or reflecting it in `x ↦ -x`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A real-rooted polynomial with nonpositive zeros and nonnegative leading
coefficient is PF. -/
private theorem isPFPolynomial_of_splits_of_roots_nonpos {g : ℝ[X]} (hg : g.Splits)
    (hroots : ∀ r ∈ g.roots, r ≤ 0) (hlc : 0 ≤ g.leadingCoeff) :
    IsPFPolynomial g := by
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_of_splits hg)]
  refine (IsPFPolynomial.of_C_nonneg hlc).mul ?_
  generalize g.roots = t at hroots ⊢
  induction t using Multiset.induction_on with
  | empty => simpa using IsPFPolynomial.one
  | cons r s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    have hr : IsPFPolynomial (X - C r : ℝ[X]) := by
      simpa [sub_eq_add_neg] using
        isPFPolynomial_X_add_C (a := -r) (neg_nonneg.mpr (hroots r (by simp)))
    exact hr.mul (ih fun x hx ↦ hroots x (by simp [hx]))

/-- Negating the right factor negates the factorial Schur product. -/
theorem gwSchurProduct_neg_right (f g : ℝ[X]) :
    gwSchurProduct f (-g) = -gwSchurProduct f g := by
  ext k
  simp

/-- Reflecting the right factor in `x ↦ -x` reflects the factorial Schur
product. -/
theorem gwSchurProduct_comp_neg_X_right (f g : ℝ[X]) :
    gwSchurProduct f (g.comp (-X)) = (gwSchurProduct f g).comp (-X) := by
  have hcoeff (k : ℕ) : (g.comp (-X)).coeff k = (-1) ^ k * g.coeff k := by
    rw [show (-X : ℝ[X]) = C (-1) * X by simp, Polynomial.comp_C_mul_X_coeff, mul_comm]
  simp only [gwSchurProduct, hcoeff, mul_left_comm (Nat.factorial _ : ℝ)]
  exact diagonalOperator_alternating _ f

/-- Schur's theorem for a PF right factor: if `f` is real-rooted and `g` is a
PF polynomial, then `∑ k! aₖ bₖ xᵏ` is zero or real-rooted. -/
theorem gwSchurProduct_eq_zero_or_splits_of_isPFPolynomial {f g : ℝ[X]}
    (hf : f.Splits) (hg : IsPFPolynomial g) :
    gwSchurProduct f g = 0 ∨ (gwSchurProduct f g).Splits :=
  isMultiplierSequence_iff_preserves.mp
    (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp
      hg.isPFMultiplierSequence_factorial_mul_coeff).1 hf

/-- Schur's factorial product theorem: if `f = ∑ aₖ xᵏ` is real-rooted and
`g = ∑ bₖ xᵏ` is real-rooted with all zeros of one sign, then
`∑ k! aₖ bₖ xᵏ` is zero or real-rooted. -/
theorem gwSchurProduct_eq_zero_or_splits {f g : ℝ[X]} (hf : f.Splits)
    (hg : g.Splits) (hsign : (∀ r ∈ g.roots, r ≤ 0) ∨ ∀ r ∈ g.roots, 0 ≤ r) :
    gwSchurProduct f g = 0 ∨ (gwSchurProduct f g).Splits := by
  have hnonpos : ∀ {g : ℝ[X]}, g.Splits → (∀ r ∈ g.roots, r ≤ 0) →
      gwSchurProduct f g = 0 ∨ (gwSchurProduct f g).Splits := by
    intro g hg hroots
    rcases le_total 0 g.leadingCoeff with hlc | hlc
    · exact gwSchurProduct_eq_zero_or_splits_of_isPFPolynomial hf
        (isPFPolynomial_of_splits_of_roots_nonpos hg hroots hlc)
    · have hneg := gwSchurProduct_eq_zero_or_splits_of_isPFPolynomial hf
        (isPFPolynomial_of_splits_of_roots_nonpos hg.neg (by simpa using hroots)
          (by simpa using hlc))
      rw [gwSchurProduct_neg_right] at hneg
      rcases hneg with h | h
      · exact .inl (neg_eq_zero.mp h)
      · exact .inr (by simpa using h.neg)
  rcases hsign with hroots | hroots
  · exact hnonpos hg hroots
  · have h := hnonpos hg.comp_neg_X (by
      simpa only [roots_comp_neg_X, Multiset.forall_mem_map_iff, neg_nonpos] using hroots)
    rwa [gwSchurProduct_comp_neg_X_right, comp_neg_X_eq_zero_or_splits_iff] at h

end RealRooted
