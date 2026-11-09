module

public import RealRooted.DerivativeProduct.Associative
public import RealRooted.RootLocation.Basic
import RealRooted.DerivativeProduct.KernelNecessity
import RealRooted.DerivativeProduct.KernelSufficiency
import Mathlib.Tactic

/-!
# The fixed-factor criterion for associative derivative products

For `a > 0` and a quadratic weight `w` with nonnegative `X ^ 2`-coefficient, and a nonzero kernel
`g`, the following are equivalent (Theorem 2 of issue #2369, kernel characterization of
issue #2363):

1. `f ↦ assocProduct a w g f` preserves real-rootedness on all inputs;
2. it does so on all inputs of degree at most one;
3. `g` is real-rooted and `w r ≤ 0` at every root `r` of `g`.

For the diamond family `betaProduct β` (`w = X * (X + 1)`) the condition (3) says that all roots
lie in `[-1, 0]`, and the case `β = 1` is the diamond product.

Sufficiency is `RealRooted.assocProduct_isRealRootedIn_univ` (the Weyl-symbol argument and the
multiplier sequence `1 / (β)_k`), necessity is
`RealRooted.isRealRootedIn_of_splits_derivProduct_affine` (the affine pencil and its residues).
-/

public section

open Polynomial Set

namespace RealRooted

noncomputable section

/-- Splitting of the outputs on affine inputs follows from `MapsRealRootedIn` in degree `≥ 1`. -/
theorem splits_derivProduct_affine_of_mapsRealRootedIn {w : ℝ[X]} {c : ℕ → ℝ} {g : ℝ[X]}
    {n : ℕ} (hn : 1 ≤ n)
    (h : MapsRealRootedIn (derivProductLinearMap w c g) n univ univ) (α β : ℝ) :
    (derivProduct w c g (C α + C β * X)).Splits := by
  by_cases hp0 : C α + C β * X = 0
  · rw [hp0, derivProduct_zero_right]
    exact Polynomial.Splits.zero
  have hdeg : (C α + C β * X).natDegree ≤ 1 := by compute_degree
  have hp : IsRealRootedIn univ (C α + C β * X) :=
    IsRealRootedIn.univ_iff.mpr ⟨hp0, Polynomial.Splits.of_natDegree_le_one hdeg⟩
  rcases h _ (hdeg.trans hn) hp with h0 | hr
  · rw [derivProductLinearMap_apply] at h0
    rw [h0]
    exact Polynomial.Splits.zero
  · rw [derivProductLinearMap_apply] at hr
    exact (IsRealRootedIn.univ_iff.mp hr).2

/-- **Fixed-factor criterion for the associative family** (issue #2369, Theorem 2).  For `a > 0`,
a quadratic weight `w` with nonnegative `X ^ 2`-coefficient and a nonzero kernel `g`, the
following are equivalent: the map `f ↦ assocProduct a w g f` preserves real-rootedness on all
inputs; it does so on all inputs of degree at most one; `g` is real-rooted with `w r ≤ 0` at every
root `r`. -/
theorem assocProduct_kernel_tfae {a : ℝ} (ha : 0 < a) {w : ℝ[X]} (hw : w.natDegree ≤ 2)
    (hA : 0 ≤ w.coeff 2) {g : ℝ[X]} (hg0 : g ≠ 0) :
    List.TFAE
      [∀ n, MapsRealRootedIn (derivProductLinearMap w (assocCoeff a (w.coeff 2)) g) n univ univ,
        MapsRealRootedIn (derivProductLinearMap w (assocCoeff a (w.coeff 2)) g) 1 univ univ,
        IsRealRootedIn {r | w.eval r ≤ 0} g] := by
  tfae_have 1 → 2 := fun h ↦ h 1
  tfae_have 2 → 3 := fun h ↦
    isRealRootedIn_of_splits_derivProduct_affine hw hA (assocCoeff_zero _ _)
      (assocCoeff_nonneg ha.le hA) (by rw [assocCoeff_one]; exact ha) hg0
      (splits_derivProduct_affine_of_mapsRealRootedIn le_rfl h)
  tfae_have 3 → 1 := fun h n p _ hp ↦
    Or.inr (assocProduct_isRealRootedIn_univ ha hw hA h hp)
  tfae_finish

/-- **Fixed-factor criterion for the diamond family** (issue #2363, issue #2369).  For `β > 0` and
a nonzero kernel `g`, the map `f ↦ f *_β g` preserves real-rootedness on all inputs if and only if
it does so on inputs of degree at most one, if and only if `g` is real-rooted with all roots in
`[-1, 0]`.  The case `β = 1` is the diamond product (Brändén, Cor. 3.5, Thms 3.11, 3.13). -/
theorem betaProduct_kernel_tfae {β : ℝ} (hβ : 0 < β) {g : ℝ[X]} (hg0 : g ≠ 0) :
    List.TFAE
      [∀ n, MapsRealRootedIn (derivProductLinearMap (X * (X + 1)) (betaCoeff β) g) n univ univ,
        MapsRealRootedIn (derivProductLinearMap (X * (X + 1)) (betaCoeff β) g) 1 univ univ,
        IsRealRootedIn (Icc (-1) 0) g] := by
  tfae_have 1 → 2 := fun h ↦ h 1
  tfae_have 2 → 3 := fun h ↦ by
    have := isRealRootedIn_of_splits_derivProduct_affine natDegree_X_mul_X_add_one_le
      (by rw [coeff_two_X_mul_X_add_one]; exact zero_le_one) (betaCoeff_zero β)
      (betaCoeff_nonneg hβ) (by rw [betaCoeff_one]; exact inv_pos.mpr hβ) hg0
      (splits_derivProduct_affine_of_mapsRealRootedIn le_rfl h)
    rwa [setOf_eval_X_mul_X_add_one_nonpos] at this
  tfae_have 3 → 1 := fun h n p _ hp ↦ Or.inr (betaProduct_isRealRootedIn_univ hβ h hp)
  tfae_finish

end

end RealRooted
