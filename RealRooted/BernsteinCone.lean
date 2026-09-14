import RealRooted.Basic.Coefficients
import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Bernstein
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Bernstein cone of an interval-rooted polynomial

An exact-degree real polynomial with nonnegative leading coefficient and all
roots in `[-1, 0]` has nonnegative coefficients in the Bernstein basis
`X ^ k * (1 + X) ^ (n - k)`.
-/

open Polynomial

noncomputable section

namespace RealRooted

private theorem hasNonnegCoeffs_multisetProd
    (s : Multiset ℝ[X]) (hs : ∀ p ∈ s, HasNonnegCoeffs p) :
    HasNonnegCoeffs s.prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using hasNonnegCoeffs_one
  | cons p s ih =>
      rw [Multiset.prod_cons]
      exact (hs p (by simp)).mul
        (ih fun q hq => hs q (by simp [hq]))

/-- If an exact-degree split polynomial has all roots in `[-1, 0]`, then its
Cayley transform has nonnegative coefficients. -/
theorem hasNonnegCoeffs_cayleyTransform_of_roots_mem_Icc
    {p : ℝ[X]} {n : ℕ} (hp : p.Splits) (hdeg : p.natDegree = n)
    (hlead : 0 ≤ p.leadingCoeff)
    (hroots : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    HasNonnegCoeffs (p.cayleyTransform n) := by
  rw [Polynomial.cayleyTransform_eq_rootFactorProduct hp hdeg]
  apply nonnegCoeffs_C_mul hlead
  apply hasNonnegCoeffs_multisetProd
  intro q hq
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
  have hrange := hroots r hr
  rw [show (1 + C r) * X - C r =
      C (1 + r) * X + C (-r) by
        simp only [map_add, map_one, map_neg]
        ring]
  intro k
  rcases k with _ | _ | k
  · simp [coeff_add, coeff_one]
    linarith [hrange.2]
  · simp [coeff_one]
    linarith [hrange.1]
  · simp [coeff_one]

/-- The Cayley coefficients give the exact degree-`n` Bernstein expansion of
an interval-rooted polynomial, and all those coefficients are nonnegative. -/
theorem bernsteinExpansion_cayleyTransform_of_roots_mem_Icc
    {p : ℝ[X]} {n : ℕ} (hp : p.Splits) (hdeg : p.natDegree = n)
    (hlead : 0 ≤ p.leadingCoeff)
    (hroots : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    p = Polynomial.bernsteinExpansion n (p.cayleyTransform n) ∧
      HasNonnegCoeffs (p.cayleyTransform n) := by
  have hqnn := hasNonnegCoeffs_cayleyTransform_of_roots_mem_Icc
    hp hdeg hlead hroots
  have hqdeg : (p.cayleyTransform n).natDegree ≤ n := by
    rw [Polynomial.cayleyTransform_eq_rootFactorProduct hp hdeg]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_multiset_prod_le _).trans ?_
    have hcard : p.roots.card = n := by
      rw [← hp.natDegree_eq_card_roots, hdeg]
    rw [Multiset.map_map]
    calc
      (p.roots.map (fun r => ((1 + C r) * X - C r).natDegree)).sum ≤
          (p.roots.map (fun _ => 1)).sum := by
            apply Multiset.sum_map_le_sum_map
            intro r hr
            compute_degree!
      _ = p.roots.card := by simp
      _ ≤ n := hcard.le
  have htransform : p.cayleyTransform n =
      (Polynomial.bernsteinExpansion n (p.cayleyTransform n)).cayleyTransform n := by
    rw [Polynomial.cayleyTransform_bernsteinExpansion hqdeg]
  have heq : p = Polynomial.bernsteinExpansion n (p.cayleyTransform n) := by
    apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
    apply Polynomial.cayleyTransform_injective_on_natDegree_le n
    · simpa [Polynomial.natDegree_map_eq_of_injective
        Complex.ofRealHom.injective] using hdeg.le
    · simpa [Polynomial.natDegree_map_eq_of_injective
        Complex.ofRealHom.injective] using
          Polynomial.natDegree_bernsteinExpansion_le n (p.cayleyTransform n)
    · simpa [Polynomial.map_cayleyTransform] using
        congrArg (Polynomial.map Complex.ofRealHom) htransform
  exact ⟨heq, hqnn⟩

/-- Positive-leading specialization of the Bernstein-cone certificate. -/
theorem exists_nonneg_bernsteinExpansion_of_roots_mem_Icc
    {p : ℝ[X]} {n : ℕ} (hp : p.Splits) (hdeg : p.natDegree = n)
    (hlead : HasPosLeadingCoeff p)
    (hroots : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    ∃ q : ℝ[X], HasNonnegCoeffs q ∧
      p = Polynomial.bernsteinExpansion n q := by
  refine ⟨p.cayleyTransform n, ?_⟩
  rcases bernsteinExpansion_cayleyTransform_of_roots_mem_Icc
    hp hdeg hlead.le hroots with ⟨heq, hnonneg⟩
  exact ⟨hnonneg, heq⟩

end RealRooted
