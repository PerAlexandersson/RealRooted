import RealRooted.HermiteBiehler.StablePencil
import RealRooted.OperatorInterlacingUpgrade.RootOrder

/-!
# Monomial-chain operators preserve nonnegative stable pencils

By the stable-pencil characterization `mvUpperHalfPlaneStable_bivariatePencil_iff_strictInterl`,
oriented interlacing of nonnegative-coefficient polynomials `g ≪ f` is the same as stability of
the bivariate pencil `f(z) + w g(z)`.  So the monomial-chain interlacing upgrade
`strictInterl_map_of_monomialChain` says that a monomial-chain operator `T` preserves stability
of nonnegative pencils.  This sits strictly between preservation of real-rootedness and
preservation of all bivariate stability: the rank-three binary-run transform is a monomial-chain
operator that does not preserve bivariate real stability
(`binaryRunTransformThree_counterexample`).
-/

open Polynomial

namespace RealRooted

/-- A monomial-chain operator preserves stability of nonnegative-coefficient pencils
`f(z) + w g(z)`. -/
theorem mvUpperHalfPlaneStable_bivariatePencil_map_of_monomialChain
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {D : ℕ} {f g : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hdeg : f.natDegree ≠ 0) (hfD : f.natDegree ≤ D) (hTdeg : (T f).natDegree ≠ 0)
    (hTnn : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTrr : ∀ ⦃p : ℝ[X]⦄, IsPFPolynomial p → p ≠ 0 →
      p.natDegree ≤ D → T p ≠ 0 ∧ (T p).Splits)
    (hmono : ∀ m : ℕ, m + 1 ≤ D →
      StrictInterl (T (X ^ m)) (T (X ^ (m + 1))))
    (hstab : MvUpperHalfPlaneStable (bivariatePencil f g)) :
    MvUpperHalfPlaneStable (bivariatePencil (T f) (T g)) := by
  have hgf : StrictInterl g f :=
    (mvUpperHalfPlaneStable_bivariatePencil_iff_strictInterl hf hg hf0 hg0 hdeg).mp hstab
  have hT : StrictInterl (T g) (T f) :=
    strictInterl_map_of_monomialChain hgf hg hf hfD hTnn hTrr hmono
  exact (mvUpperHalfPlaneStable_bivariatePencil_iff_strictInterl (hTnn hf) (hTnn hg)
    hT.2.1.1 hT.1.1 hTdeg).mpr hT

end RealRooted
