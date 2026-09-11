import RealRooted.Hyperbolicity

/-!
# Ordinary stable homogenization challenge entry point

Human statement: ordinary homogenization preserves multivariate real
stability for a polynomial with nonnegative coefficients (issue #550).

The checked endpoints are `MvRealStable.ordinaryHomogenization` and
`MvRealStable.ordinaryHomogenization_of_totalDegree_le` in
`RealRooted.Hyperbolicity`.  The latter permits padding the homogenizing
degree.  The zero-aware complex formulation is also exposed below.  These
are challenge-facing wrappers only; the proofs and their assumptions remain
in the reusable stability module.
-/

namespace RealRooted
namespace Challenges
namespace Homogenization

/-- The exact total-degree ordinary homogenization of a nonzero real-stable
multivariate polynomial with nonnegative coefficients is real stable. -/
theorem ordinaryHomogenization_stable
    {σ : Type*} {P : MvPolynomial σ ℝ} (hst : MvRealStable P)
    (hnn : MvPolynomial.HasNonnegCoeffs P) (hP : P ≠ 0) :
    MvRealStable
      (MvPolynomial.ordinaryHomogenization P P.totalDegree) := by
  exact hst.ordinaryHomogenization hnn hP

/-- Ordinary homogenization remains real stable when its target degree is any
degree at least the source total degree. -/
theorem ordinaryHomogenization_stable_of_totalDegree_le
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hst : MvRealStable P) (hnn : MvPolynomial.HasNonnegCoeffs P)
    (hP : P ≠ 0) (hdeg : P.totalDegree ≤ d) :
    MvRealStable (MvPolynomial.ordinaryHomogenization P d) := by
  exact hst.ordinaryHomogenization_of_totalDegree_le hnn hP hdeg

/-- Zero-aware version of the padded ordinary-homogenization result: the
complexification is either identically zero or upper-half-plane stable. -/
theorem ordinaryHomogenization_stableOrZero
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hst : P = 0 ∨ MvRealStable P)
    (hnn : MvPolynomial.HasNonnegCoeffs P)
    (hdeg : P.totalDegree ≤ d) :
    MvUpperHalfPlaneStableOrZero
      (complexifyMv (MvPolynomial.ordinaryHomogenization P d)) := by
  exact mvUpperHalfPlaneStableOrZero_complexify_ordinaryHomogenization
    hst hnn hdeg

end Homogenization
end Challenges
end RealRooted
