import RealRooted.NarayanaTransformation.Endpoints
import RealRooted.OperatorInterlacingUpgrade.RootOrder

/-!
# The Narayana transform preserves oriented interlacing

The Mao--Wang generalized Narayana transform `narayanaTransform m` sends `X ^ n` to
`N_{n,m}(X) = ∑ k, C(n, k) C(n + m, k) / C(m + k, k) X ^ k`.  Consecutive basis images strictly
interlace (`strictInterl_narayanaTransform_X_pow_succ`) and the transform preserves the PF cone,
so the monomial-chain interlacing upgrade `strictInterl_map_of_monomialChain` shows that it
preserves oriented interlacing of nonnegative-coefficient inputs
(`strictInterl_narayanaTransform`).  Compositions of Narayana transforms inherit the property.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The Narayana basis transform as a real-linear map. -/
def narayanaTransformLinearMap (m : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := narayanaTransform m
  map_add' p q := by
    simpa [narayanaTransform] using
      Polynomial.basisTransform_add (narayanaPolynomial m) p q
  map_smul' a p := by
    simpa [narayanaTransform, Polynomial.smul_eq_C_mul] using
      Polynomial.basisTransform_smul (narayanaPolynomial m) a p

@[simp] theorem narayanaTransformLinearMap_apply (m : ℕ) (p : ℝ[X]) :
    narayanaTransformLinearMap m p = narayanaTransform m p := rfl

/-- The Narayana image of a nonzero polynomial with nonnegative coefficients is nonzero. -/
theorem narayanaTransform_ne_zero {m : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hp0 : p ≠ 0) :
    narayanaTransform m p ≠ 0 := by
  intro hzero
  have htop : 0 < (narayanaTransform m p).coeff p.natDegree := by
    rw [coeff_narayanaTransform, Polynomial.sum_def]
    refine Finset.sum_pos' (fun k _ =>
      mul_nonneg (hp k) (hasNonnegCoeffs_narayanaPolynomial m k p.natDegree))
      ⟨p.natDegree, natDegree_mem_support_of_nonzero hp0, ?_⟩
    exact mul_pos ((hp _).lt_of_ne' (leadingCoeff_ne_zero.mpr hp0)) (by simp)
  simp [hzero] at htop

/-- Consecutive Narayana basis images strictly interlace. -/
theorem strictInterl_narayanaTransform_X_pow_succ (m n : ℕ) :
    StrictInterl (narayanaTransform m (X ^ n)) (narayanaTransform m (X ^ (n + 1))) := by
  cases n with
  | zero =>
      rw [narayanaTransform_X_pow, narayanaTransform_X_pow]
      simpa [narayanaPolynomial_one] using
        (interlaces_one_linear (p := X + C (1 : ℝ)) (by simp)).toStrictInterl
  | succ n =>
      simpa using strictInterl_narayanaPolynomial_succ m n

/-- The Narayana transform preserves oriented interlacing of nonnegative-coefficient
polynomials. -/
theorem strictInterl_narayanaTransform {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g) (m : ℕ) :
    StrictInterl (narayanaTransform m f) (narayanaTransform m g) := by
  simpa using strictInterl_map_of_monomialChain (T := narayanaTransformLinearMap m)
    (D := g.natDegree) hfg hf hg le_rfl
    (fun p hp => by simpa using hp.narayanaTransform)
    (fun p hp hp0 _ => ⟨by simpa using narayanaTransform_ne_zero hp.hasNonnegCoeffs hp0,
      by simpa using ((narayanaTransformPreservesPF m hp).eq_zero_or_splits.resolve_left
        (narayanaTransform_ne_zero hp.hasNonnegCoeffs hp0))⟩)
    (fun n _ => by simpa using strictInterl_narayanaTransform_X_pow_succ m n)

/-- Composing two Narayana transforms preserves oriented interlacing of nonnegative-coefficient
polynomials. -/
theorem strictInterl_narayanaTransform_narayanaTransform {f g : ℝ[X]}
    (hfg : StrictInterl f g) (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g) (m₁ m₂ : ℕ) :
    StrictInterl (narayanaTransform m₂ (narayanaTransform m₁ f))
      (narayanaTransform m₂ (narayanaTransform m₁ g)) :=
  strictInterl_narayanaTransform (strictInterl_narayanaTransform hfg hf hg m₁)
    hf.narayanaTransform hg.narayanaTransform m₂

end RealRooted
