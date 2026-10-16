module

public import RealRooted.AffineFamily
public import RealRooted.PFPolynomial

/-!
# Affine pencils of PF pairs

For PF polynomials `f` and `g` (nonnegative coefficients, only real roots), directed interlacing
`Interl f g` holds exactly when every positive affine pencil `(s X + t) f + g` is PF.  Zero inputs
are allowed on both sides.
-/

public noncomputable section

open Polynomial

namespace RealRooted

/-- Positive affine pencils of an interlacing PF pair are PF, including zero inputs. -/
theorem Interl.isPFPolynomial_affine {f g : ℝ[X]} (h : Interl f g)
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    IsPFPolynomial ((C s * X + C t) * f + g) := by
  have hlin : HasNonnegCoeffs (C s * X + C t) := hasNonnegCoeffs_affine_linear hs.le ht.le
  rcases h with rfl | rfl | h
  · simpa using hg
  · simpa using (IsPFPolynomial.of_realRooted_nonneg hlin
      (isRealRooted_affine_factor (t := t) hs).2).mul hf
  · exact IsPFPolynomial.of_realRooted_nonneg
      ((hlin.mul hf.hasNonnegCoeffs).add hg.hasNonnegCoeffs)
      (isRealRooted_affine_combo_of_strictInterl_nonneg h
        hf.hasNonnegCoeffs hg.hasNonnegCoeffs hs ht).2

/-- Directed interlacing of PF polynomials is equivalent to all positive affine pencils
`(s X + t) f + g` being PF. -/
theorem interl_iff_isPFPolynomial_affine {f g : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) :
    Interl f g ↔ ∀ s t : ℝ, 0 < s → 0 < t → IsPFPolynomial ((C s * X + C t) * f + g) := by
  refine ⟨fun h s t hs ht => h.isPFPolynomial_affine hf hg hs ht, fun haff => ?_⟩
  by_cases hf0 : f = 0
  · exact hf0 ▸ interl_zero_left g
  by_cases hg0 : g = 0
  · exact hg0 ▸ interl_zero_right f
  refine Or.inr <| Or.inr <| strictInterl_of_affine_family_nonneg hf0 hg0
    hf.hasNonnegCoeffs hg.hasNonnegCoeffs fun {s t} hs ht => ?_
  exact (haff s t hs ht).ne_zero_and_splits <| add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
    ((hasNonnegCoeffs_affine_linear hs.le ht.le).mul hf.hasNonnegCoeffs) hg.hasNonnegCoeffs hg0

end RealRooted
