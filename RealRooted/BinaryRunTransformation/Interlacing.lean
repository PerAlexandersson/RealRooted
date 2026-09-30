import RealRooted.BinaryRunTransformation.Continuation
import RealRooted.BinaryRunTransformation.Sturm
import RealRooted.OperatorInterlacingUpgrade

/-!
# Interlacing preservation for the binary-run transformation

This file specializes the monomial-chain operator upgrade to the binary-run
kernel `J_n`.  Its increasing-degree range is `deg ≤ (n + 1) / 2`, where the
basis images `J_{n,0}, J_{n,1}, …` form a Sturm chain.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The binary-run transform as a real-linear map. -/
def binaryRunTransformLinearMap (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := binaryRunTransform n
  map_add' := binaryRunTransform_add n
  map_smul' a p := by
    simpa [Polynomial.smul_eq_C_mul] using binaryRunTransform_smul n a p

@[simp] theorem binaryRunTransformLinearMap_apply (n : ℕ) (p : ℝ[X]) :
    binaryRunTransformLinearMap n p = binaryRunTransform n p := rfl

/-- On the increasing-degree range, the binary-run transform of a nonzero
nonnegative-coefficient polynomial is nonzero: its top coefficient is
positive. -/
theorem binaryRunTransform_ne_zero {n : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hp0 : p ≠ 0)
    (hdeg : 2 * p.natDegree ≤ n + 1) :
    binaryRunTransform n p ≠ 0 := by
  intro hzero
  have htop : 0 < (binaryRunTransform n p).coeff p.natDegree := by
    rw [binaryRunTransform, Polynomial.coeff_basisTransform, Polynomial.sum_def]
    refine Finset.sum_pos' (fun m _ =>
      mul_nonneg (hp m) (hasNonnegCoeffs_binaryRunPolynomial n m _))
      ⟨p.natDegree, natDegree_mem_support_of_nonzero hp0, mul_pos ?_ ?_⟩
    · exact (hp _).lt_of_ne' (leadingCoeff_ne_zero.mpr hp0)
    · rcases Nat.eq_zero_or_pos p.natDegree with h0 | h0
      · simp [h0]
      · have hlead := hasPosLeadingCoeff_binaryRunPolynomial n _ h0 hdeg
        rwa [HasPosLeadingCoeff, leadingCoeff,
          natDegree_binaryRunPolynomial_eq n _ h0 hdeg] at hlead
  simp [hzero] at htop

/-- The binary-run transform preserves oriented interlacing on its
increasing-degree range. -/
theorem strictInterl_binaryRunTransform
    {n : ℕ} {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hfdeg : f.natDegree ≤ (n + 1) / 2)
    (hgdeg : g.natDegree ≤ (n + 1) / 2) :
    StrictInterl (binaryRunTransform n f) (binaryRunTransform n g) := by
  let T := binaryRunTransformLinearMap n
  let D := (n + 1) / 2
  have hTnn : ∀ ⦃p : ℝ[X]⦄,
      HasNonnegCoeffs p → HasNonnegCoeffs (T p) := by
    intro p hp
    simpa [T] using hp.binaryRunTransform (n := n)
  have hTrr : ∀ ⦃p : ℝ[X]⦄, IsPFPolynomial p → p ≠ 0 →
      p.natDegree ≤ D → T p ≠ 0 ∧ (T p).Splits := by
    intro p hp hp0 hpdeg
    have hne := binaryRunTransform_ne_zero (n := n) hp.hasNonnegCoeffs hp0
      (by dsimp [D] at hpdeg; lia)
    exact ⟨by simpa [T] using hne, by
      simpa [T] using (hp.binaryRunTransform
        (hpdeg.trans (by dsimp [D]; lia))).2.1.resolve_left hne⟩
  have hmono : ∀ m : ℕ, m + 1 ≤ D →
      StrictInterl (T (X ^ m)) (T (X ^ (m + 1))) := by
    intro m hm
    simpa [T] using strictInterl_binaryRunPolynomial_succ_of_two_mul_lt n m
      (by dsimp [D] at hm; lia)
  have hshift : PreservesPFShiftInterlacingOnDegree T D :=
    preservesPFShiftInterlacingOnDegree_of_monomials hTnn hTrr hmono
  simpa [T, D] using strictInterl_map_of_pfShift
    hfg hf hg hfdeg hgdeg hTnn hTrr hshift

end RealRooted
