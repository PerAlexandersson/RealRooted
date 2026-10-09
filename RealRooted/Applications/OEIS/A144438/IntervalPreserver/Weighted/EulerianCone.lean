import RealRooted.SymmetricDecomposition.EulerianTransform
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Basic
import RealRooted.BernsteinCone.Preserver
import RealRooted.SequenceClosure
import RealRooted.Hadamard.Grace

/-!
# The zero-weight deco transform on the magic cone

The weighted deco Eulerian transform `𝔓_w` at weight `w = 0` is the Eulerian transform
`u^n ↦ A_{n+1}`, and the Eulerian transformation `𝒜 : 1 ↦ 1, u^n ↦ x A_n` satisfies
`𝒜(u f) = x 𝔓_0(f)` (`EulerianTransform.transform_X_mul_eq_X_mul_weightedDecoTransform`).
Multiplying by `u` maps the degree-`d` magic cone `∑_k c_k u^k (1+u)^(d-k)`, `c_k ≥ 0`, into the
degree-`(d+1)` cone, so Athanasiadis's cone theorem gives the cone theorem for `𝔓_0`
(`weightedDecoTransform_zero_isPF_of_magicExpansion`).  Since every polynomial with all zeros in
`[-1, 0]` lies in the cone (its Bernstein expansion has nonnegative coefficients), this
re-derives the real-rootedness part of the deco interval theorem at `w = 0`.

Whether the cone theorem holds for `𝔓_w` with `w > 0` is open (Alexandersson, *An Eulerian
deformation from deco polyominoes*, Problem "transformRange"); nothing here addresses it.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted

namespace EulerianTransform

open Applications.OEIS

/-- The zero-weight deco transform is the Eulerian transform after one input
    factor of `X`. -/
theorem transform_X_mul_eq_X_mul_weightedDecoTransform (p : ℝ[X]) :
    transform (X * p) = X * weightedDecoTransform 0 p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [mul_add, map_add, weightedDecoTransform_add, hp, hq]
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      have hmul : X * (C a * X ^ n) = C a * X ^ (n + 1) := by ring
      rw [hmul, transform_C_mul, weightedDecoTransform_C_mul]
      simp only [transform_X_pow, image, weightedDecoTransform_X_pow]
      rw [weightedDecoEulerian_zero_weight]
      ring

/-- Coefficients for the magic-basis expansion of `X * f`. -/
def shiftMagicCoeffs (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => c k

/-- The factor `X` shifts a magic-basis expansion up by one degree. -/
theorem X_mul_magicExpansion (d : ℕ) (c : ℕ → ℝ) :
    X * magicExpansion d c =
      magicExpansion (d + 1) (shiftMagicCoeffs c) := by
  unfold magicExpansion
  rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [shiftMagicCoeffs, map_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hsub : d + 1 - (k + 1) = d - k := by lia
  rw [hsub]
  ring

end EulerianTransform

namespace Applications.OEIS

/-- The zero-weight deco transform sends the nonnegative magic cone to PF
    polynomials. -/
theorem weightedDecoTransform_zero_isPF_of_magicExpansion {d : ℕ} {c : ℕ → ℝ}
    (hc : ∀ k, k ≤ d → 0 ≤ c k) :
    IsPFPolynomial (weightedDecoTransform 0 (EulerianTransform.magicExpansion d c)) := by
  apply isPFPolynomial_of_X_mul
  rw [← EulerianTransform.transform_X_mul_eq_X_mul_weightedDecoTransform,
    EulerianTransform.X_mul_magicExpansion]
  apply EulerianTransform.transform_magicExpansion_isPF
  intro k hk
  cases k with
  | zero =>
      simp [EulerianTransform.shiftMagicCoeffs]
  | succ k =>
      exact hc k (by lia)

/-- The zero-weight deco transform is PF for a positive-leading polynomial
    whose roots lie in `[-1, 0]`. -/
theorem weightedDecoTransform_zero_isPF_of_roots_mem_Icc
    {f : ℝ[X]} {d : ℕ} (hf : f.Splits) (hdeg : f.natDegree = d)
    (hlead : HasPosLeadingCoeff f)
    (hroots : ∀ r ∈ f.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    IsPFPolynomial (weightedDecoTransform 0 f) := by
  obtain ⟨q, hq, hfq⟩ :=
    exists_nonneg_bernsteinExpansion_of_roots_mem_Icc hf hdeg hlead hroots
  rw [hfq]
  exact weightedDecoTransform_zero_isPF_of_magicExpansion (c := fun k => q.coeff k)
    (fun k _ => hq k)

/-- The zero-weight deco transform preserves real-rootedness on the interval
    `[-1, 0]`, with the zero-polynomial case made explicit. -/
theorem weightedDecoTransform_zero_eq_zero_or_splits_of_roots_mem_Icc
    {f : ℝ[X]} (hf : f.Splits)
    (hroots : ∀ r ∈ f.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    weightedDecoTransform 0 f = 0 ∨ (weightedDecoTransform 0 f).Splits := by
  by_cases hf0 : f = 0
  · left
    rw [hf0, show (0 : ℝ[X]) = C 0 by simp, weightedDecoTransform_C]
  rcases lt_trichotomy f.leadingCoeff 0 with hneg | hzero | hpos
  · have hnegRoots : ∀ r ∈ (-f).roots, r ∈ Set.Icc (-1 : ℝ) 0 := by
      intro r hr
      apply hroots r
      simpa only [Polynomial.roots_neg] using hr
    have hpf : IsPFPolynomial (weightedDecoTransform 0 (-f)) :=
      weightedDecoTransform_zero_isPF_of_roots_mem_Icc (d := f.natDegree) hf.neg
        (by simp only [Polynomial.natDegree_neg]) (by
          rw [HasPosLeadingCoeff, Polynomial.leadingCoeff_neg]
          exact neg_pos.mpr hneg) hnegRoots
    rw [weightedDecoTransform_neg] at hpf
    by_cases hz : weightedDecoTransform 0 f = 0
    · exact Or.inl hz
    · exact Or.inr <| by
        simpa using (hpf.ne_zero_and_splits (neg_ne_zero.mpr hz)).2.neg
  · exact (hf0 (Polynomial.leadingCoeff_eq_zero.mp hzero)).elim
  · have hpf : IsPFPolynomial (weightedDecoTransform 0 f) :=
      weightedDecoTransform_zero_isPF_of_roots_mem_Icc (d := f.natDegree) hf rfl
        (show HasPosLeadingCoeff f from hpos) hroots
    by_cases hz : weightedDecoTransform 0 f = 0
    · exact Or.inl hz
    · exact Or.inr (hpf.ne_zero_and_splits hz).2

end Applications.OEIS

end RealRooted
