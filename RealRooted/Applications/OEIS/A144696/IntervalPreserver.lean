import RealRooted.Applications.OEIS.A144696.Endpoints
import RealRooted.BernsteinCone
import RealRooted.ChudnovskySeymour.Core
import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.BernsteinBasisTransform

/-!
# The A144696 interval-root preserver

The Bernstein images from `Endpoints` form a compatible nonnegative family.
Consequently, the A144696 basis transform sends every positive-leading
polynomial whose roots lie in `[-1, 0]` to a PF polynomial.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The A144696 transform acts coefficientwise on a finite Bernstein
expansion. -/
theorem a144696Transform_bernsteinExpansion (d : ℕ) (q : ℝ[X]) :
    a144696Transform (Polynomial.bernsteinExpansion d q) =
      ∑ k ∈ Finset.range (d + 1),
        C (q.coeff k) * a144696BernsteinImage d k := by
  simpa [a144696Transform, a144696BernsteinImage] using
    Polynomial.basisTransform_bernsteinExpansion a144696Polynomial d q

private def a144696BernsteinWeights (d : ℕ) (q : ℝ[X]) :
    List (ℝ × ℝ[X]) :=
  List.ofFn fun k : Fin (d + 1) ↦
    (q.coeff k, a144696BernsteinImage d k)

private theorem weightedSum_a144696BernsteinWeights (d : ℕ) (q : ℝ[X]) :
    weightedSum (a144696BernsteinWeights d q) =
      a144696Transform (Polynomial.bernsteinExpansion d q) := by
  rw [a144696BernsteinWeights, weightedSum_ofFn]
  calc
    ∑ k : Fin (d + 1), C (q.coeff k) * a144696BernsteinImage d k =
        ∑ k ∈ Finset.range (d + 1),
          C (q.coeff k) * a144696BernsteinImage d k := by
      simpa using Fin.sum_univ_eq_sum_range
        (fun k ↦ C (q.coeff k) * a144696BernsteinImage d k) (d + 1)
    _ = a144696Transform (Polynomial.bernsteinExpansion d q) :=
      (a144696Transform_bernsteinExpansion d q).symm

/-- A nonnegative Bernstein expansion is sent to a PF polynomial by the
A144696 transform. -/
theorem a144696Transform_bernsteinExpansion_isPF {d : ℕ} {q : ℝ[X]}
    (hq : HasNonnegCoeffs q) :
    IsPFPolynomial
      (a144696Transform (Polynomial.bernsteinExpansion d q)) := by
  let ws := a144696BernsteinWeights d q
  have hmem : ∀ ap ∈ ws, ap.2 ∈ a144696BernsteinImageRow d := by
    intro ap hap
    dsimp [ws, a144696BernsteinWeights] at hap
    rw [List.mem_ofFn] at hap
    rcases hap with ⟨k, rfl⟩
    rw [a144696BernsteinImageRow, List.mem_ofFn]
    exact ⟨k, rfl⟩
  have hweights : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    dsimp [ws, a144696BernsteinWeights] at hap
    rw [List.mem_ofFn] at hap
    rcases hap with ⟨k, rfl⟩
    exact hq k
  have hpolys : ∀ ap ∈ ws, HasNonnegCoeffs ap.2 := by
    intro ap hap
    dsimp [ws, a144696BernsteinWeights] at hap
    rw [List.mem_ofFn] at hap
    rcases hap with ⟨k, rfl⟩
    exact hasNonnegCoeffs_a144696BernsteinImage d k
  have hnn : HasNonnegCoeffs (weightedSum ws) :=
    hasNonnegCoeffs_weightedSum ws hweights hpolys
  have hsplit :=
    (a144696BernsteinImageRow_isInterlacingSeqNonneg d).familyCompatible
      ws hmem hweights
  rw [weightedSum_a144696BernsteinWeights] at hnn hsplit
  exact IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hnn <|
    hsplit.imp_right And.right

/-- Positive-leading interval-rooted polynomials are sent to PF polynomials
by the A144696 transform. -/
theorem a144696Transform_isPF_of_roots_mem_Icc
    {p : ℝ[X]} (hp : p.Splits) (hlead : HasPosLeadingCoeff p)
    (hroots : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    IsPFPolynomial (a144696Transform p) := by
  obtain ⟨q, hq, hpq⟩ :=
    exists_nonneg_bernsteinExpansion_of_roots_mem_Icc hp rfl hlead hroots
  rw [hpq]
  exact a144696Transform_bernsteinExpansion_isPF hq

/-- The A144696 basis transform sends every polynomial rooted in `[-1, 0]`
to zero or to a nonzero splitting polynomial with only nonpositive roots.
No sign normalization of the input is required. -/
theorem a144696Transform_eq_zero_or_splits_and_roots_nonpos
    {p : ℝ[X]} (hp : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    a144696Transform p = 0 ∨
      (a144696Transform p ≠ 0 ∧
        (a144696Transform p).Splits ∧
          ∀ r ∈ (a144696Transform p).roots, r ≤ 0) := by
  by_cases hp0 : p = 0
  · left
    simp [hp0, a144696Transform]
  rcases lt_trichotomy p.leadingCoeff 0 with hlead | hlead | hlead
  · have hnegRoots : ∀ r ∈ (-p).roots, r ∈ Set.Icc (-1 : ℝ) 0 := by
      intro r hr
      apply hroots r
      simpa only [Polynomial.roots_neg] using hr
    have hnegPF : IsPFPolynomial (a144696Transform (-p)) :=
      a144696Transform_isPF_of_roots_mem_Icc hp.neg
        (show HasPosLeadingCoeff (-p) by
          rw [HasPosLeadingCoeff, Polynomial.leadingCoeff_neg]
          exact neg_pos.mpr hlead)
        hnegRoots
    have htransform : a144696Transform (-p) = -a144696Transform p := by
      calc
        a144696Transform (-p) = a144696Transform (C (-1) * p) := by simp
        _ = C (-1) * a144696Transform p :=
          a144696Transform_C_mul (-1) p
        _ = -a144696Transform p := by simp
    rw [htransform] at hnegPF
    by_cases hzero : a144696Transform p = 0
    · exact Or.inl hzero
    · have hnegZero : -a144696Transform p ≠ 0 := neg_ne_zero.mpr hzero
      have hnegSplits := (hnegPF.ne_zero_and_splits hnegZero).2
      refine Or.inr ⟨hzero, ?_, ?_⟩
      · simpa using hnegSplits.neg
      · intro r hr
        apply hnegPF.roots_nonpos r
        simpa only [Polynomial.roots_neg] using hr
  · exact (hp0 (Polynomial.leadingCoeff_eq_zero.mp hlead)).elim
  · have hpf : IsPFPolynomial (a144696Transform p) :=
      a144696Transform_isPF_of_roots_mem_Icc hp hlead hroots
    by_cases hzero : a144696Transform p = 0
    · exact Or.inl hzero
    · exact Or.inr ⟨hzero, (hpf.ne_zero_and_splits hzero).2,
        hpf.roots_nonpos⟩

end RealRooted
