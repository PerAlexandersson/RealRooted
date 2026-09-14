import RealRooted.BernsteinCone
import RealRooted.ChudnovskySeymour.Core
import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.BernsteinBasisTransform

/-!
# Bernstein-image criteria for basis-transform preservers

A coefficient-basis transform sends a degree-bounded Bernstein expansion to
the corresponding weighted sum of its Bernstein-basis images. If those images
form a nonnegative interlacing sequence, Chudnovsky--Seymour compatibility
makes every such nonnegative weighted sum a PF polynomial.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The ordered images of the degree-`d` Bernstein basis under the
coefficient-basis transform determined by `B`. -/
def bernsteinBasisImageRow (B : ℕ → ℝ[X]) (d : ℕ) : List ℝ[X] :=
  List.ofFn fun k : Fin (d + 1) ↦
    Polynomial.basisTransform B (X ^ (k : ℕ) * (1 + X) ^ (d - (k : ℕ)))

private def bernsteinBasisImageWeights
    (B : ℕ → ℝ[X]) (d : ℕ) (q : ℝ[X]) : List (ℝ × ℝ[X]) :=
  List.ofFn fun k : Fin (d + 1) ↦
    (q.coeff k,
      Polynomial.basisTransform B
        (X ^ (k : ℕ) * (1 + X) ^ (d - (k : ℕ))))

private theorem weightedSum_bernsteinBasisImageWeights
    (B : ℕ → ℝ[X]) (d : ℕ) (q : ℝ[X]) :
    weightedSum (bernsteinBasisImageWeights B d q) =
      Polynomial.basisTransform B (Polynomial.bernsteinExpansion d q) := by
  rw [bernsteinBasisImageWeights, weightedSum_ofFn]
  calc
    ∑ k : Fin (d + 1),
          C (q.coeff k) * Polynomial.basisTransform B
            (X ^ (k : ℕ) * (1 + X) ^ (d - (k : ℕ))) =
        ∑ k ∈ Finset.range (d + 1),
          C (q.coeff k) * Polynomial.basisTransform B
            (X ^ k * (1 + X) ^ (d - k)) := by
      simpa using Fin.sum_univ_eq_sum_range
        (fun k ↦ C (q.coeff k) * Polynomial.basisTransform B
          (X ^ k * (1 + X) ^ (d - k))) (d + 1)
    _ = Polynomial.basisTransform B (Polynomial.bernsteinExpansion d q) :=
      (Polynomial.basisTransform_bernsteinExpansion B d q).symm

/-- If the images of a Bernstein basis form a nonnegative interlacing
sequence, then every nonnegative combination of those images is PF. -/
theorem IsInterlacingSeqNonneg.basisTransform_bernsteinExpansion_isPF
    {B : ℕ → ℝ[X]} {d : ℕ} {q : ℝ[X]}
    (hrow : IsInterlacingSeqNonneg (bernsteinBasisImageRow B d))
    (hq : HasNonnegCoeffs q) :
    IsPFPolynomial
      (Polynomial.basisTransform B (Polynomial.bernsteinExpansion d q)) := by
  let ws := bernsteinBasisImageWeights B d q
  have hmem : ∀ ap ∈ ws, ap.2 ∈ bernsteinBasisImageRow B d := by
    intro ap hap
    dsimp [ws, bernsteinBasisImageWeights] at hap
    rw [List.mem_ofFn] at hap
    rcases hap with ⟨k, rfl⟩
    rw [bernsteinBasisImageRow, List.mem_ofFn]
    exact ⟨k, rfl⟩
  have hweights : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    dsimp [ws, bernsteinBasisImageWeights] at hap
    rw [List.mem_ofFn] at hap
    rcases hap with ⟨k, rfl⟩
    exact hq k
  have hpolys : ∀ ap ∈ ws, HasNonnegCoeffs ap.2 := by
    intro ap hap
    exact (hrow.1 ap.2 (hmem ap hap)).2
  have hnn : HasNonnegCoeffs (weightedSum ws) :=
    hasNonnegCoeffs_weightedSum ws hweights hpolys
  have hsplit := hrow.familyCompatible ws hmem hweights
  rw [weightedSum_bernsteinBasisImageWeights] at hnn hsplit
  exact IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hnn <|
    hsplit.imp_right And.right

/-- A positive-leading polynomial rooted in `[-1, 0]` is sent to a PF
polynomial when its ambient Bernstein-image row is nonnegatively
interlacing. -/
theorem IsInterlacingSeqNonneg.basisTransform_isPF_of_roots_mem_Icc
    {B : ℕ → ℝ[X]} {p : ℝ[X]}
    (hrow : IsInterlacingSeqNonneg
      (bernsteinBasisImageRow B p.natDegree))
    (hp : p.Splits) (hlead : HasPosLeadingCoeff p)
    (hroots : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    IsPFPolynomial (Polynomial.basisTransform B p) := by
  obtain ⟨q, hq, hpq⟩ :=
    exists_nonneg_bernsteinExpansion_of_roots_mem_Icc hp rfl hlead hroots
  rw [hpq]
  exact hrow.basisTransform_bernsteinExpansion_isPF hq

/-- An arbitrary-sign polynomial rooted in `[-1, 0]` is sent to zero or to a
nonzero splitting polynomial with only nonpositive roots when its ambient
Bernstein-image row is nonnegatively interlacing. -/
theorem IsInterlacingSeqNonneg.basisTransform_eq_zero_or_splits_and_roots_nonpos
    {B : ℕ → ℝ[X]} {p : ℝ[X]}
    (hrow : IsInterlacingSeqNonneg
      (bernsteinBasisImageRow B p.natDegree))
    (hp : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 0) :
    Polynomial.basisTransform B p = 0 ∨
      (Polynomial.basisTransform B p ≠ 0 ∧
        (Polynomial.basisTransform B p).Splits ∧
          ∀ r ∈ (Polynomial.basisTransform B p).roots, r ≤ 0) := by
  by_cases hp0 : p = 0
  · left
    simp [hp0]
  rcases lt_trichotomy p.leadingCoeff 0 with hlead | hlead | hlead
  · have hnegRoots : ∀ r ∈ (-p).roots, r ∈ Set.Icc (-1 : ℝ) 0 := by
      intro r hr
      apply hroots r
      simpa only [Polynomial.roots_neg] using hr
    have hnegRow : IsInterlacingSeqNonneg
        (bernsteinBasisImageRow B (-p).natDegree) := by
      simpa only [Polynomial.natDegree_neg] using hrow
    have hnegPF : IsPFPolynomial (Polynomial.basisTransform B (-p)) :=
      hnegRow.basisTransform_isPF_of_roots_mem_Icc hp.neg
        (show HasPosLeadingCoeff (-p) by
          rw [HasPosLeadingCoeff, Polynomial.leadingCoeff_neg]
          exact neg_pos.mpr hlead)
        hnegRoots
    have htransform :
        Polynomial.basisTransform B (-p) =
          -Polynomial.basisTransform B p := by
      rw [show -p = (-1 : ℝ) • p by simp,
        Polynomial.basisTransform_smul]
      simp
    rw [htransform] at hnegPF
    by_cases hzero : Polynomial.basisTransform B p = 0
    · exact Or.inl hzero
    · have hnegZero : -Polynomial.basisTransform B p ≠ 0 :=
        neg_ne_zero.mpr hzero
      have hnegSplits := (hnegPF.ne_zero_and_splits hnegZero).2
      refine Or.inr ⟨hzero, ?_, ?_⟩
      · simpa using hnegSplits.neg
      · intro r hr
        apply hnegPF.roots_nonpos r
        simpa only [Polynomial.roots_neg] using hr
  · exact (hp0 (Polynomial.leadingCoeff_eq_zero.mp hlead)).elim
  · have hpf : IsPFPolynomial (Polynomial.basisTransform B p) :=
      hrow.basisTransform_isPF_of_roots_mem_Icc hp hlead hroots
    by_cases hzero : Polynomial.basisTransform B p = 0
    · exact Or.inl hzero
    · exact Or.inr ⟨hzero, (hpf.ne_zero_and_splits hzero).2,
        hpf.roots_nonpos⟩

end RealRooted
