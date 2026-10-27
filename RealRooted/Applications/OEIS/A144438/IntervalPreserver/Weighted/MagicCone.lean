module

import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.ParameterInduction
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Endpoints
public import RealRooted.BernsteinCone.Preserver
public import RealRooted.CommonInterleaver.RootDesc
public import RealRooted.SymmetricDecomposition.EulerianTransform
import RealRooted.WagnerRightSum
import RealRooted.ChudnovskySeymour.Core
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Degree
public import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Basic

/-!
# The weighted magic cone from its endpoint relation

This file reduces compatibility of a weighted deco Bernstein-image row to the
interlacing relation between its two endpoints.  The endpoint relation is an
explicit hypothesis: its proof, expected to come from nonvanishing of the
endpoint resultant, is not formalized here.

The interval/deletion API (`weightedDecoParameterInvariant_all`) currently assumes `w ≤ 1`,
so the weighted declarations below retain that bound.  The endpoint relation is the open
mathematical input of issue #1263 (exact checks show the endpoint resultant has positive
coefficients through rank twenty); the PF conclusion is derived, not assumed.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted
namespace Applications.OEIS

private def weightedDecoMagicParameter (k : ℕ) : ℕ → ℝ :=
  fun i ↦ if i < k then 0 else 1

private theorem weightedDecoParameterInput_range_magic
    (n k : ℕ) (hk : k ≤ n) :
    weightedDecoParameterInput (Finset.range n) (weightedDecoMagicParameter k) =
      X ^ k * (1 + X) ^ (n - k) := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := by lia
      subst k
      simp [weightedDecoParameterInput]
  | succ n ih =>
      rw [weightedDecoParameterInput, Finset.prod_range_succ]
      by_cases hkn : k ≤ n
      · rw [show weightedDecoMagicParameter k n = 1 by
            simp [weightedDecoMagicParameter, Nat.not_lt.mpr hkn]]
        rw [show ∏ i ∈ Finset.range n,
              (X + C (weightedDecoMagicParameter k i)) =
            weightedDecoParameterInput (Finset.range n)
              (weightedDecoMagicParameter k) by
          apply Finset.prod_congr rfl
          intro i _
          rfl]
        rw [ih k hkn]
        have hsub : n + 1 - k = (n - k) + 1 := by lia
        rw [hsub, pow_succ]
        simp only [C_1]
        ring
      · have hkEq : k = n + 1 := by lia
        subst k
        simp only [weightedDecoMagicParameter]
        have hzero : (∏ i ∈ Finset.range n,
            (X + C (if i < n + 1 then 0 else 1)) : ℝ[X]) = X ^ n := by
          calc
            _ = ∏ _i ∈ Finset.range n, (X : ℝ[X]) := by
              apply Finset.prod_congr rfl
              intro i hi
              have hi' := Finset.mem_range.mp hi
              simp only [show i < n + 1 by lia, ite_true, map_zero, add_zero]
            _ = X ^ n := by simp
        rw [hzero]
        rw [pow_succ]
        simp

private theorem weightedDecoParameterInput_univ_magic
    (n k : ℕ) (hk : k ≤ n) :
    weightedDecoParameterInput (Finset.univ : Finset (Fin n))
        (fun i ↦ weightedDecoMagicParameter k i) =
      X ^ k * (1 + X) ^ (n - k) := by
  rw [weightedDecoParameterInput]
  calc
    _ = ∏ i ∈ Finset.range n, (X + C (weightedDecoMagicParameter k i)) :=
      Fin.prod_univ_eq_prod_range
        (fun i : ℕ ↦ X + C (weightedDecoMagicParameter k i)) n
    _ = _ := weightedDecoParameterInput_range_magic n k hk

/-- The rank-`n`, position-`k` image of the magic (Bernstein) basis under the
weighted deco transform. -/
def weightedDecoMagicBasisImage (w : ℝ) (n k : ℕ) : ℝ[X] :=
  weightedDecoTransform w (X ^ k * (1 + X) ^ (n - k))

private theorem weightedDecoMagicBasisImage_eq_parameterImage
    (w : ℝ) (n k : ℕ) (hk : k ≤ n) :
    weightedDecoMagicBasisImage w n k =
      weightedDecoParameterImage w (Finset.univ : Finset (Fin n))
        (fun i ↦ weightedDecoMagicParameter k i) := by
  rw [weightedDecoMagicBasisImage, weightedDecoParameterImage,
    weightedDecoParameterInput_univ_magic n k hk]

private theorem weightedDecoMagicBasisImage_strictInterl_succ
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {n k : ℕ}
    (hn : 2 ≤ n) (hk : k < n) :
    StrictInterl (weightedDecoMagicBasisImage w n k)
      (weightedDecoMagicBasisImage w n (k + 1)) := by
  let m := n - 1
  have hm : 1 ≤ m := by
    dsimp only [m]
    lia
  have hnEq : n = m + 1 := by
    dsimp only [m]
    lia
  have hkM : k ≤ m := by lia
  let a : Fin m → ℝ := fun i ↦ weightedDecoMagicParameter k i
  have haCube : a ∈ weightedDecoParameterCube m := by
    intro i _
    dsimp only [a, weightedDecoMagicParameter]
    split <;> norm_num
  have hinv := weightedDecoParameterInvariant_all hw0 hw1 m hm
  let g : ℝ[X] := X ^ k * (1 + X) ^ (m - k)
  have hmonicOneX : (1 + X : ℝ[X]).Monic := by
    simpa only [C_1, add_comm] using monic_X_add_C (R := ℝ) 1
  have hgInput : weightedDecoParameterInput (Finset.univ : Finset (Fin m)) a = g := by
    dsimp only [a, g]
    exact weightedDecoParameterInput_univ_magic m k hkM
  have hgMonic : g.Monic := by
    dsimp only [g]
    exact (monic_X.pow k).mul (hmonicOneX.pow (m - k))
  have hgDegree : 1 ≤ g.natDegree := by
    dsimp only [g]
    rw [(monic_X.pow k).natDegree_mul (hmonicOneX.pow (m - k)),
      natDegree_X_pow, hmonicOneX.natDegree_pow]
    have hdegree : (1 + X : ℝ[X]).natDegree = 1 := by compute_degree!
    rw [hdegree]
    simp only [mul_one]
    lia
  have hpSplits : (weightedDecoTransform w g).Splits := by
    rw [← hgInput, ← weightedDecoParameterImage]
    exact hinv.splits a haCube
  have hpResidue : ∀ r, (weightedDecoTransform w g).IsRoot r →
      0 < (weightedDecoCompanionTransform w g).eval r /
        (weightedDecoTransform w g).derivative.eval r := by
    intro r hr
    rw [← hgInput, ← weightedDecoParameterImage] at hr ⊢
    rw [← weightedDecoParameterCompanion]
    exact hinv.companion_residue_pos a haCube r hr
  have hpNeg : ∀ r, (weightedDecoTransform w g).IsRoot r → r < 0 := by
    intro r hr
    rw [← hgInput, ← weightedDecoParameterImage] at hr
    exact hinv.roots_neg a haCube r hr
  have hgOne : 0 < g.eval 1 := by
    dsimp only [g]
    simp
  have hstep := weightedDecoTransform_mul_X_add_C_root_step
    (w := w) (a := 0) (g := g) (by norm_num) hgMonic hgDegree hpSplits
      hpResidue hpNeg hgOne
  have hdeletion :
      StrictInterl (weightedDecoMagicBasisImage w m k)
        (weightedDecoMagicBasisImage w n (k + 1)) := by
    have hsub : n - (k + 1) = m - k := by lia
    have hinput : (X + C (0 : ℝ)) * g =
        X ^ (k + 1) * (1 + X) ^ (n - (k + 1)) := by
      dsimp only [g]
      rw [hsub, C_0, add_zero, pow_succ']
      ring
    simpa only [weightedDecoMagicBasisImage, g, hinput] using hstep.1
  have hnextSelf :
      StrictInterl (weightedDecoMagicBasisImage w n (k + 1))
        (weightedDecoMagicBasisImage w n (k + 1)) :=
    StrictInterl.refl hdeletion.2.1.1 hdeletion.2.1.2
  have hdeletionPos : HasPosLeadingCoeff (weightedDecoMagicBasisImage w m k) := by
    apply hasPosLeadingCoeff_of_monic
    exact weightedDecoTransform_monic w <| by
      exact (monic_X.pow k).mul (hmonicOneX.pow (m - k))
  have hnextPos : HasPosLeadingCoeff (weightedDecoMagicBasisImage w n (k + 1)) :=
    hasPosLeadingCoeff_of_monic <| weightedDecoTransform_monic w <| by
      exact (monic_X.pow (k + 1)).mul
        (hmonicOneX.pow (n - (k + 1)))
  have hadd := StrictInterl.add_of_right_of_posLeadingCoeff
    hdeletion hnextSelf hdeletionPos hnextPos
  have hpascal :
      weightedDecoMagicBasisImage w n k =
        weightedDecoMagicBasisImage w m k +
          weightedDecoMagicBasisImage w n (k + 1) := by
    have hsub : n - (k + 1) = m - k := by lia
    have hsub' : n - k = (m - k) + 1 := by lia
    rw [weightedDecoMagicBasisImage, weightedDecoMagicBasisImage,
      weightedDecoMagicBasisImage, ← weightedDecoTransform_add]
    congr 1
    rw [hsub, hsub', pow_succ]
    ring
  rw [hpascal]
  exact hadd

/-- Conditional endpoint-to-row theorem for the weighted deco magic basis.

The endpoint hypothesis is the only unproved relation used here.  On the
current `origin/main`, the established deletion theorem additionally requires
`w ≤ 1`; the proof is otherwise uniform in every nonnegative weight. -/
theorem weightedDecoMagicBasisImageRow_familyCompatible_of_endpoint
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (n : ℕ)
    (hendpoint : StrictInterl (weightedDecoMagicBasisImage w n 0)
      (weightedDecoMagicBasisImage w n n)) :
    FamilyCompatible (bernsteinBasisImageRow (weightedDecoEulerian w) n) := by
  change FamilyCompatible
    (List.ofFn fun k : Fin (n + 1) ↦ weightedDecoMagicBasisImage w n k)
  let F : ℕ → ℝ[X] := weightedDecoMagicBasisImage w n
  have hcons : ∀ k, 0 ≤ k → k < n → StrictInterl (F k) (F (k + 1)) := by
    intro k _ hk
    by_cases hn : 2 ≤ n
    · exact weightedDecoMagicBasisImage_strictInterl_succ hw0 hw1 hn hk
    · have hnOne : n = 1 := by lia
      have hkZero : k = 0 := by lia
      subst n
      subst k
      simpa only [F] using hendpoint
  have hall := strictInterl_chain_of_consecutive_of_endpoint F 0 n hcons hendpoint
  have hseq : IsInterlacingSeqNonneg
      (List.ofFn fun k : Fin (n + 1) ↦ weightedDecoMagicBasisImage w n k) := by
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [List.mem_ofFn] at hp
      rcases hp with ⟨k, rfl⟩
      have hk : k.val ≤ n := by lia
      have hself := hall k k (by simp) le_rfl hk
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa only [F, weightedDecoMagicBasisImage, weightedDecoTransform] using
          hself.1.1
      · simpa only [F, weightedDecoMagicBasisImage, weightedDecoTransform] using
          hself.1.2
      · change HasNonnegCoeffs
          (weightedDecoTransform w (X ^ (k : ℕ) * (1 + X) ^ (n - (k : ℕ))))
        apply HasNonnegCoeffs.weightedDecoTransform hw0
        exact (hasNonnegCoeffs_X.pow k).mul
          ((hasNonnegCoeffs_one.add hasNonnegCoeffs_X).pow (n - k))
    · rw [isInterlacingSeq_iff_pairwise, List.pairwise_ofFn]
      intro i j hij
      have hpair := hall i j (by simp) hij.le (by lia)
      simpa only [F, weightedDecoMagicBasisImage, weightedDecoTransform] using hpair
  exact hseq.familyCompatible

private def magicCoefficientPolynomial (d : ℕ) (c : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1), C (c k) * X ^ k

private theorem magicCoefficientPolynomial_coeff
    (d : ℕ) (c : ℕ → ℝ) {k : ℕ} (hk : k ≤ d) :
    (magicCoefficientPolynomial d c).coeff k = c k := by
  simp [magicCoefficientPolynomial, hk]

private theorem magicCoefficientPolynomial_hasNonnegCoeffs
    {d : ℕ} {c : ℕ → ℝ} (hc : ∀ k, k ≤ d → 0 ≤ c k) :
    HasNonnegCoeffs (magicCoefficientPolynomial d c) := by
  apply hasNonnegCoeffs_finsetSum
  intro k hk
  exact (hasNonnegCoeffs_C (hc k (by simp_all))).mul (hasNonnegCoeffs_X.pow k)

private theorem bernsteinExpansion_magicCoefficientPolynomial
    (d : ℕ) (c : ℕ → ℝ) :
    Polynomial.bernsteinExpansion d (magicCoefficientPolynomial d c) =
      EulerianTransform.magicExpansion d c := by
  unfold Polynomial.bernsteinExpansion EulerianTransform.magicExpansion
    Polynomial.magicExpansion
  apply Finset.sum_congr rfl
  intro k hk
  rw [magicCoefficientPolynomial_coeff d c (by simpa using hk)]

/-- Conditional weighted magic-cone theorem in the range supported by the
current interval/deletion API.  It assumes the endpoint interlacing relation,
not the desired PF conclusion. -/
theorem weightedDecoTransform_isPF_of_magicExpansion_of_endpoint
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {d : ℕ} {c : ℕ → ℝ}
    (hendpoint : StrictInterl (weightedDecoMagicBasisImage w d 0)
      (weightedDecoMagicBasisImage w d d))
    (hc : ∀ k, k ≤ d → 0 ≤ c k) :
    IsPFPolynomial
      (weightedDecoTransform w (EulerianTransform.magicExpansion d c)) := by
  let q := magicCoefficientPolynomial d c
  have hfamily := weightedDecoMagicBasisImageRow_familyCompatible_of_endpoint
    hw0 hw1 d hendpoint
  have hnonneg : ∀ p ∈ bernsteinBasisImageRow (weightedDecoEulerian w) d,
      HasNonnegCoeffs p := by
    intro p hp
    rw [bernsteinBasisImageRow, List.mem_ofFn] at hp
    rcases hp with ⟨k, rfl⟩
    change HasNonnegCoeffs
      (weightedDecoTransform w (X ^ (k : ℕ) * (1 + X) ^ (d - (k : ℕ))))
    apply HasNonnegCoeffs.weightedDecoTransform hw0
    exact (hasNonnegCoeffs_X.pow k).mul
      ((hasNonnegCoeffs_one.add hasNonnegCoeffs_X).pow (d - k))
  have hpf := hfamily.basisTransform_bernsteinExpansion_isPF hnonneg
    (magicCoefficientPolynomial_hasNonnegCoeffs hc)
  rw [bernsteinExpansion_magicCoefficientPolynomial] at hpf
  exact hpf

end Applications.OEIS

end RealRooted
