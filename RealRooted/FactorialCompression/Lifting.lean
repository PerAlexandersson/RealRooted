import RealRooted.FactorialCompression.RootGeometry
import RealRooted.GammaTransform.ProperPosition

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Adjacent-degree gamma lifting

The strict adjacent-degree lifting used by factorial-compression applications.
The exported theorem uses RealRooted's native `StrictInterl` relation and keeps
the no-common-root conclusion explicit.
-/

open Polynomial RealRooted

noncomputable section

namespace RealRooted.FactorialCompression

private theorem gammaTransform_natDegree_of_coeff_zero_ne {d : ℕ} {γ : ℝ[X]} (hzero : γ.coeff 0 ≠ 0) :
    (gammaTransform d γ).natDegree = d := by
  apply Nat.le_antisymm (natDegree_gammaTransform_le d γ)
  exact le_natDegree_of_ne_zero (by simpa using hzero)

/-- The two inverse branches and central parity root transfer a strict gamma
pair of full floor degrees to a strict descent pair in adjacent degrees.
No gamma interlacing theorem is assumed as an external mathematical input:
this is the reusable transfer lemma whose input is a previously proved pair. -/
private theorem gammaTransform_succ_strictRootGeometry {d : ℕ} {γ δ : ℝ[X]}
    (hγdegree : γ.natDegree = d / 2)
    (hδdegree : δ.natDegree = (d + 1) / 2)
    (hγnn : HasNonnegCoeffs γ) (hδnn : HasNonnegCoeffs δ)
    (hγ0 : 0 < γ.coeff 0) (hδ0 : 0 < δ.coeff 0)
    (hpair : StrictRootInterl γ δ) :
    (gammaTransform d γ).natDegree = d ∧
      (gammaTransform (d + 1) δ).natDegree = d + 1 ∧
      SimpleNegativeRoots (gammaTransform d γ) ∧
      SimpleNegativeRoots (gammaTransform (d + 1) δ) ∧
      StrictRootInterl (gammaTransform d γ) (gammaTransform (d + 1) δ) := by
  have hγbound : γ.natDegree ≤ d / 2 := hγdegree.le
  have hδbound : δ.natDegree ≤ (d + 1) / 2 := hδdegree.le
  have hweak : StrictInterl (gammaTransform d γ) (gammaTransform (d + 1) δ) :=
    (strictInterl_gammaTransform_succ_iff hγbound hδbound hγnn hδnn
      (ne_of_gt hγ0) (ne_of_gt hδ0)).2 hpair.toStrictInterl
  have hno : ∀ r : ℝ,
      ¬ ((gammaTransform d γ).IsRoot r ∧ (gammaTransform (d + 1) δ).IsRoot r) := by
    intro r hr
    by_cases hrcenter : r = -1
    · subst r
      rcases Nat.even_or_odd d with heven | hodd
      · rcases heven with ⟨m, hm⟩
        have hdm : d = 2 * m := by lia
        have hγm : γ.natDegree = m := by rw [hγdegree, hdm]; simp
        have hne : (gammaTransform d γ).eval (-1) ≠ 0 := by
          rw [hdm, gammaTransform_even_eval_neg_one, ← hγm, coeff_natDegree]
          exact mul_ne_zero (ne_of_gt hpair.1)
            (pow_ne_zero _ (by norm_num))
        exact hne hr.1
      · rcases hodd with ⟨m, hm⟩
        have hdm : d + 1 = 2 * (m + 1) := by lia
        have hδm : δ.natDegree = m + 1 := by rw [hδdegree, hdm]; simp
        have hne : (gammaTransform (d + 1) δ).eval (-1) ≠ 0 := by
          rw [hdm, gammaTransform_even_eval_neg_one, ← hδm, coeff_natDegree]
          exact mul_ne_zero (ne_of_gt hpair.2.1)
            (pow_ne_zero _ (by norm_num))
        exact hne hr.2
    · exact hpair.no_common_root_pair (r / (1 + r) ^ 2)
        ⟨isRoot_gamma_of_isRoot_gammaTransform hγbound hrcenter hr.1,
          isRoot_gamma_of_isRoot_gammaTransform hδbound hrcenter hr.2⟩
  have hTγnn : HasNonnegCoeffs (gammaTransform d γ) :=
    hasNonnegCoeffs_gammaTransform hγnn
  have hTδnn : HasNonnegCoeffs (gammaTransform (d + 1) δ) :=
    hasNonnegCoeffs_gammaTransform hδnn
  have hsimp := hweak.hasSimpleRoots_of_no_common_root hno
  have hTγnegative : ∀ r ∈ (gammaTransform d γ).roots, r < 0 := by
    intro r hr
    have hrle := roots_nonpos_of_hasNonnegCoeffs hTγnn r hr
    have hrne : r ≠ 0 := by
      intro heq
      subst r
      have hroot := isRoot_of_mem_roots hr
      have hpositive : 0 < (gammaTransform d γ).eval 0 := by simpa using hγ0
      exact (ne_of_gt hpositive) (Polynomial.IsRoot.def.mp hroot)
    exact lt_of_le_of_ne hrle hrne
  have hTδnegative : ∀ r ∈ (gammaTransform (d + 1) δ).roots, r < 0 := by
    intro r hr
    have hrle := roots_nonpos_of_hasNonnegCoeffs hTδnn r hr
    have hrne : r ≠ 0 := by
      intro heq
      subst r
      have hroot := isRoot_of_mem_roots hr
      have hpositive : 0 < (gammaTransform (d + 1) δ).eval 0 := by simpa using hδ0
      exact (ne_of_gt hpositive) (Polynomial.IsRoot.def.mp hroot)
    exact lt_of_le_of_ne hrle hrne
  exact ⟨gammaTransform_natDegree_of_coeff_zero_ne (ne_of_gt hγ0), gammaTransform_natDegree_of_coeff_zero_ne (ne_of_gt hδ0),
    ⟨hweak.1.1, hweak.1.2, hsimp.1.roots_nodup, hTγnegative⟩,
    ⟨hweak.2.1.1, hweak.2.1.2, hsimp.2.roots_nodup, hTδnegative⟩,
    strictRootInterl_of_strictInterl_of_no_common_root hweak
      (hTγnn.pos_leadingCoeff hweak.1.1) (hTδnn.pos_leadingCoeff hweak.2.1.1) hno⟩


/-- Two-branch lifting lemma, with exactly its positive leading
coefficients, simple negative roots, degrees and strict oriented input.
Coefficient nonnegativity and the nonzero constant terms are derived. -/
private theorem two_branch_lifting_strictRootGeometry {n : ℕ} {A B : ℝ[X]} (hn : 2 ≤ n)
    (hAdegree : A.natDegree = (n - 1) / 2)
    (hBdegree : B.natDegree = n / 2)
    (hA : SimpleNegativeRoots A) (hB : SimpleNegativeRoots B)
    (hApos : 0 < A.leadingCoeff) (hBpos : 0 < B.leadingCoeff)
    (hpair : StrictRootInterl A B) :
    (gammaTransform (n - 1) A).natDegree = n - 1 ∧
    (gammaTransform n B).natDegree = n ∧
    SimpleNegativeRoots (gammaTransform (n - 1) A) ∧
    SimpleNegativeRoots (gammaTransform n B) ∧
    StrictRootInterl (gammaTransform (n - 1) A) (gammaTransform n B) := by
  have heq : n - 1 + 1 = n := by lia
  have hAnn : HasNonnegCoeffs A :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hA.2.1).mpr
      ⟨hApos, fun r hr => (hA.2.2.2 r hr).le⟩).1
  have hBnn : HasNonnegCoeffs B :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hB.2.1).mpr
      ⟨hBpos, fun r hr => (hB.2.2.2 r hr).le⟩).1
  have hA0 : 0 < A.coeff 0 := by
    rw [coeff_zero_eq_eval_zero]
    exact eval_pos_of_all_roots_lt hApos.ne_zero hA.2.1 hApos hA.2.2.2
  have hB0 : 0 < B.coeff 0 := by
    rw [coeff_zero_eq_eval_zero]
    exact eval_pos_of_all_roots_lt hBpos.ne_zero hB.2.1 hBpos hB.2.2.2
  simpa only [heq] using gammaTransform_succ_strictRootGeometry hAdegree
    (by simpa only [heq] using hBdegree) hAnn hBnn hA0 hB0 hpair


/-- Adjacent-degree gamma lifting in the native `RealRooted` interface.
The explicit no-common-root hypothesis upgrades the library interlacing
relation to the strong root-order package used by the proof. -/
theorem gammaTransform_succ_geometry_of_strictInterl {n : ℕ} {A B : ℝ[X]} (hn : 2 ≤ n)
    (hAdegree : A.natDegree = (n - 1) / 2)
    (hBdegree : B.natDegree = n / 2)
    (hApos : HasPosLeadingCoeff A) (hBpos : HasPosLeadingCoeff B)
    (hAneg : ∀ r ∈ A.roots, r < 0) (hBneg : ∀ r ∈ B.roots, r < 0)
    (hpair : StrictInterl A B)
    (hno : ∀ r, ¬ (A.IsRoot r ∧ B.IsRoot r)) :
    (gammaTransform (n - 1) A).natDegree = n - 1 ∧
    (gammaTransform n B).natDegree = n ∧
    HasSimpleRoots (gammaTransform (n - 1) A) ∧
    HasSimpleRoots (gammaTransform n B) ∧
    (∀ r ∈ (gammaTransform (n - 1) A).roots, r < 0) ∧
    (∀ r ∈ (gammaTransform n B).roots, r < 0) ∧
    StrictInterl (gammaTransform (n - 1) A) (gammaTransform n B) ∧
    (∀ r, (gammaTransform (n - 1) A).IsRoot r →
      ¬ (gammaTransform n B).IsRoot r) := by
  have hsimp := hpair.hasSimpleRoots_of_no_common_root hno
  have hAstrong : SimpleNegativeRoots A :=
    ⟨hpair.1.1, hpair.1.2, hsimp.1.roots_nodup, hAneg⟩
  have hBstrong : SimpleNegativeRoots B :=
    ⟨hpair.2.1.1, hpair.2.1.2, hsimp.2.roots_nodup, hBneg⟩
  have hpairStrong : StrictRootInterl A B :=
    strictRootInterl_of_strictInterl_of_no_common_root hpair hApos hBpos hno
  obtain ⟨hdeg₁, hdeg₂, hroot₁, hroot₂, hinter⟩ :=
    two_branch_lifting_strictRootGeometry hn hAdegree hBdegree hAstrong hBstrong
      hApos hBpos hpairStrong
  exact ⟨hdeg₁, hdeg₂, hroot₁.hasSimpleRoots, hroot₂.hasSimpleRoots,
    hroot₁.2.2.2, hroot₂.2.2.2, hinter.toStrictInterl, hinter.no_common_root⟩

end RealRooted.FactorialCompression
