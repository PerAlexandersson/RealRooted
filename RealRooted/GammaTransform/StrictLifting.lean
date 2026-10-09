import RealRooted.GammaTransform.ProperPosition
import RealRooted.SimpleRoots
import RealRooted.WagnerRightSum.Sign
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Strict adjacent-degree gamma lifting

If `A` and `B` have simple negative roots, strictly interlace with no common
root, and have the floor degrees `(n - 1) / 2` and `n / 2`, then the gamma
transforms `gammaTransform (n - 1) A` and `gammaTransform n B` of ambient
degrees `n - 1` and `n` again have simple negative roots, interlace and have
no common root.  The two inverse branches of the root map `ρ ↦ ρ / (1 + ρ)²`
carry a common root of the transforms to a common root of `A` and `B`; the
central root `-1`, which occurs for even ambient degree, is excluded by the
evaluation formula for `gammaTransform`.

This is the strict adjacent-degree lifting step of Zhang (SSRN 7510941,
Section 4).  It is ported from the lifting lemma of pull request `#1132`,
restated for `StrictInterl`, `HasSimpleRoots` and an explicit no-common-root
hypothesis.
-/

open Polynomial

noncomputable section

namespace RealRooted

private lemma natDegree_gammaTransform_of_coeff_zero_ne {d : ℕ} {γ : ℝ[X]}
    (hzero : γ.coeff 0 ≠ 0) : (gammaTransform d γ).natDegree = d := by
  refine Nat.le_antisymm (natDegree_gammaTransform_le d γ) ?_
  exact le_natDegree_of_ne_zero (by simpa using hzero)

/-- For even `d`, the gamma transform of a nonzero `γ` of degree exactly `d / 2`
does not vanish at `-1`. -/
private lemma eval_neg_one_gammaTransform_ne_zero {d : ℕ} {γ : ℝ[X]} (hγ : γ ≠ 0)
    (hdeg : γ.natDegree = d / 2) (heven : Even d) :
    (gammaTransform d γ).eval (-1) ≠ 0 := by
  obtain ⟨m, hm⟩ := heven
  have hdm : d = 2 * m := by lia
  have hγm : γ.natDegree = m := by rw [hdeg, hdm]; lia
  rw [hdm, gammaTransform_even_eval_neg_one, ← hγm, coeff_natDegree]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hγ) (pow_ne_zero _ (by norm_num))

/-- Negative roots and positive leading coefficient give nonnegative coefficients
and a positive constant term. -/
private lemma hasNonnegCoeffs_and_coeff_zero_pos {P : ℝ[X]} (hsplit : P.Splits)
    (hpos : HasPosLeadingCoeff P) (hneg : ∀ r ∈ P.roots, r < 0) :
    HasNonnegCoeffs P ∧ 0 < P.coeff 0 := by
  refine ⟨((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hsplit).mpr
    ⟨hpos, fun r hr => (hneg r hr).le⟩).1, ?_⟩
  rw [coeff_zero_eq_eval_zero]
  exact eval_pos_of_all_roots_lt hpos.ne_zero hsplit hpos hneg

/-- Strict adjacent-degree lifting for gamma transforms: if `A` and `B` have
positive leading coefficients and negative roots, degrees `(n - 1) / 2` and
`n / 2`, and strictly interlace without common roots, then
`gammaTransform (n - 1) A` and `gammaTransform n B` have the same properties
with degrees `n - 1` and `n`, and are simple-rooted.  The proof follows Zhang
(SSRN 7510941, Section 4), where the same lifting is used for the descent
polynomials of separable permutations. -/
theorem strictInterl_gammaTransform_succ_of_strictInterl_of_no_common {n : ℕ} {A B : ℝ[X]}
    (hn : 2 ≤ n) (hA : A.natDegree = (n - 1) / 2) (hB : B.natDegree = n / 2)
    (hApos : HasPosLeadingCoeff A) (hBpos : HasPosLeadingCoeff B)
    (hAneg : ∀ r ∈ A.roots, r < 0) (hBneg : ∀ r ∈ B.roots, r < 0)
    (hpair : StrictInterl A B) (hno : ∀ r, ¬ (A.IsRoot r ∧ B.IsRoot r)) :
    (gammaTransform (n - 1) A).natDegree = n - 1 ∧ (gammaTransform n B).natDegree = n ∧
    HasSimpleRoots (gammaTransform (n - 1) A) ∧ HasSimpleRoots (gammaTransform n B) ∧
    (∀ r ∈ (gammaTransform (n - 1) A).roots, r < 0) ∧
    (∀ r ∈ (gammaTransform n B).roots, r < 0) ∧
    StrictInterl (gammaTransform (n - 1) A) (gammaTransform n B) ∧
    ∀ r, (gammaTransform (n - 1) A).IsRoot r → ¬ (gammaTransform n B).IsRoot r := by
  have hsucc : n - 1 + 1 = n := by lia
  obtain ⟨hAnn, hA0⟩ := hasNonnegCoeffs_and_coeff_zero_pos hpair.1.2 hApos hAneg
  obtain ⟨hBnn, hB0⟩ := hasNonnegCoeffs_and_coeff_zero_pos hpair.2.1.2 hBpos hBneg
  have hAle : A.natDegree ≤ (n - 1) / 2 := hA.le
  have hBle : B.natDegree ≤ (n - 1 + 1) / 2 := by rw [hsucc]; exact hB.le
  have hweak : StrictInterl (gammaTransform (n - 1) A) (gammaTransform (n - 1 + 1) B) :=
    (strictInterl_gammaTransform_succ_iff hAle hBle hAnn hBnn hA0.ne' hB0.ne').2 hpair
  rw [hsucc] at hweak
  have hno' : ∀ r,
      ¬ ((gammaTransform (n - 1) A).IsRoot r ∧ (gammaTransform n B).IsRoot r) := by
    rintro r ⟨hrA, hrB⟩
    by_cases hr : r = -1
    · subst hr
      rcases Nat.even_or_odd (n - 1) with he | ho
      · exact eval_neg_one_gammaTransform_ne_zero hApos.ne_zero hA he hrA
      · exact eval_neg_one_gammaTransform_ne_zero hBpos.ne_zero (by rw [hB])
          (by rw [← hsucc]; exact ho.add_one) hrB
    · exact hno (r / (1 + r) ^ 2)
        ⟨isRoot_gamma_of_isRoot_gammaTransform hAle hr hrA,
          isRoot_gamma_of_isRoot_gammaTransform hB.le hr hrB⟩
  have hnegroots : ∀ {P : ℝ[X]}, HasNonnegCoeffs P → P.coeff 0 ≠ 0 →
      ∀ r ∈ P.roots, r < 0 := by
    intro P hP h0 r hr
    refine lt_of_le_of_ne (roots_nonpos_of_hasNonnegCoeffs hP r hr) ?_
    rintro rfl
    exact h0 (by rw [coeff_zero_eq_eval_zero]; exact isRoot_of_mem_roots hr)
  have hAT0 : (gammaTransform (n - 1) A).coeff 0 ≠ 0 := by
    simpa only [coeff_zero_gammaTransform] using hA0.ne'
  have hBT0 : (gammaTransform n B).coeff 0 ≠ 0 := by
    simpa only [coeff_zero_gammaTransform] using hB0.ne'
  have hsimple := hweak.hasSimpleRoots_of_no_common_root hno'
  exact ⟨natDegree_gammaTransform_of_coeff_zero_ne hA0.ne',
    natDegree_gammaTransform_of_coeff_zero_ne hB0.ne', hsimple.1, hsimple.2,
    hnegroots (hasNonnegCoeffs_gammaTransform hAnn) hAT0,
    hnegroots (hasNonnegCoeffs_gammaTransform hBnn) hBT0, hweak,
    fun r h1 h2 => hno' r ⟨h1, h2⟩⟩

end RealRooted
