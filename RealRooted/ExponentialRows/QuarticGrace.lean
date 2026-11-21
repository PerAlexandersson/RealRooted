module

public import RealRooted.ExponentialRows.HermiteAuxiliary
public import RealRooted.ExponentialRows.ProductInsertion
import Mathlib.Analysis.Complex.Polynomial.Basic
import RealRooted.ExponentialRows.GaussianIdentity
import RealRooted.ExponentialRows.QuarticInsertion
import RealRooted.ExponentialRows.QuadraticLocation
import RealRooted.Hermite.Grace
import RealRooted.HermiteBiehler.Basic
import Mathlib.Tactic

/-!
# Real-rootedness of all nonnegative quartic exponential rows

We prove Theorem A (`b² ≤ 4ac`) by Grace's apolarity theorem and combine it
with the existing Theorem C. The parameter boundaries are included directly.

Source: the unpublished manuscript and Grace-apolarity proof associated with
RealRooted issue #2415, https://github.com/PerAlexandersson/RealRooted/issues/2415.
The rows use the standard `insertionRow` definition; their formal exponential
identity is `insertionRow_quartic_eq_exponential`.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- A parameter in the open lower half-plane is the negative square of a number
in the open first quadrant. -/
theorem exists_sq_eq_neg_of_im_neg {t : ℂ} (ht : t.im < 0) :
    ∃ ω : ℂ, 0 < ω.re ∧ 0 < ω.im ∧ ω ^ 2 = -t := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (-t) (by decide : 0 < 2)
  have hi := congrArg Complex.im hw
  simp only [pow_two, Complex.mul_im, Complex.neg_im] at hi
  have hp : 0 < w.re * w.im := by linarith
  rcases mul_pos_iff.mp hp with ⟨hr, hi⟩ | ⟨hr, hi⟩
  · exact ⟨w, hr, hi, hw⟩
  · exact ⟨-w, by simpa using hr, by simpa using hi, by simpa using hw⟩

/-- The auxiliary Hermite roots lie strictly above the line through the square root
of the negative row parameter. -/
theorem im_mul_conj_pos_of_isRoot_hermiteAuxiliary {β γ : ℝ} {t ω η : ℂ} {n : ℕ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hωi : 0 < ω.im)
    (hw : ω ^ 2 = -t) (hη : (hermiteAuxiliary β ((γ : ℂ) * t) n).IsRoot η) :
    0 < (η * starRingEnd ℂ ω).im := by
  rw [IsRoot.def, eval_hermiteAuxiliary] at hη
  obtain ⟨ν, hν, hνeq⟩ := exists_nonneg_sq_add_eq_zero_of_hermiteHomogeneous_eq_zero hη
  apply im_mul_conj_pos_of_quadratic_eq_zero hβ hγ hν hωi
  convert hνeq using 1
  rw [hw]
  ring

/-- Completed-square quartic insertion rows have no zero in the open lower half-plane. -/
theorem eval₂_insertionRow_quartic_square_ne_zero {β γ c : ℝ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hc : 0 ≤ c) {t : ℂ} (ht : t.im < 0) (n : ℕ) :
    (insertionRow (markedBlockWeights
      (C (γ + c * β ^ 2) * X ^ 2 + C (2 * c * β) * X ^ 3 + C c * X ^ 4)) n).eval₂
        Complex.ofRealHom t ≠ 0 := by
  rw [← gaussianEval_hermiteAuxiliary_eq_insertionRow]
  obtain ⟨ω, _, hωi, hw⟩ := exists_sq_eq_neg_of_im_neg ht
  let p := hermiteAuxiliary (β : ℂ) ((γ : ℂ) * t) n
  have hroots : ∀ z, (p.comp (C ω * X)).IsRoot z → 0 < z.im := by
    intro z hz
    have hz' : p.IsRoot (ω * z) := by simpa [IsRoot.def] using hz
    have hh := im_mul_conj_pos_of_isRoot_hermiteAuxiliary hβ hγ hωi hw hz'
    have he : (ω * z) * starRingEnd ℂ ω = (ω * starRingEnd ℂ ω) * z := by ring
    rw [he] at hh
    simp only [Complex.mul_conj, Complex.ofReal_im,
      Complex.ofReal_re, Complex.mul_im, zero_mul, add_zero] at hh
    have hn : 0 ≤ Complex.normSq ω := Complex.normSq_nonneg _
    nlinarith
  have hn := gaussianEval_ne_zero_of_roots_im_pos hc hroots
  rw [gaussianEval_comp_C_mul_X] at hn
  have hs : ω ^ 2 * (-(c : ℂ)) = (c : ℂ) * t := by rw [hw]; ring
  rwa [hs] at hn

/-- Completed-square quartics with nonnegative parameters have real-rooted insertion rows. -/
theorem insertionRow_isRealRooted_quartic_square {β γ c : ℝ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hc : 0 ≤ c) (n : ℕ) :
    let w := markedBlockWeights
      (C (γ + c * β ^ 2) * X ^ 2 + C (2 * c * β) * X ^ 3 + C c * X ^ 4)
    insertionRow w n ≠ 0 ∧ (insertionRow w n).Splits := by
  dsimp only
  let p := insertionRow (markedBlockWeights
    (C (γ + c * β ^ 2) * X ^ 2 + C (2 * c * β) * X ^ 3 + C c * X ^ 4)) n
  have hn : ∀ z : ℂ, z.im < 0 → (complexify p).eval z ≠ 0 := by
    intro z hz
    simpa only [complexify, eval_map] using
      eval₂_insertionRow_quartic_square_ne_zero hβ hγ hc hz n
  have hp : p ≠ 0 := by
    intro he
    have hh := hn (-Complex.I) (by simp)
    simp [he] at hh
  refine ⟨hp, IsUpperHalfPlaneStable.splits_complexify ?_⟩
  intro z hz he
  exact hn (starRingEnd ℂ z) (by simpa using hz)
    (complexify_conj_root he)

/-- Theorem A: the quartic exponential rows are real-rooted when `b² ≤ 4ac`.
The proof includes `a = 0` and `b = 0`; no root-continuity theorem is used. -/
theorem insertionRow_isRealRooted_quartic_of_disc_le {a b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 < c) (hdisc : b ^ 2 ≤ 4 * a * c) (n : ℕ) :
    let w := markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)
    insertionRow w n ≠ 0 ∧ (insertionRow w n).Splits := by
  let β := b / (2 * c)
  let γ := a - b ^ 2 / (4 * c)
  have hβ : 0 ≤ β := div_nonneg hb (by positivity)
  have hγ : 0 ≤ γ := by
    dsimp [γ]
    rw [sub_nonneg, div_le_iff₀ (by positivity : 0 < 4 * c)]
    nlinarith
  have he1 : γ + c * β ^ 2 = a := by
    dsimp [γ, β]
    field_simp [hc.ne']
    ring
  have he2 : 2 * c * β = b := by
    dsimp [β]
    field_simp [hc.ne']
  simpa only [he1, he2] using insertionRow_isRealRooted_quartic_square hβ hγ hc.le n

/-- For every nonnegative triple `a,b,c`, all quartic exponential insertion rows
are nonzero and have only real zeros. This combines Theorems A and C. -/
theorem insertionRow_isRealRooted_quartic_of_nonneg {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) :
    let w := markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)
    insertionRow w n ≠ 0 ∧ (insertionRow w n).Splits := by
  by_cases hc0 : c = 0
  · subst c
    by_cases hb0 : b = 0
    · subst b
      simpa [blockProduct_eq] using insertionRow_isRealRooted_of_blockProduct ha
        (ρ := fun _ => 0) (fun _ => le_rfl) (fun _ _ _ => le_rfl) 0 n
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have he : C b * blockProduct (fun _ => a / b) 1 =
          C a * X ^ 2 + C b * X ^ 3 := by
        simp only [blockProduct_eq, Finset.prod_range_one]
        have hab : b * (a / b) = a := mul_div_cancel₀ a hb0
        calc
          _ = C (b * (a / b)) * X ^ 2 + C b * X ^ 3 := by
            simp only [map_mul]; ring
          _ = _ := by rw [hab]
      simpa [he] using insertionRow_isRealRooted_of_blockProduct hbp.le
        (ρ := fun _ => a / b) (fun _ => div_nonneg ha hb)
        (fun _ _ _ => le_rfl) 1 n
  · have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    rcases le_total (b ^ 2) (4 * a * c) with hdisc | hdisc
    · exact insertionRow_isRealRooted_quartic_of_disc_le hb hcp hdisc n
    · exact insertionRow_isRealRooted_quartic ha hb hcp hdisc n

end RealRooted.ExponentialRows
