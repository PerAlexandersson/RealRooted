module

public import RealRooted.EffectiveBKW.Certificate.IsolatedRoot
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!+# The right endpoint of the tiling pair region

The cubic `16t³ + 37t² + 24t + 2` has exactly one real zero. We isolate it by
the Bernstein checker and exclude the unbounded left ray by a sum of squares.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.Tiling4

open Set
open BigDescents321.SmallCases

/-- Integer coefficients of the discriminant factor, in ascending order. -/
def edgeCoeffs : IntPoly := [2, 24, 37, 16]

/-- The cubic discriminant factor. -/
def edgeFunction (t : ℝ) : ℝ := 16 * t ^ 3 + 37 * t ^ 2 + 24 * t + 2

/-- The integer-list polynomial evaluates to the displayed cubic. -/
theorem eval_edgeCoeffs (t : ℝ) : edgeCoeffs.eval t = edgeFunction t := by
  simp only [edgeCoeffs, edgeFunction, IntPoly.eval, IntPoly.polynomial, ofList_cons, ofList_nil,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  norm_num
  ring

/-- A rational isolating interval for the endpoint. -/
def edgeCertificate : IsolatedRoot where
  p := edgeCoeffs
  lo := ⟨-1, 10⟩
  hi := ⟨-9, 100⟩

/-- Kernel verification of the endpoint certificate. -/
theorem edgeCertificate_check : edgeCertificate.check = true := by decide +kernel

/-- The certified real root of the discriminant cubic. -/
noncomputable def rightEdge : ℝ :=
  (IsolatedRoot.check_sound edgeCertificate_check).choose

/-- The endpoint lies strictly between `-1/10` and `-9/100`. -/
theorem rightEdge_mem : rightEdge ∈ Ioo (-1 / 10 : ℝ) (-9 / 100) := by
  have h := (IsolatedRoot.check_sound edgeCertificate_check).choose_spec.1.1
  simpa only [rightEdge, edgeCertificate, QNum.val, Int.cast_neg, Int.cast_one, Nat.cast_ofNat,
    Int.cast_ofNat] using h

/-- The endpoint is a zero of the discriminant cubic. -/
@[simp] theorem edgeFunction_rightEdge : edgeFunction rightEdge = 0 := by
  have h := (IsolatedRoot.check_sound edgeCertificate_check).choose_spec.1.2
  change edgeCoeffs.eval rightEdge = 0 at h
  rwa [eval_edgeCoeffs] at h

/-- In particular, the right endpoint is negative. -/
theorem rightEdge_neg : rightEdge < 0 := lt_trans rightEdge_mem.2 (by norm_num)

private theorem edgeFunction_neg_of_le {t : ℝ} (ht : t ≤ -1 / 10) :
    edgeFunction t < 0 := by
  let u := -t - 1 / 10
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hsum : 0 ≤ 16 * u * (u - 161 / 160) ^ 2 + (1407 / 1600 : ℝ) * u := by
    positivity
  have heq : edgeFunction t =
      -(16 * u * (u - 161 / 160) ^ 2 + (1407 / 1600 : ℝ) * u + 23 / 500) := by
    dsimp [edgeFunction, u]
    ring
  rw [heq]
  linarith

private theorem strictMonoOn_edgeFunction :
    StrictMonoOn edgeFunction (Ici (-1 / 10 : ℝ)) := by
  intro a ha b hb hab
  have hs : 0 ≤ a ^ 2 + a * b + b ^ 2 := by
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  have hf : 0 < 16 * (a ^ 2 + a * b + b ^ 2) + 37 * (a + b) + 24 := by
    simp only [mem_Ici] at ha hb
    linarith
  have hp := mul_pos (sub_pos.mpr hab) hf
  dsimp [edgeFunction]
  nlinarith

/-- The discriminant factor is negative precisely on the ray to the left of the endpoint. -/
theorem edgeFunction_neg_iff (t : ℝ) : edgeFunction t < 0 ↔ t < rightEdge := by
  constructor
  · intro ht
    by_contra h
    have hle : rightEdge ≤ t := le_of_not_gt h
    have hm := strictMonoOn_edgeFunction.monotoneOn
      rightEdge_mem.1.le (rightEdge_mem.1.le.trans hle) hle
    rw [edgeFunction_rightEdge] at hm
    linarith
  · intro ht
    by_cases hlo : t ≤ -1 / 10
    · exact edgeFunction_neg_of_le hlo
    · have hm := strictMonoOn_edgeFunction (le_of_not_ge hlo) rightEdge_mem.1.le ht
      simpa only [edgeFunction_rightEdge] using hm

/-- The endpoint is the unique real zero of the cubic, including outside its isolating interval. -/
theorem edgeFunction_eq_zero_iff (t : ℝ) : edgeFunction t = 0 ↔ t = rightEdge := by
  constructor
  · intro ht
    have hlo : -1 / 10 ≤ t := by
      by_contra h
      have hn := edgeFunction_neg_of_le (le_of_not_ge h)
      rw [ht] at hn
      exact (lt_irrefl 0) hn
    exact strictMonoOn_edgeFunction.injOn hlo rightEdge_mem.1.le (ht.trans
      edgeFunction_rightEdge.symm)
  · rintro rfl
    exact edgeFunction_rightEdge

end RealRooted.EffectiveBKW.Tiling4
