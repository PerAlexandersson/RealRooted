/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.CombinatorialExamples.ZigzagEulerian.Degree
import RealRooted.IntervalDifferential.UniversalTransfer
import RealRooted.IntervalDifferential.MobiusRoots

/-!
# From the centered quotient to the actual zig-zag polynomial

This is the final algebraic reduction in the proof of `thm:zigzagEulerian`.
The parity identity and complex root disk are explicit inputs here.
`ZigzagEulerian.RealRooted` proves these inputs for the actual finite permutation
quotient and obtains the unconditional paper theorem.
-/

open Polynomial RealRooted.IntervalDifferential

noncomputable section

namespace RealRooted.ZigzagEulerian

/-- The centered parity and disk statements imply exact degree and simple
negative roots for the actual alternating-permutation swap enumerator. -/
theorem zigzagEulerianPolynomial_roots_of_centered_disk (n : ℕ) (hn : 5 ≤ n)
    (hparity : (zigzagCenteredQuotient n).comp (-X) = zigzagCenteredQuotient n ∨
      (zigzagCenteredQuotient n).comp (-X) = -zigzagCenteredQuotient n)
    (hdisk : ∀ c : ℂ,
      ((zigzagCenteredQuotient n).map (algebraMap ℝ ℂ)).eval c = 0 →
        Complex.normSq c ≤ 13 / 3) :
    (zigzagEulerianPolynomial n).natDegree = n - 2 ∧
      (zigzagEulerianPolynomial n).Splits ∧
      (zigzagEulerianPolynomial n).roots.Nodup ∧
      ∀ r ∈ (zigzagEulerianPolynomial n).roots, r < 0 := by
  have hn2 : 2 ≤ n := by lia
  have hQ0 := zigzagCenteredQuotient_ne_zero n hn2
  have hQdeg := zigzagCenteredQuotient_natDegree n hn2
  obtain ⟨hsplit, hsimple, hbounds⟩ :=
    zigzagTransform_parity_roots_of_disk (zigzagCenteredQuotient n) hQ0
      (by rw [hQdeg]; lia) hparity hdisk
  have hGdeg : (zigzagTransform (zigzagCenteredQuotient n)).natDegree = n - 2 := by
    rw [zigzagTransform_natDegree, hQdeg]
  have hresult := splits_roots_nodup_neg_of_mobius_eval
    (H := zigzagEulerianPolynomial n) (G := zigzagTransform (zigzagCenteredQuotient n))
    (zigzagEulerianPolynomial_ne_zero n)
    (by rw [hGdeg]; exact zigzagEulerianPolynomial_natDegree_le_sub_two hn2)
    (zigzagTransform_ne_zero _ hQ0) hsplit hsimple hbounds
    (by
      intro z hzL _ hzroot
      have hz : z + 1 ≠ 0 := by linarith
      have heval := zigzagCenteredQuotient_eval_identity n hn2 z hz
      rw [hzroot, mul_zero] at heval
      exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hz))
  simpa only [hGdeg] using hresult

end RealRooted.ZigzagEulerian
