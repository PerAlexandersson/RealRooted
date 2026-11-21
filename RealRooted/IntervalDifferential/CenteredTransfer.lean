/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.Basic
import RealRooted.IntervalDifferential.CenteredBasis
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Splits
import RealRooted.IntervalDifferential.UniversalTransfer
import RealRooted.IntervalDifferential.MobiusRoots
import RealRooted.IntervalDifferential.Degree
import Mathlib.Tactic

/-!
# From a centered root disk to simple negative roots

This sequence-independent version of the zig-zag transfer combines the finite
basis identity with the universal disk transfer and the Möbius root map.
It supplies the algebraic reduction proposed for Cao--Fu,
*Real-rooted Ehrhart h*-polynomials of crown posets and wheel and whirl matroids*,
arXiv:2610.40496v1, Theorem 1.1. The application-specific centered-disk estimate
and the identification of the crown numerator remain separate obligations.
-/

public section

open Polynomial Finset

noncomputable section

namespace RealRooted.IntervalDifferential

/-- A coefficient expansion in a centered parity polynomial of degree at least three
transfers a closed squared-radius `13/3` root disk to simple negative roots. -/
theorem transfer_of_centered_disk (D : ℕ) (hD : 3 ≤ D) (H Q : ℝ[X]) (hH0 : H ≠ 0)
    (hHdeg : H.natDegree ≤ D)
    (hQ : Q = ∑ i ∈ range (D + 1), C (H.coeff i) * zigzagBasis i (D - i))
    (hQdeg : Q.natDegree = D)
    (hparity : Q.comp (-X) = Q ∨ Q.comp (-X) = -Q)
    (hdisk : ∀ c : ℂ, (Q.map (algebraMap ℝ ℂ)).eval c = 0 →
      Complex.normSq c ≤ 13 / 3) :
    H.natDegree = D ∧ H.Splits ∧ H.roots.Nodup ∧ ∀ r ∈ H.roots, r < 0 := by
  have hQ0 : Q ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hQdeg
    lia
  obtain ⟨hsplit, hsimple, hbounds⟩ :=
    zigzagTransform_parity_roots_of_disk Q hQ0 (by rw [hQdeg]; exact hD) hparity hdisk
  have hGdeg : (zigzagTransform Q).natDegree = D := by
    rw [zigzagTransform_natDegree, hQdeg]
  have hresult := splits_roots_nodup_neg_of_mobius_eval
    (H := H) (G := zigzagTransform Q) hH0 (by rw [hGdeg]; exact hHdeg)
    (zigzagTransform_ne_zero Q hQ0) hsplit hsimple hbounds (by
      intro z hzL _ hzroot
      have hz : z + 1 ≠ 0 := by linarith
      have heval := zigzagTransform_coeff_sum_eval D H hHdeg z hz
      rw [← hQ, hzroot, mul_zero] at heval
      exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hz))
  simpa only [hGdeg] using hresult

end RealRooted.IntervalDifferential
