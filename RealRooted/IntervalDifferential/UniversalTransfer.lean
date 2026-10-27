/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import RealRooted.IntervalDifferential.FactorShapes
import RealRooted.IntervalDifferential.QuarticBounds
import RealRooted.IntervalDifferential.LinearInsertion
import RealRooted.IntervalDifferential.QuadraticInsertion
import RealRooted.IntervalDifferential.ParityQuarticFactor
import RealRooted.Mathlib.Algebra.Polynomial.RealQuadraticFactor
import RealRooted.IntervalDifferential.Degree
import RealRooted.IntervalDifferential.CubicDisk
public import RealRooted.IntervalDifferential.Basic
import Mathlib.Analysis.Polynomial.Factorization
import Mathlib.Tactic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Universal transfer for the centered zigzag operator

Appendix C.4 of `alternating_eulerian_shorter_proof.md`: a cubic or quartic
seed, followed by real linear and conjugate-pair insertions, transfers a
complex root disk for a parity polynomial to simple roots in `(-1,1)`.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace RealRooted.IntervalDifferential

private def intervalSimple (F : ℝ[X]) : Prop :=
  F.Splits ∧ F.roots.Nodup ∧ ∀ r ∈ F.roots, -1 < r ∧ r < 1

private theorem intervalSimple_of_monic_remainder (S R : ℝ[X])
    (hS0 : S ≠ 0) (hSdeg : 4 ≤ S.natDegree)
    (hSgood : intervalSimple (zigzagTransform S))
    (hRmonic : R.Monic)
    (hRdisk : ∀ c : ℂ, (R.map (algebraMap ℝ ℂ)).eval c = 0 →
      Complex.normSq c ≤ 13 / 3) :
    intervalSimple (zigzagTransform (R * S)) := by
  have main : ∀ n (T : ℝ[X]), T.natDegree = n → T.Monic →
      (∀ c : ℂ, (T.map (algebraMap ℝ ℂ)).eval c = 0 →
        Complex.normSq c ≤ 13 / 3) →
      intervalSimple (zigzagTransform (T * S)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hTdeg hTmonic hTdisk
      by_cases hn : n = 0
      · have hT1 : T = 1 := eq_one_of_monic_natDegree_zero hTmonic (hTdeg.trans hn)
        simpa only [hT1, one_mul] using hSgood
      · have hn0 : 0 < n := by lia
        have hmonicDegree : IsMonicOfDegree T (n - 1 + 1) := by
          refine ⟨?_, hTmonic⟩
          rw [hTdeg]
          lia
        obtain ⟨A, U, hA, hfactor⟩ :=
          hmonicDegree.eq_isMonicOfDegree_one_or_two_mul
        have hAmonic : A.Monic := hA.elim (·.monic) (·.monic)
        have hAUmonic : (A * U).Monic := hfactor ▸ hTmonic
        have hUmonic : U.Monic := hAmonic.of_mul_monic_left hAUmonic
        have hUdeg : U.natDegree < n := by
          have hsum := hAmonic.natDegree_mul hUmonic
          rw [← hfactor, hTdeg] at hsum
          rcases hA with hA | hA <;> rw [hA.natDegree_eq] at hsum <;> lia
        have hAdisk : ∀ c : ℂ, (A.map (algebraMap ℝ ℂ)).eval c = 0 →
            Complex.normSq c ≤ 13 / 3 :=
          root_normSq_le_of_dvd ⟨U, hfactor⟩ hTdisk
        have hUdisk : ∀ c : ℂ, (U.map (algebraMap ℝ ℂ)).eval c = 0 →
            Complex.normSq c ≤ 13 / 3 :=
          root_normSq_le_of_dvd
            ⟨A, by rw [hfactor]; ring⟩ hTdisk
        have hFgood : intervalSimple (zigzagTransform (U * S)) :=
          ih U.natDegree hUdeg U rfl hUmonic hUdisk
        let F := zigzagTransform (U * S)
        have hF0 : F ≠ 0 :=
          zigzagTransform_ne_zero (U * S) (mul_ne_zero hUmonic.ne_zero hS0)
        have hFdeg : 4 ≤ F.natDegree := by
          rw [show F = zigzagTransform (U * S) by rfl, zigzagTransform_natDegree]
          rw [hUmonic.natDegree_mul' hS0]
          lia
        rcases hA with hA | hA
        · let a := -A.coeff 0
          have hAsh : A = X - C a := by
            rw [hA.monic.eq_X_add_C hA.natDegree_eq]
            simp [a]
          have haDisk : a ^ 2 ≤ 13 / 3 := by
            apply real_linear_sq_le_of_disk a
            simpa only [hAsh] using hAdisk
          have haL : -3 < a := by nlinarith
          have haR : a < 3 := by nlinarith
          have hnext := zigzagLinearFactor_roots F a
            hFgood.1 hF0 hFgood.2.1 hFgood.2.2 haL haR
          simpa only [intervalSimple, hfactor, hAsh, mul_assoc,
            zigzagTransform_linear_mul, zigzagLinearFactor, F] using hnext
        · rcases hA.monic.eq_mul_X_sub_C_or_sq_add_C_sq hA.natDegree_eq with
            ⟨a, t, hAsh⟩ | ⟨a, b, _, hAsh⟩
          · have haDisk : a ^ 2 ≤ 13 / 3 := by
              apply real_linear_sq_le_of_disk a
              exact root_normSq_le_of_dvd
                (P := (X - C a : ℝ[X])) (Q := A) ⟨X - C t, hAsh⟩ hAdisk
            have htDisk : t ^ 2 ≤ 13 / 3 := by
              apply real_linear_sq_le_of_disk t
              exact root_normSq_le_of_dvd
                (P := (X - C t : ℝ[X])) (Q := A)
                ⟨X - C a, by rw [hAsh]; ring⟩ hAdisk
            have haL : -3 < a := by nlinarith
            have haR : a < 3 := by nlinarith
            have htL : -3 < t := by nlinarith
            have htR : t < 3 := by nlinarith
            let G := zigzagLinearFactor t F
            have hGgood : intervalSimple G :=
              zigzagLinearFactor_roots F t
                hFgood.1 hF0 hFgood.2.1 hFgood.2.2 htL htR
            have hG0 : G ≠ 0 := zigzagLinearFactor_ne_zero t F hF0
            have hnext := zigzagLinearFactor_roots G a
              hGgood.1 hG0 hGgood.2.1 hGgood.2.2 haL haR
            simpa only [intervalSimple, hfactor, hAsh, mul_assoc,
              zigzagTransform_linear_mul, zigzagLinearFactor, F, G] using hnext
          · have hpair : a ^ 2 + b ^ 2 ≤ 13 / 3 := by
              apply real_pair_sq_le_of_disk a b
              simpa only [hAsh] using hAdisk
            have hnext := zigzagQuadraticFactor_roots F a b
              hFgood.1 hFgood.2.1 hFdeg hFgood.2.2 hpair
            simpa only [intervalSimple, hfactor, hAsh, mul_assoc,
              zigzagTransform_quadratic_mul, F]
              using hnext
  exact main R.natDegree R rfl hRmonic hRdisk

private theorem quartic_seed_monic_natDegree (k p : ℝ) :
    (X ^ 4 + C k * X ^ 2 + C p : ℝ[X]).Monic ∧
      (X ^ 4 + C k * X ^ 2 + C p : ℝ[X]).natDegree = 4 := by
  have hlow : (C k * X ^ 2 + C p : ℝ[X]).natDegree ≤ 2 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le k (X ^ 2)).trans (by simp)
    · simp
  have hdegree : (C k * X ^ 2 + C p : ℝ[X]).degree < 4 :=
    lt_of_le_of_lt (degree_le_of_natDegree_le hlow) (by norm_num)
  constructor
  · simpa only [add_assoc] using (monic_X_pow_add hdegree)
  · have hlt : (C k * X ^ 2 + C p : ℝ[X]).natDegree <
        (X ^ 4 : ℝ[X]).natDegree := by
        rw [natDegree_X_pow]
        lia
    rw [add_assoc, natDegree_add_eq_left_of_natDegree_lt hlt]
    simp

/-- Universal centered transfer, Appendix C.4: a real parity polynomial of
degree at least three with every complex root in the closed squared-radius
`13/3` disk transforms to a polynomial with simple roots in `(-1,1)`. -/
theorem zigzagTransform_parity_roots_of_disk (Q : ℝ[X]) (hQ0 : Q ≠ 0)
    (hdeg : 3 ≤ Q.natDegree)
    (hparity : Q.comp (-X) = Q ∨ Q.comp (-X) = -Q)
    (hroot : ∀ c : ℂ, (Q.map (algebraMap ℝ ℂ)).eval c = 0 →
      Complex.normSq c ≤ 13 / 3) :
    (zigzagTransform Q).Splits ∧ (zigzagTransform Q).roots.Nodup ∧
      ∀ r ∈ (zigzagTransform Q).roots, -1 < r ∧ r < 1 := by
  let M := normalize Q
  have hMmonic : M.Monic := monic_normalize hQ0
  have hMdeg : M.natDegree = Q.natDegree := natDegree_normalize
  have hMroot : ∀ c : ℂ, (M.map (algebraMap ℝ ℂ)).eval c = 0 →
      Complex.normSq c ≤ 13 / 3 :=
    root_normSq_le_of_dvd (normalize_dvd_iff.mpr dvd_rfl) hroot
  have hMform : M = C Q.leadingCoeff⁻¹ * Q := by
    rw [show M = normalize Q by rfl, normalize_apply,
      coe_normUnit_of_ne_zero hQ0, mul_comm]
  have hMparity : M.comp (-X) = M ∨ M.comp (-X) = -M := by
    rcases hparity with heven | hodd
    · left
      rw [hMform, mul_comp, C_comp, heven]
    · right
      rw [hMform, mul_comp, C_comp, hodd]
      ring
  have hMgood : intervalSimple (zigzagTransform M) := by
    by_cases hthree : M.natDegree = 3
    · obtain ⟨k, hshape⟩ := monic_parity_cubic_shape hMmonic hthree hMparity
      rw [hshape] at hMroot ⊢
      exact zigzagTransform_cubic_roots_of_disk k hMroot
    · have hfour : 4 ≤ M.natDegree := by lia
      obtain ⟨k, p, hfactor⟩ :=
        exists_even_quartic_divisor_of_parity M hfour hMparity
      let S : ℝ[X] := X ^ 4 + C k * X ^ 2 + C p
      have hSmonic : S.Monic := (quartic_seed_monic_natDegree k p).1
      have hSdegree : S.natDegree = 4 := (quartic_seed_monic_natDegree k p).2
      have hS0 : S ≠ 0 := hSmonic.ne_zero
      have hSdvd : S ∣ M := hfactor
      obtain ⟨R, hMR⟩ := hSdvd
      have hSdvd : S ∣ M := ⟨R, hMR⟩
      have hSRmonic : (S * R).Monic := hMR ▸ hMmonic
      have hRmonic : R.Monic := hSmonic.of_mul_monic_left hSRmonic
      have hSdisk : ∀ c : ℂ, (S.map (algebraMap ℝ ℂ)).eval c = 0 →
          Complex.normSq c ≤ 13 / 3 := root_normSq_le_of_dvd hSdvd hMroot
      have hRdisk : ∀ c : ℂ, (R.map (algebraMap ℝ ℂ)).eval c = 0 →
          Complex.normSq c ≤ 13 / 3 :=
        root_normSq_le_of_dvd (P := R) (Q := M)
          ⟨S, by rw [hMR]; ring⟩ hMroot
      have hSgood : intervalSimple (zigzagTransform S) :=
        zigzagTransform_quartic_roots_of_disk k p hSdisk
      have hresult := intervalSimple_of_monic_remainder S R hS0
        (by rw [hSdegree]) hSgood hRmonic hRdisk
      simpa only [hMR, mul_comm] using hresult
  have hQlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
  have hQform : Q = C Q.leadingCoeff * M := by
    rw [hMform, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hQlc, map_one, one_mul]
  rw [hQform, zigzagTransform_C_mul]
  refine ⟨hMgood.1.C_mul _, ?_, ?_⟩
  · simpa only [roots_C_mul _ hQlc] using hMgood.2.1
  · intro r hr
    rw [roots_C_mul _ hQlc] at hr
    exact hMgood.2.2 r hr

end RealRooted.IntervalDifferential
