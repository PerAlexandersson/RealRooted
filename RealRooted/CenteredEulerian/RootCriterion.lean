/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CenteredEulerian.Basis
import RealRooted.Mathlib.LinearAlgebra.Matrix.WeightedColumnBound
import Mathlib.Algebra.BigOperators.Field

/-!
# The finite weighted-sum criterion (Appendix B.1)

Ported from Aristotle task `61da6424-89ea-4fbf-852c-6e47d3e3aef9`,
following the compendium zig-zag proof, Appendix B.

If the weighted column sums of `R` are uniformly below `ρ = 13/3`, then all complex roots of
`p_n` (`n ≥ 2`) satisfy `|c|² < 13/3`.
-/

@[expose] public section

open PowerSeries

namespace RealRooted.CenteredEulerian

/-- The weights `ω_0 = ω_1 = 1`, `ω_j = 2` for `j ≥ 2`. -/
noncomputable def columnWeight (j : ℕ) : ℝ := if j < 2 then 1 else 2

lemma columnWeight_pos (j : ℕ) : 0 < columnWeight j := by
  unfold columnWeight
  split_ifs <;> norm_num

lemma columnWeight_le_two (j : ℕ) : columnWeight j ≤ 2 := by
  unfold columnWeight
  split_ifs <;> norm_num

/-- The column bound (B.1). -/
def ColumnBound : Prop :=
  ∀ N j : ℕ, ∑ i ∈ Finset.range N, columnWeight i * |rMat i j| < 13 / 3 * columnWeight j

lemma rMat_eq_zero_of_lt {i j : ℕ} (h : i + 2 < j) : rMat i j = 0 := by
  rw [rMat, mMat]
  apply Finset.sum_eq_zero
  intro k hk
  simp at hk
  rw [beta_eq_zero_of_lt (by lia), mul_zero]

/-- Complex evaluation of `p_n`. -/
noncomputable def pC (n : ℕ) (c : ℂ) : ℂ := Polynomial.aeval c (polynomial n)

lemma pC_rel (i : ℕ) (c : ℂ) :
    c ^ 2 * pC (i + 2) c = ∑ j ∈ Finset.range (i + 3), (rMat i j : ℂ) * pC (j + 2) c := by
  have h := congrArg (Polynomial.aeval c) (X_sq_mul_polynomial' i)
  rw [map_mul, map_pow, Polynomial.aeval_X, map_sum] at h
  rw [pC, h]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, Polynomial.aeval_C, pC]
  rfl

lemma pC_two (c : ℂ) : pC 2 c = (c ^ 2 - 1) / 2 := by
  rw [pC, polynomial_two]
  simp [Polynomial.aeval_C]
  ring

lemma pC_three (c : ℂ) : pC 3 c = c * (c ^ 2 - 1) / 3 := by
  rw [pC, polynomial_three]
  simp [Polynomial.aeval_C]
  ring

/-- Restricting a recurrence to the parity of its terminal index preserves it below that index. -/
private lemma parity_restriction_relation {N : ℕ} {c : ℂ} (v v' : ℕ → ℂ)
    (hv' : ∀ j, v' j = if (Even j ↔ Even N) then v j else 0)
    (hvN : v N = 0)
    (hrel : ∀ i, c ^ 2 * v i =
      ∑ j ∈ Finset.range (i + 3), (rMat i j : ℂ) * v j) :
    ∀ i, i < N → c ^ 2 * v' i =
      ∑ j ∈ Finset.range N, (rMat i j : ℂ) * v' j := by
  have hv'N : v' N = 0 := by
    rw [hv' N]
    simp only [iff_self, ite_true, hvN]
  intro i hi
  by_cases hpar : Even i ↔ Even N
  · have hv'i : v' i = v i := by rw [hv' i]; simp only [hpar, ite_true]
    rw [hv'i, hrel i]
    have hterm : ∀ j, (rMat i j : ℂ) * v j = (rMat i j : ℂ) * v' j := by
      intro j
      by_cases hj : Even j ↔ Even N
      · rw [hv' j]
        simp only [hj, ite_true]
      · rw [rMat_parity (by tauto)]
        simp
    simp_rw [hterm]
    set L := N + i + 3
    have e1 : ∑ j ∈ Finset.range (i + 3), (rMat i j : ℂ) * v' j =
        ∑ j ∈ Finset.range L, (rMat i j : ℂ) * v' j := by
      apply Finset.sum_subset
      · intro j hj
        simp at hj ⊢
        lia
      · intro j hj hj'
        simp at hj hj'
        rw [rMat_eq_zero_of_lt (by lia)]
        simp
    have e2 : ∑ j ∈ Finset.range N, (rMat i j : ℂ) * v' j =
        ∑ j ∈ Finset.range L, (rMat i j : ℂ) * v' j := by
      apply Finset.sum_subset
      · intro j hj
        simp at hj ⊢
        lia
      · intro j hj hj'
        simp at hj hj'
        by_cases hjN : j = N
        · rw [hjN, hv'N, mul_zero]
        · have hpi : i % 2 = N % 2 := by
            rcases Nat.even_or_odd i with h1 | h1
            · have := hpar.mp h1
              rw [Nat.even_iff.mp h1, Nat.even_iff.mp this]
            · have : ¬ Even N := fun h2 => (Nat.not_even_iff_odd.mpr h1) (hpar.mpr h2)
              rw [Nat.odd_iff.mp h1, Nat.odd_iff.mp (Nat.not_even_iff_odd.mp this)]
          have : N ≥ i + 2 := by lia
          rw [rMat_eq_zero_of_lt (by lia)]
          simp
    rw [e1, e2]
  · rw [hv' i]
    simp only [hpar, ite_false, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : Even j ↔ Even N
    · rw [rMat_parity (by tauto)]
      simp
    · rw [hv' j]
      simp only [hj, ite_false, mul_zero]

/-- The parity-restricted normalized values before a terminal root are not all zero. -/
private lemma exists_ne_zero_parity_normalized_pC {N : ℕ} {c : ℂ}
    (hc1 : c ^ 2 - 1 ≠ 0) (hc0 : c ≠ 0) (hc : pC (N + 2) c = 0) :
    ∃ j ∈ Finset.range N,
      (if (Even j ↔ Even N) then pC (j + 2) c / (c ^ 2 - 1) else 0) ≠ 0 := by
  rcases Nat.even_or_odd N with hN | hN
  · rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      subst h0
      apply hc1
      rw [pC_two] at hc
      linear_combination 2 * hc
    · refine ⟨0, Finset.mem_range.mpr h0, ?_⟩
      simp only [Even.zero, hN, iff_self, ite_true]
      rw [pC_two]
      field_simp
      norm_num
  · rcases Nat.lt_or_ge N 2 with h1 | h1
    · exfalso
      have hN1 : N = 1 := by obtain ⟨r, hr⟩ := hN; lia
      subst hN1
      rw [pC_three] at hc
      rcases mul_eq_zero.mp (by linear_combination 3 * hc : c * (c ^ 2 - 1) = 0) with h | h
      · exact hc0 h
      · exact hc1 h
    · refine ⟨1, Finset.mem_range.mpr (by lia), ?_⟩
      have hodd : ¬ Even N := Nat.not_even_iff_odd.mpr hN
      simp only [show ¬ Even 1 by decide, hodd, iff_self, ite_true]
      rw [pC_three]
      field_simp
      exact div_ne_zero hc0 (by norm_num)

/-- The weighted-sum criterion: the column bound implies the root bound. -/
theorem root_bound_of_columnBound (hcol : ColumnBound) {n : ℕ} (hn : 2 ≤ n) {c : ℂ}
    (hc : pC n c = 0) : Complex.normSq c < 13 / 3 := by
  by_cases hc1 : c ^ 2 - 1 = 0
  · have : c ^ 2 = 1 := by linear_combination hc1
    have h2 : Complex.normSq c ^ 2 = 1 := by
      rw [← map_pow, this, map_one]
    have h3 : Complex.normSq c = 1 := by
      have h0 := Complex.normSq_nonneg c
      nlinarith
    rw [h3]; norm_num
  by_cases hc0 : c = 0
  · rw [hc0, map_zero]; norm_num
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by lia⟩
  set v : ℕ → ℂ := fun j => pC (j + 2) c / (c ^ 2 - 1) with hv
  set v' : ℕ → ℂ := fun j => if (Even j ↔ Even N) then v j else 0 with hv'
  have hvN : v N = 0 := by rw [hv]; simp only; rw [hc, zero_div]
  have hrel : ∀ i, c ^ 2 * v i = ∑ j ∈ Finset.range (i + 3), (rMat i j : ℂ) * v j := by
    intro i
    simp only [hv]
    rw [mul_div_assoc', pC_rel, Finset.sum_div]
    apply Finset.sum_congr rfl; intro j _; ring
  have hrel' : ∀ i, i < N →
      c ^ 2 * v' i = ∑ j ∈ Finset.range N, (rMat i j : ℂ) * v' j := by
    exact parity_restriction_relation v v' (fun j => by rw [hv']) hvN hrel
  have hex : ∃ j ∈ Finset.range N, v' j ≠ 0 := by
    simpa only [hv', hv] using exists_ne_zero_parity_normalized_pC hc1 hc0 hc
  have hbound := Matrix.norm_lt_of_weighted_column_sum_lt
    (fun i j : Fin N => (rMat i j : ℂ)) (fun i : Fin N => columnWeight i)
    (fun i => columnWeight_pos i) (13 / 3)
    (fun j => by
      rw [Fin.sum_univ_eq_sum_range
        (fun i => columnWeight i * ‖(rMat i j : ℂ)‖) N]
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hcol N j)
    (c ^ 2) (fun j : Fin N => v' j)
    (by obtain ⟨j, hj, hj0⟩ := hex; exact ⟨⟨j, Finset.mem_range.mp hj⟩, hj0⟩)
    (fun i => by
      rw [Fin.sum_univ_eq_sum_range (fun j => (rMat i j : ℂ) * v' j) N]
      exact hrel' i i.isLt)
  simpa only [norm_pow, Complex.normSq_eq_norm_sq] using hbound

end RealRooted.CenteredEulerian
