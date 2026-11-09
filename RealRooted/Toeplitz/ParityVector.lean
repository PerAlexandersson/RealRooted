module

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
public import Mathlib.RingTheory.Polynomial.Wronskian
public import RealRooted.SimpleRoots
import RealRooted.Toeplitz.HessenbergWronskian
public import RealRooted.Toeplitz.ParityRows
import RealRooted.Toeplitz.TP2HessenbergStrict
import RealRooted.Interlacing.OuterDifference

/-!
# The vector recursion of the parity block matrix

Let `A` satisfy the hypotheses of the TP2 Hessenberg certificate with `A 0 0 > 0`, and let
`B = parityBlock A` (size `2 q`) with vector recursion `f_m = (B + X J)ᵐ 𝟙`. Write `0` for the first
index and `ι = parityIndex n` for the first index of the second block.

* The Wronskian `W(f_{m,0}, f_{m,ι})` of the two first coordinates is bounded below pointwise by
  `c₀^{2(m-1)} s > 0` (`le_eval_wronskian_parityBlock`), with `c₀ = A 0 0` and `s = ∑ⱼ A 0 j`:
  the matrix minor in rows `0, ι`, columns `0, ι` is `c₀²`, and at `m = 1` the Wronskian is `s`.
  Hence `f_{m,0}` and `f_{m,ι}` have no common root and both have simple roots.
* At a root `r` of `f_{m,0}` all `f_{m,j}(r)` have the sign of `-f_{m,0}'(r)`, and
  `f_{m+1,ι}(r) = ∑ⱼ A 0 j f_{m,q+j}(r)` has a nonzero term, so `f_{m,0}` and `f_{m+1,ι}` have no
  common root either.
* Reflecting `u ↦ -u` and multiplying by `(-1)ᵐ`, the polynomials `U_m = (-1)ᵐ f_{m,0}(-u)` and
  `V_m = (-1)ᵐ f_{m,ι}(-u)` are monic of degree `m`, real-rooted with roots in `(0, ∞)`, with
  `V_m ≪ U_m` and `U_m ≪ V_{m+1}` strictly (no common roots), and `U_m(0) V_m(0) > 0`.
-/

@[expose] public section

open Polynomial Matrix

noncomputable section

namespace RealRooted

variable {n : ℕ}

section Block

variable {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

/-- The first index of the second block lies after the first index. -/
lemma zero_lt_parityIndex (n : ℕ) : (0 : Fin (n + 1 + n + 1)) < parityIndex n :=
  castAdd_lt_natAdd (0 : Fin (n + 1)) (0 : Fin (n + 1))

/-- The step of the vector recursion applied to the all-ones vector. -/
lemma hessenbergVector_one_apply {m : ℕ} (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (i : Fin (m + 1)) : hessenbergVector B 1 i = C (∑ j, B i j) + X := by
  simp [hessenbergVector, tp2AffineStep, Polynomial.smul_eq_C_mul, ← map_sum]

/-- The Wronskian of two first-degree polynomials `a + X`, `b + X`. -/
lemma wronskian_C_add_X (a b : ℝ) : wronskian (C a + X) (C b + X) = C (a - b) := by
  simp [wronskian]

variable (hA : A.IsTP2) (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j)
  (h0 : 0 < A 0 0)

include hA hcol

omit hA hcol in
lemma sum_parityBlock_zero : ∑ j : Fin (n + 1 + (n + 1)), parityBlock A
    (Fin.castAdd (n + 1) (0 : Fin (n + 1))) j = 2 * ∑ j, A 0 j := by
  rw [Fin.sum_univ_add]
  simp only [parityBlock_castAdd_castAdd, parityBlock_castAdd_natAdd]
  ring

omit hA hcol in
lemma sum_parityBlock_parityIndex : ∑ j : Fin (n + 1 + (n + 1)), parityBlock A
    (Fin.natAdd (n + 1) (0 : Fin (n + 1))) j = ∑ j, A 0 j := by
  rw [Fin.sum_univ_add]
  simp only [parityBlock_natAdd_castAdd, parityBlock_natAdd_natAdd]
  simp

/-- **Wronskian lower bound.** -/
theorem le_eval_wronskian_parityBlock (m : ℕ) (x : ℝ) :
    A 0 0 ^ (2 * m) * ∑ j, A 0 j ≤
      (wronskian (hessenbergVector (n := n + 1 + n) (parityBlock A) (m + 1) 0)
        (hessenbergVector (n := n + 1 + n) (parityBlock A) (m + 1) (parityIndex n))).eval x := by
  induction m with
  | zero =>
    have h1 : hessenbergVector (n := n + 1 + n) (parityBlock A) 1 0 =
        C (2 * ∑ j, A 0 j) + X :=
      (hessenbergVector_one_apply _ _).trans
        (congrArg (fun t => C t + X) (sum_parityBlock_zero))
    have h2 : hessenbergVector (n := n + 1 + n) (parityBlock A) 1 (parityIndex n) =
        C (∑ j, A 0 j) + X :=
      (hessenbergVector_one_apply _ _).trans
        (congrArg (fun t => C t + X) (sum_parityBlock_parityIndex))
    rw [h1, h2, wronskian_C_add_X]
    simp only [eval_C, mul_zero, pow_zero, one_mul]
    linarith
  | succ m ih =>
    have hB00 : parityBlock A 0 0 = A 0 0 := parityBlock_castAdd_castAdd A 0 0
    have hB0i : parityBlock A 0 (parityIndex n) = A 0 0 := parityBlock_castAdd_natAdd A 0 0
    have hBi0 : parityBlock A (parityIndex n) 0 = 0 := parityBlock_natAdd_castAdd A 0 0
    have hBii : parityBlock A (parityIndex n) (parityIndex n) = A 0 0 :=
      parityBlock_natAdd_natAdd A 0 0
    have hstep := le_eval_wronskian_hessenbergVector_succ (n := n + 1 + n)
      (A := parityBlock A) (parityBlock_isTP2 hA hcol)
      (fun _ _ _ h => parityBlock_col_le hA.nonneg hcol _ h) (m + 1) (zero_lt_parityIndex n)
      (zero_lt_parityIndex n) x
    rw [hB00, hB0i, hBi0, hBii] at hstep
    have hc : 0 ≤ A 0 0 * A 0 0 - A 0 0 * 0 := by nlinarith [hA.nonneg 0 0]
    calc A 0 0 ^ (2 * (m + 1)) * ∑ j, A 0 j
        = (A 0 0 * A 0 0 - A 0 0 * 0) * (A 0 0 ^ (2 * m) * ∑ j, A 0 j) := by ring
      _ ≤ (A 0 0 * A 0 0 - A 0 0 * 0) * _ := mul_le_mul_of_nonneg_left ih hc
      _ ≤ _ := hstep

omit hA hcol in
/-- The vector recursion of the block matrix. -/
abbrev parityVector (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (m : ℕ) :
    Fin (n + 1 + (n + 1)) → ℝ[X] :=
  hessenbergVector (n := n + 1 + n) (parityBlock A) m

include hA hcol

/-- `f_{m,0} ≪ f_{m,ι}`. -/
lemma strictInterl_parityVector_zero_index (m : ℕ) :
    StrictInterl (parityVector A m 0) (parityVector A m (parityIndex n)) := by
  have hseq := isInterlacingSeqNonneg_hessenbergVector (n := n + 1 + n) (A := parityBlock A)
    (parityBlock_isTP2 hA hcol) (fun _ _ _ h => parityBlock_col_le hA.nonneg hcol _ h) m
  exact List.pairwise_ofFn.mp (isInterlacingSeq_iff_pairwise.mp hseq.2) (zero_lt_parityIndex n)

include h0

omit hcol in
lemma sum_pos_of_diag_pos : 0 < ∑ j, A 0 j :=
  lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun j => A 0 j) (fun j _ => hA.nonneg 0 j)
    (Finset.mem_univ 0))

/-- **No common root of the two first coordinates.** -/
theorem not_isRoot_parityVector_zero_index (m : ℕ) (r : ℝ) :
    ¬ ((parityVector A m 0).IsRoot r ∧ (parityVector A m (parityIndex n)).IsRoot r) := by
  rcases m with _ | m
  · rintro ⟨h, -⟩
    simp [parityVector, hessenbergVector] at h
  · rintro ⟨h1, h2⟩
    have hW := le_eval_wronskian_parityBlock hA hcol m r
    have hzero : (wronskian (parityVector A (m + 1) 0)
        (parityVector A (m + 1) (parityIndex n))).eval r = 0 := by
      simp [wronskian, h1.eq_zero, h2.eq_zero]
    rw [hzero] at hW
    exact absurd hW (not_le.mpr (mul_pos (pow_pos h0 _) (sum_pos_of_diag_pos hA h0)))

/-- Simple roots of `f_{m,0}` and `f_{m,ι}`. -/
theorem hasSimpleRoots_parityVector (m : ℕ) :
    HasSimpleRoots (parityVector A m 0) ∧
      HasSimpleRoots (parityVector A m (parityIndex n)) :=
  (strictInterl_parityVector_zero_index hA hcol m).hasSimpleRoots_of_no_common_root
    fun r hr => not_isRoot_parityVector_zero_index hA hcol h0 m r hr

/-- **No common root between `f_{m,0}` and `f_{m+1,ι}`.** At a (simple) root `r` of `f_{m,0}` all
`f_{m,j}(r)` have the same weak sign, and `f_{m+1,ι}(r) = ∑ⱼ A 0 j f_{m,q+j}(r)` has the nonzero
term `A 0 0 f_{m,ι}(r)`. -/
theorem not_isRoot_parityVector_zero_succ_index (m : ℕ) (r : ℝ)
    (hr0 : (parityVector A m 0).IsRoot r) :
    ¬ (parityVector A (m + 1) (parityIndex n)).IsRoot r := by
  intro hr1
  have hsimple := (hasSimpleRoots_parityVector hA hcol h0 m).1
  have hseq := isInterlacingSeqNonneg_hessenbergVector (n := n + 1 + n) (A := parityBlock A)
    (parityBlock_isTP2 hA hcol) (fun _ _ _ h => parityBlock_col_le hA.nonneg hcol _ h) m
  have hpair : ∀ ⦃i j⦄, i < j → StrictInterl (parityVector A m i) (parityVector A m j) :=
    List.pairwise_ofFn.mp (isInterlacingSeq_iff_pairwise.mp hseq.2)
  have hlead : ∀ j, HasPosLeadingCoeff (parityVector A m j) := fun j => by
    change 0 < (hessenbergVector (n := n + 1 + n) (parityBlock A) m j).leadingCoeff
    rw [(hessenbergVector_monic_natDegree (n := n + 1 + n) (parityBlock A) m j).1.leadingCoeff]
    exact one_pos
  have hder := hsimple.eval_derivative_ne_zero hr0
  have hsign : ∀ j, (parityVector A m j).eval r * (parityVector A m 0).derivative.eval r ≤ 0 :=
    fun j => by
      rcases eq_or_ne j 0 with rfl | hj
      · simp [hr0.eq_zero]
      · exact (hpair (Fin.pos_iff_ne_zero.mpr hj)).eval_mul_derivative_nonpos_of_left_root
          (hlead 0) (hlead j) hr0
  -- the row `ι` of the step
  have hrowι : (parityVector A (m + 1) (parityIndex n)).eval r =
      ∑ j : Fin (n + 1), A 0 j * (parityVector A m (Fin.natAdd (n + 1) j)).eval r := by
    have h1 : (parityVector A (m + 1) (parityIndex n)).eval r =
        ∑ j : Fin (n + 1 + (n + 1)), parityBlock A (parityIndex n) j *
          (parityVector A m j).eval r + r * (parityVector A m 0).eval r := by
      simp [parityVector, hessenbergVector, tp2AffineStep, eval_finsetSum]
      rfl
    rw [h1, hr0.eq_zero, mul_zero, add_zero, Fin.sum_univ_add]
    simp only [parityIndex, parityBlock_natAdd_castAdd, parityBlock_natAdd_natAdd, zero_mul,
      Finset.sum_const_zero, zero_add]
  rw [hr1.eq_zero] at hrowι
  have hv : (parityVector A m (parityIndex n)).eval r = 0 := by
    rcases lt_or_gt_of_ne hder with hneg | hpos
    · have hnn : ∀ j, 0 ≤ (parityVector A m j).eval r := fun j => by nlinarith [hsign j]
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        mul_nonneg (hA.nonneg 0 j) (hnn (Fin.natAdd (n + 1) j))).mp hrowι.symm 0
        (Finset.mem_univ 0)
      exact (mul_eq_zero.mp hterm).resolve_left h0.ne'
    · have hnp : ∀ j, (parityVector A m j).eval r ≤ 0 := fun j => by nlinarith [hsign j]
      have hterm := (Finset.sum_eq_zero_iff_of_nonpos fun j _ =>
        mul_nonpos_of_nonneg_of_nonpos (hA.nonneg 0 j) (hnp (Fin.natAdd (n + 1) j))).mp
        hrowι.symm 0 (Finset.mem_univ 0)
      exact (mul_eq_zero.mp hterm).resolve_left h0.ne'
  exact not_isRoot_parityVector_zero_index hA hcol h0 m r ⟨hr0, hv⟩

omit hcol in
/-- `f_{m,j}(0) > 0` for `j = 0` and `j = ι`. -/
theorem eval_zero_parityVector_pos (m : ℕ) {j : Fin (n + 1 + (n + 1))}
    (hj : j = 0 ∨ j = parityIndex n) : 0 < (parityVector A m j).eval 0 := by
  have hvec := congrFun (eval_hessenbergVector (n := n + 1 + n) (parityBlock A) 0 m) j
  simp only [zero_smul, add_zero] at hvec
  change (hessenbergVector (n := n + 1 + n) (parityBlock A) m j).eval 0 = _ at hvec
  have hdiag : 0 < parityBlock A j j := by
    rcases hj with rfl | rfl
    · rw [show parityBlock A 0 0 = A 0 0 from parityBlock_castAdd_castAdd A 0 0]; exact h0
    · rw [show parityBlock A (parityIndex n) (parityIndex n) = A 0 0 from
        parityBlock_natAdd_natAdd A 0 0]; exact h0
  have := (pow_mulVec_one_ge (parityBlock A) (parityBlock_nonneg hA.nonneg) j hdiag m).2
  rw [hvec]
  exact lt_of_lt_of_le (pow_pos hdiag m) this

end Block

end RealRooted
