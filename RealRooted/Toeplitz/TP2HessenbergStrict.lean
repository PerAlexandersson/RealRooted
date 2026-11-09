module

public import RealRooted.SimpleRoots
import RealRooted.Toeplitz.RowDifferenceDeterminant
public import RealRooted.Toeplitz.SiteWeightedRuns
public import RealRooted.Toeplitz.TP2Hessenberg
import RealRooted.Interlacing.OuterDifference

/-!
# Strictness of the finite TP2 Hessenberg certificate

Let `A` be a `d × d` matrix (`d = n + 1 ≥ 2`) as in `hessenbergRow_certificate` with
`det A > 0`. Then every row `P_k` of `1 / (det (I + z A) - t z)` has simple positive roots, and
consecutive rows have no common root. Together with the weak interlacing of
`hessenbergRow_certificate` this is strict interlacing.

The proof follows the first coordinate `f_{k,1}` of the vector recursion. Subtracting each row
of `A + r J` from the one above gives a lower triangular matrix, so `det (A + r J) = det A`
for `d ≥ 2` and `A + r J` is invertible for every real `r`. If `r` is a simple root of
`f_{k,1}`, every `f_{k,j}(r)` has the sign opposite to `f_{k,1}'(r)` (weak interlacing), and
`f_{k+1,1}(r) = ∑ c_j f_{k,j}(r)` with all `c_j > 0` vanishes only if the whole vector
`f_k(r) = (A + r J)ᵏ 𝟙` vanishes, which contradicts invertibility. A pair of weakly interlacing
polynomials without a common root has simple roots, which propagates simplicity to
`f_{k+1,1}`.
-/

public section

open Polynomial Matrix

noncomputable section

namespace RealRooted

variable {n : ℕ}

/-- `det (A + r J) = det A` when `A i j = A j j` for `i ≤ j` and `d = n + 1 ≥ 2`. -/
theorem det_add_smul_runJ_eq {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hn : n ≠ 0)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (r : ℝ) :
    (A + r • runJ n ℝ).det = A.det := by
  have hlast : Fin.last n ≠ 0 := fun h => hn (by simpa using congrArg Fin.val h)
  rw [det_eq_last_mul_prod_of_forall_le (B := A + r • runJ n ℝ),
    det_eq_last_mul_prod_of_forall_le hrow]
  · simp only [Matrix.add_apply, Matrix.smul_apply, runJ, Matrix.of_apply, hlast, ite_false,
      smul_zero, add_zero]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  · intro i j hij
    simp [hrow hij, runJ]

/-- A matrix with `det A ≠ 0`, nonnegative entries, decreasing columns and constant
upper-triangular columns has positive diagonal. -/
theorem diag_pos_of_det_pos {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hnn : ∀ i j, 0 ≤ A i j)
    (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (hdet : A.det ≠ 0)
    (j : Fin (n + 1)) : 0 < A j j := by
  refine lt_of_le_of_ne (hnn j j) fun h0 => hdet ?_
  refine Matrix.det_eq_zero_of_column_eq_zero j fun i => ?_
  refine le_antisymm ?_ (hnn i j)
  rcases le_total i j with hij | hji
  · exact (hrow hij).le.trans h0.ge
  · exact (hcol hji).trans h0.ge

/-- Powers of a nonnegative matrix applied to `𝟙`: nonnegative, and the `i`-th coordinate is at
least the `m`-th power of the diagonal entry (the path that stays at `i`). -/
lemma pow_mulVec_one_ge {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (i : Fin N) (hi : 0 < M i i) (m : ℕ) :
    (∀ j, 0 ≤ (M ^ m *ᵥ fun _ => (1 : ℝ)) j) ∧ M i i ^ m ≤ (M ^ m *ᵥ fun _ => (1 : ℝ)) i := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hnn, hge⟩ := ih
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    refine ⟨fun j => ?_, ?_⟩
    · change 0 ≤ ∑ k, M j k * (M ^ m *ᵥ fun _ => (1 : ℝ)) k
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hM j k) (hnn k)
    calc M i i ^ (m + 1) = M i i * M i i ^ m := pow_succ' _ _
      _ ≤ M i i * ((M ^ m *ᵥ fun _ => (1 : ℝ)) i) := mul_le_mul_of_nonneg_left hge hi.le
      _ ≤ _ := Finset.single_le_sum (f := fun k => M i k * (M ^ m *ᵥ fun _ => (1 : ℝ)) k)
          (fun k _ => mul_nonneg (hM i k) (hnn k)) (Finset.mem_univ i)

/-! ### Evaluation of the vector recursion -/

/-- The evaluation of `f_k = (A + X J)ᵏ 𝟙` at a real `r` is `(A + r J)ᵏ 𝟙`. -/
theorem eval_hessenbergVector (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (r : ℝ) (k : ℕ) :
    (fun i => (hessenbergVector A k i).eval r) = (A + r • runJ n ℝ) ^ k *ᵥ fun _ => 1 := by
  induction k with
  | zero => simp [hessenbergVector]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih]
    funext i
    simp [hessenbergVector, tp2AffineStep, Matrix.mulVec, dotProduct, runJ, add_mul,
      Finset.sum_add_distrib, eval_finsetSum]

/-! ### No common root with the next stage -/

section Strict

variable {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

/-- The core step. If `r` is a simple root of `f_{k,1}`, then `f_{k+1,1}(r) ≠ 0`. -/
theorem not_isRoot_hessenbergVector_succ_zero (hA : A.IsTP2)
    (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (hn : n ≠ 0) (hdet : 0 < A.det)
    (k : ℕ) (hsimple : HasSimpleRoots (hessenbergVector A k 0)) {r : ℝ}
    (hr : (hessenbergVector A k 0).IsRoot r) : ¬ (hessenbergVector A (k + 1) 0).IsRoot r := by
  intro hr'
  set f := hessenbergVector A k with hf
  have hseq := isInterlacingSeqNonneg_hessenbergVector hA hcol k
  have hpair : ∀ ⦃i j⦄, i < j → StrictInterl (f i) (f j) :=
    List.pairwise_ofFn.mp (isInterlacingSeq_iff_pairwise.mp hseq.2)
  have hlead : ∀ j, HasPosLeadingCoeff (f j) := fun j => by
    change 0 < (hessenbergVector A k j).leadingCoeff
    rw [(hessenbergVector_monic_natDegree A k j).1.leadingCoeff]
    exact one_pos
  have hder := hsimple.eval_derivative_ne_zero hr
  have hsign : ∀ j, (f j).eval r * (f 0).derivative.eval r ≤ 0 := fun j => by
    rcases eq_or_ne j 0 with rfl | hj
    · simp [hr.eq_zero]
    · exact (hpair (Fin.pos_iff_ne_zero.mpr hj)).eval_mul_derivative_nonpos_of_left_root
        (hlead 0) (hlead j) hr
  have hc := diag_pos_of_det_pos hA.nonneg hcol hrow hdet.ne'
  have hsum : ∑ j, A j j * (f j).eval r = 0 := by
    have h1 : (hessenbergVector A (k + 1) 0).eval r =
        ∑ j, A 0 j * (f j).eval r + r * (f 0).eval r := by
      simp [hessenbergVector, tp2AffineStep, eval_finsetSum]
      rfl
    rw [hr', hr.eq_zero, mul_zero, add_zero] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun j _ => by rw [hrow (Fin.zero_le j)]
  have hzero : ∀ j, (f j).eval r = 0 := by
    rcases lt_or_gt_of_ne hder with hneg | hpos
    · have hnn : ∀ j, 0 ≤ (f j).eval r := fun j => by
        nlinarith [hsign j]
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hc j).le (hnn j)).mp hsum j
        (Finset.mem_univ j)
      exact (mul_eq_zero.mp this).resolve_left (hc j).ne'
    · have hnp : ∀ j, (f j).eval r ≤ 0 := fun j => by
        nlinarith [hsign j]
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonpos fun j _ =>
        mul_nonpos_of_nonneg_of_nonpos (hc j).le (hnp j)).mp hsum j (Finset.mem_univ j)
      exact (mul_eq_zero.mp this).resolve_left (hc j).ne'
  have hvec := eval_hessenbergVector A r k
  have hzero' : (A + r • runJ n ℝ) ^ k *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    rw [← hvec]
    funext j
    exact hzero j
  have hdetM : ((A + r • runJ n ℝ) ^ k).det ≠ 0 := by
    rw [Matrix.det_pow, det_add_smul_runJ_eq hn hrow]
    exact pow_ne_zero _ hdet.ne'
  have := Matrix.eq_zero_of_mulVec_eq_zero hdetM hzero'
  exact one_ne_zero (congrFun this 0)

/-- The first coordinate of every stage has simple roots. -/
theorem hasSimpleRoots_hessenbergVector_zero (hA : A.IsTP2)
    (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (hn : n ≠ 0) (hdet : 0 < A.det)
    (k : ℕ) : HasSimpleRoots (hessenbergVector A k 0) := by
  induction k with
  | zero => exact fun r hr => by simp [hessenbergVector] at hr
  | succ k ih =>
    exact (StrictInterl.hasSimpleRoots_of_no_common_root
      (strictInterl_hessenbergVector_zero hA hcol k) fun r hr =>
      not_isRoot_hessenbergVector_succ_zero hA hcol hrow hn hdet k ih hr.1 hr.2).2

/-- The first coordinate `f_{k,1}` does not vanish at `0`: its roots are negative. -/
theorem eval_zero_hessenbergVector_pos (hA : A.IsTP2)
    (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (hdet : 0 < A.det) (k : ℕ)
    (j : Fin (n + 1)) : 0 < (hessenbergVector A k j).eval 0 := by
  have hc := diag_pos_of_det_pos hA.nonneg hcol hrow hdet.ne'
  have hvec := congrFun (eval_hessenbergVector A 0 k) j
  simp only [zero_smul, add_zero] at hvec
  rw [hvec]
  exact lt_of_lt_of_le (pow_pos (hc j) k) (pow_mulVec_one_ge A hA.nonneg j (hc j) k).2

end Strict

/-! ### The rows -/

section Rows

variable {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

private lemma isRoot_signedComp {f : ℝ[X]} {k : ℕ} {r : ℝ} :
    (C ((-1 : ℝ) ^ k) * f.comp (-X)).IsRoot r ↔ f.IsRoot (-r) := by
  have hne : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  simp [IsRoot, eval_comp, hne]

/-- **Strict Hessenberg certificate.** Let `A` be as in `hessenbergRow_certificate` with
`d = n + 1 ≥ 2` and `det A > 0`. Then every row `P_k` has simple roots, all strictly positive,
and `P_k`, `P_{k+1}` have no common root. With the weak interlacing
`Interlaces (P_k) (P_{k+1})` of `hessenbergRow_certificate` the interlacing is strict. -/
theorem hessenbergRow_strict (hA : A.IsTP2)
    (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j)
    (hrow : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → A i j = A j j) (hn : n ≠ 0) (hdet : 0 < A.det)
    (k : ℕ) :
    HasSimpleRoots (hessenbergRow A k) ∧ (∀ r, (hessenbergRow A k).IsRoot r → 0 < r) ∧
      ∀ r, ¬ ((hessenbergRow A k).IsRoot r ∧ (hessenbergRow A (k + 1)).IsRoot r) := by
  have hne : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  refine ⟨?_, fun r hr => ?_, fun r hr => ?_⟩
  · rw [hessenbergRow_eq A hrow k]
    have hneg : (-X : ℝ[X]) = C (-1) * X + C 0 := by simp
    rw [hneg]
    exact ((hasSimpleRoots_hessenbergVector_zero hA hcol hrow hn hdet k).comp_C_mul_X_add_C
      (a := -1) (b := 0) (by norm_num)).C_mul hne
  · have hmem : r ∈ (hessenbergRow A k).roots :=
      (mem_roots (isRealRootedIn_Ici_hessenbergRow hA hcol hrow k).ne_zero).mpr hr
    have h0 : 0 ≤ r := (isRealRootedIn_Ici_hessenbergRow hA hcol hrow k).mem_of_mem_roots hmem
    refine lt_of_le_of_ne h0 fun h => ?_
    rw [hessenbergRow_eq A hrow k, ← h, isRoot_signedComp, neg_zero] at hr
    exact (eval_zero_hessenbergVector_pos hA hcol hrow hdet k 0).ne' hr
  · rw [hessenbergRow_eq A hrow k, hessenbergRow_eq A hrow (k + 1), isRoot_signedComp,
      isRoot_signedComp] at hr
    exact not_isRoot_hessenbergVector_succ_zero hA hcol hrow hn hdet k
      (hasSimpleRoots_hessenbergVector_zero hA hcol hrow hn hdet k) hr.1 hr.2

end Rows

end RealRooted
