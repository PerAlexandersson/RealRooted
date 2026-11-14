module

public import RealRooted.GammaTransform.Basic
public import RealRooted.InterlacingSequenceBasic
public import RealRooted.StaircaseSum
public import RealRooted.ThresholdMatrix.Basic
import RealRooted.Compatibility.NDCutStaircase
import RealRooted.GammaTransform.Preservation
import RealRooted.Mathlib.Algebra.BigOperators.Group.List
import RealRooted.RowThresholdOne
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Signed staircase induction for peak polynomials

We transport the D/U recurrence through the gamma transform and obtain a
marker-one threshold matrix. This gives an alternative to the six-condition
proof for the peak polynomials of P. Alexandersson, A. Jal and M. Quemener,
*Rook-Eulerian polynomials and permutation ideals*.

Columns are zero-based: column `k` represents the signed values `±(k+1)`.
The signed vector is ordered `-m, …, -1, +1, …, +m`. The concrete enumerator
identification is separate from the abstract recurrence proved here.
-/

@[expose] public section

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace RealRooted.Applications.PeakPolynomials

/-- The refinement with negative first sign in column `k`. -/
def signedDown (n : ℕ) (D U : ℕ → ℝ[X]) (k : ℕ) : ℝ[X] :=
  C 2 * gammaTransform (n - 2) ((D k).comp (C 4 * X)) +
    gammaTransform (n - 1) ((U k).comp (C 4 * X))

/-- The refinement with positive first sign in column `k`. -/
def signedUp (n : ℕ) (D U : ℕ → ℝ[X]) (k : ℕ) : ℝ[X] :=
  C 2 * X * gammaTransform (n - 2) ((D k).comp (C 4 * X)) +
    gammaTransform (n - 1) ((U k).comp (C 4 * X))

/-- The signed first-entry refinements in increasing signed order. -/
def signedVector (n m : ℕ) (D U : ℕ → ℝ[X]) : List ℝ[X] :=
  (List.range m).reverse.map (signedDown n D U) ++
    (List.range m).map (signedUp n D U)

/-- Degree bounds, coefficient signs, and signed interlacing at one level. -/
structure SignedPeakInvariant (n m : ℕ) (D U : ℕ → ℝ[X]) : Prop where
  /-- The level has at least one row. -/
  one_le : 1 ≤ n
  /-- A one-row placement cannot start with a descent. -/
  D_eq_zero_of_eq_one : n = 1 → ∀ k, D k = 0
  /-- Initial descents give the tighter peak bound. -/
  natDegree_D : ∀ k, (D k).natDegree ≤ (n - 2) / 2
  /-- Peaks cannot be adjacent. -/
  natDegree_U : ∀ k, (U k).natDegree ≤ (n - 1) / 2
  /-- The descent refinement has nonnegative coefficients. -/
  nonneg_D : ∀ k, HasNonnegCoeffs (D k)
  /-- The ascent refinement has nonnegative coefficients. -/
  nonneg_U : ∀ k, HasNonnegCoeffs (U k)
  /-- Signed first-entry refinements form a zero-aware interlacing sequence. -/
  interlacing : IsInterlacingSeq0NonnegRealRooted (signedVector n m D U)

private theorem natDegree_rescale (p : ℝ[X]) :
    (p.comp (C 4 * X)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_C_mul (by norm_num : (4 : ℝ) ≠ 0)]
  simp

private theorem signed_pair {n : ℕ} {D U : ℕ → ℝ[X]}
    (hn : 1 ≤ n) (hD0 : n = 1 → ∀ k, D k = 0)
    (hD : ∀ k, (D k).natDegree ≤ (n - 2) / 2) (k : ℕ) :
    signedDown n D U k + signedUp n D U k =
      C 2 * gammaTransform (n - 1) ((D k + U k).comp (C 4 * X)) := by
  by_cases hn1 : n = 1
  · simp [signedDown, signedUp, hD0 hn1 k, map_ofNat, two_mul]
  · have heq : n - 1 = (n - 2) + 1 := by lia
    simp only [signedDown, signedUp, add_comp, gammaTransform_add, heq,
      gammaTransform_pad_one (by rw [natDegree_rescale]; exact hD k)]
    simp only [map_ofNat]
    ring

private theorem signed_mixed {n : ℕ} {D U : ℕ → ℝ[X]}
    (hn : 1 ≤ n) (hD0 : n = 1 → ∀ k, D k = 0)
    (hU : ∀ k, (U k).natDegree ≤ (n - 1) / 2) (k : ℕ) :
    X * signedDown n D U k + signedUp n D U k =
      gammaTransform n ((X * D k + U k).comp (C 4 * X)) := by
  rw [add_comp, mul_comp, X_comp, gammaTransform_add]
  have hpad := gammaTransform_pad_one (by rw [natDegree_rescale]; exact hU k)
  rw [show n - 1 + 1 = n by lia] at hpad
  rw [hpad]
  by_cases hn1 : n = 1
  · simp [signedDown, signedUp, hD0 hn1 k]
    ring
  · have hX := gammaTransform_X_mul_two (n - 2) ((D k).comp (C 4 * X))
    rw [← show n = (n - 2) + 2 by lia] at hX
    simp only [signedDown, signedUp, mul_assoc, gammaTransform_C_mul, hX]
    simp only [map_ofNat]
    ring

/-- Summing the signed refinements gives the denominator-free signing identity.
Only the level and descent-degree hypotheses are needed for this identity. -/
theorem sum_signedVector {n : ℕ} (m : ℕ) (D U : ℕ → ℝ[X])
    (hn : 1 ≤ n) (hD0 : n = 1 → ∀ k, D k = 0)
    (hD : ∀ k, (D k).natDegree ≤ (n - 2) / 2) :
    (signedVector n m D U).sum = gammaTransform (n - 1)
      (C 2 * (∑ k ∈ Finset.range m, (D k + U k)).comp (C 4 * X)) := by
  rw [signedVector, List.sum_append, List.map_reverse, List.sum_reverse,
    List.sum_map_range, List.sum_map_range, ← Finset.sum_add_distrib]
  simp only [Polynomial.sum_comp, gammaTransform_C_mul, gammaTransform_finset_sum,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => signed_pair hn hD0 hD k

private theorem staircase_low (a b : ℕ → ℝ[X]) {m k : ℕ} (hk : k ≤ m) :
    staircaseSum ((List.range m).reverse.map a ++ (List.range m).map b) (m - k) =
      (∑ j ∈ Finset.range k, (a j + b j)) +
        ∑ j ∈ Finset.Ico k m, (X * a j + b j) := by
  rw [List.map_reverse, show m - k = ((List.range m).map a).length - k by simp,
    staircaseSum_reverse_append_low _ _ k (by simpa using hk)]
  simp only [← List.map_take, List.take_range, min_eq_left hk,
    List.sum_map_range, List.sum_drop_map_range_eq_sum_Ico]
  rw [← Finset.sum_range_add_sum_Ico b hk]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  ring

private theorem staircase_high (a b : ℕ → ℝ[X]) {m k : ℕ} (hk : k ≤ m) :
    staircaseSum ((List.range m).reverse.map a ++ (List.range m).map b) (m + k) =
      X * (∑ j ∈ Finset.range k, (a j + b j)) +
        ∑ j ∈ Finset.Ico k m, (X * a j + b j) := by
  rw [List.map_reverse, show m + k = ((List.range m).map a).length + k by simp,
    staircaseSum_reverse_append_high]
  simp only [← List.map_take, List.take_range, min_eq_left hk,
    List.sum_map_range, List.sum_drop_map_range_eq_sum_Ico]
  rw [← Finset.sum_range_add_sum_Ico a hk]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The selected thresholds, including the repeated middle threshold. -/
def signedThresholds (m r : ℕ) : List ℕ :=
  (List.range r).reverse.map (fun k => m - k) ++
    (List.range r).map (fun k => m + k)

/-- The selected thresholds are weakly increasing. -/
theorem pairwise_signedThresholds (m r : ℕ) :
    (signedThresholds m r).Pairwise (· ≤ ·) := by
  simp only [signedThresholds, List.pairwise_append, List.pairwise_map,
    List.pairwise_reverse]
  refine ⟨List.pairwise_le_range.imp (fun _ => by lia),
    List.pairwise_le_range.imp (fun _ => by lia), ?_⟩
  simp only [List.mem_map, forall_exists_index, and_imp]
  intro i _ a rfl j _ b rfl
  lia

/-- The signed D/U step is exactly a marker-one threshold matrix action. -/
theorem signedVector_step {n m r : ℕ} {D U D' U' : ℕ → ℝ[X]}
    (h : SignedPeakInvariant n m D U) (hr : r ≤ m + 1)
    (hD : ∀ k < r, D' k = ∑ j ∈ Finset.range k, (D j + U j))
    (hU : ∀ k < r, U' k = ∑ j ∈ Finset.Ico k m, (X * D j + U j)) :
    signedVector (n + 1) r D' U' =
      matPolyAction (thresholdMatrix (2 * m)
        ((signedThresholds m r).map (fun t => (t, 1)))) (signedVector n m D U) := by
  have entries (k : ℕ) (hk : k < r) :
      signedDown (n + 1) D' U' k = staircaseSum (signedVector n m D U) (m - k) ∧
        signedUp (n + 1) D' U' k = staircaseSum (signedVector n m D U) (m + k) := by
    have hkm : k ≤ m := by lia
    have hpair := signed_pair (U := U) h.one_le h.D_eq_zero_of_eq_one h.natDegree_D
    have hmixed := signed_mixed (D := D) h.one_le h.D_eq_zero_of_eq_one h.natDegree_U
    constructor <;>
      simp only [signedVector, staircase_low _ _ hkm, staircase_high _ _ hkm,
        hpair, hmixed, ← Finset.mul_sum, ← gammaTransform_finset_sum,
        ← Polynomial.sum_comp, ← hD k hk, ← hU k hk] <;>
      simp only [signedDown, signedUp, Nat.add_sub_cancel,
        show n + 1 - 2 = n - 1 by lia]
    ring
  have hlen : (signedVector n m D U).length = 2 * m := by
    simp [signedVector, two_mul]
  rw [← hlen]
  simp only [matPolyAction, thresholdMatrix, List.map_map,
    thresholdRow_one_action_eq_staircaseSum, Function.comp_def]
  rw [signedVector, signedThresholds, List.map_append, List.map_map, List.map_map]
  congr 1 <;> apply List.map_congr_left <;> intro k hk
  · exact (entries k (by simpa using hk)).1
  · exact (entries k (by simpa using hk)).2

/-- Every signed refinement of the one-row seed is the constant one. -/
theorem signedPeakInvariant_one (m : ℕ) :
    SignedPeakInvariant 1 m 0 (fun k => if k < m then 1 else 0) := by
  have hmem : ∀ p ∈ signedVector 1 m 0 (fun k => if k < m then 1 else 0),
      p = 1 := by
    intro p hp
    simp only [signedVector, List.mem_append, List.mem_map, List.mem_reverse,
      List.mem_range] at hp
    rcases hp with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
      simp [signedDown, signedUp, hk, gammaTransform, gammaBasisTerm]
  refine ⟨by norm_num, by simp, by simp, ?_, fun _ => hasNonnegCoeffs_zero, ?_, ?_⟩
  · intro k
    split_ifs <;> simp
  · intro k
    split_ifs <;> simp only [hasNonnegCoeffs_one, hasNonnegCoeffs_zero]
  · rw [List.eq_replicate_of_mem hmem]
    simp [IsInterlacingSeq0NonnegRealRooted, IsInterlacingSeq0Nonneg,
      isInterlacingSeq0_iff_pairwise, hasNonnegCoeffs_one,
      Interl.refl (f := (1 : ℝ[X])) (fun _ => Polynomial.Splits.one)]

/-- A D/U recurrence step preserves the signed peak invariant. The support
condition extends the output degree and coefficient bounds to every column. -/
theorem SignedPeakInvariant.step {n m r : ℕ} {D U D' U' : ℕ → ℝ[X]}
    (h : SignedPeakInvariant n m D U) (hr : r ≤ m + 1)
    (hD : ∀ k < r, D' k = ∑ j ∈ Finset.range k, (D j + U j))
    (hU : ∀ k < r, U' k = ∑ j ∈ Finset.Ico k m, (X * D j + U j))
    (hz : ∀ k, r ≤ k → D' k = 0 ∧ U' k = 0) :
    SignedPeakInvariant (n + 1) r D' U' := by
  have hn := h.one_le
  have bounds (k : ℕ) :
      (D' k).natDegree ≤ (n + 1 - 2) / 2 ∧ (U' k).natDegree ≤ (n + 1 - 1) / 2 ∧
        HasNonnegCoeffs (D' k) ∧ HasNonnegCoeffs (U' k) := by
    by_cases hk : k < r
    · rw [hD k hk, hU k hk]
      refine ⟨natDegree_sum_le_of_forall_le _ _ fun j _ => ?_,
        natDegree_sum_le_of_forall_le _ _ fun j _ => ?_,
        hasNonnegCoeffs_finsetSum _ _ fun j _ => (h.nonneg_D j).add (h.nonneg_U j),
        hasNonnegCoeffs_finsetSum _ _ fun j _ =>
          (hasNonnegCoeffs_X.mul (h.nonneg_D j)).add (h.nonneg_U j)⟩
      · exact natDegree_add_le_of_degree_le
          ((h.natDegree_D j).trans (by lia)) ((h.natDegree_U j).trans (by lia))
      · refine natDegree_add_le_of_degree_le ?_ ((h.natDegree_U j).trans (by lia))
        by_cases hn1 : n = 1
        · simp [h.D_eq_zero_of_eq_one hn1 j]
        · have hj := h.natDegree_D j
          have hmul := natDegree_mul_le (p := (X : ℝ[X])) (q := D j)
          simp only [natDegree_X] at hmul
          lia
    · simp [(hz k (by lia)).1, (hz k (by lia)).2, hasNonnegCoeffs_zero]
  refine ⟨by lia, by intro h; lia, fun k => (bounds k).1,
    fun k => (bounds k).2.1, fun k => (bounds k).2.2.1, fun k => (bounds k).2.2.2, ?_⟩
  rw [signedVector_step h hr hD hU]
  exact thresholdMatrix_one_preserves_interlacing _ (pairwise_signedThresholds m r)
    _ (by simp [signedVector, two_mul]) h.interlacing

/-- The unsigned D/U collapse splits, by signed interlacing and inverse gamma
transformation. The zero polynomial is treated separately. -/
theorem SignedPeakInvariant.splits_sum {n m : ℕ} {D U : ℕ → ℝ[X]}
    (h : SignedPeakInvariant n m D U) :
    (∑ k ∈ Finset.range m, (D k + U k)).Splits := by
  let P : ℝ[X] := ∑ k ∈ Finset.range m, (D k + U k)
  change P.Splits
  by_cases hp : P = 0
  · simp [hp]
  let γ : ℝ[X] := C 2 * P.comp (C 4 * X)
  have hγdeg : γ.natDegree ≤ (n - 1) / 2 := by
    simpa only [γ, natDegree_C_mul (by norm_num : (2 : ℝ) ≠ 0), natDegree_rescale]
      using natDegree_sum_le_of_forall_le _ _ fun k _ =>
        natDegree_add_le_of_degree_le ((h.natDegree_D k).trans (by lia)) (h.natDegree_U k)
  have hγne : γ ≠ 0 := by
    simpa [γ, Polynomial.comp_C_mul_X_eq_zero_iff (r := (4 : ℝ)) (by norm_num)] using hp
  have hsum : (signedVector n m D U).sum = gammaTransform (n - 1) γ :=
    sum_signedVector m D U h.one_le h.D_eq_zero_of_eq_one h.natDegree_D
  have hrr := isRealRooted_sum_of_isInterlacingSeq0Nonneg
    h.interlacing.1 h.interlacing.2 (by
      rwa [hsum, ne_eq, gammaTransform_eq_zero_iff_of_natDegree_le hγdeg])
  have hγrr := isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
    hγdeg (hsum ▸ hrr.1) (hsum ▸ hrr.2)
    (hsum ▸ roots_nonpos_of_hasNonnegCoeffs (hasNonnegCoeffs_sum _ h.interlacing.1.2))
  have hcomp : (P.comp (C 4 * X)).Splits :=
    (Polynomial.splits_mul_iff_right (by simp) (Polynomial.Splits.C 2)).mp hγrr.1.2
  exact (Polynomial.splits_iff_comp_splits_of_natDegree_eq_one
    (by rw [natDegree_C_mul (by norm_num : (4 : ℝ) ≠ 0)]; simp)).mpr hcomp

-- The board (2,3,3): D = (0,1), U = (1+X,X).
example : signedThresholds 1 2 = [0, 1, 1, 2] := rfl

example : signedThresholds 2 2 = [1, 2, 2, 3] := rfl

example : (∑ k ∈ Finset.range 2,
    ((if k = 1 then 1 else 0) +
      (if k = 0 then 1 + X else if k = 1 then X else 0))) =
    (2 + 2 * X : ℝ[X]) := by
  norm_num [Finset.sum_range_succ]
  ring

example : signedVector 3 2 (fun k => if k = 1 then 1 else 0)
    (fun k => if k = 0 then 1 + X else if k = 1 then X else 0) =
    [2 + 6 * X, 1 + 6 * X + X ^ 2, 1 + 6 * X + X ^ 2, 6 * X + 2 * X ^ 2] := by
  norm_num [signedVector, signedDown, signedUp, List.range_succ, gammaTransform,
    gammaBasisTerm, Finset.sum_range_succ, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.X_comp, map_ofNat, Polynomial.coeff_one]
  refine ⟨?_, ?_, ?_⟩ <;> ring

example : (signedVector 3 2 (fun k => if k = 1 then 1 else 0)
    (fun k => if k = 0 then 1 + X else if k = 1 then X else 0)).sum =
    4 + 24 * X + 4 * X ^ 2 := by
  norm_num [signedVector, signedDown, signedUp, List.range_succ, gammaTransform,
    gammaBasisTerm, Finset.sum_range_succ, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.X_comp, map_ofNat, Polynomial.coeff_one]
  ring

end RealRooted.Applications.PeakPolynomials
