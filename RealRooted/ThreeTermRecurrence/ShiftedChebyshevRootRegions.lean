module

public import RealRooted.ThreeTermRecurrence.ShiftedChebyshevFamily
import RealRooted.BinaryRunTransformation.Anchor
import RealRooted.DegreeDropReversal
import RealRooted.PosCombo
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Mathlib.RingTheory.Polynomial.Wronskian
import RealRooted.Wronskian.Converse
import RealRooted.Wronskian.WeakForward

/-!
# Sharp root regions for the shifted Chebyshev family

This file proves the coefficient formula, the finite-row sharp root
windows, parameter ordering, and their reciprocal-polynomial analogues.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

private theorem shiftedChebyshevFamily_eq_path_reversals (c : ℝ) : ∀ n,
    shiftedChebyshevFamily c n =
      C (1 + c) * oddPathReverse n - C c * evenPathReverse n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp [shiftedChebyshevFamily]
  | one =>
      simp [shiftedChebyshevFamily, map_ofNat]
      ring
  | more n ih ih_succ =>
      rw [shiftedChebyshevFamily, constantLagFamily_add_two,
        oddPathReverse_add_two, evenPathReverse_add_two]
      simp only [shiftedChebyshevFamily] at ih ih_succ
      rw [ih, ih_succ]
      norm_num [map_ofNat]
      ring

/-- The coefficient formula for a finite shifted Chebyshev row. -/
theorem shiftedChebyshevFamily_coeff (c : ℝ) (n k : ℕ) :
    (shiftedChebyshevFamily c n).coeff k =
      (Nat.choose (n + k) (2 * k) : ℝ) +
        (1 + c) * (Nat.choose (n + k) (2 * k + 1) : ℝ) := by
  rw [shiftedChebyshevFamily_eq_path_reversals, coeff_sub, coeff_C_mul,
    coeff_C_mul, oddPathReverse, evenPathReverse]
  simp only [coeff_reflect, coeff_pathMatchingPolynomial]
  by_cases hk : k ≤ n
  · rw [revAt_le hk]
    have heven : 2 * n - (n - k) = n + k := by lia
    rw [heven]
    have hodd : 2 * n + 1 - (n - k) = n + k + 1 := by lia
    rw [hodd,
      Nat.choose_symm_of_eq_add (show n + k = (n - k) + 2 * k by lia),
      Nat.choose_symm_of_eq_add
        (show n + k + 1 = (n - k) + (2 * k + 1) by lia),
      Nat.choose_succ_succ']
    push_cast
    ring
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [revAt_eq_self_of_lt hnk]
    rw [Nat.choose_eq_zero_of_lt (by lia), Nat.choose_eq_zero_of_lt (by lia),
      Nat.choose_eq_zero_of_lt (by lia), Nat.choose_eq_zero_of_lt (by lia)]
    simp

private theorem shiftedChebyshevFamily_hasNonnegCoeffs
    (c : ℝ) (n : ℕ) (hn : 0 < n) (hc : -1 - 1 / (n : ℝ) ≤ c) :
    HasNonnegCoeffs (shiftedChebyshevFamily c n) := by
  intro k
  rw [shiftedChebyshevFamily_coeff]
  by_cases hk : k ≤ n
  · let A : ℝ := Nat.choose (n + k) (2 * k)
    let B : ℝ := Nat.choose (n + k) (2 * k + 1)
    have hA : 0 ≤ A := by positivity
    have hB : 0 ≤ B := by positivity
    have hrelNat := Nat.choose_succ_right_eq (n + k) (2 * k)
    have hsubeq : n + k - 2 * k = n - k := by lia
    rw [hsubeq] at hrelNat
    have hrel : B * (2 * k + 1) = A * (n - k) := by
      change (Nat.choose (n + k) (2 * k + 1) : ℝ) * (2 * k + 1) =
        (Nat.choose (n + k) (2 * k) : ℝ) * (n - k)
      exact_mod_cast hrelNat
    have hB_le : B ≤ (n : ℝ) * A := by
      have hfactor : (1 : ℝ) ≤ 2 * k + 1 := by norm_num
      have hsub : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k
      nlinarith
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hdiv : B / (n : ℝ) ≤ A := (div_le_iff₀ hn').2 (by nlinarith)
    have hc' : -1 / (n : ℝ) ≤ 1 + c := by
      norm_num [div_eq_mul_inv] at hc ⊢
      linarith
    have hmul := mul_le_mul_of_nonneg_right hc' hB
    have hneg : -A ≤ (-1 / (n : ℝ)) * B := by
      calc
        -A ≤ -(B / (n : ℝ)) := neg_le_neg hdiv
        _ = (-1 / (n : ℝ)) * B := by ring
    change 0 ≤ A + (1 + c) * B
    linarith
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [Nat.choose_eq_zero_of_lt (by lia), Nat.choose_eq_zero_of_lt (by lia)]
    simp

/-- A positive row has only nonpositive roots exactly in the sharp
finite-row parameter range. -/
theorem shiftedChebyshevFamily_isRoot_nonpos_iff
    (c : ℝ) (n : ℕ) (hn : 0 < n) :
    (∀ r : ℝ, (shiftedChebyshevFamily c n).IsRoot r → r ≤ 0) ↔
      -1 - 1 / (n : ℝ) ≤ c := by
  let p := shiftedChebyshevFamily c n
  have hpmono : p.Monic := by
    simpa [p, shiftedChebyshevFamily] using
      (constantLagFamily_isMonicOfDegree 1 2 c n).monic
  have hpsplits : p.Splits := by
    simpa [p, shiftedChebyshevFamily] using
      (constantLagFamily_strictInterl (b := 1) one_ne_zero 2 c n).1.2
  constructor
  · intro hroots
    have hroots' : ∀ r ∈ p.roots, r ≤ 0 := fun r hr =>
      hroots r ((mem_roots hpmono.ne_zero).mp hr)
    have hnn := ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hpsplits).2
      ⟨hasPosLeadingCoeff_of_monic hpmono, hroots'⟩).1
    have hzero := hnn 0
    rw [coeff_zero_eq_eval_zero, show p.eval 0 = n + 1 + n * c by
      simpa [p] using shiftedChebyshevFamily_eval_zero c n] at hzero
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show -1 - 1 / (n : ℝ) = (-(n + 1 : ℝ)) / n by
      field_simp
      ring]
    apply (div_le_iff₀ hn').2
    nlinarith
  · intro hc r hr
    exact isRoot_nonpos_of_hasNonnegCoeffs
      (shiftedChebyshevFamily_hasNonnegCoeffs c n hn hc) hpmono.ne_zero hr

private theorem shiftedChebyshevFamily_eval_neg_four_sub (c x : ℝ) : ∀ n,
    (shiftedChebyshevFamily c n).eval (-4 - x) =
      (-1 : ℝ) ^ n * (shiftedChebyshevFamily (-c) n).eval x := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp [shiftedChebyshevFamily]
  | one =>
      simp [shiftedChebyshevFamily]
      ring
  | more n ih ih_succ =>
      rw [shiftedChebyshevFamily, constantLagFamily_add_two,
        shiftedChebyshevFamily, constantLagFamily_add_two]
      simp only [eval_sub, eval_mul, eval_add, eval_X, eval_C, one_pow]
      simp only [shiftedChebyshevFamily] at ih ih_succ
      rw [ih, ih_succ]
      ring

/-- A positive row has all roots in `[-4, 0]` exactly in the sharp
symmetric finite-row parameter range. -/
theorem shiftedChebyshevFamily_isRoot_mem_Icc_iff
    (c : ℝ) (n : ℕ) (hn : 0 < n) :
    (∀ r : ℝ, (shiftedChebyshevFamily c n).IsRoot r → r ∈ Set.Icc (-4) 0) ↔
      |c| ≤ 1 + 1 / (n : ℝ) := by
  have hreflect :
      (∀ r : ℝ, (shiftedChebyshevFamily c n).IsRoot r → -4 ≤ r) ↔
        ∀ s : ℝ, (shiftedChebyshevFamily (-c) n).IsRoot s → s ≤ 0 := by
    constructor
    · intro h s hs
      have hr : (shiftedChebyshevFamily c n).IsRoot (-4 - s) := by
        rw [IsRoot.def, shiftedChebyshevFamily_eval_neg_four_sub, hs, mul_zero]
      linarith [h (-4 - s) hr]
    · intro h r hr
      have hs : (shiftedChebyshevFamily (-c) n).IsRoot (-4 - r) := by
        rw [IsRoot.def, shiftedChebyshevFamily_eval_neg_four_sub, neg_neg, hr, mul_zero]
      linarith [h (-4 - r) hs]
  rw [abs_le]
  constructor
  · intro h
    have hupper := (shiftedChebyshevFamily_isRoot_nonpos_iff c n hn).1
      (fun r hr => (h r hr).2)
    have hlower := (shiftedChebyshevFamily_isRoot_nonpos_iff (-c) n hn).1
      (hreflect.1 fun r hr => (h r hr).1)
    constructor <;> linarith
  · rintro ⟨hlower, hupper⟩ r hr
    have hc := (shiftedChebyshevFamily_isRoot_nonpos_iff c n hn).2 (by linarith)
    have hnc := (shiftedChebyshevFamily_isRoot_nonpos_iff (-c) n hn).2 (by linarith)
    exact ⟨(hreflect.2 hnc) r hr, hc r hr⟩

private theorem oddPathReverse_sub_evenPathReverse : ∀ n,
    oddPathReverse (n + 1) - evenPathReverse (n + 1) = oddPathReverse n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one =>
      rw [oddPathReverse_add_two, evenPathReverse_add_two]
      simp
      ring
  | more n ih ih_succ =>
      rw [show n + 2 + 1 = (n + 1) + 2 by lia,
        oddPathReverse_add_two, evenPathReverse_add_two]
      calc
        _ = (X + 2) *
              (oddPathReverse (n + 2) - evenPathReverse (n + 2)) -
            (oddPathReverse (n + 1) - evenPathReverse (n + 1)) := by ring
        _ = (X + 2) * oddPathReverse (n + 1) - oddPathReverse n := by
          rw [ih_succ, ih]
        _ = oddPathReverse (n + 2) := (oddPathReverse_add_two n).symm

private theorem shiftedChebyshevFamily_affine (c : ℝ) (n : ℕ) :
    shiftedChebyshevFamily c (n + 1) =
      shiftedChebyshevFamily 0 (n + 1) + C c * shiftedChebyshevFamily 0 n := by
  rw [shiftedChebyshevFamily_eq_path_reversals,
    shiftedChebyshevFamily_eq_path_reversals,
    shiftedChebyshevFamily_eq_path_reversals]
  simp only [C_add, C_1, C_0, zero_mul, sub_zero]
  linear_combination C c * oddPathReverse_sub_evenPathReverse n

private theorem shiftedChebyshevFamily_zero_strictInterl_parameter
    (c : ℝ) (n : ℕ) :
    StrictInterl (shiftedChebyshevFamily 0 n) (shiftedChebyshevFamily c (n + 1)) := by
  let h := shiftedChebyshevFamily 0 n
  let f := shiftedChebyshevFamily 0 (n + 1)
  have hhf : StrictInterl h f := by
    simpa [h, f, shiftedChebyshevFamily] using
      constantLagFamily_strictInterl (b := 1) one_ne_zero 2 0 n
  have hhpos : HasPosLeadingCoeff h := by
    exact hasPosLeadingCoeff_of_monic <| by
      simpa [h, shiftedChebyshevFamily] using
        (constantLagFamily_isMonicOfDegree 1 2 0 n).monic
  have hfpos : HasPosLeadingCoeff f := by
    exact hasPosLeadingCoeff_of_monic <| by
      simpa [f, shiftedChebyshevFamily] using
        (constantLagFamily_isMonicOfDegree 1 2 0 (n + 1)).monic
  have hqmono : (shiftedChebyshevFamily c (n + 1)).Monic := by
    simpa [shiftedChebyshevFamily] using
      (constantLagFamily_isMonicOfDegree 1 2 c (n + 1)).monic
  have hqsplits : (shiftedChebyshevFamily c (n + 1)).Splits := by
    simpa [shiftedChebyshevFamily] using
      (constantLagFamily_strictInterl (b := 1) one_ne_zero 2 c (n + 1)).1.2
  apply strictInterl_of_wronskian_eval_nonneg_of_nodup
    (hasPosLeadingCoeff_of_monic hqmono) hhpos hqsplits hhf.1.2
  · have hhdeg : h.natDegree = n := by
      simpa [h, shiftedChebyshevFamily] using
        (constantLagFamily_isMonicOfDegree 1 2 0 n).natDegree_eq
    have hqdeg : (shiftedChebyshevFamily c (n + 1)).natDegree = n + 1 := by
      simpa [shiftedChebyshevFamily] using
        (constantLagFamily_isMonicOfDegree 1 2 c (n + 1)).natDegree_eq
    rw [hhdeg, hqdeg]
    exact Nat.le_succ n
  · have hhdeg : h.natDegree = n := by
      simpa [h, shiftedChebyshevFamily] using
        (constantLagFamily_isMonicOfDegree 1 2 0 n).natDegree_eq
    have hqdeg : (shiftedChebyshevFamily c (n + 1)).natDegree = n + 1 := by
      simpa [shiftedChebyshevFamily] using
        (constantLagFamily_isMonicOfDegree 1 2 c (n + 1)).natDegree_eq
    rw [hhdeg, hqdeg]
  · simpa [shiftedChebyshevFamily] using
      (constantLagFamily_hasSimpleRoots (b := 1) one_ne_zero 2 c (n + 1)).roots_nodup
  · intro t
    have hW := wronskian_eval_nonneg_of_strictInterl hfpos hhpos hhf t
    rw [shiftedChebyshevFamily_affine, Polynomial.wronskian_add_right,
      Polynomial.wronskian_C_mul_right, Polynomial.wronskian_self_eq_zero,
      mul_zero, add_zero]
    exact hW

/-- Increasing the initial-row parameter moves every root to the left, in
the library's equal-degree proper-position convention. -/
theorem shiftedChebyshevFamily_strictInterl_parameter
    {c d : ℝ} (hcd : c < d) (n : ℕ) :
    StrictInterl (shiftedChebyshevFamily d (n + 1))
      (shiftedChebyshevFamily c (n + 1)) := by
  let h := shiftedChebyshevFamily 0 n
  let q := shiftedChebyshevFamily c (n + 1)
  have hhq : StrictInterl h q := by
    simpa [h, q] using shiftedChebyshevFamily_zero_strictInterl_parameter c n
  have hhpos : HasPosLeadingCoeff h := hasPosLeadingCoeff_of_monic <| by
    simpa [h, shiftedChebyshevFamily] using
      (constantLagFamily_isMonicOfDegree 1 2 0 n).monic
  have hqpos : HasPosLeadingCoeff q := hasPosLeadingCoeff_of_monic <| by
    simpa [q, shiftedChebyshevFamily] using
      (constantLagFamily_isMonicOfDegree 1 2 c (n + 1)).monic
  have hcombo := hhq.nonneg_combo_right hhpos hqpos
    (show 0 ≤ d - c by linarith) zero_le_one (Or.inl (sub_pos.mpr hcd))
  have hcombo' : StrictInterl (C (d - c) * h + q) q := by
    simpa only [C_1, one_mul] using hcombo
  have heq : C (d - c) * h + q = shiftedChebyshevFamily d (n + 1) := by
    dsimp [h, q]
    rw [shiftedChebyshevFamily_affine d n, shiftedChebyshevFamily_affine c n, C_sub]
    ring
  change StrictInterl (shiftedChebyshevFamily d (n + 1)) q
  rw [← heq]
  exact hcombo'

/-- The positive-degree coefficients of a reflected row. The missing
`k = 0` case is `reflectedShiftedChebyshevFamily_coeff_zero`. -/
theorem reflectedShiftedChebyshevFamily_coeff
    (c : ℝ) (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (reflectedShiftedChebyshevFamily c n).coeff k =
      (Nat.choose (2 * n - k) k : ℝ) +
        (1 + c) * (Nat.choose (2 * n - k) (k - 1) : ℝ) := by
  rw [reflectedShiftedChebyshevFamily_eq_reflect, coeff_reflect, revAt_le hkn,
    shiftedChebyshevFamily_coeff]
  have htop : n + (n - k) = 2 * n - k := by lia
  rw [htop,
    Nat.choose_symm_of_eq_add (show 2 * n - k = 2 * (n - k) + k by lia),
    Nat.choose_symm_of_eq_add
      (show 2 * n - k = (2 * (n - k) + 1) + (k - 1) by lia)]

private theorem reflectedShiftedChebyshevFamily_isRoot_inv_iff
    (c : ℝ) (n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    (reflectedShiftedChebyshevFamily c n).IsRoot r ↔
      (shiftedChebyshevFamily c n).IsRoot r⁻¹ := by
  rw [reflectedShiftedChebyshevFamily_eq_reflect]
  have hdeg : (shiftedChebyshevFamily c n).natDegree ≤ n := by
    simpa [shiftedChebyshevFamily] using
      (constantLagFamily_isMonicOfDegree 1 2 c n).natDegree_eq.le
  simpa only [inv_inv] using
    (DegreeDropReversal.isRoot_reflect_inv_iff (inv_ne_zero hr) hdeg)

private theorem reflectedShiftedChebyshevFamily_root_ne_zero
    (c : ℝ) (n : ℕ) {r : ℝ}
    (hr : (reflectedShiftedChebyshevFamily c n).IsRoot r) : r ≠ 0 := by
  intro hrzero
  subst r
  rw [IsRoot.def, ← coeff_zero_eq_eval_zero,
    reflectedShiftedChebyshevFamily_coeff_zero] at hr
  exact one_ne_zero hr

/-- The sharp negative-root criterion for a positive reflected row, including
the degree-cancellation endpoint. -/
theorem reflectedShiftedChebyshevFamily_isRoot_neg_iff
    (c : ℝ) (n : ℕ) (hn : 0 < n) :
    (∀ r : ℝ, (reflectedShiftedChebyshevFamily c n).IsRoot r → r < 0) ↔
      -1 - 1 / (n : ℝ) ≤ c := by
  rw [← shiftedChebyshevFamily_isRoot_nonpos_iff c n hn]
  constructor
  · intro hreflect r hr
    by_cases hrzero : r = 0
    · simp [hrzero]
    · have hroot : (reflectedShiftedChebyshevFamily c n).IsRoot r⁻¹ := by
        exact (reflectedShiftedChebyshevFamily_isRoot_inv_iff c n
          (inv_ne_zero hrzero)).2 (by simpa only [inv_inv] using hr)
      exact (inv_lt_zero'.mp (hreflect r⁻¹ hroot)).le
  · intro hsource r hr
    have hrzero := reflectedShiftedChebyshevFamily_root_ne_zero c n hr
    have hinvroot :=
      (reflectedShiftedChebyshevFamily_isRoot_inv_iff c n hrzero).1 hr
    have hinvle := hsource r⁻¹ hinvroot
    exact lt_of_le_of_ne (inv_nonpos.mp hinvle) hrzero

/-- The sharp left-ray criterion for a positive reflected row. A zero source
root at the boundary is harmless because reflection drops it. -/
theorem reflectedShiftedChebyshevFamily_isRoot_le_neg_quarter_iff
    (c : ℝ) (n : ℕ) (hn : 0 < n) :
    (∀ r : ℝ, (reflectedShiftedChebyshevFamily c n).IsRoot r → r ≤ -(1 / 4 : ℝ)) ↔
      |c| ≤ 1 + 1 / (n : ℝ) := by
  rw [← shiftedChebyshevFamily_isRoot_mem_Icc_iff c n hn]
  constructor
  · intro hreflect r hr
    by_cases hrzero : r = 0
    · simp [hrzero]
    · have hqroot : (reflectedShiftedChebyshevFamily c n).IsRoot r⁻¹ := by
        exact (reflectedShiftedChebyshevFamily_isRoot_inv_iff c n
          (inv_ne_zero hrzero)).2 (by simpa only [inv_inv] using hr)
      have hinvle := hreflect r⁻¹ hqroot
      have hrneg : r < 0 := inv_lt_zero'.mp (lt_of_le_of_lt hinvle (by norm_num))
      have hinvle' : 1 / r ≤ -(1 / 4 : ℝ) := by simpa only [one_div] using hinvle
      have hmul := (div_le_iff_of_neg hrneg).1 hinvle'
      constructor <;> nlinarith
  · intro hsource r hr
    have hrzero := reflectedShiftedChebyshevFamily_root_ne_zero c n hr
    have hinvroot :=
      (reflectedShiftedChebyshevFamily_isRoot_inv_iff c n hrzero).1 hr
    have hbounds := hsource r⁻¹ hinvroot
    have hinvneg : r⁻¹ < 0 := lt_of_le_of_ne hbounds.2 (inv_ne_zero hrzero)
    have hquot : 1 / r⁻¹ ≤ -(1 / 4 : ℝ) := by
      apply (div_le_iff_of_neg hinvneg).2
      nlinarith [hbounds.1]
    simpa only [one_div, inv_inv] using hquot

end RealRooted
