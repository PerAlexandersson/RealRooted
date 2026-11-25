module

public import RealRooted.Hermite.Homogeneous
public import RealRooted.SimpleRoots
import RealRooted.LiuWang.SequenceCore
import RealRooted.Basic.Coefficients
import RealRooted.Derivative.Interlacing
import RealRooted.ObreschkoffConverse.Forward
import RealRooted.ObreschkoffConverse.Regularization
import RealRooted.Wronskian.Forward
import Mathlib.Tactic

/-!
# Strictly interlacing Hermite seeds on an affine line

We prove the seed assertion used in the completed-square argument for quartic
exponential rows: `Hₙ(κ + β y, y)` has degree `n`, simple negative roots, and
genuine strict consecutive interlacing when `κ, β > 0`.

Source: the unpublished manuscript, Section 2, and the proof in RealRooted #2649,
https://github.com/PerAlexandersson/RealRooted/issues/2649.
The weak induction uses the library's checked Liu--Wang criterion (Theorem 2.1
of Liu--Wang, arXiv:math/0509207v5); disjointness follows directly from the recurrence.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- The affine Hermite seed has constant coefficient `κⁿ`. -/
theorem coeff_zero_hermiteHomogeneous_affine (κ β : ℝ) (n : ℕ) :
    (hermiteHomogeneous (C κ + C β * X) X n).coeff 0 = κ ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' =>
    rw [hermiteHomogeneous_add_two]
    simp only [mul_coeff_zero, coeff_add, coeff_C_zero, coeff_X_zero, mul_zero,
      zero_mul, add_zero, ih', pow_succ]
    ring

/-- Nonnegative affine parameters give nonnegative coefficients in the Hermite seed. -/
theorem hasNonnegCoeffs_hermiteHomogeneous_affine {κ β : ℝ}
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (n : ℕ) :
    HasNonnegCoeffs (hermiteHomogeneous (C κ + C β * X) X n) := by
  have hu := (hasNonnegCoeffs_C hκ).add (hasNonnegCoeffs_C_mul hβ hasNonnegCoeffs_X)
  induction n using Nat.twoStepInduction with
  | zero => exact hasNonnegCoeffs_one
  | one => exact hu
  | more n ih ih' =>
    rw [hermiteHomogeneous_add_two]
    apply (hu.mul ih').add
    have hs := hasNonnegCoeffs_C (show 0 ≤ (2 : ℝ) * (n + 1) by positivity)
    simpa [map_mul, map_ofNat, map_natCast] using (hs.mul hasNonnegCoeffs_X).mul ih

/-- The top coefficient comes only from the affine current-row factor. -/
private theorem hermiteHomogeneous_affine_degree_coeff (κ β : ℝ) (n : ℕ) :
    (hermiteHomogeneous (C κ + C β * X) X n).natDegree ≤ n ∧
      (hermiteHomogeneous (C κ + C β * X) X n).coeff n = β ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    constructor
    · apply natDegree_add_le_of_degree_le (by simp)
      exact (natDegree_C_mul_le _ _).trans (by simp)
    · simp
  | more n ih ih' =>
    have hu : (C κ + C β * X).natDegree ≤ 1 := by
      apply natDegree_add_le_of_degree_le (by simp)
      exact (natDegree_C_mul_le _ _).trans (by simp)
    have hfirst := natDegree_mul_le (p := C κ + C β * X)
      (q := hermiteHomogeneous (C κ + C β * X) X (n + 1))
    have hsecond : ((2 : ℝ[X]) * ((n + 1 : ℕ) : ℝ[X]) * X *
        hermiteHomogeneous (C κ + C β * X) X n).natDegree ≤ n + 1 := by
      have hs : ((2 : ℝ[X]) * ((n + 1 : ℕ) : ℝ[X]) * X).natDegree ≤ 1 := by
        compute_degree
      exact natDegree_mul_le.trans (by lia)
    constructor
    · rw [hermiteHomogeneous_add_two]
      exact natDegree_add_le_of_degree_le (by lia) (by lia)
    · have hvanish := coeff_eq_zero_of_natDegree_lt (p :=
        hermiteHomogeneous (C κ + C β * X) X (n + 1)) (show
          (hermiteHomogeneous (C κ + C β * X) X (n + 1)).natDegree < n + 2 by lia)
      rw [hermiteHomogeneous_add_two, coeff_add,
        coeff_eq_zero_of_natDegree_lt (p := (2 : ℝ[X]) * ((n + 1 : ℕ) : ℝ[X]) * X *
          hermiteHomogeneous (C κ + C β * X) X n) (by lia), add_zero]
      rw [add_mul]
      simp only [coeff_add, coeff_C_mul, mul_assoc, coeff_X_mul, hvanish, mul_zero,
        zero_add, ih'.2]
      rw [pow_succ]
      ring

/-- A positive affine slope gives degree exactly the Hermite index. -/
theorem natDegree_hermiteHomogeneous_affine (κ : ℝ) {β : ℝ}
    (hβ : β ≠ 0) (n : ℕ) :
    (hermiteHomogeneous (C κ + C β * X) X n).natDegree = n := by
  have h := hermiteHomogeneous_affine_degree_coeff κ β n
  apply natDegree_eq_of_le_of_coeff_ne_zero h.1
  rw [h.2]
  exact pow_ne_zero n hβ

/-- With nonzero intercept, consecutive Hermite seeds have no common real root. -/
theorem hermiteHomogeneous_affine_no_common_root {κ : ℝ} (hκ : κ ≠ 0) (β : ℝ) (n : ℕ) :
    ∀ x, ¬ ((hermiteHomogeneous (C κ + C β * X) X n).IsRoot x ∧
      (hermiteHomogeneous (C κ + C β * X) X (n + 1)).IsRoot x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro x hx
    have hxne : x ≠ 0 := by
      intro heq
      have hzero := hx.1.eq_zero
      rw [heq, ← coeff_zero_eq_eval_zero, coeff_zero_hermiteHomogeneous_affine] at hzero
      exact pow_ne_zero (n + 1) hκ hzero
    have heq := hx.2.eq_zero
    rw [hermiteHomogeneous_add_two] at heq
    simp only [eval_add, eval_mul, eval_natCast, eval_ofNat, eval_one, eval_X, hx.1.eq_zero,
      mul_zero, zero_add, Nat.cast_add, Nat.cast_one] at heq
    have hs : (2 : ℝ) * (n + 1) * x ≠ 0 := by
      exact mul_ne_zero (by positivity) hxne
    have hprev : (hermiteHomogeneous (C κ + C β * X) X n).IsRoot x :=
      (mul_eq_zero.mp heq).resolve_left hs
    exact ih x ⟨hprev, hx.1⟩

/-- Positive-intercept, positive-slope Hermite seeds have genuine strict consecutive
interlacing, including disjointness of their real zeros. -/
theorem hermiteHomogeneous_strictInterl_affine {κ β : ℝ}
    (hκ : 0 < κ) (hβ : 0 < β) (n : ℕ) :
    StrictInterl (hermiteHomogeneous (C κ + C β * X) X n)
      (hermiteHomogeneous (C κ + C β * X) X (n + 1)) ∧
    ∀ x, ¬ ((hermiteHomogeneous (C κ + C β * X) X n).IsRoot x ∧
      (hermiteHomogeneous (C κ + C β * X) X (n + 1)).IsRoot x) := by
  let P := hermiteHomogeneous (C κ + C β * X) X
  have hnn := hasNonnegCoeffs_hermiteHomogeneous_affine hκ.le hβ.le
  have hne (j : ℕ) : P j ≠ 0 := by
    intro hz
    have hzero := coeff_zero_hermiteHomogeneous_affine κ β j
    change (P j).coeff 0 = κ ^ j at hzero
    rw [hz, coeff_zero] at hzero
    exact (pow_pos hκ j).ne hzero
  have hpos (j : ℕ) : HasPosLeadingCoeff (P j) := (hnn j).pos_leadingCoeff (hne j)
  have hdeg (j : ℕ) : (P j).natDegree = j := natDegree_hermiteHomogeneous_affine κ hβ.ne' j
  have hbase : StrictInterl (P 0) (P 1) := by
    apply StrictInterl.of_degree_zero_right_of_degree_one (hne 0) (by simp [P]) (hne 1)
      (Splits.of_natDegree_le_one (by rw [hdeg])) (hdeg 0) (hdeg 1)
  have hrec (j : ℕ) : P (j + 2) = (C κ + C β * X) * P (j + 1) +
      (C (2 * (j + 1 : ℝ)) * X) * P j := by
    simpa [P, map_mul, map_ofNat, map_natCast] using
      hermiteHomogeneous_add_two (C κ + C β * X) X j
  have hweak := LiuWang.strictInterl_succ_of_recurrence_of_eval_nonpos hbase hpos hrec
    (fun j => by rw [hdeg, hdeg]; lia) (fun j => by rw [hdeg, hdeg]) (by
      intro j r hr
      have hrle := isRoot_nonpos_of_hasNonnegCoeffs (hnn (j + 1)) (hne (j + 1)) hr
      simp only [eval_mul, eval_C, eval_X]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hrle)
  exact ⟨hweak n, hermiteHomogeneous_affine_no_common_root hκ.ne' β n⟩

/-- Every positive-intercept, positive-slope Hermite seed has simple negative real roots. -/
theorem hermiteHomogeneous_affine_roots {κ β : ℝ}
    (hκ : 0 < κ) (hβ : 0 < β) (n : ℕ) :
    IsSimpleRealRooted (hermiteHomogeneous (C κ + C β * X) X n) ∧
      ∀ r ∈ (hermiteHomogeneous (C κ + C β * X) X n).roots, r < 0 := by
  have h := hermiteHomogeneous_strictInterl_affine hκ hβ n
  refine ⟨⟨h.1.1.1, h.1.1.2, (h.1.hasSimpleRoots_of_no_common_root h.2).1⟩, ?_⟩
  exact roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne
    (hasNonnegCoeffs_hermiteHomogeneous_affine hκ.le hβ.le n)
    (by rw [coeff_zero_hermiteHomogeneous_affine]; positivity)

/-- Every nonzero real pencil of adjacent positive Hermite seeds has simple real
zeros. This is the pencil required by the quartic backward-heat argument. -/
theorem hermiteHomogeneous_affine_pencil {κ β : ℝ}
    (hκ : 0 < κ) (hβ : 0 < β) (n : ℕ) (u v : ℝ) :
    let p := hermiteHomogeneous (C κ + C β * X) X n
    let q := hermiteHomogeneous (C κ + C β * X) X (n + 1)
    C u * p + C v * q = 0 ∨ IsSimpleRealRooted (C u * p + C v * q) := by
  have h := hermiteHomogeneous_strictInterl_affine hκ hβ n
  have hs := h.1.hasSimpleRoots_of_no_common_root h.2
  have hnn := hasNonnegCoeffs_hermiteHomogeneous_affine hκ.le hβ.le
  have hdeg : (hermiteHomogeneous (C κ + C β * X) X (n + 1)).natDegree =
      (hermiteHomogeneous (C κ + C β * X) X n).natDegree + 1 := by
    rw [natDegree_hermiteHomogeneous_affine κ hβ.ne',
      natDegree_hermiteHomogeneous_affine κ hβ.ne']
  have hW := wronskian_pos_of_strictInterl_succ
    ((hnn (n + 1)).pos_leadingCoeff h.1.2.1.1) ((hnn n).pos_leadingCoeff h.1.1.1)
    hdeg h.1 hs.2.roots_nodup hs.1.roots_nodup (fun x hx hx' => h.2 x ⟨hx', hx⟩)
  have hWne : ∀ x : ℝ,
      (ObreschkoffConverse.wronskianPoly
        (hermiteHomogeneous (C κ + C β * X) X n)
        (hermiteHomogeneous (C κ + C β * X) X (n + 1))).eval x ≠ 0 := by
    intro x hx
    have hpos := hW x
    simp only [ObreschkoffConverse.wronskianPoly, eval_sub, eval_mul] at hx
    nlinarith only [hpos, hx]
  rcases ObreschkoffConverse.combo_eq_zero_or_realRooted_simple_of_wronskian_eval_ne_zero
      (allComboRealRooted_of_strictInterl h.1) hWne u v with hzero | hp
  · exact Or.inl hzero
  · exact Or.inr ⟨hp.1.1, hp.1.2, hp.2⟩

end RealRooted.ExponentialRows
