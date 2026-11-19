module

public import RealRooted.EffectiveBKW.Tiling4.Basic
public import RealRooted.EffectiveBKW.Tiling4.Endpoint
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
import RealRooted.EffectiveBKW.ZeroCount
import RealRooted.RootCounting.SignChanges
import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!+# Closing the tiling root count

The odd rows are closed by the interior alternating samples. The even rows
use one additional sign at the unbounded left end. The phase construction is
kept separate in `EdgePhase`; `Theorem` applies these implications to its samples.
-/

public section

open Polynomial Set

namespace RealRooted.EffectiveBKW.Tiling4

private theorem splits_nodup_lt_of_left_sign {p : ℝ[X]} {K : ℕ} {β : ℝ}
    (hdegree : p.natDegree ≤ K + 1) (x : Fin (K + 1) → ℝ) (hx : StrictMono x)
    (hchange : ∀ i : Fin K, p.eval (x i.castSucc) * p.eval (x i.succ) < 0)
    (hbound : x (Fin.last K) < β) {a : ℝ} (ha : a < x 0)
    (hsign : p.eval a * p.eval (x 0) < 0) :
    p.Splits ∧ p.roots.Nodup ∧ ∀ z ∈ p.roots, z < β := by
  have hp : p ≠ 0 := by intro hp; simp [hp] at hsign
  let q : Fin (K + 1 + 1) → ℝ := Fin.cons a x
  have hq : StrictMono q := Fin.strictMono_cons.mpr
    ⟨fun j ↦ ha.trans_le (hx.monotone (Fin.zero_le j)), hx⟩
  have hc (i : Fin (K + 1)) : p.eval (q i.castSucc) * p.eval (q i.succ) < 0 := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [q] using hsign
    · simpa [q] using hchange j
  have h := Polynomial.splits_nodup_roots_of_strict_sign_changes hp hdegree q hq hc
  refine ⟨h.2.1, h.2.2.1, fun z hz ↦ ((h.2.2.2 z hz).2).trans ?_⟩
  simpa [q] using hbound

/-- The odd row has exactly the number of roots furnished by its interior sample gaps. -/
theorem splits_nodup_odd_of_alternating (k : ℕ)
    (s : Fin (2 * k + 1) → ℝ) (hs : StrictAnti s) (hmem : ∀ j, s j < rightEdge)
    (hsign : ∀ j, 0 < (-1 : ℝ) ^ j.val * (polynomial (2 * k + 1)).eval (s j)) :
    (polynomial (2 * k + 1)).Splits ∧ (polynomial (2 * k + 1)).roots.Nodup ∧
      ∀ z ∈ (polynomial (2 * k + 1)).roots, z < rightEdge := by
  have hsign' : ∀ j, 0 < (-1 : ℝ) ^ ((0 : ℤ) + (j.val : ℤ)) *
      (polynomial (2 * k + 1)).eval (s j) := by
    simpa using hsign
  exact (splits_nodup_of_strictAnti_alternating (J := Iio rightEdge) inferInstance
    (natDegree_polynomial_odd k).le s hs hmem hsign').2

/-- For the even row, its monic degree supplies the one missing root at the left end. -/
theorem splits_nodup_even_of_alternating (k : ℕ)
    (s : Fin (2 * k + 2) → ℝ) (hs : StrictAnti s) (hmem : ∀ j, s j < rightEdge)
    (hsign : ∀ j, 0 < (-1 : ℝ) ^ j.val * (polynomial (2 * (k + 1))).eval (s j)) :
    (polynomial (2 * (k + 1))).Splits ∧ (polynomial (2 * (k + 1))).roots.Nodup ∧
      ∀ z ∈ (polynomial (2 * (k + 1))).roots, z < rightEdge := by
  let p := polynomial (2 * (k + 1))
  let x : Fin (2 * k + 1 + 1) → ℝ := fun j ↦ s j.rev
  have hx : StrictMono x := fun _ _ hij ↦ hs (Fin.rev_strictAnti hij)
  have hd : p.natDegree = 2 * k + 1 + 1 := by
    dsimp [p]
    rw [natDegree_polynomial_even]
    lia
  have hl : 0 < p.leadingCoeff := by
    rw [(monic_polynomial_even (k + 1)).leadingCoeff]
    norm_num
  have hn : p.eval (x 0) < 0 := by
    have h := hsign (Fin.last (2 * k + 1))
    simp only [Fin.val_last, pow_add, pow_mul, neg_one_sq, one_pow, pow_one,
      one_mul, neg_one_mul] at h
    simpa [x, p] using h
  obtain ⟨a, ha, hpos⟩ := RealRooted.exists_left_endpoint_sign hd hl (x 0)
  have hpa : 0 < p.eval a := by
    simpa [pow_add, pow_mul] using hpos
  apply splits_nodup_lt_of_left_sign hd.le x hx
  · have hsign' : ∀ j, 0 < (-1 : ℝ) ^ ((0 : ℤ) + (j.val : ℤ)) * p.eval (s j) := by
      simpa [p] using hsign
    exact eval_mul_eval_rev_neg s hsign'
  · exact hmem _
  · exact ha
  · exact mul_neg_of_pos_of_neg hpa hn

end RealRooted.EffectiveBKW.Tiling4
