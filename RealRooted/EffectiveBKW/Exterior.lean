module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
import RealRooted.EffectiveBKW.ZeroCount
import RealRooted.RootCounting.SignChanges
import Mathlib.Order.Fin.Tuple
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exterior sign changes

An exterior sign witness adds one more open gap to an interior grid. The left-escape
corollary obtains that witness from positive leading coefficient and the degree law.
-/

public section

namespace RealRooted.EffectiveBKW

/-- An exterior point to the left closes one missing sign change. -/
theorem splits_nodup_of_left_sign {p : Polynomial ℝ} {K : ℕ}
    (hdegree : p.natDegree ≤ K + 1) (x : Fin (K + 1) → ℝ) (hx : StrictMono x)
    (hchange : ∀ i : Fin K, p.eval (x i.castSucc) * p.eval (x i.succ) < 0)
    {a : ℝ} (ha : a < x 0) (hsign : p.eval a * p.eval (x 0) < 0) :
    p.Splits ∧ p.roots.Nodup := by
  have hp : p ≠ 0 := by
    intro hp
    simp [hp] at hsign
  let q : Fin (K + 1 + 1) → ℝ := Fin.cons a x
  have hq : StrictMono q := Fin.strictMono_cons.mpr
    ⟨fun j ↦ ha.trans_le (hx.monotone (Fin.zero_le j)), hx⟩
  have hqchange (i : Fin (K + 1)) :
      p.eval (q i.castSucc) * p.eval (q i.succ) < 0 := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [q] using hsign
    · simpa [q] using hchange j
  have h := Polynomial.splits_nodup_roots_of_strict_sign_changes hp hdegree q hq hqchange
  exact ⟨h.2.1, h.2.2.1⟩

/-- An exterior point to the right closes one missing sign change. -/
theorem splits_nodup_of_right_sign {p : Polynomial ℝ} {K : ℕ}
    (hdegree : p.natDegree ≤ K + 1) (x : Fin (K + 1) → ℝ) (hx : StrictMono x)
    (hchange : ∀ i : Fin K, p.eval (x i.castSucc) * p.eval (x i.succ) < 0)
    {b : ℝ} (hb : x (Fin.last K) < b)
    (hsign : p.eval (x (Fin.last K)) * p.eval b < 0) :
    p.Splits ∧ p.roots.Nodup := by
  have hp : p ≠ 0 := by
    intro hp
    simp [hp] at hsign
  let q : Fin (K + 1 + 1) → ℝ := Fin.snoc x b
  have hq : StrictMono q := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [q] using hb
    · dsimp only [q]
      rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hx j.castSucc_lt_succ
  have hqchange (i : Fin (K + 1)) :
      p.eval (q i.castSucc) * p.eval (q i.succ) < 0 := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [q] using hsign
    · dsimp only [q]
      rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hchange j
  have h := Polynomial.splits_nodup_roots_of_strict_sign_changes hp hdegree q hq hqchange
  exact ⟨h.2.1, h.2.2.1⟩

/-- Positive leading coefficient and the degree law supply a missing leftmost
sign change at a finite point, yielding both splitting and simple roots. -/
theorem splits_nodup_of_sign_changes_with_leftEscape {p : Polynomial ℝ} {K : ℕ}
    (hdegree : p.natDegree = K + 1) (hlc : 0 < p.leadingCoeff)
    (x : Fin (K + 1) → ℝ) (hx : StrictMono x)
    (hfirst : (-1 : ℝ) ^ (K + 1) * p.eval (x 0) < 0)
    (hchange : ∀ i : Fin K, p.eval (x i.castSucc) * p.eval (x i.succ) < 0) :
    p.Splits ∧ p.roots.Nodup := by
  obtain ⟨a, ha, hsign⟩ := RealRooted.exists_left_endpoint_sign hdegree hlc (x 0)
  have hprod := mul_neg_of_pos_of_neg hsign hfirst
  have hsquare : ((-1 : ℝ) ^ (K + 1)) ^ 2 = 1 := by
    nlinarith [sq_abs ((-1 : ℝ) ^ (K + 1)),
      show |(-1 : ℝ) ^ (K + 1)| = 1 by simp]
  apply splits_nodup_of_left_sign hdegree.le x hx hchange ha
  have heq : (-1 : ℝ) ^ (K + 1) * p.eval a *
      ((-1 : ℝ) ^ (K + 1) * p.eval (x 0)) = p.eval a * p.eval (x 0) := by
    calc
      _ = ((-1 : ℝ) ^ (K + 1)) ^ 2 * (p.eval a * p.eval (x 0)) := by ring
      _ = _ := by rw [hsquare, one_mul]
  rwa [heq] at hprod

/-- Decreasing alternating phase samples, positive leading coefficient, and the
opposite sign at the leftmost sample close one additional escaping root. -/
theorem splits_nodup_of_strictAnti_alternating_of_leftEscape {p : Polynomial ℝ}
    {K : ℕ} {L : ℤ} (hdegree : p.natDegree = K + 1) (hlc : 0 < p.leadingCoeff)
    (s : Fin (K + 1) → ℝ) (hs : StrictAnti s)
    (hsign : ∀ j, 0 < (-1 : ℝ) ^ (L + (j.val : ℤ)) * p.eval (s j))
    (hleft : (-1 : ℝ) ^ (K + 1) * p.eval (s (Fin.last K)) < 0) :
    p.Splits ∧ p.roots.Nodup := by
  apply splits_nodup_of_sign_changes_with_leftEscape hdegree hlc
    (fun i ↦ s i.rev) (fun _ _ hij ↦ hs (Fin.rev_strictAnti hij))
  · simpa using hleft
  · exact eval_mul_eval_rev_neg s hsign

/-- Positive leading coefficient supplies a positive far-right sign. Together with
a negative rightmost sample this closes one additional escaping root. -/
theorem splits_nodup_of_sign_changes_with_rightEscape {p : Polynomial ℝ} {K : ℕ}
    (hdegree : p.natDegree ≤ K + 1) (hlc : 0 < p.leadingCoeff)
    (x : Fin (K + 1) → ℝ) (hx : StrictMono x)
    (hlast : p.eval (x (Fin.last K)) < 0)
    (hchange : ∀ i : Fin K, p.eval (x i.castSucc) * p.eval (x i.succ) < 0) :
    p.Splits ∧ p.roots.Nodup := by
  have hlead : ∀ᶠ t : ℝ in Filter.atTop, 0 < p.leadingCoeff * t ^ p.natDegree := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    exact mul_pos hlc (pow_pos ht _)
  have hpos : ∀ᶠ t : ℝ in Filter.atTop, 0 < p.eval t :=
    p.isEquivalent_atTop_lead.eventually_pos hlead
  obtain ⟨b, hb, hsign⟩ :=
    ((Filter.eventually_gt_atTop (x (Fin.last K))).and hpos).exists
  exact splits_nodup_of_right_sign hdegree x hx hchange hb (mul_neg_of_neg_of_pos hlast hsign)

end RealRooted.EffectiveBKW
