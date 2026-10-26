module

public import RealRooted.Applications.OEIS.A275442.Bridge.Core

/-!
# The trajectory at a zero: a compatibility-free scalar reduction of the bridge

Fix a real number `x < -1`, put `t = -x > 1`, and let

```
A k = σ · (p k).eval x        (σ = ±1, in practice the sign of `(p m)'(r)`)
```

be the *trajectory* of the family at the point `x`.  Every `A` of this shape satisfies the
scalar lag-four recurrence

```
A (k+4) = A (k+3) + A (k+2) - t · A k .                                        (R)
```

If `x = r` is a zero of `p m` then `A m = 0`, and the bridge orientation at `r` is exactly
the inequality `A (m-1) < t · A (m-3)` (the *crux* below).  This file develops that
reduction *unconditionally*: no compatibility, no interlacing input, no orientation
assumption.  All statements are about an arbitrary real sequence satisfying `(R)`; the
mirrored versions (for a zero at which the signs are reversed) follow by applying them to
`fun k => -A k`, which satisfies `(R)` as well (`Bridge.neg_rec`).

Writing `aᵢ = A (m - i)` for the values preceding the crossing, the relations at hand are

```
a₁ + a₂ = t·a₄      (the crossing: A m = 0)
a₁ = a₂ + a₃ - t·a₅ ,   a₃ = a₄ + a₅ - t·a₇      (the recurrence)
```

and the bridge orientation at the zero is the inequality `a₁ < t·a₃`.

## Main contents

* `Bridge.two_mul_crux_value` — the identity
  `2·a₁ = a₃ + t·(a₄ - a₅)` at a crossing.
  It turns the bridge into the sharp comparison `t·(a₄ - a₅) < (2t-1)·a₃`.
* `Bridge.crux_of_le` — the bridge holds as soon as `a₄ ≤ a₃`.
* `Bridge.crux_of_subFib` — the bridge holds as soon as `a₄ ≤ a₃ + a₅`
  (*sub-Fibonacci bound*), equivalently `t·a₇ ≤ 2·a₅` (`Bridge.subFib_iff`).
* `Bridge.crux_of_short_run` — consequently the bridge holds at every crossing at which the
  run of consecutive same-sign values ending there has length `5` or `6`
  (then `a₅ ≥ 0 ≥ a₇`, so the sub-Fibonacci bound is automatic).
* `Bridge.crux_of_prev` — and at every crossing whose run has length `4`, provided the
  *previous* crossing of the same trajectory satisfies `t·a₇ ≤ a₅`, which is the bridge
  inequality there.
* `Bridge.next_three_neg` — the bridge inequality at a crossing forces the next three
  values to be strictly of the opposite sign: runs have length at least four.
* `Bridge.bridge_at_root_of_subFib`, `Bridge.bridge_at_root_of_short_run`,
  `Bridge.bridge_at_root_of_prev` — the polynomial-level forms at a zero of `p (n+7)`.

Only one case of the induction over crossings is left open, namely a crossing preceded by a
run of length `≥ 7`; see `PROOF_NOTES.md`, §13.
-/

public section

namespace RealRooted.Applications.OEIS.A275442.Bridge

open Polynomial

/-! ### The scalar trajectory -/

section Scalar

variable {t : ℝ} {A : ℕ → ℝ}

/-- The mirrored trajectory satisfies the same recurrence. -/
theorem neg_rec (hrec : ∀ k, A (k + 4) = A (k + 3) + A (k + 2) - t * A k) (k : ℕ) :
    (-A (k + 4)) = (-A (k + 3)) + (-A (k + 2)) - t * (-A k) := by
  rw [hrec k]; ring

/-- **The identity at a crossing.**  With `a₁ = A (m-1), …, a₅ = A (m-5)` at the crossing
`m = n+7` (`A m ≤ 0`), the two instances of the recurrence give

```
2·a₁ ≤ a₃ + t·(a₄ - a₅) ,
```

with equality when `A m = 0` (`Bridge.two_mul_crux_value_eq`).  This is the exact content of
the crossing: the bridge inequality `a₁ < t·a₃` is equivalent to
`t·(a₄ - a₅) < (2t-1)·a₃`. -/
theorem two_mul_crux_value (hrec : ∀ k, A (k + 4) = A (k + 3) + A (k + 2) - t * A k) (n : ℕ)
    (hle : A (n + 7) ≤ 0) :
    2 * A (n + 6) ≤ A (n + 4) + t * (A (n + 3) - A (n + 2)) := by
  have h0 : A (n + 7) = A (n + 6) + A (n + 5) - t * A (n + 3) := hrec (n + 3)
  have h1 : A (n + 6) = A (n + 5) + A (n + 4) - t * A (n + 2) := hrec (n + 2)
  linarith

/-- The identity in equality form, at an exact zero of the trajectory. -/
theorem two_mul_crux_value_eq (hrec : ∀ k, A (k + 4) = A (k + 3) + A (k + 2) - t * A k) (n : ℕ)
    (hzero : A (n + 7) = 0) :
    2 * A (n + 6) = A (n + 4) + t * (A (n + 3) - A (n + 2)) := by
  have h0 : A (n + 7) = A (n + 6) + A (n + 5) - t * A (n + 3) := hrec (n + 3)
  have h1 : A (n + 6) = A (n + 5) + A (n + 4) - t * A (n + 2) := hrec (n + 2)
  rw [hzero] at h0
  linarith

/-- **First sufficient condition.**  If `a₄ ≤ a₃` then the bridge inequality holds at the
crossing.  (`a₂ > 0` is the granted relation `p (m-2) ≺ p m`.) -/
theorem crux_of_le (hrec : ∀ k, A (k + 4) = A (k + 3) + A (k + 2) - t * A k) {n : ℕ}
    (ht : 0 < t) (hle : A (n + 7) ≤ 0) (h2 : 0 < A (n + 5)) (hcase : A (n + 3) ≤ A (n + 4)) :
    A (n + 6) < t * A (n + 4) := by
  have h0 : A (n + 7) = A (n + 6) + A (n + 5) - t * A (n + 3) := hrec (n + 3)
  -- `a₁ + a₂ ≤ t·a₄ ≤ t·a₃`, and `a₂ > 0`
  have hsum : A (n + 6) + A (n + 5) ≤ t * A (n + 3) := by linarith
  have hmul : t * A (n + 3) ≤ t * A (n + 4) := by nlinarith
  linarith

/-- **Second sufficient condition: the sub-Fibonacci bound.**  If `a₄ ≤ a₃ + a₅` then the
bridge inequality holds at the crossing. -/
theorem crux_of_subFib (hrec : ∀ k, A (k + 4) = A (k + 3) + A (k + 2) - t * A k) {n : ℕ}
    (ht : 1 < t) (hle : A (n + 7) ≤ 0) (h3 : 0 < A (n + 4))
    (hfib : A (n + 3) ≤ A (n + 4) + A (n + 2)) :
    A (n + 6) < t * A (n + 4) := by
  have key := two_mul_crux_value hrec n hle
  -- `2a₁ ≤ a₃ + t·(a₄ - a₅) ≤ (1+t)·a₃ < 2t·a₃`
  nlinarith

/-- The sub-Fibonacci bound `a₄ ≤ a₃ + a₅` is the same as `t·a₇ ≤ 2·a₅`. -/
theorem subFib_iff (hrec : ∀ k, A (k + 4) = A (k + 3) + A (k + 2) - t * A k) (n : ℕ) :
    A (n + 3) ≤ A (n + 4) + A (n + 2) ↔ t * A n ≤ 2 * A (n + 2) := by
  have h : A (n + 4) = A (n + 3) + A (n + 2) - t * A n := hrec n
  constructor <;> intro hh <;> linarith

/-- **The crossings with a short run.**  If the value five steps back is nonnegative and the
value seven steps back is nonpositive — which is the case exactly when the run of
same-sign values ending at the crossing has length `5` or `6`, the preceding run having
length at least four — then the bridge inequality holds, with no further input. -/
theorem crux_of_short_run (hrec : ∀ k, A (k + 4) = A (k + 3) + A (k + 2) - t * A k) {n : ℕ}
    (ht : 1 < t) (hle : A (n + 7) ≤ 0) (h3 : 0 < A (n + 4))
    (h5 : 0 ≤ A (n + 2)) (h7 : A n ≤ 0) :
    A (n + 6) < t * A (n + 4) := by
  refine crux_of_subFib hrec ht hle h3 ?_
  rw [subFib_iff hrec n]
  nlinarith

/-- **The crossings with a run of length four.**  Here the two values five and seven steps
back are both nonpositive, and the bridge inequality follows from the corresponding
inequality at the *previous* crossing of the same trajectory, which is exactly
`t · a₇ ≤ a₅`. -/
theorem crux_of_prev (hrec : ∀ k, A (k + 4) = A (k + 3) + A (k + 2) - t * A k) {n : ℕ}
    (ht : 0 < t) (hle : A (n + 7) ≤ 0) (h2 : 0 < A (n + 5))
    (hprev : t * A n ≤ A (n + 2)) :
    A (n + 6) < t * A (n + 4) := by
  refine crux_of_le hrec ht hle h2 ?_
  have h : A (n + 4) = A (n + 3) + A (n + 2) - t * A n := hrec n
  linarith

/-- **Runs have length at least four.**  If the bridge inequality holds at a crossing then
the next three values of the trajectory are strictly negative. -/
theorem next_three_neg (hrec : ∀ k, A (k + 4) = A (k + 3) + A (k + 2) - t * A k) {n : ℕ}
    (ht : 0 < t) (hle : A (n + 7) ≤ 0) (hcrux : A (n + 6) < t * A (n + 4))
    (h2 : 0 < A (n + 5)) (h1 : 0 < A (n + 6)) :
    A (n + 8) < 0 ∧ A (n + 9) < 0 ∧ A (n + 10) < 0 := by
  have h8 : A (n + 8) = A (n + 7) + A (n + 6) - t * A (n + 4) := hrec (n + 4)
  have h9 : A (n + 9) = A (n + 8) + A (n + 7) - t * A (n + 5) := hrec (n + 5)
  have h10 : A (n + 10) = A (n + 9) + A (n + 8) - t * A (n + 6) := hrec (n + 6)
  have e8 : A (n + 8) < 0 := by rw [h8]; linarith
  have e9 : A (n + 9) < 0 := by rw [h9]; nlinarith
  refine ⟨e8, e9, ?_⟩
  rw [h10]; nlinarith

end Scalar

/-! ### The polynomial-level statements at a zero -/

noncomputable section

/-- The trajectory of the family at a point, with a sign `σ`, satisfies the scalar
recurrence. -/
theorem traj_rec (r σ : ℝ) (A : ℕ → ℝ) (hA : ∀ k, A k = σ * (p k).eval r) (k : ℕ) :
    A (k + 4) = A (k + 3) + A (k + 2) - (-r) * A k := by
  simp only [hA]
  rw [eval_p_rec r k]
  ring

/-- The bridge value at a point is a difference of two trajectory values. -/
theorem traj_bridge (r σ : ℝ) (A : ℕ → ℝ) (hA : ∀ k, A k = σ * (p k).eval r) (n : ℕ) :
    σ * (b (n + 4)).eval r = A (n + 6) - (-r) * A (n + 4) := by
  simp only [hA]
  rw [eval_b]
  ring

/-- **The bridge at a zero from the sub-Fibonacci bound.**  Let `r` be a zero of `p (n+7)`
and `σ` a sign.  If the third value back is positive (the granted relation
`p (n+4) ≺ p (n+7)`) and the trajectory satisfies the sub-Fibonacci bound
`a₄ ≤ a₃ + a₅` at
`r`, then `b (n+4)` takes at `r` the sign opposite to `σ`; with `σ` the sign of
`(p (n+7))'(r)` this is the bridge orientation at `r`. -/
theorem bridge_at_root_of_subFib (n : ℕ) (r σ : ℝ) (hroot : (p (n + 7)).IsRoot r)
    (h3 : 0 < σ * (p (n + 4)).eval r)
    (hfib : σ * (p (n + 3)).eval r ≤ σ * (p (n + 4)).eval r + σ * (p (n + 2)).eval r) :
    σ * (b (n + 4)).eval r < 0 := by
  have hr1 : r < -1 := root_lt_neg_one hroot
  have ht : 1 < -r := by linarith
  set A : ℕ → ℝ := fun k => σ * (p k).eval r with hAdef
  have hA : ∀ k, A k = σ * (p k).eval r := fun _ => rfl
  have hrec := traj_rec r σ A hA
  have hle : A (n + 7) ≤ 0 := by
    rw [hA, IsRoot.def.mp hroot, mul_zero]
  have hcrux := crux_of_subFib hrec ht hle h3 hfib
  have hb := traj_bridge r σ A hA n
  rw [hb]; linarith

/-- **The bridge at a zero with a short run.**  If the fifth value back is nonnegative and
the seventh is nonpositive, the sub-Fibonacci bound is automatic and the bridge holds. -/
theorem bridge_at_root_of_short_run (n : ℕ) (r σ : ℝ) (hroot : (p (n + 7)).IsRoot r)
    (h3 : 0 < σ * (p (n + 4)).eval r) (h5 : 0 ≤ σ * (p (n + 2)).eval r)
    (h7 : σ * (p n).eval r ≤ 0) :
    σ * (b (n + 4)).eval r < 0 := by
  have hr1 : r < -1 := root_lt_neg_one hroot
  have ht : 1 < -r := by linarith
  set A : ℕ → ℝ := fun k => σ * (p k).eval r with hAdef
  have hA : ∀ k, A k = σ * (p k).eval r := fun _ => rfl
  have hrec := traj_rec r σ A hA
  have hle : A (n + 7) ≤ 0 := by
    rw [hA, IsRoot.def.mp hroot, mul_zero]
  have hcrux := crux_of_short_run hrec ht hle h3 h5 h7
  have hb := traj_bridge r σ A hA n
  rw [hb]; linarith

/-- **The bridge at a zero with a run of length four.**  Here the input is the bridge
inequality at the previous crossing of the same trajectory, `(-r)·a₇ ≤ a₅`, i.e.
`σ · (b n)(r) ≥ 0`. -/
theorem bridge_at_root_of_prev (n : ℕ) (r σ : ℝ) (hroot : (p (n + 7)).IsRoot r)
    (h2 : 0 < σ * (p (n + 5)).eval r) (hprev : 0 ≤ σ * (b n).eval r) :
    σ * (b (n + 4)).eval r < 0 := by
  have hr1 : r < -1 := root_lt_neg_one hroot
  have ht : (0 : ℝ) < -r := by linarith
  set A : ℕ → ℝ := fun k => σ * (p k).eval r with hAdef
  have hA : ∀ k, A k = σ * (p k).eval r := fun _ => rfl
  have hrec := traj_rec r σ A hA
  have hle : A (n + 7) ≤ 0 := by
    rw [hA, IsRoot.def.mp hroot, mul_zero]
  have hprev' : (-r) * A n ≤ A (n + 2) := by
    rw [hA, hA]
    rw [eval_b] at hprev
    nlinarith
  have hcrux := crux_of_prev hrec ht hle h2 hprev'
  have hb := traj_bridge r σ A hA n
  rw [hb]; linarith

end

end RealRooted.Applications.OEIS.A275442.Bridge
