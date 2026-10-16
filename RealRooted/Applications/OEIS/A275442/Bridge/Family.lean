module

public import RealRooted.Applications.OEIS.A275442.Bridge.Scalar

/-!
# The structural theorem applied to the family `p`

The trajectory of the family at a real point `r < -1` is `traj r k = (p k).eval r`; it
satisfies the scalar recurrence with `t = -r > 1` and starts with `1, 1, 1, 2`.  The
initial-run hypothesis is verified here: for a crossing at index `m ≤ 12` by the explicit
values `p 4, …, p 12` (one-variable polynomial inequalities in `t`), and for `m ≥ 13` by
the certificate `Bridge.crux_cert_z`.

Consequences, all unconditional:

* `Bridge.no_common_root` — two consecutive members of the family have no common real zero;
* `Bridge.bridge_sign_at_root` — at a zero of `p (n+7)` the bridge `b (n+4)` and `p (n+6)`
  take strictly opposite signs (in particular the bridge does not vanish there).
-/

@[expose] public noncomputable section

namespace RealRooted.Applications.OEIS.A275442.Bridge

open Polynomial

/-- The trajectory of the family at a real point. -/
def traj (r : ℝ) (k : ℕ) : ℝ := (p k).eval r

@[simp] theorem traj_zero (r : ℝ) : traj r 0 = 1 := by simp [traj]
@[simp] theorem traj_one (r : ℝ) : traj r 1 = 1 := by simp [traj]
@[simp] theorem traj_two (r : ℝ) : traj r 2 = 1 := by simp [traj]
@[simp] theorem traj_three (r : ℝ) : traj r 3 = 2 := by simp [traj]

/-- The trajectory satisfies the scalar lag-four recurrence with `t = -r`. -/
theorem traj_recurrence (r : ℝ) (k : ℕ) :
    traj r (k + 4) = traj r (k + 3) + traj r (k + 2) - (-r) * traj r k := by
  simp only [traj, eval_p_rec r k]; ring

/-- The first four values of the trajectory are positive. -/
theorem traj_startSign (r : ℝ) : StartSign (traj r) := by
  refine Or.inl fun j hj => ?_
  interval_cases j <;> norm_num

/-- The mirrored trajectory has no initial run at all. -/
theorem traj_initRun_neg (r : ℝ) : InitRun (-r) (-(traj r)) := by
  intro n _ _ hrun
  exfalso
  have h := hrun 1 (by lia) (by lia)
  simp only [Pi.neg_apply, traj_one] at h
  linarith

/-- **The initial-run hypothesis for the family.**  A crossing preceded only by positive
values satisfies the crux inequality. -/
theorem traj_initRun (r : ℝ) (hr : r < -1) : InitRun (-r) (traj r) := by
  intro n h3 h4 hrun
  set t : ℝ := -r with htdef
  have ht : 1 < t := by rw [htdef]; linarith
  have hrec := traj_recurrence r
  -- the explicit values of the trajectory
  have v4 : traj r 4 = 3 - t := by
    have h := hrec 0
    simp only [Nat.reduceAdd, traj_zero, traj_two, traj_three] at h
    linarith
  have v5 : traj r 5 = 5 - 2 * t := by
    have h := hrec 1
    simp only [Nat.reduceAdd, traj_one, traj_three] at h
    rw [v4] at h
    linarith
  have v6 : traj r 6 = 8 - 4 * t := by
    have h := hrec 2
    simp only [Nat.reduceAdd, traj_two] at h
    rw [v5, v4] at h
    linarith
  have v7 : traj r 7 = 13 - 8 * t := by
    have h := hrec 3
    simp only [Nat.reduceAdd, traj_three] at h
    rw [v6, v5] at h
    linarith
  have v8 : traj r 8 = 21 - 15 * t + t ^ 2 := by
    have h := hrec 4; rw [v7, v6, v4] at h; nlinarith [h]
  have v9 : traj r 9 = 34 - 28 * t + 3 * t ^ 2 := by
    have h := hrec 5; rw [v8, v7, v5] at h; nlinarith [h]
  have v10 : traj r 10 = 55 - 51 * t + 8 * t ^ 2 := by
    have h := hrec 6; rw [v9, v8, v6] at h; nlinarith [h]
  have v11 : traj r 11 = 89 - 92 * t + 19 * t ^ 2 := by
    have h := hrec 7; rw [v10, v9, v7] at h; nlinarith [h]
  have v12 : traj r 12 = 144 - 164 * t + 42 * t ^ 2 - t ^ 3 := by
    have h := hrec 8; rw [v11, v10, v8] at h; nlinarith [h]
  rcases Nat.lt_or_ge n 9 with hn | hn
  · -- the crossing is at an index `≤ 12`: explicit one-variable inequalities
    interval_cases n
    · rw [show (0:ℕ) + 4 = 4 from rfl, v4] at h4
      rw [show (0:ℕ) + 3 = 3 from rfl, show (0:ℕ) + 1 = 1 from rfl, traj_three, traj_one]
      linarith
    · rw [show (1:ℕ) + 4 = 5 from rfl, v5] at h4
      rw [show (1:ℕ) + 3 = 4 from rfl, show (1:ℕ) + 1 = 2 from rfl, v4, traj_two]
      linarith
    · rw [show (2:ℕ) + 4 = 6 from rfl, v6] at h4
      rw [show (2:ℕ) + 3 = 5 from rfl, show (2:ℕ) + 1 = 3 from rfl, v5, traj_three]
      linarith
    · rw [show (3:ℕ) + 4 = 7 from rfl, v7] at h4
      rw [show (3:ℕ) + 3 = 6 from rfl, show (3:ℕ) + 1 = 4 from rfl, v6, v4]
      have hp : 0 < 8 - 4 * t := by rw [← v6]; exact hrun 6 (by lia) (by lia)
      nlinarith
    · rw [show (4:ℕ) + 4 = 8 from rfl, v8] at h4
      rw [show (4:ℕ) + 3 = 7 from rfl, show (4:ℕ) + 1 = 5 from rfl, v7, v5]
      have hp : 0 < 13 - 8 * t := by rw [← v7]; exact hrun 7 (by lia) (by lia)
      nlinarith
    · rw [show (5:ℕ) + 4 = 9 from rfl, v9] at h4
      rw [show (5:ℕ) + 3 = 8 from rfl, show (5:ℕ) + 1 = 6 from rfl, v8, v6]
      have h7 : 0 < 13 - 8 * t := by rw [← v7]; exact hrun 7 (by lia) (by lia)
      have hp : 0 < 21 - 15 * t + t ^ 2 := by rw [← v8]; exact hrun 8 (by lia) (by lia)
      have hb : t < 13 / 8 := by linarith
      nlinarith
    · rw [show (6:ℕ) + 4 = 10 from rfl, v10] at h4
      rw [show (6:ℕ) + 3 = 9 from rfl, show (6:ℕ) + 1 = 7 from rfl, v9, v7]
      have h7 : 0 < 13 - 8 * t := by rw [← v7]; exact hrun 7 (by lia) (by lia)
      have h8 : 0 < 21 - 15 * t + t ^ 2 := by rw [← v8]; exact hrun 8 (by lia) (by lia)
      have hb1 : t < 13 / 8 := by linarith
      have hb : t < 8 / 5 := by nlinarith
      have hp : 0 < 34 - 28 * t + 3 * t ^ 2 := by rw [← v9]; exact hrun 9 (by lia) (by lia)
      nlinarith
    · rw [show (7:ℕ) + 4 = 11 from rfl, v11] at h4
      rw [show (7:ℕ) + 3 = 10 from rfl, show (7:ℕ) + 1 = 8 from rfl, v10, v8]
      have h7 : 0 < 13 - 8 * t := by rw [← v7]; exact hrun 7 (by lia) (by lia)
      have h8 : 0 < 21 - 15 * t + t ^ 2 := by rw [← v8]; exact hrun 8 (by lia) (by lia)
      have h9 : 0 < 34 - 28 * t + 3 * t ^ 2 := by rw [← v9]; exact hrun 9 (by lia) (by lia)
      have hb1 : t < 13 / 8 := by linarith
      have hb2 : t < 8 / 5 := by nlinarith
      have hb : t < 36 / 25 := by nlinarith
      have hp : 0 < 55 - 51 * t + 8 * t ^ 2 := by rw [← v10]; exact hrun 10 (by lia) (by lia)
      nlinarith
    · rw [show (8:ℕ) + 4 = 12 from rfl, v12] at h4
      rw [show (8:ℕ) + 3 = 11 from rfl, show (8:ℕ) + 1 = 9 from rfl, v11, v9]
      have h7 : 0 < 13 - 8 * t := by rw [← v7]; exact hrun 7 (by lia) (by lia)
      have h8 : 0 < 21 - 15 * t + t ^ 2 := by rw [← v8]; exact hrun 8 (by lia) (by lia)
      have h9 : 0 < 34 - 28 * t + 3 * t ^ 2 := by rw [← v9]; exact hrun 9 (by lia) (by lia)
      have h11 : 0 < 89 - 92 * t + 19 * t ^ 2 := by rw [← v11]; exact hrun 11 (by lia) (by lia)
      have hb1 : t < 13 / 8 := by linarith
      have hb2 : t < 8 / 5 := by nlinarith
      have hb3 : t < 36 / 25 := by nlinarith
      have hb : t < 67 / 50 := by nlinarith
      nlinarith
  · -- long initial runs: the certificate `crux_cert_z`
    obtain ⟨s, rfl⟩ : ∃ s, n = s + 9 := ⟨n - 9, by lia⟩
    have h0 : 0 < traj r s := by
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · simp
      · exact hrun s hs (by lia)
    rw [show s + 9 + 3 = s + 12 from by lia, show s + 9 + 1 = s + 10 from by lia]
    exact crux_cert_z hrec ht.le s (hrun (s + 11) (by lia) (by lia))
      (hrun (s + 2) (by lia) (by lia)) h0
      (by rw [show s + 13 = s + 9 + 4 from by lia]; exact h4)

/-- **The structural theorem for the family.** -/
theorem traj_downStep (r : ℝ) (hr : r < -1) (m : ℕ) :
    DownStep (-r) (traj r) m ∧ DownStep (-r) (-(traj r)) m :=
  downStep_all (traj_recurrence r) (by linarith) (traj_startSign r) (traj_initRun r hr)
    (traj_initRun_neg r) m

/-- **Two consecutive members of the family have no common real zero.**  This is the
`no common root` statement; it is proved, not assumed. -/
theorem no_common_root (m : ℕ) (r : ℝ) (h1 : (p m).IsRoot r) (h2 : (p (m + 1)).IsRoot r) :
    False := by
  have hr : r < -1 := root_lt_neg_one h1
  refine no_two_zeros (t := -r) (S := traj r) (n := m + 1) (traj_startSign r)
    (fun k hk => traj_downStep r hr k) m (by lia) ?_ ?_
  · exact IsRoot.def.mp h1
  · exact IsRoot.def.mp h2

/-- **The bridge does not vanish at a zero of `p (n+7)`, and its sign there is opposite to
that of `p (n+6)`.**  No compatibility, interlacing or nonvanishing input is used. -/
theorem bridge_sign_at_root (n : ℕ) (r : ℝ) (hroot : (p (n + 7)).IsRoot r) :
    (p (n + 6)).eval r * (b (n + 4)).eval r < 0 := by
  have hr : r < -1 := root_lt_neg_one hroot
  have hzero : traj r (n + 7) = 0 := IsRoot.def.mp hroot
  have hb : (b (n + 4)).eval r = traj r (n + 6) - (-r) * traj r (n + 4) := by
    simp only [traj, eval_b]; ring
  have hne : traj r (n + 6) ≠ 0 := by
    intro h
    exact no_two_zeros (t := -r) (S := traj r) (n := n + 7) (traj_startSign r)
      (fun k hk => traj_downStep r hr k) (n + 6) (by lia) h
      (by rw [show n + 6 + 1 = n + 7 from by lia]; exact hzero)
  have hpn6 : (p (n + 6)).eval r = traj r (n + 6) := rfl
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- the mirrored crossing
    have hd := (traj_downStep r hr (n + 3)).2
      (by simp only [Pi.neg_apply]; rw [show n + 3 + 3 = n + 6 from by lia]; linarith)
      (by simp only [Pi.neg_apply]; rw [show n + 3 + 4 = n + 7 from by lia, hzero]; norm_num)
    have hc := hd.1
    simp only [Pi.neg_apply] at hc
    rw [show n + 3 + 3 = n + 6 from by lia, show n + 3 + 1 = n + 4 from by lia] at hc
    rw [hpn6, hb]
    nlinarith
  · have hd := (traj_downStep r hr (n + 3)).1
      (by rw [show n + 3 + 3 = n + 6 from by lia]; exact hpos)
      (by rw [show n + 3 + 4 = n + 7 from by lia, hzero])
    have hc := hd.1
    rw [show n + 3 + 3 = n + 6 from by lia, show n + 3 + 1 = n + 4 from by lia] at hc
    rw [hpn6, hb]
    nlinarith

end RealRooted.Applications.OEIS.A275442.Bridge
