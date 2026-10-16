module

public import RealRooted.Applications.OEIS.A275442.Bridge.Family

/-!
# Unconditional signs for the A275442 bridge

The scalar no-bounce theorem rules out common consecutive roots and proves
that the preceding row and the bridge have opposite signs at every bridge root.
-/

public noncomputable section

namespace RealRooted.Applications.OEIS.A275442.Bridge

open Polynomial

/-- **No common real zero of consecutive members of the family.** -/
theorem no_common_root_succ (n : ℕ) (r : ℝ) (hr : (p (n + 3)).IsRoot r) :
    ¬ (p (n + 4)).IsRoot r := fun hr4 =>
  no_common_root (n + 3) r hr (by rw [show n + 3 + 1 = n + 4 from by lia]; exact hr4)

/-- **The bridge and the previous member of the family have opposite signs at every zero of
`p (n+3)`** (`n ≥ 4`).  In particular the bridge does not vanish there. -/
theorem bridge_pair_sign (n : ℕ) (hn : 4 ≤ n) (r : ℝ) (hr : (p (n + 3)).IsRoot r) :
    (p (n + 2)).eval r * (b n).eval r < 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by lia⟩
  have hr' : (p (k + 7)).IsRoot r := by
    rw [show k + 7 = k + 4 + 3 from by lia]; exact hr
  have := bridge_sign_at_root k r hr'
  rw [show k + 6 = k + 4 + 2 from by lia] at this
  exact this

end RealRooted.Applications.OEIS.A275442.Bridge
