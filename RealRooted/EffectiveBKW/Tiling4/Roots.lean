module

public import RealRooted.EffectiveBKW.Tiling4.Basic
public import RealRooted.EffectiveBKW.Tiling4.Endpoint
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
import RealRooted.EffectiveBKW.Tiling4.RootCount
import RealRooted.EffectiveBKW.Tiling4.EdgePhase
import Mathlib.Tactic.Linarith

/-!
# Real-rootedness of every four-row tiling polynomial

The endpoint phase bounds furnish the full alternating grid at every positive
index. We close the odd degrees with the interior gaps and the even degrees
with the additional sign at the unbounded left end.
-/

public section

namespace RealRooted.EffectiveBKW.Tiling4

/-- Every recurrence row has its prescribed degree and distinct real roots below the collision. -/
theorem polynomial_roots (n : ℕ) :
    (polynomial n).natDegree = 2 * (n / 2) ∧ (polynomial n).Splits ∧
      (polynomial n).roots.Nodup ∧ ∀ z ∈ (polynomial n).roots, z < rightEdge := by
  refine ⟨natDegree_polynomial n, ?_⟩
  cases n with
  | zero => simp
  | succ n =>
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have heq : n + 1 = 2 * k + 1 := by lia
      change (polynomial (n + 1)).Splits ∧ (polynomial (n + 1)).roots.Nodup ∧
        ∀ z ∈ (polynomial (n + 1)).roots, z < rightEdge
      rw [heq]
      obtain ⟨a, b, hab, hb, hlo, hhi⟩ := exists_phase_bounds (2 * k)
      obtain ⟨s, hs, hmem, hsign⟩ := exists_alternating (2 * k)
        (hab.trans hb) hb hab hlo hhi
      exact splits_nodup_odd_of_alternating k s hs hmem hsign
    · have heq : n + 1 = 2 * (k + 1) := by lia
      change (polynomial (n + 1)).Splits ∧ (polynomial (n + 1)).roots.Nodup ∧
        ∀ z ∈ (polynomial (n + 1)).roots, z < rightEdge
      rw [heq]
      obtain ⟨a, b, hab, hb, hlo, hhi⟩ := exists_phase_bounds (2 * k + 1)
      obtain ⟨s, hs, hmem, hsign⟩ := exists_alternating (2 * k + 1)
        (hab.trans hb) hb hab hlo hhi
      apply splits_nodup_even_of_alternating k s hs hmem
      intro j
      simpa only [show 2 * k + 1 + 1 = 2 * (k + 1) by lia] using hsign j

/-- Every root is strictly negative, including the vacuous constant rows. -/
theorem roots_polynomial_neg (n : ℕ) {z : ℝ} (hz : z ∈ (polynomial n).roots) : z < 0 :=
  ((polynomial_roots n).2.2.2 z hz).trans rightEdge_neg

end RealRooted.EffectiveBKW.Tiling4
