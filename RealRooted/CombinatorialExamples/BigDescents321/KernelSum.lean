import RealRooted.CombinatorialExamples.BigDescents321.Kernel
import Mathlib.Tactic.FieldSimp

/-!
# The kernel moments as weighted finite sums

For `r ≥ 2` the kernel coefficients `c_r(J) = -m(r, J)` have the positive-weight form

`c_r(J) = 2^(1 - 2r) ∑_(k ≤ r) W_(r,k)(J) F(r, J, k)`,

`W_(r,k)(J) = (r+k-2)! (2J+r+k+1)! (J+k+1)! / (k! (r-k)! (2J+2k+3)! (J+k+r+1)!)`,
`F(r, J, k) = k(4J + 3k + 2r + 5) - r(r - 1)`.

Both sides satisfy the recurrence
`2(r+1) m(r+1, J) = (1 - 2r)(m(r, J+2) - 2 m(r, J+1)) - ((r - 2)/2) m(r-1, J+1)`,
which for the moments comes from the differential equation of `√D` in `y`, and for the sums
from an explicit telescoping certificate in `k`.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted.BigDescents321

/-- The weights `W_(r,k)(J)`. -/
def kernelWeight (r k J : ℕ) : ℚ :=
  ((r + k - 2).factorial * (2 * J + r + k + 1).factorial * (J + k + 1).factorial : ℚ) /
    ((k.factorial * (r - k).factorial * (2 * J + 2 * k + 3).factorial *
      (J + k + r + 1).factorial : ℕ) : ℚ)

/-- `F(r, J, k) = k(4J + 3k + 2r + 5) - r(r - 1)`. -/
def kernelF (r J k : ℕ) : ℚ := k * (4 * J + 3 * k + 2 * r + 5) - r * (r - 1 : ℚ)

theorem kernelWeight_pos (r k J : ℕ) : 0 < kernelWeight r k J := by
  unfold kernelWeight
  apply div_pos
  · positivity
  · have : 0 < k.factorial * (r - k).factorial * (2 * J + 2 * k + 3).factorial *
        (J + k + r + 1).factorial := by positivity
    exact_mod_cast this

/-- `W_(r+1,k+1)(J) / W_(r+1,k)(J)`. -/
theorem kernelWeight_succ_right {r k J : ℕ} (hr : 2 ≤ r) (hk : k ≤ r) :
    kernelWeight (r + 1) (k + 1) J = kernelWeight (r + 1) k J *
      ((r + k) * (2 * J + r + k + 3) * (J + k + 2) * (r + 1 - k) /
        ((k + 1) * (2 * J + 2 * k + 4) * (2 * J + 2 * k + 5) * (J + k + r + 3)) : ℚ) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = k + s := ⟨r - k, by lia⟩
  obtain ⟨u, hu⟩ : ∃ u, k + s + 1 + k - 2 = u := ⟨_, rfl⟩
  simp only [kernelWeight]
  rw [show k + s + 1 + (k + 1) - 2 = u + 1 by lia, hu,
    show k + s + 1 - (k + 1) = s by lia, show k + s + 1 - k = s + 1 by lia,
    show 2 * J + (k + s + 1) + (k + 1) + 1 = 2 * J + (k + s + 1) + k + 1 + 1 by ring,
    show J + (k + 1) + 1 = J + k + 1 + 1 by ring,
    show 2 * J + 2 * (k + 1) + 3 = 2 * J + 2 * k + 3 + 1 + 1 by ring,
    show J + (k + 1) + (k + s + 1) + 1 = J + k + (k + s + 1) + 1 + 1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  have hu' : (u : ℚ) = 2 * k + s - 1 := by
    have : u + 1 = 2 * k + s := by lia
    rw [eq_sub_iff_add_eq]; exact_mod_cast this
  rw [hu']
  field_simp
  ring

/-- `W_(r,k)(J+2) / W_(r+1,k)(J)`. -/
theorem kernelWeight_two {r k J : ℕ} (hr : 2 ≤ r) (hk : k ≤ r) :
    kernelWeight r k (J + 2) = kernelWeight (r + 1) k J *
      ((2 * J + r + k + 3) * (2 * J + r + k + 4) * (2 * J + r + k + 5) * (J + k + 2) *
        (J + k + 3) * (r + 1 - k) / ((r + k - 1) * (2 * J + 2 * k + 4) * (2 * J + 2 * k + 5) *
        (2 * J + 2 * k + 6) * (2 * J + 2 * k + 7) * (J + k + r + 3)) : ℚ) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = k + s := ⟨r - k, by lia⟩
  simp only [kernelWeight]
  rw [show k + s + 1 + k - 2 = (k + s + k - 2) + 1 by lia, show k + s - k = s by lia,
    show k + s + 1 - k = s + 1 by lia,
    show 2 * (J + 2) + (k + s) + k + 1 = (2 * J + (k + s + 1) + k + 1) + 1 + 1 + 1 by ring,
    show J + 2 + k + 1 = (J + k + 1) + 1 + 1 by ring,
    show 2 * (J + 2) + 2 * k + 3 = (2 * J + 2 * k + 3) + 1 + 1 + 1 + 1 by ring,
    show J + 2 + k + (k + s) + 1 = (J + k + (k + s + 1) + 1) + 1 by ring]
  generalize hu : k + s + k - 2 = u
  generalize hA : 2 * J + (k + s + 1) + k + 1 = A
  generalize hB : J + k + 1 = B
  generalize hC : 2 * J + 2 * k + 3 = Cc
  generalize hE : J + k + (k + s + 1) + 1 = E
  simp only [Nat.factorial_succ]
  push_cast
  have hu' : (u : ℚ) = 2 * k + s - 2 := by
    have : u + 2 = 2 * k + s := by lia
    rw [eq_sub_iff_add_eq]; exact_mod_cast this
  have h2 : (2 : ℚ) ≤ k + s := by exact_mod_cast hr
  have hk0 : (0 : ℚ) ≤ k := k.cast_nonneg
  have hn1 : ((k : ℚ) + s + k - 1) ≠ 0 := by intro h; linarith
  have hn2 : ((k : ℚ) + s + k + 1) ≠ 0 := by intro h; linarith
  have hn3 : ((k : ℚ) + s + k) ≠ 0 := by intro h; linarith
  have hn4 : (2 * (k : ℚ) + s - 2 + 1) ≠ 0 := by intro h; linarith
  have hA' : (A : ℚ) = 2 * J + 2 * k + s + 2 := by rw [← hA]; push_cast; ring
  have hB' : (B : ℚ) = J + k + 1 := by rw [← hB]; push_cast; ring
  have hC' : (Cc : ℚ) = 2 * J + 2 * k + 3 := by rw [← hC]; push_cast; ring
  have hE' : (E : ℚ) = J + 2 * k + s + 2 := by rw [← hE]; push_cast; ring
  rw [hu', hA', hB', hC', hE']
  field_simp
  ring

/-- `W_(r,k)(J+1) / W_(r+1,k)(J)`. -/
theorem kernelWeight_one {r k J : ℕ} (hr : 2 ≤ r) (hk : k ≤ r) :
    kernelWeight r k (J + 1) = kernelWeight (r + 1) k J *
      ((2 * J + r + k + 3) * (J + k + 2) * (r + 1 - k) /
        ((r + k - 1) * (2 * J + 2 * k + 4) * (2 * J + 2 * k + 5)) : ℚ) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = k + s := ⟨r - k, by lia⟩
  simp only [kernelWeight]
  rw [show k + s + 1 + k - 2 = (k + s + k - 2) + 1 by lia, show k + s - k = s by lia,
    show k + s + 1 - k = s + 1 by lia,
    show 2 * (J + 1) + (k + s) + k + 1 = (2 * J + (k + s + 1) + k + 1) + 1 by ring,
    show J + 1 + k + 1 = (J + k + 1) + 1 by ring,
    show 2 * (J + 1) + 2 * k + 3 = (2 * J + 2 * k + 3) + 1 + 1 by ring,
    show J + 1 + k + (k + s) + 1 = J + k + (k + s + 1) + 1 by ring]
  generalize hu : k + s + k - 2 = u
  generalize hA : 2 * J + (k + s + 1) + k + 1 = A
  generalize hB : J + k + 1 = B
  generalize hC : 2 * J + 2 * k + 3 = Cc
  generalize hE : J + k + (k + s + 1) + 1 = E
  simp only [Nat.factorial_succ]
  push_cast
  have hu' : (u : ℚ) = 2 * k + s - 2 := by
    have : u + 2 = 2 * k + s := by lia
    rw [eq_sub_iff_add_eq]; exact_mod_cast this
  have h2 : (2 : ℚ) ≤ k + s := by exact_mod_cast hr
  have hk0 : (0 : ℚ) ≤ k := k.cast_nonneg
  have hn1 : ((k : ℚ) + s + k - 1) ≠ 0 := by intro h; linarith
  have hn2 : ((k : ℚ) + s + k + 1) ≠ 0 := by intro h; linarith
  have hn3 : ((k : ℚ) + s + k) ≠ 0 := by intro h; linarith
  have hn4 : (2 * (k : ℚ) + s - 2 + 1) ≠ 0 := by intro h; linarith
  have hA' : (A : ℚ) = 2 * J + 2 * k + s + 2 := by rw [← hA]; push_cast; ring
  have hB' : (B : ℚ) = J + k + 1 := by rw [← hB]; push_cast; ring
  have hC' : (Cc : ℚ) = 2 * J + 2 * k + 3 := by rw [← hC]; push_cast; ring
  have hE' : (E : ℚ) = J + 2 * k + s + 2 := by rw [← hE]; push_cast; ring
  rw [hu', hA', hB', hC']
  field_simp
  ring

/-- `W_(r,k)(J+1) / W_(r+2,k)(J)`, the lower neighbour in the recurrence. -/
theorem kernelWeight_lower {r k J : ℕ} (hr : 2 ≤ r) (hk : k ≤ r) :
    kernelWeight r k (J + 1) = kernelWeight (r + 2) k J *
      ((r + 2 - k) * (r + 1 - k) * (J + k + 2) * (J + k + r + 3) /
        ((r + k) * (r + k - 1) * (2 * J + 2 * k + 4) * (2 * J + 2 * k + 5)) : ℚ) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = k + s := ⟨r - k, by lia⟩
  simp only [kernelWeight]
  rw [show k + s + 2 + k - 2 = (k + s + k - 2) + 1 + 1 by lia, show k + s - k = s by lia,
    show k + s + 2 - k = s + 1 + 1 by lia,
    show 2 * (J + 1) + (k + s) + k + 1 = 2 * J + (k + s + 2) + k + 1 by ring,
    show J + 1 + k + 1 = (J + k + 1) + 1 by ring,
    show 2 * (J + 1) + 2 * k + 3 = (2 * J + 2 * k + 3) + 1 + 1 by ring,
    show J + k + (k + s + 2) + 1 = (J + 1 + k + (k + s) + 1) + 1 by ring]
  generalize hu : k + s + k - 2 = u
  generalize hA : 2 * J + (k + s + 2) + k + 1 = A
  generalize hB : J + k + 1 = B
  generalize hC : 2 * J + 2 * k + 3 = Cc
  generalize hE : J + 1 + k + (k + s) + 1 = E
  simp only [Nat.factorial_succ]
  push_cast
  have hu' : (u : ℚ) = 2 * k + s - 2 := by
    have : u + 2 = 2 * k + s := by lia
    rw [eq_sub_iff_add_eq]; exact_mod_cast this
  have h2 : (2 : ℚ) ≤ k + s := by exact_mod_cast hr
  have hk0 : (0 : ℚ) ≤ k := k.cast_nonneg
  have hn1 : ((k : ℚ) + s + k - 1) ≠ 0 := by intro h; linarith
  have hn2 : ((k : ℚ) + s + k + 1) ≠ 0 := by intro h; linarith
  have hn3 : ((k : ℚ) + s + k) ≠ 0 := by intro h; linarith
  have hn4 : (2 * (k : ℚ) + s - 2 + 1) ≠ 0 := by intro h; linarith
  have hA' : (A : ℚ) = 2 * J + 2 * k + s + 3 := by rw [← hA]; push_cast; ring
  have hB' : (B : ℚ) = J + k + 1 := by rw [← hB]; push_cast; ring
  have hC' : (Cc : ℚ) = 2 * J + 2 * k + 3 := by rw [← hC]; push_cast; ring
  have hE' : (E : ℚ) = J + 2 * k + s + 2 := by rw [← hE]; push_cast; ring
  rw [hu', hB', hC', hE']
  field_simp
  ring

end RealRooted.BigDescents321
