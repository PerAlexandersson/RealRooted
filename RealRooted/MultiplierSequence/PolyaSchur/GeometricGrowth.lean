module

public import RealRooted.MultiplierSequence.Infinite
import RealRooted.MultiplierSequence.PolyaSchur.Growth
import RealRooted.MultiplierSequence.PolyaSchur

/-!
# Geometric growth of PF multiplier sequences

The usual geometric estimate at a positive zeroth coefficient extends across
an arbitrary finite zero prefix by increasing the geometric ratio. The zero
sequence is included.
-/

public section

namespace RealRooted

/-- Every PF multiplier sequence admits a global geometric bound, including
sequences with a zero prefix and the identically zero sequence. -/
theorem IsPFMultiplierSequence.exists_geometric_bound {γ : ℕ → ℝ}
    (hγ : IsPFMultiplierSequence γ) :
    ∃ C ≥ 0, ∃ A ≥ 0, ∀ n, γ n ≤ C * A ^ n := by
  by_cases hz : γ = 0
  · exact ⟨0, le_rfl, 1, zero_le_one, by simp [hz]⟩
  obtain ⟨m, hm⟩ : ∃ m, γ m ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  let s := Nat.find (show ∃ m, γ m ≠ 0 from ⟨m, hm⟩)
  have hs : γ s ≠ 0 := Nat.find_spec (show ∃ m, γ m ≠ 0 from ⟨m, hm⟩)
  have hpos : 0 < γ s := (hγ.nonneg s).lt_of_ne' hs
  let r := γ (1 + s) / γ s
  have hr : 0 ≤ r := div_nonneg (hγ.nonneg _) hpos.le
  refine ⟨γ s, hpos.le, r + 1, by linarith, ?_⟩
  intro n
  by_cases hsn : s ≤ n
  · have htail := (hγ.shift s).coeff_le_geometric_of_coeff_zero_pos
      (by simpa using hpos) (n - s)
    have hbound : γ n ≤ γ s * r ^ (n - s) := by
      simpa only [zero_add, Nat.sub_add_cancel hsn] using htail
    apply hbound.trans
    apply mul_le_mul_of_nonneg_left _ hpos.le
    exact (pow_le_pow_left₀ hr (by linarith : r ≤ r + 1) _).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ r + 1) (Nat.sub_le n s))
  · have hn : γ n = 0 := by
      by_contra hn
      exact hsn (Nat.find_min' (show ∃ m, γ m ≠ 0 from ⟨m, hm⟩) hn)
    rw [hn]
    positivity

end RealRooted
