module

public import RealRooted.MultiplierSequence.Infinite
import RealRooted.MultiplierSequence.Laguerre

/-!
# Geometric and affine PF multiplier sequences

Positive geometric factors rescale the variable, and nonnegative affine
factors are shifted Euler operators. Finite products preserve the same cone.
-/

public section

open Polynomial

namespace RealRooted

/-- Every positive geometric sequence is a PF multiplier sequence. -/
theorem isPFMultiplierSequence_pow {c : ℝ} (hc : 0 < c) :
    IsPFMultiplierSequence (fun k => c ^ k) := by
  rw [isPFMultiplierSequence_iff_preserves]
  intro p hp
  have hscaled := hp.comp_C_mul_X_add_C hc le_rfl
  have heq : diagonalOperator (fun k => c ^ k) p =
      p.comp (C c * X + C 0) := by
    ext k
    rw [coeff_diagonalOperator]
    simp only [C_0, add_zero, Polynomial.comp_C_mul_X_coeff]
    ring
  rw [heq]
  exact hscaled

/-- A nonnegative affine sequence is a PF multiplier sequence. -/
theorem isPFMultiplierSequence_mul_natCast_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsPFMultiplierSequence (fun k => a * k + b) := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using isPFMultiplierSequence_const_sequence hb
  · have h := (isPFMultiplierSequence_natCast_add (div_nonneg hb ha.le)).const_mul ha.le
    convert h using 1
    ext k
    field_simp

/-- Finite products of PF multiplier sequences are PF multiplier sequences. -/
theorem IsPFMultiplierSequence.finsetProd {ι : Type*} (s : Finset ι)
    (gamma : ι → ℕ → ℝ) (hgamma : ∀ i ∈ s, IsPFMultiplierSequence (gamma i)) :
    IsPFMultiplierSequence (fun k => ∏ i ∈ s, gamma i k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPFMultiplierSequence_one_sequence
  | @insert i s hi ih =>
    simpa [Finset.prod_insert hi] using (hgamma i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hgamma j (Finset.mem_insert_of_mem hj)))

end RealRooted
