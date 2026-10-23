/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.Polynomial.Factorization

/-!
# A real quadratic divisor of every polynomial of degree at least two

This is the nonmonic corollary of Mathlib's
`Polynomial.IsMonicOfDegree.eq_isMonicOfDegree_two_mul_isMonicOfDegree`.
-/

@[expose] public section

noncomputable section

namespace Polynomial

/-- Every real polynomial of degree at least two has a monic quadratic divisor. -/
theorem exists_monic_natDegree_two_dvd (p : ℝ[X]) (hp : 2 ≤ p.natDegree) :
    ∃ q : ℝ[X], q.Monic ∧ q.natDegree = 2 ∧ q ∣ p := by
  classical
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  have hmonic : IsMonicOfDegree (normalize p) (p.natDegree - 2 + 2) := by
    refine ⟨?_, monic_normalize hp0⟩
    simp only [natDegree_normalize]
    lia
  obtain ⟨q, r, hq, _, hfactor⟩ :=
    hmonic.eq_isMonicOfDegree_two_mul_isMonicOfDegree
  refine ⟨q, hq.monic, hq.natDegree_eq, ?_⟩
  apply dvd_normalize_iff.mp
  exact ⟨r, hfactor⟩

end Polynomial
