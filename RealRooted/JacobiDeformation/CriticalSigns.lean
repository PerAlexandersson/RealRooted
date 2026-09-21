import RealRooted.MaWang.Strong
import RealRooted.SimpleRoots

/-!
# Critical-sign assembly for the Jacobi deformation

This module packages the generic Sturm step used by the Jacobi deformation.
It contains no Jacobi-specific critical-point calculation: callers supply the
strict sign at the roots of the lower-degree polynomial.
-/

open Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- A degree-one critical-sign step gives strict interlacing, splitness, and
simple roots.  The sign hypothesis itself forces the lower polynomial to have
simple roots, so no separate simplicity hypothesis is needed.

For `n = 0`, the sign condition is vacuous; the conclusion instead uses the
existing constant--linear interlacing theorem. -/
theorem strictInterl_assembly_of_eval_mul_derivative_neg_succ
    {h g : ℝ[X]} {n : ℕ}
    (hh_splits : h.Splits)
    (hh_pos : HasPosLeadingCoeff h)
    (hg_pos : HasPosLeadingCoeff g)
    (hh_degree : h.natDegree = n)
    (hg_degree : g.natDegree = n + 1)
    (hsign : ∀ r, h.IsRoot r → g.eval r * h.derivative.eval r < 0) :
    StrictInterl h g ∧ Interlaces h g ∧ g.Splits ∧ HasSimpleRoots h ∧
      HasSimpleRoots g ∧ ∀ r, h.IsRoot r → ¬ g.IsRoot r := by
  have hno_common : ∀ r : ℝ, ¬ (h.IsRoot r ∧ g.IsRoot r) := by
    intro r hroot
    have hstrict := hsign r hroot.1
    have hzero : g.eval r = 0 := hroot.2
    rw [hzero, zero_mul] at hstrict
    exact (lt_irrefl 0) hstrict
  cases n with
  | zero =>
      have hg_degree_one : g.natDegree = 1 := by simpa using hg_degree
      have hh_const : h = C (h.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hh_degree
      have hh_coeff_ne : h.coeff 0 ≠ 0 := by
        intro hh_coeff_zero
        apply hh_pos.ne_zero
        rw [hh_const, hh_coeff_zero]
        simp
      have hinter : Interlaces h g := by
        rw [hh_const]
        exact interlaces_C_linear hh_coeff_ne hg_degree_one
      have hstrict : StrictInterl h g := hinter.toStrictInterl
      have hsimp := hstrict.hasSimpleRoots_of_no_common_root hno_common
      exact ⟨hstrict, hinter, (isRealRooted_of_degree_one hg_degree_one).2,
        hsimp.1, hsimp.2, fun r hr hgr => hno_common r ⟨hr, hgr⟩⟩
  | succ n =>
      have hh_degree_pos : 1 ≤ h.natDegree := by
        rw [hh_degree]
        exact Nat.succ_le_succ (Nat.zero_le n)
      have hg_degree_succ : g.natDegree = h.natDegree + 1 := by
        calc
          g.natDegree = n.succ + 1 := hg_degree
          _ = h.natDegree + 1 := by rw [hh_degree]
      have hder : Interlaces h.derivative h :=
        interlaces_derivative_of_pos_natDegree hh_pos.ne_zero hh_splits hh_pos
          hh_degree_pos
      have hder_pos : HasPosLeadingCoeff h.derivative :=
        hh_pos.derivative (by rw [hh_degree]; exact Nat.succ_ne_zero _)
      have hstrict : StrictInterl h g :=
        prec_of_interlaces_eval_mul_neg_succ hder hder_pos hg_pos hg_degree_succ hsign
      have hinter : Interlaces h g :=
        hstrict.toInterlaces hg_degree_succ.symm
      have hsimp := hstrict.hasSimpleRoots_of_no_common_root hno_common
      exact ⟨hstrict, hinter, hstrict.2.1.2, hsimp.1, hsimp.2,
        fun r hr hgr => hno_common r ⟨hr, hgr⟩⟩

end RealRooted.JacobiDeformation
