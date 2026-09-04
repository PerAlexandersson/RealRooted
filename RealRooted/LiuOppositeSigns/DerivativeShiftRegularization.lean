import RealRooted.DerivativeShiftRootMatching
import RealRooted.LiuOppositeSigns.NoCommonRoots

/-!
# Derivative-shift regularization for Liu pairs

This module proves that sufficiently small common positive derivative shifts
preserve the no-common-root condition used in Liu's finite root-count descent.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace LiuOppositeSigns

/-- A common positive `TDeriv` shift of two nonzero splitting polynomials with
no common roots still has no common roots when the shift is sufficiently
small. -/
theorem NoCommonRoots.exists_delta_TDeriv
    {f g : ℝ[X]} (hno : NoCommonRoots f g)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0) (hf : f.Splits) (hg : g.Splits) :
    ∃ δ > 0, ∀ ⦃eps : ℝ⦄, 0 < eps → eps < δ →
      NoCommonRoots (TDeriv eps f) (TDeriv eps g) := by
  obtain ⟨η, hη_pos, _, hsep⟩ :=
    Multiset.exists_pos_lt_and_two_mul_le_abs_sub_toFinset
      (f.roots + g.roots) zero_lt_one
  obtain ⟨δf, hδf_pos, hfrel⟩ :=
    exists_delta_roots_rel_TDeriv hf hη_pos
  obtain ⟨δg, hδg_pos, hgrel⟩ :=
    exists_delta_roots_rel_TDeriv hg hη_pos
  refine ⟨min δf δg, lt_min hδf_pos hδg_pos, ?_⟩
  intro eps heps_pos hepsδ x hfx hgx
  obtain ⟨a, ha_mem, hax⟩ := by
    simpa only [Function.flip_def] using
      Multiset.exists_mem_of_rel_of_mem
        ((Multiset.rel_flip).2
          (hfrel heps_pos (hepsδ.trans_le (min_le_left _ _))))
        ((Polynomial.mem_roots (TDeriv_ne_zero hf_ne)).mpr hfx)
  obtain ⟨b, hb_mem, hbx⟩ := by
    simpa only [Function.flip_def] using
      Multiset.exists_mem_of_rel_of_mem
        ((Multiset.rel_flip).2
          (hgrel heps_pos (hepsδ.trans_le (min_le_right _ _))))
        ((Polynomial.mem_roots (TDeriv_ne_zero hg_ne)).mpr hgx)
  have hab_ne : a ≠ b := by
    rintro rfl
    exact (hno a ((Polynomial.mem_roots hf_ne).mp ha_mem))
      ((Polynomial.mem_roots hg_ne).mp hb_mem)
  have ha_sum : a ∈ (f.roots + g.roots).toFinset := by simp [ha_mem]
  have hb_sum : b ∈ (f.roots + g.roots).toFinset := by simp [hb_mem]
  have hab_sep : 2 * η ≤ |a - b| :=
    hsep a ha_sum b hb_sum hab_ne
  have hab_lt : |a - b| < 2 * η := by
    calc
      |a - b| ≤ |a - x| + |x - b| := by
        simpa only [sub_add_sub_cancel] using
          abs_add_le (a - x) (x - b)
      _ = |x - a| + |x - b| := by rw [abs_sub_comm a x]
      _ < 2 * η := by linarith
  exact (not_lt_of_ge hab_sep) hab_lt

end LiuOppositeSigns
end RealRooted
