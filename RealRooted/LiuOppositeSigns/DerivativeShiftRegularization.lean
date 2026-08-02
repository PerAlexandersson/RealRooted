import RealRooted.DerivativeShiftRootMatching
import RealRooted.LiuOppositeSigns.Theorem21Statements

/-!
# Derivative-shift regularization for Liu pairs

This module proves that sufficiently small common positive derivative shifts
preserve the no-common-root condition used in Liu's finite root-count descent.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace LiuOppositeSigns

private theorem exists_left_mem_of_right_mem_of_rel
    {α β : Type*} {r : α → β → Prop} {s : Multiset α} {t : Multiset β}
    (hrel : Multiset.Rel r s t) {b : β} (hb : b ∈ t) :
    ∃ a ∈ s, r a b := by
  induction hrel with
  | zero => simp at hb
  | @cons a b s t hab _ ih =>
      rw [Multiset.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨a, Multiset.mem_cons_self, hab⟩
      · obtain ⟨a', ha', ha'b⟩ := ih hb
        exact ⟨a', Multiset.mem_cons_of_mem ha', ha'b⟩

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
  have hfx_mem : x ∈ (TDeriv eps f).roots :=
    (Polynomial.mem_roots (TDeriv_ne_zero hf_ne)).mpr hfx
  have hgx_mem : x ∈ (TDeriv eps g).roots :=
    (Polynomial.mem_roots (TDeriv_ne_zero hg_ne)).mpr hgx
  obtain ⟨a, ha_mem, hax⟩ :=
    exists_left_mem_of_right_mem_of_rel
      (hfrel heps_pos (hepsδ.trans_le (min_le_left _ _))) hfx_mem
  obtain ⟨b, hb_mem, hbx⟩ :=
    exists_left_mem_of_right_mem_of_rel
      (hgrel heps_pos (hepsδ.trans_le (min_le_right _ _))) hgx_mem
  have hab_ne : a ≠ b := by
    rintro rfl
    exact (hno a ((Polynomial.mem_roots hf_ne).mp ha_mem))
      ((Polynomial.mem_roots hg_ne).mp hb_mem)
  have ha_sum : a ∈ (f.roots + g.roots).toFinset := by
    simp [ha_mem]
  have hb_sum : b ∈ (f.roots + g.roots).toFinset := by
    simp [hb_mem]
  have hab_sep : 2 * η ≤ |a - b| :=
    hsep a ha_sum b hb_sum hab_ne
  have hab_lt : |a - b| < 2 * η := by
    calc
      |a - b| ≤ |a - x| + |x - b| :=
        abs_sub_le_abs_sub_add_abs_sub a x b
      _ = |x - a| + |x - b| := by rw [abs_sub_comm a x]
      _ < 2 * η := by linarith
  exact (not_lt_of_ge hab_sep) hab_lt

end LiuOppositeSigns
end RealRooted
