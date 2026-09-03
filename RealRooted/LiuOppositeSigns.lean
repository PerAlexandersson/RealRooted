import RealRooted.LiuOppositeSigns.PositiveSplitRootCount

/-!
# Liu opposite-sign compatibility branches

This compatibility module extends the positive-split and root-deletion
foundations with cross-owned gap data and the left/right branches used in
Lily L. Liu's opposite-leading-sign compatibility criterion.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace LiuOppositeSigns

def CrossOwnedNotOddGaps (f g : ℝ[X]) : Prop :=
  ∀ a b x : ℝ, a < x → x < b →
    (f.IsRoot a ∨ g.IsRoot a) →
    (f.IsRoot b ∨ g.IsRoot b) →
    (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
    ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
      (g.roots.filter (x < ·)).card) →
    (f.IsRoot a ∧ g.IsRoot b) ∨ (g.IsRoot a ∧ f.IsRoot b)

theorem CrossOwnedNotOddGaps.symm {f g : ℝ[X]} (h : CrossOwnedNotOddGaps f g) :
    CrossOwnedNotOddGaps g f := by
  intro a b x hax hxb ha_root hb_root hgap hnot_odd
  refine (h a b x hax hxb ha_root.symm hb_root.symm
    (fun z haz hzb => (hgap z haz hzb).symm) ?_).symm
  intro hodd
  have hneg := hodd.neg
  rw [neg_sub] at hneg
  exact hnot_odd hneg

/-- The `r_1 >= s_1` branch of Liu Theorem 2.1: delete the largest root of
`f`, then compare the closed-at-or-above root counts of `f / (X - r)` and
`g`. -/
structure LeftRootCountBranch (f g : ℝ[X]) (r s : ℝ) : Prop where
  f_largest : IsLargestRoot f r
  g_largest : IsLargestRoot g s
  largest_ge : s ≤ r
  count : RootCountCompatible (deleteRootFactor f r) g

/-- The `r_1 < s_1` branch of Liu Theorem 2.1: delete the largest root of
`g`, then compare the closed-at-or-above root counts of `f` and
`g / (X - s)`. -/
structure RightRootCountBranch (f g : ℝ[X]) (r s : ℝ) : Prop where
  f_largest : IsLargestRoot f r
  g_largest : IsLargestRoot g s
  largest_lt : r < s
  count : RootCountCompatible f (deleteRootFactor g s)

/-- Swap a left Liu branch for `(g, f)` into the corresponding right branch
for `(f, g)`. The extra strict inequality supplies the strict largest-root
condition required by the right branch. -/
theorem LeftRootCountBranch.toRightBranch_symm_of_lt {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch g f s r) (hlargest : r < s) :
    RightRootCountBranch f g r s where
  f_largest := h.g_largest
  g_largest := h.f_largest
  largest_lt := hlargest
  count := h.count.symm

namespace RightRootCountBranch

/-- Swap a right Liu branch into the corresponding left branch for the swapped
polynomial pair. -/
theorem toLeftBranch_symm {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) :
    LeftRootCountBranch g f s r :=
  ⟨RightRootCountBranch.g_largest h, RightRootCountBranch.f_largest h,
    le_of_lt (RightRootCountBranch.largest_lt h),
    (RightRootCountBranch.count h).symm⟩

end RightRootCountBranch

/-- The root-count branch conclusion in Liu Theorem 2.1, separated from the
larger compatibility/common-interleaver statement. -/
def theorem21RootCountBranches (f g : ℝ[X]) : Prop :=
  ∃ r s, LeftRootCountBranch f g r s ∨ RightRootCountBranch f g r s

theorem theorem21RootCountBranches_of_left {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) :
    theorem21RootCountBranches f g :=
  ⟨r, s, Or.inl h⟩

theorem theorem21RootCountBranches_of_right {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) :
    theorem21RootCountBranches f g :=
  ⟨r, s, Or.inr h⟩

private theorem int_abs_sub_le_two_of_add_one_left {a b c : ℤ}
    (hab : a + 1 = b) (h : |a - c| ≤ 1) :
    |b - c| ≤ 2 := by
  rw [abs_le] at h ⊢
  constructor <;> linarith

private theorem int_abs_sub_le_two_of_add_one_right {a b c : ℤ}
    (hbc : b + 1 = c) (h : |a - b| ≤ 1) :
    |a - c| ≤ 2 := by
  rw [abs_le] at h ⊢
  constructor <;> linarith

private theorem nat_succ_eq_or_eq_succ_or_eq_succ_succ_of_abs_sub_le_one
    {m n k : ℕ} (hk : m + 1 = k)
    (h : |((m : ℤ) - (n : ℤ))| ≤ 1) :
    k = n ∨ k = n + 1 ∨ k = n + 2 := by
  rw [abs_le] at h
  have hk' : (k : ℤ) = (m : ℤ) + 1 := by exact_mod_cast hk.symm
  have hkn_low_int : (n : ℤ) ≤ (k : ℤ) := by linarith
  have hkn_high_int : (k : ℤ) ≤ (n : ℤ) + 2 := by linarith
  have hkn_low : n ≤ k := by exact_mod_cast hkn_low_int
  have hkn_high : k ≤ n + 2 := by exact_mod_cast hkn_high_int
  rcases Nat.exists_eq_add_of_le hkn_low with ⟨d, rfl⟩
  have hd : d ≤ 2 := by linarith
  rcases d with _ | d
  · simp
  rcases d with _ | d
  · simp
  rcases d with _ | d
  · simp
  · exfalso
    linarith

namespace LeftRootCountBranch

/-- If `f` has degree at most two and `g` is linear, the left deletion branch
has Liu-compatible root counts by degree alone. -/
theorem of_largestRoots_natDegree_le_two_right_le_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hlargest : s ≤ r) (hfdeg : f.natDegree ≤ 2)
    (hgdeg : g.natDegree ≤ 1) :
    LeftRootCountBranch f g r s where
  f_largest := hr
  g_largest := hs
  largest_ge := hlargest
  count :=
    rootCountCompatible_deleteRootFactor_left_of_natDegree_le_two_right_le_one
      hf_splits hg_splits hr.isRoot hfdeg hgdeg

/-- If the left endpoint is cubic and deleting its displayed largest root
leaves two roots whose interval overlaps the right two-root interval, then the
left Liu branch has compatible root counts. -/
theorem of_roots_triple_pair_right
    {f g : ℝ[X]} {r s a b c d : ℝ}
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (had : a ≤ d) (hcb : c ≤ b)
    (hfroots : f.roots = {a, b, r})
    (hffac : f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C r)))
    (hgroots : g.roots = {c, d}) (hf_ne : f ≠ 0) :
    LeftRootCountBranch f g r s where
  f_largest := hr
  g_largest := hs
  largest_ge := hlargest
  count := by
    have hdelete_roots : (deleteRootFactor f r).roots = {a, b} :=
      roots_deleteRootFactor_eq_pair_of_roots_triple_right hf_ne hfroots hffac
    exact RootCountCompatible.of_roots_pair_pair had hcb hdelete_roots hgroots

/-- To prove the left Liu deletion branch, it is enough to control the
strict-upper root counts of the deletion pair at common non-root thresholds. -/
theorem of_rootCountAbove_delete_abs_sub_le_one_of_nonRoot
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hbound : ∀ x : ℝ, ¬ (deleteRootFactor f r).IsRoot x → ¬ g.IsRoot x →
      |((((deleteRootFactor f r).roots.filter (x < ·)).card : ℤ) -
          ((g.roots.filter (x < ·)).card : ℤ))| ≤ 1) :
    LeftRootCountBranch f g r s where
  f_largest := hr
  g_largest := hs
  largest_ge := hlargest
  count :=
    RootCountCompatible.of_rootCountAbove_abs_sub_le_one_of_nonRoot
      (hr.deleteRootFactor_ne_zero hf_ne) hg_ne hbound

theorem of_rootCountAbove_left_sub_right_bounds_of_nonRoot
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ∧
        ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≤ 2) :
    LeftRootCountBranch f g r s := by
  refine LeftRootCountBranch.of_rootCountAbove_delete_abs_sub_le_one_of_nonRoot
    hf_ne hg_ne hr hs hlargest ?_
  intro x hdeletex hgx
  by_cases hx : x < r
  · have hfx : ¬ f.IsRoot x :=
      not_isRoot_of_not_deleteRootFactor_isRoot_of_lt hr.isRoot hx hdeletex
    have hwin := hbound x hfx hgx
    have hcount :
        ((f.roots.filter (x < ·)).card : ℤ) =
          ((deleteRootFactor f r).roots.filter (x < ·)).card + 1 := by
      exact_mod_cast hr.rootCountAbove_deleteRootFactor_add_one hf_ne hx
    rw [hcount] at hwin
    rw [abs_le]
    constructor <;> linarith
  · have hx_ge : r ≤ x := le_of_not_gt hx
    have hdelete_zero :=
      hr.rootCountAbove_deleteRootFactor_eq_zero_of_le hf_ne hx_ge
    have hg_zero := hs.rootCountAbove_eq_zero_of_le (hlargest.trans hx_ge)
    rw [hdelete_zero, hg_zero]
    norm_num

/-- A below-largest suffix-count criterion for the left branch.  It is enough
to prove the original strict-upper `f`-minus-`g` root-count bounds at common
non-root thresholds below the largest root of `f`; thresholds at or above that
largest root have zero strict-upper counts for both polynomials. -/
theorem of_rootCountAbove_left_sub_right_bounds_below_largest_of_nonRoot
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hbound : ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ∧
        ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≤ 2) :
    LeftRootCountBranch f g r s := by
  refine LeftRootCountBranch.of_rootCountAbove_left_sub_right_bounds_of_nonRoot
    hf_ne hg_ne hr hs hlargest ?_
  intro x hfx hgx
  by_cases hx : x < r
  · exact hbound x hx hfx hgx
  · have hx_ge : r ≤ x := not_lt.mp hx
    have hf_zero := hr.rootCountAbove_eq_zero_of_le hx_ge
    have hg_zero := hs.rootCountAbove_eq_zero_of_le (hlargest.trans hx_ge)
    rw [hf_zero, hg_zero]
    norm_num

/-- Finite descent for the left Liu branch.  A one-sided root-count upper bound
and parity-guarded cross-ownership in root-free gaps force the least combined
root above a common non-root threshold to carry the exact owner/difference
invariant needed for the left strict-upper count bound. -/
theorem owner_diff_of_crossOwned_consecutive_roots_of_left_sub_le_one
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hupper : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      ∃ c : ℝ, x < c ∧ (f.IsRoot c ∨ g.IsRoot c) ∧
        (∀ z : ℝ, x < z → f.IsRoot z ∨ g.IsRoot z → c ≤ z) ∧
          ((f.IsRoot c ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card = 1) ∨
            (g.IsRoot c ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card = 0)) := by
  let μ : ℝ → ℕ := fun x => ((f.roots + g.roots).filter (x < ·)).card
  let P : ℝ → Prop := fun x =>
    x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      ∃ c : ℝ, x < c ∧ (f.IsRoot c ∨ g.IsRoot c) ∧
        (∀ z : ℝ, x < z → f.IsRoot z ∨ g.IsRoot z → c ≤ z) ∧
          ((f.IsRoot c ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card = 1) ∨
            (g.IsRoot c ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card = 0))
  change ∀ x : ℝ, P x
  refine WellFounded.fix (measure μ).wf ?_
  intro x ih hx hfx hgx
  obtain ⟨c, hcroot, hxc, hleast⟩ :=
    exists_least_isRoot_or_isRoot_gt hf_ne hg_ne (Or.inl hr.isRoot) hx
  have hc_mem : c ∈ f.roots + g.roots :=
    (mem_roots_add_iff_isRoot_or_isRoot hf_ne hg_ne).mpr hcroot
  obtain ⟨b, hcb, hfb, hgb, hgap_f, hgap_g⟩ :=
    exists_common_nonRoot_threshold_no_mem_Ioc hf_ne hg_ne c
  have hxb : x < b := hxc.trans hcb
  have hmeasure : μ b < μ x := by
    dsimp [μ]
    exact card_filter_gt_lt_of_mem_Ioc (f.roots + g.roots)
      (le_of_lt hxb) hc_mem hxc (le_of_lt hcb)
  have hstep_f : ∀ {k : ℤ}, f.IsRoot c →
      ((f.roots.filter (b < ·)).card : ℤ) - (g.roots.filter (b < ·)).card = k →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card =
        k + 1 := by
    intro k hfc hk
    exact card_roots_filter_gt_sub_eq_add_one_of_left_least_root_no_mem_Ioc
      hf_ne hg_ne hxc (le_of_lt hcb) (hdisj c hfc) (hsimple_f c hfc)
      hleast hgap_f hgap_g hk
  refine ⟨c, hxc, hcroot, hleast, ?_⟩
  by_cases hnext : ∃ d : ℝ, b < d ∧ (f.IsRoot d ∨ g.IsRoot d)
  · obtain ⟨d₀, hbd₀, hd₀root⟩ := hnext
    have hd₀_le_r : d₀ ≤ r := by
      rcases hd₀root with hdf | hdg
      · exact hr.roots_le d₀ ((Polynomial.mem_roots hf_ne).mpr hdf)
      · exact (hs.roots_le d₀ ((Polynomial.mem_roots hg_ne).mpr hdg)).trans hlargest
    have hbr : b < r := hbd₀.trans_le hd₀_le_r
    obtain ⟨d, hbd, hdroot, hdleast, howner_d⟩ := ih b hmeasure hbr hfb hgb
    have hbetween :
        ∀ z : ℝ, c < z → z < d → ¬ f.IsRoot z ∧ ¬ g.IsRoot z := by
      intro z hcz hzd
      constructor
      · intro hfz
        have hz_mem : z ∈ f.roots := (Polynomial.mem_roots hf_ne).mpr hfz
        rcases hgap_f z hz_mem with hzc | hbz
        · exact (not_lt_of_ge hzc) hcz
        · exact (not_lt_of_ge (hdleast z hbz (Or.inl hfz))) hzd
      · intro hgz
        have hz_mem : z ∈ g.roots := (Polynomial.mem_roots hg_ne).mpr hgz
        rcases hgap_g z hz_mem with hzc | hbz
        · exact (not_lt_of_ge hzc) hcz
        · exact (not_lt_of_ge (hdleast z hbz (Or.inr hgz))) hzd
    rcases howner_d with ⟨hdf, hdiff_b⟩ | ⟨hdg, hdiff_b⟩
    · rcases hcroot with hfc | hgc
      · have hdiff := hstep_f hfc hdiff_b
        have hle :
            ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ≤ 1 :=
          hupper x hfx hgx
        exact False.elim (by linarith)
      · have hfc_not : ¬ f.IsRoot c := by
          intro hfc
          exact hdisj c hfc hgc
        have hdiff :=
          card_roots_filter_gt_sub_eq_sub_one_of_right_least_root_no_mem_Ioc
            hf_ne hg_ne hxc (le_of_lt hcb) hfc_not (hsimple_g c hgc)
            hleast hgap_f hgap_g hdiff_b
        exact Or.inr ⟨hgc, by simpa using hdiff⟩
    · have hnot_odd_b : ¬ Odd (((f.roots.filter (b < ·)).card : ℤ) -
          (g.roots.filter (b < ·)).card) := by
        simp [hdiff_b]
      have hcross_cd := hcross c d b hcb hbd hcroot hdroot hbetween hnot_odd_b
      have hfc : f.IsRoot c := by
        rcases hcross_cd with ⟨hfc, _hgd⟩ | ⟨_hgc, hfd⟩
        · exact hfc
        · exact False.elim (hdisj d hfd hdg)
      have hdiff := hstep_f hfc hdiff_b
      exact Or.inl ⟨hfc, by simpa using hdiff⟩
  · have hno_above :
        ∀ z : ℝ, b < z → ¬ f.IsRoot z ∧ ¬ g.IsRoot z := by
      intro z hbz
      constructor
      · intro hfz
        exact hnext ⟨z, hbz, Or.inl hfz⟩
      · intro hgz
        exact hnext ⟨z, hbz, Or.inr hgz⟩
    have hdiff_b :=
      card_roots_filter_gt_sub_eq_zero_of_no_isRoot_or_isRoot_gt
        hf_ne hg_ne hno_above
    have hcr : c ≤ r := hleast r hx (Or.inl hr.isRoot)
    have hrc : r ≤ c := by
      by_contra hnot
      have hcr_lt : c < r := lt_of_not_ge hnot
      by_cases hrb : r ≤ b
      · have hr_mem : r ∈ f.roots := (Polynomial.mem_roots hf_ne).mpr hr.isRoot
        rcases hgap_f r hr_mem with hle | hlt <;> linarith
      · exact False.elim (hnext ⟨r, lt_of_not_ge hrb, Or.inl hr.isRoot⟩)
    have hcr_eq : c = r := le_antisymm hcr hrc
    have hfc : f.IsRoot c := by simpa [hcr_eq] using hr.isRoot
    have hdiff := hstep_f hfc hdiff_b
    exact Or.inl ⟨hfc, hdiff⟩

/-- Compatible root counts supply the one-sided upper bound used by the finite
descent. -/
theorem rootCountAbove_owner_diff_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hcount : RootCountCompatible f g)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      ∃ c : ℝ, x < c ∧ (f.IsRoot c ∨ g.IsRoot c) ∧
        (∀ z : ℝ, x < z → f.IsRoot z ∨ g.IsRoot z → c ≤ z) ∧
          ((f.IsRoot c ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card = 1) ∨
            (g.IsRoot c ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card = 0)) :=
  owner_diff_of_crossOwned_consecutive_roots_of_left_sub_le_one
    hf_ne hg_ne hr hs hlargest
    (fun _ hfx hgx => hcount.rootCountAbove_left_sub_le_one_of_nonRoot
      hf_ne hg_ne hfx hgx)
    hsimple_f hsimple_g hdisj hcross

/-- Finite descent for the left Liu branch with the root-count window that
appears in Theorem 2.1.  In the `r_1 >= s_1` orientation, cross-owned finite
gaps force the original strict-upper difference to stay in `[0, 2]`; the
owner of the least root above the threshold gives the sharper local alternative
used in the induction. -/
theorem owner_diff_bounds_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      ∃ c : ℝ, x < c ∧ (f.IsRoot c ∨ g.IsRoot c) ∧
        (∀ z : ℝ, x < z → f.IsRoot z ∨ g.IsRoot z → c ≤ z) ∧
          ((f.IsRoot c ∧
              1 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ≤ 2) ∨
            (g.IsRoot c ∧
              0 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ≤ 1)) := by
  let μ : ℝ → ℕ := fun x => ((f.roots + g.roots).filter (x < ·)).card
  let P : ℝ → Prop := fun x =>
    x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      ∃ c : ℝ, x < c ∧ (f.IsRoot c ∨ g.IsRoot c) ∧
        (∀ z : ℝ, x < z → f.IsRoot z ∨ g.IsRoot z → c ≤ z) ∧
          ((f.IsRoot c ∧
              1 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ≤ 2) ∨
            (g.IsRoot c ∧
              0 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ∧
              ((f.roots.filter (x < ·)).card : ℤ) -
                (g.roots.filter (x < ·)).card ≤ 1))
  change ∀ x : ℝ, P x
  refine WellFounded.fix (measure μ).wf ?_
  intro x ih hx hfx hgx
  obtain ⟨c, hcroot, hxc, hleast⟩ :=
    exists_least_isRoot_or_isRoot_gt hf_ne hg_ne (Or.inl hr.isRoot) hx
  have hc_mem : c ∈ f.roots + g.roots :=
    (mem_roots_add_iff_isRoot_or_isRoot hf_ne hg_ne).mpr hcroot
  obtain ⟨b, hcb, hfb, hgb, hgap_f, hgap_g⟩ :=
    exists_common_nonRoot_threshold_no_mem_Ioc hf_ne hg_ne c
  have hxb : x < b := hxc.trans hcb
  have hmeasure : μ b < μ x := by
    dsimp [μ]
    exact card_filter_gt_lt_of_mem_Ioc (f.roots + g.roots)
      (le_of_lt hxb) hc_mem hxc (le_of_lt hcb)
  have hstep_f : f.IsRoot c →
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card =
        ((f.roots.filter (b < ·)).card : ℤ) -
          (g.roots.filter (b < ·)).card + 1 := by
    intro hfc
    exact card_roots_filter_gt_sub_eq_add_one_of_left_least_root_no_mem_Ioc
      hf_ne hg_ne hxc (le_of_lt hcb) (hdisj c hfc) (hsimple_f c hfc)
      hleast hgap_f hgap_g rfl
  have hstep_g : g.IsRoot c →
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card =
        ((f.roots.filter (b < ·)).card : ℤ) -
          (g.roots.filter (b < ·)).card - 1 := by
    intro hgc
    have hfc_not : ¬ f.IsRoot c := by
      intro hfc
      exact hdisj c hfc hgc
    exact card_roots_filter_gt_sub_eq_sub_one_of_right_least_root_no_mem_Ioc
      hf_ne hg_ne hxc (le_of_lt hcb) hfc_not (hsimple_g c hgc)
      hleast hgap_f hgap_g rfl
  refine ⟨c, hxc, hcroot, hleast, ?_⟩
  by_cases hnext : ∃ d : ℝ, b < d ∧ (f.IsRoot d ∨ g.IsRoot d)
  · have hbr : b < r := by
      obtain ⟨d₀, hbd₀, hd₀root⟩ := hnext
      have hd₀_le_r : d₀ ≤ r := by
        rcases hd₀root with hdf | hdg
        · exact hr.roots_le d₀ ((Polynomial.mem_roots hf_ne).mpr hdf)
        · exact (hs.roots_le d₀ ((Polynomial.mem_roots hg_ne).mpr hdg)).trans hlargest
      exact hbd₀.trans_le hd₀_le_r
    obtain ⟨d, hbd, hdroot, hdleast, howner_d⟩ := ih b hmeasure hbr hfb hgb
    have hbetween :
        ∀ z : ℝ, c < z → z < d → ¬ f.IsRoot z ∧ ¬ g.IsRoot z := by
      intro z hcz hzd
      constructor
      · intro hfz
        have hz_mem : z ∈ f.roots := (Polynomial.mem_roots hf_ne).mpr hfz
        rcases hgap_f z hz_mem with hzc | hbz
        · exact (not_lt_of_ge hzc) hcz
        · exact (not_lt_of_ge (hdleast z hbz (Or.inl hfz))) hzd
      · intro hgz
        have hz_mem : z ∈ g.roots := (Polynomial.mem_roots hg_ne).mpr hgz
        rcases hgap_g z hz_mem with hzc | hbz
        · exact (not_lt_of_ge hzc) hcz
        · exact (not_lt_of_ge (hdleast z hbz (Or.inr hgz))) hzd
    rcases howner_d with ⟨hdf, hdiff_b_low, hdiff_b_high⟩ |
        ⟨hdg, hdiff_b_low, hdiff_b_high⟩
    · rcases hcroot with hfc | hgc
      · have hdiff_b_ne_two :
            ((f.roots.filter (b < ·)).card : ℤ) -
                (g.roots.filter (b < ·)).card ≠ 2 := by
          intro hdiff_b_eq
          have hnot_odd_b : ¬ Odd (((f.roots.filter (b < ·)).card : ℤ) -
              (g.roots.filter (b < ·)).card) := by
            simp [hdiff_b_eq]
          have hcross_cd :=
            hcross c d b hcb hbd (Or.inl hfc) hdroot hbetween hnot_odd_b
          rcases hcross_cd with ⟨_hfc, hgd⟩ | ⟨hgc, _hfd⟩
          · exact hdisj d hdf hgd
          · exact hdisj c hfc hgc
        have hdiff_b_lt_two :
            ((f.roots.filter (b < ·)).card : ℤ) -
                (g.roots.filter (b < ·)).card < 2 :=
          lt_of_le_of_ne hdiff_b_high hdiff_b_ne_two
        have hdiff := hstep_f hfc
        exact Or.inl ⟨hfc, by linarith, by linarith⟩
      · have hdiff := hstep_g hgc
        exact Or.inr ⟨hgc, by linarith, by linarith⟩
    · rcases hcroot with hfc | hgc
      · have hdiff := hstep_f hfc
        exact Or.inl ⟨hfc, by linarith, by linarith⟩
      · have hdiff_b_ne_zero :
            ((f.roots.filter (b < ·)).card : ℤ) -
                (g.roots.filter (b < ·)).card ≠ 0 := by
          intro hdiff_b_eq
          have hnot_odd_b : ¬ Odd (((f.roots.filter (b < ·)).card : ℤ) -
              (g.roots.filter (b < ·)).card) := by
            simp [hdiff_b_eq]
          have hcross_cd :=
            hcross c d b hcb hbd (Or.inr hgc) hdroot hbetween hnot_odd_b
          rcases hcross_cd with ⟨hfc, _hgd⟩ | ⟨_hgc, hfd⟩
          · exact hdisj c hfc hgc
          · exact hdisj d hfd hdg
        have hdiff_b_pos :
            0 < ((f.roots.filter (b < ·)).card : ℤ) -
                (g.roots.filter (b < ·)).card :=
          lt_of_le_of_ne hdiff_b_low (Ne.symm hdiff_b_ne_zero)
        have hdiff := hstep_g hgc
        exact Or.inr ⟨hgc, by linarith, by linarith⟩
  · have hno_above :
        ∀ z : ℝ, b < z → ¬ f.IsRoot z ∧ ¬ g.IsRoot z := by
      intro z hbz
      constructor
      · intro hfz
        exact hnext ⟨z, hbz, Or.inl hfz⟩
      · intro hgz
        exact hnext ⟨z, hbz, Or.inr hgz⟩
    have hdiff_b :=
      card_roots_filter_gt_sub_eq_zero_of_no_isRoot_or_isRoot_gt
        hf_ne hg_ne hno_above
    have hcr : c ≤ r := hleast r hx (Or.inl hr.isRoot)
    have hrc : r ≤ c := by
      by_contra hnot
      have hcr_lt : c < r := lt_of_not_ge hnot
      by_cases hrb : r ≤ b
      · have hr_mem : r ∈ f.roots := (Polynomial.mem_roots hf_ne).mpr hr.isRoot
        rcases hgap_f r hr_mem with hle | hlt <;> linarith
      · exact False.elim (hnext ⟨r, lt_of_not_ge hrb, Or.inl hr.isRoot⟩)
    have hcr_eq : c = r := le_antisymm hcr hrc
    have hfc : f.IsRoot c := by simpa [hcr_eq] using hr.isRoot
    have hdiff := hstep_f hfc
    exact Or.inl ⟨hfc, by linarith, by linarith⟩

theorem rootCountAbove_bounds_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ∧
        ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≤ 2 := by
  intro x hx hfx hgx
  obtain ⟨_c, _hxc, _hcroot, _hleast, howner⟩ :=
    owner_diff_bounds_of_crossOwned_consecutive_roots
      hf_ne hg_ne hr hs hlargest hsimple_f hsimple_g hdisj hcross
      x hx hfx hgx
  rcases howner with ⟨_hfc, hlow, hhigh⟩ | ⟨_hgc, hlow, hhigh⟩
  · exact ⟨by linarith, hhigh⟩
  · exact ⟨hlow, by linarith⟩

theorem of_crossOwned_consecutive_roots
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    LeftRootCountBranch f g r s :=
  LeftRootCountBranch.of_rootCountAbove_left_sub_right_bounds_below_largest_of_nonRoot
    hf_ne hg_ne hr hs hlargest
    (rootCountAbove_bounds_of_crossOwned_consecutive_roots
      hf_ne hg_ne hr hs hlargest hsimple_f hsimple_g hdisj hcross)

theorem right_le_left_of_crossOwned_consecutive_roots_of_left_sub_le_one
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hupper : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      (g.roots.filter (x < ·)).card ≤ (f.roots.filter (x < ·)).card := by
  intro x hx hfx hgx
  obtain ⟨_c, _hxc, _hcroot, _hleast, howner⟩ :=
    owner_diff_of_crossOwned_consecutive_roots_of_left_sub_le_one
      hf_ne hg_ne hr hs hlargest hupper hsimple_f hsimple_g hdisj hcross
      x hx hfx hgx
  have hle_int :
      ((g.roots.filter (x < ·)).card : ℤ) ≤
        (f.roots.filter (x < ·)).card := by
    rcases howner with ⟨_hfc, hdiff⟩ | ⟨_hgc, hdiff⟩ <;> linarith
  exact_mod_cast hle_int

theorem rootCountAbove_right_le_left_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hcount : RootCountCompatible f g)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      (g.roots.filter (x < ·)).card ≤ (f.roots.filter (x < ·)).card :=
  right_le_left_of_crossOwned_consecutive_roots_of_left_sub_le_one
    hf_ne hg_ne hr hs hlargest
    (fun _ hfx hgx => hcount.rootCountAbove_left_sub_le_one_of_nonRoot
      hf_ne hg_ne hfx hgx)
    hsimple_f hsimple_g hdisj hcross

theorem of_left_sub_right_upper_of_right_le_left
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hupper : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 2)
    (hle : ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      (g.roots.filter (x < ·)).card ≤ (f.roots.filter (x < ·)).card) :
    LeftRootCountBranch f g r s := by
  refine
    LeftRootCountBranch.of_rootCountAbove_left_sub_right_bounds_below_largest_of_nonRoot
      hf_ne hg_ne hr hs hlargest ?_
  intro x hx hfx hgx
  constructor
  · have hxle :
        ((g.roots.filter (x < ·)).card : ℤ) ≤
          (f.roots.filter (x < ·)).card := by
      exact_mod_cast hle x hx hfx hgx
    linarith
  · exact hupper x hfx hgx

private theorem of_left_sub_right_le_one_of_right_le_left
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hupper : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1)
    (hle : ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      (g.roots.filter (x < ·)).card ≤ (f.roots.filter (x < ·)).card) :
    LeftRootCountBranch f g r s :=
  of_left_sub_right_upper_of_right_le_left hf_ne hg_ne hr hs hlargest
    (fun x hfx hgx => by
      have hle_one := hupper x hfx hgx
      linarith)
    hle

theorem of_rootCountCompatible_of_rootCountAbove_right_le_left
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : s ≤ r)
    (hcount : RootCountCompatible f g)
    (hle : ∀ x : ℝ, x < r → ¬ f.IsRoot x → ¬ g.IsRoot x →
      (g.roots.filter (x < ·)).card ≤ (f.roots.filter (x < ·)).card) :
    LeftRootCountBranch f g r s :=
  of_left_sub_right_le_one_of_right_le_left hf_ne hg_ne hr hs hlargest
    (fun _ hfx hgx => hcount.rootCountAbove_left_sub_le_one_of_nonRoot
      hf_ne hg_ne hfx hgx)
    hle

theorem delete_splits {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_splits : f.Splits) :
    (deleteRootFactor f r).Splits :=
  h.f_largest.deleteRootFactor_splits hf_splits

theorem delete_ne_zero {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    deleteRootFactor f r ≠ 0 :=
  h.f_largest.deleteRootFactor_ne_zero hf_ne

theorem delete_ne_zero_and_splits {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hf_splits : f.Splits) :
    deleteRootFactor f r ≠ 0 ∧ (deleteRootFactor f r).Splits :=
  h.f_largest.deleteRootFactor_ne_zero_and_splits hf_ne hf_splits

theorem delete_oppositeLeadingSigns {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g) :
    OppositeLeadingSigns (deleteRootFactor f r) g :=
  hsgn.deleteRootFactor_left h.f_largest.isRoot

theorem positiveDeletionCount {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g) :
    (HasPosLeadingCoeff (deleteRootFactor f r) ∧ HasPosLeadingCoeff (-g) ∧
        RootCountCompatible (deleteRootFactor f r) (-g)) ∨
      (HasPosLeadingCoeff (-(deleteRootFactor f r)) ∧ HasPosLeadingCoeff g ∧
        RootCountCompatible (-(deleteRootFactor f r)) g) := by
  rcases (h.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · exact Or.inl ⟨hpos.1, hpos.2, h.count.neg_right⟩
  · exact Or.inr ⟨hpos.1, hpos.2, h.count.neg_left⟩

theorem positiveSplitDeletionCount {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    PositiveSplitRootCountPair (deleteRootFactor f r) (-g) ∨
      PositiveSplitRootCountPair (-(deleteRootFactor f r)) g := by
  rcases h.positiveDeletionCount hsgn with hpos | hpos
  · exact Or.inl
      ⟨hpos.1, hpos.2.1, h.delete_splits hf_splits, hg_splits.neg, hpos.2.2⟩
  · exact Or.inr
      ⟨hpos.1, hpos.2.1, (h.delete_splits hf_splits).neg, hg_splits, hpos.2.2⟩

theorem rootCountAbove_delete_abs_sub_le_one_of_nonRoot
    {f g : ℝ[X]} {r s x : ℝ} (h : LeftRootCountBranch f g r s)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hfx : ¬ (deleteRootFactor f r).IsRoot x) (hgx : ¬ g.IsRoot x) :
    |((((deleteRootFactor f r).roots.filter (x < ·)).card : ℤ) -
        ((g.roots.filter (x < ·)).card : ℤ))| ≤ 1 :=
  h.count.rootCountAbove_abs_sub_le_one_of_nonRoot
    (h.delete_ne_zero hf_ne) hg_ne hfx hgx

theorem rootCountAbove_delete_bounds_of_nonRoot
    {f g : ℝ[X]} {r s x : ℝ} (h : LeftRootCountBranch f g r s)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hfx : ¬ (deleteRootFactor f r).IsRoot x) (hgx : ¬ g.IsRoot x) :
    (((deleteRootFactor f r).roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        ((deleteRootFactor f r).roots.filter (x < ·)).card ≤ 1 :=
  h.count.rootCountAbove_bounds_of_nonRoot
    (h.delete_ne_zero hf_ne) hg_ne hfx hgx

theorem rootCountAtOrAbove_delete_add_one {f g : ℝ[X]} {r s x : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) (hx : x ≤ r) :
    rootCountAtOrAbove f x =
      rootCountAtOrAbove (deleteRootFactor f r) x + 1 :=
  h.f_largest.rootCountAtOrAbove_deleteRootFactor_add_one hf_ne hx

theorem rootCountAtOrAbove_abs_sub_le_two {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    ∀ x : ℝ,
      |((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ))| ≤ 2 := by
  intro x
  by_cases hx : x ≤ r
  · have hdelete := h.rootCountAtOrAbove_delete_add_one hf_ne hx
    have hdelete_int :
        ((rootCountAtOrAbove (deleteRootFactor f r) x : ℤ) + 1 =
          (rootCountAtOrAbove f x : ℤ)) := by
      exact_mod_cast hdelete.symm
    exact int_abs_sub_le_two_of_add_one_left hdelete_int (h.count x)
  · have hx_lt : r < x := lt_of_not_ge hx
    have hf_zero := h.f_largest.rootCountAtOrAbove_eq_zero_of_lt hx_lt
    have hdelete_zero :=
      h.f_largest.rootCountAtOrAbove_deleteRootFactor_eq_zero_of_lt hf_ne hx_lt
    have hgap := h.count x
    rw [hdelete_zero] at hgap
    rw [hf_zero]
    exact le_trans hgap (by norm_num)

theorem rootCountAtOrAbove_right_sub_left_le_one {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    ∀ x : ℝ,
      ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 1 := by
  intro x
  by_cases hx : x ≤ r
  · have hdelete := h.rootCountAtOrAbove_delete_add_one hf_ne hx
    have hdelete_int :
        (rootCountAtOrAbove f x : ℤ) =
          (rootCountAtOrAbove (deleteRootFactor f r) x : ℤ) + 1 := by
      exact_mod_cast hdelete
    have hgap := h.count.right_sub_le_one x
    rw [hdelete_int]
    linarith
  · have hx_lt : r < x := lt_of_not_ge hx
    have hf_zero := h.f_largest.rootCountAtOrAbove_eq_zero_of_lt hx_lt
    have hdelete_zero :=
      h.f_largest.rootCountAtOrAbove_deleteRootFactor_eq_zero_of_lt hf_ne hx_lt
    simpa [hf_zero, hdelete_zero] using h.count.right_sub_le_one x

theorem rootCountAtOrAbove_bounds {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    ∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 2 ∧
        ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 1 := by
  intro x
  have h_abs := h.rootCountAtOrAbove_abs_sub_le_two hf_ne x
  rw [abs_le] at h_abs
  exact ⟨h_abs.2, h.rootCountAtOrAbove_right_sub_left_le_one hf_ne x⟩

theorem root_delete_le {f g : ℝ[X]} {r s t : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (ht : (deleteRootFactor f r).IsRoot t) :
    t ≤ r :=
  h.f_largest.root_deleteRootFactor_le hf_ne ht

theorem delete_roots_le_largest {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    ∀ t ∈ (deleteRootFactor f r).roots, t ≤ r := by
  intro t ht
  exact h.root_delete_le hf_ne
    ((Polynomial.mem_roots (h.delete_ne_zero hf_ne)).mp ht)

theorem right_roots_le_left_largest {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) :
    ∀ t ∈ g.roots, t ≤ r := by
  intro t ht
  exact (h.g_largest.roots_le t ht).trans h.largest_ge

theorem deletionPair_roots_le_left_largest {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    (∀ t ∈ (deleteRootFactor f r).roots, t ≤ r) ∧
      ∀ t ∈ g.roots, t ≤ r :=
  ⟨h.delete_roots_le_largest hf_ne, h.right_roots_le_left_largest⟩

theorem left_comp_X_add_C_eq_X_mul_deleteRootFactor_comp
    {f g : ℝ[X]} {r s : ℝ} (h : LeftRootCountBranch f g r s) :
    f.comp (X + C r) =
      X * (deleteRootFactor f r).comp (X + C r) :=
  h.f_largest.comp_X_add_C_eq_X_mul_deleteRootFactor_comp

theorem delete_natDegree_add_one_eq {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0) :
    (deleteRootFactor f r).natDegree + 1 = f.natDegree := by
  have hf_degree_pos : 0 < f.natDegree :=
    h.f_largest.natDegree_pos hf_ne
  rw [natDegree_deleteRootFactor]
  simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hf_degree_pos

theorem delete_natDegree_add_one_eq_of_sameDegree {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree) :
    (deleteRootFactor f r).natDegree + 1 = g.natDegree :=
  (h.delete_natDegree_add_one_eq hf_ne).trans hdeg

theorem delete_natDegree_eq_of_succDegree {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree + 1) :
    (deleteRootFactor f r).natDegree = g.natDegree := by
  have hdelete_succ := h.delete_natDegree_add_one_eq hf_ne
  lia

theorem delete_natDegree_eq_succ_of_twoDegree {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree + 2) :
    (deleteRootFactor f r).natDegree = g.natDegree + 1 := by
  have hdelete_succ := h.delete_natDegree_add_one_eq hf_ne
  lia

theorem commonInterleaver_natDegree_eq_of_sameDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : Prec (deleteRootFactor f r) k ∧ Prec g k) :
    k.natDegree = g.natDegree := by
  have hdelete_succ :=
    h.delete_natDegree_add_one_eq_of_sameDegree hf_ne hdeg
  have hupper := hcommon.1.natDegree_le_succ
  have hlower := hcommon.2.natDegree_le
  lia

theorem commonInterleaver_natDegree_eq_or_eq_succ_of_succDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : Prec (deleteRootFactor f r) k ∧ Prec g k) :
    k.natDegree = g.natDegree ∨ k.natDegree = g.natDegree + 1 := by
  have hdelete := h.delete_natDegree_eq_of_succDegree hf_ne hdeg
  have hupper := hcommon.1.natDegree_le_succ
  have hlower := hcommon.2.natDegree_le
  by_cases hk : k.natDegree = g.natDegree
  · exact Or.inl hk
  · right
    lia

theorem commonInterleaver_natDegree_eq_delete_of_twoDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : Prec (deleteRootFactor f r) k ∧ Prec g k) :
    k.natDegree = (deleteRootFactor f r).natDegree := by
  have hdelete := h.delete_natDegree_eq_succ_of_twoDegree hf_ne hdeg
  have hlower := hcommon.1.natDegree_le
  have hupper := hcommon.2.natDegree_le_succ
  lia

theorem commonInterleaver_natDegree_eq_succ_of_twoDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : Prec (deleteRootFactor f r) k ∧ Prec g k) :
    k.natDegree = g.natDegree + 1 := by
  rw [h.commonInterleaver_natDegree_eq_delete_of_twoDegree hf_ne hdeg hcommon]
  exact h.delete_natDegree_eq_succ_of_twoDegree hf_ne hdeg

theorem natDegree_abs_sub_le_two {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 := by
  have hgap := h.count.natDegree_abs_sub_le_one (h.delete_splits hf_splits)
    hg_splits
  have hdelete_succ := h.delete_natDegree_add_one_eq hf_ne
  have hdelete_int :
      ((deleteRootFactor f r).natDegree : ℤ) + 1 = (f.natDegree : ℤ) := by
    exact_mod_cast hdelete_succ
  exact int_abs_sub_le_two_of_add_one_left hdelete_int hgap

/-- In the left Liu branch, restoring the deleted root of `f` leaves only the
same-degree, right-succ-degree, or right-plus-two-degree alternatives. -/
theorem natDegree_eq_or_eq_succ_or_eq_succ_succ {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hf_ne : f ≠ 0)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    f.natDegree = g.natDegree ∨
      f.natDegree = g.natDegree + 1 ∨
        f.natDegree = g.natDegree + 2 := by
  have hgap := h.count.natDegree_abs_sub_le_one (h.delete_splits hf_splits)
    hg_splits
  have hdelete_succ := h.delete_natDegree_add_one_eq hf_ne
  exact nat_succ_eq_or_eq_succ_or_eq_succ_succ_of_abs_sub_le_one
    hdelete_succ hgap

end LeftRootCountBranch

namespace RightRootCountBranch

/-- If `f` is linear and `g` has degree at most two, the right deletion branch
has Liu-compatible root counts by degree alone. -/
theorem of_largestRoots_left_le_one_right_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hlargest : r < s) (hfdeg : f.natDegree ≤ 1)
    (hgdeg : g.natDegree ≤ 2) :
    RightRootCountBranch f g r s :=
  (LeftRootCountBranch.of_largestRoots_natDegree_le_two_right_le_one
    hg_splits hf_splits hs hr hlargest.le hgdeg hfdeg).toRightBranch_symm_of_lt hlargest

/-- If the right endpoint is cubic and deleting its displayed largest root
leaves two roots whose interval overlaps the left two-root interval, then the
right Liu branch has compatible root counts. -/
theorem of_roots_pair_triple_right
    {f g : ℝ[X]} {r s a b c d : ℝ}
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : r < s)
    (had : a ≤ d) (hcb : c ≤ b)
    (hfroots : f.roots = {a, b}) (hgroots : g.roots = {c, d, s})
    (hgfac : g = C g.leadingCoeff * ((X - C c) * (X - C d) * (X - C s)))
    (hg_ne : g ≠ 0) :
    RightRootCountBranch f g r s :=
  (LeftRootCountBranch.of_roots_triple_pair_right hs hr hlargest.le hcb had
    hgroots hgfac hfroots hg_ne).toRightBranch_symm_of_lt hlargest

theorem delete_splits {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_splits : g.Splits) :
    (deleteRootFactor g s).Splits :=
  h.toLeftBranch_symm.delete_splits hg_splits

theorem delete_ne_zero {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    deleteRootFactor g s ≠ 0 :=
  h.toLeftBranch_symm.delete_ne_zero hg_ne

theorem delete_ne_zero_and_splits {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hg_splits : g.Splits) :
    deleteRootFactor g s ≠ 0 ∧ (deleteRootFactor g s).Splits :=
  h.toLeftBranch_symm.delete_ne_zero_and_splits hg_ne hg_splits

theorem delete_oppositeLeadingSigns {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g) :
    OppositeLeadingSigns f (deleteRootFactor g s) :=
  (h.toLeftBranch_symm.delete_oppositeLeadingSigns hsgn.symm).symm

theorem positiveDeletionCount {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g) :
    (HasPosLeadingCoeff f ∧ HasPosLeadingCoeff (-(deleteRootFactor g s)) ∧
        RootCountCompatible f (-(deleteRootFactor g s))) ∨
      (HasPosLeadingCoeff (-f) ∧ HasPosLeadingCoeff (deleteRootFactor g s) ∧
        RootCountCompatible (-f) (deleteRootFactor g s)) := by
  rcases h.toLeftBranch_symm.positiveDeletionCount hsgn.symm with hpos | hpos
  · exact Or.inr ⟨hpos.2.1, hpos.1, hpos.2.2.symm⟩
  · exact Or.inl ⟨hpos.2.1, hpos.1, hpos.2.2.symm⟩

theorem positiveSplitDeletionCount {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    PositiveSplitRootCountPair f (-(deleteRootFactor g s)) ∨
      PositiveSplitRootCountPair (-f) (deleteRootFactor g s) := by
  rcases h.toLeftBranch_symm.positiveSplitDeletionCount hsgn.symm
    hg_splits hf_splits with hpair | hpair
  · exact Or.inr hpair.symm
  · exact Or.inl hpair.symm

theorem rootCountAbove_delete_abs_sub_le_one_of_nonRoot
    {f g : ℝ[X]} {r s x : ℝ} (h : RightRootCountBranch f g r s)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hfx : ¬ f.IsRoot x) (hgx : ¬ (deleteRootFactor g s).IsRoot x) :
    |(((f.roots.filter (x < ·)).card : ℤ) -
        (((deleteRootFactor g s).roots.filter (x < ·)).card : ℤ))| ≤ 1 := by
    simpa [abs_sub_comm] using
      h.toLeftBranch_symm.rootCountAbove_delete_abs_sub_le_one_of_nonRoot
        hg_ne hf_ne hgx hfx

theorem rootCountAbove_delete_bounds_of_nonRoot
    {f g : ℝ[X]} {r s x : ℝ} (h : RightRootCountBranch f g r s)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hfx : ¬ f.IsRoot x) (hgx : ¬ (deleteRootFactor g s).IsRoot x) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        ((deleteRootFactor g s).roots.filter (x < ·)).card ≤ 1 ∧
      (((deleteRootFactor g s).roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 := by
  exact (h.toLeftBranch_symm.rootCountAbove_delete_bounds_of_nonRoot
    hg_ne hf_ne hgx hfx).symm

/-- To prove the right Liu deletion branch, it is enough to control the
strict-upper root counts of the deletion pair at common non-root thresholds. -/
theorem of_rootCountAbove_delete_abs_sub_le_one_of_nonRoot
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : r < s)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ (deleteRootFactor g s).IsRoot x →
      |(((f.roots.filter (x < ·)).card : ℤ) -
          (((deleteRootFactor g s).roots.filter (x < ·)).card : ℤ))| ≤ 1) :
    RightRootCountBranch f g r s := by
  apply (LeftRootCountBranch.of_rootCountAbove_delete_abs_sub_le_one_of_nonRoot
    hg_ne hf_ne hs hr hlargest.le ?_).toRightBranch_symm_of_lt hlargest
  intro x hgx hfx
  simpa [abs_sub_comm] using hbound x hfx hgx

theorem of_rootCountAbove_right_sub_left_bounds_of_nonRoot
    {f g : ℝ[X]} {r s : ℝ} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hlargest : r < s)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 ≤ ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ∧
        ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≤ 2) :
    RightRootCountBranch f g r s := by
  have hleft : LeftRootCountBranch g f s r :=
    LeftRootCountBranch.of_rootCountAbove_left_sub_right_bounds_of_nonRoot
      hg_ne hf_ne hs hr hlargest.le fun x hgx hfx => hbound x hfx hgx
  exact hleft.toRightBranch_symm_of_lt hlargest

theorem rootCountAtOrAbove_delete_add_one {f g : ℝ[X]} {r s x : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) (hx : x ≤ s) :
    rootCountAtOrAbove g x =
      rootCountAtOrAbove (deleteRootFactor g s) x + 1 :=
  h.toLeftBranch_symm.rootCountAtOrAbove_delete_add_one hg_ne hx

theorem rootCountAtOrAbove_abs_sub_le_two {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    ∀ x : ℝ,
      |((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ))| ≤ 2 := by
  intro x
  simpa [abs_sub_comm] using
    h.toLeftBranch_symm.rootCountAtOrAbove_abs_sub_le_two hg_ne x

theorem rootCountAtOrAbove_left_sub_right_le_one {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    ∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 1 :=
  h.toLeftBranch_symm.rootCountAtOrAbove_right_sub_left_le_one hg_ne

theorem rootCountAtOrAbove_bounds {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    ∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 1 ∧
        ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 2 := by
  intro x
  have hbounds := h.toLeftBranch_symm.rootCountAtOrAbove_bounds hg_ne x
  exact ⟨hbounds.2, hbounds.1⟩

theorem root_delete_le {f g : ℝ[X]} {r s t : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (ht : (deleteRootFactor g s).IsRoot t) :
    t ≤ s :=
  h.toLeftBranch_symm.root_delete_le hg_ne ht

theorem left_roots_le_right_largest {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) :
    ∀ t ∈ f.roots, t ≤ s :=
  h.toLeftBranch_symm.right_roots_le_left_largest

theorem delete_roots_le_largest {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    ∀ t ∈ (deleteRootFactor g s).roots, t ≤ s :=
  h.toLeftBranch_symm.delete_roots_le_largest hg_ne

theorem deletionPair_roots_le_right_largest {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    (∀ t ∈ f.roots, t ≤ s) ∧
      ∀ t ∈ (deleteRootFactor g s).roots, t ≤ s :=
  h.toLeftBranch_symm.deletionPair_roots_le_left_largest hg_ne |>.symm

theorem right_comp_X_add_C_eq_X_mul_deleteRootFactor_comp
    {f g : ℝ[X]} {r s : ℝ} (h : RightRootCountBranch f g r s) :
    g.comp (X + C s) =
      X * (deleteRootFactor g s).comp (X + C s) :=
  h.toLeftBranch_symm.left_comp_X_add_C_eq_X_mul_deleteRootFactor_comp

theorem delete_natDegree_add_one_eq {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0) :
    (deleteRootFactor g s).natDegree + 1 = g.natDegree :=
  h.toLeftBranch_symm.delete_natDegree_add_one_eq hg_ne

theorem delete_natDegree_add_one_eq_of_sameDegree {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree) :
    (deleteRootFactor g s).natDegree + 1 = f.natDegree :=
  h.toLeftBranch_symm.delete_natDegree_add_one_eq_of_sameDegree hg_ne hdeg

theorem delete_natDegree_eq_of_succDegree {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree + 1) :
    (deleteRootFactor g s).natDegree = f.natDegree :=
  h.toLeftBranch_symm.delete_natDegree_eq_of_succDegree hg_ne hdeg

theorem delete_natDegree_eq_succ_of_twoDegree {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree + 2) :
    (deleteRootFactor g s).natDegree = f.natDegree + 1 :=
  h.toLeftBranch_symm.delete_natDegree_eq_succ_of_twoDegree hg_ne hdeg

theorem commonInterleaver_natDegree_eq_of_sameDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : Prec f k ∧ Prec (deleteRootFactor g s) k) :
    k.natDegree = f.natDegree :=
  h.toLeftBranch_symm.commonInterleaver_natDegree_eq_of_sameDegree
    hg_ne hdeg hcommon.symm

theorem commonInterleaver_natDegree_eq_or_eq_succ_of_succDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : Prec f k ∧ Prec (deleteRootFactor g s) k) :
    k.natDegree = f.natDegree ∨ k.natDegree = f.natDegree + 1 :=
  h.toLeftBranch_symm.commonInterleaver_natDegree_eq_or_eq_succ_of_succDegree
    hg_ne hdeg hcommon.symm

theorem commonInterleaver_natDegree_eq_delete_of_twoDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : Prec f k ∧ Prec (deleteRootFactor g s) k) :
    k.natDegree = (deleteRootFactor g s).natDegree :=
  h.toLeftBranch_symm.commonInterleaver_natDegree_eq_delete_of_twoDegree
    hg_ne hdeg hcommon.symm

theorem commonInterleaver_natDegree_eq_succ_of_twoDegree
    {f g k : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : Prec f k ∧ Prec (deleteRootFactor g s) k) :
    k.natDegree = f.natDegree + 1 :=
  h.toLeftBranch_symm.commonInterleaver_natDegree_eq_succ_of_twoDegree
    hg_ne hdeg hcommon.symm

theorem natDegree_abs_sub_le_two {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 := by
  simpa [abs_sub_comm] using
    h.toLeftBranch_symm.natDegree_abs_sub_le_two hg_ne hg_splits hf_splits

/-- In the right Liu branch, restoring the deleted root of `g` leaves only the
same-degree, left-succ-degree, or left-plus-two-degree alternatives. -/
theorem natDegree_eq_or_eq_succ_or_eq_succ_succ {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hg_ne : g ≠ 0)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    g.natDegree = f.natDegree ∨
      g.natDegree = f.natDegree + 1 ∨
        g.natDegree = f.natDegree + 2 :=
  h.toLeftBranch_symm.natDegree_eq_or_eq_succ_or_eq_succ_succ
    hg_ne hg_splits hf_splits

end RightRootCountBranch

/-- Choose Liu's deletion branch from the two possible largest-root
orientations.  If `s ≤ r`, use the supplied left branch for `(f, g)`; if
`r < s`, use the supplied left branch for `(g, f)` and swap it to a right
branch. -/
theorem theorem21RootCountBranches_of_leftBranch_orientations
    {f g : ℝ[X]} {r s : ℝ}
    (hfg : s ≤ r → LeftRootCountBranch f g r s)
    (hgf : r < s → LeftRootCountBranch g f s r) :
    theorem21RootCountBranches f g := by
  rcases le_or_gt s r with hsr | hrs
  · exact theorem21RootCountBranches_of_left (hfg hsr)
  · exact theorem21RootCountBranches_of_right ((hgf hrs).toRightBranch_symm_of_lt hrs)

/-- Branch-level bridge from parity-guarded cross-owned consecutive roots to
Liu's largest-root deletion branch predicate.  In the larger-largest-root
orientation, the finite descent proves the `0..2` original strict-upper window
needed after deleting that largest root. -/
theorem theorem21RootCountBranches_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    {r s : ℝ} (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_leftBranch_orientations (r := r) (s := s)
    (fun hsr =>
      LeftRootCountBranch.of_crossOwned_consecutive_roots
        hf_ne hg_ne hr hs hsr hsimple_f hsimple_g hdisj hcross)
    (fun hrs =>
      LeftRootCountBranch.of_crossOwned_consecutive_roots
        hg_ne hf_ne hs hr hrs.le hsimple_g hsimple_f
        (fun c hgc hfc => hdisj c hfc hgc) hcross.symm)

/-- Branch-level bridge from parity-guarded cross-owned consecutive roots and
one-sided strict-upper root-count bounds to Liu's largest-root deletion branch.
This route requires stronger one-sided `≤ 1` hypotheses than the general
cross-owned count-window theorem
`theorem21RootCountBranches_of_crossOwned_consecutive_roots`. -/
theorem theorem21RootCountBranches_of_left_sub_le_one_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    {r s : ℝ} (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hupper_fg : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1)
    (hupper_gf : ∀ x : ℝ, ¬ g.IsRoot x → ¬ f.IsRoot x →
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    theorem21RootCountBranches f g := by
  refine theorem21RootCountBranches_of_leftBranch_orientations (r := r) (s := s) ?_ ?_
  · intro hsr
    exact
      LeftRootCountBranch.of_left_sub_right_le_one_of_right_le_left
        hf_ne hg_ne hr hs hsr hupper_fg
        (LeftRootCountBranch.right_le_left_of_crossOwned_consecutive_roots_of_left_sub_le_one
          hf_ne hg_ne hr hs hsr hupper_fg hsimple_f hsimple_g hdisj hcross)
  · intro hrs
    exact
      LeftRootCountBranch.of_left_sub_right_le_one_of_right_le_left
        hg_ne hf_ne hs hr hrs.le hupper_gf
        (LeftRootCountBranch.right_le_left_of_crossOwned_consecutive_roots_of_left_sub_le_one
          hg_ne hf_ne hs hr hrs.le hupper_gf hsimple_g hsimple_f
          (fun c hgc hfc => hdisj c hfc hgc) hcross.symm)

/-- Branch-level bridge from parity-guarded cross-owned consecutive roots to
Liu's largest-root deletion branch predicate.  Compatible root counts supply the
two one-sided strict-upper bounds needed by the one-sided descent theorem. -/
theorem theorem21RootCountBranches_of_rootCountCompatible_of_crossOwned_consecutive_roots
    {f g : ℝ[X]} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    {r s : ℝ} (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hcount : RootCountCompatible f g)
    (hsimple_f : ∀ c : ℝ, f.IsRoot c → f.roots.count c = 1)
    (hsimple_g : ∀ c : ℝ, g.IsRoot c → g.roots.count c = 1)
    (hdisj : ∀ c : ℝ, f.IsRoot c → ¬ g.IsRoot c)
    (hcross : CrossOwnedNotOddGaps f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_left_sub_le_one_of_crossOwned_consecutive_roots
    hf_ne hg_ne hr hs
    (fun _ hfx hgx => hcount.rootCountAbove_left_sub_le_one_of_nonRoot
      hf_ne hg_ne hfx hgx)
    (fun _ hgx hfx => hcount.symm.rootCountAbove_left_sub_le_one_of_nonRoot
      hg_ne hf_ne hgx hfx)
    hsimple_f hsimple_g hdisj hcross

theorem rootCountAtOrAbove_abs_sub_le_two_of_theorem21RootCountBranches
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (h : theorem21RootCountBranches f g) :
    ∀ x : ℝ,
      |((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ))| ≤ 2 := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact hleft.rootCountAtOrAbove_abs_sub_le_two hsgn.left_ne_zero
  · exact hright.rootCountAtOrAbove_abs_sub_le_two hsgn.right_ne_zero

theorem rootCountAtOrAbove_branch_bounds_of_theorem21RootCountBranches
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (h : theorem21RootCountBranches f g) :
    (∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 2 ∧
        ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 1) ∨
      (∀ x : ℝ,
        ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 1 ∧
          ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 2) := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact Or.inl (hleft.rootCountAtOrAbove_bounds hsgn.left_ne_zero)
  · exact Or.inr (hright.rootCountAtOrAbove_bounds hsgn.right_ne_zero)

/-- Liu branch data after normalizing the compared deletion pair so that both
leading coefficients are positive. -/
def theorem21PositiveDeletionCountBranches (f g : ℝ[X]) : Prop :=
  ∃ r s,
    (PositiveSplitRootCountPair (deleteRootFactor f r) (-g) ∨
        PositiveSplitRootCountPair (-(deleteRootFactor f r)) g) ∨
      (PositiveSplitRootCountPair f (-(deleteRootFactor g s)) ∨
        PositiveSplitRootCountPair (-f) (deleteRootFactor g s))

theorem theorem21PositiveDeletionCountBranches_of_theorem21RootCountBranches
    {f g : ℝ[X]} (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (h : theorem21RootCountBranches f g) :
    theorem21PositiveDeletionCountBranches f g := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact ⟨r, s, Or.inl (hleft.positiveSplitDeletionCount
      hsgn hf_splits hg_splits)⟩
  · exact ⟨r, s, Or.inr (hright.positiveSplitDeletionCount
      hsgn hf_splits hg_splits)⟩

theorem natDegree_abs_sub_le_two_of_theorem21RootCountBranches {f g : ℝ[X]}
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (h : theorem21RootCountBranches f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact hleft.natDegree_abs_sub_le_two hsgn.left_ne_zero hf_splits hg_splits
  · exact hright.natDegree_abs_sub_le_two hsgn.right_ne_zero hf_splits hg_splits

/-- Swapped-branch form of the Liu Theorem 2.1 degree-gap consequence. -/
theorem natDegree_abs_sub_le_two_of_theorem21RootCountBranches_symm {f g : ℝ[X]}
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (h : theorem21RootCountBranches g f) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 := by
  simpa [abs_sub_comm] using
    natDegree_abs_sub_le_two_of_theorem21RootCountBranches
      hg_splits hf_splits hsgn.symm h

end LiuOppositeSigns
end RealRooted
