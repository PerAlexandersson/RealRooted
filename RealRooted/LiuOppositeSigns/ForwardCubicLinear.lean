import RealRooted.LiuOppositeSigns
import RealRooted.LiuOppositeSigns.NoCommonRoots
import RealRooted.LiuOppositeSigns.XSub.CubicQuadratic

/-!
# Liu cubic/linear forward obstruction

This module contains the cubic/linear forward obstruction used in the
endpoint-degree-three part of Liu Theorem 2.1.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The remaining cubic/linear endpoint-degree-three obstruction in root-order
form.  For a compatible opposite-sign cubic/linear pair, the linear root must
lie weakly between the lower and largest cubic roots. -/
def CompatibleCubicLinearRootOrderStatement : Prop :=
  ∀ {f g : ℝ[X]} {a b c u : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      Compatible f g →
        f.natDegree = 3 → g.natDegree = 1 →
          a ≤ b → b ≤ c →
            f.roots = {a, b, c} → g.roots = {u} →
              a ≤ u ∧ u ≤ c

/-- Conditional degree `(3, 1)` no-common forward endpoint case.  Once the
cubic/linear root-order obstruction is known, deleting the cubic largest root
leaves a quadratic/linear root-count comparison. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_three_one_of_cubicLinearRootOrder
    (horder : CompatibleCubicLinearRootOrderStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 1) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn
      (by rw [hfdeg]; norm_num) (by rw [hgdeg]; norm_num)
  obtain ⟨a, b, c, hab, hbc, hfroots, hffac⟩ :=
    exists_roots_triple_of_splits_natDegree_three hf hfdeg
  obtain ⟨u, hgroots, _hgfac⟩ :=
    exists_linear_factor_of_splits_natDegree_one hg hgdeg
  obtain ⟨hau, huc⟩ :=
    horder hf hg hsgn hcompat hfdeg hgdeg hab hbc hfroots hgroots
  have hr_eq_c : r = c :=
    IsLargestRoot.eq_right_of_roots_triple hsgn.left_ne_zero hr hab hbc
      hfroots
  have hs_eq_u : s = u := by
    have hs_mem : s ∈ g.roots := hs.mem_roots hsgn.right_ne_zero
    rw [hgroots] at hs_mem
    simpa using hs_mem
  have hs_le_r : s ≤ r := by
    rw [hr_eq_c, hs_eq_u]
    exact huc
  have hdelete_roots : (deleteRootFactor f r).roots = {a, b} := by
    rw [hr_eq_c]
    exact roots_deleteRootFactor_eq_pair_of_roots_triple_right
      hsgn.left_ne_zero hfroots hffac
  exact theorem21RootCountBranches_of_left
    ⟨hr, hs, hs_le_r,
      RootCountCompatible.of_roots_pair_singleton
        hau hdelete_roots hgroots⟩

/-- Conditional degree `(1, 3)` no-common forward endpoint case, obtained by
applying the cubic/linear root-order obstruction after swapping the pair. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_one_three_of_cubicLinearRootOrder
    (horder : CompatibleCubicLinearRootOrderStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hfdeg : f.natDegree = 1) (hgdeg : g.natDegree = 3) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn
      (by rw [hfdeg]; norm_num) (by rw [hgdeg]; norm_num)
  obtain ⟨u, hfroots, _hffac⟩ :=
    exists_linear_factor_of_splits_natDegree_one hf hfdeg
  obtain ⟨a, b, c, hab, hbc, hgroots, hgfac⟩ :=
    exists_roots_triple_of_splits_natDegree_three hg hgdeg
  obtain ⟨hau, huc⟩ :=
    horder (f := g) (g := f) (a := a) (b := b) (c := c)
      (u := u) hg hf hsgn.symm hcompat.comm hgdeg hfdeg hab hbc
      hgroots hfroots
  have hr_eq_u : r = u := by
    have hr_mem : r ∈ f.roots := hr.mem_roots hsgn.left_ne_zero
    rw [hfroots] at hr_mem
    simpa using hr_mem
  have hs_eq_c : s = c :=
    IsLargestRoot.eq_right_of_roots_triple hsgn.right_ne_zero hs hab hbc
      hgroots
  have hu_root : f.IsRoot u :=
    (Polynomial.mem_roots hsgn.left_ne_zero).mp (by
      rw [hfroots]
      simp)
  have hc_root : g.IsRoot c :=
    (Polynomial.mem_roots hsgn.right_ne_zero).mp (by
      rw [hgroots]
      simp only [Multiset.insert_eq_cons]
      simp)
  have huc_ne : u ≠ c := by
    intro huc_eq
    exact (hno u hu_root) (by simpa [huc_eq] using hc_root)
  have hu_lt_c : u < c := lt_of_le_of_ne huc huc_ne
  have hr_lt_s : r < s := by
    rw [hr_eq_u, hs_eq_c]
    exact hu_lt_c
  have hdelete_roots : (deleteRootFactor g s).roots = {a, b} := by
    rw [hs_eq_c]
    exact roots_deleteRootFactor_eq_pair_of_roots_triple_right
      hsgn.right_ne_zero hgroots hgfac
  exact theorem21RootCountBranches_of_right
    ⟨hr, hs, hr_lt_s,
      RootCountCompatible.of_roots_singleton_pair
        hau hfroots hdelete_roots⟩

/-- Choosing the tangent slope at a right-outside point gives a monic
cubic-minus-linear pencil with negative discriminant. -/
lemma cubicDiscr_cubicSubLinear_slope_right_neg
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcu : c < u) :
    let μ : ℝ :=
      (u - b) * (u - c) + (u - a) * (u - c) + (u - a) * (u - b)
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)) < 0 := by
  intro μ
  have hdisc_eq :
      cubicDiscr
          (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)) =
        -((u - c) * (u - b) * (u - a) *
          (4 * (b - a) ^ 3 + 24 * (b - a) ^ 2 * (c - b) +
            36 * (b - a) ^ 2 * (u - c) +
            48 * (b - a) * (c - b) ^ 2 +
            171 * (b - a) * (c - b) * (u - c) +
            135 * (b - a) * (u - c) ^ 2 + 32 * (c - b) ^ 3 +
            171 * (c - b) ^ 2 * (u - c) +
            270 * (c - b) * (u - c) ^ 2 +
            135 * (u - c) ^ 3)) := by
    rw [cubicSubLinear_eq_cubic_expansion, cubicDiscr_of_coeffs]
    dsimp [μ]
    ring_nf
  rw [hdisc_eq]
  have huc : 0 < u - c := sub_pos.mpr hcu
  have hub : 0 < u - b := sub_pos.mpr (lt_of_le_of_lt hbc hcu)
  have hua : 0 < u - a := sub_pos.mpr (lt_of_le_of_lt (hab.trans hbc) hcu)
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hcb : 0 ≤ c - b := sub_nonneg.mpr hbc
  have hbracket :
      0 < 4 * (b - a) ^ 3 + 24 * (b - a) ^ 2 * (c - b) +
        36 * (b - a) ^ 2 * (u - c) +
        48 * (b - a) * (c - b) ^ 2 +
        171 * (b - a) * (c - b) * (u - c) +
        135 * (b - a) * (u - c) ^ 2 + 32 * (c - b) ^ 3 +
        171 * (c - b) ^ 2 * (u - c) +
        270 * (c - b) * (u - c) ^ 2 +
        135 * (u - c) ^ 3 := by
    positivity
  nlinarith [mul_pos (mul_pos (mul_pos huc hub) hua) hbracket]

/-- Choosing the tangent slope at a left-outside point gives a monic
cubic-minus-linear pencil with negative discriminant. -/
lemma cubicDiscr_cubicSubLinear_slope_left_neg
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u < a) :
    let μ : ℝ :=
      (u - b) * (u - c) + (u - a) * (u - c) + (u - a) * (u - b)
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)) < 0 := by
  intro μ
  have hdisc_eq :
      cubicDiscr
          (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)) =
        -((a - u) * (b - u) * (c - u) *
          (135 * (a - u) ^ 3 + 270 * (a - u) ^ 2 * (b - a) +
            135 * (a - u) ^ 2 * (c - b) +
            171 * (a - u) * (b - a) ^ 2 +
            171 * (a - u) * (b - a) * (c - b) +
            36 * (a - u) * (c - b) ^ 2 + 32 * (b - a) ^ 3 +
            48 * (b - a) ^ 2 * (c - b) +
            24 * (b - a) * (c - b) ^ 2 + 4 * (c - b) ^ 3)) := by
    rw [cubicSubLinear_eq_cubic_expansion, cubicDiscr_of_coeffs]
    dsimp [μ]
    ring_nf
  rw [hdisc_eq]
  have hau : 0 < a - u := sub_pos.mpr hua
  have hbu : 0 < b - u := sub_pos.mpr (lt_of_lt_of_le hua hab)
  have hcu : 0 < c - u := sub_pos.mpr (lt_of_lt_of_le hua (hab.trans hbc))
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hcb : 0 ≤ c - b := sub_nonneg.mpr hbc
  have hbracket :
      0 < 135 * (a - u) ^ 3 + 270 * (a - u) ^ 2 * (b - a) +
        135 * (a - u) ^ 2 * (c - b) +
        171 * (a - u) * (b - a) ^ 2 +
        171 * (a - u) * (b - a) * (c - b) +
        36 * (a - u) * (c - b) ^ 2 + 32 * (b - a) ^ 3 +
        48 * (b - a) ^ 2 * (c - b) +
        24 * (b - a) * (c - b) ^ 2 + 4 * (c - b) ^ 3 := by
    positivity
  nlinarith [mul_pos (mul_pos (mul_pos hau hbu) hcu) hbracket]

/-- If the linear root lies strictly above the cubic roots, then some positive
subtraction coefficient makes the monic cubic-minus-linear pencil fail to
split. -/
lemma exists_cubicSubLinear_not_splits_of_upper_lt_right_root
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcu : c < u) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * (X - C u)).Splits := by
  let μ : ℝ :=
    (u - b) * (u - c) + (u - a) * (u - c) + (u - a) * (u - b)
  have hμ : 0 < μ := by
    dsimp [μ]
    have huc : 0 < u - c := sub_pos.mpr hcu
    have hub : 0 < u - b := sub_pos.mpr (lt_of_le_of_lt hbc hcu)
    have hua : 0 < u - a := sub_pos.mpr (lt_of_le_of_lt (hab.trans hbc) hcu)
    positivity
  refine ⟨μ, hμ, ?_⟩
  have hdeg :
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * (X - C u)).natDegree ≤ 3 := by
    rw [natDegree_cubicSubLinear]
  have hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)) < 0 :=
    cubicDiscr_cubicSubLinear_slope_right_neg hab hbc hcu
  intro hsplit
  exact (not_le.mpr hdisc)
    (cubicDiscr_nonneg_of_splits_natDegree_le_three hdeg hsplit)

/-- If the linear root lies strictly below the cubic roots, then some positive
subtraction coefficient makes the monic cubic-minus-linear pencil fail to
split. -/
lemma exists_cubicSubLinear_not_splits_of_left_root_lt_lower
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u < a) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * (X - C u)).Splits := by
  let μ : ℝ :=
    (u - b) * (u - c) + (u - a) * (u - c) + (u - a) * (u - b)
  have hμ : 0 < μ := by
    dsimp [μ]
    have hba : u - b < 0 := sub_neg.mpr (lt_of_lt_of_le hua hab)
    have hca : u - c < 0 := sub_neg.mpr (lt_of_lt_of_le hua (hab.trans hbc))
    have hua' : u - a < 0 := sub_neg.mpr hua
    have h1 : 0 < (u - b) * (u - c) := mul_pos_of_neg_of_neg hba hca
    have h2 : 0 < (u - a) * (u - c) := mul_pos_of_neg_of_neg hua' hca
    have h3 : 0 < (u - a) * (u - b) := mul_pos_of_neg_of_neg hua' hba
    linarith
  refine ⟨μ, hμ, ?_⟩
  have hdeg :
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * (X - C u)).natDegree ≤ 3 := by
    rw [natDegree_cubicSubLinear]
  have hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)) < 0 :=
    cubicDiscr_cubicSubLinear_slope_left_neg hab hbc hua
  intro hsplit
  exact (not_le.mpr hdisc)
    (cubicDiscr_nonneg_of_splits_natDegree_le_three hdeg hsplit)

/-- The cubic/linear factor endpoint is not compatible when the leading
coefficients have opposite signs and the linear root lies strictly above the
cubic root interval. -/
lemma not_compatible_scaled_cubic_linear_of_opposite_of_upper_lt_right_root
    {a b c u A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hcu : c < u) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * (X - C u)) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubLinear_not_splits_of_upper_lt_right_root hab hbc hcu
  have hA_ne : A ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).1
  have hB_ne : B ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).2
  intro hcompat
  rcases lt_or_gt_of_ne hA_ne with hA_neg | hA_pos
  · have hB_pos : 0 < B := by
      by_contra hB_not
      have hB_nonpos : B ≤ 0 := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA_neg) hB_nonpos
      linarith
    have hnegA_pos : 0 < -A := by linarith
    have hα : 0 ≤ 1 / (-A) := by positivity
    have hβ : 0 ≤ μ / B := by positivity
    have hcase := hcompat (1 / (-A)) (μ / B) hα hβ
    have hcombo_eq :
        C (1 / (-A)) *
              (C A * ((X - C a) * (X - C b) * (X - C c))) +
            C (μ / B) * (C B * (X - C u)) =
          -((((X - C a) * (X - C b) * (X - C c)) -
            C μ * (X - C u))) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · have hzero' :
          ((X - C a) * (X - C b) * (X - C c)) -
              C μ * (X - C u) = 0 := by
        rw [← neg_eq_zero]
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzero
      exact hnot_splits (hzero'.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits (by simpa using hsplit.neg)
  · have hB_neg : B < 0 := by
      by_contra hB_not
      have hB_nonneg : 0 ≤ B := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B := mul_nonneg (le_of_lt hA_pos) hB_nonneg
      linarith
    have hnegB_pos : 0 < -B := by linarith
    have hα : 0 ≤ 1 / A := by positivity
    have hβ : 0 ≤ μ / (-B) := by positivity
    have hcase := hcompat (1 / A) (μ / (-B)) hα hβ
    have hcombo_eq :
        C (1 / A) *
              (C A * ((X - C a) * (X - C b) * (X - C c))) +
            C (μ / (-B)) * (C B * (X - C u)) =
          ((X - C a) * (X - C b) * (X - C c)) -
            C μ * (X - C u) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits hsplit

/-- The cubic/linear factor endpoint is not compatible when the leading
coefficients have opposite signs and the linear root lies strictly below the
cubic root interval. -/
lemma not_compatible_scaled_cubic_linear_of_opposite_of_left_root_lt_lower
    {a b c u A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hua : u < a) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * (X - C u)) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubLinear_not_splits_of_left_root_lt_lower hab hbc hua
  have hA_ne : A ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).1
  have hB_ne : B ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).2
  intro hcompat
  rcases lt_or_gt_of_ne hA_ne with hA_neg | hA_pos
  · have hB_pos : 0 < B := by
      by_contra hB_not
      have hB_nonpos : B ≤ 0 := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA_neg) hB_nonpos
      linarith
    have hnegA_pos : 0 < -A := by linarith
    have hα : 0 ≤ 1 / (-A) := by positivity
    have hβ : 0 ≤ μ / B := by positivity
    have hcase := hcompat (1 / (-A)) (μ / B) hα hβ
    have hcombo_eq :
        C (1 / (-A)) *
              (C A * ((X - C a) * (X - C b) * (X - C c))) +
            C (μ / B) * (C B * (X - C u)) =
          -((((X - C a) * (X - C b) * (X - C c)) -
            C μ * (X - C u))) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · have hzero' :
          ((X - C a) * (X - C b) * (X - C c)) -
              C μ * (X - C u) = 0 := by
        rw [← neg_eq_zero]
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzero
      exact hnot_splits (hzero'.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits (by simpa using hsplit.neg)
  · have hB_neg : B < 0 := by
      by_contra hB_not
      have hB_nonneg : 0 ≤ B := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B := mul_nonneg (le_of_lt hA_pos) hB_nonneg
      linarith
    have hnegB_pos : 0 < -B := by linarith
    have hα : 0 ≤ 1 / A := by positivity
    have hβ : 0 ≤ μ / (-B) := by positivity
    have hcase := hcompat (1 / A) (μ / (-B)) hα hβ
    have hcombo_eq :
        C (1 / A) *
              (C A * ((X - C a) * (X - C b) * (X - C c))) +
            C (μ / (-B)) * (C B * (X - C u)) =
          ((X - C a) * (X - C b) * (X - C c)) -
            C μ * (X - C u) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits hsplit

/-- Compatible opposite-sign cubic/linear pairs have the linear root in the
closed interval spanned by the cubic roots. -/
theorem compatibleCubicLinearRootOrder :
    CompatibleCubicLinearRootOrderStatement := by
  intro f g a b c u hf hg hsgn hcompat hfdeg hgdeg hab hbc hfroots hgroots
  have hffac :
      f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) :=
    eq_C_leadingCoeff_mul_prod_three hf a b c hfroots
  have hgfac : g = C g.leadingCoeff * (X - C u) := by
    have hprod := hg.eq_prod_roots
    rw [hgroots] at hprod
    simpa using hprod
  have hcompat_fac :
      Compatible
        (C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)))
        (C g.leadingCoeff * (X - C u)) := by
    rw [← hffac, ← hgfac]
    exact hcompat
  refine ⟨?_, ?_⟩
  · by_contra hnot
    have hua : u < a := lt_of_not_ge hnot
    exact
      not_compatible_scaled_cubic_linear_of_opposite_of_left_root_lt_lower
        (A := f.leadingCoeff) (B := g.leadingCoeff)
        hsgn hab hbc hua hcompat_fac
  · by_contra hnot
    have hcu : c < u := lt_of_not_ge hnot
    exact
      not_compatible_scaled_cubic_linear_of_opposite_of_upper_lt_right_root
        (A := f.leadingCoeff) (B := g.leadingCoeff)
        hsgn hab hbc hcu hcompat_fac

/-- Checked degree `(3, 1)` no-common forward endpoint case. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_three_one
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 1) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_natDegree_three_one_of_cubicLinearRootOrder
    compatibleCubicLinearRootOrder hf hg hsgn hcompat hfdeg hgdeg

/-- Checked degree `(1, 3)` no-common forward endpoint case. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_one_three
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hfdeg : f.natDegree = 1) (hgdeg : g.natDegree = 3) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_natDegree_one_three_of_cubicLinearRootOrder
    compatibleCubicLinearRootOrder hf hg hsgn hcompat hno hfdeg hgdeg

end LiuOppositeSigns
end RealRooted
