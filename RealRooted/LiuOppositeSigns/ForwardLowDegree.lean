import RealRooted.LiuOppositeSigns.Theorem21Assembly

/-!
# Liu low-degree forward branch lemmas

This module contains the checked low-degree forward branch lemmas used by the
bounded endpoint-two Liu theorem packages.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- In the nonconstant degree-one endpoint case, Liu's largest-root deletion
branch condition is automatic: deleting one endpoint leaves a degree-zero
polynomial, while the other endpoint has at most one root above any threshold.
-/
theorem theorem21RootCountBranches_of_natDegree_le_one_nonconstant
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hf_le : f.natDegree ≤ 1) (hg_le : g.natDegree ≤ 1) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn hf_deg hg_deg
  have hf_eq : f.natDegree = 1 :=
    le_antisymm hf_le (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hf_deg))
  have hg_eq : g.natDegree = 1 :=
    le_antisymm hg_le (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hg_deg))
  by_cases hs_le_r : s ≤ r
  · refine theorem21RootCountBranches_of_left
      ⟨hr, hs, hs_le_r, ?_⟩
    have hdelete_splits : (deleteRootFactor f r).Splits :=
      hr.deleteRootFactor_splits hf
    have hdelete_deg : (deleteRootFactor f r).natDegree = 0 := by
      rw [natDegree_deleteRootFactor, hf_eq]
    exact RootCountCompatible.of_left_natDegree_zero_right_natDegree_le_one
      hdelete_splits hg hdelete_deg hg_le
  · refine theorem21RootCountBranches_of_right
      ⟨hr, hs, lt_of_not_ge hs_le_r, ?_⟩
    have hdelete_splits : (deleteRootFactor g s).Splits :=
      hs.deleteRootFactor_splits hg
    have hdelete_deg : (deleteRootFactor g s).natDegree = 0 := by
      rw [natDegree_deleteRootFactor, hg_eq]
    exact (RootCountCompatible.of_left_natDegree_zero_right_natDegree_le_one
      hdelete_splits hf hdelete_deg hf_le).symm

/-- Degree `(2, 1)` forward subcase when the largest root lies on the
degree-two side, so deleting that root leaves two linear-or-constant endpoints.
-/
theorem theorem21RootCountBranches_of_left_largest_natDegree_le_two_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hs_le_r : s ≤ r) (hf_le : f.natDegree ≤ 2)
    (hg_le : g.natDegree ≤ 1) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_left
    (LeftRootCountBranch.of_largestRoots_natDegree_le_two_right_le_one
      hf hg hr hs hs_le_r hf_le hg_le)

/-- Degree `(1, 2)` forward subcase when the largest root lies on the
degree-two side, so deleting that root leaves two linear-or-constant endpoints.
-/
theorem theorem21RootCountBranches_of_right_largest_natDegree_le_one_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hr_lt_s : r < s) (hf_le : f.natDegree ≤ 1)
    (hg_le : g.natDegree ≤ 2) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_right
    (RightRootCountBranch.of_largestRoots_left_le_one_right_le_two
      hf hg hr hs hr_lt_s hf_le hg_le)

/-- Low-degree endpoint forward direction for the nonconstant degree-one case.
The compatibility hypothesis is retained to match the Liu Theorem 2.1 forward
shape, although the root-count branch condition follows from degree alone. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_le_one_nonconstant
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hf_le : f.natDegree ≤ 1) (hg_le : g.natDegree ≤ 1)
    (_hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_natDegree_le_one_nonconstant
    hf hg hsgn hf_deg hg_deg hf_le hg_le
/-- If the linear root lies strictly above the upper quadratic root, then some
positive subtraction coefficient makes the monic quadratic-minus-linear pencil
fail to split. -/
lemma exists_quadraticSubLinear_not_splits_of_upper_lt_right_root
    {a b c : ℝ} (hab : a ≤ b) (hbc : b < c) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b)) - C μ * (X - C c)).Splits := by
  let μ : ℝ := 2 * c - a - b
  have hμ : 0 < μ := by
    dsimp [μ]
    linarith
  refine ⟨μ, hμ, ?_⟩
  have hpoly :
      ((X - C a) * (X - C b)) - C μ * (X - C c) =
        C 1 * X ^ 2 + C (-(a + b + μ)) * X + C (a * b + μ * c) := by
    simp only [C_add, C_mul, C_neg, C_1]
    ring
  have hdisc : discrim 1 (-(a + b + μ)) (a * b + μ * c) < 0 := by
    have hac : a < c := lt_of_le_of_lt hab hbc
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos (sub_pos.mpr hac) (sub_pos.mpr hbc)
    have hdisc_eq :
        discrim 1 (-(a + b + μ)) (a * b + μ * c) =
          -4 * ((c - a) * (c - b)) := by
      dsimp [μ]
      unfold discrim
      ring_nf
    rw [hdisc_eq]
    nlinarith
  intro hsplit
  exact (quadraticPoly_not_splits_of_discrim_neg one_ne_zero hdisc) (by
    simpa [hpoly] using hsplit)

/-- The sign-normalized quadratic/linear endpoint is not compatible when the
linear root lies strictly above the upper quadratic root. -/
lemma not_compatible_quadratic_neg_linear_of_upper_lt_right_root
    {a b c : ℝ} (hab : a ≤ b) (hbc : b < c) :
    ¬ Compatible ((X - C a) * (X - C b)) (-(X - C c)) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_quadraticSubLinear_not_splits_of_upper_lt_right_root hab hbc
  intro hcompat
  have hcase := hcompat (1 : ℝ) μ zero_le_one (le_of_lt hμ)
  have hcombo_eq :
      C (1 : ℝ) * ((X - C a) * (X - C b)) + C μ * (-(X - C c)) =
        (X - C a) * (X - C b) - C μ * (X - C c) := by
    simp only [C_1, one_mul]
    ring_nf
  have hcase' :
      ((X - C a) * (X - C b) - C μ * (X - C c) = 0) ∨
        ((X - C a) * (X - C b) - C μ * (X - C c) ≠ 0 ∧
          ((X - C a) * (X - C b) - C μ * (X - C c)).Splits) := by
    rw [hcombo_eq] at hcase
    exact hcase
  rcases hcase' with hzero | ⟨_, hsplit⟩
  · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
  · exact hnot_splits hsplit

/-- The quadratic/linear factor endpoint is not compatible when the leading
coefficients have opposite signs and the linear root lies strictly above the
upper quadratic root. -/
lemma not_compatible_scaled_quadratic_linear_of_opposite_of_upper_lt_right_root
    {a b c A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b < c) :
    ¬ Compatible (C A * ((X - C a) * (X - C b))) (C B * (X - C c)) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_quadraticSubLinear_not_splits_of_upper_lt_right_root hab hbc
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
        C (1 / (-A)) * (C A * ((X - C a) * (X - C b))) +
            C (μ / B) * (C B * (X - C c)) =
          -(((X - C a) * (X - C b)) - C μ * (X - C c)) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · have hzero' :
          ((X - C a) * (X - C b)) - C μ * (X - C c) = 0 := by
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
        C (1 / A) * (C A * ((X - C a) * (X - C b))) +
            C (μ / (-B)) * (C B * (X - C c)) =
          ((X - C a) * (X - C b)) - C μ * (X - C c) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits hsplit

/-- Normalized discriminant identity for the bad quadratic/quadratic nested
root order. -/
lemma discrim_quadraticSubQuadratic_inner_vertex {u v w : ℝ}
    (hv : v ≠ 0) :
    let μ := (u * v + 2 * u * w + v ^ 2 + v * w) / v ^ 2
    discrim (1 - μ) (-(0 + (u + v + w)) + μ * (u + (u + v)))
      (0 * (u + v + w) - μ * (u * (u + v))) =
        -4 * u * w * (u + v) * (v + w) / v ^ 2 := by
  intro μ
  dsimp [μ]
  have hv2_ne : v ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 hv
  unfold discrim
  field_simp [hv2_ne]
  ring

/-- If the two roots of one monic quadratic lie strictly inside the root
interval of another, then some positive monic quadratic-minus-quadratic
pencil fails to split. -/
lemma exists_quadraticSubQuadratic_not_splits_of_inner_roots
    {a b c d : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d))).Splits := by
  by_cases hcd_eq : c = d
  · let μ : ℝ := ((b - a) ^ 2 + 1) / (4 * (c - a) * (b - c))
    subst d
    have hca_pos : 0 < c - a := sub_pos.mpr hac
    have hbc_pos : 0 < b - c := sub_pos.mpr (by linarith)
    have hden_pos : 0 < 4 * (c - a) * (b - c) := by positivity
    have hden_ne : 4 * (c - a) * (b - c) ≠ 0 := ne_of_gt hden_pos
    have hμ_pos : 0 < μ := by
      dsimp [μ]
      positivity
    have hμ_gt_one : 1 < μ := by
      dsimp [μ]
      have hnum_gt : 4 * (c - a) * (b - c) < (b - a) ^ 2 + 1 := by
        nlinarith [sq_nonneg ((c - a) - (b - c))]
      rw [one_lt_div hden_pos]
      linarith
    refine ⟨μ, hμ_pos, ?_⟩
    have hlead_ne : (1 - μ) ≠ 0 := by linarith
    have hdisc :
        discrim (1 - μ) (-(a + b) + μ * (c + c))
            (a * b - μ * (c * c)) < 0 := by
      have hdisc_eq :
          discrim (1 - μ) (-(a + b) + μ * (c + c))
              (a * b - μ * (c * c)) =
            -1 := by
        dsimp [μ]
        unfold discrim
        field_simp [hden_ne]
        ring_nf
      rw [hdisc_eq]
      norm_num
    intro hsplit
    have hpoly :
        ((X - C a) * (X - C b)) -
            C μ * ((X - C c) * (X - C c)) =
          C (1 - μ) * X ^ 2 + C (-(a + b) + μ * (c + c)) * X +
            C (a * b - μ * (c * c)) := by
      simp only [C_add, C_mul, C_neg, C_sub, C_1]
      ring
    exact
      (quadraticPoly_not_splits_of_discrim_neg hlead_ne hdisc)
        (by simpa [hpoly] using hsplit)
  · have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
    let u : ℝ := c - a
    let v : ℝ := d - c
    let w : ℝ := b - d
    let μ : ℝ := (u * v + 2 * u * w + v ^ 2 + v * w) / v ^ 2
    have hu : 0 < u := by
      dsimp [u]
      linarith
    have hv : 0 < v := by
      dsimp [v]
      linarith
    have hw : 0 < w := by
      dsimp [w]
      linarith
    have hμ_pos : 0 < μ := by
      dsimp [μ]
      positivity
    have hμ_gt_one : 1 < μ := by
      dsimp [μ]
      have hnum_gt : v ^ 2 < u * v + 2 * u * w + v ^ 2 + v * w := by
        nlinarith [mul_pos hu hv, mul_pos hu hw, mul_pos hv hw]
      rw [one_lt_div (by positivity : 0 < v ^ 2)]
      linarith
    refine ⟨μ, hμ_pos, ?_⟩
    have hlead_ne : (1 - μ) ≠ 0 := by linarith
    have hdisc :
        discrim (1 - μ) (-(a + b) + μ * (c + d))
            (a * b - μ * (c * d)) < 0 := by
      have hroots_eq :
          discrim (1 - μ) (-(a + b) + μ * (c + d))
              (a * b - μ * (c * d)) =
            discrim (1 - μ)
              (-(0 + (u + v + w)) + μ * (u + (u + v)))
              (0 * (u + v + w) - μ * (u * (u + v))) := by
        dsimp [u, v, w]
        unfold discrim
        ring_nf
      rw [hroots_eq]
      rw [discrim_quadraticSubQuadratic_inner_vertex hv.ne']
      have hrewrite :
          -4 * u * w * (u + v) * (v + w) / v ^ 2 =
            -(4 * u * w * (u + v) * (v + w) / v ^ 2) := by
        ring
      rw [hrewrite]
      have hpos : 0 < 4 * u * w * (u + v) * (v + w) / v ^ 2 := by
        positivity
      linarith
    intro hsplit
    have hpoly :
        ((X - C a) * (X - C b)) -
            C μ * ((X - C c) * (X - C d)) =
          C (1 - μ) * X ^ 2 + C (-(a + b) + μ * (c + d)) * X +
            C (a * b - μ * (c * d)) := by
      simp only [C_add, C_mul, C_neg, C_sub, C_1]
      ring
    exact
      (quadraticPoly_not_splits_of_discrim_neg hlead_ne hdisc)
        (by simpa [hpoly] using hsplit)

/-- The scaled quadratic/quadratic endpoint is not compatible when one pair of
roots lies strictly inside the other and the leading coefficients have
opposite signs. -/
lemma not_compatible_scaled_quadratic_quadratic_of_opposite_of_inner_roots
    {a b c d A B : ℝ} (hAB : A * B < 0)
    (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b)))
      (C B * ((X - C c) * (X - C d))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_quadraticSubQuadratic_not_splits_of_inner_roots hac hcd hdb
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
        C (1 / (-A)) * (C A * ((X - C a) * (X - C b))) +
            C (μ / B) * (C B * ((X - C c) * (X - C d))) =
          -(((X - C a) * (X - C b)) -
            C μ * ((X - C c) * (X - C d))) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · have hzero' :
          ((X - C a) * (X - C b)) -
              C μ * ((X - C c) * (X - C d)) = 0 := by
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
        C (1 / A) * (C A * ((X - C a) * (X - C b))) +
            C (μ / (-B)) * (C B * ((X - C c) * (X - C d))) =
          ((X - C a) * (X - C b)) -
            C μ * ((X - C c) * (X - C d)) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits hsplit

/-- In the degree `(2, 1)` endpoint, compatibility rules out the orientation
where the quadratic side has smaller largest root. -/
lemma not_compatible_of_natDegree_two_one_largest_lt
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 1)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hr_lt_s : r < s) :
    ¬ Compatible f g := by
  obtain ⟨a, b, hab, hfroots, hffac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hf hfdeg
  obtain ⟨c, hgroots, hgfac⟩ :=
    exists_linear_factor_of_splits_natDegree_one hg hgdeg
  have hb_le_r : b ≤ r := by
    have hb_mem : b ∈ f.roots := by
      rw [hfroots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact hr.roots_le b hb_mem
  have hs_eq_c : s = c := by
    have hs_mem : s ∈ g.roots := hs.mem_roots hsgn.right_ne_zero
    rw [hgroots] at hs_mem
    simpa using hs_mem
  have hb_lt_c : b < c := by
    rw [← hs_eq_c]
    exact lt_of_le_of_lt hb_le_r hr_lt_s
  intro hcompat
  exact
    not_compatible_scaled_quadratic_linear_of_opposite_of_upper_lt_right_root
      (A := f.leadingCoeff) (B := g.leadingCoeff)
      hsgn hab hb_lt_c (by
        rw [hffac, hgfac] at hcompat
        exact hcompat)

/-- Forward degree `(2, 1)` endpoint case of Liu's root-count branch theorem.
Compatibility forces the largest root to lie on the quadratic side, and the
existing low-degree branch constructor then applies. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_two_one
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 1) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn
      (by rw [hfdeg]; norm_num) (by rw [hgdeg]; norm_num)
  by_cases hs_le_r : s ≤ r
  · exact theorem21RootCountBranches_of_left_largest_natDegree_le_two_one
      hf hg hr hs hs_le_r (by rw [hfdeg]) (by rw [hgdeg])
  · exact False.elim
      (not_compatible_of_natDegree_two_one_largest_lt
        hf hg hsgn hfdeg hgdeg hr hs (lt_of_not_ge hs_le_r) hcompat)

/-- In the degree `(1, 2)` endpoint, compatibility rules out the orientation
where the quadratic side has smaller largest root. -/
lemma not_compatible_of_natDegree_one_two_largest_gt
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree = 1) (hgdeg : g.natDegree = 2)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hs_lt_r : s < r) :
    ¬ Compatible f g := by
  intro hcompat
  exact not_compatible_of_natDegree_two_one_largest_lt
    hg hf hsgn.symm hgdeg hfdeg hs hr hs_lt_r hcompat.comm

/-- Forward degree `(1, 2)` endpoint case with distinct largest roots.
Compatibility forces the largest root to lie on the quadratic side, and the
existing low-degree branch constructor then applies. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_one_two_of_largest_ne
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hfdeg : f.natDegree = 1)
    (hgdeg : g.natDegree = 2) (hr : IsLargestRoot f r)
    (hs : IsLargestRoot g s) (hrs_ne : r ≠ s) :
    theorem21RootCountBranches f g := by
  rcases lt_or_gt_of_ne hrs_ne with hr_lt_s | hs_lt_r
  · exact theorem21RootCountBranches_of_right_largest_natDegree_le_one_two
      hf hg hr hs hr_lt_s (by rw [hfdeg]) (by rw [hgdeg])
  · exact False.elim
      (not_compatible_of_natDegree_one_two_largest_gt
        hf hg hsgn hfdeg hgdeg hr hs hs_lt_r hcompat)

/-- Forward degree `(1, 2)` endpoint case in the no-common-root regime used by
Liu's proof reduction.  The no-common hypothesis rules out the otherwise
separate equal-largest-root corner. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_one_two_of_no_common
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hfdeg : f.natDegree = 1) (hgdeg : g.natDegree = 2)
    (hno : NoCommonRoots f g) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn
      (by rw [hfdeg]; norm_num) (by rw [hgdeg]; norm_num)
  have hrs_ne : r ≠ s := by
    intro hrs
    exact (hno r hr.isRoot) (by simpa [hrs] using hs.isRoot)
  exact theorem21RootCountBranches_of_compatible_natDegree_one_two_of_largest_ne
    hf hg hsgn hcompat hfdeg hgdeg hr hs hrs_ne

/-- Mixed endpoint degree-two no-common forward case.  This combines the
checked `(2, 1)` obstruction with its `(1, 2)` no-common counterpart. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_one_two_or_two_one_of_no_common
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hdeg :
      (f.natDegree = 2 ∧ g.natDegree = 1) ∨
        (f.natDegree = 1 ∧ g.natDegree = 2)) :
    theorem21RootCountBranches f g := by
  rcases hdeg with hdeg | hdeg
  · exact theorem21RootCountBranches_of_compatible_natDegree_two_one
      hf hg hsgn hcompat hdeg.1 hdeg.2
  · exact theorem21RootCountBranches_of_compatible_natDegree_one_two_of_no_common
      hf hg hsgn hcompat hdeg.1 hdeg.2 hno

/-- No-common quadratic/quadratic forward endpoint case.  If the largest root
of one side lies to the right, deleting it leaves a singleton/two-root
comparison.  The only way that count comparison could fail is the bad nested
root order, which contradicts compatibility by the discriminant obstruction
above. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_two_two_of_no_common
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 2)
    (hno : NoCommonRoots f g) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn
      (by rw [hfdeg]; norm_num) (by rw [hgdeg]; norm_num)
  obtain ⟨a, b, hab, hfroots, hffac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hf hfdeg
  obtain ⟨c, d, hcd, hgroots, hgfac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hg hgdeg
  have hr_eq_b : r = b :=
    IsLargestRoot.eq_right_of_roots_pair hsgn.left_ne_zero hr hab hfroots
  have hs_eq_d : s = d :=
    IsLargestRoot.eq_right_of_roots_pair hsgn.right_ne_zero hs hcd hgroots
  have hdelete_f_roots : (deleteRootFactor f r).roots = {a} := by
    rw [hr_eq_b]
    exact roots_deleteRootFactor_eq_singleton_of_roots_pair_right
      hsgn.left_ne_zero hfroots hffac
  have hdelete_g_roots : (deleteRootFactor g s).roots = {c} := by
    rw [hs_eq_d]
    exact roots_deleteRootFactor_eq_singleton_of_roots_pair_right
      hsgn.right_ne_zero hgroots hgfac
  have hcompat_fac :
      Compatible
        (C f.leadingCoeff * ((X - C a) * (X - C b)))
        (C g.leadingCoeff * ((X - C c) * (X - C d))) := by
    rw [← hffac, ← hgfac]
    exact hcompat
  by_cases hs_le_r : s ≤ r
  · have hca : c ≤ a := by
      by_contra hnot
      have hac : a < c := lt_of_not_ge hnot
      have hd_le_b : d ≤ b := by
        simpa [hr_eq_b, hs_eq_d] using hs_le_r
      have hb_root : f.IsRoot b :=
        (Polynomial.mem_roots hsgn.left_ne_zero).mp (by
          rw [hfroots]
          simp only [Multiset.insert_eq_cons]
          simp)
      have hd_root : g.IsRoot d :=
        (Polynomial.mem_roots hsgn.right_ne_zero).mp (by
          rw [hgroots]
          simp only [Multiset.insert_eq_cons]
          simp)
      have hdb_ne : d ≠ b := by
        intro hdb_eq
        exact (hno b hb_root) (by simpa [hdb_eq] using hd_root)
      have hdb : d < b := lt_of_le_of_ne hd_le_b hdb_ne
      exact
        not_compatible_scaled_quadratic_quadratic_of_opposite_of_inner_roots
          (A := f.leadingCoeff) (B := g.leadingCoeff)
          hsgn hac hcd hdb hcompat_fac
    exact theorem21RootCountBranches_of_left
      ⟨hr, hs, hs_le_r,
        RootCountCompatible.of_roots_singleton_pair
          hca hdelete_f_roots hgroots⟩
  · have hr_lt_s : r < s := lt_of_not_ge hs_le_r
    have hac : a ≤ c := by
      by_contra hnot
      have hca : c < a := lt_of_not_ge hnot
      have hb_lt_d : b < d := by
        simpa [hr_eq_b, hs_eq_d] using hr_lt_s
      exact
        not_compatible_scaled_quadratic_quadratic_of_opposite_of_inner_roots
          (a := c) (b := d) (c := a) (d := b)
          (A := g.leadingCoeff) (B := f.leadingCoeff)
          hsgn.symm hca hab hb_lt_d hcompat_fac.comm
    exact theorem21RootCountBranches_of_right
      ⟨hr, hs, hr_lt_s,
        RootCountCompatible.of_roots_pair_singleton
          hac hfroots hdelete_g_roots⟩

/-- Nonconstant degree-`≤ 2` no-common forward case, excluding only the
remaining quadratic-quadratic corner. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_le_two_nonquadratic_of_no_common
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 2) (hgdeg_le : g.natDegree ≤ 2)
    (hnot_quad_quad : ¬ (f.natDegree = 2 ∧ g.natDegree = 2)) :
    theorem21RootCountBranches f g := by
  have hf_cases : f.natDegree = 1 ∨ f.natDegree = 2 := by
    have hfdeg_pos : 0 < f.natDegree := Nat.pos_of_ne_zero hfdeg_ne
    interval_cases f.natDegree <;> simp_all
  have hg_cases : g.natDegree = 1 ∨ g.natDegree = 2 := by
    have hgdeg_pos : 0 < g.natDegree := Nat.pos_of_ne_zero hgdeg_ne
    interval_cases g.natDegree <;> simp_all
  rcases hf_cases with hfdeg | hfdeg <;> rcases hg_cases with hgdeg | hgdeg
  · exact theorem21RootCountBranches_of_compatible_natDegree_le_one_nonconstant
      hf hg hsgn hfdeg_ne hgdeg_ne (by rw [hfdeg]) (by rw [hgdeg]) hcompat
  · exact theorem21RootCountBranches_of_compatible_natDegree_one_two_of_no_common
      hf hg hsgn hcompat hfdeg hgdeg hno
  · exact theorem21RootCountBranches_of_compatible_natDegree_two_one
      hf hg hsgn hcompat hfdeg hgdeg
  · exact False.elim (hnot_quad_quad ⟨hfdeg, hgdeg⟩)

/-- Nonconstant degree-`≤ 2` no-common forward case. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_le_two_of_no_common
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 2) (hgdeg_le : g.natDegree ≤ 2) :
    theorem21RootCountBranches f g := by
  by_cases hquad_quad : f.natDegree = 2 ∧ g.natDegree = 2
  · exact theorem21RootCountBranches_of_compatible_natDegree_two_two_of_no_common
      hf hg hsgn hcompat hquad_quad.1 hquad_quad.2 hno
  · exact
      theorem21RootCountBranches_of_compatible_natDegree_le_two_nonquadratic_of_no_common
        hf hg hsgn hcompat hno hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le hquad_quad

end LiuOppositeSigns
end RealRooted
