import RealRooted.Bezoutian.WronskianConverse
import RealRooted.Mathlib.Analysis.Polynomial.Basic
import RealRooted.Wronskian.WeakForward

/-!
# The weak Wronskian converse

Let `f` and `g` be real-rooted with positive leading coefficients and
`deg f - deg g ∈ {0, 1}`. The forward theorem
`RealRooted.wronskian_eval_nonneg_of_strictInterl` shows that `g ≪ f` forces
`f' g - f g' ≥ 0` on `ℝ`. This file proves the converse under the root
multiplicity condition `mult_r f ≤ mult_r g + 1`, and shows that this
condition cannot be dropped.

* `RealRooted.strictInterl_of_wronskian_eval_nonneg`: the weak converse.
* `RealRooted.strictInterl_of_wronskian_eval_nonneg_of_nodup`: the special
  case of a polynomial `f` with simple roots.
* `RealRooted.strictInterl_iff_wronskian_eval_nonneg`: the resulting
  characterization of interlacing.
* `RealRooted.exists_wronskian_eval_nonneg_not_strictInterl`: the pair
  `f = (X - 1) ^ 3`, `g = X ^ 3` has a nonnegative Wronskian but does not
  interlace.

Common roots are removed recursively, since `W(hg, hf) = h ^ 2 W(g, f)`.
Without common roots, the multiplicity condition makes the roots of `f`
simple, so the Wronskian is positive at every root of `f`. The Bezout-matrix
certificate `RealRooted.wronskian_pos_of_pos_at_roots` then makes it positive
on all of `ℝ`, and the strict converses apply.
-/

open Polynomial

namespace RealRooted

/-- The weak converse when `f` and `g` have no common root. -/
private theorem strictInterl_of_wronskian_eval_nonneg_of_forall_not_isRoot {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hdeg_le : g.natDegree ≤ f.natDegree) (hdeg : f.natDegree ≤ g.natDegree + 1)
    (hmult : ∀ r, f.rootMultiplicity r ≤ g.rootMultiplicity r + 1)
    (hW : ∀ t, 0 ≤ (wronskian g f).eval t)
    (hcommon : ∀ r, f.IsRoot r → ¬ g.IsRoot r) : StrictInterl g f := by
  have hf₀ := hf_pos.ne_zero
  rcases Nat.eq_zero_or_pos f.natDegree with hf_deg₀ | hf_deg_pos
  · have hg_deg₀ : g.natDegree = 0 := by lia
    have hf_eq := eq_C_of_natDegree_eq_zero hf_deg₀
    have hg_eq := eq_C_of_natDegree_eq_zero hg_deg₀
    have hf_c : f.coeff 0 ≠ 0 := by
      have := hf_pos.ne'
      rwa [leadingCoeff, hf_deg₀] at this
    have hg_c : g.coeff 0 ≠ 0 := by
      have := hg_pos.ne'
      rwa [leadingCoeff, hg_deg₀] at this
    have hg_eq' : C (g.coeff 0 / f.coeff 0) * f = g := by
      conv_lhs => arg 2; rw [hf_eq]
      rw [← C_mul, div_mul_cancel₀ _ hf_c, ← hg_eq]
    rw [← hg_eq']
    exact (StrictInterl.refl hf₀ hf_splits).C_mul_left (div_ne_zero hg_c hf_c)
  · have hroot : ∀ r, f.IsRoot r →
        0 < (-g).derivative.eval r * f.eval r - (-g).eval r * f.derivative.eval r := by
      intro r hr
      have hg_r : g.eval r ≠ 0 := hcommon r hr
      have hf'_r : f.derivative.eval r ≠ 0 := by
        intro hd
        have h₁ := (one_lt_rootMultiplicity_iff_isRoot hf₀).mpr ⟨hr, hd⟩
        have h₂ := rootMultiplicity_eq_zero (hcommon r hr)
        have := hmult r
        lia
      have hWr := hW r
      rw [wronskian_eval_right_root g hr] at hWr
      rw [hr.eq_zero, derivative_neg, eval_neg, eval_neg]
      have := mul_ne_zero hg_r hf'_r
      have : 0 < g.eval r * f.derivative.eval r := lt_of_le_of_ne hWr this.symm
      linarith
    obtain ⟨d, hd⟩ : ∃ d, f.natDegree = d + 1 := ⟨f.natDegree - 1, by lia⟩
    have hWpos : ∀ t, 0 < f.derivative.eval t * g.eval t - f.eval t * g.derivative.eval t := by
      intro t
      have := wronskian_pos_of_pos_at_roots hf_splits hd (by rw [natDegree_neg]; lia) hroot t
      rw [derivative_neg, eval_neg, eval_neg] at this
      linarith
    rcases eq_or_lt_of_le hdeg_le with hsame | hsucc
    · exact (StrictInterlSameDegree.of_wronskian_pos hg_pos hf_pos rfl hsame.symm
        hg_splits hf_splits hWpos).toStrictInterl
    · exact strictInterl_of_wronskian_pos_succ hf_pos hg_pos (by lia) rfl hf_splits hg_splits
        hWpos

/-- **Weak Wronskian converse.** Let `f` and `g` be real-rooted with positive
leading coefficients and `deg f - deg g ∈ {0, 1}`. If every root of `f` has
multiplicity at most one more than its multiplicity as a root of `g`, and the
Wronskian `f' g - f g'` is nonnegative on `ℝ`, then `g ≪ f`. -/
theorem strictInterl_of_wronskian_eval_nonneg {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hdeg_le : g.natDegree ≤ f.natDegree) (hdeg : f.natDegree ≤ g.natDegree + 1)
    (hmult : ∀ r, f.rootMultiplicity r ≤ g.rootMultiplicity r + 1)
    (hW : ∀ t, 0 ≤ (wronskian g f).eval t) : StrictInterl g f := by
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f g with
  | h n ih =>
    subst hn
    by_cases hcommon : ∃ r, f.IsRoot r ∧ g.IsRoot r
    · obtain ⟨r, hrf, hrg⟩ := hcommon
      have hf_factor : (X - C r) * (f /ₘ (X - C r)) = f :=
        mul_divByMonic_eq_iff_isRoot.mpr hrf
      have hg_factor : (X - C r) * (g /ₘ (X - C r)) = g :=
        mul_divByMonic_eq_iff_isRoot.mpr hrg
      have hf₁_pos := hf_pos.divByMonic_X_sub_C hrf
      have hg₁_pos := hg_pos.divByMonic_X_sub_C hrg
      have hf_deg_pos : 0 < f.natDegree :=
        natDegree_pos_iff_degree_pos.mpr (degree_pos_of_root hf_pos.ne_zero hrf)
      have hg_deg_pos : 0 < g.natDegree :=
        natDegree_pos_iff_degree_pos.mpr (degree_pos_of_root hg_pos.ne_zero hrg)
      have hf₁_splits : (f /ₘ (X - C r)).Splits := by
        rw [← splits_X_sub_C_mul_iff (a := r), hf_factor]
        exact hf_splits
      have hg₁_splits : (g /ₘ (X - C r)).Splits := by
        rw [← splits_X_sub_C_mul_iff (a := r), hg_factor]
        exact hg_splits
      have hmult₁ : ∀ s, (f /ₘ (X - C r)).rootMultiplicity s ≤
          (g /ₘ (X - C r)).rootMultiplicity s + 1 := by
        intro s
        have h := hmult s
        rw [← hf_factor, ← hg_factor,
          rootMultiplicity_mul (by rw [hf_factor]; exact hf_pos.ne_zero),
          rootMultiplicity_mul (by rw [hg_factor]; exact hg_pos.ne_zero)] at h
        lia
      have hW₁ : ∀ t, 0 ≤ (wronskian (g /ₘ (X - C r)) (f /ₘ (X - C r))).eval t := by
        refine eval_nonneg_of_forall_ne (r := r) fun t ht ↦ ?_
        have h := hW t
        rw [← hf_factor, ← hg_factor, wronskian_mul_both, eval_mul, eval_pow] at h
        have hpos : 0 < ((X - C r).eval t) ^ 2 := by
          rw [eval_sub, eval_X, eval_C]
          exact lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (sub_ne_zero.mpr ht)).symm
        exact (mul_nonneg_iff_of_pos_left hpos).mp h
      have hrec := ih (f /ₘ (X - C r)).natDegree
        (by rw [natDegree_divByMonic_X_sub_C]; lia) hf₁_pos hg₁_pos hf₁_splits hg₁_splits
        (by rw [natDegree_divByMonic_X_sub_C, natDegree_divByMonic_X_sub_C]; lia)
        (by rw [natDegree_divByMonic_X_sub_C, natDegree_divByMonic_X_sub_C]; lia)
        hmult₁ hW₁ rfl
      exact hrec.of_cofactor_of_common_root hrf hrg
    · push Not at hcommon
      exact strictInterl_of_wronskian_eval_nonneg_of_forall_not_isRoot hf_pos hg_pos
        hf_splits hg_splits hdeg_le hdeg hmult hW hcommon

/-- **Weak Wronskian converse, simple roots.** If `f` and `g` are
real-rooted with positive leading coefficients, `deg f - deg g ∈ {0, 1}`,
`f` has only simple roots, and `f' g - f g' ≥ 0` on `ℝ`, then `g ≪ f`. -/
theorem strictInterl_of_wronskian_eval_nonneg_of_nodup {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hdeg_le : g.natDegree ≤ f.natDegree) (hdeg : f.natDegree ≤ g.natDegree + 1)
    (hf_nodup : f.roots.Nodup)
    (hW : ∀ t, 0 ≤ (wronskian g f).eval t) : StrictInterl g f := by
  refine strictInterl_of_wronskian_eval_nonneg hf_pos hg_pos hf_splits hg_splits hdeg_le hdeg
    (fun r ↦ ?_) hW
  have := Multiset.nodup_iff_count_le_one.mp hf_nodup r
  rw [count_roots] at this
  lia

/-- **Wronskian criterion for interlacing.** Let `f` and `g` be real-rooted
with positive leading coefficients and `deg f - deg g ∈ {0, 1}`. Then `g ≪ f`
if and only if `f' g - f g' ≥ 0` on `ℝ` and every root of `f` has
multiplicity at most one more than its multiplicity as a root of `g`. -/
theorem strictInterl_iff_wronskian_eval_nonneg {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hdeg_le : g.natDegree ≤ f.natDegree) (hdeg : f.natDegree ≤ g.natDegree + 1) :
    StrictInterl g f ↔
      (∀ t, 0 ≤ (wronskian g f).eval t) ∧
        ∀ r, f.rootMultiplicity r ≤ g.rootMultiplicity r + 1 :=
  ⟨fun h ↦ ⟨wronskian_eval_nonneg_of_strictInterl hf_pos hg_pos h,
      fun r ↦ (h.rootMultiplicity_le_add_one r).1⟩,
    fun h ↦ strictInterl_of_wronskian_eval_nonneg hf_pos hg_pos hf_splits hg_splits hdeg_le
      hdeg h.2 h.1⟩

/-- **The multiplicity condition is needed.** The polynomials
`f = (X - 1) ^ 3` and `g = X ^ 3` are real-rooted, monic and of equal degree,
and `f' g - f g' = 3 X ^ 2 (X - 1) ^ 2 ≥ 0`, but `g ≪ f` fails. -/
theorem exists_wronskian_eval_nonneg_not_strictInterl :
    ∃ f g : ℝ[X], HasPosLeadingCoeff f ∧ HasPosLeadingCoeff g ∧ f.Splits ∧ g.Splits ∧
      g.natDegree = f.natDegree ∧ (∀ t, 0 ≤ (wronskian g f).eval t) ∧
        ¬ StrictInterl g f := by
  refine ⟨(X - C 1) ^ 3, X ^ 3, ?_, ?_, (Splits.X_sub_C 1).pow 3, Splits.X_pow 3, ?_,
    fun t ↦ ?_, fun h ↦ ?_⟩
  · change 0 < ((X - C 1 : ℝ[X]) ^ 3).leadingCoeff
    rw [((monic_X_sub_C (1 : ℝ)).pow 3).leadingCoeff]
    exact one_pos
  · simp [HasPosLeadingCoeff]
  · rw [natDegree_pow, natDegree_pow, natDegree_X_sub_C, natDegree_X]
  · have : (wronskian (X ^ 3) ((X - C 1) ^ 3)).eval t = 3 * (t * (t - 1)) ^ 2 := by
      simp only [wronskian, derivative_pow, derivative_X, derivative_sub, derivative_C,
        eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_zero]
      ring
    rw [this]
    positivity
  · have hroot := h.isRoot_of_one_lt_rootMultiplicity (r := 1)
      (by rw [rootMultiplicity_X_sub_C_pow]; lia)
    simp at hroot

end RealRooted
