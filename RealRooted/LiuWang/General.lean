import RealRooted.MaWang.Weak.DerivativeSign

/-!
# The Liu--Wang criterion in full generality

Liu and Wang (2007, Theorem 2.1): let `g ≪ f`, where `g` has positive leading coefficient, and
put `F = a f + b g` with `deg f ≤ deg F ≤ deg f + 1` and positive leading coefficient.  If `b`
is nonpositive at the roots of `f`, then `f ≪ F`.

Here `g ≪ f` may have either shape (`deg g = deg f` or `deg g + 1 = deg f`), and `f`, `g` may
have common and repeated roots.  The proof removes common roots of `f` and `g` until `f` has
simple roots, and then applies `strictInterl_of_eval_mul_derivative_nonpos`: the interlacers
`g` and `f'` of `f` agree in sign at the roots of `f`, so `g(r) f'(r) ≥ 0` and
`F(r) f'(r) = b(r) g(r) f'(r) ≤ 0`.
-/

open Polynomial

noncomputable section

namespace RealRooted.LiuWang

/-- The Liu--Wang criterion when `f` also has positive leading coefficient. -/
private theorem strictInterl_mul_add_mul_of_eval_nonpos_of_pos {f g a b : ℝ[X]}
    (hgf : StrictInterl g f) (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hb : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    StrictInterl f (a * f + b * g) := by
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f g with
  | h n ih =>
    subst hn
    by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
    · have hnodup : f.roots.Nodup := by
        refine Multiset.nodup_iff_count_le_one.mpr fun r ↦ ?_
        rw [count_roots]
        by_cases hr : f.IsRoot r
        · have hg0 := rootMultiplicity_eq_zero (hno r hr)
          have := (hgf.rootMultiplicity_bounds r).2
          lia
        · rw [rootMultiplicity_eq_zero hr]
          lia
      refine strictInterl_of_eval_mul_derivative_nonpos hf_pos hgf.2.1.2 hnodup hF_pos hdeg_lo
        hdeg_hi fun r hr ↦ ?_
      have hW := hgf.eval_mul_eval_derivative_nonneg hg_pos hf_pos hr
      have hFr : (a * f + b * g).eval r = b.eval r * g.eval r := by
        simp [hr.eq_zero]
      rw [hFr, mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg (hb r hr) hW
    push Not at hno
    obtain ⟨r, hrf, hrg⟩ := hno
    obtain ⟨qf, rfl⟩ := dvd_iff_isRoot.mpr hrf
    obtain ⟨qg, rfl⟩ := dvd_iff_isRoot.mpr hrg
    have hF_eq : a * ((X - C r) * qf) + b * ((X - C r) * qg) =
        (X - C r) * (a * qf + b * qg) := by
      ring
    rw [hF_eq] at hF_pos hdeg_lo hdeg_hi ⊢
    have hqf_pos : HasPosLeadingCoeff qf := hasPosLeadingCoeff_of_X_sub_C_mul hf_pos
    have hqF_pos : HasPosLeadingCoeff (a * qf + b * qg) := hasPosLeadingCoeff_of_X_sub_C_mul hF_pos
    have hdeg_mul : ∀ p : ℝ[X], p ≠ 0 → ((X - C r) * p).natDegree = p.natDegree + 1 :=
      fun p hp ↦ by rw [natDegree_mul (X_sub_C_ne_zero r) hp, natDegree_X_sub_C, add_comm]
    rw [hdeg_mul _ hqf_pos.ne_zero] at hdeg_lo hdeg_hi ih
    rw [hdeg_mul _ hqF_pos.ne_zero] at hdeg_lo hdeg_hi
    have hq : StrictInterl qf (a * qf + b * qg) :=
      ih qf.natDegree (by lia) hgf.of_mul_X_sub_C_both hqf_pos
        (hasPosLeadingCoeff_of_X_sub_C_mul hg_pos) hqF_pos (by lia) (by lia)
        (fun s hs ↦ hb s (by simp [hs.eq_zero])) rfl
    exact hq.mul_common_factor (X_sub_C_ne_zero r) (Splits.X_sub_C r)

/-- **Liu--Wang criterion** (Liu--Wang 2007, Theorem 2.1).  Let `g ≪ f` (`StrictInterl g f`,
of either degree shape) with `g` of positive leading coefficient, and let
`F = a f + b g` have positive leading coefficient and degree `deg f` or `deg f + 1`.  If `b` is
nonpositive at every root of `f`, then `f ≪ F`.

Common and repeated roots of `f` and `g` are allowed, and the sign of the leading coefficient
of `f` is arbitrary. -/
theorem strictInterl_mul_add_mul_of_eval_nonpos {f g a b : ℝ[X]}
    (hgf : StrictInterl g f) (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hb : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    StrictInterl f (a * f + b * g) := by
  have hf_ne : f ≠ 0 := hgf.2.1.1
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hf_ne) with hneg | hpos
  · have hF_eq : a * f + b * g = -a * -f + b * g := by ring
    have hnf_pos : HasPosLeadingCoeff (-f) := by
      simpa [HasPosLeadingCoeff, leadingCoeff_neg] using hneg
    have hgnf : StrictInterl g (-f) := by
      simpa using hgf.C_mul_right (a := -1) (by norm_num)
    rw [hF_eq] at hF_pos hdeg_lo hdeg_hi ⊢
    have h := strictInterl_mul_add_mul_of_eval_nonpos_of_pos hgnf hnf_pos hg_pos hF_pos
      (by rwa [natDegree_neg]) (by rwa [natDegree_neg])
      (fun r hr ↦ hb r (by simpa using hr))
    simpa using h.C_mul_left (a := -1) (by norm_num)
  · exact strictInterl_mul_add_mul_of_eval_nonpos_of_pos hgf hpos hg_pos hF_pos hdeg_lo hdeg_hi hb

end RealRooted.LiuWang
