import RealRooted.LiuOppositeSigns.XSub.SplittingTools

/-!
# No-common-root API for Liu's opposite-sign theorem

This module isolates the reusable no-common-root predicate and its elementary
endpoint consequences from the analytic crossing argument.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The two polynomials have no common real root.  This is the reduction
regime used explicitly in Liu's proof of Theorem 2.1 before the largest-root
case split. -/
def NoCommonRoots (f g : ℝ[X]) : Prop :=
  ∀ r : ℝ, f.IsRoot r → ¬ g.IsRoot r

theorem NoCommonRoots.symm {f g : ℝ[X]} (h : NoCommonRoots f g) :
    NoCommonRoots g f := by
  intro r hgr hfr
  exact (h r hfr) hgr

/-- A nonzero right-family member has no root at a left endpoint root when the
endpoint polynomials have no common root. -/
theorem NoCommonRoots.rightFamily_not_isRoot_of_left_root
    {f g : ℝ[X]} (h : NoCommonRoots f g) {μ x : ℝ}
    (hμ : μ ≠ 0) (hf : f.IsRoot x) :
    ¬ (f + C μ * g).IsRoot x := by
  simpa [IsRoot, hf.eq_zero, hμ] using h x hf

/-- A right-family member has no root at a right endpoint root when the
endpoint polynomials have no common root. -/
theorem NoCommonRoots.rightFamily_not_isRoot_of_right_root
    {f g : ℝ[X]} (h : NoCommonRoots f g) {μ x : ℝ}
    (hg : g.IsRoot x) :
    ¬ (f + C μ * g).IsRoot x := by
  have hf : ¬ f.IsRoot x := h.symm x hg
  have hf_eval_ne : f.eval x ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero f x).mp hf
  have hg_eval : g.eval x = 0 := by simpa [Polynomial.IsRoot.def] using hg
  have hq_eval_ne : (f + C μ * g).eval x ≠ 0 := by
    simpa [eval_add, eval_mul, eval_C, hg_eval] using hf_eval_ne
  exact
    (Polynomial.not_isRoot_iff_eval_ne_zero (f + C μ * g) x).mpr hq_eval_ne

/-- If the endpoints of `[a, b]` are roots of `f`, the polynomials have no
common roots, and `g` has no roots in `(a, b)`, then `g` has no roots on the
closed interval `[a, b]`. -/
theorem NoCommonRoots.right_not_isRoot_Icc_of_left_roots
    {f g : ℝ[X]} (h : NoCommonRoots f g) {a b : ℝ}
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z) :
    ∀ z ∈ Set.Icc a b, ¬ g.IsRoot z := by
  intro z hz hgz
  by_cases hza : z = a
  · exact (h a hfa) (by simpa [hza] using hgz)
  have haz : a < z := lt_of_le_of_ne hz.1 (Ne.symm hza)
  by_cases hzb : z = b
  · exact (h b hfb) (by simpa [hzb] using hgz)
  have hzb_lt : z < b := lt_of_le_of_ne hz.2 hzb
  exact hg_no z haz hzb_lt hgz

/-- If two roots of `p` bracket an odd number of roots of a nonzero splitting
polynomial `q`, and `p` and `q` have no common roots, then the x-subtraction
pencil has an interior root in the bracket. -/
theorem NoCommonRoots.exists_isRoot_between_X_mul_sub_C_mul_of_odd_right_roots
    {p q : ℝ[X]} (h : NoCommonRoots p q) (hq_ne : q ≠ 0)
    (hq : q.Splits) {a b μ : ℝ} (hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) (hμ : μ ≠ 0)
    (hodd : Odd (q.roots.filter (fun x => a < x ∧ x < b)).card) :
    ∃ c, a < c ∧ c < b ∧ (X * p - C μ * q).IsRoot c :=
  exists_isRoot_between_X_mul_sub_C_mul_of_left_roots_odd_right_roots
    hq_ne hq hab ha hb hμ hodd (h a ha) (h b hb)

/-- Failure of the no-common-root predicate produces an explicit common root. -/
theorem exists_common_root_of_not_noCommonRoots {f g : ℝ[X]}
    (hno : ¬ NoCommonRoots f g) :
    ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r := by
  by_contra hmissing
  exact hno (by
    intro r hfr hgr
    exact hmissing ⟨r, hfr, hgr⟩)

end LiuOppositeSigns
end RealRooted
