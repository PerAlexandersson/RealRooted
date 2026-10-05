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
