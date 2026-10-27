module

public import RealRooted.MaWang.Weak.DerivativeSign
public import RealRooted.SimpleRoots

/-!
# Strict interlacing from critical signs

A split polynomial `h` of degree `n` and a polynomial `g` of degree `n + 1`,
both with positive leading coefficient, strictly interlace as soon as
`g * h'` is negative at every root of `h`.  The sign condition also forces
both polynomials to have simple roots and no common root.  This packages the
successor-degree Sturm step of `strictInterl_of_interlaces_eval_mul_neg_succ`
for callers that supply only the strict critical signs, and
`strictInterl_of_eval_mul_derivative_neg` gives the same conclusion when `g` has the same degree
as `h` or the successor degree (Liu–Wang, *A unified approach to polynomial sequences with only
real zeros*, Theorem 2.1; Ma–Wang, *q-Eulerian polynomials and polynomials with only real
zeros*, Theorem 2).
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

private lemma roots_nodup_of_eval_mul_derivative_neg {f F : ℝ[X]} (hf_ne : f ≠ 0)
    (hsign : ∀ r, f.IsRoot r → F.eval r * f.derivative.eval r < 0) :
    f.roots.Nodup := by
  refine Multiset.nodup_iff_count_le_one.mpr fun r ↦ ?_
  rw [count_roots]
  by_contra hle
  have hmult : 1 < f.rootMultiplicity r := by lia
  obtain ⟨hr, hder⟩ := (one_lt_rootMultiplicity_iff_isRoot hf_ne).mp hmult
  have hstrict := hsign r hr
  rw [hder.eq_zero, mul_zero] at hstrict
  exact (lt_irrefl 0) hstrict

/-- A successor-degree critical-sign step gives strict interlacing, splitness,
and simple roots.  The sign hypothesis itself forces the lower polynomial to
have simple roots, so no separate simplicity hypothesis is needed.

For `n = 0`, the sign condition is vacuous; the conclusion instead uses the
constant--linear interlacing theorem. -/
theorem strictInterl_package_of_eval_mul_derivative_neg_succ
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
  have hdeg : g.natDegree = h.natDegree + 1 := by
    calc
      g.natDegree = n + 1 := hg_degree
      _ = h.natDegree + 1 := by rw [hh_degree]
  have hstrict : StrictInterl h g := by
    cases n with
    | zero =>
        apply StrictInterl.of_natDegree_eq_zero_left hh_pos.ne_zero hh_degree hg_pos.ne_zero
        rw [hg_degree]
    | succ n =>
        apply strictInterl_of_eval_mul_derivative_nonpos hh_pos hh_splits
          (roots_nodup_of_eval_mul_derivative_neg hh_pos.ne_zero hsign) hg_pos
          (by lia) (by lia)
        exact fun r hr ↦ (hsign r hr).le
  have hinter : Interlaces h g := hstrict.toInterlaces hdeg.symm
  have hsimp := hstrict.hasSimpleRoots_of_no_common_root hno_common
  exact ⟨hstrict, hinter, hstrict.2.1.2, hsimp.1, hsimp.2,
    fun r hr hgr ↦ hno_common r ⟨hr, hgr⟩⟩

/-- Strict critical signs imply strict interlacing in the same-or-successor
degree range.  The positive leading coefficients fix the orientation, and
the strict sign hypothesis is `F(r) * f'(r) < 0` at every root of `f`. -/
theorem strictInterl_of_eval_mul_derivative_neg
    {f F : ℝ[X]}
    (hf : f.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hF_pos : HasPosLeadingCoeff F)
    (hdegf : f.natDegree ≠ 0)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hdeg_hi : F.natDegree ≤ f.natDegree + 1)
    (hsign : ∀ r, f.IsRoot r →
      F.eval r * f.derivative.eval r < 0) :
    StrictInterl f F := by
  have hf_ne : f ≠ 0 := by
    intro hf_zero
    subst f
    simp at hdegf
  exact strictInterl_of_eval_mul_derivative_nonpos hf_pos hf
    (roots_nodup_of_eval_mul_derivative_neg hf_ne hsign) hF_pos hdeg_lo hdeg_hi
    fun r hr ↦ (hsign r hr).le

/- Same-degree regression: `X + 1` strictly interlaces `X - 1`, although the right polynomial
has a negative value at zero, so no endpoint sign belongs among the hypotheses. -/
example : StrictInterl (X + C (1 : ℝ)) (X - C (1 : ℝ)) := by
  have hf_splits : (X + C (1 : ℝ)).Splits := Polynomial.Splits.X_add_C _
  have hf_pos : HasPosLeadingCoeff (X + C (1 : ℝ)) :=
    hasPosLeadingCoeff_of_monic (monic_X_add_C _)
  have hF_pos : HasPosLeadingCoeff (X - C (1 : ℝ)) :=
    hasPosLeadingCoeff_of_monic (monic_X_sub_C _)
  have hf_degree : (X + C (1 : ℝ)).natDegree = 1 := by simp
  have hF_degree : (X - C (1 : ℝ)).natDegree = 1 := by
    simpa [sub_eq_add_neg] using
      (Polynomial.natDegree_X_add_C (x := (-1 : ℝ)))
  apply strictInterl_of_eval_mul_derivative_neg hf_splits hf_pos hF_pos (by simp)
  · rw [hf_degree, hF_degree]
  · rw [hf_degree, hF_degree]
    simp
  intro r hr
  rw [Polynomial.IsRoot.def] at hr
  simp only [eval_add, eval_X, eval_C] at hr
  have hr_eq : r = -1 := by linarith
  subst r
  norm_num [derivative_add, derivative_X, derivative_C]

end RealRooted
