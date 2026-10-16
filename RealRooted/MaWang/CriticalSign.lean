module

public import RealRooted.MaWang.Strong
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

public noncomputable section

open Polynomial

namespace RealRooted

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
  cases n with
  | zero =>
      have hg_degree_one : g.natDegree = 1 := by simpa using hg_degree
      have hh_const : h = C (h.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hh_degree
      have hh_coeff_ne : h.coeff 0 ≠ 0 := by
        intro hh_coeff_zero
        apply hh_pos.ne_zero
        rw [hh_const, hh_coeff_zero]
        simp
      have hinter : Interlaces h g := by
        rw [hh_const]
        exact interlaces_C_linear hh_coeff_ne hg_degree_one
      have hstrict : StrictInterl h g := hinter.toStrictInterl
      have hsimp := hstrict.hasSimpleRoots_of_no_common_root hno_common
      exact ⟨hstrict, hinter, (isRealRooted_of_degree_one hg_degree_one).2,
        hsimp.1, hsimp.2, fun r hr hgr => hno_common r ⟨hr, hgr⟩⟩
  | succ n =>
      have hh_degree_pos : 1 ≤ h.natDegree := by
        rw [hh_degree]
        exact Nat.succ_le_succ (Nat.zero_le n)
      have hg_degree_succ : g.natDegree = h.natDegree + 1 := by
        calc
          g.natDegree = n.succ + 1 := hg_degree
          _ = h.natDegree + 1 := by rw [hh_degree]
      have hder : Interlaces h.derivative h :=
        interlaces_derivative_of_pos_natDegree hh_pos.ne_zero hh_splits hh_pos
          hh_degree_pos
      have hder_pos : HasPosLeadingCoeff h.derivative :=
        hh_pos.derivative (by rw [hh_degree]; exact Nat.succ_ne_zero _)
      have hstrict : StrictInterl h g :=
        strictInterl_of_interlaces_eval_mul_neg_succ hder hder_pos hg_pos hg_degree_succ hsign
      have hinter : Interlaces h g :=
        hstrict.toInterlaces hg_degree_succ.symm
      have hsimp := hstrict.hasSimpleRoots_of_no_common_root hno_common
      exact ⟨hstrict, hinter, hstrict.2.1.2, hsimp.1, hsimp.2,
        fun r hr hgr => hno_common r ⟨hr, hgr⟩⟩

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
  have hder : Interlaces f.derivative f :=
    interlaces_derivative_of_pos_natDegree hf_pos.ne_zero hf hf_pos (by lia)
  have hder_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative hdegf
  have hcases : F.natDegree = f.natDegree ∨
      F.natDegree = f.natDegree + 1 := by
    lia
  rcases hcases with hsame | hsucc
  · exact strictInterl_of_interlaces_eval_mul_neg_same hder hder_pos hF_pos hsame hsign
  · exact strictInterl_of_interlaces_eval_mul_neg_succ hder hder_pos hF_pos hsucc hsign

/-- A positive weighted critical sign gives strict interlacing when all roots
of `f` are nonpositive.  At a root `r`, the strict product excludes `r = 0`,
so `0 < F(r) * (r * f'(r))` is exactly the unweighted negative critical sign.
-/
theorem strictInterl_of_eval_mul_derivative_neg_of_roots_nonpos
    {f F : ℝ[X]}
    (hf : f.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hF_pos : HasPosLeadingCoeff F)
    (hdegf : f.natDegree ≠ 0)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hdeg_hi : F.natDegree ≤ f.natDegree + 1)
    (hroots : ∀ r, f.IsRoot r → r ≤ 0)
    (hsignX : ∀ r, f.IsRoot r →
      0 < F.eval r * (r * f.derivative.eval r)) :
    StrictInterl f F := by
  apply strictInterl_of_eval_mul_derivative_neg hf hf_pos hF_pos hdegf hdeg_lo hdeg_hi
  intro r hr
  have hr_nonpos : r ≤ 0 := hroots r hr
  have hr_neg : r < 0 := by
    by_contra hr_not_neg
    have hr_nonneg : 0 ≤ r := le_of_not_gt hr_not_neg
    have hr_zero : r = 0 := le_antisymm hr_nonpos hr_nonneg
    subst r
    have hzero := hsignX 0 hr
    simp at hzero
  have hweighted : 0 < r * (F.eval r * f.derivative.eval r) := by
    calc
      0 < F.eval r * (r * f.derivative.eval r) := hsignX r hr
      _ = r * (F.eval r * f.derivative.eval r) := by ring
  by_contra hnot
  have hnonneg : 0 ≤ F.eval r * f.derivative.eval r := le_of_not_gt hnot
  have hnonpos : r * (F.eval r * f.derivative.eval r) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hr_neg.le hnonneg
  exact (not_lt_of_ge hnonpos) hweighted

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
