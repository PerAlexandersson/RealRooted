import RealRooted.MaWang.Weak.Successor
import RealRooted.WagnerRightSum.Sign

/-!
# Interlacing from derivative signs at simple roots

Let `f` be real-rooted with simple roots and positive leading coefficient.  The signs of a
polynomial `F` at the roots of `f`, measured against the derivative `f'`, determine whether
`f` is interlaced by `F`: if `F(r) f'(r) ≤ 0` at every root `r` of `f` and
`deg f ≤ deg F ≤ deg f + 1`, then `f ≪ F`.

The derivative `f'` serves as a canonical interlacer of `f` (Rolle), and it does not vanish
at the roots of `f`.  This lets the weak-sign Ma--Wang and Liu--Wang criteria avoid both a
distinguished interlacer and a no-common-root hypothesis.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- At a root of a polynomial with no repeated roots, the derivative does not vanish. -/
private lemma eval_derivative_ne_zero_of_roots_nodup {f : ℝ[X]} (hf_ne : f ≠ 0)
    (hf_nodup : f.roots.Nodup) {r : ℝ} (hr : f.IsRoot r) :
    f.derivative.eval r ≠ 0 := by
  intro hder
  have hle : f.rootMultiplicity r ≤ 1 := by
    rw [← count_roots]
    exact Multiset.nodup_iff_count_le_one.mp hf_nodup r
  have hlt : 1 < f.rootMultiplicity r :=
    (one_lt_rootMultiplicity_iff_isRoot hf_ne).mpr ⟨hr, hder⟩
  lia

/-- A degree-zero real polynomial is interlaced by any nonzero polynomial of degree at most
one. -/
private lemma strictInterl_of_natDegree_eq_zero {f F : ℝ[X]} (hf_ne : f ≠ 0)
    (hf_deg : f.natDegree = 0) (hF_ne : F ≠ 0) (hF_deg : F.natDegree ≤ 1) :
    StrictInterl f F := by
  have hf_splits : f.Splits := Splits.of_natDegree_le_one (by lia)
  have hF_splits : F.Splits := Splits.of_natDegree_le_one hF_deg
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hF_deg with hF0 | hF1
  · have hc : f.coeff 0 ≠ 0 := by
      intro h0
      exact hf_ne (by rw [eq_C_of_natDegree_eq_zero hf_deg, h0, C_0])
    have hd : F.coeff 0 ≠ 0 := by
      intro h0
      exact hF_ne (by rw [eq_C_of_natDegree_eq_zero hF0, h0, C_0])
    have hF_eq : F = C (F.coeff 0 / f.coeff 0) * f := by
      rw [eq_C_of_natDegree_eq_zero hF0, eq_C_of_natDegree_eq_zero hf_deg, ← C_mul,
        coeff_C_zero, coeff_C_zero, div_mul_cancel₀ _ hc]
    rw [hF_eq]
    exact (StrictInterl.refl hf_ne hf_splits).C_mul_right (div_ne_zero hd hc)
  · exact StrictInterl.of_degree_zero_right_of_degree_one hf_ne hf_splits hF_ne hF_splits
      hf_deg hF1

/-- Every interlacer `g ≪ f` with positive leading coefficients has the sign of `f'` at the
roots of `f`: `g(r) f'(r) ≥ 0`.  At a root of `f` this is the value of the Wronskian
`W(g, f) = g f' - g' f`. -/
theorem StrictInterl.eval_mul_eval_derivative_nonneg {g f : ℝ[X]} (hgf : StrictInterl g f)
    (hg_pos : HasPosLeadingCoeff g) (hf_pos : HasPosLeadingCoeff f) {r : ℝ}
    (hr : f.IsRoot r) :
    0 ≤ g.eval r * f.derivative.eval r := by
  have hdeg : f.natDegree ≠ 0 :=
    (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_root hf_pos.ne_zero hr)).ne'
  exact eval_mul_eval_nonneg_of_strictInterl_right hgf
    (interlaces_derivative_of_pos_natDegree hf_pos.ne_zero hgf.2.1.2 hf_pos
      (by lia)).toStrictInterl hg_pos (hf_pos.derivative hdeg) hr

/-- **Interlacing from derivative signs.**  Let `f` be real-rooted with simple roots and
positive leading coefficient, and let `F` have positive leading coefficient and degree
`deg f` or `deg f + 1`.  If `F(r) f'(r) ≤ 0` at every root `r` of `f`, then `f ≪ F`
(`StrictInterl f F`).

Common roots of `f` and `F` are allowed.  The real-rootedness of `F` is part of the
conclusion: it follows by perturbing `F` to `F - δ f'`, whose signs at the roots of `f` are
strict. -/
theorem strictInterl_of_eval_mul_derivative_nonpos {f F : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hf_splits : f.Splits) (hf_nodup : f.roots.Nodup)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_lo : f.natDegree ≤ F.natDegree) (hdeg_hi : F.natDegree ≤ f.natDegree + 1)
    (hsign : ∀ r, f.IsRoot r → F.eval r * f.derivative.eval r ≤ 0) :
    StrictInterl f F := by
  by_cases hdeg0 : f.natDegree = 0
  · exact strictInterl_of_natDegree_eq_zero hf_pos.ne_zero hdeg0 hF_pos.ne_zero (by lia)
  have hgf : Interlaces f.derivative f :=
    interlaces_derivative_of_pos_natDegree hf_pos.ne_zero hf_splits hf_pos (by lia)
  have hg_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative hdeg0
  have hder_ne : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0 := fun _ hr ↦
    eval_derivative_ne_zero_of_roots_nodup hf_pos.ne_zero hf_nodup hr
  have hF_rr : F ≠ 0 ∧ F.Splits := by
    refine MaWangInternal.isRealRooted_of_interlaces_sub_C_mul_of_forall_pos hgf hF_pos hdeg_lo
      fun {δ} hδ ↦ ?_
    have hG_pos : HasPosLeadingCoeff (F - C δ * f.derivative) :=
      hasPosLeadingCoeff_sub_C_mul_of_interlaces_degree_lower_bound hgf hdeg_lo hF_pos δ
    have hG_deg : (F - C δ * f.derivative).natDegree = F.natDegree :=
      natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound hgf hdeg_lo δ
    have hG_sign : ∀ r, f.IsRoot r →
        (F - C δ * f.derivative).eval r * f.derivative.eval r < 0 := by
      intro r hr
      have hne := hder_ne r hr
      have hsq : 0 < f.derivative.eval r ^ 2 := by positivity
      have hFr := hsign r hr
      simp only [eval_sub, eval_mul, eval_C]
      nlinarith
    have hG : StrictInterl f (F - C δ * f.derivative) := by
      rcases Nat.le_and_le_add_one_iff.mp ⟨hdeg_lo, hdeg_hi⟩ with hsame | hsucc
      · exact strictInterl_of_interlaces_eval_mul_neg_same hgf hg_pos hG_pos
          (hG_deg.trans hsame) hG_sign
      · exact strictInterl_of_interlaces_eval_mul_neg_succ hgf hg_pos hG_pos
          (hG_deg.trans hsucc) hG_sign
    exact hG.2.1
  exact strictInterl_of_interlaces_eval_mul_nonpos_of_no_common hgf hg_pos hF_rr.1 hF_rr.2
    hF_pos hdeg_lo hdeg_hi (fun r hr hder ↦ hder_ne r hr hder) hsign

end RealRooted
