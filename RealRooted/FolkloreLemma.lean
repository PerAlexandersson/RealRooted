import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Derivative
import RealRooted.Wagner
import RealRooted.ObreschkoffConverse
import RealRooted.CombinatorialExamples.Motzkin
-- import RealRooted.AffineDerivative  -- uncomment when AffineDerivative is built

/-!
# Folklore lemma for subtracting `X * g`

This file studies the standard claim that, under suitable monic and
nonpositive-root hypotheses, interlacing is preserved by the transformation
`(f, g) ↦ f - X * g`.

At a root `r` of `f`, `(f - X * g)(r) = -r * g(r)`.  Since the roots are
nonpositive, this has the same sign as `g(r)`.  The expected interlacing
conclusion then follows from sign alternation.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- At a root `r` of `f`, `(f - X*g)(r) = -r * g(r)`. -/
lemma eval_sub_X_mul_at_root {f g : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) :
    (f - X * g).eval r = -r * g.eval r := by
  simp [eval_sub, eval_mul, eval_X, IsRoot.def.mp hr]

/-- If `g ⊳ f` (differ-by-1), monic, all roots ≤ 0, then `(f - X*g) ≪₀ f`.
Again this is stated in the zero-aware convention to allow complete
cancellation. -/
theorem prec_sub_X_mul_left {f g : ℝ[X]}
    (hgf : Prec g f)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree + 1 = f.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    Prec0 (f - X * g) f := by
  set q : ℝ[X] := f - X * g
  by_cases hq0 : q = 0
  · simpa [q, hq0] using prec0_zero_left f
  · have hg : IsRealRooted g := hgf.1
    have hf : IsRealRooted f := hgf.2.1
    have hg_pos : HasPosLeadingCoeff g := by
      unfold HasPosLeadingCoeff
      simp [hg_monic.leadingCoeff]
    have hf_pos : HasPosLeadingCoeff f := by
      unfold HasPosLeadingCoeff
      simp [hf_monic.leadingCoeff]
    have hprec_fXg : Prec f (X * g) := by
      exact
        (prec_iff_prec_mul_X_of_roots_nonpos
          (f := g) (g := f) hg hf hg_pos hf_pos hg_nonpos hf_nonpos hdeg).mp hgf
    have hall_fXg : AllComboRealRooted f (X * g) :=
      allComboRealRooted_of_prec hprec_fXg
    have hall_qf : AllComboRealRooted q f := by
      intro α β
      have hrew :
          C α * q + C β * f =
            C (α + β) * f + C (-α) * (X * g) := by
        calc
          C α * q + C β * f
              = C α * (f - X * g) + C β * f := by simp [q]
          _ = (C α * f - C α * (X * g)) + C β * f := by simp [mul_sub]
          _ = C (α + β) * f + C (-α) * (X * g) := by
                ext n
                have hcf : (C α * f + C β * f).coeff n = α * f.coeff n + β * f.coeff n := by
                  rw [coeff_add, coeff_C_mul, coeff_C_mul]
                calc
                  (C α * f - C α * (X * g) + C β * f).coeff n
                      = α * f.coeff n - α * (X * g).coeff n + β * f.coeff n := by
                          rw [coeff_add, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_C_mul]
                  _ = -(α * (X * g).coeff n) + (α * f.coeff n + β * f.coeff n) := by ring
                  _ = -(α * (X * g).coeff n) + (C α * f + C β * f).coeff n := by
                        rw [hcf]
                  _ = (C (α + β) * f + C (-α) * (X * g)).coeff n := by
                        rw [hcf, coeff_add, coeff_C_mul, coeff_C_mul]
                        ring
      simpa [hrew] using hall_fXg (α + β) (-α)
    have hq : IsRealRooted q := by
      rcases hall_qf 1 0 with hzero | hrr
      · exact False.elim (hq0 (by simpa [q] using hzero))
      · simpa using hrr
    have hf0 : f ≠ 0 := hf.1
    have hclose := natDegree_close_of_allComboRealRooted hall_qf hq0 hf0
    have hq_lt : q.natDegree < f.natDegree := by
      have hq_le : q.natDegree ≤ f.natDegree := by
        have hXg_le : (X * g).natDegree ≤ f.natDegree := by
          rw [natDegree_X_mul hg.1]
          omega
        have hsub : (f - X * g).natDegree ≤ f.natDegree :=
          (natDegree_sub_le_iff_left hXg_le).mpr le_rfl
        simpa [q] using hsub
      by_contra hnot
      have hf_le_q : f.natDegree ≤ q.natDegree := le_of_not_gt hnot
      have hq_eq : q.natDegree = f.natDegree := le_antisymm hq_le hf_le_q
      have hq_top_ne : q.coeff f.natDegree ≠ 0 := by
        rw [← hq_eq, coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hq0
      have hq_top_zero : q.coeff f.natDegree = 0 := by
        calc
          q.coeff f.natDegree
              = f.coeff f.natDegree - (X * g).coeff f.natDegree := by
                  simp [q, coeff_sub]
          _ = 1 - (X * g).coeff f.natDegree := by
                simpa using hf_monic.coeff_natDegree
          _ = 1 - g.coeff g.natDegree := by
                rw [← hdeg, coeff_X_mul]
          _ = 1 - g.leadingCoeff := by
                rw [coeff_natDegree]
          _ = 0 := by
                simp [hg_monic.leadingCoeff]
      exact hq_top_ne hq_top_zero
    have hdeg_qf : q.natDegree + 1 = f.natDegree := by
      omega
    have hprec_or : Prec q f ∨ Prec f q :=
      prec_of_allComboRealRooted hq hf hall_qf (Or.inl hdeg_qf)
    have hnot_prec_fq : ¬ Prec f q := by
      intro hfq
      rcases hfq with ⟨_, _, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩
      have hss_len : ss.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_eq, hf.2]
      have hrs_len : rs.length = q.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, hq.2]
      rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩ <;> omega
    rcases hprec_or with hqf | hfq
    · exact hqf.toPrec0
    · exact False.elim (hnot_prec_fq hfq)

/-- If `g ⊳ f` (differ-by-1), monic, all roots ≤ 0, then `g ≪₀ (f - X*g)`.
This zero-aware form is the right endpoint behavior when cancellation
`f - X*g = 0` occurs. -/
theorem prec_sub_X_mul_right {f g : ℝ[X]}
    (hgf : Prec g f)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree + 1 = f.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    Prec0 g (f - X * g) := by
  set q : ℝ[X] := f - X * g
  by_cases hq0 : q = 0
  · simpa [q, hq0] using prec0_zero_right g
  · have hleft0 : Prec0 q f := by
      simpa [q] using prec_sub_X_mul_left hgf hf_monic hg_monic hdeg hf_nonpos hg_nonpos
    have hf0 : f ≠ 0 := hgf.2.1.1
    have hqf : Prec q f := by
      rcases hleft0 with hqz | hfz | hqf
      · exact False.elim (hq0 hqz)
      · exact False.elim (hf0 hfz)
      · exact hqf
    have hall_qf : AllComboRealRooted q f := allComboRealRooted_of_prec hqf
    have hall_qXg : AllComboRealRooted q (X * g) := by
      intro α β
      have hrew :
          C α * q + C β * (X * g) =
            C (α - β) * q + C β * f := by
        ext n
        have hqcoeff : q.coeff n = f.coeff n - (X * g).coeff n := by
          simp [q, coeff_sub]
        rw [coeff_add, coeff_C_mul, coeff_C_mul, coeff_add, coeff_C_mul, coeff_C_mul, hqcoeff]
        ring
      simpa [hrew] using hall_qf (α - β) β
    have hq : IsRealRooted q := hqf.1
    have hg : IsRealRooted g := hgf.1
    have hXg : IsRealRooted (X * g) := isRealRooted_mul isRealRooted_X hg
    have hq_lt : q.natDegree < f.natDegree := by
      have hq_le : q.natDegree ≤ f.natDegree := by
        have hXg_le : (X * g).natDegree ≤ f.natDegree := by
          rw [natDegree_X_mul hg.1]
          omega
        have hsub : (f - X * g).natDegree ≤ f.natDegree :=
          (natDegree_sub_le_iff_left hXg_le).mpr le_rfl
        simpa [q] using hsub
      by_contra hnot
      have hf_le_q : f.natDegree ≤ q.natDegree := le_of_not_gt hnot
      have hq_eq : q.natDegree = f.natDegree := le_antisymm hq_le hf_le_q
      have hq_top_ne : q.coeff f.natDegree ≠ 0 := by
        rw [← hq_eq, coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hq0
      have hq_top_zero : q.coeff f.natDegree = 0 := by
        calc
          q.coeff f.natDegree
              = f.coeff f.natDegree - (X * g).coeff f.natDegree := by
                  simp [q, coeff_sub]
          _ = 1 - (X * g).coeff f.natDegree := by
                simpa using hf_monic.coeff_natDegree
          _ = 1 - g.coeff g.natDegree := by
                rw [← hdeg, coeff_X_mul]
          _ = 1 - g.leadingCoeff := by
                rw [coeff_natDegree]
          _ = 0 := by
                simp [hg_monic.leadingCoeff]
      exact hq_top_ne hq_top_zero
    have hclose_qf := natDegree_close_of_allComboRealRooted hall_qf hq0 hf0
    have hdeg_qf : q.natDegree + 1 = f.natDegree := by
      omega
    have hdeg_qXg : q.natDegree + 1 = (X * g).natDegree := by
      rw [natDegree_X_mul hg.1]
      omega
    have hprec_or : Prec q (X * g) ∨ Prec (X * g) q :=
      prec_of_allComboRealRooted hq hXg hall_qXg (Or.inl hdeg_qXg)
    have hnot_prec_Xgq : ¬ Prec (X * g) q := by
      intro hXgq
      rcases hXgq with ⟨_, _, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩
      have hss_len : ss.length = (X * g).natDegree := by
        rw [← Multiset.coe_card, hss_eq, hXg.2]
      have hrs_len : rs.length = q.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, hq.2]
      rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩ <;> omega
    have hprec_qXg : Prec q (X * g) := by
      rcases hprec_or with hqXg | hXgq
      · exact hqXg
      · exact False.elim (hnot_prec_Xgq hXgq)
    have hq_nonpos : ∀ r ∈ q.roots, r ≤ 0 :=
      roots_le_of_prec_right hqf hf_nonpos
    have hdeg_gq : g.natDegree = q.natDegree := by
      omega
    exact
      (prec_of_prec_mul_X_of_sameDegree_of_roots_nonpos
        (f := g) (g := q) hprec_qXg hdeg_gq hg_nonpos hq_nonpos).toPrec0

end RealRooted
