import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Derivative
import RealRooted.Wagner
import RealRooted.ObreschkoffConverse
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
  · have hg : (g ≠ 0 ∧ g.Splits) := hgf.1
    have hf : (f ≠ 0 ∧ f.Splits) := hgf.2.1
    have hg_pos : HasPosLeadingCoeff g := by
      unfold HasPosLeadingCoeff
      simp [hg_monic.leadingCoeff]
    have hf_pos : HasPosLeadingCoeff f := by
      unfold HasPosLeadingCoeff
      simp [hf_monic.leadingCoeff]
    have hprec_fXg : Prec f (X * g) := by
      exact
        (prec_iff_prec_mul_X_of_roots_nonpos
          (f := g) (g := f) hg.2 hf.2 hg_pos hf_pos hg_nonpos hf_nonpos hdeg).mp hgf
    have hall_fXg : AllComboRealRooted f (X * g) :=
      allComboRealRooted_of_prec hprec_fXg
    have hall_qf : AllComboRealRooted q f := by
      intro α β
      have hrew :
          C α * q + C β * f =
            C (α + β) * f + C (-α) * (X * g) := by
        grind
      simpa [hrew] using hall_fXg (α + β) (-α)
    have hq : (q ≠ 0 ∧ q.Splits) := by
      exact ⟨hq0, by simpa using hall_qf 1 0⟩
    have hf0 : f ≠ 0 := hf.1
    have hclose := natDegree_close_of_allComboRealRooted hall_qf hq0 hf0
    have hq_lt : q.natDegree < f.natDegree := by
      have hq_le : q.natDegree ≤ f.natDegree := by
        have hXg_le : (X * g).natDegree ≤ f.natDegree := by
          simp_all
        have hsub : (f - X * g).natDegree ≤ f.natDegree :=
          (natDegree_sub_le_iff_left hXg_le).mpr le_rfl
        lia
      by_contra hnot
      have hf_le_q : f.natDegree ≤ q.natDegree := le_of_not_gt hnot
      have hq_eq : q.natDegree = f.natDegree := le_antisymm hq_le hf_le_q
      have hq_top_ne : q.coeff f.natDegree ≠ 0 := by
        rw [← hq_eq, coeff_natDegree]
        simp_all
      have hq_top_zero : q.coeff f.natDegree = 0 := by
        calc
          q.coeff f.natDegree
              = f.coeff f.natDegree - (X * g).coeff f.natDegree := by
                  simp [q, coeff_sub]
          _ = 1 - (X * g).coeff f.natDegree := by
                simp_all
          _ = 1 - g.coeff g.natDegree := by
                rw [← hdeg, coeff_X_mul]
          _ = 1 - g.leadingCoeff := by
                simp
          _ = 0 := by
                simp [hg_monic.leadingCoeff]
      lia
    have hdeg_qf : q.natDegree + 1 = f.natDegree := by
      lia
    have hprec_or : Prec q f ∨ Prec f q :=
      prec_of_allComboRealRooted hq.1 hq.2 hf.1 hf.2 hall_qf (Or.inl hdeg_qf)
    have hnot_prec_fq : ¬ Prec f q := by
      intro hfq
      rcases hfq with ⟨_, _, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩
      have hss_len : ss.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
      have hrs_len : rs.length = q.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hq.2]
      lia
    rcases hprec_or with hqf | hfq
    · exact hqf.toPrec0
    · lia

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
      rcases hleft0 with hqz | hfz | hqf <;> lia
    have hall_qf : AllComboRealRooted q f := allComboRealRooted_of_prec hqf
    have hall_qXg : AllComboRealRooted q (X * g) := by
      intro α β
      have hrew :
          C α * q + C β * (X * g) =
            C (α - β) * q + C β * f := by
        grind
      simpa [hrew] using hall_qf (α - β) β
    have hq : (q ≠ 0 ∧ q.Splits) := hqf.1
    have hg : (g ≠ 0 ∧ g.Splits) := hgf.1
    have hXg : ((X * g) ≠ 0 ∧ (X * g).Splits) := isRealRooted_X_mul hg.1 hg.2
    have hq_lt : q.natDegree < f.natDegree := by
      have hq_le : q.natDegree ≤ f.natDegree := by
        have hXg_le : (X * g).natDegree ≤ f.natDegree := by
          simp_all
        have hsub : (f - X * g).natDegree ≤ f.natDegree :=
          (natDegree_sub_le_iff_left hXg_le).mpr le_rfl
        lia
      by_contra hnot
      have hf_le_q : f.natDegree ≤ q.natDegree := le_of_not_gt hnot
      have hq_eq : q.natDegree = f.natDegree := le_antisymm hq_le hf_le_q
      have hq_top_ne : q.coeff f.natDegree ≠ 0 := by
        rw [← hq_eq, coeff_natDegree]
        simp_all
      have hq_top_zero : q.coeff f.natDegree = 0 := by
        calc
          q.coeff f.natDegree
              = f.coeff f.natDegree - (X * g).coeff f.natDegree := by
                  simp [q, coeff_sub]
          _ = 1 - (X * g).coeff f.natDegree := by
                simp_all
          _ = 1 - g.coeff g.natDegree := by
                rw [← hdeg, coeff_X_mul]
          _ = 1 - g.leadingCoeff := by
                simp
          _ = 0 := by
                simp [hg_monic.leadingCoeff]
      lia
    have hclose_qf := natDegree_close_of_allComboRealRooted hall_qf hq0 hf0
    have hdeg_qf : q.natDegree + 1 = f.natDegree := by
      lia
    have hdeg_qXg : q.natDegree + 1 = (X * g).natDegree := by
      simp_all
    have hprec_or : Prec q (X * g) ∨ Prec (X * g) q :=
      prec_of_allComboRealRooted hq.1 hq.2 hXg.1 hXg.2 hall_qXg (Or.inl hdeg_qXg)
    have hnot_prec_Xgq : ¬ Prec (X * g) q := by
      intro hXgq
      rcases hXgq with ⟨_, _, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩
      have hss_len : ss.length = (X * g).natDegree := by
        rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hXg.2]
      have hrs_len : rs.length = q.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hq.2]
      lia
    have hprec_qXg : Prec q (X * g) := by
      lia
    have hdeg_gq : g.natDegree = q.natDegree := by
      lia
    exact
      (prec_of_prec_mul_X_of_sameDegree_of_roots_nonpos
        (f := g) (g := q) hprec_qXg hdeg_gq hg_nonpos).toPrec0

end RealRooted
