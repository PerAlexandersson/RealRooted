import RealRooted.MaWang.Weak.Successor

open Polynomial Filter

noncomputable section

namespace RealRooted.MaWangInternal

/-- Degree-bounded structured Liu--Wang theorem in the weak-sign regime. -/
theorem prec_of_interlaces_evalCoeff_nonpos
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + b * g) := by
  classical
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g a b : ℝ[X]},
          f.natDegree = n →
          Interlaces g f →
          HasPosLeadingCoeff g →
          HasPosLeadingCoeff (a * f + b * g) →
          f.natDegree ≤ (a * f + b * g).natDegree →
          (a * f + b * g).natDegree ≤ f.natDegree + 1 →
          (∀ r, f.IsRoot r → b.eval r ≤ 0) →
          Prec f (a * f + b * g))
      f.natDegree ?_ rfl hgf hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  intro n ih f g a b hfdeg hgf hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · have hcases :
        (a * f + b * g).natDegree = f.natDegree ∨
          (a * f + b * g).natDegree = f.natDegree + 1 := by
      lia
    rcases hcases with hsame | hsucc
    · exact
        prec_of_interlaces_evalCoeff_nonpos_same_of_no_common
          hgf hg_pos hF_pos hsame hno hb_nonpos
    · exact
        prec_of_interlaces_evalCoeff_nonpos_succ_of_no_common
          hgf hg_pos hF_pos hsucc hno hb_nonpos
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, qg, hqf, hqg, hqinter, hqg_pos, hqF_pos, hqdeg_lo, hqdeg_hi, hq_nonpos⟩ :=
      common_root_reduction_data hgf hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos hrf hrg
    obtain ⟨hf, _, _, _, _, _, _, _, _, _⟩ := hgf
    have hqf_ne : qf ≠ 0 := by simp_all
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C]
      lia
    have hprec_q : Prec qf (a * qf + b * qg) := by grind
    have hprec_mul :
        Prec ((X - C r) * qf) (a * ((X - C r) * qf) + b * ((X - C r) * qg)) :=
      prec_mul_X_sub_C_of_linearCombo_quotient (a := a) (b := b) (r := r) hprec_q
    lia


end RealRooted.MaWangInternal

namespace RealRooted

export MaWangInternal
  (prec_of_interlaces_evalCoeff_nonpos)

end RealRooted
