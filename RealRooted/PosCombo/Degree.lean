import RealRooted.Linear

/-!
# Degrees of positive polynomial combinations

Degree and positive-leading-coefficient bookkeeping for positive linear
combinations of two real polynomials.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Positive combinations keep the larger of the two degrees when the summands
have positive leading coefficients. This is the degree bookkeeping needed for
the restricted converse setup. -/
lemma natDegree_pos_combo_eq_right_of_natDegree_le {f g : ℝ[X]}
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (C a * f + C b * g).natDegree = g.natDegree := by
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · simpa [natDegree_C_mul ha.ne', natDegree_C_mul hb.ne'] using
      (natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
        (by simpa [natDegree_C_mul ha.ne', natDegree_C_mul hb.ne'] using hlt)
        (hasPosLeadingCoeff_C_mul hb hg_pos) :
          (C a * f + C b * g).natDegree = (C b * g).natDegree)
  · have hsame : (C a * f + C b * g).natDegree = f.natDegree := by
      simpa [natDegree_C_mul ha.ne', natDegree_C_mul hb.ne'] using
        (natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
          (by simpa [natDegree_C_mul ha.ne', natDegree_C_mul hb.ne'] using heq)
          (hasPosLeadingCoeff_C_mul ha hf_pos)
          (hasPosLeadingCoeff_C_mul hb hg_pos) :
            (C a * f + C b * g).natDegree = (C a * f).natDegree)
    lia

/-- Symmetric form of `natDegree_pos_combo_eq_right_of_natDegree_le`. -/
lemma natDegree_pos_combo_eq_left_of_natDegree_le {f g : ℝ[X]}
    (hdeg : g.natDegree ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (C a * f + C b * g).natDegree = f.natDegree := by
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · simpa [natDegree_C_mul ha.ne', natDegree_C_mul hb.ne'] using
      (natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff
        (by simpa [natDegree_C_mul ha.ne', natDegree_C_mul hb.ne'] using hlt)
        (hasPosLeadingCoeff_C_mul ha hf_pos) :
          (C a * f + C b * g).natDegree = (C a * f).natDegree)
  · simpa [natDegree_C_mul ha.ne', natDegree_C_mul hb.ne'] using
      (natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
        (by simpa [natDegree_C_mul ha.ne', natDegree_C_mul hb.ne'] using heq.symm)
        (hasPosLeadingCoeff_C_mul ha hf_pos)
        (hasPosLeadingCoeff_C_mul hb hg_pos) :
          (C a * f + C b * g).natDegree = (C a * f).natDegree)

/-- Positive combinations inherit a positive leading coefficient from the
summand of maximal degree. -/
lemma hasPosLeadingCoeff_pos_combo_of_natDegree_le_right {f g : ℝ[X]}
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasPosLeadingCoeff (C a * f + C b * g) := by
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact hasPosLeadingCoeff_add_of_natDegree_lt_right
      (by simpa [natDegree_C_mul ha.ne', natDegree_C_mul hb.ne'] using hlt)
      (hasPosLeadingCoeff_C_mul hb hg_pos)
  · exact hasPosLeadingCoeff_add_of_same_natDegree
      (by simpa [natDegree_C_mul ha.ne', natDegree_C_mul hb.ne'] using heq)
      (hasPosLeadingCoeff_C_mul ha hf_pos)
      (hasPosLeadingCoeff_C_mul hb hg_pos)

/-- Symmetric form of `hasPosLeadingCoeff_pos_combo_of_natDegree_le_right`. -/
lemma hasPosLeadingCoeff_pos_combo_of_natDegree_le_left {f g : ℝ[X]}
    (hdeg : g.natDegree ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasPosLeadingCoeff (C a * f + C b * g) := by
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact hasPosLeadingCoeff_add_of_natDegree_lt_left
      (by simpa [natDegree_C_mul ha.ne', natDegree_C_mul hb.ne'] using hlt)
      (hasPosLeadingCoeff_C_mul ha hf_pos)
  · exact hasPosLeadingCoeff_add_of_same_natDegree
      (by simpa [natDegree_C_mul ha.ne', natDegree_C_mul hb.ne'] using heq.symm)
      (hasPosLeadingCoeff_C_mul ha hf_pos)
      (hasPosLeadingCoeff_C_mul hb hg_pos)

namespace PosComboRealRooted

lemma family_natDegree_right {f g : ℝ[X]}
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {μ : ℝ} (hμ : 0 < μ) :
    (f + C μ * g).natDegree = g.natDegree := by
  simpa [one_mul] using
    natDegree_pos_combo_eq_right_of_natDegree_le hdeg hf_pos hg_pos zero_lt_one hμ

lemma family_natDegree_left {f g : ℝ[X]}
    (hdeg : g.natDegree ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {lam : ℝ} (hlam : 0 < lam) :
    (C lam * f + g).natDegree = f.natDegree := by
  simpa [one_mul] using
    natDegree_pos_combo_eq_left_of_natDegree_le hdeg hf_pos hg_pos hlam zero_lt_one

lemma family_hasPosLeadingCoeff_right {f g : ℝ[X]}
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {μ : ℝ} (hμ : 0 < μ) :
    HasPosLeadingCoeff (f + C μ * g) := by
  simpa [one_mul] using
    hasPosLeadingCoeff_pos_combo_of_natDegree_le_right
      hdeg hf_pos hg_pos zero_lt_one hμ

lemma family_hasPosLeadingCoeff_left {f g : ℝ[X]}
    (hdeg : g.natDegree ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {lam : ℝ} (hlam : 0 < lam) :
    HasPosLeadingCoeff (C lam * f + g) := by
  simpa [one_mul] using
    hasPosLeadingCoeff_pos_combo_of_natDegree_le_left
      hdeg hf_pos hg_pos hlam zero_lt_one

end PosComboRealRooted
end RealRooted
