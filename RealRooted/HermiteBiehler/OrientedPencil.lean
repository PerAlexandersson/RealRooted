import RealRooted.HermiteBiehler.StablePencil
import RealRooted.Mathlib.Analysis.Polynomial.Asymptotics
import RealRooted.ObreschkoffConverse.DegreeGap
import RealRooted.Wronskian.Algebra

/-!
# Oriented stable pencils

This module combines the unoriented Obreschkoff converse with a pointwise
Wronskian sign.  The sign selects the proper-position orientation compatible
with the two-variable pencil `f(z) + w g(z)`.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- If every real combination of two positive-leading-coefficient polynomials
splits or vanishes, nonnegativity of `W(g,f)` selects `Prec g f`. -/
theorem prec_of_allComboRealRooted_of_wronskian_nonneg
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f)
    (hg : HasPosLeadingCoeff g) (hall : AllComboRealRooted f g)
    (hW : ∀ x : ℝ, 0 ≤ (wronskian g f).eval x) :
    Prec g f := by
  have hfrr : f ≠ 0 ∧ f.Splits := hall.isRealRooted_left hf.ne_zero
  have hgrr : g ≠ 0 ∧ g.Splits := hall.isRealRooted_right hg.ne_zero
  rcases natDegree_eq_or_succ_or_revSucc_of_allComboRealRooted
      hall hf.ne_zero hg.ne_zero with hsame | hfsucc | hgsucc
  · have horient : Prec g f ∨ Prec f g :=
      prec_of_allComboRealRooted hgrr.1 hgrr.2 hfrr.1 hfrr.2
        (allComboRealRooted_comm hall) (Or.inr hsame.symm)
    rcases horient with hgf | hfg
    · exact hgf
    · apply prec_of_reverse_prec_of_roots_sum_le hfg hsame.symm
      by_cases hdeg0 : f.natDegree = 0
      · have hfroots : f.roots = 0 := by
          apply Multiset.card_eq_zero.mp
          rw [card_roots_of_splits hfrr.2, hdeg0]
        have hgroots : g.roots = 0 := by
          apply Multiset.card_eq_zero.mp
          rw [card_roots_of_splits hgrr.2, ← hsame, hdeg0]
        simp [hfroots, hgroots]
      · let n := f.natDegree
        have hn : 1 ≤ n := by simp only [n]; lia
        have hgdeg : g.natDegree = n := by simp only [n]; exact hsame.symm
        have hWdeg : (wronskian g f).natDegree ≤ 2 * n - 2 :=
          natDegree_wronskian_le_two_mul_sub_two_of_sameDegree
            g f n hn hgdeg rfl
        have hcoeff : 0 ≤ (wronskian g f).coeff (2 * n - 2) :=
          Polynomial.coeff_nonneg_of_forall_eval_nonneg_of_natDegree_le hW hWdeg
        rw [coeff_wronskian_two_mul_sub_two_of_sameDegree
          g f n hn hgdeg rfl] at hcoeff
        have hgnext : g.nextCoeff =
            -g.leadingCoeff * g.roots.sum :=
          hgrr.2.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
        have hfnext : f.nextCoeff =
            -f.leadingCoeff * f.roots.sum :=
          hfrr.2.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
        rw [hgnext, hfnext] at hcoeff
        nlinarith [mul_pos hg hf]
  · have hWcoeff : (wronskian g f).coeff (2 * f.natDegree) =
        -(g.leadingCoeff * f.leadingCoeff) :=
      coeff_wronskian_two_mul_of_natDegree_eq_succ
        g f f.natDegree hfsucc.symm rfl
    have hW0 : wronskian g f ≠ 0 := by
      intro hzero
      have := congrArg (fun p : ℝ[X] ↦ p.coeff (2 * f.natDegree)) hzero
      rw [hWcoeff] at this
      simp only [coeff_zero] at this
      nlinarith [mul_pos hg hf]
    have hWdeg : (wronskian g f).natDegree ≤ 2 * f.natDegree := by
      have hlt := natDegree_wronskian_lt_add hW0
      rw [← hfsucc] at hlt
      lia
    have hcoeff : 0 ≤ (wronskian g f).coeff (2 * f.natDegree) :=
      Polynomial.coeff_nonneg_of_forall_eval_nonneg_of_natDegree_le hW hWdeg
    rw [hWcoeff] at hcoeff
    nlinarith [mul_pos hg hf]
  · apply prec_forward_of_orientation_of_succDegree hgsucc.symm
    exact prec_of_allComboRealRooted hgrr.1 hgrr.2 hfrr.1 hfrr.2
      (allComboRealRooted_comm hall) (Or.inl hgsucc)

/-- All-real-combination splitness and the oriented Wronskian sign imply
upper-half-plane stability of the two-parameter pencil. -/
theorem isUpperHalfPlaneStablePencil_of_allComboRealRooted_of_wronskian_nonneg
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f)
    (hg : HasPosLeadingCoeff g) (hall : AllComboRealRooted f g)
    (hW : ∀ x : ℝ, 0 ≤ (wronskian g f).eval x) :
    IsUpperHalfPlaneStablePencil f g :=
  isUpperHalfPlaneStablePencil_of_prec hf hg
    (prec_of_allComboRealRooted_of_wronskian_nonneg hf hg hall hW)

end

end RealRooted
