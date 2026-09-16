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

/-- Without sign assumptions on the leading coefficients, all-real-
combination splitness and nonnegativity of `W(g,f)` still give a stable
pencil, provided neither endpoint is zero. -/
theorem isUpperHalfPlaneStablePencil_of_allComboRealRooted_of_wronskian_nonneg_of_ne
    {f g : ℝ[X]} (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hall : AllComboRealRooted f g)
    (hW : ∀ x : ℝ, 0 ≤ (wronskian g f).eval x) :
    IsUpperHalfPlaneStablePencil f g := by
  have hflc0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hglc0 : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  rcases lt_or_gt_of_ne hflc0 with hfneg | hfpos
  · rcases lt_or_gt_of_ne hglc0 with hgneg | hgpos
    · have hnfp : HasPosLeadingCoeff (-f) := by
        unfold HasPosLeadingCoeff
        simp only [leadingCoeff_neg]
        linarith
      have hngp : HasPosLeadingCoeff (-g) := by
        unfold HasPosLeadingCoeff
        simp only [leadingCoeff_neg]
        linarith
      have hall_left : AllComboRealRooted (-f) g := by
        simpa using allComboRealRooted_C_mul_left (c := -1) hall
      have hall' : AllComboRealRooted (-f) (-g) := by
        simpa using allComboRealRooted_C_mul_right (c := -1) hall_left
      have hW' : ∀ x : ℝ, 0 ≤ (wronskian (-g) (-f)).eval x := by
        intro x
        rw [wronskian_neg_left, wronskian_neg_right, neg_neg]
        exact hW x
      have hstable :=
        isUpperHalfPlaneStablePencil_of_allComboRealRooted_of_wronskian_nonneg
          hnfp hngp hall' hW'
      simpa using hstable.neg_neg
    · have hnfp : HasPosLeadingCoeff (-f) := by
        unfold HasPosLeadingCoeff
        simp only [leadingCoeff_neg]
        linarith
      have hall_left : AllComboRealRooted (-f) g := by
        simpa using allComboRealRooted_C_mul_left (c := -1) hall
      have hall' : AllComboRealRooted g (-f) :=
        allComboRealRooted_comm hall_left
      have hW' : ∀ x : ℝ, 0 ≤ (wronskian (-f) g).eval x := by
        intro x
        rw [wronskian_neg_left, wronskian_neg_eq]
        exact hW x
      have hstable :=
        isUpperHalfPlaneStablePencil_of_allComboRealRooted_of_wronskian_nonneg
          hgpos hnfp hall' hW'
      simpa using hstable.swap_neg.neg_neg
  · rcases lt_or_gt_of_ne hglc0 with hgneg | hgpos
    · have hngp : HasPosLeadingCoeff (-g) := by
        unfold HasPosLeadingCoeff
        simp only [leadingCoeff_neg]
        linarith
      have hall_right : AllComboRealRooted f (-g) := by
        simpa using allComboRealRooted_C_mul_right (c := -1) hall
      have hall' : AllComboRealRooted (-g) f :=
        allComboRealRooted_comm hall_right
      have hW' : ∀ x : ℝ, 0 ≤ (wronskian f (-g)).eval x := by
        intro x
        rw [wronskian_neg_right, wronskian_neg_eq]
        exact hW x
      have hstable :=
        isUpperHalfPlaneStablePencil_of_allComboRealRooted_of_wronskian_nonneg
          hngp hfpos hall' hW'
      simpa using hstable.swap_neg
    · exact
        isUpperHalfPlaneStablePencil_of_allComboRealRooted_of_wronskian_nonneg
          hfpos hgpos hall hW

/-- Zero-aware oriented Obreschkoff criterion: either both endpoints vanish,
or their two-parameter pencil is upper-half-plane stable. -/
theorem eq_zero_pair_or_isUpperHalfPlaneStablePencil_of_allComboRealRooted_of_wronskian_nonneg
    {f g : ℝ[X]} (hall : AllComboRealRooted f g)
    (hW : ∀ x : ℝ, 0 ≤ (wronskian g f).eval x) :
    (f = 0 ∧ g = 0) ∨ IsUpperHalfPlaneStablePencil f g := by
  by_cases hf0 : f = 0
  · subst f
    by_cases hg0 : g = 0
    · exact Or.inl ⟨rfl, hg0⟩
    · exact Or.inr <|
        isUpperHalfPlaneStablePencil_zero_left hg0 hall.right_splits
  · by_cases hg0 : g = 0
    · subst g
      exact Or.inr <|
        isUpperHalfPlaneStablePencil_zero_right hf0 hall.left_splits
    · exact Or.inr <|
        isUpperHalfPlaneStablePencil_of_allComboRealRooted_of_wronskian_nonneg_of_ne
          hf0 hg0 hall hW

end

end RealRooted
