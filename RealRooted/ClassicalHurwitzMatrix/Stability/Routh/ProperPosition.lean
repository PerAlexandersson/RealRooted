import RealRooted.ClassicalHurwitzMatrix.Stability.Routh
import RealRooted.HermiteBiehler.Forward
import RealRooted.HermiteBiehler.Hurwitz

/-!
# Proper-position data for stable Routh reduction

This module completes the proper-position and coefficient-sign transport for
the odd-degree parity shape, complementing the even-shape theorem in the
algebraic Routh module.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Open right-half-plane stability becomes strict Hurwitz stability once the
two real parity inputs have no common root and the even input is nonzero at
the origin. -/
theorem isStrictlyHurwitzStable_oddEvenPolynomial_of_rightHalfPlaneStable
    {p q : ℝ[X]}
    (hstable : IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q)))
    (hq0 : q.coeff 0 ≠ 0)
    (hno : ∀ r : ℝ, ¬ (p.IsRoot r ∧ q.IsRoot r)) :
    IsStrictlyHurwitzStable (oddEvenPolynomial p q) := by
  intro z hz
  have hzNonpos : z.re ≤ 0 := by
    by_contra hzle
    exact hstable z (lt_of_not_ge hzle) hz
  rcases lt_or_eq_of_le hzNonpos with hzNeg | hzZero
  · exact hzNeg
  · exfalso
    have hzEq : z = Complex.I * (z.im : ℂ) := by
      apply Complex.ext
      · simp [hzZero]
      · simp
    have hsquare :
        (Complex.I * (z.im : ℂ)) ^ 2 = ((-(z.im ^ 2) : ℝ) : ℂ) := by
      rw [mul_pow, Complex.I_sq]
      norm_num
    rw [eval_complexify_oddEvenPolynomial, hzEq, hsquare,
      eval_complexify_ofReal, eval_complexify_ofReal] at hz
    have hzRe := congrArg Complex.re hz
    have hzIm := congrArg Complex.im hz
    norm_num [Complex.mul_re, Complex.mul_im] at hzRe hzIm
    by_cases hy : z.im = 0
    · apply hq0
      simpa [hy, ← Polynomial.coeff_zero_eq_eval_zero] using hzRe
    · apply hno (-(z.im ^ 2))
      constructor
      · rw [Polynomial.IsRoot.def]
        exact hzIm.resolve_left hy
      · rw [Polynomial.IsRoot.def]
        exact hzRe

/-- In the positive-degree odd shape, the source parity Wronskian is strictly
positive on the real line. -/
theorem IsStrictlyHurwitzStable.wronskian_parts_pos_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree)
    (hdegreePos : 0 < odd.natDegree) (t : ℝ) :
    0 < even.derivative.eval t * odd.eval t -
      even.eval t * odd.derivative.eval t := by
  obtain ⟨hoddnn, _⟩ :=
    h.hasNonnegCoeffs_parts_of_oddShape hodd heven hdegree
  have hprec := h.prec_parts_of_oddShape hodd heven hdegree
  have hstrict : StrictPrecSameDegree odd even :=
    StrictPrecSameDegree.of_prec_of_no_common hprec hdegree.symm
      (fun r hoddRoot hevenRoot =>
        h.noCommonRoot_parts_of_hasNonnegCoeffs hodd.ne_zero hoddnn r
          ⟨hoddRoot, hevenRoot⟩)
  exact wronskian_pos_of_strictPrecSameDegree hodd heven
    (by simpa only [hdegree] using hdegreePos) hstrict t

/-- In a positive-degree odd-shape Routh step, the reduced input precedes the
old odd input and has nonnegative coefficients. -/
theorem IsStrictlyHurwitzStable.prec_routhReducedOddPart_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree)
    (hdegreePos : 0 < odd.natDegree) :
    Prec (routhReducedOddPart (routhCoefficient odd even) odd even) odd ∧
      HasNonnegCoeffs
        (routhReducedOddPart (routhCoefficient odd even) odd even) := by
  obtain ⟨hoddnn, _⟩ :=
    h.hasNonnegCoeffs_parts_of_oddShape hodd heven hdegree
  obtain ⟨hodd0, _⟩ :=
    h.coeff_zero_pos_parts_of_oddShape hodd heven hdegree
  have hprec := h.prec_parts_of_oddShape hodd heven hdegree
  let c := routhCoefficient odd even
  let q := even - Polynomial.C c * odd
  have hq0 : q.coeff 0 = 0 := by
    dsimp only [q, c]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, sub_eq_zero]
    exact routhCoefficient_mul_coeff_zero odd even hodd0.ne'
  have hqRoot : q.IsRoot 0 := by
    rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero]
    exact hq0
  have hredNe :
      routhReducedOddPart (routhCoefficient odd even) odd even ≠ 0 :=
    h.routhReducedOddPart_ne_zero_of_oddShape hodd heven hdegree hdegreePos
  have hqNe : q ≠ 0 := by
    intro hq
    apply hredNe
    simp [routhReducedOddPart, c, q, hq]
  have hall : AllComboRealRooted odd q := by
    simpa only [q] using allComboRealRooted_routhNumerator hprec c
  have hqSplits : q.Splits := hall.right_splits
  have hqDegreeLe : q.natDegree ≤ odd.natDegree := by
    dsimp only [q]
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    exact max_le hdegree.le
      (Polynomial.natDegree_C_mul_le c odd)
  have hclose := natDegree_close_of_allComboRealRooted hall hodd.ne_zero hqNe
  have hoddNeg : ∀ r, odd.IsRoot r → r < 0 := by
    intro r hr
    have hrNonpos : r ≤ 0 :=
      roots_nonpos_of_hasNonnegCoeffs hoddnn r
        ((Polynomial.mem_roots hodd.ne_zero).mpr hr)
    have hrNe : r ≠ 0 := by
      intro hr0
      subst r
      change odd.eval 0 = 0 at hr
      rw [← Polynomial.coeff_zero_eq_eval_zero] at hr
      exact hodd0.ne' hr
    exact lt_of_le_of_ne hrNonpos hrNe
  have hqDegree : q.natDegree = odd.natDegree := by
    have hor : q.natDegree = odd.natDegree ∨
        q.natDegree + 1 = odd.natDegree := by lia
    rcases hor with heq | hsucc
    · exact heq
    · have hprecOr := prec_of_allComboRealRooted hqNe hqSplits
          hodd.ne_zero hprec.1.2 (allComboRealRooted_comm hall)
          (Or.inl hsucc)
      have hqodd : Prec q odd := by
        rcases hprecOr with hqodd | hoddq
        · exact hqodd
        · rcases hoddq.natDegree_eq_or_eq_succ with hs | hs <;> lia
      have hqNeg : ∀ r, q.IsRoot r → r < 0 :=
        roots_neg_of_interlaces_of_right_roots_neg
          (hqodd.toInterlaces hsucc) hoddNeg
      exact False.elim ((ne_of_lt (hqNeg 0 hqRoot)) rfl)
  have hprecQ : Prec odd q := by
    rcases prec_of_allComboRealRooted hodd.ne_zero hprec.1.2
        hqNe hqSplits hall (Or.inr hqDegree.symm) with hoddq | hqodd
    · exact hoddq
    · have hqNeg :=
        roots_neg_of_prec_sameDegree_of_roots_neg hqodd hqDegree hoddNeg
      exact False.elim ((ne_of_lt (hqNeg 0 hqRoot)) rfl)
  have hqNonpos : ∀ r, q.IsRoot r → r ≤ 0 :=
    roots_nonpos_of_prec_sameDegree_of_zero_root_of_left_roots_neg
      hprecQ hqDegree.symm hqRoot hoddNeg
  have hredPrec : Prec q.divX odd :=
    prec_divX_left_of_prec_sameDegree_of_roots_nonpos_coeff_zero hprecQ
      (fun r hr => hqNonpos r ((Polynomial.mem_roots hqNe).mp hr))
      hq0 hqDegree
  have hdivNe : q.divX ≠ 0 := by
    simpa only [routhReducedOddPart, c, q] using hredNe
  have hdivSplits : q.divX.Splits :=
    (DegreeDropReversal.splits_iff_divX_splits_of_coeff_zero hq0).1 hqSplits
  have hdivRootsNonpos : ∀ r ∈ q.divX.roots, r ≤ 0 := by
    intro r hr
    apply hqNonpos r
    apply (Polynomial.mem_roots hqNe).mp
    have hroots := roots_eq_zero_cons_divX_of_coeff_zero hqNe hq0
    rw [hroots]
    simp [hr]
  have hcoeffPos : 0 < even.coeff 1 - c * odd.coeff 1 := by
    have hW := h.wronskian_parts_pos_of_oddShape
      hodd heven hdegree hdegreePos 0
    simp only [← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_derivative,
      Nat.cast_zero, zero_add, mul_one] at hW
    have heq := routhCoefficient_mul_coeff_zero odd even hodd0.ne'
    rw [heq] at hW
    have hfactor :
        even.coeff 1 * odd.coeff 0 -
            (routhCoefficient odd even * odd.coeff 0) * odd.coeff 1 =
          odd.coeff 0 *
            (even.coeff 1 - routhCoefficient odd even * odd.coeff 1) := by
      ring
    rw [hfactor] at hW
    exact (mul_pos_iff_of_pos_left hodd0).mp hW
  have hdivEval : 0 < q.divX.eval 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    change 0 <
      (routhReducedOddPart (routhCoefficient odd even) odd even).coeff 0
    simpa using hcoeffPos
  have hdivRootsNeg : ∀ r ∈ q.divX.roots, r < 0 := by
    intro r hr
    have hrNonpos := hdivRootsNonpos r hr
    have hrNe : r ≠ 0 := by
      intro hr0
      subst r
      have hroot : q.divX.IsRoot 0 :=
        (Polynomial.mem_roots hdivNe).mp hr
      change q.divX.eval 0 = 0 at hroot
      linarith
    exact lt_of_le_of_ne hrNonpos hrNe
  have hprodPos : 0 < (q.divX.roots.map (0 - ·)).prod := by
    refine Multiset.prod_pos ?_
    simp_all
  have hdivPos : HasPosLeadingCoeff q.divX := by
    rw [eval_eq_leadingCoeff_mul_prod_sub hdivSplits 0] at hdivEval
    exact (mul_pos_iff_of_pos_right hprodPos).mp hdivEval
  have hdivnn : HasNonnegCoeffs q.divX :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hdivSplits).2
      ⟨hdivPos, hdivRootsNonpos⟩).1
  change Prec q.divX odd ∧ HasNonnegCoeffs q.divX
  exact ⟨hredPrec, hdivnn⟩

/-- A nonterminal odd-shape Routh step lowers the parity degree by exactly
one. -/
theorem IsStrictlyHurwitzStable.natDegree_routhReducedOddPart_add_one_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree)
    (hdegreePos : 0 < odd.natDegree) :
    (routhReducedOddPart (routhCoefficient odd even) odd even).natDegree + 1 =
      odd.natDegree := by
  have hprec :=
    (h.prec_routhReducedOddPart_of_oddShape
      hodd heven hdegree hdegreePos).1
  have hle := natDegree_routhReducedOddPart_le_pred_of_oddShape
    (routhCoefficient odd even) hdegree
  rcases hprec.natDegree_eq_or_eq_succ with hsame | hsucc
  · lia
  · exact hsucc.symm

/-- A stable Routh remainder and the old odd input have no common real root.
Otherwise the defining recurrence would give a common root of both original
parity inputs. -/
theorem IsStrictlyHurwitzStable.noCommonRoot_routhReducedOddPart
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hoddnn : HasNonnegCoeffs odd) (hodd0 : odd.coeff 0 ≠ 0)
    (r : ℝ) :
    ¬ ((routhReducedOddPart (routhCoefficient odd even) odd even).IsRoot r ∧
      odd.IsRoot r) := by
  rintro ⟨hred, hoddRoot⟩
  apply h.noCommonRoot_parts_of_hasNonnegCoeffs
    (hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hoddnn (by
      intro hoddZero
      subst odd
      simp at hodd0)).ne_zero hoddnn r
  refine ⟨hoddRoot, ?_⟩
  rw [Polynomial.IsRoot.def,
    even_eq_C_mul_odd_add_X_mul_routhReducedOddPart_ratio odd even hodd0]
  change odd.eval r = 0 at hoddRoot
  change (routhReducedOddPart
    (routhCoefficient odd even) odd even).eval r = 0 at hred
  simp [hoddRoot, hred]

/-- A strictly stable even-shape polynomial remains strictly stable after one
Routh reduction. -/
theorem IsStrictlyHurwitzStable.routhReducedPolynomial_of_evenShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) :
    IsStrictlyHurwitzStable
      (routhReducedPolynomial (routhCoefficient odd even) odd even) := by
  obtain ⟨hoddnn, _⟩ :=
    h.hasNonnegCoeffs_parts_of_evenShape hodd heven hdegree
  obtain ⟨hodd0, _⟩ :=
    h.coeff_zero_pos_parts_of_evenShape hodd heven hdegree
  obtain ⟨hprec, hrednn⟩ :=
    h.prec_routhReducedOddPart_of_evenShape hodd heven hdegree
  have hredPos : HasPosLeadingCoeff
      (routhReducedOddPart (routhCoefficient odd even) odd even) :=
    hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hrednn hprec.1.1
  have hHB := hermiteBiehlerForwardPos hodd hredPos hprec
  have hright :=
    hermiteBiehlerStableToHurwitzOddEven hrednn hoddnn hHB
  rw [routhReducedPolynomial]
  exact isStrictlyHurwitzStable_oddEvenPolynomial_of_rightHalfPlaneStable
    hright hodd0.ne'
      (h.noCommonRoot_routhReducedOddPart hoddnn hodd0.ne')

/-- A strictly stable odd-shape polynomial remains strictly stable after one
Routh reduction, including the terminal constant case. -/
theorem IsStrictlyHurwitzStable.routhReducedPolynomial_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree) :
    IsStrictlyHurwitzStable
      (routhReducedPolynomial (routhCoefficient odd even) odd even) := by
  obtain ⟨hoddnn, _⟩ :=
    h.hasNonnegCoeffs_parts_of_oddShape hodd heven hdegree
  obtain ⟨hodd0, _⟩ :=
    h.coeff_zero_pos_parts_of_oddShape hodd heven hdegree
  by_cases hdegreeZero : odd.natDegree = 0
  · have hevenDegreeZero : even.natDegree = 0 := hdegree.trans hdegreeZero
    have hredZero :
        routhReducedOddPart (routhCoefficient odd even) odd even = 0 := by
      ext n
      rw [coeff_routhReducedOddPart]
      have hoddCoeff : odd.coeff (n + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by lia)
      have hevenCoeff : even.coeff (n + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by lia)
      rw [hoddCoeff, hevenCoeff]
      simp
    have hoddC := Polynomial.eq_C_of_natDegree_eq_zero hdegreeZero
    have hredPolynomial :
        routhReducedPolynomial (routhCoefficient odd even) odd even =
          Polynomial.C (odd.coeff 0) := by
      rw [routhReducedPolynomial, hredZero, oddEvenPolynomial, hoddC]
      simp
    rw [hredPolynomial]
    exact (IsStrictlyHurwitzStable.C (odd.coeff 0)).2 hodd0.ne'
  · have hdegreePos : 0 < odd.natDegree := Nat.pos_of_ne_zero hdegreeZero
    obtain ⟨hprec, hrednn⟩ :=
      h.prec_routhReducedOddPart_of_oddShape
        hodd heven hdegree hdegreePos
    have hredPos : HasPosLeadingCoeff
        (routhReducedOddPart (routhCoefficient odd even) odd even) :=
      hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hrednn hprec.1.1
    have hHB := hermiteBiehlerForwardPos hodd hredPos hprec
    have hright :=
      hermiteBiehlerStableToHurwitzOddEven hrednn hoddnn hHB
    rw [routhReducedPolynomial]
    exact isStrictlyHurwitzStable_oddEvenPolynomial_of_rightHalfPlaneStable
      hright hodd0.ne'
        (h.noCommonRoot_routhReducedOddPart hoddnn hodd0.ne')

end RealRooted
