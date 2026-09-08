import RealRooted.ClassicalHurwitzMatrix.Routh.Sequence
import RealRooted.ClassicalHurwitzMatrix.Routh.TotallyNonnegative
import RealRooted.ClassicalHurwitzMatrix.Stability.Routh.ProperPosition
import RealRooted.ClassicalHurwitzMatrix.TotallyNonnegative

/-!
# Stable Routh sequences and leading Hurwitz determinants

The one-step strict-stability theorem is iterated here by induction on the
order of the requested leading principal determinant.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A nonterminal odd-shape Routh step lowers the degree of the represented
polynomial by exactly one. -/
theorem IsStrictlyHurwitzStable.natDegree_routhReducedPolynomial_add_one_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree)
    (hdegreePos : 0 < odd.natDegree) :
    (routhReducedPolynomial (routhCoefficient odd even) odd even).natDegree + 1 =
      (oddEvenPolynomial odd even).natDegree := by
  have hredDegree :=
    h.natDegree_routhReducedOddPart_add_one_of_oddShape
      hodd heven hdegree hdegreePos
  have hredData :=
    h.prec_routhReducedOddPart_of_oddShape
      hodd heven hdegree hdegreePos
  have hredPos : HasPosLeadingCoeff
      (routhReducedOddPart (routhCoefficient odd even) odd even) :=
    hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hredData.2 hredData.1.1.1
  rw [routhReducedPolynomial,
    natDegree_oddEvenPolynomial hredPos.ne_zero,
    natDegree_oddEvenPolynomial hodd.ne_zero, hdegree]
  rw [max_eq_left (by lia), max_eq_right (by lia)]

end RealRooted

namespace Matrix

open RealRooted

/-- Strict Hurwitz stability and the natural positive-leading parity shape
force every leading classical Hurwitz determinant through the polynomial's
degree to be positive. -/
theorem hurwitzLeadingPrincipal_oddEvenPolynomial_det_pos_of_strictlyStable
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hshape : even.natDegree = odd.natDegree + 1 ∨
      even.natDegree = odd.natDegree) :
    ∀ n, n ≤ (oddEvenPolynomial odd even).natDegree →
      0 < (hurwitzLeadingPrincipal
        (oddEvenPolynomial odd even).coeff n).det := by
  intro n hn
  induction n generalizing odd even with
  | zero => simp
  | succ n ih =>
      rcases hshape with hevenShape | hoddShape
      · obtain ⟨hodd0, heven0⟩ :=
          h.coeff_zero_pos_parts_of_evenShape hodd heven hevenShape
        obtain ⟨hredPrec, hrednn⟩ :=
          h.prec_routhReducedOddPart_of_evenShape hodd heven hevenShape
        have hredPos : HasPosLeadingCoeff
            (routhReducedOddPart (routhCoefficient odd even) odd even) :=
          hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero
            hrednn hredPrec.1.1
        have hredStable :=
          h.routhReducedPolynomial_of_evenShape hodd heven hevenShape
        have hredShape : odd.natDegree =
            (routhReducedOddPart
              (routhCoefficient odd even) odd even).natDegree := by
          rw [natDegree_routhReducedOddPart_of_evenShape _ hevenShape]
        have hdegreeDrop :=
          natDegree_routhReducedPolynomial_add_one_of_evenShape
            (routhCoefficient odd even) hodd heven hevenShape
        rw [hurwitzLeadingPrincipal_oddEvenPolynomial_det_succ_ratio
          odd even hodd0.ne' n]
        apply mul_pos heven0
        refine ih (odd := routhReducedOddPart
            (routhCoefficient odd even) odd even) (even := odd)
          hredStable hredPos hodd (Or.inr hredShape) ?_
        change n ≤
          (routhReducedPolynomial
            (routhCoefficient odd even) odd even).natDegree
        lia
      · obtain ⟨hodd0, heven0⟩ :=
          h.coeff_zero_pos_parts_of_oddShape hodd heven hoddShape
        by_cases hdegreeZero : odd.natDegree = 0
        · have hnZero : n = 0 := by
            rw [natDegree_oddEvenPolynomial hodd.ne_zero,
              hoddShape, hdegreeZero] at hn
            simp at hn
            lia
          subst n
          rw [hurwitzLeadingPrincipal_oddEvenPolynomial_det_succ_ratio
            odd even hodd0.ne' 0]
          simpa using heven0
        · have hdegreePos : 0 < odd.natDegree :=
            Nat.pos_of_ne_zero hdegreeZero
          obtain ⟨hredPrec, hrednn⟩ :=
            h.prec_routhReducedOddPart_of_oddShape
              hodd heven hoddShape hdegreePos
          have hredPos : HasPosLeadingCoeff
              (routhReducedOddPart (routhCoefficient odd even) odd even) :=
            hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero
              hrednn hredPrec.1.1
          have hredStable :=
            h.routhReducedPolynomial_of_oddShape hodd heven hoddShape
          have hredShape :=
            h.natDegree_routhReducedOddPart_add_one_of_oddShape
              hodd heven hoddShape hdegreePos
          have hdegreeDrop :=
            h.natDegree_routhReducedPolynomial_add_one_of_oddShape
              hodd heven hoddShape hdegreePos
          rw [hurwitzLeadingPrincipal_oddEvenPolynomial_det_succ_ratio
            odd even hodd0.ne' n]
          apply mul_pos heven0
          refine ih (odd := routhReducedOddPart
              (routhCoefficient odd even) odd even) (even := odd)
            hredStable hredPos hodd (Or.inl hredShape.symm) ?_
          change n ≤
            (routhReducedPolynomial
              (routhCoefficient odd even) odd even).natDegree
          lia

/-- Strict Hurwitz stability and the natural positive-leading parity shape
force total nonnegativity of the infinite classical Hurwitz matrix. -/
theorem hurwitz_oddEvenPolynomial_isTotallyNonneg_of_strictlyStable
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hshape : even.natDegree = odd.natDegree + 1 ∨
      even.natDegree = odd.natDegree) :
    (hurwitz (oddEvenPolynomial odd even).coeff).IsTotallyNonneg := by
  rcases hshape with hevenShape | hoddShape
  · obtain ⟨hodd0, heven0⟩ :=
      h.coeff_zero_pos_parts_of_evenShape hodd heven hevenShape
    obtain ⟨hredPrec, hrednn⟩ :=
      h.prec_routhReducedOddPart_of_evenShape hodd heven hevenShape
    have hredPos : HasPosLeadingCoeff
        (routhReducedOddPart (routhCoefficient odd even) odd even) :=
      hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hrednn hredPrec.1.1
    have hredStable :=
      h.routhReducedPolynomial_of_evenShape hodd heven hevenShape
    have hredShape : odd.natDegree =
        (routhReducedOddPart
          (routhCoefficient odd even) odd even).natDegree := by
      rw [natDegree_routhReducedOddPart_of_evenShape _ hevenShape]
    have htail :=
      hurwitz_oddEvenPolynomial_isTotallyNonneg_of_strictlyStable
        hredStable hredPos hodd (Or.inr hredShape)
    exact htail.hurwitz_oddEvenPolynomial_of_routhReduced_of_pos hodd0 heven0
  · obtain ⟨hodd0, heven0⟩ :=
      h.coeff_zero_pos_parts_of_oddShape hodd heven hoddShape
    by_cases hdegreeZero : odd.natDegree = 0
    · have hevenDegreeZero : even.natDegree = 0 :=
        hoddShape.trans hdegreeZero
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
      have htail :
          (hurwitz
            (routhReducedPolynomial
              (routhCoefficient odd even) odd even).coeff).IsTotallyNonneg := by
        rw [hredPolynomial]
        exact hurwitz_C_isTotallyNonneg _ hodd0.le
      exact htail.hurwitz_oddEvenPolynomial_of_routhReduced_of_pos
        hodd0 heven0
    · have hdegreePos : 0 < odd.natDegree :=
        Nat.pos_of_ne_zero hdegreeZero
      obtain ⟨hredPrec, hrednn⟩ :=
        h.prec_routhReducedOddPart_of_oddShape
          hodd heven hoddShape hdegreePos
      have hredPos : HasPosLeadingCoeff
          (routhReducedOddPart (routhCoefficient odd even) odd even) :=
        hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero
          hrednn hredPrec.1.1
      have hredStable :=
        h.routhReducedPolynomial_of_oddShape hodd heven hoddShape
      have hredShape :=
        h.natDegree_routhReducedOddPart_add_one_of_oddShape
          hodd heven hoddShape hdegreePos
      have htail :=
        hurwitz_oddEvenPolynomial_isTotallyNonneg_of_strictlyStable
          hredStable hredPos hodd (Or.inl hredShape.symm)
      exact htail.hurwitz_oddEvenPolynomial_of_routhReduced_of_pos
        hodd0 heven0
termination_by (oddEvenPolynomial odd even).natDegree
decreasing_by
  · have hdegreeDrop :=
      natDegree_routhReducedPolynomial_add_one_of_evenShape
        (routhCoefficient odd even) hodd heven hevenShape
    change
      (routhReducedPolynomial
        (routhCoefficient odd even) odd even).natDegree <
        (oddEvenPolynomial odd even).natDegree
    lia
  · have hdegreeDrop :=
      h.natDegree_routhReducedPolynomial_add_one_of_oddShape
        hodd heven hoddShape hdegreePos
    change
      (routhReducedPolynomial
        (routhCoefficient odd even) odd even).natDegree <
        (oddEvenPolynomial odd even).natDegree
    lia

end Matrix
