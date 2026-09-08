import RealRooted.ClassicalHurwitzMatrix.Stability.Parity
import RealRooted.SimpleRoots

/-!
# Algebraic data for stable Routh reduction

This module records the exact rotated recurrence and the degree and leading-
coefficient data used when transporting strict Hurwitz stability through one
Routh step. The analytic preservation theorem is built on these identities.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The two rotated parity parts of a strictly Hurwitz-stable polynomial have
no common real root. Such a root would lie on the forbidden boundary of the
closed upper half plane after rotation. -/
theorem IsStrictlyHurwitzStable.noCommonRoot_rotatedParts
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even)) (r : ℝ) :
    ¬ ((hurwitzRotatedEvenPart even).IsRoot r ∧
      (hurwitzRotatedOddPart odd).IsRoot r) := by
  rintro ⟨heven, hodd⟩
  have hne := h.closedUpperHalfPlaneStable_rotatedParts (r : ℂ) (by simp)
  apply hne
  rw [eval_hermiteBiehlerPolynomial, eval_complexify_ofReal,
    eval_complexify_ofReal]
  change (hurwitzRotatedEvenPart even).eval r = 0 at heven
  change (hurwitzRotatedOddPart odd).eval r = 0 at hodd
  rw [heven, hodd]
  simp

/-- If the odd parity input has nonpositive roots, strict Hurwitz stability
also rules out a common real root of the unrotated parity inputs. The square
root of the negated common root would give a common rotated root. -/
theorem IsStrictlyHurwitzStable.noCommonRoot_parts_of_hasNonnegCoeffs
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd0 : odd ≠ 0) (hoddnn : HasNonnegCoeffs odd) (r : ℝ) :
    ¬ (odd.IsRoot r ∧ even.IsRoot r) := by
  rintro ⟨hoddRoot, hevenRoot⟩
  have hr_nonpos : r ≤ 0 :=
    roots_nonpos_of_hasNonnegCoeffs hoddnn r
      ((Polynomial.mem_roots hodd0).mpr hoddRoot)
  let w : ℝ := Real.sqrt (-r)
  have hw_sq : -(w ^ 2) = r := by
    rw [Real.sq_sqrt (by linarith : 0 ≤ -r)]
    ring
  apply h.noCommonRoot_rotatedParts w
  constructor
  · change (even.comp (-(X ^ 2))).IsRoot w
    rw [Polynomial.IsRoot.def, Polynomial.eval_comp]
    simp only [Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hw_sq]
    exact hevenRoot
  · change (-X * odd.comp (-(X ^ 2))).IsRoot w
    rw [Polynomial.IsRoot.def, Polynomial.eval_mul,
      Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_comp]
    simp only [Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hw_sq, hoddRoot]
    ring

private theorem hasSimpleRoots_pair_of_prec_of_noCommon
    {f g : ℝ[X]} (hprec : Prec f g)
    (hno : ∀ r : ℝ, ¬ (f.IsRoot r ∧ g.IsRoot r)) :
    HasSimpleRoots f ∧ HasSimpleRoots g := by
  constructor
  · intro r hroot
    have hother : ¬ g.IsRoot r := fun hr ↦ hno r ⟨hroot, hr⟩
    have hotherMult : g.rootMultiplicity r = 0 := by simp_all
    have hpos : 0 < f.rootMultiplicity r :=
      (Polynomial.rootMultiplicity_pos hprec.1.1).mpr hroot
    have hbound := (rootMultiplicity_bounds_of_prec hprec r).1
    lia
  · intro r hroot
    have hother : ¬ f.IsRoot r := fun hr ↦ hno r ⟨hr, hroot⟩
    have hotherMult : f.rootMultiplicity r = 0 := by simp_all
    have hpos : 0 < g.rootMultiplicity r :=
      (Polynomial.rootMultiplicity_pos hprec.2.1.1).mpr hroot
    have hbound := (rootMultiplicity_bounds_of_prec hprec r).2
    lia

/-- In the even-degree parity shape, both rotated parts of a strictly stable
polynomial have simple real roots. -/
theorem IsStrictlyHurwitzStable.hasSimpleRoots_rotatedParts_of_evenShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) :
    HasSimpleRoots (hurwitzRotatedOddPart odd) ∧
      HasSimpleRoots (hurwitzRotatedEvenPart even) := by
  exact hasSimpleRoots_pair_of_prec_of_noCommon
    (h.prec_rotatedParts_of_evenShape hodd heven hdegree)
    (fun r hr ↦ h.noCommonRoot_rotatedParts r ⟨hr.2, hr.1⟩)

/-- In the odd-degree parity shape, both rotated parts of a strictly stable
polynomial have simple real roots. -/
theorem IsStrictlyHurwitzStable.hasSimpleRoots_rotatedParts_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree) :
    HasSimpleRoots (hurwitzRotatedEvenPart even) ∧
      HasSimpleRoots (hurwitzRotatedOddPart odd) := by
  exact hasSimpleRoots_pair_of_prec_of_noCommon
    (h.prec_rotatedParts_of_oddShape hodd heven hdegree)
    h.noCommonRoot_rotatedParts

/-- The defining Routh recurrence after the `X ↦ -X²` rotation. -/
theorem hurwitzRotatedEvenPart_eq_routh
    (c : ℝ) (odd even : ℝ[X])
    (h0 : even.coeff 0 = c * odd.coeff 0) :
    hurwitzRotatedEvenPart even =
      C c * odd.comp (-(X ^ 2)) +
        X * hurwitzRotatedOddPart (routhReducedOddPart c odd even) := by
  have h := congrArg (fun p : ℝ[X] => p.comp (-(X ^ 2)))
    (even_eq_C_mul_odd_add_X_mul_routhReducedOddPart c odd even h0)
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_comp] at h
  rw [hurwitzRotatedEvenPart, h, hurwitzRotatedOddPart]
  ring

/-- Ratio-specialized form of the rotated Routh recurrence. -/
theorem hurwitzRotatedEvenPart_eq_routh_ratio
    (odd even : ℝ[X]) (hodd0 : odd.coeff 0 ≠ 0) :
    hurwitzRotatedEvenPart even =
      C (routhCoefficient odd even) * odd.comp (-(X ^ 2)) +
        X * hurwitzRotatedOddPart
          (routhReducedOddPart (routhCoefficient odd even) odd even) :=
  hurwitzRotatedEvenPart_eq_routh _ _ _
    (routhCoefficient_mul_coeff_zero odd even hodd0)

/-- In an even-shape Routh step, division by `X` lowers the dominant even
input exactly to the degree of the odd input. -/
theorem natDegree_routhReducedOddPart_of_evenShape
    (c : ℝ) {odd even : ℝ[X]}
    (hdegree : even.natDegree = odd.natDegree + 1) :
    (routhReducedOddPart c odd even).natDegree = odd.natDegree := by
  rw [routhReducedOddPart, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  have hlt : (C c * odd).natDegree < even.natDegree := by
    calc
      (C c * odd).natDegree ≤ odd.natDegree :=
        Polynomial.natDegree_C_mul_le c odd
      _ < even.natDegree := by lia
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hdegree]
  lia

/-- The reduced odd input inherits the leading coefficient of the dominant
even input in an even-shape Routh step. -/
theorem leadingCoeff_routhReducedOddPart_of_evenShape
    (c : ℝ) {odd even : ℝ[X]}
    (hdegree : even.natDegree = odd.natDegree + 1) :
    (routhReducedOddPart c odd even).leadingCoeff = even.leadingCoeff := by
  rw [Polynomial.leadingCoeff,
    natDegree_routhReducedOddPart_of_evenShape c hdegree,
    coeff_routhReducedOddPart, ← hdegree, Polynomial.coeff_natDegree]
  have hlt : odd.natDegree < even.natDegree := by lia
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
  ring

/-- Positive leading coefficient passes to the reduced odd input in an
even-shape Routh step. -/
theorem hasPosLeadingCoeff_routhReducedOddPart_of_evenShape
    (c : ℝ) {odd even : ℝ[X]} (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) :
    HasPosLeadingCoeff (routhReducedOddPart c odd even) := by
  rw [HasPosLeadingCoeff,
    leadingCoeff_routhReducedOddPart_of_evenShape c hdegree]
  exact heven

/-- An even-shape Routh step lowers the degree of the represented polynomial
by exactly one. -/
theorem natDegree_routhReducedPolynomial_add_one_of_evenShape
    (c : ℝ) {odd even : ℝ[X]}
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) :
    (routhReducedPolynomial c odd even).natDegree + 1 =
      (oddEvenPolynomial odd even).natDegree := by
  have hredPos :=
    hasPosLeadingCoeff_routhReducedOddPart_of_evenShape c heven hdegree
  rw [routhReducedPolynomial,
    natDegree_oddEvenPolynomial hredPos.ne_zero,
    natDegree_oddEvenPolynomial hodd.ne_zero,
    natDegree_routhReducedOddPart_of_evenShape c hdegree, hdegree]
  rw [max_eq_right (by lia : 2 * odd.natDegree ≤ 2 * odd.natDegree + 1)]
  rw [max_eq_left
    (by lia : 2 * odd.natDegree + 1 ≤ 2 * (odd.natDegree + 1))]
  lia

/-- In an odd-shape Routh step, constant-term cancellation makes the reduced
odd input at least one degree smaller than the new even input. -/
theorem natDegree_routhReducedOddPart_le_pred_of_oddShape
    (c : ℝ) {odd even : ℝ[X]}
    (hdegree : even.natDegree = odd.natDegree) :
    (routhReducedOddPart c odd even).natDegree ≤ odd.natDegree - 1 := by
  rw [routhReducedOddPart, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  apply Nat.sub_le_sub_right
  calc
    (even - C c * odd).natDegree ≤
        max even.natDegree (C c * odd).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ odd.natDegree := by
      rw [hdegree]
      exact max_le le_rfl (Polynomial.natDegree_C_mul_le c odd)

/-- Away from the terminal linear case, the odd-shape Routh remainder is
nonzero. Otherwise the two parity inputs would be proportional and hence
would share a root. -/
theorem IsStrictlyHurwitzStable.routhReducedOddPart_ne_zero_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree)
    (hdegreePos : 0 < odd.natDegree) :
    routhReducedOddPart (routhCoefficient odd even) odd even ≠ 0 := by
  obtain ⟨hoddnn, _⟩ :=
    h.hasNonnegCoeffs_parts_of_oddShape hodd heven hdegree
  obtain ⟨hodd0, _⟩ :=
    h.coeff_zero_pos_parts_of_oddShape hodd heven hdegree
  have hoddSplits :=
    (h.splits_parts_of_oddShape hodd heven hdegree).1
  obtain ⟨r, hroot⟩ :=
    exists_isRoot_of_isRealRooted_of_not_isUnit hodd.ne_zero hoddSplits
      (Polynomial.not_isUnit_of_natDegree_pos odd hdegreePos)
  intro hred
  apply h.noCommonRoot_parts_of_hasNonnegCoeffs hodd.ne_zero hoddnn r
  refine ⟨hroot, ?_⟩
  have heq :=
    even_eq_C_mul_odd_add_X_mul_routhReducedOddPart_ratio
      odd even hodd0.ne'
  rw [Polynomial.IsRoot.def, heq, hred]
  change odd.eval r = 0 at hroot
  simp only [Polynomial.eval_mul, Polynomial.eval_C, mul_zero, add_zero]
  exact mul_eq_zero_of_right _ hroot

end RealRooted
