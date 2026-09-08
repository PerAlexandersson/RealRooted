import RealRooted.ClassicalHurwitzMatrix.Stability.Parity
import RealRooted.DegreeDropDivXPrec
import RealRooted.Interlacing.NegativeRoots
import RealRooted.SimpleRoots
import RealRooted.Wronskian.Forward
import RealRooted.Wronskian.Successor.Interlacing

/-!
# Algebraic data for stable Routh reduction

This module records the exact rotated recurrence and the degree and leading-
coefficient data used when transporting strict Hurwitz stability through one
Routh step. The analytic preservation theorem is built on these identities.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The Wronskian of the rotated parity parts, expressed at the unrotated
argument. At a root of either source part, the first summand vanishes and the
second summand transfers the strict Wronskian sign. -/
theorem wronskian_hurwitzRotatedParts_eval (odd even : ℝ[X]) (x : ℝ) :
    (hurwitzRotatedEvenPart even).derivative.eval x *
          (hurwitzRotatedOddPart odd).eval x -
        (hurwitzRotatedEvenPart even).eval x *
          (hurwitzRotatedOddPart odd).derivative.eval x =
      even.eval (-(x ^ 2)) * odd.eval (-(x ^ 2)) +
        2 * x ^ 2 *
          (even.derivative.eval (-(x ^ 2)) * odd.eval (-(x ^ 2)) -
            even.eval (-(x ^ 2)) * odd.derivative.eval (-(x ^ 2))) := by
  simp [hurwitzRotatedEvenPart, hurwitzRotatedOddPart,
    Polynomial.derivative_comp]
  ring

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

/-- A simple product `-X * p` can only have simple roots coming from `p`. -/
theorem hasSimpleRoots_of_neg_X_mul {p : ℝ[X]}
    (h : HasSimpleRoots (-X * p)) : HasSimpleRoots p := by
  have hp0 : p ≠ 0 := by
    intro hp
    exact h.ne_zero (by simp [hp])
  intro r hroot
  have hmul0 : -X * p ≠ 0 := h.ne_zero
  have hmulRoot : (-X * p).IsRoot r := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_mul]
    change p.eval r = 0 at hroot
    rw [hroot, mul_zero]
  have hmult := h r hmulRoot
  rw [Polynomial.rootMultiplicity_mul hmul0] at hmult
  have hpos := (Polynomial.rootMultiplicity_pos hp0).mpr hroot
  lia

/-- Simplicity descends through `p(X) ↦ p(-X²)` when all source roots are
nonpositive. A repeated source root would lift to a repeated real root at the
square root of its negation. -/
theorem hasSimpleRoots_of_comp_neg_X_sq {p : ℝ[X]} (hp0 : p ≠ 0)
    (hroots : ∀ r : ℝ, p.IsRoot r → r ≤ 0)
    (hcomp : HasSimpleRoots (p.comp (-(X ^ 2)))) : HasSimpleRoots p := by
  intro r hroot
  have hr_nonpos := hroots r hroot
  let w : ℝ := Real.sqrt (-r)
  have hw_sq : -(w ^ 2) = r := by
    rw [Real.sq_sqrt (by linarith : 0 ≤ -r)]
    ring
  have hcompRoot : (p.comp (-(X ^ 2))).IsRoot w := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_comp]
    simp only [Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hw_sq]
    exact hroot
  have hpos := (Polynomial.rootMultiplicity_pos hp0).mpr hroot
  by_contra hmult_ne
  have hmult_gt : 1 < p.rootMultiplicity r := by lia
  have hderRoot : p.derivative.IsRoot r :=
    ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hp0).mp hmult_gt).2
  change p.derivative.eval r = 0 at hderRoot
  apply hcomp.eval_derivative_ne_zero hcompRoot
  rw [Polynomial.derivative_comp, Polynomial.eval_mul,
    Polynomial.eval_comp]
  simp only [Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hw_sq]
  rw [hderRoot, mul_zero]

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

/-- In the even-degree parity shape, both unrotated parity inputs of a
strictly stable polynomial have simple real roots. -/
theorem IsStrictlyHurwitzStable.hasSimpleRoots_parts_of_evenShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) :
    HasSimpleRoots odd ∧ HasSimpleRoots even := by
  obtain ⟨hoddnn, hevennn⟩ :=
    h.hasNonnegCoeffs_parts_of_evenShape hodd heven hdegree
  obtain ⟨hrotOdd, hrotEven⟩ :=
    h.hasSimpleRoots_rotatedParts_of_evenShape hodd heven hdegree
  have hoddComp : HasSimpleRoots (odd.comp (-(X ^ 2))) :=
    hasSimpleRoots_of_neg_X_mul (by
      simpa only [hurwitzRotatedOddPart] using hrotOdd)
  constructor
  · apply hasSimpleRoots_of_comp_neg_X_sq hodd.ne_zero _ hoddComp
    intro r hroot
    exact roots_nonpos_of_hasNonnegCoeffs hoddnn r
      ((Polynomial.mem_roots hodd.ne_zero).mpr hroot)
  · apply hasSimpleRoots_of_comp_neg_X_sq heven.ne_zero _
      (by simpa only [hurwitzRotatedEvenPart] using hrotEven)
    intro r hroot
    exact roots_nonpos_of_hasNonnegCoeffs hevennn r
      ((Polynomial.mem_roots heven.ne_zero).mpr hroot)

/-- In the odd-degree parity shape, both unrotated parity inputs of a strictly
stable polynomial have simple real roots. -/
theorem IsStrictlyHurwitzStable.hasSimpleRoots_parts_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree) :
    HasSimpleRoots odd ∧ HasSimpleRoots even := by
  obtain ⟨hoddnn, hevennn⟩ :=
    h.hasNonnegCoeffs_parts_of_oddShape hodd heven hdegree
  obtain ⟨hrotEven, hrotOdd⟩ :=
    h.hasSimpleRoots_rotatedParts_of_oddShape hodd heven hdegree
  have hoddComp : HasSimpleRoots (odd.comp (-(X ^ 2))) :=
    hasSimpleRoots_of_neg_X_mul (by
      simpa only [hurwitzRotatedOddPart] using hrotOdd)
  constructor
  · apply hasSimpleRoots_of_comp_neg_X_sq hodd.ne_zero _ hoddComp
    intro r hroot
    exact roots_nonpos_of_hasNonnegCoeffs hoddnn r
      ((Polynomial.mem_roots hodd.ne_zero).mpr hroot)
  · apply hasSimpleRoots_of_comp_neg_X_sq heven.ne_zero _
      (by simpa only [hurwitzRotatedEvenPart] using hrotEven)
    intro r hroot
    exact roots_nonpos_of_hasNonnegCoeffs hevennn r
      ((Polynomial.mem_roots heven.ne_zero).mpr hroot)

/-- In the even-degree parity shape, the Wronskian of the raw rotated parts
has the strict sign needed to descend interlacing. -/
theorem IsStrictlyHurwitzStable.wronskian_rotatedParts_pos_of_evenShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) (x : ℝ) :
    0 < (hurwitzRotatedEvenPart even).derivative.eval x *
          (hurwitzRotatedOddPart odd).eval x -
        (hurwitzRotatedEvenPart even).eval x *
          (hurwitzRotatedOddPart odd).derivative.eval x := by
  let s : ℝ := (-1 : ℝ) ^ even.natDegree
  have hs0 : s ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsquare : s * s = 1 := by
    dsimp [s]
    rw [← pow_add]
    simp [← two_mul]
  have hsign : s = -((-1 : ℝ) ^ odd.natDegree) := by
    simp only [s, hdegree, pow_succ]
    ring
  have hprec := h.prec_rotatedParts_of_evenShape hodd heven hdegree
  have hprecScaled := (hprec.C_mul_left hs0).C_mul_right hs0
  have hevenPos : HasPosLeadingCoeff
      (Polynomial.C s * hurwitzRotatedEvenPart even) :=
    by simpa only [s] using
      hasPosLeadingCoeff_sign_mul_hurwitzRotatedEvenPart heven
  have hoddPos : HasPosLeadingCoeff
      (Polynomial.C s * hurwitzRotatedOddPart odd) := by
    rw [hsign]
    exact hasPosLeadingCoeff_neg_sign_mul_hurwitzRotatedOddPart hodd
  obtain ⟨hoddSimple, hevenSimple⟩ :=
    h.hasSimpleRoots_rotatedParts_of_evenShape hodd heven hdegree
  have hevenNodup :
      (Polynomial.C s * hurwitzRotatedEvenPart even).roots.Nodup := by
    rw [Polynomial.roots_C_mul _ hs0]
    exact hevenSimple.roots_nodup
  have hoddNodup :
      (Polynomial.C s * hurwitzRotatedOddPart odd).roots.Nodup := by
    rw [Polynomial.roots_C_mul _ hs0]
    exact hoddSimple.roots_nodup
  have hno (r : ℝ) :
      (Polynomial.C s * hurwitzRotatedEvenPart even).IsRoot r →
        ¬ (Polynomial.C s * hurwitzRotatedOddPart odd).IsRoot r := by
    intro hevenRoot hoddRoot
    apply h.noCommonRoot_rotatedParts r
    simp only [Polynomial.IsRoot.def, Polynomial.eval_mul,
      Polynomial.eval_C, mul_eq_zero, hs0, false_or] at hevenRoot hoddRoot
    exact ⟨hevenRoot, hoddRoot⟩
  have hW := wronskian_pos_of_prec_succ hevenPos hoddPos
    (by
      rw [Polynomial.natDegree_C_mul hs0,
        Polynomial.natDegree_C_mul hs0,
        natDegree_hurwitzRotatedEvenPart,
        natDegree_hurwitzRotatedOddPart hodd.ne_zero]
      lia)
    hprecScaled hevenNodup hoddNodup hno x
  have hscale :
      (Polynomial.C s * hurwitzRotatedEvenPart even).derivative.eval x *
            (Polynomial.C s * hurwitzRotatedOddPart odd).eval x -
          (Polynomial.C s * hurwitzRotatedEvenPart even).eval x *
            (Polynomial.C s * hurwitzRotatedOddPart odd).derivative.eval x =
        s * s *
          ((hurwitzRotatedEvenPart even).derivative.eval x *
              (hurwitzRotatedOddPart odd).eval x -
            (hurwitzRotatedEvenPart even).eval x *
              (hurwitzRotatedOddPart odd).derivative.eval x) := by
    simp only [Polynomial.derivative_C_mul, Polynomial.eval_mul,
      Polynomial.eval_C]
    ring
  rw [hscale, hsquare, one_mul] at hW
  exact hW

/-- In the odd-degree parity shape, opposite sign normalizations again give a
positive Wronskian for the raw rotated even/odd pair. -/
theorem IsStrictlyHurwitzStable.wronskian_rotatedParts_pos_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree) (x : ℝ) :
    0 < (hurwitzRotatedEvenPart even).derivative.eval x *
          (hurwitzRotatedOddPart odd).eval x -
        (hurwitzRotatedEvenPart even).eval x *
          (hurwitzRotatedOddPart odd).derivative.eval x := by
  let s : ℝ := (-1 : ℝ) ^ odd.natDegree
  let t : ℝ := -s
  have hs0 : s ≠ 0 := pow_ne_zero _ (by norm_num)
  have ht0 : t ≠ 0 := neg_ne_zero.mpr hs0
  have hsquare : s * s = 1 := by
    dsimp [s]
    rw [← pow_add]
    simp [← two_mul]
  have hprec := h.prec_rotatedParts_of_oddShape hodd heven hdegree
  have hprecScaled := (hprec.C_mul_left hs0).C_mul_right ht0
  have hevenPos : HasPosLeadingCoeff
      (Polynomial.C s * hurwitzRotatedEvenPart even) := by
    simpa only [s, hdegree] using
      hasPosLeadingCoeff_sign_mul_hurwitzRotatedEvenPart heven
  have hoddPos : HasPosLeadingCoeff
      (Polynomial.C t * hurwitzRotatedOddPart odd) := by
    simpa only [t, s] using
      hasPosLeadingCoeff_neg_sign_mul_hurwitzRotatedOddPart hodd
  obtain ⟨hevenSimple, hoddSimple⟩ :=
    h.hasSimpleRoots_rotatedParts_of_oddShape hodd heven hdegree
  have hoddNodup :
      (Polynomial.C t * hurwitzRotatedOddPart odd).roots.Nodup := by
    rw [Polynomial.roots_C_mul _ ht0]
    exact hoddSimple.roots_nodup
  have hevenNodup :
      (Polynomial.C s * hurwitzRotatedEvenPart even).roots.Nodup := by
    rw [Polynomial.roots_C_mul _ hs0]
    exact hevenSimple.roots_nodup
  have hno (r : ℝ) :
      (Polynomial.C t * hurwitzRotatedOddPart odd).IsRoot r →
        ¬ (Polynomial.C s * hurwitzRotatedEvenPart even).IsRoot r := by
    intro hoddRoot hevenRoot
    apply h.noCommonRoot_rotatedParts r
    simp only [Polynomial.IsRoot.def, Polynomial.eval_mul,
      Polynomial.eval_C, mul_eq_zero, hs0, ht0, false_or] at hoddRoot hevenRoot
    exact ⟨hevenRoot, hoddRoot⟩
  have hW := wronskian_pos_of_prec_succ hoddPos hevenPos
    (by
      rw [Polynomial.natDegree_C_mul ht0,
        Polynomial.natDegree_C_mul hs0,
        natDegree_hurwitzRotatedOddPart hodd.ne_zero,
        natDegree_hurwitzRotatedEvenPart, hdegree])
    hprecScaled hoddNodup hevenNodup hno x
  have hscale :
      (Polynomial.C t * hurwitzRotatedOddPart odd).derivative.eval x *
            (Polynomial.C s * hurwitzRotatedEvenPart even).eval x -
          (Polynomial.C t * hurwitzRotatedOddPart odd).eval x *
            (Polynomial.C s * hurwitzRotatedEvenPart even).derivative.eval x =
        (hurwitzRotatedEvenPart even).derivative.eval x *
            (hurwitzRotatedOddPart odd).eval x -
          (hurwitzRotatedEvenPart even).eval x *
            (hurwitzRotatedOddPart odd).derivative.eval x := by
    simp only [Polynomial.derivative_C_mul, Polynomial.eval_mul,
      Polynomial.eval_C]
    dsimp only [t]
    have hsquare' : s ^ 2 = 1 := by nlinarith [hsquare]
    ring_nf
    rw [hsquare']
    ring
  rw [hscale] at hW
  exact hW

/-- In the even-degree parity shape, strict stability descends from the
rotated Hermite--Biehler pair to strict interlacing of the original parity
inputs. -/
theorem IsStrictlyHurwitzStable.prec_parts_of_evenShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) : Prec odd even := by
  obtain ⟨hoddnn, hevennn⟩ :=
    h.hasNonnegCoeffs_parts_of_evenShape hodd heven hdegree
  obtain ⟨hoddSplits, hevenSplits⟩ :=
    h.splits_parts_of_evenShape hodd heven hdegree
  obtain ⟨_, heven0⟩ :=
    h.coeff_zero_pos_parts_of_evenShape hodd heven hdegree
  apply Interlaces.toPrec
  apply interlaces_of_wronskian_neg_succ_atRoots hodd heven rfl hdegree
    hoddSplits hevenSplits
  intro r hevenRoot
  have hr_nonpos : r ≤ 0 :=
    roots_nonpos_of_hasNonnegCoeffs hevennn r
      ((Polynomial.mem_roots heven.ne_zero).mpr hevenRoot)
  have hr_ne : r ≠ 0 := by
    intro hr
    subst r
    change even.eval 0 = 0 at hevenRoot
    rw [← Polynomial.coeff_zero_eq_eval_zero] at hevenRoot
    exact heven0.ne' hevenRoot
  have hr_neg : r < 0 := lt_of_le_of_ne hr_nonpos hr_ne
  let w : ℝ := Real.sqrt (-r)
  have hw_pos : 0 < w := Real.sqrt_pos.2 (by linarith)
  have hw_sq : -(w ^ 2) = r := by
    rw [Real.sq_sqrt (by linarith : 0 ≤ -r)]
    ring
  have hW := h.wronskian_rotatedParts_pos_of_evenShape
    hodd heven hdegree w
  rw [wronskian_hurwitzRotatedParts_eval, hw_sq] at hW
  change even.eval r = 0 at hevenRoot
  rw [hevenRoot] at hW ⊢
  simp only [zero_mul, zero_add, sub_zero] at hW
  have hprod : 0 < even.derivative.eval r * odd.eval r :=
    pos_of_mul_pos_right hW (by positivity)
  simp only [mul_zero, zero_sub]
  nlinarith

/-- In the odd-degree parity shape, strict stability descends from the
rotated Hermite--Biehler pair to strict same-degree proper position of the
original parity inputs. -/
theorem IsStrictlyHurwitzStable.prec_parts_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree) : Prec odd even := by
  obtain ⟨hoddnn, _⟩ :=
    h.hasNonnegCoeffs_parts_of_oddShape hodd heven hdegree
  obtain ⟨hoddSplits, hevenSplits⟩ :=
    h.splits_parts_of_oddShape hodd heven hdegree
  obtain ⟨hodd0, _⟩ :=
    h.coeff_zero_pos_parts_of_oddShape hodd heven hdegree
  by_cases hdegreeZero : odd.natDegree = 0
  · have hevenDegreeZero : even.natDegree = 0 := hdegree.trans hdegreeZero
    have hoddRoots : odd.roots = 0 := by
      rw [← Multiset.card_eq_zero, card_roots_of_splits hoddSplits,
        hdegreeZero]
    have hevenRoots : even.roots = 0 := by
      rw [← Multiset.card_eq_zero, card_roots_of_splits hevenSplits,
        hevenDegreeZero]
    exact ⟨⟨hodd.ne_zero, hoddSplits⟩, ⟨heven.ne_zero, hevenSplits⟩,
      [], [], by simp, by simp, by simp [hoddRoots], by simp [hevenRoots],
      Or.inr ⟨rfl, by simp [ListAlternates]⟩⟩
  · have hdegreePos : 0 < odd.natDegree := Nat.pos_of_ne_zero hdegreeZero
    let d := odd.natDegree - 1
    have hoddDegree : odd.natDegree = d + 1 := by
      dsimp only [d]
      lia
    have hWRoots : ∀ r : ℝ, odd.IsRoot r →
        0 < even.derivative.eval r * odd.eval r -
          even.eval r * odd.derivative.eval r := by
      intro r hoddRoot
      have hr_nonpos : r ≤ 0 :=
        roots_nonpos_of_hasNonnegCoeffs hoddnn r
          ((Polynomial.mem_roots hodd.ne_zero).mpr hoddRoot)
      have hr_ne : r ≠ 0 := by
        intro hr
        subst r
        change odd.eval 0 = 0 at hoddRoot
        rw [← Polynomial.coeff_zero_eq_eval_zero] at hoddRoot
        exact hodd0.ne' hoddRoot
      have hr_neg : r < 0 := lt_of_le_of_ne hr_nonpos hr_ne
      let w : ℝ := Real.sqrt (-r)
      have hw_pos : 0 < w := Real.sqrt_pos.2 (by linarith)
      have hw_sq : -(w ^ 2) = r := by
        rw [Real.sq_sqrt (by linarith : 0 ≤ -r)]
        ring
      have hW := h.wronskian_rotatedParts_pos_of_oddShape
        hodd heven hdegree w
      rw [wronskian_hurwitzRotatedParts_eval, hw_sq] at hW
      change odd.eval r = 0 at hoddRoot
      rw [hoddRoot] at hW ⊢
      simp only [mul_zero, zero_add, zero_sub] at hW
      have hprod : 0 < -(even.eval r * odd.derivative.eval r) :=
        pos_of_mul_pos_right hW (by positivity)
      simpa only [mul_zero, zero_sub] using hprod
    have hW : ∀ t : ℝ,
        0 < even.derivative.eval t * odd.eval t -
          even.eval t * odd.derivative.eval t :=
      wronskian_pos_of_pos_at_roots hoddSplits hoddDegree
        (by rw [hdegree, hoddDegree]) hWRoots
    exact (StrictPrecSameDegree.of_wronskian_pos hodd heven rfl hdegree
      hoddSplits hevenSplits hW).to_prec

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

/-- Subtracting a scalar multiple of the left member preserves the
all-real-combinations plane generated by a proper-position pair. -/
theorem allComboRealRooted_routhNumerator {odd even : ℝ[X]}
    (hprec : Prec odd even) (c : ℝ) :
    AllComboRealRooted odd (even - C c * odd) := by
  apply allComboRealRooted_linear_recombination
    (f := odd) (g := even) (a := 1) (b := 0) (c := -c) (d := 1)
    (hall := allComboRealRooted_of_prec hprec)
  · simp
  · simp [sub_eq_add_neg, mul_comm, add_comm]

/-- In an even-shape Routh step, the reduced input precedes the old odd
input and has nonnegative coefficients. -/
theorem IsStrictlyHurwitzStable.prec_routhReducedOddPart_of_evenShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) :
    Prec (routhReducedOddPart (routhCoefficient odd even) odd even) odd ∧
      HasNonnegCoeffs
        (routhReducedOddPart (routhCoefficient odd even) odd even) := by
  obtain ⟨hoddnn, _⟩ :=
    h.hasNonnegCoeffs_parts_of_evenShape hodd heven hdegree
  obtain ⟨hodd0, _⟩ :=
    h.coeff_zero_pos_parts_of_evenShape hodd heven hdegree
  have hprec := h.prec_parts_of_evenShape hodd heven hdegree
  let c := routhCoefficient odd even
  let q := even - Polynomial.C c * odd
  have hlt : (Polynomial.C c * odd).natDegree < even.natDegree := by
    calc
      (Polynomial.C c * odd).natDegree ≤ odd.natDegree :=
        Polynomial.natDegree_C_mul_le c odd
      _ < even.natDegree := by lia
  have hqDegree : q.natDegree = even.natDegree := by
    dsimp only [q]
    exact Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt
  have hqPos : HasPosLeadingCoeff q := by
    rw [HasPosLeadingCoeff, Polynomial.leadingCoeff, hqDegree]
    dsimp only [q]
    rw [Polynomial.coeff_sub,
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt, sub_zero]
    exact heven
  have hq0 : q.coeff 0 = 0 := by
    dsimp only [q, c]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, sub_eq_zero]
    exact routhCoefficient_mul_coeff_zero odd even hodd0.ne'
  have hqRoot : q.IsRoot 0 := by
    rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero]
    exact hq0
  have hall : AllComboRealRooted odd q := by
    simpa only [q] using allComboRealRooted_routhNumerator hprec c
  have hqSplits : q.Splits := hall.right_splits
  have hprecQ : Prec odd q := by
    rcases prec_of_allComboRealRooted hodd.ne_zero hprec.1.2
        hqPos.ne_zero hqSplits hall (Or.inl (by lia)) with hoq | hqo
    · exact hoq
    · rcases hqo.natDegree_eq_or_eq_succ with hsame | hsucc <;> lia
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
  have hqNonpos : ∀ r, q.IsRoot r → r ≤ 0 :=
    roots_nonpos_of_interlaces_of_zero_root_of_roots_neg
      (hprecQ.toInterlaces (by lia)) hqRoot hoddNeg
  have hqnn : HasNonnegCoeffs q :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hqSplits).2
      ⟨hqPos, fun r hr =>
        hqNonpos r ((Polynomial.mem_roots hqPos.ne_zero).mp hr)⟩).1
  have hredPrec : Prec q.divX odd :=
    prec_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero
      hprecQ hqnn hq0 (by lia)
  change Prec q.divX odd ∧ HasNonnegCoeffs q.divX
  exact ⟨hredPrec, hqnn.divX⟩

end RealRooted
