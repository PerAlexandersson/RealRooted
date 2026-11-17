module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.RingTheory.Polynomial.Wronskian
import RealRooted.HermiteBiehler.OrientedPencil
import RealRooted.CriticalValueContinuation
import RealRooted.DegreeDropReversal
import RealRooted.Interlacing.Residue
public import RealRooted.IteratedDerivativeShift
import RealRooted.LiuOppositeSigns.JensenRootCount
import RealRooted.Mathlib.Data.List.Zip
import RealRooted.PFPolynomial.Closure
import RealRooted.RootCountLocalConstancy
import RealRooted.RootCounting.CrossingExhaustion
public import RealRooted.RootCounting.Descartes
import RealRooted.SameDegreeMultiplicityLowerCount
import RealRooted.Wronskian.WeakForward
import RealRooted.Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import RealRooted.Mathlib.Algebra.Polynomial.RuleOfSigns
import RealRooted.Mathlib.RingTheory.Polynomial.Wronskian
import RealRooted.HermiteBiehler.Converse
import RealRooted.HermiteBiehler.ConverseLowDegree
import RealRooted.HermiteBiehler.Forward
public import RealRooted.HermiteBiehler.Basic
import RealRooted.ObreschkoffConverse.Derivative
import RealRooted.ObreschkoffConverse.Forward
import RealRooted.ObreschkoffConverse.Converse
public import RealRooted.AllCombo
import RealRooted.Mathlib.Algebra.Polynomial.Eval.Defs
import RealRooted.Linear
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignVariation
public import RealRooted.QuadraticInterlacing.Basic
import RealRooted.QuadraticInterlacing.Residue

/-!
# Quadratic interlacing preservation

Assembly of forward and reciprocal regularized paths and the final
quadratic tangent and right-pencil interlacing conclusions.
-/

public section

open Polynomial
open SignType
open Topology
open scoped ContDiff

noncomputable section

namespace RealRooted

private lemma hasNonnegCoeffs_quadraticInterlacingPencil
    {F G H : ℝ[X]} (hF : HasNonnegCoeffs F) (hG : HasNonnegCoeffs G)
    (hH : HasNonnegCoeffs H) {a : ℝ} (ha : 0 ≤ a) :
    HasNonnegCoeffs (quadraticInterlacingPencil F G H a) :=
  (hH.add (hasNonnegCoeffs_C_mul (mul_nonneg (by norm_num) ha) hG)).add
    (hasNonnegCoeffs_C_mul (sq_nonneg a) hF)


/-- A negative derivative shift gives the forward pencil all simple-path hypotheses. -/
private theorem regularized_quadraticInterlacingPencil_forward_data
    {F G H : ℝ[X]} (hF : HasNonnegCoeffs F) (hG : HasNonnegCoeffs G)
    (hH : HasNonnegCoeffs H) (hFG : StrictInterl F G)
    (hGH : StrictInterl G H)
    (hsplits : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).Splits)
    (hHdeg : H.natDegree ≠ 0) {eps : ℝ} (heps : 0 < eps) :
    let D := H.natDegree
    let Fε := iterateTDeriv (-eps) D F
    let Gε := iterateTDeriv (-eps) D G
    let Hε := iterateTDeriv (-eps) D H
    (∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil Fε Gε Hε b).natDegree = D) ∧
    (∀ b : ℝ, 0 ≤ b → ∀ᶠ c in nhds b,
      (quadraticInterlacingPencil Fε Gε Hε c).natDegree = D) ∧
    (∀ b : ℝ, 0 ≤ b →
      HasPosLeadingCoeff (quadraticInterlacingPencil Fε Gε Hε b)) ∧
    (∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil Fε Gε Hε b).Splits) ∧
    (∀ b : ℝ, 0 ≤ b →
      HasSimpleRoots (quadraticInterlacingPencil Fε Gε Hε b)) ∧
    ∀ b : ℝ, 0 ≤ b → ∀ q ∈
      (quadraticInterlacingPencil Fε Gε Hε b).roots, q < 0 := by
  let D := H.natDegree
  let Fε := iterateTDeriv (-eps) D F
  let Gε := iterateTDeriv (-eps) D G
  let Hε := iterateTDeriv (-eps) D H
  have hFdeg : F.natDegree ≤ D := hFG.natDegree_le.trans hGH.natDegree_le
  have hGdeg : G.natDegree ≤ D := hGH.natDegree_le
  have hHne : H ≠ 0 := hGH.2.1.1
  have hQnn : ∀ b : ℝ, 0 ≤ b →
      HasNonnegCoeffs (quadraticInterlacingPencil F G H b) :=
    fun _ hb => hasNonnegCoeffs_quadraticInterlacingPencil hF hG hH hb
  have hQdegree : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).natDegree = D :=
    fun _ hb => natDegree_quadraticInterlacingPencil_eq
      hF hG hH hHne hFdeg hGdeg hb
  have hQne : ∀ b : ℝ, 0 ≤ b →
      quadraticInterlacingPencil F G H b ≠ 0 := fun b hb hzero =>
    hHdeg (by simpa [D, hzero] using (hQdegree b hb).symm)
  have hFεnn : HasNonnegCoeffs Fε := hF.iterateTDeriv_neg heps.le D
  have hGεnn : HasNonnegCoeffs Gε := hG.iterateTDeriv_neg heps.le D
  have hHεnn : HasNonnegCoeffs Hε := hH.iterateTDeriv_neg heps.le D
  have hFεdeg : Fε.natDegree ≤ D := by simpa [Fε, D] using hFdeg
  have hGεdeg : Gε.natDegree ≤ D := by simpa [Gε, D] using hGdeg
  have hHεdeg : Hε.natDegree ≤ D := by simp [Hε, D]
  have hQεdegree : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil Fε Gε Hε b).natDegree = D := fun b hb => by
    rw [← iterateTDeriv_quadraticInterlacingPencil, natDegree_iterateTDeriv]
    exact hQdegree b hb
  have hQεdegreeLocal : ∀ b : ℝ, 0 ≤ b → ∀ᶠ c in nhds b,
      (quadraticInterlacingPencil Fε Gε Hε c).natDegree = D := fun b hb =>
    Polynomial.eventually_natDegree_eq_of_le_of_continuous_coeff
      (fun c => quadraticInterlacingPencil Fε Gε Hε c) (hQεdegree b hb)
      (fun hzero => hHdeg (by simpa [D, hzero] using (hQεdegree b hb).symm))
      (natDegree_quadraticInterlacingPencil_le hFεdeg hGεdeg hHεdeg)
      fun i => (contDiff_coeff_quadraticInterlacingPencil Fε Gε Hε i).continuous
  have hQεnn : ∀ b : ℝ, 0 ≤ b →
      HasNonnegCoeffs (quadraticInterlacingPencil Fε Gε Hε b) :=
    fun _ hb => hasNonnegCoeffs_quadraticInterlacingPencil hFεnn hGεnn hHεnn hb
  have hQεne : ∀ b : ℝ, 0 ≤ b →
      quadraticInterlacingPencil Fε Gε Hε b ≠ 0 := fun b hb hzero =>
    hHdeg (by simpa [D, hzero] using (hQεdegree b hb).symm)
  refine ⟨hQεdegree, hQεdegreeLocal,
    fun b hb => (hQεnn b hb).pos_leadingCoeff (hQεne b hb), ?_, ?_, ?_⟩
  · intro b hb
    rw [← iterateTDeriv_quadraticInterlacingPencil]
    exact splits_iterateTDeriv_all (hsplits b hb) D
  · exact fun _ hb => hasSimpleRoots_regularized_quadraticInterlacingPencil
      heps hQne hsplits (fun c hc => (hQdegree c hc).le) hb
  · intro b hb
    apply roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne (hQεnn b hb)
    have hpos := coeff_zero_iterateTDeriv_neg_pos_of_natDegree_le
      heps (hQnn b hb) (hQne b hb) (k := D) (hQdegree b hb).le
    rw [iterateTDeriv_quadraticInterlacingPencil] at hpos
    exact hpos.ne'

/-- A negative derivative shift gives the reciprocal pencil its root-location package. -/
private theorem regularized_quadraticInterlacingPencil_reciprocal_data
    {F G H : ℝ[X]} (hF : HasNonnegCoeffs F) (hG : HasNonnegCoeffs G)
    (hH : HasNonnegCoeffs H) (hFG : StrictInterl F G)
    (hGH : StrictInterl G H)
    (hsplits : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).Splits)
    {eps : ℝ} (heps : 0 < eps) :
    let D := H.natDegree
    let Fε := iterateTDeriv (-eps) D F
    let Gε := iterateTDeriv (-eps) D G
    let Hε := iterateTDeriv (-eps) D H
    (∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil Hε Gε Fε b).Splits) ∧
    (∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil Hε Gε Fε b).coeff 0 ≠ 0) ∧
    ∀ b : ℝ, 0 ≤ b → ∀ q ∈
      (quadraticInterlacingPencil Hε Gε Fε b).roots, q < 0 := by
  let D := H.natDegree
  let Fε := iterateTDeriv (-eps) D F
  let Gε := iterateTDeriv (-eps) D G
  let Hε := iterateTDeriv (-eps) D H
  have hFdeg : F.natDegree ≤ D := hFG.natDegree_le.trans hGH.natDegree_le
  have hGdeg : G.natDegree ≤ D := hGH.natDegree_le
  have hFne : F ≠ 0 := hFG.1.1
  have hFεnn : HasNonnegCoeffs Fε := hF.iterateTDeriv_neg heps.le D
  have hGεnn : HasNonnegCoeffs Gε := hG.iterateTDeriv_neg heps.le D
  have hHεnn : HasNonnegCoeffs Hε := hH.iterateTDeriv_neg heps.le D
  have hQrecipNN : ∀ b : ℝ, 0 ≤ b →
      HasNonnegCoeffs (quadraticInterlacingPencil H G F b) :=
    fun _ hb => hasNonnegCoeffs_quadraticInterlacingPencil hH hG hF hb
  have hQrecipNe : ∀ b : ℝ, 0 ≤ b →
      quadraticInterlacingPencil H G F b ≠ 0 := by
    intro b hb
    have hsum : C (2 * b) * G + C (b ^ 2) * H + F ≠ 0 :=
      add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
        ((hasNonnegCoeffs_C_mul (mul_nonneg (by norm_num) hb) hG).add
          (hasNonnegCoeffs_C_mul (sq_nonneg b) hH)) hF hFne
    simpa [quadraticInterlacingPencil, add_comm, add_left_comm, add_assoc] using hsum
  have hQεsplitsRecip : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil Hε Gε Fε b).Splits := fun b hb => by
    rw [← iterateTDeriv_quadraticInterlacingPencil]
    exact splits_iterateTDeriv_all
      (splits_reciprocalQuadraticInterlacingPencil hFG.1.2 hsplits b hb) D
  have hQεcoeff0Recip : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil Hε Gε Fε b).coeff 0 ≠ 0 := by
    intro b hb
    have hpos := coeff_zero_iterateTDeriv_neg_pos_of_natDegree_le
      heps (hQrecipNN b hb) (hQrecipNe b hb) (k := D)
        (natDegree_quadraticInterlacingPencil_le le_rfl hGdeg hFdeg b)
    rw [iterateTDeriv_quadraticInterlacingPencil] at hpos
    exact hpos.ne'
  exact ⟨hQεsplitsRecip, hQεcoeff0Recip, fun b hb =>
    roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne
      (hasNonnegCoeffs_quadraticInterlacingPencil hHεnn hGεnn hFεnn hb)
      (hQεcoeff0Recip b hb)⟩

/-- Quadratic tangent closure in positive degree.  A common negative
derivative shift makes the whole pencil simple with strictly negative roots;
the simple-path theorem applies there, and coefficientwise closure descends
the result to the original triple. -/
theorem strictInterl_quadraticInterlacingTangent_pencil_of_pos_natDegree
    {F G H : ℝ[X]}
    (hF : HasNonnegCoeffs F) (hG : HasNonnegCoeffs G)
    (hH : HasNonnegCoeffs H) (hFG : StrictInterl F G)
    (hGH : StrictInterl G H)
    (hsplits : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).Splits)
    (hHdeg : H.natDegree ≠ 0) {a : ℝ} (ha : 0 < a) :
    StrictInterl (quadraticInterlacingTangent F G a)
      (quadraticInterlacingPencil F G H a) := by
  let D := H.natDegree
  have hD : D ≠ 0 := hHdeg
  have hFdeg : F.natDegree ≤ D := hFG.natDegree_le.trans hGH.natDegree_le
  have hGdeg : G.natDegree ≤ D := hGH.natDegree_le
  have hFne : F ≠ 0 := hFG.1.1
  have hGne : G ≠ 0 := hFG.2.1.1
  have hHne : H ≠ 0 := hGH.2.1.1
  have hQnn : ∀ b : ℝ, 0 ≤ b →
      HasNonnegCoeffs (quadraticInterlacingPencil F G H b) :=
    fun _ hb => hasNonnegCoeffs_quadraticInterlacingPencil hF hG hH hb
  have hQdegree : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).natDegree = D :=
    fun _ hb => natDegree_quadraticInterlacingPencil_eq hF hG hH hHne hFdeg hGdeg hb
  have hQne : ∀ b : ℝ, 0 ≤ b →
      quadraticInterlacingPencil F G H b ≠ 0 := fun b hb hzero => by
    have := hQdegree b hb
    simp_all
  have hAnn : HasNonnegCoeffs (quadraticInterlacingTangent F G a) :=
    hG.add (hasNonnegCoeffs_C_mul ha.le hF)
  have hAne : quadraticInterlacingTangent F G a ≠ 0 := by
    simpa [quadraticInterlacingTangent, add_comm] using
      add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
        (hasNonnegCoeffs_C_mul ha.le hF) hG hGne
  apply strictInterl_of_iterateTDeriv_neg hAnn (hQnn a ha.le)
    hAne (hQne a ha.le) D
  intro eps heps
  rw [iterateTDeriv_quadraticInterlacingTangent,
    iterateTDeriv_quadraticInterlacingPencil]
  let Fε := iterateTDeriv (-eps) D F
  let Gε := iterateTDeriv (-eps) D G
  let Hε := iterateTDeriv (-eps) D H
  change StrictInterl (quadraticInterlacingTangent Fε Gε a)
    (quadraticInterlacingPencil Fε Gε Hε a)
  have hFεnn : HasNonnegCoeffs Fε := hF.iterateTDeriv_neg heps.le D
  have hGεnn : HasNonnegCoeffs Gε := hG.iterateTDeriv_neg heps.le D
  have hHεnn : HasNonnegCoeffs Hε := hH.iterateTDeriv_neg heps.le D
  have hFGε : StrictInterl Fε Gε := hFG.iterateTDeriv_common (-eps) D
  have hGHε : StrictInterl Gε Hε := hGH.iterateTDeriv_common (-eps) D
  have hFεdeg : Fε.natDegree ≤ D := by simpa [Fε, D] using hFdeg
  have hGεdeg : Gε.natDegree ≤ D := by simpa [Gε, D] using hGdeg
  have hHεdeg : Hε.natDegree ≤ D := by simp [Hε, D]
  obtain ⟨hQεdegree, hQεdegreeLocal, hQεpos, hQεsplits,
      hQεsimple, hQεneg⟩ :=
    regularized_quadraticInterlacingPencil_forward_data
      hF hG hH hFG hGH hsplits hHdeg heps
  obtain ⟨hQεsplitsRecip, hQεcoeff0Recip, hQεnegRecip⟩ :=
    regularized_quadraticInterlacingPencil_reciprocal_data
      hF hG hH hFG hGH hsplits heps
  have hAεnn : HasNonnegCoeffs (quadraticInterlacingTangent Fε Gε a) :=
    hGεnn.add (hasNonnegCoeffs_C_mul ha.le hFεnn)
  have hAεne : quadraticInterlacingTangent Fε Gε a ≠ 0 := by
    simpa [quadraticInterlacingTangent, add_comm] using
      add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
        (hasNonnegCoeffs_C_mul ha.le hFεnn) hGεnn
        (iterateTDeriv_ne_zero hGne)
  exact strictInterl_quadraticInterlacingTangent_pencil_of_simple_path
    (hFεnn.pos_leadingCoeff (iterateTDeriv_ne_zero hFne))
    (hGεnn.pos_leadingCoeff (iterateTDeriv_ne_zero hGne))
    (hHεnn.pos_leadingCoeff (iterateTDeriv_ne_zero hHne)) hFGε hGHε hD
    hFεdeg hGεdeg hHεdeg hQεdegree hQεdegreeLocal hQεpos
    hQεsplits hQεsimple hQεneg hQεsplitsRecip hQεcoeff0Recip
    hQεnegRecip ha (hAεnn.pos_leadingCoeff hAεne)
    ((natDegree_add_le _ _).trans
      (max_le hGεdeg ((natDegree_C_mul_le _ _).trans hFεdeg)))

/-- The parameter tangent of a real-rooted quadratic pencil follows the
pencil in oriented interlacing order.  This is the quadratic closure step
used to propagate a consecutive monomial chain through PF factors. -/
theorem strictInterl_quadraticInterlacingTangent_pencil
    {F G H : ℝ[X]}
    (hF : HasNonnegCoeffs F) (hG : HasNonnegCoeffs G)
    (hH : HasNonnegCoeffs H) (hFG : StrictInterl F G)
    (hGH : StrictInterl G H)
    (hsplits : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).Splits)
    {a : ℝ} (ha : 0 ≤ a) :
    StrictInterl (quadraticInterlacingTangent F G a)
      (quadraticInterlacingPencil F G H a) := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa [quadraticInterlacingTangent, quadraticInterlacingPencil] using hGH
  by_cases hHdeg : H.natDegree = 0
  · have hGdeg : G.natDegree = 0 := by
      exact Nat.eq_zero_of_le_zero (by simpa [hHdeg] using hGH.natDegree_le)
    have hFdeg : F.natDegree = 0 :=
      Nat.eq_zero_of_le_zero (by simpa [hGdeg] using hFG.natDegree_le)
    have hFne : F ≠ 0 := hFG.1.1
    have hGne : G ≠ 0 := hFG.2.1.1
    have hHne : H ≠ 0 := hGH.2.1.1
    have hAnn : HasNonnegCoeffs (quadraticInterlacingTangent F G a) :=
      hG.add (hasNonnegCoeffs_C_mul ha.le hF)
    have hAne : quadraticInterlacingTangent F G a ≠ 0 := by
      simpa [quadraticInterlacingTangent, add_comm] using
        add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
          (hasNonnegCoeffs_C_mul ha.le hF) hG hGne
    have hAdeg : (quadraticInterlacingTangent F G a).natDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      calc
        (quadraticInterlacingTangent F G a).natDegree ≤
            max G.natDegree (C a * F).natDegree := by
          simpa [quadraticInterlacingTangent] using
            natDegree_add_le G (C a * F)
        _ ≤ max 0 0 := max_le hGdeg.le
          ((natDegree_C_mul_le a F).trans hFdeg.le)
        _ = 0 := by simp
    have hQne : quadraticInterlacingPencil F G H a ≠ 0 := by
      have hsum : C (2 * a) * G + C (a ^ 2) * F + H ≠ 0 :=
        add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
          ((hasNonnegCoeffs_C_mul (mul_nonneg (by norm_num) ha.le) hG).add
            (hasNonnegCoeffs_C_mul (sq_nonneg a) hF)) hH hHne
      simpa [quadraticInterlacingPencil, add_comm, add_left_comm,
        add_assoc] using hsum
    have hQdeg : (quadraticInterlacingPencil F G H a).natDegree = 0 := by
      have hFleH : F.natDegree ≤ H.natDegree := by simp [hFdeg, hHdeg]
      have hGleH : G.natDegree ≤ H.natDegree := by simp [hGdeg, hHdeg]
      exact (natDegree_quadraticInterlacingPencil_eq
        hF hG hH hHne hFleH hGleH ha.le).trans hHdeg
    exact StrictInterl.of_degree_zero_degree_zero hAne
      (isRealRooted_of_deg_zero hAne hAdeg).2 hQne (hsplits a ha.le)
      hAdeg hQdeg
  · exact strictInterl_quadraticInterlacingTangent_pencil_of_pos_natDegree
      hF hG hH hFG hGH hsplits hHdeg ha

/-- The quadratic pencil is the right member plus `a` times its tangent. -/
theorem quadraticInterlacingPencil_eq_right_add_tangent
    (F G H : ℝ[X]) (a : ℝ) :
    quadraticInterlacingPencil F G H a =
      quadraticInterlacingRight G H a +
        C a * quadraticInterlacingTangent F G a := by
  simp only [quadraticInterlacingPencil, quadraticInterlacingRight,
    quadraticInterlacingTangent]
  simp only [map_mul, map_pow, map_ofNat]
  ring

/-- The right member is obtained from the pencil by subtracting `a` times
the tangent. -/
theorem quadraticInterlacingRight_eq_pencil_sub_tangent
    (F G H : ℝ[X]) (a : ℝ) :
    quadraticInterlacingRight G H a =
      quadraticInterlacingPencil F G H a -
        C a * quadraticInterlacingTangent F G a := by
  rw [quadraticInterlacingPencil_eq_right_add_tangent]
  ring

/-- Replacing the quadratic pencil by its right member does not change the
Wronskian against the parameter tangent. -/
theorem wronskian_quadraticInterlacingTangent_pencil
    (F G H : ℝ[X]) (a : ℝ) :
    wronskian (quadraticInterlacingTangent F G a)
        (quadraticInterlacingPencil F G H a) =
      wronskian (quadraticInterlacingTangent F G a)
        (quadraticInterlacingRight G H a) := by
  rw [quadraticInterlacingPencil_eq_right_add_tangent,
    wronskian_add_right, Polynomial.wronskian_C_mul_right,
    wronskian_self_eq_zero, mul_zero, add_zero]

/-- The tangent/right pair and the tangent/pencil pair span the same real
linear pencil. -/
theorem allComboRealRooted_quadraticInterlacingTangent_right
    {F G H : ℝ[X]} {a : ℝ}
    (h : AllComboRealRooted
      (quadraticInterlacingTangent F G a)
      (quadraticInterlacingPencil F G H a)) :
    AllComboRealRooted
      (quadraticInterlacingTangent F G a)
      (quadraticInterlacingRight G H a) := by
  intro alpha beta
  rw [quadraticInterlacingRight_eq_pencil_sub_tangent]
  rw [← show C (alpha - a * beta) * quadraticInterlacingTangent F G a +
      C beta * quadraticInterlacingPencil F G H a =
      C alpha * quadraticInterlacingTangent F G a +
        C beta * (quadraticInterlacingPencil F G H a -
          C a * quadraticInterlacingTangent F G a) by
    simp only [map_sub, map_mul]
    ring
  ]
  exact h (alpha - a * beta) beta

/-- Algebraic end of the quadratic closure argument.

If the parameter tangent precedes the quadratic pencil, then it also precedes
the right member `H + a G`.  The proof transports the full Obreschkoff pencil
and its Wronskian orientation through `Q a = B a + a A a`.
-/
theorem strictInterl_quadraticInterlacingRight_of_tangent
    {F G H : ℝ[X]} {a : ℝ}
    (hApos : HasPosLeadingCoeff (quadraticInterlacingTangent F G a))
    (hBpos : HasPosLeadingCoeff (quadraticInterlacingRight G H a))
    (hQpos : HasPosLeadingCoeff (quadraticInterlacingPencil F G H a))
    (hAQ : StrictInterl
      (quadraticInterlacingTangent F G a)
      (quadraticInterlacingPencil F G H a)) :
    StrictInterl
      (quadraticInterlacingTangent F G a)
      (quadraticInterlacingRight G H a) := by
  exact strictInterl_of_allComboRealRooted_of_wronskian_nonneg
    hBpos hApos
    (allComboRealRooted_quadraticInterlacingTangent_right
      (allComboRealRooted_of_strictInterl hAQ)).comm fun x => by
      rw [← wronskian_quadraticInterlacingTangent_pencil]
      exact wronskian_eval_nonneg_of_strictInterl hQpos hApos hAQ x

/-- A nonpositive upper-half-plane logarithmic ratio gives the full
quadratic-closure conclusion.  This packages the Hermite--Biehler endpoint
with the algebraic change from the pencil to `H + a G`. -/
theorem strictInterl_quadraticInterlacingRight_of_im_ratio_nonpos
    {F G H : ℝ[X]} {a : ℝ}
    (hApos : HasPosLeadingCoeff (quadraticInterlacingTangent F G a))
    (hBpos : HasPosLeadingCoeff (quadraticInterlacingRight G H a))
    (hQpos : HasPosLeadingCoeff (quadraticInterlacingPencil F G H a))
    (hQsplit : (quadraticInterlacingPencil F G H a).Splits)
    (hratio : ∀ z : ℂ, 0 < z.im →
      ((complexify (quadraticInterlacingTangent F G a)).eval z /
        (complexify (quadraticInterlacingPencil F G H a)).eval z).im ≤ 0) :
    StrictInterl (quadraticInterlacingTangent F G a)
      (quadraticInterlacingRight G H a) := by
  apply strictInterl_quadraticInterlacingRight_of_tangent hApos hBpos hQpos
  exact strictInterl_quadraticInterlacingTangent_pencil_of_im_ratio_nonpos
    hQpos hApos hQsplit hratio

end RealRooted
