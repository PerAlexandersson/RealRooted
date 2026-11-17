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
public import RealRooted.QuadraticInterlacing.Crossing

/-!
# Tangent residues and oriented pencils

Nonnegative tangent residues, limits through exceptional spatial levels,
and upper-half-plane ratio criteria for oriented interlacing.
-/

public section

open Polynomial
open SignType
open Topology
open scoped ContDiff

noncomputable section

namespace RealRooted

/-- Under the simple fixed-degree pencil hypotheses, every positive root of
the parameter evaluation is simple.  The proof selects the root-count endpoint
at infinity and exhausts the ordered list of at most two crossings. -/
theorem quadraticParameterEvaluation_positive_root_count_eq_one
    {F G H : ℝ[X]} {D K : ℕ}
    (hFpos : HasPosLeadingCoeff F) (hGpos : HasPosLeadingCoeff G)
    (hHpos : HasPosLeadingCoeff H) (hFG : StrictInterl F G)
    (hGH : StrictInterl G H) (hD : D ≠ 0)
    (hFdeg : F.natDegree ≤ K) (hGdeg : G.natDegree ≤ K)
    (hHdeg : H.natDegree ≤ K)
    (hdegree : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).natDegree = D)
    (hdegree_local : ∀ b : ℝ, 0 ≤ b → ∀ᶠ c in 𝓝 b,
      (quadraticInterlacingPencil F G H c).natDegree = D)
    (hsplits : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).Splits)
    (hsimple : ∀ b : ℝ, 0 ≤ b →
      HasSimpleRoots (quadraticInterlacingPencil F G H b))
    (hsplits_recip : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil H G F b).Splits)
    (hcoeff0_recip : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil H G F b).coeff 0 ≠ 0)
    (hneg_recip : ∀ b : ℝ, 0 ≤ b → ∀ q ∈
      (quadraticInterlacingPencil H G F b).roots, q < 0)
    {r a : ℝ} (hr : r < 0) (hrF : ¬F.IsRoot r)
    (hrG : ¬G.IsRoot r) (hrH : ¬H.IsRoot r)
    (ha : 0 < a) (haroot : (quadraticParameterEvaluation F G H r).IsRoot a) :
    (quadraticParameterEvaluation F G H r).roots.count a = 1 := by
  let q := quadraticParameterEvaluation F G H r
  have hqdeg : q.natDegree = 2 := quadraticParameterEvaluation_natDegree hrF
  have hqne : q ≠ 0 := by grind
  have hamem : a ∈ positiveQuadraticParameterRoots F G H r := by
    rw [mem_positiveQuadraticParameterRoots_iff]
    exact ⟨(Polynomial.mem_roots hqne).2 haroot, ha⟩
  have hlen := positiveQuadraticParameterRoots_length_le_two
    (F := F) (G := G) (H := H) (r := r) hrF
  generalize hrs : positiveQuadraticParameterRoots F G H r = xs at hamem hlen
  have hend := eventually_quadraticInterlacingPencil_card_roots_gt_eq_atTop
    hFdeg hGdeg hHdeg hsplits_recip hcoeff0_recip hneg_recip hr hrF
  rcases xs with _ | ⟨c, xs⟩
  · simp at hamem
  · rcases xs with _ | ⟨d, xs⟩
    · have hac : a = c := by simpa using hamem
      subst a
      obtain ⟨R, hRcount, hcR⟩ :=
        (hend.and (Filter.eventually_gt_atTop c)).exists
      have hexact := quadraticInterlacingPencil_one_positive_crossing_exact_drop
        hFpos hGpos hHpos hFG hGH hrF hrG hrH hrs hcR hD
        (fun μ hμ => hdegree μ hμ.1)
        (fun μ hμ => hdegree_local μ hμ.1)
        (fun μ hμ => hsplits μ hμ.1)
        (fun μ hμ => hsimple μ hμ.1) hRcount
      simpa only [q] using hexact.2
    · have hxsNil : xs = [] := by
        simpa using hlen
      subst xs
      have haCases : a = c ∨ a = d := by simpa using hamem
      obtain ⟨R, hRcount, hdR⟩ :=
        (hend.and (Filter.eventually_gt_atTop d)).exists
      have hexact := quadraticInterlacingPencil_two_positive_crossings_exact_drop
        hFpos hGpos hHpos hFG hGH hrF hrG hrH hrs hdR hD
        (fun μ hμ => hdegree μ hμ.1)
        (fun μ hμ => hdegree_local μ hμ.1)
        (fun μ hμ => hsplits μ hμ.1)
        (fun μ hμ => hsimple μ hμ.1) hRcount
      rcases haCases with rfl | rfl
      · simpa only [q] using hexact.2.2.1
      · simpa only [q] using hexact.2.2.2

/-- The two positive crossings give a nonnegative residue at either crossing. -/
private theorem quadraticInterlacingTangent_residue_nonneg_of_two_crossings
    {F G H : ℝ[X]} {D : ℕ} {r a c d R : ℝ}
    (hFpos : HasPosLeadingCoeff F) (hGpos : HasPosLeadingCoeff G)
    (hHpos : HasPosLeadingCoeff H) (hFG : StrictInterl F G)
    (hGH : StrictInterl G H) (hD : D ≠ 0)
    (hrF : ¬F.IsRoot r) (hrG : ¬G.IsRoot r) (hrH : ¬H.IsRoot r)
    (hdegree : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).natDegree = D)
    (hdegree_local : ∀ b : ℝ, 0 ≤ b → ∀ᶠ x in nhds b,
      (quadraticInterlacingPencil F G H x).natDegree = D)
    (hpos : ∀ b : ℝ, 0 ≤ b →
      HasPosLeadingCoeff (quadraticInterlacingPencil F G H b))
    (hsplits : ∀ b : ℝ, 0 ≤ b → (quadraticInterlacingPencil F G H b).Splits)
    (hsimple : ∀ b : ℝ, 0 ≤ b →
      HasSimpleRoots (quadraticInterlacingPencil F G H b))
    (hrs : positiveQuadraticParameterRoots F G H r = [c, d])
    (hdR : d < R)
    (hRcount : ((quadraticInterlacingPencil F G H R).roots.filter (r < ·)).card =
      (F.roots.filter (r < ·)).card)
    (ha : 0 < a) (haCases : a = c ∨ a = d)
    (haroot : (quadraticInterlacingPencil F G H a).IsRoot r) :
    0 ≤ (quadraticInterlacingTangent F G a).eval r /
      (quadraticInterlacingPencil F G H a).derivative.eval r := by
  have hpair := positiveQuadraticParameterRoots_pairwise F G H r
  have hcd : c < d := by
    rw [hrs] at hpair
    simpa using hpair
  have hcmem : c ∈ positiveQuadraticParameterRoots F G H r := by
    rw [hrs]
    simp
  have hcpos : 0 < c :=
    (mem_positiveQuadraticParameterRoots_iff.mp hcmem).2
  let m := (c + d) / 2
  have hcm : c < m := by dsimp [m]; linarith
  have hmd : m < d := by dsimp [m]; linarith
  have hm0 : 0 ≤ m := hcpos.le.trans hcm.le
  have hexact := quadraticInterlacingPencil_two_positive_crossings_exact_drop
    hFpos hGpos hHpos hFG hGH hrF hrG hrH hrs hdR hD
    (fun μ hμ => hdegree μ hμ.1)
    (fun μ hμ => hdegree_local μ hμ.1)
    (fun μ hμ => hsplits μ hμ.1)
    (fun μ hμ => hsimple μ hμ.1) hRcount
  have hzip : (c, d) ∈
      (positiveQuadraticParameterRoots F G H r).zip
        (positiveQuadraticParameterRoots F G H r).tail := by
    rw [hrs]
    simp
  rcases haCases with rfl | rfl
  · have hdrop :
        ((quadraticInterlacingPencil F G H 0).roots.filter (r < ·)).card =
          ((quadraticInterlacingPencil F G H m).roots.filter (r < ·)).card + 1 := by
      simpa only [m, hexact.2.2.1] using hexact.1
    exact quadraticInterlacingTangent_residue_nonneg_of_exact_crossing
      ha hcm hD
      (fun μ hμ => hdegree μ hμ.1)
      (fun μ hμ => hdegree_local μ hμ.1)
      (fun μ hμ => hpos μ hμ.1)
      (fun μ hμ => hsplits μ hμ.1)
      (fun μ hμ => hsimple μ hμ.1) haroot
      (fun μ hμ => quadraticParameterEvaluation_not_isRoot_before_first_positive
        hrF hrH hrs hμ.1 hμ.2)
      (fun μ hμ => quadraticParameterEvaluation_not_isRoot_between_adjacent_positive
        hrF hzip hμ.1 (hμ.2.trans_lt hmd))
      hdrop
  · have hdrop :
        ((quadraticInterlacingPencil F G H m).roots.filter (r < ·)).card =
          ((quadraticInterlacingPencil F G H R).roots.filter (r < ·)).card + 1 := by
      simpa only [m, hexact.2.2.2] using hexact.2.1
    exact quadraticInterlacingTangent_residue_nonneg_of_exact_crossing
      hmd hdR hD
      (fun μ hμ => hdegree μ (hm0.trans hμ.1))
      (fun μ hμ => hdegree_local μ (hm0.trans hμ.1))
      (fun μ hμ => hpos μ (hm0.trans hμ.1))
      (fun μ hμ => hsplits μ (hm0.trans hμ.1))
      (fun μ hμ => hsimple μ (hm0.trans hμ.1)) haroot
      (fun μ hμ => quadraticParameterEvaluation_not_isRoot_between_adjacent_positive
        hrF hzip (hcm.trans_le hμ.1) hμ.2)
      (fun μ hμ => quadraticParameterEvaluation_not_isRoot_after_last_positive
        hrF (xs := [c]) (by simpa using hrs) hμ.1)
      hdrop

/-- At a spatial level avoiding the three coefficient polynomials, the
ordered-crossing exhaustion gives a nonnegative tangent residue at every
positive-parameter crossing. -/
theorem quadraticInterlacingTangent_residue_nonneg_of_nonexceptional
    {F G H : ℝ[X]} {D K : ℕ}
    (hFpos : HasPosLeadingCoeff F) (hGpos : HasPosLeadingCoeff G)
    (hHpos : HasPosLeadingCoeff H) (hFG : StrictInterl F G)
    (hGH : StrictInterl G H) (hD : D ≠ 0)
    (hFdeg : F.natDegree ≤ K) (hGdeg : G.natDegree ≤ K)
    (hHdeg : H.natDegree ≤ K)
    (hdegree : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).natDegree = D)
    (hdegree_local : ∀ b : ℝ, 0 ≤ b → ∀ᶠ c in nhds b,
      (quadraticInterlacingPencil F G H c).natDegree = D)
    (hpos : ∀ b : ℝ, 0 ≤ b →
      HasPosLeadingCoeff (quadraticInterlacingPencil F G H b))
    (hsplits : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).Splits)
    (hsimple : ∀ b : ℝ, 0 ≤ b →
      HasSimpleRoots (quadraticInterlacingPencil F G H b))
    (hsplits_recip : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil H G F b).Splits)
    (hcoeff0_recip : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil H G F b).coeff 0 ≠ 0)
    (hneg_recip : ∀ b : ℝ, 0 ≤ b → ∀ q ∈
      (quadraticInterlacingPencil H G F b).roots, q < 0)
    {r a : ℝ} (hr : r < 0) (hrF : ¬F.IsRoot r)
    (hrG : ¬G.IsRoot r) (hrH : ¬H.IsRoot r)
    (ha : 0 < a)
    (haroot : (quadraticInterlacingPencil F G H a).IsRoot r) :
    0 ≤ (quadraticInterlacingTangent F G a).eval r /
      (quadraticInterlacingPencil F G H a).derivative.eval r := by
  let q := quadraticParameterEvaluation F G H r
  have hqdeg : q.natDegree = 2 := quadraticParameterEvaluation_natDegree hrF
  have hqne : q ≠ 0 := by grind
  have haqroot : q.IsRoot a :=
    (quadraticParameterEvaluation_isRoot_iff F G H r a).2 haroot
  have hamem : a ∈ positiveQuadraticParameterRoots F G H r := by
    rw [mem_positiveQuadraticParameterRoots_iff]
    exact ⟨(Polynomial.mem_roots hqne).2 haqroot, ha⟩
  have hlen := positiveQuadraticParameterRoots_length_le_two
    (F := F) (G := G) (H := H) (r := r) hrF
  generalize hrs : positiveQuadraticParameterRoots F G H r = xs at hamem hlen
  have hend := eventually_quadraticInterlacingPencil_card_roots_gt_eq_atTop
    hFdeg hGdeg hHdeg hsplits_recip hcoeff0_recip hneg_recip hr hrF
  rcases xs with _ | ⟨c, xs⟩
  · simp at hamem
  · rcases xs with _ | ⟨d, xs⟩
    · have hac : a = c := by simpa using hamem
      subst a
      obtain ⟨R, hRcount, hcR⟩ :=
        (hend.and (Filter.eventually_gt_atTop c)).exists
      have hexact := quadraticInterlacingPencil_one_positive_crossing_exact_drop
        hFpos hGpos hHpos hFG hGH hrF hrG hrH hrs hcR hD
        (fun μ hμ => hdegree μ hμ.1)
        (fun μ hμ => hdegree_local μ hμ.1)
        (fun μ hμ => hsplits μ hμ.1)
        (fun μ hμ => hsimple μ hμ.1) hRcount
      have hdrop :
          ((quadraticInterlacingPencil F G H 0).roots.filter (r < ·)).card =
            ((quadraticInterlacingPencil F G H R).roots.filter (r < ·)).card + 1 := by
        rw [hexact.1, hexact.2]
      exact quadraticInterlacingTangent_residue_nonneg_of_exact_crossing
        ha hcR hD
        (fun μ hμ => hdegree μ hμ.1)
        (fun μ hμ => hdegree_local μ hμ.1)
        (fun μ hμ => hpos μ hμ.1)
        (fun μ hμ => hsplits μ hμ.1)
        (fun μ hμ => hsimple μ hμ.1) haroot
        (fun μ hμ => quadraticParameterEvaluation_not_isRoot_before_first_positive
          hrF hrH hrs hμ.1 hμ.2)
        (fun μ hμ => quadraticParameterEvaluation_not_isRoot_after_last_positive
          hrF (xs := []) (by simpa using hrs) hμ.1)
        hdrop
    · have hxsNil : xs = [] := by
        simpa using hlen
      subst xs
      have haCases : a = c ∨ a = d := by simpa using hamem
      obtain ⟨R, hRcount, hdR⟩ :=
        (hend.and (Filter.eventually_gt_atTop d)).exists
      exact quadraticInterlacingTangent_residue_nonneg_of_two_crossings
        hFpos hGpos hHpos hFG hGH hD hrF hrG hrH hdegree hdegree_local
        hpos hsplits hsimple hrs hdR hRcount ha haCases haroot

/-- Tangent-residue nonnegativity is closed under a continuous branch of
parameter crossings.  This is the topological endpoint used to pass from
nonexceptional spatial levels to a level meeting one of `F`, `G`, or `H`. -/
theorem quadraticInterlacingTangent_residue_nonneg_of_branch_limit
    {F G H : ℝ[X]} {r a : ℝ} {α : ℝ → ℝ}
    (hα : ContinuousAt α r) (hαbase : α r = a)
    (hder : (quadraticInterlacingPencil F G H a).derivative.eval r ≠ 0)
    (hres : ∀ᶠ s in nhdsWithin r (Set.Iio r),
      0 ≤ (quadraticInterlacingTangent F G (α s)).eval s /
        (quadraticInterlacingPencil F G H (α s)).derivative.eval s) :
    0 ≤ (quadraticInterlacingTangent F G a).eval r /
      (quadraticInterlacingPencil F G H a).derivative.eval r := by
  have hnumCont : ContinuousAt
      (fun s => (quadraticInterlacingTangent F G (α s)).eval s) r := by
    simp only [quadraticInterlacingTangent, eval_add, eval_mul, eval_C]
    fun_prop
  have hdenCont : ContinuousAt
      (fun s =>
        (quadraticInterlacingPencil F G H (α s)).derivative.eval s) r := by
    simp only [quadraticInterlacingPencil, derivative_add, derivative_C_mul,
      eval_add, eval_mul, eval_C]
    fun_prop
  rw [← hαbase] at hder ⊢
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    ((hnumCont.tendsto.mono_left nhdsWithin_le_nhds).div
      (hdenCont.tendsto.mono_left nhdsWithin_le_nhds) hder) hres

/-- A regular parameter root extends to a smooth local spatial branch. -/
private theorem exists_contDiffAt_quadraticParameter_root
    {F G H : ℝ[X]} {r a : ℝ}
    (hproot : (quadraticParameterEvaluation F G H r).IsRoot a)
    (hpregular : (quadraticParameterEvaluation F G H r).derivative.eval a ≠ 0) :
    ∃ α : ℝ → ℝ, ContDiffAt ℝ 1 α r ∧ α r = a ∧
      ∀ᶠ s in nhds r, (quadraticParameterEvaluation F G H s).IsRoot (α s) := by
  let p : ℝ → ℝ[X] := fun s => quadraticParameterEvaluation F G H s
  have hpsmooth : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ => (p z.1).eval z.2) (r, a) := by
    rw [show (fun z : ℝ × ℝ => (p z.1).eval z.2) =
        fun z => H.eval z.1 + 2 * G.eval z.1 * z.2 +
          F.eval z.1 * z.2 ^ 2 by
      funext z
      simp [p, quadraticParameterEvaluation]]
    exact ((((Polynomial.contDiff_aeval H ∞).comp contDiff_fst).add
      ((contDiff_const.mul
        ((Polynomial.contDiff_aeval G ∞).comp contDiff_fst)).mul
          contDiff_snd)).add
      (((Polynomial.contDiff_aeval F ∞).comp contDiff_fst).mul
        (contDiff_snd.pow 2))).contDiffAt.of_le (by norm_num)
  exact exists_contDiffAt_polynomial_root p hpsmooth hproot hpregular

/-- Every simple negative root of the positive-parameter quadratic pencil has
a nonnegative tangent residue.  Exceptional levels are reached by a local
implicit branch of the parameter-evaluation polynomial and the closed branch
limit above. -/
theorem quadraticInterlacingTangent_residue_nonneg
    {F G H : ℝ[X]} {D K : ℕ}
    (hFpos : HasPosLeadingCoeff F) (hGpos : HasPosLeadingCoeff G)
    (hHpos : HasPosLeadingCoeff H) (hFG : StrictInterl F G)
    (hGH : StrictInterl G H) (hD : D ≠ 0)
    (hFdeg : F.natDegree ≤ K) (hGdeg : G.natDegree ≤ K)
    (hHdeg : H.natDegree ≤ K)
    (hdegree : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).natDegree = D)
    (hdegree_local : ∀ b : ℝ, 0 ≤ b → ∀ᶠ c in nhds b,
      (quadraticInterlacingPencil F G H c).natDegree = D)
    (hpos : ∀ b : ℝ, 0 ≤ b →
      HasPosLeadingCoeff (quadraticInterlacingPencil F G H b))
    (hsplits : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).Splits)
    (hsimple : ∀ b : ℝ, 0 ≤ b →
      HasSimpleRoots (quadraticInterlacingPencil F G H b))
    (hsplits_recip : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil H G F b).Splits)
    (hcoeff0_recip : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil H G F b).coeff 0 ≠ 0)
    (hneg_recip : ∀ b : ℝ, 0 ≤ b → ∀ q ∈
      (quadraticInterlacingPencil H G F b).roots, q < 0)
    {r a : ℝ} (hr : r < 0) (ha : 0 < a)
    (haroot : (quadraticInterlacingPencil F G H a).IsRoot r) :
    0 ≤ (quadraticInterlacingTangent F G a).eval r /
      (quadraticInterlacingPencil F G H a).derivative.eval r := by
  have hsimpleA := hsimple a ha.le
  have hder : (quadraticInterlacingPencil F G H a).derivative.eval r ≠ 0 :=
    hsimpleA.eval_derivative_ne_zero haroot
  by_cases hAzero : (quadraticInterlacingTangent F G a).eval r = 0
  · rw [hAzero, zero_div]
  let p : ℝ → ℝ[X] := fun s => quadraticParameterEvaluation F G H s
  have hproot : (p r).IsRoot a :=
    (quadraticParameterEvaluation_isRoot_iff F G H r a).2 haroot
  have hpregular : (p r).derivative.eval a ≠ 0 := by
    rw [show (p r).derivative.eval a =
      2 * (quadraticInterlacingTangent F G a).eval r by
        simpa only [p] using
          derivative_eval_quadraticParameterEvaluation F G H r a]
    exact mul_ne_zero (by norm_num) hAzero
  obtain ⟨α, hαdiff, hαbase, hαroot⟩ :=
    exists_contDiffAt_quadraticParameter_root hproot hpregular
  apply quadraticInterlacingTangent_residue_nonneg_of_branch_limit
    hαdiff.continuousAt hαbase hder
  let E : Finset ℝ :=
    F.roots.toFinset ∪ G.roots.toFinset ∪ H.roots.toFinset
  have havoidNhds : ∀ᶠ s in nhds r, s ∉ E.erase r := by
    have hopen : IsOpen ((↑(E.erase r) : Set ℝ)ᶜ) :=
      (E.erase r).isClosed.isOpen_compl
    exact hopen.mem_nhds (by simp)
  have hαposNhds : ∀ᶠ s in nhds r, 0 < α s := by
    apply continuousAt_const.eventually_lt hαdiff.continuousAt
    simpa [hαbase] using ha
  have hαroot' : ∀ᶠ s in nhdsWithin r (Set.Iio r),
      (p s).IsRoot (α s) :=
    hαroot.filter_mono nhdsWithin_le_nhds
  have havoid : ∀ᶠ s in nhdsWithin r (Set.Iio r), s ∉ E.erase r :=
    havoidNhds.filter_mono nhdsWithin_le_nhds
  have hαpos : ∀ᶠ s in nhdsWithin r (Set.Iio r), 0 < α s :=
    hαposNhds.filter_mono nhdsWithin_le_nhds
  filter_upwards [hαroot', havoid, hαpos, self_mem_nhdsWithin] with
    s hsroot hsavoid hsαpos hsr
  have hsrne : s ≠ r := ne_of_lt hsr
  have hsF : ¬F.IsRoot s := by
    intro hs
    exact hsavoid (Finset.mem_erase.mpr ⟨hsrne, by
      simp only [E, Finset.mem_union, Multiset.mem_toFinset]
      exact Or.inl (Or.inl ((Polynomial.mem_roots hFpos.ne_zero).2 hs))⟩)
  have hsG : ¬G.IsRoot s := by
    intro hs
    exact hsavoid (Finset.mem_erase.mpr ⟨hsrne, by
      simp only [E, Finset.mem_union, Multiset.mem_toFinset]
      exact Or.inl (Or.inr ((Polynomial.mem_roots hGpos.ne_zero).2 hs))⟩)
  have hsH : ¬H.IsRoot s := by
    intro hs
    exact hsavoid (Finset.mem_erase.mpr ⟨hsrne, by
      simp only [E, Finset.mem_union, Multiset.mem_toFinset]
      exact Or.inr ((Polynomial.mem_roots hHpos.ne_zero).2 hs)⟩)
  have hsQroot :
      (quadraticInterlacingPencil F G H (α s)).IsRoot s :=
    (quadraticParameterEvaluation_isRoot_iff F G H s (α s)).1 hsroot
  exact quadraticInterlacingTangent_residue_nonneg_of_nonexceptional
    hFpos hGpos hHpos hFG hGH hD hFdeg hGdeg hHdeg hdegree
    hdegree_local hpos hsplits hsimple hsplits_recip hcoeff0_recip
    hneg_recip (hsr.trans hr) hsF hsG hsH hsαpos hsQroot

/-! ## Logarithmic-ratio endpoint -/

/-- Nonnegative residues at the simple roots of the denominator force the
upper-half-plane imaginary part of the polynomial ratio to be nonpositive.
The numerator may have either the same degree or one of smaller degree. -/
theorem im_ratio_nonpos_of_residue_nonneg
    {f g : ℝ[X]} (hfpos : HasPosLeadingCoeff f)
    (hfs : f.Splits) (hfnd : f.roots.Nodup)
    (hfdeg : 1 ≤ f.natDegree) (hgdeg : g.natDegree ≤ f.natDegree)
    (hres : ∀ s ∈ f.roots, 0 ≤ g.eval s / f.derivative.eval s)
    {z : ℂ} (hz : 0 < z.im) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  have hfne : f ≠ 0 := by grind
  by_cases hgne : g = 0
  · subst g
    simp
  by_cases hlt : g.natDegree < f.natDegree
  · have hgdegree : g.degree < f.natDegree := by
      rw [degree_eq_natDegree hgne]
      exact_mod_cast hlt
    apply im_partialfraction_nonpos z hz 0
      (fun s => g.eval s / f.derivative.eval s) hres
    rw [complexify_ratio_eq_partialfraction hfs hfnd hfdeg hgdegree hz]
    simp
  · have heq : g.natDegree = f.natDegree := by lia
    set c₀ := g.leadingCoeff / f.leadingCoeff with hc₀
    set g' := g - C c₀ * f with hg'
    have hg'deg : g'.degree < f.natDegree :=
      degree_sub_c₀_mul_lt hfne hgne heq hfpos
    have hg'eval : ∀ s ∈ f.roots, g'.eval s = g.eval s := by
      intro s hs
      simp [hg', Polynomial.IsRoot.def.mp (Polynomial.isRoot_of_mem_roots hs)]
    have hfz : (complexify f).eval z ≠ 0 :=
      eval_complexify_ne_zero_of_splits_of_im_pos hfs hfne hz
    have hproper : (complexify g').eval z / (complexify f).eval z =
        (f.roots.map fun s =>
          ((g.eval s / f.derivative.eval s : ℝ) : ℂ) / (z - (s : ℂ))).sum := by
      rw [complexify_ratio_eq_partialfraction hfs hfnd hfdeg hg'deg hz]
      congr 1
      exact Multiset.map_congr rfl (by simp_all)
    have hsplit : (complexify g).eval z =
        (complexify g').eval z + (c₀ : ℂ) * (complexify f).eval z := by
      simp [hg', complexify]
    have hid : (complexify g).eval z / (complexify f).eval z =
        (c₀ : ℂ) + (f.roots.map fun s =>
          ((g.eval s / f.derivative.eval s : ℝ) : ℂ) / (z - (s : ℂ))).sum := by
      rw [hsplit, add_div, mul_div_assoc, div_self hfz, mul_one, add_comm,
        hproper]
    exact im_partialfraction_nonpos z hz c₀
      (fun s => g.eval s / f.derivative.eval s) hres hid

/-- A nonpositive upper-half-plane logarithmic ratio puts the parameter
tangent before the quadratic pencil in oriented interlacing order.

This is the exact formal endpoint needed from the analytic root-motion
argument.  Rellich root branches with nonpositive velocities give `hratio`
by logarithmic differentiation; the existing Hermite--Biehler converse then
supplies proper position, including common and repeated roots. -/
theorem strictInterl_quadraticInterlacingTangent_pencil_of_im_ratio_nonpos
    {F G H : ℝ[X]} {a : ℝ}
    (hQpos : HasPosLeadingCoeff (quadraticInterlacingPencil F G H a))
    (hApos : HasPosLeadingCoeff (quadraticInterlacingTangent F G a))
    (hQsplit : (quadraticInterlacingPencil F G H a).Splits)
    (hratio : ∀ z : ℂ, 0 < z.im →
      ((complexify (quadraticInterlacingTangent F G a)).eval z /
        (complexify (quadraticInterlacingPencil F G H a)).eval z).im ≤ 0) :
    StrictInterl (quadraticInterlacingTangent F G a)
      (quadraticInterlacingPencil F G H a) := by
  let Q := quadraticInterlacingPencil F G H a
  let A := quadraticInterlacingTangent F G a
  have hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial Q A) :=
    stable_of_im_ratio_nonpos hQpos.ne_zero hQsplit hratio
  by_cases hQdeg : 1 ≤ Q.natDegree
  · exact strictInterl_of_stable_general hQpos hApos hstable hQdeg
  · have hQdeg0 : Q.natDegree = 0 := by lia
    have hAdeg0 : A.natDegree = 0 := by
      have hshape := (natDegree_shape_of_stable hQpos hApos hstable).1
      lia
    exact StrictInterl.of_degree_zero_degree_zero hApos.ne_zero
      (isRealRooted_of_deg_zero hApos.ne_zero hAdeg0).2 hQpos.ne_zero
      (isRealRooted_of_deg_zero hQpos.ne_zero hQdeg0).2 hAdeg0 hQdeg0

/-- Nonnegative tangent residues at every simple pencil root imply that the
parameter tangent precedes the pencil. -/
theorem strictInterl_quadraticInterlacingTangent_pencil_of_residue_nonneg
    {F G H : ℝ[X]} {a : ℝ}
    (hQpos : HasPosLeadingCoeff (quadraticInterlacingPencil F G H a))
    (hApos : HasPosLeadingCoeff (quadraticInterlacingTangent F G a))
    (hQsplit : (quadraticInterlacingPencil F G H a).Splits)
    (hQsimple : HasSimpleRoots (quadraticInterlacingPencil F G H a))
    (hQdeg : 1 ≤ (quadraticInterlacingPencil F G H a).natDegree)
    (hAdeg : (quadraticInterlacingTangent F G a).natDegree ≤
      (quadraticInterlacingPencil F G H a).natDegree)
    (hres : ∀ r ∈ (quadraticInterlacingPencil F G H a).roots,
      0 ≤ (quadraticInterlacingTangent F G a).eval r /
        (quadraticInterlacingPencil F G H a).derivative.eval r) :
    StrictInterl (quadraticInterlacingTangent F G a)
      (quadraticInterlacingPencil F G H a) := by
  apply strictInterl_quadraticInterlacingTangent_pencil_of_im_ratio_nonpos
    hQpos hApos hQsplit
  intro z hz
  exact im_ratio_nonpos_of_residue_nonneg hQpos hQsplit
    hQsimple.roots_nodup hQdeg hAdeg hres hz

/-- The simple fixed-degree quadratic path satisfies the tangent conclusion.
All analytic crossing work is packaged in
`quadraticInterlacingTangent_residue_nonneg`; this theorem feeds those
residues into the logarithmic-ratio endpoint. -/
theorem strictInterl_quadraticInterlacingTangent_pencil_of_simple_path
    {F G H : ℝ[X]} {D K : ℕ}
    (hFpos : HasPosLeadingCoeff F) (hGpos : HasPosLeadingCoeff G)
    (hHpos : HasPosLeadingCoeff H) (hFG : StrictInterl F G)
    (hGH : StrictInterl G H) (hD : D ≠ 0)
    (hFdeg : F.natDegree ≤ K) (hGdeg : G.natDegree ≤ K)
    (hHdeg : H.natDegree ≤ K)
    (hdegree : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).natDegree = D)
    (hdegree_local : ∀ b : ℝ, 0 ≤ b → ∀ᶠ c in nhds b,
      (quadraticInterlacingPencil F G H c).natDegree = D)
    (hpos : ∀ b : ℝ, 0 ≤ b →
      HasPosLeadingCoeff (quadraticInterlacingPencil F G H b))
    (hsplits : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).Splits)
    (hsimple : ∀ b : ℝ, 0 ≤ b →
      HasSimpleRoots (quadraticInterlacingPencil F G H b))
    (hneg : ∀ b : ℝ, 0 ≤ b → ∀ q ∈
      (quadraticInterlacingPencil F G H b).roots, q < 0)
    (hsplits_recip : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil H G F b).Splits)
    (hcoeff0_recip : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil H G F b).coeff 0 ≠ 0)
    (hneg_recip : ∀ b : ℝ, 0 ≤ b → ∀ q ∈
      (quadraticInterlacingPencil H G F b).roots, q < 0)
    {a : ℝ} (ha : 0 < a)
    (hApos : HasPosLeadingCoeff (quadraticInterlacingTangent F G a))
    (hAdeg : (quadraticInterlacingTangent F G a).natDegree ≤ D) :
    StrictInterl (quadraticInterlacingTangent F G a)
      (quadraticInterlacingPencil F G H a) := by
  apply strictInterl_quadraticInterlacingTangent_pencil_of_residue_nonneg
    (hpos a ha.le) hApos (hsplits a ha.le) (hsimple a ha.le)
  · rw [hdegree a ha.le]
    exact Nat.one_le_iff_ne_zero.mpr hD
  · simpa [hdegree a ha.le] using hAdeg
  · intro r hrmem
    exact quadraticInterlacingTangent_residue_nonneg
      hFpos hGpos hHpos hFG hGH hD hFdeg hGdeg hHdeg hdegree
      hdegree_local hpos hsplits hsimple hsplits_recip hcoeff0_recip
      hneg_recip (hneg a ha.le r hrmem) ha
      (Polynomial.isRoot_of_mem_roots hrmem)

end RealRooted
