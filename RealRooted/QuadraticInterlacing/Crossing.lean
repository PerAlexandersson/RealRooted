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

/-!
# Parameter roots and crossing counts

Parameter-evaluation polynomials and their positive roots, chamber root
counts, and exact drops at one or two positive crossings.
-/

@[expose] public section

open Polynomial
open SignType
open Topology
open scoped ContDiff

noncomputable section

namespace RealRooted

/-- Evaluation of the quadratic pencil at a fixed spatial level, regarded as
a polynomial in the parameter. -/
def quadraticParameterEvaluation (F G H : ℝ[X]) (r : ℝ) : ℝ[X] :=
  C (H.eval r) + C (2 * G.eval r) * X + C (F.eval r) * X ^ 2

/-- Evaluating first in the parameter or first in the spatial variable gives
the same scalar. -/
theorem quadraticParameterEvaluation_eval (F G H : ℝ[X]) (r a : ℝ) :
    (quadraticParameterEvaluation F G H r).eval a =
      (quadraticInterlacingPencil F G H a).eval r := by
  simp only [quadraticParameterEvaluation, quadraticInterlacingPencil,
    eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

/-- A parameter value gives a spatial-level crossing exactly when it is a
root of the parameter-evaluation polynomial. -/
theorem quadraticParameterEvaluation_isRoot_iff (F G H : ℝ[X]) (r a : ℝ) :
    (quadraticParameterEvaluation F G H r).IsRoot a ↔
      (quadraticInterlacingPencil F G H a).IsRoot r := by
  simp only [Polynomial.IsRoot.def, quadraticParameterEvaluation_eval]

/-- The parameter derivative is twice the spatial evaluation of the tangent. -/
theorem derivative_eval_quadraticParameterEvaluation
    (F G H : ℝ[X]) (r a : ℝ) :
    (quadraticParameterEvaluation F G H r).derivative.eval a =
      2 * (quadraticInterlacingTangent F G a).eval r := by
  simp [quadraticParameterEvaluation, quadraticInterlacingTangent]
  ring

/-- On a parameter interval containing no crossing of a fixed spatial level,
the quadratic pencil has constant strict-upper root count. -/
theorem quadraticInterlacingPencil_card_roots_gt_eq_of_no_crossing
    {F G H : ℝ[X]} {μ₀ μ₁ r : ℝ} {D : ℕ}
    (hμ₀μ₁ : μ₀ ≤ μ₁) (hD : D ≠ 0)
    (hdegree : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (quadraticInterlacingPencil F G H μ).natDegree = D)
    (hdegree_local : ∀ μ ∈ Set.Icc μ₀ μ₁, ∀ᶠ b in 𝓝 μ,
      (quadraticInterlacingPencil F G H b).natDegree = D)
    (hsplits : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (quadraticInterlacingPencil F G H μ).Splits)
    (hsimple : ∀ μ ∈ Set.Icc μ₀ μ₁,
      HasSimpleRoots (quadraticInterlacingPencil F G H μ))
    (hno : ∀ μ ∈ Set.Icc μ₀ μ₁,
      ¬ (quadraticParameterEvaluation F G H r).IsRoot μ) :
    ((quadraticInterlacingPencil F G H μ₀).roots.filter (r < ·)).card =
      ((quadraticInterlacingPencil F G H μ₁).roots.filter
        (r < ·)).card := by
  apply polynomialFamily_card_roots_gt_eq_of_local_lower_counts
    (p := fun μ => quadraticInterlacingPencil F G H μ) hμ₀μ₁
  · intro μ hμ
    rw [hdegree μ hμ, hdegree μ₀ ⟨le_rfl, hμ₀μ₁⟩]
  · exact hsplits
  · intro μ hμ hroot
    exact hno μ hμ ((quadraticParameterEvaluation_isRoot_iff F G H r μ).2 hroot)
  · intro μ hμ ρ hρ
    obtain ⟨ε, hε, hlocal⟩ :=
      exists_eps_forall_quadraticInterlacingPencil_root_count_le_near
        hD (hdegree_local μ hμ) (hsplits μ hμ) (hsimple μ hμ) hρ
    exact ⟨ε, hε, fun ν _ hν => hlocal ν hν⟩

/-- The two chamber bounds around one isolated crossing: the left-chamber
count is at most the crossing count plus one, and the crossing count is at most
the right-chamber count. -/
private theorem quadraticInterlacingPencil_card_roots_gt_crossing_bounds
    {F G H : ℝ[X]} {μL a μR r : ℝ} {D : ℕ}
    (hμLa : μL < a) (haμR : a < μR) (hD : D ≠ 0)
    (hdegree : ∀ μ ∈ Set.Icc μL μR,
      (quadraticInterlacingPencil F G H μ).natDegree = D)
    (hdegree_local : ∀ μ ∈ Set.Icc μL μR, ∀ᶠ b in 𝓝 μ,
      (quadraticInterlacingPencil F G H b).natDegree = D)
    (hsplits : ∀ μ ∈ Set.Icc μL μR,
      (quadraticInterlacingPencil F G H μ).Splits)
    (hsimple : ∀ μ ∈ Set.Icc μL μR,
      HasSimpleRoots (quadraticInterlacingPencil F G H μ))
    (hroot : (quadraticInterlacingPencil F G H a).IsRoot r)
    (hnoLeft : ∀ μ ∈ Set.Ico μL a,
      ¬(quadraticParameterEvaluation F G H r).IsRoot μ)
    (hnoRight : ∀ μ ∈ Set.Ioc a μR,
      ¬(quadraticParameterEvaluation F G H r).IsRoot μ) :
    ((quadraticInterlacingPencil F G H μL).roots.filter (r < ·)).card ≤
        ((quadraticInterlacingPencil F G H a).roots.filter (r < ·)).card + 1 ∧
      ((quadraticInterlacingPencil F G H a).roots.filter (r < ·)).card ≤
        ((quadraticInterlacingPencil F G H μR).roots.filter (r < ·)).card := by
  have haIcc : a ∈ Set.Icc μL μR := ⟨hμLa.le, haμR.le⟩
  have hlocal := exists_eventually_quadraticInterlacingPencil_root_count_bounds
    hD (hdegree_local a haIcc) (hsplits a haIcc) (hsimple a haIcc) hroot
  obtain ⟨bL, hbLa, hbLbound, hμLbL⟩ := (hlocal.and (eventually_gt_nhds hμLa)).exists_lt
  obtain ⟨bR, habR, hbRbound, hbRμR⟩ := (hlocal.and (eventually_lt_nhds haμR)).exists_gt
  have hleft := quadraticInterlacingPencil_card_roots_gt_eq_of_no_crossing
    hμLbL.le hD
    (fun μ hμ => hdegree μ ⟨hμ.1, hμ.2.trans (hbLa.le.trans haμR.le)⟩)
    (fun μ hμ => hdegree_local μ
      ⟨hμ.1, hμ.2.trans (hbLa.le.trans haμR.le)⟩)
    (fun μ hμ => hsplits μ ⟨hμ.1, hμ.2.trans (hbLa.le.trans haμR.le)⟩)
    (fun μ hμ => hsimple μ ⟨hμ.1, hμ.2.trans (hbLa.le.trans haμR.le)⟩)
    (fun μ hμ => hnoLeft μ ⟨hμ.1, hμ.2.trans_lt hbLa⟩)
  have hright := quadraticInterlacingPencil_card_roots_gt_eq_of_no_crossing
    hbRμR.le hD
    (fun μ hμ => hdegree μ ⟨(hμLa.le.trans habR.le).trans hμ.1, hμ.2⟩)
    (fun μ hμ => hdegree_local μ
      ⟨(hμLa.le.trans habR.le).trans hμ.1, hμ.2⟩)
    (fun μ hμ => hsplits μ ⟨(hμLa.le.trans habR.le).trans hμ.1, hμ.2⟩)
    (fun μ hμ => hsimple μ ⟨(hμLa.le.trans habR.le).trans hμ.1, hμ.2⟩)
    (fun μ hμ => hnoRight μ ⟨habR.trans_le hμ.1, hμ.2⟩)
  exact ⟨by lia, by lia⟩

/-- Across one crossing, the strict-upper root count in the chamber on the
left is at most the count in the chamber on the right plus one. -/
theorem quadraticInterlacingPencil_card_roots_gt_left_le_right_add_one
    {F G H : ℝ[X]} {μL a μR r : ℝ} {D : ℕ}
    (hμLa : μL < a) (haμR : a < μR) (hD : D ≠ 0)
    (hdegree : ∀ μ ∈ Set.Icc μL μR,
      (quadraticInterlacingPencil F G H μ).natDegree = D)
    (hdegree_local : ∀ μ ∈ Set.Icc μL μR, ∀ᶠ b in 𝓝 μ,
      (quadraticInterlacingPencil F G H b).natDegree = D)
    (hsplits : ∀ μ ∈ Set.Icc μL μR,
      (quadraticInterlacingPencil F G H μ).Splits)
    (hsimple : ∀ μ ∈ Set.Icc μL μR,
      HasSimpleRoots (quadraticInterlacingPencil F G H μ))
    (hroot : (quadraticInterlacingPencil F G H a).IsRoot r)
    (hnoLeft : ∀ μ ∈ Set.Ico μL a,
      ¬(quadraticParameterEvaluation F G H r).IsRoot μ)
    (hnoRight : ∀ μ ∈ Set.Ioc a μR,
      ¬(quadraticParameterEvaluation F G H r).IsRoot μ) :
    ((quadraticInterlacingPencil F G H μL).roots.filter (r < ·)).card ≤
      ((quadraticInterlacingPencil F G H μR).roots.filter (r < ·)).card + 1 := by
  have h := quadraticInterlacingPencil_card_roots_gt_crossing_bounds hμLa haμR hD hdegree
    hdegree_local hsplits hsimple hroot hnoLeft hnoRight
  lia

/-- If a single isolated crossing realizes an exact downward jump of one,
then the strict-upper root count at the crossing equals the right-chamber
count. -/
theorem quadraticInterlacingPencil_card_roots_gt_at_crossing_eq_right
    {F G H : ℝ[X]} {μL a μR r : ℝ} {D : ℕ}
    (hμLa : μL < a) (haμR : a < μR) (hD : D ≠ 0)
    (hdegree : ∀ μ ∈ Set.Icc μL μR,
      (quadraticInterlacingPencil F G H μ).natDegree = D)
    (hdegree_local : ∀ μ ∈ Set.Icc μL μR, ∀ᶠ b in 𝓝 μ,
      (quadraticInterlacingPencil F G H b).natDegree = D)
    (hsplits : ∀ μ ∈ Set.Icc μL μR,
      (quadraticInterlacingPencil F G H μ).Splits)
    (hsimple : ∀ μ ∈ Set.Icc μL μR,
      HasSimpleRoots (quadraticInterlacingPencil F G H μ))
    (hroot : (quadraticInterlacingPencil F G H a).IsRoot r)
    (hnoLeft : ∀ μ ∈ Set.Ico μL a,
      ¬(quadraticParameterEvaluation F G H r).IsRoot μ)
    (hnoRight : ∀ μ ∈ Set.Ioc a μR,
      ¬(quadraticParameterEvaluation F G H r).IsRoot μ)
    (hexact :
      ((quadraticInterlacingPencil F G H μL).roots.filter (r < ·)).card =
        ((quadraticInterlacingPencil F G H μR).roots.filter (r < ·)).card + 1) :
    ((quadraticInterlacingPencil F G H a).roots.filter (r < ·)).card =
      ((quadraticInterlacingPencil F G H μR).roots.filter (r < ·)).card := by
  have h := quadraticInterlacingPencil_card_roots_gt_crossing_bounds hμLa haμR hD hdegree
    hdegree_local hsplits hsimple hroot hnoLeft hnoRight
  lia

/-- Equal right-root counts give matching evaluation and derivative signs. -/
private theorem eval_mul_derivative_pos_of_root_count_eq
    {p q : ℝ[X]} {r : ℝ}
    (hpsplit : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hqsplit : q.Splits) (hqpos : HasPosLeadingCoeff q)
    (hsimple : HasSimpleRoots q) (hroot : q.IsRoot r)
    (hnotmem : r ∉ p.roots)
    (hcount : (p.roots.filter (r < ·)).card = (q.roots.filter (r < ·)).card) :
    0 < p.eval r * q.derivative.eval r := by
  have hEval := eval_sign hpsplit hppos r hnotmem
  have hRootMem : r ∈ q.roots :=
    (Polynomial.mem_roots hqpos.ne_zero).2 hroot
  have hDer := deriv_at_root_sign hqsplit
    hqpos r hRootMem (hsimple.roots_count_eq_one hroot)
  rw [Multiset.countP_eq_card_filter, hcount] at hEval
  rw [Multiset.countP_eq_card_filter] at hDer
  let e : ℝ := (-1 : ℝ) ^ (q.roots.filter (r < ·)).card
  have heSq : e * e = 1 := by
    dsimp only [e]
    rw [← pow_add]
    simp
  have hprod0 := mul_pos hEval hDer
  have hprod : 0 < p.eval r * q.derivative.eval r := by
    have heq :
        (p.eval r * e) * (q.derivative.eval r * e) =
          p.eval r * q.derivative.eval r * (e * e) := by ring
    rw [heq, heSq, mul_one] at hprod0
    exact hprod0
  exact hprod

/-- An exact downward chamber jump forces a nonnegative tangent residue at the
crossing.  The proof uses right-chamber evaluation signs and then lets the
right parameter approach the crossing; the quadratic remainder contributes
only a vanishing first-order correction. -/
theorem quadraticInterlacingTangent_residue_nonneg_of_exact_crossing
    {F G H : ℝ[X]} {μL a μR r : ℝ} {D : ℕ}
    (hμLa : μL < a) (haμR : a < μR) (hD : D ≠ 0)
    (hdegree : ∀ μ ∈ Set.Icc μL μR,
      (quadraticInterlacingPencil F G H μ).natDegree = D)
    (hdegree_local : ∀ μ ∈ Set.Icc μL μR, ∀ᶠ b in 𝓝 μ,
      (quadraticInterlacingPencil F G H b).natDegree = D)
    (hpos : ∀ μ ∈ Set.Icc μL μR,
      HasPosLeadingCoeff (quadraticInterlacingPencil F G H μ))
    (hsplits : ∀ μ ∈ Set.Icc μL μR,
      (quadraticInterlacingPencil F G H μ).Splits)
    (hsimple : ∀ μ ∈ Set.Icc μL μR,
      HasSimpleRoots (quadraticInterlacingPencil F G H μ))
    (hroot : (quadraticInterlacingPencil F G H a).IsRoot r)
    (hnoLeft : ∀ μ ∈ Set.Ico μL a,
      ¬(quadraticParameterEvaluation F G H r).IsRoot μ)
    (hnoRight : ∀ μ ∈ Set.Ioc a μR,
      ¬(quadraticParameterEvaluation F G H r).IsRoot μ)
    (hexact :
      ((quadraticInterlacingPencil F G H μL).roots.filter (r < ·)).card =
        ((quadraticInterlacingPencil F G H μR).roots.filter (r < ·)).card + 1) :
    0 ≤ (quadraticInterlacingTangent F G a).eval r /
      (quadraticInterlacingPencil F G H a).derivative.eval r := by
  let Q : ℝ → ℝ[X] := fun b => quadraticInterlacingPencil F G H b
  let A := quadraticInterlacingTangent F G a
  have haIcc : a ∈ Set.Icc μL μR := ⟨hμLa.le, haμR.le⟩
  have hcountAt :=
    quadraticInterlacingPencil_card_roots_gt_at_crossing_eq_right
      hμLa haμR hD hdegree hdegree_local hsplits hsimple hroot hnoLeft
      hnoRight hexact
  have hlocal := exists_eventually_quadraticInterlacingPencil_root_count_bounds
    hD (hdegree_local a haIcc) (hsplits a haIcc) (hsimple a haIcc) hroot
  have hmulNonneg : 0 ≤ A.eval r * (Q a).derivative.eval r := by
    by_contra hnot
    have hmulNeg : A.eval r * (Q a).derivative.eval r < 0 :=
      lt_of_not_ge hnot
    have hphiCont : ContinuousAt
        (fun b => (2 * A.eval r + (b - a) * F.eval r) *
          (Q a).derivative.eval r) a := by
      fun_prop
    have hphiNeg : ∀ᶠ b in 𝓝 a,
        (2 * A.eval r + (b - a) * F.eval r) *
          (Q a).derivative.eval r < 0 := by
      apply hphiCont.eventually_lt continuousAt_const
      nlinarith
    have hrightEvent : ∀ᶠ b in 𝓝 a,
        ((((Q a).roots.filter (r < ·)).card ≤
            ((Q b).roots.filter (r < ·)).card ∧
          ((Q b).roots.filter (r < ·)).card ≤
            ((Q a).roots.filter (r < ·)).card + 1) ∧
          b < μR) ∧
        (2 * A.eval r + (b - a) * F.eval r) *
          (Q a).derivative.eval r < 0 :=
      (hlocal.and (eventually_lt_nhds haμR)).and hphiNeg
    obtain ⟨b, hab, ⟨⟨hbBounds, hbμR⟩, hphi⟩⟩ := hrightEvent.exists_gt
    have hbIcc : b ∈ Set.Icc μL μR :=
      ⟨hμLa.le.trans hab.le, hbμR.le⟩
    have hright := quadraticInterlacingPencil_card_roots_gt_eq_of_no_crossing
      hbμR.le hD
      (fun μ hμ => hdegree μ ⟨(hμLa.le.trans hab.le).trans hμ.1, hμ.2⟩)
      (fun μ hμ => hdegree_local μ
        ⟨(hμLa.le.trans hab.le).trans hμ.1, hμ.2⟩)
      (fun μ hμ => hsplits μ ⟨(hμLa.le.trans hab.le).trans hμ.1, hμ.2⟩)
      (fun μ hμ => hsimple μ ⟨(hμLa.le.trans hab.le).trans hμ.1, hμ.2⟩)
      (fun μ hμ => hnoRight μ ⟨hab.trans_le hμ.1, hμ.2⟩)
    have hbCount : ((Q b).roots.filter (r < ·)).card =
        ((Q a).roots.filter (r < ·)).card := by
      dsimp only [Q] at hright hcountAt ⊢
      lia
    have hbNotRoot : ¬(Q b).IsRoot r := by
      intro hbr
      exact hnoRight b ⟨hab, hbμR.le⟩
        ((quadraticParameterEvaluation_isRoot_iff F G H r b).2 hbr)
    have hbNotMem : r ∉ (Q b).roots := by
      intro hmem
      exact hbNotRoot (Polynomial.isRoot_of_mem_roots hmem)
    have hprod := eval_mul_derivative_pos_of_root_count_eq
      (hsplits b hbIcc) (hpos b hbIcc) (hsplits a haIcc) (hpos a haIcc)
      (hsimple a haIcc) hroot hbNotMem hbCount
    have hQexpand : (Q b).eval r =
        (b - a) * (2 * A.eval r + (b - a) * F.eval r) := by
      have hzero : (Q a).eval r = 0 := Polynomial.IsRoot.def.mp hroot
      calc
        (Q b).eval r = (Q a).eval r +
            (b - a) * (2 * A.eval r + (b - a) * F.eval r) := by
              dsimp only [Q, A, quadraticInterlacingPencil,
                quadraticInterlacingTangent]
              simp only [eval_add, eval_mul, eval_C]
              ring
        _ = (b - a) * (2 * A.eval r + (b - a) * F.eval r) := by
          rw [hzero, zero_add]
    rw [hQexpand] at hprod
    have hneg := mul_neg_of_pos_of_neg (sub_pos.mpr hab) hphi
    apply (not_lt_of_ge hprod.le)
    nlinarith
  have hderNe : (Q a).derivative.eval r ≠ 0 :=
    (hsimple a haIcc).eval_derivative_ne_zero hroot
  rcases lt_or_gt_of_ne hderNe with hderNeg | hderPos
  · exact div_nonneg_of_nonpos (by nlinarith) hderNeg.le
  · exact div_nonneg (by nlinarith) hderPos.le

/-- If the leading spatial polynomial does not vanish at `r`, the parameter
evaluation is a genuine quadratic. -/
theorem quadraticParameterEvaluation_natDegree
    {F G H : ℝ[X]} {r : ℝ} (hrF : ¬F.IsRoot r) :
    (quadraticParameterEvaluation F G H r).natDegree = 2 := by
  have hF : F.eval r ≠ 0 := (Polynomial.not_isRoot_iff_eval_ne_zero F r).mp hrF
  rw [quadraticParameterEvaluation]
  compute_degree <;> simp_all

/-- A genuine quadratic parameter evaluation splits as soon as one real
parameter root is known. -/
theorem quadraticParameterEvaluation_splits_of_isRoot
    {F G H : ℝ[X]} {r a : ℝ} (hrF : ¬F.IsRoot r)
    (ha : (quadraticParameterEvaluation F G H r).IsRoot a) :
    (quadraticParameterEvaluation F G H r).Splits := by
  apply Polynomial.Splits.of_natDegree_eq_two
    (quadraticParameterEvaluation_natDegree hrF)
  exact Polynomial.IsRoot.def.mp ha

/-- The distinct positive parameter values at which the quadratic pencil
crosses a fixed spatial level, listed in increasing order. -/
noncomputable def positiveQuadraticParameterRoots
    (F G H : ℝ[X]) (r : ℝ) : List ℝ :=
  ((quadraticParameterEvaluation F G H r).roots.toFinset.filter (0 < ·)).sort
    (· ≤ ·)

theorem positiveQuadraticParameterRoots_pairwise
    (F G H : ℝ[X]) (r : ℝ) :
    (positiveQuadraticParameterRoots F G H r).Pairwise (· < ·) := by
  exact (Finset.sortedLT_sort
    ((quadraticParameterEvaluation F G H r).roots.toFinset.filter
      (0 < ·))).pairwise

theorem mem_positiveQuadraticParameterRoots_iff
    {F G H : ℝ[X]} {r a : ℝ} :
    a ∈ positiveQuadraticParameterRoots F G H r ↔
      a ∈ (quadraticParameterEvaluation F G H r).roots ∧ 0 < a := by
  simp [positiveQuadraticParameterRoots]

/-- A genuine quadratic parameter evaluation has at most two distinct
positive crossing parameters. -/
theorem positiveQuadraticParameterRoots_length_le_two
    {F G H : ℝ[X]} {r : ℝ} (hrF : ¬F.IsRoot r) :
    (positiveQuadraticParameterRoots F G H r).length ≤ 2 := by
  let q := quadraticParameterEvaluation F G H r
  calc
    (positiveQuadraticParameterRoots F G H r).length =
        (q.roots.toFinset.filter (0 < ·)).card := by
      simp [positiveQuadraticParameterRoots, q]
    _ ≤ q.roots.toFinset.card := Finset.card_filter_le _ _
    _ ≤ q.roots.card := Multiset.toFinset_card_le q.roots
    _ ≤ q.natDegree := Polynomial.card_roots' q
    _ = 2 := quadraticParameterEvaluation_natDegree hrF

/-- Summing parameter-root multiplicities over the ordered distinct positive
crossings recovers the positive root count of the parameter evaluation. -/
theorem sum_count_positiveQuadraticParameterRoots_eq_positiveRootCount
    (F G H : ℝ[X]) (r : ℝ) :
    ((positiveQuadraticParameterRoots F G H r).map fun a =>
        (quadraticParameterEvaluation F G H r).roots.count a).sum =
      (quadraticParameterEvaluation F G H r).positiveRootCount := by
  let q := quadraticParameterEvaluation F G H r
  let S := q.roots.toFinset.filter (0 < ·)
  have hperm : List.Perm
      ((S.sort (· ≤ ·)).map fun a => q.roots.count a)
        (S.toList.map fun a => q.roots.count a) :=
    (Finset.sort_perm_toList S (· ≤ ·)).map _
  rw [show positiveQuadraticParameterRoots F G H r = S.sort (· ≤ ·) by
    rfl]
  rw [hperm.sum_eq]
  simpa [q, S, Polynomial.positiveRootCount] using
    (sum_count_filter_toFinset_eq_countP q.roots (0 < ·))

/-- Consecutive entries of the ordered positive-crossing list delimit a
parameter chamber with no crossing in its interior. -/
theorem quadraticParameterEvaluation_not_isRoot_between_adjacent_positive
    {F G H : ℝ[X]} {r a b z : ℝ} (hrF : ¬F.IsRoot r)
    (hab : (a, b) ∈ (positiveQuadraticParameterRoots F G H r).zip
      (positiveQuadraticParameterRoots F G H r).tail)
    (haz : a < z) (hzb : z < b) :
    ¬(quadraticParameterEvaluation F G H r).IsRoot z := by
  let q := quadraticParameterEvaluation F G H r
  have hqdeg : q.natDegree = 2 := quadraticParameterEvaluation_natDegree hrF
  have hqne : q ≠ 0 := fun hzero => by simp [hzero] at hqdeg
  have hamem : a ∈ positiveQuadraticParameterRoots F G H r :=
    List.fst_mem_of_mem_zip hab
  have hapos : 0 < a :=
    (mem_positiveQuadraticParameterRoots_iff.mp hamem).2
  intro hzroot
  have hzmem : z ∈ positiveQuadraticParameterRoots F G H r := by
    rw [mem_positiveQuadraticParameterRoots_iff]
    exact ⟨(Polynomial.mem_roots hqne).2 hzroot, hapos.trans haz⟩
  exact List.not_mem_of_mem_zip_tail_of_pairwise_lt
    (positiveQuadraticParameterRoots_pairwise F G H r) hab haz hzb hzmem

/-- Before the first positive crossing, the nonnegative parameter chamber is
root-free, provided the zero endpoint is not itself a crossing. -/
theorem quadraticParameterEvaluation_not_isRoot_before_first_positive
    {F G H : ℝ[X]} {r a z : ℝ} {xs : List ℝ}
    (hrF : ¬F.IsRoot r) (hrH : ¬H.IsRoot r)
    (hrs : positiveQuadraticParameterRoots F G H r = a :: xs)
    (hz0 : 0 ≤ z) (hza : z < a) :
    ¬(quadraticParameterEvaluation F G H r).IsRoot z := by
  let q := quadraticParameterEvaluation F G H r
  have hqdeg : q.natDegree = 2 := quadraticParameterEvaluation_natDegree hrF
  have hqne : q ≠ 0 := fun hzero => by simp [hzero] at hqdeg
  intro hzroot
  rcases hz0.eq_or_lt with rfl | hzpos
  · apply hrH
    simpa [quadraticInterlacingPencil] using
      (quadraticParameterEvaluation_isRoot_iff F G H r 0).1 hzroot
  · have hzmem : z ∈ positiveQuadraticParameterRoots F G H r := by
      rw [mem_positiveQuadraticParameterRoots_iff]
      exact ⟨(Polynomial.mem_roots hqne).2 hzroot, hzpos⟩
    rw [hrs] at hzmem
    rcases List.mem_cons.mp hzmem with hzaeq | hzmem
    · subst z
      exact (lt_irrefl a hza).elim
    · have hpair := positiveQuadraticParameterRoots_pairwise F G H r
      rw [hrs, List.pairwise_cons] at hpair
      exact (not_lt_of_ge hza.le) (hpair.1 z hzmem)

/-- After the final positive crossing, the parameter chamber is root-free. -/
theorem quadraticParameterEvaluation_not_isRoot_after_last_positive
    {F G H : ℝ[X]} {r a z : ℝ} {xs : List ℝ}
    (hrF : ¬F.IsRoot r)
    (hrs : positiveQuadraticParameterRoots F G H r = xs ++ [a])
    (haz : a < z) :
    ¬(quadraticParameterEvaluation F G H r).IsRoot z := by
  let q := quadraticParameterEvaluation F G H r
  have hqdeg : q.natDegree = 2 := quadraticParameterEvaluation_natDegree hrF
  have hqne : q ≠ 0 := fun hzero => by simp [hzero] at hqdeg
  have hamem : a ∈ positiveQuadraticParameterRoots F G H r := by
    rw [hrs, List.mem_append]
    simp
  have hapos : 0 < a :=
    (mem_positiveQuadraticParameterRoots_iff.mp hamem).2
  intro hzroot
  have hzmem : z ∈ positiveQuadraticParameterRoots F G H r := by
    rw [mem_positiveQuadraticParameterRoots_iff]
    exact ⟨(Polynomial.mem_roots hqne).2 hzroot, hapos.trans haz⟩
  have hpair := positiveQuadraticParameterRoots_pairwise F G H r
  rw [hrs, List.pairwise_append] at hpair
  rw [hrs, List.mem_append] at hzmem
  rcases hzmem with hzxs | hzlast
  · have hza := hpair.2.2 z hzxs a (by simp)
    exact (not_lt_of_ge haz.le) hza
  · simp only [List.mem_singleton] at hzlast
    subst z
    exact (lt_irrefl a haz).elim

/-- Beyond the Cauchy bound, the parameter evaluation has no roots.  This
provides a canonical terminal chamber to the right of every positive crossing. -/
theorem quadraticParameterEvaluation_not_isRoot_above_cauchyBound
    {F G H : ℝ[X]} {r A z : ℝ} (hrF : ¬F.IsRoot r)
    (hA : ((quadraticParameterEvaluation F G H r).cauchyBound : ℝ) ≤ A)
    (hAz : A ≤ z) :
    ¬(quadraticParameterEvaluation F G H r).IsRoot z := by
  let q := quadraticParameterEvaluation F G H r
  have hqdeg : q.natDegree = 2 := quadraticParameterEvaluation_natDegree hrF
  have hqne : q ≠ 0 := fun hzero => by simp [hzero] at hqdeg
  intro hzroot
  have hzlt : |z| < (q.cauchyBound : ℝ) := by
    have hlt := hzroot.norm_lt_cauchyBound hqne
    exact_mod_cast hlt
  have hznonneg : 0 ≤ z :=
    (NNReal.coe_nonneg q.cauchyBound).trans (hA.trans hAz)
  rw [abs_of_nonneg hznonneg] at hzlt
  exact (not_lt_of_ge (hA.trans hAz)) hzlt

/-- The constant and leading coefficients of the parameter evaluation are
the endpoint evaluations `H(r)` and `F(r)`. -/
theorem quadraticParameterEvaluation_end_coeffs (F G H : ℝ[X]) (r : ℝ) :
    (quadraticParameterEvaluation F G H r).coeff 0 = H.eval r ∧
      (quadraticParameterEvaluation F G H r).coeff 2 = F.eval r := by
  simp [quadraticParameterEvaluation]

/-- Opposite endpoint coefficients allow at most one positive parameter root. -/
private theorem quadraticParameterEvaluation_positiveRootCount_le_one_of_mul_neg
    {F G H : ℝ[X]} {r : ℝ} (hFHneg : F.eval r * H.eval r < 0) :
    (quadraticParameterEvaluation F G H r).positiveRootCount ≤ 1 := by
  let p := quadraticParameterEvaluation F G H r
  have hFne : F.eval r ≠ 0 := left_ne_zero_of_mul hFHneg.ne
  have hHne : H.eval r ≠ 0 := right_ne_zero_of_mul hFHneg.ne
  have hrF : ¬F.IsRoot r := (Polynomial.not_isRoot_iff_eval_ne_zero F r).mpr hFne
  have hpdeg : p.natDegree = 2 := quadraticParameterEvaluation_natDegree hrF
  have hpne : p ≠ 0 := fun hpzero => by simp [hpzero] at hpdeg
  have hsign : sign (F.eval r) ≠ sign (H.eval r) :=
    (SignType.sign_ne_zero_and_ne_of_mul_neg hFHneg).2.2
  have hlead : p.leadingCoeff = F.eval r := by
    rw [leadingCoeff, hpdeg]
    exact (quadraticParameterEvaluation_end_coeffs F G H r).2
  have htrail : p.trailingCoeff = H.eval r := by
    rw [trailingCoeff_eq_coeff_zero]
    · exact (quadraticParameterEvaluation_end_coeffs F G H r).1
    · rw [(quadraticParameterEvaluation_end_coeffs F G H r).1]
      exact hHne
  have hodd : Odd p.signVariations := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    apply hsign
    rw [← hlead, ← htrail]
    exact (even_signVariations_iff_sign_leadingCoeff_eq_sign_trailingCoeff hpne).mp heven
  have hvarLe : p.signVariations ≤ 2 := by
    have h := List.signVariations_le_length_sub_one p.coeffList
    simpa [Polynomial.signVariations, hpne, hpdeg] using h
  have hvar : p.signVariations = 1 := by
    rcases hodd with ⟨k, hk⟩
    lia
  simpa only [hvar] using (descartes_rule_of_signs p).1

/-- **Descartes crossing budget for a quadratic interlacing chain.**

At a level avoiding the roots of `F`, `G`, and `H`, the number of positive
parameter values at which the quadratic pencil crosses that level is at most
the drop in the strict-upper root count from `H` to `F`.

This is the exact algebraic counting input in the quadratic closure argument.
The two adjacent root-count drops are each zero or one by oriented
interlacing.  If their sum is zero, all three evaluations have the same sign
and there is no positive crossing.  If it is one, the endpoint coefficients
of the parameter quadratic have opposite signs, so Descartes' rule gives one
crossing at most.  The remaining sum-two case follows from its degree. -/
theorem quadraticParameterEvaluation_positiveRootCount_le
    {F G H : ℝ[X]} {r : ℝ}
    (hFpos : HasPosLeadingCoeff F) (hGpos : HasPosLeadingCoeff G)
    (hHpos : HasPosLeadingCoeff H) (hFG : StrictInterl F G)
    (hGH : StrictInterl G H) (hrF : ¬F.IsRoot r)
    (hrG : ¬G.IsRoot r) (hrH : ¬H.IsRoot r) :
    (quadraticParameterEvaluation F G H r).positiveRootCount ≤
      (H.roots.filter (r < ·)).card - (F.roots.filter (r < ·)).card := by
  let nF := (F.roots.filter (r < ·)).card
  let nG := (G.roots.filter (r < ·)).card
  let nH := (H.roots.filter (r < ·)).card
  let e : ℝ := (-1 : ℝ) ^ nF
  let p := quadraticParameterEvaluation F G H r
  change p.positiveRootCount ≤ nH - nF
  have hrF' : r ∉ F.roots := fun hr =>
    hrF (Polynomial.isRoot_of_mem_roots hr)
  have hrG' : r ∉ G.roots := fun hr =>
    hrG (Polynomial.isRoot_of_mem_roots hr)
  have hrH' : r ∉ H.roots := fun hr =>
    hrH (Polynomial.isRoot_of_mem_roots hr)
  have hFe : 0 < F.eval r * e := by
    simpa [e, nF, Multiset.countP_eq_card_filter] using
      eval_sign hFG.1.2 hFpos r hrF'
  have hGeRaw : 0 < G.eval r * (-1 : ℝ) ^ nG := by
    simpa [nG, Multiset.countP_eq_card_filter] using
      eval_sign hFG.2.1.2 hGpos r hrG'
  have hHeRaw : 0 < H.eval r * (-1 : ℝ) ^ nH := by
    simpa [nH, Multiset.countP_eq_card_filter] using
      eval_sign hGH.2.1.2 hHpos r hrH'
  have hFGcount := rootCountAboveOriented_of_strictInterl hFG r
  have hGHcount := rootCountAboveOriented_of_strictInterl hGH r
  have hnFG : nG = nF ∨ nG = nF + 1 := by
    have hle : nF ≤ nG := by
      exact_mod_cast hFGcount.1
    have hle' : nG ≤ nF + 1 := by
      exact_mod_cast hFGcount.2
    grind
  have hnGH : nH = nG ∨ nH = nG + 1 := by
    have hle : nG ≤ nH := by
      exact_mod_cast hGHcount.1
    have hle' : nH ≤ nG + 1 := by
      exact_mod_cast hGHcount.2
    grind
  have hpdeg : p.natDegree = 2 :=
    quadraticParameterEvaluation_natDegree hrF
  have hpositiveRootsLeOne (hHe : H.eval r * e < 0) :
      p.positiveRootCount ≤ 1 := by
    have hFHneg : F.eval r * H.eval r < 0 := by
      have heSq : e * e = 1 := by
        dsimp only [e]
        rw [← pow_add]
        simp
      have hprod := mul_neg_of_pos_of_neg hFe hHe
      nlinarith
    exact quadraticParameterEvaluation_positiveRootCount_le_one_of_mul_neg hFHneg
  have hdropOne (hn : nH = nF + 1) : p.positiveRootCount ≤ nH - nF := by
    have hHe : H.eval r * e < 0 := by
      rw [hn, pow_succ] at hHeRaw
      dsimp only [e]
      nlinarith
    simpa [hn] using hpositiveRootsLeOne hHe
  rcases hnFG with hGF | hGF <;> rcases hnGH with hHG | hHG
  · have hGe : 0 < G.eval r * e := by simpa [hGF, e] using hGeRaw
    have hHe : 0 < H.eval r * e := by simpa [hHG, hGF, e] using hHeRaw
    have hno : p.positiveRootCount = 0 := by
      rw [positiveRootCount, Multiset.countP_eq_zero]
      intro a ha hapos
      have hroot : p.IsRoot a := Polynomial.isRoot_of_mem_roots ha
      have hpval : 0 < p.eval a * e := by
        rw [show p.eval a =
            H.eval r + 2 * a * G.eval r + a ^ 2 * F.eval r by
          simp [p, quadraticParameterEvaluation]
          ring]
        nlinarith [mul_pos hapos hGe, mul_pos (sq_pos_of_pos hapos) hFe]
      rw [Polynomial.IsRoot.def.mp hroot, zero_mul] at hpval
      exact lt_irrefl 0 hpval
    simp [hGF, hHG, hno]
  · exact hdropOne (by lia)
  · exact hdropOne (by lia)
  · have hroots : p.positiveRootCount ≤ 2 := by
      exact le_trans (Multiset.countP_le_card _ _)
        ((Polynomial.card_roots' p).trans_eq hpdeg)
    simpa [hGF, hHG, Nat.add_assoc] using hroots

/-- If there is exactly one positive crossing parameter, its chamber-count
jump is downward and equals its full parameter-root multiplicity. -/
theorem quadraticInterlacingPencil_one_positive_crossing_exact_drop
    {F G H : ℝ[X]} {r a R : ℝ} {D : ℕ}
    (hFpos : HasPosLeadingCoeff F) (hGpos : HasPosLeadingCoeff G)
    (hHpos : HasPosLeadingCoeff H) (hFG : StrictInterl F G)
    (hGH : StrictInterl G H) (hrF : ¬F.IsRoot r)
    (hrG : ¬G.IsRoot r) (hrH : ¬H.IsRoot r)
    (hrs : positiveQuadraticParameterRoots F G H r = [a])
    (haR : a < R) (hD : D ≠ 0)
    (hdegree : ∀ μ ∈ Set.Icc (0 : ℝ) R,
      (quadraticInterlacingPencil F G H μ).natDegree = D)
    (hdegree_local : ∀ μ ∈ Set.Icc (0 : ℝ) R, ∀ᶠ b in 𝓝 μ,
      (quadraticInterlacingPencil F G H b).natDegree = D)
    (hsplits : ∀ μ ∈ Set.Icc (0 : ℝ) R,
      (quadraticInterlacingPencil F G H μ).Splits)
    (hsimple : ∀ μ ∈ Set.Icc (0 : ℝ) R,
      HasSimpleRoots (quadraticInterlacingPencil F G H μ))
    (hR : ((quadraticInterlacingPencil F G H R).roots.filter (r < ·)).card =
      (F.roots.filter (r < ·)).card) :
    ((quadraticInterlacingPencil F G H 0).roots.filter (r < ·)).card =
      ((quadraticInterlacingPencil F G H R).roots.filter (r < ·)).card +
        (quadraticParameterEvaluation F G H r).roots.count a ∧
      (quadraticParameterEvaluation F G H r).roots.count a = 1 := by
  let q := quadraticParameterEvaluation F G H r
  have hamem : a ∈ positiveQuadraticParameterRoots F G H r := by
    simp [hrs]
  obtain ⟨haq, hapos⟩ := mem_positiveQuadraticParameterRoots_iff.mp hamem
  have haroot : q.IsRoot a := Polynomial.isRoot_of_mem_roots haq
  have haQroot : (quadraticInterlacingPencil F G H a).IsRoot r :=
    (quadraticParameterEvaluation_isRoot_iff F G H r a).1 haroot
  have hjump :=
    quadraticInterlacingPencil_card_roots_gt_left_le_right_add_one
      (show (0 : ℝ) < a from hapos) haR hD hdegree hdegree_local hsplits
      hsimple haQroot
      (fun μ hμ => quadraticParameterEvaluation_not_isRoot_before_first_positive
        hrF hrH hrs hμ.1 hμ.2)
      (fun μ hμ => quadraticParameterEvaluation_not_isRoot_after_last_positive
        hrF (xs := []) (by simpa using hrs) hμ.1)
  have hmult : 1 ≤ q.roots.count a := Multiset.one_le_count_iff_mem.mpr haq
  have hsum :=
    sum_count_positiveQuadraticParameterRoots_eq_positiveRootCount F G H r
  rw [hrs] at hsum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at hsum
  have hbudget0 := quadraticParameterEvaluation_positiveRootCount_le
    hFpos hGpos hHpos hFG hGH hrF hrG hrH
  have hbudget : q.roots.count a ≤
      (H.roots.filter (r < ·)).card - (F.roots.filter (r < ·)).card := by
    rw [hsum]
    exact hbudget0
  have hFleH : (F.roots.filter (r < ·)).card ≤
      (H.roots.filter (r < ·)).card := by
    have hFGcount := (rootCountAboveOriented_of_strictInterl hFG r).1
    have hGHcount := (rootCountAboveOriented_of_strictInterl hGH r).1
    exact_mod_cast hFGcount.trans hGHcount
  have hQ0 : quadraticInterlacingPencil F G H 0 = H := by
    simp [quadraticInterlacingPencil]
  have hdrop := Nat.sub_add_cancel hFleH
  rw [hQ0] at hjump ⊢
  rw [hR] at hjump ⊢
  change q.roots.count a ≤ _ at hbudget
  have hmult_eq_drop : q.roots.count a =
      (H.roots.filter (r < ·)).card - (F.roots.filter (r < ·)).card := by
    lia
  rw [hmult_eq_drop]
  constructor <;> lia

/-- Two ordered positive crossings bound each neighboring chamber drop by one. -/
private theorem quadraticInterlacingPencil_two_crossing_bounds
    {F G H : ℝ[X]} {r a b R : ℝ} {D : ℕ}
    (hrF : ¬F.IsRoot r) (hrH : ¬H.IsRoot r)
    (hrs : positiveQuadraticParameterRoots F G H r = [a, b])
    (hbR : b < R) (hD : D ≠ 0)
    (hdegree : ∀ μ ∈ Set.Icc (0 : ℝ) R,
      (quadraticInterlacingPencil F G H μ).natDegree = D)
    (hdegree_local : ∀ μ ∈ Set.Icc (0 : ℝ) R, ∀ᶠ c in 𝓝 μ,
      (quadraticInterlacingPencil F G H c).natDegree = D)
    (hsplits : ∀ μ ∈ Set.Icc (0 : ℝ) R,
      (quadraticInterlacingPencil F G H μ).Splits)
    (hsimple : ∀ μ ∈ Set.Icc (0 : ℝ) R,
      HasSimpleRoots (quadraticInterlacingPencil F G H μ)) :
    let m := (a + b) / 2
    ((quadraticInterlacingPencil F G H 0).roots.filter (r < ·)).card ≤
        ((quadraticInterlacingPencil F G H m).roots.filter (r < ·)).card + 1 ∧
      ((quadraticInterlacingPencil F G H m).roots.filter (r < ·)).card ≤
        ((quadraticInterlacingPencil F G H R).roots.filter (r < ·)).card + 1 ∧
      1 ≤ (quadraticParameterEvaluation F G H r).roots.count a ∧
      1 ≤ (quadraticParameterEvaluation F G H r).roots.count b := by
  dsimp only
  let q := quadraticParameterEvaluation F G H r
  let m := (a + b) / 2
  have hamem : a ∈ positiveQuadraticParameterRoots F G H r := by
    simp [hrs]
  have hbmem : b ∈ positiveQuadraticParameterRoots F G H r := by
    simp [hrs]
  obtain ⟨hamemQ, hapos⟩ := mem_positiveQuadraticParameterRoots_iff.mp hamem
  obtain ⟨hbmemQ, hbpos⟩ := mem_positiveQuadraticParameterRoots_iff.mp hbmem
  have hab : a < b := by
    have hpair := positiveQuadraticParameterRoots_pairwise F G H r
    rw [hrs] at hpair
    simpa using hpair
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  have hmR : m < R := hmb.trans hbR
  have hm0 : (0 : ℝ) ≤ m := hapos.le.trans ham.le
  have haRoot : q.IsRoot a := Polynomial.isRoot_of_mem_roots hamemQ
  have hbRoot : q.IsRoot b := Polynomial.isRoot_of_mem_roots hbmemQ
  have haQroot : (quadraticInterlacingPencil F G H a).IsRoot r :=
    (quadraticParameterEvaluation_isRoot_iff F G H r a).1 haRoot
  have hbQroot : (quadraticInterlacingPencil F G H b).IsRoot r :=
    (quadraticParameterEvaluation_isRoot_iff F G H r b).1 hbRoot
  have habZip : (a, b) ∈
      (positiveQuadraticParameterRoots F G H r).zip
        (positiveQuadraticParameterRoots F G H r).tail := by
    rw [hrs]
    simp
  have hjumpA :=
    quadraticInterlacingPencil_card_roots_gt_left_le_right_add_one
      hapos ham hD
      (fun μ hμ => hdegree μ ⟨hμ.1, hμ.2.trans hmR.le⟩)
      (fun μ hμ => hdegree_local μ ⟨hμ.1, hμ.2.trans hmR.le⟩)
      (fun μ hμ => hsplits μ ⟨hμ.1, hμ.2.trans hmR.le⟩)
      (fun μ hμ => hsimple μ ⟨hμ.1, hμ.2.trans hmR.le⟩)
      haQroot
      (fun μ hμ => quadraticParameterEvaluation_not_isRoot_before_first_positive
        hrF hrH hrs hμ.1 hμ.2)
      (fun μ hμ => quadraticParameterEvaluation_not_isRoot_between_adjacent_positive
        hrF habZip hμ.1 (hμ.2.trans_lt hmb))
  have hjumpB :=
    quadraticInterlacingPencil_card_roots_gt_left_le_right_add_one
      hmb hbR hD
      (fun μ hμ => hdegree μ ⟨hm0.trans hμ.1, hμ.2⟩)
      (fun μ hμ => hdegree_local μ ⟨hm0.trans hμ.1, hμ.2⟩)
      (fun μ hμ => hsplits μ ⟨hm0.trans hμ.1, hμ.2⟩)
      (fun μ hμ => hsimple μ ⟨hm0.trans hμ.1, hμ.2⟩)
      hbQroot
      (fun μ hμ => quadraticParameterEvaluation_not_isRoot_between_adjacent_positive
        hrF habZip (ham.trans_le hμ.1) hμ.2)
      (fun μ hμ => quadraticParameterEvaluation_not_isRoot_after_last_positive
        hrF (xs := [a]) (by simpa using hrs) hμ.1)
  have hmultA : 1 ≤ q.roots.count a := Multiset.one_le_count_iff_mem.mpr hamemQ
  have hmultB : 1 ≤ q.roots.count b := Multiset.one_le_count_iff_mem.mpr hbmemQ
  exact ⟨hjumpA, hjumpB, hmultA, hmultB⟩

/-- With two positive crossing parameters, both successive chamber-count
jumps are downward and equal their full parameter-root multiplicities. -/
theorem quadraticInterlacingPencil_two_positive_crossings_exact_drop
    {F G H : ℝ[X]} {r a b R : ℝ} {D : ℕ}
    (hFpos : HasPosLeadingCoeff F) (hGpos : HasPosLeadingCoeff G)
    (hHpos : HasPosLeadingCoeff H) (hFG : StrictInterl F G)
    (hGH : StrictInterl G H) (hrF : ¬F.IsRoot r)
    (hrG : ¬G.IsRoot r) (hrH : ¬H.IsRoot r)
    (hrs : positiveQuadraticParameterRoots F G H r = [a, b])
    (hbR : b < R) (hD : D ≠ 0)
    (hdegree : ∀ μ ∈ Set.Icc (0 : ℝ) R,
      (quadraticInterlacingPencil F G H μ).natDegree = D)
    (hdegree_local : ∀ μ ∈ Set.Icc (0 : ℝ) R, ∀ᶠ c in 𝓝 μ,
      (quadraticInterlacingPencil F G H c).natDegree = D)
    (hsplits : ∀ μ ∈ Set.Icc (0 : ℝ) R,
      (quadraticInterlacingPencil F G H μ).Splits)
    (hsimple : ∀ μ ∈ Set.Icc (0 : ℝ) R,
      HasSimpleRoots (quadraticInterlacingPencil F G H μ))
    (hR : ((quadraticInterlacingPencil F G H R).roots.filter (r < ·)).card =
      (F.roots.filter (r < ·)).card) :
    let m := (a + b) / 2
    ((quadraticInterlacingPencil F G H 0).roots.filter (r < ·)).card =
        ((quadraticInterlacingPencil F G H m).roots.filter (r < ·)).card +
          (quadraticParameterEvaluation F G H r).roots.count a ∧
      ((quadraticInterlacingPencil F G H m).roots.filter (r < ·)).card =
        ((quadraticInterlacingPencil F G H R).roots.filter (r < ·)).card +
          (quadraticParameterEvaluation F G H r).roots.count b ∧
      (quadraticParameterEvaluation F G H r).roots.count a = 1 ∧
      (quadraticParameterEvaluation F G H r).roots.count b = 1 := by
  dsimp only
  let q := quadraticParameterEvaluation F G H r
  let m := (a + b) / 2
  change
    ((quadraticInterlacingPencil F G H 0).roots.filter (r < ·)).card =
        ((quadraticInterlacingPencil F G H m).roots.filter (r < ·)).card +
          q.roots.count a ∧
      ((quadraticInterlacingPencil F G H m).roots.filter (r < ·)).card =
        ((quadraticInterlacingPencil F G H R).roots.filter (r < ·)).card +
          q.roots.count b ∧
      q.roots.count a = 1 ∧ q.roots.count b = 1
  obtain ⟨hjumpA, hjumpB, hmultA, hmultB⟩ :=
    quadraticInterlacingPencil_two_crossing_bounds hrF hrH hrs hbR hD
      hdegree hdegree_local hsplits hsimple
  have hsum :=
    sum_count_positiveQuadraticParameterRoots_eq_positiveRootCount F G H r
  rw [hrs] at hsum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at hsum
  have hbudget0 := quadraticParameterEvaluation_positiveRootCount_le
    hFpos hGpos hHpos hFG hGH hrF hrG hrH
  have hbudget : q.roots.count a + q.roots.count b ≤
      (H.roots.filter (r < ·)).card - (F.roots.filter (r < ·)).card := by
    rw [hsum]
    exact hbudget0
  have hFleH : (F.roots.filter (r < ·)).card ≤
      (H.roots.filter (r < ·)).card := by
    have hFGcount := (rootCountAboveOriented_of_strictInterl hFG r).1
    have hGHcount := (rootCountAboveOriented_of_strictInterl hGH r).1
    exact_mod_cast hFGcount.trans hGHcount
  have hdrop := Nat.sub_add_cancel hFleH
  have hQ0 : quadraticInterlacingPencil F G H 0 = H := by
    simp [quadraticInterlacingPencil]
  rw [hQ0] at hjumpA ⊢
  rw [hR] at hjumpB ⊢
  change q.roots.count a + q.roots.count b ≤ _ at hbudget
  have hmult_eq_drop : q.roots.count a + q.roots.count b =
      (H.roots.filter (r < ·)).card - (F.roots.filter (r < ·)).card := by
    lia
  exact ⟨by lia, by lia, by lia, by lia⟩

end RealRooted
