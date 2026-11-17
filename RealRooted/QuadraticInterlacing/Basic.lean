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

/-!
# Quadratic pencils and regularization

Quadratic pencils, their tangents and right pencils, derivative-shift
regularization, degree bounds, and local smooth root paths.
-/

@[expose] public section

open Polynomial
open SignType
open Topology
open scoped ContDiff

noncomputable section

namespace RealRooted


/-! ## Derivative-shift regularization of oriented pairs -/

/-- Applying the same derivative shift to an oriented interlacing pair
preserves its orientation. In the equal-degree case, the all-combination
criterion determines the pair only up to reversal; the common translation of
the two root sums selects the original orientation. -/
theorem StrictInterl.tDeriv_common {f g : ℝ[X]} (hfg : StrictInterl f g)
    (eps : ℝ) : StrictInterl (tDeriv eps f) (tDeriv eps g) := by
  have hall : AllComboRealRooted f g := allComboRealRooted_of_strictInterl hfg
  have hallT : AllComboRealRooted (tDeriv eps f) (tDeriv eps g) := by
    simpa [iterateTDeriv_succ] using
      allComboRealRooted_iterateTDeriv_all hall eps 1
  rcases hfg.natDegree_eq_or_eq_succ with hsame | hsucc
  · have horient :
        StrictInterl (tDeriv eps f) (tDeriv eps g) ∨
          StrictInterl (tDeriv eps g) (tDeriv eps f) :=
      strictInterl_of_allComboRealRooted
        (tDeriv_ne_zero hfg.1.1) (splits_tDeriv_all hfg.1.2)
        (tDeriv_ne_zero hfg.2.1.1) (splits_tDeriv_all hfg.2.1.2)
        hallT (Or.inr (by simpa using hsame.symm))
    rcases horient with hforward | hreverse
    · exact hforward
    · apply hreverse.of_reverse_of_roots_sum_le
      · simpa using hsame.symm
      · rw [roots_sum_tDeriv eps hfg.1.1 hfg.1.2,
          roots_sum_tDeriv eps hfg.2.1.1 hfg.2.1.2]
        simpa [hsame] using
          add_le_add_right (hfg.roots_sum_le_of_sameDegree hsame.symm)
            (eps * (f.natDegree : ℝ))
  · apply StrictInterl.forward_of_orientation_of_succDegree (by simpa using hsucc)
    exact strictInterl_of_allComboRealRooted
      (tDeriv_ne_zero hfg.1.1) (splits_tDeriv_all hfg.1.2)
      (tDeriv_ne_zero hfg.2.1.1) (splits_tDeriv_all hfg.2.1.2)
      hallT (Or.inl (by simpa using hsucc.symm))

/-- Common iterated derivative shifts preserve oriented interlacing. -/
theorem StrictInterl.iterateTDeriv_common {f g : ℝ[X]}
    (hfg : StrictInterl f g) (eps : ℝ) :
    ∀ k : ℕ, StrictInterl (iterateTDeriv eps k f) (iterateTDeriv eps k g)
  | 0 => by simpa
  | k + 1 => by
      rw [iterateTDeriv_succ, iterateTDeriv_succ]
      exact (hfg.iterateTDeriv_common eps k).tDeriv_common eps

/-- If every positive nonnegative-coefficient derivative regularization of a
pair is in proper position, then so is the original pair. This is the closure
step that lets the quadratic argument be proved first with simple roots. -/
theorem strictInterl_of_iterateTDeriv_neg
    {f g : ℝ[X]} (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0) (k : ℕ)
    (hreg : ∀ eps : ℝ, 0 < eps →
      StrictInterl (iterateTDeriv (-eps) k f)
        (iterateTDeriv (-eps) k g)) :
    StrictInterl f g := by
  let delta : ℕ → ℝ := fun M ↦ ((M : ℝ) + 1)⁻¹
  have hdelta_pos (M : ℕ) : 0 < delta M := by
    dsimp [delta]
    positivity
  have hdelta : Filter.Tendsto delta Filter.atTop (nhds 0) := by
    simpa [delta, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hneg_delta :
      Filter.Tendsto (fun M ↦ -(delta M)) Filter.atTop (nhds 0) := by
    simpa using hdelta.neg
  let fM : ℕ → ℝ[X] := fun M ↦ iterateTDeriv (-(delta M)) k f
  let gM : ℕ → ℝ[X] := fun M ↦ iterateTDeriv (-(delta M)) k g
  have hinterl (M : ℕ) : Interl (fM M) (gM M) :=
    (hreg (delta M) (hdelta_pos M)).toInterl
  have hfM_pf (M : ℕ) : IsPFPolynomial (fM M) := by
    apply IsPFPolynomial.of_realRooted_nonneg
    · exact hf.iterateTDeriv_neg (hdelta_pos M).le k
    · exact (hreg (delta M) (hdelta_pos M)).1.2
  have hgM_pf (M : ℕ) : IsPFPolynomial (gM M) := by
    apply IsPFPolynomial.of_realRooted_nonneg
    · exact hg.iterateTDeriv_neg (hdelta_pos M).le k
    · exact (hreg (delta M) (hdelta_pos M)).2.1.2
  have hlimit : Interl f g :=
    interl_of_pf_coeff_tendsto_of_natDegree_le hfM_pf hgM_pf hinterl
      (N := max f.natDegree g.natDegree)
      (fun M ↦ by simp [fM]) (fun M ↦ by simp [gM])
      (fun i ↦ by
        simpa [fM, Function.comp_def] using
          (continuousAt_coeff_iterateTDeriv_zero k f i).tendsto.comp hneg_delta)
      (fun i ↦ by
        simpa [gM, Function.comp_def] using
          (continuousAt_coeff_iterateTDeriv_zero k g i).tendsto.comp hneg_delta)
  exact hlimit.toStrictInterl_of_ne hf_ne hg_ne

/-- The quadratic polynomial path `H + 2 a G + a² F`. -/
def quadraticInterlacingPencil (F G H : ℝ[X]) (a : ℝ) : ℝ[X] :=
  H + C (2 * a) * G + C (a ^ 2) * F

/-- Half of the parameter derivative of `quadraticInterlacingPencil`. -/
def quadraticInterlacingTangent (F G : ℝ[X]) (a : ℝ) : ℝ[X] :=
  G + C a * F

/-- The right member in the quadratic closure conclusion. -/
def quadraticInterlacingRight (G H : ℝ[X]) (a : ℝ) : ℝ[X] :=
  H + C a * G

/-- The fixed-degree reflection of the reciprocal-parameter quadratic pencil.

For `b ≠ 0`, its unreflected member is `b² Q (b⁻¹)`. At `b = 0` it is
`F`, so reflection turns roots escaping as `a → ∞` into ordinary roots near
zero. -/
def compactifiedQuadraticInterlacingPencil
    (F G H : ℝ[X]) (D : ℕ) (b : ℝ) : ℝ[X] :=
  reflect D (quadraticInterlacingPencil H G F b)

/-- A common degree bound for the three coefficient polynomials bounds every
member of their quadratic pencil. -/
theorem natDegree_quadraticInterlacingPencil_le
    {F G H : ℝ[X]} {D : ℕ}
    (hF : F.natDegree ≤ D) (hG : G.natDegree ≤ D)
    (hH : H.natDegree ≤ D) (a : ℝ) :
    (quadraticInterlacingPencil F G H a).natDegree ≤ D := by
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_add_le _ _).trans
      (max_le hH ((natDegree_C_mul_le _ _).trans hG))
  · exact (natDegree_C_mul_le _ _).trans hF

/-- A nonnegative quadratic pencil has the degree of its right endpoint when
the other two coefficient polynomials have no larger degree. -/
theorem natDegree_quadraticInterlacingPencil_eq
    {F G H : ℝ[X]} (hF : HasNonnegCoeffs F)
    (hG : HasNonnegCoeffs G) (hH : HasNonnegCoeffs H) (hHne : H ≠ 0)
    (hFdeg : F.natDegree ≤ H.natDegree)
    (hGdeg : G.natDegree ≤ H.natDegree)
    {a : ℝ} (ha : 0 ≤ a) :
    (quadraticInterlacingPencil F G H a).natDegree = H.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_quadraticInterlacingPencil_le hFdeg hGdeg le_rfl a
  · have hHlead : 0 < H.coeff H.natDegree := by
      have hlead := hH.pos_leadingCoeff hHne
      rw [HasPosLeadingCoeff, leadingCoeff] at hlead
      exact hlead
    have hGcoeff : 0 ≤ G.coeff H.natDegree := hG H.natDegree
    have hFcoeff : 0 ≤ F.coeff H.natDegree := hF H.natDegree
    simp only [quadraticInterlacingPencil, coeff_add, coeff_C_mul]
    nlinarith [mul_nonneg ha hGcoeff, mul_nonneg (sq_nonneg a) hFcoeff]

/-- The compactified pencil has degree at most its reflection degree. -/
theorem natDegree_compactifiedQuadraticInterlacingPencil_le
    {F G H : ℝ[X]} {D : ℕ}
    (hF : F.natDegree ≤ D) (hG : G.natDegree ≤ D)
    (hH : H.natDegree ≤ D) (b : ℝ) :
    (compactifiedQuadraticInterlacingPencil F G H D b).natDegree ≤ D := by
  unfold compactifiedQuadraticInterlacingPencil
  refine Polynomial.natDegree_reflect_le.trans ?_
  rw [max_eq_left]
  exact natDegree_quadraticInterlacingPencil_le hH hG hF b

/-- Every coefficient of the compactified reciprocal pencil is continuous in
the reciprocal parameter. -/
theorem continuous_coeff_compactifiedQuadraticInterlacingPencil
    (F G H : ℝ[X]) (D i : ℕ) :
    Continuous fun b =>
      (compactifiedQuadraticInterlacingPencil F G H D b).coeff i := by
  simp only [compactifiedQuadraticInterlacingPencil, coeff_reflect,
    quadraticInterlacingPencil, coeff_add, coeff_C_mul]
  fun_prop

/-- At reciprocal parameter zero, the compactified pencil is the fixed-degree
reflection of `F`. -/
@[simp] theorem compactifiedQuadraticInterlacingPencil_zero
    (F G H : ℝ[X]) (D : ℕ) :
    compactifiedQuadraticInterlacingPencil F G H D 0 = reflect D F := by
  simp [compactifiedQuadraticInterlacingPencil,
    quadraticInterlacingPencil]

/-- Near the compactified `a = ∞` endpoint, the strict-upper root count of the
reflected pencil is constant across every level avoiding the reflected roots
of `F`.

The nearby member is required to split only when the conclusion is consumed;
the theorem's continuity argument itself is valid for the full real parameter
line. Repeated zero roots created by a degree drop are handled by the general
multiplicity-persistence theorem. -/
theorem eventually_compactifiedQuadraticInterlacingPencil_card_roots_gt_eq
    {F G H : ℝ[X]} {D : ℕ}
    (hF : F.natDegree ≤ D) (hG : G.natDegree ≤ D)
    (hH : H.natDegree ≤ D) (hF0 : F.coeff 0 ≠ 0)
    (hFsplit : F.Splits) {s : ℝ} (hs : s ∉ (reflect D F).roots) :
    ∀ᶠ b in 𝓝 0,
      (compactifiedQuadraticInterlacingPencil F G H D b).Splits →
        ((compactifiedQuadraticInterlacingPencil F G H D b).roots.filter
            (s < ·)).card =
          ((reflect D F).roots.filter (s < ·)).card := by
  let p : ℝ → ℝ[X] := fun b =>
    compactifiedQuadraticInterlacingPencil F G H D b
  have hdegree_le : ∀ b, (p b).natDegree ≤ D := fun b =>
    natDegree_compactifiedQuadraticInterlacingPencil_le hF hG hH b
  have hp0 : p 0 = reflect D F := by simp [p]
  have hp0degree : (p 0).natDegree = D := by
    rw [hp0]
    exact DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne hF hF0
  have hp0ne : p 0 ≠ 0 := by
    rw [hp0]
    apply leadingCoeff_ne_zero.mp
    rw [DegreeDropReversal.leadingCoeff_reflect_eq_coeff_zero_of_natDegree_le hF hF0]
    exact hF0
  have hp0split : (p 0).Splits := by
    rw [hp0]
    exact Polynomial.Splits.reflect hFsplit hF
  have hcoeff : ∀ i, Continuous fun b => (p b).coeff i := fun i => by
    simpa [p] using
      continuous_coeff_compactifiedQuadraticInterlacingPencil F G H D i
  obtain ⟨ρ, hρ, hbridge⟩ :=
    exists_radius_card_roots_filter_gt_eq_of_sameDegree_local_lower_counts
      (p := p 0) (x := s) (by simpa [hp0] using hs)
  have hlower :=
    eventually_forall_root_count_le_card_filter_near_of_continuous_coeff
      p hdegree_le hp0degree hcoeff hp0split ρ hρ
  have hdegree :=
    Polynomial.eventually_natDegree_eq_of_le_of_continuous_coeff
      p hp0degree hp0ne hdegree_le hcoeff
  filter_upwards [hlower, hdegree] with b hb hdeg
  intro hsplit
  simpa [p] using
    hbridge (p b) hp0split hsplit (by rw [hdeg, hp0degree]) (hb hsplit)

/-- Reciprocal rescaling of the quadratic pencil. -/
theorem C_sq_mul_quadraticInterlacingPencil_inv
    (F G H : ℝ[X]) {b : ℝ} (hb : b ≠ 0) :
    C (b ^ 2) * quadraticInterlacingPencil F G H b⁻¹ =
      quadraticInterlacingPencil H G F b := by
  simp only [quadraticInterlacingPencil, mul_add, map_mul, map_pow]
  have hlinear : C b ^ 2 * (C 2 * C b⁻¹) = C 2 * C b := by
    simp only [← map_mul, ← map_pow]
    congr 1
    field_simp
  have hquadratic : C b ^ 2 * C b⁻¹ ^ 2 = (1 : ℝ[X]) := by
    simp only [← map_mul, ← map_pow]
    rw [show b ^ 2 * b⁻¹ ^ 2 = 1 by field_simp, map_one]
  calc
    C b ^ 2 * H + C b ^ 2 * (C 2 * C b⁻¹ * G) +
        C b ^ 2 * (C b⁻¹ ^ 2 * F) =
      C b ^ 2 * H + (C b ^ 2 * (C 2 * C b⁻¹)) * G +
        (C b ^ 2 * C b⁻¹ ^ 2) * F := by ring
    _ = F + C 2 * C b * G + C b ^ 2 * H := by rw [hlinear, hquadratic]; ring

/-- Splitting of the forward quadratic pencil implies splitting of its
reciprocal pencil on nonnegative parameters. -/
theorem splits_reciprocalQuadraticInterlacingPencil
    {F G H : ℝ[X]} (hFsplit : F.Splits)
    (hsplits : ∀ a : ℝ, 0 ≤ a →
      (quadraticInterlacingPencil F G H a).Splits) :
    ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil H G F b).Splits := by
  intro b hb
  rcases hb.eq_or_lt with rfl | hbpos
  · simpa [quadraticInterlacingPencil] using hFsplit
  · have hscaled := (hsplits b⁻¹ (inv_nonneg.mpr hbpos.le)).C_mul (b ^ 2)
    rwa [C_sq_mul_quadraticInterlacingPencil_inv F G H hbpos.ne'] at hscaled

/-- Reciprocal rescaling does not change the root multiset. -/
theorem roots_quadraticInterlacingPencil_reciprocal
    (F G H : ℝ[X]) {b : ℝ} (hb : b ≠ 0) :
    (quadraticInterlacingPencil H G F b).roots =
      (quadraticInterlacingPencil F G H b⁻¹).roots := by
  rw [← C_sq_mul_quadraticInterlacingPencil_inv F G H hb,
    roots_C_mul _ (pow_ne_zero 2 hb)]

/-- Reciprocal-parameter form of the `a → ∞` endpoint count.

If the reciprocal pencil remains split, has nonzero constant coefficient, and
has strictly negative roots for nonnegative reciprocal parameters, then its
strict-upper root count at a generic negative level agrees with that of `F`
for all sufficiently small positive reciprocal parameters. -/
theorem eventually_reciprocalQuadraticInterlacingPencil_card_roots_gt_eq
    {F G H : ℝ[X]} {D : ℕ}
    (hF : F.natDegree ≤ D) (hG : G.natDegree ≤ D)
    (hH : H.natDegree ≤ D)
    (hsplits : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil H G F b).Splits)
    (hcoeff0 : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil H G F b).coeff 0 ≠ 0)
    (hneg : ∀ b : ℝ, 0 ≤ b → ∀ q ∈
      (quadraticInterlacingPencil H G F b).roots, q < 0)
    {r : ℝ} (hr : r < 0) (hrF : ¬F.IsRoot r) :
    ∀ᶠ b in 𝓝 0, 0 < b →
      ((quadraticInterlacingPencil H G F b).roots.filter (r < ·)).card =
        (F.roots.filter (r < ·)).card := by
  have hFsplit : F.Splits := by
    simpa [quadraticInterlacingPencil] using hsplits 0 le_rfl
  have hF0 : F.coeff 0 ≠ 0 := by
    simpa [quadraticInterlacingPencil] using hcoeff0 0 le_rfl
  have hFneg : ∀ q ∈ F.roots, q < 0 := by
    simpa [quadraticInterlacingPencil] using hneg 0 le_rfl
  have hs : r⁻¹ ∉ (reflect D F).roots := by
    intro hmem
    apply hrF
    exact (DegreeDropReversal.isRoot_reflect_inv_iff (ne_of_lt hr) hF).1
      (Polynomial.isRoot_of_mem_roots hmem)
  have hreflect :=
    eventually_compactifiedQuadraticInterlacingPencil_card_roots_gt_eq
      hF hG hH hF0 hFsplit hs
  have heval_cont : Continuous fun b =>
      (quadraticInterlacingPencil H G F b).eval r := by
    simp only [quadraticInterlacingPencil, eval_add, eval_mul, eval_C]
    fun_prop
  have hFeval : F.eval r ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero F r).mp hrF
  have hbaseeval : (quadraticInterlacingPencil H G F 0).eval r ≠ 0 := by
    simpa [quadraticInterlacingPencil] using hFeval
  have hrootfree : ∀ᶠ b in 𝓝 0,
      ¬(quadraticInterlacingPencil H G F b).IsRoot r := by
    have hne := heval_cont.continuousAt.eventually_ne hbaseeval
    simpa [quadraticInterlacingPencil, Polynomial.IsRoot.def] using hne
  filter_upwards [hreflect, hrootfree] with b hbreflect hbroot
  intro hbpos
  have hbsplit := hsplits b hbpos.le
  have hb0 := hcoeff0 b hbpos.le
  have hbneg := hneg b hbpos.le
  have hbdegree := natDegree_quadraticInterlacingPencil_le hH hG hF b
  have hbcount := DegreeDropReversal.card_roots_filter_gt_eq_reflect_compl
    hbsplit hb0 hbdegree hr hbroot hbneg
  have hFcount := DegreeDropReversal.card_roots_filter_gt_eq_reflect_compl
    hFsplit hF0 hF hr hrF hFneg
  have hreflect_eq := hbreflect
    (Polynomial.Splits.reflect hbsplit hbdegree)
  change ((reflect D (quadraticInterlacingPencil H G F b)).roots.filter
      (r⁻¹ < ·)).card = ((reflect D F).roots.filter (r⁻¹ < ·)).card at hreflect_eq
  lia

/-- Original-parameter form of the root-count endpoint at `a → ∞`. -/
theorem eventually_quadraticInterlacingPencil_card_roots_gt_eq_atTop
    {F G H : ℝ[X]} {D : ℕ}
    (hF : F.natDegree ≤ D) (hG : G.natDegree ≤ D)
    (hH : H.natDegree ≤ D)
    (hsplits : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil H G F b).Splits)
    (hcoeff0 : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil H G F b).coeff 0 ≠ 0)
    (hneg : ∀ b : ℝ, 0 ≤ b → ∀ q ∈
      (quadraticInterlacingPencil H G F b).roots, q < 0)
    {r : ℝ} (hr : r < 0) (hrF : ¬F.IsRoot r) :
    ∀ᶠ a in Filter.atTop,
      ((quadraticInterlacingPencil F G H a).roots.filter (r < ·)).card =
        (F.roots.filter (r < ·)).card := by
  have hsmall :=
    eventually_reciprocalQuadraticInterlacingPencil_card_roots_gt_eq
      hF hG hH hsplits hcoeff0 hneg hr hrF
  have hsmall_atTop := tendsto_inv_atTop_zero.eventually hsmall
  filter_upwards [hsmall_atTop, Filter.eventually_gt_atTop (0 : ℝ)] with a ha hapos
  have hainvpos : 0 < a⁻¹ := inv_pos.mpr hapos
  have hcount := ha hainvpos
  have hroots := roots_quadraticInterlacingPencil_reciprocal
    F G H (inv_ne_zero (ne_of_gt hapos))
  rw [inv_inv] at hroots
  rwa [hroots] at hcount

/-- Every coefficient of the quadratic pencil depends smoothly on its real
parameter. -/
theorem contDiff_coeff_quadraticInterlacingPencil
    (F G H : ℝ[X]) (i : ℕ) :
    ContDiff ℝ ∞
      (fun a => (quadraticInterlacingPencil F G H a).coeff i) := by
  rw [show (fun a => (quadraticInterlacingPencil F G H a).coeff i) =
      fun a => H.coeff i + (2 * a) * G.coeff i + a ^ 2 * F.coeff i by
    funext a
    simp only [quadraticInterlacingPencil, coeff_add, coeff_C_mul]]
  fun_prop

/-- Evaluation of the quadratic pencil is jointly smooth in the parameter and
the polynomial variable. -/
theorem contDiff_quadraticInterlacingPencil_eval_prod
    (F G H : ℝ[X]) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (quadraticInterlacingPencil F G H z.1).eval z.2) := by
  rw [show (fun z : ℝ × ℝ =>
      (quadraticInterlacingPencil F G H z.1).eval z.2) =
      fun z => H.eval z.2 + (2 * z.1) * G.eval z.2 +
        z.1 ^ 2 * F.eval z.2 by
    funext z
    simp [quadraticInterlacingPencil]]
  exact (((Polynomial.contDiff_aeval H ∞).comp contDiff_snd).add
    ((contDiff_const.mul contDiff_fst).mul
      ((Polynomial.contDiff_aeval G ∞).comp contDiff_snd))).add
    ((contDiff_fst.pow 2).mul
      ((Polynomial.contDiff_aeval F ∞).comp contDiff_snd))

/-- A simple root of the quadratic pencil admits a local differentiable root
branch. Its velocity is the implicit quotient of the parameter tangent by the
spatial derivative. -/
theorem exists_hasDerivAt_quadraticInterlacingPencil_root
    {F G H : ℝ[X]} {a r : ℝ}
    (hr : (quadraticInterlacingPencil F G H a).IsRoot r)
    (hregular :
      (quadraticInterlacingPencil F G H a).derivative.eval r ≠ 0) :
    ∃ ρ : ℝ → ℝ,
      HasDerivAt ρ
        (-2 * (quadraticInterlacingTangent F G a).eval r /
          (quadraticInterlacingPencil F G H a).derivative.eval r) a ∧
        ρ a = r ∧
          ∀ᶠ b in 𝓝 a,
            (quadraticInterlacingPencil F G H b).IsRoot (ρ b) := by
  let p : ℝ → ℝ[X] := fun b => quadraticInterlacingPencil F G H b
  let Φ : ℝ × ℝ → ℝ := fun z => (p z.1).eval z.2
  have hcont : ContDiffAt ℝ ∞ Φ (a, r) :=
    (contDiff_quadraticInterlacingPencil_eval_prod F G H).contDiffAt
  let A : ℝ →L[ℝ] ℝ :=
    fderiv ℝ Φ (a, r) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  let B : ℝ →L[ℝ] ℝ :=
    fderiv ℝ Φ (a, r) ∘L ContinuousLinearMap.inl ℝ ℝ ℝ
  have hfull : HasFDerivAt Φ (fderiv ℝ Φ (a, r)) (a, r) :=
    (hcont.differentiableAt (by simp)).hasFDerivAt
  have hA : A = ContinuousLinearMap.toSpanSingleton ℝ
      ((p a).derivative.eval r) := by
    apply HasFDerivAt.unique
    · exact hfull.comp r (hasFDerivAt_prodMk_right a r)
    · exact (p a).hasFDerivAt r
  have hparam : HasDerivAt (fun b => (p b).eval r)
      (2 * (quadraticInterlacingTangent F G a).eval r) a := by
    simp only [p, quadraticInterlacingPencil, quadraticInterlacingTangent,
      eval_add, eval_mul, eval_C]
    convert (((hasDerivAt_const a (H.eval r)).add
      ((hasDerivAt_id a).const_mul (2 * G.eval r))).add
      ((hasDerivAt_pow 2 a).mul_const (F.eval r))) using 1
    · funext b
      dsimp
      ring
    · ring
  have hB : B = ContinuousLinearMap.toSpanSingleton ℝ
      (2 * (quadraticInterlacingTangent F G a).eval r) := by
    apply HasFDerivAt.unique
    · exact hfull.comp a (hasFDerivAt_prodMk_left a r)
    · exact hparam.hasFDerivAt
  have hAinv : A.IsInvertible := by
    rw [hA]
    exact ContinuousLinearMap.toSpanSingleton_isInvertible hregular
  let ρ : ℝ → ℝ := hcont.implicitFunction (by simp) hAinv
  have hρbase : ρ a = r :=
    hcont.implicitFunction_apply_self (by simp) hAinv
  have hρroot : ∀ᶠ b in 𝓝 a, (p b).IsRoot (ρ b) := by
    have heq := hcont.eventually_apply_implicitFunction (by simp) hAinv
    filter_upwards [heq] with b hb
    rw [Polynomial.IsRoot.def]
    change Φ (b, ρ b) = 0
    simpa only [Φ, Polynomial.IsRoot.def] using hb.trans (by simpa [p] using hr)
  have hρstrict := hcont.hasStrictFDerivAt_implicitFunction (by simp) hAinv
  have hρderiv : HasDerivAt ρ ((-(A.inverse ∘L B)) 1) a := by
    simpa only [ρ, A, B] using hρstrict.hasFDerivAt.hasDerivAt
  have hquotient : (-(A.inverse ∘L B)) 1 =
      -2 * (quadraticInterlacingTangent F G a).eval r /
        (quadraticInterlacingPencil F G H a).derivative.eval r := by
    rw [neg_apply, ContinuousLinearMap.comp_apply, hB,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, hA]
    rw [ContinuousLinearMap.inverse_toSpanSingleton_apply hregular]
    ring
  refine ⟨ρ, ?_, hρbase, ?_⟩
  · rwa [hquotient] at hρderiv
  · simpa only [p] using hρroot

/-- Local multiplicity preservation for a simple member of a quadratic
interlacing pencil. -/
theorem exists_eps_forall_quadraticInterlacingPencil_root_count_le_near
    {F G H : ℝ[X]} {a : ℝ} {D : ℕ} (hD : D ≠ 0)
    (hdegree : ∀ᶠ b in 𝓝 a,
      (quadraticInterlacingPencil F G H b).natDegree = D)
    (hsplits : (quadraticInterlacingPencil F G H a).Splits)
    (hsimple : HasSimpleRoots (quadraticInterlacingPencil F G H a))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε > 0, ∀ b : ℝ, |b - a| < ε →
      ∀ r ∈ (quadraticInterlacingPencil F G H a).roots.toFinset,
        (quadraticInterlacingPencil F G H a).roots.count r ≤
          ((quadraticInterlacingPencil F G H b).roots.filter
            (fun q => |q - r| < ρ)).card := by
  refine exists_eps_forall_root_count_le_card_filter_near_of_simple
    (fun b => quadraticInterlacingPencil F G H b) hD hdegree hsplits
      hsimple ?_ hρ
  intro x _
  exact (contDiff_quadraticInterlacingPencil_eval_prod F G H).contDiffAt.of_le
    (by norm_num)

/-- At a simple spatial crossing of the quadratic pencil, the nearby
strict-upper root count is the crossing count itself or one larger. -/
theorem exists_eventually_quadraticInterlacingPencil_root_count_bounds
    {F G H : ℝ[X]} {a r : ℝ} {D : ℕ} (hD : D ≠ 0)
    (hdegree : ∀ᶠ b in 𝓝 a,
      (quadraticInterlacingPencil F G H b).natDegree = D)
    (hsplits : (quadraticInterlacingPencil F G H a).Splits)
    (hsimple : HasSimpleRoots (quadraticInterlacingPencil F G H a))
    (hroot : (quadraticInterlacingPencil F G H a).IsRoot r) :
    ∀ᶠ b in 𝓝 a,
      ((quadraticInterlacingPencil F G H a).roots.filter (r < ·)).card ≤
          ((quadraticInterlacingPencil F G H b).roots.filter (r < ·)).card ∧
        ((quadraticInterlacingPencil F G H b).roots.filter (r < ·)).card ≤
          ((quadraticInterlacingPencil F G H a).roots.filter
            (r < ·)).card + 1 := by
  refine exists_eventually_card_roots_gt_bounds_near_simple_root
    (fun b => quadraticInterlacingPencil F G H b) hD hdegree hsplits
      hsimple ?_ hroot
  intro x _
  exact (contDiff_quadraticInterlacingPencil_eval_prod F G H).contDiffAt.of_le
    (by norm_num)

/-- Iterated derivative shifts commute with the quadratic pencil. -/
theorem iterateTDeriv_quadraticInterlacingPencil
    (eps : ℝ) (k : ℕ) (F G H : ℝ[X]) (a : ℝ) :
    iterateTDeriv eps k (quadraticInterlacingPencil F G H a) =
      quadraticInterlacingPencil (iterateTDeriv eps k F)
        (iterateTDeriv eps k G) (iterateTDeriv eps k H) a := by
  unfold quadraticInterlacingPencil
  rw [iterateTDeriv_add, iterateTDeriv_add, iterateTDeriv_C_mul,
    iterateTDeriv_C_mul]

/-- Iterated derivative shifts commute with the parameter tangent. -/
theorem iterateTDeriv_quadraticInterlacingTangent
    (eps : ℝ) (k : ℕ) (F G : ℝ[X]) (a : ℝ) :
    iterateTDeriv eps k (quadraticInterlacingTangent F G a) =
      quadraticInterlacingTangent (iterateTDeriv eps k F)
        (iterateTDeriv eps k G) a := by
  simp [quadraticInterlacingTangent, iterateTDeriv_add,
    iterateTDeriv_C_mul]

/-- Iterated derivative shifts commute with the right member of the
quadratic closure pair. -/
theorem iterateTDeriv_quadraticInterlacingRight
    (eps : ℝ) (k : ℕ) (G H : ℝ[X]) (a : ℝ) :
    iterateTDeriv eps k (quadraticInterlacingRight G H a) =
      quadraticInterlacingRight (iterateTDeriv eps k G)
        (iterateTDeriv eps k H) a := by
  simp [quadraticInterlacingRight, iterateTDeriv_add,
    iterateTDeriv_C_mul]

/-- A quadratic closure proof for every positive derivative regularization
descends to the original pair. This is the fixed-triple interface used to
reduce the general quadratic lemma to its simple-root case. -/
theorem strictInterl_quadraticInterlacingRight_of_regularized
    {F G H : ℝ[X]} {a : ℝ} {k : ℕ}
    (hTangent_nonneg :
      HasNonnegCoeffs (quadraticInterlacingTangent F G a))
    (hRight_nonneg : HasNonnegCoeffs (quadraticInterlacingRight G H a))
    (hTangent_ne : quadraticInterlacingTangent F G a ≠ 0)
    (hRight_ne : quadraticInterlacingRight G H a ≠ 0)
    (hreg : ∀ eps : ℝ, 0 < eps →
      StrictInterl
        (quadraticInterlacingTangent (iterateTDeriv (-eps) k F)
          (iterateTDeriv (-eps) k G) a)
        (quadraticInterlacingRight (iterateTDeriv (-eps) k G)
          (iterateTDeriv (-eps) k H) a)) :
    StrictInterl (quadraticInterlacingTangent F G a)
      (quadraticInterlacingRight G H a) := by
  apply strictInterl_of_iterateTDeriv_neg hTangent_nonneg hRight_nonneg
    hTangent_ne hRight_ne k
  intro eps heps
  rw [iterateTDeriv_quadraticInterlacingTangent,
    iterateTDeriv_quadraticInterlacingRight]
  exact hreg eps heps

/-- A common negative derivative shift makes every member of a split
quadratic pencil simple once the iteration count dominates its degree. -/
theorem hasSimpleRoots_regularized_quadraticInterlacingPencil
    {F G H : ℝ[X]} {eps : ℝ} {k : ℕ} (heps : 0 < eps)
    (hne : ∀ b : ℝ, 0 ≤ b → quadraticInterlacingPencil F G H b ≠ 0)
    (hsplits : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).Splits)
    (hdeg : ∀ b : ℝ, 0 ≤ b →
      (quadraticInterlacingPencil F G H b).natDegree ≤ k)
    {b : ℝ} (hb : 0 ≤ b) :
    HasSimpleRoots
      (quadraticInterlacingPencil (iterateTDeriv (-eps) k F)
        (iterateTDeriv (-eps) k G) (iterateTDeriv (-eps) k H) b) := by
  rw [← iterateTDeriv_quadraticInterlacingPencil]
  exact hasSimpleRoots_iterateTDeriv_neg_of_natDegree_le heps
    (hne b hb) (hsplits b hb) (hdeg b hb)

end RealRooted
