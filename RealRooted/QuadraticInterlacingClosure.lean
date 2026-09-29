import RealRooted.HermiteBiehler.OrientedPencil
import RealRooted.CriticalValueContinuation
import RealRooted.DegreeDropReversal
import RealRooted.Interlacing.Residue
import RealRooted.IteratedDerivativeShift
import RealRooted.LiuOppositeSigns.JensenRootCount
import RealRooted.Mathlib.Data.List.Zip
import RealRooted.PFPolynomial.Closure
import RealRooted.RootCountLocalConstancy
import RealRooted.RootCounting.CrossingExhaustion
import RealRooted.RootCounting.Descartes
import RealRooted.SameDegreeMultiplicityLowerCount
import RealRooted.Wronskian.WeakForward

/-!
# Quadratic interlacing closure

This file isolates the algebraic end of the quadratic-parameter closure
argument used by interlacing-preserving linear maps.  For

`Q a = H + 2 a G + a ^ 2 F`,

the parameter tangent is `A a = G + a F`, while
`B a = H + a G` satisfies `Q a = B a + a A a`.

Consequently, once the analytic root-motion argument proves
`A a ≪ Q a`, the desired relation `A a ≪ B a` follows without further
root analysis: the two pairs span the same real pencil and have the same
oriented Wronskian.
-/

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
theorem StrictInterl.TDeriv_common {f g : ℝ[X]} (hfg : StrictInterl f g)
    (eps : ℝ) : StrictInterl (TDeriv eps f) (TDeriv eps g) := by
  have hall : AllComboRealRooted f g := allComboRealRooted_of_strictInterl hfg
  have hallT : AllComboRealRooted (TDeriv eps f) (TDeriv eps g) := by
    simpa [iterateTDeriv_succ] using
      allComboRealRooted_iterateTDeriv_all hall eps 1
  rcases hfg.natDegree_eq_or_eq_succ with hsame | hsucc
  · have horient :
        StrictInterl (TDeriv eps f) (TDeriv eps g) ∨
          StrictInterl (TDeriv eps g) (TDeriv eps f) :=
      strictInterl_of_allComboRealRooted
        (TDeriv_ne_zero hfg.1.1) (splits_tderiv_all hfg.1.2)
        (TDeriv_ne_zero hfg.2.1.1) (splits_tderiv_all hfg.2.1.2)
        hallT (Or.inr (by simpa using hsame.symm))
    rcases horient with hforward | hreverse
    · exact hforward
    · apply hreverse.of_reverse_of_roots_sum_le
      · simpa using hsame.symm
      · rw [roots_sum_TDeriv eps hfg.1.1 hfg.1.2,
          roots_sum_TDeriv eps hfg.2.1.1 hfg.2.1.2]
        simpa [hsame] using
          add_le_add_right (hfg.roots_sum_le_of_sameDegree hsame.symm)
            (eps * (f.natDegree : ℝ))
  · apply StrictInterl.forward_of_orientation_of_succDegree (by simpa using hsucc)
    exact strictInterl_of_allComboRealRooted
      (TDeriv_ne_zero hfg.1.1) (splits_tderiv_all hfg.1.2)
      (TDeriv_ne_zero hfg.2.1.1) (splits_tderiv_all hfg.2.1.2)
      hallT (Or.inl (by simpa using hsucc.symm))

/-- Common iterated derivative shifts preserve oriented interlacing. -/
theorem StrictInterl.iterateTDeriv_common {f g : ℝ[X]}
    (hfg : StrictInterl f g) (eps : ℝ) :
    ∀ k : ℕ, StrictInterl (iterateTDeriv eps k f) (iterateTDeriv eps k g)
  | 0 => by simpa
  | k + 1 => by
      rw [iterateTDeriv_succ, iterateTDeriv_succ]
      exact (hfg.iterateTDeriv_common eps k).TDeriv_common eps

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
  have hinterl (M : ℕ) : Interl (fM M) (gM M) := by
    exact (hreg (delta M) (hdelta_pos M)).toInterl
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
    exact DegreeDropReversal.splits_reflect_of_splits hFsplit hF
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
  have hlinear : C (b ^ 2) * C (b⁻¹ * 2) = C (b * 2) := by
    calc
      C (b ^ 2) * C (b⁻¹ * 2) = C (b ^ 2 * (b⁻¹ * 2)) := C_mul.symm
      _ = C (b * 2) := by
        congr 1
        field_simp [hb]
  have hquadratic : C (b ^ 2) * C (b⁻¹ ^ 2) = (1 : ℝ[X]) := by
    calc
      C (b ^ 2) * C (b⁻¹ ^ 2) = C (b ^ 2 * b⁻¹ ^ 2) := C_mul.symm
      _ = C 1 := by
        congr 1
        field_simp [hb]
      _ = 1 := map_one C
  have hlinear' : C b ^ 2 * (C 2 * C b⁻¹) = C 2 * C b := by
    calc
      C b ^ 2 * (C 2 * C b⁻¹) =
          C (b ^ 2) * C (b⁻¹ * 2) := by
        simp only [map_mul, map_pow]
        ring
      _ = C (b * 2) := hlinear
      _ = C 2 * C b := by
        simp only [map_mul]
        ring
  have hquadratic' : C b ^ 2 * C b⁻¹ ^ 2 = (1 : ℝ[X]) := by
    simpa only [map_pow] using hquadratic
  calc
    C b ^ 2 * H + C b ^ 2 * (C 2 * C b⁻¹ * G) +
        C b ^ 2 * (C b⁻¹ ^ 2 * F) =
      C b ^ 2 * H + (C b ^ 2 * (C 2 * C b⁻¹)) * G +
        (C b ^ 2 * C b⁻¹ ^ 2) * F := by ring
    _ = F + C 2 * C b * G + C b ^ 2 * H := by
      rw [hlinear', hquadratic']
      ring

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
    (DegreeDropReversal.splits_reflect_of_splits hbsplit hbdegree)
  change ((reflect D (quadraticInterlacingPencil H G F b)).roots.filter
      (r⁻¹ < ·)).card = ((reflect D F).roots.filter (r⁻¹ < ·)).card at hreflect_eq
  omega

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

private theorem quadratic_toSpanSingleton_isInvertible {c : ℝ} (hc : c ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℝ c).IsInvertible := by
  let e : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  refine ⟨e, ?_⟩
  ext
  simp [e, ContinuousLinearMap.toSpanSingleton_apply, mul_comm]

private theorem quadratic_inverse_toSpanSingleton_apply
    {c y : ℝ} (hc : c ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℝ c).inverse y = y / c := by
  have hinv := quadratic_toSpanSingleton_isInvertible hc
  have h := hinv.self_apply_inverse y
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
  exact (eq_div_iff hc).2 h

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
  have hcont : ContDiffAt ℝ ∞ Φ (a, r) := by
    exact (contDiff_quadraticInterlacingPencil_eval_prod F G H).contDiffAt
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
    exact quadratic_toSpanSingleton_isInvertible hregular
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
    rw [quadratic_inverse_toSpanSingleton_apply hregular]
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
  have haIcc : a ∈ Set.Icc μL μR := ⟨hμLa.le, haμR.le⟩
  have hlocal := exists_eventually_quadraticInterlacingPencil_root_count_bounds
    hD (hdegree_local a haIcc) (hsplits a haIcc) (hsimple a haIcc) hroot
  have hleftEvent : ∀ᶠ b in 𝓝 a,
      (((quadraticInterlacingPencil F G H a).roots.filter (r < ·)).card ≤
          ((quadraticInterlacingPencil F G H b).roots.filter (r < ·)).card ∧
        ((quadraticInterlacingPencil F G H b).roots.filter (r < ·)).card ≤
          ((quadraticInterlacingPencil F G H a).roots.filter (r < ·)).card + 1) ∧
        μL < b :=
    hlocal.and (eventually_gt_nhds hμLa)
  obtain ⟨bL, hbLa, hbLbound, hμLbL⟩ := hleftEvent.exists_lt
  have hrightEvent : ∀ᶠ b in 𝓝 a,
      (((quadraticInterlacingPencil F G H a).roots.filter (r < ·)).card ≤
          ((quadraticInterlacingPencil F G H b).roots.filter (r < ·)).card ∧
        ((quadraticInterlacingPencil F G H b).roots.filter (r < ·)).card ≤
          ((quadraticInterlacingPencil F G H a).roots.filter (r < ·)).card + 1) ∧
        b < μR :=
    hlocal.and (eventually_lt_nhds haμR)
  obtain ⟨bR, habR, hbRbound, hbRμR⟩ := hrightEvent.exists_gt
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
  omega

/-- If the leading spatial polynomial does not vanish at `r`, the parameter
evaluation is a genuine quadratic. -/
theorem quadraticParameterEvaluation_natDegree
    {F G H : ℝ[X]} {r : ℝ} (hrF : ¬F.IsRoot r) :
    (quadraticParameterEvaluation F G H r).natDegree = 2 := by
  have hF : F.eval r ≠ 0 := (Polynomial.not_isRoot_iff_eval_ne_zero F r).mp hrF
  rw [quadraticParameterEvaluation]
  compute_degree <;> simp_all

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
  have hqne : q ≠ 0 := by
    intro hzero
    rw [hzero] at hqdeg
    simp at hqdeg
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
  have hqne : q ≠ 0 := by
    intro hzero
    rw [hzero] at hqdeg
    simp at hqdeg
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
  have hqne : q ≠ 0 := by
    intro hzero
    rw [hzero] at hqdeg
    simp at hqdeg
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
  have hqne : q ≠ 0 := by
    intro hzero
    rw [hzero] at hqdeg
    simp at hqdeg
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
theorem positiveRootCount_quadraticParameterEvaluation_le_rootCountDrop
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
    rcases eq_or_lt_of_le hle with h | h
    · exact Or.inl h.symm
    · right
      lia
  have hnGH : nH = nG ∨ nH = nG + 1 := by
    have hle : nG ≤ nH := by
      exact_mod_cast hGHcount.1
    have hle' : nH ≤ nG + 1 := by
      exact_mod_cast hGHcount.2
    rcases eq_or_lt_of_le hle with h | h
    · exact Or.inl h.symm
    · right
      lia
  have hpdeg : p.natDegree = 2 := by
    exact quadraticParameterEvaluation_natDegree hrF
  have hFne : F.eval r ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero F r).mp hrF
  have hpne : p ≠ 0 := by
    intro hpzero
    have hcoeff := congrArg (fun q : ℝ[X] => q.coeff 2) hpzero
    simp [p, quadraticParameterEvaluation, hFne] at hcoeff
  have hHne : H.eval r ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero H r).mp hrH
  have hpositiveRootsLeOne (hHe : H.eval r * e < 0) :
      p.positiveRootCount ≤ 1 := by
    have hFHneg : F.eval r * H.eval r < 0 := by
      have heSq : e * e = 1 := by
        dsimp only [e]
        rw [← pow_add]
        simp
      have hprod := mul_neg_of_pos_of_neg hFe hHe
      nlinarith
    have hsign : sign (F.eval r) ≠ sign (H.eval r) := by
      rcases lt_or_gt_of_ne hFne with hFneg | hFpos'
      · have hHpos' : 0 < H.eval r := by nlinarith
        simp [sign_neg hFneg, sign_pos hHpos']
      · have hHneg : H.eval r < 0 := by nlinarith
        simp [sign_pos hFpos', sign_neg hHneg]
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
  · have hHe : H.eval r * e < 0 := by
      rw [hHG, hGF, pow_succ] at hHeRaw
      dsimp only [e]
      nlinarith
    have hdrop : nH - nF = 1 := by simp [hGF, hHG]
    rw [hdrop]
    exact hpositiveRootsLeOne hHe
  · have hHe : H.eval r * e < 0 := by
      rw [hHG, hGF, pow_succ] at hHeRaw
      dsimp only [e]
      nlinarith
    have hdrop : nH - nF = 1 := by simp [hGF, hHG]
    rw [hdrop]
    exact hpositiveRootsLeOne hHe
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
    rw [hrs]
    simp
  have hapos : 0 < a :=
    (mem_positiveQuadraticParameterRoots_iff.mp hamem).2
  have haq : a ∈ q.roots :=
    (mem_positiveQuadraticParameterRoots_iff.mp hamem).1
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
  have hbudget0 := positiveRootCount_quadraticParameterEvaluation_le_rootCountDrop
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
    omega
  rw [hmult_eq_drop]
  constructor <;> omega

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
  have hamem : a ∈ positiveQuadraticParameterRoots F G H r := by
    rw [hrs]
    simp
  have hbmem : b ∈ positiveQuadraticParameterRoots F G H r := by
    rw [hrs]
    simp
  have hapos : 0 < a :=
    (mem_positiveQuadraticParameterRoots_iff.mp hamem).2
  have hbpos : 0 < b :=
    (mem_positiveQuadraticParameterRoots_iff.mp hbmem).2
  have hab : a < b := by
    have hpair := positiveQuadraticParameterRoots_pairwise F G H r
    rw [hrs] at hpair
    simpa using hpair
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  have hmR : m < R := hmb.trans hbR
  have hm0 : (0 : ℝ) ≤ m := hapos.le.trans ham.le
  have haRoot : q.IsRoot a :=
    Polynomial.isRoot_of_mem_roots
      (mem_positiveQuadraticParameterRoots_iff.mp hamem).1
  have hbRoot : q.IsRoot b :=
    Polynomial.isRoot_of_mem_roots
      (mem_positiveQuadraticParameterRoots_iff.mp hbmem).1
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
  have hmultA : 1 ≤ q.roots.count a :=
    Multiset.one_le_count_iff_mem.mpr
      (mem_positiveQuadraticParameterRoots_iff.mp hamem).1
  have hmultB : 1 ≤ q.roots.count b :=
    Multiset.one_le_count_iff_mem.mpr
      (mem_positiveQuadraticParameterRoots_iff.mp hbmem).1
  have hsum :=
    sum_count_positiveQuadraticParameterRoots_eq_positiveRootCount F G H r
  rw [hrs] at hsum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at hsum
  have hbudget0 := positiveRootCount_quadraticParameterEvaluation_le_rootCountDrop
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
    omega
  constructor
  · omega
  · constructor
    · omega
    · constructor <;> omega

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
  have hqne : q ≠ 0 := by
    intro hzero
    rw [hzero] at hqdeg
    simp at hqdeg
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
  have hfne : f ≠ 0 := by
    intro hzero
    subst f
    simp at hfdeg
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
  · have heq : g.natDegree = f.natDegree := by omega
    set c₀ := g.leadingCoeff / f.leadingCoeff with hc₀
    set g' := g - C c₀ * f with hg'
    have hg'deg : g'.degree < f.natDegree :=
      degree_sub_c₀_mul_lt hfne hgne heq hfpos
    have hg'eval : ∀ s ∈ f.roots, g'.eval s = g.eval s := by
      intro s hs
      have hsroot : f.IsRoot s := Polynomial.isRoot_of_mem_roots hs
      simp [hg', Polynomial.IsRoot.def.mp hsroot]
    have hfz : (complexify f).eval z ≠ 0 :=
      eval_complexify_ne_zero_of_splits_of_im_pos hfs hfne hz
    have hproper : (complexify g').eval z / (complexify f).eval z =
        (f.roots.map fun s =>
          ((g.eval s / f.derivative.eval s : ℝ) : ℂ) / (z - (s : ℂ))).sum := by
      rw [complexify_ratio_eq_partialfraction hfs hfnd hfdeg hg'deg hz]
      congr 1
      apply Multiset.map_congr rfl
      simp_all
    have hsplit : (complexify g).eval z =
        (complexify g').eval z + (c₀ : ℂ) * (complexify f).eval z := by
      rw [hg']
      unfold complexify
      simp
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
    wronskian_add_right, wronskian_C_mul_right,
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
  have hcomb := h (alpha - a * beta) beta
  rw [quadraticInterlacingRight_eq_pencil_sub_tangent]
  rw [← show
    C (alpha - a * beta) * quadraticInterlacingTangent F G a +
        C beta * quadraticInterlacingPencil F G H a =
      C alpha * quadraticInterlacingTangent F G a +
        C beta * (quadraticInterlacingPencil F G H a -
          C a * quadraticInterlacingTangent F G a) by
    simp only [map_sub, map_mul]
    ring]
  exact hcomb

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
  have hallAQ : AllComboRealRooted
      (quadraticInterlacingTangent F G a)
      (quadraticInterlacingPencil F G H a) :=
    allComboRealRooted_of_strictInterl hAQ
  have hallAB : AllComboRealRooted
      (quadraticInterlacingTangent F G a)
      (quadraticInterlacingRight G H a) :=
    allComboRealRooted_quadraticInterlacingTangent_right hallAQ
  have hWQ : ∀ x : ℝ, 0 ≤
      (wronskian (quadraticInterlacingTangent F G a)
        (quadraticInterlacingPencil F G H a)).eval x :=
    wronskian_eval_nonneg_of_strictInterl hQpos hApos hAQ
  have hWB : ∀ x : ℝ, 0 ≤
      (wronskian (quadraticInterlacingTangent F G a)
        (quadraticInterlacingRight G H a)).eval x := by
    intro x
    rw [← wronskian_quadraticInterlacingTangent_pencil]
    exact hWQ x
  exact strictInterl_of_allComboRealRooted_of_wronskian_nonneg
    hBpos hApos (allComboRealRooted_comm hallAB) hWB

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
