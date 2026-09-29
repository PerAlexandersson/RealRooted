import RealRooted.HermiteBiehler.OrientedPencil
import RealRooted.CriticalValueContinuation
import RealRooted.DegreeDropReversal
import RealRooted.Interlacing.Residue
import RealRooted.IteratedDerivativeShift
import RealRooted.LiuOppositeSigns.JensenRootCount
import RealRooted.PFPolynomial.Closure
import RealRooted.RootCountLocalConstancy
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

/-- If the leading spatial polynomial does not vanish at `r`, the parameter
evaluation is a genuine quadratic. -/
theorem quadraticParameterEvaluation_natDegree
    {F G H : ℝ[X]} {r : ℝ} (hrF : ¬F.IsRoot r) :
    (quadraticParameterEvaluation F G H r).natDegree = 2 := by
  have hF : F.eval r ≠ 0 := (Polynomial.not_isRoot_iff_eval_ne_zero F r).mp hrF
  rw [quadraticParameterEvaluation]
  compute_degree <;> simp_all

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

/-! ## Logarithmic-ratio endpoint -/

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
