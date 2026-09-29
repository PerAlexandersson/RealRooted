import RealRooted.HermiteBiehler.OrientedPencil
import RealRooted.Interlacing.Residue
import RealRooted.IteratedDerivativeShift
import RealRooted.LiuOppositeSigns.JensenRootCount
import RealRooted.PFPolynomial.Closure
import RealRooted.RootCounting.Descartes
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

end RealRooted
