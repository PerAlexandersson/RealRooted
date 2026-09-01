/-
# Affine-family Wronskian bridge

The local Wronskian obstruction, root picker, and all-combinations bridge used
by the affine-family high-degree endgame.
-/
import RealRooted.ProductFamily
import RealRooted.AffineDerivative
import RealRooted.AffineFamily.Basic
import RealRooted.AffineFamily.PositiveFamily
import RealRooted.AffineFamily.Boundary
import RealRooted.AffineFamily.RootCrossing
import RealRooted.PosCombo
import RealRooted.SuccDegreeLeftEndpoint
import RealRooted.ObreschkoffConverse
import RealRooted.FolkloreLemma
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

open Polynomial

noncomputable section

namespace RealRooted

/-- In a one-parameter boundary family `g + t f`, a Wronskian-zero point where
`g` and `f` have opposite signs would force an interior double root. Hence the
Wronskian cannot vanish on the positive-level set of the ratio `-g / f`. -/
private lemma wronskian_eval_ne_zero_of_add_left_family_of_no_common
    {f g : ℝ[X]}
    (hfamily : ∀ {t : ℝ}, 0 < t → ((C t * f + g) ≠ 0 ∧ (C t * f + g).Splits))
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    {x : ℝ}
    (hopp : g.eval x * f.eval x < 0) :
    f.derivative.eval x * g.eval x - f.eval x * g.derivative.eval x ≠ 0 := by
  have hf_eval_ne : f.eval x ≠ 0 :=
    fun hfx => by simp_all
  have hg_eval_ne : g.eval x ≠ 0 :=
    fun hgx => by simp_all
  let t : ℝ := -(g.eval x / f.eval x)
  have ht_pos : 0 < t := by
    have hnum_pos : 0 < -(g.eval x * f.eval x) := by linarith
    have hmul_pos : 0 < t * (f.eval x) ^ 2 := by grind
    have hsq_nonneg : 0 ≤ (f.eval x) ^ 2 := sq_nonneg _
    nlinarith
  have hcombo : PosComboRealRooted g f := by
    rw [PosComboRealRooted.iff_add_right]
    grind
  have hsimple : HasSimpleRoots (g + C t * f) :=
    PosComboRealRooted.hasSimpleRoots_add_right
      hcombo hno ht_pos
  have hp_rr : ((g + C t * f) ≠ 0 ∧ (g + C t * f).Splits) := by grind
  have hp_root : (g + C t * f).IsRoot x := by
    rw [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C]
    grind
  intro hW
  have hp_der_root : (g + C t * f).derivative.IsRoot x := by
    rw [Polynomial.IsRoot.def, derivative_add, derivative_C_mul,
      eval_add, eval_mul, eval_C]
    grind
  have hp_ne : g + C t * f ≠ 0 := hp_rr.1
  have hmult :
      1 < (g + C t * f).rootMultiplicity x :=
    (one_lt_rootMultiplicity_iff_isRoot hp_ne).2 ⟨hp_root, hp_der_root⟩
  rw [hsimple x hp_root] at hmult
  lia

/-- Derivative of the boundary ratio `x ↦ -g(x) / f(x)` at a point where
`f(x) ≠ 0`, rewritten in the Wronskian form natural for the affine-family
arguments. -/
private lemma hasDerivAt_neg_eval_div_eval
    {f g : ℝ[X]} {x : ℝ}
    (hf_eval_ne : f.eval x ≠ 0) :
    HasDerivAt (fun y : ℝ => -(g.eval y / f.eval y))
      ((f.derivative.eval x * g.eval x - f.eval x * g.derivative.eval x) / (f.eval x) ^ 2) x := by
  have hg' : HasDerivAt (fun y : ℝ => g.eval y) (g.derivative.eval x) x := by
    simpa using (g.differentiable.differentiableAt.hasDerivAt)
  have hf' : HasDerivAt (fun y : ℝ => f.eval y) (f.derivative.eval x) x := by
    simpa using (f.differentiable.differentiableAt.hasDerivAt)
  have hdiv : HasDerivAt (fun y : ℝ => g.eval y / f.eval y)
      ((g.derivative.eval x * f.eval x - g.eval x * f.derivative.eval x) / (f.eval x) ^ 2) x :=
    hg'.div hf' hf_eval_ne
  have hcoef :
      (f.derivative.eval x * g.eval x - f.eval x * g.derivative.eval x) / (f.eval x) ^ 2 =
        -((g.derivative.eval x * f.eval x - g.eval x * f.derivative.eval x) /
          (f.eval x) ^ 2) := by
    ring_nf
  rw [hcoef]
  exact hdiv.neg

/-- Any local extremum of the positive-level ratio `x ↦ -g(x) / f(x)` forces the
Wronskian numerator to vanish. This is the analytic form of the usual "critical
point of the ratio" obstruction. -/
private lemma wronskian_eq_zero_of_localExtr_neg_eval_div_eval
    {f g : ℝ[X]} {x : ℝ}
    (hlocal : IsLocalExtr (fun y : ℝ => -(g.eval y / f.eval y)) x)
    (hf_eval_ne : f.eval x ≠ 0) :
    f.derivative.eval x * g.eval x - f.eval x * g.derivative.eval x = 0 := by
  have hderiv := hasDerivAt_neg_eval_div_eval (f := f) (g := g) hf_eval_ne
  have hzero := hlocal.hasDerivAt_eq_zero hderiv
  simp_all

/-- In a one-parameter affine boundary family, the positive ratio
`x ↦ -g(x) / f(x)` cannot have an interior local extremum: that would force a
Wronskian zero at a point where `g(x)` and `f(x)` already have opposite signs,
contradicting `wronskian_eval_ne_zero_of_add_left_family_of_no_common`. -/
private lemma false_of_localExtr_neg_eval_div_eval_pos_of_add_left_family_of_no_common
    {f g : ℝ[X]}
    (hfamily : ∀ {t : ℝ}, 0 < t → ((C t * f + g) ≠ 0 ∧ (C t * f + g).Splits))
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    {x : ℝ}
    (hlocal : IsLocalExtr (fun y : ℝ => -(g.eval y / f.eval y)) x)
    (hpos : 0 < -(g.eval x / f.eval x)) :
    False := by
  have hf_eval_ne : f.eval x ≠ 0 := by grind
  have hopp : g.eval x * f.eval x < 0 := by
    have hsq_pos : 0 < (f.eval x) ^ 2 := sq_pos_of_ne_zero hf_eval_ne
    have hcalc :
        (-(g.eval x / f.eval x)) * (f.eval x) ^ 2 = -(g.eval x * f.eval x) := by
      grind
    have hnum_pos : 0 < -(g.eval x * f.eval x) := by simpa [hcalc] using mul_pos hpos hsq_pos
    nlinarith
  have hW_zero : f.derivative.eval x * g.eval x - f.eval x * g.derivative.eval x = 0 :=
    wronskian_eq_zero_of_localExtr_neg_eval_div_eval (f := f) (g := g) hlocal hf_eval_ne
  exact (wronskian_eval_ne_zero_of_add_left_family_of_no_common hfamily hno hopp) hW_zero
private lemma consecNoRoots_tail {p : ℝ[X]} {a : ℝ} {l : List ℝ} :
    ConsecNoRoots p (a :: l) → ConsecNoRoots p l := by
  cases l with
  | nil =>
      intro _
      trivial
  | cons b rest =>
      exact fun h => h.2

private lemma consecNoRoots_suffix {p : ℝ[X]} :
    ∀ pre suf : List ℝ, ConsecNoRoots p (pre ++ suf) → ConsecNoRoots p suf
  | [], suf, h => by grind
  | _ :: pre, suf, h => by
      simpa [List.cons_append] using
        consecNoRoots_suffix pre suf (consecNoRoots_tail h)

private lemma pos_neg_div_of_mul_neg {a b : ℝ}
    (hb : b ≠ 0) (hab : a * b < 0) :
    0 < -(a / b) := by
  have hsq_pos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hcalc : (-(a / b)) * b ^ 2 = -(a * b) := by grind
  have hnum_pos : 0 < -(a * b) := by nlinarith
  have hmul_pos : 0 < (-(a / b)) * b ^ 2 := by lia
  nlinarith

/-- Recursive root-picker: if a polynomial `F` has a root strictly between each
consecutive pair of a sorted real list `rs`, we can package these roots as a
strictly sorted interlacing list. -/
private theorem exists_roots_strictly_interlacing_of_consecutive_exists {F : ℝ[X]} :
    ∀ (rs : List ℝ),
      rs.Pairwise (· ≤ ·) →
      (∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        ∃ u, r₁ < u ∧ u < r₂ ∧ F.IsRoot u) →
      ∃ us : List ℝ, us.length = rs.length - 1 ∧
        ListInterlaces us rs ∧
        (∀ u ∈ us, F.IsRoot u) ∧
        us.Pairwise (· < ·)
  | [], _, _ => by
      refine ⟨[], by simp, ?_, ?_, ?_⟩
      · simp [ListInterlaces]
      · simp
      · simp
  | [_], _, _ => by
      refine ⟨[], by simp, ?_, ?_, ?_⟩
      · simp [ListInterlaces]
      · simp
      · simp
  | r₁ :: r₂ :: rest, hrs_sorted, hexists => by
      obtain ⟨u, hu₁, hu₂, hu_root⟩ := hexists [] rfl
      have htail_sorted : (r₂ :: rest).Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp hrs_sorted).2
      obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
        exists_roots_strictly_interlacing_of_consecutive_exists
          (F := F) (r₂ :: rest) htail_sorted
          (fun pre {a b tail} hEq => by
            grind)
      have hu_lt_all : ∀ w ∈ us, u < w :=
        fun w hw => lt_of_lt_of_le hu₂ (listInterlaces_all_ge us rest r₂ hus_int w hw)
      refine ⟨u :: us, ?_, ?_, ?_, ?_⟩
      · simp_all
      · exact ⟨le_of_lt hu₁, le_of_lt hu₂, hus_int⟩
      · simp_all
      · simp_all

/-- In the hard succ-degree affine branch with `g(0) ≠ 0`, every open interval
between consecutive roots of `g` contains a root of `f`. The proof uses the
boundary-ratio obstruction: if such an interval were root-free for `f`, then
one of the positive ratios `-g/f` or `-g/(X*f)` would have equal endpoint values
and a positive interior local extremum, contradicting the Wronskian lemma. -/
private lemma exists_f_root_between_consecutive_g_roots_of_affine_family_succDegree_not_isRoot_zero
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg_root0 : ¬ g.IsRoot 0)
    {r₁ r₂ : ℝ}
    (hr₁ : g.IsRoot r₁) (hr₂ : g.IsRoot r₂)
    (hr₁r₂ : r₁ < r₂)
    (hno_between_g : ∀ r ∈ g.roots, ¬ (r₁ < r ∧ r < r₂)) :
    ∃ u, r₁ < u ∧ u < r₂ ∧ f.IsRoot u := by
  have hg_rr : (g ≠ 0 ∧ g.Splits) :=
    AffineFamily.isRealRooted_right_of_affine_family_succDegree hf0 hg0 hfnn hgnn haff hsucc.symm
  have hXf_pos : HasPosLeadingCoeff (X * f) :=
    (hfnn.pos_leadingCoeff hf0).X_mul
  have hposcombo : PosComboRealRooted g (X * f) :=
    AffineFamily.posComboRealRooted_right_of_affine_family hf0 hg0 hfnn hgnn haff
  have hno_right :
      ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r :=
    no_common_right_pair_of_no_common_of_not_isRoot_zero hno hg_root0
  have hr₁_mem : r₁ ∈ g.roots := (mem_roots hg0).mpr hr₁
  have hr₂_mem : r₂ ∈ g.roots := (mem_roots hg0).mpr hr₂
  have hr₁_neg : r₁ < 0 :=
    roots_strictly_neg_of_nonneg_of_no_common_right_pair
      hg_rr.1 hg_rr.2 hgnn hno_right r₁ hr₁_mem
  have hr₂_neg : r₂ < 0 :=
    roots_strictly_neg_of_nonneg_of_no_common_right_pair
      hg_rr.1 hg_rr.2 hgnn hno_right r₂ hr₂_mem
  let m : ℝ := (r₁ + r₂) / 2
  have hm_mem : m ∈ Set.Ioo r₁ r₂ := by
    dsimp [m]
    exact ⟨by linarith, by linarith⟩
  by_contra hexists
  push Not at hexists
  have hden_nonzero_f : ∀ x ∈ Set.Icc r₁ r₂, f.eval x ≠ 0 := by
    intro x hx hfx
    have hroot : f.IsRoot x := by simpa [Polynomial.IsRoot.def] using hfx
    have hx_ne1 : x ≠ r₁ := by
      intro h
      rw [h] at hroot
      exact hno r₁ hr₁ hroot
    have hx_ne2 : x ≠ r₂ := by
      intro h
      rw [h] at hroot
      exact hno r₂ hr₂ hroot
    have hx_mem := Set.mem_Icc.mp hx
    have hx_between : r₁ < x ∧ x < r₂ :=
      ⟨lt_of_le_of_ne hx_mem.1 hx_ne1.symm, lt_of_le_of_ne hx_mem.2 hx_ne2⟩
    exact hexists x hx_between.1 hx_between.2 hroot
  have hg_mid_ne : g.eval m ≠ 0 := by
    intro hgm
    have hroot : g.IsRoot m := by simpa [Polynomial.IsRoot.def] using hgm
    exact hno_between_g m ((mem_roots hg0).mpr hroot) hm_mem
  have hf_mid_ne : f.eval m ≠ 0 := by
    intro hfm
    have hroot : f.IsRoot m := by simpa [Polynomial.IsRoot.def] using hfm
    exact hexists m hm_mem.1 hm_mem.2 hroot
  by_cases hmid_opp : g.eval m * f.eval m < 0
  · have hfamily_f :
        ∀ {t : ℝ}, 0 < t → ((C t * f + g) ≠ 0 ∧ (C t * f + g).Splits) := by
      intro t ht
      simpa [add_comm] using
        AffineFamily.isRealRooted_add_left_of_affine_family_of_natDegree_succ_le
          hf0 hg0 hfnn hgnn haff (by lia) ht
    have hratio_cont :
        ContinuousOn (fun y : ℝ => -(g.eval y / f.eval y)) (Set.Icc r₁ r₂) :=
      (g.continuous.continuousOn.div f.continuous.continuousOn hden_nonzero_f).neg
    have hratio_eq :
        (fun y : ℝ => -(g.eval y / f.eval y)) r₁ =
          (fun y : ℝ => -(g.eval y / f.eval y)) r₂ := by
      have hg₁_eval : g.eval r₁ = 0 := by simpa [Polynomial.IsRoot.def] using hr₁
      have hg₂_eval : g.eval r₂ = 0 := by simpa [Polynomial.IsRoot.def] using hr₂
      simp [hg₁_eval, hg₂_eval]
    obtain ⟨c, hc_mem, hlocal⟩ :=
      exists_isLocalExtr_Ioo hr₁r₂ hratio_cont hratio_eq
    have hprod_c_neg : g.eval c * f.eval c < 0 := by
      by_cases hmc : m ≤ c
      · have hno_mul :
            ∀ x, m ≤ x → x ≤ c → (g * f).eval x ≠ 0 := by
          intro x hmx hxc
          have hx₁ : r₁ < x := lt_of_lt_of_le hm_mem.1 hmx
          have hx₂ : x < r₂ := lt_of_le_of_lt hxc hc_mem.2
          have hgx_ne : g.eval x ≠ 0 := by
            intro hgx
            have hroot : g.IsRoot x := by simpa [Polynomial.IsRoot.def] using hgx
            exact hno_between_g x ((mem_roots hg0).mpr hroot) ⟨hx₁, hx₂⟩
          have hfx_ne : f.eval x ≠ 0 :=
            hden_nonzero_f x (Set.mem_Icc.mpr ⟨le_of_lt hx₁, le_of_lt hx₂⟩)
          simpa [eval_mul] using mul_ne_zero hgx_ne hfx_ne
        have hsame :
            0 < (g * f).eval m * (g * f).eval c :=
          eval_same_sign_of_no_roots (p := g * f) hmc hno_mul
        have hsame' : 0 < (g.eval m * f.eval m) * (g.eval c * f.eval c) := by
          simp only [eval_mul] at hsame
          exact hsame
        have hmid_prod' : g.eval m * f.eval m < 0 := hmid_opp
        have hprod_c' : g.eval c * f.eval c < 0 := by nlinarith
        exact hprod_c'
      · have hcm : c ≤ m := le_of_not_ge hmc
        have hno_mul :
            ∀ x, c ≤ x → x ≤ m → (g * f).eval x ≠ 0 := by
          intro x hcx hxm
          have hx₁ : r₁ < x := lt_of_lt_of_le hc_mem.1 hcx
          have hx₂ : x < r₂ := lt_of_le_of_lt hxm hm_mem.2
          have hgx_ne : g.eval x ≠ 0 := by
            intro hgx
            have hroot : g.IsRoot x := by simpa [Polynomial.IsRoot.def] using hgx
            exact hno_between_g x ((mem_roots hg0).mpr hroot) ⟨hx₁, hx₂⟩
          have hfx_ne : f.eval x ≠ 0 :=
            hden_nonzero_f x (Set.mem_Icc.mpr ⟨le_of_lt hx₁, le_of_lt hx₂⟩)
          simpa [eval_mul] using mul_ne_zero hgx_ne hfx_ne
        have hsame :
            0 < (g * f).eval c * (g * f).eval m :=
          eval_same_sign_of_no_roots (p := g * f) hcm hno_mul
        have hsame' : 0 < (g.eval c * f.eval c) * (g.eval m * f.eval m) := by
          simp only [eval_mul] at hsame
          exact hsame
        have hmid_prod' : g.eval m * f.eval m < 0 := hmid_opp
        have hprod_c' : g.eval c * f.eval c < 0 := by nlinarith
        exact hprod_c'
    have hf_c_ne : f.eval c ≠ 0 :=
      hden_nonzero_f c (Set.mem_Icc.mpr ⟨le_of_lt hc_mem.1, le_of_lt hc_mem.2⟩)
    have hpos_c : 0 < -(g.eval c / f.eval c) :=
      pos_neg_div_of_mul_neg hf_c_ne hprod_c_neg
    exact
      false_of_localExtr_neg_eval_div_eval_pos_of_add_left_family_of_no_common
        hfamily_f hno hlocal hpos_c
  · have hmid_pos : 0 < g.eval m * f.eval m :=
      lt_of_le_of_ne (le_of_not_gt hmid_opp) (mul_ne_zero hg_mid_ne hf_mid_ne).symm
    have hm_neg : m < 0 :=
      lt_trans hm_mem.2 hr₂_neg
    have hmid_right :
        g.eval m * (X * f).eval m < 0 := by
      rw [eval_mul]
      simp only [eval_X]
      nlinarith
    have hden_nonzero_Xf : ∀ x ∈ Set.Icc r₁ r₂, (X * f).eval x ≠ 0 := by
      intro x hx hxf
      rw [eval_mul, eval_X] at hxf
      have hx_neg : x < 0 := lt_of_le_of_lt hx.2 hr₂_neg
      have hx_ne : x ≠ 0 := ne_of_lt hx_neg
      have hfx_ne : f.eval x ≠ 0 := hden_nonzero_f x (Set.mem_Icc.mpr hx)
      exact mul_ne_zero hx_ne hfx_ne hxf
    have hratio_cont :
        ContinuousOn (fun y : ℝ => -(g.eval y / (X * f).eval y)) (Set.Icc r₁ r₂) :=
      (g.continuous.continuousOn.div (X * f).continuous.continuousOn hden_nonzero_Xf).neg
    have hratio_eq :
        (fun y : ℝ => -(g.eval y / (X * f).eval y)) r₁ =
          (fun y : ℝ => -(g.eval y / (X * f).eval y)) r₂ := by
      have hg₁_eval : g.eval r₁ = 0 := by simpa [Polynomial.IsRoot.def] using hr₁
      have hg₂_eval : g.eval r₂ = 0 := by simpa [Polynomial.IsRoot.def] using hr₂
      simp [hg₁_eval, hg₂_eval]
    obtain ⟨c, hc_mem, hlocal⟩ :=
      exists_isLocalExtr_Ioo hr₁r₂ hratio_cont hratio_eq
    have hprod_c_neg :
        g.eval c * (X * f).eval c < 0 := by
      by_cases hmc : m ≤ c
      · have hno_mul :
            ∀ x, m ≤ x → x ≤ c → (g * (X * f)).eval x ≠ 0 := by
          intro x hmx hxc
          have hx₁ : r₁ < x := lt_of_lt_of_le hm_mem.1 hmx
          have hx₂ : x < r₂ := lt_of_le_of_lt hxc hc_mem.2
          have hgx_ne : g.eval x ≠ 0 := by
            intro hgx
            have hroot : g.IsRoot x := by simpa [Polynomial.IsRoot.def] using hgx
            exact hno_between_g x ((mem_roots hg0).mpr hroot) ⟨hx₁, hx₂⟩
          have hXfx_ne : (X * f).eval x ≠ 0 := by
            rw [eval_mul, eval_X]
            have hx_neg : x < 0 := lt_trans hx₂ hr₂_neg
            exact mul_ne_zero (ne_of_lt hx_neg)
              (hden_nonzero_f x (Set.mem_Icc.mpr ⟨le_of_lt hx₁, le_of_lt hx₂⟩))
          simpa [eval_mul] using mul_ne_zero hgx_ne hXfx_ne
        have hsame :
            0 < (g * (X * f)).eval m * (g * (X * f)).eval c :=
          eval_same_sign_of_no_roots (p := g * (X * f)) hmc hno_mul
        have hsame' :
            0 < (g.eval m * (X * f).eval m) * (g.eval c * (X * f).eval c) := by
          rw [eval_mul (p := g) (q := X * f), eval_mul (p := g) (q := X * f)] at hsame
          exact hsame
        have hmid_prod' : g.eval m * (X * f).eval m < 0 := hmid_right
        have hprod_c' : g.eval c * (X * f).eval c < 0 := by nlinarith
        exact hprod_c'
      · have hcm : c ≤ m := le_of_not_ge hmc
        have hno_mul :
            ∀ x, c ≤ x → x ≤ m → (g * (X * f)).eval x ≠ 0 := by
          intro x hcx hxm
          have hx₁ : r₁ < x := lt_of_lt_of_le hc_mem.1 hcx
          have hx₂ : x < r₂ := lt_of_le_of_lt hxm hm_mem.2
          have hgx_ne : g.eval x ≠ 0 := by
            intro hgx
            have hroot : g.IsRoot x := by simpa [Polynomial.IsRoot.def] using hgx
            exact hno_between_g x ((mem_roots hg0).mpr hroot) ⟨hx₁, hx₂⟩
          have hXfx_ne : (X * f).eval x ≠ 0 := by
            rw [eval_mul, eval_X]
            have hx_neg : x < 0 := lt_trans hx₂ hr₂_neg
            exact mul_ne_zero (ne_of_lt hx_neg)
              (hden_nonzero_f x (Set.mem_Icc.mpr ⟨le_of_lt hx₁, le_of_lt hx₂⟩))
          simpa [eval_mul] using mul_ne_zero hgx_ne hXfx_ne
        have hsame :
            0 < (g * (X * f)).eval c * (g * (X * f)).eval m :=
          eval_same_sign_of_no_roots (p := g * (X * f)) hcm hno_mul
        have hsame' :
            0 < (g.eval c * (X * f).eval c) * (g.eval m * (X * f).eval m) := by
          rw [eval_mul (p := g) (q := X * f), eval_mul (p := g) (q := X * f)] at hsame
          exact hsame
        have hmid_prod' : g.eval m * (X * f).eval m < 0 := hmid_right
        have hprod_c' : g.eval c * (X * f).eval c < 0 := by nlinarith
        exact hprod_c'
    have hXf_c_ne : (X * f).eval c ≠ 0 :=
      hden_nonzero_Xf c (Set.mem_Icc.mpr ⟨le_of_lt hc_mem.1, le_of_lt hc_mem.2⟩)
    have hpos_c : 0 < -(g.eval c / (X * f).eval c) :=
      pos_neg_div_of_mul_neg hXf_c_ne hprod_c_neg
    exact
      false_of_localExtr_neg_eval_div_eval_pos_of_add_left_family_of_no_common
        (fun ht => by
          have h_add := PosComboRealRooted.isRealRooted_add_right hposcombo ht
          rw [add_comm] at h_add
          exact h_add)
        hno_right hlocal hpos_c

/-- Boundary same-degree package for the fixed right pair `(g, X * f)` in the
succ-degree affine branch with `g(0) ≠ 0`.

For every `μ > 0`, the pair `(g, g + μ X f)` stays inside the same positive
cone, the second member has the same degree as `g`, its roots are simple, and
it has no common root with `g`. This is the honest same-degree perturbation data
needed if we want to orient the boundary family directly rather than going
through a converse shortcut. -/
private lemma right_boundary_pair_sameDegree_data_of_affine_family_succDegree_not_isRoot_zero
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg_root0 : ¬ g.IsRoot 0)
    {μ : ℝ}
    (hμ : 0 < μ) :
    PosComboRealRooted g (g + C μ * (X * f)) ∧
    ((g + C μ * (X * f)) ≠ 0 ∧ (g + C μ * (X * f)).Splits) ∧
    HasSimpleRoots (g + C μ * (X * f)) ∧
    HasPosLeadingCoeff (g + C μ * (X * f)) ∧
    (g + C μ * (X * f)).natDegree = g.natDegree ∧
    (∀ r, g.IsRoot r → ¬ (g + C μ * (X * f)).IsRoot r) := by
  have hg_rr : (g ≠ 0 ∧ g.Splits) :=
    AffineFamily.isRealRooted_right_of_affine_family_succDegree hf0 hg0 hfnn hgnn haff hsucc.symm
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  have hXf_pos : HasPosLeadingCoeff (X * f) :=
    (hfnn.pos_leadingCoeff hf0).X_mul
  have hposcombo : PosComboRealRooted g (X * f) :=
    AffineFamily.posComboRealRooted_right_of_affine_family hf0 hg0 hfnn hgnn haff
  have hno_right :
      ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r :=
    no_common_right_pair_of_no_common_of_not_isRoot_zero hno hg_root0
  have hpair :
      PosComboRealRooted g (g + C μ * (X * f)) := by
    intro lam ν hlam hν
    have hrr :
        ((C (lam + ν) * g + C (ν * μ) * (X * f)) ≠ 0 ∧
          (C (lam + ν) * g + C (ν * μ) * (X * f)).Splits) :=
      hposcombo (lam := lam + ν) (μ := ν * μ) (by grind) (by positivity)
    grind
  have hμ_rr : ((g + C μ * (X * f)) ≠ 0 ∧ (g + C μ * (X * f)).Splits) :=
    PosComboRealRooted.isRealRooted_add_right hposcombo hμ
  have hμ_simple : HasSimpleRoots (g + C μ * (X * f)) :=
    PosComboRealRooted.hasSimpleRoots_add_right hposcombo hno_right hμ
  have hμ_pos : HasPosLeadingCoeff (g + C μ * (X * f)) := by
    have hdeg : g.natDegree ≤ (X * f).natDegree := by simp_all
    have hsum_nonneg : HasNonnegCoeffs (g + C μ * (X * f)) :=
      hgnn.add (nonnegCoeffs_C_mul hμ.le hfnn.X_mul)
    have hsum_ne : g + C μ * (X * f) ≠ 0 := hμ_rr.1
    exact hsum_nonneg.pos_leadingCoeff hsum_ne
  have hμ_deg : (g + C μ * (X * f)).natDegree = g.natDegree := by
    have hdeg : g.natDegree ≤ (X * f).natDegree := by simp_all
    calc
      (g + C μ * (X * f)).natDegree = (X * f).natDegree :=
        PosComboRealRooted.family_natDegree_right hdeg hg_pos hXf_pos hμ
      _ = g.natDegree := by simp_all
  have hno_boundary :
      ∀ r, g.IsRoot r → ¬ (g + C μ * (X * f)).IsRoot r := by
    intro r hgr hboundary
    simp_all
  lia

/-- The affine family `(C s * X + C t) * f + g` being real-rooted for all `s, t > 0`
implies `AllComboRealRooted g f` (all linear combinations `α g + β f` are
real-rooted), provided `f, g` have nonneg coefficients, positive leading
coefficients, no common roots, and `g.natDegree = f.natDegree + 1`.

The key observation is that for `x₀ < 0`, the affine substitution
`y = s x₀ + t` sweeps all of `ℝ` as `(s, t)` ranges over `(0,∞)²`,
so the affine family pins every fibre `g(x₀) + y f(x₀)`.  Combined with
the completed Obreschkoff converse this gives `Prec g f ∨ Prec f g`. -/
private lemma allComboRealRooted_of_affine_family_succDegree_not_isRoot_zero
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hXf_rr : ((X * f) ≠ 0 ∧ (X * f).Splits))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg_root0 : ¬ g.IsRoot 0) :
    AllComboRealRooted g f := by
  have hf_rr : (f ≠ 0 ∧ f.Splits) :=
    isRealRooted_of_X_mul hXf_rr.1 hXf_rr.2
  have hg_rr : (g ≠ 0 ∧ g.Splits) :=
    AffineFamily.isRealRooted_right_of_affine_family_succDegree hf0 hg0 hfnn hgnn haff hsucc.symm
  have hsimple_g : HasSimpleRoots g :=
    AffineFamily.hasSimpleRoots_right_of_affine_family_succDegree_not_isRoot_zero
      hf0 hg0 hfnn hgnn haff hsucc hno hg_root0
  let rs := g.roots.sort (· ≤ ·)
  have hrs_sorted : rs.Pairwise (· ≤ ·) := by simp [rs]
  have hrs_sortedLT : rs.Pairwise (· < ·) := by
    simpa [rs] using hsimple_g.roots_sort_sortedLT.pairwise
  have hrs_eq : (↑rs : Multiset ℝ) = g.roots := by simp [rs]
  have hgap_rs : ConsecNoRoots g rs :=
    consecNoRoots_of_sorted_eq hrs_eq hrs_sorted
  have hroot_between :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        ∃ u, r₁ < u ∧ u < r₂ ∧ f.IsRoot u := by
    intro pre r₁ r₂ rest hEq
    have hpair_full : (pre ++ r₁ :: r₂ :: rest).Pairwise (· < ·) := by lia
    have hsuf_sortedLT : (r₁ :: r₂ :: rest).Pairwise (· < ·) :=
      hpair_full.sublist (List.sublist_append_right pre (r₁ :: r₂ :: rest))
    have hgap_full : ConsecNoRoots g (pre ++ r₁ :: r₂ :: rest) := by lia
    have hsuf_gap : ConsecNoRoots g (r₁ :: r₂ :: rest) :=
      consecNoRoots_suffix pre (r₁ :: r₂ :: rest) hgap_full
    have hr₁r₂ : r₁ < r₂ := List.rel_of_pairwise_cons hsuf_sortedLT (.head _)
    have hr₁_mem_rs : r₁ ∈ rs := by simp_all
    have hr₂_mem_rs : r₂ ∈ rs := by simp_all
    have hr₁_root : g.IsRoot r₁ := by
      have : r₁ ∈ (↑rs : Multiset ℝ) := Multiset.mem_coe.mpr hr₁_mem_rs
      simp_all
    have hr₂_root : g.IsRoot r₂ := by
      have : r₂ ∈ (↑rs : Multiset ℝ) := Multiset.mem_coe.mpr hr₂_mem_rs
      simp_all
    exact
      exists_f_root_between_consecutive_g_roots_of_affine_family_succDegree_not_isRoot_zero
        hf0 hg0 hfnn hgnn haff hsucc hno hg_root0
        hr₁_root hr₂_root hr₁r₂ hsuf_gap.1
  obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_exists (F := f) rs hrs_sorted hroot_between
  have hus_sub : (↑us : Multiset ℝ) ≤ f.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hus_pw.imp ne_of_lt))]
    intro x hx
    simp_all
  have hrs_len : rs.length = g.natDegree := by
    rw [show rs = g.roots.sort (· ≤ ·) by lia, Multiset.length_sort,
      card_roots_of_splits hg_rr.2]
  have hus_eq : (↑us : Multiset ℝ) = f.roots := by
    apply Multiset.eq_of_le_of_card_le hus_sub
    calc
      f.roots.card = f.natDegree := card_roots_of_splits hf_rr.2
      _ = g.natDegree - 1 := by lia
      _ = rs.length - 1 := by lia
      _ = us.length := hus_len.symm
      _ = (↑us : Multiset ℝ).card := (Multiset.coe_card us).symm
      _ ≤ (↑us : Multiset ℝ).card := le_rfl
  have hprec_fg : Prec f g := by
    refine ⟨hf_rr, hg_rr, us, rs, hus_pw.imp le_of_lt, hrs_sorted, hus_eq, hrs_eq, ?_⟩
    lia
  have hall_fg : AllComboRealRooted f g :=
    allComboRealRooted_of_prec hprec_fg
  exact allComboRealRooted_comm hall_fg

protected lemma AffineFamily.allComboRealRooted_of_affine_family_succDegree
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hXf_rr : ((X * f) ≠ 0 ∧ (X * f).Splits))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r) :
    AllComboRealRooted g f := by
  by_cases hg_root0 : g.IsRoot 0
  · have hf_root0_false : ¬ f.IsRoot 0 := hno 0 hg_root0
    have hshift_nonneg : HasNonnegCoeffs (g + f) := hgnn.add hfnn
    have hshift_ne : g + f ≠ 0 :=
      add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hgnn hfnn hf0
    have hshift_succ : (g + f).natDegree = f.natDegree + 1 := by
      have hdeg_lt : f.natDegree < g.natDegree := by lia
      calc
        (g + f).natDegree = g.natDegree :=
          natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff
            hdeg_lt (hgnn.pos_leadingCoeff hg0)
        _ = f.natDegree + 1 := hsucc
    have hshift_aff :
        ∀ {s t : ℝ}, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + (g + f)) ≠ 0 ∧
            (((C s * X + C t) * f) + (g + f)).Splits) := by
      intro s t hs ht
      have hbase :
          ((((C s * X + C (t + 1)) * f) + g) ≠ 0 ∧ (((C s * X + C (t + 1)) * f) + g).Splits) :=
        haff hs (by grind)
      grind
    have hshift_no : ∀ r, (g + f).IsRoot r → ¬ f.IsRoot r :=
      fun r hshift_root hfr => by simp_all
    have hshift_root0_false : ¬ (g + f).IsRoot 0 := by simp_all
    have hall_shift : AllComboRealRooted (g + f) f :=
      allComboRealRooted_of_affine_family_succDegree_not_isRoot_zero
        hf0 hshift_ne hfnn hshift_nonneg hshift_aff hXf_rr
          hshift_succ hshift_no hshift_root0_false
    intro α β
    have hEq :
        C α * g + C β * f =
          C α * (g + f) + C (β - α) * f := by
      grind
    simpa [hEq] using hall_shift α (β - α)
  · exact
      allComboRealRooted_of_affine_family_succDegree_not_isRoot_zero
        hf0 hg0 hfnn hgnn haff hXf_rr hsucc hno hg_root0

end RealRooted
