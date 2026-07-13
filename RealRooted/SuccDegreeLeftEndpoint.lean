/-
# Succ-degree left endpoint via root continuity

This file proves, by a direct complex-root-continuity ("escaping root")
argument, that in a positive-combination family `f + μ g` with
`deg g = deg f + 1`, the lower-degree member `f` splits.
-/
import RealRooted.Basic
import RealRooted.PosCombo
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

open Polynomial Topology

noncomputable section

namespace RealRooted

/-- Complex evaluation of a split real polynomial as a product over its real
roots. -/
lemma norm_aeval_eq_prod_norm_roots {p : ℝ[X]} (hp : p.Splits) (z : ℂ) :
    ‖(Polynomial.aeval z) p‖ =
      |p.leadingCoeff| * (p.roots.map (fun r : ℝ => ‖z - (r : ℂ)‖)).prod := by
  have h_prod :
      p = Polynomial.C p.leadingCoeff *
        Multiset.prod (Multiset.map (fun r => Polynomial.X - Polynomial.C r) p.roots) := by
    convert Polynomial.Splits.eq_prod_roots hp
  conv_lhs =>
    rw [h_prod]
    simp [norm_mul]
    ring_nf
  induction p.roots using Multiset.induction <;> norm_num at *
  tauto

/-- Escaping-root estimate: for a split real polynomial `p`, a complex point
`z` with `z.im ≠ 0`, and any root `r` of `p`, the distance `‖z - r‖` is
controlled by `‖p(z)‖`, since the other `card - 1` factors are bounded below by
`|z.im|`. -/
lemma leadingCoeff_mul_pow_im_mul_norm_sub_le_norm_aeval
    {p : ℝ[X]} (hp : p.Splits) {z : ℂ} (hz : z.im ≠ 0)
    {r : ℝ} (hr : r ∈ p.roots) :
    |p.leadingCoeff| * |z.im| ^ (p.roots.card - 1) * ‖z - (r : ℂ)‖
      ≤ ‖(Polynomial.aeval z) p‖ := by
  have hRHS :
      ‖(Polynomial.aeval z) p‖ =
        |p.leadingCoeff| * (p.roots.map (fun r : ℝ => ‖z - (r : ℂ)‖)).prod := by
    convert norm_aeval_eq_prod_norm_roots hp z using 1
  rw [hRHS]
  have h_prod_bound :
      |z.im| ^ ((p.roots.erase r).card) ≤
        ((p.roots.erase r).map (fun s : ℝ => ‖z - (s : ℂ)‖)).prod := by
    have h_prod_bound :
        ∀ (m : Multiset ℝ),
          (∀ s ∈ m, ‖z - (s : ℂ)‖ ≥ |z.im|) →
            |z.im| ^ m.card ≤ (m.map (fun s : ℝ => ‖z - (s : ℂ)‖)).prod := by
      intro m hm
      induction m using Multiset.induction with
      | empty =>
        simp only [Multiset.card_zero, pow_zero, Multiset.map_zero,
          Multiset.prod_zero, le_refl]
      | cons a m ih =>
          have h_ih : |z.im| ^ m.card ≤ (m.map (fun s : ℝ => ‖z - (s : ℂ)‖)).prod := by
            apply ih
            intro s hs
            apply hm
            exact Multiset.mem_cons_of_mem hs
          have ha : ‖z - (a : ℂ)‖ ≥ |z.im| := by
            apply hm
            exact Multiset.mem_cons_self a m
          rw [Multiset.card_cons, pow_succ', Multiset.map_cons, Multiset.prod_cons]
          exact mul_le_mul ha h_ih (by positivity) (by positivity)
    exact h_prod_bound _ fun s hs => by
      simpa using Complex.abs_im_le_norm (z - s)
  rw [← Multiset.cons_erase hr, Multiset.map_cons, Multiset.prod_cons]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left h_prod_bound
      (by positivity : 0 ≤ |p.leadingCoeff| * ‖z - r‖)

/-- Uniform bound on the next coefficient of a split real polynomial, obtained
from the escaping estimate and Vieta's formula
`nextCoeff = -leadingCoeff * roots.sum`. -/
lemma abs_nextCoeff_le_of_splits
    {p : ℝ[X]} (hp : p.Splits) {z : ℂ} (hz : z.im ≠ 0)
    (hlc : 0 < p.leadingCoeff) :
    |p.nextCoeff| ≤
      p.leadingCoeff * p.roots.card *
        (‖z‖ + ‖(Polynomial.aeval z) p‖ /
          (p.leadingCoeff * |z.im| ^ (p.roots.card - 1))) := by
  have h_vieta : p.nextCoeff = -p.leadingCoeff * Multiset.sum p.roots :=
    hp.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have h_escape_bound :
      ∀ r ∈ p.roots,
        ‖(r : ℂ)‖ ≤
          ‖z‖ + ‖(Polynomial.aeval z) p‖ /
            (p.leadingCoeff * |z.im| ^ (p.roots.card - 1)) := by
    intro r hr
    have h_escape_bound :
        ‖(z - (r : ℂ))‖ ≤
          ‖(Polynomial.aeval z) p‖ /
            (p.leadingCoeff * |z.im| ^ (p.roots.card - 1)) := by
      have := leadingCoeff_mul_pow_im_mul_norm_sub_le_norm_aeval hp hz hr
      rw [le_div_iff₀] <;> first
      | positivity
      | rw [abs_of_pos hlc] at this
        linarith
    have := norm_sub_le (z : ℂ) (z - r)
    norm_num at *
    linarith
  have h_sum_escape_bound :
      ‖p.roots.sum‖ ≤
        p.roots.card *
          (‖z‖ + ‖(Polynomial.aeval z) p‖ /
            (p.leadingCoeff * |z.im| ^ (p.roots.card - 1))) := by
    have h_sum_escape_bound :
        ∀ {s : Multiset ℝ},
          (∀ r ∈ s,
            ‖(r : ℂ)‖ ≤
              ‖z‖ + ‖(Polynomial.aeval z) p‖ /
                (p.leadingCoeff * |z.im| ^ (p.roots.card - 1))) →
          ‖s.sum‖ ≤
            s.card *
              (‖z‖ + ‖(Polynomial.aeval z) p‖ /
                (p.leadingCoeff * |z.im| ^ (p.roots.card - 1))) := by
      intro s hs
      induction s using Multiset.induction <;> norm_num at *
      grind
    exact h_sum_escape_bound h_escape_bound
  simp_all [mul_assoc, abs_mul, abs_neg, abs_of_pos hlc]

/-- Single-member escaping-root inequality.  Given a *single* real-rooted
member `f + C μ * g` (`μ > 0`) of the succ-degree family, the next coefficient
of `f + μ g` is bounded by `μ` times a constant independent of `μ`.  This is the
per-`μ` heart of `key_family_ineq`, stated so it only depends on the one member
being real-rooted rather than the whole family. -/
lemma key_family_ineq_of_splits {f g : ℝ[X]} {μ : ℝ}
    (hsplit : (f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits)
    (_hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hsucc : g.natDegree = f.natDegree + 1)
    {z : ℂ} (hz : z.im ≠ 0) (hzf : (Polynomial.aeval z) f = 0)
    (hμ : 0 < μ) :
    |f.leadingCoeff + μ * g.coeff f.natDegree|
      ≤ μ * (g.leadingCoeff * (f.natDegree + 1) *
        (‖z‖ + ‖(Polynomial.aeval z) g‖ /
          (g.leadingCoeff * |z.im| ^ f.natDegree))) := by
  have := @abs_nextCoeff_le_of_splits (f + Polynomial.C μ * g) ?_ z ?_ ?_
  · convert this using 1
    · rw [Polynomial.nextCoeff]
      rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt]
      · rw [Polynomial.natDegree_C_mul hμ.ne']; aesop
      · rw [Polynomial.natDegree_C_mul hμ.ne']; aesop
    · have hcard : (f + Polynomial.C μ * g).roots.card = f.natDegree + 1 := by
        have := Polynomial.Splits.natDegree_eq_card_roots hsplit.2
        rw [← this, Polynomial.natDegree_add_eq_right_of_natDegree_lt]
        · rw [Polynomial.natDegree_C_mul hμ.ne']; aesop
        · rw [Polynomial.natDegree_C_mul hμ.ne']; aesop
      rw [hcard, Polynomial.leadingCoeff_add_of_degree_lt]
      · simp only [map_add, map_mul, aeval_C, hzf, zero_add, leadingCoeff_mul,
          Polynomial.leadingCoeff_C, norm_mul]
        norm_num [abs_of_pos hg_pos, mul_assoc, mul_div_mul_left, hμ.ne', abs_of_pos hμ]
      · rw [Polynomial.degree_C_mul hμ.ne',
          Polynomial.degree_eq_natDegree (leadingCoeff_ne_zero.mp hg_pos.ne'), hsucc]
        exact lt_of_le_of_lt (α := WithBot ℕ) (Polynomial.degree_le_natDegree (p := f))
          (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self f.natDegree))
  · exact hsplit.2
  · assumption
  · rw [Polynomial.leadingCoeff_add_of_degree_lt]
    · rw [leadingCoeff_mul]
      rw [Polynomial.leadingCoeff_C]
      positivity
    · rw [Polynomial.degree_C_mul hμ.ne',
        Polynomial.degree_eq_natDegree (leadingCoeff_ne_zero.mp hg_pos.ne'), hsucc]
      exact lt_of_le_of_lt (α := WithBot ℕ) (Polynomial.degree_le_natDegree (p := f))
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self f.natDegree))

/-- A positive quantity cannot be bounded by `μ * M` for every `μ > 0`. -/
lemma false_of_forall_pos_mul_le {a M : ℝ} (ha : 0 < a)
    (h : ∀ μ : ℝ, 0 < μ → a ≤ μ * M) : False :=
  absurd
    (h (a / (2 * |M| + 1)) (by positivity))
    (by
      cases abs_cases M <;>
        nlinarith [mul_div_cancel₀ a (by positivity : (2 * |M| + 1) ≠ 0)])

/-- A positive quantity cannot be bounded by `μ * M` for every small positive
`μ` either: it suffices that `a ≤ μ * M` holds on some interval `(0, ε)`. -/
lemma false_of_forall_Ioo_mul_le {a M ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (h : ∀ μ : ℝ, 0 < μ → μ < ε → a ≤ μ * M) : False := by
  have hden : (0 : ℝ) < 2 * |M| + 1 := by positivity
  set c : ℝ := a / (2 * |M| + 1) with hc
  have hcpos : 0 < c := by positivity
  set μ : ℝ := min c (ε / 2) with hμdef
  have hμpos : 0 < μ := lt_min hcpos (by positivity)
  have hμlt : μ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hμc : μ ≤ c := min_le_left _ _
  have hkey : a ≤ μ * M := h μ hμpos hμlt
  rcases le_or_gt M 0 with hM | hM
  · have : μ * M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμpos.le hM
    linarith
  · have hcM : c * M < a := by
      rw [hc, div_mul_eq_mul_div, div_lt_iff₀ hden, abs_of_pos hM]
      nlinarith
    have hμM : μ * M ≤ c * M := mul_le_mul_of_nonneg_right hμc hM.le
    linarith

/-- The per-`μ` escaping-root inequality.  Under the succ-degree family
hypotheses, for a complex root `z` of `f` with `z.im ≠ 0`, the next coefficient
of `f + μ g` is bounded by `μ` times a constant independent of `μ`. -/
lemma key_family_ineq {f g : ℝ[X]}
    (hfamily : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (_hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hsucc : g.natDegree = f.natDegree + 1)
    {z : ℂ} (hz : z.im ≠ 0) (hzf : (Polynomial.aeval z) f = 0)
    {μ : ℝ} (hμ : 0 < μ) :
    |f.leadingCoeff + μ * g.coeff f.natDegree|
      ≤ μ * (g.leadingCoeff * (f.natDegree + 1) *
        (‖z‖ + ‖(Polynomial.aeval z) g‖ /
          (g.leadingCoeff * |z.im| ^ f.natDegree))) :=
  key_family_ineq_of_splits (hfamily hμ) _hf_pos hg_pos hsucc hz hzf hμ

/-- Eventual (small-`μ`) form of the succ-degree left endpoint.  It suffices
that the members `f + C μ * g` are real-rooted for all small positive `μ`; the
escaping-root argument only probes the family near `μ = 0⁺`. -/
theorem splits_of_eventually_add_C_mul_family_of_succDegree
    {f g : ℝ[X]} {ε : ℝ} (hε : 0 < ε)
    (hfamily : ∀ {μ : ℝ}, 0 < μ → μ < ε →
      ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hf_pos : 0 < f.leadingCoeff)
    (hg_pos : 0 < g.leadingCoeff)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits := by
  refine Polynomial.Splits.of_splits_map (algebraMap ℝ ℂ) (IsAlgClosed.splits _) ?_
  intro z hz_mem
  have hzf : (Polynomial.aeval (R := ℝ) z f) = 0 := by
    aesop
  by_contra hz_im_ne_zero
  have hz_im : z.im ≠ 0 :=
    fun h => hz_im_ne_zero <| ⟨z.re, by simp [Complex.ext_iff, h]⟩
  have h_bound :
      ∀ μ : ℝ, 0 < μ → μ < ε →
        f.leadingCoeff ≤
          μ * (g.leadingCoeff * (f.natDegree + 1) *
            (‖z‖ + ‖(Polynomial.aeval (R := ℝ) z) g‖ /
              (g.leadingCoeff * |z.im| ^ f.natDegree)) +
            |g.coeff f.natDegree|) := by
    intro μ hμ_pos hμ_lt
    have h_bound :
        |f.leadingCoeff + μ * g.coeff f.natDegree| ≤
          μ * (g.leadingCoeff * (f.natDegree + 1) *
            (‖z‖ + ‖(Polynomial.aeval (R := ℝ) z) g‖ /
              (g.leadingCoeff * |z.im| ^ f.natDegree))) := by
      convert key_family_ineq_of_splits (hfamily hμ_pos hμ_lt) hf_pos hg_pos hsucc
        hz_im hzf hμ_pos using 1
    cases abs_cases (g.coeff f.natDegree) <;> nlinarith [abs_le.mp h_bound]
  exact false_of_forall_Ioo_mul_le hf_pos hε h_bound

/-- Neighborhood-at-zero form of the succ-degree left endpoint. It suffices
that the members `f + C μ * g` are real-rooted for `μ` ranging over a right
neighborhood of `0`, packaged as `∀ᶠ μ in 𝓝[>] (0 : ℝ)`. This is the filter
reformulation of `splits_of_eventually_add_C_mul_family_of_succDegree`; the
`Eventually` phrasing composes directly with downstream continuity arguments. -/
theorem splits_of_eventually_nhdsGT_add_C_mul_family_of_succDegree
    {f g : ℝ[X]}
    (hfamily : ∀ᶠ μ in 𝓝[>] (0 : ℝ),
      ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hf_pos : 0 < f.leadingCoeff)
    (hg_pos : 0 < g.leadingCoeff)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits := by
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hfamily
  exact splits_of_eventually_add_C_mul_family_of_succDegree hε
    (fun {μ} hμ_pos hμ_lt => hsub ⟨hμ_pos, hμ_lt⟩) hf_pos hg_pos hsucc

/-- A predicate that holds for every strictly positive real holds eventually
along the right-neighborhood filter `𝓝[>] 0`. -/
lemma eventually_nhdsGT_of_forall_pos {P : ℝ → Prop}
    (h : ∀ μ : ℝ, 0 < μ → P μ) :
    ∀ᶠ μ in 𝓝[>] (0 : ℝ), P μ :=
  Filter.eventually_of_mem self_mem_nhdsWithin (fun μ hμ => h μ hμ)

/-- Global positive-family form of the right-neighborhood endpoint theorem. -/
theorem splits_of_forall_pos_nhdsGT_add_C_mul_family_of_succDegree
    {f g : ℝ[X]}
    (hfamily : ∀ μ : ℝ, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hf_pos : 0 < f.leadingCoeff)
    (hg_pos : 0 < g.leadingCoeff)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits :=
  splits_of_eventually_nhdsGT_add_C_mul_family_of_succDegree
    (eventually_nhdsGT_of_forall_pos hfamily) hf_pos hg_pos hsucc

/-- `Filter.Eventually` packaging of the right-neighborhood endpoint theorem
when eventual nonvanishing and eventual splitting are produced separately. -/
theorem splits_of_eventually_nhdsGT_ne_zero_and_splits
    {f g : ℝ[X]}
    (hne : ∀ᶠ μ in 𝓝[>] (0 : ℝ), (f + C μ * g) ≠ 0)
    (hsplit : ∀ᶠ μ in 𝓝[>] (0 : ℝ), (f + C μ * g).Splits)
    (hf_pos : 0 < f.leadingCoeff)
    (hg_pos : 0 < g.leadingCoeff)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits :=
  splits_of_eventually_nhdsGT_add_C_mul_family_of_succDegree
    (hne.and hsplit) hf_pos hg_pos hsucc

/-- Closed-ray neighborhood form of the succ-degree left endpoint. -/
theorem splits_of_eventually_nhdsGE_add_C_mul_family_of_succDegree
    {f g : ℝ[X]}
    (hfamily : ∀ᶠ μ in 𝓝[≥] (0 : ℝ),
      ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hf_pos : 0 < f.leadingCoeff)
    (hg_pos : 0 < g.leadingCoeff)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits :=
  splits_of_eventually_nhdsGT_add_C_mul_family_of_succDegree
    (hfamily.filter_mono (nhdsWithin_mono _ Set.Ioi_subset_Ici_self))
    hf_pos hg_pos hsucc

/-- If every member `f + C μ * g`, `μ > 0`, of the affine family is
real-rooted, both `f` and `g` have positive leading coefficients, and
`g.natDegree = f.natDegree + 1`, then the lower-degree member `f` splits. -/
theorem splits_of_add_C_mul_family_of_succDegree
    {f g : ℝ[X]}
    (hfamily : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hf_pos : 0 < f.leadingCoeff)
    (hg_pos : 0 < g.leadingCoeff)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits :=
  splits_of_eventually_add_C_mul_family_of_succDegree (ε := 1) one_pos
    (fun {_} hμ _ => hfamily hμ) hf_pos hg_pos hsucc

/-- Closed-segment form of the succ-degree left endpoint.  If for every `β`
with `0 < β < 1` the closed-segment member `C (1 - β) * f + C β * g` is nonzero
and splits, both leading coefficients are positive, and
`g.natDegree = f.natDegree + 1`, then the lower-degree member `f` splits.

The proof reduces to `splits_of_add_C_mul_family_of_succDegree` via the
substitution `β = μ / (μ + 1)`. -/
theorem splits_of_closedSegment_family_of_succDegree
    {f g : ℝ[X]}
    (hfamily : ∀ {β : ℝ}, 0 < β → β < 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧ (C (1 - β) * f + C β * g).Splits))
    (hf_pos : 0 < f.leadingCoeff)
    (hg_pos : 0 < g.leadingCoeff)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits := by
  refine splits_of_add_C_mul_family_of_succDegree ?_ hf_pos hg_pos hsucc
  intro μ hμ
  have hμ1 : (0 : ℝ) < μ + 1 := by linarith
  have hne : μ + 1 ≠ 0 := hμ1.ne'
  set β : ℝ := μ / (μ + 1) with hβdef
  have hβpos : 0 < β := by
    rw [hβdef]
    exact div_pos hμ hμ1
  have hβlt : β < 1 := by
    rw [hβdef, div_lt_one hμ1]
    linarith
  have hseg := hfamily hβpos hβlt
  have hscaled := isRealRooted_C_mul hseg.1 hseg.2 hne
  have hEq : C (μ + 1) * (C (1 - β) * f + C β * g) = f + C μ * g := by
    have h1 : (μ + 1) * (1 - β) = 1 := by
      rw [hβdef]
      field_simp
      ring
    have h2 : (μ + 1) * β = μ := by
      rw [hβdef]
      field_simp
    calc
      C (μ + 1) * (C (1 - β) * f + C β * g)
          = C ((μ + 1) * (1 - β)) * f + C ((μ + 1) * β) * g := by
            simp only [mul_add, ← mul_assoc, ← C_mul]
      _ = f + C μ * g := by rw [h1, h2, C_1, one_mul]
  rw [hEq] at hscaled
  exact hscaled

/-- Right-family form of the succ-degree endpoint theorem. -/
theorem splits_right_of_add_C_mul_family_of_succDegree
    {f g : ℝ[X]}
    (hfamily : ∀ {μ : ℝ}, 0 < μ → ((g + C μ * f) ≠ 0 ∧ (g + C μ * f).Splits))
    (hf_pos : 0 < f.leadingCoeff)
    (hg_pos : 0 < g.leadingCoeff)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g.Splits :=
  splits_of_add_C_mul_family_of_succDegree hfamily hg_pos hf_pos hsucc

/-- Succ-degree positive-combination families split at the lower-degree
endpoint. -/
theorem PosComboRealRooted.left_splits_of_succDegree {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits :=
  splits_of_add_C_mul_family_of_succDegree
    (fun hμ => hfg.isRealRooted_add_right hμ) hf_pos hg_pos hsucc

/-- Succ-degree positive-combination families split at the higher-degree
endpoint after swapping the pair. -/
theorem PosComboRealRooted.right_splits_of_succDegree {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g.Splits :=
  PosComboRealRooted.left_splits_of_succDegree
    (PosComboRealRooted.comm hfg) hg_pos hf_pos hsucc

/-- Closed-segment form of the succ-degree endpoint for positive-combination
families.  If `PosComboRealRooted f g`, both leading coefficients are positive,
and `g.natDegree = f.natDegree + 1`, then the lower-degree member `f` splits.

This is direct #42 support: it packages
`splits_of_closedSegment_family_of_succDegree` against the
`PosComboRealRooted` interface used by the closed-segment route. -/
theorem PosComboRealRooted.left_splits_of_closedSegment_of_succDegree
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits :=
  splits_of_closedSegment_family_of_succDegree
    (fun {β} hβ0 hβ1 => hfg (show (0 : ℝ) < 1 - β by linarith) hβ0)
    hf_pos hg_pos hsucc

/-- Closed-segment form of the succ-degree endpoint theorem at the
higher-degree endpoint, obtained by swapping the pair. -/
theorem PosComboRealRooted.right_splits_of_closedSegment_of_succDegree
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g.Splits :=
  PosComboRealRooted.left_splits_of_closedSegment_of_succDegree
    (PosComboRealRooted.comm hfg) hg_pos hf_pos hsucc

/-!
### Direct #42 closed-segment endpoint API

The following small public wrappers package the closed-segment endpoint-splitting
facts for direct downstream #42 use.  They differ from the
`PosComboRealRooted.*_splits_of_closedSegment_of_succDegree` lemmas above only in
hypothesis order: the arguments are arranged exactly as in the nonnegative
succ-degree statements of `CommonInterleaverTwo` (positive leading `f`, positive
leading `g`, then the `PosComboRealRooted f g` pairing hypothesis, then the
degree equality `g.natDegree = f.natDegree + 1`), so that they line up with the
direct #42 call sites without reordering.  No new mathematics is introduced. -/

/-- Direct #42 closed-segment endpoint support (lower-degree endpoint).

Hypotheses are arranged in the same order as the nonnegative succ-degree
statements in `CommonInterleaverTwo`: positive leading `f`, positive leading
`g`, the `PosComboRealRooted f g` pairing hypothesis, and the degree equality
`g.natDegree = f.natDegree + 1`.  Under these hypotheses the lower-degree member
`f` splits.  This is a thin reordering wrapper around
`PosComboRealRooted.left_splits_of_closedSegment_of_succDegree`. -/
theorem left_splits_closedSegment_of_succDegree {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits :=
  hfg.left_splits_of_closedSegment_of_succDegree hf_pos hg_pos hsucc

/-- Direct #42 closed-segment endpoint support (higher-degree endpoint).

Hypotheses are arranged in the same order as the nonnegative succ-degree
statements in `CommonInterleaverTwo`: positive leading `f`, positive leading
`g`, the `PosComboRealRooted f g` pairing hypothesis, and the degree equality
`f.natDegree = g.natDegree + 1`.  Under these hypotheses the higher-degree side
member `g` splits.  This is a thin reordering wrapper around
`PosComboRealRooted.right_splits_of_closedSegment_of_succDegree`. -/
theorem right_splits_closedSegment_of_succDegree {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g.Splits :=
  hfg.right_splits_of_closedSegment_of_succDegree hf_pos hg_pos hsucc

/-- Direct #42 closed-segment endpoint support (lower-degree endpoint), packaged
as the `≠ 0 ∧ Splits` pair used by the compatibility/interleaver interface.

Hypotheses are arranged in the same order as the nonnegative succ-degree
statements in `CommonInterleaverTwo`: positive leading `f`, positive leading
`g`, the `PosComboRealRooted f g` pairing hypothesis, and the degree equality
`g.natDegree = f.natDegree + 1`.  Nonvanishing of `f` comes from its positive
leading coefficient. -/
theorem left_ne_zero_and_splits_closedSegment_of_succDegree {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f ≠ 0 ∧ f.Splits :=
  ⟨hf_pos.ne_zero,
    left_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc⟩

/-- Direct #42 closed-segment endpoint support (higher-degree endpoint),
packaged as the `≠ 0 ∧ Splits` pair used by the compatibility/interleaver
interface.

Hypotheses are arranged in the same order as the nonnegative succ-degree
statements in `CommonInterleaverTwo`: positive leading `f`, positive leading
`g`, the `PosComboRealRooted f g` pairing hypothesis, and the degree equality
`f.natDegree = g.natDegree + 1`.  Nonvanishing of `g` comes from its positive
leading coefficient. -/
theorem right_ne_zero_and_splits_closedSegment_of_succDegree {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g ≠ 0 ∧ g.Splits :=
  ⟨hg_pos.ne_zero,
    right_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc⟩

/-!
### Additional direct #42 endpoint wrappers

These are thin API wrappers around the closed-segment succ-degree endpoint
lemmas above.  They only change binder style, namespace placement, or currying
order so downstream `CommonInterleaverTwo` call sites can use the endpoint
facts without local hypothesis shuffling.
-/

/-- Explicit-binder variant of `left_splits_closedSegment_of_succDegree`. -/
theorem left_splits_closedSegment_of_succDegree' (f g : ℝ[X])
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits :=
  left_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Explicit-binder variant of `right_splits_closedSegment_of_succDegree`. -/
theorem right_splits_closedSegment_of_succDegree' (f g : ℝ[X])
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g.Splits :=
  right_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Explicit-binder variant of
`left_ne_zero_and_splits_closedSegment_of_succDegree`. -/
theorem left_ne_zero_and_splits_closedSegment_of_succDegree' (f g : ℝ[X])
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f ≠ 0 ∧ f.Splits :=
  left_ne_zero_and_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Explicit-binder variant of
`right_ne_zero_and_splits_closedSegment_of_succDegree`. -/
theorem right_ne_zero_and_splits_closedSegment_of_succDegree' (f g : ℝ[X])
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g ≠ 0 ∧ g.Splits :=
  right_ne_zero_and_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Dot-notation variant of the lower-degree endpoint packaged as
`≠ 0 ∧ Splits`. -/
theorem PosComboRealRooted.left_ne_zero_and_splits_closedSegment_of_succDegree
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f ≠ 0 ∧ f.Splits :=
  _root_.RealRooted.left_ne_zero_and_splits_closedSegment_of_succDegree
    hf_pos hg_pos hfg hsucc

/-- Dot-notation variant of the higher-degree endpoint packaged as
`≠ 0 ∧ Splits`. -/
theorem PosComboRealRooted.right_ne_zero_and_splits_closedSegment_of_succDegree
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g ≠ 0 ∧ g.Splits :=
  _root_.RealRooted.right_ne_zero_and_splits_closedSegment_of_succDegree
    hf_pos hg_pos hfg hsucc

/-- Curried strict-implicit form of the lower-degree endpoint. -/
theorem left_splits_closedSegment_of_succDegree_curried :
    ∀ ⦃f g : ℝ[X]⦄, HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      PosComboRealRooted f g → g.natDegree = f.natDegree + 1 → f.Splits :=
  fun _ _ hf_pos hg_pos hfg hsucc =>
    left_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Curried strict-implicit form of the higher-degree endpoint. -/
theorem right_splits_closedSegment_of_succDegree_curried :
    ∀ ⦃f g : ℝ[X]⦄, HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      PosComboRealRooted f g → f.natDegree = g.natDegree + 1 → g.Splits :=
  fun _ _ hf_pos hg_pos hfg hsucc =>
    right_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Curried strict-implicit form of the lower-degree endpoint, packaged as
`≠ 0 ∧ Splits`. -/
theorem left_ne_zero_and_splits_closedSegment_of_succDegree_curried :
    ∀ ⦃f g : ℝ[X]⦄, HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      PosComboRealRooted f g → g.natDegree = f.natDegree + 1 →
      f ≠ 0 ∧ f.Splits :=
  fun _ _ hf_pos hg_pos hfg hsucc =>
    left_ne_zero_and_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Curried strict-implicit form of the higher-degree endpoint, packaged as
`≠ 0 ∧ Splits`. -/
theorem right_ne_zero_and_splits_closedSegment_of_succDegree_curried :
    ∀ ⦃f g : ℝ[X]⦄, HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      PosComboRealRooted f g → f.natDegree = g.natDegree + 1 →
      g ≠ 0 ∧ g.Splits :=
  fun _ _ hf_pos hg_pos hfg hsucc =>
    right_ne_zero_and_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-!
### Nonnegative-coefficient statement-shaped endpoint wrappers

The nonnegativity hypotheses below are threaded only to match the downstream
nonnegative succ-degree statement shapes.
-/

/-- Nonneg-shaped lower-degree endpoint wrapper. -/
theorem left_splits_nonneg_closedSegment_of_succDegree {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (_hfnn : HasNonnegCoeffs f) (_hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits :=
  left_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Nonneg-shaped higher-degree endpoint wrapper. -/
theorem right_splits_nonneg_closedSegment_of_succDegree {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (_hfnn : HasNonnegCoeffs f) (_hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g.Splits :=
  right_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Nonneg-shaped lower-degree endpoint wrapper packaged as `≠ 0 ∧ Splits`. -/
theorem left_ne_zero_and_splits_nonneg_closedSegment_of_succDegree {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (_hfnn : HasNonnegCoeffs f) (_hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f ≠ 0 ∧ f.Splits :=
  left_ne_zero_and_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Nonneg-shaped higher-degree endpoint wrapper packaged as `≠ 0 ∧ Splits`. -/
theorem right_ne_zero_and_splits_nonneg_closedSegment_of_succDegree {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (_hfnn : HasNonnegCoeffs f) (_hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g ≠ 0 ∧ g.Splits :=
  right_ne_zero_and_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Curried strict-implicit nonneg-shaped lower-degree endpoint. -/
theorem left_splits_nonneg_closedSegment_of_succDegree_curried :
    ∀ ⦃f g : ℝ[X]⦄, HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      HasNonnegCoeffs f → HasNonnegCoeffs g →
      PosComboRealRooted f g → g.natDegree = f.natDegree + 1 → f.Splits :=
  fun _ _ hf_pos hg_pos _ _ hfg hsucc =>
    left_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Curried strict-implicit nonneg-shaped higher-degree endpoint. -/
theorem right_splits_nonneg_closedSegment_of_succDegree_curried :
    ∀ ⦃f g : ℝ[X]⦄, HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      HasNonnegCoeffs f → HasNonnegCoeffs g →
      PosComboRealRooted f g → f.natDegree = g.natDegree + 1 → g.Splits :=
  fun _ _ hf_pos hg_pos _ _ hfg hsucc =>
    right_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Curried strict-implicit nonneg-shaped lower-degree endpoint with `≠ 0`. -/
theorem left_ne_zero_and_splits_nonneg_closedSegment_of_succDegree_curried :
    ∀ ⦃f g : ℝ[X]⦄, HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      HasNonnegCoeffs f → HasNonnegCoeffs g →
      PosComboRealRooted f g → g.natDegree = f.natDegree + 1 →
      f ≠ 0 ∧ f.Splits :=
  fun _ _ hf_pos hg_pos _ _ hfg hsucc =>
    left_ne_zero_and_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Curried strict-implicit nonneg-shaped higher-degree endpoint with `≠ 0`. -/
theorem right_ne_zero_and_splits_nonneg_closedSegment_of_succDegree_curried :
    ∀ ⦃f g : ℝ[X]⦄, HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      HasNonnegCoeffs f → HasNonnegCoeffs g →
      PosComboRealRooted f g → f.natDegree = g.natDegree + 1 →
      g ≠ 0 ∧ g.Splits :=
  fun _ _ hf_pos hg_pos _ _ hfg hsucc =>
    right_ne_zero_and_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-!
### Inclusive closed-segment endpoint wrappers

The succ-degree closed-segment statements in `CommonInterleaverTwo` phrase their
no-vanishing/splitting family hypothesis over the closed parameter interval
`0 ≤ β ≤ 1`.  The following wrappers accept exactly that inclusive form, so the
downstream statement shapes line up without first restricting to the open
interval.  They are thin reparametrizations of
`splits_of_closedSegment_family_of_succDegree`, introducing no new mathematics. -/

/-- Inclusive (closed-interval) form of the succ-degree left endpoint.  Identical
to `splits_of_closedSegment_family_of_succDegree` except the closed-segment
family hypothesis ranges over the closed interval `0 ≤ β ≤ 1`, matching the
`CommonInterleaverTwo` closed-segment statement shape. -/
theorem splits_of_closedSegmentIcc_family_of_succDegree {f g : ℝ[X]}
    (hfamily : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧ (C (1 - β) * f + C β * g).Splits))
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits :=
  splits_of_closedSegment_family_of_succDegree
    (fun {_} hβ0 hβ1 => hfamily hβ0.le hβ1.le) hf_pos hg_pos hsucc

/-- Inclusive (closed-interval) form of the succ-degree right endpoint, obtained
from the left form by the involution `β ↦ 1 - β` on the closed segment. -/
theorem splits_right_of_closedSegmentIcc_family_of_succDegree {f g : ℝ[X]}
    (hfamily : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧ (C (1 - β) * f + C β * g).Splits))
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g.Splits := by
  refine splits_of_closedSegmentIcc_family_of_succDegree (f := g) (g := f)
    (fun {β} hβ0 hβ1 => ?_) hg_pos hf_pos hsucc
  have h := hfamily (β := 1 - β) (by linarith) (by linarith)
  have he : C (1 - (1 - β)) * f + C (1 - β) * g = C (1 - β) * g + C β * f := by
    rw [sub_sub_cancel]
    ring
  rw [he] at h
  exact h

/-!
### Succ-degree endpoint root-count packages

These bundle the closed-segment endpoint-splitting facts with the corresponding
full real root-count equality `roots.card = natDegree` (via
`card_roots_of_splits`), the form consumed by the root-count leg of the direct
#42 route.  They introduce no new mathematics. -/

/-- Root-count package for the lower-degree endpoint: under the succ-degree
positive-combination hypotheses the lower-degree member `f` has a full real root
multiset. -/
theorem left_card_roots_of_succDegree {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.roots.card = f.natDegree :=
  card_roots_of_splits
    (left_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc)

/-- Root-count package for the higher-degree endpoint. -/
theorem right_card_roots_of_succDegree {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g.roots.card = g.natDegree :=
  card_roots_of_splits
    (right_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc)

/-- Root-count package for the lower-degree endpoint, packaged as the
`≠ 0 ∧ roots.card = natDegree` pair. -/
theorem left_ne_zero_and_card_roots_of_succDegree {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f ≠ 0 ∧ f.roots.card = f.natDegree :=
  ⟨hf_pos.ne_zero, left_card_roots_of_succDegree hf_pos hg_pos hfg hsucc⟩

/-- Root-count package for the higher-degree endpoint, packaged as the
`≠ 0 ∧ roots.card = natDegree` pair. -/
theorem right_ne_zero_and_card_roots_of_succDegree {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g ≠ 0 ∧ g.roots.card = g.natDegree :=
  ⟨hg_pos.ne_zero, right_card_roots_of_succDegree hf_pos hg_pos hfg hsucc⟩

/-- Closed-segment (inclusive) root-count package at the lower-degree endpoint. -/
theorem left_card_roots_of_closedSegmentIcc_family_of_succDegree {f g : ℝ[X]}
    (hfamily : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧ (C (1 - β) * f + C β * g).Splits))
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.roots.card = f.natDegree :=
  card_roots_of_splits
    (splits_of_closedSegmentIcc_family_of_succDegree hfamily hf_pos hg_pos hsucc)

/-- Closed-segment (inclusive) root-count package at the higher-degree endpoint. -/
theorem right_card_roots_of_closedSegmentIcc_family_of_succDegree {f g : ℝ[X]}
    (hfamily : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧ (C (1 - β) * f + C β * g).Splits))
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g.roots.card = g.natDegree :=
  card_roots_of_splits
    (splits_right_of_closedSegmentIcc_family_of_succDegree hfamily hf_pos hg_pos
      hsucc)

end RealRooted
