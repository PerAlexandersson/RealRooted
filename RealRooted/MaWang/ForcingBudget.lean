module

import RealRooted.MaWang.Weak.DerivativeSign
import RealRooted.Interlacing.OuterDifference
import RealRooted.Linear
public import RealRooted.SimpleRoots
public import RealRooted.EulerOperator

/-!
# Root-flux budgets for forced recurrences

The exact statewise criterion of the unpublished manuscript
`weyl-operators/notes/forcing-budget-weyl-recurrences.md`, §§1–3 (RealRooted #1879).
The current row must have simple roots. Arbitrary forcing at repeated roots is not covered;
use `LiuWang.strictInterl_derivative_lag_of_combined_flux` with its repeated-root gates instead.
The degree and leading-sign gates are retained even when the current row is constant.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Exact weak root-flux criterion for a simple split current row. Shared roots are allowed. -/
theorem strictInterl_iff_eval_mul_derivative_nonpos
    {f q : ℝ[X]} (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff q) (hlo : f.natDegree ≤ q.natDegree)
    (hhi : q.natDegree ≤ f.natDegree + 1) :
    StrictInterl f q ↔ ∀ r, f.IsRoot r → q.eval r * f.derivative.eval r ≤ 0 := by
  exact ⟨fun h _ hr => h.eval_mul_derivative_nonpos_of_left_root hf hq hr,
    strictInterl_of_eval_mul_derivative_nonpos hf hs hn hq hlo hhi⟩

/-- Strict root flux is exactly the coprime branch of the directed interlacing criterion. -/
theorem strictInterl_isCoprime_iff_eval_mul_derivative_neg
    {f q : ℝ[X]} (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff q) (hlo : f.natDegree ≤ q.natDegree)
    (hhi : q.natDegree ≤ f.natDegree + 1) :
    (StrictInterl f q ∧ IsCoprime f q) ↔
      ∀ r, f.IsRoot r → q.eval r * f.derivative.eval r < 0 := by
  constructor
  · rintro ⟨h, hc⟩ r hr
    exact h.eval_mul_derivative_neg_of_left_root_of_isCoprime hf hq hc hr
  · intro h
    have he := strictInterl_of_eval_mul_derivative_nonpos hf hs hn hq hlo hhi
      (fun r hr => (h r hr).le)
    refine ⟨he, isCoprime_of_no_common_real_root_of_isRealRooted hf.ne_zero hs ?_⟩
    intro r hr hqr
    have hneg := h r hr
    simp [hqr.eq_zero] at hneg

/-- Strict flux also gives simple roots of the output, including the constant-row boundary. -/
theorem hasSimpleRoots_of_eval_mul_derivative_neg
    {f q : ℝ[X]} (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff q) (hlo : f.natDegree ≤ q.natDegree)
    (hhi : q.natDegree ≤ f.natDegree + 1)
    (h : ∀ r, f.IsRoot r → q.eval r * f.derivative.eval r < 0) :
    HasSimpleRoots q := by
  obtain ⟨he, hc⟩ :=
    (strictInterl_isCoprime_iff_eval_mul_derivative_neg hf hs hn hq hlo hhi).2 h
  exact (he.hasSimpleRoots_of_isCoprime hc).2

/-- Division-free relative root-motion margin. It is valid for every real margin parameter;
nonnegative parameters measure rightward motion relative to the distance to the origin. -/
theorem strictInterl_sub_theta_iff {f q : ℝ[X]} {c : ℝ}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff (q - C c * theta f))
    (hlo : f.natDegree ≤ (q - C c * theta f).natDegree)
    (hhi : (q - C c * theta f).natDegree ≤ f.natDegree + 1) :
    StrictInterl f (q - C c * theta f) ↔
      ∀ r, f.IsRoot r → q.eval r * f.derivative.eval r ≤
        c * r * (f.derivative.eval r) ^ 2 := by
  rw [strictInterl_iff_eval_mul_derivative_nonpos hf hs hn hq hlo hhi]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  simp only [eval_sub, eval_mul, eval_C, theta, eval_X]
  constructor <;> intro h <;> nlinarith [h]

/-- Quotient form of the relative-motion criterion, using nonvanishing at simple roots. -/
theorem strictInterl_sub_theta_iff_div {f q : ℝ[X]} {c : ℝ}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff (q - C c * theta f))
    (hlo : f.natDegree ≤ (q - C c * theta f).natDegree)
    (hhi : (q - C c * theta f).natDegree ≤ f.natDegree + 1) :
    StrictInterl f (q - C c * theta f) ↔
      ∀ r, f.IsRoot r → c * (-r) ≤ -q.eval r / f.derivative.eval r := by
  rw [strictInterl_sub_theta_iff hf hs hn hq hlo hhi]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro hr
  have hd := (HasSimpleRoots.of_roots_nodup hf.ne_zero hn).eval_derivative_ne_zero hr
  have heq : -q.eval r / f.derivative.eval r =
      -(q.eval r * f.derivative.eval r) / (f.derivative.eval r) ^ 2 := by
    field_simp [hd]
  rw [heq, le_div_iff₀ (sq_pos_iff.mpr hd)]
  constructor <;> intro h <;> nlinarith [h]

/-- Adding any scalar multiple of the current row leaves its relative-motion margin unchanged.
Both corrected outputs retain their degree and leading-sign gates. -/
theorem strictInterl_add_C_mul_sub_theta_iff {f q : ℝ[X]} {a c : ℝ}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff (q - C c * theta f))
    (hlo : f.natDegree ≤ (q - C c * theta f).natDegree)
    (hhi : (q - C c * theta f).natDegree ≤ f.natDegree + 1)
    (hq' : HasPosLeadingCoeff (q + C a * f - C c * theta f))
    (hlo' : f.natDegree ≤ (q + C a * f - C c * theta f).natDegree)
    (hhi' : (q + C a * f - C c * theta f).natDegree ≤ f.natDegree + 1) :
    StrictInterl f (q + C a * f - C c * theta f) ↔
      StrictInterl f (q - C c * theta f) := by
  rw [strictInterl_sub_theta_iff hf hs hn hq' hlo' hhi',
    strictInterl_sub_theta_iff hf hs hn hq hlo hhi]
  simp only [eval_add, eval_mul, eval_C]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro hr
  simp [hr.eq_zero]

/-- Positive simultaneous scaling preserves the relative-motion margin.
The original and scaled corrected outputs each keep their degree and leading-sign gates. -/
theorem strictInterl_C_mul_sub_theta_iff {f q : ℝ[X]} {a c : ℝ} (ha : 0 < a)
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff (q - C c * theta f))
    (hlo : f.natDegree ≤ (q - C c * theta f).natDegree)
    (hhi : (q - C c * theta f).natDegree ≤ f.natDegree + 1)
    (hq' : HasPosLeadingCoeff (C a * q - C c * theta (C a * f)))
    (hlo' : (C a * f).natDegree ≤ (C a * q - C c * theta (C a * f)).natDegree)
    (hhi' : (C a * q - C c * theta (C a * f)).natDegree ≤ (C a * f).natDegree + 1) :
    StrictInterl (C a * f) (C a * q - C c * theta (C a * f)) ↔
      StrictInterl f (q - C c * theta f) := by
  have hn' : (C a * f).roots.Nodup := by rwa [roots_C_mul f ha.ne']
  rw [strictInterl_sub_theta_iff (hasPosLeadingCoeff_C_mul ha hf) (hs.C_mul a) hn'
    hq' hlo' hhi', strictInterl_sub_theta_iff hf hs hn hq hlo hhi]
  apply forall_congr'
  intro r
  have hr : (C a * f).IsRoot r ↔ f.IsRoot r := by simp [IsRoot.def, ha.ne']
  have hd : (C a * f).derivative.eval r = a * f.derivative.eval r := by
    simp [derivative_mul]
  rw [hr]
  apply imp_congr_right
  intro _
  simp only [eval_mul, eval_C, hd]
  rw [show a * q.eval r * (a * f.derivative.eval r) =
    (a * a) * (q.eval r * f.derivative.eval r) by ring]
  rw [show c * r * (a * f.derivative.eval r) ^ 2 =
    (a * a) * (c * r * (f.derivative.eval r) ^ 2) by ring]
  exact mul_le_mul_iff_right₀ (mul_pos ha ha)

/-- Relative-motion margins decrease monotonically for PF current rows.
The corrected outputs keep explicit degree and leading-sign gates. -/
theorem strictInterl_sub_theta_of_le {f q : ℝ[X]} {c c' : ℝ}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hfnn : HasNonnegCoeffs f) (hcc : c' ≤ c)
    (hq : HasPosLeadingCoeff (q - C c * theta f))
    (hlo : f.natDegree ≤ (q - C c * theta f).natDegree)
    (hhi : (q - C c * theta f).natDegree ≤ f.natDegree + 1)
    (hq' : HasPosLeadingCoeff (q - C c' * theta f))
    (hlo' : f.natDegree ≤ (q - C c' * theta f).natDegree)
    (hhi' : (q - C c' * theta f).natDegree ≤ f.natDegree + 1)
    (he : StrictInterl f (q - C c * theta f)) :
    StrictInterl f (q - C c' * theta f) := by
  apply (strictInterl_sub_theta_iff hf hs hn hq' hlo' hhi').2
  intro r hr
  have hflux := (strictInterl_sub_theta_iff hf hs hn hq hlo hhi).1 he r hr
  have hr0 := roots_nonpos_of_hasNonnegCoeffs hfnn r ((mem_roots hf.ne_zero).2 hr)
  exact hflux.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonpos_right hcc hr0) (sq_nonneg _))

namespace ForcingBudget

variable {ι : Type*} {f q H : ℝ[X]} {s : Finset ι} {g : ι → ℝ[X]}
  {v : ℝ → ℝ} {ell : ι → ℝ → ℝ}

/-- At a root, the pointwise recurrence identity expands to the division-free flux budget. -/
theorem eval_mul_derivative_eq
    (hrec : ∀ r, f.IsRoot r → q.eval r = v r * f.derivative.eval r +
      ∑ i ∈ s, ell i r * (g i).eval r + H.eval r)
    {r : ℝ} (hr : f.IsRoot r) :
    q.eval r * f.derivative.eval r =
      v r * (f.derivative.eval r) ^ 2 +
        ∑ i ∈ s, ell i r * (g i).eval r * f.derivative.eval r +
        H.eval r * f.derivative.eval r := by
  rw [hrec r hr, add_mul, add_mul, Finset.sum_mul]
  ring

/-- Exact finite-family forcing budget, allowing arbitrary real-valued root coefficients. -/
theorem strictInterl_iff_of_root_identity
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff q) (hlo : f.natDegree ≤ q.natDegree)
    (hhi : q.natDegree ≤ f.natDegree + 1)
    (hrec : ∀ r, f.IsRoot r → q.eval r = v r * f.derivative.eval r +
      ∑ i ∈ s, ell i r * (g i).eval r + H.eval r) :
    StrictInterl f q ↔ ∀ r, f.IsRoot r →
      H.eval r * f.derivative.eval r ≤
        -(v r * (f.derivative.eval r) ^ 2 +
          ∑ i ∈ s, ell i r * (g i).eval r * f.derivative.eval r) := by
  rw [strictInterl_iff_eval_mul_derivative_nonpos hf hs hn hq hlo hhi]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro hr
  rw [eval_mul_derivative_eq hrec hr]
  constructor <;> intro h <;> linarith

/-- Strict finite-family forcing budget, with coprimality as part of the exact conclusion. -/
theorem strictInterl_isCoprime_iff_of_root_identity
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff q) (hlo : f.natDegree ≤ q.natDegree)
    (hhi : q.natDegree ≤ f.natDegree + 1)
    (hrec : ∀ r, f.IsRoot r → q.eval r = v r * f.derivative.eval r +
      ∑ i ∈ s, ell i r * (g i).eval r + H.eval r) :
    (StrictInterl f q ∧ IsCoprime f q) ↔ ∀ r, f.IsRoot r →
      H.eval r * f.derivative.eval r <
        -(v r * (f.derivative.eval r) ^ 2 +
          ∑ i ∈ s, ell i r * (g i).eval r * f.derivative.eval r) := by
  rw [strictInterl_isCoprime_iff_eval_mul_derivative_neg hf hs hn hq hlo hhi]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro hr
  rw [eval_mul_derivative_eq hrec hr]
  constructor <;> intro h <;> linarith

/-- A polynomial recurrence supplies the pointwise identity; its current-row term vanishes. -/
theorem root_identity_of_recurrence {U V : ℝ[X]} {L : ι → ℝ[X]}
    (hrec : q = U * f + V * f.derivative + ∑ i ∈ s, L i * g i + H)
    {r : ℝ} (hr : f.IsRoot r) :
    q.eval r = V.eval r * f.derivative.eval r +
      ∑ i ∈ s, (L i).eval r * (g i).eval r + H.eval r := by
  simp [hrec, eval_add, eval_mul, eval_finsetSum, hr.eq_zero]

/-- Exact polynomial finite-family recurrence budget. No coefficient signs are needed. -/
theorem strictInterl_iff_of_recurrence {U V : ℝ[X]} {L : ι → ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff q) (hlo : f.natDegree ≤ q.natDegree)
    (hhi : q.natDegree ≤ f.natDegree + 1)
    (hrec : q = U * f + V * f.derivative + ∑ i ∈ s, L i * g i + H) :
    StrictInterl f q ↔ ∀ r, f.IsRoot r →
      H.eval r * f.derivative.eval r ≤
        -(V.eval r * (f.derivative.eval r) ^ 2 +
          ∑ i ∈ s, (L i).eval r * (g i).eval r * f.derivative.eval r) := by
  exact strictInterl_iff_of_root_identity hf hs hn hq hlo hhi
    (fun _ hr => root_identity_of_recurrence hrec hr)

/-- Strict polynomial finite-family recurrence budget. -/
theorem strictInterl_isCoprime_iff_of_recurrence {U V : ℝ[X]} {L : ι → ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff q) (hlo : f.natDegree ≤ q.natDegree)
    (hhi : q.natDegree ≤ f.natDegree + 1)
    (hrec : q = U * f + V * f.derivative + ∑ i ∈ s, L i * g i + H) :
    (StrictInterl f q ∧ IsCoprime f q) ↔ ∀ r, f.IsRoot r →
      H.eval r * f.derivative.eval r <
        -(V.eval r * (f.derivative.eval r) ^ 2 +
          ∑ i ∈ s, (L i).eval r * (g i).eval r * f.derivative.eval r) := by
  exact strictInterl_isCoprime_iff_of_root_identity hf hs hn hq hlo hhi
    (fun _ hr => root_identity_of_recurrence hrec hr)

/-- Exact weak budget for a single polynomial lag. -/
theorem strictInterl_iff_of_one_lag {f q g U V L H : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff q) (hlo : f.natDegree ≤ q.natDegree)
    (hhi : q.natDegree ≤ f.natDegree + 1)
    (hrec : q = U * f + V * f.derivative + L * g + H) :
    StrictInterl f q ↔ ∀ r, f.IsRoot r →
      H.eval r * f.derivative.eval r ≤
        -(V.eval r * (f.derivative.eval r) ^ 2 + L.eval r * g.eval r * f.derivative.eval r) := by
  simpa using strictInterl_iff_of_recurrence (s := Finset.univ)
    (g := fun _ : Unit => g) (L := fun _ : Unit => L) hf hs hn hq hlo hhi (by simpa using hrec)

/-- Exact strict budget for a single polynomial lag. -/
theorem strictInterl_isCoprime_iff_of_one_lag {f q g U V L H : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff q) (hlo : f.natDegree ≤ q.natDegree)
    (hhi : q.natDegree ≤ f.natDegree + 1)
    (hrec : q = U * f + V * f.derivative + L * g + H) :
    (StrictInterl f q ∧ IsCoprime f q) ↔ ∀ r, f.IsRoot r →
      H.eval r * f.derivative.eval r <
        -(V.eval r * (f.derivative.eval r) ^ 2 + L.eval r * g.eval r * f.derivative.eval r) := by
  simpa using strictInterl_isCoprime_iff_of_recurrence (s := Finset.univ)
    (g := fun _ : Unit => g) (L := fun _ : Unit => L) hf hs hn hq hlo hhi (by simpa using hrec)

/-- At a positive derivative, the strict one-lag budget keeps the entire favorable lag margin. -/
theorem budget_lt_iff_of_pos {D : ℝ} (hD : 0 < D) (H v lag : ℝ) :
    H * D < -(v * D ^ 2 + lag * D) ↔ H < -v * D - lag := by
  rw [show -(v * D ^ 2 + lag * D) = (-v * D - lag) * D by ring]
  exact mul_lt_mul_iff_left₀ hD

/-- At a negative derivative, dividing the budget reverses its inequality. -/
theorem budget_lt_iff_of_neg {D : ℝ} (hD : D < 0) (H v lag : ℝ) :
    H * D < -(v * D ^ 2 + lag * D) ↔ -v * D - lag < H := by
  rw [show -(v * D ^ 2 + lag * D) = (-v * D - lag) * D by ring]
  exact mul_lt_mul_right_of_neg hD

/-- Each lag-to-current edge supplies a nonnegative margin; no lag-to-lag edges are used. -/
theorem margin_nonneg (hf : HasPosLeadingCoeff f)
    (hg : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (he : ∀ i ∈ s, StrictInterl (g i) f) {r : ℝ} (hr : f.IsRoot r)
    (hv : v r ≤ 0) (hl : ∀ i ∈ s, ell i r ≤ 0) :
    0 ≤ -(v r * (f.derivative.eval r) ^ 2 +
      ∑ i ∈ s, ell i r * (g i).eval r * f.derivative.eval r) := by
  apply neg_nonneg.mpr
  apply add_nonpos (mul_nonpos_of_nonpos_of_nonneg hv (sq_nonneg _))
  apply Finset.sum_nonpos
  intro i hi
  rw [mul_assoc]
  exact mul_nonpos_of_nonpos_of_nonneg (hl i hi)
    ((he i hi).eval_mul_eval_derivative_nonneg (hg i hi) hf hr)

/-- Only adverse forcing roots require a quantitative weak budget. -/
theorem strictInterl_of_adverse_roots
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff q) (hlo : f.natDegree ≤ q.natDegree)
    (hhi : q.natDegree ≤ f.natDegree + 1)
    (hrec : ∀ r, f.IsRoot r → q.eval r = v r * f.derivative.eval r +
      ∑ i ∈ s, ell i r * (g i).eval r + H.eval r)
    (hg : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (he : ∀ i ∈ s, StrictInterl (g i) f)
    (hv : ∀ r, f.IsRoot r → v r ≤ 0)
    (hl : ∀ r, f.IsRoot r → ∀ i ∈ s, ell i r ≤ 0)
    (hbudget : ∀ r, f.IsRoot r → 0 < H.eval r * f.derivative.eval r →
      H.eval r * f.derivative.eval r ≤
        -(v r * (f.derivative.eval r) ^ 2 +
          ∑ i ∈ s, ell i r * (g i).eval r * f.derivative.eval r)) :
    StrictInterl f q := by
  apply (strictInterl_iff_of_root_identity hf hs hn hq hlo hhi hrec).2
  intro r hr
  by_cases ha : 0 < H.eval r * f.derivative.eval r
  · exact hbudget r hr ha
  · exact (le_of_not_gt ha).trans (margin_nonneg hf hg he hr (hv r hr) (hl r hr))

/-- With a strictly negative derivative coefficient, nonadverse roots have strict slack.
An adverse-root strict budget gives coprimality and simple output roots. -/
theorem strictInterl_isCoprime_of_adverse_roots
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff q) (hlo : f.natDegree ≤ q.natDegree)
    (hhi : q.natDegree ≤ f.natDegree + 1)
    (hrec : ∀ r, f.IsRoot r → q.eval r = v r * f.derivative.eval r +
      ∑ i ∈ s, ell i r * (g i).eval r + H.eval r)
    (hg : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (he : ∀ i ∈ s, StrictInterl (g i) f)
    (hv : ∀ r, f.IsRoot r → v r < 0)
    (hl : ∀ r, f.IsRoot r → ∀ i ∈ s, ell i r ≤ 0)
    (hbudget : ∀ r, f.IsRoot r → 0 < H.eval r * f.derivative.eval r →
      H.eval r * f.derivative.eval r <
        -(v r * (f.derivative.eval r) ^ 2 +
          ∑ i ∈ s, ell i r * (g i).eval r * f.derivative.eval r)) :
    StrictInterl f q ∧ IsCoprime f q ∧ HasSimpleRoots q := by
  have hb : ∀ r, f.IsRoot r →
      H.eval r * f.derivative.eval r <
        -(v r * (f.derivative.eval r) ^ 2 +
          ∑ i ∈ s, ell i r * (g i).eval r * f.derivative.eval r) := by
    intro r hr
    by_cases ha : 0 < H.eval r * f.derivative.eval r
    · exact hbudget r hr ha
    · have hder := (HasSimpleRoots.of_roots_nodup hf.ne_zero hn).eval_derivative_ne_zero hr
      have hstrict := mul_neg_of_neg_of_pos (hv r hr) (sq_pos_iff.mpr hder)
      have hlag : (∑ i ∈ s, ell i r * (g i).eval r * f.derivative.eval r) ≤ 0 := by
        apply Finset.sum_nonpos
        intro i hi
        rw [mul_assoc]
        exact mul_nonpos_of_nonpos_of_nonneg (hl r hr i hi)
          ((he i hi).eval_mul_eval_derivative_nonneg (hg i hi) hf hr)
      linarith [le_of_not_gt ha]
  obtain ⟨he, hc⟩ :=
    (strictInterl_isCoprime_iff_of_root_identity hf hs hn hq hlo hhi hrec).2 hb
  exact ⟨he, hc, (he.hasSimpleRoots_of_isCoprime hc).2⟩

end ForcingBudget
end RealRooted
