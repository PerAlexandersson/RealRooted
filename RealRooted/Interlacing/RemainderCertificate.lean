module

public import RealRooted.Basic.ProperPosition
public import RealRooted.Interlacing.Euclid
public import RealRooted.Mathlib.Algebra.Polynomial.Splits

/-!
# Interlacing from a division remainder

For a quadratic `R = a X² + b X + c` with `a > 0` and a cubic written as
`R * (p X + d) + (α X + β)` with `p > 0`, the cubic strictly interlaces `R` when `α < 0` and
`a β² - b α β + c α² < 0`;
the second condition says `R (-β / α) < 0`, so the root of the remainder lies strictly between the
roots of `R` (`strictInterl_quadratic_of_remainder`). The linear analogue needs only `β < 0`
(`strictInterl_linear_of_remainder`). Multiplying both rows by powers of a common real-rooted
factor `q` gives interlacing of `q ^ m * R` and `q ^ (m + 1) * S` from a certificate for `q * S`
(`Interlaces.pow_mul_of_quadratic_remainder`, `Interlaces.pow_mul_of_linear_remainder`): rows of
order-three recurrences with characteristic polynomial `(λ - q)³` have this shape.

The explicit root bracketing was found by Aristotle and ported here.
-/

@[expose] public section

open Polynomial Filter

namespace RealRooted

private lemma odd_tendsto (P : ℝ[X]) (hd : P.natDegree = 3)
    (hl : 0 < P.leadingCoeff) (M : ℝ) :
    (∃ x < M, P.eval x < 0) ∧ (∃ x > M, 0 < P.eval x) := by
  constructor
  · have hdeg : 0 < (P.comp (-X)).degree := by
      exact natDegree_pos_iff_degree_pos.mp (by simp [natDegree_comp, hd])
    have hlc : (P.comp (-X)).leadingCoeff ≤ 0 := by
      rw [leadingCoeff_comp (by simp)]
      simp [hd]
      linarith
    have := tendsto_atBot_of_leadingCoeff_nonpos _ hdeg hlc
    obtain ⟨y, hy⟩ :=
      ((this.eventually (eventually_lt_atBot 0)).and
        (eventually_gt_atTop (-M))).exists
    refine ⟨-y, by linarith [hy.2], ?_⟩
    simpa using hy.1
  · have hdeg : 0 < P.degree := by
      exact natDegree_pos_iff_degree_pos.mp (by simp [hd])
    have := tendsto_atTop_of_leadingCoeff_nonneg _ hdeg hl.le
    obtain ⟨y, hy⟩ :=
      ((this.eventually (eventually_gt_atTop 0)).and
        (eventually_gt_atTop M)).exists
    exact ⟨y, hy.2, hy.1⟩

private lemma even_tendsto (P : ℝ[X]) (hd : P.natDegree = 2)
    (hl : 0 < P.leadingCoeff) (M : ℝ) :
    (∃ x < M, 0 < P.eval x) ∧ (∃ x > M, 0 < P.eval x) := by
  constructor
  · have hdeg : 0 < (P.comp (-X)).degree := by
      exact natDegree_pos_iff_degree_pos.mp (by simp [natDegree_comp, hd])
    have hlc : 0 ≤ (P.comp (-X)).leadingCoeff := by
      rw [leadingCoeff_comp (by simp)]
      simp [hd]
      linarith
    have := tendsto_atTop_of_leadingCoeff_nonneg _ hdeg hlc
    obtain ⟨y, hy⟩ :=
      ((this.eventually (eventually_gt_atTop 0)).and
        (eventually_gt_atTop (-M))).exists
    refine ⟨-y, by linarith [hy.2], ?_⟩
    simpa using hy.1
  · have hdeg : 0 < P.degree := by
      exact natDegree_pos_iff_degree_pos.mp (by simp [hd])
    have := tendsto_atTop_of_leadingCoeff_nonneg _ hdeg hl.le
    obtain ⟨y, hy⟩ :=
      ((this.eventually (eventually_gt_atTop 0)).and
        (eventually_gt_atTop M)).exists
    exact ⟨y, hy.2, hy.1⟩

private theorem quadratic_cubic_roots_of_remainder {a b c p d α β : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hα : α < 0)
    (hcert : a * β ^ 2 - b * α * β + c * α ^ 2 < 0) :
    let f : ℝ[X] := C a * X ^ 2 + C b * X + C c
    let g : ℝ[X] := f * (C p * X + C d) + (C α * X + C β)
    ∃ r₁ r₂ s₁ s₂ s₃ : ℝ,
      s₁ < r₁ ∧ r₁ < s₂ ∧ s₂ < r₂ ∧ r₂ < s₃ ∧
      f.IsRoot r₁ ∧ f.IsRoot r₂ ∧ g.IsRoot s₁ ∧ g.IsRoot s₂ ∧ g.IsRoot s₃ := by
  intro f g
  have hfe : ∀ x, f.eval x = a * x ^ 2 + b * x + c := by
    intro x
    simp [f]
  have hge : ∀ x, g.eval x =
      (a * x ^ 2 + b * x + c) * (p * x + d) + (α * x + β) := by
    intro x
    simp [g, f]
  have hap : a * p ≠ 0 := by positivity
  have hgform : g = C (a * p) * X ^ 3 + C (a * d + b * p) * X ^ 2 +
      C (b * d + c * p + α) * X + C (c * d + β) := by
    simp only [g, f, C_mul, C_add]
    ring
  have hgdeg : g.natDegree = 3 := by
    rw [hgform]
    exact natDegree_cubic hap
  have hglc : 0 < g.leadingCoeff := by
    rw [hgform, leadingCoeff_cubic hap]
    positivity
  have hα2 : 0 < α ^ 2 := by nlinarith
  have hDα : 0 < α ^ 2 * (b ^ 2 - 4 * a * c) := by
    nlinarith [sq_nonneg (2 * a * β - b * α)]
  have hD : 0 < b ^ 2 - 4 * a * c :=
    (pos_iff_pos_of_mul_pos hDα).mp hα2
  set s := Real.sqrt (b ^ 2 - 4 * a * c) with hs_def
  have hs : s ^ 2 = b ^ 2 - 4 * a * c := Real.sq_sqrt hD.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hD
  set r₁ := (-b - s) / (2 * a) with hr₁
  set r₂ := (-b + s) / (2 * a) with hr₂
  have ha0 : a ≠ 0 := ha.ne'
  have hsum : a * (r₁ + r₂) = -b := by
    rw [hr₁, hr₂]
    field_simp
    ring
  have hprod : a * (r₁ * r₂) = c := by
    rw [hr₁, hr₂]
    field_simp
    linear_combination (-1 : ℝ) * hs
  have hlt : r₁ < r₂ := by
    rw [hr₁, hr₂]
    apply div_lt_div_of_pos_right _ (by positivity)
    linarith
  have hroot1 : a * r₁ ^ 2 + b * r₁ + c = 0 := by
    linear_combination r₁ * hsum - hprod
  have hroot2 : a * r₂ ^ 2 + b * r₂ + c = 0 := by
    linear_combination r₂ * hsum - hprod
  have hP : a * ((α * r₁ + β) * (α * r₂ + β)) < 0 := by
    have : a * ((α * r₁ + β) * (α * r₂ + β)) =
        α ^ 2 * (a * (r₁ * r₂)) + α * β * (a * (r₁ + r₂)) + a * β ^ 2 := by
      ring
    rw [this, hprod, hsum]
    linarith
  have hP' : (α * r₁ + β) * (α * r₂ + β) < 0 := by
    by_contra h
    push Not at h
    nlinarith
  have hgap : α * r₂ + β < α * r₁ + β := by nlinarith
  have hg1 : 0 < g.eval r₁ := by
    rw [hge, hroot1]
    nlinarith
  have hg2 : g.eval r₂ < 0 := by
    rw [hge, hroot2]
    nlinarith
  obtain ⟨x₁, hx₁, hgx₁⟩ := (odd_tendsto g hgdeg hglc r₁).1
  obtain ⟨x₃', hx₃', hgx₃'⟩ := (odd_tendsto g hgdeg hglc r₂).2
  have hcont : ∀ u v : ℝ, ContinuousOn (fun x => g.eval x) (Set.Icc u v) :=
    fun _ _ => g.continuous.continuousOn
  obtain ⟨s₁, ⟨hs₁a, hs₁b⟩, hs₁⟩ :=
    intermediate_value_Ioo hx₁.le (hcont _ _)
      (show (0 : ℝ) ∈ Set.Ioo _ _ from ⟨hgx₁, hg1⟩)
  obtain ⟨s₂, ⟨hs₂a, hs₂b⟩, hs₂⟩ :=
    intermediate_value_Ioo' hlt.le (hcont _ _)
      (show (0 : ℝ) ∈ Set.Ioo _ _ from ⟨hg2, hg1⟩)
  obtain ⟨s₃, ⟨hs₃a, hs₃b⟩, hs₃⟩ :=
    intermediate_value_Ioo hx₃'.le (hcont _ _)
      (show (0 : ℝ) ∈ Set.Ioo _ _ from ⟨hg2, hgx₃'⟩)
  refine ⟨r₁, r₂, s₁, s₂, s₃, hs₁b, hs₂a, hs₂b, hs₃a,
    ?_, ?_, hs₁, hs₂, hs₃⟩
  · change f.eval r₁ = 0
    rw [hfe]
    exact hroot1
  · change f.eval r₂ = 0
    rw [hfe]
    exact hroot2

private theorem linear_quadratic_roots_of_remainder {a b p d β : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hβ : β < 0) :
    let f : ℝ[X] := C a * X + C b
    let g : ℝ[X] := f * (C p * X + C d) + C β
    ∃ r s₁ s₂ : ℝ,
      s₁ < r ∧ r < s₂ ∧ f.IsRoot r ∧ g.IsRoot s₁ ∧ g.IsRoot s₂ := by
  intro f g
  have hfe : ∀ x, f.eval x = a * x + b := by
    intro x
    simp [f]
  have hge : ∀ x, g.eval x = (a * x + b) * (p * x + d) + β := by
    intro x
    simp [g, f]
  have hap : a * p ≠ 0 := by positivity
  have hgform : g = C (a * p) * X ^ 2 + C (a * d + b * p) * X + C (b * d + β) := by
    simp only [g, f, C_mul, C_add]
    ring
  have hgdeg : g.natDegree = 2 := by
    rw [hgform]
    exact natDegree_quadratic hap
  have hglc : 0 < g.leadingCoeff := by
    rw [hgform, leadingCoeff_quadratic hap]
    positivity
  set r := -b / a with hr
  have hroot : a * r + b = 0 := by
    rw [hr]
    field_simp
    ring
  have hgr : g.eval r < 0 := by
    rw [hge, hroot]
    simpa using hβ
  obtain ⟨⟨x₁, hx₁, hgx₁⟩, ⟨x₂, hx₂, hgx₂⟩⟩ :=
    (even_tendsto g hgdeg hglc r)
  have hcont : ∀ u v : ℝ, ContinuousOn (fun x => g.eval x) (Set.Icc u v) :=
    fun _ _ => g.continuous.continuousOn
  obtain ⟨s₁, ⟨hs₁a, hs₁b⟩, hs₁⟩ :=
    intermediate_value_Ioo' hx₁.le (hcont _ _)
      (show (0 : ℝ) ∈ Set.Ioo _ _ from ⟨hgr, hgx₁⟩)
  obtain ⟨s₂, ⟨hs₂a, hs₂b⟩, hs₂⟩ :=
    intermediate_value_Ioo hx₂.le (hcont _ _)
      (show (0 : ℝ) ∈ Set.Ioo _ _ from ⟨hgr, hgx₂⟩)
  refine ⟨r, s₁, s₂, hs₁b, hs₂a, ?_, hs₁, hs₂⟩
  change f.eval r = 0
  rw [hfe]
  exact hroot

private lemma roots_eq_of_list_roots {p : ℝ[X]} {xs : List ℝ}
    (hp : p ≠ 0) (hps : p.Splits) (hxs : xs.Nodup)
    (hroot : ∀ x ∈ xs, p.IsRoot x) (hcard : p.natDegree = xs.length) :
    (↑xs : Multiset ℝ) = p.roots := by
  have hsub : (↑xs : Multiset ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_subset (by simpa using hxs)]
    intro x hx
    exact (mem_roots hp).mpr (hroot x (by simpa using hx))
  apply Multiset.eq_of_le_of_card_le hsub
  rw [Polynomial.splits_iff_card_roots.mp hps, hcard]
  simp

/-- Remainder certificates for an affine perturbation of a linear polynomial. -/
theorem strictInterl_linear_of_remainder {a b p d β : ℝ} (ha : 0 < a)
    (hp : 0 < p) (hβ : β < 0) :
    StrictInterl (C a * X + C b)
      ((C a * X + C b) * (C p * X + C d) + C β) := by
  let f : ℝ[X] := C a * X + C b
  let g : ℝ[X] := f * (C p * X + C d) + C β
  obtain ⟨r, s₁, s₂, hs₁r, hrs₂, hfr, hgs₁, hgs₂⟩ :=
    linear_quadratic_roots_of_remainder ha hp hβ
  have hfr' : f.IsRoot r := by simpa [f] using hfr
  have hgs₁' : g.IsRoot s₁ := by simpa [g, f] using hgs₁
  have hgs₂' : g.IsRoot s₂ := by simpa [g, f] using hgs₂
  have hfgdeg : f.natDegree = 1 := by simp [f, ha.ne']
  have hggdeg : g.natDegree = 2 := by
    have hform : g = C (a * p) * X ^ 2 + C (a * d + b * p) * X + C (b * d + β) := by
      simp only [g, f, C_mul, C_add]
      ring
    rw [hform]
    exact natDegree_quadratic (mul_ne_zero ha.ne' hp.ne')
  have hfn : f ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by rw [hfgdeg]; norm_num)
  have hgn : g ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by rw [hggdeg]; norm_num)
  have hfs : f.Splits := Splits.of_natDegree_le_one (by rw [hfgdeg])
  have hgs : g.Splits := by
    apply Polynomial.splits_of_finset_roots_of_natDegree_le_card
      (s := {s₁, s₂})
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hgs₁'
      · exact hgs₂'
    · rw [hggdeg]
      have hs₁s₂ : s₁ ≠ s₂ := ne_of_lt (lt_trans hs₁r hrs₂)
      simp [hs₁s₂]
  have hfrts : (↑[r] : Multiset ℝ) = f.roots := by
    apply roots_eq_of_list_roots hfn hfs <;> simp_all
  have hgrts : (↑[s₁, s₂] : Multiset ℝ) = g.roots := by
    have hs₁s₂ : s₁ ≠ s₂ := ne_of_lt (lt_trans hs₁r hrs₂)
    apply roots_eq_of_list_roots hgn hgs <;> simp_all
  refine ⟨⟨hfn, hfs⟩, ⟨hgn, hgs⟩, [r], [s₁, s₂], by simp, ?_, ?_, ?_, ?_⟩
  · simp [le_of_lt (lt_trans hs₁r hrs₂)]
  · exact hfrts
  · exact hgrts
  · exact Or.inl ⟨by simp, ⟨hs₁r.le, hrs₂.le, by simp [ListInterlaces]⟩⟩

/-- Remainder certificates for an affine perturbation of a quadratic polynomial. -/
theorem strictInterl_quadratic_of_remainder {a b c p d α β : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hα : α < 0)
    (hcert : a * β ^ 2 - b * α * β + c * α ^ 2 < 0) :
    StrictInterl (C a * X ^ 2 + C b * X + C c)
      ((C a * X ^ 2 + C b * X + C c) * (C p * X + C d) +
        (C α * X + C β)) := by
  obtain ⟨r₁, r₂, s₁, s₂, s₃, hs₁r₁, hr₁s₂, hs₂r₂, hr₂s₃,
      hfr₁, hfr₂, hgs₁, hgs₂, hgs₃⟩ :=
    quadratic_cubic_roots_of_remainder ha hp hα hcert
  let f : ℝ[X] := C a * X ^ 2 + C b * X + C c
  let g : ℝ[X] := f * (C p * X + C d) + (C α * X + C β)
  have hfdeg : f.natDegree = 2 := by
    rw [show f = C a * X ^ 2 + C b * X + C c by rfl]
    exact natDegree_quadratic ha.ne'
  have hgdeg : g.natDegree = 3 := by
    rw [show g = C (a * p) * X ^ 3 + C (a * d + b * p) * X ^ 2 +
      C (b * d + c * p + α) * X + C (c * d + β) by
      simp only [g, f, C_mul, C_add]
      ring]
    exact natDegree_cubic (mul_ne_zero ha.ne' hp.ne')
  have hfr₁' : f.IsRoot r₁ := by simpa [f] using hfr₁
  have hfr₂' : f.IsRoot r₂ := by simpa [f] using hfr₂
  have hgs₁' : g.IsRoot s₁ := by simpa [g, f] using hgs₁
  have hgs₂' : g.IsRoot s₂ := by simpa [g, f] using hgs₂
  have hgs₃' : g.IsRoot s₃ := by simpa [g, f] using hgs₃
  have hfn : f ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by rw [hfdeg]; norm_num)
  have hgn : g ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by rw [hgdeg]; norm_num)
  have hfs : f.Splits := by
    apply Polynomial.splits_of_finset_roots_of_natDegree_le_card
      (s := {r₁, r₂})
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hfr₁'
      · exact hfr₂'
    · have hr₁r₂ : r₁ ≠ r₂ := ne_of_lt (lt_trans hr₁s₂ hs₂r₂)
      rw [hfdeg]
      simp [hr₁r₂]
  have hgs : g.Splits := by
    apply Polynomial.splits_of_finset_roots_of_natDegree_le_card
      (s := {s₁, s₂, s₃})
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hgs₁'
      · exact hgs₂'
      · exact hgs₃'
    · rw [hgdeg]
      have hs₁s₂ : s₁ < s₂ := lt_trans hs₁r₁ hr₁s₂
      have hs₂s₃ : s₂ < s₃ := lt_trans hs₂r₂ hr₂s₃
      have hs₁s₃ : s₁ < s₃ := lt_trans hs₁s₂ hs₂s₃
      simp [hs₁s₂.ne, hs₂s₃.ne, hs₁s₃.ne]
  have hr₁r₂ : r₁ ≠ r₂ := ne_of_lt (lt_trans hr₁s₂ hs₂r₂)
  have hfrts : (↑[r₁, r₂] : Multiset ℝ) = f.roots := by
    apply roots_eq_of_list_roots hfn hfs <;> simp_all
  have hgrts : (↑[s₁, s₂, s₃] : Multiset ℝ) = g.roots := by
    have hs₁s₂' : s₁ < s₂ := lt_trans hs₁r₁ hr₁s₂
    have hs₂s₃' : s₂ < s₃ := lt_trans hs₂r₂ hr₂s₃
    have hs₁s₃' : s₁ < s₃ := lt_trans hs₁s₂' hs₂s₃'
    exact roots_eq_of_list_roots hgn hgs
      (by simp [hs₁s₂'.ne, hs₁s₃'.ne, hs₂s₃'.ne]) (by simp_all) (by simp [hgdeg])
  apply Interlaces.toStrictInterl
  apply Interlaces.of_quadratic_cubic_root_lists
    (g := f) (f := g) hgn hgs hfn hfs
    hgdeg hfdeg
    (by simpa using hgrts.symm) (by simpa using hfrts.symm)
    (le_of_lt (lt_trans hs₁r₁ hr₁s₂))
    (le_of_lt (lt_trans hs₂r₂ hr₂s₃))
    (le_of_lt (lt_trans hr₁s₂ hs₂r₂))
    (le_of_lt hs₁r₁) (le_of_lt hr₁s₂) (le_of_lt hs₂r₂) (le_of_lt hr₂s₃)

/-- Rows `q ^ m * R` and `q ^ (m + 1) * S` interlace when `q * S` leaves a
remainder certificate after division by the quadratic `R`. -/
theorem Interlaces.pow_mul_of_quadratic_remainder {q R S : ℝ[X]} (m : ℕ)
    {a b c p d α β : ℝ} (hR : R = C a * X ^ 2 + C b * X + C c)
    (hqS : q * S = R * (C p * X + C d) + (C α * X + C β))
    (hq : q.Splits) (hq0 : q ≠ 0) (ha : 0 < a) (hp : 0 < p) (hα : α < 0)
    (hcert : a * β ^ 2 - b * α * β + c * α ^ 2 < 0) :
    Interlaces (q ^ m * R) (q ^ (m + 1) * S) := by
  have hbase := strictInterl_quadratic_of_remainder (a := a) (b := b) (c := c)
    (p := p) (d := d) (α := α) (β := β) ha hp hα hcert
  have hstrict : StrictInterl R (q * S) := by
    rw [hR, hqS, hR]
    exact hbase
  have hRdeg : R.natDegree = 2 := by rw [hR]; exact natDegree_quadratic ha.ne'
  have hqSform : q * S =
      C (a * p) * X ^ 3 + C (a * d + b * p) * X ^ 2 +
        C (b * d + c * p + α) * X + C (c * d + β) := by
    rw [hqS, hR]; simp only [C_mul, C_add]; ring
  have hqSdeg : (q * S).natDegree = 3 := by
    rw [hqSform]; exact natDegree_cubic (mul_ne_zero ha.ne' hp.ne')
  have hdeg : R.natDegree + 1 = (q * S).natDegree := by rw [hRdeg, hqSdeg]
  have hmul := (hstrict.toInterlaces hdeg).mul_both_of_splits (hq.pow m)
    (pow_ne_zero m hq0)
  simpa [pow_succ, mul_assoc] using hmul

/-- Rows `q ^ m * R` and `q ^ (m + 1) * S` interlace when `q * S` leaves a
remainder certificate after division by the linear polynomial `R`. -/
theorem Interlaces.pow_mul_of_linear_remainder {q R S : ℝ[X]} (m : ℕ)
    {a b p d β : ℝ} (hR : R = C a * X + C b)
    (hqS : q * S = R * (C p * X + C d) + C β)
    (hq : q.Splits) (hq0 : q ≠ 0) (ha : 0 < a) (hp : 0 < p) (hβ : β < 0) :
    Interlaces (q ^ m * R) (q ^ (m + 1) * S) := by
  have hbase := strictInterl_linear_of_remainder (a := a) (b := b) (p := p)
    (d := d) (β := β) ha hp hβ
  have hstrict : StrictInterl R (q * S) := by
    rw [hR, hqS, hR]
    exact hbase
  have hRdeg : R.natDegree = 1 := by rw [hR]; exact natDegree_linear ha.ne'
  have hqSform : q * S =
      C (a * p) * X ^ 2 + C (a * d + b * p) * X + C (b * d + β) := by
    rw [hqS, hR]; simp only [C_mul, C_add]; ring
  have hqSdeg : (q * S).natDegree = 2 := by
    rw [hqSform]; exact natDegree_quadratic (mul_ne_zero ha.ne' hp.ne')
  have hdeg : R.natDegree + 1 = (q * S).natDegree := by rw [hRdeg, hqSdeg]
  have hmul := (hstrict.toInterlaces hdeg).mul_both_of_splits (hq.pow m)
    (pow_ne_zero m hq0)
  simpa [pow_succ, mul_assoc] using hmul

end RealRooted
