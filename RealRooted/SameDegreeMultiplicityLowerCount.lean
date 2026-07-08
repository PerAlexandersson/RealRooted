import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Same-degree per-root multiplicity lower counts

This file proves a *multiplicity-aware* root-continuity input for the issue #42
route.  For a same-`natDegree` real polynomial family member
`p0 = f + C μ0 * g` (with `μ0 > 0`) and nearby members `pnu = f + C ν * g` that
split and keep the same `natDegree` as `p0`, every root `a` of `p0`, counted with
multiplicity, is eventually accounted for by at least that many roots of `pnu`
in a small ball around `a`.

The main theorem is
`RealRooted.exists_eps_forall_root_count_le_card_filter_near`, whose conclusion
is exactly the per-root lower-count hypothesis consumed by
`Multiset.card_filter_gt_eq_of_forall_le_count_and_card_eq`.

## Harvesting into the matching bridge

To feed the finite matching step, instantiate
`Multiset.card_filter_gt_eq_of_forall_le_count_and_card_eq` with
`s := (f + C μ0 * g).roots`, `t := (f + C ν * g).roots`, and `δ := ρ`; the
`hcount` hypothesis is then supplied verbatim by the conclusion of
`exists_eps_forall_root_count_le_card_filter_near` (after shrinking `ρ` to the
separation radius from `Multiset.exists_pos_lt_and_two_mul_le_abs_sub_toFinset`).
The remaining `hcard` and separation hypotheses are purely finite and are
independent of the analytic content proved here.

Unlike the pointwise single-root continuity results in
`RealRooted.RootContinuity`, this genuinely tracks multiplicity: the proof
factors the nearby polynomial into its near/far clusters and bounds the
coefficients of the near cluster from those of a shifted polynomial whose low
coefficients are small, via a "polynomial division" coefficient recursion.
-/

open Polynomial
open scoped BigOperators
open scoped NNReal

namespace RealRooted

noncomputable section

/-! ### Shift (Taylor) bookkeeping -/

/-
Shifting the variable by `a` shifts every root of `p` by `-a`.
-/
lemma roots_taylor (a : ℝ) (p : ℝ[X]) :
    (taylor a p).roots = p.roots.map (fun r => r - a) := by
  classical
  refine Multiset.ext.mpr fun x => ?_
  have hmul : rootMultiplicity x (taylor a p) = rootMultiplicity (x + a) p := by
    rw [taylor_apply,
      rootMultiplicity_eq_rootMultiplicity (p := p.comp (X + C a)) (t := x),
      rootMultiplicity_eq_rootMultiplicity (p := p) (t := x + a)]
    congr 1
    rw [comp_assoc, add_comp, X_comp, C_comp, add_assoc, ← C_add]
  rw [count_roots, Multiset.count_map, hmul, ← count_roots,
    Multiset.count_eq_card_filter_eq]
  exact congrArg Multiset.card
    (Multiset.filter_congr fun r _ => eq_sub_iff_add_eq.symm)

/-- The number of roots of `p` within `ρ` of `a` equals the number of roots of
the shifted polynomial `taylor a p` within `ρ` of `0`. -/
lemma card_filter_roots_near_eq_taylor (a ρ : ℝ) (p : ℝ[X]) :
    ((taylor a p).roots.filter (fun r => |r| < ρ)).card =
      (p.roots.filter (fun q => |q - a| < ρ)).card := by
  rw [roots_taylor, Multiset.filter_map, Multiset.card_map]
  rfl

/-! ### Coefficient division recursion -/

/-
**Coefficient division bound.**  If `R = N * F` with `|F.coeff 0| ≥ φ > 0`
and every coefficient of `F` bounded by `CF`, then the coefficients of `N` up to
its degree are controlled by a uniform bound in the coefficients of `R`.  This
is the quantitative heart of the multiplicity argument.
-/
lemma abs_coeff_le_of_mul {F N : ℝ[X]} {CF δ φ : ℝ}
    (hφ : 0 < φ) (hF0 : φ ≤ |F.coeff 0|)
    (hCF : ∀ j, |F.coeff j| ≤ CF)
    (hR : ∀ j, j ≤ N.natDegree → |(N * F).coeff j| ≤ δ) :
    ∀ k, k ≤ N.natDegree → |N.coeff k| ≤ (δ / φ) * (1 + CF / φ) ^ k := by
  intro k
  induction k using Nat.strongRecOn with | ind k ih => ?_
  intro hk
  -- Bound the `k`-th coefficient of `N` in terms of the lower coefficients.
  have h_coeff : |N.coeff k * F.coeff 0| ≤ δ + CF * ∑ i ∈ Finset.range k, |N.coeff i| := by
    have hbound : |N.coeff k * F.coeff 0| ≤
        |(N * F).coeff k| + ∑ i ∈ Finset.range k, |N.coeff i| * |F.coeff (k - i)| := by
      have hexpand : (N * F).coeff k =
          N.coeff k * F.coeff 0 + ∑ i ∈ Finset.range k, N.coeff i * F.coeff (k - i) := by
        rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp [Finset.sum_range_succ]
        ring
      rw [hexpand, ← Finset.sum_congr rfl fun _ _ => abs_mul _ _]
      cases abs_cases (N.coeff k * F.coeff 0
            + ∑ i ∈ Finset.range k, N.coeff i * F.coeff (k - i)) <;>
          cases abs_cases (N.coeff k * F.coeff 0) <;>
        linarith [abs_le.mp (Finset.abs_sum_le_sum_abs
          (fun i => N.coeff i * F.coeff (k - i)) (Finset.range k))]
    refine hbound.trans (add_le_add (hR k hk) ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      nlinarith [abs_nonneg (N.coeff i), hCF (k - i)]
  -- Bound the running sum of lower coefficients by a geometric series.
  have h_sum : ∑ i ∈ Finset.range k, |N.coeff i| ≤
      (δ / φ) * ((1 + CF / φ) ^ k - 1) / (CF / φ) := by
    by_cases hCF_pos : CF > 0
    · have hx : (1 + CF / φ) ≠ 1 := by
        have : 0 < CF / φ := div_pos hCF_pos hφ
        linarith
      refine le_trans (Finset.sum_le_sum fun i hi =>
        ih i (Finset.mem_range.mp hi) (by linarith [Finset.mem_range.mp hi])) (le_of_eq ?_)
      rw [← Finset.mul_sum, geom_sum_eq hx]
      ring
    · -- If `CF ≤ 0` then `φ ≤ |F.coeff 0| ≤ CF ≤ 0` contradicts `0 < φ`.
      exact absurd (le_trans hF0 (hCF 0)) (by linarith [not_lt.mp hCF_pos])
  by_cases hCF0 : CF = 0 <;> simp_all [abs_mul]
  · linarith
  · rw [le_div_iff₀ (div_pos (lt_of_le_of_ne
      (by linarith [abs_nonneg (F.coeff 0), hCF 0]) (Ne.symm hCF0)) hφ)] at h_sum
    field_simp at *
    nlinarith [abs_nonneg (N.coeff k), abs_nonneg (F.coeff 0),
      mul_div_cancel₀ (φ + CF) hφ.ne']

lemma abs_coeff_zero_prod_X_sub_C (s : Multiset ℝ) :
    |((s.map (fun w => X - C w)).prod).coeff 0| = (s.map (fun w => |w|)).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, mul_coeff_zero, abs_mul, ih,
        Multiset.map_cons, Multiset.prod_cons]
      congr 1
      rw [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, abs_neg]

lemma pow_card_le_prod_abs (s : Multiset ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hs : ∀ w ∈ s, b ≤ |w|) :
    b ^ s.card ≤ (s.map (fun w => |w|)).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
      exact mul_le_mul (hs a (Multiset.mem_cons_self a t))
        (ih fun w hw => hs w (Multiset.mem_cons_of_mem hw)) (pow_nonneg hb _)
        (abs_nonneg a)

/-! ### Core: many roots near zero from small low coefficients -/

/-
**Core multiplicity lemma.**  There is a positive threshold `δ` (depending
only on the degree bound `n`, the target multiplicity `m`, the radius `ρ`, and
the root bound `B`) such that any monic split real polynomial of degree `n` with
roots bounded by `B` whose lowest `m` coefficients are all smaller than `δ` has
at least `m` roots within `ρ` of `0`.
-/
private lemma exists_delta_le_card_filter_roots_near_zero
    (n : ℕ) (ρ B : ℝ) (hρ : 0 < ρ) (hB : 0 < B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (m : ℕ), m ≤ n → ∀ R : ℝ[X],
      R.Monic → R.Splits → R.natDegree = n →
        (∀ r ∈ R.roots, |r| ≤ B) → (∀ j, j < m → |R.coeff j| < δ) →
          m ≤ (R.roots.filter (fun r => |r| < ρ)).card := by
  use (min ρ 1) ^ n /
    (2 * (1 + (max B 1) ^ n * Nat.choose n (n / 2) / (min ρ 1) ^ n) ^ n)
  refine ⟨div_pos (pow_pos (lt_min hρ zero_lt_one) _) ?_, ?_⟩
  · positivity
  · intro m hmn R hR₁ hR₂ hR₃ hR₄ hR₅
    by_contra h_contra
    -- Split the roots of `R` into a near cluster and a far cluster.
    set near := R.roots.filter (fun r => |r| < ρ)
    set far := R.roots.filter (fun r => ¬ (|r| < ρ))
    -- The monic products of linear factors over each cluster.
    set N := Multiset.prod (Multiset.map (fun r => Polynomial.X - Polynomial.C r) near)
    set F := Multiset.prod (Multiset.map (fun r => Polynomial.X - Polynomial.C r) far)
    have hR : R = N * F := by
      have hprod : R =
          Multiset.prod (Multiset.map (fun r => Polynomial.X - Polynomial.C r) R.roots) :=
        hR₂.eq_prod_roots_of_monic hR₁
      convert hprod using 1
      rw [← Multiset.prod_add]
      rw [← Multiset.map_add, Multiset.filter_add_not]
    -- Facts about N:
    have hN_monic : N.Monic := by
      exact Polynomial.monic_multiset_prod_of_monic _ _ fun x hx => Polynomial.monic_X_sub_C _
    have hN_deg : N.natDegree = near.card :=
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card near
    have hN_coeff : N.coeff near.card = 1 := by
      rw [← hN_deg, hN_monic.coeff_natDegree]
    -- Facts about F:
    have hF_monic : F.Monic := by
      exact Polynomial.monic_multiset_prod_of_monic _ _ fun x hx => Polynomial.monic_X_sub_C _
    have hF_deg : F.natDegree = far.card :=
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card far
    have hFroots : F.roots = far := roots_multiset_prod_X_sub_C far
    have hF_split : F.Splits :=
      splits_iff_card_roots.mpr (by rw [hFroots, hF_deg])
    have hF_coeff_bdd : ∀ j, |F.coeff j| ≤ (max B 1) ^ n * Nat.choose n (n / 2) := by
      intro j
      have hdeg : F.natDegree ≤ n := by
        rw [hF_deg]
        exact le_trans (Multiset.card_le_card <| Multiset.filter_le _ _)
          (by simpa [hR₃] using Polynomial.card_roots' R)
      have hbnd : ∀ z ∈ (F.map (RingHom.id ℝ)).roots, ‖z‖ ≤ B := by
        rw [Polynomial.map_id]
        intro z hz
        rw [hFroots] at hz
        rw [Real.norm_eq_abs]
        exact hR₄ z (Multiset.mem_of_le (Multiset.filter_le _ _) hz)
      have hb := coeff_bdd_of_roots_le (RingHom.id ℝ) hF_monic
        (by rw [Polynomial.map_id]; exact hF_split) hdeg hbnd j
      rwa [Polynomial.map_id, Real.norm_eq_abs] at hb
    have hF_coeff_zero : |F.coeff 0| ≥ (min ρ 1) ^ n := by
      have hEq : |F.coeff 0| = Multiset.prod (Multiset.map (fun r => |r|) far) := by
        simpa [F] using abs_coeff_zero_prod_X_sub_C far
      have hge : Multiset.prod (Multiset.map (fun r => |r|) far) ≥ (min ρ 1) ^ far.card := by
        have hfar : ∀ r ∈ far, |r| ≥ min ρ 1 := fun r hr =>
          le_trans (min_le_left _ _)
            (le_of_not_gt fun h => (Multiset.mem_filter.mp hr).2 h)
        exact pow_card_le_prod_abs far (min ρ 1) (by positivity) hfar
      refine le_trans ?_ (hge.trans_eq hEq.symm)
      refine pow_le_pow_of_le_one (by positivity) (min_le_right _ _) ?_
      exact le_trans (Multiset.card_le_card <| Multiset.filter_le _ _)
        (by simpa [hR₃] using Polynomial.card_roots' R)
    -- Feed the near-cluster factor `N` into `abs_coeff_le_of_mul`.
    have h_abs_coeff : ∀ k ≤ N.natDegree, |N.coeff k| ≤
        (min ρ 1 ^ n / (2 * (1 + (max B 1) ^ n * Nat.choose n (n / 2) / (min ρ 1) ^ n) ^ n)
            / (min ρ 1) ^ n)
          * (1 + (max B 1) ^ n * Nat.choose n (n / 2) / (min ρ 1) ^ n) ^ k := by
      apply abs_coeff_le_of_mul
      any_goals assumption
      · positivity
      · intro j hj
        rw [← hR]
        exact le_of_lt (hR₅ j (by linarith))
    specialize h_abs_coeff near.card (by linarith)
    norm_num [hN_coeff] at h_abs_coeff
    rw [div_div, div_mul_eq_mul_div, le_div_iff₀] at h_abs_coeff <;> norm_num at *
    · contrapose! h_abs_coeff
      rw [mul_comm]
      gcongr
      exact lt_of_le_of_lt
        (pow_le_pow_right₀ (le_add_of_nonneg_right <| by positivity) <| by linarith)
        (lt_mul_of_one_lt_left (by positivity) <| by norm_num)
    · positivity

/-
Coefficients of the Taylor shift of `f + C ν * g` are affine in `ν`.
-/
lemma coeff_taylor_add_C_mul (a ν : ℝ) (f g : ℝ[X]) (j : ℕ) :
    (taylor a (f + C ν * g)).coeff j
      = (taylor a f).coeff j + ν * (taylor a g).coeff j := by
  rw [taylor_apply, taylor_apply, taylor_apply, add_comp, mul_comp, C_comp, coeff_add,
    coeff_C_mul]

/-
If `j` is below the multiplicity of `a` as a root of `p ≠ 0`, then the
`j`-th coefficient of the Taylor shift `taylor a p` vanishes.  (Equivalently,
`X ^ (count a) ∣ taylor a p`.)
-/
lemma coeff_taylor_eq_zero_of_lt_count {p : ℝ[X]} {a : ℝ} {j : ℕ}
    (hj : j < p.roots.count a) : (taylor a p).coeff j = 0 := by
  set m := p.roots.count a with hm
  have h_div : (X - C a) ^ m ∣ p := by
    rw [hm, count_roots]; exact pow_rootMultiplicity_dvd p a
  obtain ⟨q, hq⟩ := h_div
  have hXa : (X - C a).comp (X + C a) = (X : ℝ[X]) := by
    rw [sub_comp, X_comp, C_comp]; ring
  have htay : taylor a p = X ^ m * taylor a q := by
    conv_lhs => rw [hq]
    rw [taylor_apply, taylor_apply, mul_comp, pow_comp, hXa]
  rw [htay, coeff_X_pow_mul', if_neg (not_le.mpr hj)]

/-
A uniform root bound: if every coefficient of `p` has absolute value at most
`M` and the leading coefficient has absolute value at least `C0 > 0`, then every
root of `p` has absolute value below `M / C0 + 1`.  (A convenient real-valued
repackaging of Cauchy's bound.)
-/
private lemma abs_root_lt_of_coeff_le {p : ℝ[X]} {C0 M : ℝ} (hC0 : 0 < C0)
    (hlc : C0 ≤ |p.leadingCoeff|) (hM : ∀ i, |p.coeff i| ≤ M)
    {r : ℝ} (hr : r ∈ p.roots) : |r| < M / C0 + 1 := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hp0 : p ≠ 0 := by rintro rfl; simp at hr
  have hroot : p.IsRoot r := (mem_roots'.mp hr).2
  have hlt := hroot.norm_lt_cauchyBound hp0
  have hcb : |r| < (p.cauchyBound : ℝ) := by
    have h2 : ((‖r‖₊ : ℝ≥0) : ℝ) < ((p.cauchyBound : ℝ≥0) : ℝ) := by
      exact_mod_cast hlt
    simpa [Real.norm_eq_abs] using h2
  set s : ℝ≥0 := Finset.sup (Finset.range p.natDegree) (fun i => ‖p.coeff i‖₊) with hs
  have hsM : (s : ℝ) ≤ M := by
    have hle :
        Finset.sup (Finset.range p.natDegree) (fun i => ‖p.coeff i‖₊) ≤
          M.toNNReal := by
      apply Finset.sup_le
      intro i _
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hM0]
      simpa [Real.norm_eq_abs] using hM i
    calc (s : ℝ) = ((Finset.sup (Finset.range p.natDegree)
            (fun i => ‖p.coeff i‖₊) : ℝ≥0) : ℝ) := by rw [hs]
      _ ≤ ((M.toNNReal : ℝ≥0) : ℝ) := by exact_mod_cast hle
      _ = M := Real.coe_toNNReal _ hM0
  have hden : C0 ≤ ‖p.leadingCoeff‖ := by rwa [Real.norm_eq_abs]
  have hbound : (p.cauchyBound : ℝ) ≤ M / C0 + 1 := by
    rw [Polynomial.cauchyBound]
    push_cast
    rw [← hs]
    have hratio : (s : ℝ) / ‖p.leadingCoeff‖ ≤ M / C0 :=
      div_le_div₀ hM0 hsM hC0 hden
    linarith
  linarith

/-! ### Family reduction -/

/-- **Per-root multiplicity lower counts for a same-degree family.**

Let `p0 = f + C μ0 * g` with `p0` splitting.  For every `ρ > 0` there
is an `ε > 0` such that for every `ν` with `|ν - μ0| < ε` for which
`pnu = f + C ν * g` splits and has the same `natDegree` as `p0`, every root `a`
of `p0`, counted with multiplicity, has at least that many roots of `pnu` within
`ρ` of `a`.

The base parameter `μ0` is completely unconstrained.  The live #42 route uses
this same-degree theorem on positive parameter intervals via
`positiveParameter_local_lower_count`; the jumping endpoint is handled
separately by `degreeIncreasing_local_lower_count`. -/
theorem exists_eps_forall_root_count_le_card_filter_near
    {f g : ℝ[X]} {μ0 : ℝ}
    (hp0_split : (f + C μ0 * g).Splits)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : ℝ, |ν - μ0| < ε →
      (f + C ν * g).Splits →
      (f + C ν * g).natDegree = (f + C μ0 * g).natDegree →
      ∀ a ∈ (f + C μ0 * g).roots.toFinset,
        (f + C μ0 * g).roots.count a ≤
          ((f + C ν * g).roots.filter (fun q => |q - a| < ρ)).card := by
  classical
  by_cases hp0 : f + C μ0 * g = 0
  · exact ⟨1, one_pos, fun ν _ _ _ a ha => by rw [hp0] at ha; simp at ha⟩
  set p0 := f + C μ0 * g with hp0def
  set n := p0.natDegree with hndef
  have hlc0ne : p0.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  set lc0 := p0.leadingCoeff with hlc0def
  have hlc0pos : 0 < |lc0| := abs_pos.mpr hlc0ne
  set c0 : ℝ := |lc0| / 2 with hc0def
  have hc0 : 0 < c0 := by positivity
  set N := max f.natDegree g.natDegree with hNdef
  set Cfg : ℝ :=
    ∑ k ∈ Finset.range (N + 1), (|f.coeff k| + (|μ0| + 1) * |g.coeff k|)
    with hCfgdef
  have hCfg0 : 0 ≤ Cfg := Finset.sum_nonneg (fun k _ => by positivity)
  set M0 : ℝ := ∑ k ∈ Finset.range (n+1), |p0.coeff k| with hM0def
  have hM00 : 0 ≤ M0 := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  set A : ℝ := M0 / |lc0| + 1 with hAdef
  set B : ℝ := (Cfg / c0 + 1) + A with hBdef
  have hB : 0 < B := by
    have h1 : 0 ≤ Cfg / c0 := by positivity
    have h2 : 0 ≤ M0 / |lc0| := by positivity
    rw [hBdef, hAdef]; linarith
  set G : ℝ :=
    ∑ a ∈ p0.roots.toFinset, ∑ j ∈ Finset.range n, |(taylor a g).coeff j|
    with hGdef
  have hG0 : 0 ≤ G :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  obtain ⟨δ, hδ0, hδ⟩ := exists_delta_le_card_filter_roots_near_zero n ρ B hρ hB
  set ε : ℝ := min (min 1 (|lc0| / (2*(|g.coeff n|+1)))) (δ * c0 / (G+1)) with hεdef
  have hε0 : 0 < ε := lt_min (lt_min one_pos (by positivity)) (by positivity)
  have hp0_coeff : ∀ i, |p0.coeff i| ≤ M0 := by
    intro i
    by_cases hi : i ≤ n
    · exact Finset.single_le_sum (f := fun k => |p0.coeff k|) (fun k _ => abs_nonneg _)
        (Finset.mem_range.mpr (by lia))
    · rw [coeff_eq_zero_of_natDegree_lt (by lia), abs_zero]; exact hM00
  refine ⟨ε, hε0, ?_⟩
  intro ν hν hνsplit hνdeg a ha
  have hνabs : |ν| ≤ |μ0| + 1 := by
    have h1 : |ν - μ0| < 1 := lt_of_lt_of_le hν (le_trans (min_le_left _ _) (min_le_left _ _))
    have h2 : |ν| ≤ |ν - μ0| + |μ0| := by
      have : |ν| = |(ν - μ0) + μ0| := by congr 1; ring
      rw [this]; exact abs_add_le _ _
    linarith
  set pnu := f + C ν * g with hpnudef
  have hpnu_deg : pnu.natDegree = n := hνdeg
  have hpnu_coeff : ∀ i, |pnu.coeff i| ≤ Cfg := by
    intro i
    have hcoeff : pnu.coeff i = f.coeff i + ν * g.coeff i := by
      simp [hpnudef, coeff_add, coeff_C_mul]
    by_cases hi : i ≤ N
    · have hterm : |f.coeff i| + (|μ0|+1) * |g.coeff i| ≤ Cfg :=
        Finset.single_le_sum (f := fun k => |f.coeff k| + (|μ0|+1)*|g.coeff k|)
          (fun k _ => by positivity) (Finset.mem_range.mpr (by lia))
      rw [hcoeff]
      calc |f.coeff i + ν * g.coeff i| ≤ |f.coeff i| + |ν * g.coeff i| := abs_add_le _ _
        _ = |f.coeff i| + |ν| * |g.coeff i| := by rw [abs_mul]
        _ ≤ |f.coeff i| + (|μ0|+1) * |g.coeff i| := by
            have := mul_le_mul_of_nonneg_right hνabs (abs_nonneg (g.coeff i)); linarith
        _ ≤ Cfg := hterm
    · have hfN : f.natDegree ≤ N := by rw [hNdef]; exact le_max_left _ _
      have hgN : g.natDegree ≤ N := by rw [hNdef]; exact le_max_right _ _
      have hfi : f.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
      have hgi : g.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
      rw [hcoeff, hfi, hgi]; simpa using hCfg0
  have hpnu_lc : pnu.leadingCoeff = pnu.coeff n := by rw [leadingCoeff, hpnu_deg]
  have hp0_cn : p0.coeff n = lc0 := by rw [hlc0def, leadingCoeff, hndef]
  have hpnu_cn : pnu.coeff n = lc0 + (ν - μ0) * g.coeff n := by
    have e1 : pnu.coeff n = f.coeff n + ν * g.coeff n := by
      simp [hpnudef, coeff_add, coeff_C_mul]
    have e2 : p0.coeff n = f.coeff n + μ0 * g.coeff n := by
      simp [hp0def, coeff_add, coeff_C_mul]
    have hlc0e : lc0 = f.coeff n + μ0 * g.coeff n := by rw [← hp0_cn, e2]
    rw [e1, hlc0e]; ring
  have hgabs : |ν - μ0| * |g.coeff n| ≤ c0 := by
    have hεle : ε ≤ |lc0| / (2*(|g.coeff n|+1)) := le_trans (min_le_left _ _) (min_le_right _ _)
    have h1 : |ν - μ0| ≤ |lc0| / (2*(|g.coeff n|+1)) := le_of_lt (lt_of_lt_of_le hν hεle)
    have hgn0 : 0 ≤ |g.coeff n| := abs_nonneg _
    calc |ν - μ0| * |g.coeff n| ≤ (|lc0|/(2*(|g.coeff n|+1))) * |g.coeff n| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ c0 := by
          rw [hc0def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hlc0pos.le, hgn0]
  have hclower : c0 ≤ |pnu.coeff n| := by
    rw [hpnu_cn]
    have h3 : |lc0| - |ν - μ0| * |g.coeff n| ≤ |lc0 + (ν - μ0) * g.coeff n| := by
      have h := abs_add_le (lc0 + (ν - μ0) * g.coeff n) (-((ν - μ0) * g.coeff n))
      simp only [add_neg_cancel_right, abs_neg, abs_mul] at h
      linarith
    have hc0eq : c0 = |lc0| / 2 := hc0def
    linarith [hgabs, h3]
  have hcne : pnu.coeff n ≠ 0 := fun h => by rw [h, abs_zero] at hclower; linarith
  set c := pnu.coeff n with hcdef
  have hcinv : c⁻¹ ≠ 0 := inv_ne_zero hcne
  set ptil := C c⁻¹ * pnu with hptildef
  have hptil_monic : ptil.Monic := by
    have hl : ptil.leadingCoeff = c⁻¹ * pnu.leadingCoeff := by
      rw [hptildef, leadingCoeff_mul, leadingCoeff_C]
    rw [Monic.def, hl, hpnu_lc]; exact inv_mul_cancel₀ hcne
  have hptil_deg : ptil.natDegree = n := by rw [hptildef, natDegree_C_mul hcinv, hpnu_deg]
  have hptil_roots : ptil.roots = pnu.roots := by rw [hptildef]; exact roots_C_mul pnu hcinv
  set R := taylor a ptil with hRdef
  have hR_monic : R.Monic := by
    rw [hRdef, taylor_apply]; exact hptil_monic.comp (monic_X_add_C a) (by simp)
  have hR_deg : R.natDegree = n := by rw [hRdef, natDegree_taylor, hptil_deg]
  have hR_roots : R.roots = pnu.roots.map (fun r => r - a) := by
    rw [hRdef, roots_taylor, hptil_roots]
  have hpnu_card : pnu.roots.card = n := by
    rw [← hpnu_deg]; exact (hνsplit.natDegree_eq_card_roots).symm
  have hR_splits : R.Splits := by
    apply splits_iff_card_roots.mpr
    rw [hR_roots, Multiset.card_map, hR_deg, hpnu_card]
  have hR_bound : ∀ r ∈ R.roots, |r| ≤ B := by
    intro r hr
    rw [hR_roots, Multiset.mem_map] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    have hqbound : |q| < Cfg / c0 + 1 := by
      refine abs_root_lt_of_coeff_le hc0 ?_ hpnu_coeff hq
      rw [hpnu_lc]; exact hclower
    have habound : |a| < A := by
      have haroot : a ∈ p0.roots := by simpa using ha
      refine abs_root_lt_of_coeff_le hlc0pos ?_ hp0_coeff haroot
      rw [hlc0def]
    have htri : |q - a| ≤ |q| + |a| := by
      have := abs_add_le q (-a); simpa [sub_eq_add_neg, abs_neg] using this
    rw [hBdef]; linarith
  have hR_low : ∀ j, j < p0.roots.count a → |R.coeff j| < δ := by
    intro j hj
    have hRj : R.coeff j = c⁻¹ * (taylor a pnu).coeff j := by
      rw [hRdef, hptildef]
      have ht : taylor a (C c⁻¹ * pnu) = C c⁻¹ * taylor a pnu := by
        rw [taylor_apply, taylor_apply, mul_comp, C_comp]
      rw [ht, coeff_C_mul]
    have hp0z : (taylor a p0).coeff j = 0 := coeff_taylor_eq_zero_of_lt_count hj
    have hpnucoeff : (taylor a pnu).coeff j = (ν - μ0) * (taylor a g).coeff j := by
      have e_pnu := coeff_taylor_add_C_mul a ν f g j
      have e_p0 := coeff_taylor_add_C_mul a μ0 f g j
      rw [← hp0def, hp0z] at e_p0
      rw [hpnudef, e_pnu]
      linear_combination -e_p0
    have hjn : j < n := lt_of_lt_of_le hj (by
      rw [hndef]; exact le_trans (Multiset.count_le_card a p0.roots)
        (le_of_eq (hp0_split.natDegree_eq_card_roots).symm))
    have hTbound : |(taylor a g).coeff j| ≤ G := by
      rw [hGdef]
      refine le_trans (Finset.single_le_sum (f := fun j => |(taylor a g).coeff j|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.mpr hjn)) ?_
      exact Finset.single_le_sum
        (f := fun a => ∑ j ∈ Finset.range n, |(taylor a g).coeff j|)
        (fun a _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) ha
    have hcabs : c0 ≤ |c| := by rw [hcdef]; exact hclower
    have hcinv_le : |c⁻¹| ≤ 1/c0 := by rw [abs_inv, one_div]; exact inv_anti₀ hc0 hcabs
    have hνle : |ν - μ0| ≤ ε := le_of_lt hν
    have hεδ : ε ≤ δ * c0 / (G+1) := min_le_right _ _
    rw [hRj, hpnucoeff, abs_mul, abs_mul]
    clear_value c ε c0 G
    have hstep1 :
        |c⁻¹| * (|ν - μ0| * |(taylor a g).coeff j|) ≤ (1/c0) * (ε * G) := by
      gcongr
    have h2 : (δ * c0 / (G+1)) * G / c0 = δ * (G/(G+1)) := by field_simp
    have h3 : δ * (G/(G+1)) < δ := by
      have hlt1 : G/(G+1) < 1 := by rw [div_lt_one (by positivity)]; linarith
      calc δ * (G/(G+1)) < δ * 1 := mul_lt_mul_of_pos_left hlt1 hδ0
        _ = δ := mul_one δ
    have key : (1/c0) * (ε * G) < δ := by
      calc (1/c0)*(ε*G) = (ε*G)/c0 := by ring
        _ ≤ ((δ*c0/(G+1))*G)/c0 := by gcongr
        _ = δ*(G/(G+1)) := h2
        _ < δ := h3
    exact lt_of_le_of_lt hstep1 key
  have hmn : p0.roots.count a ≤ n := by
    rw [hndef]
    exact le_trans (Multiset.count_le_card a p0.roots)
      (le_of_eq (hp0_split.natDegree_eq_card_roots).symm)
  have hcount := hδ (p0.roots.count a) hmn R hR_monic hR_splits hR_deg hR_bound hR_low
  have htransfer : (R.roots.filter (fun r => |r| < ρ)).card
      = (pnu.roots.filter (fun q => |q - a| < ρ)).card := by
    rw [hRdef, card_filter_roots_near_eq_taylor a ρ ptil, hptil_roots]
  rw [← htransfer]; exact hcount

end

end RealRooted
