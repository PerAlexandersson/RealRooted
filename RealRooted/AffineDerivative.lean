/-
# Affine derivative preserves interlacing

Main result (`strictInterl_affine_derivative`): if `f` is real-rooted with all roots ≤ 0
and `c > natDegree f`, then
  `StrictInterl (C c * f + (1 - X) * f.derivative) f`.

## Proof sketch

Let `g = C c * f + (1 - X) * f'` and `d = natDegree f`.

1. At each root `r` of `f`, `g(r) = (1 - r) * f'(r)`.
   Since `r ≤ 0`, `1 - r ≥ 1 > 0`, so `g` has the same sign as `f'` at `f`-roots.

2. The derivative `f'` alternates sign at consecutive simple roots of `f`.
   So `g` alternates sign → IVT gives `d - 1` roots between consecutive `f`-roots.

3. `g` has degree `d` with leading coefficient `(c - d) * lc(f) > 0`.
   With `d - 1` roots and degree `d`, the remaining factor has degree 1,
   giving one more root. So `g` is real-rooted.

4. The roots interlace in the same-degree (`ListAlternates`) sense: `StrictInterl g f`.
-/
module

public import RealRooted.Basic
import RealRooted.Linear
public import RealRooted.Derivative
public import RealRooted.Wagner
import RealRooted.Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic
import RealRooted.WagnerX.AffineFactors
import RealRooted.Derivative.Interlacing
import RealRooted.Derivative.Algebra
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

@[expose] public section

open Polynomial Filter

noncomputable section

namespace RealRooted

/-! ## Evaluation at roots -/

/-- At a root `r` of `f`, the affine derivative evaluates to `(1 - r) * f'(r)`. -/
lemma eval_affineDeriv_at_root {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) (c : ℝ) :
    (C c * f + (1 - X) * f.derivative).eval r = (1 - r) * f.derivative.eval r := by
  simp_all

/-- At a root of `f` with `r ≤ 0`, the affine derivative vanishes iff `f'` does. -/
lemma eval_affineDeriv_eq_zero_iff {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) (c : ℝ)
    (hr_nonpos : r ≤ 0) :
    (C c * f + (1 - X) * f.derivative).eval r = 0 ↔ f.derivative.eval r = 0 := by
  rw [eval_affineDeriv_at_root hr c]
  grind

/-! ## Degree and leading coefficient

The affine derivative `g = C c * f + (1 - X) * f'` has degree `d` with
leading coefficient `(c - d) * lc(f)`, since:
- `coeff (C c * f) d = c * lc(f)`
- `coeff ((1 - X) * f') d = -d * lc(f)`   (from `coeff f' (d-1) = d * lc(f)`)
-/

/-- For positive degree `d`, the coefficient of `X^d` in the affine derivative
is `(c - d)` times the leading coefficient of `f`. -/
lemma coeff_affineDeriv {f : ℝ[X]} (hdeg : 1 ≤ f.natDegree) (c : ℝ) :
    (C c * f + (1 - X) * f.derivative).coeff f.natDegree =
      (c - f.natDegree) * f.leadingCoeff := by
  set d := f.natDegree
  have hd1 : d - 1 + 1 = d := Nat.sub_add_cancel hdeg
  have hrw : (1 - X : ℝ[X]) * f.derivative = f.derivative - X * f.derivative := by ring
  rw [hrw, coeff_add, coeff_sub, coeff_C_mul]
  have hf'd : f.derivative.coeff d = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [f.natDegree_derivative]; lia)
  have hXf'd : (X * f.derivative).coeff d = f.derivative.coeff (d - 1) := by
    conv_lhs => rw [← hd1]
    rw [coeff_X_mul]
  have hcoeff_deriv : f.derivative.coeff (d - 1) = (↑(d - 1) + 1) * f.coeff d := by
    rw [coeff_derivative, hd1, mul_comm]
  have hcast : (↑(d - 1) : ℝ) + 1 = (↑d : ℝ) := by simp_all
  rw [hf'd, hXf'd, hcoeff_deriv, hcast, show f.leadingCoeff = f.coeff d from rfl]
  ring

/-- The affine derivative of a nonzero positive-degree polynomial has the same
degree as `f` when `c` differs from that degree. -/
lemma natDegree_affineDeriv {f : ℝ[X]} (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    {c : ℝ} (hc : c ≠ (f.natDegree : ℝ)) :
    (C c * f + (1 - X) * f.derivative).natDegree = f.natDegree := by
  apply le_antisymm
  · -- Upper bound: natDegree g ≤ d
    calc (C c * f + (1 - X) * f.derivative).natDegree
        ≤ max (C c * f).natDegree ((1 - X : ℝ[X]) * f.derivative).natDegree :=
          natDegree_add_le _ _
      _ ≤ max f.natDegree f.natDegree := by
          apply max_le_max
          · by_cases hc0 : c = 0
            · simp [hc0]
            · exact le_of_eq (natDegree_C_mul hc0)
          · calc ((1 - X : ℝ[X]) * f.derivative).natDegree
                ≤ (1 - X : ℝ[X]).natDegree + f.derivative.natDegree := natDegree_mul_le
              _ ≤ 1 + (f.natDegree - 1) := by
                  apply Nat.add_le_add
                  · calc (1 - X : ℝ[X]).natDegree
                        ≤ max (1 : ℝ[X]).natDegree X.natDegree := natDegree_sub_le _ _
                      _ = 1 := by simp [natDegree_one, natDegree_X]
                  · exact f.natDegree_derivative.le
              _ = f.natDegree := by lia
      _ = f.natDegree := max_self _
  · -- Lower bound: the coefficient at degree d is (c - d) * lc(f) ≠ 0
    apply Polynomial.le_natDegree_of_ne_zero
    rw [coeff_affineDeriv hdeg c]
    exact mul_ne_zero (sub_ne_zero.mpr hc) (leadingCoeff_ne_zero.mpr hf)

/-- Under the same nonzero, positive-degree, and scalar-not-degree hypotheses,
the affine derivative has leading coefficient `(c - deg f) * lc(f)`. -/
lemma leadingCoeff_affineDeriv {f : ℝ[X]} (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    {c : ℝ} (hc : c ≠ (f.natDegree : ℝ)) :
    (C c * f + (1 - X) * f.derivative).leadingCoeff =
      (c - f.natDegree) * f.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_affineDeriv hf hdeg hc, coeff_affineDeriv hdeg c]

/-- The affine derivative is nonzero when `f` is nonzero of positive degree and
`c` differs from that degree. -/
lemma affineDeriv_ne_zero {f : ℝ[X]} (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    {c : ℝ} (hc : c ≠ (f.natDegree : ℝ)) :
    C c * f + (1 - X) * f.derivative ≠ 0 := by
  intro h
  have := natDegree_affineDeriv hf hdeg hc
  rw [h, natDegree_zero] at this; lia

/-! ## IVT contrapositive and sign analysis -/

/-- If a polynomial has no roots in `[a, b]`, it has constant sign there
    (product of evaluations at the endpoints is positive). -/
lemma eval_same_sign_of_no_roots {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hno_roots : ∀ x, a ≤ x → x ≤ b → p.eval x ≠ 0) :
    0 < p.eval a * p.eval b := by
  have ha : p.eval a ≠ 0 := hno_roots a le_rfl hab
  have hb : p.eval b ≠ 0 := hno_roots b hab le_rfl
  rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb
  · exact mul_pos_of_neg_of_neg ha hb
  · obtain ⟨x, hx, hpx⟩ := intermediate_value_Icc hab p.continuous.continuousOn
      ⟨ha.le, hb.le⟩
    exact (hno_roots x hx.1 hx.2 hpx).elim
  · obtain ⟨x, hx, hpx⟩ := intermediate_value_Icc' hab p.continuous.continuousOn
      ⟨hb.le, ha.le⟩
    exact (hno_roots x hx.1 hx.2 hpx).elim
  · positivity

/-- **Key sign lemma**: at consecutive roots `r₁ < r₂` of `f` (with no f-roots
    strictly between them), the derivative satisfies `f'(r₁) * f'(r₂) ≤ 0`.

    Proof: Factor `f = (X - r₁) * q₁` and `f = (X - r₂) * q₂`.
    Then `q₁(r₁) = f'(r₁)` and `q₂(r₂) = f'(r₂)`.
    Since `f` has no roots in `(r₁, r₂)`, neither do `q₁` or `q₂`.
    Evaluating `f` at the midpoint via both factorizations gives
    `sign(f'(r₁)) = -sign(f'(r₂))`. -/
lemma derivative_sign_at_consecutive_roots {f : ℝ[X]}
    {r₁ r₂ : ℝ} (hr₁ : f.IsRoot r₁) (hr₂ : f.IsRoot r₂)
    (hlt : r₁ < r₂)
    (hno_between : ∀ r ∈ f.roots, ¬(r₁ < r ∧ r < r₂))
    (hf_ne : f ≠ 0) :
    f.derivative.eval r₁ * f.derivative.eval r₂ ≤ 0 := by
  by_cases hf1 : f.derivative.eval r₁ = 0; · simp [hf1]
  by_cases hf2 : f.derivative.eval r₂ = 0; · simp [hf2]
  obtain ⟨q₁, hfq₁⟩ := dvd_iff_isRoot.mpr hr₁
  have hq₁r₁ : q₁.eval r₁ = f.derivative.eval r₁ := by simp_all
  obtain ⟨q₂, hfq₂⟩ := dvd_iff_isRoot.mpr hr₂
  have hq₂r₂ : q₂.eval r₂ = f.derivative.eval r₂ := by
    have hd : f.derivative = q₂ + (X - C r₂) * q₂.derivative := by
      rw [hfq₂, derivative_mul, derivative_X_sub_C, one_mul]
    rw [hd, eval_add, eval_mul, eval_sub, eval_X, eval_C]
    simp
  have hq₁_nr : ∀ x, r₁ < x → x < r₂ → q₁.eval x ≠ 0 := by
    intro x hx1 hx2 hq
    apply hno_between x ((mem_roots hf_ne).mpr ?_) ⟨hx1, hx2⟩
    simp [hfq₁, hq]
  have hq₂_nr : ∀ x, r₁ < x → x < r₂ → q₂.eval x ≠ 0 := by
    intro x hx1 hx2 hq
    apply hno_between x ((mem_roots hf_ne).mpr ?_) ⟨hx1, hx2⟩
    simp [hfq₂, hq]
  set m := (r₁ + r₂) / 2 with hm_def
  have hm1 : r₁ < m := by grind
  have hm2 : m < r₂ := by grind
  have hq₁_same : 0 < q₁.eval r₁ * q₁.eval m :=
    eval_same_sign_of_no_roots hm1.le fun x hx1 hx2 ↦ by grind
  have hq₂_same : 0 < q₂.eval m * q₂.eval r₂ :=
    eval_same_sign_of_no_roots hm2.le fun x hx1 hx2 => by grind
  have hmr₁ : 0 < m - r₁ := by linarith
  have hmr₂ : m - r₂ < 0 := by linarith
  have hq₁m_ne : q₁.eval m ≠ 0 := hq₁_nr m hm1 hm2
  have heq : (m - r₁) * q₁.eval m = (m - r₂) * q₂.eval m := by
    have h1 : f.eval m = (m - r₁) * q₁.eval m := by
      rw [hfq₁, eval_mul, eval_sub, eval_X, eval_C]
    have h2 : f.eval m = (m - r₂) * q₂.eval m := by
      rw [hfq₂, eval_mul, eval_sub, eval_X, eval_C]
    lia
  have hprod_neg : q₁.eval m * q₂.eval m < 0 := by
    rcases lt_or_gt_of_ne hq₁m_ne with h | h
    · exact mul_neg_of_neg_of_pos h (by nlinarith)
    · exact mul_neg_of_pos_of_neg h (by nlinarith)
  have : q₁.eval r₁ * q₂.eval r₂ < 0 := by
    rcases lt_or_gt_of_ne hq₁m_ne with h | h
    · exact mul_neg_of_neg_of_pos
        (by nlinarith [hq₁_same]) (by nlinarith [hq₂_same, hprod_neg])
    · exact mul_neg_of_pos_of_neg
        (by nlinarith [hq₁_same]) (by nlinarith [hq₂_same, hprod_neg])
  grind

/-! ## Root existence between consecutive roots of f

Between consecutive roots `r₁ ≤ r₂` of `f`, we show `g` has a root in `[r₁, r₂]`:
- If `r₁ = r₂` (repeated root): `f'(r₁) = 0`, so `g(r₁) = 0`.
- If `r₁ < r₂` (distinct roots): `f'(r₁)` and `f'(r₂)` have opposite signs,
  hence `g(r₁)` and `g(r₂)` have opposite signs. IVT gives a root. -/

lemma exists_affineDeriv_root_between {f : ℝ[X]}
    (hf_ne : f ≠ 0)
    {c : ℝ}
    {r₁ r₂ : ℝ} (hr₁ : f.IsRoot r₁) (hr₂ : f.IsRoot r₂)
    (hle : r₁ ≤ r₂)
    (hr₂_nonpos : r₂ ≤ 0)
    (hsub : (↑[r₁, r₂] : Multiset ℝ) ≤ f.roots)
    (hno_between : ∀ r ∈ f.roots, ¬(r₁ < r ∧ r < r₂)) :
    ∃ s, r₁ ≤ s ∧ s ≤ r₂ ∧ (C c * f + (1 - X) * f.derivative).IsRoot s := by
  set g := C c * f + (1 - X) * f.derivative
  rcases eq_or_lt_of_le hle with rfl | hlt
  · have hcount : 2 ≤ Multiset.count r₁ f.roots := by
      exact (by simpa using Multiset.count_le_of_le r₁ hsub)
    rw [count_roots] at hcount
    have hf'_root : f.derivative.IsRoot r₁ :=
      isRoot_derivative_of_rootMultiplicity_ge_two hcount
    have hg_root : g.IsRoot r₁ := by
      change (C c * f + (1 - X) * f.derivative).eval r₁ = 0
      rw [eval_affineDeriv_at_root hr₁ c, hf'_root, mul_zero]
    exact ⟨r₁, le_rfl, le_rfl, hg_root⟩
  · have hsign : g.eval r₁ * g.eval r₂ ≤ 0 := by
      rw [eval_affineDeriv_at_root hr₁ c, eval_affineDeriv_at_root hr₂ c]
      have h1 : 0 < 1 - r₁ := by linarith
      have h2 : 0 < 1 - r₂ := by linarith
      suffices f.derivative.eval r₁ * f.derivative.eval r₂ ≤ 0 by nlinarith [mul_pos h1 h2]
      exact derivative_sign_at_consecutive_roots hr₁ hr₂ hlt hno_between hf_ne
    rcases le_total (g.eval r₁) (g.eval r₂) with h12 | h21
    · obtain ⟨s, hs, hval⟩ := intermediate_value_Icc hlt.le
        g.continuous.continuousOn (show (0 : ℝ) ∈ Set.Icc (g.eval r₁) (g.eval r₂) by
          constructor <;> nlinarith)
      exact ⟨s, hs.1, hs.2, hval⟩
    · obtain ⟨s, hs, hval⟩ := intermediate_value_Icc' hlt.le
        g.continuous.continuousOn (show (0 : ℝ) ∈ Set.Icc (g.eval r₂) (g.eval r₁) by
          constructor <;> nlinarith)
      exact ⟨s, hs.1, hs.2, hval⟩

/-- In the distinct-root case, the affine derivative has a root strictly between the endpoints. -/
lemma exists_affineDeriv_root_between_strict {f : ℝ[X]}
    {c : ℝ} (hc : (f.natDegree : ℝ) < c)
    {r₁ r₂ : ℝ} (hr₁ : f.IsRoot r₁) (hr₂ : f.IsRoot r₂)
    (hlt : r₁ < r₂)
    (hr₂_nonpos : r₂ ≤ 0) :
    ∃ s, r₁ < s ∧ s < r₂ ∧ (C c * f + (1 - X) * f.derivative).IsRoot s := by
  let φ : ℝ → ℝ := fun x => f.eval x * (1 - x) ^ (-c)
  have hfa : Filter.Tendsto φ (nhdsWithin r₁ (Set.Ioi r₁)) (nhds 0) := by
    have hpow : ContinuousAt (fun x : ℝ => (1 - x) ^ (-c)) r₁ := by
      refine (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl ?_)
      change 1 - r₁ ≠ 0
      linarith
    simpa only [φ, show f.eval r₁ = 0 from hr₁, zero_mul] using
      (f.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
        (hpow.tendsto.mono_left nhdsWithin_le_nhds)
  have hfb : Filter.Tendsto φ (nhdsWithin r₂ (Set.Iio r₂)) (nhds 0) := by
    have hpow : ContinuousAt (fun x : ℝ => (1 - x) ^ (-c)) r₂ := by
      refine (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl ?_)
      change 1 - r₂ ≠ 0
      linarith
    simpa only [φ, show f.eval r₂ = 0 from hr₂, zero_mul] using
      (f.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
        (hpow.tendsto.mono_left nhdsWithin_le_nhds)
  have hderiv :
      ∀ x ∈ Set.Ioo r₁ r₂,
        HasDerivAt φ ((C c * f + (1 - X) * f.derivative).eval x * (1 - x) ^ (-c - 1)) x := by
    intro x hx
    have hx_ne : 1 - x ≠ 0 := by grind
    have hbase : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
      simpa [Pi.sub_def] using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have hpow :
        HasDerivAt (fun y : ℝ => (1 - y) ^ (-c)) (c * (1 - x) ^ (-c - 1)) x := by
      convert hbase.rpow_const (p := -c) (Or.inl hx_ne) using 1
      simp
    have hmul :
        HasDerivAt φ
          (f.derivative.eval x * (1 - x) ^ (-c) + f.eval x * (c * (1 - x) ^ (-c - 1))) x := by
      simpa [φ, Pi.mul_def] using (f.hasDerivAt x).mul hpow
    have htarget :
        (C c * f + (1 - X) * f.derivative).eval x * (1 - x) ^ (-c - 1) =
          f.derivative.eval x * (1 - x) ^ (-c) + f.eval x * (c * (1 - x) ^ (-c - 1)) := by
      have hx_nonneg : 0 ≤ 1 - x := by grind
      have hpow_shift : (1 - x) ^ (-c) = (1 - x) * (1 - x) ^ (-1 - c) := by
        rw [show (-c : ℝ) = 1 + (-1 - c) by ring]
        exact Real.rpow_one_add' hx_nonneg (by linarith)
      have hneg : (-c - 1 : ℝ) = (-1 - c) := by ring
      calc
        (C c * f + (1 - X) * f.derivative).eval x * (1 - x) ^ (-c - 1)
            = (c * f.eval x + (1 - x) * f.derivative.eval x) * (1 - x) ^ (-c - 1) := by
                simp [eval_add, eval_mul, eval_C, eval_sub, eval_X]
        _ = c * f.eval x * (1 - x) ^ (-c - 1) +
              f.derivative.eval x * ((1 - x) * (1 - x) ^ (-1 - c)) := by grind
        _ = c * f.eval x * (1 - x) ^ (-c - 1) +
              f.derivative.eval x * (1 - x) ^ (-c) := by lia
        _ = f.derivative.eval x * (1 - x) ^ (-c) +
              f.eval x * (c * (1 - x) ^ (-c - 1)) := by ring
    lia
  obtain ⟨s, hs, hs0⟩ := exists_hasDerivAt_eq_zero' hlt hfa hfb hderiv
  have hs_factor_ne : (1 - s) ^ (-c - 1) ≠ 0 :=
    (Real.rpow_ne_zero (by grind) (by linarith)).2 (by grind)
  exact ⟨s, hs.1, hs.2, by simp_all⟩

/-! ## Inner interleaving construction

Produce a root of `g` between each consecutive pair in the sorted root list of `f`.
Structure mirrors `mkInterleaving` from `Derivative.lean`: when `r₁ < r₂`, use the
IVT root; when `r₁ = r₂`, use the repeated root. -/

/-- For a list `rs` and polynomial `f`, no root of `f` lies strictly between
    consecutive entries of `rs`. Used to supply the `hno_between` hypothesis to
    `derivative_sign_at_consecutive_roots` in the recursive interleaving construction. -/
def ConsecNoRoots (f : ℝ[X]) : List ℝ → Prop
  | [] | [_] => True
  | a :: b :: rest => (∀ r ∈ f.roots, ¬(a < r ∧ r < b)) ∧ ConsecNoRoots f (b :: rest)

/-- If `rs` is a sorted list whose multiset equals `f.roots`, then
    no root of `f` lies strictly between consecutive entries. -/
lemma consecNoRoots_of_sorted_eq {f : ℝ[X]} {rs : List ℝ}
    (heq : (↑rs : Multiset ℝ) = f.roots)
    (hsorted : rs.Pairwise (· ≤ ·)) :
    ConsecNoRoots f rs := by
  have hmem : ∀ r ∈ f.roots, r ∈ rs := fun r hr => by
    rw [← Multiset.mem_coe, heq]; lia
  -- Prove for all suffixes: if rs = pre ++ suf, then ConsecNoRoots f suf
  suffices ∀ (pre suf : List ℝ), rs = pre ++ suf → ConsecNoRoots f suf by
    simp_all
  intro pre suf happ
  induction suf generalizing pre with
  | nil => trivial
  | cons a tl ih =>
    match tl with
    | [] => trivial
    | b :: rest =>
      have hsorted_full : (pre ++ (a :: b :: rest)).Pairwise (· ≤ ·) := happ ▸ hsorted
      have hpw_app := List.pairwise_append.mp hsorted_full
      have hsorted_suf : (a :: b :: rest).Pairwise (· ≤ ·) := hpw_app.2.1
      have hcross : ∀ x ∈ pre, ∀ y ∈ a :: b :: rest, x ≤ y := hpw_app.2.2
      have hab : a ≤ b := List.rel_of_pairwise_cons hsorted_suf (.head _)
      have hb_le_rest : ∀ x ∈ rest, b ≤ x :=
        fun x hx => List.rel_of_pairwise_cons (List.pairwise_cons.mp hsorted_suf).2 hx
      constructor
      · -- ∀ r ∈ f.roots, ¬(a < r ∧ r < b)
        grind
      · exact ih (pre ++ [a]) (by simp [List.append_assoc, happ])

/-- Recursively produce a root of `g` between each consecutive pair in `rs`.
When `r₁ < r₂`, uses the IVT root from `exists_affineDeriv_root_between`.
When `r₁ = r₂` (repeated root), uses `r₁` itself. -/
noncomputable def mkAffineInterleaving (f : ℝ[X]) (c : ℝ) (hdeg : 2 ≤ f.natDegree)
    (hc : (f.natDegree : ℝ) < c)
    (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0) :
    (rs : List ℝ) → (hrs : ∀ r ∈ rs, f.IsRoot r) →
    (hsorted : rs.Pairwise (· ≤ ·)) →
    (hsub : (↑rs : Multiset ℝ) ≤ f.roots) →
    (hgap : ConsecNoRoots f rs) →
    List ℝ
  | [], _, _, _, _ | [_], _, _, _, _ => []
  | r₁ :: r₂ :: rest, hrs, hsorted, hsub, hgap =>
    have hrest : ∀ r ∈ r₂ :: rest, f.IsRoot r :=
      List.forall_mem_of_forall_mem_cons hrs
    have hsorted_tail := (List.pairwise_cons.mp hsorted).2
    have hsub_tail : (↑(r₂ :: rest) : Multiset ℝ) ≤ f.roots := by
      apply le_trans _ hsub
      simp [Multiset.le_iff_count, Multiset.coe_count, List.count_cons]
    have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hsorted (.head _)
    let s : ℝ := if hlt : r₁ < r₂ then
      (exists_affineDeriv_root_between_strict hc
        (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))
        hlt
        (hroots_nonpos r₂ (Multiset.subset_of_le hsub
          (Multiset.mem_coe.mpr (.tail _ (.head _)))))).choose
    else r₁
    s :: mkAffineInterleaving f c hdeg hc hroots_nonpos
      (r₂ :: rest) hrest hsorted_tail hsub_tail hgap.2

lemma mkAffineInterleaving_length (f : ℝ[X]) (c : ℝ) (hdeg : 2 ≤ f.natDegree)
    (hc : (f.natDegree : ℝ) < c)
    (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0) :
    ∀ (rs : List ℝ) (hrs : ∀ r ∈ rs, f.IsRoot r)
      (hsorted : rs.Pairwise (· ≤ ·))
      (hsub : (↑rs : Multiset ℝ) ≤ f.roots)
      (hgap : ConsecNoRoots f rs),
    (mkAffineInterleaving f c hdeg hc hroots_nonpos rs hrs hsorted hsub hgap).length =
      rs.length - 1
  | [], _, _, _, _ | [_], _, _, _, _ => by simp [mkAffineInterleaving]
  | _ :: r₂ :: rest, hrs, hsorted, hsub, hgap => by
    simp only [mkAffineInterleaving, List.length_cons]
    rw [mkAffineInterleaving_length f c hdeg hc hroots_nonpos
      (r₂ :: rest) (List.forall_mem_of_forall_mem_cons hrs)
      (List.pairwise_cons.mp hsorted).2 (by
        apply le_trans _ hsub
        simp [Multiset.le_iff_count, Multiset.coe_count, List.count_cons]) hgap.2]
    simp

/-- Each element of the affine interleaving is a root of `g` and satisfies
    the interlacing bounds. -/
lemma mkAffineInterleaving_spec (f : ℝ[X]) (c : ℝ) (hdeg : 2 ≤ f.natDegree)
    (hc : (f.natDegree : ℝ) < c)
    (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0) :
    ∀ (rs : List ℝ) (hrs : ∀ r ∈ rs, f.IsRoot r)
      (hsorted : rs.Pairwise (· ≤ ·))
      (hsub : (↑rs : Multiset ℝ) ≤ f.roots)
      (hgap : ConsecNoRoots f rs),
    let g := C c * f + (1 - X) * f.derivative
    (∀ s ∈ mkAffineInterleaving f c hdeg hc hroots_nonpos rs hrs hsorted hsub hgap,
      g.IsRoot s) ∧
    ListInterlaces
      (mkAffineInterleaving f c hdeg hc hroots_nonpos rs hrs hsorted hsub hgap) rs
  | [], _, _, _, _ | [_], _, _, _, _ => by
    refine ⟨?_, ?_⟩ <;> simp [mkAffineInterleaving, ListInterlaces]
  | r₁ :: r₂ :: rest, hrs, hsorted, hsub, hgap => by
    have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hsorted (.head _)
    have hrest : ∀ r ∈ r₂ :: rest, f.IsRoot r :=
      List.forall_mem_of_forall_mem_cons hrs
    have hsorted_tail := (List.pairwise_cons.mp hsorted).2
    have hsub_tail : (↑(r₂ :: rest) : Multiset ℝ) ≤ f.roots := by
      apply le_trans _ hsub
      simp [Multiset.le_iff_count, Multiset.coe_count, List.count_cons]
    have ih := mkAffineInterleaving_spec f c hdeg hc hroots_nonpos
      (r₂ :: rest) hrest hsorted_tail hsub_tail hgap.2
    simp only [mkAffineInterleaving]
    have hsub_pair : (↑[r₁, r₂] : Multiset ℝ) ≤ f.roots := by
      apply le_trans _ hsub
      simp [Multiset.le_iff_count, Multiset.coe_count, List.count_cons]
    by_cases hlt : r₁ < r₂
    · -- Distinct roots: use IVT root
      simp only [dite_eq_left hlt]
      have hspec := (exists_affineDeriv_root_between_strict hc
        (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))
        hlt
        (hroots_nonpos r₂ (Multiset.subset_of_le hsub
          (Multiset.mem_coe.mpr (.tail _ (.head _)))))).choose_spec
      constructor
      · simp_all
      · exact ⟨hspec.1.le, hspec.2.1.le, ih.2⟩
    · -- Repeated root: s = r₁ = r₂
      have hr_eq : r₁ = r₂ := le_antisymm hr₁r₂ (not_lt.mp hlt)
      simp only [dite_eq_right hlt]
      have hcount : 2 ≤ Multiset.count r₁ f.roots := by
        have : 2 ≤ Multiset.count r₁ (↑[r₁, r₁] : Multiset ℝ) := by simp
        exact le_trans this (Multiset.count_le_of_le r₁ (hr_eq ▸ hsub_pair))
      rw [count_roots] at hcount
      have hf'_root : f.derivative.IsRoot r₁ :=
        isRoot_derivative_of_rootMultiplicity_ge_two hcount
      have hg_root : (C c * f + (1 - X) * f.derivative).IsRoot r₁ := by simp_all
      constructor
      · simp_all
      · exact ⟨le_refl _, hr_eq ▸ le_refl _, ih.2⟩

/-! ## Submultiset and real-rootedness of `g`

The `d - 1` inner roots form a submultiset of `g.roots`.
Since `g` has degree `d`, it has `d - 1 ≤ roots.card ≤ d`.
The remaining factor has degree ≤ 1, so it has a root (degree 1 over ℝ
always has a root). Hence `roots.card = d`, i.e., `g` is real-rooted. -/

/-- All elements of the affine interleaving of `r₁ :: rest` are ≥ r₁. -/
private lemma mkAffineInterleaving_ge (f : ℝ[X]) (c : ℝ) (hdeg : 2 ≤ f.natDegree)
    (hc : (f.natDegree : ℝ) < c)
    (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0) :
    ∀ (r₁ : ℝ) (rest : List ℝ) (hrs : ∀ r ∈ r₁ :: rest, f.IsRoot r)
      (hsorted : (r₁ :: rest).Pairwise (· ≤ ·))
      (hsub : (↑(r₁ :: rest) : Multiset ℝ) ≤ f.roots)
      (hgap : ConsecNoRoots f (r₁ :: rest)),
    ∀ x ∈ mkAffineInterleaving f c hdeg hc hroots_nonpos (r₁ :: rest)
        hrs hsorted hsub hgap,
      r₁ ≤ x
  | _, [], _, _, _, _ => by simp [mkAffineInterleaving]
  | r₁, r₂ :: rest', hrs, hsorted, hsub, hgap => by
    intro x hx
    simp only [mkAffineInterleaving, List.mem_cons] at hx
    have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hsorted (.head _)
    rcases hx with rfl | hx
    · grind
    · have hrest : ∀ r ∈ r₂ :: rest', f.IsRoot r :=
        List.forall_mem_of_forall_mem_cons hrs
      have hsorted_tail := (List.pairwise_cons.mp hsorted).2
      have hsub_tail : (↑(r₂ :: rest') : Multiset ℝ) ≤ f.roots := by lia
      exact le_trans hr₁r₂ (mkAffineInterleaving_ge f c hdeg hc hroots_nonpos
        r₂ rest' hrest hsorted_tail hsub_tail hgap.2 x hx)

/-- Root multiplicity of `g = C c * f + (1 - X) * f'` at a nonpositive point
    is at least `f.rootMultiplicity a - 1`, provided `g ≠ 0`. -/
private lemma rootMultiplicity_sub_one_le_affineDeriv
    {f : ℝ[X]} {c : ℝ} (a : ℝ)
    (hg_ne : C c * f + (1 - X) * f.derivative ≠ 0) :
    f.rootMultiplicity a - 1 ≤
      (C c * f + (1 - X) * f.derivative).rootMultiplicity a := by
  set g := C c * f + (1 - X) * f.derivative with hg_def
  set m := f.rootMultiplicity a
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · lia
  have hf_ne : f ≠ 0 := by grind
  have hdvd_f : (X - C a) ^ m ∣ f := (le_rootMultiplicity_iff hf_ne).mp le_rfl
  have hdvd_cf : (X - C a) ^ m ∣ C c * f := dvd_mul_of_dvd_right hdvd_f _
  have hdvd_f' : (X - C a) ^ (m - 1) ∣ f.derivative :=
    pow_sub_one_dvd_derivative_of_pow_dvd hdvd_f
  have hdvd_1xf' : (X - C a) ^ (m - 1) ∣ (1 - X) * f.derivative :=
    dvd_mul_of_dvd_right hdvd_f' _
  have hdvd_cf' : (X - C a) ^ (m - 1) ∣ C c * f :=
    (pow_dvd_pow _ (Nat.sub_le m 1)).trans hdvd_cf
  have hdvd_g : (X - C a) ^ (m - 1) ∣ g := dvd_add hdvd_cf' hdvd_1xf'
  exact (le_rootMultiplicity_iff hg_ne).mpr hdvd_g

/-- Inner roots of the affine interleaving form a submultiset of `g.roots`, with the
expected multiplicity bound on repeated roots. -/
lemma mkAffineInterleaving_sub_multiset (f : ℝ[X]) (c : ℝ) (hdeg : 2 ≤ f.natDegree)
    (hc : (f.natDegree : ℝ) < c)
    (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0) :
    ∀ (rs : List ℝ) (hrs : ∀ r ∈ rs, f.IsRoot r)
      (hsorted : rs.Pairwise (· ≤ ·))
      (hsub : (↑rs : Multiset ℝ) ≤ f.roots)
      (hgap : ConsecNoRoots f rs),
    let g := C c * f + (1 - X) * f.derivative
    (↑(mkAffineInterleaving f c hdeg hc hroots_nonpos rs hrs hsorted hsub hgap) :
      Multiset ℝ) ≤ g.roots ∧
    (∀ a, a ∈ (↑rs : Multiset ℝ) →
      (↑(mkAffineInterleaving f c hdeg hc hroots_nonpos rs hrs hsorted hsub hgap) :
        Multiset ℝ).count a + 1 ≤ (↑rs : Multiset ℝ).count a) := by
  intro rs hrs hsorted hsub hgap
  induction rs using List.recOn with
  | nil =>
      simp [mkAffineInterleaving]
  | cons r₁ rest ih =>
      cases rest with
      | nil =>
          simp [mkAffineInterleaving]
      | cons r₂ rest =>
          have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hsorted (.head _)
          have hrest : ∀ r ∈ r₂ :: rest, f.IsRoot r :=
            List.forall_mem_of_forall_mem_cons hrs
          have hsorted_tail := (List.pairwise_cons.mp hsorted).2
          have hsub_tail : (↑(r₂ :: rest) : Multiset ℝ) ≤ f.roots := by
            apply le_trans _ hsub
            simp [Multiset.le_iff_count, Multiset.coe_count, List.count_cons]
          have ih := ih hrest hsorted_tail hsub_tail hgap.2
          have hc_ne : c ≠ (f.natDegree : ℝ) := ne_of_gt hc
          have hg_ne : C c * f + (1 - X) * f.derivative ≠ 0 :=
            affineDeriv_ne_zero (by rintro rfl; simp at hdeg) (by lia) hc_ne
          have hge_tail : ∀ x ∈ mkAffineInterleaving f c hdeg hc hroots_nonpos
              (r₂ :: rest) hrest hsorted_tail hsub_tail hgap.2, r₂ ≤ x :=
            mkAffineInterleaving_ge f c hdeg hc hroots_nonpos
              r₂ rest hrest hsorted_tail hsub_tail hgap.2
          let s : ℝ := if hlt : r₁ < r₂ then
            (exists_affineDeriv_root_between_strict hc
              (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))
              hlt
              (hroots_nonpos r₂ (Multiset.subset_of_le hsub
                (Multiset.mem_coe.mpr (.tail _ (.head _)))))).choose
          else r₁
          have hunfold : mkAffineInterleaving f c hdeg hc hroots_nonpos
              (r₁ :: r₂ :: rest) hrs hsorted hsub hgap =
            s :: mkAffineInterleaving f c hdeg hc hroots_nonpos
              (r₂ :: rest) hrest hsorted_tail hsub_tail hgap.2 := rfl
          rw [hunfold]
          constructor
          · change s ::ₘ ↑(mkAffineInterleaving f c hdeg hc hroots_nonpos
              (r₂ :: rest) hrest hsorted_tail hsub_tail hgap.2) ≤
              (C c * f + (1 - X) * f.derivative).roots
            have hs_root : (C c * f + (1 - X) * f.derivative).IsRoot s :=
              (mkAffineInterleaving_spec f c hdeg hc hroots_nonpos
                (r₁ :: r₂ :: rest) hrs hsorted (le_of_eq rfl |>.trans hsub)
                hgap).1 s (by simp_all)
            have hs_mem : s ∈ (C c * f + (1 - X) * f.derivative).roots :=
              (mem_roots hg_ne).mpr hs_root
            by_cases hlt : r₁ < r₂
            · have hspec := (exists_affineDeriv_root_between_strict hc
                (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))
                hlt
                (hroots_nonpos r₂ (Multiset.subset_of_le hsub
                  (Multiset.mem_coe.mpr (.tail _ (.head _)))))).choose_spec
              have hs_notin : s ∉ (↑(mkAffineInterleaving f c hdeg hc hroots_nonpos
                  (r₂ :: rest) hrest hsorted_tail hsub_tail hgap.2) : Multiset ℝ) := by
                rw [Multiset.mem_coe]
                grind
              rw [Multiset.cons_le_of_notMem hs_notin]
              lia
            · have hr_eq : r₁ = r₂ := le_antisymm hr₁r₂ (not_lt.mp hlt)
              have hs : s = r₁ := dite_eq_right hlt
              rw [Multiset.le_iff_count]
              intro a
              rw [Multiset.count_cons]
              split_ifs with heq
              · have ih_B := ih.2 a (by
                  simp_all)
                have hcount_full : (↑(r₁ :: r₂ :: rest) : Multiset ℝ).count a ≤
                    f.rootMultiplicity a := by
                  rw [← count_roots]
                  exact Multiset.count_le_of_le a hsub
                have : (↑(r₁ :: r₂ :: rest) : Multiset ℝ).count a =
                    (↑(r₂ :: rest) : Multiset ℝ).count a + 1 := by
                  simp_all
                rw [this] at hcount_full
                have hmult := rootMultiplicity_sub_one_le_affineDeriv a hg_ne
                simp only [count_roots] at *
                lia
              · simp only [add_zero]
                exact Multiset.count_le_of_le a ih.1
          · intro a ha
            change a ∈ (r₁ ::ₘ ↑(r₂ :: rest) : Multiset ℝ) at ha
            rw [Multiset.mem_cons] at ha
            change (s ::ₘ ↑(mkAffineInterleaving f c hdeg hc hroots_nonpos
              (r₂ :: rest) hrest hsorted_tail hsub_tail hgap.2)).count a + 1 ≤
              (r₁ ::ₘ ↑(r₂ :: rest) : Multiset ℝ).count a
            rw [Multiset.count_cons, Multiset.count_cons]
            by_cases heq : a = s <;> by_cases hr₁a : a = r₁
            · rw [ite_eq_left heq, ite_eq_left hr₁a]
              have hr_eq : r₁ = r₂ := by grind
              simp_all
            · rw [ite_eq_left heq, ite_eq_right hr₁a]
              exfalso
              rcases ha with rfl | ha_tail
              · lia
              · by_cases hlt : r₁ < r₂
                · have hspec := (exists_affineDeriv_root_between_strict hc
                    (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))
                    hlt
                    (hroots_nonpos r₂ (Multiset.subset_of_le hsub
                      (Multiset.mem_coe.mpr (.tail _ (.head _)))))).choose_spec
                  have : a < r₂ := by lia
                  have : r₂ ≤ a := by
                    have hmem := Multiset.mem_coe.mp ha_tail
                    rcases List.mem_cons.mp hmem with h | h
                    · simp_all
                    · exact List.rel_of_pairwise_cons hsorted_tail h
                  linarith
                · lia
            · rw [ite_eq_right heq, ite_eq_left hr₁a]
              by_cases ha2 : a ∈ (↑(r₂ :: rest) : Multiset ℝ)
              · grind
              · have hlt : r₁ < r₂ := by lia
                have : (↑(mkAffineInterleaving f c hdeg hc hroots_nonpos (r₂ :: rest) hrest
                    hsorted_tail hsub_tail hgap.2) : Multiset ℝ).count a = 0 :=
                  Multiset.count_eq_zero.mpr (by
                    rw [Multiset.mem_coe]
                    grind)
                lia
            · grind

/-- Inner roots are a submultiset of `g.roots`. -/
lemma mkAffineInterleaving_sub_roots (f : ℝ[X]) (c : ℝ) (hdeg : 2 ≤ f.natDegree)
    (hc : (f.natDegree : ℝ) < c)
    (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0) :
    ∀ (rs : List ℝ) (hrs : ∀ r ∈ rs, f.IsRoot r)
      (hsorted : rs.Pairwise (· ≤ ·))
      (hsub : (↑rs : Multiset ℝ) ≤ f.roots)
      (hgap : ConsecNoRoots f rs),
    let g := C c * f + (1 - X) * f.derivative
    (↑(mkAffineInterleaving f c hdeg hc hroots_nonpos rs hrs hsorted hsub hgap) :
      Multiset ℝ) ≤ g.roots :=
  fun rs hrs hsorted hsub hgap =>
    (mkAffineInterleaving_sub_multiset f c hdeg hc hroots_nonpos rs hrs hsorted hsub hgap).1

/-- A polynomial of degree `d` with at least `d - 1` real roots
    actually has `d` real roots: the quotient by the known root product
    has degree 1, which must have a root over ℝ. -/
lemma roots_card_of_sub_pred {p : ℝ[X]} (hp : p ≠ 0)
    {S : Multiset ℝ} (hle : S ≤ p.roots)
    (hcard : S.card + 1 = p.natDegree) :
    p.Splits := by
  by_contra hne
  have h1 : p.roots.card ≤ p.natDegree := card_roots' p
  have h2 : S.card ≤ p.roots.card := Multiset.card_le_card hle
  have hne_card : p.roots.card ≠ p.natDegree :=
    fun h => hne (Polynomial.splits_iff_card_roots.mpr h)
  have hrc : p.roots.card = p.natDegree - 1 := by lia
  set rprod := (p.roots.map (X - C ·)).prod with hrprod_def
  obtain ⟨q, hpq⟩ := prod_multiset_X_sub_C_dvd p
  have hrprod_ne : rprod ≠ 0 := Polynomial.multiset_prod_X_sub_C_ne_zero p.roots
  have hq_ne : q ≠ 0 := right_ne_zero_of_mul (hpq ▸ hp)
  have hrprod_roots : rprod.roots = p.roots := roots_multiset_prod_X_sub_C p.roots
  have hroots : p.roots = rprod.roots + q.roots := by
    conv_lhs => rw [hpq]; exact roots_mul (hpq ▸ hp)
  have hq_empty : q.roots = 0 := by
    rw [hrprod_roots] at hroots
    have hcard_eq := congr_arg Multiset.card hroots
    rw [Multiset.card_add] at hcard_eq
    exact Multiset.card_eq_zero.mp (by lia)
  have hq_deg : q.natDegree = 1 := by
    have h3 := natDegree_mul hrprod_ne hq_ne
    rw [natDegree_multiset_prod_X_sub_C_eq_card, hrc, ← hpq] at h3
    lia
  have hq_split := (isRealRooted_of_degree_one hq_deg).2
  have hq_card := Polynomial.splits_iff_card_roots.mp hq_split
  rw [hq_empty, Multiset.card_zero, hq_deg] at hq_card
  lia

/-- A submultiset whose cardinality is exactly one smaller differs by a singleton. -/
private lemma exists_cons_of_card_succ {α : Type*} {s t : Multiset α}
    (hsub : s ≤ t) (hcard : s.card + 1 = t.card) :
    ∃ a, t = a ::ₘ s := by
  rcases Multiset.le_iff_exists_add.mp hsub with ⟨u, rfl⟩
  have hu_card : u.card = 1 := by simp_all
  rcases Multiset.card_eq_one.mp hu_card with ⟨a, rfl⟩
  refine ⟨a, ?_⟩
  simpa using (Multiset.add_comm s ({a} : Multiset α))

private lemma eval_ne_zero_of_not_dvd_X_sub_C {p : ℝ[X]} {a : ℝ}
    (h : ¬ (X - C a) ∣ p) :
    p.eval a ≠ 0 :=
  fun hp => h ((dvd_iff_isRoot).2 hp)

private lemma neg_pow_prod_nonneg_of_all_nonpos (s : Multiset ℝ)
    (hs : ∀ x ∈ s, x ≤ 0) :
    0 ≤ (-1 : ℝ) ^ s.card * s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ih' := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
      have ha : a ≤ 0 := hs a (Multiset.mem_cons_self _ _)
      rw [Multiset.card_cons, Multiset.prod_cons]
      have : (-1 : ℝ) ^ (s.card + 1) * (a * s.prod) =
          (-a) * ((-1 : ℝ) ^ s.card * s.prod) := by
        ring
      rw [this]
      exact mul_nonneg (by simp_all) ih'

/-- Removing a leftmost root factor leaves only roots strictly to its right. -/
private lemma roots_gt_of_leftmost_factor {f q : ℝ[X]} {r : ℝ} {m : ℕ}
    (hq₀ : q ≠ 0) (hfact : f = (X - C r) ^ m * q)
    (hnodvd : ¬ (X - C r) ∣ q) {rest : List ℝ}
    (hsorted : (r :: rest).Pairwise (· ≤ ·))
    (hroots : (↑(r :: rest) : Multiset ℝ) = f.roots) :
    ∀ t ∈ q.roots, r < t := by
  intro t ht
  have ht_root : q.IsRoot t := (mem_roots hq₀).mp ht
  have ht_ne : t ≠ r := fun htr => hnodvd ((dvd_iff_isRoot).2 (htr ▸ ht_root))
  have ht_mem_f : t ∈ f.roots := by
    rw [hfact, roots_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) hq₀),
      Multiset.mem_add]
    exact Or.inr ht
  have ht_mem : t ∈ r :: rest := Multiset.mem_coe.mp (hroots.symm ▸ ht_mem_f)
  rcases List.mem_cons.mp ht_mem with rfl | ht_rest
  · exact (ht_ne rfl).elim
  · exact lt_of_le_of_ne (List.rel_of_pairwise_cons hsorted ht_rest) (Ne.symm ht_ne)

/-- A quotient's roots are right of the first slot when its full roots are an extra root plus
an interlacing list. -/
private lemma roots_gt_of_extra_and_interlacing {g q : ℝ[X]} {r u : ℝ} {m : ℕ}
    (hq₀ : q ≠ 0) (hfact : g = (X - C r) ^ m * q)
    (hnodvd : ¬ (X - C r) ∣ q) {ss rest : List ℝ}
    (hroots : (↑(u :: ss) : Multiset ℝ) = g.roots)
    (hint : ListInterlaces ss (r :: rest)) (hu : r < u) :
    ∀ t ∈ q.roots, r < t := by
  intro t ht
  have ht_root : q.IsRoot t := (mem_roots hq₀).mp ht
  have ht_ne : t ≠ r := fun htr => hnodvd ((dvd_iff_isRoot).2 (htr ▸ ht_root))
  have ht_mem_g : t ∈ g.roots := by
    rw [hfact, roots_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) hq₀),
      Multiset.mem_add]
    exact Or.inr ht
  have ht_mem : t ∈ u :: ss := Multiset.mem_coe.mp (hroots.symm ▸ ht_mem_g)
  rcases List.mem_cons.mp ht_mem with rfl | ht_ss
  · exact hu
  · exact lt_of_le_of_ne (listInterlaces_all_ge ss rest r hint t ht_ss) (Ne.symm ht_ne)

/-- Successive positive quotients supported to the right give incompatible signs at the slot. -/
private lemma quotient_eval_sign_contradiction {q qg : ℝ[X]} {r : ℝ} {m : ℕ}
    (hq_rr : q ≠ 0 ∧ q.Splits) (hqg_rr : qg ≠ 0 ∧ qg.Splits)
    (hq_pos : HasPosLeadingCoeff q) (hqg_pos : HasPosLeadingCoeff qg)
    (hq_roots : ∀ t ∈ q.roots, r < t) (hqg_roots : ∀ t ∈ qg.roots, r < t)
    (hcard : qg.roots.card = q.roots.card + 1)
    (hq_nodvd : ¬ (X - C r) ∣ q)
    (heval : qg.eval r = ((1 - r) * (m : ℝ)) * q.eval r)
    (hr : r ≤ 0) (hm : 0 < m) : False := by
  let Pq := (q.roots.map (r - ·)).prod
  let Pg := (qg.roots.map (r - ·)).prod
  have hPq : 0 ≤ (-1 : ℝ) ^ q.roots.card * Pq := by
    simpa only [Pq, Multiset.card_map] using
      neg_pow_prod_nonneg_of_all_nonpos (q.roots.map (r - ·)) (by
        intro x hx
        rcases Multiset.mem_map.mp hx with ⟨t, ht, rfl⟩
        exact sub_nonpos.mpr (hq_roots t ht).le)
  have hPg : 0 ≤ (-1 : ℝ) ^ qg.roots.card * Pg := by
    simpa only [Pg, Multiset.card_map] using
      neg_pow_prod_nonneg_of_all_nonpos (qg.roots.map (r - ·)) (by
        intro x hx
        rcases Multiset.mem_map.mp hx with ⟨t, ht, rfl⟩
        exact sub_nonpos.mpr (hqg_roots t ht).le)
  have hPg' : 0 ≤ -(((-1 : ℝ) ^ q.roots.card) * Pg) := by
    rw [hcard, pow_add, pow_one, mul_neg_one] at hPg
    grind
  have hprod : Pg * Pq ≤ 0 := by
    have hmulp := mul_nonneg hPg' hPq
    have hsquare : ((-1 : ℝ) ^ q.roots.card) * ((-1 : ℝ) ^ q.roots.card) = 1 := by
      nth_rewrite 2 [← one_mul q.roots.card]
      rw [← pow_add, one_mul]
      norm_num
    have hmulp' : 0 ≤ -(Pg * Pq) := by nlinarith [hmulp, hsquare]
    linarith
  have hnonpos : qg.eval r * q.eval r ≤ 0 := by
    rw [Polynomial.Splits.eval_eq_prod_roots hqg_rr.2 r,
      Polynomial.Splits.eval_eq_prod_roots hq_rr.2 r,
      show (q.roots.map (r - ·)).prod = Pq by rfl,
      show (qg.roots.map (r - ·)).prod = Pg by rfl]
    nlinarith [mul_pos hqg_pos hq_pos]
  have hq_eval_ne := eval_ne_zero_of_not_dvd_X_sub_C hq_nodvd
  have hpos : 0 < qg.eval r * q.eval r := by
    rw [heval]
    nlinarith [sq_pos_iff.mpr hq_eval_ne,
      mul_pos (show 0 < 1 - r by linarith) (Nat.cast_pos.mpr hm)]
  linarith

/-- Package a same-degree interlacing witness once the extra root on the `g` side
    is known to lie to the left of the first root of `f`. -/
private lemma strictInterl_of_extra_root_left {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0)
    (hf : f.Splits) (hg : g.Splits)
    {u r₁ : ℝ} {ss rest : List ℝ}
    (hrs_sorted : (r₁ :: rest).Pairwise (· ≤ ·))
    (hrs_eq : (↑(r₁ :: rest) : Multiset ℝ) = f.roots)
    (hss_eq : (↑(u :: ss) : Multiset ℝ) = g.roots)
    (hint : ListInterlaces ss (r₁ :: rest))
    (hu : u ≤ r₁) :
    StrictInterl g f := by
  have hug_sorted : (u :: ss).Pairwise (· ≤ ·) := by
    exact List.pairwise_cons.mpr ⟨fun s hs ↦
      le_trans hu (listInterlaces_all_ge ss rest r₁ hint s hs),
      pairwise_le_of_listInterlaces ss (r₁ :: rest) hint⟩
  have hlen : ss.length = rest.length := listInterlaces_cons_length_eq hint
  exact ⟨⟨hg₀, hg⟩, ⟨hf₀, hf⟩, u :: ss, r₁ :: rest, hug_sorted, hrs_sorted,
    hss_eq, hrs_eq, Or.inr ⟨by simp [hlen], ⟨hu, hint⟩⟩⟩

/-- Evaluation of the residual factor in the affine-derivative factorization. -/
private lemma eval_affine_quotient_at_root {f g q qg : ℝ[X]} {c r : ℝ} {m : ℕ}
    (hm_pos : 0 < m) (hg_def : g = C c * f + (1 - X) * f.derivative)
    (hf_fact : f = (X - C r) ^ m * q)
    (hg_fact : g = (X - C r) ^ (m - 1) * qg) :
    qg.eval r = ((1 - r) * (m : ℝ)) * q.eval r := by
  have hm_succ : m = (m - 1) + 1 := by lia
  have hf_deriv_fact : f.derivative = (X - C r) ^ (m - 1) *
      (C (m : ℝ) * q + (X - C r) * q.derivative) := by
    rw [hf_fact, derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C,
      sub_zero, hm_succ, pow_succ']
    grind
  have hg_expand : g = (X - C r) ^ (m - 1) *
      (C c * (X - C r) * q +
        (1 - X) * (C (m : ℝ) * q + (X - C r) * q.derivative)) := by
    rw [hg_def, hf_deriv_fact, hf_fact, hm_succ, pow_succ']
    grind
  have hqg_eq : qg = C c * (X - C r) * q +
      (1 - X) * (C (m : ℝ) * q + (X - C r) * q.derivative) := by
    apply mul_left_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero _))
    rw [← hg_fact, hg_expand]
  rw [hqg_eq]
  simp
  ring

/-- The remaining affine-derivative root cannot lie right of the first original root. -/
private lemma extra_affine_root_not_right {f g : ℝ[X]} (hf : f.Splits)
    (hf_pos : HasPosLeadingCoeff f) {c : ℝ} {d : ℕ}
    (hg_def : g = C c * f + (1 - X) * f.derivative)
    (hd_def : d = f.natDegree) (hg_deg : g.natDegree = d)
    (hg_pos : HasPosLeadingCoeff g) (hg_rr : g.Splits)
    {r₁ u : ℝ} {ss rest : List ℝ}
    (hrs_sorted : (r₁ :: rest).Pairwise (· ≤ ·))
    (hrs_eq : (↑(r₁ :: rest) : Multiset ℝ) = f.roots)
    (hss_eq : (↑(u :: ss) : Multiset ℝ) = g.roots)
    (hint : ListInterlaces ss (r₁ :: rest))
    (hcount : (↑ss : Multiset ℝ).count r₁ + 1 ≤
      (↑(r₁ :: rest) : Multiset ℝ).count r₁)
    (hr₁_nonpos : r₁ ≤ 0) (hu : r₁ < u) : False := by
  set m := f.rootMultiplicity r₁ with hm_def
  have hr₁_root : f.IsRoot r₁ := (mem_roots hf_pos.ne_zero).mp (by
    rw [← hrs_eq]
    simp)
  have hm_pos : 0 < m := by
    rw [hm_def]
    exact (rootMultiplicity_pos hf_pos.ne_zero).mpr hr₁_root
  have hrs_count : (↑(r₁ :: rest) : Multiset ℝ).count r₁ = m := by simp_all
  have hu_ne : u ≠ r₁ := ne_of_gt hu
  have hgmult_eq_ss : g.rootMultiplicity r₁ = (↑ss : Multiset ℝ).count r₁ := by
    rw [← count_roots, ← hss_eq]
    simp [hu_ne]
  have hgmult_ge : m - 1 ≤ g.rootMultiplicity r₁ := by
    rw [hg_def, hm_def]
    exact rootMultiplicity_sub_one_le_affineDeriv r₁ (hg_def ▸ hg_pos.ne_zero)
  have hgmult_eq : g.rootMultiplicity r₁ = m - 1 := by lia
  obtain ⟨q, hf_fact, hq_nodvd⟩ :=
    exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf_pos.ne_zero r₁
  obtain ⟨qg, hg_fact, hqg_nodvd⟩ :=
    exists_eq_pow_rootMultiplicity_mul_and_not_dvd g hg_pos.ne_zero r₁
  have hf_fact' : f = (X - C r₁) ^ m * q := by lia
  have hg_fact' : g = (X - C r₁) ^ (m - 1) * qg := by lia
  have hq_ne : q ≠ 0 := by
    intro hq
    apply hf_pos.ne_zero
    rw [hf_fact, hq, mul_zero]
  have hqg_ne : qg ≠ 0 := by
    intro hqg
    apply hg_pos.ne_zero
    rw [hg_fact, hqg, mul_zero]
  have hq_rr : q ≠ 0 ∧ q.Splits :=
    isRealRooted_of_dvd (hf_fact' ▸ hf_pos.ne_zero) (hf_fact' ▸ hf) hq_ne
      ⟨(X - C r₁) ^ m, by rw [mul_comm]⟩
  have hqg_rr : qg ≠ 0 ∧ qg.Splits :=
    isRealRooted_of_dvd (hg_fact' ▸ hg_pos.ne_zero) (hg_fact' ▸ hg_rr) hqg_ne
      ⟨(X - C r₁) ^ (m - 1), by rw [mul_comm]⟩
  have hq_pos : HasPosLeadingCoeff q :=
    hasPosLeadingCoeff_of_pow_X_sub_C_mul (by simpa [hf_fact'] using hf_pos)
  have hqg_pos : HasPosLeadingCoeff qg :=
    hasPosLeadingCoeff_of_pow_X_sub_C_mul (by simpa [hg_fact'] using hg_pos)
  have hq_roots := roots_gt_of_leftmost_factor hq_ne hf_fact'
    hq_nodvd hrs_sorted hrs_eq
  have hqg_roots := roots_gt_of_extra_and_interlacing hqg_ne hg_fact'
    hqg_nodvd hss_eq hint hu
  have hqg_eval := eval_affine_quotient_at_root hm_pos hg_def hf_fact' hg_fact'
  have hm_le_d : m ≤ d := by
    calc
      m = f.roots.count r₁ := by lia
      _ ≤ f.roots.card := Multiset.count_le_card _ _
      _ = d := by rw [Polynomial.splits_iff_card_roots.mp hf, hd_def]
  have hq_deg : q.natDegree = d - m := by
    have hmul := natDegree_mul (p := (X - C r₁) ^ m) (q := q)
      (pow_ne_zero _ (X_sub_C_ne_zero _)) hq_ne
    rw [← hf_fact', ← hd_def, (monic_X_sub_C r₁).natDegree_pow, natDegree_X_sub_C] at hmul
    lia
  have hqg_deg : qg.natDegree = d - (m - 1) := by
    have hmul := natDegree_mul (p := (X - C r₁) ^ (m - 1)) (q := qg)
      (pow_ne_zero _ (X_sub_C_ne_zero _)) hqg_ne
    rw [← hg_fact', hg_deg, (monic_X_sub_C r₁).natDegree_pow, natDegree_X_sub_C] at hmul
    lia
  have hcard : qg.roots.card = q.roots.card + 1 := by
    rw [Polynomial.splits_iff_card_roots.mp hqg_rr.2,
      Polynomial.splits_iff_card_roots.mp hq_rr.2, hqg_deg, hq_deg]
    lia
  exact quotient_eval_sign_contradiction hq_rr hqg_rr hq_pos hqg_pos hq_roots
    hqg_roots hcard hq_nodvd hqg_eval hr₁_nonpos hm_pos

/-! ## Main theorem -/

/-- **Affine derivative interlacing**: if `f` is real-rooted with all roots ≤ 0,
positive leading coefficient, degree ≥ 2, and `c > natDegree f`, then
`C c * f + (1 - X) * f.derivative` interlaces `f` (same-degree `StrictInterl`). -/
theorem strictInterl_affine_derivative {f : ℝ[X]} (hf : f.Splits)
    (hdeg : 2 ≤ f.natDegree)
    (hf₀ : HasPosLeadingCoeff f)
    (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    {c : ℝ} (hc : (f.natDegree : ℝ) < c) :
    StrictInterl (C c * f + (1 - X) * f.derivative) f := by
  set g := C c * f + (1 - X) * f.derivative with hg_def
  set d := f.natDegree with hd_def
  have hc_ne : c ≠ (d : ℝ) := ne_of_gt hc
  have hg_deg : g.natDegree = d := natDegree_affineDeriv hf₀.ne_zero (by lia) hc_ne
  -- Sort the roots of f
  set rs := f.roots.sort (· ≤ ·) with hrs_def
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_length : rs.length = d := by
    rw [hrs_def, Multiset.length_sort, Polynomial.splits_iff_card_roots.mp hf]
  have hrs_root : ∀ r ∈ rs, f.IsRoot r := by simp_all
  have hsub_rs : (↑rs : Multiset ℝ) ≤ f.roots := le_of_eq hrs_eq
  have hgap_rs : ConsecNoRoots f rs := consecNoRoots_of_sorted_eq hrs_eq hrs_sorted
  -- Construct d-1 inner roots of g
  set ss := mkAffineInterleaving f c hdeg hc hroots_nonpos rs hrs_root hrs_sorted hsub_rs
    hgap_rs
  have hss_length : ss.length = d - 1 := by rw [mkAffineInterleaving_length]; lia
  have hspec := mkAffineInterleaving_spec f c hdeg hc hroots_nonpos
    rs hrs_root hrs_sorted hsub_rs hgap_rs
  have hss_interlaces : ListInterlaces ss rs := hspec.2
  -- Inner roots are a submultiset of g.roots
  have hsub_info := mkAffineInterleaving_sub_multiset f c hdeg hc hroots_nonpos
    rs hrs_root hrs_sorted hsub_rs hgap_rs
  have hss_sub : (↑ss : Multiset ℝ) ≤ g.roots := hsub_info.1
  have hss_count_bound :
      ∀ a,
        a ∈ (↑rs : Multiset ℝ) →
        (↑ss : Multiset ℝ).count a + 1 ≤ (↑rs : Multiset ℝ).count a :=
    hsub_info.2
  -- g is real-rooted: degree d with d-1 inner roots → d total roots
  have hg₀ : HasPosLeadingCoeff g := by
    rw [HasPosLeadingCoeff, hg_def, leadingCoeff_affineDeriv hf₀.ne_zero (by lia) hc_ne]
    exact mul_pos (sub_pos.mpr hc) hf₀
  have hg_rr : g.Splits :=
    roots_card_of_sub_pred hg₀.ne_zero hss_sub (by
      rw [Multiset.coe_card, hss_length, hg_deg]; lia)
  have hss_eq_card : (↑ss : Multiset ℝ).card + 1 = g.roots.card := by
    rw [Multiset.coe_card, hss_length, Polynomial.splits_iff_card_roots.mp hg_rr, hg_deg]
    lia
  obtain ⟨r₁, rest, hrs_cons⟩ : ∃ r₁ rest, rs = r₁ :: rest := by
    cases h : rs with
    | nil =>
        grind
    | cons r rest =>
        lia
  obtain ⟨u, hu_roots_eq⟩ : ∃ u, g.roots = u ::ₘ (↑ss : Multiset ℝ) :=
    exists_cons_of_card_succ hss_sub hss_eq_card
  have hu_roots_eq' : (↑(u :: ss) : Multiset ℝ) = g.roots := by simp_all
  rw [hrs_cons] at hrs_sorted hrs_eq hss_interlaces hss_count_bound
  have hr₁_root : f.IsRoot r₁ := hrs_root r₁ (by simp [hrs_cons])
  have hr₁_mem_f : r₁ ∈ f.roots := (mem_roots hf₀.ne_zero).mpr hr₁_root
  have hr₁_nonpos : r₁ ≤ 0 := hroots_nonpos r₁ hr₁_mem_f
  by_cases hu : u ≤ r₁
  · exact strictInterl_of_extra_root_left hf₀.ne_zero hg₀.ne_zero hf hg_rr hrs_sorted
      hrs_eq hu_roots_eq' hss_interlaces hu
  · exact (extra_affine_root_not_right hf hf₀ hg_def hd_def hg_deg hg₀ hg_rr
      hrs_sorted hrs_eq hu_roots_eq' hss_interlaces
      (hss_count_bound r₁ (by simp)) hr₁_nonpos (lt_of_not_ge hu)).elim

/-- Degree 1 version: both `g` and `f` have degree 1, and `g`'s root is left of `f`'s. -/
theorem strictInterl_affine_derivative_deg_one {f : ℝ[X]} (hf : f.Splits)
    (hdeg : f.natDegree = 1)
    (hf₀ : HasPosLeadingCoeff f)
    (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    {c : ℝ} (hc : (f.natDegree : ℝ) < c) :
    StrictInterl (C c * f + (1 - X) * f.derivative) f := by
  set g := C c * f + (1 - X) * f.derivative with hg_def
  have hc1 : (1 : ℝ) < c := by simp_all
  have hc_ne : c ≠ (f.natDegree : ℝ) := ne_of_gt hc
  have hg_deg : g.natDegree = 1 := by rw [natDegree_affineDeriv hf₀.ne_zero (by lia) hc_ne, hdeg]
  have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_degree_one hg_deg
  have hg_lc_pos : 0 < g.leadingCoeff := by
    rw [leadingCoeff_affineDeriv hf₀.ne_zero (by lia) hc_ne, hdeg]
    exact mul_pos (by simp_all) hf₀
  obtain ⟨r, hr_eq⟩ :=
    Multiset.card_eq_one.mp (show f.roots.card = 1 by
      rw [Polynomial.splits_iff_card_roots.mp hf, hdeg])
  obtain ⟨s, hs_eq⟩ :=
    Multiset.card_eq_one.mp (show g.roots.card = 1 by
      rw [Polynomial.splits_iff_card_roots.mp hg_rr.2, hg_deg])
  have hr_root : f.IsRoot r :=
    (mem_roots hf₀.ne_zero).mp (hr_eq ▸ Multiset.mem_singleton_self r)
  have hr_nonpos : r ≤ 0 := hroots_nonpos r (hr_eq ▸ Multiset.mem_singleton_self r)
  have hgr_pos : 0 < g.eval r := by
    rw [eval_affineDeriv_at_root hr_root c]
    apply mul_pos (by linarith)
    have hdeg0 : f.derivative.natDegree = 0 := by rw [f.natDegree_derivative, hdeg]
    have hc0 : f.derivative.coeff 0 = f.leadingCoeff := by
      rw [coeff_derivative]; simp [Polynomial.leadingCoeff, hdeg]
    rw [eq_C_of_natDegree_eq_zero hdeg0, eval_C, hc0]
    exact hf₀
  have hgr_eq : g.eval r = g.leadingCoeff * (r - s) := by
    rw [Polynomial.Splits.eval_eq_prod_roots hg_rr.2 r, hs_eq]; simp
  have hsr : s ≤ r := by nlinarith
  exact ⟨hg_rr, ⟨hf₀.ne_zero, hf⟩, [s], [r], List.pairwise_singleton _ _,
    List.pairwise_singleton _ _, by simp [hs_eq], by simp [hr_eq],
    Or.inr ⟨rfl, hsr, trivial⟩⟩

/-- Combined version for degree ≥ 1. -/
theorem strictInterl_affine_derivative' {f : ℝ[X]} (hf : f.Splits) (hdeg : 1 ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    {c : ℝ} (hc : (f.natDegree : ℝ) < c) :
    StrictInterl (C c * f + (1 - X) * f.derivative) f := by
  rcases eq_or_lt_of_le hdeg with h | h
  · exact strictInterl_affine_derivative_deg_one hf h.symm hf_pos hroots_nonpos hc
  · exact strictInterl_affine_derivative hf h hf_pos hroots_nonpos hc

/-! ## Sign wrappers at nonpositive roots

These give the sign of the affine derivative `g = C c * f + (1 - X) * f'` at a
nonpositive root `r` of `f` directly in terms of the sign of `f'(r)`, using
`g(r) = (1 - r) * f'(r)` with `1 - r > 0`. They complement
`eval_affineDeriv_eq_zero_iff` and remove the local `(1 - r) > 0` rewriting that
otherwise recurs in sign-crossing / interleaving arguments. -/

/-- At a nonpositive root `r` of `f`, the affine derivative is positive iff `f'`
is positive there. -/
lemma eval_affineDeriv_pos_iff {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) (c : ℝ)
    (hr_nonpos : r ≤ 0) :
    0 < (C c * f + (1 - X) * f.derivative).eval r ↔ 0 < f.derivative.eval r := by
  rw [eval_affineDeriv_at_root hr c]
  have h1 : (0 : ℝ) < 1 - r := by linarith
  simp_all

/-- At a nonpositive root `r` of `f`, the affine derivative is negative iff `f'`
is negative there. -/
lemma eval_affineDeriv_neg_iff {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) (c : ℝ)
    (hr_nonpos : r ≤ 0) :
    (C c * f + (1 - X) * f.derivative).eval r < 0 ↔ f.derivative.eval r < 0 := by
  rw [eval_affineDeriv_at_root hr c]
  have h1 : (0 : ℝ) < 1 - r := by linarith
  constructor
  · intro h
    exact lt_of_not_ge fun hx => absurd h (not_lt.mpr (mul_nonneg h1.le hx))
  · intro h
    exact mul_neg_of_pos_of_neg h1 h

/-- **Applied form** of `strictInterl_affine_derivative'` for polynomials with
nonnegative coefficients. Such polynomials automatically have nonpositive roots
(`roots_nonpos_of_hasNonnegCoeffs`) and positive leading coefficient
(`HasNonnegCoeffs.pos_leadingCoeff`), so only real-rootedness, degree `≥ 1`, and
`c > natDegree f` need to be supplied. -/
theorem strictInterl_affine_derivative_of_nonnegCoeffs {f : ℝ[X]} (hf : f.Splits)
    (hdeg : 1 ≤ f.natDegree) (hfnn : HasNonnegCoeffs f)
    {c : ℝ} (hc : (f.natDegree : ℝ) < c) :
    StrictInterl (C c * f + (1 - X) * f.derivative) f := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hdeg
  exact strictInterl_affine_derivative' hf hdeg (hfnn.pos_leadingCoeff hf0)
    (roots_nonpos_of_hasNonnegCoeffs hfnn) hc

/-- If `f` is split with nonnegative coefficients and degree at least two, then
the derivative block `(1 - X) * f'` lies on the right of `f` in the oriented
`StrictInterl` relation. -/
theorem strictInterl_one_sub_X_mul_derivative_right_of_nonnegCoeffs {f : ℝ[X]}
    (hf : f.Splits) (hdeg : 2 ≤ f.natDegree) (hnn : HasNonnegCoeffs f) :
    StrictInterl f ((1 - X) * f.derivative) := by
  have hder : StrictInterl f.derivative f :=
    (derivative_interlaces_of_natDegree_ne_zero hf (by lia)).toStrictInterl
  have hnn' : HasNonnegCoeffs f.derivative := hnn.derivative
  have hf'_pos : HasPosLeadingCoeff f.derivative := hnn'.pos_leadingCoeff hder.1.1
  have hf_pos : HasPosLeadingCoeff f := hnn.pos_leadingCoeff <| by
    rintro rfl
    simp at hdeg
  have hf_le1 : ∀ s ∈ f.roots, s ≤ 1 := by
    intro s hs
    linarith [roots_nonpos_of_hasNonnegCoeffs hnn s hs]
  have hf'_le1 : ∀ s ∈ f.derivative.roots, s ≤ 1 := by
    intro s hs
    linarith [roots_nonpos_of_hasNonnegCoeffs hnn' s hs]
  have hdeg' : f.derivative.natDegree + 1 = f.natDegree := by
    rw [f.natDegree_derivative]
    lia
  have hmain : StrictInterl f ((X - C 1) * f.derivative) :=
    (strictInterl_iff_strictInterl_mul_X_sub_C_of_roots_le
      1 hder.1.2 hf hf'_pos hf_pos hf'_le1 hf_le1 hdeg').mp
      hder
  have hscaled : StrictInterl f (C (-1) * ((X - C 1) * f.derivative)) :=
    StrictInterl.C_mul_right hmain (by simp)
  grind

end RealRooted
