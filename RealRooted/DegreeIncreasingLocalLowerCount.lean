import RealRooted.SameDegreeMultiplicityLowerCount
import RealRooted.RootSumBounds

/-!
# Issue #42: degree-increasing per-root multiplicity lower counts

This file proves the honest degree-*increasing* analytic input for the issue #42
count-equality route.

For `f g : ℝ[X]` with `f.Splits` and `f.natDegree < g.natDegree`, and every
`ρ > 0`, there is a threshold `δ > 0` such that for all `0 < μ < δ` for which
`f + C μ * g` splits, every root `a` of `f`, counted with multiplicity, has at
least that many roots of `f + C μ * g` within `ρ` of `a`.

## Why this needs a genuinely new argument

The same-degree core `exists_eps_forall_root_count_le_card_filter_near` cannot
be reused directly: for `μ ≠ 0` the member `f + C μ * g` has degree
`g.natDegree > f.natDegree`, so the degree jumps by at least one across the
`μ = 0` endpoint, and the same-degree normalisation (dividing by the leading
coefficient `≈ μ * g.leadingCoeff → 0`) breaks down.

The route here instead **factors out the escaping root(s)** rigorously:

* `abs_coeff_prod_X_sub_C_le`: for a product `∏ (X - w)` whose factors all have
  `ρ ≤ |w|`, every coefficient is bounded by the constant coefficient times
  `(1 + ρ⁻¹) ^ card`.  This controls the *far* cluster coefficients relative to
  its (large) constant term, replacing the bounded-roots coefficient bound used
  in the same-degree file (which fails when a root escapes to `∞`).

* `near_card_ge_of_low_coeff_le_of_large_root`: the analytic core.  A monic
  split polynomial of degree `n` with small low coefficients but possessing one
  root `r0` of large magnitude must have at least `m` roots within `ρ` of `0`.
  Proof: split into near/far clusters; the far cluster's constant term is huge
  (it contains `r0`), so `abs_coeff_le_of_mul` forces the near cluster's leading
  (monic) coefficient to be `< 1`, a contradiction unless the near cluster is
  large enough.

* `exists_mem_roots_abs_sub_gt`: the escaping-root existence (any degree gap).
  Since `∏ |q - c| = |f c + μ g c| / (μ |g.leadingCoeff|) → ∞` for a point `c`
  with `f c ≠ 0`, some root of `f + C μ * g` has arbitrarily large distance from
  `c` for small `μ`.

* `degreeIncreasing_local_lower_count` assembles these: normalise the Taylor
  shift `taylor a (f + C μ * g)` to monic, note its low coefficients are
  `≈ (taylor a g).coeff j / g.leadingCoeff` (bounded, and the numerator
  vanishes below the multiplicity of `a`), and feed the escaping root into the
  core.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted

noncomputable section

/-
**Far-cluster coefficient bound.**  For a product of linear factors
`∏ (X - w)` over a multiset `s` all of whose entries satisfy `ρ ≤ |w|`
(with `ρ > 0`), every coefficient is bounded by the constant coefficient times
`(1 + ρ⁻¹) ^ s.card`.  Because each `|w| ≥ ρ > 0`, the constant coefficient
`∏ (-w)` is nonzero, so this is a genuine relative bound.
-/
private lemma abs_coeff_prod_X_sub_C_le (s : Multiset ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hs : ∀ w ∈ s, ρ ≤ |w|) (j : ℕ) :
    |((s.map (fun w => X - C w)).prod).coeff j|
      ≤ |((s.map (fun w => X - C w)).prod).coeff 0| * (1 + ρ⁻¹) ^ s.card := by
  induction s using Multiset.induction generalizing j with
  | empty =>
      cases j with
      | zero => simp
      | succ k => simp [Polynomial.coeff_one]
  | cons w t ih =>
      have hw : ρ ≤ |w| := hs w (Multiset.mem_cons_self w t)
      have hinv : (0 : ℝ) ≤ ρ⁻¹ := le_of_lt (inv_pos.mpr hρ)
      have hbase : (1 : ℝ) ≤ 1 + ρ⁻¹ := by linarith
      have ihP : ∀ i, |((t.map (fun w => X - C w)).prod).coeff i|
          ≤ |((t.map (fun w ↦ X - C w)).prod).coeff 0| * (1 + ρ⁻¹) ^ t.card :=
        fun i ↦ ih (fun v hv ↦ hs v (Multiset.mem_cons_of_mem hv)) i
      set P := (t.map (fun w ↦ X - C w)).prod with hP
      have hprod : ((w ::ₘ t).map (fun w ↦ X - C w)).prod = (X - C w) * P := by simp_all
      have hcoeff : ∀ k, ((X - C w) * P).coeff k
          = (X * P).coeff k - w * P.coeff k := by
        intro k; rw [sub_mul, coeff_sub, coeff_C_mul]
      have hPnn : (0 : ℝ) ≤ |P.coeff 0| * (1 + ρ⁻¹) ^ t.card := by positivity
      have hB : (1 : ℝ) ≤ (1 + ρ⁻¹) ^ t.card * (1 + ρ⁻¹) := by
        nlinarith [one_le_pow₀ (n := t.card) hbase, hbase]
      rw [hprod, Multiset.card_cons, pow_succ]
      have hP0 : |((X - C w) * P).coeff 0| = |w| * |P.coeff 0| := by simp
      rw [hP0]
      cases j with
      | zero =>
          rw [hcoeff, coeff_X_mul_zero, zero_sub, abs_neg, abs_mul]
          exact le_mul_of_one_le_right
            (mul_nonneg (abs_nonneg w) (abs_nonneg (P.coeff 0))) hB
      | succ k =>
          rw [hcoeff, coeff_X_mul]
          have htri : |P.coeff k - w * P.coeff (k + 1)|
              ≤ |P.coeff k| + |w| * |P.coeff (k + 1)| := by
            have h := abs_sub (P.coeff k) (w * P.coeff (k + 1))
            simp_all
          have h1w : (1 : ℝ) ≤ |w| * ρ⁻¹ := by
            have := mul_le_mul_of_nonneg_right hw hinv
            grind
          have hwρ : 1 + |w| ≤ |w| * (1 + ρ⁻¹) := by grind
          have hkey : |P.coeff k| + |w| * |P.coeff (k + 1)|
              ≤ |w| * |P.coeff 0| * ((1 + ρ⁻¹) ^ t.card * (1 + ρ⁻¹)) := by
            nlinarith [ihP k, ihP (k + 1), mul_le_mul_of_nonneg_left hwρ hPnn,
              abs_nonneg w, mul_le_mul_of_nonneg_left (ihP (k + 1)) (abs_nonneg w)]
          grind

/-- **Analytic core (escaping form).**  A monic split real polynomial `R` of
degree `n` whose low coefficients (below `m ≤ n`) are all `≤ D`, and which has a
root `r0` of large magnitude (`ρ ≤ |r0|` and
`D * (1 + (1 + ρ⁻¹) ^ n) ^ n < |r0| * (min ρ 1) ^ n`), has at least `m` roots
strictly within `ρ` of `0`.

The large root forces the far cluster's constant coefficient to exceed the bound
that `abs_coeff_le_of_mul` would otherwise impose on the near cluster's monic
leading coefficient, so the near cluster must contain at least `m` roots. -/
private lemma near_card_ge_of_low_coeff_le_of_large_root
    (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (R : ℝ[X])
    (hmonic : R.Monic) (hsplit : R.Splits) (hdeg : R.natDegree = n)
    (m : ℕ) (hm : m ≤ n) (D : ℝ) (hD : 0 ≤ D)
    (hlow : ∀ j, j < m → |R.coeff j| ≤ D)
    (r0 : ℝ) (hr0 : r0 ∈ R.roots) (hr0ρ : ρ ≤ |r0|)
    (hr0big : D * (1 + (1 + ρ⁻¹) ^ n) ^ n < |r0| * (min ρ 1) ^ n) :
    m ≤ (R.roots.filter (fun r => |r| < ρ)).card := by
  by_contra h_contra
  have hnear : (R.roots.filter (fun r => |r| < ρ)).card < m := lt_of_not_ge h_contra
  set near := R.roots.filter (fun r => |r| < ρ) with hnear_def
  set far := R.roots.filter (fun r => ¬ (|r| < ρ)) with hfar_def
  set F := (far.map (fun r => X - C r)).prod with hF_def
  set N := (near.map (fun r => X - C r)).prod with hN_def
  have hR_eq : R = N * F := by
    have h1 : R.roots = near + far := (Multiset.filter_add_not _ _).symm
    have h2 : R = (R.roots.map (fun r => X - C r)).prod := by
      have h := hsplit.eq_prod_roots
      rwa [hmonic.leadingCoeff, C_1, one_mul] at h
    rw [h2, h1, Multiset.map_add, Multiset.prod_add]
  have hcard_le : far.card ≤ n := by
    have h := Multiset.card_le_card (Multiset.filter_le (fun r => ¬ (|r| < ρ)) R.roots)
    calc far.card ≤ R.roots.card := h
      _ = n := by rw [← hsplit.natDegree_eq_card_roots, hdeg]
  have hN_monic : N.Monic :=
    Polynomial.monic_multiset_prod_of_monic _ _ fun x _ => Polynomial.monic_X_sub_C _
  have hN_deg : N.natDegree = near.card :=
    Polynomial.natDegree_multiset_prod_X_sub_C_eq_card near
  have hN_coeff : N.coeff near.card = 1 := by rw [← hN_deg, hN_monic.coeff_natDegree]
  have hfar_ge : ∀ w ∈ far, ρ ≤ |w| := by
    intro w hw
    rw [hfar_def, Multiset.mem_filter] at hw
    grind
  have hφ_prod : |F.coeff 0| = (far.map (fun w ↦ |w|)).prod := by
    rw [hF_def, abs_coeff_zero_prod_X_sub_C]
  have hφ_pos : 0 < |F.coeff 0| := by
    rw [hφ_prod]
    apply Multiset.prod_pos
    intro x hx
    rw [Multiset.mem_map] at hx
    grind
  have hinv : (0 : ℝ) ≤ ρ⁻¹ := le_of_lt (inv_pos.mpr hρ)
  have hfar_coeff_le : ∀ j, |F.coeff j| ≤ |F.coeff 0| * (1 + ρ⁻¹) ^ n := by
    intro j
    have h := abs_coeff_prod_X_sub_C_le far ρ hρ hfar_ge j
    rw [← hF_def] at h
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    exact pow_le_pow_right₀ (by linarith) hcard_le
  have hφ_le : |F.coeff 0| ≤ D * (1 + (1 + ρ⁻¹) ^ n) ^ n := by
    have hbound := abs_coeff_le_of_mul (F := F) (N := N)
      (CF := |F.coeff 0| * (1 + ρ⁻¹) ^ n) (δ := D) (φ := |F.coeff 0|)
      hφ_pos le_rfl hfar_coeff_le
      (fun j hj ↦ by
        grind)
    have hk := hbound near.card (le_of_eq hN_deg.symm)
    have hCFφ : |F.coeff 0| * (1 + ρ⁻¹) ^ n / |F.coeff 0| = (1 + ρ⁻¹) ^ n := by grind
    rw [hN_coeff, abs_one, hCFφ] at hk
    have hφ1 : |F.coeff 0| ≤ D * (1 + (1 + ρ⁻¹) ^ n) ^ near.card := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hφ_pos] at hk
      linarith
    have hBpow : (1 + (1 + ρ⁻¹) ^ n) ^ near.card ≤ (1 + (1 + ρ⁻¹) ^ n) ^ n := by
      refine pow_le_pow_right₀ ?_ (le_of_lt (lt_of_lt_of_le hnear hm))
      have : (0 : ℝ) ≤ (1 + ρ⁻¹) ^ n := by positivity
      linarith
    exact le_trans hφ1 (mul_le_mul_of_nonneg_left hBpow hD)
  have hr0_far : r0 ∈ far := by
    rw [hfar_def, Multiset.mem_filter]
    grind
  have hφ_ge : |r0| * (min ρ 1) ^ n ≤ |F.coeff 0| := by
    rw [hφ_prod]
    have hfe : far = r0 ::ₘ far.erase r0 := (Multiset.cons_erase hr0_far).symm
    rw [hfe, Multiset.map_cons, Multiset.prod_cons]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg r0)
    have herase_card : (far.erase r0).card ≤ n :=
      le_trans (Multiset.card_le_card (Multiset.erase_le r0 far)) hcard_le
    have hprod_ge : (min ρ 1) ^ (far.erase r0).card
        ≤ ((far.erase r0).map (fun w ↦ |w|)).prod := by
      refine pow_card_le_prod_abs (far.erase r0) (min ρ 1) (by positivity) ?_
      grind
    have hmono : (min ρ 1) ^ n ≤ (min ρ 1) ^ (far.erase r0).card :=
      pow_le_pow_of_le_one (by positivity) (min_le_right _ _) herase_card
    grind
  grind

/-
**Escaping root (any degree gap).**  If `f.natDegree < g.natDegree` and
`f.eval c ≠ 0`, then for every bound `A` there is a threshold `δ > 0` such that
every splitting member `f + C μ * g` with `0 < μ < δ` has a root `q` with
`A < |q - c|`.

The product of `|q - c|` over the roots equals
`|f c + μ g c| / (μ |g.leadingCoeff|)`, which tends to `+∞` as `μ → 0⁺`, so some
factor must be large.
-/
private lemma exists_mem_roots_abs_sub_gt (f g : ℝ[X]) (hlt : f.natDegree < g.natDegree)
    (c : ℝ) (hc : f.eval c ≠ 0) (A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ → (f + C μ * g).Splits →
      ∃ q ∈ (f + C μ * g).roots, A < |q - c| := by
  classical
  have hg : g ≠ 0 := by
    rintro rfl
    simp only [natDegree_zero, Nat.not_lt_zero] at hlt
  have hglc : 0 < |g.leadingCoeff| := abs_pos.mpr (leadingCoeff_ne_zero.mpr hg)
  have hfc : 0 < |f.eval c| := abs_pos.mpr hc
  set L := max A 1 with hLdef
  have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one (le_max_right _ _)
  -- Product of `|c - r|` over any bounded root set is bounded by `L ^ card`.
  have hpow_le : ∀ s : Multiset ℝ, (∀ r ∈ s, |c - r| ≤ L) →
      (s.map (fun r ↦ |c - r|)).prod ≤ L ^ Multiset.card s := by
    intro s
    induction s using Multiset.induction with
    | empty => simp
    | cons a t ih =>
        intro hs
        rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
        refine mul_le_mul (hs a (Multiset.mem_cons_self a t))
          (ih fun r hr ↦ hs r (Multiset.mem_cons_of_mem hr)) ?_ hL0
        refine Multiset.prod_nonneg ?_
        simp
  set δ := min (|f.eval c| / (2 * (|g.eval c| + 1)))
    (|f.eval c| / (2 * (L ^ g.natDegree + 1) * |g.leadingCoeff|)) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ0, ?_⟩
  intro μ hμ hμδ hsplit
  have hμne : μ ≠ 0 := hμ.ne'
  have hpdeg : (f + C μ * g).natDegree = g.natDegree :=
    Polynomial.natDegree_add_C_mul_of_natDegree_lt hμne hlt
  have hplc : (f + C μ * g).leadingCoeff = μ * g.leadingCoeff :=
    Polynomial.leadingCoeff_add_C_mul_of_natDegree_lt hμne hlt
  -- Product identity for the split member evaluated at `c`.
  have habs_prod : ∀ s : Multiset ℝ,
      |(s.map (fun r => c - r)).prod| = (s.map (fun r => |c - r|)).prod := by
    intro s
    induction s using Multiset.induction with
    | empty => simp
    | cons a t ih =>
        simp_all
  have heval : (f + C μ * g).eval c
      = (f + C μ * g).leadingCoeff *
        ((f + C μ * g).roots.map (fun r ↦ c - r)).prod := by
    conv_lhs => rw [hsplit.eq_prod_roots]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    simp
  set P := ((f + C μ * g).roots.map (fun r ↦ |c - r|)).prod with hPdef
  have : |(f + C μ * g).eval c| = μ * |g.leadingCoeff| * P := by grind
  -- Numerator stays away from `0`.
  have hnum : |f.eval c| / 2 ≤ |(f + C μ * g).eval c| := by
    have he : (f + C μ * g).eval c = f.eval c + μ * g.eval c := by simp
    have hμsmall : μ * |g.eval c| < |f.eval c| / 2 := by
      have hμlt1 : μ < |f.eval c| / (2 * (|g.eval c| + 1)) :=
        lt_of_lt_of_le hμδ (min_le_left _ _)
      rw [lt_div_iff₀ (by positivity)] at hμlt1
      grind
    have hμabs : |μ * g.eval c| = μ * |g.eval c| := by grind
    grind
  -- Hence the product exceeds `L ^ g.natDegree`.
  have hLng : L ^ g.natDegree < P := by
    have hμlt2 : μ < |f.eval c| / (2 * (L ^ g.natDegree + 1) * |g.leadingCoeff|) :=
      lt_of_lt_of_le hμδ (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at hμlt2
    have h2 : |f.eval c| ≤ 2 * (μ * |g.leadingCoeff| * P) := by grind
    have hmul : 0 < μ * |g.leadingCoeff| := by positivity
    nlinarith [hμlt2, h2, hmul]
  -- If every root were within `L` of `c`, the product would be `≤ L ^ card`.
  by_contra hcon
  push Not at hcon
  have hcard : Multiset.card (f + C μ * g).roots = g.natDegree := by
    rw [← hsplit.natDegree_eq_card_roots]
    simp_all
  grind

/-- **Degree-increasing per-root multiplicity lower counts.**

For `f.Splits` and `f.natDegree < g.natDegree`, every root `a` of `f`, counted
with multiplicity, is eventually accounted for by at least that many roots of
`f + C μ * g` within `ρ` of `a`, for all small positive `μ` making the member
split. -/
theorem degreeIncreasing_local_lower_count {f g : ℝ[X]}
    (hf : f.Splits) (hlt : f.natDegree < g.natDegree)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ → (f + C μ * g).Splits →
      ∀ a ∈ f.roots.toFinset,
        f.roots.count a ≤
          ((f + C μ * g).roots.filter (fun q => |q - a| < ρ)).card := by
  classical
  rcases eq_or_ne f 0 with hf0 | hfne
  · refine ⟨1, one_pos, ?_⟩
    simp_all
  obtain ⟨c, hc0⟩ := Finset.exists_notMem f.roots.toFinset
  have hc : f.eval c ≠ 0 := fun h ↦
    hc0 (Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hfne, h⟩))
  have hglc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by
    rintro rfl; simp only [natDegree_zero, Nat.not_lt_zero] at hlt)
  set T : ℝ → ℝ := fun a =>
    (∑ j ∈ Finset.range (f.roots.count a), |(taylor a g).coeff j|) / |g.leadingCoeff|
      * (1 + (1 + ρ⁻¹) ^ g.natDegree) ^ g.natDegree / (min ρ 1) ^ g.natDegree with hT
  set A : ℝ := ∑ a ∈ f.roots.toFinset, (max ρ (T a) + |c - a| + 1) with hA
  obtain ⟨δ, hδ0, hδ⟩ := exists_mem_roots_abs_sub_gt f g hlt c hc A
  refine ⟨δ, hδ0, fun μ hμ hμδ hsplit a ha => ?_⟩
  obtain ⟨q, hq_mem, hq_gt⟩ := hδ μ hμ hμδ hsplit
  set D : ℝ := (∑ j ∈ Finset.range (f.roots.count a), |(taylor a g).coeff j|)
    / |g.leadingCoeff| with hD
  have hAge : max ρ (T a) + |c - a| + 1 ≤ A := by
    rw [hA]
    refine Finset.single_le_sum (f := fun a ↦ max ρ (T a) + |c - a| + 1) ?_ ha
    grind
  have hqa : max ρ (T a) < |q - a| := by grind
  set pnu : ℝ[X] := f + C μ * g with hpnu
  have hμne : μ ≠ 0 := hμ.ne'
  have hpdeg : pnu.natDegree = g.natDegree := by
    rw [hpnu]
    exact Polynomial.natDegree_add_C_mul_of_natDegree_lt hμne hlt
  have hplc : pnu.leadingCoeff = μ * g.leadingCoeff := by
    rw [hpnu]
    exact Polynomial.leadingCoeff_add_C_mul_of_natDegree_lt hμne hlt
  have hcne : pnu.leadingCoeff ≠ 0 := by simp_all
  set ptil : ℝ[X] := C pnu.leadingCoeff⁻¹ * pnu with hptil
  have hptil_monic : ptil.Monic := by
    have hlc : ptil.leadingCoeff = pnu.leadingCoeff⁻¹ * pnu.leadingCoeff := by simp_all
    rw [Monic, hlc, inv_mul_cancel₀ hcne]
  have hptil_deg : ptil.natDegree = g.natDegree := by
    rw [hptil, natDegree_C_mul (inv_ne_zero hcne), hpdeg]
  have hptil_roots : ptil.roots = pnu.roots := by
    rw [hptil]; exact roots_C_mul pnu (inv_ne_zero hcne)
  set R : ℝ[X] := taylor a ptil with hR
  have hR_monic : R.Monic := by
    rw [hR, taylor_apply]; exact hptil_monic.comp (monic_X_add_C a) (by simp)
  have hR_deg : R.natDegree = g.natDegree := by rw [hR, natDegree_taylor, hptil_deg]
  have hpnu_card : pnu.roots.card = g.natDegree := by
    rw [← hsplit.natDegree_eq_card_roots, hpdeg]
  have hR_roots : R.roots = pnu.roots.map (fun r => r - a) := by
    rw [hR, roots_taylor, hptil_roots]
  have hR_splits : R.Splits := by
    rw [splits_iff_card_roots, hR_roots, Multiset.card_map, hpnu_card, hR_deg]
  set r0 : ℝ := q - a with hr0def
  have hr0_mem : r0 ∈ R.roots := by simp_all
  have hcard_f : f.roots.card = f.natDegree := hf.natDegree_eq_card_roots.symm
  have hm : f.roots.count a ≤ g.natDegree := by
    have h1 := Multiset.count_le_card a f.roots
    grind
  have hDnn : 0 ≤ D := by rw [hD]; positivity
  have hlow : ∀ j, j < f.roots.count a → |R.coeff j| ≤ D := by
    intro j hj
    have hRj : R.coeff j = (taylor a g).coeff j / g.leadingCoeff := by
      have hRe : R = C pnu.leadingCoeff⁻¹ * taylor a pnu := by simp_all
      have e2 : (taylor a pnu).coeff j = μ * (taylor a g).coeff j := by
        have et := coeff_taylor_add_C_mul a μ f g j
        rw [hpnu, et, coeff_taylor_eq_zero_of_lt_count hj, zero_add]
      rw [hRe, coeff_C_mul, e2, hplc, mul_inv]
      field_simp
    rw [hRj, abs_div, hD]
    gcongr
    exact Finset.single_le_sum (f := fun k => |(taylor a g).coeff k|)
      (fun x _ => abs_nonneg _) (Finset.mem_range.mpr hj)
  have hres := near_card_ge_of_low_coeff_le_of_large_root g.natDegree ρ hρ R
    hR_monic hR_splits hR_deg (f.roots.count a) hm D hDnn hlow r0 hr0_mem
    (le_trans (le_max_left _ _) hqa.le)
    (by
      have hTlt : T a < |r0| := by simp_all
      have hTa : T a = D * (1 + (1 + ρ⁻¹) ^ g.natDegree) ^ g.natDegree
          / (min ρ 1) ^ g.natDegree := by simp only [hT, hD]
      rw [hTa, div_lt_iff₀ (by positivity)] at hTlt
      exact hTlt)
  have htrans := card_filter_roots_near_eq_taylor a ρ ptil
  simp_all

end

end RealRooted
