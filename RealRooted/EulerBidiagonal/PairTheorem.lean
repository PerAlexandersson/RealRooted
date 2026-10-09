import RealRooted.EulerBidiagonal.PairStep
import RealRooted.Interlacing.RootDeletionExpansion
import RealRooted.Mathlib.Algebra.Polynomial.FieldDivision
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Theorem C′ (positive regime): `T` preserves strict interlacing

Let `T = generalStep κ a b u v`.  If `f` and `g` are negative-simple, `deg g = deg f + 1`,
`f ≪ g` strictly with no common roots, and `u + v k > 0` for `k ≤ deg f + 1`, then
`T f ≪ T g` strictly with no common roots.  The proof applies `T` to the root-deletion expansion
of `g` and evaluates at the roots of `T f`.
-/

open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

/-- Removing a root from a negative-simple polynomial gives a negative-simple polynomial. -/
theorem isNegativeSimple_divByMonic_X_sub_C {f : ℝ[X]} (hf : IsNegativeSimple f) {s : ℝ}
    (hs : f.IsRoot s) : IsNegativeSimple (f /ₘ (X - C s)) := by
  have hfac : (X - C s) * (f /ₘ (X - C s)) = f := mul_divByMonic_eq_iff_isRoot.mpr hs
  have hne : f /ₘ (X - C s) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfac
    exact hf.1 hfac.symm
  have hroots : (f /ₘ (X - C s)).roots = f.roots.erase s := roots_divByMonic_X_sub_C hs
  have hmem : s ∈ f.roots := (mem_roots hf.1).mpr hs
  have hsplits : (f /ₘ (X - C s)).Splits := by
    apply splits_of_card_roots
    rw [hroots, Multiset.card_erase_of_mem hmem, card_roots_of_splits hf.2.1,
      natDegree_divByMonic_X_sub_C, Nat.pred_eq_sub_one]
  refine ⟨hne, hsplits, ?_, ?_, ?_⟩
  · apply HasSimpleRoots.of_roots_nodup hne
    rw [hroots]
    exact hf.2.2.1.roots_nodup.erase s
  · simpa [HasPosLeadingCoeff, leadingCoeff_divByMonic_X_sub_C hs] using hf.2.2.2.1
  · intro r hr
    rw [hroots] at hr
    exact hf.2.2.2.2 r (Multiset.mem_of_mem_erase hr)

/-- The coefficient of degree `d + 2` of `T g + s X T f`, and the degree bound. -/
theorem natDegree_generalStep_add_C_mul_X_mul (κ a b u v s : ℝ) (f g : ℝ[X]) (d : ℕ)
    (hfd : f.natDegree = d) (hgd : g.natDegree = d + 1)
    (hlead : 0 < (u + v * ((d : ℝ) + 1)) * g.leadingCoeff +
      s * (u + v * (d : ℝ)) * f.leadingCoeff) :
    (generalStep κ a b u v g + C s * (X * generalStep κ a b u v f)).natDegree = d + 2 ∧
      0 < (generalStep κ a b u v g + C s * (X * generalStep κ a b u v f)).leadingCoeff := by
  have hTgle : (generalStep κ a b u v g).natDegree ≤ d + 2 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    cases k with
    | zero => lia
    | succ k =>
        rw [coeff_generalStep]
        have h1 : g.coeff (k + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
        have h2 : g.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
        rw [h1, h2]
        ring
  have hTfle : (generalStep κ a b u v f).natDegree ≤ d + 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    cases k with
    | zero => lia
    | succ k =>
        rw [coeff_generalStep]
        have h1 : f.coeff (k + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
        have h2 : f.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
        rw [h1, h2]
        ring
  have hXle : (C s * (X * generalStep κ a b u v f)).natDegree ≤ d + 2 := by
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_mul_le (p := X)).trans ?_
    rw [natDegree_X]
    lia
  have hle : (generalStep κ a b u v g + C s * (X * generalStep κ a b u v f)).natDegree ≤ d + 2 :=
    (natDegree_add_le _ _).trans (max_le hTgle hXle)
  have htop : (generalStep κ a b u v g + C s * (X * generalStep κ a b u v f)).coeff (d + 2) =
      (u + v * ((d : ℝ) + 1)) * g.leadingCoeff +
        s * (u + v * (d : ℝ)) * f.leadingCoeff := by
    rw [coeff_add, coeff_C_mul, coeff_X_mul]
    have h1 := coeff_generalStep κ a b u v g (d + 1)
    have h2 := coeff_generalStep κ a b u v f d
    have hg0 : g.coeff (d + 1 + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
    have hf0 : f.coeff (d + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
    rw [hg0] at h1
    rw [hf0] at h2
    have hglc : g.coeff (d + 1) = g.leadingCoeff := by simp [leadingCoeff, hgd]
    have hflc : f.coeff d = f.leadingCoeff := by simp [leadingCoeff, hfd]
    rw [hglc] at h1
    rw [hflc] at h2
    push_cast at h1 h2
    rw [h1, h2]
    ring
  have hdeg : (generalStep κ a b u v g + C s * (X * generalStep κ a b u v f)).natDegree = d + 2 :=
    natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [htop]; exact hlead.ne')
  refine ⟨hdeg, ?_⟩
  rw [leadingCoeff, hdeg, htop]
  exact hlead

/-- **Theorem C′ (shifted cone).**  Let `f`, `g` be negative-simple of degrees `d`, `d + 1`, with
`f ≪ g` strictly and no common roots.  If `u + v k > 0` for `k ≤ d` and
`(u + v (d + 1)) lc g + s (u + v d) lc f > 0`, then `T f ≪ T g + s X T f` strictly, with no common
roots.  (For `s = 0` this is the positive regime; for `s ≠ 0` it also covers the regimes
`u + v (d + 1) ≤ 0`.) -/
theorem strictInterl_generalStep_add_C_mul_X_mul_of_strictInterl
    (κ a b u v s : ℝ) (f g : ℝ[X]) (d : ℕ) (hf : IsNegativeSimple f) (hg : IsNegativeSimple g)
    (hfd : f.natDegree = d) (hgd : g.natDegree = d + 1) (hfg : StrictInterl f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hell : ∀ k ≤ d, 0 < u + v * k)
    (hlead : 0 < (u + v * ((d : ℝ) + 1)) * g.leadingCoeff +
      s * (u + v * (d : ℝ)) * f.leadingCoeff)
    (hQ : ∀ t ≤ 0, comparisonDefect κ a b u v t < 0) :
    StrictInterl (generalStep κ a b u v f)
        (generalStep κ a b u v g + C s * (X * generalStep κ a b u v f)) ∧
      ∀ x, (generalStep κ a b u v f).IsRoot x →
        ¬ (generalStep κ a b u v g + C s * (X * generalStep κ a b u v f)).IsRoot x := by
  obtain ⟨α, β, hα, hexp, hpos⟩ := hfg.root_deletion_expansion hfd hgd hf.2.2.2.1 hg.2.2.2.1
    hf.2.2.1.roots_nodup hno
  obtain ⟨hTf, hTfdeg⟩ := isNegativeSimple_generalStep_of_natDegree κ a b u v f d hf hfd hκ ha hb
    hell hQ
  obtain ⟨hFdeg, hFlc⟩ := natDegree_generalStep_add_C_mul_X_mul κ a b u v s f g d hfd hgd hlead
  refine strictInterl_of_eval_mul_neg_one_pow_countP_neg hTf.1 hTf.2.1 hTf.2.2.1.roots_nodup
    (by lia) hFlc (by lia) ?_
  intro x hx
  have hxneg : x < 0 := hTf.2.2.2.2 x hx
  have hxroot : (generalStep κ a b u v f).eval x = 0 := isRoot_of_mem_roots hx
  have hA1 := generalComparison_sign_at_generalStep_root κ a b u v f d hf hfd hκ ha hb hell hQ x hx
  set σ : ℝ := (-1 : ℝ) ^ ((generalStep κ a b u v f).roots.countP (fun r => x < r)) with hσ
  -- the deletion terms
  have hdel : ∀ s ∈ f.roots.toFinset,
      0 < (generalStep κ a b u v (f /ₘ (X - C s))).eval x * σ := by
    intro s hs
    have hsroot : f.IsRoot s := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hs)
    have hfs := isNegativeSimple_divByMonic_X_sub_C hf hsroot
    have hfsdeg : (f /ₘ (X - C s)).natDegree = d - 1 := by
      rw [natDegree_divByMonic_X_sub_C, hfd]
    have hd1 : 1 ≤ d := by
      have hcard : 0 < Multiset.card f.roots :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨s, Multiset.mem_toFinset.mp hs⟩
      rw [card_roots_of_splits hf.2.1, hfd] at hcard
      exact hcard
    obtain ⟨hBint, hBno⟩ := strictInterl_generalStep_mul_X_sub_C κ a b u v s (f /ₘ (X - C s))
      (d - 1) hfs hfsdeg hκ ha hb (fun k hk => hell k (by lia)) hQ
    rw [mul_divByMonic_eq_iff_isRoot.mpr hsroot] at hBint hBno
    obtain ⟨hTfs, _⟩ := isNegativeSimple_generalStep_of_natDegree κ a b u v (f /ₘ (X - C s))
      (d - 1) hfs hfsdeg hκ ha hb (fun k hk => hell k (by lia)) hQ
    have hxs : x ∉ (generalStep κ a b u v (f /ₘ (X - C s))).roots := by
      intro hxs
      exact hBno x (isRoot_of_mem_roots hxs) (isRoot_of_mem_roots hx)
    have hcnt := hBint.roots_countP_eq hTf.2.2.1.roots_nodup hTfs.2.2.1.roots_nodup x hx hxs
    have h := eval_sign hTfs.2.1 hTfs.2.2.2.1 x hxs
    rw [← hcnt] at h
    exact h
  have hlin : ∀ (c : ℝ) (p : ℝ[X]),
      generalStep κ a b u v (C c * p) = C c * generalStep κ a b u v p := by
    intro c p
    have h := (generalStepLinearMap κ a b u v).map_smul c p
    simpa only [generalStepLinearMap_apply, smul_eq_C_mul] using h
  have hTg : generalStep κ a b u v g =
      C α * generalStep κ a b u v (X * f) + C β * generalStep κ a b u v f -
        ∑ s ∈ f.roots.toFinset, C (-g.eval s / f.derivative.eval s) *
          generalStep κ a b u v (f /ₘ (X - C s)) := by
    have h := congrArg (generalStepLinearMap κ a b u v) hexp
    have hrw : (C α * X + C β) * f = C α * (X * f) + C β * f := by ring
    rw [hrw] at h
    simp only [generalStepLinearMap_apply, map_sub, map_add, map_sum, hlin] at h
    exact h
  have hTXf : (generalStep κ a b u v (X * f)).eval x =
      x * (generalComparison κ a b v f).eval x := by
    rw [generalStep_X_mul]
    simp only [eval_add, eval_mul, eval_X, hxroot, mul_zero, zero_add]
  have hfirst : α * (x * (generalComparison κ a b v f).eval x) * σ < 0 := by
    have h : 0 < (generalComparison κ a b v f).eval x * σ := hA1
    have h2 : x * ((generalComparison κ a b v f).eval x * σ) < 0 := mul_neg_of_neg_of_pos hxneg h
    have h3 := mul_neg_of_pos_of_neg hα h2
    linarith
  have hsum : 0 ≤ ∑ s ∈ f.roots.toFinset, (-g.eval s / f.derivative.eval s) *
      ((generalStep κ a b u v (f /ₘ (X - C s))).eval x * σ) := by
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (hpos s (Multiset.mem_toFinset.mp hs)).le (hdel s hs).le
  have hFx : (generalStep κ a b u v g + C s * (X * generalStep κ a b u v f)).eval x =
      (generalStep κ a b u v g).eval x := by
    simp only [eval_add, eval_mul, eval_C, eval_X, hxroot, mul_zero, add_zero]
  rw [hFx, hTg]
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_finsetSum, hTXf, hxroot, mul_zero,
    add_zero]
  rw [sub_mul, Finset.sum_mul]
  have : ∀ s ∈ f.roots.toFinset,
      -g.eval s / f.derivative.eval s * (generalStep κ a b u v (f /ₘ (X - C s))).eval x * σ =
      (-g.eval s / f.derivative.eval s) *
        ((generalStep κ a b u v (f /ₘ (X - C s))).eval x * σ) := fun s _ => by ring
  rw [Finset.sum_congr rfl this]
  linarith


/-- **Theorem C′ (positive regime).**  The general Euler step preserves strict interlacing of
negative-simple polynomials of consecutive degrees, without common roots, provided the multiplier
`u + v k` is positive for `k ≤ deg f + 1`. -/
theorem strictInterl_generalStep_of_strictInterl
    (κ a b u v : ℝ) (f g : ℝ[X]) (d : ℕ) (hf : IsNegativeSimple f) (hg : IsNegativeSimple g)
    (hfd : f.natDegree = d) (hgd : g.natDegree = d + 1) (hfg : StrictInterl f g)
    (hno : ∀ s, f.IsRoot s → ¬ g.IsRoot s) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hell : ∀ k ≤ d + 1, 0 < u + v * k) (hQ : ∀ t ≤ 0, comparisonDefect κ a b u v t < 0) :
    StrictInterl (generalStep κ a b u v f) (generalStep κ a b u v g) ∧
      ∀ x, (generalStep κ a b u v f).IsRoot x → ¬ (generalStep κ a b u v g).IsRoot x := by
  have hlead : 0 < (u + v * ((d : ℝ) + 1)) * g.leadingCoeff +
      0 * (u + v * (d : ℝ)) * f.leadingCoeff := by
    have h1 : 0 < u + v * ((d + 1 : ℕ) : ℝ) := hell (d + 1) le_rfl
    push_cast at h1
    rw [zero_mul, zero_mul, add_zero]
    exact mul_pos h1 hg.2.2.2.1
  have h := strictInterl_generalStep_add_C_mul_X_mul_of_strictInterl κ a b u v 0 f g d hf hg hfd
    hgd hfg hno hκ ha hb (fun k hk => hell k (by lia)) hlead hQ
  simpa only [C_0, zero_mul, add_zero] using h

end RealRooted.EulerBidiagonal
