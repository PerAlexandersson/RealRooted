import RealRooted.CoefficientShape.Hoggar

/-!
# Log-concave sequences without internal zeros

Preliminaries for the Liu–Mao theorem on Euler numerators of products of polynomials.

* `LCNIZ d a` bundles the three coefficient-shape predicates `CoeffNonnegUpTo`,
  `CoeffLogConcaveUpTo` and `CoeffNoInternalZerosUpTo` through index `d`.
* `GLC a` is the global version (nonnegative, log-concave, no internal zeros on all of `ℕ`),
  with the "outer ≤ inner" inequality derived from `Hoggar.mul_le_mul_of_logConcave`.
* The Toeplitz matrix `toep a` of such a sequence is totally positive of order two, and the
  `2 × 2` Cauchy–Binet inequalities (from `Hoggar.two_mul_det_eq`) transport this to products.
* `GLC.conv`: Hoggar's convolution `Hoggar.conv a g` of two `GLC` sequences is `GLC`.
  The log-concavity part is reproved here through Toeplitz matrices, because the corresponding
  step in `RealRooted.CoefficientShape.Hoggar` is private.
* Truncation, reversal and Toeplitz windows of `LCNIZ` sequences.
-/

open Finset

namespace RealRooted.LiuMao

/-- Nonnegative, log-concave and without internal zeros on `[0, d]`. -/
def LCNIZ (d : ℕ) (a : ℕ → ℝ) : Prop :=
  CoeffNonnegUpTo d a ∧ CoeffLogConcaveUpTo d a ∧ CoeffNoInternalZerosUpTo d a

/-- A globally nonnegative log-concave sequence without internal zeros. -/
structure GLC (a : ℕ → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ a k
  lc : ∀ k, 0 < k → a (k - 1) * a (k + 1) ≤ a k ^ 2
  niz : ∀ i j k, i < j → j < k → a i ≠ 0 → a k ≠ 0 → a j ≠ 0

/-- Truncation of a sequence to `[0, d]`. -/
def trunc (d : ℕ) (a : ℕ → ℝ) (k : ℕ) : ℝ := if k ≤ d then a k else 0

/-- The truncation of an `LCNIZ` sequence is `GLC`. -/
theorem LCNIZ.glc_trunc {d : ℕ} {a : ℕ → ℝ} (h : LCNIZ d a) : GLC (trunc d a) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro k
    unfold trunc
    split_ifs with hk
    · exact h0 k hk
    · exact le_rfl
  · intro k hk
    unfold trunc
    by_cases hkd : k < d
    · rw [ite_eq_left (by lia), ite_eq_left (by lia), ite_eq_left (by lia)]
      exact h1 k hk hkd
    · rw [ite_eq_right (show ¬ (k + 1 ≤ d) by lia), mul_zero]
      exact sq_nonneg _
  · intro i j k hij hjk hi hk
    unfold trunc at hi hk ⊢
    split_ifs at hk with hkd
    · split_ifs at hi with hid
      · rw [ite_eq_left (by lia)]
        exact h2 i j k hij hjk hkd hi hk
      · exact absurd rfl hi
    · exact absurd rfl hk

/-- Truncation does not change the entries up to the cutoff. -/
theorem trunc_eq_of_le {d : ℕ} (a : ℕ → ℝ) {k : ℕ} (hk : k ≤ d) : trunc d a k = a k := by
  rw [trunc, ite_eq_left hk]

/-- An `LCNIZ` sequence that vanishes beyond `d` is `GLC`. -/
theorem LCNIZ.glc {d : ℕ} {a : ℕ → ℝ} (h : LCNIZ d a) (hz : ∀ k, d < k → a k = 0) : GLC a := by
  have : trunc d a = a := by
    funext k
    unfold trunc
    split_ifs with hk
    · rfl
    · rw [hz k (by lia)]
  rw [← this]
  exact h.glc_trunc

/-- A `GLC` sequence is `LCNIZ` through every index. -/
theorem GLC.lcniz {a : ℕ → ℝ} (h : GLC a) (d : ℕ) : LCNIZ d a :=
  ⟨fun k _ => h.nonneg k, fun k hk _ => h.lc k hk, fun i j k hij hjk _ => h.niz i j k hij hjk⟩

/-- Between two nonzero entries of a `GLC` sequence, every entry is nonzero. -/
theorem GLC.ne_zero_between {a : ℕ → ℝ} (h : GLC a) {x y t : ℕ} (hx : a x ≠ 0) (hy : a y ≠ 0)
    (h1 : min x y ≤ t) (h2 : t ≤ max x y) : a t ≠ 0 := by
  rcases le_total x y with hxy | hxy
  · rw [min_eq_left hxy] at h1
    rw [max_eq_right hxy] at h2
    exact Hoggar.ne_zero_of_between h.niz x t y hx hy h1 h2
  · rw [min_eq_right hxy] at h1
    rw [max_eq_left hxy] at h2
    exact Hoggar.ne_zero_of_between h.niz y t x hy hx h1 h2

private theorem GLC.outer_le_inner_succ {a : ℕ → ℝ} (h : GLC a) (x m : ℕ) :
    a x * a (x + m + 1) ≤ a (x + 1) * a (x + m) :=
  Hoggar.mul_le_mul_of_logConcave h.nonneg (fun k => by simpa using h.lc (k + 1) (by lia))
    h.niz x m

private theorem GLC.inner_outer' {a : ℕ → ℝ} (h : GLC a) (m : ℕ) :
    ∀ x y z w, y = x + m → y ≤ z → x + w = y + z → a x * a w ≤ a y * a z := by
  induction m with
  | zero =>
    intro x y z w hy _ hs
    subst hy
    rw [show w = z by lia]
  | succ m ih =>
    intro x y z w hy hyz hs
    have hstep := h.outer_le_inner_succ x (w - x - 1)
    rw [show x + (w - x - 1) + 1 = w by lia, show x + (w - x - 1) = w - 1 by lia] at hstep
    have := ih (x + 1) y z (w - 1) (by lia) hyz (by lia)
    linarith

/-- Outer products are at most inner products: `a x * a w ≤ a y * a z` whenever `x ≤ y`,
`x ≤ z` and `x + w = y + z`. -/
theorem GLC.inner_outer {a : ℕ → ℝ} (h : GLC a) {x y z w : ℕ} (hxy : x ≤ y) (hxz : x ≤ z)
    (hs : x + w = y + z) : a x * a w ≤ a y * a z := by
  rcases le_total y z with hyz | hyz
  · exact h.inner_outer' (y - x) x y z w (by lia) hyz hs
  · rw [mul_comm (a y)]
    exact h.inner_outer' (z - x) x z y w (by lia) hyz (by lia)

/-- The Toeplitz matrix `(a (r - i))_{r,i}` (zero above the diagonal). -/
def toep (a : ℕ → ℝ) (r i : ℕ) : ℝ := if i ≤ r then a (r - i) else 0

/-- Entries of the Toeplitz matrix of a `GLC` sequence are nonnegative. -/
theorem GLC.toep_nonneg {a : ℕ → ℝ} (h : GLC a) (r i : ℕ) : 0 ≤ toep a r i := by
  unfold toep
  split_ifs
  · exact h.nonneg _
  · exact le_rfl

/-- The Toeplitz matrix of a `GLC` sequence is totally positive of order two. -/
theorem GLC.toep_tp2 {a : ℕ → ℝ} (h : GLC a) {r₁ r₂ i₁ i₂ : ℕ} (hr : r₁ < r₂) (hi : i₁ < i₂) :
    toep a r₁ i₂ * toep a r₂ i₁ ≤ toep a r₁ i₁ * toep a r₂ i₂ := by
  by_cases h2 : i₂ ≤ r₁
  · unfold toep
    rw [ite_eq_left h2, ite_eq_left (by lia), ite_eq_left (by lia), ite_eq_left (by lia)]
    exact h.inner_outer (by lia) (by lia) (by lia)
  · have : toep a r₁ i₂ = 0 := by rw [toep, ite_eq_right h2]
    rw [this, zero_mul]
    exact mul_nonneg (h.toep_nonneg _ _) (h.toep_nonneg _ _)

/-! ### The `2 × 2` Cauchy–Binet inequalities -/

/-- `TP₂ · TP₂` gives a nonnegative `2 × 2` minor. -/
private theorem cauchyBinet_tp2 (s : Finset ℕ) (A₁ A₂ B₁ B₂ : ℕ → ℝ)
    (hA : ∀ i ∈ s, ∀ j ∈ s, i < j → A₁ j * A₂ i ≤ A₁ i * A₂ j)
    (hB : ∀ i ∈ s, ∀ j ∈ s, i < j → B₁ j * B₂ i ≤ B₁ i * B₂ j) :
    (∑ i ∈ s, A₁ i * B₂ i) * (∑ i ∈ s, A₂ i * B₁ i) ≤
      (∑ i ∈ s, A₁ i * B₁ i) * (∑ i ∈ s, A₂ i * B₂ i) := by
  have h := Hoggar.two_mul_det_eq s A₁ A₂ B₁ B₂
  have : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (A₁ i * A₂ j - A₁ j * A₂ i) * (B₁ i * B₂ j - B₂ i * B₁ j) := by
    refine sum_nonneg fun i hi => sum_nonneg fun j hj => ?_
    rcases lt_trichotomy i j with hij | hij | hij
    · exact mul_nonneg (by linarith [hA i hi j hj hij]) (by linarith [hB i hi j hj hij])
    · simp [hij]
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hA j hj i hi hij])
        (by linarith [hB j hj i hi hij])
  linarith

/-- `TP₂ · RR₂` gives a nonpositive `2 × 2` minor. -/
theorem cauchyBinet_rr2 (s : Finset ℕ) (A₁ A₂ B₁ B₂ : ℕ → ℝ)
    (hA : ∀ i ∈ s, ∀ j ∈ s, i < j → A₁ j * A₂ i ≤ A₁ i * A₂ j)
    (hB : ∀ i ∈ s, ∀ j ∈ s, i < j → B₁ i * B₂ j ≤ B₁ j * B₂ i) :
    (∑ i ∈ s, A₁ i * B₁ i) * (∑ i ∈ s, A₂ i * B₂ i) ≤
      (∑ i ∈ s, A₁ i * B₂ i) * (∑ i ∈ s, A₂ i * B₁ i) := by
  have h := Hoggar.two_mul_det_eq s A₁ A₂ B₁ B₂
  have : ∑ i ∈ s, ∑ j ∈ s, (A₁ i * A₂ j - A₁ j * A₂ i) * (B₁ i * B₂ j - B₂ i * B₁ j) ≤ 0 := by
    refine sum_nonpos fun i hi => sum_nonpos fun j hj => ?_
    rcases lt_trichotomy i j with hij | hij | hij
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hA i hi j hj hij])
        (by linarith [hB i hi j hj hij])
    · simp [hij]
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hA j hj i hi hij])
        (by linarith [hB j hj i hi hij])
  linarith

/-! ### Hoggar's convolution theorem for `GLC` sequences -/

private theorem conv_eq_sum_toep (a g : ℕ → ℝ) (r n : ℕ) (hn : r < n) :
    Hoggar.conv a g r = ∑ i ∈ range n, toep g r i * toep a i 0 := by
  unfold Hoggar.conv toep
  symm
  rw [show n = (r + 1) + (n - (r + 1)) by lia, sum_range_add,
    sum_eq_zero (s := range (n - (r + 1))) (fun i _ => by rw [ite_eq_right (by lia)]; simp),
    add_zero]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [ite_eq_left (by lia), ite_eq_left (by lia), Nat.sub_zero, mul_comm]

private theorem conv_eq_sum_toep_shift (a g : ℕ → ℝ) (r n : ℕ) (hn : r + 1 < n) :
    Hoggar.conv a g r = ∑ i ∈ range n, toep g (r + 1) i * toep a i 1 := by
  unfold Hoggar.conv toep
  symm
  rw [show n = (r + 1 + 1) + (n - (r + 1 + 1)) by lia, sum_range_add,
    sum_eq_zero (s := range (n - (r + 1 + 1))) (fun i _ => by rw [ite_eq_right (by lia)]; simp),
    add_zero, sum_range_succ', ite_eq_right (show ¬ (1 ≤ 0) by lia), mul_zero, add_zero]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [ite_eq_left (by lia), ite_eq_left (by lia), mul_comm]
  congr 2
  lia

/-- Hoggar's theorem: the convolution of two `GLC` sequences is `GLC`.  Log-concavity is proved
by the `2 × 2` Cauchy–Binet inequality for Toeplitz matrices; the absence of internal zeros is
`Hoggar.conv_noInternalZeros`. -/
theorem GLC.conv {a g : ℕ → ℝ} (ha : GLC a) (hg : GLC g) : GLC (Hoggar.conv a g) := by
  refine ⟨fun r => sum_nonneg fun i _ => mul_nonneg (ha.nonneg _) (hg.nonneg _), ?_, ?_⟩
  · intro r hr
    have e1 := conv_eq_sum_toep a g r (r + 2) (by lia)
    have e2 := conv_eq_sum_toep a g (r + 1) (r + 2) (by lia)
    have e3 := conv_eq_sum_toep_shift a g r (r + 2) (by lia)
    have e4 := conv_eq_sum_toep_shift a g (r - 1) (r + 2) (by lia)
    rw [show r - 1 + 1 = r by lia] at e4
    have key := cauchyBinet_tp2 (range (r + 2)) (toep g r) (toep g (r + 1))
      (fun i => toep a i 0) (fun i => toep a i 1)
      (fun i _ j _ hij => hg.toep_tp2 (by lia) hij)
      (fun i _ j _ hij => by
        have := ha.toep_tp2 (r₁ := i) (r₂ := j) (i₁ := 0) (i₂ := 1) hij (by lia)
        linarith)
    rw [← e1, ← e2, ← e3, ← e4] at key
    rw [sq]
    exact key
  · intro i j k hij hjk hi hk
    exact Hoggar.conv_noInternalZeros ha.nonneg hg.nonneg ha.niz hg.niz hij hjk hi hk

/-- The convolution of `g` with `a` in Toeplitz form, for `g` supported on `[0, D]`. -/
theorem conv_eq_sum_toep_of_support (a g : ℕ → ℝ) (D r : ℕ) (hg : ∀ i, D < i → g i = 0) :
    Hoggar.conv g a r = ∑ i ∈ range (D + 1), toep a r i * g i := by
  rw [conv_eq_sum_toep g a r (r + D + 1) (by lia)]
  symm
  refine sum_subset ?_ ?_
  · intro i
    simp only [mem_range]
    lia
  · intro i hi hi2
    simp only [mem_range] at hi hi2
    rw [hg i (by lia)]
    simp

/-! ### Congruence, reversal and windows -/

/-- `LCNIZ` depends only on the entries up to the cutoff. -/
theorem LCNIZ.congr {d : ℕ} {f g : ℕ → ℝ} (h : LCNIZ d f) (hfg : ∀ i, i ≤ d → f i = g i) :
    LCNIZ d g := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨fun k hk => hfg k hk ▸ h0 k hk, ?_, ?_⟩
  · intro k hk hkd
    rw [← hfg (k - 1) (by lia), ← hfg (k + 1) (by lia), ← hfg k (by lia)]
    exact h1 k hk hkd
  · intro i j k hij hjk hkd hi hk
    rw [← hfg i (by lia)] at hi
    rw [← hfg k hkd] at hk
    rw [← hfg j (by lia)]
    exact h2 i j k hij hjk hkd hi hk

/-- Reversal `k ↦ a (d - k)` preserves `LCNIZ`. -/
theorem LCNIZ.rev {d : ℕ} {a : ℕ → ℝ} (h : LCNIZ d a) : LCNIZ d (fun k => a (d - k)) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨fun k _ => h0 _ (by lia), ?_, ?_⟩
  · intro k hk hkd
    have := h1 (d - k) (by lia) (by lia)
    rw [show d - k - 1 = d - (k + 1) by lia, show d - k + 1 = d - (k - 1) by lia] at this
    linarith
  · intro i j k hij hjk hkd hi hk
    exact h2 (d - k) (d - j) (d - i) (by lia) (by lia) (by lia) hk hi

/-- The window `j ↦ b (s - j)` (zero for `j > s`) of a `GLC` sequence is `GLC`. -/
theorem GLC.window {b : ℕ → ℝ} (h : GLC b) (s : ℕ) : GLC (fun j => toep b s j) := by
  refine ⟨fun j => h.toep_nonneg s j, ?_, ?_⟩
  · intro j hj
    by_cases hjs : j + 1 ≤ s
    · unfold toep
      rw [ite_eq_left (by lia), ite_eq_left hjs, ite_eq_left (by lia)]
      have := h.lc (s - j) (by lia)
      rw [show s - j - 1 = s - (j + 1) by lia, show s - j + 1 = s - (j - 1) by lia] at this
      linarith
    · have : toep b s (j + 1) = 0 := by rw [toep, ite_eq_right hjs]
      rw [this, mul_zero]
      exact sq_nonneg _
  · intro i j k hij hjk hi hk
    unfold toep at hi hk ⊢
    split_ifs at hk with hks
    · rw [ite_eq_left (by lia)]
      rw [ite_eq_left (by lia)] at hi
      exact h.niz (s - k) (s - j) (s - i) (by lia) (by lia) hk hi
    · exact absurd rfl hk

end RealRooted.LiuMao

/-!
## Bernstein degree elevation and reduction preserve LC-NIZ

`Eop n` is the degree-elevation map `ℝ^{n+1} → ℝ^{n+2}` and `Dop n` the degree-reduction map
`ℝ^{n+1} → ℝ^n` (in the normalisation of Liu–Mao, Section 3).  Both preserve nonnegative
log-concave sequences without internal zeros.
-/

open Finset

namespace RealRooted.LiuMao

/-- A globally LC-NIZ sequence supported on `[0, n]`. -/
def GLCN (n : ℕ) (u : ℕ → ℝ) : Prop := GLC u ∧ ∀ k, n < k → u k = 0

/-- Degree elevation `ℝ^{n+1} → ℝ^{n+2}`. -/
noncomputable def Eop (n : ℕ) (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  ((j : ℝ) * v (j - 1) + ((n : ℝ) + 1 - j) * v j) / ((n : ℝ) + 1)

/-- Degree reduction `ℝ^{n+1} → ℝ^n`. -/
noncomputable def Dop (n : ℕ) (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  (((n : ℝ) - j) * v j + ((j : ℝ) + 1) * v (j + 1)) / ((n : ℝ) + 1)

/-- The elementary inequality behind both preservation results. -/
private theorem two_term_core (P Q s x₀ x₁ x₂ x₃ : ℝ)
    (hc₁ : 0 ≤ P - s) (hc₂ : 0 ≤ Q + s) (hc₃ : 0 ≤ P + s) (hc₄ : 0 ≤ Q - s)
    (l₁ : x₀ * x₂ ≤ x₁ ^ 2) (l₂ : x₁ * x₃ ≤ x₂ ^ 2) (l₃ : x₀ * x₃ ≤ x₁ * x₂) :
    ((P - s) * x₀ + (Q + s) * x₁) * ((P + s) * x₂ + (Q - s) * x₃) ≤ (P * x₁ + Q * x₂) ^ 2 := by
  have e₁ := mul_le_mul_of_nonneg_left l₁ (mul_nonneg hc₁ hc₃)
  have e₂ := mul_le_mul_of_nonneg_left l₃ (mul_nonneg hc₁ hc₄)
  have e₃ := mul_le_mul_of_nonneg_left l₂ (mul_nonneg hc₂ hc₄)
  nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg (x₁ - x₂))]

private theorem Eop_zero_of_gt {n : ℕ} {u : ℕ → ℝ} (hz : ∀ k, n < k → u k = 0) {j : ℕ}
    (hj : n + 1 < j) : Eop n u j = 0 := by
  unfold Eop; rw [hz j (by lia), hz (j - 1) (by lia)]; simp

private theorem Eop_nonneg {n : ℕ} {u : ℕ → ℝ} (h : GLCN n u) (j : ℕ) : 0 ≤ Eop n u j := by
  by_cases hj : n + 1 < j
  · rw [Eop_zero_of_gt h.2 hj]
  · unfold Eop
    apply div_nonneg _ (by positivity)
    have : (j : ℝ) ≤ n + 1 := by exact_mod_cast (show j ≤ n + 1 by lia)
    have h1 := h.1.nonneg (j - 1)
    have h2 := h.1.nonneg j
    have : 0 ≤ ((n : ℝ) + 1 - j) * u j := mul_nonneg (by linarith) h2
    positivity

/-- Degree elevation preserves globally LC-NIZ sequences supported on `[0, n]`. -/
theorem GLCN.elev {n : ℕ} {u : ℕ → ℝ} (h : GLCN n u) : GLCN (n + 1) (Eop n u) := by
  obtain ⟨hg, hz⟩ := h
  refine ⟨⟨Eop_nonneg ⟨hg, hz⟩, ?_, ?_⟩, fun k hk => Eop_zero_of_gt hz hk⟩
  · intro p hp
    by_cases hpn : n + 1 ≤ p
    · rw [Eop_zero_of_gt (j := p + 1) hz (by lia), mul_zero]; exact sq_nonneg _
    have hpc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by lia)]; simp
    have hnp : (p : ℝ) ≤ n := by exact_mod_cast (show p ≤ n by lia)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    set x₀ : ℝ := if p = 1 then 0 else u (p - 2) with hx₀
    have hE1 : Eop n u (p - 1) =
        (((p : ℝ) - 1) * x₀ + (((n : ℝ) + 1 - p) + 1) * u (p - 1)) / ((n : ℝ) + 1) := by
      unfold Eop
      rw [hpc]
      congr 1
      by_cases h1 : p = 1
      · subst h1; rw [hx₀, ite_eq_left rfl]; simp
      · rw [hx₀, ite_eq_right h1, show p - 1 - 1 = p - 2 by lia]; ring
    have hE2 : Eop n u (p + 1) =
        (((p : ℝ) + 1) * u p + (((n : ℝ) + 1 - p) - 1) * u (p + 1)) / ((n : ℝ) + 1) := by
      unfold Eop
      push_cast
      ring
    have hE0 : Eop n u p = ((p : ℝ) * u (p - 1) + ((n : ℝ) + 1 - p) * u p) / ((n : ℝ) + 1) := rfl
    have l₁ : x₀ * u p ≤ u (p - 1) ^ 2 := by
      rw [hx₀]; split_ifs with h1
      · rw [zero_mul]; exact sq_nonneg _
      · have := hg.lc (p - 1) (by lia)
        rw [show p - 1 - 1 = p - 2 by lia, show p - 1 + 1 = p by lia] at this
        exact this
    have l₂ : u (p - 1) * u (p + 1) ≤ u p ^ 2 := hg.lc p hp
    have l₃ : x₀ * u (p + 1) ≤ u (p - 1) * u p := by
      rw [hx₀]; split_ifs with h1
      · rw [zero_mul]; exact mul_nonneg (hg.nonneg _) (hg.nonneg _)
      · exact hg.inner_outer (by lia) (by lia) (by lia)
    have core := two_term_core (p : ℝ) ((n : ℝ) + 1 - p) 1 x₀ (u (p - 1)) (u p) (u (p + 1))
      (by linarith) (by linarith) (by linarith) (by linarith) l₁ l₂ l₃
    rw [hE1, hE2, hE0, div_mul_div_comm, div_pow, ← pow_two]
    exact div_le_div_of_nonneg_right core (by positivity)
  · intro i j k hij hjk hi hk
    have wit : ∀ q, q ≤ n + 1 → Eop n u q ≠ 0 →
        ∃ α, α ≤ q ∧ q ≤ α + 1 ∧ α ≤ n ∧ u α ≠ 0 := by
      intro q hq hne
      by_cases h1 : 1 ≤ q ∧ u (q - 1) ≠ 0
      · exact ⟨q - 1, by lia, by lia, by lia, h1.2⟩
      · refine ⟨q, le_refl _, by lia, ?_, ?_⟩
        · by_contra hqn
          have hq' : q = n + 1 := by lia
          subst hq'
          apply hne
          have h5 : u n = 0 := by
            by_contra h4; exact h1 ⟨by lia, by simpa using h4⟩
          unfold Eop; simp [h5]
        · intro h2
          apply hne
          unfold Eop
          rw [h2]
          by_cases h3 : q = 0
          · subst h3; simp
          · have : u (q - 1) = 0 := by
              by_contra h4; exact h1 ⟨by lia, h4⟩
            rw [this]; simp
    have hk' : k ≤ n + 1 := by
      by_contra hkn; exact hk (Eop_zero_of_gt hz (by lia))
    obtain ⟨α, hα1, hα2, hα3, hα4⟩ := wit i (by lia) hi
    obtain ⟨β, hβ1, hβ2, hβ3, hβ4⟩ := wit k hk' hk
    have hv : u (j - 1) ≠ 0 := hg.ne_zero_between hα4 hβ4 (by lia) (by lia)
    have hpos : 0 < u (j - 1) := lt_of_le_of_ne (hg.nonneg _) (Ne.symm hv)
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by lia)
    have hjn : (j : ℝ) ≤ n + 1 := by exact_mod_cast (show j ≤ n + 1 by lia)
    unfold Eop
    apply ne_of_gt
    apply div_pos _ (by positivity)
    have := mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) + 1 - j by linarith) (hg.nonneg j)
    nlinarith

private theorem Dop_zero_of_gt {n : ℕ} {u : ℕ → ℝ} (hz : ∀ k, n + 1 < k → u k = 0) {j : ℕ}
    (hj : n < j) : Dop (n + 1) u j = 0 := by
  unfold Dop
  rw [hz (j + 1) (by lia)]
  rcases eq_or_lt_of_le (show n + 1 ≤ j by lia) with h | h
  · subst h; push_cast; ring
  · rw [hz j h]; ring

private theorem Dop_nonneg {n : ℕ} {u : ℕ → ℝ} (h : GLCN (n + 1) u) (j : ℕ) :
    0 ≤ Dop (n + 1) u j := by
  by_cases hj : n < j
  · rw [Dop_zero_of_gt h.2 hj]
  · unfold Dop
    apply div_nonneg _ (by positivity)
    have : (j : ℝ) ≤ n := by exact_mod_cast (show j ≤ n by lia)
    have h1 := h.1.nonneg (j + 1)
    have h2 := h.1.nonneg j
    push_cast
    have : 0 ≤ ((n : ℝ) + 1 - j) * u j := mul_nonneg (by linarith) h2
    positivity

/-- Degree reduction preserves globally LC-NIZ sequences supported on `[0, n + 1]`. -/
theorem GLCN.reduce {n : ℕ} {u : ℕ → ℝ} (h : GLCN (n + 1) u) : GLCN n (Dop (n + 1) u) := by
  obtain ⟨hg, hz⟩ := h
  refine ⟨⟨Dop_nonneg ⟨hg, hz⟩, ?_, ?_⟩, fun k hk => Dop_zero_of_gt hz hk⟩
  · intro p hp
    by_cases hpn : n ≤ p
    · rw [Dop_zero_of_gt (j := p + 1) hz (by lia), mul_zero]; exact sq_nonneg _
    have hpc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by lia)]; simp
    have hnp : (p : ℝ) + 1 ≤ n := by exact_mod_cast (show p + 1 ≤ n by lia)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hD1 : Dop (n + 1) u (p - 1) =
        ((((n : ℝ) + 1 - p) - (-1)) * u (p - 1) + (((p : ℝ) + 1) + (-1)) * u p) /
          (((n + 1 : ℕ) : ℝ) + 1) := by
      unfold Dop
      rw [hpc, show p - 1 + 1 = p by lia]
      push_cast
      ring_nf
    have hD2 : Dop (n + 1) u (p + 1) =
        ((((n : ℝ) + 1 - p) + (-1)) * u (p + 1) + (((p : ℝ) + 1) - (-1)) * u (p + 1 + 1)) /
          (((n + 1 : ℕ) : ℝ) + 1) := by
      unfold Dop
      push_cast
      ring_nf
    have hD0 : Dop (n + 1) u p =
        (((n : ℝ) + 1 - p) * u p + ((p : ℝ) + 1) * u (p + 1)) / (((n + 1 : ℕ) : ℝ) + 1) := by
      unfold Dop; push_cast; ring_nf
    have l₁ : u (p - 1) * u (p + 1) ≤ u p ^ 2 := hg.lc p hp
    have l₂ : u p * u (p + 1 + 1) ≤ u (p + 1) ^ 2 := by
      have := hg.lc (p + 1) (by lia)
      simpa using this
    have l₃ : u (p - 1) * u (p + 1 + 1) ≤ u p * u (p + 1) :=
      hg.inner_outer (by lia) (by lia) (by lia)
    have core := two_term_core ((n : ℝ) + 1 - p) ((p : ℝ) + 1) (-1) (u (p - 1)) (u p) (u (p + 1))
      (u (p + 1 + 1)) (by linarith) (by linarith) (by linarith) (by linarith)
      l₁ l₂ l₃
    rw [hD1, hD2, hD0, div_mul_div_comm, div_pow, ← pow_two]
    exact div_le_div_of_nonneg_right core (by positivity)
  · intro i j k hij hjk hi hk
    have wit : ∀ q, Dop (n + 1) u q ≠ 0 → ∃ α, q ≤ α ∧ α ≤ q + 1 ∧ u α ≠ 0 := by
      intro q hne
      by_cases h1 : u (q + 1) ≠ 0
      · exact ⟨q + 1, by lia, le_refl _, h1⟩
      · refine ⟨q, le_refl _, by lia, ?_⟩
        intro h2
        apply hne
        unfold Dop
        push Not at h1
        rw [h1, h2]; simp
    obtain ⟨α, hα1, hα2, hα4⟩ := wit i hi
    obtain ⟨β, hβ1, hβ2, hβ4⟩ := wit k hk
    have hv : u (j + 1) ≠ 0 := hg.ne_zero_between hα4 hβ4 (by lia) (by lia)
    have hpos : 0 < u (j + 1) := lt_of_le_of_ne (hg.nonneg _) (Ne.symm hv)
    have hjn : j ≤ n + 1 := by
      by_contra hjn
      exact hv (hz (j + 1) (by lia))
    have hjr : (j : ℝ) ≤ n + 1 := by exact_mod_cast hjn
    unfold Dop
    apply ne_of_gt
    apply div_pos _ (by positivity)
    have := mul_nonneg (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) - j by push_cast; linarith) (hg.nonneg j)
    have : 0 < ((j : ℝ) + 1) * u (j + 1) := mul_pos (by positivity) hpos
    linarith

end RealRooted.LiuMao
