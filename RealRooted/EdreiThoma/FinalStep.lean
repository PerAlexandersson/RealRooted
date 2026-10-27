module

public import RealRooted.Mathlib.Analysis.Complex.EntireExponentialType
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.Field

/-!
# Edrei's final affine-exponent lemma

A pair of entire functions with nonnegative Taylor coefficients controls the growth of an entire
exponent whose odd part is linear.  The resulting zero-free exponential is of exponential type,
so the affine-exponential theorem implies that the exponent itself is affine.  Positivity of the
Taylor coefficients then makes its slope real and nonnegative.

This is the final lemma in Edrei's proof of the converse Aissen--Schoenberg--Whitney theorem.
-/

public section

open Complex Filter Topology

noncomputable section

namespace RealRooted.EdreiThoma

open Complex

/-! ### Auxiliary lemmas for `final_lemma` -/

/-- Power series with nonnegative coefficients: values at real points. -/
private lemma nonneg_series_real {p : ℕ → ℝ} {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, HasSum (fun n => (p n : ℂ) * z ^ n) (F z)) (r : ℝ) :
    HasSum (fun n => p n * r ^ n) (F r).re ∧ (F r).im = 0 := by
  have := (Complex.hasSum_iff _ _).1 (hF r)
  refine ⟨?_, ?_⟩
  · simpa [← Complex.ofReal_pow, Complex.re_ofReal_mul] using this.1
  · have h2 := this.2
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im] at h2
    exact (h2.unique hasSum_zero)

private lemma nonneg_series_zero {p : ℕ → ℝ} {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, HasSum (fun n => (p n : ℂ) * z ^ n) (F z)) : F 0 = p 0 := by
  have h := hF 0
  have h' : HasSum (fun n => (p n : ℂ) * (0:ℂ) ^ n) (p 0 : ℂ) := by
    convert hasSum_single (f := fun n => (p n : ℂ) * (0:ℂ) ^ n) 0 ?_ using 1
    · simp
    · intro b hb; simp [zero_pow hb]
  exact h.unique h'

private lemma nonneg_series_ge {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, HasSum (fun n => (p n : ℂ) * z ^ n) (F z)) {r : ℝ} (hr : 0 ≤ r) :
    p 0 ≤ ‖F r‖ := by
  have h := (nonneg_series_real hF r).1
  have : p 0 * r ^ 0 ≤ (F r).re :=
    le_hasSum h 0 (fun j _ => mul_nonneg (hp j) (pow_nonneg hr j))
  simp at this
  exact this.trans (Complex.re_le_norm _)

private lemma nonneg_series_norm_le {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, HasSum (fun n => (p n : ℂ) * z ^ n) (F z)) (z : ℂ) :
    ‖F z‖ ≤ ‖F (‖z‖ : ℂ)‖ := by
  refine ((hF z).norm_le_of_bounded (nonneg_series_real hF ‖z‖).1 ?_).trans
    (Complex.re_le_norm _)
  intro n
  simp [norm_pow, abs_of_nonneg (hp n)]

/-- Lower bound for the product on the closed right half-plane. -/
private lemma one_le_norm_tprod {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) {z : ℂ}
    (hz : 0 ≤ z.re) :
    1 ≤ ‖∏' i, (1 + (α i : ℂ) * z)‖ := by
  by_cases hm : Multipliable (fun i => (1 + (α i : ℂ) * z))
  · have ht := hm.hasProd.norm
    refine ge_of_tendsto' ht (fun s => ?_)
    calc (1 : ℝ) = ∏ i ∈ s, (1 : ℝ) := by simp
      _ ≤ ∏ i ∈ s, ‖1 + (α i : ℂ) * z‖ :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => ?_)
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [add_re, one_re, re_ofReal_mul]
    nlinarith [hα i]
  · rw [tprod_eq_one_of_not_multipliable hm]; simp

/-- Subexponential growth of the product on the positive real axis. -/
private lemma norm_tprod_le {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (sα : Summable α)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 ≤ r →
      ‖∏' i, (1 + (α i : ℂ) * (r : ℂ))‖ ≤ K * Real.exp (δ * r) := by
  obtain ⟨N, hN⟩ : ∃ N, ∑' i, α i - ∑ i ∈ Finset.range N, α i < δ / 2 := by
    have := (sα.hasSum.tendsto_sum_nat.eventually (lt_mem_nhds
      (show ∑' i, α i - δ / 2 < ∑' i, α i by linarith))).exists
    obtain ⟨N, hN⟩ := this
    exact ⟨N, by linarith⟩
  set t : ℝ := δ / (2 * (N + 1)) with ht
  have htpos : 0 < t := by positivity
  have hNt : (N : ℝ) * t ≤ δ / 2 := by
    rw [ht, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set M : ℝ := ∑ i ∈ Finset.range N, α i / t
  refine ⟨Real.exp M, Real.exp_pos _, fun r hr => ?_⟩
  -- finite products
  have hfin : ∀ s : Finset ℕ,
      ∏ i ∈ s, (1 + α i * r) ≤ Real.exp M * Real.exp (δ * r) := by
    intro s
    set e : ℕ → ℝ := fun i => if i < N then α i / t + t * r else α i * r
    have h1 : ∏ i ∈ s, (1 + α i * r) ≤ ∏ i ∈ s, Real.exp (e i) := by
      refine Finset.prod_le_prod₀ (fun i _ => by nlinarith [hα i]) (fun i _ => ?_)
      simp only [e]
      split_ifs
      · rw [Real.exp_add]
        have ha := Real.add_one_le_exp (α i / t)
        have hb := Real.add_one_le_exp (t * r)
        have hai : 0 ≤ α i / t := div_nonneg (hα i) htpos.le
        calc 1 + α i * r ≤ (α i / t + 1) * (t * r + 1) := by
              have : α i / t * (t * r) = α i * r := by field_simp
              nlinarith [mul_nonneg hai (mul_nonneg htpos.le hr), mul_nonneg htpos.le hr]
          _ ≤ _ := mul_le_mul ha hb (by positivity) (Real.exp_pos _).le
      · linarith [Real.add_one_le_exp (α i * r)]
    have h2 : ∑ i ∈ s, e i ≤ M + δ * r := by
      simp only [e]
      rw [Finset.sum_ite]
      have hA : ∑ i ∈ s.filter (fun i => i < N), (α i / t + t * r) ≤
          ∑ i ∈ Finset.range N, (α i / t + t * r) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ?_)
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          exact hi.2
        · have := div_nonneg (hα i) htpos.le; positivity
      have hB : ∑ i ∈ s.filter (fun i => ¬ i < N), α i ≤
          ∑' i, α i - ∑ i ∈ Finset.range N, α i := by
        have hd : Disjoint (s.filter (fun i => ¬ i < N)) (Finset.range N) := by
          rw [Finset.disjoint_left]
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_range, not_lt] at hi ⊢
          exact hi.2
        have := sα.sum_le_tsum (s.filter (fun i => ¬ i < N) ∪ Finset.range N)
          (fun i _ => hα i)
        rw [Finset.sum_union hd] at this
        linarith
      have hR : ∑ i ∈ Finset.range N, (α i / t + t * r) = M + N * (t * r) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← Finset.sum_mul]
      have := mul_le_mul_of_nonneg_right hNt hr
      have : (∑ i ∈ s.filter (fun i => ¬ i < N), α i) * r ≤ δ / 2 * r :=
        mul_le_mul_of_nonneg_right (by linarith) hr
      nlinarith
    calc ∏ i ∈ s, (1 + α i * r) ≤ ∏ i ∈ s, Real.exp (e i) := h1
      _ = Real.exp (∑ i ∈ s, e i) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (M + δ * r) := Real.exp_le_exp.2 h2
      _ = _ := Real.exp_add _ _
  by_cases hm : Multipliable (fun i => (1 + (α i : ℂ) * (r : ℂ)))
  · refine le_of_tendsto' hm.hasProd.norm (fun s => ?_)
    refine le_trans (le_of_eq ?_) (hfin s)
    change (∏ i ∈ s, ‖1 + (α i : ℂ) * (r : ℂ)‖) = ∏ i ∈ s, (1 + α i * r)
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [show (1:ℂ) + ↑(α i) * ↑r = ↑(1 + α i * r) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by nlinarith [hα i])]
  · rw [tprod_eq_one_of_not_multipliable hm, norm_one]
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_exp (Finset.sum_nonneg (fun i _ => div_nonneg (hα i) htpos.le)))
      (Real.one_le_exp (by nlinarith))

/-- The product at real points is real. -/
private lemma tprod_ofReal_eq {α : ℕ → ℝ} (sα : Summable α) (r : ℝ) :
    (∏' i, (1 + (α i : ℂ) * (r : ℂ))) = ((∏' i, (1 + α i * r) : ℝ) : ℂ) := by
  have hm : Multipliable (fun i => 1 + α i * r) :=
    multipliable_one_add_of_summable (by simpa [norm_mul] using sα.norm.mul_right ‖r‖)
  have := hm.hasProd.map Complex.ofRealHom Complex.continuous_ofReal
  refine Eq.trans ?_ this.tprod_eq
  congr 1; ext i; simp

/-- Entire `h` with `Re h` of at most linear growth is affine. -/
private lemma affine_of_re_le {h : ℂ → ℂ} (hh : Differentiable ℂ h) {A B : ℝ}
    (hb : ∀ z, (h z).re ≤ A + B * ‖z‖) : ∃ a : ℂ, ∀ z, h z = h 0 + a * z := by
  set f : ℂ → ℂ := fun z => Complex.exp (h z - h 0) with hf
  have hfd : Differentiable ℂ f := (hh.sub_const _).cexp
  have hf0 : f 0 = 1 := by simp [hf]
  set C : ℝ := |A - (h 0).re| + |B|
  have hC : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖)) := by
    intro z
    rw [hf, Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have h1 := hb z
    have h2 : A - (h 0).re ≤ |A - (h 0).re| := le_abs_self _
    have h3 : B * ‖z‖ ≤ |B| * ‖z‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    have h4 : 0 ≤ |A - (h 0).re| * ‖z‖ := by positivity
    change (h z - h 0).re ≤ (|A - (h 0).re| + |B|) * (1 + ‖z‖)
    rw [sub_re]
    nlinarith [abs_nonneg B]
  obtain ⟨a, b, hab⟩ :=
    hfd.exists_eq_exp_affine_of_norm_le_exp (fun _ => Complex.exp_ne_zero _) hC
  have hb : Complex.exp b = 1 := by
    simpa [hf0] using (hab 0).symm
  have ha : ∀ w, f w = Complex.exp (a * w) := by
    intro w
    rw [hab w, Complex.exp_add, hb, mul_one]
  refine ⟨a, fun z => ?_⟩
  set g : ℂ → ℂ := fun w => h w - h 0 - a * w with hg
  have hgd : Differentiable ℂ g := (hh.sub_const _).sub (differentiable_id.const_mul a)
  have hexp : ∀ w, Complex.exp (g w) = 1 := by
    intro w
    have := ha w
    simp only [hf] at this
    simp only [hg, sub_eq_add_neg _ (a * w)]
    rw [Complex.exp_add, this, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hderiv : ∀ w, deriv g w = 0 := by
    intro w
    have h1 : deriv (fun w => Complex.exp (g w)) w = Complex.exp (g w) * deriv g w :=
      deriv_cexp (hgd w)
    have h2 : (fun w => Complex.exp (g w)) = fun _ => (1:ℂ) := funext hexp
    rw [h2, deriv_const, hexp] at h1
    simpa using h1.symm
  have := is_const_of_deriv_eq_zero hgd hderiv z 0
  simp only [hg, sub_self, mul_zero] at this
  linear_combination this

/-- Linear upper bound on `Re h` (Steps 1-3). -/
private lemma re_le_of_series {h : ℂ → ℂ} {c : ℂ}
    (hodd : ∀ z, h z - h (-z) = 2 * c * z) {α β : ℕ → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) (sα : Summable α) (sβ : Summable β)
    {p q : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) (hq : ∀ n, 0 ≤ q n)
    (hu1 : ∀ z : ℂ, HasSum (fun n => (p n : ℂ) * z ^ n)
        (Complex.exp (h z + (1:ℝ) * z) * ∏' i, (1 + (α i : ℂ) * z)))
    (hu2 : ∀ z : ℂ, HasSum (fun n => (q n : ℂ) * z ^ n)
        (Complex.exp ((1:ℝ) * z - h (-z)) * ∏' i, (1 + (β i : ℂ) * z))) :
    ∃ A B : ℝ, ∀ z, (h z).re ≤ A + B * ‖z‖ := by
  obtain ⟨K1, hK1, hK1b⟩ := norm_tprod_le hα sα one_pos
  obtain ⟨K2, hK2, hK2b⟩ := norm_tprod_le hβ sβ one_pos
  set F1 : ℂ → ℂ := fun z => Complex.exp (h z + (1:ℝ) * z) * ∏' i, (1 + (α i : ℂ) * z)
  set F2 : ℂ → ℂ := fun z =>
    Complex.exp ((1:ℝ) * z - h (-z)) * ∏' i, (1 + (β i : ℂ) * z)
  have hF20 : F2 0 = Complex.exp (- h 0) := by simp [F2]
  have hq0 : q 0 = Real.exp (-(h 0).re) := by
    have := congrArg norm ((nonneg_series_zero hu2).symm.trans hF20)
    rw [Complex.norm_real, Real.norm_of_nonneg (hq 0), Complex.norm_exp] at this
    simpa using this
  -- bound on the positive axis
  have hpos : ∀ r : ℝ, 0 ≤ r →
      ‖F1 r‖ ≤ K1 * K2 * Real.exp ((h 0).re) * Real.exp ((2 * ‖c‖ + 4) * r) := by
    intro r hr
    have hlow : Real.exp (-(h 0).re) ≤ ‖F2 r‖ := hq0 ▸ nonneg_series_ge hq hu2 hr
    have hprod : ‖F1 r‖ * ‖F2 r‖ ≤
        Real.exp ((2 * ‖c‖ + 2) * r) * (K1 * Real.exp (1 * r)) *
          (K2 * Real.exp (1 * r)) := by
      rw [← norm_mul]
      have : F1 r * F2 r = Complex.exp (2 * c * r + 2 * r) *
          ((∏' i, (1 + (α i : ℂ) * r)) * ∏' i, (1 + (β i : ℂ) * r)) := by
        have e : Complex.exp (2 * c * r + 2 * r) =
            Complex.exp (h r + (1:ℝ) * r) * Complex.exp ((1:ℝ) * r - h (-r)) := by
          rw [← Complex.exp_add]; congr 1; push_cast; linear_combination -(hodd r)
        simp only [F1, F2]
        rw [e]; ring
      rw [this, norm_mul, norm_mul, Complex.norm_exp]
      refine le_trans (mul_le_mul ?_ (mul_le_mul (hK1b r hr) (hK2b r hr) (norm_nonneg _)
        (by positivity)) (by positivity) (by positivity)) (le_of_eq (mul_assoc _ _ _).symm)
      refine Real.exp_le_exp.2 ?_
      have := Complex.re_le_norm c
      simp
      nlinarith [mul_le_mul_of_nonneg_right this hr]
    have hE : 0 < Real.exp (-(h 0).re) := Real.exp_pos _
    have : ‖F1 r‖ * Real.exp (-(h 0).re) ≤ ‖F1 r‖ * ‖F2 r‖ :=
      mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
    have key : ‖F1 r‖ * Real.exp (-(h 0).re) ≤
        K1 * K2 * Real.exp ((h 0).re) * Real.exp ((2 * ‖c‖ + 4) * r) *
          Real.exp (-(h 0).re) := by
      refine this.trans (hprod.trans (le_of_eq ?_))
      have e1 :
          Real.exp ((2 * ‖c‖ + 2) * r) * (K1 * Real.exp (1 * r)) *
              (K2 * Real.exp (1 * r)) =
            K1 * K2 * Real.exp ((2 * ‖c‖ + 4) * r) := by
        rw [show (2 * ‖c‖ + 4) * r = (2 * ‖c‖ + 2) * r + 1 * r + 1 * r by ring,
          Real.exp_add, Real.exp_add]
        ring
      have hh0 : Real.exp ((h 0).re) * Real.exp (-(h 0).re) = 1 := by
        rw [← Real.exp_add]; simp
      rw [e1]
      linear_combination -(K1 * K2 * Real.exp ((2 * ‖c‖ + 4) * r)) * hh0
    exact le_of_mul_le_mul_right key hE
  set L := Real.log (K1 * K2 * Real.exp ((h 0).re))
  have hKpos : 0 < K1 * K2 * Real.exp ((h 0).re) := by positivity
  have hright : ∀ z : ℂ, 0 ≤ z.re → (h z).re ≤ L + (2 * ‖c‖ + 5) * ‖z‖ := by
    intro z hz
    have h1 := nonneg_series_norm_le hp hu1 z
    have h2 := hpos ‖z‖ (norm_nonneg _)
    have h3 : Real.exp ((h z).re + z.re) ≤ ‖F1 z‖ := by
      simp only [F1, norm_mul, Complex.norm_exp]
      have := one_le_norm_tprod hα hz
      simp only [add_re, Complex.ofReal_one, one_mul]
      nlinarith [Real.exp_pos ((h z).re + z.re)]
    have h4 : Real.exp ((h z).re + z.re) ≤ Real.exp (L + (2 * ‖c‖ + 4) * ‖z‖) := by
      calc Real.exp ((h z).re + z.re) ≤ ‖F1 z‖ := h3
        _ ≤ _ := h1.trans h2
        _ = _ := by rw [Real.exp_add, Real.exp_log hKpos]
    have h5 := Real.exp_le_exp.1 h4
    have h6 : -z.re ≤ ‖z‖ := by
      have := Complex.abs_re_le_norm z
      linarith [neg_abs_le z.re, neg_le_abs z.re]
    linarith
  refine ⟨L, 4 * ‖c‖ + 5, fun z => ?_⟩
  rcases le_or_gt 0 z.re with hz | hz
  · have := hright z hz
    nlinarith [norm_nonneg z, norm_nonneg c]
  · have h1 := hright (-z) (by simp; linarith)
    have h2 : h z = h (-z) + 2 * c * z := by linear_combination hodd z
    have h3 : (2 * c * z).re ≤ 2 * ‖c‖ * ‖z‖ := by
      refine (Complex.re_le_norm _).trans (le_of_eq ?_)
      simp
    rw [h2, add_re]
    rw [norm_neg] at h1
    nlinarith [norm_nonneg z, norm_nonneg c]


/-- Step 2: the linear coefficient is real. -/
private lemma im_eq_zero_of_affine {h : ℂ → ℂ} {a : ℂ}
    (ha : ∀ z, h z = h 0 + a * z) {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i)
    (sα : Summable α) {p : ℕ → ℝ} {ε : ℝ}
    (hu1 : ∀ z : ℂ, HasSum (fun n => (p n : ℂ) * z ^ n)
        (Complex.exp (h z + ε * z) * ∏' i, (1 + (α i : ℂ) * z))) : a.im = 0 := by
  have him := fun r : ℝ => (nonneg_series_real hu1 r).2
  have h0 : Real.sin (h 0).im = 0 := by
    simpa [Complex.exp_im] using him 0
  set r : ℝ := 1 / (|a.im| + 1) with hr
  have hrpos : 0 < r := by positivity
  have hP : (∏' i, (1 + α i * r) : ℝ) ≠ 0 := by
    have := one_le_norm_tprod hα (z := (r : ℂ))
      (by simpa only [Complex.ofReal_re] using hrpos.le)
    rw [tprod_ofReal_eq sα r] at this
    intro h'
    have : (1 : ℝ) ≤ 0 := by simpa [h'] using this
    norm_num at this
  have h1 := him r
  rw [tprod_ofReal_eq sα r, Complex.im_mul_ofReal, Complex.exp_im, ha r] at h1
  have h2 : Real.sin ((h 0).im + a.im * r) = 0 := by
    have := mul_eq_zero.1 h1
    rcases this with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 (Real.exp_pos _).ne'
      · simpa [Complex.mul_im] using h4
    · exact absurd h3 hP
  rw [Real.sin_add, h0, zero_mul, zero_add] at h2
  have hcos : Real.cos (h 0).im ≠ 0 := by
    intro hc
    have := Real.sin_sq_add_cos_sq (h 0).im
    rw [h0, hc] at this; norm_num at this
  have h3 : Real.sin (a.im * r) = 0 := by
    rcases mul_eq_zero.1 h2 with h4 | h4
    · exact absurd h4 hcos
    · exact h4
  have hlt : |a.im * r| < 1 := by
    rw [abs_mul, abs_of_pos hrpos, hr, mul_one_div, div_lt_one (by positivity)]
    linarith
  have h4 := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [neg_abs_le (a.im * r),
    Real.pi_gt_three]) (by linarith [le_abs_self (a.im * r), Real.pi_gt_three])).1 h3
  rcases mul_eq_zero.1 h4 with h5 | h5
  · exact h5
  · exact absurd h5 hrpos.ne'

/-- Step 5: the (real) linear coefficient is nonnegative. -/
private lemma nonneg_of_affine {h : ℂ → ℂ} {γ : ℝ}
    (ha : ∀ z, h z = h 0 + γ * z) {α β : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i)
    (hβ : ∀ i, 0 ≤ β i) (sα : Summable α) (sβ : Summable β)
    (h1 : ∀ ε : ℝ, 0 < ε → ∃ p : ℕ → ℝ, (∀ n, 0 ≤ p n) ∧ ∀ z : ℂ,
      HasSum (fun n => (p n : ℂ) * z ^ n)
        (Complex.exp (h z + ε * z) * ∏' i, (1 + (α i : ℂ) * z)))
    (h2 : ∀ ε : ℝ, 0 < ε → ∃ p : ℕ → ℝ, (∀ n, 0 ≤ p n) ∧ ∀ z : ℂ,
      HasSum (fun n => (p n : ℂ) * z ^ n)
        (Complex.exp (ε * z - h (-z)) * ∏' i, (1 + (β i : ℂ) * z))) :
    0 ≤ γ := by
  by_contra hneg
  push Not at hneg
  obtain ⟨p, hp, hu1⟩ := h1 (-γ / 2) (by linarith)
  obtain ⟨q, hq, hu2⟩ := h2 (-γ / 2) (by linarith)
  obtain ⟨K1, hK1, hK1b⟩ := norm_tprod_le hα sα (δ := -γ / 4) (by linarith)
  obtain ⟨K2, hK2, hK2b⟩ := norm_tprod_le hβ sβ (δ := -γ / 4) (by linarith)
  set F1 : ℂ → ℂ := fun z => Complex.exp (h z + ((-γ / 2 : ℝ) : ℂ) * z) *
    ∏' i, (1 + (α i : ℂ) * z)
  set F2 : ℂ → ℂ := fun z => Complex.exp (((-γ / 2 : ℝ) : ℂ) * z - h (-z)) *
    ∏' i, (1 + (β i : ℂ) * z)
  have hp0 : p 0 = Real.exp ((h 0).re) := by
    have := congrArg norm ((nonneg_series_zero hu1).symm.trans (show F1 0 = _ by rfl))
    rw [Complex.norm_real, Real.norm_of_nonneg (hp 0)] at this
    simpa [F1, Complex.norm_exp] using this
  have hq0 : q 0 = Real.exp (-(h 0).re) := by
    have := congrArg norm ((nonneg_series_zero hu2).symm.trans (show F2 0 = _ by rfl))
    rw [Complex.norm_real, Real.norm_of_nonneg (hq 0)] at this
    simpa [F2, Complex.norm_exp] using this
  have hbound : ∀ r : ℝ, 0 ≤ r → 1 ≤ K1 * K2 * Real.exp (γ / 2 * r) := by
    intro r hr
    have l1 : Real.exp ((h 0).re) ≤ ‖F1 r‖ := hp0 ▸ nonneg_series_ge hp hu1 hr
    have l2 : Real.exp (-(h 0).re) ≤ ‖F2 r‖ := hq0 ▸ nonneg_series_ge hq hu2 hr
    have hlow : 1 ≤ ‖F1 r‖ * ‖F2 r‖ := by
      have := mul_le_mul l1 l2 (Real.exp_pos _).le (norm_nonneg _)
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
    have e : F1 r * F2 r = Complex.exp ((γ * r : ℝ) : ℂ) *
        ((∏' i, (1 + (α i : ℂ) * r)) * ∏' i, (1 + (β i : ℂ) * r)) := by
      have e : Complex.exp ((γ * r : ℝ) : ℂ) =
          Complex.exp (h r + ((-γ / 2 : ℝ) : ℂ) * r) *
            Complex.exp (((-γ / 2 : ℝ) : ℂ) * r - h (-r)) := by
        rw [← Complex.exp_add]; congr 1; rw [ha r, ha (-r)]; push_cast; ring
      simp only [F1, F2]
      rw [e]; ring
    have hup : ‖F1 r‖ * ‖F2 r‖ ≤ K1 * K2 * Real.exp (γ / 2 * r) := by
      rw [← norm_mul, e, norm_mul, norm_mul, Complex.norm_exp, Complex.ofReal_re]
      calc
        Real.exp (γ * r) *
              (‖∏' i, (1 + (α i : ℂ) * r)‖ * ‖∏' i, (1 + (β i : ℂ) * r)‖) ≤
            Real.exp (γ * r) *
              ((K1 * Real.exp (-γ / 4 * r)) * (K2 * Real.exp (-γ / 4 * r))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hK1b r hr) (hK2b r hr) (norm_nonneg _)
              (by positivity)) (Real.exp_pos _).le
        _ = K1 * K2 * Real.exp (γ / 2 * r) := by
          rw [show γ / 2 * r = γ * r + -γ / 4 * r + -γ / 4 * r by ring, Real.exp_add,
            Real.exp_add]; ring
    linarith
  set L := Real.log (K1 * K2)
  have hKpos : 0 < K1 * K2 := by positivity
  set r : ℝ := 2 * (|L| + 1) / (-γ) with hr
  have hrpos : 0 < r := by
    apply div_pos (by positivity) (by linarith)
  have hγr : γ / 2 * r = -(|L| + 1) := by
    have hγ0 : γ ≠ 0 := hneg.ne
    rw [hr]; field_simp
  have := hbound r hrpos.le
  rw [hγr, ← Real.exp_log hKpos, ← Real.exp_add] at this
  have := Real.one_le_exp_iff.1 this
  linarith [le_abs_self L]

/-- **Final lemma of Edrei's Proposition B** (Edrei, Canad. J. Math. 5 (1953), p. 93-94; the
odd-part hypothesis is essential: `h = z^3` is a counterexample without it).

Let `h` be entire with `h z - h (-z) = 2 c z` (linear odd part), and let
`α, β ≥ 0` be summable.
Suppose that for every `ε > 0` the two entire functions
`u₁^ε = exp (h z + ε z) * ∏ (1 + α_i z)` and
`u₂^ε = exp (ε z - h (-z)) * ∏ (1 + β_i z)`
have nonnegative Taylor coefficients at `0` (their power series converge to them on all of `ℂ`).
Then `h z = h 0 + γ z` with `γ ≥ 0`. -/
theorem exists_nonneg_eq_affine_of_series {h : ℂ → ℂ} (hh : Differentiable ℂ h) {c : ℂ}
    (hodd : ∀ z, h z - h (-z) = 2 * c * z) {α β : ℕ → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) (sα : Summable α) (sβ : Summable β)
    (h1 : ∀ ε : ℝ, 0 < ε → ∃ p : ℕ → ℝ, (∀ n, 0 ≤ p n) ∧ ∀ z : ℂ,
      HasSum (fun n => (p n : ℂ) * z ^ n)
        (Complex.exp (h z + ε * z) * ∏' i, (1 + (α i : ℂ) * z)))
    (h2 : ∀ ε : ℝ, 0 < ε → ∃ p : ℕ → ℝ, (∀ n, 0 ≤ p n) ∧ ∀ z : ℂ,
      HasSum (fun n => (p n : ℂ) * z ^ n)
        (Complex.exp (ε * z - h (-z)) * ∏' i, (1 + (β i : ℂ) * z))) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ z : ℂ, h z = h 0 + γ * z := by
  obtain ⟨p, hp, hu1⟩ := h1 1 one_pos
  obtain ⟨q, hq, hu2⟩ := h2 1 one_pos
  obtain ⟨A, B, hAB⟩ := re_le_of_series hodd hα hβ sα sβ hp hq hu1 hu2
  obtain ⟨a, ha⟩ := affine_of_re_le hh hAB
  have him := im_eq_zero_of_affine ha hα sα hu1
  have haγ : a = (a.re : ℂ) := Complex.ext rfl (by simp [him])
  rw [haγ] at ha
  exact ⟨a.re, nonneg_of_affine ha hα hβ sα sβ h1 h2, ha⟩

end RealRooted.EdreiThoma

