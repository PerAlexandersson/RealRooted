module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.RootContinuity
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Products in the Laguerre–Pólya class

Every entire function
`c z ^ m e^(-a z² + b z) ∏ₖ (1 - yₖ z) e^(yₖ z)` with `a ≥ 0` and `∑ yₖ² < ∞` belongs to the
Laguerre–Pólya class: it is a locally uniform limit of real polynomials with only real zeros.
The zeros are written through their reciprocals `yₖ = 1 / xₖ`; a factor with `yₖ = 0` is `1`,
so functions with finitely many zeros are included.

The approximants are
`c X ^ m (1 - a X² / n) ^ n (1 + b X / n) ^ n ∏_{k < n} (1 - yₖ X) (1 + yₖ X / n) ^ n`.

The converse, that every function in the class has this form, is not formalized here.
-/

@[expose] public section

open Polynomial

namespace RealRooted

/-- A real polynomial that is zero or has only real complex zeros. -/
private def RealRootedOrZero (p : ℝ[X]) : Prop :=
  p = 0 ∨ ∀ z : ℂ, (p.map Complex.ofRealHom).eval z = 0 → z.im = 0

namespace LaguerrePolya

open Complex Filter Topology

/-- Error term in `(1 + w/n)^n = exp (w + lpErr n w)`. -/
private noncomputable def lpErr (n : ℕ) (w : ℂ) : ℂ := n * (Complex.log (1 + w / n) - w / n)

private lemma one_add_div_pow_eq_exp {n : ℕ} (hn : 0 < n) {w : ℂ} (hw : ‖w‖ ≤ n / 2) :
    (1 + w / n) ^ n = Complex.exp (w + lpErr n w) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsmall : ‖w / n‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hn']; linarith
  have hne : 1 + w / n ≠ 0 := by
    intro h
    have : w / n = -1 := by linear_combination h
    rw [this] at hsmall; norm_num at hsmall
  have : w + lpErr n w = n * Complex.log (1 + w / n) := by
    unfold lpErr; field_simp; ring
  rw [this, Complex.exp_nat_mul, Complex.exp_log hne]

private lemma norm_lpErr_le {n : ℕ} (hn : 0 < n) {w : ℂ} (hw : ‖w‖ ≤ n / 2) :
    ‖lpErr n w‖ ≤ ‖w‖ ^ 2 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsmall : ‖w / n‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hn']; linarith
  have h := Complex.norm_log_one_add_sub_self_le (z := w / n) (by linarith)
  have h2 : ‖w / n‖ ^ 2 * (1 - ‖w / n‖)⁻¹ / 2 ≤ ‖w / n‖ ^ 2 := by
    have : (1 - ‖w / n‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    nlinarith [sq_nonneg ‖w / n‖]
  unfold lpErr
  rw [norm_mul, Complex.norm_natCast]
  calc (n : ℝ) * ‖Complex.log (1 + w / n) - w / n‖ ≤ n * ‖w / n‖ ^ 2 := by
        gcongr; exact h.trans h2
    _ = ‖w‖ ^ 2 / n := by
        rw [norm_div, Complex.norm_natCast]; field_simp

/-- Products of uniformly convergent sequences with bounded limits converge uniformly. -/
private lemma tendstoUniformlyOn_mul_of_bdd {K : Set ℂ} {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    (hF : TendstoUniformlyOn F f atTop K) (hG : TendstoUniformlyOn G g atTop K)
    (hf : ∃ A, ∀ z ∈ K, ‖f z‖ ≤ A) (hg : ∃ B, ∀ z ∈ K, ‖g z‖ ≤ B) :
    TendstoUniformlyOn (fun n z => F n z * G n z) (fun z => f z * g z) atTop K := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  rw [Metric.tendstoUniformlyOn_iff] at hF hG ⊢
  intro ε hε
  set A' := max A 0
  set B' := max B 0
  have hA' : 0 ≤ A' := le_max_right _ _
  have hB' : 0 ≤ B' := le_max_right _ _
  set δ := min 1 (ε / (2 * (1 + A' + B'))) with hδ
  have hδpos : 0 < δ := lt_min one_pos (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ * (1 + A' + B') ≤ ε / 2 := by
    have := min_le_right 1 (ε / (2 * (1 + A' + B')))
    rw [← hδ, le_div_iff₀ (by positivity)] at this
    linarith
  filter_upwards [hF δ hδpos, hG δ hδpos] with n hn1 hn2 z hz
  have h1 := hn1 z hz
  have h2 := hn2 z hz
  rw [dist_eq_norm] at h1 h2 ⊢
  have hfz : ‖f z‖ ≤ A' := (hA z hz).trans (le_max_left _ _)
  have hgz : ‖g z‖ ≤ B' := (hB z hz).trans (le_max_left _ _)
  have key : f z * g z - F n z * G n z = (f z - F n z) * g z + f z * (g z - G n z)
      - (f z - F n z) * (g z - G n z) := by ring
  rw [key]
  calc ‖(f z - F n z) * g z + f z * (g z - G n z) - (f z - F n z) * (g z - G n z)‖
      ≤ ‖f z - F n z‖ * ‖g z‖ + ‖f z‖ * ‖g z - G n z‖ + ‖f z - F n z‖ * ‖g z - G n z‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
        gcongr
        exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
    _ ≤ δ * B' + A' * δ + δ * δ := by
        gcongr
    _ ≤ δ * (1 + A' + B') := by nlinarith
    _ < ε := by linarith

/-- The canonical product converges uniformly on compact sets. -/
private lemma tendstoUniformlyOn_canonicalProduct (y : ℕ → ℝ) (hy : Summable fun k => y k ^ 2)
    {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n z => ∏ k ∈ Finset.range n, (1 - (y k : ℂ) * z) * cexp (y k * z))
      (fun z => ∏' k, (1 - (y k : ℂ) * z) * cexp (y k * z)) atTop K := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hev : ∀ᶠ k in atTop, ∀ z ∈ K,
      ‖(1 - (y k : ℂ) * z) * cexp (y k * z) - 1‖ ≤ 3 * (y k ^ 2 * R ^ 2) := by
    have ht : Tendsto (fun k => y k ^ 2 * R ^ 2) atTop (𝓝 0) := by
      simpa using hy.tendsto_atTop_zero.mul_const (R ^ 2)
    filter_upwards [ht.eventually_le_const one_pos] with k hk z hz
    have hzR : ‖z‖ ≤ R := by simpa using hR hz
    have hw2 : ‖(y k : ℂ) * z‖ ^ 2 ≤ y k ^ 2 * R ^ 2 := by
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      gcongr
    have hw1 : ‖(y k : ℂ) * z‖ ≤ 1 := by
      by_contra h
      push Not at h
      nlinarith
    set w : ℂ := (y k : ℂ) * z
    have key : (1 - w) * cexp w - 1 = (cexp w - 1 - w) - w * (cexp w - 1) := by ring
    rw [key]
    calc ‖(cexp w - 1 - w) - w * (cexp w - 1)‖ ≤ ‖cexp w - 1 - w‖ + ‖w‖ * ‖cexp w - 1‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ ‖w‖ ^ 2 + ‖w‖ * (2 * ‖w‖) := by
          gcongr
          · exact Complex.norm_exp_sub_one_sub_id_le hw1
          · exact Complex.norm_exp_sub_one_le hw1
      _ = 3 * ‖w‖ ^ 2 := by ring
      _ ≤ 3 * (y k ^ 2 * R ^ 2) := by linarith
  have hcts : ∀ k, ContinuousOn (fun z : ℂ => (1 - (y k : ℂ) * z) * cexp (y k * z) - 1) K :=
    fun k => by apply Continuous.continuousOn; fun_prop
  have H := (Summable.hasProdUniformlyOn_nat_one_add hK
    ((hy.mul_right (R ^ 2)).mul_left 3) hev hcts).tendstoUniformlyOn_finsetRange
  simpa using H

/-- The correction factor `H_n` tends to `1` uniformly on closed balls. -/
private lemma tendstoUniformlyOn_correction (a b : ℝ) (y : ℕ → ℝ) (hy : Summable fun k => y k ^ 2)
    (R : ℝ) :
    TendstoUniformlyOn (fun (n : ℕ) (z : ℂ) =>
      ((1 + (-(a : ℂ) * z ^ 2) / n) ^ n * (1 + (b : ℂ) * z / n) ^ n *
        ∏ k ∈ Finset.range n, (1 + (y k : ℂ) * z / n) ^ n) /
      (cexp (-(a : ℂ) * z ^ 2 + b * z) * ∏ k ∈ Finset.range n, cexp (y k * z)))
      (fun _ => 1) atTop (Metric.closedBall 0 R) := by
  set R' := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  set S := ∑' k, y k ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => sq_nonneg _
  have hyS : ∀ k, y k ^ 2 ≤ S := fun k =>
    hy.le_tsum k (fun j _ => sq_nonneg (y j))
  set C := a ^ 2 * R' ^ 4 + b ^ 2 * R' ^ 2 + S * R' ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set N0 : ℝ := 2 + 2 * |a| * R' ^ 2 + 2 * |b| * R' + 2 * S * R' ^ 2 + C + 2 * C / ε
  have hN0 : 0 ≤ 2 * C / ε := by positivity
  filter_upwards [eventually_ge_atTop ⌈N0⌉₊] with n hn z hz
  have hnN : N0 ≤ n := (Nat.le_ceil N0).trans (by exact_mod_cast hn)
  have hab : 0 ≤ 2 * |a| * R' ^ 2 := by positivity
  have hbb : 0 ≤ 2 * |b| * R' := by positivity
  have hSS : 0 ≤ 2 * S * R' ^ 2 := by positivity
  have hn2 : (2 : ℝ) ≤ n := by linarith
  have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hnpos : (0 : ℝ) < n := by linarith
  have hz' : ‖z‖ ≤ R' := by
    have : ‖z‖ ≤ R := by simpa using hz
    exact this.trans (le_max_left _ _)
  -- norms of the three kinds of arguments
  have hwa : ‖-(a : ℂ) * z ^ 2‖ ≤ |a| * R' ^ 2 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    gcongr
  have hwb : ‖(b : ℂ) * z‖ ≤ |b| * R' := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
  have hwy : ∀ k, ‖(y k : ℂ) * z‖ ^ 2 ≤ y k ^ 2 * R' ^ 2 := by
    intro k
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    gcongr
  have ha2 : ‖-(a : ℂ) * z ^ 2‖ ≤ n / 2 := by linarith
  have hb2 : ‖(b : ℂ) * z‖ ≤ n / 2 := by linarith
  have hy2 : ∀ k, ‖(y k : ℂ) * z‖ ≤ n / 2 := by
    intro k
    by_contra h
    push Not at h
    have h1 : (n / 2 : ℝ) ^ 2 < ‖(y k : ℂ) * z‖ ^ 2 := by
      have : (0 : ℝ) ≤ n / 2 := by linarith
      nlinarith
    have h2 : y k ^ 2 * R' ^ 2 ≤ S * R' ^ 2 := by gcongr; exact hyS k
    have h3 : S * R' ^ 2 ≤ n / 2 := by linarith
    nlinarith [hwy k]
  -- rewrite everything as an exponential
  set E : ℂ := lpErr n (-(a : ℂ) * z ^ 2) + lpErr n ((b : ℂ) * z) +
    ∑ k ∈ Finset.range n, lpErr n ((y k : ℂ) * z) with hE
  have hH : ((1 + (-(a : ℂ) * z ^ 2) / n) ^ n * (1 + (b : ℂ) * z / n) ^ n *
        ∏ k ∈ Finset.range n, (1 + (y k : ℂ) * z / n) ^ n) /
      (cexp (-(a : ℂ) * z ^ 2 + b * z) * ∏ k ∈ Finset.range n, cexp (y k * z)) = cexp E := by
    rw [one_add_div_pow_eq_exp hn0 ha2, one_add_div_pow_eq_exp hn0 hb2,
      Finset.prod_congr rfl (fun k _ => one_add_div_pow_eq_exp hn0 (hy2 k)),
      ← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add, ← Complex.exp_sub, hE, Finset.sum_add_distrib]
    congr 1
    ring
  have hEb : ‖E‖ ≤ C / n := by
    have e1 := norm_lpErr_le hn0 ha2
    have e2 := norm_lpErr_le hn0 hb2
    have e3 : ‖∑ k ∈ Finset.range n, lpErr n ((y k : ℂ) * z)‖ ≤ S * R' ^ 2 / n := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k ∈ Finset.range n, ‖lpErr n ((y k : ℂ) * z)‖
          ≤ ∑ k ∈ Finset.range n, y k ^ 2 * R' ^ 2 / n := by
            refine Finset.sum_le_sum fun k _ => (norm_lpErr_le hn0 (hy2 k)).trans ?_
            gcongr
            exact hwy k
        _ = (∑ k ∈ Finset.range n, y k ^ 2) * R' ^ 2 / n := by
            rw [Finset.sum_mul, Finset.sum_div]
        _ ≤ S * R' ^ 2 / n := by
            gcongr
            exact hy.sum_le_tsum _ (fun j _ => sq_nonneg (y j))
    have e1' : ‖-(a : ℂ) * z ^ 2‖ ^ 2 / n ≤ a ^ 2 * R' ^ 4 / n := by
      gcongr
      calc ‖-(a : ℂ) * z ^ 2‖ ^ 2 ≤ (|a| * R' ^ 2) ^ 2 := by gcongr
        _ = a ^ 2 * R' ^ 4 := by rw [mul_pow, sq_abs]; ring
    have e2' : ‖(b : ℂ) * z‖ ^ 2 / n ≤ b ^ 2 * R' ^ 2 / n := by
      gcongr
      calc ‖(b : ℂ) * z‖ ^ 2 ≤ (|b| * R') ^ 2 := by gcongr
        _ = b ^ 2 * R' ^ 2 := by rw [mul_pow, sq_abs]
    calc ‖E‖ ≤ ‖lpErr n (-(a : ℂ) * z ^ 2)‖ + ‖lpErr n ((b : ℂ) * z)‖ +
          ‖∑ k ∈ Finset.range n, lpErr n ((y k : ℂ) * z)‖ := by
          rw [hE]; exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ a ^ 2 * R' ^ 4 / n + b ^ 2 * R' ^ 2 / n + S * R' ^ 2 / n := by linarith
      _ = C / n := by rw [hC]; ring
  have hCn : C / n ≤ 1 := by rw [div_le_one hnpos]; linarith
  have hCe : 2 * (C / n) < ε := by
    have : 2 * C / ε < n := by linarith
    rw [div_lt_iff₀ hε] at this
    rw [← mul_div_assoc, div_lt_iff₀ hnpos]
    linarith
  rw [hH, dist_comm, dist_eq_norm]
  calc ‖cexp E - 1‖ ≤ 2 * ‖E‖ := Complex.norm_exp_sub_one_le (hEb.trans hCn)
    _ ≤ 2 * (C / n) := by gcongr
    _ < ε := hCe

/-- The approximating polynomials. -/
private noncomputable def approx (c : ℝ) (m : ℕ) (a b : ℝ) (y : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  C c * X ^ m * (1 + C (-a / n) * X ^ 2) ^ n * (1 + C (b / n) * X) ^ n *
    ∏ k ∈ Finset.range n, ((1 - C (y k) * X) * (1 + C (y k / n) * X) ^ n)

private lemma eval_approx (c : ℝ) (m : ℕ) (a b : ℝ) (y : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    ((approx c m a b y n).map Complex.ofRealHom).eval z =
      c * z ^ m * (1 + (-(a : ℂ) * z ^ 2) / n) ^ n * (1 + (b : ℂ) * z / n) ^ n *
        ∏ k ∈ Finset.range n, ((1 - (y k : ℂ) * z) * (1 + (y k : ℂ) * z / n) ^ n) := by
  simp only [approx, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_one, Polynomial.map_C,
    Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_prod, Polynomial.eval_one, Polynomial.eval_C,
    Polynomial.eval_X, Complex.ofRealHom_eq_coe]
  push_cast
  congr 1
  · congr 1
    · congr 2; ring
    · congr 2; ring
  · refine Finset.prod_congr rfl fun k _ => ?_
    congr 2; ring

private lemma im_eq_zero_of_linear {r : ℝ} {z : ℂ} (h : 1 + (r : ℂ) * z = 0) : z.im = 0 := by
  have h1 : 1 + r * z.re = 0 := by simpa using congrArg Complex.re h
  have h2 : r * z.im = 0 := by simpa using congrArg Complex.im h
  rcases mul_eq_zero.1 h2 with hr | hz
  · simp [hr] at h1
  · exact hz

private lemma im_eq_zero_of_quadratic {r : ℝ} (hr : 0 ≤ r) {z : ℂ}
    (h : 1 + (-(r : ℂ)) * z ^ 2 = 0) : z.im = 0 := by
  have h1 : 1 - r * (z.re * z.re - z.im * z.im) = 0 := by
    simpa [pow_two, sub_eq_add_neg] using congrArg Complex.re h
  have h2 : r * (z.re * z.im + z.im * z.re) = 0 := by
    simpa [pow_two] using congrArg Complex.im h
  by_contra hz
  have h3 : r * z.re = 0 := by
    have : r * z.re * (2 * z.im) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (by linarith : z.im = 0) hz
  have h4 : 1 + r * (z.im * z.im) = 0 := by
    linear_combination h1 + z.re * h3
  linarith [mul_nonneg hr (mul_self_nonneg z.im)]

private lemma realRootedOrZero_approx (c : ℝ) (m : ℕ) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (y : ℕ → ℝ)
    (n : ℕ) : RealRootedOrZero (approx c m a b y n) := by
  by_cases hc : c = 0
  · left; simp [approx, hc]
  right
  intro z hz
  rw [eval_approx] at hz
  simp only [mul_eq_zero, Finset.prod_eq_zero_iff] at hz
  rcases hz with ((((h | h) | h) | h) | ⟨k, -, h | h⟩)
  · exact absurd (by exact_mod_cast h) hc
  · rw [eq_zero_of_pow_eq_zero h]; simp
  · apply im_eq_zero_of_quadratic (r := a / n) (div_nonneg ha (Nat.cast_nonneg n))
    push_cast; linear_combination eq_zero_of_pow_eq_zero h
  · apply im_eq_zero_of_linear (r := b / n)
    push_cast; linear_combination eq_zero_of_pow_eq_zero h
  · apply im_eq_zero_of_linear (r := -y k)
    push_cast; linear_combination h
  · apply im_eq_zero_of_linear (r := y k / n)
    push_cast; linear_combination eq_zero_of_pow_eq_zero h

end LaguerrePolya

private theorem exists_tendstoLocallyUniformly_canonicalProduct
    (c : ℝ) (m : ℕ) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (y : ℕ → ℝ)
    (hy : Summable fun k => y k ^ 2) :
    ∃ p : ℕ → ℝ[X], (∀ n, RealRootedOrZero (p n)) ∧
      TendstoLocallyUniformly (fun n (z : ℂ) => ((p n).map Complex.ofRealHom).eval z)
        (fun z => (c : ℂ) * z ^ m * Complex.exp (-(a : ℂ) * z ^ 2 + b * z) *
          ∏' k, (1 - (y k : ℂ) * z) * Complex.exp (y k * z)) Filter.atTop := by
  classical
  refine ⟨LaguerrePolya.approx c m a b y,
    fun n => LaguerrePolya.realRootedOrZero_approx c m ha b y n, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine TendstoUniformlyOn.mono ?_ hR
  have hBc : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  set g : ℂ → ℂ := fun z => (c : ℂ) * z ^ m * Complex.exp (-(a : ℂ) * z ^ 2 + b * z) with hg
  set P : ℂ → ℂ := fun z => ∏' k, (1 - (y k : ℂ) * z) * Complex.exp (y k * z) with hPdef
  have hP := LaguerrePolya.tendstoUniformlyOn_canonicalProduct y hy hBc
  have hPc : ContinuousOn P (Metric.closedBall 0 R) :=
    hP.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n => by
      apply Continuous.continuousOn; fun_prop))
  have hgc : Continuous g := by fun_prop
  obtain ⟨A, hA⟩ := hBc.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨A', hA'⟩ := hBc.exists_bound_of_continuousOn hPc
  have h1 := LaguerrePolya.tendstoUniformlyOn_mul_of_bdd
    (F := fun _ => g)
    (Metric.tendstoUniformlyOn_iff.2 fun ε hε => Filter.Eventually.of_forall fun n z _ => by
      simpa using hε) hP ⟨A, hA⟩ ⟨A', hA'⟩
  have h2 := LaguerrePolya.tendstoUniformlyOn_mul_of_bdd h1
    (LaguerrePolya.tendstoUniformlyOn_correction a b y hy R)
    ⟨A * A', fun z hz => by
      rw [norm_mul]
      exact mul_le_mul (hA z hz) (hA' z hz) (norm_nonneg _) ((norm_nonneg _).trans (hA z hz))⟩
    ⟨1, fun z _ => by simp⟩
  refine (h2.congr ?_).congr_right ?_
  · refine Filter.Eventually.of_forall fun n z _ => ?_
    simp only
    rw [LaguerrePolya.eval_approx, hg]
    simp only [Finset.prod_mul_distrib]
    have h1 : Complex.exp (-(a : ℂ) * z ^ 2 + b * z) ≠ 0 := Complex.exp_ne_zero _
    have h2 : ∏ k ∈ Finset.range n, Complex.exp ((y k : ℂ) * z) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun _ _ => Complex.exp_ne_zero _
    rw [← mul_div_assoc, div_eq_iff (mul_ne_zero h1 h2)]
    ring
  · intro z _
    simp [hg]

/-- **Laguerre–Pólya class, product form.** Every function
`c z ^ m e^(-a z² + b z) ∏ₖ (1 - yₖ z) e^(yₖ z)` with `a ≥ 0` and `∑ yₖ² < ∞` is a locally
uniform limit of real-rooted real polynomials. -/
theorem isLaguerrePolya_canonicalProduct (c : ℝ) (m : ℕ) {a : ℝ} (ha : 0 ≤ a) (b : ℝ)
    (y : ℕ → ℝ) (hy : Summable fun k => y k ^ 2) :
    IsLaguerrePolya fun z => (c : ℂ) * z ^ m * Complex.exp (-(a : ℂ) * z ^ 2 + b * z) *
      ∏' k, (1 - (y k : ℂ) * z) * Complex.exp (y k * z) := by
  obtain ⟨p, hp, hlim⟩ := exists_tendstoLocallyUniformly_canonicalProduct c m ha b y hy
  refine ⟨p, fun n => (hp n).imp id fun h => splits_of_forall_aeval_im_eq_zero fun z hz => ?_,
    hlim⟩
  exact h z (by rw [Polynomial.eval_map]; exact hz)

end RealRooted
