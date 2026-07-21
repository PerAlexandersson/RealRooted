import RealRooted.AffineDerivative
import RealRooted.Basic
import RealRooted.MaWang

/-!
# Kurtz challenge entry point

Human statement:
https://www.symmetricfunctions.com/realRooted.htm#kurtzTheorem

Original references: J. I. Hutchinson, "On a remarkable class of entire
functions", Trans. Amer. Math. Soc. 25 (1923), 325--332, and D. C. Kurtz,
"A sufficient condition for all the roots of a polynomial to be real",
Amer. Math. Monthly 99 (1992), 259--263.

This module records the formal coefficient-inequality criterion.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Kurtz

/-- Challenge-facing name for positivity of all coefficients up to the degree
of `p`. -/
abbrev PositiveCoeffsUpToDegree (p : ℝ[X]) : Prop :=
  ∀ i ≤ p.natDegree, 0 < p.coeff i

/-- Compatibility spelling for positivity of all coefficients up to the degree
of `p`. -/
abbrev PositiveCoefficientsUpToDegree (p : ℝ[X]) : Prop :=
  PositiveCoeffsUpToDegree p

/-- Challenge-facing name for the strict Hutchinson--Kurtz coefficient
inequalities. -/
abbrev KurtzStrictInequalities (p : ℝ[X]) : Prop :=
  ∀ i : ℕ, 0 < i → i < p.natDegree →
    4 * p.coeff (i - 1) * p.coeff (i + 1) < (p.coeff i) ^ 2

theorem ne_zero_of_kurtz {p : ℝ[X]}
    (hpos : PositiveCoeffsUpToDegree p) :
    p ≠ 0 :=
  fun h ↦ lt_irrefl 0 ((h ▸ hpos) 0 le_rfl)

theorem hasPosLeadingCoeff_of_kurtz {p : ℝ[X]}
    (hpos : PositiveCoeffsUpToDegree p) :
    HasPosLeadingCoeff p :=
  hpos p.natDegree le_rfl

theorem hasNonnegCoeffs_of_kurtz {p : ℝ[X]}
    (hpos : PositiveCoeffsUpToDegree p) :
    HasNonnegCoeffs p := fun n ↦
  if hn : n ≤ p.natDegree then
    (hpos n hn).le
  else
    (coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn)).symm.le

lemma sum_range_succ_alternating (c : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * c j =
      c 0 - ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * c (j + 1) := by
  have : ∀ j, (-1 : ℝ) ^ (j + 1) * c (j + 1) = -((-1) ^ j * c (j + 1)) := by
    intro j
    rw [pow_succ]
    ring
  rw [Finset.sum_range_succ']
  simp only [this, pow_zero, one_mul, Finset.sum_neg_distrib]
  ring

private lemma alternating_sum_bounds {c : ℕ → ℝ}
    (hnonneg : ∀ j, 0 ≤ c j) (hanti : Antitone c) (n : ℕ) :
    (0 ≤ ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * c j) ∧
    (∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * c j ≤ c 0) := by
  induction n generalizing c with
  | zero => simp [hnonneg 0]
  | succ n ih =>
    rw [sum_range_succ_alternating]
    have : 0 ≤ ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * c (j + 1) ∧
        ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * c (j + 1) ≤ c 1 :=
      ih (fun j ↦ hnonneg (j + 1)) (fun a b hab ↦ hanti (Nat.succ_le_succ hab))
    have : c 1 ≤ c 0 := hanti (Nat.zero_le 1)
    refine ⟨?_, ?_⟩
    · linarith
    · linarith

private lemma alternating_sum_ge {c : ℕ → ℝ}
    (hnonneg : ∀ j, 0 ≤ c j) (hanti : Antitone c) (n : ℕ) :
    c 0 - c 1 ≤ ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * c j := by
  rw [sum_range_succ_alternating]
  have : 0 ≤ ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * c (j + 1) ∧
      ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * c (j + 1) ≤ c 1 :=
    alternating_sum_bounds (fun j ↦ hnonneg (j + 1))
      (fun a b hab ↦ hanti (Nat.succ_le_succ hab)) n
  linarith

private lemma neg_one_pow_mul_neg_one_pow_sub {j i : ℕ} (hij : i < j) :
    (-1 : ℝ) ^ j * (-1 : ℝ) ^ (j - 1 - i) = -((-1) ^ i) := by
  rw [← pow_add]
  have : j + (j - 1 - i) = i + 2 * (j - 1 - i) + 1 := by lia
  rw [this, pow_add, pow_add, pow_mul]
  norm_num

private lemma neg_one_pow_mul_neg_one_pow_add (j i : ℕ) :
    (-1 : ℝ) ^ j * (-1 : ℝ) ^ (j + i) = (-1 : ℝ) ^ i := by
  rw [pow_add, ← mul_assoc, ← mul_pow]
  simp

private lemma consecutive_of_map_range {g : ℕ → ℝ} {n : ℕ}
    {pre : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ}
    (heq : (List.range n).map g = pre ++ r₁ :: r₂ :: rest) :
    ∃ i, i + 1 < n ∧ r₁ = g i ∧ r₂ = g (i + 1) := by
  have : ((List.range n).map g).length = (pre ++ r₁ :: r₂ :: rest).length :=
    congrArg List.length heq
  have : pre.length + rest.length + 2 = n := by
    simp only [List.length_map, List.length_range, List.length_append, List.length_cons] at this
    lia
  refine ⟨pre.length, ?_, ?_, ?_⟩
  · lia
  · have : ((List.range n).map g)[pre.length]? = some r₁ := by simp_all
    grind
  · have : ((List.range n).map g)[pre.length + 1]? = some r₂ := by simp_all
    grind

lemma antitone_of_succ_lt {f : ℕ → ℝ} {n j : ℕ}
    (hstep : ∀ i, j ≤ i → i < n → f (i + 1) < f i)
    (s t : ℕ) (hjs : j ≤ s) (hst : s ≤ t) (htn : t ≤ n) : f t ≤ f s := by
  induction t with
  | zero =>
    have : s = 0 := by lia
    rw [this]
  | succ t iht =>
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · have hstep_t : f (t + 1) < f t := hstep t (by lia) (by lia)
      have : f t ≤ f s := iht (by lia) (by lia)
      exact hstep_t.le.trans this
    · have : s = t + 1 := by lia
      rw [this]

lemma monotone_of_succ_gt {f : ℕ → ℝ} {j : ℕ}
    (hstep : ∀ i, 1 ≤ i → i ≤ j → f (i - 1) < f i)
    (s t : ℕ) (hst : s ≤ t) (htj : t ≤ j) : f s ≤ f t := by
  induction t with
  | zero =>
    have : s = 0 := by lia
    rw [this]
  | succ t iht =>
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · have hstep_t : f t < f (t + 1) := hstep (t + 1) (by lia) (by lia)
      have : f s ≤ f t := iht (by lia) (by lia)
      exact this.trans hstep_t.le
    · have : s = t + 1 := by lia
      rw [this]

lemma antitone_capped_of_antitone {m : ℕ → ℝ} {n j : ℕ} (hjn : j ≤ n)
    (hdec : ∀ s t, j ≤ s → s ≤ t → t ≤ n → m t ≤ m s) :
    Antitone (fun i ↦ m (min (j + i) n)) := by
  intro a b hab
  apply hdec
  · simp only [Nat.min_def]
    split <;> lia
  · simp only [Nat.min_def]
    split <;> split <;> lia
  · simp only [Nat.min_def]
    split <;> lia

lemma antitone_rev_of_monotone {m : ℕ → ℝ} {j : ℕ}
    (hincr : ∀ s t, s ≤ t → t ≤ j → m s ≤ m t) :
    Antitone (fun i ↦ m (j - 1 - i)) := by
  intro a b hab
  apply hincr
  · lia
  · lia

lemma alternating_sum_reflect (m : ℕ → ℝ) (j : ℕ) :
    (-1 : ℝ) ^ j * ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * m i =
    - ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * m (j - 1 - i) := by
  rw [Finset.mul_sum,
    ← Finset.sum_range_reflect (fun i ↦ (-1 : ℝ) ^ j * ((-1) ^ i * m i)) j,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_assoc, neg_one_pow_mul_neg_one_pow_sub (Finset.mem_range.mp hi), neg_mul]

private lemma sign_alternating_of_unimodal {m : ℕ → ℝ} {n j : ℕ}
    (hj₀ : 1 ≤ j) (hjn : j ≤ n)
    (hnonneg : ∀ i, 0 ≤ m i)
    (hup : ∀ i, 1 ≤ i → i ≤ j → m (i - 1) < m i)
    (hdown : ∀ i, j ≤ i → i < n → m (i + 1) < m i)
    (hkey : m (j - 1) + (if j < n then m (j + 1) else 0) < m j) :
    0 < (-1 : ℝ) ^ j * ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * m i := by
  have hdec (s t : ℕ) (hjs : j ≤ s) (hst : s ≤ t) (htn : t ≤ n) : m t ≤ m s :=
    antitone_of_succ_lt hdown s t hjs hst htn
  have hincr (s t : ℕ) (hst : s ≤ t) (htj : t ≤ j) : m s ≤ m t :=
    monotone_of_succ_gt hup s t hst htj
  have : n + 1 = j + (n + 1 - j) := by lia
  have : ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * m i
      = (∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * m i)
        + ∑ i ∈ Finset.range (n + 1 - j), (-1 : ℝ) ^ (j + i) * m (j + i) := by
    conv_lhs => rw [this]
    rw [Finset.sum_range_add (fun i => (-1 : ℝ) ^ i * m i) j (n + 1 - j)]
  rw [this, mul_add]
  set sa := ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * m i with hsa
  set sb := ∑ i ∈ Finset.range (n + 1 - j), (-1 : ℝ) ^ (j + i) * m (j + i) with hsb
  set cu : ℕ → ℝ := fun i ↦ m (min (j + i) n) with hcu
  have hcu_agree (i : ℕ) (hi : i < n + 1 - j) : cu i = m (j + i) :=
    congrArg m (min_eq_left (by lia))
  have hcu_anti : Antitone cu := antitone_capped_of_antitone hjn hdec
  have hsb_val : (-1 : ℝ) ^ j * sb
      = ∑ i ∈ Finset.range (n + 1 - j), (-1 : ℝ) ^ i * cu i := by
    rw [hsb, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hcu_agree i (Finset.mem_range.mp hi), ← mul_assoc, neg_one_pow_mul_neg_one_pow_add]
  have : m j - (if j < n then m (j + 1) else 0) ≤ (-1 : ℝ) ^ j * sb := by
    rw [hsb_val]
    by_cases hjlt : j < n
    · have : n + 1 - j = (n - j) + 1 := by lia
      rw [this, if_pos hjlt]
      have : cu 0 - cu 1 ≤ ∑ i ∈ Finset.range (n - j + 1), (-1 : ℝ) ^ i * cu i :=
        alternating_sum_ge (fun i ↦ hnonneg (min (j + i) n)) hcu_anti (n - j)
      rw [hcu] at this
      simp only [add_zero, min_eq_left hjn, min_eq_left (Nat.succ_le_of_lt hjlt)] at this
      dsimp only [cu]
      exact this
    · simp [Nat.le_antisymm hjn (not_lt.mp hjlt), hcu]
  set cd : ℕ → ℝ := fun i ↦ m (j - 1 - i) with hcd
  have hcd_anti : Antitone cd := antitone_rev_of_monotone hincr
  have hsa_val : (-1 : ℝ) ^ j * sa
      = - ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * cd i := by
    rw [hsa, alternating_sum_reflect m j]
  have : -m (j - 1) ≤ (-1 : ℝ) ^ j * sa := by
    rw [hsa_val, ← Nat.sub_add_cancel hj₀]
    have : ∑ i ∈ Finset.range (j - 1 + 1), (-1 : ℝ) ^ i * cd i ≤ cd 0 :=
      (alternating_sum_bounds (fun i ↦ hnonneg _) hcd_anti ((j - 1) + 1)).2
    dsimp [cd] at this ⊢
    linarith
  linarith

lemma lt_sqrt_mul_and_lt_of_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    x < Real.sqrt (x * y) ∧ Real.sqrt (x * y) < y := by
  have hxy_pos : 0 < x * y := mul_pos hx (hx.trans hxy)
  have hlt_left : x < Real.sqrt (x * y) := by
    rw [Real.lt_sqrt hx.le]
    nlinarith
  have hlt_right : Real.sqrt (x * y) < y := by
    rw [Real.sqrt_lt hxy_pos.le (hx.trans hxy).le]
    nlinarith
  exact ⟨hlt_left, hlt_right⟩

lemma monotone_of_lt_succ {f : ℕ → ℝ} {n : ℕ}
    (hstep : ∀ k, 1 ≤ k → k + 1 ≤ n → f k < f (k + 1))
    (s t : ℕ) (hs : 1 ≤ s) (hst : s ≤ t) (htn : t ≤ n) : f s ≤ f t := by
  induction t with
  | zero => lia
  | succ t iht =>
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · have : f s ≤ f t := iht (by lia) (by lia)
      have : f t < f (t + 1) := hstep t (by lia) htn
      linarith
    · have : s = t + 1 := by lia
      rw [this]

lemma strictMono_of_lt_succ {f : ℕ → ℝ} {n : ℕ}
    (hstep : ∀ k, 1 ≤ k → k < n → f k < f (k + 1))
    (s t : ℕ) (hs : 1 ≤ s) (hst : s < t) (htn : t ≤ n) : f s < f t := by
  induction t, hst using Nat.le_induction with
  | base => exact hstep s hs (by lia)
  | succ t' hst' ih =>
    have : f t' < f (t' + 1) := hstep t' (by lia) (by lia)
    linarith [ih (by lia)]

lemma add_mul_sq_sqrt_div_lt_mul {u v w : ℝ} (hu : 0 < u) (hw : 0 < w) (hv : 0 < v)
    (h : 4 * u * w < v ^ 2) :
    u + w * (Real.sqrt (u / w)) ^ 2 < v * Real.sqrt (u / w) := by
  have hsq : (Real.sqrt (u / w)) ^ 2 = u / w := Real.sq_sqrt (div_pos hu hw).le
  have : (2 * u) ^ 2 < (v * Real.sqrt (u / w)) ^ 2 := by
    simp only [mul_pow, hsq]
    rw [← mul_div_assoc, lt_div_iff₀ hw]
    nlinarith
  have : 2 * u < v * Real.sqrt (u / w) := (sq_lt_sq₀ (by linarith) (by positivity)).mp this
  have : u + w * (Real.sqrt (u / w)) ^ 2 = 2 * u := by
    rw [hsq, mul_comm, div_mul_cancel₀ u hw.ne']
    ring
  linarith

lemma add_mul_self_lt_mul_self_of_add_mul_sq_lt {u v w x : ℝ} {k : ℕ} (hk₁ : 1 ≤ k)
    (hx : 0 < x) (hlt : u + w * x ^ 2 < v * x) :
    u * x ^ (k - 1) + w * x ^ (k + 1) < v * x ^ k := by
  have hxk_pred : 0 < x ^ (k - 1) := pow_pos hx _
  have hlhs : u * x ^ (k - 1) + w * x ^ (k + 1) = (u + w * x ^ 2) * x ^ (k - 1) := by
    have : x ^ (k + 1) = x ^ 2 * x ^ (k - 1) := by
      rw [show k + 1 = 2 + (k - 1) by lia, pow_add]
    rw [this]
    ring
  have hrhs : v * x ^ k = (v * x) * x ^ (k - 1) := by
    rw [show x ^ k = x ^ (k - 1) * x by rw [← pow_succ, Nat.sub_add_cancel hk₁]]
    ring
  rw [hlhs, hrhs]
  nlinarith [hlt, hxk_pred]

lemma div_lt_div_of_mul_lt_sq {u v w : ℝ} (hv : 0 < v) (hw : 0 < w) (h : u * w < v ^ 2) :
    u / v < v / w := by
  rw [div_lt_div_iff₀ hv hw, ← pow_two]
  exact h

lemma mul_neg_of_neg_mul_pos_of_mul_pos {a x y : ℝ} (ha : a * a = 1) (hx : 0 < -a * x)
    (hy : 0 < a * y) :
    x * y < 0 := by
  have hax : a * x < 0 := by linarith
  have heq : (a * x) * (a * y) = x * y := by
    rw [show (a * x) * (a * y) = (a * a) * (x * y) by ring, ha, one_mul]
  rw [← heq]
  nlinarith

lemma eval_neg_eq_sum_range (p : ℝ[X]) (x : ℝ) :
    p.eval (-x) =
      ∑ i ∈ Finset.range (p.natDegree + 1), (-1 : ℝ) ^ i * (p.coeff i * x ^ i) := by
  rw [Polynomial.eval_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [neg_pow]
  ring

lemma sign_eval_neg_of_ratio_bounds {p : ℝ[X]} {x : ℝ} {k : ℕ}
    (hk₁ : 1 ≤ k) (hkn : k ≤ p.natDegree) (hx : 0 < x)
    (hnonneg : HasNonnegCoeffs p)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hratio_lt_x : ∀ i, 1 ≤ i → i ≤ k → p.coeff (i - 1) / p.coeff i < x)
    (hx_lt_ratio : ∀ i, k ≤ i → i < p.natDegree → x < p.coeff i / p.coeff (i + 1))
    (hineq : k < p.natDegree → 4 * p.coeff (k - 1) * p.coeff (k + 1) < (p.coeff k) ^ 2)
    (hx_eq : k < p.natDegree → x = Real.sqrt (p.coeff (k - 1) / p.coeff (k + 1))) :
    0 < (-1 : ℝ) ^ k * p.eval (-x) := by
  set n := p.natDegree with hn
  set a : ℕ → ℝ := fun i => p.coeff i with ha
  set m : ℕ → ℝ := fun i => a i * x ^ i with hm
  have hapos {i : ℕ} (hi : i ≤ n) : 0 < a i := hpos i hi
  have : p.eval (-x) = ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * m i :=
    eval_neg_eq_sum_range p x
  rw [this]
  have hm_nonneg (i : ℕ) : 0 ≤ m i := mul_nonneg (hnonneg i) (pow_nonneg hx.le i)
  have hup_ineq (i : ℕ) (hi₁ : 1 ≤ i) (hik : i ≤ k) : a (i - 1) < a i * x := by
    rw [mul_comm, ← div_lt_iff₀ (hapos (hik.trans hkn))]
    exact hratio_lt_x i hi₁ hik
  have hup (i : ℕ) (hi₁ : 1 ≤ i) (hik : i ≤ k) : m (i - 1) < m i := by
    simp only [hm]
    rw [show x ^ i = x ^ (i - 1) * x by rw [← pow_succ, Nat.sub_add_cancel hi₁]]
    nlinarith [hup_ineq i hi₁ hik, pow_pos hx (i - 1)]
  have hdown_ineq (i : ℕ) (hki : k ≤ i) (hin : i < n) : a (i + 1) * x < a i := by
    rw [mul_comm, ← lt_div_iff₀ (hapos hin)]
    exact hx_lt_ratio i hki hin
  have hdown (i : ℕ) (hki : k ≤ i) (hin : i < n) : m (i + 1) < m i := by
    simp only [hm, pow_succ]
    nlinarith [hdown_ineq i hki hin, pow_pos hx i]
  have hkey : m (k - 1) + (if k < n then m (k + 1) else 0) < m k := by
    simp only [hm]
    have hak : 0 < a k := hapos hkn
    have hak_pred : 0 < a (k - 1) := hapos ((Nat.sub_le k 1).trans hkn)
    by_cases hlt : k < n
    · simp only [hlt, if_true]
      have hak_succ : 0 < a (k + 1) := hapos hlt
      have : a (k - 1) + a (k + 1) * x ^ 2 < a k * x := by
        rw [hx_eq hlt]
        exact add_mul_sq_sqrt_div_lt_mul hak_pred hak_succ hak (hineq hlt)
      exact add_mul_self_lt_mul_self_of_add_mul_sq_lt hk₁ hx this
    · grind
  exact sign_alternating_of_unimodal hk₁ hkn hm_nonneg hup hdown hkey

lemma ratio_lt_of_log_concave {a : ℕ → ℝ} {n : ℕ} (hpos : ∀ i ≤ n, 0 < a i)
    (hlogconc : ∀ i, 1 ≤ i → i < n → a (i - 1) * a (i + 1) < a i ^ 2)
    (i : ℕ) (hi₁ : 1 ≤ i) (hin : i + 1 ≤ n) :
    a (i - 1) / a i < a i / a (i + 1) :=
  div_lt_div_of_mul_lt_sq (hpos i (by lia)) (hpos (i + 1) hin) (hlogconc i hi₁ (by lia))

lemma ratio_monotone_of_log_concave {a : ℕ → ℝ} {n : ℕ} (hpos : ∀ i ≤ n, 0 < a i)
    (hlogconc : ∀ i, 1 ≤ i → i < n → a (i - 1) * a (i + 1) < a i ^ 2)
    (s t : ℕ) (hs : 1 ≤ s) (hst : s ≤ t) (htn : t ≤ n) :
    a (s - 1) / a s ≤ a (t - 1) / a t :=
  monotone_of_lt_succ
    (fun k hk₁ hkn ↦ ratio_lt_of_log_concave hpos hlogconc k hk₁ hkn) s t hs hst htn

lemma sqrt_ratio_between {a : ℕ → ℝ} {n : ℕ} (hpos : ∀ i ≤ n, 0 < a i)
    (hlogconc : ∀ i, 1 ≤ i → i < n → a (i - 1) * a (i + 1) < a i ^ 2)
    (k : ℕ) (hk₁ : 1 ≤ k) (hkn : k < n) :
    a (k - 1) / a k < Real.sqrt (a (k - 1) / a (k + 1)) ∧
    Real.sqrt (a (k - 1) / a (k + 1)) < a k / a (k + 1) := by
  have hk : k ≤ n := hkn.le
  have hk_pred : k - 1 ≤ n := (Nat.sub_le k 1).trans hk
  have hr₁ : 0 < a (k - 1) / a k := div_pos (hpos _ hk_pred) (hpos _ hk)
  have hr₂ : a (k - 1) / a k < a k / a (k + 1) :=
    ratio_lt_of_log_concave hpos hlogconc k hk₁ hkn
  have : (a (k - 1) / a k) * (a k / a (k + 1)) = a (k - 1) / a (k + 1) := by
    rw [div_mul_div_cancel₀ (hpos k hk).ne']
  rw [← this]
  exact lt_sqrt_mul_and_lt_of_lt hr₁ hr₂

theorem coefficient_criterion_card_roots {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : PositiveCoeffsUpToDegree p)
    (hineq : KurtzStrictInequalities p) :
    p.roots.card = p.natDegree := by
  classical
  set n := p.natDegree with hn
  set a : ℕ → ℝ := fun i => p.coeff i with ha
  have hpne : p ≠ 0 := ne_zero_of_kurtz hpos
  have hapos {i : ℕ} (hi : i ≤ n) : 0 < a i := hpos i hi
  have hlogconc (i : ℕ) (hi₁ : 1 ≤ i) (hin : i < n) : a (i - 1) * a (i + 1) < a i ^ 2 := by
    nlinarith [hineq i hi₁ hin, hapos ((Nat.sub_le i 1).trans hin.le), hapos hin]
  have hrmono (s t : ℕ) (hs : 1 ≤ s) (hst : s ≤ t) (htn : t ≤ n) :
      a (s - 1) / a s ≤ a (t - 1) / a t :=
    ratio_monotone_of_log_concave (fun i hi ↦ hapos hi) hlogconc s t hs hst htn
  set r : ℕ → ℝ := fun i ↦ a (i - 1) / a i with hr
  set xpt : ℕ → ℝ := fun k ↦ if k < n then Real.sqrt (a (k - 1) / a (k + 1))
      else r n + 1 with hxpt
  have hrpos (i : ℕ) (hi₁ : 1 ≤ i) (hin : i ≤ n) : 0 < r i :=
    div_pos (hapos ((Nat.sub_le i 1).trans hin)) (hapos hin)
  have hxpt_between (k : ℕ) (hk₁ : 1 ≤ k) (hkn : k < n) :
      r k < xpt k ∧ xpt k < r (k + 1) := by
    have heq : xpt k = Real.sqrt (a (k - 1) / a (k + 1)) := by
      simp only [hxpt, hkn, if_true]
    rw [heq]
    exact sqrt_ratio_between (fun i hi ↦ hapos hi) hlogconc k hk₁ hkn
  have hxpt_pos (k : ℕ) (hk₁ : 1 ≤ k) (hkn : k ≤ n) : 0 < xpt k := by grind
  have hnonneg : HasNonnegCoeffs p := hasNonnegCoeffs_of_kurtz hpos
  have hsign (k : ℕ) (hk₁ : 1 ≤ k) (hkn : k ≤ n) :
      0 < (-1 : ℝ) ^ k * p.eval (- xpt k) := by
    apply sign_eval_neg_of_ratio_bounds hk₁ hkn (hxpt_pos k hk₁ hkn) hnonneg hpos
    · intro i hi₁ hik
      grind
    · intro i hki hin
      change xpt k < r (i + 1)
      linarith [(hxpt_between k hk₁ (hki.trans_lt hin)).2,
        hrmono (k + 1) (i + 1) k.succ_pos (Nat.succ_le_succ hki) hin]
    · intro hlt
      exact hineq k hk₁ hlt
    · intro hlt
      unfold xpt
      rw [if_pos hlt]
  have hxpt_lt_succ (k : ℕ) (hk₁ : 1 ≤ k) (hkn : k < n) : xpt k < xpt (k + 1) := by grind
  set g : ℕ → ℝ := fun i ↦ - xpt (n - i) with hg
  set pts : List ℝ := (List.range n).map g with hpts
  have hg_anti (i j : ℕ) (hij : i < j) (hjn : j < n) : g i < g j := by
    simp only [hg]
    linarith [strictMono_of_lt_succ hxpt_lt_succ (n - j) (n - i) (by lia) (by lia) (by lia)]
  have hpts_sorted : pts.Pairwise (· ≤ ·) := by
    rw [hpts, List.pairwise_map, List.pairwise_iff_getElem]
    grind
  have hsign_pts (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ}
      (heq : pts = pre ++ r₁ :: r₂ :: rest) : p.eval r₁ * p.eval r₂ < 0 := by
    obtain ⟨i, hi, hr₁, hr₂⟩ := consecutive_of_map_range (hpts ▸ heq)
    set m := n - i - 1
    have hnim : n - i = m + 1 := by lia
    have hnii : n - (i + 1) = m := by lia
    have ⟨hm₁, hmn⟩ : 1 ≤ m ∧ m + 1 ≤ n := by lia
    have hsign_succ : 0 < - ((-1 : ℝ) ^ m) * p.eval (- xpt (m + 1)) := by
      have : 0 < (-1 : ℝ) ^ (m + 1) * p.eval (- xpt (m + 1)) :=
        hsign (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hmn
      rwa [pow_succ, mul_neg, mul_one] at this
    have hsign_curr : 0 < (-1 : ℝ) ^ m * p.eval (- xpt m) :=
      hsign m hm₁ ((Nat.le_succ m).trans hmn)
    rw [hr₁, hr₂]
    simp only [hg, hnim, hnii]
    have : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by simp [← mul_pow]
    exact mul_neg_of_neg_mul_pos_of_mul_pos this hsign_succ hsign_curr
  obtain ⟨us, hus_len, -, hus_roots, hus_pw⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_signs
      (F := p) (rs := pts) hpts_sorted hsign_pts
  have : pts.length = n := by simp [*]
  have : us.length = n - 1 := by simp [*]
  have hus_nodup : us.Nodup := hus_pw.imp (fun h ↦ h.ne)
  set s : Multiset ℝ := (us : Multiset ℝ) with hs
  have hs_card : s.card = n - 1 := by simp [*]
  have hs_le : s ≤ p.roots := by
    rw [hs, Multiset.le_iff_subset (Multiset.coe_nodup.mpr hus_nodup)]
    intro x hx
    rw [Multiset.mem_coe] at hx
    exact (mem_roots hpne).mpr (hus_roots x hx)
  have : s.card + 1 = p.natDegree := by
    have : 1 ≤ n := (Nat.le_succ 1).trans (hn ▸ hdeg)
    rw [hs_card, Nat.sub_add_cancel this, hn]
  exact card_roots_of_splits (roots_card_of_sub_pred hpne hs_le this)

/-- Kurtz's sufficient condition: positive coefficients and the strict
Hutchinson--Kurtz log-concavity inequalities imply real-rootedness. -/
theorem coefficient_criterion {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : PositiveCoeffsUpToDegree p)
    (hineq : KurtzStrictInequalities p) :
    p.Splits :=
  splits_of_card_roots (coefficient_criterion_card_roots hdeg hpos hineq)

/-- Compatibility wrapper for the original challenge-facing theorem name. -/
theorem coefficientCriterion {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : PositiveCoefficientsUpToDegree p)
    (hineq : KurtzStrictInequalities p) :
    p.Splits :=
  coefficient_criterion hdeg hpos hineq

end Kurtz
end Challenges
end RealRooted
