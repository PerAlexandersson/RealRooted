import Mathlib.Algebra.Polynomial.Splits
import RealRooted.Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Multiset.Fintype

/-!
# Darroch's mean–mode theorem

Let `p : ℝ[X]` be a nonzero real-rooted polynomial with nonnegative coefficients and let
`μ = p'(1) / p(1)` be the mean of the coefficient distribution `k ↦ p.coeff k / p(1)`.
Darroch (1964) proved that every mode `k` of the coefficient sequence satisfies `|k - μ| < 1`.

The proof writes `p` up to a positive constant as `∏ i, (1 - w i + w i X)` with `w i ∈ [0, 1]`
and uses the identities

* `A' - μ A = (1 - X) ∑ i, w i ^ 2 A⁽ⁱ⁾`,
* `X (n A - X A') - (n - μ) A = (X - 1) ∑ i, (1 - w i) ^ 2 A⁽ⁱ⁾`,

where `A⁽ⁱ⁾` omits the `i`-th factor, together with strong induction on the set of factors.

## References

* J. N. Darroch, *On the distribution of the number of successes in independent trials*,
  Ann. Math. Statist. 35 (1964), 1317–1321.
-/

open Finset

namespace Polynomial

variable {ι : Type*} [DecidableEq ι]

/-- The generating polynomial `∏ i ∈ s, (1 - w i + w i X)` of a sum of independent Bernoulli
variables with success probabilities `w i`. -/
private noncomputable def bernPoly (w : ι → ℝ) (s : Finset ι) : ℝ[X] :=
  ∏ i ∈ s, (C (1 - w i) + C (w i) * X)

private lemma coeff_bernFactor_mul_zero (a : ℝ) (q : ℝ[X]) :
    ((C (1 - a) + C a * X) * q).coeff 0 = (1 - a) * q.coeff 0 := by
  simp only [add_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul_zero, mul_zero, add_zero]

private lemma coeff_bernFactor_mul_succ (a : ℝ) (q : ℝ[X]) (k : ℕ) :
    ((C (1 - a) + C a * X) * q).coeff (k + 1) = (1 - a) * q.coeff (k + 1) + a * q.coeff k := by
  simp only [add_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul]

private lemma bernPoly_erase (w : ι → ℝ) {s : Finset ι} {i : ι} (hi : i ∈ s) :
    bernPoly w s = (C (1 - w i) + C (w i) * X) * bernPoly w (s.erase i) :=
  (mul_prod_erase s (fun j => C (1 - w j) + C (w j) * X) hi).symm

omit [DecidableEq ι] in
private lemma coeff_bernPoly_nonneg (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1) (k : ℕ) : 0 ≤ (bernPoly w s).coeff k := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rw [bernPoly, prod_empty, coeff_one]
    split_ifs <;> norm_num
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1 := fun i hi => hw i (mem_insert_of_mem hi)
    obtain ⟨h0, h1⟩ := hw a (mem_insert_self a s)
    have hp : bernPoly w (insert a s) = (C (1 - w a) + C (w a) * X) * bernPoly w s :=
      prod_insert ha
    rw [hp]
    cases k with
    | zero =>
      rw [coeff_bernFactor_mul_zero]
      exact mul_nonneg (by linarith) (ih hs 0)
    | succ k =>
      rw [coeff_bernFactor_mul_succ]
      exact add_nonneg (mul_nonneg (by linarith) (ih hs _)) (mul_nonneg h0 (ih hs k))

omit [DecidableEq ι] in
private lemma natDegree_bernPoly_le (w : ι → ℝ) (s : Finset ι) :
    (bernPoly w s).natDegree ≤ s.card := by
  refine (natDegree_prod_le _ _).trans ?_
  refine (sum_le_sum (g := fun _ => 1) fun i _ => ?_).trans (by simp)
  exact (natDegree_add_le _ _).trans
    (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))

omit [DecidableEq ι] in
private lemma eval_one_bernPoly (w : ι → ℝ) (s : Finset ι) : (bernPoly w s).eval 1 = 1 := by
  simp [bernPoly, eval_prod]

/-- The first key identity: `A' - μ A = (1 - X) ∑ w_i² A^{(i)}`. -/
private lemma derivative_bernPoly_sub (w : ι → ℝ) (s : Finset ι) :
    derivative (bernPoly w s) - C (∑ i ∈ s, w i) * bernPoly w s =
      (1 - X) * ∑ i ∈ s, C (w i ^ 2) * bernPoly w (s.erase i) := by
  rw [bernPoly, derivative_prod_finset, map_sum, sum_mul, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [← mul_prod_erase s _ hi]
  rw [derivative_add, derivative_C, derivative_C_mul_X, zero_add]
  simp only [bernPoly, map_sub, map_one, map_pow]
  ring

/-- The companion identity: `n A - X A' = ∑ (1 - w_i) A^{(i)}`. -/
private lemma card_mul_bernPoly_sub (w : ι → ℝ) (s : Finset ι) :
    C (s.card : ℝ) * bernPoly w s - X * derivative (bernPoly w s) =
      ∑ i ∈ s, C (1 - w i) * bernPoly w (s.erase i) := by
  have hc : C (s.card : ℝ) * bernPoly w s = ∑ i ∈ s, bernPoly w s := by
    rw [sum_const, nsmul_eq_mul, map_natCast]
  rw [hc, bernPoly, derivative_prod_finset, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [← mul_prod_erase s _ hi]
  rw [derivative_add, derivative_C, derivative_C_mul_X, zero_add]
  simp only [bernPoly, map_sub, map_one]
  ring

/-- Coefficient form of `derivative_bernPoly_sub`. -/
private lemma coeff_derivative_bernPoly_sub (w : ι → ℝ) (s : Finset ι) (k : ℕ) :
    (bernPoly w s).coeff (k + 1) * (k + 1) - (∑ i ∈ s, w i) * (bernPoly w s).coeff k =
      ∑ i ∈ s, w i ^ 2 * ((1 - X) * bernPoly w (s.erase i)).coeff k := by
  have h := congrArg (fun q => q.coeff k) (derivative_bernPoly_sub w s)
  simp only [coeff_sub, coeff_derivative, coeff_C_mul, mul_sum, finsetSum_coeff] at h
  rw [h]
  exact sum_congr rfl fun i _ => by rw [mul_left_comm, coeff_C_mul]

/-- Coefficient form of `card_mul_bernPoly_sub`. -/
private lemma coeff_card_mul_bernPoly_sub (w : ι → ℝ) (s : Finset ι) (k : ℕ) :
    ((s.card : ℝ) - k) * (bernPoly w s).coeff k =
      ∑ i ∈ s, (1 - w i) * (bernPoly w (s.erase i)).coeff k := by
  have h := congrArg (fun q => q.coeff k) (card_mul_bernPoly_sub w s)
  simp only [coeff_sub, coeff_C_mul, finsetSum_coeff] at h
  rw [← h]
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

omit [DecidableEq ι] in
/-- If the mean is at least `k + 1` and the `k`-th coefficient is positive, then the
coefficients strictly increase from `k` to `k + 1`. -/
private lemma coeff_lt_coeff_succ_bernPoly (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1) (k : ℕ) (hμ : (k : ℝ) + 1 ≤ ∑ i ∈ s, w i)
    (hk : 0 < (bernPoly w s).coeff k) :
    (bernPoly w s).coeff k < (bernPoly w s).coeff (k + 1) := by
  classical
  induction s using Finset.strongInduction generalizing k with
  | H s ih =>
  have hD : ∀ i ∈ s, 0 < w i → 0 < ((1 - X) * bernPoly w (s.erase i)).coeff k := by
    intro i hi hwi
    have hw' : ∀ j ∈ s.erase i, 0 ≤ w j ∧ w j ≤ 1 := fun j hj => hw j (mem_of_mem_erase hj)
    have hB := coeff_bernPoly_nonneg w (s.erase i) hw'
    have hA := hk
    rw [bernPoly_erase w hi] at hA
    obtain ⟨h0, h1⟩ := hw i hi
    cases k with
    | zero =>
      rw [coeff_one_sub_X_mul_zero]
      rw [coeff_bernFactor_mul_zero] at hA
      nlinarith [hB 0]
    | succ j =>
      rw [coeff_one_sub_X_mul_succ]
      rw [coeff_bernFactor_mul_succ] at hA
      rcases (hB j).eq_or_lt with hj | hj
      · nlinarith [hB (j + 1)]
      · have hμ' : (j : ℝ) + 1 ≤ ∑ l ∈ s.erase i, w l := by
          rw [sum_erase_eq_sub hi]
          push_cast at hμ
          linarith
        linarith [ih (s.erase i) (erase_ssubset hi) hw' j hμ' hj]
  have hex : ∃ i ∈ s, 0 < w i := by
    by_contra hne
    push Not at hne
    have := sum_nonpos hne
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hS : 0 < ∑ i ∈ s, w i ^ 2 * ((1 - X) * bernPoly w (s.erase i)).coeff k := by
    refine sum_pos' (fun i hi => ?_) ?_
    · rcases (hw i hi).1.eq_or_lt with h | h
      · rw [← h]
        simp
      · exact (mul_pos (pow_pos h 2) (hD i hi h)).le
    · obtain ⟨i, hi, h⟩ := hex
      exact ⟨i, hi, mul_pos (pow_pos h 2) (hD i hi h)⟩
  rw [← coeff_derivative_bernPoly_sub] at hS
  nlinarith [mul_le_mul_of_nonneg_right hμ hk.le]

omit [DecidableEq ι] in
/-- If the mean is at most `k` and the `(k + 1)`-st coefficient is positive, then the
coefficients strictly decrease from `k` to `k + 1`. -/
private lemma coeff_succ_lt_coeff_bernPoly (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1) (k : ℕ) (hμ : ∑ i ∈ s, w i ≤ k)
    (hk : 0 < (bernPoly w s).coeff (k + 1)) :
    (bernPoly w s).coeff (k + 1) < (bernPoly w s).coeff k := by
  classical
  induction s using Finset.strongInduction generalizing k with
  | H s ih =>
  have hn : k + 1 ≤ s.card := by
    by_contra hc
    push Not at hc
    rw [coeff_eq_zero_of_natDegree_lt ((natDegree_bernPoly_le w s).trans_lt hc)] at hk
    exact lt_irrefl _ hk
  have hE : ∀ i ∈ s, 0 < 1 - w i →
      0 < (bernPoly w (s.erase i)).coeff k - (bernPoly w (s.erase i)).coeff (k + 1) := by
    intro i hi hwi
    have hw' : ∀ j ∈ s.erase i, 0 ≤ w j ∧ w j ≤ 1 := fun j hj => hw j (mem_of_mem_erase hj)
    have hB := coeff_bernPoly_nonneg w (s.erase i) hw'
    have hA := hk
    rw [bernPoly_erase w hi, coeff_bernFactor_mul_succ] at hA
    obtain ⟨h0, h1⟩ := hw i hi
    rcases (hB (k + 1)).eq_or_lt with hj | hj
    · nlinarith [hB k]
    · have hμ' : ∑ l ∈ s.erase i, w l ≤ k := by
        rw [sum_erase_eq_sub hi]
        linarith
      linarith [ih (s.erase i) (erase_ssubset hi) hw' k hμ' hj]
  have hex : ∃ i ∈ s, 0 < 1 - w i := by
    by_contra hne
    push Not at hne
    have h1 : (s.card : ℝ) ≤ ∑ i ∈ s, w i := by
      rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact sum_le_sum fun i hi => by linarith [hne i hi]
    have h2 : ((k + 1 : ℕ) : ℝ) ≤ s.card := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hS : 0 < ∑ i ∈ s, (1 - w i) ^ 2 *
      ((bernPoly w (s.erase i)).coeff k - (bernPoly w (s.erase i)).coeff (k + 1)) := by
    refine sum_pos' (fun i hi => ?_) ?_
    · rcases (sub_nonneg.2 (hw i hi).2).eq_or_lt with h | h
      · rw [← h]
        simp
      · exact (mul_pos (pow_pos h 2) (hE i hi h)).le
    · obtain ⟨i, hi, h⟩ := hex
      exact ⟨i, hi, mul_pos (pow_pos h 2) (hE i hi h)⟩
  have h2 := coeff_card_mul_bernPoly_sub w s k
  have h3 : ((s.card : ℝ) - ∑ i ∈ s, w i) * (bernPoly w s).coeff (k + 1) =
      ∑ i ∈ s, (1 - w i) * ((1 - w i) * (bernPoly w (s.erase i)).coeff (k + 1) +
        w i * (bernPoly w (s.erase i)).coeff k) := by
    have hc : (s.card : ℝ) - ∑ i ∈ s, w i = ∑ i ∈ s, (1 - w i) := by
      simp [sum_sub_distrib]
    rw [hc, sum_mul]
    exact sum_congr rfl fun i hi => by rw [bernPoly_erase w hi, coeff_bernFactor_mul_succ]
  have h4 : ((s.card : ℝ) - k) * (bernPoly w s).coeff k -
      ((s.card : ℝ) - ∑ i ∈ s, w i) * (bernPoly w s).coeff (k + 1) =
      ∑ i ∈ s, (1 - w i) ^ 2 *
        ((bernPoly w (s.erase i)).coeff k - (bernPoly w (s.erase i)).coeff (k + 1)) := by
    rw [h2, h3, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  have hn' : ((k + 1 : ℕ) : ℝ) ≤ s.card := by exact_mod_cast hn
  push_cast at hn'
  nlinarith [mul_le_mul_of_nonneg_right hμ hk.le]

private lemma X_sub_C_eq_C_mul_bernFactor {a : ℝ} (ha : a ≤ 0) :
    X - C a = C (1 - a) * (C (1 - (1 - a)⁻¹) + C (1 - a)⁻¹ * X) := by
  have h : (1 - a) ≠ 0 := by linarith
  rw [mul_add, ← mul_assoc, ← C_mul, ← C_mul, mul_sub, mul_one, mul_inv_cancel₀ h]
  simp only [map_sub, map_one, one_mul]
  ring

/-- **Darroch's mean–mode theorem** (1964). Let `p` be a nonzero real-rooted polynomial with
nonnegative coefficients and let `μ = p'(1) / p(1)` be the mean of the coefficient
distribution. Then every mode `k` of the coefficient sequence satisfies `|k - μ| < 1`;
equivalently, `k = ⌊μ⌋` or `k = ⌈μ⌉`. -/
theorem abs_sub_lt_one_of_isMode {p : ℝ[X]} (hp : p ≠ 0) (hsplit : p.Splits)
    (hcoeff : ∀ i, 0 ≤ p.coeff i) {k : ℕ} (hk : ∀ j, p.coeff j ≤ p.coeff k) :
    |(k : ℝ) - (derivative p).eval 1 / p.eval 1| < 1 := by
  classical
  have hlc : 0 < p.leadingCoeff :=
    lt_of_le_of_ne (hcoeff _) (leadingCoeff_ne_zero.2 hp).symm
  -- all roots are nonpositive
  have hroot : ∀ a ∈ p.roots, a ≤ 0 := by
    intro a ha
    by_contra h
    push Not at h
    have hev : p.eval a = 0 := (mem_roots hp).1 ha
    rw [eval_eq_sum_range] at hev
    have hpos : 0 < ∑ i ∈ range (p.natDegree + 1), p.coeff i * a ^ i :=
      sum_pos' (fun i _ => mul_nonneg (hcoeff i) (pow_pos h i).le)
        ⟨p.natDegree, self_mem_range_succ _, mul_pos hlc (pow_pos h _)⟩
    linarith
  set m := p.roots with hm
  set T := m.toEnumFinset
  set w : ℝ × ℕ → ℝ := fun x => (1 - x.1)⁻¹
  have hw : ∀ x ∈ T, 0 ≤ w x ∧ w x ≤ 1 := by
    intro x hx
    have hx0 := hroot x.1 (Multiset.mem_of_mem_toEnumFinset hx)
    exact ⟨inv_nonneg.2 (by linarith), inv_le_one_of_one_le₀ (by linarith)⟩
  set K := p.leadingCoeff * (m.map fun a => 1 - a).prod
  have hK : 0 < K := by
    refine mul_pos hlc (Multiset.prod_pos fun b hb => ?_)
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
    linarith [hroot a ha]
  set A := bernPoly w T with hA_def
  have hfac : p = C K * A := by
    have hT' : A = (m.map fun a => C (1 - (1 - a)⁻¹) + C (1 - a)⁻¹ * X).prod := by
      rw [hA_def, bernPoly, prod_eq_multiset_prod, ← Multiset.map_toEnumFinset_fst m,
        Multiset.map_map]
      rfl
    have hprod : (m.map fun a => X - C a).prod =
        C (m.map fun a => 1 - a).prod * A := by
      rw [hT', map_multiset_prod, Multiset.map_map, ← Multiset.prod_map_mul]
      exact congrArg Multiset.prod
        (Multiset.map_congr rfl fun a ha => X_sub_C_eq_C_mul_bernFactor (hroot a ha))
    conv_lhs => rw [hsplit.eq_prod_roots, ← hm, hprod]
    rw [← mul_assoc, ← C_mul]
  have hcoeffA : ∀ j, p.coeff j = K * A.coeff j := fun j => by rw [hfac, coeff_C_mul]
  have hmode : ∀ j, A.coeff j ≤ A.coeff k := fun j =>
    le_of_mul_le_mul_left (by rw [← hcoeffA, ← hcoeffA]; exact hk j) hK
  have hAk : 0 < A.coeff k := by
    have h1 : 0 < p.coeff k := hlc.trans_le (hk _)
    rw [hcoeffA] at h1
    exact pos_of_mul_pos_right h1 hK.le
  -- the mean
  set μ := ∑ x ∈ T, w x
  have hmean : (derivative p).eval 1 / p.eval 1 = μ := by
    have hid := congrArg (eval 1) (derivative_bernPoly_sub w T)
    simp only [eval_sub, eval_mul, eval_C, eval_one, eval_X, sub_self, zero_mul,
      eval_one_bernPoly, mul_one] at hid
    rw [hfac, derivative_C_mul, eval_mul, eval_mul, eval_C, hA_def, eval_one_bernPoly, mul_one,
      mul_div_cancel_left₀ _ hK.ne']
    linarith
  have hμ0 : 0 ≤ μ := sum_nonneg fun x hx => (hw x hx).1
  rw [hmean, abs_sub_lt_iff]
  constructor
  · by_contra h
    push Not at h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero (by
      rintro rfl
      push_cast at h
      linarith)
    have hj : μ ≤ j := by
      push_cast at h
      linarith
    exact absurd (hmode j) (not_le.2 (coeff_succ_lt_coeff_bernPoly w T hw j hj hAk))
  · by_contra h
    push Not at h
    exact absurd (hmode (k + 1))
      (not_le.2 (coeff_lt_coeff_succ_bernPoly w T hw k (by linarith) hAk))

end Polynomial
