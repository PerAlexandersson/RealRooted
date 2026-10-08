import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import RealRooted.CombinatorialExamples.BorosMoll.Estimates

/-!
# The Boros–Moll log-concavity transform interlaces the Narayana polynomial

Xie and Zhang (arXiv:2609.20653, Theorem 1.1): for `n ≥ 1`, the polynomial
`M_n(x) = ∑_{i=0}^n L(d(n))_i x^i`, where `L(d(n))_i = d_i(n)^2 - d_{i-1}(n) d_{i+1}(n)` and
the `d_i(n)` are the Boros–Moll coefficients, has `n` simple negative zeros, and they strictly
interlace the zeros of the Narayana polynomial `N_n`, the zeros of `M_n` being the leftmost.

The proof reduces the sign of `M_n` at the zeros of `N_n` to the positivity of a weighted sum
(`Reduction`), which is controlled by the estimates in
`RealRooted.CombinatorialExamples.BorosMoll.Estimates` for `n ≥ 36`; the cases `1 ≤ n ≤ 35`
are kernel-checked certificates in `RealRooted.CombinatorialExamples.BorosMoll.Basic`.
-/

namespace RealRooted.BorosMoll

section Reduction

/-! ## Reduction to the sign of the weighted sum (Section 2 of Xie–Zhang)

At a zero `x < 0` of `N_n`, with `u = x/(x-1)`, the normalized derivatives
`x^k N^{(k+1)}(x) / (n^{\underline k} N'(x))` are the values `A_{n,k}(u)`, and
`M_n(1/x) = x^{-n} d_n(n)^2 · x N'(x) ∑_k b_k A_{n,k}(u)`.
-/

open Polynomial

private lemma narC_ratio (n j : ℕ) :
    ((j : ℝ) + 1) * ((j : ℝ) + 2) * narC n (j + 1) =
        ((n : ℝ) - j) * ((n : ℝ) - j + 1) * narC n j := by
  rcases lt_or_ge j n with hj | hj
  · have h1 := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq n j)
    have h2 := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq (n+1) j)
    simp only [Nat.cast_mul] at h1 h2
    rw [Nat.cast_sub hj.le] at h1
    rw [Nat.cast_sub (by lia)] at h2
    push_cast at h1 h2
    unfold narC
    field_simp
    push_cast
    linear_combination ((n+1).choose (j+1) : ℝ) * ((j:ℝ) + 1) * ((j:ℝ) + 2) * h1 +
      ((j:ℝ) + 2) * ((n:ℝ) - j) * (n.choose j : ℝ) * h2
  · have h0 : narC n (j+1) = 0 := by
      simp [narC, Nat.choose_eq_zero_of_lt (show n < j + 1 by lia)]
    rcases Nat.eq_or_lt_of_le hj with rfl | hj'
    · rw [h0]; ring
    · have h0' : narC n j = 0 := by simp [narC, Nat.choose_eq_zero_of_lt hj']
      rw [h0, h0']; ring

/-- The hypergeometric differential equation for `N_n`:
`x(1-x) N'' + (2 + 2n x) N' - n(n+1) N = 0`. -/
private lemma narayanaN_ode (n : ℕ) :
    X * derivative (derivative (narayanaN n)) - X * (X * derivative (derivative (narayanaN n))) +
      C 2 * derivative (narayanaN n) + C (2 * (n : ℝ)) * (X * derivative (narayanaN n)) -
        C ((n : ℝ) * ((n : ℝ) + 1)) * narayanaN n = 0 := by
  ext j
  have hr := narC_ratio n j
  rcases j with _ | _ | j
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_zero, coeff_derivative,
      coeff_narayanaN, coeff_zero]
    push_cast at hr ⊢
    linear_combination hr
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_X_mul_zero, coeff_derivative,
      coeff_narayanaN, coeff_zero]
    push_cast at hr ⊢
    linear_combination hr
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative,
      coeff_narayanaN, coeff_zero]
    push_cast at hr ⊢
    linear_combination hr

/-- Iterated derivatives of `N_n`. -/
private noncomputable def Dk (n k : ℕ) : ℝ[X] := derivative^[k] (narayanaN n)

private lemma Dk_succ (n k : ℕ) : Dk n (k + 1) = derivative (Dk n k) := by
  simp only [Dk, Function.iterate_succ_apply']

/-- The differentiated equation:
`x(1-x) N^{(r+2)} + (r+2+(2n-2r)x) N^{(r+1)} - (n-r)(n-r+1) N^{(r)} = 0`. -/
private lemma ode_iter (n r : ℕ) :
    X * Dk n (r + 2) - X * (X * Dk n (r + 2)) + C ((r : ℝ) + 2) * Dk n (r + 1) +
      C (2 * (n : ℝ) - 2 * r) * (X * Dk n (r + 1)) -
        C (((n : ℝ) - r) * ((n : ℝ) - r + 1)) * Dk n r = 0 := by
  induction r with
  | zero =>
    have h := narayanaN_ode n
    simp only [Dk_succ, Nat.cast_zero, zero_add, mul_zero, sub_zero]
    simpa [Dk] using h
  | succ r ih =>
    have h := congrArg derivative ih
    simp only [derivative_add, derivative_sub, derivative_mul, derivative_X, derivative_C,
      zero_mul, zero_add, one_mul, derivative_zero] at h
    rw [← Dk_succ, ← Dk_succ, ← Dk_succ] at h
    simp only [show r + 1 + 2 = r + 3 by ring,
      show r + 1 + 1 = r + 2 by ring] at h ⊢
    simp only [map_add, map_sub, map_mul, map_natCast, map_ofNat, map_one, Nat.cast_add,
      Nat.cast_one] at h ⊢
    linear_combination h

private lemma ode_eval (n r : ℕ) (x : ℝ) :
    x * (1 - x) * (Dk n (r + 2)).eval x + ((r : ℝ) + 2 + (2 * (n : ℝ) - 2 * r) * x) *
      (Dk n (r + 1)).eval x - ((n : ℝ) - r) * ((n : ℝ) - r + 1) * (Dk n r).eval x = 0 := by
  have h := congrArg (eval x) (ode_iter n r)
  simp only [eval_add, eval_sub, eval_mul, eval_X, eval_C, eval_zero] at h
  linear_combination h

private lemma Apoly_two_eval (n k : ℕ) (w : ℝ) : (Apoly n (k + 2)).eval w =
    (2 * w - (((k : ℝ) + 3) / ((n : ℝ) - ((k : ℝ) + 1))) * (1 - w)) * (Apoly n (k + 1)).eval w -
      w * (Apoly n k).eval w := by
  simp [Apoly]

/-- At a zero `x < 0` of `N_n`: `x^k N^{(k+1)}(x) = n^{\underline k} N'(x) A_{n,k}(x/(x-1))`. -/
private lemma A_at_root (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : x < 0) (hN : (narayanaN n).eval x = 0) :
    ∀ k ≤ n, x ^ k * (Dk n (k + 1)).eval x =
      (n.descFactorial k : ℝ) * (Dk n 1).eval x * (Apoly n k).eval (x / (x - 1)) := by
  set u := x / (x - 1) with hu
  have hx1 : x - 1 ≠ 0 := by intro h; linarith
  have hx1' : 1 - x ≠ 0 := by intro h; linarith
  have hd0 : (Dk n 0).eval x = 0 := by simpa [Dk] using hN
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have two : ∀ k, k + 1 ≤ n → (x ^ k * (Dk n (k+1)).eval x =
      (n.descFactorial k : ℝ) * (Dk n 1).eval x * (Apoly n k).eval u) ∧
      (x ^ (k+1) * (Dk n (k+2)).eval x =
      (n.descFactorial (k+1) : ℝ) * (Dk n 1).eval x * (Apoly n (k+1)).eval u) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨by simp [Apoly], ?_⟩
      have h := ode_eval n 0 x
      simp only [Nat.cast_zero, hd0, zero_add, mul_zero, sub_zero, pow_one] at h ⊢
      simp only [Nat.descFactorial_one, Apoly, eval_sub, eval_mul, eval_C, eval_X, eval_one]
      rw [hu]
      have hn0 : (n:ℝ) ≠ 0 := by linarith
      field_simp
      linear_combination (-1:ℝ) * h
    | succ k ih =>
      obtain ⟨h0, h1⟩ := ih (by lia)
      refine ⟨h1, ?_⟩
      have h := ode_eval n (k+1) x
      have hF1 : (n.descFactorial (k+1) : ℝ) = ((n:ℝ) - k) * (n.descFactorial k : ℝ) := by
        rw [Nat.descFactorial_succ]; push_cast [Nat.cast_sub (show k ≤ n by lia)]; ring
      have hF2 : (n.descFactorial (k+2) : ℝ) = ((n:ℝ) - k - 1) * (n.descFactorial (k+1) : ℝ) := by
        rw [Nat.descFactorial_succ]; push_cast [Nat.cast_sub (show k + 1 ≤ n by lia)]; ring
      rw [show k + 1 + 1 = k + 2 by ring, show k + 1 + 2 = k + 3 by ring] at *
      rw [Apoly_two_eval]
      have hnk : (n:ℝ) - ((k:ℝ) + 1) ≠ 0 := by
        have : (k:ℝ) + 2 ≤ n := by exact_mod_cast hk
        linarith
      -- multiply the equation by `x^(k+1)`
      have key : (1 - x) * (x ^ (k+2) * (Dk n (k+3)).eval x) =
          -(((k:ℝ) + 3) + (2 * (n:ℝ) - 2 * ((k:ℝ) + 1)) * x) * (x ^ (k+1) * (Dk n (k+2)).eval x) +
            ((n:ℝ) - k - 1) * ((n:ℝ) - k) * x * (x ^ k * (Dk n (k+1)).eval x) := by
        push_cast at h
        linear_combination x ^ (k+1) * h
      apply mul_left_cancel₀ hx1'
      rw [key, h0, h1, hF2, hF1, hu]
      field_simp
      ring
  intro k hk
  rcases k with _ | k
  · exact (two 0 (by lia)).1
  · exact (two k (by lia)).2

/-- Taylor coefficients: `∑_j C(j,r) N_{n,j} x^j = x^r N^{(r)}(x)/r!`. -/
private lemma taylor_sum (n r : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range (n + 1), (j.choose r : ℝ) * narC n j * x ^ j =
      x ^ r * (Dk n r).eval x / (r.factorial : ℝ) := by
  have hD : Dk n r = (r.factorial • hasseDeriv r) (narayanaN n) := by
    rw [factorial_smul_hasseDeriv]; rfl
  have hH : (hasseDeriv r (narayanaN n)).eval x =
      ∑ j ∈ Finset.range (n + 1), (j.choose r : ℝ) * narC n j * x ^ (j - r) := by
    unfold narayanaN
    rw [map_sum, eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j _
    rw [C_mul_X_pow_eq_monomial, hasseDeriv_monomial, eval_monomial]
    unfold narC; ring
  rw [hD, LinearMap.smul_apply, eval_smul, hH, nsmul_eq_mul, Finset.mul_sum, Finset.mul_sum,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_or_ge j r with h | h
  · simp [Nat.choose_eq_zero_of_lt h]
  · have : x ^ r * x ^ (j - r) = x ^ j := by rw [← pow_add]; congr 1; lia
    field_simp
    rw [← this]; ring

private lemma narC_symm (n i : ℕ) (hi : i ≤ n) : narC n (n - i) = narC n i := by
  unfold narC
  rw [Nat.choose_symm hi]
  have h := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq (n+1) i)
  simp only [Nat.cast_mul] at h
  rw [Nat.cast_sub (by lia)] at h
  have e : (n + 1).choose (n - i) = (n + 1).choose (i + 1) := by
    rw [← Nat.choose_symm (show i + 1 ≤ n + 1 by lia)]; congr 1; lia
  rw [e]
  push_cast [Nat.cast_sub hi] at h ⊢
  have hi' : (i:ℝ) ≤ n := by exact_mod_cast hi
  have hne : (n:ℝ) - i + 1 ≠ 0 := by linarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_div_iff hne (by positivity)]
  linear_combination (n.choose i : ℝ) * h

/-- Reciprocity: `t^n N_n(1/t) = N_n(t)`. -/
private lemma narayanaN_recip (n : ℕ) (t : ℝ) (ht : t ≠ 0) :
    t ^ n * (narayanaN n).eval t⁻¹ = (narayanaN n).eval t := by
  unfold narayanaN
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Finset.mul_sum]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [show n + 1 - 1 - j = n - j by lia]
  have := narC_symm n j (by lia)
  unfold narC at this
  rw [this]
  have hp : t ^ n * t⁻¹ ^ (n - j) = t ^ j := by
    rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ ht), ← pow_add]; congr 1; lia
  calc t ^ n * (1 / ((j:ℝ) + 1) * (n.choose j : ℝ) * ((n + 1).choose j : ℝ) * t⁻¹ ^ (n - j))
      = 1 / ((j:ℝ) + 1) * (n.choose j : ℝ) * ((n + 1).choose j : ℝ) * (t ^ n * t⁻¹ ^ (n - j)) := by
        ring
    _ = _ := by rw [hp]

/-- At a root `ρ ≠ 0`: `N_n'(ρ) = -ρ^n ρ^{-2} N_n'(1/ρ)`. -/
private lemma narayanaN_deriv_recip (n : ℕ) (ρ : ℝ) (hρ : ρ ≠ 0) (hr : (narayanaN n).eval ρ⁻¹ = 0) :
    (derivative (narayanaN n)).eval ρ =
        -(ρ ^ n * (ρ ^ 2)⁻¹) * (derivative (narayanaN n)).eval ρ⁻¹ := by
  have h1 : HasDerivAt (fun t => t ^ n * (narayanaN n).eval t⁻¹)
      ((n:ℝ) * ρ ^ (n - 1) * (narayanaN n).eval ρ⁻¹ +
        ρ ^ n * ((derivative (narayanaN n)).eval ρ⁻¹ * (-(ρ ^ 2)⁻¹))) ρ := by
    have hp := hasDerivAt_pow n ρ
    have hc := ((narayanaN n).hasDerivAt ρ⁻¹).comp ρ (hasDerivAt_inv hρ)
    exact hp.mul hc
  have h2 : HasDerivAt (fun t => t ^ n * (narayanaN n).eval t⁻¹)
      ((derivative (narayanaN n)).eval ρ) ρ := by
    apply ((narayanaN n).hasDerivAt ρ).congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hρ] with t ht
    exact narayanaN_recip n t ht
  rw [h2.unique h1, hr]
  ring

/-- `M_n(1/x) = x^{-n} d_n(n)^2 ∑_r η_{n,r} x^r N^{(r)}(x)/r!`. -/
private lemma bmM_eval_inv_taylor (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    (bmM n).eval x⁻¹ = x⁻¹ ^ n * bmCoeff n n ^ 2 *
      ∑ r ∈ Finset.range (n + 1), eta n r * (x ^ r * (Dk n r).eval x / (r.factorial : ℝ)) := by
  have h1 : (bmM n).eval x⁻¹ = ∑ i ∈ Finset.range (n + 1), bmL n i * x⁻¹ ^ i := by
    simp [bmM, eval_finsetSum]
  rw [h1, ← Finset.sum_range_reflect]
  simp only [show ∀ j, n + 1 - 1 - j = n - j from fun j => by lia]
  have h2 : ∀ j ∈ Finset.range (n + 1), bmL n (n - j) * x⁻¹ ^ (n - j) =
      x⁻¹ ^ n * bmCoeff n n ^ 2 * ∑ r ∈ Finset.range (n + 1),
        eta n r * ((j.choose r : ℝ) * narC n j * x ^ j) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [bmL_eq_eta n j (by lia)]
    have hp : x⁻¹ ^ (n - j) = x⁻¹ ^ n * x ^ j := by
      rw [show n = (n - j) + j from by lia, pow_add, inv_pow x j]
      rw [show n - j + j - j = n - j by lia]
      field_simp
    rw [hp]
    have hsub : ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) * eta n r =
        ∑ r ∈ Finset.range (n + 1), (j.choose r : ℝ) * eta n r := by
      apply Finset.sum_subset
      · intro r hr; simp at hr ⊢; lia
      · intro r _ hr; simp at hr; simp [Nat.choose_eq_zero_of_lt (show j < r by lia)]
    rw [hsub, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.mul_sum, taylor_sum]

/-- **The reduction identity.** At a zero `x < 0` of `N_n`,
`M_n(1/x) = x^{-n} d_n(n)^2 · x N'(x) ∑_{k<n} b_k A_{n,k}(x/(x-1))`. -/
private theorem bmM_eval_inv (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : x < 0)
    (hN : (narayanaN n).eval x = 0) :
    (bmM n).eval x⁻¹ = x⁻¹ ^ n * bmCoeff n n ^ 2 *
      (x * (derivative (narayanaN n)).eval x *
        ∑ k ∈ Finset.range n, bw n k * (Apoly n k).eval (x / (x - 1))) := by
  rw [bmM_eval_inv_taylor n x hx.ne]
  congr 1
  rw [Finset.sum_range_succ']
  have hd0 : (Dk n 0).eval x = 0 := by simpa [Dk] using hN
  rw [hd0]
  simp only [mul_zero, zero_div, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  have hA := A_at_root n hn x hx hN k hk.le
  have hD1 : Dk n 1 = derivative (narayanaN n) := by simp [Dk]
  rw [hD1] at hA
  unfold bw
  rw [pow_succ, show x ^ k * x * (Dk n (k+1)).eval x = x * (x ^ k * (Dk n (k+1)).eval x) by ring,
    hA]
  ring

private lemma Jpoly_eval_trans (n : ℕ) (t : ℝ) (ht : t ≠ 1) :
    (Jpoly n).eval (t / (t - 1)) * (t - 1) ^ n = (narayanaN n).eval t := by
  have ht1 : t - 1 ≠ 0 := sub_ne_zero.2 ht
  unfold Jpoly narayanaN
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have e1 : t / (t - 1) - 1 = 1 / (t - 1) := by field_simp; ring
  rw [e1]
  have e2 : (t - 1) ^ n = (t - 1) ^ i * (t - 1) ^ (n - i) := by
    rw [← pow_add]; congr 1; lia
  rw [e2, div_pow, div_pow, one_pow]
  unfold narC
  field_simp

/-- **Sign at the zeros of `N_n`** for `n ≥ 36`. -/
private theorem sign_at_roots_large (n : ℕ) (hn : 36 ≤ n) (r : ℝ) (hr : (narayanaN n).IsRoot r) :
    0 < (bmM n).eval r * (derivative (narayanaN n)).eval r := by
  obtain ⟨ρs, hmono, hneg, hroots⟩ := narayanaN_roots n
  have hN0 := narayanaN_ne_zero n
  have mem_iff : ∀ t, (narayanaN n).IsRoot t ↔ t ∈ (narayanaN n).roots := fun t =>
    (mem_roots hN0).symm
  have root_neg : ∀ t, (narayanaN n).IsRoot t → t < 0 := by
    intro t ht
    rw [mem_iff, hroots] at ht
    simp only [Multiset.mem_coe, List.mem_map, List.mem_range] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    exact hneg j hj
  have deriv_ne : ∀ t, (narayanaN n).IsRoot t → (derivative (narayanaN n)).eval t ≠ 0 := by
    intro t ht
    rw [mem_iff, hroots] at ht
    simp only [Multiset.mem_coe, List.mem_map, List.mem_range] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    have := sign_deriv_at_sorted_root hmono (narayanaN_natDegree n) hroots hN0
      (by rw [narayanaN_leadingCoeff]; norm_num) hj
    intro h0; rw [h0, mul_zero] at this; exact lt_irrefl _ this
  -- the transformed zeros
  set g : ℝ → ℝ := fun t => t / (t - 1) with hg
  set U : Finset ℝ := (narayanaN n).roots.toFinset.image g with hU
  have hRn : ∀ t, (narayanaN n).IsRoot t → (Rpoly n n).eval (g t) = 0 := by
    intro t ht
    have htn := root_neg t ht
    have hA := A_at_root n (by lia) t htn ht n le_rfl
    have hz : Dk n (n+1) = 0 := by
      unfold Dk
      apply iterate_derivative_eq_zero
      rw [narayanaN_natDegree]; lia
    rw [hz, eval_zero, mul_zero] at hA
    have hD1 : Dk n 1 = derivative (narayanaN n) := by simp [Dk]
    rw [hD1] at hA
    have hF : (n.descFactorial n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.2 le_rfl).ne'
    have hAn : (Apoly n n).eval (g t) = 0 := by
      rcases mul_eq_zero.1 hA.symm with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · exact absurd h' hF
        · exact absurd h' (deriv_ne t ht)
      · exact h
    rw [Rpoly_self, eval_mul, hAn, mul_zero]
  have hZ : ZeroSet n U := by
    refine ⟨?_, ?_⟩
    · rw [hU, Finset.card_image_of_injOn]
      · rw [Multiset.toFinset_card_of_nodup]
        · rw [hroots]; simp
        · rw [hroots]; exact nodup_map_range hmono
      · intro a ha b hb hab
        simp only [Multiset.mem_toFinset,
          Finset.mem_coe] at ha hb
        have ha' := root_neg a ((mem_iff a).2 ha)
        have hb' := root_neg b ((mem_iff b).2 hb)
        simp only [hg] at hab
        have h1 : a - 1 ≠ 0 := by intro h; linarith
        have h2 : b - 1 ≠ 0 := by intro h; linarith
        field_simp at hab
        linarith
    · intro u hu
      rw [hU, Finset.mem_image] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      rw [Multiset.mem_toFinset] at ht
      have htr := (mem_iff t).2 ht
      have htn := root_neg t htr
      refine ⟨div_pos_of_neg_of_neg htn (by linarith), ?_, ?_, hRn t htr⟩
      · rw [div_lt_one_of_neg (by linarith)]; linarith
      · have := Jpoly_eval_trans n t (by intro h; linarith)
        rw [htr.eq_zero] at this
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd (pow_eq_zero_iff (by lia) |>.1 h) (by intro h'; linarith)
  -- the root `r` and its reciprocal
  have hrn := root_neg r hr
  have hr0 : r ≠ 0 := hrn.ne
  set x := r⁻¹ with hx
  have hxn : x < 0 := inv_lt_zero.2 hrn
  have hNx : (narayanaN n).eval x = 0 := by
    have := narayanaN_recip n r hr0
    rw [hr.eq_zero] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (pow_eq_zero_iff (by lia) |>.1 h) hr0
    · exact h
  have hxroot : (narayanaN n).IsRoot x := hNx
  have hMr : (bmM n).eval r = x⁻¹ ^ n * bmCoeff n n ^ 2 *
      (x * (derivative (narayanaN n)).eval x *
        ∑ k ∈ Finset.range n, bw n k * (Apoly n k).eval (x / (x - 1))) := by
    rw [← bmM_eval_inv n (by lia) x hxn hNx, hx, inv_inv]
  have hDr := narayanaN_deriv_recip n r hr0 hNx
  have hS := weighted_sum_pos n hn U hZ (g x) (by
    rw [hU, Finset.mem_image]
    exact ⟨x, Multiset.mem_toFinset.2 ((mem_iff x).1 hxroot), rfl⟩)
  simp only [hg] at hS
  rw [hMr, hDr, hx, inv_inv]
  set S := ∑ k ∈ Finset.range n, bw n k * (Apoly n k).eval (r⁻¹ / (r⁻¹ - 1))
  set d := (derivative (narayanaN n)).eval r⁻¹
  have hd : d ≠ 0 := deriv_ne x hxroot
  have hdd : 0 < d ^ 2 := by positivity
  have hb := bmCoeff_self_pos n
  have hrr : 0 < (r ^ n) ^ 2 * (r ^ 2)⁻¹ := by positivity
  have hx' : 0 < -r⁻¹ := by linarith
  have : r ^ n * bmCoeff n n ^ 2 * (r⁻¹ * d * S) * (-(r ^ n * (r ^ 2)⁻¹) * d) =
      ((r ^ n) ^ 2 * (r ^ 2)⁻¹) * bmCoeff n n ^ 2 * (-r⁻¹) * d ^ 2 * S := by ring
  rw [this]
  positivity

end Reduction

section MainTheorems

/-! ## Xie–Zhang, Theorem 1.1: the zeros of `M_n` interlace the zeros of the Narayana polynomial

The definitions (`bmCoeff`, `bmL`, `bmM`, `narayanaN`, `sortedRoots`,
`StrictInterlacesSameDegree`) are in `BorosMoll/Basic.lean`.

The proof follows the paper:
* `1 ≤ n ≤ 35`: kernel-checked Sturm-type certificates (`BorosMoll/SmallCases.lean`);
* `n ≥ 36`: the sign of `M_n` at the zeros of `N_n` (`BorosMoll/Reduction.lean`), using the
  moment estimates (`Moments`, `Eta`, `Coeff`, `Shape`), the bounds for the partial sums
  (`Energy`, `PartialSums`, `Gauss`, `GaussBound`, `AllZeros`).
-/

open Polynomial

/-- The interlacing data for every `n ≥ 1`. -/
theorem bmInterlace (n : ℕ) (hn : 1 ≤ n) : BMInterlace n := by
  rcases le_or_gt n 35 with h | h
  · exact bmInterlace_small n hn h
  · exact bmInterlace_of_sign n hn (fun r hr => sign_at_roots_large n (by lia) r hr)

/-- Xie–Zhang (arXiv:2609.20653), Theorem 1.1 (first part): `M_n` has `n` simple negative zeros. -/
theorem bmM_roots (n : ℕ) (hn : 1 ≤ n) :
    bmM n ≠ 0 ∧ (bmM n).natDegree = n ∧ (bmM n).Splits ∧ (bmM n).roots.Nodup ∧
      ∀ r ∈ (bmM n).roots, r < 0 :=
  bmM_roots_of_interlace n (bmInterlace n hn)

/-- Xie–Zhang (arXiv:2609.20653), Theorem 1.1 (second part): the zeros of `M_n` strictly
interlace the zeros of the Narayana polynomial `N_n` of the same degree, the zeros of `M_n`
being the leftmost. -/
theorem bmM_strictInterlaces_narayanaN (n : ℕ) (hn : 1 ≤ n) :
    StrictInterlacesSameDegree (bmM n) (narayanaN n) n :=
  bmM_strictInterlaces_of_interlace n (bmInterlace n hn)

example : bmCoeff 1 0 = 3 / 2 := by
  norm_num [bmCoeff, Finset.sum_Icc_succ_top, Nat.choose]
example : bmCoeff 2 1 = 15 / 4 := by
  norm_num [bmCoeff, Finset.sum_Icc_succ_top, Nat.choose]
example : bmL 1 0 = 9 / 4 := by
  norm_num [bmL, bmCoeff, Finset.sum_Icc_succ_top, Nat.choose]

end MainTheorems

end RealRooted.BorosMoll
