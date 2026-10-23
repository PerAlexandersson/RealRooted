/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CenteredEulerian.Parity
public import RealRooted.CenteredEulerian.EulerFormula

/-!
# The basis `p_n` and the matrix of multiplication by `c²`

Ported from Aristotle task `61da6424-89ea-4fbf-852c-6e47d3e3aef9`,
following the compendium zig-zag proof, Appendix B.

`p_n(c) = ∑_k e_k α_{nk} c^k` where `α_{nk} = [s^n] q(s) f(s)^k`; formally
`∑ₙ pₙ(c) sⁿ = q(s) (sec + tan)(c arcsin s)`.
The dual coefficients are `β_{jm} = [z^m] sec z sin^j z`.
-/

@[expose] public section

open PowerSeries

namespace RealRooted.CenteredEulerian

/-- `α_{nk} = [s^n] q f^k`. -/
noncomputable def alpha (n k : ℕ) : ℝ := coeff n (qS * fS ^ k)
/-- `β_{jm} = [z^m] sec z sin^j z`. -/
noncomputable def beta (j m : ℕ) : ℝ := coeff m (secS * sinS ^ j)

/-- `f = X * fT`. -/
noncomputable def fT : ℝ⟦X⟧ := mk (fun n => fc (n + 1))

lemma fS_eq_X_mul : fS = X * fT := by
  ext n
  rcases n with _ | n
  · simp [fS, fc]
  · rw [coeff_succ_X_mul, fS, fT, coeff_mk, coeff_mk]

lemma constantCoeff_fT : constantCoeff fT = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, fT, coeff_mk, fc]
  simp [constantCoeff_invqS]

/-- `sin = X * sT`. -/
noncomputable def sT : ℝ⟦X⟧ := mk (fun n => coeff (n + 1) sinS)

lemma sinS_eq_X_mul : sinS = X * sT := by
  ext n
  rcases n with _ | n
  · simp [coeff_sinS]
  · rw [coeff_succ_X_mul, sT, coeff_mk]

lemma constantCoeff_sT : constantCoeff sT = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, sT, coeff_mk, coeff_sinS]; simp

lemma alpha_eq_zero_of_lt {n k : ℕ} (h : n < k) : alpha n k = 0 := by
  rw [alpha, fS_eq_X_mul, mul_pow, mul_left_comm, coeff_X_pow_mul', ite_eq_right (by lia)]

lemma beta_eq_zero_of_lt {j m : ℕ} (h : m < j) : beta j m = 0 := by
  rw [beta, sinS_eq_X_mul, mul_pow, mul_left_comm, coeff_X_pow_mul', ite_eq_right (by lia)]

lemma alpha_self (n : ℕ) : alpha n n = 1 := by
  rw [alpha, fS_eq_X_mul, mul_pow, mul_left_comm, coeff_X_pow_mul', ite_eq_left le_rfl,
    Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, constantCoeff_qS,
    constantCoeff_fT]; simp

lemma beta_self (j : ℕ) : beta j j = 1 := by
  rw [beta, sinS_eq_X_mul, mul_pow, mul_left_comm, coeff_X_pow_mul', ite_eq_left le_rfl,
    Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, constantCoeff_sT]
  have : constantCoeff secS = 1 := by
    have := congrArg constantCoeff cosS_mul_secS
    rw [map_mul, constantCoeff_cosS, one_mul, map_one] at this; exact this
  rw [this]; simp

lemma alpha_parity {n k : ℕ} (h : ¬ (Even n ↔ Even k)) : alpha n k = 0 :=
  coeff_even_mul_odd_pow_eq_zero isEvenPS_qS isOddPS_fS h

lemma beta_parity {j m : ℕ} (h : ¬ (Even m ↔ Even j)) : beta j m = 0 :=
  coeff_even_mul_odd_pow_eq_zero isEvenPS_secS isOddPS_sinS h

/-- First duality: `∑_j α_{jl} β_{jm} = δ_{lm}`. -/
lemma alpha_beta_dual (l m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), alpha j l * beta j m = if l = m then 1 else 0 := by
  have hs := constantCoeff_sinS
  have h := coeff_mul_subst hs secS (qS * fS ^ l) m
  rw [subst_mul (hasSubst_of_cc_zero hs), subst_pow (hasSubst_of_cc_zero hs), qS_subst_sinS,
    fS_subst_sinS, ← mul_assoc, mul_comm secS cosS, cosS_mul_secS, one_mul, coeff_X_pow] at h
  simp only [alpha, beta]
  rw [← h]
  by_cases hlm : l = m
  · subst hlm; simp
  · rw [ite_eq_right hlm, ite_eq_right (Ne.symm hlm)]

lemma alpha_beta_dual' (l m L : ℕ) (hL : m < L) :
    ∑ j ∈ Finset.range L, alpha j l * beta j m = if l = m then 1 else 0 := by
  rw [← alpha_beta_dual l m]
  symm
  apply Finset.sum_subset
  · intro j hj; simp at hj ⊢; lia
  · intro j hj hj'
    simp at hj hj'
    rw [beta_eq_zero_of_lt (by lia), mul_zero]

/-- Second duality: `∑_k α_{nk} β_{jk} = δ_{nj}`. -/
lemma alpha_beta_dual2 (n j : ℕ) :
    ∑ k ∈ Finset.range (n + 1), alpha n k * beta j k = if n = j then 1 else 0 := by
  set N := n + j + 1 with hN
  let A : Matrix (Fin N) (Fin N) ℝ := fun a b => alpha a b
  let B : Matrix (Fin N) (Fin N) ℝ := fun a b => beta a b
  have hAB : A.transpose * B = 1 := by
    ext l m
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    change (∑ a : Fin N, alpha a l * beta a m) = if l = m then 1 else 0
    rw [Fin.sum_univ_eq_sum_range (fun a => alpha a l * beta a m) N,
      alpha_beta_dual' l m N m.isLt]
    simp [Fin.ext_iff]
  have hBA := mul_eq_one_comm.mp hAB
  have hjn := congrFun (congrFun hBA ⟨j, by lia⟩) ⟨n, by lia⟩
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hjn
  change (∑ a : Fin N, beta j a * alpha n a) =
    if (⟨j, by lia⟩ : Fin N) = (⟨n, by lia⟩ : Fin N) then 1 else 0 at hjn
  rw [Fin.sum_univ_eq_sum_range (fun a => beta j a * alpha n a) N] at hjn
  have : ∑ k ∈ Finset.range (n + 1), alpha n k * beta j k =
      ∑ a ∈ Finset.range N, beta j a * alpha n a := by
    apply Finset.sum_subset_zero_on_sdiff
    · intro k hk; simp at hk ⊢; lia
    · intro k hk; simp at hk; rw [alpha_eq_zero_of_lt (by lia), mul_zero]
    · intro k _; ring
  rw [this, hjn]
  simp only [Fin.mk.injEq]
  by_cases h : n = j
  · subst h; simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

/-- `e_k = β_{0k} + β_{1k}`. -/
lemma eulerCoeff_eq_beta (k : ℕ) : eulerCoeff k = beta 0 k + beta 1 k := by
  rw [eulerCoeff, beta, beta, eulerS, pow_zero, pow_one, mul_add, mul_one, map_add]

/-! ### The polynomials `p_n` -/

/-- `p_n(c) = ∑_k e_k α_{nk} c^k`; formally `∑ pₙ(c) sⁿ = q(s) (sec + tan)(c f(s))`. -/
noncomputable def polynomial (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (eulerCoeff k * alpha n k) * Polynomial.X ^ k

lemma coeff_polynomial (n m : ℕ) : (polynomial n).coeff m = eulerCoeff m * alpha n m := by
  rw [polynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hm : m < n + 1
  · rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; rw [ite_eq_right (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_range.mpr hm) h
  · rw [Finset.sum_eq_zero, alpha_eq_zero_of_lt (by lia), mul_zero]
    intro b hb; simp at hb; rw [ite_eq_right (by lia)]

lemma eval_polynomial (n : ℕ) (c : ℝ) :
    (polynomial n).eval c = ∑ k ∈ Finset.range (n + 1), eulerCoeff k * alpha n k * c ^ k := by
  rw [polynomial, Polynomial.eval_finsetSum]
  simp

lemma alpha_neg_one_pow (n k : ℕ) : (-1 : ℝ) ^ k * alpha n k = (-1) ^ n * alpha n k := by
  by_cases h : (Even n ↔ Even k)
  · rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_one_pow, (h.mpr hk).neg_one_pow]
    · have hn : Odd n := by
        rw [← Nat.not_even_iff_odd] at hk ⊢; exact fun hn => hk (h.mp hn)
      rw [hk.neg_one_pow, hn.neg_one_pow]
  · rw [alpha_parity h]; ring

/-- The formal basis polynomial has the parity dictated by its index. -/
theorem polynomial_comp_neg_X (n : ℕ) :
    (polynomial n).comp (-Polynomial.X) =
      Polynomial.C ((-1 : ℝ) ^ n) * polynomial n := by
  apply Polynomial.funext
  intro r
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_neg, Polynomial.eval_X, eval_polynomial, eval_polynomial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h := alpha_neg_one_pow n k
  rw [neg_pow]
  linear_combination (eulerCoeff k * r ^ k) * h

lemma polynomial_eval_one {n : ℕ} (hn : 2 ≤ n) : (polynomial n).eval 1 = 0 := by
  rw [eval_polynomial]
  simp only [one_pow, mul_one]
  have := alpha_beta_dual2 n 0
  have h1 := alpha_beta_dual2 n 1
  rw [ite_eq_right (by lia)] at this h1
  calc ∑ k ∈ Finset.range (n + 1), eulerCoeff k * alpha n k
      = ∑ k ∈ Finset.range (n + 1), (alpha n k * beta 0 k + alpha n k * beta 1 k) := by
        apply Finset.sum_congr rfl; intro k _; rw [eulerCoeff_eq_beta]; ring
    _ = 0 := by rw [Finset.sum_add_distrib, this, h1]; ring

lemma polynomial_eval_neg_one {n : ℕ} (hn : 2 ≤ n) : (polynomial n).eval (-1) = 0 := by
  rw [eval_polynomial]
  have : ∀ k ∈ Finset.range (n + 1), eulerCoeff k * alpha n k * (-1) ^ k =
      (-1) ^ n * (eulerCoeff k * alpha n k * 1 ^ k) := by
    intro k _
    rw [one_pow, mul_one, mul_assoc, mul_comm (alpha n k), alpha_neg_one_pow]; ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← eval_polynomial,
    polynomial_eval_one hn, mul_zero]

lemma alpha_zero_zero : alpha 0 0 = 1 := alpha_self 0

lemma polynomial_zero : polynomial 0 = 1 := by
  rw [polynomial]; simp [alpha_zero_zero, eulerCoeff_zero]

lemma alpha_one_zero : alpha 1 0 = 0 := alpha_parity (by decide)

lemma polynomial_one : polynomial 1 = Polynomial.X := by
  rw [polynomial]; simp [Finset.sum_range_succ, alpha_one_zero, alpha_self, eulerCoeff_one]

/-! ### Multiplication by `c²` -/

/-- The matrix of multiplication by `c²` in the basis `p_n`. -/
noncomputable def mMat (n j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), eulerRatio k * alpha n k * beta j (k + 2)

lemma eulerRatio_mul (k : ℕ) : eulerRatio k * eulerCoeff (k + 2) = eulerCoeff k := by
  rw [eulerRatio, div_mul_cancel₀ _ (eulerCoeff_pos (k + 2)).ne']

/-- `c² p_n = ∑_j M_{nj} p_j`. -/
theorem X_sq_mul_polynomial (n : ℕ) :
    Polynomial.X ^ 2 * polynomial n =
      ∑ j ∈ Finset.range (n + 3), Polynomial.C (mMat n j) * polynomial j := by
  ext m
  rw [Polynomial.coeff_X_pow_mul', Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, coeff_polynomial, mMat]
  have hswap : ∑ j ∈ Finset.range (n + 3),
      (∑ k ∈ Finset.range (n + 1), eulerRatio k * alpha n k * beta j (k + 2)) *
        (eulerCoeff m * alpha j m) =
      ∑ k ∈ Finset.range (n + 1), eulerRatio k * alpha n k * eulerCoeff m *
        (∑ j ∈ Finset.range (n + 3), alpha j m * beta j (k + 2)) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro j _; ring
  rw [hswap]
  have hk : ∀ k ∈ Finset.range (n + 1),
      eulerRatio k * alpha n k * eulerCoeff m *
        (∑ j ∈ Finset.range (n + 3), alpha j m * beta j (k + 2)) =
      if m = k + 2 then eulerCoeff k * alpha n k else 0 := by
    intro k hk
    rw [alpha_beta_dual' m (k + 2) (n + 3) (by simp at hk; lia)]
    split_ifs with h
    · subst h; rw [mul_one, ← eulerRatio_mul k]; ring
    · ring
  rw [Finset.sum_congr rfl hk]
  split_ifs with h
  · have : ∀ k ∈ Finset.range (n + 1), (if m = k + 2 then eulerCoeff k * alpha n k else 0) =
        if m - 2 = k then eulerCoeff k * alpha n k else 0 := by
      intro k _
      by_cases hk : m = k + 2
      · rw [ite_eq_left hk, ite_eq_left (by lia)]
      · rw [ite_eq_right hk, ite_eq_right (by lia)]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    split_ifs with h'
    · rfl
    · simp at h'; rw [alpha_eq_zero_of_lt (by lia), mul_zero]
  · rw [Finset.sum_eq_zero]; intro k _; rw [ite_eq_right (by lia)]

lemma mMat_zero_one {n : ℕ} (hn : 2 ≤ n) : mMat n 0 = 0 ∧ mMat n 1 = 0 := by
  have h := X_sq_mul_polynomial n
  have e1 := congrArg (Polynomial.eval 1) h
  have e2 := congrArg (Polynomial.eval (-1)) h
  rw [Polynomial.eval_mul, polynomial_eval_one hn, mul_zero, Polynomial.eval_finsetSum] at e1
  rw [Polynomial.eval_mul, polynomial_eval_neg_one hn, mul_zero, Polynomial.eval_finsetSum] at e2
  have split : ∀ c : ℝ,
      ∑ j ∈ Finset.range (n + 3), (Polynomial.C (mMat n j) * polynomial j).eval c =
        mMat n 0 + mMat n 1 * c + ∑ j ∈ Finset.range (n + 1),
          mMat n (j + 2) * (polynomial (j + 2)).eval c := by
    intro c
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp [polynomial_zero, polynomial_one]
    ring
  rw [split] at e1 e2
  have z1 : ∑ j ∈ Finset.range (n + 1), mMat n (j + 2) * (polynomial (j + 2)).eval 1 = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [polynomial_eval_one (by lia), mul_zero])
  have z2 : ∑ j ∈ Finset.range (n + 1), mMat n (j + 2) * (polynomial (j + 2)).eval (-1) = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [polynomial_eval_neg_one (by lia), mul_zero])
  rw [z1] at e1; rw [z2] at e2
  constructor <;> linarith

/-- The matrix `R_{ij}` of multiplication by `c²` in the basis `r_j = p_{j+2}/(c²-1)`. -/
noncomputable def rMat (i j : ℕ) : ℝ := mMat (i + 2) (j + 2)

/-- `c² p_{i+2} = ∑_j R_{ij} p_{j+2}`. -/
theorem X_sq_mul_polynomial' (i : ℕ) :
    Polynomial.X ^ 2 * polynomial (i + 2) =
      ∑ j ∈ Finset.range (i + 3), Polynomial.C (rMat i j) * polynomial (j + 2) := by
  rw [X_sq_mul_polynomial, show i + 2 + 3 = (i + 3) + 2 by ring, Finset.sum_range_succ',
    Finset.sum_range_succ']
  obtain ⟨h0, h1⟩ := mMat_zero_one (n := i + 2) (by lia)
  simp only [h0, h1, map_zero, zero_mul, add_zero, rMat]

lemma rMat_parity {i j : ℕ} (h : ¬ (Even i ↔ Even j)) : rMat i j = 0 := by
  rw [rMat, mMat]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : (Even (i + 2) ↔ Even k)
  · rw [beta_parity (j := j + 2) (m := k + 2), mul_zero]
    intro h'
    apply h
    simp only [Nat.even_add, even_two, iff_true] at hk h'
    tauto
  · rw [alpha_parity hk]; ring

lemma coeff_invqS_two : coeff 2 invqS = 1 / 2 := by
  have h := congrArg (coeff 2) qS_mul_invqS
  rw [coeff_mul, coeff_one] at h
  have h1 : coeff 1 invqS = 0 := isEvenPS_invqS.coeff_odd (by decide)
  have h0 : coeff 0 invqS = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_invqS]
  simp [Finset.Nat.sum_antidiagonal_succ, qS, qc, h1, h0] at h
  norm_num at h
  linarith

lemma polynomial_two :
    polynomial 2 = Polynomial.C (-1 / 2) + Polynomial.C (1 / 2) * Polynomial.X ^ 2 := by
  have h20 : alpha 2 0 = -1 / 2 := by
    simp [alpha, qS, qc]
  have h21 : alpha 2 1 = 0 := alpha_parity (by decide)
  rw [polynomial]
  simp [Finset.sum_range_succ, h20, h21, alpha_self, eulerCoeff_zero, eulerCoeff_one,
    eulerCoeff_two]

lemma polynomial_three : polynomial 3 = Polynomial.C (-1 / 3) * Polynomial.X +
    Polynomial.C (1 / 3) * Polynomial.X ^ 3 := by
  have h30 : alpha 3 0 = 0 := alpha_parity (by decide)
  have h32 : alpha 3 2 = 0 := alpha_parity (by decide)
  have h31 : alpha 3 1 = -1 / 3 := by
    rw [alpha, pow_one, coeff_mul]
    norm_num [Finset.Nat.sum_antidiagonal_succ, qS, qc, fS, fc,
      coeff_invqS_two, constantCoeff_invqS]
  rw [polynomial]
  simp [Finset.sum_range_succ, h30, h31, h32, alpha_self, eulerCoeff_zero, eulerCoeff_one,
    eulerCoeff_two, eulerCoeff_three]

end RealRooted.CenteredEulerian
