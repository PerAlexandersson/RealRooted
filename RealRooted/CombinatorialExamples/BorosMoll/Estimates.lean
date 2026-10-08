import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import RealRooted.CombinatorialExamples.BorosMoll.Basic

/-!
# Boros–Moll log-concavity transform: estimates for large `n`

Analytic estimates for the proof of Xie–Zhang (arXiv:2609.20653, Theorem 1.1) for `n ≥ 36`:
the moment functional of the product weight (`Moments`), the recurrence bound (`Energy`),
the quantities `η_{n,r}` (`Eta`), the coefficient identity (`Coeff`), the shape of the weights
`b_j` (`Shape`), the polynomials `A_{n,k}`, partial sums `V_{n,k}` and remainders `R_{n,k}`
(`PartialSums`), Jacobi-type polynomials with a Gauss–Lagrange identity (`Gauss`), the Gaussian
bound (`GaussBound`), and the positivity of the weighted sum at all zeros (`AllZeros`).
-/

namespace RealRooted.BorosMoll

section Moments

/-! ## Moments (Section 3 of Xie–Zhang, in formal form)

We work with the moment functional of the product weight `f_n(x) f_n(y)` in the coordinates
`x = 1 + 2 s₀`, `y = 1 + 2 s₁`.  The one-dimensional moments are
`μ_a = E[s^a] = ∏_{b<a} (2b+1)/(4n-2b)`, and the two-dimensional functional `Lm` is defined
on `MvPolynomial (Fin 2) ℝ` by `Lm (s₀^a s₁^b) = μ_a μ_b`.  Integration by parts becomes the
purely algebraic identity `Lm (Dop i p) = 0`.
-/

open MvPolynomial

/-- One-dimensional moments `μ_a = ∏_{b<a} (2b+1)/(4n-2b)`. -/
private noncomputable def mu (n a : ℕ) : ℝ :=
  ∏ b ∈ Finset.range a, ((2 * (b:ℝ) + 1) / (4 * (n:ℝ) - 2 * b))

private lemma mu_zero (n : ℕ) : mu n 0 = 1 := by simp [mu]

private lemma mu_succ (n a : ℕ) :
    mu n (a + 1) = mu n a * ((2 * (a : ℝ) + 1) / (4 * (n : ℝ) - 2 * a)) := by
  rw [mu, mu, Finset.prod_range_succ]

private lemma mu_rec (n a : ℕ) (ha : a < 2 * n) :
    (4 * (n : ℝ) - 2 * a) * mu n (a + 1) = (2 * (a : ℝ) + 1) * mu n a := by
  have : (4 * (n:ℝ) - 2 * a) ≠ 0 := by
    have : (a:ℝ) + 1 ≤ 2 * n := by exact_mod_cast ha
    linarith
  rw [mu_succ]; field_simp

private lemma mu_pos (n a : ℕ) (ha : a ≤ 2 * n) : 0 < mu n a := by
  unfold mu
  apply Finset.prod_pos
  intro b hb
  simp only [Finset.mem_range] at hb
  have : (b:ℝ) + 1 ≤ 2 * n := by exact_mod_cast (show b + 1 ≤ 2 * n by lia)
  apply div_pos
  · positivity
  · linarith

private abbrev P2 := MvPolynomial (Fin 2) ℝ

/-- The weight of a monomial. -/
private noncomputable def wt (n : ℕ) (m : Fin 2 →₀ ℕ) : ℝ := mu n (m 0) * mu n (m 1)

/-- The two-dimensional moment functional. -/
private noncomputable def Lm (n : ℕ) : P2 →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (wt n) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv (R := ℝ) (S := ℝ) (M := Fin 2 →₀ ℕ)).toLinearMap

private lemma Lm_monomial (n : ℕ) (s : Fin 2 →₀ ℕ) (c : ℝ) : Lm n (monomial s c) = c * wt n s := by
  have h : (monomial s c : P2).coeff = Finsupp.single s c := by
    ext m
    simp only [coeff_monomial, Finsupp.single_apply]
  simp only [Lm, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change Finsupp.linearCombination ℝ (wt n) (monomial s c : P2).coeff = _
  rw [h, Finsupp.linearCombination_single, smul_eq_mul]

private lemma Lm_C_mul (n : ℕ) (c : ℝ) (p : P2) : Lm n (C c * p) = c * Lm n p := by
  rw [C_mul', map_smul, smul_eq_mul]

private lemma Lm_one (n : ℕ) : Lm n 1 = 1 := by
  rw [show (1 : P2) = monomial 0 1 from rfl, Lm_monomial]
  simp [wt, mu_zero]

private lemma Lm_X_pow (n a b : ℕ) : Lm n (X 0 ^ a * X 1 ^ b) = mu n a * mu n b := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, Lm_monomial]
  simp [wt]

/-! ### Integration by parts -/

/-- The integration-by-parts operator in the `i`-th variable:
`D_i p = 2 s_i (1 + s_i) ∂_i p + (1 - 4 n s_i) p`. -/
private noncomputable def Dop (n : ℕ) (i : Fin 2) : P2 →ₗ[ℝ] P2 :=
  LinearMap.mulLeft ℝ (C 2 * (1 + X i)) ∘ₗ LinearMap.mulLeft ℝ (X i) ∘ₗ
      (pderiv (R := ℝ) i).toLinearMap +
    LinearMap.mulLeft ℝ (1 - C (4 * (n:ℝ)) * X i)

private lemma Dop_apply (n : ℕ) (i : Fin 2) (p : P2) :
    Dop n i p = C 2 * (1 + X i) * (X i * pderiv i p) + (1 - C (4 * (n : ℝ)) * X i) * p := by
  simp [Dop, mul_assoc]

private lemma X_mul_monomial' (i : Fin 2) (s : Fin 2 →₀ ℕ) (c : ℝ) :
    X i * monomial s c = monomial (s + Finsupp.single i 1) c := by
  rw [X, monomial_mul_monomial, one_mul, add_comm]

private lemma Lm_Dop_monomial (n : ℕ) (i : Fin 2) (s : Fin 2 →₀ ℕ) (c : ℝ) (hs : s i < 2 * n) :
    Lm n (Dop n i (monomial s c)) = 0 := by
  rw [Dop_apply, X_mul_pderiv_monomial, nsmul_eq_mul]
  have e : C 2 * (1 + X i) * ((s i : P2) * monomial s c) + (1 - C (4 * (n:ℝ)) * X i) *
      monomial s c = monomial s ((2 * (s i : ℝ) + 1) * c) +
        monomial (s + Finsupp.single i 1) ((2 * (s i : ℝ) - 4 * n) * c) := by
    have h1 : (s i : P2) = C (s i : ℝ) := by simp
    rw [h1]
    simp only [mul_add, add_mul, mul_one, one_mul, sub_mul]
    rw [show C 2 * X i * (C (s i : ℝ) * monomial s c) = C (2 * (s i : ℝ)) * (X i * monomial s c)
      by simp only [map_mul]; ring,
      show C (4 * (n:ℝ)) * X i * monomial s c = C (4 * (n:ℝ)) * (X i * monomial s c) by ring,
      X_mul_monomial']
    simp only [C_mul_monomial]
    rw [map_add (monomial s), map_sub (monomial _),
      show 2 * ((s i : ℝ) * c) = 2 * (s i : ℝ) * c by ring]
    abel
  rw [e, map_add, Lm_monomial, Lm_monomial]
  have hr := mu_rec n (s i) hs
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · simp only [wt, Finsupp.add_apply, Finsupp.single_apply]
    simp
    linear_combination (-c * mu n (s 1)) * hr
  · simp only [wt, Finsupp.add_apply, Finsupp.single_apply]
    simp
    linear_combination (-c * mu n (s 0)) * hr

private lemma mem_support_le (p : P2) (s : Fin 2 →₀ ℕ) (hs : s ∈ p.support) (i : Fin 2) :
    s i ≤ p.totalDegree := by
  have h := le_totalDegree hs
  have : s i ≤ s.sum (fun _ e => e) := by
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
    fin_cases i <;> simp
  lia

/-- **Integration by parts.** -/
private lemma Lm_Dop (n : ℕ) (i : Fin 2) (p : P2) (hp : p.totalDegree < 2 * n) :
    Lm n (Dop n i p) = 0 := by
  rw [p.as_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro s hs
  exact Lm_Dop_monomial n i s _ (lt_of_le_of_lt (mem_support_le p s hs i) hp)

/-! ### Positivity -/

/-- Nonnegative coefficients. -/
private def NN (p : P2) : Prop := ∀ s, 0 ≤ p.coeff s

private lemma NN_add {p q : P2} (hp : NN p) (hq : NN q) : NN (p + q) := fun s => by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]; exact add_nonneg (hp s) (hq s)

private lemma NN_mul {p q : P2} (hp : NN p) (hq : NN q) : NN (p * q) := fun s => by
  rw [coeff_mul]; exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

private lemma NN_pow {p : P2} (hp : NN p) (k : ℕ) : NN (p ^ k) := by
  induction k with
  | zero => intro s; rw [pow_zero, coeff_one]; split_ifs <;> norm_num
  | succ k ih => rw [pow_succ]; exact NN_mul ih hp

private lemma NN_X (i : Fin 2) : NN (X i) := fun s => by
  rw [coeff_X]; split_ifs <;> norm_num

private lemma NN_C {c : ℝ} (hc : 0 ≤ c) : NN (C c) := fun s => by
  rw [coeff_C]; split_ifs
  · exact hc
  · exact le_rfl

private lemma Lm_nonneg (n : ℕ) (p : P2) (hp : NN p) (hd : p.totalDegree ≤ 2 * n) : 0 ≤ Lm n p := by
  rw [p.as_sum, map_sum]
  apply Finset.sum_nonneg
  intro s hs
  rw [Lm_monomial]
  apply mul_nonneg (hp s)
  exact mul_nonneg (mu_pos n _ ((mem_support_le p s hs 0).trans hd)).le
    (mu_pos n _ ((mem_support_le p s hs 1).trans hd)).le

/-! ### The coordinates `x`, `y`, `t = xy - 1`, `e = (x-y)^2` -/

private noncomputable def xx : P2 := 1 + 2 * X 0
private noncomputable def yy : P2 := 1 + 2 * X 1
private noncomputable def tt : P2 := xx * yy - 1
private noncomputable def ee : P2 := (xx - yy) ^ 2

/-- The one-variable moments `m_j = E[x^j] = ∑_r C(j,r) 2^r μ_r`. -/
private noncomputable def mom (n j : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) * 2 ^ r * mu n r

private lemma pow_xx_eq (a : ℕ) (i : Fin 2) : (1 + 2 * X i : P2) ^ a =
    ∑ r ∈ Finset.range (a + 1), C ((a.choose r : ℝ) * 2 ^ r) * X i ^ r := by
  rw [add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro r _
  simp only [one_pow, mul_one, map_mul, map_pow, map_natCast, mul_pow]
  rw [map_ofNat C 2]
  ring

private lemma Lm_xx_yy (n a b : ℕ) : Lm n (xx ^ a * yy ^ b) = mom n a * mom n b := by
  unfold xx yy mom
  rw [pow_xx_eq, pow_xx_eq, Finset.sum_mul_sum, map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_mul_mul_comm, ← map_mul, Lm_C_mul, Lm_X_pow]
  ring

private lemma tt_eq : tt = C 2 * X 0 + C 2 * X 1 + C 4 * (X 0 * X 1) := by
  simp only [tt, xx, yy]
  rw [map_ofNat C 2, map_ofNat C 4]
  ring

private lemma NN_tt : NN tt := by
  rw [tt_eq]
  exact NN_add (NN_add (NN_mul (NN_C (by norm_num)) (NN_X 0)) (NN_mul (NN_C (by norm_num))
    (NN_X 1))) (NN_mul (NN_C (by norm_num)) (NN_mul (NN_X 0) (NN_X 1)))

private lemma totalDegree_xx : xx.totalDegree ≤ 1 := by
  unfold xx
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [(map_ofNat C 2).symm, totalDegree_C, totalDegree_X]

private lemma totalDegree_yy : yy.totalDegree ≤ 1 := by
  unfold yy
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [(map_ofNat C 2).symm, totalDegree_C, totalDegree_X]

private lemma totalDegree_tt : tt.totalDegree ≤ 2 := by
  unfold tt
  refine (totalDegree_sub _ _).trans (max_le ?_ (by simp))
  refine (totalDegree_mul _ _).trans ?_
  have := totalDegree_xx; have := totalDegree_yy; lia

private lemma totalDegree_tt_pow (k : ℕ) : (tt ^ k).totalDegree ≤ 2 * k := by
  refine (totalDegree_pow _ _).trans ?_
  have := totalDegree_tt
  nlinarith

/-! ### Derivatives of the coordinates -/

private lemma pd_two (i : Fin 2) : pderiv i (2 : P2) = 0 := by
  rw [← map_ofNat C 2, pderiv_C]

private lemma pd0_xx : pderiv 0 xx = 2 := by simp [xx, pd_two]
private lemma pd1_xx : pderiv 1 xx = 0 := by simp [xx, pd_two]
private lemma pd0_yy : pderiv 0 yy = 0 := by simp [yy, pd_two]
private lemma pd1_yy : pderiv 1 yy = 2 := by simp [yy, pd_two]

private lemma pd0_tt : pderiv 0 tt = 2 * yy := by
  simp only [tt, map_sub, Derivation.leibniz, pd0_xx, pd0_yy, smul_eq_mul,
      Derivation.map_one_eq_zero]
  ring

private lemma pd1_tt : pderiv 1 tt = 2 * xx := by
  simp only [tt, map_sub, Derivation.leibniz, pd1_xx, pd1_yy, smul_eq_mul,
      Derivation.map_one_eq_zero]
  ring

private lemma pd0_tt_pow (k : ℕ) : pderiv 0 (tt ^ (k + 1)) = ((k:P2) + 1) * tt ^ k * (2 * yy) := by
  rw [Derivation.leibniz_pow, pd0_tt, nsmul_eq_mul, smul_eq_mul]
  push_cast; ring

private lemma pd1_tt_pow (k : ℕ) : pderiv 1 (tt ^ (k + 1)) = ((k:P2) + 1) * tt ^ k * (2 * xx) := by
  rw [Derivation.leibniz_pow, pd1_tt, nsmul_eq_mul, smul_eq_mul]
  push_cast; ring

private lemma C_four_n (n : ℕ) : (C (4 * (n : ℝ)) : P2) = 4 * (n : P2) := by
  rw [map_mul, map_natCast, map_ofNat]

/-! ### Polynomial identities behind integration by parts -/

private lemma poly_star (n k : ℕ) :
    Dop n 0 ((xx - yy) * tt ^ (k + 1)) - Dop n 1 ((xx - yy) * tt ^ (k + 1)) =
      C 2 * tt ^ (k + 2) - C (2 * (n : ℝ) - ((k : ℝ) + 2)) * (ee * tt ^ (k + 1)) +
        C (2 * ((k : ℝ) + 1)) * (ee * tt ^ k) := by
  simp only [Dop_apply, Derivation.leibniz, map_sub, pd0_xx, pd0_yy, pd1_xx, pd1_yy, pd0_tt_pow,
    pd1_tt_pow, smul_eq_mul, C_four_n]
  simp only [map_mul, map_add, map_natCast, map_ofNat, map_one]
  simp only [ee, tt, xx, yy]
  ring

private lemma poly_star_one (n : ℕ) :
    Dop n 0 (xx - yy) - Dop n 1 (xx - yy) = C 2 * tt - C (2 * (n : ℝ) - 1) * ee := by
  simp only [Dop_apply, map_sub, pd0_xx, pd0_yy, pd1_xx, pd1_yy, C_four_n]
  simp only [map_mul, map_natCast, map_ofNat, map_one]
  simp only [ee, tt, xx, yy]
  ring

private lemma poly_S (n k : ℕ) :
    Dop n 0 (tt ^ (k + 1)) + Dop n 1 (tt ^ (k + 1)) =
      C ((k : ℝ) + 1 - 2 * n) * ((xx + yy) * tt ^ (k + 1)) + C (2 * (2 * (n : ℝ) + 1)) * tt ^
          (k + 1) := by
  simp only [Dop_apply, pd0_tt_pow, pd1_tt_pow, C_four_n]
  simp only [map_sub, map_mul, map_add, map_natCast, map_ofNat, map_one]
  simp only [tt, xx, yy]
  ring

private lemma poly_Y (n k : ℕ) :
    Dop n 0 (yy * tt ^ (k + 1)) + Dop n 1 (xx * tt ^ (k + 1)) =
      C ((k : ℝ) + 1) * (C 2 * tt ^ (k + 2) + C 2 * tt ^ (k + 1) - ee * tt ^ k) +
        C (2 * (n : ℝ) + 1) * ((xx + yy) * tt ^ (k + 1)) - C (4 * (n : ℝ)) * tt ^ (k + 2) -
          C (4 * (n : ℝ)) * tt ^ (k + 1) := by
  simp only [Dop_apply, Derivation.leibniz, pd0_yy, pd1_xx, pd0_tt_pow,
    pd1_tt_pow, smul_eq_mul, C_four_n]
  simp only [map_mul, map_add, map_natCast, map_ofNat, map_one]
  simp only [ee, tt, xx, yy]
  ring

end Moments

section Energy

/-! ## The recurrence bound (Proposition `prop:recurrence-bound` of Xie–Zhang)

A real sequence `R` with `R 0 = 1`, `R 1 = ((n+3)u-2)/(n+1)` and
`(n-j+1) R (j+1) = ((2n-j+3)u - j - 2) R j - (n-j) u R (j-1)` satisfies `R k ^ 2 ≤ u`
whenever `k ≤ (n+3)u - 2`.
-/

/-- The recurrence for the normalized remainders at a fixed point `u`. -/
private def RRec (n : ℕ) (u : ℝ) (R : ℕ → ℝ) : Prop :=
  R 0 = 1 ∧ R 1 = (((n:ℝ) + 3) * u - 2) / ((n:ℝ) + 1) ∧
    ∀ j : ℕ, 1 ≤ j → j < n →
      ((n:ℝ) - j + 1) * R (j+1) = (((2 * (n:ℝ) - j + 3) * u - j - 2) * R j
        - ((n:ℝ) - j) * u * R (j-1))

/-- The increment identity: with `m = n-j+1`, `λ = (n+3)(1-u)`,
`R(j+1) = R j + ((m-1)u/m)(R j - R(j-1)) - (λ/m) R j`. -/
private lemma rrec_delta {n : ℕ} {u : ℝ} {R : ℕ → ℝ} (h : RRec n u R) {j : ℕ} (hj1 : 1 ≤ j)
    (hjn : j < n) :
    R (j + 1) = R j + (((((n : ℝ) - j + 1) - 1) * u / ((n : ℝ) - j + 1)) * (R j - R (j-1))
      - (((n : ℝ) + 3) * (1 - u) / ((n : ℝ) - j + 1)) * R j) := by
  have hm : (0:ℝ) < (n:ℝ) - j + 1 := by
    have : (j:ℝ) < n := by exact_mod_cast hjn
    linarith
  have hr := h.2.2 j hj1 hjn
  field_simp
  linear_combination hr

private lemma small_step_identity (m lam u r d : ℝ) (hm : 0 < m) (hlam : 0 < lam) :
    (r + ((m-1) * u / m * d - lam / m * r)) ^ 2 + ((m - 1 + 1 - lam) / lam) *
        ((m-1) * u / m * d - lam / m * r) ^ 2 =
      (1 - lam / m) * r ^ 2 + ((m-1) ^ 2 * u ^ 2 / (lam * m)) * d ^ 2 := by
  field_simp
  ring

private lemma small_step (m lam u r d : ℝ) (hm : 1 ≤ m) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hu0 : 0 < u) (hu1 : u < 1) (hc1 : 1 - lam / m ≤ u) :
    (r + ((m-1) * u / m * d - lam / m * r)) ^ 2 + ((m - 1 + 1 - lam) / lam) *
        ((m-1) * u / m * d - lam / m * r) ^ 2 ≤
      u * (r ^ 2 + ((m + 1 - lam) / lam) * d ^ 2) := by
  rw [small_step_identity m lam u r d (by linarith) hlam]
  have hc2 : (m-1)^2 * u^2 / (lam * m) ≤ u * ((m + 1 - lam) / lam) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (m-1)^2 * u ≤ (m-1)^2 := by nlinarith [sq_nonneg (m-1)]
    have h2 : (m-1)^2 ≤ m * (m + 1 - lam) := by nlinarith
    have e : u * ((m + 1 - lam) / lam) * (lam * m) = u * (m * (m + 1 - lam)) := by
      field_simp
    rw [e]
    nlinarith
  have hr := sq_nonneg r
  have hd := sq_nonneg d
  have := mul_le_mul_of_nonneg_right hc1 hr
  have := mul_le_mul_of_nonneg_right hc2 hd
  nlinarith

/-- Small `λ = (n+3)(1-u) ≤ 1`. -/
private lemma energy_small {n : ℕ} {u : ℝ} {R : ℕ → ℝ} (h : RRec n u R) (hu0 : 0 < u) (hu1 : u < 1)
    (hlam : ((n : ℝ) + 3) * (1 - u) ≤ 1) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    R k ^ 2 < u := by
  obtain ⟨lam, hl⟩ : ∃ l : ℝ, l = ((n:ℝ) + 3) * (1 - u) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hl]; apply mul_pos <;> linarith
  rw [← hl] at hlam
  let Es : ℕ → ℝ := fun j => R j ^ 2 + (((n:ℝ) - j + 1 + 1 - lam) / lam) * (R j - R (j-1)) ^ 2
  have hEs_ge : ∀ j, j ≤ n → R j ^ 2 ≤ Es j := by
    intro j hj
    have : (0:ℝ) ≤ ((n:ℝ) - j + 1 + 1 - lam) / lam := by
      apply div_nonneg _ hlam0.le
      have : (j:ℝ) ≤ n := by exact_mod_cast hj
      linarith
    have := mul_nonneg this (sq_nonneg (R j - R (j-1)))
    simp only [Es]
    linarith
  have hstep : ∀ j, 1 ≤ j → j < n → Es (j+1) ≤ Es j := by
    intro j hj1 hjn
    have hD := rrec_delta h hj1 hjn
    rw [← hl] at hD
    have hjr : (j:ℝ) + 1 ≤ n := by exact_mod_cast hjn
    have hj1r : (1:ℝ) ≤ j := by exact_mod_cast hj1
    have hm1 : (1:ℝ) ≤ (n:ℝ) - j + 1 := by linarith
    have hc1 : 1 - lam / ((n:ℝ) - j + 1) ≤ u := by
      rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ (by linarith)]
      rw [hl]
      nlinarith
    have key := small_step ((n:ℝ) - j + 1) lam u (R j) (R j - R (j-1)) hm1 hlam0 hlam hu0 hu1 hc1
    have hEj1 : Es (j+1) = (R j + ((((n:ℝ) - j + 1)-1)*u/((n:ℝ) - j + 1)*(R j - R (j-1))
        - lam/((n:ℝ) - j + 1)*R j))^2 + ((((n:ℝ) - j + 1) - 1 + 1 - lam)/lam) *
        ((((n:ℝ) - j + 1)-1)*u/((n:ℝ) - j + 1)*(R j - R (j-1)) - lam/((n:ℝ) - j + 1)*R j)^2 := by
      simp only [Es]
      rw [show j + 1 - 1 = j by lia]
      have e2 : ((n:ℝ) - ((j+1:ℕ):ℝ) + 1 + 1 - lam) = ((n:ℝ) - j + 1) - 1 + 1 - lam := by
        push_cast; ring
      rw [e2, hD]; ring
    have hEnn : 0 ≤ Es j := (sq_nonneg _).trans (hEs_ge j hjn.le)
    rw [hEj1]
    calc _ ≤ u * Es j := key
      _ ≤ Es j := by nlinarith
  have hmono : ∀ j, 1 ≤ j → j ≤ k → Es j ≤ Es 1 := by
    intro j hj1 hjk
    induction j with
    | zero => lia
    | succ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact le_rfl
      · exact (hstep i hi (by lia)).trans (ih hi (by lia))
  have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hE1 : Es 1 = 1 - lam / ((n:ℝ) + 1) := by
    simp only [Es]
    rw [h.2.1, show 1 - 1 = 0 from rfl, h.1]
    push_cast
    have hl' : lam ≠ 0 := hlam0.ne'
    field_simp
    rw [hl]
    ring
  have hE1u : Es 1 < u := by
    rw [hE1, sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', lt_div_iff₀ hn]
    rw [hl]
    nlinarith
  calc R k ^ 2 ≤ Es k := hEs_ge k hkn
    _ ≤ Es 1 := hmono k hk1 le_rfl
    _ < u := hE1u

/-- The energy used for large `λ` (with `m = n - j + 1`). -/
private noncomputable def Ef (nn m u r d : ℝ) : ℝ :=
  (nn + 1) / m * (r ^ 2 + ((1 - ((nn + 3) - m) * (1 - u)) / ((nn + 3) * (1 - u))) * r * d
    + (m * u / ((nn + 3) * (1 - u))) * d ^ 2)

private lemma large_lower (nn m u r d : ℝ) (hu0 : 0 < u) (hu1 : u < 1)
    (hlam1 : 1 < (nn + 3) * (1 - u)) (hlm : (nn + 3) * (1 - u) ≤ m) (hmn : m ≤ nn) :
    r ^ 2 ≤ Ef nn m u r d := by
  have hq : 0 < 1 - u := by linarith
  set q := 1 - u with hq_def
  set lam := (nn + 3) * q with hlam_def
  have hm0 : 0 < m := by linarith
  have hlam0 : 0 < lam := by linarith
  set a := nn + 3 - m with ha
  have ha3 : 3 ≤ a := by rw [ha]; linarith
  set dj := 1 - a * q with hdj
  have key : (nn + 3) * (m * a * q * u - dj ^ 2) = m * (a - 1) + a * (lam - 1) * (m + 1 - lam) := by
    rw [hdj, hlam_def, ha, hq_def]; ring
  have hpos : 0 < m * (a - 1) + a * (lam - 1) * (m + 1 - lam) := by
    have h1 : 0 < m * (a - 1) := by nlinarith
    have h2 : 0 ≤ a * (lam - 1) * (m + 1 - lam) := by
      apply mul_nonneg; apply mul_nonneg <;> linarith
      linarith
    linarith
  have hdj2 : dj ^ 2 < m * a * q * u := by
    have hN : 0 < nn + 3 := by linarith
    nlinarith
  -- the quadratic form
  set A := (nn + 1 - m) * lam with hA
  set B := (nn + 1) * dj with hB
  set Cc := (nn + 1) * m * u with hC
  have hA0 : 0 < A := by
    rw [hA]; apply mul_pos _ hlam0
    linarith
  have hdisc : B ^ 2 ≤ 4 * A * Cc := by
    rw [hA, hB, hC]
    have hn1 : 0 < nn + 1 := by linarith
    have h1 : (nn + 1) * dj ^ 2 ≤ (nn + 1) * (m * a * q * u) :=
      mul_le_mul_of_nonneg_left hdj2.le hn1.le
    have h2 : (nn + 1) * a ≤ 4 * (nn + 1 - m) * (nn + 3) := by
      rw [ha]; nlinarith
    have h3 : (nn + 1) * (m * a * q * u) ≤ 4 * (nn + 1 - m) * (nn + 3) * (m * q * u) := by
      have : 0 ≤ m * q * u := by positivity
      nlinarith
    have : ((nn + 1) * dj) ^ 2 = (nn + 1) * ((nn + 1) * dj ^ 2) := by ring
    rw [this]
    have : 4 * ((nn + 1 - m) * lam) * ((nn + 1) * m * u) =
        (nn + 1) * (4 * (nn + 1 - m) * (nn + 3) * (m * q * u)) := by rw [hlam_def]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (h1.trans h3) hn1.le
  have hQ : 0 ≤ A * r ^ 2 + B * r * d + Cc * d ^ 2 := by
    have h4 : 4 * A * (A * r ^ 2 + B * r * d + Cc * d ^ 2) =
        (2 * A * r + B * d) ^ 2 + (4 * A * Cc - B ^ 2) * d ^ 2 := by ring
    have : 0 ≤ (2 * A * r + B * d) ^ 2 + (4 * A * Cc - B ^ 2) * d ^ 2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg d))
    rw [← h4] at this
    exact (mul_nonneg_iff_of_pos_left (by positivity : (0:ℝ) < 4 * A)).1 this
  have hE : m * lam * (Ef nn m u r d - r ^ 2) = A * r ^ 2 + B * r * d + Cc * d ^ 2 := by
    unfold Ef
    rw [← hq_def, ← hlam_def, hA, hB, hC, hdj, ha]
    field_simp
    ring
  have : 0 ≤ m * lam * (Ef nn m u r d - r ^ 2) := by rw [hE]; exact hQ
  have hml : 0 < m * lam := mul_pos hm0 hlam0
  have := (mul_nonneg_iff_of_pos_left hml).1 this
  linarith

private lemma large_step (nn m u r d : ℝ) (hu0 : 0 < u) (hu1 : u < 1) (hnn : 0 ≤ nn)
    (hm : 1 ≤ m - 1) (hmn : m ≤ nn + 1)
    (hE : r ^ 2 ≤ Ef nn m u r d) :
    Ef nn (m - 1) u (r + ((m-1) * u / m * d - ((nn + 3) * (1 - u)) / m * r))
      ((m-1) * u / m * d - ((nn + 3) * (1 - u)) / m * r) ≤ Ef nn m u r d := by
  have hm0 : 0 < m := by linarith
  have hq : 0 < 1 - u := by linarith
  have hid : Ef nn (m - 1) u (r + ((m-1)*u/m*d - ((nn + 3) * (1 - u))/m*r))
      ((m-1)*u/m*d - ((nn + 3) * (1 - u))/m*r) =
      u * Ef nn m u r d - (nn + 1) * u / (((nn + 3) * (1 - u)) * m) * d *
          ((1 - u) * r + u * d) := by
    unfold Ef
    have : m - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hid]
  have hsq : 0 ≤ (2 * u * d + (1 - u) * r) ^ 2 := sq_nonneg _
  have hdq : -( (1 - u) ^ 2 * r ^ 2 / (4 * u)) ≤ d * ((1 - u) * r + u * d) := by
    have e : d * ((1 - u) * r + u * d) - (-( (1 - u) ^ 2 * r ^ 2 / (4 * u))) =
        (2 * u * d + (1 - u) * r) ^ 2 / (4 * u) := by
      field_simp; ring
    have : 0 ≤ (2 * u * d + (1 - u) * r) ^ 2 / (4 * u) := by positivity
    linarith
  have hc : 0 < (nn + 1) * u / (((nn + 3) * (1 - u)) * m) := by positivity
  have h1 : -((nn + 1) * u / (((nn + 3) * (1 - u)) * m) * d * ((1 - u) * r + u * d)) ≤
      (nn + 1) * u / (((nn + 3) * (1 - u)) * m) * ((1 - u) ^ 2 * r ^ 2 / (4 * u)) := by
    have := mul_le_mul_of_nonneg_left hdq hc.le
    linarith
  have h2 : (nn + 1) * u / (((nn + 3) * (1 - u)) * m) * ((1 - u) ^ 2 * r ^ 2 / (4 * u)) =
      ((nn + 1) / (4 * (nn + 3) * m)) * (1 - u) * r ^ 2 := by
    field_simp
  have h3 : (nn + 1) / (4 * (nn + 3) * m) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hE0 : 0 ≤ Ef nn m u r d := (sq_nonneg r).trans hE
  have h4 : ((nn + 1) / (4 * (nn + 3) * m)) * (1 - u) * r ^ 2 ≤ (1 - u) * Ef nn m u r d := by
    have h5 : 0 ≤ (nn + 1) / (4 * (nn + 3) * m) := by positivity
    calc ((nn + 1) / (4 * (nn + 3) * m)) * (1 - u) * r ^ 2
        ≤ 1 * (1 - u) * r ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg r)
          exact mul_le_mul_of_nonneg_right h3 hq.le
      _ ≤ (1 - u) * Ef nn m u r d := by nlinarith
  nlinarith

/-- Large `λ`: if `1 < λ ≤ n - k + 1`, then `R k ^ 2 ≤ u`. -/
private lemma energy_large {n : ℕ} {u : ℝ} {R : ℕ → ℝ} (h : RRec n u R) (hu0 : 0 < u) (hu1 : u < 1)
    (hlam1 : 1 < ((n : ℝ) + 3) * (1 - u)) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hk : ((n : ℝ) + 3) * (1 - u) ≤ (n : ℝ) - k + 1) :
    R k ^ 2 ≤ u := by
  let Es : ℕ → ℝ := fun j => Ef n ((n:ℝ) - j + 1) u (R j) (R j - R (j-1))
  have hlow : ∀ j, 1 ≤ j → j ≤ k → R j ^ 2 ≤ Es j := by
    intro j hj1 hjk
    have hjk' : (j:ℝ) ≤ k := by exact_mod_cast hjk
    have hj1' : (1:ℝ) ≤ j := by exact_mod_cast hj1
    exact large_lower n _ u _ _ hu0 hu1 hlam1 (by linarith) (by linarith)
  have hstep : ∀ j, 1 ≤ j → j < k → Es (j+1) ≤ Es j := by
    intro j hj1 hjk
    have hD := rrec_delta h hj1 (by lia)
    have hjk' : (j:ℝ) + 1 ≤ k := by exact_mod_cast hjk
    have hkn' : (k:ℝ) ≤ n := by exact_mod_cast hkn
    have hj1' : (1:ℝ) ≤ j := by exact_mod_cast hj1
    have := large_step n ((n:ℝ) - j + 1) u (R j) (R j - R (j-1)) hu0 hu1 (by positivity)
      (by linarith) (by linarith) (hlow j hj1 hjk.le)
    have e : Es (j+1) = Ef n ((n:ℝ) - j + 1 - 1) u
        (R j + ((((n:ℝ) - j + 1)-1)*u/((n:ℝ) - j + 1)*(R j - R (j-1))
          - ((n + 3) * (1 - u))/((n:ℝ) - j + 1)*R j))
        ((((n:ℝ) - j + 1)-1)*u/((n:ℝ) - j + 1)*(R j - R (j-1))
          - ((n + 3) * (1 - u))/((n:ℝ) - j + 1)*R j) := by
      simp only [Es]
      rw [show j + 1 - 1 = j by lia, hD]
      push_cast
      congr 1
      · ring
      · ring
    rw [e]
    exact this
  have hmono : ∀ j, 1 ≤ j → j ≤ k → Es j ≤ Es 1 := by
    intro j hj1 hjk
    induction j with
    | zero => lia
    | succ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact le_rfl
      · exact (hstep i hi (by lia)).trans (ih hi (by lia))
  have hE1 : Es 1 = u := by
    simp only [Es]
    rw [h.2.1, show 1 - 1 = 0 from rfl, h.1]
    unfold Ef
    push_cast
    simp only [sub_add_cancel]
    have hn : (0:ℝ) < n := by
      have : (1:ℝ) ≤ n := by exact_mod_cast hk1.trans hkn
      linarith
    have : (0:ℝ) < 1 - u := by linarith
    have hn' : (n:ℝ) ≠ 0 := hn.ne'
    field_simp
    ring
  calc R k ^ 2 ≤ Es k := hlow k hk1 le_rfl
    _ ≤ Es 1 := hmono k hk1 le_rfl
    _ = u := hE1

/-- **Proposition (recurrence bound).** If `1 ≤ k ≤ n` and `k ≤ (n+3)u - 2`, then
`R k ^ 2 ≤ u`. -/
private theorem recurrence_bound {n : ℕ} {u : ℝ} {R : ℕ → ℝ} (h : RRec n u R) (hu0 : 0 < u)
    (hu1 : u < 1) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hk : (k : ℝ) ≤ ((n : ℝ) + 3) * u - 2) :
    R k ^ 2 ≤ u := by
  rcases le_or_gt (((n:ℝ) + 3) * (1 - u)) 1 with hl | hl
  · exact (energy_small h hu0 hu1 hl k hk1 hkn).le
  · exact energy_large h hu0 hu1 hl k hk1 hkn (by linarith)

end Energy

section Eta

/-! ## The quantities `η_{n,r}` (Lemma `lem:eta-integrals` and Proposition `prop:moment-ratio`)
-/

open MvPolynomial

/-- `I_j = E[t^j]`. -/
private noncomputable def Imom (n j : ℕ) : ℝ := Lm n (tt ^ j)
/-- `E_j = E[e t^j]`. -/
private noncomputable def Emom (n j : ℕ) : ℝ := Lm n (ee * tt ^ j)
/-- `S_k = E[(x+y) t^k]`. -/
private noncomputable def Smom (n k : ℕ) : ℝ := Lm n ((xx + yy) * tt ^ k)

private lemma totalDegree_xx_sub_yy : (xx - yy).totalDegree ≤ 1 :=
  (totalDegree_sub _ _).trans (max_le totalDegree_xx totalDegree_yy)

private lemma star_succ (n k : ℕ) (h : k + 2 ≤ n) :
    (2 * (n : ℝ) - ((k : ℝ) + 2)) * Emom n (k + 1) =
        2 * Imom n (k + 2) + 2 * ((k : ℝ) + 1) * Emom n k := by
  have hd : ((xx - yy) * tt ^ (k+1)).totalDegree < 2 * n := by
    refine lt_of_le_of_lt (totalDegree_mul _ _) ?_
    have := totalDegree_xx_sub_yy; have := totalDegree_tt_pow (k+1); lia
  have h0 := Lm_Dop n 0 _ hd
  have h1 := Lm_Dop n 1 _ hd
  have e := congrArg (Lm n) (poly_star n k)
  rw [map_sub, h0, h1, map_add, map_sub, Lm_C_mul, Lm_C_mul, Lm_C_mul] at e
  unfold Imom Emom
  linarith

private lemma star_one (n : ℕ) (h : 1 ≤ n) : (2 * (n : ℝ) - 1) * Emom n 0 = 2 * Imom n 1 := by
  have hd : (xx - yy).totalDegree < 2 * n := by have := totalDegree_xx_sub_yy; lia
  have e := congrArg (Lm n) (poly_star_one n)
  rw [map_sub, Lm_Dop n 0 _ hd, Lm_Dop n 1 _ hd, map_sub, Lm_C_mul, Lm_C_mul] at e
  unfold Imom Emom
  simp only [pow_zero, mul_one, pow_one]
  linarith

private lemma S_id (n k : ℕ) (h : k + 1 < n) :
    (2 * (n : ℝ) - ((k : ℝ) + 1)) * Smom n (k + 1) = 2 * (2 * (n : ℝ) + 1) * Imom n (k + 1) := by
  have hd : (tt ^ (k+1)).totalDegree < 2 * n := by
    have := totalDegree_tt_pow (k+1); lia
  have e := congrArg (Lm n) (poly_S n k)
  rw [map_add, Lm_Dop n 0 _ hd, Lm_Dop n 1 _ hd, map_add, Lm_C_mul, Lm_C_mul] at e
  unfold Imom Smom
  linarith

private lemma Y_id (n k : ℕ) (h : k + 1 < n) :
    2 * (2 * (n : ℝ) - ((k : ℝ) + 1)) * (Imom n (k + 2) + Imom n (k + 1)) =
      (2 * (n : ℝ) + 1) * Smom n (k + 1) - ((k : ℝ) + 1) * Emom n k := by
  have hdy : (yy * tt ^ (k+1)).totalDegree < 2 * n := by
    refine lt_of_le_of_lt (totalDegree_mul _ _) ?_
    have := totalDegree_yy; have := totalDegree_tt_pow (k+1); lia
  have hdx : (xx * tt ^ (k+1)).totalDegree < 2 * n := by
    refine lt_of_le_of_lt (totalDegree_mul _ _) ?_
    have := totalDegree_xx; have := totalDegree_tt_pow (k+1); lia
  have e := congrArg (Lm n) (poly_Y n k)
  rw [map_add, Lm_Dop n 0 _ hdy, Lm_Dop n 1 _ hdx] at e
  simp only [LinearMap.map_sub, LinearMap.map_add, Lm_C_mul] at e
  unfold Imom Smom Emom
  linarith

/-! ### Positivity -/

private lemma Imom_nonneg (n j : ℕ) (hj : j ≤ n) : 0 ≤ Imom n j :=
  Lm_nonneg n _ (NN_pow NN_tt j) ((totalDegree_tt_pow j).trans (by lia))

private lemma Imom_zero (n : ℕ) : Imom n 0 = 1 := by simp [Imom, Lm_one]

private lemma mu_one (n : ℕ) : mu n 1 = 1 / (4 * (n : ℝ)) := by
  rw [mu_succ, mu_zero]; simp

private lemma mu_two (n : ℕ) : mu n 2 = 1 / (4 * (n : ℝ)) * (3 / (4 * (n : ℝ) - 2)) := by
  rw [mu_succ, mu_one]; norm_num

private lemma Emom_zero_pos (n : ℕ) (hn : 1 ≤ n) : 0 < Emom n 0 := by
  have e : ee * tt ^ 0 = C 4 * (X 0 ^ 2 * X 1 ^ 0) - C 8 * (X 0 ^ 1 * X 1 ^ 1) +
      C 4 * (X 0 ^ 0 * X 1 ^ 2) := by
    simp only [ee, xx, yy, map_ofNat]; ring
  unfold Emom
  rw [e, map_add, map_sub, Lm_C_mul, Lm_C_mul, Lm_C_mul, Lm_X_pow, Lm_X_pow, Lm_X_pow,
    mu_zero, mu_one, mu_two]
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (0:ℝ) < 4 * n - 2 := by linarith
  have h2 : (0:ℝ) < 4 * n := by linarith
  rw [← sub_pos]
  field_simp
  nlinarith

private lemma Emom_pos (n j : ℕ) (hj : j + 1 ≤ n) : 0 < Emom n j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | j
    · exact Emom_zero_pos n (by lia)
    · have hs := star_succ n j (by lia)
      have hI := Imom_nonneg n (j+2) (by lia)
      have hE := ih j (by lia) (by lia)
      have hc : (0:ℝ) < 2 * (n:ℝ) - ((j:ℝ) + 2) := by
        have : (j:ℝ) + 2 ≤ n := by exact_mod_cast hj
        linarith
      have : 0 < (2 * (n:ℝ) - ((j:ℝ) + 2)) * Emom n (j+1) := by
        rw [hs]; positivity
      exact pos_of_mul_pos_right this hc.le

/-! ### `η_{n,r}` -/

/-- `η_{n,r} = I_r - (r/(2(n+1))) ((n-r) E_{r-1} - (r-1) E_{r-2})`. -/
noncomputable def eta (n r : ℕ) : ℝ :=
  Imom n r - ((r:ℝ) / (2 * ((n:ℝ) + 1))) *
    (((n:ℝ) - r) * Emom n (r - 1) - ((r:ℝ) - 1) * Emom n (r - 2))

private lemma eta_zero (n : ℕ) : eta n 0 = 1 := by simp [eta, Imom_zero]

/-- The positive form of `η_{n,r}`. -/
private lemma eta_pos_form (n r : ℕ) (h1 : 1 ≤ r) (hr : r ≤ n) :
    4 * ((n : ℝ) + 1) * eta n r = 2 * (2 * (n : ℝ) + 2 - r) * Imom n r + (r : ℝ) ^ 2 * Emom n
        (r - 1) := by
  have hn : ((n:ℝ) + 1) ≠ 0 := by positivity
  unfold eta
  rcases r with _ | r
  · lia
  rcases r with _ | r
  · have := star_one n (by lia)
    simp only [Nat.sub_self, zero_add] at *
    field_simp
    push_cast
    linear_combination (-2:ℝ) * this
  · have := star_succ n r (by lia)
    simp only [show r + 2 - 1 = r + 1 by lia, show r + 2 - 2 = r by lia]
    field_simp
    push_cast
    linear_combination (-2 * ((r:ℝ) + 2)) * this

private lemma eta_pos (n r : ℕ) (h1 : 1 ≤ r) (hr : r ≤ n) : 0 < eta n r := by
  have h := eta_pos_form n r h1 hr
  have hI := Imom_nonneg n r hr
  have hE := Emom_pos n (r - 1) (by lia)
  have hr' : (r:ℝ) ≤ n := by exact_mod_cast hr
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast h1
  have : 0 < 4 * ((n:ℝ) + 1) * eta n r := by
    rw [h]
    have : 0 ≤ 2 * (2 * (n:ℝ) + 2 - r) * Imom n r := by
      apply mul_nonneg _ hI; linarith
    have : 0 < (r:ℝ) ^ 2 * Emom n (r - 1) := by positivity
    linarith
  have hn : (0:ℝ) < 4 * ((n:ℝ) + 1) := by positivity
  exact pos_of_mul_pos_right this hn.le

/-- The polynomial `P_r(h)` of the ratio estimate. -/
private noncomputable def ratioP (r h : ℝ) : ℝ :=
  2 * (r^2 - 3*r - 1) * h^3 + 2 * (r^3 - 6*r^2 - 4*r - 3) * h^2 +
    (2*r^4 - 16*r^3 - 7*r^2 - 5*r - 4) * h + r * (r + 1) * (r^3 - 7*r^2 + 2*r - 2)

/-- The polynomial `Q_r(h)` of the ratio estimate. -/
private noncomputable def ratioQ (r h : ℝ) : ℝ :=
  4 * h^3 + 12 * h^2 + 2 * (r - 2) * (r^2 - 3*r - 2) * h + r * (r - 4) * (r - 1) * (r + 1)

private lemma ratio_identity (n q : ℕ) (hq : q + 4 ≤ n) :
    2 * ((n : ℝ) + 1) * (2 * (n : ℝ) - ((q : ℝ) + 4)) * (2 * (n : ℝ) - ((q : ℝ) + 4) + 1) ^ 2 *
        (((q : ℝ) + 4) * eta n (q + 3) - ((n : ℝ) - ((q : ℝ) + 4) + 2) * eta n (q + 4)) =
      2 * ratioP ((q : ℝ) + 4) ((n : ℝ) - ((q : ℝ) + 4)) * Imom n (q + 3) +
        ((q : ℝ) + 3) * ((q : ℝ) + 2) * ratioQ ((q : ℝ) + 4) ((n : ℝ) - ((q : ℝ) + 4)) * Emom n
            (q + 1) := by
  have e1 := star_succ n (q+2) (by lia)
  have e2 := star_succ n (q+1) (by lia)
  have e3 := S_id n (q+2) (by lia)
  have e4 := Y_id n (q+2) (by lia)
  have e5 := eta_pos_form n (q+4) (by lia) hq
  have e6 := eta_pos_form n (q+3) (by lia) (by lia)
  simp only [show q + 4 - 1 = q + 3 by lia, show q + 3 - 1 = q + 2 by lia,
    show q + 2 + 2 = q + 4 by lia, show q + 2 + 1 = q + 3 by lia,
    show q + 1 + 1 = q + 2 by lia] at *
  push_cast at *
  unfold ratioP ratioQ
  linear_combination (((q:ℝ)+4)^2*(-2*(n:ℝ) + ((q:ℝ)+4) - 1)^2*(-(n:ℝ) + ((q:ℝ)+4) - 2)/2) * e1 +
      ((1 - ((q:ℝ)+4))*(-4*(n:ℝ)^3 + 12*(n:ℝ)^2*((q:ℝ)+4) - 12*(n:ℝ)^2 - 2*(n:ℝ)*((q:ℝ)+4)^3 -
      2*(n:ℝ)*((q:ℝ)+4)^2 + 16*(n:ℝ)*((q:ℝ)+4) - 8*(n:ℝ) + ((q:ℝ)+4)^4 - 2*((q:ℝ)+4)^3 -
      3*((q:ℝ)+4)^2 + 4*((q:ℝ)+4))/2) * e2 +
      ((2*(n:ℝ) + 1)*(-(n:ℝ) + ((q:ℝ)+4) - 2)*(2*(n:ℝ)^2 - 2*(n:ℝ)*((q:ℝ)+4) + 2*(n:ℝ) + ((q:ℝ)+4)^2
      - ((q:ℝ)+4))) * e3 + ((-(n:ℝ) + ((q:ℝ)+4) - 2)*(2*(n:ℝ) - ((q:ℝ)+4) + 1)*(2*(n:ℝ)^2 -
      2*(n:ℝ)*((q:ℝ)+4) + 2*(n:ℝ) + ((q:ℝ)+4)^2 - ((q:ℝ)+4))) * e4 +
      ((2*(n:ℝ) - ((q:ℝ)+4))*(-2*(n:ℝ) + ((q:ℝ)+4) - 1)^2*(-(n:ℝ) + ((q:ℝ)+4) - 2)/2) * e5 +
      (-((q:ℝ)+4)*(-2*(n:ℝ) + ((q:ℝ)+4))*(-2*(n:ℝ) + ((q:ℝ)+4) - 1)^2/2) * e6

private lemma ratioP_pos (q h : ℕ) (hn : 36 ≤ q + 4 + h) : 0 < ratioP ((q : ℝ) + 4) (h : ℝ) := by
  unfold ratioP
  rcases Nat.lt_or_ge q 5 with hq | hq
  · have hh : (32:ℝ) - q ≤ h := by
      have : 32 ≤ q + h := by lia
      have : (32:ℝ) ≤ q + h := by exact_mod_cast this
      linarith
    have h28 : (28:ℝ) ≤ h := by
      have : (q:ℝ) ≤ 4 := by exact_mod_cast (show q ≤ 4 by lia)
      linarith
    have hh0 : (0:ℝ) ≤ h := by positivity
    have a1 := mul_nonneg (sub_nonneg.2 h28) (sq_nonneg (h:ℝ))
    have a2 := mul_nonneg (sub_nonneg.2 h28) hh0
    interval_cases q <;> norm_num <;> nlinarith
  · obtain ⟨s, rfl⟩ : ∃ s, q = s + 5 := ⟨q - 5, by lia⟩
    push_cast
    have hs : (0:ℝ) ≤ s := by positivity
    have hh : (0:ℝ) ≤ h := by positivity
    have e : 2 * (((s:ℝ) + 5 + 4) ^ 2 - 3 * ((s:ℝ) + 5 + 4) - 1) * (h:ℝ) ^ 3 +
        2 * (((s:ℝ) + 5 + 4) ^ 3 - 6 * ((s:ℝ) + 5 + 4) ^ 2 - 4 * ((s:ℝ) + 5 + 4) - 3) * (h:ℝ) ^ 2 +
        (2 * ((s:ℝ) + 5 + 4) ^ 4 - 16 * ((s:ℝ) + 5 + 4) ^ 3 - 7 * ((s:ℝ) + 5 + 4) ^ 2 -
          5 * ((s:ℝ) + 5 + 4) - 4) * (h:ℝ) +
        ((s:ℝ) + 5 + 4) * ((s:ℝ) + 5 + 4 + 1) *
          (((s:ℝ) + 5 + 4) ^ 3 - 7 * ((s:ℝ) + 5 + 4) ^ 2 + 2 * ((s:ℝ) + 5 + 4) - 2) =
        2*h^3*s^2 + 30*h^3*s + 106*h^3 + 2*h^2*s^3 + 42*h^2*s^2 + 262*h^2*s + 408*h^2 +
        2*h*s^4 + 56*h*s^3 + 533*h*s^2 + 1813*h*s + 842*h + s^5 + 39*s^4 + 589*s^3 +
        4239*s^2 + 14092*s + 16020 := by ring
    rw [e]
    positivity

private lemma ratioQ_pos (q h : ℕ) (hn : 36 ≤ q + 4 + h) : 0 < ratioQ ((q : ℝ) + 4) (h : ℝ) := by
  unfold ratioQ
  have hh : (1:ℝ) ≤ h ∨ (1:ℝ) ≤ q := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · right; exact_mod_cast (show 1 ≤ q by lia)
    · left; exact_mod_cast h0
  have e : 4 * (h:ℝ) ^ 3 + 12 * (h:ℝ) ^ 2 + 2 * ((q:ℝ) + 4 - 2) * (((q:ℝ) + 4) ^ 2 -
      3 * ((q:ℝ) + 4) - 2) * h + ((q:ℝ) + 4) * ((q:ℝ) + 4 - 4) * ((q:ℝ) + 4 - 1) * ((q:ℝ) + 4 + 1) =
      4*h^3 + 12*h^2 + 2*h*q^3 + 14*h*q^2 + 24*h*q + 8*h + q^4 + 12*q^3 + 47*q^2 + 60*q := by ring
  rw [e]
  rcases hh with hh | hh
  · have : (0:ℝ) ≤ q := by positivity
    positivity
  · have : 0 ≤ 4*(h:ℝ)^3 + 12*h^2 + 2*h*q^3 + 14*h*q^2 + 24*h*q + 8*h + q^4 + 12*q^3 +
        47*q^2 := by positivity
    linarith

/-- **Proposition (moment ratio).** For `n ≥ 36` and `4 ≤ r ≤ n`,
`(n - r + 2) η_{n,r} < r η_{n,r-1}`. -/
private theorem eta_ratio (n r : ℕ) (hn : 36 ≤ n) (hr4 : 4 ≤ r) (hrn : r ≤ n) :
    ((n : ℝ) - r + 2) * eta n r < (r : ℝ) * eta n (r - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 4 := ⟨r - 4, by lia⟩
  obtain ⟨h, rfl⟩ : ∃ h, n = q + 4 + h := ⟨n - (q + 4), by lia⟩
  have hid := ratio_identity (q + 4 + h) q (by lia)
  simp only [show q + 4 - 1 = q + 3 by lia]
  have hP := ratioP_pos q h hn
  have hQ := ratioQ_pos q h hn
  have hI := Imom_nonneg (q + 4 + h) (q + 3) (by lia)
  have hE := Emom_pos (q + 4 + h) (q + 1) (by lia)
  push_cast at hid ⊢
  have eh : ((q:ℝ) + 4 + h - ((q:ℝ) + 4)) = h := by ring
  rw [eh] at hid
  have hrhs : 0 < 2 * ratioP ((q:ℝ) + 4) h * Imom (q + 4 + h) (q + 3) +
      ((q:ℝ) + 3) * ((q:ℝ) + 2) * ratioQ ((q:ℝ) + 4) h * Emom (q + 4 + h) (q + 1) := by
    have : 0 ≤ 2 * ratioP ((q:ℝ) + 4) h * Imom (q + 4 + h) (q + 3) := by positivity
    have : 0 < ((q:ℝ) + 3) * ((q:ℝ) + 2) * ratioQ ((q:ℝ) + 4) h * Emom (q + 4 + h) (q + 1) := by
      positivity
    linarith
  rw [← hid] at hrhs
  have hc : 0 < 2 * ((q:ℝ) + 4 + h + 1) * (2 * ((q:ℝ) + 4 + h) - ((q:ℝ) + 4)) *
      (2 * ((q:ℝ) + 4 + h) - ((q:ℝ) + 4) + 1) ^ 2 := by
    have : (0:ℝ) ≤ q := by positivity
    have : (0:ℝ) ≤ h := by positivity
    have : 0 < 2 * ((q:ℝ) + 4 + h) - ((q:ℝ) + 4) := by linarith
    positivity
  have := pos_of_mul_pos_right hrhs hc.le
  linarith

end Eta

section Coeff

/-! ## The coefficient identity (Lemma `lem:moments` and the binomial expansion of `M̃_n`)

`L(d(n))_{n-j} = d_n(n)^2 N_{n,j} ∑_{r ≤ j} C(j,r) η_{n,r}`.
-/

open MvPolynomial

private lemma mu_closed (n r : ℕ) (hr : r ≤ 2 * n) :
    mu n r * ((2 * n).factorial : ℝ) * (r.factorial : ℝ) * 4 ^ r =
      ((2 * r).factorial : ℝ) * ((2 * n - r).factorial : ℝ) := by
  induction r with
  | zero => simp [mu_zero]
  | succ r ih =>
    have ih := ih (by lia)
    rw [mu_succ]
    have h1 : (2 * n - r).factorial = (2 * n - r) * (2 * n - (r + 1)).factorial := by
      rw [show 2 * n - r = (2 * n - (r + 1)) + 1 by lia, Nat.factorial_succ]
    have h2 : (2 * (r + 1)).factorial = (2 * r + 2) * ((2 * r + 1) * (2 * r).factorial) := by
      rw [show 2 * (r + 1) = (2 * r + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    rw [h1] at ih
    rw [h2, Nat.factorial_succ]
    have hc : ((2 * n - r : ℕ) : ℝ) = 4 * (n:ℝ) / 2 - r := by
      rw [Nat.cast_sub (by lia)]; push_cast; ring
    rw [Nat.cast_mul, hc] at ih
    have hne : (4 * (n:ℝ) - 2 * r) ≠ 0 := by
      have : (r:ℝ) + 1 ≤ 2 * n := by exact_mod_cast hr
      linarith
    push_cast at ih ⊢
    rw [pow_succ]
    field_simp
    field_simp at ih
    linear_combination (2:ℝ) * ih

private lemma choose_cast (a b : ℕ) (h : b ≤ a) :
    (a.choose b : ℝ) = (a.factorial : ℝ) / ((b.factorial : ℝ) * ((a - b).factorial : ℝ)) :=
  Nat.cast_choose ℝ h

/-- The termwise identity behind `c_{n,j} = C(n,j) m_{n,j}`. -/
private lemma rev_term (n j r : ℕ) (hr : r ≤ j) (hj : j ≤ n) :
    ((2 * r).choose r : ℝ) * ((2 * n - r).choose n : ℝ) * ((n - r).choose (n - j) : ℝ) =
      ((2 * n).choose n : ℝ) * (n.choose j : ℝ) * (j.choose r : ℝ) * (4 ^ r * mu n r) := by
  have hm := mu_closed n r (by lia)
  have hmu : 4 ^ r * mu n r = ((2 * r).factorial : ℝ) * ((2 * n - r).factorial : ℝ) /
      (((2 * n).factorial : ℝ) * (r.factorial : ℝ)) := by
    rw [eq_div_iff (by positivity)]; linear_combination hm
  rw [hmu, choose_cast _ _ (by lia), choose_cast _ _ (by lia), choose_cast _ _ (by lia),
    choose_cast _ _ (by lia), choose_cast _ _ (by lia), choose_cast _ _ (by lia)]
  rw [show 2 * r - r = r by lia, show 2 * n - r - n = n - r by lia,
    show n - r - (n - j) = j - r by lia, show 2 * n - n = n by lia]
  field_simp

/-- `d_{n-j}(n) = d_n(n) C(n,j) m_{n,j}`. -/
private lemma bmCoeff_rev (n j : ℕ) (hj : j ≤ n) :
    bmCoeff n (n - j) = bmCoeff n n * (n.choose j : ℝ) * mom n j := by
  have hdn : bmCoeff n n = (1/4 : ℝ) ^ n * (2 ^ n * ((2 * n).choose n : ℝ)) := by
    simp [bmCoeff, two_mul]
  have hre : ∑ k ∈ Finset.Icc (n - j) n, (2 : ℝ) ^ k * ((2 * n - 2 * k).choose (n - k) : ℝ) *
      ((n + k).choose n : ℝ) * (k.choose (n - j) : ℝ) =
      ∑ r ∈ Finset.range (j + 1), (2 : ℝ) ^ (n - r) *
          ((2 * n - 2 * (n - r)).choose (n - (n - r)) : ℝ) *
      ((n + (n - r)).choose n : ℝ) * ((n - r).choose (n - j) : ℝ) := by
    symm
    apply Finset.sum_nbij' (fun r => n - r) (fun k => n - k)
    · intro r hr; simp at hr ⊢; lia
    · intro k hk; simp at hk ⊢; lia
    · intro r hr; simp at hr ⊢; lia
    · intro k hk; simp at hk ⊢; lia
    · intro r hr; rfl
  rw [hdn]
  unfold bmCoeff
  rw [hre]
  unfold mom
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mem_range] at hr
  have ht := rev_term n j r (by lia) hj
  rw [show 2 * n - 2 * (n - r) = 2 * r by lia, show n - (n - r) = r by lia,
    show n + (n - r) = 2 * n - r by lia]
  have h2 : (2:ℝ) ^ (n - r) * 2 ^ r = 2 ^ n := by rw [← pow_add]; congr 1; lia
  have h4 : (4:ℝ) ^ r = 2 ^ r * 2 ^ r := by rw [← mul_pow]; norm_num
  rw [h4] at ht
  linear_combination ((1/4:ℝ) ^ n * (2 : ℝ) ^ (n - r)) * ht + ((1/4:ℝ) ^ n *
    ((2 * n).choose n : ℝ) * (n.choose j : ℝ) * (j.choose r : ℝ) * (2 ^ r * mu n r)) * h2

/-- `Λ_{n,j} = m_j^2 - (j(n-j)/(n+1)) (m_{j+1} m_{j-1} - m_j^2)`. -/
private noncomputable def Lam (n j : ℕ) : ℝ :=
  mom n j ^ 2 - ((j:ℝ) * ((n:ℝ) - j) / ((n:ℝ) + 1)) * (mom n (j+1) * mom n (j-1) - mom n j ^ 2)

private lemma mom_zero (n : ℕ) : mom n 0 = 1 := by simp [mom, mu_zero]

private lemma narC_mul (n j : ℕ) (hj : j ≤ n) :
    narC n j * ((j : ℝ) + 1) * ((n : ℝ) - j + 1) = (n.choose j : ℝ) ^ 2 * ((n : ℝ) + 1) := by
  have h := Nat.choose_mul_succ_eq n j
  have h' : ((n.choose j : ℕ) : ℝ) * ((n:ℝ) + 1) = ((n+1).choose j : ℝ) * ((n:ℝ) - j + 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) h
    simp only [Nat.cast_mul] at this
    rw [Nat.cast_sub (by lia)] at this
    push_cast at this
    linarith
  unfold narC
  field_simp
  linear_combination (-(n.choose j : ℝ)) * h'

/-- `L(d(n))_{n-j} = d_n(n)^2 N_{n,j} Λ_{n,j}`. -/
private lemma bmL_eq_Lam (n j : ℕ) (hj : j ≤ n) :
    bmL n (n - j) = bmCoeff n n ^ 2 * narC n j * Lam n j := by
  unfold bmL Lam
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [bmCoeff_succ_self, narC, mom_zero]
  rcases Nat.eq_or_lt_of_le hj with rfl | hjn
  · simp only [Nat.sub_self, ite_true, zero_mul, sub_zero, narC_self, mul_one]
    rw [show (0:ℕ) = j - j from (Nat.sub_self j).symm, bmCoeff_rev j j le_rfl]
    simp
    ring
  · rw [ite_eq_right (by lia)]
    rw [show n - j - 1 = n - (j + 1) by lia, show n - j + 1 = n - (j - 1) by lia,
      bmCoeff_rev n j hj, bmCoeff_rev n (j+1) (by lia), bmCoeff_rev n (j-1) (by lia)]
    have hN := narC_mul n j hj
    have hb : ((n.choose (j+1) : ℕ) : ℝ) * ((j:ℝ) + 1) = (n.choose j : ℝ) * ((n:ℝ) - j) := by
      have := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq n j)
      simp only [Nat.cast_mul] at this
      rw [Nat.cast_sub (by lia)] at this
      push_cast at this
      linarith
    have hc : (n.choose j : ℝ) * (j:ℝ) = ((n.choose (j-1) : ℕ) : ℝ) * ((n:ℝ) - j + 1) := by
      have := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq n (j-1))
      simp only [Nat.cast_mul] at this
      rw [Nat.cast_sub (by lia), show j - 1 + 1 = j by lia] at this
      rw [Nat.cast_sub (by lia)] at this
      push_cast at this
      linarith
    have hj1 : (0:ℝ) < (j:ℝ) + 1 := by positivity
    have hj2 : (0:ℝ) < (n:ℝ) - j + 1 := by
      have : (j:ℝ) ≤ n := by exact_mod_cast hj
      linarith
    have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
    set a := (n.choose j : ℝ)
    set c := ((n.choose (j+1) : ℕ) : ℝ)
    set e := ((n.choose (j-1) : ℕ) : ℝ)
    set N := narC n j
    set d := bmCoeff n n
    -- `N = a^2 (n+1)/((j+1)(n-j+1))`
    have hNa : N = a ^ 2 * ((n:ℝ) + 1) / (((j:ℝ) + 1) * ((n:ℝ) - j + 1)) := by
      rw [eq_div_iff (by positivity)]; linarith
    have hca : c = a * ((n:ℝ) - j) / ((j:ℝ) + 1) := by
      rw [eq_div_iff hj1.ne']; linarith
    have hea : e = a * j / ((n:ℝ) - j + 1) := by
      rw [eq_div_iff hj2.ne']; linarith
    rw [hNa, hca, hea]
    field_simp
    ring

private lemma tt_add_one : tt + 1 = xx * yy := by simp [tt]

private lemma xxyy_pow_eq (i : ℕ) : (xx * yy) ^ i =
    ∑ s ∈ Finset.range (i + 1), C ((i.choose s : ℕ) : ℝ) * tt ^ s := by
  rw [← tt_add_one, add_pow]
  apply Finset.sum_congr rfl
  intro s _
  rw [one_pow, mul_one, map_natCast, mul_comm]

private lemma sum_choose_Imom (n j : ℕ) :
    ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) * Imom n r = mom n j ^ 2 := by
  have h := congrArg (Lm n) (xxyy_pow_eq j)
  rw [mul_pow, Lm_xx_yy, map_sum] at h
  simp only [Lm_C_mul] at h
  unfold Imom
  rw [← h]; ring

private lemma sum_choose_Emom (n i : ℕ) :
    ∑ s ∈ Finset.range (i + 1), (i.choose s : ℝ) * Emom n s =
      2 * mom n (i + 2) * mom n i - 2 * mom n (i + 1) ^ 2 := by
  have h := congrArg (fun p => Lm n (ee * p)) (xxyy_pow_eq i)
  simp only [Finset.mul_sum, map_sum] at h
  have e : ee * (xx * yy) ^ i = xx ^ (i+2) * yy ^ i + xx ^ i * yy ^ (i+2) -
      C 2 * (xx ^ (i+1) * yy ^ (i+1)) := by
    rw [map_ofNat]; simp only [ee]; ring
  rw [e, map_sub, map_add, Lm_C_mul, Lm_xx_yy, Lm_xx_yy, Lm_xx_yy] at h
  unfold Emom
  rw [show (∑ s ∈ Finset.range (i + 1), (i.choose s : ℝ) * Lm n (ee * tt ^ s)) =
      ∑ s ∈ Finset.range (i + 1), Lm n (ee * (C ((i.choose s : ℕ) : ℝ) * tt ^ s)) by
    apply Finset.sum_congr rfl; intro s _
    rw [mul_left_comm, Lm_C_mul], ← h]
  ring

private lemma choose_term (n i s : ℕ) (hs : s ≤ i) :
    (((i + 1).choose (s + 1) : ℕ) : ℝ) * ((s : ℝ) + 1) * ((n : ℝ) - (s + 1)) -
      (((i + 1).choose (s + 2) : ℕ) : ℝ) * ((s : ℝ) + 2) * ((s : ℝ) + 2 - 1) =
      ((i : ℝ) + 1) * ((n : ℝ) - (i + 1)) * (i.choose s : ℝ) := by
  have h1 := congrArg (fun x : ℕ => (x : ℝ)) (Nat.add_one_mul_choose_eq i s)
  have h2 := congrArg (fun x : ℕ => (x : ℝ)) (Nat.add_one_mul_choose_eq i (s+1))
  have h3 := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq i s)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h1 h2 h3
  rw [Nat.cast_sub hs] at h3
  linear_combination ((n:ℝ) - (s + 1)) * (-h1) + ((s:ℝ) + 1) * h2 - ((i:ℝ) + 1) * h3

private lemma sum_choose_E_terms (n j : ℕ) :
    ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) * ((r : ℝ) *
      (((n : ℝ) - r) * Emom n (r - 1) - ((r : ℝ) - 1) * Emom n (r - 2))) =
      (j : ℝ) * ((n : ℝ) - j) * (2 * mom n (j + 1) * mom n (j-1) - 2 * mom n j ^ 2) := by
  rcases j with _ | i
  · simp
  have hE := sum_choose_Emom n i
  simp only [Nat.add_sub_cancel]
  rw [show i + 1 + 1 = i + 2 by ring] at *
  simp only [mul_sub, Finset.sum_sub_distrib]
  -- first sum
  have hA : ∑ r ∈ Finset.range (i + 2), (((i+1).choose r : ℕ) : ℝ) * ((r:ℝ) * (((n:ℝ) - r) *
      Emom n (r - 1))) = ∑ s ∈ Finset.range (i + 1), (((i+1).choose (s+1) : ℕ) : ℝ) *
      ((s:ℝ) + 1) * ((n:ℝ) - (s + 1)) * Emom n s := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
    apply Finset.sum_congr rfl; intro s _; push_cast; ring
  have hB : ∑ r ∈ Finset.range (i + 2), (((i+1).choose r : ℕ) : ℝ) * ((r:ℝ) * (((r:ℝ) - 1) *
      Emom n (r - 2))) = ∑ s ∈ Finset.range (i + 1), (((i+1).choose (s+2) : ℕ) : ℝ) *
      ((s:ℝ) + 2) * ((s:ℝ) + 2 - 1) * Emom n s := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ _ i,
      Nat.choose_eq_zero_of_lt (show i + 1 < i + 2 by lia)]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.cast_one, sub_self, zero_add]
    apply Finset.sum_congr rfl; intro s _
    rw [show s + 1 + 1 = s + 2 by ring, show s + 2 - 2 = s by lia]; push_cast; ring
  rw [hA, hB, ← Finset.sum_sub_distrib]
  rw [show ∑ s ∈ Finset.range (i + 1), ((((i+1).choose (s+1) : ℕ) : ℝ) *
      ((s:ℝ) + 1) * ((n:ℝ) - (s + 1)) * Emom n s - (((i+1).choose (s+2) : ℕ) : ℝ) *
      ((s:ℝ) + 2) * ((s:ℝ) + 2 - 1) * Emom n s) =
      ((i:ℝ) + 1) * ((n:ℝ) - (i + 1)) * ∑ s ∈ Finset.range (i + 1), (i.choose s : ℝ) * Emom n s by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s hs
    simp only [Finset.mem_range] at hs
    have := choose_term n i s (by lia)
    linear_combination (Emom n s) * this]
  rw [hE]
  push_cast
  ring

/-- Binomial expansion: `∑_{r ≤ j} C(j,r) η_{n,r} = Λ_{n,j}`. -/
private lemma sum_choose_eta (n j : ℕ) :
    ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) * eta n r = Lam n j := by
  have h1 := sum_choose_Imom n j
  have h2 := sum_choose_E_terms n j
  have hn : (2 * ((n:ℝ) + 1)) ≠ 0 := by positivity
  unfold eta Lam
  have : ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) * (Imom n r - ((r:ℝ) / (2 * ((n:ℝ) + 1))) *
      (((n:ℝ) - r) * Emom n (r - 1) - ((r:ℝ) - 1) * Emom n (r - 2))) =
      ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) * Imom n r - (1 / (2 * ((n:ℝ) + 1))) *
      ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) * ((r:ℝ) *
      (((n:ℝ) - r) * Emom n (r - 1) - ((r:ℝ) - 1) * Emom n (r - 2))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro r _; ring
  rw [this, h1, h2]
  field_simp

/-- **Coefficient identity.** `L(d(n))_{n-j} = d_n(n)^2 N_{n,j} ∑_{r ≤ j} C(j,r) η_{n,r}`. -/
theorem bmL_eq_eta (n j : ℕ) (hj : j ≤ n) :
    bmL n (n - j) = bmCoeff n n ^ 2 * narC n j *
      ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) * eta n r := by
  rw [sum_choose_eta, bmL_eq_Lam n j hj]

end Coeff

section Shape

/-! ## The weights `b_j = η_{n,j+1} n^{\underline j}/(j+1)!` (Lemma `lem:weight-shape`)
-/

/-- The weights `b_j = η_{n,j+1} C(n,j)/(j+1) = η_{n,j+1} n^{\underline j}/(j+1)!`. -/
noncomputable def bw (n j : ℕ) : ℝ :=
  eta n (j+1) * (n.descFactorial j : ℝ) / ((j+1).factorial : ℝ)

private lemma mu_three (n : ℕ) : mu n 3 = 1 / (4 * (n : ℝ)) * (3 / (4 * (n : ℝ) - 2)) *
    (5 / (4 * (n : ℝ) - 4)) := by
  rw [mu_succ, mu_two]; norm_num

private lemma mu_four (n : ℕ) : mu n 4 = 1 / (4 * (n : ℝ)) * (3 / (4 * (n : ℝ) - 2)) *
    (5 / (4 * (n : ℝ) - 4)) * (7 / (4 * (n : ℝ) - 6)) := by
  rw [mu_succ, mu_three]; norm_num

private lemma mom_one (n : ℕ) : mom n 1 = 1 + 2 * mu n 1 := by
  simp [mom, Finset.sum_range_succ, mu_zero]
private lemma mom_two (n : ℕ) : mom n 2 = 1 + 4 * mu n 1 + 4 * mu n 2 := by
  simp [mom, Finset.sum_range_succ, mu_zero]; norm_num
private lemma mom_three (n : ℕ) : mom n 3 = 1 + 6 * mu n 1 + 12 * mu n 2 + 8 * mu n 3 := by
  simp [mom, Finset.sum_range_succ, mu_zero, Nat.choose]; norm_num
private lemma mom_four (n : ℕ) : mom n 4 =
    1 + 8 * mu n 1 + 24 * mu n 2 + 32 * mu n 3 + 16 * mu n 4 := by
  simp [mom, Finset.sum_range_succ, mu_zero, Nat.choose]; norm_num

private lemma Lam_one (n : ℕ) : Lam n 1 = mom n 1 ^ 2 -
    (((n : ℝ) - 1) / ((n : ℝ) + 1)) * (mom n 2 - mom n 1 ^ 2) := by
  simp only [Lam]; norm_num [mom_zero]
private lemma Lam_two (n : ℕ) : Lam n 2 = mom n 2 ^ 2 -
    (2 * ((n : ℝ) - 2) / ((n : ℝ) + 1)) * (mom n 3 * mom n 1 - mom n 2 ^ 2) := by
  simp only [Lam]; norm_num
private lemma Lam_three (n : ℕ) : Lam n 3 = mom n 3 ^ 2 -
    (3 * ((n : ℝ) - 3) / ((n : ℝ) + 1)) * (mom n 4 * mom n 2 - mom n 3 ^ 2) := by
  simp only [Lam]; norm_num

private lemma eta_one_rec (n : ℕ) : eta n 1 = Lam n 1 - 1 := by
  have := sum_choose_eta n 1
  simp [Finset.sum_range_succ, eta_zero] at this
  linarith
private lemma eta_two_rec (n : ℕ) : eta n 2 = Lam n 2 - 2 * eta n 1 - 1 := by
  have := sum_choose_eta n 2
  simp [Finset.sum_range_succ, eta_zero] at this
  linarith
private lemma eta_three_rec (n : ℕ) : eta n 3 = Lam n 3 - 3 * eta n 2 - 3 * eta n 1 - 1 := by
  have := sum_choose_eta n 3
  simp [Finset.sum_range_succ, eta_zero, Nat.choose] at this
  linarith

private lemma eta_one_eq (n : ℕ) (hn : 36 ≤ n) :
    eta n 1 = (4 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1) * (2 * (n : ℝ) - 1)) := by
  have hn' : (36:ℝ) ≤ n := by exact_mod_cast hn
  rw [eta_one_rec, Lam_one, mom_one, mom_two, mu_one, mu_two]
  have h1 : (4 * (n:ℝ) - 2) ≠ 0 := by linarith
  have h2 : (2 * (n:ℝ) - 1) ≠ 0 := by linarith
  have h3 : (n:ℝ) ≠ 0 := by linarith
  field_simp
  ring

private lemma eta_two_eq (n : ℕ) (hn : 36 ≤ n) :
    eta n 2 = (4 * (n : ℝ) + 1) * (8 * (n : ℝ) ^ 3 - 9 * (n : ℝ) ^ 2 + 13 * n - 3) /
      (4 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) * ((n : ℝ) + 1) * (2 * (n : ℝ) - 1) ^ 2) := by
  have hn' : (36:ℝ) ≤ n := by exact_mod_cast hn
  rw [eta_two_rec, eta_one_eq n hn, Lam_two, mom_one, mom_two, mom_three, mu_one, mu_two, mu_three]
  have h1 : (4 * (n:ℝ) - 2) ≠ 0 := by linarith
  have h2 : (2 * (n:ℝ) - 1) ≠ 0 := by linarith
  have h3 : (n:ℝ) ≠ 0 := by linarith
  have h5 : ((n:ℝ) - 1) ≠ 0 := by linarith
  have h6 : ((n:ℝ) + 1) ≠ 0 := by linarith
  have h2' : (n:ℝ) * 2 - 1 ≠ 0 := by linarith
  rw [show 4 * (n:ℝ) - 2 = 2 * (2 * n - 1) by ring, show 4 * (n:ℝ) - 4 = 4 * (n - 1) by ring]
  field_simp
  ring

private lemma eta_three_eq (n : ℕ) (hn : 36 ≤ n) :
    eta n 3 = 3 * (4 * (n : ℝ) - 1) * (4 * (n : ℝ) + 1) *
        (8 * (n : ℝ) ^ 3 - 19 * (n : ℝ) ^ 2 + 48 * n - 27) /
      (8 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) ^ 2 * ((n : ℝ) + 1) * (2 * (n : ℝ) - 3) * (2 * (n : ℝ) - 1) ^
          2) := by
  have hn' : (36:ℝ) ≤ n := by exact_mod_cast hn
  rw [eta_three_rec, eta_two_eq n hn, eta_one_eq n hn, Lam_three, mom_two, mom_three, mom_four,
    mu_one, mu_two, mu_three, mu_four]
  have h1 : (4 * (n:ℝ) - 2) ≠ 0 := by linarith
  have h2 : (2 * (n:ℝ) - 1) ≠ 0 := by linarith
  have h3 : (n:ℝ) ≠ 0 := by linarith
  have h5 : ((n:ℝ) - 1) ≠ 0 := by linarith
  have h7 : (2 * (n:ℝ) - 3) ≠ 0 := by linarith
  have h8 : ((n:ℝ) + 1) ≠ 0 := by linarith
  have h2' : (n:ℝ) * 2 - 1 ≠ 0 := by linarith
  have h7' : (n:ℝ) * 2 - 3 ≠ 0 := by linarith
  rw [show 4 * (n:ℝ) - 2 = 2 * (2 * n - 1) by ring, show 4 * (n:ℝ) - 4 = 4 * (n - 1) by ring,
    show 4 * (n:ℝ) - 6 = 2 * (2 * n - 3) by ring]
  field_simp
  ring

private lemma bw_zero (n : ℕ) : bw n 0 = eta n 1 := by simp [bw]
private lemma bw_one (n : ℕ) : bw n 1 = eta n 2 * (n : ℝ) / 2 := by simp [bw]
private lemma bw_two (n : ℕ) (hn : 1 ≤ n) : bw n 2 = eta n 3 * ((n : ℝ) * ((n : ℝ) - 1)) / 6 := by
  simp only [bw, Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial, Nat.sub_zero]
  push_cast [Nat.cast_sub hn]
  ring

private lemma bw_pos (n j : ℕ) (hj : j < n) : 0 < bw n j := by
  unfold bw
  have := eta_pos n (j+1) (by lia) (by lia)
  have : 0 < (n.descFactorial j : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 (by lia)
  positivity

/-- **Weight shape**, part 1: `b_1 ≤ b_2`. -/
private lemma bw_one_le_two (n : ℕ) (hn : 36 ≤ n) : bw n 1 ≤ bw n 2 := by
  have hn' : (36:ℝ) ≤ n := by exact_mod_cast hn
  have key : bw n 2 - bw n 1 = 3 * (4 * (n:ℝ) + 1) * (5 * (n:ℝ) - 1) * (7 * (n:ℝ) - 3) /
      (16 * (n:ℝ) * ((n:ℝ) - 1) * ((n:ℝ) + 1) * (2 * (n:ℝ) - 3) * (2 * (n:ℝ) - 1) ^ 2) := by
    rw [bw_two n (by lia), bw_one, eta_two_eq n hn, eta_three_eq n hn]
    have h2' : (n:ℝ) * 2 - 1 ≠ 0 := by linarith
    have h7' : (n:ℝ) * 2 - 3 ≠ 0 := by linarith
    have h2 : 2 * (n:ℝ) - 1 ≠ 0 := by linarith
    have h7 : 2 * (n:ℝ) - 3 ≠ 0 := by linarith
    have h3 : (n:ℝ) ≠ 0 := by linarith
    have h5 : ((n:ℝ) - 1) ≠ 0 := by linarith
    have h8 : ((n:ℝ) + 1) ≠ 0 := by linarith
    field_simp
    ring
  have hA : 0 < 3 * (4 * (n:ℝ) + 1) * (5 * (n:ℝ) - 1) * (7 * (n:ℝ) - 3) := by
    have a1 : 0 < 4 * (n:ℝ) + 1 := by linarith
    have a2 : 0 < 5 * (n:ℝ) - 1 := by linarith
    have a3 : 0 < 7 * (n:ℝ) - 3 := by linarith
    positivity
  have hB : 0 < 16 * (n:ℝ) * ((n:ℝ) - 1) * ((n:ℝ) + 1) * (2 * (n:ℝ) - 3) *
      (2 * (n:ℝ) - 1) ^ 2 := by
    have a1 : 0 < (n:ℝ) - 1 := by linarith
    have a2 : 0 < 2 * (n:ℝ) - 3 := by linarith
    have a3 : 0 < 2 * (n:ℝ) - 1 := by linarith
    positivity
  have := div_pos hA hB
  linarith

/-- **Weight shape**, part 2: `(b_1 - b_0) + 3 (b_2 - b_1) ≤ b_2 / 3`. -/
private lemma bw_shape (n : ℕ) (hn : 36 ≤ n) :
    (bw n 1 - bw n 0) + 3 * (bw n 2 - bw n 1) ≤ bw n 2 / 3 := by
  have hn' : (36:ℝ) ≤ n := by exact_mod_cast hn
  have key : bw n 2 / 3 - ((bw n 1 - bw n 0) + 3 * (bw n 2 - bw n 1)) =
      (4 * (n:ℝ) - 1) * (4 * (n:ℝ) + 1) * ((n:ℝ) ^ 2 - 3 * n - 27) /
      (12 * (n:ℝ) * ((n:ℝ) - 1) * ((n:ℝ) + 1) * (2 * (n:ℝ) - 3) * (2 * (n:ℝ) - 1)) := by
    rw [bw_two n (by lia), bw_one, bw_zero, eta_one_eq n hn, eta_two_eq n hn, eta_three_eq n hn]
    have h2' : (n:ℝ) * 2 - 1 ≠ 0 := by linarith
    have h7' : (n:ℝ) * 2 - 3 ≠ 0 := by linarith
    have h2 : 2 * (n:ℝ) - 1 ≠ 0 := by linarith
    have h7 : 2 * (n:ℝ) - 3 ≠ 0 := by linarith
    have h3 : (n:ℝ) ≠ 0 := by linarith
    have h5 : ((n:ℝ) - 1) ≠ 0 := by linarith
    have h8 : ((n:ℝ) + 1) ≠ 0 := by linarith
    field_simp
    ring
  have hA : 0 < (4 * (n:ℝ) - 1) * (4 * (n:ℝ) + 1) * ((n:ℝ) ^ 2 - 3 * n - 27) := by
    have a1 : 0 < 4 * (n:ℝ) - 1 := by linarith
    have a2 : 0 < 4 * (n:ℝ) + 1 := by linarith
    have a3 : 0 < (n:ℝ) ^ 2 - 3 * n - 27 := by nlinarith
    positivity
  have hB : 0 < 12 * (n:ℝ) * ((n:ℝ) - 1) * ((n:ℝ) + 1) * (2 * (n:ℝ) - 3) *
      (2 * (n:ℝ) - 1) := by
    have a1 : 0 < (n:ℝ) - 1 := by linarith
    have a2 : 0 < 2 * (n:ℝ) - 3 := by linarith
    have a3 : 0 < 2 * (n:ℝ) - 1 := by linarith
    positivity
  have := div_pos hA hB
  linarith

/-- **Weight shape**, part 3: `b_j < b_{j-1}` for `3 ≤ j < n`. -/
private lemma bw_decr (n j : ℕ) (hn : 36 ≤ n) (hj3 : 3 ≤ j) (hjn : j < n) : bw n j < bw n
    (j - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by lia⟩
  simp only [Nat.add_sub_cancel]
  have hr := eta_ratio n (k + 2) hn (by lia) (by lia)
  simp only [show k + 2 - 1 = k + 1 by lia] at hr
  unfold bw
  rw [Nat.descFactorial_succ, Nat.factorial_succ (k+1)]
  have hd : 0 < (n.descFactorial k : ℝ) := by exact_mod_cast Nat.descFactorial_pos.2 (by lia)
  have hf : 0 < ((k+1).factorial : ℝ) := by positivity
  push_cast [Nat.cast_sub (show k ≤ n by lia)]
  push_cast at hr
  rw [div_lt_div_iff₀ (by positivity) hf]
  have : ((n:ℝ) - (k + 2) + 2) * eta n (k + 2) < ((k:ℝ) + 2) * eta n (k + 1) := hr
  have e : ((n:ℝ) - (k + 2) + 2) = (n:ℝ) - k := by ring
  rw [e] at this
  have := mul_lt_mul_of_pos_right this (mul_pos hd hf)
  nlinarith

end Shape

section PartialSums

/-! ## The polynomials `A_{n,k}`, the partial sums `V_{n,k}` and the remainders `R_{n,k}`

`A_{n,0} = 1`, `A_{n,-1} = 0`,
`A_{n,k+1} = (2w - (k+2)/(n-k) (1-w)) A_{n,k} - w A_{n,k-1}`,
`V_{n,k} = ∑_{j<k} A_{n,j}` and
`R_{n,k} = ((n-k+1) A_{n,k} - w (n-k) A_{n,k-1}) / (n+1)`.
-/

open Polynomial

/-- The polynomials `A_{n,k}(w)`. -/
noncomputable def Apoly (n : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C 2 * X - C (2 / (n : ℝ)) * (1 - X)
  | (k + 2) => (C 2 * X - C (((k : ℝ) + 3) / ((n : ℝ) - ((k : ℝ) + 1))) * (1 - X)) * Apoly n (k + 1)
      - X * Apoly n k

/-- `A_{n,k-1}` with `A_{n,-1} = 0`. -/
private noncomputable def Aprev (n k : ℕ) : ℝ[X] := if k = 0 then 0 else Apoly n (k - 1)

/-- The normalized remainders `R_{n,k}(w)` (boundary form). -/
noncomputable def Rpoly (n k : ℕ) : ℝ[X] :=
  C (1 / ((n:ℝ) + 1)) * (C ((n:ℝ) - k + 1) * Apoly n k - C ((n:ℝ) - k) * X * Aprev n k)

/-- The partial sums `V_{n,k}(w) = ∑_{j<k} A_{n,j}(w)`. -/
private noncomputable def Vpoly (n k : ℕ) : ℝ[X] := ∑ j ∈ Finset.range k, Apoly n j

private lemma Apoly_succ (n k : ℕ) : Apoly n (k + 1) =
    (C 2 * X - C (((k : ℝ) + 2) / ((n : ℝ) - k)) * (1 - X)) * Apoly n k - X * Aprev n k := by
  rcases k with _ | k
  · simp [Apoly, Aprev]
  · simp only [Apoly, Aprev, ite_eq_right (Nat.succ_ne_zero k), Nat.add_sub_cancel]
    push_cast
    ring_nf

private lemma Apoly_succ_eval (n k : ℕ) (x : ℝ) : (Apoly n (k + 1)).eval x =
    (2 * x - (((k : ℝ) + 2) / ((n : ℝ) - k)) * (1 - x)) * (Apoly n k).eval x
      - x * (Aprev n k).eval x := by
  rw [Apoly_succ]; simp

private lemma Aprev_succ (n k : ℕ) : Aprev n (k + 1) = Apoly n k := by simp [Aprev]

private lemma Rpoly_eval (n k : ℕ) (x : ℝ) : (Rpoly n k).eval x =
    (((n : ℝ) - k + 1) * (Apoly n k).eval x - ((n : ℝ) - k) * x * (Aprev n k).eval x) /
      ((n : ℝ) + 1) := by
  simp [Rpoly]; ring

private lemma Rpoly_zero (n : ℕ) : Rpoly n 0 = 1 := by
  have h : ((n:ℝ) + 1) ≠ 0 := by positivity
  apply Polynomial.funext; intro x
  rw [Rpoly_eval]; simp [Aprev, Apoly, h]

private lemma Rpoly_one_eval (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    (Rpoly n 1).eval x = (((n : ℝ) + 3) * x - 2) / ((n : ℝ) + 1) := by
  rw [Rpoly_eval]
  simp only [Aprev, Apoly, one_ne_zero, ite_false, eval_one, eval_sub, eval_mul,
    eval_C, eval_X, show Apoly n 0 = 1 from rfl]
  have : (n:ℝ) ≠ 0 := by have : (1:ℝ) ≤ n := by exact_mod_cast hn
                         linarith
  push_cast
  field_simp
  ring

/-- The three-term recurrence for `R_{n,k}` (evaluated). -/
private lemma Rpoly_rec_eval (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) (x : ℝ) :
    ((n : ℝ) - k + 1) * (Rpoly n (k + 1)).eval x =
      ((2 * (n : ℝ) - k + 3) * x - k - 2) * (Rpoly n k).eval x
        - ((n : ℝ) - k) * x * (Rpoly n (k-1)).eval x := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
  simp only [Nat.add_sub_cancel]
  rw [Rpoly_eval, Rpoly_eval, Rpoly_eval, Aprev_succ, Aprev_succ]
  have h1 := Apoly_succ_eval n (j+1) x
  have h2 := Apoly_succ_eval n j x
  rw [Aprev_succ] at h1
  have hnk : ((n:ℝ) - ((j+1:ℕ):ℝ)) ≠ 0 := by
    have : ((j+1:ℕ):ℝ) < n := by exact_mod_cast hkn
    linarith
  have hnk' : ((n:ℝ) - (j:ℝ)) ≠ 0 := by
    have : ((j+1:ℕ):ℝ) < n := by exact_mod_cast hkn
    push_cast at this; linarith
  have hn1 : ((n:ℝ) + 1) ≠ 0 := by positivity
  push_cast at h1 h2 hnk ⊢
  rw [h1]
  linear_combination (norm := (field_simp; ring))
    (-((n:ℝ) - ((j:ℝ)+1)) * ((n:ℝ) - ((j:ℝ)+1) + 1) * x / ((n:ℝ) + 1)) * h2

/-- `R_{n,k+1} - R_{n,k} = -((n+3)/(n+1)) (1-w) A_{n,k}` (evaluated), for `k < n`. -/
private lemma Rpoly_succ_sub_eval (n k : ℕ) (hkn : k < n) (x : ℝ) :
    (Rpoly n (k + 1)).eval x - (Rpoly n k).eval x =
      -(((n : ℝ) + 3) / ((n : ℝ) + 1)) * (1 - x) * (Apoly n k).eval x := by
  rw [Rpoly_eval, Rpoly_eval, Aprev_succ, Apoly_succ_eval]
  have hnk : ((n:ℝ) - k) ≠ 0 := by
    have : (k:ℝ) < n := by exact_mod_cast hkn
    linarith
  have hn1 : ((n:ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `(n+3)(1-w) V_{n,k} = (n+1)(1 - R_{n,k})` (evaluated), for `k ≤ n`. -/
private lemma Vpoly_eval (n k : ℕ) (hkn : k ≤ n) (x : ℝ) :
    ((n : ℝ) + 3) * (1 - x) * (Vpoly n k).eval x = ((n : ℝ) + 1) * (1 - (Rpoly n k).eval x) := by
  induction k with
  | zero => simp [Vpoly, Rpoly_zero]
  | succ k ih =>
    have ih := ih (by lia)
    have hs := Rpoly_succ_sub_eval n k (by lia) x
    have hn1 : ((n:ℝ) + 1) ≠ 0 := by positivity
    simp only [Vpoly, Finset.sum_range_succ, eval_add] at ih ⊢
    rw [eval_finsetSum] at ih ⊢
    have : (Rpoly n (k+1)).eval x = (Rpoly n k).eval x -
        (((n:ℝ) + 3) / ((n:ℝ) + 1)) * (1 - x) * (Apoly n k).eval x := by linarith
    rw [this, mul_add, ih]
    field_simp
    ring

private lemma Apoly_eval_one (n k : ℕ) : (Apoly n k).eval 1 = (k : ℝ) + 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · simp [Apoly]
    · rw [Apoly_succ_eval]
      rcases k with _ | k
      · simp [Aprev, Apoly]; norm_num
      · rw [ih (k+1) (by lia), Aprev_succ, ih k (by lia)]
        push_cast; ring

private lemma Rpoly_eval_one (n k : ℕ) : (Rpoly n k).eval 1 = 1 := by
  rw [Rpoly_eval, Apoly_eval_one]
  have hn1 : ((n:ℝ) + 1) ≠ 0 := by positivity
  rcases k with _ | k
  · simp [Aprev, hn1]
  · rw [Aprev_succ, Apoly_eval_one]; push_cast; field_simp; ring

/-- `R_{n,n} = A_{n,n} / (n + 1)`. -/
lemma Rpoly_self (n : ℕ) : Rpoly n n = C (1 / ((n : ℝ) + 1)) * Apoly n n := by
  simp [Rpoly]

/-- The remainders at `u` satisfy the recurrence of `RRec`. -/
private lemma rrec_Rpoly (n : ℕ) (hn : 1 ≤ n) (u : ℝ) : RRec n u (fun k => (Rpoly n k).eval u) :=
  ⟨by simp [Rpoly_zero], Rpoly_one_eval n hn u, fun j hj1 hjn => Rpoly_rec_eval n j hj1 hjn u⟩

/-! ### Degrees and leading coefficients -/

private lemma lin_natDegree (a b : ℝ) : (C a * X - C b * (1 - X)).natDegree ≤ 1 := by
  compute_degree

private lemma Apoly_natDegree (n k : ℕ) : (Apoly n k).natDegree ≤ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · simp [Apoly]
    · rw [Apoly_succ]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_mul_le).trans ?_
        have := ih k (by lia)
        have := lin_natDegree 2 (((k:ℝ) + 2) / ((n:ℝ) - k))
        lia
      · rcases k with _ | k
        · simp [Aprev]
        · rw [Aprev_succ]
          refine (natDegree_mul_le).trans ?_
          have := ih k (by lia)
          have : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
          lia

private lemma Aprev_natDegree (n k : ℕ) : (Aprev n k).natDegree + 1 ≤ k ∨ Aprev n k = 0 := by
  rcases k with _ | k
  · right; simp [Aprev]
  · left; rw [Aprev_succ]; have := Apoly_natDegree n k; lia

private lemma Rpoly_natDegree (n k : ℕ) : (Rpoly n k).natDegree ≤ k := by
  unfold Rpoly
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_C_mul_le _ _).trans (Apoly_natDegree n k)
  · rcases Aprev_natDegree n k with h | h
    · rw [mul_assoc]
      refine (natDegree_C_mul_le _ _).trans ?_
      refine (natDegree_mul_le).trans ?_
      have : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
      lia
    · simp [h]

/-- Polynomial form of the recurrence. -/
private lemma Rpoly_rec (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    C ((n : ℝ) - k + 1) * Rpoly n (k + 1) =
      (C (2 * (n : ℝ) - k + 3) * X - C ((k : ℝ) + 2)) * Rpoly n k
        - C ((n : ℝ) - k) * X * Rpoly n (k-1) := by
  apply Polynomial.funext
  intro x
  have := Rpoly_rec_eval n k hk1 hkn x
  simp only [eval_mul, eval_C, eval_sub, eval_X]
  linear_combination this

private lemma Rpoly_coeff_succ (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    (Rpoly n (k + 1)).coeff (k + 1) =
      ((2 * (n : ℝ) - k + 3) / ((n : ℝ) - k + 1)) * (Rpoly n k).coeff k := by
  have h := congrArg (fun p => p.coeff (k+1)) (Rpoly_rec n k hk1 hkn)
  simp only [coeff_C_mul, coeff_sub, mul_assoc, coeff_X_mul, sub_mul, coeff_C_mul] at h
  have h1 : (Rpoly n k).coeff (k+1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by have := Rpoly_natDegree n k; lia)
  have h2 : (Rpoly n (k-1)).coeff k = 0 :=
    coeff_eq_zero_of_natDegree_lt (by have := Rpoly_natDegree n (k-1); lia)
  rw [h1, h2] at h
  have hnk : ((n:ℝ) - k + 1) ≠ 0 := by
    have : (k:ℝ) < n := by exact_mod_cast hkn
    linarith
  field_simp
  linear_combination h

private lemma Rpoly_coeff_one (n : ℕ) (hn : 1 ≤ n) :
    (Rpoly n 1).coeff 1 = ((n : ℝ) + 3) / ((n : ℝ) + 1) := by
  have : Rpoly n 1 = C (((n:ℝ) + 3) / ((n:ℝ) + 1)) * X - C (2 / ((n:ℝ) + 1)) := by
    apply Polynomial.funext; intro x
    rw [Rpoly_one_eval n hn]; simp; ring
  rw [this]; simp

end PartialSums

section Gauss

/-! ## Jacobi-type polynomials and a Gauss–Lagrange identity

We use the explicit polynomials
`Y_{n,k}(w) = ∑_s C(n+1,s) C(n-k+1,s+2) (w-1)^s w^{n-1-s}`
(these are `w^k P^{(2,k+2)}_{n-k-1}(2w-1)`), which satisfy the same three-term recurrence as
the remainders `R_{n,k}`, and the polynomial
`J_n(w) = ∑_i N_{n,i} w^i (w-1)^{n-i}` whose zeros are the images `x/(x-1)` of the zeros `x`
of the Narayana polynomial.  Instead of Gaussian quadrature we use Lagrange interpolation
(`Lagrange.coeff_eq_sum`), which gives the same identity.
-/

open Polynomial

/-- Coefficients `C(n+1,s) C(n-k+1,s+2)`. -/
private noncomputable def gc (n k s : ℕ) : ℝ :=
    ((n + 1).choose s : ℝ) * ((n - k + 1).choose (s + 2) : ℝ)

/-- The generating polynomial `G_{n,k}(z) = ∑_s gc n k s z^s`. -/
private noncomputable def Gpoly (n k : ℕ) : ℝ[X] := ∑ s ∈ Finset.range (n + 1), C (gc n k s) * X ^ s

private lemma gc_eq_zero (n k s : ℕ) (hs : n - k ≤ s) : gc n k s = 0 := by
  unfold gc; rw [Nat.choose_eq_zero_of_lt (show n - k + 1 < s + 2 by lia)]; simp

private lemma coeff_Gpoly (n k s : ℕ) : (Gpoly n k).coeff s = gc n k s := by
  unfold Gpoly
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · simp at h; rw [gc_eq_zero]; lia

/-- The key binomial identity behind the three-term recurrence. -/
private lemma gc_rec (n k s : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    ((n : ℝ) - k + 1) * (gc n (k + 1) (s + 1) - gc n (k + 1) s) =
      (2 * (n : ℝ) - 2 * k + 1) * gc n k (s + 1) + ((k : ℝ) + 2) * gc n k s
        - ((n : ℝ) - k) * gc n (k-1) (s + 1) := by
  -- notation: `a = n - k + 1`, `m = a - 1 = n - k`
  obtain ⟨m, hm⟩ : ∃ m, n - k = m := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by lia
  have e1 : n - (k+1) + 1 = m := by lia
  have e2 : n - k + 1 = m + 1 := by lia
  have e3 : n - (k-1) + 1 = m + 2 := by lia
  unfold gc
  rw [e1, e2, e3]
  have hmr : ((m:ℕ):ℝ) = (n:ℝ) - k := by
    rw [← hm]; push_cast [Nat.cast_sub hkn.le]; ring
  set p := ((n+1).choose (s+1) : ℝ)
  set p' := ((n+1).choose s : ℝ)
  set x := (m.choose (s+1) : ℝ)
  set y := (m.choose (s+2) : ℝ)
  set z := (m.choose (s+3) : ℝ)
  have P1 : ((m+1).choose (s+2) : ℝ) = x + y := by
    simp only [x, y]; rw [Nat.choose_succ_succ]; push_cast; ring
  have P2 : ((m+1).choose (s+3) : ℝ) = y + z := by
    simp only [y, z]; rw [Nat.choose_succ_succ]; push_cast; ring
  have P3 : ((m+2).choose (s+3) : ℝ) = ((m+1).choose (s+2) : ℝ) + ((m+1).choose (s+3) : ℝ) := by
    rw [show m + 2 = (m+1) + 1 by ring, Nat.choose_succ_succ]; push_cast; ring
  have A1 : ((s:ℝ) + 2) * y = ((m:ℝ) - (s + 1)) * x := by
    simp only [x, y]
    have := Nat.choose_succ_right_eq m (s+1)
    rcases le_or_gt (s+1) m with h | h
    · have := congrArg (fun t : ℕ => (t:ℝ)) this
      push_cast [Nat.cast_sub h] at this
      linarith
    · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by lia)]; simp
  have A2 : ((s:ℝ) + 1) * p = ((n:ℝ) + 1 - s) * p' := by
    simp only [p, p']
    have := Nat.choose_succ_right_eq (n+1) s
    rcases le_or_gt s (n+1) with h | h
    · have := congrArg (fun t : ℕ => (t:ℝ)) this
      push_cast [Nat.cast_sub h] at this
      linarith
    · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by lia)]; simp
  rw [P3, P1, P2]
  rw [← hmr]
  have hs2 : (0:ℝ) < (s:ℝ) + 2 := by positivity
  have key : ((s:ℝ) + 2) * ((((m:ℝ) + 1) * (p * z - p' * y)) -
      ((2 * (m:ℝ) + 1) * (p * (y + z)) + (((n:ℝ) + 3 - ((m:ℝ) + 1)) * (p' * (x + y)))
        - (m:ℝ) * (p * (x + y + (y + z))))) = 0 := by
    linear_combination (-(p + ((n:ℝ) + 3) * p')) * A1 + ((m:ℝ) + 1) * x * A2
  have : (((m:ℝ) + 1) * (p * z - p' * y)) -
      ((2 * (m:ℝ) + 1) * (p * (y + z)) + (((n:ℝ) + 3 - ((m:ℝ) + 1)) * (p' * (x + y)))
        - (m:ℝ) * (p * (x + y + (y + z)))) = 0 := by
    rcases mul_eq_zero.1 key with h | h
    · linarith
    · exact h
  have hk : (k:ℝ) = (n:ℝ) - m := by rw [hmr]; ring
  rw [hk]
  linear_combination this

private lemma gc_rec0 (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    ((n : ℝ) - k + 1) * gc n (k + 1) 0 =
      (2 * (n : ℝ) - 2 * k + 1) * gc n k 0 - ((n : ℝ) - k) * gc n (k-1) 0 := by
  obtain ⟨m, hm⟩ : ∃ m, n - k = m := ⟨_, rfl⟩
  have e1 : n - (k+1) + 1 = m := by lia
  have e2 : n - k + 1 = m + 1 := by lia
  have e3 : n - (k-1) + 1 = m + 2 := by lia
  unfold gc
  rw [e1, e2, e3]
  have hmr : ((m:ℕ):ℝ) = (n:ℝ) - k := by
    rw [← hm]; push_cast [Nat.cast_sub hkn.le]; ring
  have P1 : ((m+1).choose 2 : ℝ) = m + (m.choose 2 : ℝ) := by
    rw [Nat.choose_succ_succ]; push_cast; simp
  have P2 : ((m+2).choose 2 : ℝ) = (m + 1) + ((m+1).choose 2 : ℝ) := by
    rw [show m + 2 = (m+1) + 1 by ring, Nat.choose_succ_succ]; push_cast; simp
  rw [P2, P1, ← hmr]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, zero_add]
  have hk : (k:ℝ) = (n:ℝ) - m := by rw [hmr]; ring
  rw [hk]; ring

/-- The recurrence for the generating polynomials. -/
private lemma Gpoly_rec (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    C ((n : ℝ) - k + 1) * ((1 - X) * Gpoly n (k + 1)) =
      (C (2 * (n : ℝ) - 2 * k + 1) + C ((k : ℝ) + 2) * X) * Gpoly n k
        - C ((n : ℝ) - k) * Gpoly n (k-1) := by
  ext s
  rcases s with _ | s
  · simp only [coeff_C_mul, coeff_sub, sub_mul, one_mul, add_mul, coeff_add, mul_assoc,
      coeff_X_mul_zero, coeff_Gpoly]
    simp only [mul_zero, add_zero, sub_zero]
    linear_combination gc_rec0 n k hk1 hkn
  · simp only [coeff_C_mul, coeff_sub, sub_mul, one_mul, add_mul, coeff_add, mul_assoc,
      coeff_X_mul, coeff_Gpoly]
    linear_combination gc_rec n k s hk1 hkn

/-- `Q_{n,k}(w) = ∑_{s < n-k} gc n k s (w-1)^s w^{n-1-k-s}`. -/
private noncomputable def Qpoly (n k : ℕ) : ℝ[X] :=
  ∑ s ∈ Finset.range (n - k), C (gc n k s) * (X - 1) ^ s * X ^ (n - 1 - k - s)

/-- `Y_{n,k}(w) = w^k Q_{n,k}(w)`. -/
private noncomputable def Ypoly (n k : ℕ) : ℝ[X] := X ^ k * Qpoly n k

private lemma Ypoly_eval (n k : ℕ) (hk : k ≤ n) (w : ℝ) (hw : w ≠ 0) :
    (Ypoly n k).eval w = w ^ (n - 1) * (Gpoly n k).eval ((w - 1) / w) := by
  unfold Ypoly Qpoly Gpoly
  simp only [eval_mul, eval_pow, eval_X, eval_finsetSum, eval_C, eval_sub, eval_one]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_range_add_sum_Ico _ (show n - k ≤ n + 1 by lia)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (n - k) (n + 1)) (fun s hs => by
    rw [gc_eq_zero n k s (Finset.mem_Ico.1 hs).1]; simp), add_zero]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s < n - k := Finset.mem_range.1 hs
  rw [div_pow]
  have : w ^ (n - 1) = w ^ k * w ^ (n - 1 - k - s) * w ^ s := by
    rw [← pow_add, ← pow_add]; congr 1; lia
  rw [this]
  field_simp

private lemma Qpoly_natDegree (n k : ℕ) : (Qpoly n k).natDegree ≤ n - 1 - k := by
  unfold Qpoly
  apply natDegree_sum_le_of_forall_le
  intro s hs
  have hs' : s < n - k := Finset.mem_range.1 hs
  refine (natDegree_mul_le).trans ?_
  refine (Nat.add_le_add_right (natDegree_C_mul_le _ _) _).trans ?_
  refine (Nat.add_le_add (natDegree_pow_le) (natDegree_pow_le)).trans ?_
  have h1 : (X - 1 : ℝ[X]).natDegree ≤ 1 := by compute_degree
  have h2 : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
  have := Nat.mul_le_mul_left s h1
  have := Nat.mul_le_mul_left (n - 1 - k - s) h2
  lia

private lemma Qpoly_coeff_top (n k : ℕ) (hk : k < n) :
    (Qpoly n k).coeff (n - 1 - k) = (Gpoly n k).eval 1 := by
  unfold Qpoly Gpoly
  rw [finsetSum_coeff, eval_finsetSum]
  rw [← Finset.sum_range_add_sum_Ico _ (show n - k ≤ n + 1 by lia)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (n - k) (n + 1)) (fun s hs => by
    rw [gc_eq_zero n k s (Finset.mem_Ico.1 hs).1]; simp), add_zero]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s < n - k := Finset.mem_range.1 hs
  simp only [eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
  rw [mul_assoc, coeff_C_mul]
  have e : (X - 1 : ℝ[X]) = X - C 1 := by simp
  rw [e]
  have hm1 : ((X - C 1 : ℝ[X]) ^ s).Monic := (monic_X_sub_C 1).pow s
  have hm2 : ((X : ℝ[X]) ^ (n - 1 - k - s)).Monic := monic_X_pow _
  have hd : ((X - C 1 : ℝ[X]) ^ s * X ^ (n - 1 - k - s)).natDegree = n - 1 - k := by
    rw [hm1.natDegree_mul hm2, natDegree_pow, natDegree_X_sub_C, natDegree_X_pow]; lia
  have h3 := (hm1.mul hm2).coeff_natDegree
  rw [hd] at h3
  rw [h3, mul_one]

private lemma Gpoly_eval_one_rec (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    ((n : ℝ) - k) * (Gpoly n (k-1)).eval 1 = (2 * (n : ℝ) - k + 3) * (Gpoly n k).eval 1 := by
  have := congrArg (eval 1) (Gpoly_rec n k hk1 hkn)
  simp only [eval_mul, eval_C, eval_sub, eval_one, eval_add, eval_X, sub_self, zero_mul,
    mul_zero] at this
  linear_combination this

private lemma Gpoly_eval_one_last (n : ℕ) (hn : 1 ≤ n) : (Gpoly n (n-1)).eval 1 = 1 := by
  unfold Gpoly
  rw [eval_finsetSum, Finset.sum_eq_single 0]
  · simp [gc, show n - (n-1) + 1 = 2 by lia]
  · intro s _ hs
    rw [gc_eq_zero n (n-1) s (by lia)]; simp
  · simp

/-- The polynomial `J_n(w) = ∑_i N_{n,i} w^i (w-1)^{n-i}`. -/
noncomputable def Jpoly (n : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (n + 1), C (narC n i) * X ^ i * (X - 1) ^ (n - i)

private lemma narC_identity (n s : ℕ) (hs : s < n) :
    ((n : ℝ) - s) * narC n (n - s) + ((s : ℝ) + 1) * narC n (n - 1 - s) =
      (((n : ℝ) + 3) / ((n : ℝ) + 1)) * gc n 0 s := by
  unfold narC gc
  rw [Nat.choose_symm_of_eq_add (show n = (n - s) + s by lia),
    Nat.choose_symm_of_eq_add (show n + 1 = (n - s) + (s + 1) by lia),
    Nat.choose_symm_of_eq_add (show n = (n - 1 - s) + (s + 1) by lia),
    Nat.choose_symm_of_eq_add (show n + 1 = (n - 1 - s) + (s + 2) by lia),
    show n - 0 + 1 = n + 1 by lia]
  have hs' : (s:ℝ) + 1 ≤ n := by exact_mod_cast hs
  have r1 := Nat.choose_mul_succ_eq n s
  have r2 := Nat.choose_succ_right_eq (n+1) s
  have r3 := Nat.choose_succ_right_eq n s
  have r4 := Nat.choose_succ_right_eq (n+1) (s+1)
  have c1 : ((n.choose s : ℕ) : ℝ) = ((n+1).choose s) * ((n:ℝ) + 1 - s) / ((n:ℝ) + 1) := by
    rw [eq_div_iff (by positivity)]
    have := congrArg (fun t : ℕ => (t:ℝ)) r1
    push_cast [Nat.cast_sub (show s ≤ n + 1 by lia)] at this; linarith
  have c2 : (((n+1).choose (s+1) : ℕ) : ℝ) = ((n+1).choose s) * ((n:ℝ) + 1 - s) / ((s:ℝ) + 1) := by
    rw [eq_div_iff (by positivity)]
    have := congrArg (fun t : ℕ => (t:ℝ)) r2
    push_cast [Nat.cast_sub (show s ≤ n + 1 by lia)] at this; linarith
  have c3 : ((n.choose (s+1) : ℕ) : ℝ) = (n.choose s) * ((n:ℝ) - s) / ((s:ℝ) + 1) := by
    rw [eq_div_iff (by positivity)]
    have := congrArg (fun t : ℕ => (t:ℝ)) r3
    push_cast [Nat.cast_sub (show s ≤ n by lia)] at this; linarith
  have c4 : (((n+1).choose (s+2) : ℕ) : ℝ) = ((n+1).choose (s+1)) * ((n:ℝ) - s) / ((s:ℝ) + 2) := by
    rw [eq_div_iff (by positivity)]
    have := congrArg (fun t : ℕ => (t:ℝ)) r4
    rw [show s + 1 + 1 = s + 2 from rfl, show n + 1 - (s + 1) = n - s by lia] at this
    push_cast [Nat.cast_sub hs.le] at this; linarith
  have e1 : ((n - 1 - s : ℕ) : ℝ) = (n:ℝ) - 1 - s := by
    rw [Nat.cast_sub (by lia), Nat.cast_sub (by lia)]; simp
  have e2 : ((n - s : ℕ) : ℝ) = (n:ℝ) - s := by rw [Nat.cast_sub hs.le]
  rw [e1, e2, c4, c3, c2, c1]
  have h1 : (n:ℝ) - s ≠ 0 := by linarith
  have h2 : (n:ℝ) - s + 1 ≠ 0 := by linarith
  have h3 : (n:ℝ) - 1 - s + 1 ≠ 0 := by linarith
  field_simp
  ring

private lemma X_sub_one_eq : (X - 1 : ℝ[X]) = X - C 1 := by simp

private lemma Jpoly_derivative (n : ℕ) :
    derivative (Jpoly n) = C (((n : ℝ) + 3) / ((n : ℝ) + 1)) * Ypoly n 0 := by
  unfold Jpoly Ypoly Qpoly
  simp only [pow_zero, one_mul, Nat.sub_zero, X_sub_one_eq]
  rw [derivative_sum]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_pow,
    derivative_X_sub_C_pow]
  simp only [Finset.sum_add_distrib]
  have S1 : ∑ i ∈ Finset.range (n + 1), C (narC n i) * (C (i:ℝ) * X ^ (i - 1)) *
      (X - C 1) ^ (n - i) = ∑ s ∈ Finset.range n,
        C (((n:ℝ) - s) * narC n (n - s)) * (X - C 1) ^ s * X ^ (n - 1 - s) := by
    rw [← Finset.sum_range_reflect, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero, C_0, zero_mul, mul_zero,
      add_zero]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : s < n := Finset.mem_range.1 hs
    rw [show n - (n - s) = s by lia, show n - s - 1 = n - 1 - s by lia,
      Nat.cast_sub hs'.le, C_mul]
    ring
  have S2 : ∑ i ∈ Finset.range (n + 1), C (narC n i) * X ^ i *
      (C ((n - i : ℕ) : ℝ) * (X - C 1) ^ (n - i - 1)) = ∑ s ∈ Finset.range n,
        C (((s:ℝ) + 1) * narC n (n - 1 - s)) * (X - C 1) ^ s * X ^ (n - 1 - s) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, C_0, zero_mul, mul_zero, add_zero]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : s < n := Finset.mem_range.1 hs
    rw [show n - (n - 1 - s) - 1 = s by lia, show n - (n - 1 - s) = s + 1 by lia, C_mul]
    push_cast
    ring
  rw [S1, S2, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s < n := Finset.mem_range.1 hs
  rw [← add_mul, ← add_mul, ← C_add, narC_identity n s hs', C_mul]
  ring

end Gauss

section GaussBound

/-! ## The Gaussian bound (Proposition `prop:gaussian-bound` of Xie–Zhang)

If `U` is the set of the `n` zeros of `J_n` in `(0,1)` and `R_{n,n}` vanishes on `U`, then for
every `u ∈ U` and `1 ≤ k < n`,
`R_{n,k}(u)^2 ≤ ((n+3)/(n+1)) (n-k+1)(n-k)/(2n-k+3) u^k`.
-/

open Polynomial

/-- The recurrence for `Y_{n,k}` at a nonzero point. -/
private lemma Ypoly_rec_eval (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) (w : ℝ) (hw : w ≠ 0) :
    ((n : ℝ) - k + 1) * (Ypoly n (k + 1)).eval w =
      ((2 * (n : ℝ) - k + 3) * w - k - 2) * (Ypoly n k).eval w
        - ((n : ℝ) - k) * w * (Ypoly n (k-1)).eval w := by
  have h := congrArg (eval ((w - 1) / w)) (Gpoly_rec n k hk1 hkn)
  simp only [eval_mul, eval_C, eval_sub, eval_one, eval_add, eval_X] at h
  rw [Ypoly_eval n (k+1) (by lia) w hw, Ypoly_eval n k (by lia) w hw,
    Ypoly_eval n (k-1) (by lia) w hw]
  have hn1 : 1 ≤ n := by lia
  have e : w ^ (n - 1) * w = w ^ n := by rw [← pow_succ]; congr 1; lia
  have h1 : (1 - (w - 1) / w) = 1 / w := by field_simp; ring
  rw [h1] at h
  have := congrArg (fun t => t * w ^ n) h
  beta_reduce at this
  rw [← e] at this
  field_simp at this
  linear_combination w ^ (n - 1) * this

private lemma Qpoly_self (n : ℕ) : Qpoly n n = 0 := by simp [Qpoly]

private lemma Ypoly_last_eval (n : ℕ) (hn : 1 ≤ n) (w : ℝ) : (Ypoly n (n-1)).eval w =
    w ^ (n - 1) := by
  unfold Ypoly Qpoly
  rw [show n - (n-1) = 1 by lia]
  simp [gc, show n - (n-1) + 1 = 2 by lia]

/-- Backward uniqueness: at a zero `u ≠ 0` of `R_{n,n}`, the remainders are proportional to
the `Y_{n,k}`. -/
private lemma Rpoly_eq_Y_ratio (n : ℕ) (hn : 2 ≤ n) (u : ℝ) (hu : u ≠ 0)
    (hR : (Rpoly n n).eval u = 0) :
    (Ypoly n 0).eval u ≠ 0 ∧
      ∀ k ≤ n, (Rpoly n k).eval u = (Ypoly n k).eval u / (Ypoly n 0).eval u := by
  set r : ℕ → ℝ := fun k => (Rpoly n k).eval u
  set y : ℕ → ℝ := fun k => (Ypoly n k).eval u
  set D : ℕ → ℝ := fun k => r k * y (n-1) - y k * r (n-1)
  have hyn : y n = 0 := by simp [y, Ypoly, Qpoly_self]
  have hD : ∀ t, t ≤ n - 1 → D (n - 1 - t) = 0 ∧ D (n - t) = 0 := by
    intro t ht
    induction t with
    | zero =>
      refine ⟨by simp only [D, Nat.sub_zero]; ring, ?_⟩
      simp only [D, Nat.sub_zero]
      rw [show r n = 0 from hR, hyn]; ring
    | succ t ih =>
      obtain ⟨h1, h2⟩ := ih (by lia)
      refine ⟨?_, by rw [show n - (t+1) = n - 1 - t by lia]; exact h1⟩
      -- recurrence at `k = n - 1 - t`
      set k := n - 1 - t with hk
      have hk1 : 1 ≤ k := by lia
      have hkn : k < n := by lia
      have er := Rpoly_rec_eval n k hk1 hkn u
      have ey := Ypoly_rec_eval n k hk1 hkn u hu
      have hD1 : D (k+1) = 0 := by rw [show k + 1 = n - t by lia]; exact h2
      have hrec : ((n:ℝ) - k) * u * D (k-1) =
          ((2 * (n:ℝ) - k + 3) * u - k - 2) * D k - ((n:ℝ) - k + 1) * D (k+1) := by
        simp only [D, r, y]
        linear_combination (Polynomial.eval u (Ypoly n (n-1))) * er
          - (Polynomial.eval u (Rpoly n (n-1))) * ey
      rw [h1, hD1] at hrec
      have hnk : ((n:ℝ) - k) * u ≠ 0 := by
        apply mul_ne_zero _ hu
        have : (k:ℝ) < n := by exact_mod_cast hkn
        linarith
      rw [show n - 1 - (t + 1) = k - 1 by lia]
      have : ((n:ℝ) - k) * u * D (k-1) = 0 := by rw [hrec]; ring
      exact (mul_eq_zero.1 this).resolve_left hnk
  have hyl : y (n-1) = u ^ (n-1) := Ypoly_last_eval n (by lia) u
  have hyl0 : y (n-1) ≠ 0 := by rw [hyl]; exact pow_ne_zero _ hu
  have hD0 : D 0 = 0 := by
    have := (hD (n-1) le_rfl).1; rwa [Nat.sub_self] at this
  have hr0 : r 0 = 1 := by simp [r, Rpoly_zero]
  have hy0 : y 0 ≠ 0 := by
    intro h0
    simp only [D, hr0, h0] at hD0
    apply hyl0; linarith
  refine ⟨hy0, fun k hk => ?_⟩
  have hDk : D k = 0 := by
    rcases Nat.eq_or_lt_of_le hk with rfl | hk'
    · simpa using (hD 0 (by lia)).2
    · have := (hD (n - 1 - k) (by lia)).1; rwa [show n - 1 - (n - 1 - k) = k by lia] at this
  have hrn : r (n-1) = y (n-1) / y 0 := by
    simp only [D, hr0] at hD0
    field_simp; linarith
  change r k = y k / y 0
  simp only [D] at hDk
  rw [hrn] at hDk
  field_simp at hDk ⊢
  apply mul_right_cancel₀ hyl0
  linarith

private lemma Jpoly_eval_one (n : ℕ) : (Jpoly n).eval 1 = 1 := by
  unfold Jpoly
  rw [eval_finsetSum, Finset.sum_eq_single n]
  · simp [narC_self]
  · intro i hi hin
    have : i < n := by simp at hi; lia
    simp [zero_pow (show n - i ≠ 0 by lia)]
  · simp

private lemma Jpoly_natDegree (n : ℕ) : (Jpoly n).natDegree ≤ n := by
  unfold Jpoly
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hi' : i ≤ n := by simp at hi; lia
  refine (natDegree_mul_le).trans ?_
  refine (Nat.add_le_add_right (natDegree_C_mul_le _ _) _).trans ?_
  refine (Nat.add_le_add (natDegree_pow_le) (natDegree_pow_le)).trans ?_
  have h1 : (X - 1 : ℝ[X]).natDegree ≤ 1 := by compute_degree
  have h2 : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
  have := Nat.mul_le_mul_left (n - i) h1
  have := Nat.mul_le_mul_left i h2
  lia

/-- The product of the leading coefficients. -/
private lemma key_lc (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n) :
    (Rpoly n k).coeff k * (Gpoly n k).eval 1 =
      (Rpoly n n).coeff n * (((n : ℝ) - k + 1) * ((n : ℝ) - k) / (2 * (n : ℝ) - k + 3)) := by
  obtain ⟨t, rfl⟩ : ∃ t, k = n - 1 - t := ⟨n - 1 - k, by lia⟩
  induction t with
  | zero =>
    simp only [Nat.sub_zero] at *
    rw [Gpoly_eval_one_last n (by lia)]
    have h := Rpoly_coeff_succ n (n-1) hk1 (by lia)
    rw [show n - 1 + 1 = n by lia] at h
    rw [h]
    have hn : (1:ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hk1
    push_cast [Nat.cast_sub (show 1 ≤ n by lia)] at hn ⊢
    have h2 : (2:ℝ) * n - (n - 1) + 3 ≠ 0 := by linarith
    have h3 : (n:ℝ) - (n - 1) + 1 ≠ 0 := by linarith
    field_simp
    ring
  | succ t ih =>
    have ih := ih (by lia) (by lia)
    set k := n - 1 - (t + 1) with hk
    have e : n - 1 - t = k + 1 := by lia
    rw [e] at ih
    have hc := Rpoly_coeff_succ n k hk1 (by lia)
    have hg := Gpoly_eval_one_rec n (k+1) (by lia) (by lia)
    simp only [Nat.add_sub_cancel] at hg
    rw [hc] at ih
    push_cast at ih hg
    have hk' : (k:ℝ) + 2 ≤ n := by
      have : k + 2 ≤ n := by lia
      exact_mod_cast this
    have h1 : (n:ℝ) - (k + 1) ≠ 0 := by linarith
    have h2 : (n:ℝ) - k + 1 ≠ 0 := by linarith
    have h3 : 2 * (n:ℝ) - k + 3 ≠ 0 := by linarith
    have h4 : 2 * (n:ℝ) - (k + 1) + 3 ≠ 0 := by linarith
    have hG : (Gpoly n k).eval 1 = (2 * (n:ℝ) - (k + 1) + 3) / ((n:ℝ) - (k + 1)) *
        (Gpoly n (k+1)).eval 1 := by
      rw [div_mul_eq_mul_div, eq_div_iff h1]; linarith [hg]
    have ha : (Rpoly n k).coeff k * (Gpoly n (k+1)).eval 1 = (Rpoly n n).coeff n *
        (((n:ℝ) - (k + 1) + 1) * ((n:ℝ) - (k + 1)) / (2 * (n:ℝ) - (k + 1) + 3)) *
        (((n:ℝ) - k + 1) / (2 * (n:ℝ) - k + 3)) := by
      rw [← ih]; field_simp
    rw [hG, show (Rpoly n k).coeff k * ((2 * (n:ℝ) - (k + 1) + 3) / ((n:ℝ) - (k + 1)) *
        (Gpoly n (k+1)).eval 1) = ((2 * (n:ℝ) - (k + 1) + 3) / ((n:ℝ) - (k + 1))) *
        ((Rpoly n k).coeff k * (Gpoly n (k+1)).eval 1) by ring, ha]
    field_simp
    ring

open Classical in
/-- **Gaussian bound.** -/
private theorem gauss_bound (n : ℕ) (hn : 2 ≤ n) (U : Finset ℝ) (hcard : U.card = n)
    (hU : ∀ u ∈ U, 0 < u ∧ u < 1 ∧ (Jpoly n).eval u = 0 ∧ (Rpoly n n).eval u = 0)
    (u : ℝ) (hu : u ∈ U) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    (Rpoly n k).eval u ^ 2 ≤
      (((n : ℝ) + 3) / ((n : ℝ) + 1)) * (((n : ℝ) - k + 1) * ((n : ℝ) - k) / (2 * (n : ℝ) - k + 3))
          *
        u ^ k := by
  set c : ℝ := ((n:ℝ) + 3) / ((n:ℝ) + 1) with hc
  have hc0 : 0 < c := by positivity
  -- factorization of `J`
  have hJ0 : Jpoly n ≠ 0 := by
    intro h; have := Jpoly_eval_one n; rw [h] at this; simp at this
  have hle : U.val ≤ (Jpoly n).roots := by
    rw [Multiset.le_iff_subset U.nodup]
    intro v hv
    exact (mem_roots hJ0).2 (hU v hv).2.2.1
  have hcardr : (Jpoly n).roots.card = (Jpoly n).natDegree := by
    have h1 := Multiset.card_le_card hle
    have h2 := card_roots' (Jpoly n)
    have h3 := Jpoly_natDegree n
    simp only [Finset.card_val, hcard] at h1
    lia
  have hroots : (Jpoly n).roots = U.val := by
    symm
    apply Multiset.eq_of_le_of_card_le hle
    rw [hcardr]
    have := Jpoly_natDegree n
    simp [hcard, this]
  set lc := (Jpoly n).leadingCoeff with hlc
  have hlc0 : lc ≠ 0 := leadingCoeff_ne_zero.2 hJ0
  have hfac : Jpoly n = C lc * Lagrange.nodal U id := by
    rw [Lagrange.nodal, Finset.prod_eq_multiset_prod, ← hroots]
    exact (C_leadingCoeff_mul_prod_multiset_X_sub_C hcardr).symm
  have hJd : ∀ v ∈ U, (derivative (Jpoly n)).eval v = lc * ∏ w ∈ U.erase v, (v - w) := by
    intro v hv
    have h := Lagrange.eval_nodal_derivative_eval_node_eq (s := U) (v := id) hv
    simp only [id] at h
    rw [hfac, derivative_C_mul, eval_mul, eval_C, h, Lagrange.eval_nodal]
    simp
  -- `R_n = J`
  have hRJ : Rpoly n n = Jpoly n := by
    have h1U : (1:ℝ) ∉ U := fun h => by linarith [(hU 1 h).2.1]
    have := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (Rpoly n n - Jpoly n) (insert 1 U)
      (by
        intro v hv
        rcases Finset.mem_insert.1 hv with rfl | hv
        · simp [Rpoly_eval_one, Jpoly_eval_one]
        · simp [(hU v hv).2.2.1, (hU v hv).2.2.2])
      (by
        rw [Finset.card_insert_of_notMem h1U, hcard]
        have := natDegree_sub_le (Rpoly n n) (Jpoly n)
        have := Rpoly_natDegree n n
        have := Jpoly_natDegree n
        lia)
    exact sub_eq_zero.1 this
  have hlcR : lc = (Rpoly n n).coeff n := by
    rw [hlc, ← hRJ, leadingCoeff]
    congr 1
    have h := Rpoly_natDegree n n
    have : (Rpoly n n).natDegree = n := by
      rw [hRJ]
      have := Jpoly_natDegree n
      have := Multiset.card_le_card hle
      have := card_roots' (Jpoly n)
      simp only [Finset.card_val, hcard] at *
      lia
    exact this
  -- values at the nodes
  have hval : ∀ v ∈ U, (Rpoly n k).eval v ^ 2 / v ^ k =
      (c / lc) * ((Rpoly n k * Qpoly n k).eval v / ∏ w ∈ U.erase v, (v - w)) := by
    intro v hv
    obtain ⟨hv0, -, -, hvR⟩ := hU v hv
    obtain ⟨hY0, hR⟩ := Rpoly_eq_Y_ratio n hn v hv0.ne' hvR
    have hd := hJd v hv
    rw [Jpoly_derivative, eval_mul, eval_C] at hd
    have hprod : ∏ w ∈ U.erase v, (v - w) = c * (Ypoly n 0).eval v / lc := by
      rw [eq_div_iff hlc0, mul_comm]; exact hd.symm
    rw [hprod, eval_mul, hR k hkn.le]
    unfold Ypoly
    simp only [eval_mul, eval_pow, eval_X]
    have hv0' : v ≠ 0 := hv0.ne'
    have hY0' : (Ypoly n 0).eval v ≠ 0 := hY0
    unfold Ypoly at hY0'
    simp only [pow_zero, one_mul] at hY0' ⊢
    field_simp
  -- the Lagrange identity
  have hdeg : (Rpoly n k * Qpoly n k).degree < U.card := by
    rw [hcard]
    refine (degree_le_natDegree).trans_lt ?_
    have := natDegree_mul_le (p := Rpoly n k) (q := Qpoly n k)
    have := Rpoly_natDegree n k
    have := Qpoly_natDegree n k
    exact_mod_cast (show (Rpoly n k * Qpoly n k).natDegree < n by lia)
  have hlag := Lagrange.coeff_eq_sum (v := id) (Set.injOn_id _) hdeg
  simp only [id] at hlag
  rw [hcard, show n - 1 = k + (n - 1 - k) by lia,
    coeff_mul_add_eq_of_natDegree_le (Rpoly_natDegree n k) (Qpoly_natDegree n k),
    Qpoly_coeff_top n k hkn, key_lc n k hk1 (by lia)] at hlag
  have hsum : ∑ v ∈ U, (Rpoly n k).eval v ^ 2 / v ^ k =
      c * (((n:ℝ) - k + 1) * ((n:ℝ) - k) / (2 * (n:ℝ) - k + 3)) := by
    rw [Finset.sum_congr rfl hval, ← Finset.mul_sum, ← hlag, ← hlcR]
    field_simp
  have hterm : (Rpoly n k).eval u ^ 2 / u ^ k ≤ ∑ v ∈ U, (Rpoly n k).eval v ^ 2 / v ^ k :=
    Finset.single_le_sum (f := fun v => (Rpoly n k).eval v ^ 2 / v ^ k)
      (fun v hv => div_nonneg (sq_nonneg _) (pow_nonneg (hU v hv).1.le _)) hu
  rw [hsum] at hterm
  have hu0 : 0 < u ^ k := pow_pos (hU u hu).1 k
  rwa [div_le_iff₀ hu0] at hterm

end GaussBound

section AllZeros

/-! ## Partial sums at the zeros of `J_n` (Theorem `thm:all-zeros`) and the summation by parts
-/

open Polynomial

private lemma one_add_pow_ge (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    1 + k * t + ((k : ℝ) * ((k : ℝ) - 1) / 2) * t ^ 2 ≤ (1 + t) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ (1 + t)]
    push_cast
    have h0 : 0 ≤ (k:ℝ) * ((k:ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h]
      · have : (1:ℝ) ≤ k := by exact_mod_cast h
        nlinarith
    nlinarith [mul_nonneg h0 (pow_nonneg ht 3), mul_le_mul_of_nonneg_right ih
      (show (0:ℝ) ≤ 1 + t by linarith)]

/-- The estimate used with the Gaussian bound when `k > (n+3)u - 2`. -/
private lemma gauss_small (n k : ℕ) (hk3 : 3 ≤ k) (hkn : k < n) (hn : 36 ≤ n) (u : ℝ) (hu0 : 0 < u)
    (hu : ((n : ℝ) + 3) * u - 2 < k) :
    (((n : ℝ) + 3) / ((n : ℝ) + 1)) * (((n : ℝ) - k + 1) * ((n : ℝ) - k) / (2 * (n : ℝ) - k + 3)) *
      u ^ k < 1 / 4 := by
  set a : ℝ := (k:ℝ) + 2 with ha
  set b : ℝ := (n:ℝ) - k + 1 with hb
  have hk3' : (3:ℝ) ≤ k := by exact_mod_cast hk3
  have hkn' : (k:ℝ) + 1 ≤ n := by exact_mod_cast hkn
  have hn' : (36:ℝ) ≤ n := by exact_mod_cast hn
  have ha0 : 0 < a := by linarith
  have hb2 : 2 ≤ b := by linarith
  have hN : (n:ℝ) + 3 = a + b := by rw [ha, hb]; ring
  have hua : u ≤ a / (a + b) := by
    rw [le_div_iff₀ (by linarith)]; rw [← hN]; linarith
  -- `u^k ≤ (a/(a+b))^k ≤ 2 a^2 / (k(k-1) b^2)`
  have hpow : u ^ k ≤ (a / (a + b)) ^ k := pow_le_pow_left₀ hu0.le hua k
  have hbin := one_add_pow_ge (b / a) (by positivity) k
  have hprod : (a / (a + b)) ^ k * (1 + b / a) ^ k = 1 := by
    rw [← mul_pow]
    have : a / (a + b) * (1 + b / a) = 1 := by field_simp
    rw [this, one_pow]
  have hkk : 0 < (k:ℝ) * ((k:ℝ) - 1) / 2 := by
    have : 0 < (k:ℝ) - 1 := by linarith
    positivity
  have hq : (a / (a + b)) ^ k * (((k:ℝ) * ((k:ℝ) - 1) / 2) * (b / a) ^ 2) ≤ 1 := by
    have : 0 ≤ (k:ℝ) * (b / a) := by positivity
    have h1 : ((k:ℝ) * ((k:ℝ) - 1) / 2) * (b / a) ^ 2 ≤ (1 + b / a) ^ k := by linarith
    have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (a / (a + b)) ^ k by positivity)
    linarith
  have hubound : u ^ k * (((k:ℝ) * ((k:ℝ) - 1) / 2) * (b / a) ^ 2) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right hpow (by positivity)) hq
  -- rewrite the target in terms of `a, b`
  have e1 : ((n:ℝ) - k) = b - 1 := by rw [hb]; ring
  have e2 : (2 * (n:ℝ) - k + 3) = a + 2 * b - 1 := by rw [ha, hb]; ring
  rw [e1, e2, hN]
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hD : 0 < a + 2 * b - 1 := by linarith
  -- key inequality `8 a^2 ≤ (n+1) k (k-1)`
  have hkey : 8 * a ^ 2 ≤ ((n:ℝ) + 1) * ((k:ℝ) * ((k:ℝ) - 1)) := by
    rw [ha]
    nlinarith
  have hub' : u ^ k ≤ 2 * a ^ 2 / ((k:ℝ) * ((k:ℝ) - 1) * b ^ 2) := by
    rw [le_div_iff₀ (by have : 0 < (k:ℝ) - 1 := by linarith
                        positivity)]
    have : u ^ k * (((k:ℝ) * ((k:ℝ) - 1) / 2) * (b / a) ^ 2) * (2 * a ^ 2) =
        u ^ k * ((k:ℝ) * ((k:ℝ) - 1) * b ^ 2) := by field_simp
    nlinarith [pow_pos hu0 k]
  calc (a + b) / ((n:ℝ) + 1) * (b * (b - 1) / (a + 2 * b - 1)) * u ^ k
      ≤ (a + b) / ((n:ℝ) + 1) * (b * (b - 1) / (a + 2 * b - 1)) *
          (2 * a ^ 2 / ((k:ℝ) * ((k:ℝ) - 1) * b ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hub'
        have : 0 ≤ b - 1 := by linarith
        positivity
    _ < 1 / 4 := by
        have hk1 : 0 < (k:ℝ) * ((k:ℝ) - 1) := by
          have : 0 < (k:ℝ) - 1 := by linarith
          positivity
        rw [div_mul_div_comm, div_mul_div_comm, div_lt_div_iff₀ (by positivity) (by norm_num)]
        have hab : (a + b) * (b - 1) < b * (a + 2 * b - 1) := by nlinarith
        have hb0 : 0 < b := by linarith
        nlinarith [mul_lt_mul_of_pos_right hab (show 0 < 8 * a ^ 2 * b by positivity),
          mul_le_mul_of_nonneg_right hkey (show 0 ≤ b * (a + 2 * b - 1) * b ^ 2 by positivity)]

/-- Hypotheses on the set `U` of zeros of `J_n` used throughout. -/
def ZeroSet (n : ℕ) (U : Finset ℝ) : Prop :=
  U.card = n ∧ ∀ u ∈ U, 0 < u ∧ u < 1 ∧ (Jpoly n).eval u = 0 ∧ (Rpoly n n).eval u = 0

private lemma R_two_lt (n : ℕ) (hn : 36 ≤ n) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    (Rpoly n 2).eval u < (1 + u) / 2 := by
  have h := Rpoly_rec_eval n 1 le_rfl (by lia) u
  rw [Rpoly_one_eval n (by lia), show 1 - 1 = 0 by rfl, Rpoly_zero, eval_one] at h
  have hn' : (36:ℝ) ≤ n := by exact_mod_cast hn
  push_cast at h
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hR : (Rpoly n 2).eval u = (((2 * (n:ℝ) - 1 + 3) * u - 1 - 2) *
      (((n:ℝ) + 3) * u - 2) / ((n:ℝ) + 1) - ((n:ℝ) - 1) * u) / n := by
    rw [eq_div_iff (by positivity), mul_div_assoc]
    have : ((n:ℝ) - 1 + 1) = n := by ring
    rw [this] at h; linarith
  rw [hR, div_lt_iff₀ (by positivity), div_sub' (by positivity), div_lt_iff₀ hn1]
  nlinarith [mul_pos hu0 (sub_pos.2 hu1), mul_pos (mul_pos hu0 (sub_pos.2 hu1)) hn1]

/-- `R_{n,k}(u) < (1+u)/2` at every zero `u` of `J_n`, `1 ≤ k ≤ n`. -/
private lemma R_lt (n : ℕ) (hn : 36 ≤ n) (U : Finset ℝ) (hU : ZeroSet n U) (u : ℝ) (hu : u ∈ U)
    (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) : (Rpoly n k).eval u < (1 + u) / 2 := by
  obtain ⟨hu0, hu1, -, hRn⟩ := hU.2 u hu
  have hn' : (36:ℝ) ≤ n := by exact_mod_cast hn
  rcases Nat.eq_or_lt_of_le hkn with rfl | hkn'
  · rw [hRn]; linarith
  rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1'
  · rw [Rpoly_one_eval n (by lia)]
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rcases Nat.eq_or_lt_of_le hk1' with rfl | hk2
  · exact R_two_lt n hn u hu0 hu1
  -- `3 ≤ k < n`
  have hsq : ∀ v : ℝ, v ^ 2 < ((1 + u) / 2) ^ 2 → v < (1 + u) / 2 := by
    intro v hv
    have : 0 < (1 + u) / 2 := by linarith
    nlinarith [sq_nonneg (v - (1 + u) / 2)]
  apply hsq
  rcases le_or_gt (k:ℝ) (((n:ℝ) + 3) * u - 2) with hc | hc
  · have := recurrence_bound (rrec_Rpoly n (by lia) u) hu0 hu1 k hk1 hkn hc
    nlinarith [sq_nonneg (1 - u)]
  · have hg := gauss_bound n (by lia) U hU.1 hU.2 u hu k hk1 hkn'
    have hs := gauss_small n k (by lia) hkn' hn u hu0 hc
    nlinarith

private lemma V_gt (n : ℕ) (hn : 36 ≤ n) (U : Finset ℝ) (hU : ZeroSet n U) (u : ℝ) (hu : u ∈ U)
    (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ((n : ℝ) + 1) / (2 * ((n : ℝ) + 3)) < (Vpoly n k).eval u := by
  obtain ⟨hu0, hu1, -, -⟩ := hU.2 u hu
  have hR := R_lt n hn U hU u hu k hk1 hkn
  have hV := Vpoly_eval n k hkn u
  have h3 : (0:ℝ) < ((n:ℝ) + 3) * (1 - u) := by
    have : (0:ℝ) < 1 - u := by linarith
    positivity
  rw [div_lt_iff₀ (by positivity)]
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  nlinarith [mul_lt_mul_of_pos_left hR hn1]

private lemma V_one (n : ℕ) (u : ℝ) : (Vpoly n 1).eval u = 1 := by
  simp [Vpoly, Apoly]

private lemma V_two_le (n : ℕ) (u : ℝ) (hu1 : u < 1) :
    (Vpoly n 2).eval u ≤ 3 := by
  simp only [Vpoly, Finset.sum_range_succ, Finset.sum_range_zero, eval_add, Apoly, eval_one,
    eval_sub, eval_mul, eval_C, eval_X, zero_add]
  have : (0:ℝ) ≤ 2 / (n:ℝ) := by positivity
  nlinarith [mul_nonneg this (show (0:ℝ) ≤ 1 - u by linarith)]

/-- Abstract summation by parts with the weight shape. -/
private lemma abel_lower (n : ℕ) (hn : 3 ≤ n) (b V : ℕ → ℝ) (c : ℝ)
    (hdec : ∀ j, 3 ≤ j → j < n → b j ≤ b (j - 1)) (hbn : 0 ≤ b (n - 1))
    (hV : ∀ j, 1 ≤ j → j ≤ n → c ≤ V j) :
    (b 0 - b 1) * V 1 + (b 1 - b 2) * V 2 + c * b 2 - V 0 * b 0 ≤
      ∑ j ∈ Finset.range n, b j * (V (j + 1) - V j) := by
  have key : ∀ m, 3 ≤ m → m ≤ n →
      (b 0 - b 1) * V 1 + (b 1 - b 2) * V 2 + c * (b 2 - b (m-1)) + b (m-1) * V m - V 0 * b 0 ≤
        ∑ j ∈ Finset.range m, b j * (V (j+1) - V j) := by
    intro m hm3 hmn
    induction m with
    | zero => lia
    | succ m ih =>
      rcases Nat.eq_or_lt_of_le hm3 with h | h
      · rw [← h]; simp [Finset.sum_range_succ]; ring_nf; rfl
      · have ih := ih (by lia) (by lia)
        rw [Finset.sum_range_succ]
        have h1 := hdec m (by lia) (by lia)
        have h2 := hV m (by lia) (by lia)
        simp only [Nat.add_sub_cancel] at *
        nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ b (m - 1) - b m by linarith)]
  have := key n hn le_rfl
  have h2 := hV n (by lia) le_rfl
  nlinarith [mul_le_mul_of_nonneg_left h2 hbn]

/-- **Positivity of the weighted sum** `∑_j b_j A_{n,j}(u) > 0` at the zeros of `J_n`. -/
theorem weighted_sum_pos (n : ℕ) (hn : 36 ≤ n) (U : Finset ℝ) (hU : ZeroSet n U) (u : ℝ)
    (hu : u ∈ U) : 0 < ∑ j ∈ Finset.range n, bw n j * (Apoly n j).eval u := by
  obtain ⟨hu0, hu1, -, -⟩ := hU.2 u hu
  set c : ℝ := ((n:ℝ) + 1) / (2 * ((n:ℝ) + 3)) with hc
  have hA : ∀ j, (Apoly n j).eval u = (Vpoly n (j+1)).eval u - (Vpoly n j).eval u := by
    intro j; simp [Vpoly, Finset.sum_range_succ]
  simp_rw [hA]
  have hab := abel_lower n (by lia) (bw n) (fun j => (Vpoly n j).eval u) c
    (fun j hj3 hjn => (bw_decr n j hn hj3 hjn).le) (bw_pos n (n-1) (by lia)).le
    (fun j hj1 hjn => (V_gt n hn U hU u hu j hj1 hjn).le)
  beta_reduce at hab
  have hV0 : (Vpoly n 0).eval u = 0 := by simp [Vpoly]
  rw [hV0, V_one] at hab
  have hV2 := V_two_le n u hu1
  have h12 := bw_one_le_two n hn
  have hsh := bw_shape n hn
  have hb2 := bw_pos n 2 (by lia)
  have hn' : (36:ℝ) ≤ n := by exact_mod_cast hn
  have hc3 : 1 / 3 + 1 / 20 ≤ c := by
    rw [hc, le_div_iff₀ (by positivity)]; linarith
  nlinarith [mul_le_mul_of_nonneg_left hV2 (show 0 ≤ bw n 2 - bw n 1 by linarith)]

end AllZeros

end RealRooted.BorosMoll
