import Mathlib

/-!
# Capacity and the permanent

The capacity `capacity p = inf_{x > 0} p(x) / ∏ i, x i` of a real multivariate polynomial, the
permanent as the coefficient of `∏ i, x i` in `prodLin A = ∏ i, ∑ j, A i j * x j`, the bound
`1 ≤ capacity (prodLin A)` for doubly stochastic `A`, and the extraction of that coefficient
one variable at a time (`step`: differentiate in `x₀`, then set `x₀ = 0`).
-/

noncomputable section

namespace RealRooted.Gurvits

section CapacityDef

open MvPolynomial

variable {σ : Type*}

/-- A polynomial with nonnegative coefficients is nonnegative on the nonnegative orthant. -/
theorem eval_nonneg_of_coeff_nonneg {p : MvPolynomial σ ℝ} (hp : ∀ m, 0 ≤ p.coeff m)
    {x : σ → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x p := by
  rw [eval_eq]
  exact Finset.sum_nonneg fun m _ =>
    mul_nonneg (hp m) (Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _)

instance instNonemptyPosVec : Nonempty {x : σ → ℝ // ∀ i, 0 < x i} :=
  ⟨⟨fun _ => 1, fun _ => one_pos⟩⟩

variable [Fintype σ]

/-- The capacity `inf_{x > 0} p(x) / ∏ i, x i` of a real multivariate polynomial. -/
noncomputable def capacity (p : MvPolynomial σ ℝ) : ℝ :=
  ⨅ x : {x : σ → ℝ // ∀ i, 0 < x i}, eval x.1 p / ∏ i, x.1 i

theorem div_prod_nonneg_of_coeff_nonneg {p : MvPolynomial σ ℝ} (hp : ∀ m, 0 ≤ p.coeff m)
    (x : {x : σ → ℝ // ∀ i, 0 < x i}) : 0 ≤ eval x.1 p / ∏ i, x.1 i :=
  div_nonneg (eval_nonneg_of_coeff_nonneg hp fun i => (x.2 i).le)
    (Finset.prod_nonneg fun i _ => (x.2 i).le)

theorem bddBelow_range_div_prod {p : MvPolynomial σ ℝ} (hp : ∀ m, 0 ≤ p.coeff m) :
    BddBelow (Set.range fun x : {x : σ → ℝ // ∀ i, 0 < x i} => eval x.1 p / ∏ i, x.1 i) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    exact div_prod_nonneg_of_coeff_nonneg hp x⟩

/-- The capacity of a polynomial with nonnegative coefficients is nonnegative. -/
theorem capacity_nonneg {p : MvPolynomial σ ℝ} (hp : ∀ m, 0 ≤ p.coeff m) :
    0 ≤ capacity p :=
  le_ciInf fun x => div_prod_nonneg_of_coeff_nonneg hp x

/-- For nonnegative coefficients, the capacity is at most `p(x) / ∏ i, x i` at each `x > 0`. -/
theorem capacity_le {p : MvPolynomial σ ℝ} (hp : ∀ m, 0 ≤ p.coeff m) {x : σ → ℝ}
    (hx : ∀ i, 0 < x i) : capacity p ≤ eval x p / ∏ i, x i :=
  ciInf_le (bddBelow_range_div_prod hp) ⟨x, hx⟩

/-- `capacity_le` in multiplicative form. -/
theorem capacity_mul_prod_le {p : MvPolynomial σ ℝ} (hp : ∀ m, 0 ≤ p.coeff m) {x : σ → ℝ}
    (hx : ∀ i, 0 < x i) : capacity p * ∏ i, x i ≤ eval x p :=
  (le_div_iff₀ (Finset.prod_pos fun i _ => hx i)).1 (capacity_le hp hx)

/-- A uniform lower bound for `p(x) / ∏ i, x i` over `x > 0` bounds the capacity from below.
No hypothesis on `p` is needed. -/
theorem le_capacity {p : MvPolynomial σ ℝ} {c : ℝ}
    (h : ∀ x : σ → ℝ, (∀ i, 0 < x i) → c ≤ eval x p / ∏ i, x i) : c ≤ capacity p :=
  le_ciInf fun x => h x.1 x.2

/-- `le_capacity` in multiplicative form. -/
theorem le_capacity_of_mul_le {p : MvPolynomial σ ℝ} {c : ℝ}
    (h : ∀ x : σ → ℝ, (∀ i, 0 < x i) → c * ∏ i, x i ≤ eval x p) : c ≤ capacity p :=
  le_capacity fun x hx => (le_div_iff₀ (Finset.prod_pos fun i _ => hx i)).2 (h x hx)

end CapacityDef

section Permanent

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- The all-ones exponent `∑ i, single i 1`, i.e. the monomial `∏ i, x i`. -/
noncomputable def allOnes (σ : Type*) [Fintype σ] : σ →₀ ℕ :=
  ∑ i, Finsupp.single i 1

@[simp]
theorem allOnes_apply [Fintype σ] (i : σ) : allOnes σ i = 1 := by
  classical
  simp [allOnes, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- The product `∏ i, ∑ j, A i j * X j` of the linear forms given by the rows of `A`. -/
noncomputable def prodLin [Fintype σ] (A : Matrix σ σ R) : MvPolynomial σ R :=
  ∏ i, ∑ j, C (A i j) * X j

/-- The exponent `∑ i, single (g i) 1` equals `allOnes σ` exactly when `g` is bijective. -/
theorem sum_single_eq_allOnes_iff [Fintype σ] (g : σ → σ) :
    ∑ i, Finsupp.single (g i) 1 = allOnes σ ↔ Function.Bijective g := by
  classical
  constructor
  · intro h
    have hsurj : Function.Surjective g := by
      intro j
      have hj := DFunLike.congr_fun h j
      simp only [allOnes_apply, Finsupp.finsetSum_apply, Finsupp.single_apply] at hj
      by_contra hne
      push Not at hne
      simp [hne] at hj
    exact ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  · intro hg
    ext j
    obtain ⟨k, rfl⟩ := hg.2 j
    simp only [allOnes_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hg.1.ne hb])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp

/-- The coefficient of `∏ i, x i` in `∏ i, ∑ j, A i j * x j` is the permanent of `A`. -/
theorem coeff_allOnes_prodLin [Fintype σ] [DecidableEq σ] (A : Matrix σ σ R) :
    (prodLin A).coeff (allOnes σ) = A.permanent := by
  have hterm : ∀ g : σ → σ, ∏ i, C (A i (g i)) * X (g i) =
      monomial (∑ i, Finsupp.single (g i) 1) (∏ i, A i (g i) : R) := by
    intro g
    have hX : ∏ i, (X (g i) : MvPolynomial σ R) =
        monomial (∑ i, Finsupp.single (g i) 1) (1 : R) := by
      rw [monomial_sum_one]
      rfl
    rw [Finset.prod_mul_distrib, ← map_prod, hX, C_mul_monomial, mul_one]
  rw [prodLin, Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, hterm, coeff_sum, coeff_monomial,
    sum_single_eq_allOnes_iff]
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  symm
  refine Fintype.sum_of_injective (fun τ : Equiv.Perm σ => (τ : σ → σ))
    DFunLike.coe_injective _ _ ?_ ?_
  · intro g hg
    exact ite_eq_right_iff.2 fun hb => absurd ⟨Equiv.ofBijective g hb, rfl⟩ hg
  · intro τ
    simp

end Permanent

section DoublyStochastic

open MvPolynomial

variable {σ : Type*} [Fintype σ]






theorem eval_prodLin (A : Matrix σ σ ℝ) (x : σ → ℝ) :
    eval x (prodLin A) = ∏ i, ∑ j, A i j * x j := by
  simp [prodLin]

/-- For a nonnegative matrix with row and column sums one, `∏ j, x j ≤ ∏ i, ∑ j, A i j * x j`
for all `x > 0` (weighted AM–GM row by row). -/
theorem prod_le_eval_prodLin {A : Matrix σ σ ℝ} (hnn : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1) {x : σ → ℝ}
    (hx : ∀ i, 0 < x i) : ∏ j, x j ≤ eval x (prodLin A) := by
  rw [eval_prodLin]
  calc ∏ j, x j = ∏ j, x j ^ (∑ i, A i j) := by simp [hcol]
    _ = ∏ j, ∏ i, x j ^ A i j :=
      Finset.prod_congr rfl fun j _ => Real.rpow_sum_of_pos (hx j) _ _
    _ = ∏ i, ∏ j, x j ^ A i j := Finset.prod_comm
    _ ≤ ∏ i, ∑ j, A i j * x j :=
      Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hx j).le _)
        fun i _ => Real.geom_mean_le_arith_mean_weighted _ _ _ (fun j _ => hnn i j) (hrow i)
          fun j _ => (hx j).le

/-- The capacity of `∏ i, ∑ j, A i j * x j` is at least one when `A` is nonnegative with
row and column sums one. -/
theorem one_le_capacity_prodLin_of_sum {A : Matrix σ σ ℝ} (hnn : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1) :
    1 ≤ capacity (prodLin A) :=
  le_capacity_of_mul_le fun _ hx => (one_mul _).trans_le (prod_le_eval_prodLin hnn hrow hcol hx)

/-- The capacity of `∏ i, ∑ j, A i j * x j` is at least one for a doubly stochastic `A`. -/
theorem one_le_capacity_prodLin [DecidableEq σ] {A : Matrix σ σ ℝ}
    (hA : A ∈ doublyStochastic ℝ σ) : 1 ≤ capacity (prodLin A) := by
  obtain ⟨hnn, hrow, hcol⟩ := mem_doublyStochastic_iff_sum.1 hA
  exact one_le_capacity_prodLin_of_sum hnn hrow hcol

end DoublyStochastic

section Extraction

open MvPolynomial

variable {R : Type*} [CommSemiring R] {n : ℕ}



/-- `∂p/∂x₀` evaluated at `x₀ = 0`, as a polynomial in the remaining `n` variables. -/
noncomputable def step (p : MvPolynomial (Fin (n + 1)) R) : MvPolynomial (Fin n) R :=
  aeval (Fin.cons 0 X : Fin (n + 1) → MvPolynomial (Fin n) R) (pderiv 0 p)

/-- Under `finSuccEquiv`, the partial derivative in the variable `0` is `Polynomial.derivative`. -/
theorem finSuccEquiv_pderiv_zero (p : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R n (pderiv 0 p) = Polynomial.derivative (finSuccEquiv R n p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    induction i using Fin.cases with
    | zero =>
      simp only [Derivation.leibniz, pderiv_X_self, smul_eq_mul, map_add, map_mul, hp,
        finSuccEquiv_X_zero, Polynomial.derivative_mul, Polynomial.derivative_X, map_one]
      ring
    | succ k =>
      simp only [Derivation.leibniz, pderiv_X_of_ne (Fin.succ_ne_zero k), smul_eq_mul,
        map_add, map_mul, hp, finSuccEquiv_X_succ, Polynomial.derivative_mul,
        Polynomial.derivative_C, map_zero, mul_zero, add_zero]
      ring

/-- Setting the variable `0` to zero is evaluation at `0` after `finSuccEquiv`. -/
theorem aeval_cons_zero_X (q : MvPolynomial (Fin (n + 1)) R) :
    aeval (Fin.cons 0 X : Fin (n + 1) → MvPolynomial (Fin n) R) q =
      Polynomial.eval 0 (finSuccEquiv R n q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.eval_add]
  | mul_X p i hp =>
    induction i using Fin.cases with
    | zero =>
      rw [map_mul, map_mul, hp, Polynomial.eval_mul, aeval_X, finSuccEquiv_X_zero,
        Polynomial.eval_X, Fin.cons_zero]
    | succ k =>
      rw [map_mul, map_mul, hp, Polynomial.eval_mul, aeval_X, finSuccEquiv_X_succ,
        Polynomial.eval_C, Fin.cons_succ]

/-- `step p` is the coefficient of `x₀ ^ 1` in `p`, viewed as a polynomial in `x₀`. -/
theorem step_eq_coeff_one (p : MvPolynomial (Fin (n + 1)) R) :
    step p = (finSuccEquiv R n p).coeff 1 := by
  rw [step, aeval_cons_zero_X, finSuccEquiv_pderiv_zero, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_derivative]
  simp

/-- One step preserves the coefficient of the all-ones monomial. -/
theorem coeff_allOnes_step (p : MvPolynomial (Fin (n + 1)) R) :
    (step p).coeff (allOnes (Fin n)) = p.coeff (allOnes (Fin (n + 1))) := by
  rw [step_eq_coeff_one, finSuccEquiv_coeff_coeff]
  congr 1
  ext j
  induction j using Fin.cases with
  | zero => simp
  | succ k => simp

/-- Apply `step` `n` times and take the resulting constant. -/
noncomputable def coeffIter : (n : ℕ) → MvPolynomial (Fin n) R → R
  | 0, p => p.coeff 0
  | n + 1, p => coeffIter n (step p)

/-- After `n` steps, the constant is the coefficient of `x₀ ⋯ xₙ₋₁` in `p`. -/
theorem coeffIter_eq_coeff_allOnes (n : ℕ) (p : MvPolynomial (Fin n) R) :
    coeffIter n p = p.coeff (allOnes (Fin n)) := by
  induction n with
  | zero => rw [coeffIter, Subsingleton.elim (allOnes (Fin 0)) 0]
  | succ n ih => rw [coeffIter, ih, coeff_allOnes_step]

end Extraction

end RealRooted.Gurvits
