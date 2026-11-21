module

public import RealRooted.ExponentialRows.Insertion
public import RealRooted.ExponentialRows.RealRootedProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# The product rows satisfy the standard insertion recurrence

We identify the auxiliary coordinates with the factorial-scaled coefficients of
`Qⱼ(z) exp(z + t B(z))`, prove the standard insertion-recurrence identity, and transfer
Theorem C to that definition. The formal exponential uses Mathlib's substitution API.

Source: the unpublished argument in RealRooted issue #2415,
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

@[expose] public section

open Finset Polynomial

namespace RealRooted.ExponentialRows

/-- Singleton weight one and marked block weight `r! [z^r] B * t` at every other size. -/
noncomputable def markedBlockWeights (B : ℝ[X]) (r : ℕ) : ℝ[X] :=
  if r = 1 then 1 else C ((r.factorial : ℝ) * B.coeff r) * X

/-- Singletons have weight one in the marked-block specialization. -/
@[simp] theorem markedBlockWeights_one (B : ℝ[X]) : markedBlockWeights B 1 = 1 := by
  simp [markedBlockWeights]

/-- Every other block size has the prescribed factorial coefficient multiplied by `t`. -/
theorem markedBlockWeights_of_ne_one (B : ℝ[X]) {r : ℕ} (hr : r ≠ 1) :
    markedBlockWeights B r = C ((r.factorial : ℝ) * B.coeff r) * X := by
  simp [markedBlockWeights, hr]

/-- The formal exponent `z + t B(z)` over the coefficient ring `ℝ[t]`. -/
noncomputable def markedExponent (B : ℝ[X]) : PowerSeries ℝ[X] :=
  PowerSeries.X + PowerSeries.C X * Polynomial.coeToPowerSeries.algHom ℝ[X] B

/-- Coefficients of the canonical scalar-to-polynomial power-series map. -/
theorem coeff_polynomialSeries (p : ℝ[X]) (n : ℕ) :
    PowerSeries.coeff n (Polynomial.coeToPowerSeries.algHom ℝ[X] p) = C (p.coeff n) := by
  rw [Polynomial.coeToPowerSeries.algHom_apply, PowerSeries.coeff_map, Polynomial.coeff_coe]
  rfl

/-- The standard marked weights have exponent `z + t B(z)` when `B` has a double zero. -/
theorem blockWeightSeries_markedBlockWeights (B : ℝ[X])
    (hzero : B.coeff 0 = 0) (hone : B.coeff 1 = 0) :
    blockWeightSeries (markedBlockWeights B) = markedExponent B := by
  apply factorialCoeff_ext
  intro n
  cases n with
  | zero =>
    simp only [factorialCoeff, blockWeightSeries, PowerSeries.coeff_mk, markedExponent,
      map_add, PowerSeries.coeff_C_mul, coeff_polynomialSeries, PowerSeries.coeff_X,
      hzero, map_zero, mul_zero, add_zero, Nat.factorial_zero, Nat.cast_one, map_one,
      Nat.zero_ne_one, ↓reduceIte]
  | succ n =>
    rw [factorialCoeff_blockWeightSeries]
    by_cases hn : n + 1 = 1
    · have hn' : n = 0 := by lia
      subst n
      simp [markedBlockWeights, markedExponent, factorialCoeff, PowerSeries.coeff_X, hone]
    · simp only [markedBlockWeights, ite_eq_right hn, markedExponent, factorialCoeff,
        map_add, PowerSeries.coeff_C_mul, coeff_polynomialSeries, PowerSeries.coeff_X]
      simp only [zero_add, map_mul]
      ring

/-- The insertion rows are exactly `n! [z^n] exp(z + t B(z))` for a double-zero block polynomial. -/
theorem insertionRow_eq_marked_exponential (B : ℝ[X])
    (hzero : B.coeff 0 = 0) (hone : B.coeff 1 = 0) (n : ℕ) :
    insertionRow (markedBlockWeights B) n =
      C (n.factorial : ℝ) * PowerSeries.coeff n
        ((PowerSeries.exp ℝ[X]).subst (markedExponent B)) := by
  rw [insertionRow_eq_factorialCoeff, insertionSeries,
    blockWeightSeries_markedBlockWeights B hzero hone]
  rfl

/-- Factorial-scaled coefficients after multiplying a series by a real polynomial. -/
noncomputable def polynomialBracket (p : ℝ[X]) (f : PowerSeries ℝ[X]) (n : ℕ) : ℝ[X] :=
  factorialCoeff (Polynomial.coeToPowerSeries.algHom ℝ[X] p * f) n

/-- The constant partial product leaves factorial coefficients unchanged. -/
@[simp] theorem polynomialBracket_one (f : PowerSeries ℝ[X]) (n : ℕ) :
    polynomialBracket 1 f n = factorialCoeff f n := by
  simp [polynomialBracket]

/-- Addition in the polynomial factor adds brackets. -/
theorem polynomialBracket_add (p q : ℝ[X]) (f : PowerSeries ℝ[X]) (n : ℕ) :
    polynomialBracket (p + q) f n = polynomialBracket p f n + polynomialBracket q f n := by
  simp [polynomialBracket, add_mul, factorialCoeff_add]

/-- A real scalar factor pulls out of a polynomial bracket. -/
theorem polynomialBracket_C_mul (a : ℝ) (p : ℝ[X]) (f : PowerSeries ℝ[X]) (n : ℕ) :
    polynomialBracket (C a * p) f n = C a * polynomialBracket p f n := by
  have hlift : Polynomial.coeToPowerSeries.algHom ℝ[X] (C a) = PowerSeries.C (C a) := by
    ext k
    simp [PowerSeries.coeff_C]
  simp only [polynomialBracket, map_mul, hlift, mul_assoc, factorialCoeff_C_mul]

/-- Finite sums of polynomial factors become finite sums of brackets. -/
theorem polynomialBracket_sum {ι : Type*} (s : Finset ι) (p : ι → ℝ[X])
    (f : PowerSeries ℝ[X]) (n : ℕ) :
    polynomialBracket (∑ i ∈ s, p i) f n = ∑ i ∈ s, polynomialBracket (p i) f n := by
  simp [polynomialBracket, map_sum, sum_mul, factorialCoeff, mul_sum]

/-- Multiplication by a linear factor gives the partial-product coefficient recursion. -/
theorem polynomialBracket_linear_mul (a : ℝ) (p : ℝ[X]) (f : PowerSeries ℝ[X]) (n : ℕ) :
    polynomialBracket ((X + C a) * p) f (n + 1) =
      C a * polynomialBracket p f (n + 1) + C (n + 1 : ℝ) * polynomialBracket p f n := by
  have hX : Polynomial.coeToPowerSeries.algHom ℝ[X] (X : ℝ[X]) = PowerSeries.X := by
    ext k
    simp [PowerSeries.coeff_X]
  have hC : Polynomial.coeToPowerSeries.algHom ℝ[X] (C a) = PowerSeries.C (C a) := by
    ext k
    simp [PowerSeries.coeff_C]
  simp only [polynomialBracket, map_mul, map_add, hX, hC, add_mul, mul_assoc,
    factorialCoeff_add, factorialCoeff_C_mul, factorialCoeff_X_mul]
  exact add_comm _ _

/-- A zero constant coefficient in the factor makes the zeroth bracket vanish. -/
theorem polynomialBracket_zero_of_coeff_zero {p : ℝ[X]} (hp : p.coeff 0 = 0)
    (f : PowerSeries ℝ[X]) : polynomialBracket p f 0 = 0 := by
  simp only [polynomialBracket, factorialCoeff, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_zero, sum_singleton, coeff_polynomialSeries, hp,
    map_zero, zero_mul, mul_zero]

/-- Formal differentiation commutes with the canonical polynomial-to-series map. -/
theorem derivative_polynomialSeries (p : ℝ[X]) :
    PowerSeries.derivative (Polynomial.coeToPowerSeries.algHom ℝ[X] p) =
      Polynomial.coeToPowerSeries.algHom ℝ[X] p.derivative := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_derivative, coeff_polynomialSeries, Polynomial.coeff_derivative,
    map_mul, map_add, map_one, map_natCast]

/-- Differentiating `z + t B(z)` gives `1 + t B'(z)`. -/
theorem markedExponent_derivative (B : ℝ[X]) :
    PowerSeries.derivative (markedExponent B) =
      1 + PowerSeries.C X * Polynomial.coeToPowerSeries.algHom ℝ[X] B.derivative := by
  simp only [markedExponent, map_add, PowerSeries.derivative_X,
    PowerSeries.derivative.leibniz, PowerSeries.derivative_C, smul_eq_mul,
    mul_zero, add_zero, derivative_polynomialSeries]

/-- The marked exponential satisfies its defining formal differential equation. -/
theorem insertionSeries_marked_derivative (B : ℝ[X])
    (hzero : B.coeff 0 = 0) (hone : B.coeff 1 = 0) :
    PowerSeries.derivative (insertionSeries (markedBlockWeights B)) =
      (1 + PowerSeries.C X * Polynomial.coeToPowerSeries.algHom ℝ[X] B.derivative) *
        insertionSeries (markedBlockWeights B) := by
  rw [insertionSeries_derivative, blockWeightSeries_markedBlockWeights B hzero hone,
    markedExponent_derivative]

/-- The factorial coefficients of the marked exponential obey the Newton-bracket update. -/
theorem factorialCoeff_marked_succ (B : ℝ[X])
    (hzero : B.coeff 0 = 0) (hone : B.coeff 1 = 0) (n : ℕ) :
    factorialCoeff (insertionSeries (markedBlockWeights B)) (n + 1) =
      factorialCoeff (insertionSeries (markedBlockWeights B)) n +
        X * polynomialBracket B.derivative (insertionSeries (markedBlockWeights B)) n := by
  rw [← factorialCoeff_derivative, insertionSeries_marked_derivative B hzero hone,
    add_mul, one_mul, factorialCoeff_add, mul_assoc, factorialCoeff_C_mul]
  rfl

/-- Prefix products in the Newton basis, including the two zero nodes. -/
private noncomputable def prefixProduct (ρ : ℕ → ℝ) (j : ℕ) : ℝ[X] :=
  ∏ k ∈ range j, (X + C (productNodes ρ k))

/-- Appending one node gives the prefix-product recurrence. -/
private lemma prefixProduct_succ (ρ : ℕ → ℝ) (j : ℕ) :
    prefixProduct ρ (j + 1) = (X + C (productNodes ρ j)) * prefixProduct ρ j := by
  simp only [prefixProduct, prod_range_succ]
  ring

/-- Every nonempty prefix has zero constant coefficient. -/
private lemma prefixProduct_coeff_zero (ρ : ℕ → ℝ) {j : ℕ} (hj : 0 < j) :
    (prefixProduct ρ j).coeff 0 = 0 := by
  simp only [prefixProduct, coeff_zero_prod, coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
  apply prod_eq_zero (i := 0)
  · exact mem_range.mpr hj
  · simp [productNodes]

/-- A full block product has no constant or linear term. -/
private lemma markedProduct_coeff_small (c : ℝ) (ρ : ℕ → ℝ) (d : ℕ)
    {k : ℕ} (hk : k < 2) : (C c * blockProduct ρ d).coeff k = 0 := by
  rw [coeff_C_mul, blockProduct_eq, coeff_X_pow_mul']
  simp [show ¬ 2 ≤ k by lia]

/-- Reverse the nonzero Newton indices, keeping index zero as a separate term. -/
private lemma sum_reverse_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    (∑ i ∈ range (m + 1), f i) = f 0 + ∑ j : Fin m, f (m - j) := by
  rw [sum_range_succ', add_comm]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin m))
  intro j
  congr 1
  simp only [Fin.revPerm_apply, Fin.val_rev]
  lia

/-- The derivative bracket is the weighted sum of the auxiliary prefix brackets. -/
private lemma polynomialBracket_product_derivative (c : ℝ) (ρ : ℕ → ℝ) (d : ℕ)
    (f : PowerSeries ℝ[X]) (n : ℕ) :
    polynomialBracket (C c * blockProduct ρ d).derivative f n =
      ∑ j : Fin (d + 1), C (c * newtonDerivativeCoeff (productNodes ρ) (d + 2)
        (d + 1 - j)) * polynomialBracket (prefixProduct ρ (d + 1 - j)) f n := by
  rw [derivative_C_mul, polynomialBracket_C_mul]
  unfold blockProduct
  rw [derivative_prod_eq_sum_newtonDerivativeCoeff, polynomialBracket_sum]
  simp_rw [polynomialBracket_C_mul]
  change C c * (∑ i ∈ range (d + 1 + 1),
    C (newtonDerivativeCoeff (productNodes ρ) (d + 2) i) *
      polynomialBracket (prefixProduct ρ i) f n) = _
  rw [sum_reverse_succ (fun i =>
    C (newtonDerivativeCoeff (productNodes ρ) (d + 2) i) *
      polynomialBracket (prefixProduct ρ i) f n) (d + 1)]
  rw [newtonDerivativeCoeff_zero (by simp [productNodes]) (by simp [productNodes])]
  simp only [map_zero, zero_mul, zero_add, mul_sum, map_mul]
  apply sum_congr rfl
  intro j _
  ring

/-- The recurrence vector in increasing partial-product degree after reversing its coordinates. -/
private noncomputable def productVector (c : ℝ) (ρ : ℕ → ℝ) (d n : ℕ) :
    Fin (d + 2) → ℝ[X] :=
  partialProductVector (fun k => productNodes ρ (d + 1 - k))
    (fun k => c * newtonDerivativeCoeff (productNodes ρ) (d + 2) (d + 1 - k)) (d + 1) n

/-- The next auxiliary coordinates are polynomial brackets whenever the preceding vector is. -/
private lemma productVector_aux_eq_bracket (c : ℝ) (ρ : ℕ → ℝ) (d n : ℕ)
    (f : PowerSeries ℝ[X])
    (hprev : ∀ i : Fin (d + 2), productVector c ρ d n i =
      polynomialBracket (prefixProduct ρ (d + 1 - i)) f n) :
    ∀ i : Fin (d + 1), productVector c ρ d (n + 1) i.castSucc =
      polynomialBracket (prefixProduct ρ (d + 1 - i)) f (n + 1) := by
  have haux : ∀ j, j < d + 1 → productVector c ρ d (n + 1)
      (⟨d - j, by lia⟩ : Fin (d + 1)).castSucc =
      polynomialBracket (prefixProduct ρ (j + 1)) f (n + 1) := by
    intro j
    induction j with
    | zero =>
      intro hj
      change partialProductVector _ _ (d + 1) (n + 1) (Fin.last d).castSucc = _
      rw [partialProductVector_last_aux]
      have hscalar := hprev (Fin.last (d + 1))
      simp only [Fin.val_last, Nat.sub_self, prefixProduct, range_zero, prod_empty,
        polynomialBracket_one] at hscalar
      change C (n + 1 : ℝ) * productVector c ρ d n (Fin.last (d + 1)) = _
      rw [hscalar, prefixProduct_succ, polynomialBracket_linear_mul]
      simp [prefixProduct, productNodes]
    | succ j ih =>
      intro hj
      have hi : d - (j + 1) + 1 < d + 1 := by lia
      have hidx : d - (j + 1) + 1 = d - j := by lia
      have hnode : d + 1 - (d - j) = j + 1 := by lia
      have hlocal := partialProductVector_aux_succ
        (fun k => productNodes ρ (d + 1 - k))
        (fun k => c * newtonDerivativeCoeff (productNodes ρ) (d + 2) (d + 1 - k)) hi n
      simp only [hidx] at hlocal
      change productVector c ρ d (n + 1) (⟨d - (j + 1), by lia⟩ : Fin (d + 1)).castSucc = _
      change productVector c ρ d (n + 1) (⟨d - (j + 1), by lia⟩ : Fin (d + 1)).castSucc =
        C (productNodes ρ (d + 1 - (d - j))) * productVector c ρ d (n + 1)
          (⟨d - j, by lia⟩ : Fin (d + 1)).castSucc +
        C (n + 1 : ℝ) * productVector c ρ d n
          (⟨d - j, by lia⟩ : Fin (d + 1)).castSucc at hlocal
      rw [hlocal, ih (by lia), hprev]
      simp only [Fin.val_castSucc, hnode]
      rw [prefixProduct_succ ρ (j + 1), polynomialBracket_linear_mul]
  intro i
  have hj : d - (i : ℕ) < d + 1 := by lia
  have hidx : d - (d - (i : ℕ)) = (i : ℕ) := by have := i.isLt; lia
  have hdegree : d - (i : ℕ) + 1 = d + 1 - (i : ℕ) := by have := i.isLt; lia
  simpa only [hidx, Fin.eta, hdegree] using haux (d - i) hj

/-- Every recurrence coordinate is the coefficient row of its partial product times the EGF. -/
private lemma productVector_eq_bracket (c : ℝ) (ρ : ℕ → ℝ) (d n : ℕ) :
    ∀ i : Fin (d + 2), productVector c ρ d n i = polynomialBracket
      (prefixProduct ρ (d + 1 - i))
      (insertionSeries (markedBlockWeights (C c * blockProduct ρ d))) n := by
  induction n with
  | zero =>
    intro i
    induction i using Fin.lastCases with
    | last => simp [productVector, partialProductVector, prefixProduct, polynomialBracket,
        factorialCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    | cast i =>
      have hpos : 0 < d + 1 - (i : ℕ) := by have := i.isLt; lia
      simp only [Fin.val_castSucc]
      rw [polynomialBracket_zero_of_coeff_zero (prefixProduct_coeff_zero ρ hpos)]
      simp [productVector, partialProductVector]
  | succ n ih =>
    intro i
    induction i using Fin.lastCases with
    | cast i => exact productVector_aux_eq_bracket c ρ d n _ ih i
    | last =>
      have hzero := markedProduct_coeff_small c ρ d (k := 0) (by lia)
      have hone := markedProduct_coeff_small c ρ d (k := 1) (by lia)
      have hscalar := ih (Fin.last (d + 1))
      simp only [Fin.val_last, Nat.sub_self, prefixProduct, range_zero, prod_empty,
        polynomialBracket_one] at hscalar ⊢
      change partialProductRow _ _ (d + 1) (n + 1) = _
      rw [partialProductRow_succ]
      change productVector c ρ d n (Fin.last (d + 1)) + X *
        (∑ j : Fin (d + 1), C (c * newtonDerivativeCoeff (productNodes ρ) (d + 2)
          (d + 1 - j)) * productVector c ρ d n j.castSucc) = _
      simp_rw [ih]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, prefixProduct,
        range_zero, prod_empty, polynomialBracket_one]
      rw [factorialCoeff_marked_succ _ hzero hone, polynomialBracket_product_derivative]
      rfl

/-- The product recurrence is exactly the standard block-weight insertion recurrence. -/
theorem productRow_eq_insertionRow (c : ℝ) (ρ : ℕ → ℝ) (d n : ℕ) :
    productRow c ρ d n = insertionRow (markedBlockWeights (C c * blockProduct ρ d)) n := by
  rw [insertionRow_eq_factorialCoeff]
  have h := productVector_eq_bracket c ρ d n (Fin.last (d + 1))
  simpa only [Fin.val_last, Nat.sub_self, prefixProduct, range_zero, prod_empty,
    polynomialBracket_one, productVector, productRow, partialProductRow] using h

/-- A polynomial factor gives the explicit binomial convolution of insertion rows. -/
theorem polynomialBracket_eq_insertionSum (p : ℝ[X]) (w : ℕ → ℝ[X]) (n : ℕ) :
    polynomialBracket p (insertionSeries w) n = ∑ k ∈ range (n + 1),
      C ((n.choose k : ℝ) * (k.factorial : ℝ) * p.coeff k) * insertionRow w (n - k) := by
  rw [polynomialBracket, factorialCoeff_mul]
  apply sum_congr rfl
  intro k hk
  rw [insertionRow_eq_factorialCoeff]
  simp only [factorialCoeff, coeff_polynomialSeries, map_mul]
  ring

/-- All product coordinates are explicit binomial sums of the standard insertion rows. -/
theorem partialProductVector_eq_insertionSum (c : ℝ) (ρ : ℕ → ℝ) (d n : ℕ)
    (i : Fin (d + 2)) :
    partialProductVector (fun k => productNodes ρ (d + 1 - k))
      (fun k => c * newtonDerivativeCoeff (productNodes ρ) (d + 2) (d + 1 - k))
      (d + 1) n i = ∑ k ∈ range (n + 1),
        C ((n.choose k : ℝ) * (k.factorial : ℝ) *
          (∏ j ∈ range (d + 1 - i), (X + C (productNodes ρ j))).coeff k) *
            insertionRow (markedBlockWeights (C c * blockProduct ρ d)) (n - k) := by
  have h := productVector_eq_bracket c ρ d n i
  rw [polynomialBracket_eq_insertionSum] at h
  exact h

/-- The product recurrence also equals the literal factorial-scaled formal exponential. -/
theorem productRow_eq_marked_exponential (c : ℝ) (ρ : ℕ → ℝ) (d n : ℕ) :
    productRow c ρ d n = C (n.factorial : ℝ) * PowerSeries.coeff n
      ((PowerSeries.exp ℝ[X]).subst (markedExponent (C c * blockProduct ρ d))) := by
  rw [productRow_eq_insertionRow, insertionRow_eq_marked_exponential _
    (markedProduct_coeff_small c ρ d (by lia)) (markedProduct_coeff_small c ρ d (by lia))]

/-- Nonnegative real-rooted block products give real-rooted standard insertion rows. -/
theorem insertionRow_isRealRooted_of_blockProduct {c : ℝ} (hc : 0 ≤ c) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 ≤ ρ k) (hmono : Monotone ρ) (d n : ℕ) :
    insertionRow (markedBlockWeights (C c * blockProduct ρ d)) n ≠ 0 ∧
      (insertionRow (markedBlockWeights (C c * blockProduct ρ d)) n).Splits := by
  simpa only [productRow_eq_insertionRow] using productRow_isRealRooted hc hρ hmono d n

/-- Theorem C on the standard insertion rows: simple real roots and both interlacings. -/
theorem insertionRow_roots_of_blockProduct {c : ℝ} (hc : 0 < c) {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 < ρ k) (hmono : Monotone ρ) (d n : ℕ) :
    let w := markedBlockWeights (C c * blockProduct ρ d)
    IsSimpleRealRooted (insertionRow w n) ∧
      StrictInterl (insertionRow w n) (insertionRow w (n + 1)) ∧
      StrictInterl (insertionRow w n) (insertionRow w (n + 2)) := by
  simpa only [productRow_eq_insertionRow] using productRow_roots hc hρ hmono d n

end RealRooted.ExponentialRows

