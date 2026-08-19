import RealRooted.GeneralizedSnakePosets.Narayana.Modified

/-!
# Jacobi transport for Braun--Jal Narayana inputs

This module contains the Jacobi-polynomial transport and Lemma 3.4 side lemmas
for the modified Narayana family.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-! ## Jacobi-polynomial transport for Braun--Jal Lemma 3.1 -/

/-- The change of variables used in the Jacobi-polynomial proof of
Braun--Jal Lemma 3.1. -/
def jacobi11ChangeOfVariables (r : ℝ) : ℝ :=
  (r + 1) / (r - 1)

/-- For `r ≤ 0`, the Braun--Jal Jacobi change of variables lands in
`[-1, 1]`, the interval where Gasper's Turan theorem applies. -/
theorem jacobi11ChangeOfVariables_mem_Icc_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    jacobi11ChangeOfVariables r ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · have hden : r - 1 < 0 := by linarith
    rw [jacobi11ChangeOfVariables, le_div_iff_of_neg hden]
    nlinarith
  · have hden : r - 1 < 0 := by linarith
    rw [jacobi11ChangeOfVariables, div_le_iff_of_neg hden]
    nlinarith

/-- The Braun--Jal change of variables never maps a real number to `1`. -/
theorem jacobi11ChangeOfVariables_ne_one (x : ℝ) :
    jacobi11ChangeOfVariables x ≠ 1 := by
  intro h
  by_cases hx : x = 1
  · subst x
    norm_num [jacobi11ChangeOfVariables] at h
  · have hden : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    have hmul := congrArg (fun y : ℝ => y * (x - 1)) h
    rw [jacobi11ChangeOfVariables, div_mul_cancel₀ _ hden, one_mul] at hmul
    linarith

/-- Away from the endpoint `1`, the Braun--Jal change of variables maps
`[-1, 1]` to nonpositive inputs. -/
theorem jacobi11ChangeOfVariables_nonpos_of_mem_Icc
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hx1 : x ≠ 1) :
    jacobi11ChangeOfVariables x ≤ 0 := by
  have hxleft : -1 ≤ x := hx.1
  have hxright : x ≤ 1 := hx.2
  have hlt : x < 1 := lt_of_le_of_ne hxright hx1
  rw [jacobi11ChangeOfVariables]
  exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

/-- The Braun--Jal change of variables is an involution away from the point
where its denominator vanishes. -/
theorem jacobi11ChangeOfVariables_involutive {x : ℝ} (hx : x ≠ 1) :
    jacobi11ChangeOfVariables (jacobi11ChangeOfVariables x) = x := by
  rw [jacobi11ChangeOfVariables]
  unfold jacobi11ChangeOfVariables
  field_simp [sub_ne_zero.mpr hx]
  ring

/-- The even power scale factor in Braun--Jal Lemma 3.1 is nonnegative. -/
theorem jacobi11TuranScale_nonneg (n : ℕ) (r : ℝ) :
    0 ≤ (r - 1) ^ (2 * n) := by
  simpa [pow_mul] using pow_nonneg (sq_nonneg (r - 1)) n

/-- Coefficients obtained after substituting
`x = (t + 1) / (t - 1)` into the normalized Jacobi polynomial
`R_n^(1,1)(x)`, multiplying by `(t - 1)^n`, and canceling the powers of `2`.
-/
def jacobi11TransportCoeff (n k : ℕ) : ℝ :=
  (Nat.choose (n + 1) k : ℝ) * (Nat.choose (n + 1) (n - k) : ℝ) /
    (n + 1 : ℝ)

/-- The polynomial left by the normalized Jacobi expression after the
Braun--Jal change of variables. -/
def jacobi11TransportPolynomial (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (jacobi11TransportCoeff n k) * X ^ k

@[simp] theorem coeff_jacobi11TransportPolynomial_of_le
    {n k : ℕ} (hk : k ≤ n) :
    (jacobi11TransportPolynomial n).coeff k = jacobi11TransportCoeff n k := by
  simp [jacobi11TransportPolynomial, hk]

@[simp] theorem coeff_jacobi11TransportPolynomial_of_lt
    {n k : ℕ} (hk : n < k) :
    (jacobi11TransportPolynomial n).coeff k = 0 := by
  simp [jacobi11TransportPolynomial, hk.not_ge]

/-- The normalized Jacobi transport coefficients are exactly the
`m = 1` generalized Narayana coefficients. -/
theorem jacobi11TransportCoeff_eq_narayanaTransformCoeff_one
    {n k : ℕ} (hk : k ≤ n) :
    jacobi11TransportCoeff n k = narayanaTransformCoeff 1 n k := by
  unfold jacobi11TransportCoeff narayanaTransformCoeff
  have hden_choose : (Nat.choose (1 + k) k : ℝ) = (k + 1 : ℝ) := by
    have hnat : Nat.choose (1 + k) k = k + 1 := by simp [Nat.add_comm]
    exact_mod_cast hnat
  rw [hden_choose]
  have hsym : Nat.choose (n + 1) (n - k) = Nat.choose (n + 1) (k + 1) := by
    have hle : n - k ≤ n + 1 := by lia
    have hsub : n + 1 - (n - k) = k + 1 := by lia
    rw [← Nat.choose_symm hle, hsub]
  have hchoose_nat :
      (n + 1) * Nat.choose n k =
        Nat.choose (n + 1) (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq n k
  have hchoose :
      (n + 1 : ℝ) * (Nat.choose n k : ℝ) =
        (Nat.choose (n + 1) (k + 1) : ℝ) * (k + 1 : ℝ) := by
    exact_mod_cast hchoose_nat
  rw [hsym]
  have hnz : (n + 1 : ℝ) ≠ 0 := by positivity
  have hkz : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hnz, hkz]
  nlinarith

/-- The polynomial obtained from the normalized Jacobi expression is the
coefficient-side modified Narayana polynomial. -/
theorem jacobi11TransportPolynomial_eq_coeffPolynomial (n : ℕ) :
    jacobi11TransportPolynomial n = modifiedNarayanaCoeffPolynomial n := by
  ext k
  by_cases hk : k ≤ n
  · rw [coeff_jacobi11TransportPolynomial_of_le hk,
      modifiedNarayanaCoeffPolynomial,
      coeff_narayanaPolynomial_of_le (m := 1) hk]
    exact jacobi11TransportCoeff_eq_narayanaTransformCoeff_one hk
  · have hklt : n < k := Nat.lt_of_not_ge hk
    rw [coeff_jacobi11TransportPolynomial_of_lt hklt,
      modifiedNarayanaCoeffPolynomial,
      coeff_narayanaPolynomial_of_lt (m := 1) hklt]

/-- Braun--Jal's normalized Jacobi transport polynomial is the concrete
modified Narayana polynomial. -/
theorem jacobi11TransportPolynomial_eq_modifiedNarayanaPolynomial (n : ℕ) :
    jacobi11TransportPolynomial n = modifiedNarayanaPolynomial n := by
  rw [jacobi11TransportPolynomial_eq_coeffPolynomial,
    modifiedNarayanaPolynomial_eq_coeffPolynomial]

/-- The `α = β = 1` normalized Jacobi polynomial in the explicit form used by
Braun--Jal Lemma 3.1. -/
def jacobi11NormalizedPolynomial (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (jacobi11TransportCoeff n k) *
      (C ((2 : ℝ)⁻¹) * (X - 1)) ^ (n - k) *
        (C ((2 : ℝ)⁻¹) * (X + 1)) ^ k

/-- The explicit `α = β = 1` Jacobi polynomial is normalized to take value
`1` at `1`. -/
theorem jacobi11NormalizedPolynomial_eval_one (n : ℕ) :
    (jacobi11NormalizedPolynomial n).eval 1 = 1 := by
  rw [jacobi11NormalizedPolynomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  rw [Finset.sum_eq_single n]
  · rw [jacobi11TransportCoeff, Nat.choose_succ_self_right]
    norm_num
    positivity
  · intro k hkmem hk_ne
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkmem)
    have hk_lt : k < n := lt_of_le_of_ne hk_le hk_ne
    have hsub_pos : 0 < n - k := Nat.sub_pos_of_lt hk_lt
    simp [hsub_pos.ne']
  · simp

private theorem jacobi11Transport_denominator_cancel
    {n k : ℕ} {r : ℝ} (hk : k ≤ n) (hden : r - 1 ≠ 0) :
    (r - 1) ^ n * ((r - 1)⁻¹) ^ (n - k) * (r / (r - 1)) ^ k = r ^ k := by
  have hsum : n - k + k = n := Nat.sub_add_cancel hk
  rw [div_eq_mul_inv, mul_pow]
  calc
    (r - 1) ^ n * (r - 1)⁻¹ ^ (n - k) *
        (r ^ k * (r - 1)⁻¹ ^ k)
        = r ^ k * ((r - 1) ^ n *
          ((r - 1)⁻¹ ^ (n - k) * (r - 1)⁻¹ ^ k)) := by ring
    _ = r ^ k * ((r - 1) ^ n * ((r - 1)⁻¹ ^ n)) := by rw [← pow_add, hsum]
    _ = r ^ k := by simp [hden]

/-- After Braun--Jal's change of variables, multiplying by `(r - 1)^n`
transports the normalized Jacobi polynomial to the polynomial from #108. -/
theorem jacobi11NormalizedPolynomial_transport_eval
    {n : ℕ} {r : ℝ} (hr : r ≠ 1) :
    (r - 1) ^ n *
        (jacobi11NormalizedPolynomial n).eval (jacobi11ChangeOfVariables r) =
      (jacobi11TransportPolynomial n).eval r := by
  rw [jacobi11NormalizedPolynomial, jacobi11TransportPolynomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hkmem
  have hk : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkmem)
  have hden : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  have hxsub :
      (2 : ℝ)⁻¹ * ((r + 1) / (r - 1) - 1) = (r - 1)⁻¹ := by
    field_simp [hden]
    ring
  have hxadd :
      (2 : ℝ)⁻¹ * ((r + 1) / (r - 1) + 1) = r / (r - 1) := by
    field_simp [hden]
    ring
  rw [jacobi11ChangeOfVariables, hxsub, hxadd]
  calc
    (r - 1) ^ n * (jacobi11TransportCoeff n k *
        (r - 1)⁻¹ ^ (n - k) * (r / (r - 1)) ^ k)
        = jacobi11TransportCoeff n k *
          ((r - 1) ^ n * (r - 1)⁻¹ ^ (n - k) *
            (r / (r - 1)) ^ k) := by ring
    _ = jacobi11TransportCoeff n k * r ^ k := by rw [jacobi11Transport_denominator_cancel hk hden]

/-- The quotient Narayana sequence has nonnegative coefficients, via the
coefficient-side model. -/
theorem narayanaQuot_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (narayanaQuot n) := by
  cases n with
  | zero => simp [HasNonnegCoeffs]
  | succ n =>
      have heq : narayanaQuot (n + 1) = narayanaPolynomial 1 n := by
        simpa [modifiedNarayanaPolynomial, modifiedNarayanaCoeffPolynomial]
          using modifiedNarayanaPolynomial_eq_coeffPolynomial n
      rw [heq]
      exact hasNonnegCoeffs_narayanaPolynomial 1 n

/-- Modified Narayana polynomials have nonnegative coefficients. -/
theorem modifiedNarayanaPolynomial_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (modifiedNarayanaPolynomial n) := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial n]
  exact modifiedNarayanaCoeffPolynomial_hasNonnegCoeffs n

/-- The `m = 1` Narayana coefficients are monotone in the polynomial index. -/
theorem narayanaTransformCoeff_one_mono_right {n k : ℕ} (hn : 1 ≤ n) :
    narayanaTransformCoeff 1 (n - 1) k ≤ narayanaTransformCoeff 1 n k := by
  unfold narayanaTransformCoeff
  by_cases hk : k ≤ n - 1
  · have hchoose₁ : (Nat.choose (n - 1) k : ℝ) ≤ Nat.choose n k := by
      exact_mod_cast Nat.choose_mono k (Nat.sub_le n 1)
    have hchoose₂ :
        (Nat.choose ((n - 1) + 1) k : ℝ) ≤ Nat.choose (n + 1) k := by
      exact_mod_cast Nat.choose_mono k (by lia : (n - 1) + 1 ≤ n + 1)
    gcongr
  · by_cases hkn : k ≤ n
    · have hk_eq : k = n := by lia
      subst k
      have hlt_prev : n - 1 < n := Nat.sub_one_lt (Nat.ne_of_gt hn)
      have hchoose_prev : Nat.choose (n - 1) n = 0 :=
        Nat.choose_eq_zero_of_lt hlt_prev
      rw [hchoose_prev]
      simpa using div_nonneg (by positivity : 0 ≤ ((n : ℝ) + 1))
        (by positivity : 0 ≤ ((Nat.choose (1 + n) n : ℕ) : ℝ))
    · have hlt_prev : n - 1 < k := Nat.lt_of_not_ge hk
      have hlt : n < k := Nat.lt_of_not_ge hkn
      have hchoose_prev : Nat.choose (n - 1) k = 0 :=
        Nat.choose_eq_zero_of_lt hlt_prev
      have hchoose : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt hlt
      simp [hchoose_prev, hchoose]

/-- The modified Narayana difference `P_n - P_{n-1}` has nonnegative
coefficients.  This is the coefficient fact used in Braun--Jal Lemma 3.4 to
show that the Liu--Wang lower polynomial has no positive real roots. -/
theorem modifiedNarayanaPolynomial_sub_prev_hasNonnegCoeffs
    {n : ℕ} (hn : 1 ≤ n) :
    HasNonnegCoeffs
      (modifiedNarayanaPolynomial n - modifiedNarayanaPolynomial (n - 1)) := by
  intro k
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial n,
    modifiedNarayanaPolynomial_eq_coeffPolynomial (n - 1), coeff_sub]
  dsimp [modifiedNarayanaCoeffPolynomial]
  by_cases hkprev : k ≤ n - 1
  · rw [coeff_narayanaPolynomial_of_le (m := 1) hkprev]
    have hkn : k ≤ n := by lia
    rw [coeff_narayanaPolynomial_of_le (m := 1) hkn]
    exact sub_nonneg.mpr
      (narayanaTransformCoeff_one_mono_right (n := n) (k := k) hn)
  · by_cases hkn : k ≤ n
    · have hk_eq : k = n := by lia
      subst k
      have hprev_lt : n - 1 < n := Nat.sub_one_lt (Nat.ne_of_gt hn)
      rw [coeff_narayanaPolynomial_of_le (m := 1) le_rfl,
        coeff_narayanaPolynomial_of_lt (m := 1) hprev_lt]
      simp
    · have hn_lt : n < k := Nat.lt_of_not_ge hkn
      have hprev_lt : n - 1 < k := by lia
      rw [coeff_narayanaPolynomial_of_lt (m := 1) hn_lt,
        coeff_narayanaPolynomial_of_lt (m := 1) hprev_lt]
      norm_num

/-- The named difference `Q_n = P_n - P_{n-1}` has nonnegative
coefficients for the concrete modified Narayana family. -/
theorem narayanaDifference_modified_hasNonnegCoeffs {n : ℕ} (hn : 1 ≤ n) :
    HasNonnegCoeffs (narayanaDifference modifiedNarayanaPolynomial n) := by
  simpa [narayanaDifference] using
    modifiedNarayanaPolynomial_sub_prev_hasNonnegCoeffs (n := n) hn

/-- The named difference `Q_n = P_n - P_{n-1}` has degree `n` for the
concrete modified Narayana family. -/
theorem narayanaDifference_modified_natDegree {n : ℕ} (hn : 1 ≤ n) :
    (narayanaDifference modifiedNarayanaPolynomial n).natDegree = n := by
  rw [narayanaDifference, sub_eq_add_neg]
  have hdeg : (-modifiedNarayanaPolynomial (n - 1)).natDegree <
      (modifiedNarayanaPolynomial n).natDegree := by
    rw [Polynomial.natDegree_neg, modifiedNarayanaPolynomial_natDegree,
      modifiedNarayanaPolynomial_natDegree]
    lia
  simpa [modifiedNarayanaPolynomial_natDegree] using
    natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg
      (modifiedNarayanaPolynomial_posLeadingCoeff n)

/-- The named difference `Q_n = P_n - P_{n-1}` has positive leading
coefficient for the concrete modified Narayana family. -/
theorem narayanaDifference_modified_posLeadingCoeff {n : ℕ} (hn : 1 ≤ n) :
    HasPosLeadingCoeff (narayanaDifference modifiedNarayanaPolynomial n) := by
  rw [narayanaDifference, sub_eq_add_neg]
  have hdeg : (-modifiedNarayanaPolynomial (n - 1)).natDegree <
      (modifiedNarayanaPolynomial n).natDegree := by
    rw [Polynomial.natDegree_neg, modifiedNarayanaPolynomial_natDegree,
      modifiedNarayanaPolynomial_natDegree]
    lia
  exact hasPosLeadingCoeff_add_of_natDegree_lt_left hdeg
    (modifiedNarayanaPolynomial_posLeadingCoeff n)

/-- The named difference `Q_n = P_n - P_{n-1}` is nonzero for the concrete
modified Narayana family. -/
theorem narayanaDifference_modified_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    narayanaDifference modifiedNarayanaPolynomial n ≠ 0 :=
  (narayanaDifference_modified_posLeadingCoeff hn).ne_zero

private theorem affineLinear_natDegree_le {lam mu : ℝ} :
    (C lam * X + C mu : ℝ[X]).natDegree ≤ 1 := by
  have hleft : (C lam * X : ℝ[X]).natDegree ≤ 1 := by
    calc
      (C lam * X : ℝ[X]).natDegree ≤
          (C lam : ℝ[X]).natDegree + (X : ℝ[X]).natDegree :=
        Polynomial.natDegree_mul_le
      _ = 0 + 1 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
      _ = 1 := by norm_num
  have hright : (C mu : ℝ[X]).natDegree ≤ 1 := by
    rw [Polynomial.natDegree_C]
    norm_num
  exact (Polynomial.natDegree_add_le (C lam * X : ℝ[X]) (C mu)).trans
    (max_le hleft hright)

private theorem affineLinear_natDegree_of_lam_pos
    {lam mu : ℝ} (hlam : 0 < lam) :
    (C lam * X + C mu : ℝ[X]).natDegree = 1 := by
  have hX_pos : HasPosLeadingCoeff (X : ℝ[X]) := by simp [HasPosLeadingCoeff]
  have hCX_pos : HasPosLeadingCoeff (C lam * X : ℝ[X]) :=
    hasPosLeadingCoeff_C_mul hlam hX_pos
  have hdeg : (C mu : ℝ[X]).natDegree < (C lam * X : ℝ[X]).natDegree := by
    rw [Polynomial.natDegree_C, Polynomial.natDegree_C_mul hlam.ne',
      Polynomial.natDegree_X]
    norm_num
  rw [natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg hCX_pos,
    Polynomial.natDegree_C_mul hlam.ne', Polynomial.natDegree_X]

private theorem affineLinear_posLeadingCoeff_of_lam_pos
    {lam mu : ℝ} (hlam : 0 < lam) :
    HasPosLeadingCoeff (C lam * X + C mu : ℝ[X]) := by
  have hX_pos : HasPosLeadingCoeff (X : ℝ[X]) := by simp [HasPosLeadingCoeff]
  have hCX_pos : HasPosLeadingCoeff (C lam * X : ℝ[X]) :=
    hasPosLeadingCoeff_C_mul hlam hX_pos
  have hdeg : (C mu : ℝ[X]).natDegree < (C lam * X : ℝ[X]).natDegree := by
    rw [Polynomial.natDegree_C, Polynomial.natDegree_C_mul hlam.ne',
      Polynomial.natDegree_X]
    norm_num
  exact hasPosLeadingCoeff_add_of_natDegree_lt_left hdeg hCX_pos

/-- The affine-linear modified Narayana product has degree at most `n + 1`. -/
theorem modifiedNarayana_affine_natDegree_le
    {n : ℕ} {lam mu : ℝ} :
    ((C lam * X + C mu) * modifiedNarayanaPolynomial n).natDegree ≤ n + 1 := by
  calc
    ((C lam * X + C mu) * modifiedNarayanaPolynomial n).natDegree ≤
        (C lam * X + C mu : ℝ[X]).natDegree +
          (modifiedNarayanaPolynomial n).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 1 + n := by
      exact Nat.add_le_add affineLinear_natDegree_le
        (le_of_eq (modifiedNarayanaPolynomial_natDegree n))
    _ = n + 1 := by rw [Nat.add_comm]

/-- Constant multiples of modified Narayana polynomials do not increase
degree. -/
theorem modifiedNarayana_const_mul_natDegree_le
    {n : ℕ} {mu : ℝ} :
    (C mu * modifiedNarayanaPolynomial n).natDegree ≤ n := by
  calc
    (C mu * modifiedNarayanaPolynomial n).natDegree ≤
        (C mu : ℝ[X]).natDegree + (modifiedNarayanaPolynomial n).natDegree :=
      Polynomial.natDegree_mul_le
    _ = 0 + n := by rw [Polynomial.natDegree_C, modifiedNarayanaPolynomial_natDegree]
    _ = n := by norm_num

/-- If the `X`-coefficient is positive, the affine-linear modified Narayana
product has degree exactly `n + 1`. -/
theorem modifiedNarayana_affine_natDegree_of_lam_pos
    {n : ℕ} {lam mu : ℝ} (hlam : 0 < lam) :
    ((C lam * X + C mu) * modifiedNarayanaPolynomial n).natDegree = n + 1 := by
  rw [Polynomial.natDegree_mul
    (affineLinear_posLeadingCoeff_of_lam_pos hlam).ne_zero
    (modifiedNarayanaPolynomial_ne_zero n),
    affineLinear_natDegree_of_lam_pos hlam,
    modifiedNarayanaPolynomial_natDegree]
  rw [Nat.add_comm]

/-- If the `X`-coefficient is positive, the affine-linear modified Narayana
product has positive leading coefficient. -/
theorem modifiedNarayana_affine_posLeadingCoeff_of_lam_pos
    {n : ℕ} {lam mu : ℝ} (hlam : 0 < lam) :
    HasPosLeadingCoeff ((C lam * X + C mu) * modifiedNarayanaPolynomial n) :=
  (affineLinear_posLeadingCoeff_of_lam_pos hlam).mul
    (modifiedNarayanaPolynomial_posLeadingCoeff n)

/-- The affine-linear multiple appearing in Braun--Jal's shifted Lemma 3.4 has
nonnegative coefficients for nonnegative parameters. -/
theorem modifiedNarayana_linear_hasNonnegCoeffs
    {m : ℕ} {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    HasNonnegCoeffs
      ((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1)) := by
  have hlin : HasNonnegCoeffs (C lam * X + C mu : ℝ[X]) :=
    (nonnegCoeffs_C_mul hlam hasNonnegCoeffs_X).add (hasNonnegCoeffs_C hmu)
  exact hlin.mul (modifiedNarayanaPolynomial_hasNonnegCoeffs (m - 1))

/-- The left-hand polynomial in Braun--Jal's shifted Lemma 3.4 has
nonnegative coefficients. -/
theorem lemma34ModifiedNarayanaShifted_left_hasNonnegCoeffs
    {m : ℕ} {lam mu : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    HasNonnegCoeffs
      ((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m) :=
  (modifiedNarayana_linear_hasNonnegCoeffs (m := m) hlam hmu).add
    (narayanaDifference_modified_hasNonnegCoeffs hm)

/-- The left-hand polynomial in Braun--Jal's shifted Lemma 3.4 has positive
leading coefficient. -/
theorem lemma34ModifiedNarayanaShifted_left_posLeadingCoeff
    {m : ℕ} {lam mu : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam) (_hmu : 0 ≤ mu) :
    HasPosLeadingCoeff
      ((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m) := by
  rcases lt_or_eq_of_le hlam with hlam_pos | hlam_zero
  · have hA_pos := modifiedNarayana_affine_posLeadingCoeff_of_lam_pos
      (n := m - 1) (mu := mu) hlam_pos
    have hA_deg :
        ((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1)).natDegree =
          m := by
      simpa [Nat.sub_add_cancel hm] using
        modifiedNarayana_affine_natDegree_of_lam_pos
          (n := m - 1) (mu := mu) hlam_pos
    have hQ_pos := narayanaDifference_modified_posLeadingCoeff hm
    have hQ_deg := narayanaDifference_modified_natDegree hm
    exact hasPosLeadingCoeff_add_of_same_natDegree (by rw [hA_deg, hQ_deg])
      hA_pos hQ_pos
  · subst lam
    have hA_le :
        ((C (0 : ℝ) * X + C mu) *
          modifiedNarayanaPolynomial (m - 1)).natDegree ≤ m - 1 := by
      simpa using modifiedNarayana_const_mul_natDegree_le
        (n := m - 1) (mu := mu)
    have hQ_pos := narayanaDifference_modified_posLeadingCoeff hm
    have hQ_deg := narayanaDifference_modified_natDegree hm
    have hA_lt :
        ((C (0 : ℝ) * X + C mu) *
          modifiedNarayanaPolynomial (m - 1)).natDegree <
            (narayanaDifference modifiedNarayanaPolynomial m).natDegree := by
      rw [hQ_deg]
      exact lt_of_le_of_lt hA_le (Nat.sub_one_lt (Nat.ne_of_gt hm))
    exact hasPosLeadingCoeff_add_of_natDegree_lt_right hA_lt hQ_pos

/-- The left-hand polynomial in Braun--Jal's shifted Lemma 3.4 has degree
`m`. -/
theorem lemma34ModifiedNarayanaShifted_left_natDegree
    {m : ℕ} {lam mu : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam) (_hmu : 0 ≤ mu) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).natDegree = m) := by
  rcases lt_or_eq_of_le hlam with hlam_pos | hlam_zero
  · have hA_pos := modifiedNarayana_affine_posLeadingCoeff_of_lam_pos
      (n := m - 1) (mu := mu) hlam_pos
    have hA_deg :
        ((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1)).natDegree =
          m := by
      simpa [Nat.sub_add_cancel hm] using
        modifiedNarayana_affine_natDegree_of_lam_pos
          (n := m - 1) (mu := mu) hlam_pos
    have hQ_pos := narayanaDifference_modified_posLeadingCoeff hm
    have hQ_deg := narayanaDifference_modified_natDegree hm
    simpa [hA_deg] using
      natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff (by rw [hA_deg, hQ_deg])
        hA_pos hQ_pos
  · subst lam
    have hA_le :
        ((C (0 : ℝ) * X + C mu) *
          modifiedNarayanaPolynomial (m - 1)).natDegree ≤ m - 1 := by
      simpa using modifiedNarayana_const_mul_natDegree_le
        (n := m - 1) (mu := mu)
    have hQ_pos := narayanaDifference_modified_posLeadingCoeff hm
    have hQ_deg := narayanaDifference_modified_natDegree hm
    have hA_lt :
        ((C (0 : ℝ) * X + C mu) *
          modifiedNarayanaPolynomial (m - 1)).natDegree <
            (narayanaDifference modifiedNarayanaPolynomial m).natDegree := by
      rw [hQ_deg]
      exact lt_of_le_of_lt hA_le (Nat.sub_one_lt (Nat.ne_of_gt hm))
    simpa [hQ_deg] using
      natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hA_lt hQ_pos

/-- The left-hand polynomial in Braun--Jal's shifted Lemma 3.4 is nonzero. -/
theorem lemma34ModifiedNarayanaShifted_left_ne_zero
    {m : ℕ} {lam mu : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    (C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
      narayanaDifference modifiedNarayanaPolynomial m ≠ 0 :=
  (lemma34ModifiedNarayanaShifted_left_posLeadingCoeff hm hlam hmu).ne_zero

/-- In Braun--Jal's shifted Lemma 3.4, the previous modified Narayana
polynomial interlaces the left-hand polynomial. -/
theorem lemma34ModifiedNarayanaShifted_prev_interlaces_left
    {m : ℕ} {lam mu : ℝ} (hm : 2 ≤ m) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    Interlaces (modifiedNarayanaPolynomial (m - 1))
      ((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by lia⟩
  let a : ℝ[X] := C lam * X + C mu + narayanaCoeffA (k + 1) - 1
  let b : ℝ[X] := narayanaCoeffB (k + 1)
  have hleft_eq :
      a * modifiedNarayanaPolynomial (k + 1) +
          b * modifiedNarayanaPolynomial k =
        (C lam * X + C mu) * modifiedNarayanaPolynomial (k + 1) +
          narayanaDifference modifiedNarayanaPolynomial (k + 2) := by
    rw [narayanaDifference, modifiedNarayanaPolynomial_succ_succ k]
    simp [a, b]
    ring
  have hleft_deg :
      (((C lam * X + C mu) * modifiedNarayanaPolynomial (k + 1) +
        narayanaDifference modifiedNarayanaPolynomial (k + 2)).natDegree =
          k + 2) := by
    simpa using lemma34ModifiedNarayanaShifted_left_natDegree
      (m := k + 2) (by lia) hlam hmu
  have hprec :
      Prec (modifiedNarayanaPolynomial (k + 1))
        (a * modifiedNarayanaPolynomial (k + 1) +
          b * modifiedNarayanaPolynomial k) := by
    have hF_pos :
        HasPosLeadingCoeff
          (a * modifiedNarayanaPolynomial (k + 1) +
            b * modifiedNarayanaPolynomial k) := by
      rw [hleft_eq]
      exact lemma34ModifiedNarayanaShifted_left_posLeadingCoeff
        (m := k + 2) (by lia) hlam hmu
    have hdeg_lo :
        (modifiedNarayanaPolynomial (k + 1)).natDegree ≤
          (a * modifiedNarayanaPolynomial (k + 1) +
            b * modifiedNarayanaPolynomial k).natDegree := by
      rw [hleft_eq, modifiedNarayanaPolynomial_natDegree, hleft_deg]
      lia
    have hdeg_hi :
        (a * modifiedNarayanaPolynomial (k + 1) +
          b * modifiedNarayanaPolynomial k).natDegree ≤
            (modifiedNarayanaPolynomial (k + 1)).natDegree + 1 := by
      rw [hleft_eq, modifiedNarayanaPolynomial_natDegree, hleft_deg]
    have hb_nonpos :
        ∀ r, (modifiedNarayanaPolynomial (k + 1)).IsRoot r → b.eval r ≤ 0 := by
      intro r _hr
      simpa [b] using narayanaCoeffB_eval_nonpos (k + 1) r
    exact
      prec_of_interlaces_evalCoeff_nonpos
        (modifiedNarayanaPolynomial_interlaces_succ_of_nonnegCoeffs k
          narayanaQuot_hasNonnegCoeffs)
        (modifiedNarayanaPolynomial_posLeadingCoeff k)
        hF_pos hdeg_lo hdeg_hi hb_nonpos
  rw [hleft_eq] at hprec
  exact hprec.toInterlaces (by
    rw [modifiedNarayanaPolynomial_natDegree, hleft_deg])

/-- The shifted Lemma 3.4 left-hand polynomial has no common root with the
previous modified Narayana polynomial. -/
theorem lemma34ModifiedNarayanaShifted_left_no_common_prev
    {m : ℕ} {lam mu : ℝ} (hm : 1 ≤ m) :
    ∀ r : ℝ,
      (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r) →
        ¬ (modifiedNarayanaPolynomial (m - 1)).IsRoot r := by
  intro r hr hprev
  have hprev_eval : (modifiedNarayanaPolynomial (m - 1)).eval r = 0 :=
    Polynomial.IsRoot.def.mp hprev
  have hm_root : (modifiedNarayanaPolynomial m).IsRoot r := by
    rw [Polynomial.IsRoot.def]
    have hr_eval := Polynomial.IsRoot.def.mp hr
    simpa [narayanaDifference, eval_add, eval_sub, eval_mul, hprev_eval] using hr_eval
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by lia⟩
  exact modifiedNarayanaPolynomial_no_common_root n r (by simpa using hm_root)
    (by simpa using hprev)

/-- The right-hand polynomial in Braun--Jal's shifted Lemma 3.4 has
nonnegative coefficients. -/
theorem lemma34ModifiedNarayanaShifted_right_hasNonnegCoeffs
    {m : ℕ} {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    HasNonnegCoeffs
      ((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)) :=
  (modifiedNarayana_linear_hasNonnegCoeffs (m := m + 1) hlam hmu).add
    (narayanaDifference_modified_hasNonnegCoeffs (by lia : 1 ≤ m + 1))

/-- The right-hand polynomial in Braun--Jal's shifted Lemma 3.4 has positive
leading coefficient. -/
theorem lemma34ModifiedNarayanaShifted_right_posLeadingCoeff
    {m : ℕ} {lam mu : ℝ} (hlam : 0 ≤ lam) (_hmu : 0 ≤ mu) :
    HasPosLeadingCoeff
      ((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)) := by
  rcases lt_or_eq_of_le hlam with hlam_pos | hlam_zero
  · have hA_pos := modifiedNarayana_affine_posLeadingCoeff_of_lam_pos
      (n := m) (mu := mu) hlam_pos
    have hA_deg := modifiedNarayana_affine_natDegree_of_lam_pos
      (n := m) (mu := mu) hlam_pos
    have hQ_pos := narayanaDifference_modified_posLeadingCoeff
      (n := m + 1) (by lia : 1 ≤ m + 1)
    have hQ_deg := narayanaDifference_modified_natDegree
      (n := m + 1) (by lia : 1 ≤ m + 1)
    exact hasPosLeadingCoeff_add_of_same_natDegree (by rw [hA_deg, hQ_deg])
      hA_pos hQ_pos
  · subst lam
    have hA_le :
        ((C (0 : ℝ) * X + C mu) *
          modifiedNarayanaPolynomial m).natDegree ≤ m := by
      simpa using modifiedNarayana_const_mul_natDegree_le (n := m) (mu := mu)
    have hQ_pos := narayanaDifference_modified_posLeadingCoeff
      (n := m + 1) (by lia : 1 ≤ m + 1)
    have hQ_deg := narayanaDifference_modified_natDegree
      (n := m + 1) (by lia : 1 ≤ m + 1)
    have hA_lt :
        ((C (0 : ℝ) * X + C mu) * modifiedNarayanaPolynomial m).natDegree <
          (narayanaDifference modifiedNarayanaPolynomial (m + 1)).natDegree := by
      rw [hQ_deg]
      exact Nat.lt_succ_of_le hA_le
    exact hasPosLeadingCoeff_add_of_natDegree_lt_right hA_lt hQ_pos

/-- The right-hand polynomial in Braun--Jal's shifted Lemma 3.4 has degree
`m + 1`. -/
theorem lemma34ModifiedNarayanaShifted_right_natDegree
    {m : ℕ} {lam mu : ℝ} (hlam : 0 ≤ lam) (_hmu : 0 ≤ mu) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).natDegree =
          m + 1) := by
  rcases lt_or_eq_of_le hlam with hlam_pos | hlam_zero
  · have hA_pos := modifiedNarayana_affine_posLeadingCoeff_of_lam_pos
      (n := m) (mu := mu) hlam_pos
    have hA_deg := modifiedNarayana_affine_natDegree_of_lam_pos
      (n := m) (mu := mu) hlam_pos
    have hQ_pos := narayanaDifference_modified_posLeadingCoeff
      (n := m + 1) (by lia : 1 ≤ m + 1)
    have hQ_deg := narayanaDifference_modified_natDegree
      (n := m + 1) (by lia : 1 ≤ m + 1)
    simpa [hA_deg] using
      natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff (by rw [hA_deg, hQ_deg])
        hA_pos hQ_pos
  · subst lam
    have hA_le :
        ((C (0 : ℝ) * X + C mu) *
          modifiedNarayanaPolynomial m).natDegree ≤ m := by
      simpa using modifiedNarayana_const_mul_natDegree_le (n := m) (mu := mu)
    have hQ_pos := narayanaDifference_modified_posLeadingCoeff
      (n := m + 1) (by lia : 1 ≤ m + 1)
    have hQ_deg := narayanaDifference_modified_natDegree
      (n := m + 1) (by lia : 1 ≤ m + 1)
    have hA_lt :
        ((C (0 : ℝ) * X + C mu) * modifiedNarayanaPolynomial m).natDegree <
          (narayanaDifference modifiedNarayanaPolynomial (m + 1)).natDegree := by
      rw [hQ_deg]
      exact Nat.lt_succ_of_le hA_le
    simpa [hQ_deg] using
      natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hA_lt hQ_pos

/-- The right-hand polynomial in Braun--Jal's shifted Lemma 3.4 is nonzero. -/
theorem lemma34ModifiedNarayanaShifted_right_ne_zero
    {m : ℕ} {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    (C lam * X + C mu) * modifiedNarayanaPolynomial m +
      narayanaDifference modifiedNarayanaPolynomial (m + 1) ≠ 0 :=
  (lemma34ModifiedNarayanaShifted_right_posLeadingCoeff hlam hmu).ne_zero

/-- The left-hand polynomial in the shifted Lemma 3.4 route has no positive
roots. -/
theorem lemma34ModifiedNarayanaShifted_left_roots_nonpos
    {m : ℕ} {lam mu : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    ∀ r ∈ (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
      narayanaDifference modifiedNarayanaPolynomial m).roots), r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs
    (lemma34ModifiedNarayanaShifted_left_hasNonnegCoeffs hm hlam hmu)

/-- IsRoot-facing form of
`lemma34ModifiedNarayanaShifted_left_roots_nonpos`. -/
theorem lemma34ModifiedNarayanaShifted_left_isRoot_nonpos
    {m : ℕ} {lam mu : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam)
    (hmu : 0 ≤ mu)
    (hne :
      (C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m ≠ 0) :
    ∀ r,
      (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r) → r ≤ 0 := by
  intro r hr
  exact lemma34ModifiedNarayanaShifted_left_roots_nonpos hm hlam hmu r
    ((Polynomial.mem_roots hne).mpr hr)

/-- The right-hand polynomial in the shifted Lemma 3.4 route has no positive
roots. -/
theorem lemma34ModifiedNarayanaShifted_right_roots_nonpos
    {m : ℕ} {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    ∀ r ∈ (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
      narayanaDifference modifiedNarayanaPolynomial (m + 1)).roots), r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs
    (lemma34ModifiedNarayanaShifted_right_hasNonnegCoeffs hlam hmu)

/-- IsRoot-facing form of
`lemma34ModifiedNarayanaShifted_right_roots_nonpos`. -/
theorem lemma34ModifiedNarayanaShifted_right_isRoot_nonpos
    {m : ℕ} {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hne :
      (C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1) ≠ 0) :
    ∀ r,
      (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).IsRoot r) →
          r ≤ 0 := by
  intro r hr
  exact lemma34ModifiedNarayanaShifted_right_roots_nonpos hlam hmu r
    ((Polynomial.mem_roots hne).mpr hr)

private theorem lemma34ModifiedNarayanaShifted_left_eq_paper
    {m : ℕ} {lam nu : ℝ} :
    ((C lam * X + (C nu + 1)) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m) =
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m) := by
  rw [narayanaDifference]
  ring_nf

private theorem lemma34ModifiedNarayanaShifted_right_eq_paper
    {m : ℕ} {lam nu : ℝ} :
    ((C lam * X + (C nu + 1)) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)) =
      ((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)) := by
  rw [narayanaDifference]
  simp only [Nat.add_sub_cancel]
  ring_nf

/-- The paper-shaped left-hand polynomial in Braun--Jal Lemma 3.4 has
nonnegative coefficients when `ν ≥ -1`. -/
theorem lemma34ModifiedNarayana_left_hasNonnegCoeffs
    {m : ℕ} {lam nu : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    HasNonnegCoeffs
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m) := by
  have hmu : 0 ≤ nu + 1 := by linarith
  have hbase :=
    lemma34ModifiedNarayanaShifted_left_hasNonnegCoeffs
      (m := m) (lam := lam) (mu := nu + 1) hm hlam hmu
  simpa [lemma34ModifiedNarayanaShifted_left_eq_paper] using hbase

/-- The paper-shaped right-hand polynomial in Braun--Jal Lemma 3.4 has
nonnegative coefficients when `ν ≥ -1`. -/
theorem lemma34ModifiedNarayana_right_hasNonnegCoeffs
    {m : ℕ} {lam nu : ℝ} (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    HasNonnegCoeffs
      ((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)) := by
  have hmu : 0 ≤ nu + 1 := by linarith
  have hbase :=
    lemma34ModifiedNarayanaShifted_right_hasNonnegCoeffs
      (m := m) (lam := lam) (mu := nu + 1) hlam hmu
  simpa [lemma34ModifiedNarayanaShifted_right_eq_paper] using hbase

/-- The paper-shaped left-hand polynomial in Braun--Jal Lemma 3.4 has positive
leading coefficient when `ν ≥ -1`. -/
theorem lemma34ModifiedNarayana_left_posLeadingCoeff
    {m : ℕ} {lam nu : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    HasPosLeadingCoeff
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m) := by
  have hmu : 0 ≤ nu + 1 := by linarith
  have hbase :=
    lemma34ModifiedNarayanaShifted_left_posLeadingCoeff
      (m := m) (lam := lam) (mu := nu + 1) hm hlam hmu
  simpa [lemma34ModifiedNarayanaShifted_left_eq_paper] using hbase

/-- The paper-shaped left-hand polynomial in Braun--Jal Lemma 3.4 has degree
`m` when `ν ≥ -1`. -/
theorem lemma34ModifiedNarayana_left_natDegree
    {m : ℕ} {lam nu : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).natDegree = m) := by
  have hmu : 0 ≤ nu + 1 := by linarith
  have hbase :=
    lemma34ModifiedNarayanaShifted_left_natDegree
      (m := m) (lam := lam) (mu := nu + 1) hm hlam hmu
  simpa [lemma34ModifiedNarayanaShifted_left_eq_paper] using hbase

/-- The paper-shaped left-hand polynomial in Braun--Jal Lemma 3.4 is nonzero
when `ν ≥ -1`. -/
theorem lemma34ModifiedNarayana_left_ne_zero
    {m : ℕ} {lam nu : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    (C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
      modifiedNarayanaPolynomial m ≠ 0 :=
  (lemma34ModifiedNarayana_left_posLeadingCoeff hm hlam hnu).ne_zero

/-- The paper-shaped right-hand polynomial in Braun--Jal Lemma 3.4 has
positive leading coefficient when `ν ≥ -1`. -/
theorem lemma34ModifiedNarayana_right_posLeadingCoeff
    {m : ℕ} {lam nu : ℝ} (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    HasPosLeadingCoeff
      ((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)) := by
  have hmu : 0 ≤ nu + 1 := by linarith
  have hbase :=
    lemma34ModifiedNarayanaShifted_right_posLeadingCoeff
      (m := m) (lam := lam) (mu := nu + 1) hlam hmu
  simpa [lemma34ModifiedNarayanaShifted_right_eq_paper] using hbase

/-- The paper-shaped right-hand polynomial in Braun--Jal Lemma 3.4 has degree
`m + 1` when `ν ≥ -1`. -/
theorem lemma34ModifiedNarayana_right_natDegree
    {m : ℕ} {lam nu : ℝ} (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).natDegree = m + 1) := by
  have hmu : 0 ≤ nu + 1 := by linarith
  have hbase :=
    lemma34ModifiedNarayanaShifted_right_natDegree
      (m := m) (lam := lam) (mu := nu + 1) hlam hmu
  simpa [lemma34ModifiedNarayanaShifted_right_eq_paper] using hbase

/-- The paper-shaped right-hand polynomial in Braun--Jal Lemma 3.4 is nonzero
when `ν ≥ -1`. -/
theorem lemma34ModifiedNarayana_right_ne_zero
    {m : ℕ} {lam nu : ℝ} (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    (C lam * X + C nu) * modifiedNarayanaPolynomial m +
      modifiedNarayanaPolynomial (m + 1) ≠ 0 :=
  (lemma34ModifiedNarayana_right_posLeadingCoeff hlam hnu).ne_zero

/-- The paper-shaped left-hand polynomial in Braun--Jal Lemma 3.4 has no
positive roots. -/
theorem lemma34ModifiedNarayana_left_roots_nonpos
    {m : ℕ} {lam nu : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    ∀ r ∈ (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
      modifiedNarayanaPolynomial m).roots), r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs
    (lemma34ModifiedNarayana_left_hasNonnegCoeffs hm hlam hnu)

/-- The paper-shaped right-hand polynomial in Braun--Jal Lemma 3.4 has no
positive roots. -/
theorem lemma34ModifiedNarayana_right_roots_nonpos
    {m : ℕ} {lam nu : ℝ} (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    ∀ r ∈ (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
      modifiedNarayanaPolynomial (m + 1)).roots), r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs
    (lemma34ModifiedNarayana_right_hasNonnegCoeffs hlam hnu)

/-- IsRoot-facing form of `lemma34ModifiedNarayana_left_roots_nonpos`. -/
theorem lemma34ModifiedNarayana_left_isRoot_nonpos
    {m : ℕ} {lam nu r : ℝ} (hm : 1 ≤ m) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hr :
      (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).IsRoot r)) :
    r ≤ 0 :=
  lemma34ModifiedNarayana_left_roots_nonpos hm hlam hnu r
    ((Polynomial.mem_roots
      (lemma34ModifiedNarayana_left_ne_zero hm hlam hnu)).mpr hr)

/-- IsRoot-facing form of `lemma34ModifiedNarayana_right_roots_nonpos`. -/
theorem lemma34ModifiedNarayana_right_isRoot_nonpos
    {m : ℕ} {lam nu r : ℝ} (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hr :
      (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).IsRoot r)) :
    r ≤ 0 :=
  lemma34ModifiedNarayana_right_roots_nonpos hlam hnu r
    ((Polynomial.mem_roots
      (lemma34ModifiedNarayana_right_ne_zero hlam hnu)).mpr hr)

end GeneralizedSnakePosets
end RealRooted
