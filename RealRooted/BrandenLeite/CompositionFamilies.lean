import RealRooted.BrandenLeite.ZeroConstant
import RealRooted.BrandenLeite.TwoKernelAlgebra
import RealRooted.BrandenVecchi.SupersymmetricCoefficients
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Polynomial.Div

/-!
# Finite supersymmetric composition-row families

This file packages the positive-order kernels

`z * prod_i (1 + x_i z) / prod_j (1 - y_j z)`

and applies the zero-constant composition-row theorem.  The parameterized API
keeps the Pólya-frequency argument independent of the later OEIS
specializations.
-/

open Polynomial

namespace RealRooted.BrandenLeite

noncomputable section

open BrandenVecchi

/-- Insert one initial zero before the coefficients of a finite
supersymmetric product. -/
def shiftedFiniteSupersymmetricCoeff
    (xs ys : List ℝ) (n : ℕ) : ℝ :=
  if 1 ≤ n then finiteSupersymmetricCoeff xs ys (n - 1) else 0

@[simp]
theorem shiftedFiniteSupersymmetricCoeff_zero (xs ys : List ℝ) :
    shiftedFiniteSupersymmetricCoeff xs ys 0 = 0 := by
  simp [shiftedFiniteSupersymmetricCoeff]

@[simp]
theorem shiftedFiniteSupersymmetricCoeff_succ
    (xs ys : List ℝ) (n : ℕ) :
    shiftedFiniteSupersymmetricCoeff xs ys (n + 1) =
      finiteSupersymmetricCoeff xs ys n := by
  simp [shiftedFiniteSupersymmetricCoeff]

/-- The generating series of the shifted coefficients is multiplication by
the series variable. -/
theorem mk_shiftedFiniteSupersymmetricCoeff
    (xs ys : List ℝ) :
    PowerSeries.mk (shiftedFiniteSupersymmetricCoeff xs ys) =
      PowerSeries.X * finiteSupersymmetricSeries xs ys := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      simp [finiteSupersymmetricCoeff]

/-- A positive-order finite supersymmetric product has a PF coefficient
sequence whenever all numerator and denominator parameters are nonnegative. -/
theorem shiftedFiniteSupersymmetricCoeff_isPolyaFreqSeq
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) :
    IsPolyaFreqSeq (shiftedFiniteSupersymmetricCoeff xs ys) := by
  change IsPolyaFreqSeq fun n =>
    if 1 ≤ n then finiteSupersymmetricCoeff xs ys (n - 1) else 0
  exact (finiteSupersymmetricCoeff_isPolyaFreqSeq hxs hys).prefix_zeros 1

/-- All composition rows of a positive-order finite supersymmetric product
are PF, and consecutive rows are in zero-aware proper position. -/
theorem shiftedFiniteSupersymmetricCompositionRows_pf_and_prec0
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) :
    (∀ n, IsPFPolynomial
      (compositionRow
        (PowerSeries.mk (shiftedFiniteSupersymmetricCoeff xs ys)) n)) ∧
      ∀ n, Interl
        (compositionRow
          (PowerSeries.mk (shiftedFiniteSupersymmetricCoeff xs ys)) n)
        (compositionRow
          (PowerSeries.mk (shiftedFiniteSupersymmetricCoeff xs ys)) (n + 1)) := by
  exact compositionRows_mk_pf_and_prec0_of_zero
    (shiftedFiniteSupersymmetricCoeff_isPolyaFreqSeq hxs hys)
    (shiftedFiniteSupersymmetricCoeff_zero xs ys)

/-! ## Polynomial-valued generating series -/

/-- The formal series whose `n`th coefficient is the `n`th composition row. -/
def compositionRowGeneratingSeries {R : Type*} [CommSemiring R]
    (h : PowerSeries R) : PowerSeries R[X] :=
  PowerSeries.mk (compositionRow h)

@[simp]
theorem coeff_compositionRowGeneratingSeries
    {R : Type*} [CommSemiring R]
    (h : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (compositionRowGeneratingSeries h) =
      compositionRow h n := by
  simp [compositionRowGeneratingSeries]

/-- A composition row is the unit-background specialization of a literal
two-kernel row. -/
theorem twoKernelRow_one_eq_compositionRow
    {R : Type*} [CommSemiring R]
    (h : PowerSeries R) (n : ℕ) :
    twoKernelRow 1 h n = compositionRow h n := by
  simp [twoKernelRow, compositionRow]

/-- Exact geometric denominator identity for composition rows. -/
theorem one_sub_mul_compositionRowGeneratingSeries
    {R : Type*} [CommRing R] {h : PowerSeries R}
    (hzero : PowerSeries.constantCoeff h = 0) :
    (1 - PowerSeries.C X * polynomialLift h) *
        compositionRowGeneratingSeries h = 1 := by
  have htwo := one_sub_mul_twoKernelGeneratingSeries
    (g := (1 : PowerSeries R)) hzero
  have hseries :
      twoKernelGeneratingSeries (1 : PowerSeries R) h =
        compositionRowGeneratingSeries h := by
    ext n
    rw [coeff_twoKernelGeneratingSeries,
      coeff_compositionRowGeneratingSeries,
      twoKernelRow_one_eq_compositionRow]
  rw [← hseries]
  simpa using htwo

/-! ## Binomial numerator families -/

/-- Repeating the unit numerator parameter produces a binomial power. -/
theorem finiteSupersymmetricSeries_replicate_one_nil (d : ℕ) :
    finiteSupersymmetricSeries (List.replicate d 1) [] =
      (1 + PowerSeries.X) ^ d := by
  simp [finiteSupersymmetricSeries, supersymmetricNumeratorFactor]

/-- The positive-order binomial kernel `z (1 + z)^d`. -/
def binomialCompositionKernel (d : ℕ) : ℕ → ℝ :=
  shiftedFiniteSupersymmetricCoeff (List.replicate d 1) []

/-- Exact formal-series identity for the binomial kernel. -/
theorem mk_binomialCompositionKernel (d : ℕ) :
    PowerSeries.mk (binomialCompositionKernel d) =
      PowerSeries.X * (1 + PowerSeries.X) ^ d := by
  rw [binomialCompositionKernel,
    mk_shiftedFiniteSupersymmetricCoeff,
    finiteSupersymmetricSeries_replicate_one_nil]

/-- Exact coefficient of a power of the binomial kernel. -/
theorem coeff_binomialCompositionKernel_pow
    (d n k : ℕ) (hkn : k ≤ n) :
    PowerSeries.coeff n
        ((PowerSeries.mk (binomialCompositionKernel d)) ^ k) =
      (Nat.choose (d * k) (n - k) : ℝ) := by
  rw [mk_binomialCompositionKernel, mul_pow, ← pow_mul]
  rw [PowerSeries.coeff_X_pow_mul']
  rw [if_pos hkn]
  have hcoe :
      ((1 + PowerSeries.X : PowerSeries ℝ) ^ (d * k)) =
        (((1 + X : ℝ[X]) ^ (d * k) : ℝ[X]) : PowerSeries ℝ) := by
    simp
  rw [hcoe, Polynomial.coeff_coe,
    Polynomial.coeff_one_add_X_pow]

/-- The finite binomial row formula
`sum_k choose (d*k) (n-k) X^k`. -/
theorem compositionRow_binomialCompositionKernel (d n : ℕ) :
    compositionRow (PowerSeries.mk (binomialCompositionKernel d)) n =
      ∑ k ∈ Finset.range (n + 1),
        C (Nat.choose (d * k) (n - k) : ℝ) * X ^ k := by
  rw [compositionRow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff_binomialCompositionKernel_pow d n k (by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk))]

/-- Coefficients of a binomial composition row, including indices beyond the
finite row. -/
theorem coeff_compositionRow_binomialCompositionKernel
    (d n k : ℕ) :
    (compositionRow
        (PowerSeries.mk (binomialCompositionKernel d)) n).coeff k =
      if k ≤ n then (Nat.choose (d * k) (n - k) : ℝ) else 0 := by
  rw [coeff_compositionRow (by simp [binomialCompositionKernel])]
  by_cases hkn : k ≤ n
  · rw [if_pos hkn, coeff_binomialCompositionKernel_pow d n k hkn]
  · rw [if_neg hkn,
      coeff_pow_eq_zero_of_lt
        (by simp [binomialCompositionKernel]) (Nat.lt_of_not_ge hkn)]

/-- For a binomial composition row, the exact multiplicity of
the zero root is `ceil(n / (d+1))`, expressed by consecutive divisibility
certificates. -/
theorem binomialCompositionRow_exact_X_power
    (d n : ℕ) :
    let m := n ⌈/⌉ (d + 1)
    X ^ m ∣ compositionRow
        (PowerSeries.mk (binomialCompositionKernel d)) n ∧
      ¬X ^ (m + 1) ∣ compositionRow
        (PowerSeries.mk (binomialCompositionKernel d)) n := by
  let m := n ⌈/⌉ (d + 1)
  have hden : 0 < d + 1 := by positivity
  have hnle : n ≤ (d + 1) * m := by
    exact (ceilDiv_le_iff_le_mul hden).mp le_rfl
  have hmle : m ≤ n := by
    rw [ceilDiv_le_iff_le_mul hden]
    simp [Nat.add_mul, Nat.add_comm]
  have hcoeffm :
      (compositionRow
          (PowerSeries.mk (binomialCompositionKernel d)) n).coeff m ≠ 0 := by
    rw [coeff_compositionRow_binomialCompositionKernel,
      if_pos hmle]
    have hsum : n ≤ m + d * m := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        Nat.add_mul] using hnle
    have hchoose : Nat.choose (d * m) (n - m) ≠ 0 :=
      Nat.choose_ne_zero_iff.mpr (Nat.sub_le_iff_le_add.mpr (by
        simpa [Nat.add_comm] using hsum))
    exact_mod_cast hchoose
  constructor
  · rw [Polynomial.X_pow_dvd_iff]
    intro k hk
    rw [coeff_compositionRow_binomialCompositionKernel]
    by_cases hkn : k ≤ n
    · rw [if_pos hkn, Nat.cast_eq_zero,
        Nat.choose_eq_zero_of_lt]
      have hprodlt : (d + 1) * k < n := by
        by_contra hnot
        have hnprod : n ≤ (d + 1) * k := le_of_not_gt hnot
        have hmk : m ≤ k :=
          (ceilDiv_le_iff_le_mul hden).mpr hnprod
        exact (Nat.not_le_of_lt hk) hmk
      rw [Nat.lt_sub_iff_add_lt]
      simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hprodlt
    · rw [if_neg hkn]
  · intro hdvd
    have hz := (Polynomial.X_pow_dvd_iff.mp hdvd) m
      (Nat.lt_succ_self m)
    exact hcoeffm hz

/-- Binomial composition rows are PF and consecutive rows are in zero-aware
proper position. -/
theorem binomialCompositionRows_pf_and_prec0 (d : ℕ) :
    (∀ n, IsPFPolynomial
      (compositionRow (PowerSeries.mk (binomialCompositionKernel d)) n)) ∧
      ∀ n, Interl
        (compositionRow (PowerSeries.mk (binomialCompositionKernel d)) n)
        (compositionRow
          (PowerSeries.mk (binomialCompositionKernel d)) (n + 1)) := by
  simpa [binomialCompositionKernel] using
    (shiftedFiniteSupersymmetricCompositionRows_pf_and_prec0
      (xs := List.replicate d 1) (ys := []) (by simp) (by simp))

/-- Every nonzero root of a binomial composition row is strictly negative. -/
theorem binomialCompositionRow_nonzero_roots_neg
    (d n : ℕ) {r : ℝ}
    (hr : r ∈ (compositionRow
      (PowerSeries.mk (binomialCompositionKernel d)) n).roots)
    (hr0 : r ≠ 0) : r < 0 := by
  exact lt_of_le_of_ne
    ((binomialCompositionRows_pf_and_prec0 d).1 n |>.roots_nonpos r hr)
    hr0

/-! ## Negative-binomial denominator families -/

/-- Repeating the unit denominator parameter produces a power of the
geometric series. -/
theorem finiteSupersymmetricSeries_nil_replicate_one (e : ℕ) :
    finiteSupersymmetricSeries [] (List.replicate e 1) =
      (PowerSeries.mk 1 : PowerSeries ℝ) ^ e := by
  simp [finiteSupersymmetricSeries, supersymmetricDenominatorFactor]

/-- The positive-order inverse-power kernel `z / (1-z)^e`. -/
def inversePowerCompositionKernel (e : ℕ) : ℕ → ℝ :=
  shiftedFiniteSupersymmetricCoeff [] (List.replicate e 1)

/-- Exact formal-series identity for the inverse-power kernel. -/
theorem mk_inversePowerCompositionKernel (e : ℕ) :
    PowerSeries.mk (inversePowerCompositionKernel e) =
      PowerSeries.X * (PowerSeries.mk 1 : PowerSeries ℝ) ^ e := by
  rw [inversePowerCompositionKernel,
    mk_shiftedFiniteSupersymmetricCoeff,
    finiteSupersymmetricSeries_nil_replicate_one]

/-- Guarded negative-binomial coefficient of a positive power of the
inverse-power kernel. -/
theorem coeff_inversePowerCompositionKernel_pow
    {e n k : ℕ} (he : 1 ≤ e) (hk : 1 ≤ k) (hkn : k ≤ n) :
    PowerSeries.coeff n
        ((PowerSeries.mk (inversePowerCompositionKernel e)) ^ k) =
      (Nat.choose (e * k - 1 + (n - k)) (e * k - 1) : ℝ) := by
  rw [mk_inversePowerCompositionKernel, mul_pow, ← pow_mul]
  rw [PowerSeries.coeff_X_pow_mul', if_pos hkn]
  have hek : e * k = (e * k - 1) + 1 := by
    exact (Nat.sub_add_cancel
      (Nat.succ_le_iff.mpr (Nat.mul_pos (by lia) (by lia)))).symm
  rw [hek, PowerSeries.mk_one_pow_eq_mk_choose_add]
  simp

/-- The guarded coefficient used in an inverse-power composition row.  The
exceptional zeroth power is kept explicit. -/
def inversePowerCompositionRowCoeff
    (e n k : ℕ) : ℝ :=
  if k = 0 then if n = 0 then 1 else 0
  else Nat.choose (e * k - 1 + (n - k)) (e * k - 1)

/-- Exact guarded negative-binomial row formula. -/
theorem compositionRow_inversePowerCompositionKernel
    {e : ℕ} (he : 1 ≤ e) (n : ℕ) :
    compositionRow (PowerSeries.mk (inversePowerCompositionKernel e)) n =
      ∑ k ∈ Finset.range (n + 1),
        C (inversePowerCompositionRowCoeff e n k) * X ^ k := by
  rw [compositionRow]
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  by_cases hk0 : k = 0
  · subst k
    simp [inversePowerCompositionRowCoeff]
  · rw [inversePowerCompositionRowCoeff, if_neg hk0,
      coeff_inversePowerCompositionKernel_pow he
        (Nat.one_le_iff_ne_zero.mpr hk0)
        (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]

/-- A positive-index inverse-power composition row has zero constant
coefficient. -/
theorem coeff_zero_compositionRow_inversePowerCompositionKernel
    (e : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (compositionRow
        (PowerSeries.mk (inversePowerCompositionKernel e)) n).coeff 0 = 0 := by
  rw [coeff_compositionRow (by simp [inversePowerCompositionKernel])]
  simp [hn]

/-- The linear coefficient of a positive-index inverse-power composition
row is the displayed positive binomial coefficient. -/
theorem coeff_one_compositionRow_inversePowerCompositionKernel
    {e n : ℕ} (he : 1 ≤ e) (hn : 1 ≤ n) :
    (compositionRow
        (PowerSeries.mk (inversePowerCompositionKernel e)) n).coeff 1 =
      (Nat.choose (e - 1 + (n - 1)) (e - 1) : ℝ) := by
  rw [coeff_compositionRow (by simp [inversePowerCompositionKernel])]
  simpa using coeff_inversePowerCompositionKernel_pow
    he (show 1 ≤ 1 by rfl) hn

/-- Every positive-index inverse-power composition row has a simple zero,
expressed by exact consecutive divisibility certificates. -/
theorem inversePowerCompositionRow_exact_X
    {e n : ℕ} (he : 1 ≤ e) (hn : 1 ≤ n) :
    X ∣ compositionRow
        (PowerSeries.mk (inversePowerCompositionKernel e)) n ∧
      ¬X ^ 2 ∣ compositionRow
        (PowerSeries.mk (inversePowerCompositionKernel e)) n := by
  have hcoeffOne :
      (compositionRow
          (PowerSeries.mk (inversePowerCompositionKernel e)) n).coeff 1 ≠ 0 := by
    rw [coeff_one_compositionRow_inversePowerCompositionKernel he hn]
    have hchoose :
        Nat.choose (e - 1 + (n - 1)) (e - 1) ≠ 0 :=
      Nat.choose_ne_zero_iff.mpr (Nat.le_add_right (e - 1) (n - 1))
    exact_mod_cast hchoose
  constructor
  · rw [Polynomial.X_dvd_iff]
    exact coeff_zero_compositionRow_inversePowerCompositionKernel e
      (Nat.ne_zero_of_lt hn)
  · intro hdvd
    exact hcoeffOne
      ((Polynomial.X_pow_dvd_iff.mp hdvd) 1 (by norm_num))

/-- Inverse-power composition rows are PF and consecutive rows are in
zero-aware proper position. -/
theorem inversePowerCompositionRows_pf_and_prec0 (e : ℕ) :
    (∀ n, IsPFPolynomial
      (compositionRow
        (PowerSeries.mk (inversePowerCompositionKernel e)) n)) ∧
      ∀ n, Interl
        (compositionRow
          (PowerSeries.mk (inversePowerCompositionKernel e)) n)
        (compositionRow
          (PowerSeries.mk (inversePowerCompositionKernel e)) (n + 1)) := by
  simpa [inversePowerCompositionKernel] using
    (shiftedFiniteSupersymmetricCompositionRows_pf_and_prec0
      (xs := []) (ys := List.replicate e 1) (by simp) (by simp))

/-- Every nonzero root of an inverse-power composition row is strictly
negative. -/
theorem inversePowerCompositionRow_nonzero_roots_neg
    (e n : ℕ) {r : ℝ}
    (hr : r ∈ (compositionRow
      (PowerSeries.mk (inversePowerCompositionKernel e)) n).roots)
    (hr0 : r ≠ 0) : r < 0 := by
  exact lt_of_le_of_ne
    ((inversePowerCompositionRows_pf_and_prec0 e).1 n |>.roots_nonpos r hr)
    hr0

/-! ## The mixed quadratic/geometric family -/

/-- The OEIS A207327 kernel `z (1 + z)^2 / (1 - z)`. -/
def a207327Kernel : ℕ → ℝ :=
  shiftedFiniteSupersymmetricCoeff [1, 1] [1]

/-- The formal kernel identity, with its denominator retained. -/
theorem mk_a207327Kernel_mul_one_sub :
    PowerSeries.mk a207327Kernel * (1 - PowerSeries.X) =
      PowerSeries.X * (1 + PowerSeries.X) ^ 2 := by
  rw [a207327Kernel, mk_shiftedFiniteSupersymmetricCoeff]
  calc
    (PowerSeries.X * finiteSupersymmetricSeries [1, 1] [1]) *
          (1 - PowerSeries.X) =
        PowerSeries.X *
          (finiteSupersymmetricSeries [1, 1] [1] *
            (1 - PowerSeries.X)) := by ring
    _ = PowerSeries.X * (1 + PowerSeries.X) ^ 2 := by
      have hs := finiteSupersymmetricSeries_mul_denominators
        ([1, 1] : List ℝ) ([1] : List ℝ)
      have hs' :
          finiteSupersymmetricSeries [1, 1] [1] *
              (1 - PowerSeries.X) =
            (1 + PowerSeries.X) ^ 2 := by
        simpa [pow_two, supersymmetricNumeratorFactor] using hs
      rw [hs']

/-- The A207327 row polynomial. -/
def a207327Row (n : ℕ) : ℝ[X] :=
  compositionRow (PowerSeries.mk a207327Kernel) n

/-- A207327 rows are PF and consecutive rows are in zero-aware proper
position. -/
theorem a207327Rows_pf_and_prec0 :
    (∀ n, IsPFPolynomial (a207327Row n)) ∧
      ∀ n, Interl (a207327Row n) (a207327Row (n + 1)) := by
  simpa [a207327Row, a207327Kernel] using
    (shiftedFiniteSupersymmetricCompositionRows_pf_and_prec0
      (xs := [1, 1]) (ys := [1]) (by simp) (by simp))

/-- Every nonzero root of an A207327 row is strictly negative. -/
theorem a207327Row_nonzero_roots_neg
    (n : ℕ) {r : ℝ} (hr : r ∈ (a207327Row n).roots)
    (hr0 : r ≠ 0) : r < 0 := by
  exact lt_of_le_of_ne
    ((a207327Rows_pf_and_prec0.1 n).roots_nonpos r hr) hr0

/-- The polynomial-valued denominator
`(1-z) - X*z*(1+z)^2` for the A207327 row series. -/
def a207327DenominatorSeries : PowerSeries ℝ[X] :=
  polynomialLift (1 - PowerSeries.X) -
    PowerSeries.C X *
      polynomialLift (PowerSeries.X * (1 + PowerSeries.X) ^ 2)

@[simp]
theorem constantCoeff_a207327DenominatorSeries :
    PowerSeries.constantCoeff a207327DenominatorSeries = 1 := by
  have hQ :
      PowerSeries.constantCoeff
        (polynomialLift
          (1 - PowerSeries.X : PowerSeries ℝ)) = 1 := by
    change C (PowerSeries.coeff 0
      (1 - PowerSeries.X : PowerSeries ℝ)) = 1
    simp
  have hA :
      PowerSeries.constantCoeff
        (polynomialLift
          (PowerSeries.X * (1 + PowerSeries.X) ^ 2 : PowerSeries ℝ)) = 0 := by
    change C (PowerSeries.coeff 0
      (PowerSeries.X * (1 + PowerSeries.X) ^ 2 : PowerSeries ℝ)) = 0
    simp
  rw [a207327DenominatorSeries, map_sub, map_mul, hQ, hA]
  simp

/-- Exact four-term support of the A207327 denominator. -/
theorem coeff_a207327DenominatorSeries (n : ℕ) :
    PowerSeries.coeff n a207327DenominatorSeries =
      if n = 0 then 1 else if n = 1 then -(1 + X)
      else if n = 2 then -(2 * X) else if n = 3 then -X else 0 := by
  rw [a207327DenominatorSeries]
  rw [show PowerSeries.coeff n
      (polynomialLift ((1 - PowerSeries.X) : PowerSeries ℝ) -
        PowerSeries.C X *
          polynomialLift
            ((PowerSeries.X * (1 + PowerSeries.X) ^ 2) : PowerSeries ℝ)) =
      PowerSeries.coeff n
          (polynomialLift ((1 - PowerSeries.X) : PowerSeries ℝ)) -
        PowerSeries.coeff n
          (PowerSeries.C X *
            polynomialLift
              ((PowerSeries.X * (1 + PowerSeries.X) ^ 2) :
                PowerSeries ℝ)) by
      exact (PowerSeries.coeff n :
        PowerSeries ℝ[X] →ₗ[ℝ[X]] ℝ[X]).map_sub _ _]
  rw [coeff_polynomialLift, PowerSeries.coeff_C_mul,
    coeff_polynomialLift]
  have hQ :
      (1 - PowerSeries.X : PowerSeries ℝ) =
        ((1 - X : ℝ[X]) : PowerSeries ℝ) := by
    simp
  have hA :
      (PowerSeries.X * (1 + PowerSeries.X) ^ 2 : PowerSeries ℝ) =
        ((X + X ^ 2 + X ^ 2 + X ^ 3 : ℝ[X]) : PowerSeries ℝ) := by
    norm_num
    ring
  rw [hQ, hA, Polynomial.coeff_coe, Polynomial.coeff_coe]
  by_cases hn0 : n = 0
  · subst n
    norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  by_cases hn1 : n = 1
  · subst n
    norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
    ring
  by_cases hn2 : n = 2
  · subst n
    norm_num [Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.C_ofNat]
    ring
  by_cases hn3 : n = 3
  · subst n
    norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  simp [hn0, hn1, hn2, hn3, Polynomial.coeff_X_pow,
    Polynomial.coeff_one, Polynomial.coeff_X, Ne.symm hn1]

/-- The A207327 row generating series has numerator exactly `1-z`. -/
theorem a207327Denominator_mul_rowGeneratingSeries :
    a207327DenominatorSeries *
        compositionRowGeneratingSeries (PowerSeries.mk a207327Kernel) =
      polynomialLift (1 - PowerSeries.X) := by
  have hzero :
      PowerSeries.constantCoeff (PowerSeries.mk a207327Kernel) = 0 := by
    simp [a207327Kernel]
  have hgeom := one_sub_mul_compositionRowGeneratingSeries
    (h := PowerSeries.mk a207327Kernel) hzero
  have hlift :
      polynomialLift (PowerSeries.X * (1 + PowerSeries.X) ^ 2) =
        polynomialLift (PowerSeries.mk a207327Kernel) *
          polynomialLift (1 - PowerSeries.X) := by
    rw [← polynomialLift_mul, mk_a207327Kernel_mul_one_sub]
  have hfactor :
      a207327DenominatorSeries =
        polynomialLift (1 - PowerSeries.X) *
          (1 - PowerSeries.C X *
            polynomialLift (PowerSeries.mk a207327Kernel)) := by
    rw [a207327DenominatorSeries, hlift]
    ring
  rw [hfactor, mul_assoc, hgeom, mul_one]

/-- Finite coefficient form of the exact A207327 rational identity. -/
theorem a207327Row_finite_denominator (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
        PowerSeries.coeff j a207327DenominatorSeries *
          a207327Row (n - j) =
      C (PowerSeries.coeff n (1 - PowerSeries.X : PowerSeries ℝ)) := by
  have h := congrArg (PowerSeries.coeff n)
    a207327Denominator_mul_rowGeneratingSeries
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa [a207327Row] using h

/-- The exact causal recurrence, retaining the numerator coefficient at
indices zero and one. -/
theorem a207327Row_eq_sub_sum (n : ℕ) :
    a207327Row n =
      C (PowerSeries.coeff n (1 - PowerSeries.X : PowerSeries ℝ)) -
        ∑ j ∈ Finset.range n,
          PowerSeries.coeff (j + 1) a207327DenominatorSeries *
            a207327Row (n - (j + 1)) := by
  apply eq_sub_sum_of_finite_denominator_numerator
    (D := fun j => PowerSeries.coeff j a207327DenominatorSeries)
    (E := fun j =>
      C (PowerSeries.coeff j (1 - PowerSeries.X : PowerSeries ℝ)))
  · rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact constantCoeff_a207327DenominatorSeries
  · exact a207327Row_finite_denominator

/-- The numerator/denominator recurrence determines the A207327 rows
uniquely. -/
theorem eq_a207327Row_of_finite_denominator
    (P : ℕ → ℝ[X])
    (hP : ∀ n,
      ∑ j ∈ Finset.range (n + 1),
          PowerSeries.coeff j a207327DenominatorSeries * P (n - j) =
        C (PowerSeries.coeff n
          (1 - PowerSeries.X : PowerSeries ℝ))) :
    P = a207327Row := by
  apply eq_of_finite_denominator_numerator
    (D := fun j => PowerSeries.coeff j a207327DenominatorSeries)
    (E := fun j =>
      C (PowerSeries.coeff j (1 - PowerSeries.X : PowerSeries ℝ)))
  · rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact constantCoeff_a207327DenominatorSeries
  · exact hP
  · exact a207327Row_finite_denominator

/-- The homogeneous order-three recurrence after the two numerator indices
have passed. -/
theorem a207327Row_recurrence (n : ℕ) :
    a207327Row (n + 3) =
      (1 + X) * a207327Row (n + 2) +
        (2 * X) * a207327Row (n + 1) + X * a207327Row n := by
  have h := a207327Row_finite_denominator (n + 3)
  have hsubset :
      Finset.range 4 ⊆ Finset.range (n + 3 + 1) := by
    exact Finset.range_mono (by lia)
  have hsum :
      (∑ j ∈ Finset.range 4,
          PowerSeries.coeff j a207327DenominatorSeries *
            a207327Row (n + 3 - j)) =
        ∑ j ∈ Finset.range (n + 3 + 1),
          PowerSeries.coeff j a207327DenominatorSeries *
            a207327Row (n + 3 - j) := by
    apply Finset.sum_subset hsubset
    intro j hj hnot
    have hj4 : 4 ≤ j := by
      simpa using hnot
    rw [coeff_a207327DenominatorSeries]
    simp [show j ≠ 0 by lia, show j ≠ 1 by lia,
      show j ≠ 2 by lia, show j ≠ 3 by lia]
  rw [← hsum] at h
  simp [Finset.sum_range_succ, coeff_a207327DenominatorSeries,
    PowerSeries.coeff_X] at h
  linear_combination h

@[simp]
theorem a207327Row_zero : a207327Row 0 = 1 := by
  simp [a207327Row]

@[simp]
theorem a207327Row_one : a207327Row 1 = X := by
  have h := a207327Row_finite_denominator 1
  norm_num [Finset.sum_range_succ, coeff_a207327DenominatorSeries,
    a207327Row_zero] at h
  linear_combination h

@[simp]
theorem a207327Row_two : a207327Row 2 = 3 * X + X ^ 2 := by
  have h := a207327Row_finite_denominator 2
  norm_num [Finset.sum_range_succ, coeff_a207327DenominatorSeries,
    a207327Row_zero, a207327Row_one] at h
  simp [PowerSeries.coeff_X] at h
  linear_combination h

@[simp]
theorem a207327Row_three :
    a207327Row 3 = 4 * X + 6 * X ^ 2 + X ^ 3 := by
  have h := a207327Row_recurrence 0
  norm_num [a207327Row_zero, a207327Row_one,
    a207327Row_two] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The three checked initial rows and the homogeneous recurrence uniquely
identify the A207327 family. -/
theorem eq_a207327Row_of_initial_and_recurrence
    (P : ℕ → ℝ[X])
    (hzero : P 0 = 1) (hone : P 1 = X)
    (htwo : P 2 = 3 * X + X ^ 2)
    (hrec : ∀ n,
      P (n + 3) = (1 + X) * P (n + 2) +
        (2 * X) * P (n + 1) + X * P n) :
    P = a207327Row := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      cases n with
      | zero => simpa using hzero
      | succ n =>
          cases n with
          | zero => simpa using hone
          | succ n =>
              cases n with
              | zero => simpa using htwo
              | succ n =>
                  rw [show n + 1 + 1 + 1 = n + 3 by lia,
                    hrec, a207327Row_recurrence,
                    ih (n + 2) (by lia), ih (n + 1) (by lia),
                    ih n (by lia)]

/-! ## Thin OEIS aliases for the polynomial and inverse-power families -/

/-- A116088 is the quadratic binomial composition family. -/
def a116088Row (n : ℕ) : ℝ[X] :=
  compositionRow (PowerSeries.mk (binomialCompositionKernel 2)) n

/-- The exact A116088 binomial row formula. -/
theorem a116088Row_eq_sum_choose (n : ℕ) :
    a116088Row n =
      ∑ k ∈ Finset.range (n + 1),
        C (Nat.choose (2 * k) (n - k) : ℝ) * X ^ k := by
  exact compositionRow_binomialCompositionKernel 2 n

/-- A116088 rows are PF and consecutively in zero-aware proper position. -/
theorem a116088Rows_pf_and_prec0 :
    (∀ n, IsPFPolynomial (a116088Row n)) ∧
      ∀ n, Interl (a116088Row n) (a116088Row (n + 1)) := by
  exact binomialCompositionRows_pf_and_prec0 2

/-- The zero root of a positive A116088 row has multiplicity
`ceil(n/3)`. -/
theorem a116088Row_exact_X_power (n : ℕ) :
    let m := n ⌈/⌉ 3
    X ^ m ∣ a116088Row n ∧ ¬X ^ (m + 1) ∣ a116088Row n := by
  simpa [a116088Row] using
    (binomialCompositionRow_exact_X_power 2 n)

/-- Every nonzero root of an A116088 row is strictly negative. -/
theorem a116088Row_nonzero_roots_neg
    (n : ℕ) {r : ℝ} (hr : r ∈ (a116088Row n).roots)
    (hr0 : r ≠ 0) : r < 0 := by
  exact binomialCompositionRow_nonzero_roots_neg 2 n hr hr0

/-- A116089 is the cubic binomial composition family. -/
def a116089Row (n : ℕ) : ℝ[X] :=
  compositionRow (PowerSeries.mk (binomialCompositionKernel 3)) n

/-- The exact A116089 binomial row formula. -/
theorem a116089Row_eq_sum_choose (n : ℕ) :
    a116089Row n =
      ∑ k ∈ Finset.range (n + 1),
        C (Nat.choose (3 * k) (n - k) : ℝ) * X ^ k := by
  exact compositionRow_binomialCompositionKernel 3 n

/-- A116089 rows are PF and consecutively in zero-aware proper position. -/
theorem a116089Rows_pf_and_prec0 :
    (∀ n, IsPFPolynomial (a116089Row n)) ∧
      ∀ n, Interl (a116089Row n) (a116089Row (n + 1)) := by
  exact binomialCompositionRows_pf_and_prec0 3

/-- The zero root of a positive A116089 row has multiplicity
`ceil(n/4)`. -/
theorem a116089Row_exact_X_power (n : ℕ) :
    let m := n ⌈/⌉ 4
    X ^ m ∣ a116089Row n ∧ ¬X ^ (m + 1) ∣ a116089Row n := by
  simpa [a116089Row] using
    (binomialCompositionRow_exact_X_power 3 n)

/-- Every nonzero root of an A116089 row is strictly negative. -/
theorem a116089Row_nonzero_roots_neg
    (n : ℕ) {r : ℝ} (hr : r ∈ (a116089Row n).roots)
    (hr0 : r ≠ 0) : r < 0 := by
  exact binomialCompositionRow_nonzero_roots_neg 3 n hr hr0

/-- A206294 is the cubic inverse-power composition family. -/
def a206294Row (n : ℕ) : ℝ[X] :=
  compositionRow (PowerSeries.mk (inversePowerCompositionKernel 3)) n

/-- The exact guarded negative-binomial A206294 row formula. -/
theorem a206294Row_eq_sum_choose (n : ℕ) :
    a206294Row n =
      ∑ k ∈ Finset.range (n + 1),
        C (inversePowerCompositionRowCoeff 3 n k) * X ^ k := by
  exact compositionRow_inversePowerCompositionKernel (by norm_num) n

/-- A206294 rows are PF and consecutively in zero-aware proper position. -/
theorem a206294Rows_pf_and_prec0 :
    (∀ n, IsPFPolynomial (a206294Row n)) ∧
      ∀ n, Interl (a206294Row n) (a206294Row (n + 1)) := by
  exact inversePowerCompositionRows_pf_and_prec0 3

/-- Every positive-index A206294 row has a simple zero. -/
theorem a206294Row_exact_X {n : ℕ} (hn : 1 ≤ n) :
    X ∣ a206294Row n ∧ ¬X ^ 2 ∣ a206294Row n := by
  exact inversePowerCompositionRow_exact_X (by norm_num) hn

/-- Every nonzero root of an A206294 row is strictly negative. -/
theorem a206294Row_nonzero_roots_neg
    (n : ℕ) {r : ℝ} (hr : r ∈ (a206294Row n).roots)
    (hr0 : r ≠ 0) : r < 0 := by
  exact inversePowerCompositionRow_nonzero_roots_neg 3 n hr hr0

end

end RealRooted.BrandenLeite
