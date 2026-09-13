import RealRooted.AissenSchoenbergWhitneyBase
import RealRooted.BrandenLeite.KernelRow
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Finite Toeplitz algebra for two-kernel rows

This file identifies finite Toeplitz matrix products with truncated formal
power-series products.  It then packages the literal coefficient rows of
`g(z) / (1 - X g(z) h(z))` and relates them to finite kernel rows.
-/

open Matrix Polynomial BigOperators

namespace RealRooted.BrandenLeite

noncomputable section

/-- The leading finite square block of the Toeplitz matrix of a sequence. -/
def finiteToeplitz {R : Type*} [Zero R]
    (a : ℕ → R) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  (toeplitz a).submatrix Fin.val Fin.val

@[simp]
theorem finiteToeplitz_apply {R : Type*} [Zero R]
    (a : ℕ → R) (N : ℕ) (i j : Fin (N + 1)) :
    finiteToeplitz a N i j = if j ≤ i then a (i.val - j.val) else 0 := by
  simp [finiteToeplitz, toeplitz_apply]

/-- Finite Toeplitz truncation commutes exactly with Cauchy multiplication. -/
theorem finiteToeplitz_mul {R : Type*} [CommSemiring R]
    (a b : ℕ → R) (N : ℕ) :
    finiteToeplitz a N * finiteToeplitz b N =
      finiteToeplitz
        (fun n => PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b)) N := by
  ext i j
  by_cases hji : j ≤ i
  · rw [Matrix.mul_apply, finiteToeplitz_apply, if_pos hji]
    simp only [finiteToeplitz_apply]
    simp only [Fin.le_iff_val_le_val]
    change (∑ k : Fin (N + 1),
      (fun m : ℕ =>
        (if m ≤ i.val then a (i.val - m) else 0) *
          if j.val ≤ m then b (m - j.val) else 0) k.val) = _
    calc
      (∑ k : Fin (N + 1),
          (fun m : ℕ =>
            (if m ≤ i.val then a (i.val - m) else 0) *
              if j.val ≤ m then b (m - j.val) else 0) k.val) =
          ∑ k ∈ Finset.range (N + 1),
            (if k ≤ i.val then a (i.val - k) else 0) *
              if j.val ≤ k then b (k - j.val) else 0 :=
        Fin.sum_univ_eq_sum_range
          (fun m : ℕ =>
            (if m ≤ i.val then a (i.val - m) else 0) *
              if j.val ≤ m then b (m - j.val) else 0)
          (N + 1)
      (∑ k ∈ Finset.range (N + 1),
          (if k ≤ i.val then a (i.val - k) else 0) *
            if j.val ≤ k then b (k - j.val) else 0) =
          ∑ k ∈ Finset.Ico j.val (i.val + 1),
            (if k ≤ i.val then a (i.val - k) else 0) *
              if j.val ≤ k then b (k - j.val) else 0 := by
        symm
        apply Finset.sum_subset
        · intro k hk
          simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
          exact hk.2.trans_le i.isLt
        · intro k hkRange hkIco
          simp only [Finset.mem_Ico, not_and_or, not_lt, not_le] at hkIco
          rcases hkIco with hkj | hik
          · simp [hkj]
          · simp [show ¬k ≤ i.val by lia]
      _ =
          ∑ k ∈ Finset.Ico j.val (i.val + 1),
            a (i.val - k) * b (k - j.val) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_Ico] at hk
        simp [hk.1, show k ≤ i.val by lia]
      _ = ∑ k ∈ Finset.range (i.val + 1 - j.val),
            a (i.val - (j.val + k)) * b k := by
        rw [Finset.sum_Ico_eq_sum_range]
        apply Finset.sum_congr rfl
        intro k hk
        have hklt : k < i.val + 1 - j.val := Finset.mem_range.mp hk
        congr 2
        lia
      _ = ∑ k ∈ Finset.range (i.val - j.val + 1),
            a (i.val - j.val - k) * b k := by
        have hsize : i.val + 1 - j.val = i.val - j.val + 1 := by lia
        rw [hsize]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.sub_sub]
      _ = PowerSeries.coeff (i.val - j.val)
          (PowerSeries.mk a * PowerSeries.mk b) := by
        rw [mul_comm (PowerSeries.mk a) (PowerSeries.mk b)]
        rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp [mul_comm]
  · rw [finiteToeplitz_apply, if_neg hji, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k ≤ i
    · have hjk : ¬j ≤ k := fun hjk => hji (hjk.trans hki)
      simp [finiteToeplitz_apply, hki, hjk]
    · simp [finiteToeplitz_apply, hki]

@[simp]
theorem mk_coeff_eq {R : Type*} [Semiring R] (f : PowerSeries R) :
    PowerSeries.mk (fun n => PowerSeries.coeff n f) = f := by
  ext n
  simp

/-- Powers of a finite Toeplitz truncation are the corresponding truncations
of formal power-series powers. -/
theorem finiteToeplitz_pow {R : Type*} [CommSemiring R]
    (a : ℕ → R) (N q : ℕ) :
    finiteToeplitz a N ^ q =
      finiteToeplitz
        (fun n => PowerSeries.coeff n (PowerSeries.mk a ^ q)) N := by
  induction q with
  | zero =>
      ext i j
      by_cases hij : i = j
      · subst j
        simp [finiteToeplitz_apply]
      · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
        by_cases hji : j ≤ i
        · have hsub : i.val - j.val ≠ 0 := by lia
          simp [finiteToeplitz_apply, hji, hij, hsub]
        · simp [finiteToeplitz_apply, hji, hij]
  | succ q ih =>
      rw [pow_succ, ih, finiteToeplitz_mul]
      congr 1
      funext n
      simp [pow_succ]

/-- Exact matrix expression behind the two-kernel coefficient formula. -/
theorem finiteToeplitz_kernelProduct {R : Type*} [CommSemiring R]
    (g h : PowerSeries R) (N q : ℕ) :
    finiteToeplitz (fun n => PowerSeries.coeff n g) N *
        (finiteToeplitz (fun n => PowerSeries.coeff n h) N *
          finiteToeplitz (fun n => PowerSeries.coeff n g) N) ^ q =
      finiteToeplitz
        (fun n => PowerSeries.coeff n (g ^ (q + 1) * h ^ q)) N := by
  rw [finiteToeplitz_mul, finiteToeplitz_pow, finiteToeplitz_mul]
  congr 1
  funext n
  simp only [mk_coeff_eq]
  congr 1
  rw [pow_succ, mul_pow]
  ac_rfl

/-- The column-zero entry of the finite kernel product is the literal formal
power-series coefficient. -/
theorem finiteToeplitz_kernelProduct_apply_zero
    {R : Type*} [CommSemiring R]
    (g h : PowerSeries R) {N : ℕ} (q : ℕ) (i : Fin (N + 1)) :
    (finiteToeplitz (fun n => PowerSeries.coeff n g) N *
        (finiteToeplitz (fun n => PowerSeries.coeff n h) N *
          finiteToeplitz (fun n => PowerSeries.coeff n g) N) ^ q) i 0 =
      PowerSeries.coeff i.val (g ^ (q + 1) * h ^ q) := by
  rw [finiteToeplitz_kernelProduct, finiteToeplitz_apply, if_pos (Fin.zero_le i)]
  simp

/-- The literal `n`th coefficient row of the two-kernel geometric series. -/
def twoKernelRow {R : Type*} [CommSemiring R]
    (g h : PowerSeries R) (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (PowerSeries.coeff n (g ^ (k + 1) * h ^ k)) * X ^ k

/-- A two-kernel term has no coefficient below the exponent of a
zero-constant second kernel. -/
theorem coeff_twoKernelTerm_eq_zero_of_lt
    {R : Type*} [CommSemiring R] {g h : PowerSeries R}
    (hzero : PowerSeries.constantCoeff h = 0)
    {n k : ℕ} (hnk : n < k) :
    PowerSeries.coeff n (g ^ (k + 1) * h ^ k) = 0 := by
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.mpr hzero
  rw [hu, mul_pow]
  have hreorder :
      g ^ (k + 1) * (PowerSeries.X ^ k * u ^ k) =
        PowerSeries.X ^ k * (g ^ (k + 1) * u ^ k) := by
    ac_rfl
  rw [hreorder, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le_of_lt hnk]

/-- The finite row definition has the literal coefficient at every polynomial
index; beyond the displayed range the power-series coefficient vanishes. -/
theorem coeff_twoKernelRow {R : Type*} [CommSemiring R]
    {g h : PowerSeries R} (hzero : PowerSeries.constantCoeff h = 0)
    (n k : ℕ) :
    (twoKernelRow g h n).coeff k =
      PowerSeries.coeff n (g ^ (k + 1) * h ^ k) := by
  rw [twoKernelRow, Polynomial.finsetSum_coeff]
  by_cases hk : k ∈ Finset.range (n + 1)
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j hj hjk
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hjk]
    · exact fun hnot => (hnot hk).elim
  · have hnk : n < k := by simpa using hk
    rw [coeff_twoKernelTerm_eq_zero_of_lt hzero hnk]
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : j ≠ k := by
      intro heq
      subst j
      exact hk hj
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hjk]

/-- Every literal two-kernel row has degree at most its series index. -/
theorem natDegree_twoKernelRow_le {R : Type*} [CommSemiring R]
    (g h : PowerSeries R) (n : ℕ) :
    (twoKernelRow g h n).natDegree ≤ n := by
  unfold twoKernelRow
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_X_pow_le _ k).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

/-- A literal two-kernel row is the last row of the corresponding finite
Toeplitz kernel construction. -/
theorem twoKernelRow_eq_kernelRow {R : Type*} [CommSemiring R]
    {g h : PowerSeries R} (hzero : PowerSeries.constantCoeff h = 0)
    (n : ℕ) :
    twoKernelRow g h n =
      kernelRow
        (finiteToeplitz (fun m => PowerSeries.coeff m g) n)
        (finiteToeplitz (fun m => PowerSeries.coeff m h) n)
        (Fin.last n) := by
  ext k
  rw [coeff_twoKernelRow hzero, coeff_kernelRow]
  by_cases hk : k < n + 1
  · rw [if_pos hk]
    symm
    exact finiteToeplitz_kernelProduct_apply_zero g h k (Fin.last n)
  · rw [if_neg hk]
    exact coeff_twoKernelTerm_eq_zero_of_lt hzero (by lia)

/-- For each polynomial column, the generating series of literal row
coefficients is exactly the corresponding geometric-series term.  This is a
coefficientwise, locally finite formulation: column `k` starts in series
degree `k`. -/
theorem mk_coeff_twoKernelRow
    {R : Type*} [CommSemiring R] {g h : PowerSeries R}
    (hzero : PowerSeries.constantCoeff h = 0) (k : ℕ) :
    PowerSeries.mk (fun n => (twoKernelRow g h n).coeff k) =
      g ^ (k + 1) * h ^ k := by
  ext n
  simp [coeff_twoKernelRow hzero]

/-- Coefficientwise lifting of a scalar power series to one whose
coefficients are constant polynomials. -/
def polynomialLift {R : Type*} [Semiring R]
    (f : PowerSeries R) : PowerSeries R[X] :=
  PowerSeries.mk fun n => C (PowerSeries.coeff n f)

@[simp]
theorem coeff_polynomialLift {R : Type*} [Semiring R]
    (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (polynomialLift f) = C (PowerSeries.coeff n f) := by
  simp [polynomialLift]

/-- The formal generating series whose `n`th coefficient is the literal
two-kernel row. -/
def twoKernelGeneratingSeries {R : Type*} [CommSemiring R]
    (g h : PowerSeries R) : PowerSeries R[X] :=
  PowerSeries.mk (twoKernelRow g h)

@[simp]
theorem coeff_twoKernelGeneratingSeries
    {R : Type*} [CommSemiring R]
    (g h : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (twoKernelGeneratingSeries g h) =
      twoKernelRow g h n := by
  simp [twoKernelGeneratingSeries]

/-- Multiplication by a coefficientwise constant lift acts independently on
each polynomial column of the locally finite two-kernel series. -/
theorem coeff_polynomialLift_mul_twoKernelGeneratingSeries
    {R : Type*} [CommSemiring R]
    (a : PowerSeries R) {g h : PowerSeries R}
    (hzero : PowerSeries.constantCoeff h = 0) (n k : ℕ) :
    (PowerSeries.coeff n
        (polynomialLift a * twoKernelGeneratingSeries g h)).coeff k =
      PowerSeries.coeff n (a * (g ^ (k + 1) * h ^ k)) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro ij hij
  simp [coeff_twoKernelRow hzero, Polynomial.coeff_C_mul]

/-- Multiplying the locally finite two-kernel series by its geometric
denominator recovers the lifted numerator. -/
theorem one_sub_mul_twoKernelGeneratingSeries
    {R : Type*} [CommRing R] {g h : PowerSeries R}
    (hzero : PowerSeries.constantCoeff h = 0) :
    (1 - PowerSeries.C X * polynomialLift (g * h)) *
        twoKernelGeneratingSeries g h = polynomialLift g := by
  rw [sub_mul, one_mul, mul_assoc]
  apply PowerSeries.ext
  intro n
  apply Polynomial.ext
  intro k
  rw [show PowerSeries.coeff n
        (twoKernelGeneratingSeries g h -
          PowerSeries.C X *
            (polynomialLift (g * h) * twoKernelGeneratingSeries g h)) =
      PowerSeries.coeff n (twoKernelGeneratingSeries g h) -
        PowerSeries.coeff n
          (PowerSeries.C X *
            (polynomialLift (g * h) * twoKernelGeneratingSeries g h)) by
      exact
        (PowerSeries.coeff n : PowerSeries R[X] →ₗ[R[X]] R[X]).map_sub _ _]
  rw [PowerSeries.coeff_C_mul, coeff_twoKernelGeneratingSeries,
    coeff_polynomialLift, Polynomial.coeff_sub]
  cases k with
  | zero =>
      simp [coeff_twoKernelRow hzero]
  | succ k =>
      rw [coeff_twoKernelRow hzero,
        Polynomial.coeff_X_mul,
        coeff_polynomialLift_mul_twoKernelGeneratingSeries
          (g * h) hzero n k]
      have hseries :
          g ^ (k + 1 + 1) * h ^ (k + 1) =
            (g * h) * (g ^ (k + 1) * h ^ k) := by
        rw [pow_succ g (k + 1), pow_succ h k, pow_succ g k]
        ac_rfl
      rw [hseries, sub_self]
      simp

/-- Literal formal quotient identity for the two-kernel rows.  The coefficient
of series degree `n` on the left is the finite polynomial
`twoKernelRow g h n`; hence no analytic or infinite polynomial sum is used. -/
theorem twoKernelGeneratingSeries_eq_div
    {R : Type*} [CommRing R] {g h : PowerSeries R}
    (hzero : PowerSeries.constantCoeff h = 0) :
    twoKernelGeneratingSeries g h =
      polynomialLift g *
        (1 - PowerSeries.C X * polynomialLift (g * h)).invOfUnit 1 := by
  let D : PowerSeries R[X] :=
    1 - PowerSeries.C X * polynomialLift (g * h)
  have hDzero : PowerSeries.constantCoeff D = 1 := by
    have hlift : PowerSeries.constantCoeff (polynomialLift (g * h)) = 0 := by
      change C (PowerSeries.coeff 0 (g * h)) = 0
      simp [PowerSeries.coeff_zero_eq_constantCoeff, hzero]
    simp [D, hlift]
  have hmul : D * twoKernelGeneratingSeries g h = polynomialLift g := by
    exact one_sub_mul_twoKernelGeneratingSeries hzero
  calc
    twoKernelGeneratingSeries g h =
        1 * twoKernelGeneratingSeries g h := by rw [one_mul]
    _ = (D.invOfUnit 1 * D) * twoKernelGeneratingSeries g h := by
      rw [PowerSeries.invOfUnit_mul D 1 hDzero]
    _ = D.invOfUnit 1 * (D * twoKernelGeneratingSeries g h) := by
      rw [mul_assoc]
    _ = D.invOfUnit 1 * polynomialLift g := by rw [hmul]
    _ = polynomialLift g * D.invOfUnit 1 := mul_comm _ _

end

end RealRooted.BrandenLeite
