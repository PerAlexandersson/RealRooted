import RealRooted.PFPolynomial

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Finite multiplier sequences

This file records the finite-degree multiplier-sequence interface needed for
the PF side of the Hadamard/Schur--Szego machinery.  It deliberately stays
independent of `RealRooted.Hadamard`, so work here can proceed while the
Garloff--Wagner theorem file is being edited elsewhere.

The main classical input is the finite Polya--Schur theorem: for nonnegative
diagonal coefficients, preservation of real-rootedness up to degree `n` is
equivalent to the corresponding Jensen polynomial being PF.
-/

/-- Diagonal operator attached to a sequence `gamma`: it sends
`sum a_n X^n` to `sum gamma_n a_n X^n`. -/
def diagonalOperator (gamma : ℕ → ℝ) (p : ℝ[X]) : ℝ[X] :=
  p.sum fun n a => monomial n (gamma n * a)

@[simp] theorem coeff_diagonalOperator
    (gamma : ℕ → ℝ) (p : ℝ[X]) (n : ℕ) :
    (diagonalOperator gamma p).coeff n = gamma n * p.coeff n := by
  classical
  rw [diagonalOperator, Polynomial.coeff_sum]
  simp only [Polynomial.coeff_monomial]
  rw [Polynomial.sum_def]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _ hbn
    simp [hbn]
  · intro hn
    rw [(Polynomial.notMem_support_iff).mp hn]
    simp

@[simp] theorem diagonalOperator_zero (gamma : ℕ → ℝ) :
    diagonalOperator gamma 0 = 0 := by
  ext n
  simp

@[simp] theorem diagonalOperator_zero_sequence (p : ℝ[X]) :
    diagonalOperator (fun _ => (0 : ℝ)) p = 0 := by
  ext n
  simp

@[simp] theorem diagonalOperator_one_sequence (p : ℝ[X]) :
    diagonalOperator (fun _ => (1 : ℝ)) p = p := by
  ext n
  simp

theorem diagonalOperator_add (gamma : ℕ → ℝ) (p q : ℝ[X]) :
    diagonalOperator gamma (p + q) =
      diagonalOperator gamma p + diagonalOperator gamma q := by
  ext n
  simp [mul_add]

theorem diagonalOperator_sub (gamma : ℕ → ℝ) (p q : ℝ[X]) :
    diagonalOperator gamma (p - q) =
      diagonalOperator gamma p - diagonalOperator gamma q := by
  ext n
  simp [mul_sub]

theorem diagonalOperator_neg (gamma : ℕ → ℝ) (p : ℝ[X]) :
    diagonalOperator gamma (-p) = -diagonalOperator gamma p := by
  ext n
  simp

theorem diagonalOperator_C_mul (gamma : ℕ → ℝ) (a : ℝ) (p : ℝ[X]) :
    diagonalOperator gamma (C a * p) =
      C a * diagonalOperator gamma p := by
  ext n
  simp [mul_comm, mul_left_comm]

@[simp] theorem diagonalOperator_C (gamma : ℕ → ℝ) (a : ℝ) :
    diagonalOperator gamma (C a) = C (gamma 0 * a) := by
  ext n
  cases n <;> simp

theorem diagonalOperator_monomial (gamma : ℕ → ℝ) (n : ℕ) (a : ℝ) :
    diagonalOperator gamma (monomial n a) = monomial n (gamma n * a) := by
  ext k
  by_cases hk : k = n
  · subst k
    simp
  · simp [Polynomial.coeff_monomial, Ne.symm hk]

theorem support_diagonalOperator_eq_filter (gamma : ℕ → ℝ) (p : ℝ[X]) :
    (diagonalOperator gamma p).support = p.support.filter fun n => gamma n ≠ 0 := by
  ext n
  by_cases hgamma : gamma n = 0
  · simp [Polynomial.mem_support_iff, coeff_diagonalOperator, hgamma]
  · simp [Polynomial.mem_support_iff, coeff_diagonalOperator, hgamma]

theorem support_diagonalOperator_subset (gamma : ℕ → ℝ) (p : ℝ[X]) :
    (diagonalOperator gamma p).support ⊆ p.support := by
  rw [support_diagonalOperator_eq_filter]
  exact Finset.filter_subset _ _

theorem natDegree_diagonalOperator_le (gamma : ℕ → ℝ) (p : ℝ[X]) :
    (diagonalOperator gamma p).natDegree ≤ p.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_diagonalOperator, coeff_eq_zero_of_natDegree_lt hn, mul_zero]

theorem diagonalOperator_comp (gamma delta : ℕ → ℝ) (p : ℝ[X]) :
    diagonalOperator gamma (diagonalOperator delta p) =
      diagonalOperator (fun n => gamma n * delta n) p := by
  ext n
  simp [mul_assoc]

theorem diagonalOperator_comm (gamma delta : ℕ → ℝ) (p : ℝ[X]) :
    diagonalOperator gamma (diagonalOperator delta p) =
      diagonalOperator delta (diagonalOperator gamma p) := by
  ext n
  simp [mul_left_comm]

/-- Nonnegative diagonal coefficients preserve nonnegative coefficients. -/
theorem HasNonnegCoeffs.diagonalOperator
    {gamma : ℕ → ℝ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hgamma : ∀ n, 0 ≤ gamma n) :
    HasNonnegCoeffs (diagonalOperator gamma p) := by
  intro n
  simpa using mul_nonneg (hgamma n) (hp n)

/-- The degree-`n` Jensen polynomial attached to a diagonal sequence. -/
def jensenPolynomial (n : ℕ) (gamma : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k ((Nat.choose n k : ℝ) * gamma k)

@[simp] theorem jensenPolynomial_zero (gamma : ℕ → ℝ) :
    jensenPolynomial 0 gamma = C (gamma 0) := by
  ext k
  cases k <;> simp [jensenPolynomial]

@[simp] theorem coeff_jensenPolynomial (n : ℕ) (gamma : ℕ → ℝ) (k : ℕ) :
    (jensenPolynomial n gamma).coeff k =
      if k ≤ n then (Nat.choose n k : ℝ) * gamma k else 0 := by
  classical
  by_cases hk : k ≤ n
  · have hmem : k ∈ Finset.range (n + 1) := by simpa [Nat.lt_succ_iff] using hk
    rw [jensenPolynomial, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro b hb hbk
      simp [Polynomial.coeff_monomial, hbk]
    · exact fun hnot => (hnot hmem).elim
  · rw [jensenPolynomial, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_zero]
    · simp [hk]
    · intro b hb
      have hb_le : b ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hne : k ≠ b := by
        intro hkb
        subst k
        exact hk hb_le
      have hbk : b ≠ k := Ne.symm hne
      simp [Polynomial.coeff_monomial, hbk]

/-- The Jensen polynomial of `gamma` is the image of `(X + 1) ^ n` under the
diagonal operator attached to `gamma`. -/
theorem jensenPolynomial_eq_diagonalOperator_X_add_one_pow
    (n : ℕ) (gamma : ℕ → ℝ) :
    jensenPolynomial n gamma = diagonalOperator gamma ((X + 1) ^ n) := by
  ext k
  rw [coeff_jensenPolynomial, coeff_diagonalOperator, coeff_X_add_one_pow]
  by_cases hk : k ≤ n
  · simp only [hk, if_true]
    ring
  · have hlt : n < k := Nat.lt_of_not_le hk
    simp [hk, Nat.choose_eq_zero_of_lt hlt]

theorem hasNonnegCoeffs_jensenPolynomial
    {n : ℕ} {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k) :
    HasNonnegCoeffs (jensenPolynomial n gamma) := by
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
  exact (hasNonnegCoeffs_X_add_one.pow n).diagonalOperator hgamma

theorem natDegree_jensenPolynomial_le (n : ℕ) (gamma : ℕ → ℝ) :
    (jensenPolynomial n gamma).natDegree ≤ n := by
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
  exact (natDegree_diagonalOperator_le _ _).trans (natDegree_X_add_one_pow_le n)

theorem support_jensenPolynomial_eq_filter (n : ℕ) (gamma : ℕ → ℝ) :
    (jensenPolynomial n gamma).support =
      (Finset.range (n + 1)).filter fun k => gamma k ≠ 0 := by
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow,
    support_diagonalOperator_eq_filter, support_X_add_one_pow_eq_range]

theorem support_jensenPolynomial_subset (n : ℕ) (gamma : ℕ → ℝ) :
    (jensenPolynomial n gamma).support ⊆ Finset.range (n + 1) := by
  rw [support_jensenPolynomial_eq_filter]
  exact Finset.filter_subset _ _

theorem jensenPolynomial_eq_zero_iff {n : ℕ} {gamma : ℕ → ℝ} :
    jensenPolynomial n gamma = 0 ↔ ∀ k, k ≤ n → gamma k = 0 := by
  rw [← support_eq_empty, support_jensenPolynomial_eq_filter, Finset.filter_eq_empty_iff]
  simp [Finset.mem_range]

@[simp] theorem jensenPolynomial_zero_sequence (n : ℕ) :
    jensenPolynomial n (fun _ => (0 : ℝ)) = 0 := by
  rw [jensenPolynomial_eq_zero_iff]
  simp

/-- Finite multiplier sequence up to degree `n`: the diagonal operator
preserves real-rootedness, allowing the zero polynomial. -/
def IsFiniteMultiplierSequence (n : ℕ) (gamma : ℕ → ℝ) : Prop :=
  ∀ {p : ℝ[X]},
    p.natDegree ≤ n →
    p.Splits →
    diagonalOperator gamma p = 0 ∨ (diagonalOperator gamma p).Splits

/-- Finite PF multiplier sequence up to degree `n`: the diagonal operator
preserves the polynomial PF cone on polynomials of degree at most `n`. -/
def IsFinitePFMultiplierSequence (n : ℕ) (gamma : ℕ → ℝ) : Prop :=
  ∀ {p : ℝ[X]},
    IsPFPolynomial p →
    p.natDegree ≤ n →
    IsPFPolynomial (diagonalOperator gamma p)

theorem IsFiniteMultiplierSequence.mono {m n : ℕ} {gamma : ℕ → ℝ}
    (hmn : m ≤ n) (h : IsFiniteMultiplierSequence n gamma) :
    IsFiniteMultiplierSequence m gamma :=
  fun {_} hp hsplit => h (hp.trans hmn) hsplit

theorem IsFinitePFMultiplierSequence.mono {m n : ℕ} {gamma : ℕ → ℝ}
    (hmn : m ≤ n) (h : IsFinitePFMultiplierSequence n gamma) :
    IsFinitePFMultiplierSequence m gamma :=
  fun {_} hp hdeg => h hp (hdeg.trans hmn)

theorem splits_X_add_one_pow (n : ℕ) :
    ((X + 1 : ℝ[X]) ^ n).Splits :=
  (show (X + 1 : ℝ[X]).Splits by
    simpa [sub_eq_add_neg] using (isRealRooted_X_sub_C (-1)).2).pow n

/-- The easy direction of finite Polya--Schur: a nonnegative finite multiplier
sequence has a PF Jensen polynomial. -/
theorem isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hmult : IsFiniteMultiplierSequence n gamma) :
    IsPFPolynomial (jensenPolynomial n gamma) := by
  have hd := hmult (natDegree_X_add_one_pow_le n) (splits_X_add_one_pow n)
  rw [← jensenPolynomial_eq_diagonalOperator_X_add_one_pow] at hd
  rcases hd with hzero | hsplits
  · simpa [hzero] using IsPFPolynomial.zero
  · exact IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_jensenPolynomial hgamma) hsplits

/-- The finite Polya--Schur theorem in the nonnegative-coefficient convention:
a nonnegative diagonal sequence preserves real-rootedness up to degree `n` if
and only if its degree-`n` Jensen polynomial is PF. -/
def finitePolyaSchurNonnegStatement : Prop :=
  ∀ {n : ℕ} {gamma : ℕ → ℝ},
    (∀ k, 0 ≤ gamma k) →
      (IsFiniteMultiplierSequence n gamma ↔
        IsPFPolynomial (jensenPolynomial n gamma))

/-- The remaining hard direction of the finite Polya--Schur theorem. -/
def finitePolyaSchurNonnegBackwardStatement : Prop :=
  ∀ {n : ℕ} {gamma : ℕ → ℝ},
    (∀ k, 0 ≤ gamma k) →
      IsPFPolynomial (jensenPolynomial n gamma) →
        IsFiniteMultiplierSequence n gamma

theorem finitePolyaSchur_nonneg_of_backward
    (hBack : finitePolyaSchurNonnegBackwardStatement) :
    finitePolyaSchurNonnegStatement :=
  fun hgamma => ⟨isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence hgamma,
    hBack hgamma⟩

/- The classical finite Pólya--Schur theorem `finitePolyaSchur_nonneg` is
established in `RealRooted.Hadamard`, where the Schur--Szegő composition
machinery (`finiteSchurSzegoComposition`) needed for the backward direction
`finitePolyaSchurNonnegBackwardStatement` is available. -/

/-- A nonnegative finite multiplier sequence preserves the PF cone on the same
degree range. -/
theorem isFinitePFMultiplierSequence_of_finiteMultiplierSequence
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hmult : IsFiniteMultiplierSequence n gamma) :
    IsFinitePFMultiplierSequence n gamma := by
  intro p hp hdeg
  by_cases hp0 : p = 0
  · simpa [hp0] using IsPFPolynomial.zero
  have hsplit := hmult hdeg (hp.ne_zero_and_splits hp0).2
  rcases hsplit with hzero | hsplits
  · simpa [hzero] using IsPFPolynomial.zero
  · exact IsPFPolynomial.of_realRooted_nonneg
      (hp.hasNonnegCoeffs.diagonalOperator hgamma) hsplits

/-- The finite Polya--Schur classification, used in the forward direction. -/
theorem jensenPolynomial_isPF_of_finiteMultiplierSequence
    (_hFPS : finitePolyaSchurNonnegStatement)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hmult : IsFiniteMultiplierSequence n gamma) :
    IsPFPolynomial (jensenPolynomial n gamma) :=
  isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence hgamma hmult

/-- The finite Polya--Schur classification, used in the reverse direction. -/
theorem isFiniteMultiplierSequence_of_jensenPolynomial
    (hFPS : finitePolyaSchurNonnegStatement)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma :=
  (hFPS hgamma).2 hjensen

/-- PF preservation obtained from the finite Polya--Schur classification and a
PF Jensen polynomial. -/
theorem isFinitePFMultiplierSequence_of_jensenPolynomial
    (hFPS : finitePolyaSchurNonnegStatement)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_finiteMultiplierSequence hgamma
    (isFiniteMultiplierSequence_of_jensenPolynomial hFPS hgamma hjensen)

end RealRooted
