import RealRooted.Hadamard.Basic

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Finite Schur--Szego composition interfaces

Classical finite composition statements, their finite Polya--Schur reductions,
and the degree-two discriminant base case.
-/

/-- **Finite Schur--Szegő composition theorem** (classical input).

If `f` is a PF polynomial (only real, nonpositive zeros) of degree at most `n`
and `p` has only real zeros, then their fixed-degree Schur--Szegő composition
`schurSzegoComp n f p` again has only real zeros, unless it vanishes
identically.

This is the classical composition/coincidence result of Schur and Szegő; it is
the single remaining analytic input behind the backward direction of the finite
Pólya--Schur theorem, isolated here as a named statement. -/
def finiteSchurSzegoCompositionStatement : Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    IsPFPolynomial f →
    f.natDegree ≤ n →
    p.natDegree ≤ n →
    p.Splits →
      schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits

/-- Nonzero core of the finite Schur--Szegő composition theorem.  The full
statement is equivalent to this one because the zero cases make the composition
identically zero. -/
def finiteSchurSzegoCompositionNonzeroStatement : Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    IsPFPolynomial f →
    f ≠ 0 →
    f.natDegree ≤ n →
    p ≠ 0 →
    p.natDegree ≤ n →
    p.Splits →
      schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits

theorem finiteSchurSzegoCompositionNonzero_of_full
    (h : finiteSchurSzegoCompositionStatement) :
    finiteSchurSzegoCompositionNonzeroStatement :=
  fun hf _hf0 hfdeg _hp0 hpdeg hp => h hf hfdeg hpdeg hp

theorem finiteSchurSzegoComposition_of_nonzero
    (h : finiteSchurSzegoCompositionNonzeroStatement) :
    finiteSchurSzegoCompositionStatement := by
  intro n f p hf hfdeg hpdeg hp
  by_cases hf0 : f = 0
  · simp [hf0, schurSzegoComp_zero_left]
  by_cases hp0 : p = 0
  · simp [hp0, schurSzegoComp_zero_right]
  exact h hf hf0 hfdeg hp0 hpdeg hp

theorem finiteSchurSzegoCompositionStatement_iff_nonzero :
    finiteSchurSzegoCompositionStatement ↔
      finiteSchurSzegoCompositionNonzeroStatement :=
  ⟨finiteSchurSzegoCompositionNonzero_of_full,
    finiteSchurSzegoComposition_of_nonzero⟩

/-- The backward direction of the finite Pólya--Schur theorem follows, by a
fully checked reduction, from the finite Schur--Szegő composition theorem: the
diagonal operator attached to `gamma` acting on a polynomial `p` of degree at
most `n` is exactly the Schur--Szegő composition of the PF Jensen polynomial of
`gamma` with `p`. -/
theorem finitePolyaSchurNonnegBackward_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    finitePolyaSchurNonnegBackwardStatement := by
  intro n gamma _hgamma hjensen p hp hsplit
  have hfdeg : (jensenPolynomial n gamma).natDegree ≤ n :=
    natDegree_jensenPolynomial_le n gamma
  simpa [← schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le hp] using
    hSZ hjensen hfdeg hp hsplit

/-- The backward finite Pólya--Schur direction follows directly from the
nonzero core of the finite Schur--Szegő theorem. -/
theorem finitePolyaSchurNonnegBackward_of_schurSzegoNonzero
    (hSZ : finiteSchurSzegoCompositionNonzeroStatement) :
    finitePolyaSchurNonnegBackwardStatement :=
  finitePolyaSchurNonnegBackward_of_schurSzego
    (finiteSchurSzegoComposition_of_nonzero hSZ)

/-- Full finite Pólya--Schur from the nonzero core of finite Schur--Szegő. -/
theorem finitePolyaSchur_nonneg_of_schurSzegoNonzero
    (hSZ : finiteSchurSzegoCompositionNonzeroStatement) :
    finitePolyaSchurNonnegStatement :=
  finitePolyaSchur_nonneg_of_backward
    (finitePolyaSchurNonnegBackward_of_schurSzegoNonzero hSZ)

/-- The finite Pólya--Schur theorem implies fixed-degree Schur--Szegő
composition.

The diagonal sequence used here is the binomially normalized coefficient
sequence of the PF factor.  The theorem
`jensenPolynomial_normalized_coeff_eq_of_natDegree_le` identifies its Jensen
polynomial with that factor, and the fixed-degree Schur--Szegő composition is
the corresponding diagonal operator on the other factor. -/
theorem finiteSchurSzegoComposition_of_finitePolyaSchur
    (hFPS : finitePolyaSchurNonnegStatement) :
    finiteSchurSzegoCompositionStatement := by
  intro n f p hf hfdeg hpdeg hsplit
  let gamma : ℕ → ℝ := fun k => f.coeff k / (Nat.choose n k : ℝ)
  have hgamma : ∀ k, 0 ≤ gamma k := fun k =>
    div_nonneg (hf.hasNonnegCoeffs k) (by positivity)
  have hjensen : IsPFPolynomial (jensenPolynomial n gamma) := by
    simpa [gamma] using hf.jensenPolynomial_normalized_coeff_of_natDegree_le hfdeg
  rw [schurSzegoComp_comm]
  simpa [gamma, schurSzegoComp_eq_diagonalOperator] using
    ((hFPS hgamma).2 hjensen) hpdeg hsplit

/-- Low-degree fixed-degree Schur--Szegő composition, through degree two.

This is the specialization of the finite Pólya--Schur route using the checked
degree-`≤ 2` backward theorem from `RealRooted.MultiplierSequence`; it does
not use the remaining classical Schur--Szegő input. -/
theorem finiteSchurSzegoComposition_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  let gamma : ℕ → ℝ := fun k => f.coeff k / (Nat.choose n k : ℝ)
  have hgamma : ∀ k, 0 ≤ gamma k := fun k =>
    div_nonneg (hf.hasNonnegCoeffs k) (by positivity)
  have hjensen : IsPFPolynomial (jensenPolynomial n gamma) := by
    simpa [gamma] using hf.jensenPolynomial_normalized_coeff_of_natDegree_le hfdeg
  rw [schurSzegoComp_comm]
  simpa [gamma, schurSzegoComp_eq_diagonalOperator] using
    finitePolyaSchurNonnegBackward_of_natDegree_le_two hn hgamma hjensen hpdeg hsplit

/-- Nonzero-core version of the checked degree-`≤ 2` Schur--Szegő composition
case. -/
theorem finiteSchurSzegoCompositionNonzero_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ n)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_natDegree_le_two hn hf hfdeg hpdeg hsplit

/-- Pure arithmetic core of the Schur--Szego discriminant inequality for two
degree-`≤ 2` factors at level `N ≥ 2`.  Here `a`, `b`, `c` are the coefficients
of the PF factor and `d`, `e`, `g` those of the splitting factor. -/
private theorem schurSzegoComp_disc_arith
    {a b c d e g N : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hfd : 4 * (a * c) ≤ b ^ 2)
    (hpd : 4 * (d * g) ≤ e ^ 2)
    (hN : 2 ≤ N) :
    4 * (a * d * (c * g / (N * (N - 1) / 2))) ≤ (b * e / N) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hN1ne : N - 1 ≠ 0 := ne_of_gt hN1
  have hac : 0 ≤ a * c := mul_nonneg ha hc
  have hkey : 4 * (a * d * (c * g / (N * (N - 1) / 2))) =
      8 * (a * c) * (d * g) / (N * (N - 1)) := by
    field_simp
    ring
  rw [hkey, div_pow, div_le_div_iff₀ (mul_pos hNpos hN1) (pow_pos hNpos 2)]
  rcases le_total (d * g) 0 with hdg | hdg
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hac (sq_nonneg N)) hdg,
      mul_nonneg (sq_nonneg (b * e)) (mul_pos hNpos hN1).le]
  · have h4dg : (0 : ℝ) ≤ 4 * (d * g) := by linarith
    have hmul : 4 * (a * c) * (4 * (d * g)) ≤ b ^ 2 * e ^ 2 :=
      mul_le_mul hfd hpd h4dg (sq_nonneg b)
    nlinarith [hmul, mul_nonneg hac hdg, sq_nonneg N,
      mul_nonneg (mul_nonneg hac hdg) (sq_nonneg N),
      mul_nonneg (mul_nonneg (sq_nonneg b) (sq_nonneg e))
        (mul_nonneg hNpos.le (show (0 : ℝ) ≤ N - 2 by linarith)),
      mul_nonneg (sq_nonneg (b * e)) (mul_pos hNpos hN1).le]

/-- **Schur--Szego discriminant inequality.**  For a level `n ≥ 2`, a PF factor
`f` of degree at most two, and a splitting factor `p` of degree at most two, the
fixed-degree Schur--Szego composition satisfies the quadratic discriminant
inequality `4 * coeff 0 * coeff 2 ≤ coeff 1 ^ 2`.

The two inputs to the estimate are the quadratic discriminant inequality
`quadratic_disc_coeff_le_of_splits_natDegree_le_two` applied to `f` (which
splits, being a PF polynomial) and to `p`, together with the nonnegativity of
the coefficients of `f`. -/
theorem four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp
    {n : ℕ} (hn : 2 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ 2) (hsplit : p.Splits) :
    4 * ((schurSzegoComp n f p).coeff 0 * (schurSzegoComp n f p).coeff 2) ≤
      (schurSzegoComp n f p).coeff 1 ^ 2 := by
  have h0n : 0 ≤ n := Nat.zero_le n
  have h1n : 1 ≤ n := le_trans (by norm_num) hn
  have hfd : 4 * (f.coeff 0 * f.coeff 2) ≤ f.coeff 1 ^ 2 := by
    rcases hf.eq_zero_or_splits with h | h
    · simp [h]
    · exact quadratic_disc_coeff_le_of_splits_natDegree_le_two hfdeg h
  have hpd : 4 * (p.coeff 0 * p.coeff 2) ≤ p.coeff 1 ^ 2 :=
    quadratic_disc_coeff_le_of_splits_natDegree_le_two hpdeg hsplit
  have hf0 : 0 ≤ f.coeff 0 := hf.hasNonnegCoeffs 0
  have hf2 : 0 ≤ f.coeff 2 := hf.hasNonnegCoeffs 2
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [coeff_schurSzegoComp_of_le h0n, coeff_schurSzegoComp_of_le h1n,
    coeff_schurSzegoComp_of_le hn, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.cast_one, div_one, Nat.cast_choose_two]
  exact schurSzegoComp_disc_arith hf0 hf2 hfd hpd hnR

/-- **Low-degree fixed-degree Schur--Szego composition (degree-`≤ 2` factors).**

For an arbitrary level `n`, a PF polynomial `f` of degree at most two, and a
splitting polynomial `p` of degree at most two, the fixed-degree Schur--Szego
composition `schurSzegoComp n f p` is either zero or splits over `ℝ`.

The composition has degree at most two, so it is settled by the quadratic
discriminant inequality
`four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp`; the
low-level cases `n ≤ 1` (where the composition already has degree at most one)
are handled separately.  Unlike
`finiteSchurSzegoComposition_of_natDegree_le_two`, here the level `n` is
unrestricted and the degree bound is placed on the two factors. -/
theorem finiteSchurSzegoComposition_of_factors_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ 2) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  by_cases hq0 : schurSzegoComp n f p = 0
  · exact Or.inl hq0
  by_cases hqle1 : (schurSzegoComp n f p).natDegree ≤ 1
  · exact Or.inr (isRealRooted_of_natDegree_le_one hq0 hqle1).2
  have hqle2 : (schurSzegoComp n f p).natDegree ≤ 2 :=
    le_trans (natDegree_schurSzegoComp_le_left n f p) hfdeg
  have hqdeg : (schurSzegoComp n f p).natDegree = 2 :=
    le_antisymm hqle2 (Nat.succ_le_of_lt (not_le.mp hqle1))
  have hn : 2 ≤ n := hqdeg ▸ natDegree_schurSzegoComp_le n f p
  have hdisc : 0 ≤ (schurSzegoComp n f p).coeff 1 ^ 2 -
      4 * (schurSzegoComp n f p).coeff 2 * (schurSzegoComp n f p).coeff 0 := by
    have := four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp
      hn hf hfdeg hpdeg hsplit
    nlinarith [this]
  obtain ⟨x, hx⟩ := exists_root_of_disc_nonneg
    (a := (schurSzegoComp n f p).coeff 2)
    (b := (schurSzegoComp n f p).coeff 1)
    (c := (schurSzegoComp n f p).coeff 0)
    (by
      have hlc : (schurSzegoComp n f p).leadingCoeff ≠ 0 :=
        leadingCoeff_ne_zero.mpr hq0
      rwa [Polynomial.leadingCoeff, hqdeg] at hlc)
    hdisc
  have hroot : (schurSzegoComp n f p).IsRoot x := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_eq_sum_range, hqdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    linear_combination hx
  exact Or.inr (Polynomial.Splits.of_natDegree_eq_two hqdeg hroot)
end RealRooted
