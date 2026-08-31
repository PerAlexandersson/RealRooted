import RealRooted.Hadamard.Basic

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Hadamard products of real-rooted polynomials

This compatibility module retains the finite-composition, analytic, and
consequence layers. Foundational Schur--Szego algebra is in
`Hadamard.Basic`.
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

/-- Newton's first coefficient inequality (`k = 1`) for a real polynomial that
splits and has degree at least two, in the level-`natDegree` normalization:
`2 * natDegree * coeff 0 * coeff 2 ≤ (natDegree - 1) * coeff 1 ^ 2`.

This is the splitting-only form of the ultra-log-concavity inequality
`hasUltraLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits` at index
`k = 1`; no nonnegativity of the coefficients is assumed. -/
theorem two_natDegree_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits
    {p : ℝ[X]} (hdeg : 2 ≤ p.natDegree) (hs : p.Splits) :
    2 * (p.natDegree : ℝ) * (p.coeff 0 * p.coeff 2) ≤
      ((p.natDegree : ℝ) - 1) * p.coeff 1 ^ 2 := by
  set t := p.roots.map Neg.neg with ht_def
  have htcard : Multiset.card t = p.natDegree := by
    rw [ht_def, Multiset.card_map, card_roots_of_splits hs]
  have h1d : 1 ≤ p.natDegree := le_trans one_le_two hdeg
  have hc0 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 0) (Nat.zero_le _)
  have hc1 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 1) h1d
  have hc2 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 2) hdeg
  rw [← ht_def] at hc0 hc1 hc2
  have hnewton := NewtonAux.newton_esymm_ineq t (n := p.natDegree)
    (m := p.natDegree - 1) htcard
    (Nat.sub_pos_of_lt (lt_of_lt_of_le one_lt_two hdeg))
    (Nat.sub_lt (lt_of_lt_of_le (by norm_num) hdeg) Nat.one_pos)
  have idxm1 : p.natDegree - 1 - 1 = p.natDegree - 2 := by rw [Nat.sub_sub]
  have idxp1 : p.natDegree - 1 + 1 = p.natDegree := Nat.sub_add_cancel h1d
  rw [idxm1, idxp1] at hnewton
  have hi0 : p.natDegree - 0 = p.natDegree := Nat.sub_zero _
  rw [hi0] at hc0
  have hcast_m : ((p.natDegree - 1 : ℕ) : ℝ) = (p.natDegree : ℝ) - 1 := by
    rw [Nat.cast_sub h1d]
    norm_num
  have hself : p.natDegree - (p.natDegree - 1) = 1 := Nat.sub_sub_self h1d
  have hcast_nm : ((p.natDegree - (p.natDegree - 1) : ℕ) : ℝ) = 1 := by
    rw [hself]
    norm_num
  have hcast_nm1 : ((p.natDegree - (p.natDegree - 1) + 1 : ℕ) : ℝ) = 2 := by
    rw [hself]
    norm_num
  rw [hcast_m, hcast_nm, hcast_nm1] at hnewton
  rw [hc0, hc1, hc2]
  nlinarith [mul_le_mul_of_nonneg_left hnewton (sq_nonneg p.leadingCoeff),
    sq_nonneg p.leadingCoeff]

/-- Level-lift arithmetic for Newton's `k = 1` inequality: an inequality in the
level-`N` normalization lifts to any larger level `M ≥ N`.  The key algebraic
identity is
`(N - 1) * ((M - 1) * A - 2 * M * B) =
  (M - 1) * ((N - 1) * A - 2 * N * B) + 2 * B * (M - N)`. -/
private theorem newton_level_lift_arith {A B M N : ℝ}
    (hA : 0 ≤ A) (hMN : N ≤ M) (hN1 : 1 < N)
    (hnat : 2 * N * B ≤ (N - 1) * A) :
    2 * M * B ≤ (M - 1) * A := by
  rcases le_or_gt B 0 with hB | hB
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ M - 1 by linarith) hA,
      mul_nonneg (show (0 : ℝ) ≤ M by linarith)
        (show (0 : ℝ) ≤ -B by linarith)]
  · have key : (N - 1) * ((M - 1) * A - 2 * M * B)
        = (M - 1) * ((N - 1) * A - 2 * N * B) + 2 * B * (M - N) := by
      ring
    nlinarith [key,
      mul_nonneg (show (0 : ℝ) ≤ M - 1 by linarith)
        (show (0 : ℝ) ≤ (N - 1) * A - 2 * N * B by linarith),
      mul_nonneg hB.le (show (0 : ℝ) ≤ M - N by linarith), hN1]

/-- Newton's first coefficient inequality (`k = 1`) in the level-`n`
normalization, for a splitting polynomial of degree at most `n`.  It is the
level-`natDegree` inequality
`two_natDegree_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits` lifted to
level `n` via `newton_level_lift_arith`; the low-degree cases (`natDegree ≤ 1`)
have `coeff 2 = 0`. -/
theorem two_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_of_natDegree_le
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) (hs : p.Splits) :
    2 * (n : ℝ) * (p.coeff 0 * p.coeff 2) ≤ ((n : ℝ) - 1) * p.coeff 1 ^ 2 := by
  rcases le_or_gt 2 p.natDegree with hdeg | hdeg
  · have hnat :=
      two_natDegree_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits hdeg hs
    have hNn : (p.natDegree : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpdeg
    have h1N : (1 : ℝ) < (p.natDegree : ℝ) := by
      have : (2 : ℝ) ≤ (p.natDegree : ℝ) := by exact_mod_cast hdeg
      linarith
    exact newton_level_lift_arith (A := p.coeff 1 ^ 2)
      (B := p.coeff 0 * p.coeff 2) (M := (n : ℝ)) (N := (p.natDegree : ℝ))
      (sq_nonneg _) hNn h1N hnat
  · have hc2 : p.coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt hdeg
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [hc2]
    nlinarith [sq_nonneg (p.coeff 1), hnR]

/-- Newton's second coefficient inequality (`k = 2`) for a real polynomial that
splits and has degree at least three, in the level-`natDegree` normalization:
`3 * (natDegree - 1) * coeff 1 * coeff 3 ≤
  2 * (natDegree - 2) * coeff 2 ^ 2`.

This is the splitting-only form of the ultra-log-concavity inequality
`hasUltraLogConcaveCoeffs_of_hasNonnegCoeffs_of_eq_zero_or_splits` at index
`k = 2`; no nonnegativity of the coefficients is assumed. -/
theorem newton_three_coeff_one_coeff_three_of_splits
    {p : ℝ[X]} (hdeg : 3 ≤ p.natDegree) (hs : p.Splits) :
    3 * ((p.natDegree : ℝ) - 1) * (p.coeff 1 * p.coeff 3) ≤
      2 * ((p.natDegree : ℝ) - 2) * p.coeff 2 ^ 2 := by
  set t := p.roots.map Neg.neg with ht_def
  have htcard : Multiset.card t = p.natDegree := by
    rw [ht_def, Multiset.card_map, card_roots_of_splits hs]
  have h1d : 1 ≤ p.natDegree := by lia
  have h2d : 2 ≤ p.natDegree := by lia
  have hc1 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 1) h1d
  have hc2 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 2) h2d
  have hc3 := coeff_eq_leadingCoeff_mul_esymm_neg_roots hs (k := 3) hdeg
  rw [← ht_def] at hc1 hc2 hc3
  have hnewton := NewtonAux.newton_esymm_ineq t (n := p.natDegree)
    (m := p.natDegree - 2) htcard (by lia) (by lia)
  have idxm1 : p.natDegree - 2 - 1 = p.natDegree - 3 := by rw [Nat.sub_sub]
  have idxp1 : p.natDegree - 2 + 1 = p.natDegree - 1 := by lia
  rw [idxm1, idxp1] at hnewton
  have hnm2 : p.natDegree - (p.natDegree - 2) = 2 := by lia
  have hcast_m : ((p.natDegree - 2 : ℕ) : ℝ) = (p.natDegree : ℝ) - 2 := by
    rw [Nat.cast_sub h2d]
    norm_num
  have hcast_nm : ((p.natDegree - (p.natDegree - 2) : ℕ) : ℝ) = 2 := by
    rw [hnm2]
    norm_num
  have hcast_nm1 : ((p.natDegree - (p.natDegree - 2) + 1 : ℕ) : ℝ) = 3 := by
    rw [hnm2]
    norm_num
  rw [hcast_m, hcast_nm, hcast_nm1] at hnewton
  rw [hc1, hc2, hc3]
  nlinarith [mul_le_mul_of_nonneg_left hnewton (sq_nonneg p.leadingCoeff),
    sq_nonneg p.leadingCoeff]

/-- Level-lift arithmetic for Newton's `k = 2` inequality: an inequality in the
level-`N` normalization lifts to any larger level `M ≥ N`.  The key algebraic
identity is
`(N - 1) * (2 * (M - 2) * A - 3 * (M - 1) * B) =
  (M - 1) * (2 * (N - 2) * A - 3 * (N - 1) * B) + 2 * A * (M - N)`. -/
private theorem newton_second_level_lift_arith {A B M N : ℝ}
    (hA : 0 ≤ A) (hMN : N ≤ M) (hN2 : 2 < N)
    (hnat : 3 * (N - 1) * B ≤ 2 * (N - 2) * A) :
    3 * (M - 1) * B ≤ 2 * (M - 2) * A := by
  rcases le_or_gt B 0 with hB | hB
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ M - 2 by linarith) hA,
      mul_nonneg (show (0 : ℝ) ≤ M - 1 by linarith)
        (show (0 : ℝ) ≤ -B by linarith)]
  · have key : (N - 1) * (2 * (M - 2) * A - 3 * (M - 1) * B)
        = (M - 1) * (2 * (N - 2) * A - 3 * (N - 1) * B) +
          2 * A * (M - N) := by
      ring
    nlinarith [key,
      mul_nonneg (show (0 : ℝ) ≤ M - 1 by linarith)
        (show (0 : ℝ) ≤ 2 * (N - 2) * A - 3 * (N - 1) * B by linarith),
      mul_nonneg hA (show (0 : ℝ) ≤ M - N by linarith), hN2]

/-- Newton's second coefficient inequality (`k = 2`) in the level-`n`
normalization, for a splitting polynomial of degree at most `n`.  It is the
level-`natDegree` inequality `newton_three_coeff_one_coeff_three_of_splits`
lifted to level `n`; the low-degree cases (`natDegree ≤ 2`) have
`coeff 3 = 0`. -/
theorem newton_three_coeff_one_coeff_three_of_splits_of_natDegree_le
    {n : ℕ} (hn : 3 ≤ n) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) (hs : p.Splits) :
    3 * ((n : ℝ) - 1) * (p.coeff 1 * p.coeff 3) ≤
      2 * ((n : ℝ) - 2) * p.coeff 2 ^ 2 := by
  rcases le_or_gt 3 p.natDegree with hdeg | hdeg
  · have hnat :=
      newton_three_coeff_one_coeff_three_of_splits hdeg hs
    have hNn : (p.natDegree : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpdeg
    have h2N : (2 : ℝ) < (p.natDegree : ℝ) := by
      have : (3 : ℝ) ≤ (p.natDegree : ℝ) := by exact_mod_cast hdeg
      linarith
    exact newton_second_level_lift_arith (A := p.coeff 2 ^ 2)
      (B := p.coeff 1 * p.coeff 3) (M := (n : ℝ)) (N := (p.natDegree : ℝ))
      (sq_nonneg _) hNn h2N hnat
  · have hc3 : p.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt hdeg
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [hc3]
    nlinarith [sq_nonneg (p.coeff 2), hnR]

/-- Normalized binomial-level coefficient log-concavity of a splitting polynomial.

Writing `γ k = p.coeff k / (n.choose k)`, the two adjacent inequalities
`γ 0 * γ 2 ≤ γ 1 ^ 2` and `γ 1 * γ 3 ≤ γ 2 ^ 2` hold when `p` splits and has
degree at most `n`.  These are exactly the level-`n` Newton inequalities at
`k = 1` and `k = 2`, divided through by the binomial factors.

This is the splitting-factor input for the normalized Jensen-product form of
the degree-`≤ 3` Schur--Szegő cubic-discriminant route. -/
theorem normalized_coeff_logConcave_of_splits_natDegree_le
    {n : ℕ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) (hs : p.Splits) :
    (p.coeff 0 / (n.choose 0 : ℝ)) * (p.coeff 2 / (n.choose 2 : ℝ)) ≤
        (p.coeff 1 / (n.choose 1 : ℝ)) ^ 2 ∧
      (p.coeff 1 / (n.choose 1 : ℝ)) * (p.coeff 3 / (n.choose 3 : ℝ)) ≤
        (p.coeff 2 / (n.choose 2 : ℝ)) ^ 2 := by
  set N : ℝ := (n : ℝ) with hN_def
  constructor
  · rcases le_or_gt 2 n with h2 | h2
    · have hpd :=
        two_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_of_natDegree_le
          h2 hpdeg hs
      have hN2 : (2 : ℝ) ≤ N := by rw [hN_def]; exact_mod_cast h2
      have hNpos : (0 : ℝ) < N := by linarith
      have hN1pos : (0 : ℝ) < N - 1 := by linarith
      have hc0 : (n.choose 0 : ℝ) = 1 := by norm_num
      have hc1 : (n.choose 1 : ℝ) = N := by rw [Nat.choose_one_right, hN_def]
      have hc2 : (n.choose 2 : ℝ) = N * (N - 1) / 2 := by rw [Nat.cast_choose_two, hN_def]
      rw [hc0, hc1, hc2]
      have key1 :
          p.coeff 0 / 1 * (p.coeff 2 / (N * (N - 1) / 2))
            = 2 * (p.coeff 0 * p.coeff 2) / (N * (N - 1)) := by
        field_simp
      have key2 : (p.coeff 1 / N) ^ 2 = p.coeff 1 ^ 2 / N ^ 2 := by rw [div_pow]
      rw [key1, key2, div_le_div_iff₀ (mul_pos hNpos hN1pos) (pow_pos hNpos 2)]
      nlinarith [mul_le_mul_of_nonneg_right hpd hNpos.le, hpd]
    · have hlt : n < 2 := h2
      have hc2 : (n.choose 2 : ℝ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt hlt]
        norm_num
      rw [hc2, div_zero, mul_zero]
      positivity
  · rcases le_or_gt 3 n with h3 | h3
    · have hpd :=
        newton_three_coeff_one_coeff_three_of_splits_of_natDegree_le
          h3 hpdeg hs
      have hN3 : (3 : ℝ) ≤ N := by rw [hN_def]; exact_mod_cast h3
      have hNpos : (0 : ℝ) < N := by linarith
      have hN1pos : (0 : ℝ) < N - 1 := by linarith
      have hN2pos : (0 : ℝ) < N - 2 := by linarith
      have hc1 : (n.choose 1 : ℝ) = N := by rw [Nat.choose_one_right, hN_def]
      have hc2 : (n.choose 2 : ℝ) = N * (N - 1) / 2 := by rw [Nat.cast_choose_two, hN_def]
      have hc3 : (n.choose 3 : ℝ) = N * (N - 1) * (N - 2) / 6 := by
        rw [Nat.cast_choose_three, hN_def]
      rw [hc1, hc2, hc3]
      have key1 :
          p.coeff 1 / N * (p.coeff 3 / (N * (N - 1) * (N - 2) / 6))
            = 6 * (p.coeff 1 * p.coeff 3) / (N ^ 2 * (N - 1) * (N - 2)) := by
        field_simp
      have key2 :
          (p.coeff 2 / (N * (N - 1) / 2)) ^ 2
            = 4 * p.coeff 2 ^ 2 / (N ^ 2 * (N - 1) ^ 2) := by
        field_simp
        ring
      have hden1 : (0 : ℝ) < N ^ 2 * (N - 1) * (N - 2) := by positivity
      have hden2 : (0 : ℝ) < N ^ 2 * (N - 1) ^ 2 := by positivity
      rw [key1, key2, div_le_div_iff₀ hden1 hden2]
      nlinarith [mul_le_mul_of_nonneg_right hpd
        (show (0 : ℝ) ≤ 2 * N ^ 2 * (N - 1) by positivity), hpd]
    · have hlt : n < 3 := h3
      have hc3 : (n.choose 3 : ℝ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt hlt]
        norm_num
      rw [hc3, div_zero, mul_zero]
      positivity

/-- First adjacent normalized log-concavity inequality for a splitting
polynomial at binomial level `n`. -/
theorem normalized_coeff_left_logConcave_of_splits_natDegree_le
    {n : ℕ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) (hs : p.Splits) :
    (p.coeff 0 / (n.choose 0 : ℝ)) * (p.coeff 2 / (n.choose 2 : ℝ)) ≤
      (p.coeff 1 / (n.choose 1 : ℝ)) ^ 2 :=
  (normalized_coeff_logConcave_of_splits_natDegree_le hpdeg hs).1

/-- Second adjacent normalized log-concavity inequality for a splitting
polynomial at binomial level `n`. -/
theorem normalized_coeff_right_logConcave_of_splits_natDegree_le
    {n : ℕ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) (hs : p.Splits) :
    (p.coeff 1 / (n.choose 1 : ℝ)) * (p.coeff 3 / (n.choose 3 : ℝ)) ≤
      (p.coeff 2 / (n.choose 2 : ℝ)) ^ 2 :=
  (normalized_coeff_logConcave_of_splits_natDegree_le hpdeg hs).2

/-- Binomially normalized coefficients of a PF polynomial are nonnegative. -/
theorem normalized_coeff_nonneg_of_isPF (n : ℕ) {f : ℝ[X]}
    (hf : IsPFPolynomial f) :
    ∀ k, 0 ≤ f.coeff k / (Nat.choose n k : ℝ) :=
  fun k =>
    div_nonneg (hf.hasNonnegCoeffs k)
      (by exact_mod_cast Nat.zero_le (Nat.choose n k))

/-- Constant normalized coefficient nonnegativity for a PF polynomial at
binomial level three. -/
theorem normalized_coeff_zero_nonneg_of_isPF_three {f : ℝ[X]}
    (hf : IsPFPolynomial f) :
    0 ≤ f.coeff 0 / (Nat.choose 3 0 : ℝ) :=
  normalized_coeff_nonneg_of_isPF 3 hf 0

/-- Linear normalized coefficient nonnegativity for a PF polynomial at
binomial level three. -/
theorem normalized_coeff_one_nonneg_of_isPF_three {f : ℝ[X]}
    (hf : IsPFPolynomial f) :
    0 ≤ f.coeff 1 / (Nat.choose 3 1 : ℝ) :=
  normalized_coeff_nonneg_of_isPF 3 hf 1

/-- Quadratic normalized coefficient nonnegativity for a PF polynomial at
binomial level three. -/
theorem normalized_coeff_two_nonneg_of_isPF_three {f : ℝ[X]}
    (hf : IsPFPolynomial f) :
    0 ≤ f.coeff 2 / (Nat.choose 3 2 : ℝ) :=
  normalized_coeff_nonneg_of_isPF 3 hf 2

/-- Cubic normalized coefficient nonnegativity for a PF polynomial at binomial
level three. -/
theorem normalized_coeff_three_nonneg_of_isPF_three {f : ℝ[X]}
    (hf : IsPFPolynomial f) :
    0 ≤ f.coeff 3 / (Nat.choose 3 3 : ℝ) :=
  normalized_coeff_nonneg_of_isPF 3 hf 3

/-- Normalized coefficient log-concavity of a degree-`≤ 3` PF polynomial.

Writing `γ k = f.coeff k / (3.choose k)`, the adjacent cubic log-concavity
inequalities `γ 0 * γ 2 ≤ γ 1 ^ 2` and `γ 1 * γ 3 ≤ γ 2 ^ 2` follow by
identifying the degree-three Jensen polynomial of `γ` with `f`.  This is the
PF-factor input parallel to
`normalized_coeff_logConcave_of_splits_natDegree_le` in the normalized
Jensen-product Schur--Szegő route. -/
theorem normalized_coeff_logConcave_of_isPF_natDegree_le_three
    {f : ℝ[X]} (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3) :
    (f.coeff 0 / (Nat.choose 3 0 : ℝ)) * (f.coeff 2 / (Nat.choose 3 2 : ℝ)) ≤
        (f.coeff 1 / (Nat.choose 3 1 : ℝ)) ^ 2 ∧
      (f.coeff 1 / (Nat.choose 3 1 : ℝ)) * (f.coeff 3 / (Nat.choose 3 3 : ℝ)) ≤
        (f.coeff 2 / (Nat.choose 3 2 : ℝ)) ^ 2 := by
  let gamma : ℕ → ℝ := fun k => f.coeff k / (Nat.choose 3 k : ℝ)
  have hjensen : IsPFPolynomial (jensenPolynomial 3 gamma) := by
    simpa [gamma] using hf.jensenPolynomial_normalized_coeff_of_natDegree_le hfdeg
  simpa [gamma] using hjensen.jensenPolynomial_three_logConcave

/-- First adjacent normalized log-concavity inequality for a degree-`≤ 3` PF
polynomial. -/
theorem normalized_coeff_left_logConcave_of_isPF_natDegree_le_three
    {f : ℝ[X]} (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3) :
    (f.coeff 0 / (Nat.choose 3 0 : ℝ)) * (f.coeff 2 / (Nat.choose 3 2 : ℝ)) ≤
      (f.coeff 1 / (Nat.choose 3 1 : ℝ)) ^ 2 :=
  (normalized_coeff_logConcave_of_isPF_natDegree_le_three hf hfdeg).1

/-- Second adjacent normalized log-concavity inequality for a degree-`≤ 3` PF
polynomial. -/
theorem normalized_coeff_right_logConcave_of_isPF_natDegree_le_three
    {f : ℝ[X]} (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3) :
    (f.coeff 1 / (Nat.choose 3 1 : ℝ)) * (f.coeff 3 / (Nat.choose 3 3 : ℝ)) ≤
      (f.coeff 2 / (Nat.choose 3 2 : ℝ)) ^ 2 :=
  (normalized_coeff_logConcave_of_isPF_natDegree_le_three hf hfdeg).2

/-- Pure arithmetic core of the Schur--Szego discriminant inequality when only
the PF factor has degree at most two.  Here `a`, `b`, `c` are the coefficients of
the PF factor and `d`, `e`, `g` those of the splitting factor, with the level-`N`
Newton inequality `2 N (d g) ≤ (N - 1) e^2` replacing the quadratic
discriminant of the splitting factor. -/
private theorem schurSzegoComp_pf_disc_arith
    {a b c d e g N : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hfd : 4 * (a * c) ≤ b ^ 2)
    (hpd : 2 * N * (d * g) ≤ (N - 1) * e ^ 2)
    (hN : 2 ≤ N) :
    4 * (a * d * (c * g / (N * (N - 1) / 2))) ≤ (b * e / N) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have hac : 0 ≤ a * c := mul_nonneg ha hc
  have hkey : 4 * (a * d * (c * g / (N * (N - 1) / 2))) =
      8 * (a * c) * (d * g) / (N * (N - 1)) := by
    field_simp
    ring
  rw [hkey, div_pow, div_le_div_iff₀ (mul_pos hNpos hN1) (pow_pos hNpos 2)]
  rcases le_total (d * g) 0 with hdg | hdg
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hac (sq_nonneg N)) hdg,
      mul_nonneg (sq_nonneg (b * e)) (mul_pos hNpos hN1).le]
  · have hmul : 4 * (a * c) * (2 * N * (d * g)) ≤
        b ^ 2 * ((N - 1) * e ^ 2) :=
      mul_le_mul hfd hpd (by nlinarith [hdg, hNpos.le]) (sq_nonneg b)
    nlinarith [mul_le_mul_of_nonneg_right hmul hNpos.le, sq_nonneg (b * e)]

/-- **Schur--Szego discriminant inequality with a degree-`≤ 2` PF factor.**
For a level `n ≥ 2`, a PF factor `f` of degree at most two, and a splitting
factor `p` of arbitrary degree at most `n`, the fixed-degree Schur--Szego
composition satisfies the quadratic discriminant inequality
`4 * coeff 0 * coeff 2 ≤ coeff 1 ^ 2`.

The input for `f` is its degree-`≤ 2` quadratic discriminant inequality
`quadratic_disc_coeff_le_of_splits_natDegree_le_two` (with the nonnegativity of
its coefficients); the input for `p` is the level-`n` Newton inequality
`two_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_of_natDegree_le`. -/
theorem four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp_of_pf
    {n : ℕ} (hn : 2 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    4 * ((schurSzegoComp n f p).coeff 0 * (schurSzegoComp n f p).coeff 2) ≤
      (schurSzegoComp n f p).coeff 1 ^ 2 := by
  have h0n : 0 ≤ n := Nat.zero_le n
  have h1n : 1 ≤ n := le_trans (by norm_num) hn
  have hfd : 4 * (f.coeff 0 * f.coeff 2) ≤ f.coeff 1 ^ 2 := by
    rcases hf.eq_zero_or_splits with h | h
    · simp [h]
    · exact quadratic_disc_coeff_le_of_splits_natDegree_le_two hfdeg h
  have hpd : 2 * (n : ℝ) * (p.coeff 0 * p.coeff 2) ≤
      ((n : ℝ) - 1) * p.coeff 1 ^ 2 :=
    two_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_of_natDegree_le
      hn hpdeg hsplit
  have hf0 : 0 ≤ f.coeff 0 := hf.hasNonnegCoeffs 0
  have hf2 : 0 ≤ f.coeff 2 := hf.hasNonnegCoeffs 2
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [coeff_schurSzegoComp_of_le h0n, coeff_schurSzegoComp_of_le h1n,
    coeff_schurSzegoComp_of_le hn, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.cast_one, div_one, Nat.cast_choose_two]
  exact schurSzegoComp_pf_disc_arith hf0 hf2 hfd hpd hnR

/-- **Fixed-degree Schur--Szego composition with a degree-`≤ 2` PF factor.**

For an arbitrary level `n`, a PF polynomial `f` of degree at most two, and a
splitting polynomial `p` of arbitrary degree at most `n`, the fixed-degree
Schur--Szego composition `schurSzegoComp n f p` is either zero or splits over
`ℝ`.

The composition has degree at most two (it inherits the degree bound of the PF
factor), so it is settled by the quadratic discriminant inequality
`four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp_of_pf`; the
low-level cases (composition of degree at most one) are handled separately.
Unlike `finiteSchurSzegoComposition_of_factors_natDegree_le_two`, here the
splitting factor `p` may have arbitrary degree up to the level `n`. -/
theorem finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
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
    have := four_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_schurSzegoComp_of_pf
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

/-- Nonzero-core version of the arbitrary-level Schur--Szego base case with a
degree-`≤ 2` PF factor. -/
theorem finiteSchurSzegoCompositionNonzero_of_pf_factor_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 2)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
    hf hfdeg hpdeg hsplit

/-- If the degree-`n` Jensen polynomial is PF and itself has degree at most
two, then the diagonal sequence is a finite multiplier sequence through degree
`n`.

Unlike `isFiniteMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two`,
the degree bound here is on the Jensen polynomial, not on the ambient level
`n`.  The proof is the Schur--Szegő base case with a degree-`≤ 2` PF factor,
applied to the Jensen polynomial and then identified with the diagonal
operator. -/
theorem isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma))
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFiniteMultiplierSequence n gamma := by
  intro p hp hsplit
  have hschur : schurSzegoComp n (jensenPolynomial n gamma) p = 0 ∨
      (schurSzegoComp n (jensenPolynomial n gamma) p).Splits :=
    finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
      hjensen hjdeg hp hsplit
  have heq : schurSzegoComp n (jensenPolynomial n gamma) p =
      diagonalOperator gamma p :=
    schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le hp
  rwa [heq] at hschur

/-- PF-preservation version of
`isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two`. -/
theorem isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma))
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_finiteMultiplierSequence hgamma
    (isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
      hjensen hjdeg)

/-- Finite multiplier sequences are classified by the PF Jensen polynomial in
the special case where that Jensen polynomial has degree at most two. -/
theorem isFiniteMultiplierSequence_iff_jensenPolynomial_of_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFiniteMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  ⟨isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence hgamma,
    fun hjensen =>
      isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
        hjensen hjdeg⟩

/-- PF-preservation classification in the special case where the Jensen
polynomial has degree at most two. -/
theorem isFinitePFMultiplierSequence_iff_jensenPolynomial_of_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  ⟨isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence,
    fun hjensen =>
      isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
        hgamma hjensen hjdeg⟩

/-- Nonzero-core version of the arbitrary-level degree-`≤ 2` Schur--Szego
base case. -/
theorem finiteSchurSzegoCompositionNonzero_of_factors_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 2)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ 2) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_factors_natDegree_le_two
    hf hfdeg hpdeg hsplit

/-- Cubic-discriminant splitting route for the fixed-degree Schur--Szegő
composition with a degree-`≤ 3` factor.

Once the fixed-degree Schur--Szegő composition's cubic coefficient discriminant
`cubicDiscr (schurSzegoComp n f p)` is known to be nonnegative, the composition
is either zero or splits over `ℝ`.  The composition inherits the degree bound of
the degree-`≤ 3` factor `f` via `natDegree_schurSzegoComp_le_left`, so the
result is the degree-`≤ 3` cubic discriminant criterion applied to it. -/
theorem finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg
    {n : ℕ} {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  Or.inr (splits_of_natDegree_le_three_cubicDiscr_nonneg
    (le_trans (natDegree_schurSzegoComp_le_left n f p) hfdeg) hdisc)

/-- Nonzero-core version of the degree-`≤ 3` cubic-discriminant splitting route
for the fixed-degree Schur--Szegő composition. -/
theorem finiteSchurSzegoCompositionNonzero_of_natDegree_le_three_cubicDiscr_nonneg
    {n : ℕ} {f p : ℝ[X]} (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg
    hfdeg hdisc

/-- Degree-`≤ 3` PF-factor Schur--Szegő composition reduced to the cubic
discriminant inequality.

This packages the exact hypotheses of the Schur--Szegő PF-factor route while
leaving only `0 ≤ cubicDiscr (schurSzegoComp n f p)` as the remaining
degree-three obligation. -/
theorem finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (_hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (_hpdeg : p.natDegree ≤ n) (_hsplit : p.Splits)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg
    hfdeg hdisc

/-- The level-three normalized diagonal-operator form is exactly the
Schur--Szego composition cubic discriminant. -/
theorem cubicDiscr_diagonalOperator_normalized_three_eq_cubicDiscr_schurSzegoComp
    (f q : ℝ[X]) :
    cubicDiscr (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ)) q) =
      cubicDiscr (schurSzegoComp 3 f q) := by
  rw [← schurSzegoComp_eq_diagonalOperator 3 q f, schurSzegoComp_comm]

/-- Level-three normalized diagonal-operator cubic-discriminant base case for
a degree-`≤ 3` PF factor and a splitting factor. -/
def pfCubicDiscrDiagonalNonnegStatement : Prop :=
  ∀ {f q : ℝ[X]},
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    q.natDegree ≤ 3 →
    q.Splits →
    0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ)) q)

/-- The normalized diagonal base case is equivalent to the level-three
Schur--Szego cubic-discriminant base case. -/
theorem pfCubicDiscrDiagonalNonnegStatement_iff :
    pfCubicDiscrDiagonalNonnegStatement ↔
      ∀ {f q : ℝ[X]},
        IsPFPolynomial f →
        f.natDegree ≤ 3 →
        q.natDegree ≤ 3 →
        q.Splits →
        0 ≤ cubicDiscr (schurSzegoComp 3 f q) := by
  simp only [pfCubicDiscrDiagonalNonnegStatement,
    cubicDiscr_diagonalOperator_normalized_three_eq_cubicDiscr_schurSzegoComp]

/-- The classical fixed-degree Schur--Szego theorem discharges the isolated
level-three diagonal cubic-discriminant base case. -/
theorem pfCubicDiscrDiagonalNonnegStatement_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    pfCubicDiscrDiagonalNonnegStatement :=
  pfCubicDiscrDiagonalNonnegStatement_iff.mpr fun {f q} hf hfdeg hqdeg hsplit => by
    rcases hSZ hf hfdeg hqdeg hsplit with hzero | hs
    · simp [hzero, cubicDiscr]
    · exact cubicDiscr_nonneg_of_splits_natDegree_le_three
        ((natDegree_schurSzegoComp_le_left 3 f q).trans hfdeg) hs

/-- The isolated normalized diagonal base case discharges the level-three
degree-`≤ 3` PF-factor Schur--Szego composition route. -/
theorem finiteSchurSzegoComposition_of_pf_factor_three_of_base
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {f q : ℝ[X]} (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hqdeg : q.natDegree ≤ 3) (hsplit : q.Splits) :
    schurSzegoComp 3 f q = 0 ∨ (schurSzegoComp 3 f q).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hqdeg hsplit
    (pfCubicDiscrDiagonalNonnegStatement_iff.mp h hf hfdeg hqdeg hsplit)

/-- The isolated level-three diagonal base case proves the reflected
diagonal-operator discriminant input at every level `n ≥ 3`. -/
theorem cubicDiscr_reflect_diagonalOperator_nonneg_of_pfCubicDiscrDiagonalNonneg
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (reflect 3 ((derivative^[n - 3]) (reflect n p)))) :=
  h hf hfdeg
    (natDegree_reflect_iterate_derivative_reflect_le_three hn hpdeg)
    (reflect_iterate_derivative_reflect_splits_of_splits hn hpdeg hsplit)

/-- The isolated level-three diagonal base case proves high-level
cubic-discriminant nonnegativity for degree-`≤ 3` PF factors. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  cubicDiscr_schurSzegoComp_nonneg_of_reflect_diagonalOperator_three
    hn hfdeg hpdeg
    (cubicDiscr_reflect_diagonalOperator_nonneg_of_pfCubicDiscrDiagonalNonneg
      h hn hf hfdeg hpdeg hsplit)

/-- Low-level (`n < 3`) cubic-discriminant nonnegativity for a degree-`≤ 3`
PF factor with `f.natDegree ≤ n`. -/
private theorem cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_natDegree_lt_three
    {n : ℕ} (hn : n < 3) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) := by
  rcases finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
      hf (hfn.trans (Nat.lt_succ_iff.mp hn)) hpdeg hsplit with hzero | hs
  · simp [hzero, cubicDiscr]
  · exact cubicDiscr_nonneg_of_splits_natDegree_le_three
      ((natDegree_schurSzegoComp_le_left n f p).trans hfdeg) hs

/-- The isolated level-three diagonal base case proves the corrected all-level
cubic-discriminant route retaining `f.natDegree ≤ n`. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_leftNatDegree_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  (le_or_gt 3 n).elim
    (fun hn =>
      cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_of_pfDiagonalBase
        h hn hf hfdeg hpdeg hsplit)
    (fun hn =>
      cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_natDegree_lt_three
        hn hf hfdeg hfn hpdeg hsplit)

/-- Degree-`≤ 3` Schur--Szego composition reduced to the reflected-derivative
diagonal-operator discriminant. -/
theorem finiteSchurSzegoComposition_of_pf_factor_le_three_reflect_diagonalOperator
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hdisc : 0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (reflect 3 ((derivative^[n - 3]) (reflect n p))))) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit
    (cubicDiscr_schurSzegoComp_nonneg_of_reflect_diagonalOperator_three
      hn hfdeg hpdeg hdisc)

/-- The isolated level-three diagonal base case discharges the high-level
degree-`≤ 3` PF-factor Schur--Szego route. -/
theorem finiteSchurSzegoComposition_of_pf_factor_le_three_of_pfCubicDiscrDiagonalNonneg
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit
    (cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_of_pfDiagonalBase
      h hn hf hfdeg hpdeg hsplit)

/-- Corrected all-level degree-`≤ 3` PF-factor Schur--Szego route from the
isolated level-three diagonal base case, retaining `f.natDegree ≤ n`. -/
theorem
    finiteSchurSzegoComposition_of_pf_factor_le_three_leftNatDegree_of_pfCubicDiscrDiagonalNonneg
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit
    (cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_leftNatDegree_of_pfDiagonalBase
      h hf hfdeg hfn hpdeg hsplit)

/-- Degree-`≤ 3` PF-factor Schur--Szegő composition reduced to the
denominator-cleared cubic-discriminant numerator at levels `n ≥ 3`. -/
theorem finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hnum : 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit
    ((cubicDiscr_schurSzegoComp_nonneg_iff_of_three_le hn f p).2 hnum)

/-- Corrected all-level denominator-cleared numerator route for cubic
discriminant nonnegativity, retaining the original fixed-degree Schur--Szegő
hypothesis `f.natDegree ≤ n`.

For `3 ≤ n`, this is exactly the denominator-cleared numerator equivalence.
For `n < 3`, the left-degree hypothesis makes `f` a degree-`≤ 2` PF factor,
so the checked quadratic Schur--Szegő base case supplies splitting, hence
cubic-discriminant nonnegativity in degree at most three. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_leftNatDegree_num_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  (le_or_gt 3 n).elim
    (fun hn =>
      (cubicDiscr_schurSzegoComp_nonneg_iff_of_three_le hn f p).2
        (hnum hn))
    (fun hn =>
      cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_natDegree_lt_three
        hn hf hfdeg hfn hpdeg hsplit)

/-- Corrected all-level denominator-cleared numerator route for degree-`≤ 3`
PF factors, retaining the original fixed-degree Schur--Szegő hypothesis
`f.natDegree ≤ n`.

For `3 ≤ n`, this is the denominator-cleared cubic-discriminant route.  For
`n < 3`, the hypothesis `f.natDegree ≤ n` makes `f` a degree-`≤ 2` PF factor,
so the checked quadratic Schur--Szegő base case applies directly. -/
theorem finiteSchurSzegoComposition_of_pf_factor_le_three_leftNatDegree_num_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit
    (cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_leftNatDegree_num_nonneg
      hf hfdeg hfn hpdeg hsplit hnum)

/-- Nonzero-core version of the degree-`≤ 3` PF-factor Schur--Szegő reduction
to the cubic discriminant inequality. -/
theorem finiteSchurSzegoCompositionNonzero_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit hdisc

/-- Nonzero-core version of the high-level diagonal-base route for degree-`≤ 3`
PF factors. -/
theorem finiteSchurSzegoCompositionNonzero_of_pf_factor_le_three_of_pfCubicDiscrDiagonalNonneg
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_le_three_of_pfCubicDiscrDiagonalNonneg
    h hn hf hfdeg hpdeg hsplit

/-- Nonzero-core version of the corrected all-level diagonal-base route for
degree-`≤ 3` PF factors, retaining `f.natDegree ≤ n`. -/
theorem
    finiteSchurSzegoCompositionNonzero_of_pf_factor_le_three_leftNatDegree_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_le_three_leftNatDegree_of_pfCubicDiscrDiagonalNonneg
    h hf hfdeg hfn hpdeg hsplit

/-- Nonzero-core version of the degree-`≤ 3` PF-factor Schur--Szegő reduction
to the denominator-cleared cubic-discriminant numerator at levels `n ≥ 3`. -/
theorem finiteSchurSzegoCompositionNonzero_of_pf_factor_le_three_cubicDiscrNumerator_nonneg
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hnum : 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
    hn hf hfdeg hpdeg hsplit hnum

/-- Nonzero-core version of the corrected all-level denominator-cleared
numerator route for degree-`≤ 3` PF factors, retaining the original
fixed-degree Schur--Szegő hypothesis `f.natDegree ≤ n`. -/
theorem finiteSchurSzegoCompositionNonzero_of_pf_factor_le_three_leftNatDegree_num_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_le_three_leftNatDegree_num_nonneg
    hf hfdeg hfn hpdeg hsplit hnum

/-- The full finite Schur--Szegő theorem implies the finite Pólya--Schur
theorem. -/
theorem finitePolyaSchur_nonneg_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    finitePolyaSchurNonnegStatement :=
  finitePolyaSchur_nonneg_of_backward
    (finitePolyaSchurNonnegBackward_of_schurSzego hSZ)

/-- Fixed-degree Schur--Szegő composition and finite Pólya--Schur are
equivalent classical inputs in the nonnegative-coefficient convention used
here. -/
theorem finiteSchurSzegoCompositionStatement_iff_finitePolyaSchur :
    finiteSchurSzegoCompositionStatement ↔ finitePolyaSchurNonnegStatement :=
  ⟨finitePolyaSchur_nonneg_of_schurSzego,
    finiteSchurSzegoComposition_of_finitePolyaSchur⟩

/-- The finite Pólya--Schur theorem implies the nonzero core of fixed-degree
Schur--Szegő composition. -/
theorem finiteSchurSzegoCompositionNonzero_of_finitePolyaSchur
    (hFPS : finitePolyaSchurNonnegStatement) :
    finiteSchurSzegoCompositionNonzeroStatement :=
  finiteSchurSzegoCompositionNonzero_of_full
    (finiteSchurSzegoComposition_of_finitePolyaSchur hFPS)

/-- The nonzero core of fixed-degree Schur--Szegő composition and finite
Pólya--Schur are equivalent classical inputs in the local convention. -/
theorem finiteSchurSzegoCompositionNonzeroStatement_iff_finitePolyaSchur :
    finiteSchurSzegoCompositionNonzeroStatement ↔ finitePolyaSchurNonnegStatement :=
  ⟨finitePolyaSchur_nonneg_of_schurSzegoNonzero,
    finiteSchurSzegoCompositionNonzero_of_finitePolyaSchur⟩

/-- The nonzero Schur--Szegő core is equivalent to the hard backward direction
of finite Pólya--Schur. -/
theorem finiteSchurSzegoCompositionNonzeroStatement_iff_finitePolyaSchurBackward :
    finiteSchurSzegoCompositionNonzeroStatement ↔
      finitePolyaSchurNonnegBackwardStatement :=
  ⟨finitePolyaSchurNonnegBackward_of_schurSzegoNonzero,
    fun hBack =>
      finiteSchurSzegoCompositionNonzero_of_finitePolyaSchur
        (finitePolyaSchur_nonneg_of_backward hBack)⟩

theorem apolarEval_apolarTwist (n : Nat) (z : ℂ) (g : ℂ[X]) (w : ℂ) :
    apolarEval n (apolarTwist n z g) w =
      ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℂ) * g.coeff i * (-z) ^ i * w ^ (n - i) := by
  unfold apolarEval
  rw [← Finset.sum_range_reflect
    (fun i ↦ (Nat.choose n i : ℂ) * g.coeff i * (-z) ^ i * w ^ (n - i)) (n + 1)]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [coeff_apolarTwist, if_pos hj']
  have he : n + 1 - 1 - j = n - j := by simp [*]
  rw [he]
  have hnn : n - (n - j) = j := by lia
  rw [hnn]
  have hnegz : (-z) ^ (n - j) = (-1 : ℂ) ^ (n - j) * z ^ (n - j) := by rw [neg_pow]
  rw [hnegz, Nat.choose_symm hj']
  ring

theorem apolarEval_apolarTwist_eq_mul (n : Nat) (z : ℂ) (g : ℂ[X]) {w : ℂ}
    (hw : w ≠ 0) :
    apolarEval n (apolarTwist n z g) w = w ^ n * apolarEval n g (-z / w) := by
  rw [apolarEval_apolarTwist, apolarEval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hwi : w ^ (n - i) = w ^ n / w ^ i := by
    rw [eq_div_iff (pow_ne_zero i hw), ← pow_add, Nat.sub_add_cancel hi']
  rw [hwi, div_pow]
  grind

theorem isRoot_binomialLift_apolarTwist_iff (n : Nat) (z : ℂ) (g : ℂ[X]) {w : ℂ}
    (hw : w ≠ 0) :
    (binomialLift n (apolarTwist n z g)).IsRoot w ↔
      (binomialLift n g).IsRoot (-z / w) := by
  simp only [Polynomial.IsRoot, eval_binomialLift]
  rw [apolarEval_apolarTwist_eq_mul n z g hw]
  simp [*]

theorem exists_apolarTwist_root_of_grace_lowerHalf {n : Nat} {b : ℝ}
    {f g : ℂ[X]} {z : ℂ}
    (hf : (binomialLift n f).natDegree = n)
    (htw : (binomialLift n (apolarTwist n z g)).natDegree = n)
    (hcomp : ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℂ) * f.coeff k * g.coeff k * z ^ k = 0)
    (hroots : (binomialLift n f).RootsIn (lowerHalf b)) :
    (binomialLift n (apolarTwist n z g)).HasRootIn (lowerHalf b) := by
  have hap : AreApolar n f (apolarTwist n z g) :=
    (areApolar_apolarTwist_iff n f g z).2 hcomp
  exact grace_apolarity_lowerHalf hf.le htw hap hroots

theorem exists_apolarTwist_root_of_grace_upperHalf {n : Nat} {b : ℝ}
    {f g : ℂ[X]} {z : ℂ}
    (hf : (binomialLift n f).natDegree = n)
    (htw : (binomialLift n (apolarTwist n z g)).natDegree = n)
    (hcomp : ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℂ) * f.coeff k * g.coeff k * z ^ k = 0)
    (hroots : (binomialLift n f).RootsIn (upperHalf b)) :
    (binomialLift n (apolarTwist n z g)).HasRootIn (upperHalf b) := by
  have hap : AreApolar n f (apolarTwist n z g) :=
    (areApolar_apolarTwist_iff n f g z).2 hcomp
  exact grace_apolarity_upperHalf hf htw hap hroots

theorem eval_map_schurSzegoComp_eq_sum (n : Nat) (f p : ℝ[X])
    {F₀ P₀ : ℂ[X]}
    (hF : binomialLift n F₀ = f.map Complex.ofRealHom)
    (hP : binomialLift n P₀ = p.map Complex.ofRealHom)
    (z : ℂ) :
    ((schurSzegoComp n f p).map Complex.ofRealHom).eval z =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * F₀.coeff k * P₀.coeff k * z ^ k := by
  rw [Polynomial.eval_eq_sum_range' (n := n + 1)
    (Nat.lt_succ_of_le ((natDegree_map_le).trans (natDegree_schurSzegoComp_le n f p)))]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [coeff_map, coeff_schurSzegoComp_of_le hk']
  have hFk : (f.map Complex.ofRealHom).coeff k = (Nat.choose n k : ℂ) * F₀.coeff k := by
    rw [← hF, coeff_binomialLift, if_pos hk']
  have hPk : (p.map Complex.ofRealHom).coeff k = (Nat.choose n k : ℂ) * P₀.coeff k := by
    rw [← hP, coeff_binomialLift, if_pos hk']
  rw [coeff_map, Complex.ofRealHom_eq_coe] at hFk hPk
  have : (Nat.choose n k : ℂ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℂ) hk'
  rw [Complex.ofRealHom_eq_coe, Complex.ofReal_div, Complex.ofReal_mul]
  push_cast
  grind

theorem coeff_n_binomialLift_apolarTwist (n : Nat) (z : ℂ) {F₀ f : ℂ[X]}
    (hF : binomialLift n F₀ = f) :
    (binomialLift n (apolarTwist n z F₀)).coeff n = f.coeff 0 := by
  rw [coeff_binomialLift, if_pos (le_refl n), coeff_apolarTwist, if_pos (le_refl n)]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, one_mul]
  rw [← hF, coeff_binomialLift, if_pos (Nat.zero_le n)]
  simp

theorem natDegree_binomialLift_apolarTwist (n : Nat) (z : ℂ) {F₀ f : ℂ[X]}
    (hF : binomialLift n F₀ = f) (hf0 : f.coeff 0 ≠ 0) :
    (binomialLift n (apolarTwist n z F₀)).natDegree = n := by
  refine le_antisymm (natDegree_binomialLift_le n _) ?_
  apply Polynomial.le_natDegree_of_ne_zero
  rw [coeff_n_binomialLift_apolarTwist n z hF]
  simp [*]

theorem pf_complex_root_nonpos_real {f : ℝ[X]} (hf : IsPFPolynomial f) (hf0 : f ≠ 0)
    {μ : ℂ} (hμ : (f.map Complex.ofRealHom).IsRoot μ) :
    μ.im = 0 ∧ μ.re ≤ 0 := by
  have hsplits : f.Splits := hf.eq_zero_or_splits.resolve_left hf0
  obtain ⟨r, hr⟩ : μ ∈ Complex.ofRealHom.range := hsplits.mem_range_of_isRoot hf0 hμ
  have hr_root : f.IsRoot r := by
    have hev : (f.map Complex.ofRealHom).eval μ = 0 := hμ
    rw [← hr, Polynomial.eval_map, Polynomial.eval₂_hom] at hev
    simp_all
  have : r ≤ 0 := hf.roots_nonpos r ((Polynomial.mem_roots hf0).mpr hr_root)
  rw [← hr]
  refine ⟨by simp [Complex.ofRealHom_eq_coe], ?_⟩
  simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_re]
  grind

theorem splits_complex_root_im_zero {p : ℝ[X]} (hp0 : p ≠ 0) (hsplit : p.Splits)
    {μ : ℂ} (hμ : (p.map Complex.ofRealHom).IsRoot μ) :
    μ.im = 0 := by
  obtain ⟨r, hr⟩ : μ ∈ Complex.ofRealHom.range := hsplit.mem_range_of_isRoot hp0 hμ
  rw [← hr]
  simp [Complex.ofRealHom_eq_coe]

theorem core_squeeze {n : Nat} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree = n)
    (hf00 : f.coeff 0 ≠ 0)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree = n) (hsplit : p.Splits) :
    (schurSzegoComp n f p).Splits := by
  apply Polynomial.splits_of_all_roots_real
  intro z hz
  obtain ⟨F₀, hF⟩ := exists_binomialLift_eq (f.map Complex.ofRealHom)
    (le_of_eq (by rw [natDegree_map_eq_of_injective Complex.ofReal_injective, hfdeg]))
  obtain ⟨P₀, hP⟩ := exists_binomialLift_eq (p.map Complex.ofRealHom)
    (le_of_eq (by rw [natDegree_map_eq_of_injective Complex.ofReal_injective, hpdeg]))
  have : ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℂ) * F₀.coeff k * P₀.coeff k * z ^ k = 0 := by
    rw [← eval_map_schurSzegoComp_eq_sum n f p hF hP z]
    simp [*]
  by_cases hz0 : z = 0
  · simp [*]
  have hPdeg : (binomialLift n P₀).natDegree = n := by simp [*]
  have hf00c : (f.map Complex.ofRealHom).coeff 0 ≠ 0 := by simp [*]
  have hTwdeg : (binomialLift n (apolarTwist n z F₀)).natDegree = n :=
    natDegree_binomialLift_apolarTwist n z hF hf00c
  have hPmap : binomialLift n P₀ = p.map Complex.ofRealHom := hP
  have hRootsLower : (binomialLift n P₀).RootsIn (lowerHalf 0) := fun w hw => by
    rw [mem_lowerHalf]
    rw [hPmap] at hw
    have := splits_complex_root_im_zero hp0 hsplit hw
    simp [*]
  have hRootsUpper : (binomialLift n P₀).RootsIn (upperHalf 0) := fun w hw => by
    rw [mem_upperHalf]
    rw [hPmap] at hw
    have := splits_complex_root_im_zero hp0 hsplit hw
    simp [*]
  have hsum' : ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℂ) * P₀.coeff k * F₀.coeff k * z ^ k = 0 := by grind
  obtain ⟨w, hwroot, hwmem⟩ :=
    exists_apolarTwist_root_of_grace_lowerHalf hPdeg hTwdeg hsum' hRootsLower
  obtain ⟨w', hw'root, hw'mem⟩ :=
    exists_apolarTwist_root_of_grace_upperHalf hPdeg hTwdeg hsum' hRootsUpper
  rw [mem_lowerHalf] at hwmem
  rw [mem_upperHalf] at hw'mem
  have : f.coeff n ≠ 0 := by
    rw [← hfdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hf0
  have : F₀.coeff n = (f.map Complex.ofRealHom).coeff n := by
    have : (f.map Complex.ofRealHom).coeff n = (Nat.choose n n : ℂ) * F₀.coeff n := by
      rw [← hF, coeff_binomialLift, if_pos (le_refl n)]
    simp [*]
  have hcoeff0 : (binomialLift n (apolarTwist n z F₀)).coeff 0 ≠ 0 := by
    rw [coeff_binomialLift, if_pos (Nat.zero_le n), coeff_apolarTwist, if_pos (Nat.zero_le n)]
    simp [*]
  have hwne : w ≠ 0 := by
    rintro rfl
    apply hcoeff0
    have : (binomialLift n (apolarTwist n z F₀)).eval 0 = 0 := hwroot
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [*]
  have hw'ne : w' ≠ 0 := by
    rintro rfl
    apply hcoeff0
    have : (binomialLift n (apolarTwist n z F₀)).eval 0 = 0 := hw'root
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [*]
  have hμ : (binomialLift n F₀).IsRoot (-z / w) :=
    (isRoot_binomialLift_apolarTwist_iff n z F₀ hwne).mp hwroot
  have hμ' : (binomialLift n F₀).IsRoot (-z / w') :=
    (isRoot_binomialLift_apolarTwist_iff n z F₀ hw'ne).mp hw'root
  rw [hF] at hμ hμ'
  obtain ⟨hμim, hμre⟩ := pf_complex_root_nonpos_real hf hf0 hμ
  obtain ⟨hμ'im, hμ're⟩ := pf_complex_root_nonpos_real hf hf0 hμ'
  set μ := -z / w with hμdef
  set μ' := -z / w' with hμ'def
  have hzμ : z = -(μ * w) := by simp [*]
  have hzμ' : z = -(μ' * w') := by grind
  have hμre0 : μ.re < 0 := by
    rcases lt_or_eq_of_le hμre with h | h
    · grind
    · exfalso; apply hz0
      have hμ0 : μ = 0 :=
        Complex.ext (by rw [Complex.zero_re, ← h]) (by rw [hμim, Complex.zero_im])
      grind
  have hμ're0 : μ'.re < 0 := by
    rcases lt_or_eq_of_le hμ're with h | h
    · grind
    · exfalso; apply hz0
      have hμ'0 : μ' = 0 :=
        Complex.ext (by rw [Complex.zero_re, ← h]) (by rw [hμ'im, Complex.zero_im])
      grind
  have hzim : z.im = -(μ.re * w.im) := by
    rw [hzμ]
    simp [Complex.mul_im, hμim]
  have hzim' : z.im = -(μ'.re * w'.im) := by
    rw [hzμ']
    simp [Complex.mul_im, hμ'im]
  have : z.im ≤ 0 := by
    rw [hzim]
    nlinarith [hwmem, hμre0]
  have : 0 ≤ z.im := by
    rw [hzim']
    nlinarith [hw'mem, hμ're0]
  linarith




theorem reflect_schurSzegoComp (n : Nat) (f p : ℝ[X]) :
    reflect n (schurSzegoComp n f p) =
      schurSzegoComp n (reflect n f) (reflect n p) := by
  ext k
  rw [coeff_reflect]
  by_cases hk : k ≤ n
  · rw [revAt_le hk, coeff_schurSzegoComp_of_le (Nat.sub_le n k),
      coeff_schurSzegoComp_of_le hk, coeff_reflect, coeff_reflect,
      revAt_le hk, Nat.choose_symm hk]
  · rw [coeff_schurSzegoComp_eq_zero_of_lt (Nat.lt_of_not_le hk),
      revAt_eq_self_of_lt (Nat.lt_of_not_le hk),
      coeff_schurSzegoComp_eq_zero_of_lt (Nat.lt_of_not_le hk)]

theorem schurSzegoComp_X_mul_left (n : Nat) (hn : 1 ≤ n) (f₁ p : ℝ[X]) :
    schurSzegoComp n (X * f₁) p =
      X * schurSzegoComp (n - 1) f₁ (C (n : ℝ)⁻¹ * derivative p) := by
  ext k
  rcases k with _ | k
  · rw [coeff_schurSzegoComp_of_le (Nat.zero_le n), coeff_X_mul_zero, zero_mul,
      zero_div, coeff_X_mul_zero]
  · rw [coeff_X_mul]
    by_cases hk : k ≤ n - 1
    · rw [coeff_schurSzegoComp_of_le (by lia : k + 1 ≤ n),
        coeff_schurSzegoComp_of_le hk, coeff_X_mul, coeff_C_mul, coeff_derivative]
      have : ((n - 1).choose k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℝ) hk
      have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
      have : (n.choose (k + 1) : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℝ) (by lia)
      have hnat : n * (n - 1).choose k = n.choose (k + 1) * (k + 1) := by
        have := Nat.add_one_mul_choose_eq (n - 1) k
        simp_all
      have : (n.choose (k + 1) : ℝ) * ((k : ℝ) + 1) = (n : ℝ) * ((n - 1).choose k : ℝ) := by
        have := congrArg (Nat.cast (R := ℝ)) hnat
        grind
      grind
    · rw [coeff_schurSzegoComp_eq_zero_of_lt (by lia : n < k + 1),
        coeff_schurSzegoComp_eq_zero_of_lt (by lia : n - 1 < k)]

theorem schurSzegoComp_eq_diagonalOperator_pred (n : Nat) (hn : 1 ≤ n) (f p : ℝ[X])
    (hpn : p.coeff n = 0) :
    schurSzegoComp n f p =
      diagonalOperator (fun k ↦ ((n : ℝ) - k) / n) (schurSzegoComp (n - 1) f p) := by
  ext k
  rw [coeff_diagonalOperator]
  by_cases hk : k ≤ n - 1
  · rw [coeff_schurSzegoComp_of_le (by lia : k ≤ n), coeff_schurSzegoComp_of_le hk]
    have : ((n - 1).choose k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℝ) hk
    have : (n.choose k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℝ) (by lia)
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    have hnat : (n - 1).choose k * n = n.choose k * (n - k) := by
      have := Nat.choose_mul_succ_eq (n - 1) k
      simp_all
    have : ((n - 1).choose k : ℝ) * (n : ℝ) = (n.choose k : ℝ) * ((n : ℝ) - k) := by
      have := congrArg (Nat.cast (R := ℝ)) hnat
      push_cast [Nat.cast_sub (by lia : k ≤ n)] at this
      assumption
    grind
  · rw [coeff_schurSzegoComp_eq_zero_of_lt (by lia : n - 1 < k)]
    by_cases hkn : k = n
    · rw [hkn, coeff_schurSzegoComp_of_le (le_refl n)]
      simp [hpn]
    · rw [coeff_schurSzegoComp_eq_zero_of_lt (by lia : n < k), mul_zero]

theorem diagonalOperator_pred_eq_reflect_derivative (n : Nat) (hn : 1 ≤ n)
    (q : ℝ[X]) (hq : q.natDegree ≤ n) :
    diagonalOperator (fun k ↦ ((n : ℝ) - k) / n) q =
      C (n : ℝ)⁻¹ * reflect (n - 1) (derivative (reflect n q)) := by
  ext k
  rw [coeff_diagonalOperator, coeff_C_mul, coeff_reflect]
  by_cases hk : k ≤ n - 1
  · rw [revAt_le hk, coeff_derivative, coeff_reflect, revAt_le (by lia : n - 1 - k + 1 ≤ n)]
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    have hidx : n - (n - 1 - k + 1) = k := by lia
    rw [hidx]
    have : ((n - 1 - k : ℕ) : ℝ) + 1 = (n : ℝ) - k := by
      push_cast [Nat.cast_sub (by assumption : k ≤ n - 1), Nat.cast_sub hn]
      ring
    grind
  · have hRHS : (derivative (reflect n q)).coeff (revAt (n - 1) k) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [revAt_eq_self_of_lt (by lia : n - 1 < k)]
      calc (derivative (reflect n q)).natDegree
          = (reflect n q).natDegree - 1 := (reflect n q).natDegree_derivative
        _ ≤ n - 1 := by
            have := Polynomial.natDegree_reflect_le (N := n) (p := q)
            simp_all
        _ < k := by lia
    rw [hRHS, mul_zero]
    by_cases k = n
    · simp [*]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by lia : q.natDegree < k)]; simp

theorem isPFPolynomial_of_X_mul {f₁ : ℝ[X]} (hp : IsPFPolynomial (X * f₁)) :
    IsPFPolynomial f₁ := by
  by_cases hf1 : f₁ = 0
  · simp_all
  refine IsPFPolynomial.of_realRooted_nonneg ?_ ?_
  · intro k
    have := hp.hasNonnegCoeffs (k + 1)
    simp_all
  · have hXsplit : (X * f₁).Splits := hp.eq_zero_or_splits.resolve_left (by
      simp [mul_eq_zero, X_ne_zero, hf1])
    simp_all

theorem schurSzegoComp_X_mul_right (n : Nat) (hn : 1 ≤ n) (f p₁ : ℝ[X]) :
    schurSzegoComp n f (X * p₁) =
      X * schurSzegoComp (n - 1) (C (n : ℝ)⁻¹ * derivative f) p₁ := by
  rw [schurSzegoComp_comm, schurSzegoComp_X_mul_left n hn p₁ f, schurSzegoComp_comm]

theorem splits_diagonalOperator_pred (n : Nat) (hn : 1 ≤ n) {q : ℝ[X]}
    (hq : q.natDegree ≤ n) (hsplit : q.Splits) :
    (diagonalOperator (fun k ↦ ((n : ℝ) - k) / n) q).Splits := by
  rw [diagonalOperator_pred_eq_reflect_derivative n hn q hq]
  refine (Polynomial.Splits.C (R := ℝ) _).mul ?_
  · have hrq : (reflect n q).Splits :=
      (DegreeDropReversal.splits_reflect_iff hq).mpr hsplit
    have hder : (derivative (reflect n q)).Splits := splits_derivative hrq
    refine DegreeDropReversal.splits_reflect_of_splits hder ?_
    rw [(reflect n q).natDegree_derivative]
    have := Polynomial.natDegree_reflect_le (N := n) (p := q)
    simp_all

theorem splits_schurSzegoComp_X_mul_left {n : Nat} (hn : 1 ≤ n) {f₁ p : ℝ[X]}
    (hinner : (schurSzegoComp (n - 1) f₁ (C (n : ℝ)⁻¹ * derivative p)).Splits) :
    (schurSzegoComp n (X * f₁) p).Splits := by
  rw [schurSzegoComp_X_mul_left n hn f₁ p]
  simp [*]

theorem splits_schurSzegoComp_X_mul_right {n : Nat} (hn : 1 ≤ n) {f p₁ : ℝ[X]}
    (hinner : (schurSzegoComp (n - 1) (C (n : ℝ)⁻¹ * derivative f) p₁).Splits) :
    (schurSzegoComp n f (X * p₁)).Splits := by
  rw [schurSzegoComp_X_mul_right n hn f p₁]
  simp [*]

theorem isPFPolynomial_reflect {n : Nat} {f : ℝ[X]} (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n) : IsPFPolynomial (reflect n f) := by
  rw [DegreeDropReversal.reflect_eq_X_pow_mul_reverse f hfdeg]
  have : IsPFPolynomial f.reverse := hf.reverse
  clear hf hfdeg
  induction (n - f.natDegree) with
  | zero => simp [*]
  | succ m ih =>
    rw [pow_succ, mul_comm (X ^ m) X, mul_assoc]
    exact ih.X_mul

theorem splits_schurSzegoComp_of_isPF (n : Nat) :
    ∀ (f p : ℝ[X]), IsPFPolynomial f → f ≠ 0 → f.natDegree ≤ n →
      p ≠ 0 → p.natDegree ≤ n → p.Splits →
      (schurSzegoComp n f p).Splits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f p hf hf0 hfdeg _ hp hsplit
    by_cases htriv : (schurSzegoComp n f p).natDegree ≤ 1
    · by_cases hz : schurSzegoComp n f p = 0
      · simp [*]
      · exact (isRealRooted_of_natDegree_le_one hz htriv).2
    have hn1 : 1 ≤ n := by
      by_contra h
      push Not at h
      interval_cases n
      · exact htriv ((natDegree_schurSzegoComp_le 0 f p).trans (by simp [*]))
    by_cases hf00 : f.coeff 0 = 0
    · have hfX : f = X * f.divX := DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hf00
      have hf1pf : IsPFPolynomial f.divX := isPFPolynomial_of_X_mul (hfX ▸ hf)
      have hderiv_split : (C (n : ℝ)⁻¹ * derivative p).Splits :=
        (Polynomial.Splits.C (R := ℝ) _).mul (splits_derivative hsplit)
      have hinner : (schurSzegoComp (n - 1) f.divX (C (n : ℝ)⁻¹ * derivative p)).Splits := by
        by_cases hz : schurSzegoComp (n - 1) f.divX (C (n : ℝ)⁻¹ * derivative p) = 0
        · rw [hz]; simp
        refine ih (n - 1) (by lia) f.divX (C (n : ℝ)⁻¹ * derivative p) hf1pf ?_ ?_ ?_ ?_
          hderiv_split
        · grind
        · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]; lia
        · intro h
          apply hz
          rw [schurSzegoComp_comm, schurSzegoComp_eq_diagonalOperator, h]
          simp
        · exact (Polynomial.natDegree_C_mul_le _ _).trans
            (by rw [p.natDegree_derivative]; simp [*])
      have := splits_schurSzegoComp_X_mul_left hn1 (f₁ := f.divX) (p := p) hinner
      grind
    by_cases hp00 : p.coeff 0 = 0
    · have hpX : p = X * p.divX := DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hp00
      have hp1split : p.divX.Splits := (DegreeDropReversal.splits_X_mul_iff).mp (hpX ▸ hsplit)
      have hderiv_pf : IsPFPolynomial (C (n : ℝ)⁻¹ * derivative f) :=
        (hf.derivative).const_mul (by positivity)
      have hderiv_split : (C (n : ℝ)⁻¹ * derivative f).Splits :=
        (Polynomial.Splits.C (R := ℝ) _).mul (splits_derivative
          (hf.eq_zero_or_splits.resolve_left hf0))
      have hinner : (schurSzegoComp (n - 1) (C (n : ℝ)⁻¹ * derivative f) p.divX).Splits := by
        by_cases hz : schurSzegoComp (n - 1) (C (n : ℝ)⁻¹ * derivative f) p.divX = 0
        · rw [hz]; simp
        refine ih (n - 1) (by lia) (C (n : ℝ)⁻¹ * derivative f) p.divX hderiv_pf ?_ ?_ ?_ ?_
          hp1split
        · intro h; rw [h] at hz; simp at hz
        · exact (Polynomial.natDegree_C_mul_le _ _).trans
            (by rw [f.natDegree_derivative]; simp [*])
        · grind
        · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]; lia
      have := splits_schurSzegoComp_X_mul_right hn1 (f := f)
        (p₁ := p.divX) hinner
      grind
    by_cases hlt : f.natDegree < n ∧ p.natDegree < n
    · have hpn : p.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt.2
      rw [schurSzegoComp_eq_diagonalOperator_pred n hn1 f p hpn]
      refine splits_diagonalOperator_pred n hn1 ?_ ?_
      · exact (natDegree_schurSzegoComp_le (n - 1) f p).trans (by simp [*])
      · grind
    push Not at hlt
    have hRf_pf : IsPFPolynomial (reflect n f) := isPFPolynomial_reflect hf hfdeg
    have hRf_deg : (reflect n f).natDegree = n :=
      DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne hfdeg hf00
    have hRf_ne : reflect n f ≠ 0 := by simp [*]
    have hRp_deg : (reflect n p).natDegree = n :=
      DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne hp hp00
    have hRp_ne : reflect n p ≠ 0 := by simp [*]
    have hRp_split : (reflect n p).Splits :=
      DegreeDropReversal.splits_reflect_of_splits hsplit hp
    suffices hcore : (schurSzegoComp n (reflect n f) (reflect n p)).Splits by
      rw [← reflect_schurSzegoComp] at hcore
      exact (DegreeDropReversal.splits_reflect_iff (natDegree_schurSzegoComp_le n f p)).mp hcore
    by_cases hfn : f.natDegree = n
    · have hRf_coeff0 : (reflect n f).coeff 0 ≠ 0 := by
        rw [coeff_reflect, revAt_zero, ← hfn]
        exact Polynomial.leadingCoeff_ne_zero.mpr hf0
      exact core_squeeze hRf_pf hRf_ne hRf_deg hRf_coeff0 hRp_ne hRp_deg hRp_split
    · have hRf_coeff0 : (reflect n f).coeff 0 = 0 := by
        rw [coeff_reflect, revAt_zero]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by lia)
      have hRfX : reflect n f = X * (reflect n f).divX :=
        DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hRf_coeff0
      have hRf1_pf : IsPFPolynomial (reflect n f).divX :=
        isPFPolynomial_of_X_mul (hRfX ▸ hRf_pf)
      have hderiv_split : (C (n : ℝ)⁻¹ * derivative (reflect n p)).Splits :=
        (Polynomial.Splits.C (R := ℝ) _).mul (splits_derivative hRp_split)
      have hinner :
          (schurSzegoComp (n - 1) (reflect n f).divX
            (C (n : ℝ)⁻¹ * derivative (reflect n p))).Splits := by
        by_cases hz : schurSzegoComp (n - 1) (reflect n f).divX
            (C (n : ℝ)⁻¹ * derivative (reflect n p)) = 0
        · rw [hz]; simp
        refine ih (n - 1) (by lia) (reflect n f).divX
          (C (n : ℝ)⁻¹ * derivative (reflect n p)) hRf1_pf ?_ ?_ ?_ ?_ hderiv_split
        · grind
        · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hRf_deg]
        · intro h; rw [h] at hz; simp at hz
        · exact (Polynomial.natDegree_C_mul_le _ _).trans
            (by rw [(reflect n p).natDegree_derivative]; simp [*])
      have := splits_schurSzegoComp_X_mul_left hn1 (f₁ := (reflect n f).divX)
        (p := reflect n p) hinner
      grind

/-- Nonzero finite Schur--Szegő composition theorem.  This is the substantive
classical leaf: `f` is a nonzero PF polynomial, `p` is a nonzero real-rooted
polynomial, both have degree at most `n`, and the fixed-degree Schur--Szegő
composition is either zero or real-rooted. -/
theorem finiteSchurSzegoCompositionNonzero :
    finiteSchurSzegoCompositionNonzeroStatement :=
  fun {n} {f} {p} hf hf0 hfdeg hp0 hp hsplit =>
    Or.inr (splits_schurSzegoComp_of_isPF n f p hf hf0 hfdeg hp0 hp hsplit)

/-- Finite Schur--Szegő composition theorem. The degenerate cases (`f = 0` or
`p = 0`, where the composition vanishes) are discharged by
`finiteSchurSzegoComposition_of_nonzero`; the remaining classical content is
`finiteSchurSzegoCompositionNonzero`. -/
theorem finiteSchurSzegoComposition : finiteSchurSzegoCompositionStatement :=
  finiteSchurSzegoComposition_of_nonzero finiteSchurSzegoCompositionNonzero

/-- Directly applicable form of the finite Schur--Szegő composition theorem:
for a PF polynomial `f` and a real-rooted polynomial `p`, both of degree at most
`n`, the fixed-degree Schur--Szegő composition is either zero or real-rooted. -/
theorem schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hp : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition hf hfdeg hpdeg hp

/-- Fixed-degree Schur--Szegő composition of two PF polynomials is again PF.

This is the zero-aware wrapper around
`schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial`; coefficient
nonnegativity is preserved directly by the composition. -/
theorem IsPFPolynomial.schurSzegoComp
    {n : ℕ} {f p : ℝ[X]} (hf : IsPFPolynomial f)
    (hp : IsPFPolynomial p) (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n) :
    IsPFPolynomial (schurSzegoComp n f p) := by
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    (hf.hasNonnegCoeffs.schurSzegoComp hp.hasNonnegCoeffs)
  by_cases hp0 : p = 0
  · subst p
    simp
  · exact schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial
      hf hfdeg hpdeg (hp.eq_zero_or_splits.resolve_left hp0)

/-- The backward direction of the finite Pólya--Schur theorem, obtained from the
finite Schur--Szegő composition theorem. -/
theorem finitePolyaSchurNonnegBackward : finitePolyaSchurNonnegBackwardStatement :=
  finitePolyaSchurNonnegBackward_of_schurSzegoNonzero finiteSchurSzegoCompositionNonzero

/-- Classical finite Pólya--Schur theorem (nonnegative-coefficient convention).
The only remaining analytic obligation is isolated in
`finiteSchurSzegoComposition`. -/
theorem finitePolyaSchur_nonneg : finitePolyaSchurNonnegStatement :=
  finitePolyaSchur_nonneg_of_schurSzegoNonzero finiteSchurSzegoCompositionNonzero

/-- Nonnegative coefficients are preserved by coefficientwise Hadamard
products. -/
theorem HasNonnegCoeffs.hadamardProduct {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (hadamardProduct p q) :=
  (hadamardProduct_eq_diagonalOperator p q).symm ▸ hp.diagonalOperator hq

/-- **Odd/even Hadamard identity.**  The coefficientwise Hadamard product
commutes with the odd/even construction `oddEvenPolynomial p q = q(x²) + x·p(x²)`:
the even coefficients multiply the `q`-parts and the odd coefficients multiply
the `p`-parts. This is the algebraic bridge that reduces the two-pair
Garloff--Wagner interlacing theorem to the single-polynomial Hurwitz-stability
fact through the Hermite--Biehler odd/even correspondence. -/
theorem hadamardProduct_oddEvenPolynomial (p q p' q' : ℝ[X]) :
    hadamardProduct (oddEvenPolynomial p q) (oddEvenPolynomial p' q') =
      oddEvenPolynomial (hadamardProduct p p') (hadamardProduct q q') := by
  ext n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show k + k = 2 * k by ring]
    simp
  · subst hk
    simp

/-- Nonnegative-coefficient Schur--Polya/Garloff--Wagner real-rootedness
interface for coefficientwise Hadamard products.

Garloff--Wagner, Theorem 4(a), proves this in the standard-polynomial setting
with only nonpositive zeros. The hypotheses below are the corresponding
nonnegative-coefficient wrapper: real-rooted nonzero polynomials with
nonnegative coefficients automatically have only nonpositive roots. The conclusion is
zero-aware because the Hadamard product can vanish when supports are disjoint.
-/
def garloffWagnerHadamardNonnegRealRootedStatement : Prop :=
  ∀ {p q : ℝ[X]},
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    (p ≠ 0 ∧ p.Splits) →
    (q ≠ 0 ∧ q.Splits) →
    (hadamardProduct p q = 0 ∨ (hadamardProduct p q).Splits) ∧
      HasNonnegCoeffs (hadamardProduct p q) ∧
      ∀ r ∈ (hadamardProduct p q).roots, r ≤ 0

theorem IsPFPolynomial.hadamardProduct
    (hGW : garloffWagnerHadamardNonnegRealRootedStatement)
    {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) := by
  by_cases hp0 : p = 0
  · subst p
    simpa using IsPFPolynomial.zero
  by_cases hq0 : q = 0
  · subst q
    simpa using IsPFPolynomial.zero
  rcases hGW hp.hasNonnegCoeffs hq.hasNonnegCoeffs
      (hp.ne_zero_and_splits hp0)
      (hq.ne_zero_and_splits hq0) with ⟨hrr, hnn, hroots⟩
  exact ⟨hnn, hrr, hroots⟩

/-- Polynomial PF form of the Schur--Polya--Wagner Hadamard theorem. -/
def schurPolyaWagnerHadamardPFStatement : Prop :=
  ∀ {p q : ℝ[X]},
    IsPFPolynomial p →
    IsPFPolynomial q →
    IsPFPolynomial (hadamardProduct p q)

theorem schurPolyaWagnerHadamardPF_of_garloffWagner_nonneg
    (hGW : garloffWagnerHadamardNonnegRealRootedStatement) :
    schurPolyaWagnerHadamardPFStatement :=
  fun hp hq => hp.hadamardProduct hGW hq

/- Nonnegative-coefficient Garloff--Wagner interlacing interface for
coefficientwise Hadamard products.

This is the `Prec`/`Prec0` wrapper around Garloff--Wagner, Theorem 4(b):
if two nonnegative-coefficient real-rooted pairs are in the same
proper-position relation, then the pair of Hadamard products is again in
proper position.  The conclusion is zero-aware for the same support reason as
`garloffWagnerHadamardNonnegRealRootedStatement`.

Orientation audit: in this repository `Prec f g` is the convention `f ≪ g`.
In the differ-by-one case, `g` has the rightmost root; in the same-degree case,
each root of `f` is weakly to the left of the corresponding root of `g`.  Thus
for linear factors we have `Prec (X + C b) (X + C a) ↔ a ≤ b`, because their
roots are `-b` and `-a`.  Consequently the Garloff--Wagner hypotheses written
as `g $ f` and `q $ p` are represented here as `Prec f g` and `Prec p q`, and
the conclusion is `Prec0 (f ⊙ p) (g ⊙ q)`.

This statement is proved directly in `RealRooted.GarloffWagner`; the wrapper
keeps the historical `Hadamard` API used by downstream theorem bundles.
-/
/-- Hadamard product preserves proper position in the nonnegative setting
(Garloff--Wagner, Theorem 4(b)). -/
theorem garloffWagnerHadamardNonnegPrec {f g p q : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hfg : Prec f g) (hpq : Prec p q) :
    Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  exact gwHadamardProductNonnegPrec hf hg hp hq hfg hpq


/-- Linear-factor sanity check for the orientation used in
`garloffWagnerHadamardNonnegPrec`. -/
theorem garloffWagnerHadamard_linear_orientation_sanity {a b : ℝ} :
    Prec (X + C b) (X + C a) ↔ a ≤ b :=
  prec_X_add_C_iff

/-- **Hadamard product preserves Hurwitz stability** (Garloff--Wagner,
Theorem 1) — precise external interface.

This is the main theorem of Garloff--Wagner, *Hadamard Products of Stable
Polynomials Are Stable*: the coefficientwise Hadamard product of two
Hurwitz-stable real polynomials is again Hurwitz stable, provided the
coefficientwise product is nonzero.  The nonzero side condition is part of the
interface because this project's `IsHurwitzStable` convention excludes the zero
polynomial, while coefficientwise products of two nonzero stable polynomials can
vanish when their coefficient supports are disjoint.  This is the genuinely
deep classical input (its classical proofs go through Polya--Schur /
total-nonnegativity machinery that is not available in Mathlib), recorded here
as a precise interface. This is the only new external interface needed below;
the remaining inputs are the Hermite--Biehler odd/even bridges already recorded
in `RealRooted.VeroneseSection`. -/
def hadamardPreservesHurwitzStableStatement : Prop :=
  ∀ {a b : ℝ[X]},
    IsHurwitzStable a →
    IsHurwitzStable b →
    hadamardProduct a b ≠ 0 →
    IsHurwitzStable (hadamardProduct a b)

/-! ### Sharper sub-interfaces for Garloff--Wagner Theorem 1

The Hurwitz-stability conclusion `IsHurwitzStable (hadamardProduct a b)` unfolds
to two parts: nonnegativity of the coefficients and right-half-plane stability
of the complexification.  The first part is elementary
(`HasNonnegCoeffs.hadamardProduct`); the genuinely deep content is the second
part.  We record that split, and the faithful Hurwitz-matrix decomposition of
Garloff--Wagner Theorem 1, as fully checked reductions. -/

/-- The deep half of Garloff--Wagner Theorem 1: the complexified coefficientwise
Hadamard product of two right-half-plane-stable, nonnegative-coefficient
polynomials is again right-half-plane stable when the product is nonzero. -/
def hadamardPreservesRightHalfPlaneStableStatement : Prop :=
  ∀ {a b : ℝ[X]},
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    IsRightHalfPlaneStable (complexify a) →
    IsRightHalfPlaneStable (complexify b) →
    hadamardProduct a b ≠ 0 →
    IsRightHalfPlaneStable (complexify (hadamardProduct a b))

/-- Reduction of Garloff--Wagner Theorem 1 to its deep half: the
nonnegative-coefficient half of Hurwitz stability is discharged here, so only
right-half-plane stability of the product remains. -/
theorem hadamardPreservesHurwitzStable_of_rightHalfPlane
    (h : hadamardPreservesRightHalfPlaneStableStatement) :
    hadamardPreservesHurwitzStableStatement :=
  fun ha hb hprod => ⟨ha.1.hadamardProduct hb.1, h ha.1 hb.1 ha.2 hb.2 hprod⟩

/-- The analytic core is conversely implied by Garloff--Wagner Theorem 1, so the
two interfaces are equivalent: isolating the right-half-plane half loses no
content. -/
theorem hadamardPreservesRightHalfPlaneStable_of_hurwitzStable
    (h : hadamardPreservesHurwitzStableStatement) :
    hadamardPreservesRightHalfPlaneStableStatement :=
  fun hann hbnn harhp hbrhp hprod => (h ⟨hann, harhp⟩ ⟨hbnn, hbrhp⟩ hprod).2

/-- Garloff--Wagner Theorem 1 is equivalent to its right-half-plane analytic
core; coefficient nonnegativity of the product is elementary. -/
theorem hadamardPreservesHurwitzStable_iff_rightHalfPlane :
    hadamardPreservesHurwitzStableStatement ↔
      hadamardPreservesRightHalfPlaneStableStatement :=
  ⟨hadamardPreservesRightHalfPlaneStable_of_hurwitzStable,
    hadamardPreservesHurwitzStable_of_rightHalfPlane⟩

/-- The combinatorial heart of Garloff--Wagner Theorem 1, as a pure matrix
statement: total nonnegativity of the row-oriented Hurwitz matrix is preserved
under coefficientwise products. -/
def hadamardPreservesHurwitzMatrixTNStatement : Prop :=
  ∀ {a b : ℝ[X]},
    (hurwitz a.coeff).IsTotallyNonneg →
    (hurwitz b.coeff).IsTotallyNonneg →
    (hurwitz (hadamardProduct a b).coeff).IsTotallyNonneg

/-- Hurwitz-matrix form of the coefficientwise Hadamard product of two
polynomials. -/
theorem hurwitz_hadamardProduct_matrix (a b : ℝ[X]) :
    hurwitz (hadamardProduct a b).coeff =
      Matrix.of fun i j => hurwitz a.coeff i j * hurwitz b.coeff i j := by
  rw [show (hadamardProduct a b).coeff = fun n => a.coeff n * b.coeff n by
    funext n
    exact coeff_hadamardProduct a b n]
  exact hurwitz_mul_entrywise_matrix a.coeff b.coeff

/-- Low-order checked part of the Hurwitz-matrix Hadamard leaf: every minor of
size at most two is nonnegative.  The first remaining case for
`hadamardPreservesHurwitzMatrixTNStatement` is the `3 × 3` Hurwitz-specific
minor. -/
theorem hadamardPreservesHurwitzMatrixTN_det_of_card_le_two
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg)
    {n : ℕ} {rows cols : Fin n → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hn : n ≤ 2) :
    0 ≤ (((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det) := by
  simpa [hurwitz_hadamardProduct_matrix] using
    hurwitz_schurProduct_det_of_card_le_two ha hb hrows hcols hn

/-- Structural `3 × 3` band-fail case for the Hurwitz matrix of a Hadamard
product.  This is the polynomial-facing form of
`hurwitz_schurProduct_det_fin_three_of_band_fail`. -/
theorem hurwitz_hadamardProduct_det_fin_three_of_band_fail
    {a b : ℝ[X]} {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows)
    (hcols : StrictMono cols) (l : Fin 3) (hl : rows l < 2 * cols l) :
    ((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det = 0 := by
  simpa [hurwitz_hadamardProduct_matrix] using
    hurwitz_schurProduct_det_fin_three_of_band_fail hrows hcols l hl

/-- Nonnegativity form of the structural `3 × 3` band-fail case for the
Hurwitz matrix of a Hadamard product. -/
theorem hurwitz_hadamardProduct_det_fin_three_nonneg_of_band_fail
    {a b : ℝ[X]} {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows)
    (hcols : StrictMono cols) (l : Fin 3) (hl : rows l < 2 * cols l) :
    0 ≤ ((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det := by
  rw [hurwitz_hadamardProduct_det_fin_three_of_band_fail hrows hcols l hl]

/-- `3 × 3` Hurwitz-matrix Hadamard minors from the pure in-band `3 × 3`
matrix core.  The out-of-band case is handled structurally by the
band-fail zero lemma. -/
theorem hadamardPreservesHurwitzMatrixTN_det_fin_three
    (hInBand : HurwitzMatrixSchurProductDetFinThreeInBandStatement)
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg)
    {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 ≤ ((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det := by
  simpa [hurwitz_hadamardProduct_matrix] using
    hurwitz_schurProduct_det_fin_three hInBand ha hb hrows hcols

/-- Low-order checked part of the Hurwitz-matrix Hadamard leaf through size
three, assuming the pure in-band `3 × 3` matrix core. -/
theorem hadamardPreservesHurwitzMatrixTN_det_of_card_le_three
    (hInBand : HurwitzMatrixSchurProductDetFinThreeInBandStatement)
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg)
    {n : ℕ} {rows cols : Fin n → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hn : n ≤ 3) :
    0 ≤ (((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det) := by
  simpa [hurwitz_hadamardProduct_matrix] using
    hurwitz_schurProduct_det_of_card_le_three hInBand ha hb hrows hcols hn

/-- Low-order, size-`≤ 3`, form of the Hurwitz-matrix Hadamard leaf. -/
def hadamardPreservesHurwitzMatrixTNDetLeThreeStatement : Prop :=
  ∀ {a b : ℝ[X]},
    (hurwitz a.coeff).IsTotallyNonneg →
    (hurwitz b.coeff).IsTotallyNonneg →
    ∀ {n : ℕ} {rows cols : Fin n → ℕ},
      StrictMono rows →
      StrictMono cols →
      n ≤ 3 →
      0 ≤ (((hurwitz (hadamardProduct a b).coeff).submatrix rows cols).det)

/-- The isolated in-band `3 × 3` core implies the low-order, size-`≤ 3`,
Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand
    (hInBand : HurwitzMatrixSchurProductDetFinThreeInBandStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  @hadamardPreservesHurwitzMatrixTN_det_of_card_le_three hInBand

/-- The fully in-band top-right subcase of the `3 × 3` Hurwitz Schur-product
core implies the low-order, size-`≤ 3`, Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_fullBand
    (hF : HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand
    (hurwitzMatrixSchurProductDetFinThreeInBand_of_fullBand hF)

/-- The single-matrix corner-zeroed determinant subtarget implies the
low-order, size-`≤ 3`, Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingle
    (hSingle :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand
    (hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingle hSingle)

/-- The column-normalized single-matrix corner-zeroed determinant subtarget
implies the low-order, size-`≤ 3`, Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleColZero
    (hZero :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingle
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle_of_colZero hZero)

/-- The first-column normal form implies the low-order, size-`≤ 3`,
Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleFirstCol
    (hFirst :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleColZero
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_firstCol
      hFirst)

/-- The strict-remainder first-column branch implies the low-order,
size-`≤ 3`, Hurwitz-matrix Hadamard leaf. -/
theorem
    hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleFirstColPositiveRemainder
    (hPos : HurwitzMatrixSchurProductDetFirstColPositiveRemainderStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleFirstCol
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_positiveRemainder
      hPos)

/-- The pure size-`≤ 3` Hurwitz matrix Schur-product statement implies the
Hadamard-product Hurwitz-matrix size-`≤ 3` statement. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_hurwitzLeThree
    (hLeThree : HurwitzMatrixSchurProductDetLeThreeStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  fun {_a _b} ha hb {_n} {_rows} {_cols} hrows hcols hn => by
    simpa [hurwitz_hadamardProduct_matrix] using hLeThree ha hb hrows hcols hn

/-- The full Hurwitz-matrix Hadamard leaf implies its named low-order,
size-`≤ 3`, consequence. -/
theorem hadamardPreservesHurwitzMatrixTNDetLeThree_of_matrixTN
    (h : hadamardPreservesHurwitzMatrixTNStatement) :
    hadamardPreservesHurwitzMatrixTNDetLeThreeStatement :=
  fun {_a _b} ha hb {_n} {_rows} {_cols} hrows hcols _hn => h ha hb hrows hcols

/-- Odd/even coefficient-subsequence PF consequence of the Hurwitz-matrix
Hadamard leaf. -/
def hadamardPreservesHurwitzMatrixOddEvenPFStatement : Prop :=
  ∀ {a b : ℝ[X]},
    (hurwitz a.coeff).IsTotallyNonneg →
    (hurwitz b.coeff).IsTotallyNonneg →
    IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n + 1)) ∧
      IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n))

/-- The Hurwitz-matrix Hadamard leaf makes the odd coefficient subsequence of
the Hadamard product Pólya-frequency. -/
theorem hadamardProduct_oddCoeff_isPolyaFreqSeq_of_matrixTN
    (h : hadamardPreservesHurwitzMatrixTNStatement)
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg) :
    IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n + 1)) :=
  hurwitz_isPolyaFreqSeq_odd (h ha hb)

/-- The Hurwitz-matrix Hadamard leaf makes the even coefficient subsequence of
the Hadamard product Pólya-frequency. -/
theorem hadamardProduct_evenCoeff_isPolyaFreqSeq_of_matrixTN
    (h : hadamardPreservesHurwitzMatrixTNStatement)
    {a b : ℝ[X]} (ha : (hurwitz a.coeff).IsTotallyNonneg)
    (hb : (hurwitz b.coeff).IsTotallyNonneg) :
    IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n)) :=
  hurwitz_isPolyaFreqSeq_even (h ha hb)

/-- Bundled odd/even PF consequence of the Hurwitz-matrix Hadamard leaf. -/
theorem hadamardPreservesHurwitzMatrixOddEvenPF_of_matrixTN
    (h : hadamardPreservesHurwitzMatrixTNStatement) :
    hadamardPreservesHurwitzMatrixOddEvenPFStatement :=
  fun ha hb =>
    ⟨hurwitz_isPolyaFreqSeq_odd (h ha hb),
      hurwitz_isPolyaFreqSeq_even (h ha hb)⟩

/-- **Garloff--Wagner, Theorem 4(b), reduced to legacy odd/even inputs**
(TODO T9).

The two-pair interlacing form of the Garloff--Wagner Hadamard theorem follows,
with a fully checked conditional reduction, from the following inputs (the
latter three are pre-existing interfaces from `RealRooted.VeroneseSection`):

* `hadamardPreservesHurwitzStableStatement` — Garloff--Wagner Theorem 1
  (Hadamard products of Hurwitz-stable polynomials are Hurwitz stable when the
  coefficientwise product is nonzero);
* `NonnegPrecToHurwitzOddEvenStatement` — the forward Hermite--Biehler bridge
  from proper position `Prec f g` of nonnegative-coefficient polynomials to
  Hurwitz stability of `oddEvenPolynomial f g = g(x²) + x·f(x²)`;
* `LegacyHurwitzOddEvenToFullyInterlacingPairStatement` — the legacy row-oriented
  Hurwitz-to-Lace bridge, now known false as a general theorem; and
* `FullyInterlacingPairToPrec0Statement` — the converse lace-to-interlacing
  bridge back to zero-aware proper position.

The bridge between the two-pair and single-polynomial worlds is the proven
algebraic identity `hadamardProduct_oddEvenPolynomial`:
`oddEvenPolynomial f g ⊙ oddEvenPolynomial p q
   = oddEvenPolynomial (f ⊙ p) (g ⊙ q)`,
whose even part is `g ⊙ q` and whose odd part is `f ⊙ p`.

Thus all of the interlacing bookkeeping of Theorem 4(b) is discharged here once
these conditional inputs are supplied.
Note that the odd/even polynomial of an interlacing pair is Hurwitz stable, not
real-rooted (e.g. `f = 1`, `g = X + 1` gives `X² + X + 1`), which is why the
reduction goes through `IsHurwitzStable` (Theorem 1) rather than the
single-polynomial real-rootedness fact
`garloffWagnerHadamardNonnegRealRootedStatement`. -/
theorem garloffWagnerHadamardNonnegPrec_of_oddEven
    (hThm1 : hadamardPreservesHurwitzStableStatement)
    (hPrecToHurwitz : NonnegPrecToHurwitzOddEvenStatement)
    (hHurwitzToFull : LegacyHurwitzOddEvenToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    ∀ {f g p q : ℝ[X]},
      HasNonnegCoeffs f → HasNonnegCoeffs g → HasNonnegCoeffs p → HasNonnegCoeffs q →
      Prec f g → Prec p q → Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  intro f g p q hf hg hp hq hfg hpq
  by_cases hfp0 : hadamardProduct f p = 0
  · simpa [hfp0] using prec0_zero_left (hadamardProduct g q)
  by_cases hgq0 : hadamardProduct g q = 0
  · simpa [hgq0] using prec0_zero_right (hadamardProduct f p)
  have hOE1 : IsHurwitzStable (oddEvenPolynomial f g) := hPrecToHurwitz hf hg hfg
  have hOE2 : IsHurwitzStable (oddEvenPolynomial p q) := hPrecToHurwitz hp hq hpq
  have hOEprod0 :
      hadamardProduct (oddEvenPolynomial f g) (oddEvenPolynomial p q) ≠ 0 := by
    rw [hadamardProduct_oddEvenPolynomial]
    exact oddEvenPolynomial_ne_zero_iff.mpr (Or.inl hfp0)
  exact hFullToPrec0 (hHurwitzToFull (by
    simpa [hadamardProduct_oddEvenPolynomial] using hThm1 hOE1 hOE2 hOEprod0))

/-- PF-polynomial wrapper around the checked nonnegative
Garloff--Wagner two-pair theorem. -/
def garloffWagnerHadamardPFPrecStatement : Prop :=
  ∀ {f g p q : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial g →
    IsPFPolynomial p →
    IsPFPolynomial q →
    Prec f g →
    Prec p q →
    Prec0 (hadamardProduct f p) (hadamardProduct g q)

theorem garloffWagnerHadamardPFPrec_of_nonnegPrec :
    garloffWagnerHadamardPFPrecStatement :=
  fun hf hg hp hq hfg hpq =>
    garloffWagnerHadamardNonnegPrec hf.hasNonnegCoeffs hg.hasNonnegCoeffs
      hp.hasNonnegCoeffs hq.hasNonnegCoeffs hfg hpq

/-- Zero-aware PF-polynomial wrapper around the checked Garloff--Wagner
two-pair theorem. -/
def garloffWagnerHadamardPFPrec0Statement : Prop :=
  ∀ {f g p q : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial g →
    IsPFPolynomial p →
    IsPFPolynomial q →
    Prec0 f g →
    Prec0 p q →
    Prec0 (hadamardProduct f p) (hadamardProduct g q)

theorem garloffWagnerHadamardPFPrec0_of_prec
    (hGW : garloffWagnerHadamardPFPrecStatement) :
    garloffWagnerHadamardPFPrec0Statement := by
  intro f g p q hf hg hp hq hfg hpq
  rcases hfg with rfl | rfl | hfg'
  · simpa using prec0_zero_left (hadamardProduct g q)
  · simpa using prec0_zero_right (hadamardProduct f p)
  rcases hpq with rfl | rfl | hpq'
  · simpa using prec0_zero_left (hadamardProduct g q)
  · simpa using prec0_zero_right (hadamardProduct f p)
  exact hGW hf hg hp hq hfg' hpq'

theorem garloffWagnerHadamardPFPrec0_of_nonnegPrec :
    garloffWagnerHadamardPFPrec0Statement :=
  garloffWagnerHadamardPFPrec0_of_prec
    garloffWagnerHadamardPFPrec_of_nonnegPrec

/-- PF-polynomial closure under Hadamard product, stated directly from the
zero-aware Garloff--Wagner PF wrapper. -/
theorem hadamardProduct_preserves_pf_of_garloffWagner
    (hGW : garloffWagnerHadamardPFPrec0Statement)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  IsPFPolynomial.of_prec0_self
    (hp.hasNonnegCoeffs.hadamardProduct hq.hasNonnegCoeffs)
    (hGW hp hp hq hq hp.prec0_self hq.prec0_self)

theorem hadamardProduct_preserves_pf_of_nonnegPrec :
    {p q : ℝ[X]} → IsPFPolynomial p → IsPFPolynomial q →
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_garloffWagner
    garloffWagnerHadamardPFPrec0_of_nonnegPrec

theorem hadamardProduct_preserves_pf_of_matrixHadamardBridges
    (_hToFull : LegacyNonnegPrecToFullyInterlacingPairStatement)
    (_hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (_hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    {p q : ℝ[X]} → IsPFPolynomial p → IsPFPolynomial q →
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_nonnegPrec

theorem hadamardProduct_preserves_pf_of_hurwitzSchur
    (_hToFull : LegacyNonnegPrecToFullyInterlacingPairStatement)
    (_hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    {p q : ℝ[X]} → IsPFPolynomial p → IsPFPolynomial q →
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_nonnegPrec

/-- The nonnegative two-pair Garloff--Wagner theorem gives PF closure under
Hadamard products through the zero-aware PF wrapper. -/
theorem schurPolyaWagnerHadamardPF_of_garloffWagner_nonnegPrec :
    schurPolyaWagnerHadamardPFStatement :=
  hadamardProduct_preserves_pf_of_nonnegPrec

/-- The checked PF Hadamard theorem gives the one-polynomial
real-rootedness statement directly. -/
theorem garloffWagnerHadamardNonnegRealRooted_of_nonnegPrec :
    garloffWagnerHadamardNonnegRealRootedStatement := by
  intro p q hpnn hqnn hprr hqrr
  have hp : IsPFPolynomial p := IsPFPolynomial.of_realRooted_nonneg hpnn hprr.2
  have hq : IsPFPolynomial q := IsPFPolynomial.of_realRooted_nonneg hqnn hqrr.2
  have hpf : IsPFPolynomial (hadamardProduct p q) :=
    hadamardProduct_preserves_pf_of_nonnegPrec hp hq
  exact ⟨hpf.eq_zero_or_splits, hpf.hasNonnegCoeffs, hpf.roots_nonpos⟩

/-- Fixed-right Hadamard multiplication preserves zero-aware proper position
inside the PF cone. -/
theorem hadamardProduct_preserves_prec0_right
    (hGW : garloffWagnerHadamardPFPrec0Statement)
    {f g p : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hp : IsPFPolynomial p)
    (hfg : Prec0 f g) :
    Prec0 (hadamardProduct f p) (hadamardProduct g p) :=
  hGW hf hg hp hp hfg hp.prec0_self

/-- Fixed-left Hadamard multiplication preserves zero-aware proper position
inside the PF cone. -/
theorem hadamardProduct_preserves_prec0_left
    (hGW : garloffWagnerHadamardPFPrec0Statement)
    {f p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (hadamardProduct f p) (hadamardProduct f q) := by
  simpa [hadamardProduct_comm] using
    hadamardProduct_preserves_prec0_right hGW hp hq hf hpq

theorem reciprocalShift_hadamardProduct (D : ℕ) (p q : ℝ[X]) :
    reciprocalShift D (hadamardProduct p q) =
      hadamardProduct (reciprocalShift D p) (reciprocalShift D q) := by
  ext n
  simp

/-- Hadamard closure for the reciprocal-interlacing cone. -/
def hadamardReciprocalConeClosureStatement : Prop :=
  ∀ {D : ℕ} {p q : ℝ[X]},
    IsPFPolynomial p →
    IsPFPolynomial q →
    Prec p (reciprocalShift D p) →
    Prec q (reciprocalShift D q) →
    Prec0 (hadamardProduct p q)
      (reciprocalShift D (hadamardProduct p q))

/-- Hadamard closure for the reciprocal-interlacing cone, obtained from the
zero-aware PF two-pair Garloff--Wagner wrapper. -/
theorem hadamardReciprocalConeClosure_of_garloffWagner_prec0
    (hGW : garloffWagnerHadamardPFPrec0Statement) :
    hadamardReciprocalConeClosureStatement := by
  intro D p q hp hq hprec_p hprec_q
  have hp_shift : IsPFPolynomial (reciprocalShift D p) :=
    IsPFPolynomial.of_realRooted_nonneg hp.hasNonnegCoeffs.reciprocalShift hprec_p.2.1.2
  have hq_shift : IsPFPolynomial (reciprocalShift D q) :=
    IsPFPolynomial.of_realRooted_nonneg hq.hasNonnegCoeffs.reciprocalShift hprec_q.2.1.2
  simpa [reciprocalShift_hadamardProduct] using
    hGW hp hp_shift hq hq_shift hprec_p.toPrec0 hprec_q.toPrec0

theorem hadamardReciprocalConeClosure_of_garloffWagner_prec
    (hGW : garloffWagnerHadamardPFPrecStatement) :
    hadamardReciprocalConeClosureStatement :=
  hadamardReciprocalConeClosure_of_garloffWagner_prec0
    (garloffWagnerHadamardPFPrec0_of_prec hGW)

/-- Polynomial-coefficient form of Polya-frequency closure under termwise
products. This is finite-sequence closure packaged through coefficient
polynomials. -/
def polyaFrequencyHadamardCoeffStatement : Prop :=
  ∀ {p q : ℝ[X]},
    IsPolyaFreqSeq p.coeff →
    IsPolyaFreqSeq q.coeff →
    IsPolyaFreqSeq (fun n => (hadamardProduct p q).coeff n)

theorem polyaFrequencyHadamardCoeff_of_schurPolyaWagner
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hSPW : schurPolyaWagnerHadamardPFStatement) :
    polyaFrequencyHadamardCoeffStatement :=
  fun hp hq =>
    (hSPW (IsPFPolynomial.of_sequence hASW hp)
      (IsPFPolynomial.of_sequence hASW hq)).to_sequence

end RealRooted
