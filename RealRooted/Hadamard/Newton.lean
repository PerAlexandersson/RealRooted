import RealRooted.Hadamard.Finite

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Normalized coefficient inequalities

Newton inequalities, level-lifting, normalized log-concavity, and the
degree-two PF Schur--Szego base case.
-/

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
end RealRooted
