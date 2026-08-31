import RealRooted.MultiplierSequence.Bidiagonal.Jensen

/-!
# Low-degree bidiagonal Jensen preservers

This module proves the degree-one and degree-two finite Jensen-pencil
preserver criteria. The general contraction backend remains separate.
-/

open Polynomial

noncomputable section

namespace RealRooted

private theorem bidiagonalOperator_discrim_eq_sq_mul_jensenPencil_one
    {alpha beta : ℕ → ℝ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ 1)
    (hp1 : p.coeff 1 ≠ 0) :
    discrim
        ((bidiagonalOperator alpha beta p).coeff 2)
        ((bidiagonalOperator alpha beta p).coeff 1)
        ((bidiagonalOperator alpha beta p).coeff 0) =
      p.coeff 1 ^ 2 * discrim
        ((bidiagonalJensenPencil alpha beta 1
          (p.coeff 0 / p.coeff 1)).coeff 2)
        ((bidiagonalJensenPencil alpha beta 1
          (p.coeff 0 / p.coeff 1)).coeff 1)
        ((bidiagonalJensenPencil alpha beta 1
          (p.coeff 0 / p.coeff 1)).coeff 0) := by
  have hp2 : p.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg (by norm_num))
  have hpencil0 :
      (bidiagonalJensenPencil alpha beta 1
        (p.coeff 0 / p.coeff 1)).coeff 0 = alpha 0 := by
    simp [bidiagonalJensenPencil, mul_assoc, coeff_jensenPolynomial]
  have hpencil1 :
      (bidiagonalJensenPencil alpha beta 1
        (p.coeff 0 / p.coeff 1)).coeff 1 =
          alpha 1 + (p.coeff 0 / p.coeff 1) * beta 0 := by
    simp [bidiagonalJensenPencil, mul_assoc, coeff_jensenPolynomial]
  have hpencil2 :
      (bidiagonalJensenPencil alpha beta 1
        (p.coeff 0 / p.coeff 1)).coeff 2 =
          (p.coeff 0 / p.coeff 1) * beta 1 := by
    simp [bidiagonalJensenPencil, mul_assoc, coeff_jensenPolynomial]
  rw [hpencil0, hpencil1, hpencil2]
  simp only [coeff_bidiagonalOperator_succ, Nat.reduceAdd, hp2, mul_zero,
    zero_add, coeff_bidiagonalOperator_zero]
  unfold discrim
  field_simp [hp1]

/-- The one-sided Jensen-pencil certificate is sufficient in degrees at most
one. -/
theorem jensenPencilBidiagonalPreserver_of_degree_le_one
    {alpha beta : ℕ → ℝ} {d : ℕ} (hd : d ≤ 1)
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d := by
  intro p hp hdeg
  have halpha : ∀ k, k ≤ d → 0 ≤ alpha k :=
    fun k hk ↦ hcert.alpha_nonneg_of_le hk
  have hbeta : ∀ k, k ≤ d → 0 ≤ beta k :=
    fun k hk ↦ hcert.beta_nonneg_of_le hk
  have hout_nonneg : HasNonnegCoeffs (bidiagonalOperator alpha beta p) :=
    hp.hasNonnegCoeffs.bidiagonalOperator_of_degree_le hdeg halpha hbeta
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hout_nonneg
  by_cases hout_zero : bidiagonalOperator alpha beta p = 0
  · exact Or.inl hout_zero
  right
  by_cases hd0 : d = 0
  · have hpdeg0 : p.natDegree = 0 := by lia
    exact (isRealRooted_of_natDegree_le_one hout_zero
      ((natDegree_bidiagonalOperator_le alpha beta p).trans (by lia))).2
  have hd1 : d = 1 := by lia
  subst d
  have hpdeg : p.natDegree ≤ 1 := hdeg
  by_cases hp1 : p.coeff 1 = 0
  · have hpdeg0 : p.natDegree ≤ 0 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro n hn
      by_cases hn1 : n = 1
      · simpa [hn1] using hp1
      · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg (by lia))
    exact (isRealRooted_of_natDegree_le_one hout_zero
      ((natDegree_bidiagonalOperator_le alpha beta p).trans (by lia))).2
  · have hp1_pos : 0 < p.coeff 1 :=
      lt_of_le_of_ne (hp.hasNonnegCoeffs 1) (Ne.symm hp1)
    let lam : ℝ := p.coeff 0 / p.coeff 1
    have hlam : 0 ≤ lam := div_nonneg (hp.hasNonnegCoeffs 0) hp1_pos.le
    have hpencil := hcert.2.2 lam hlam
    have hpencil_disc :
        4 * ((bidiagonalJensenPencil alpha beta 1 lam).coeff 0 *
          (bidiagonalJensenPencil alpha beta 1 lam).coeff 2) ≤
            (bidiagonalJensenPencil alpha beta 1 lam).coeff 1 ^ 2 := by
      rcases hpencil.eq_zero_or_splits with hpencil_zero | hpencil_splits
      · simp [hpencil_zero]
      · exact quadratic_disc_coeff_le_of_splits_natDegree_le_two
          (natDegree_bidiagonalJensenPencil_le alpha beta 1 lam) hpencil_splits
    have hpencil_discrim : 0 ≤ discrim
        ((bidiagonalJensenPencil alpha beta 1 lam).coeff 2)
        ((bidiagonalJensenPencil alpha beta 1 lam).coeff 1)
        ((bidiagonalJensenPencil alpha beta 1 lam).coeff 0) := by
      unfold discrim
      linarith
    have hout_discrim : 0 ≤ discrim
        ((bidiagonalOperator alpha beta p).coeff 2)
        ((bidiagonalOperator alpha beta p).coeff 1)
        ((bidiagonalOperator alpha beta p).coeff 0) := by
      rw [bidiagonalOperator_discrim_eq_sq_mul_jensenPencil_one hpdeg hp1]
      exact mul_nonneg (sq_nonneg _) hpencil_discrim
    have hout_deg : (bidiagonalOperator alpha beta p).natDegree ≤ 2 :=
      (natDegree_bidiagonalOperator_le alpha beta p).trans (by lia)
    rw [Polynomial.eq_quadratic_of_degree_le_two
      (Polynomial.degree_le_of_natDegree_le hout_deg)]
    exact quadraticPoly_splits_of_discrim_nonneg_or_linear hout_discrim

/-- If the last subdiagonal coefficient vanishes, the bidiagonal operator does
not raise the input degree. -/
private theorem natDegree_bidiagonalOperator_le_of_beta_eq_zero
    {alpha beta : ℕ → ℝ} {p : ℝ[X]} {d : ℕ}
    (hpdeg : p.natDegree ≤ d) (hbeta : beta d = 0) :
    (bidiagonalOperator alpha beta p).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  cases n with
  | zero => lia
  | succ k =>
      rw [coeff_bidiagonalOperator_succ]
      have hp_succ : p.coeff (k + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg hn)
      by_cases hk : k = d
      · subst k
        simp [hp_succ, hbeta]
      · have hdk : d < k := by lia
        have hp_k : p.coeff k = 0 :=
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg hdk)
        simp [hp_succ, hp_k]

/-- If the last subdiagonal coefficient vanishes, the Jensen pencil stays
within the certified degree. -/
private theorem natDegree_bidiagonalJensenPencil_le_of_beta_eq_zero
    {alpha beta : ℕ → ℝ} {d : ℕ} {lam : ℝ}
    (hbeta : beta d = 0) :
    (bidiagonalJensenPencil alpha beta d lam).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have halpha : (jensenPolynomial d alpha).coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_jensenPolynomial_le d alpha) hn)
  cases n with
  | zero => lia
  | succ k =>
      by_cases hk : k = d
      · subst k
        simp [bidiagonalJensenPencil, mul_assoc, halpha,
          coeff_jensenPolynomial, hbeta]
      · have hdk : d < k := by lia
        have hbeta_coeff : (jensenPolynomial d beta).coeff k = 0 :=
          coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt (natDegree_jensenPolynomial_le d beta) hdk)
        simp [bidiagonalJensenPencil, mul_assoc, halpha, hbeta_coeff]

/-- Degree-two output discriminant identity at the coefficient-determined
Jensen-pencil parameter. -/
private theorem four_mul_bidiagonalOperator_discrim_eq_jensenPencil_two
    {alpha beta : ℕ → ℝ} {p : ℝ[X]} (hp1 : p.coeff 1 ≠ 0) :
    4 * discrim
        ((bidiagonalOperator alpha beta p).coeff 2)
        ((bidiagonalOperator alpha beta p).coeff 1)
        ((bidiagonalOperator alpha beta p).coeff 0) =
      p.coeff 1 ^ 2 * discrim
        ((bidiagonalJensenPencil alpha beta 2
          (2 * p.coeff 0 / p.coeff 1)).coeff 2)
        ((bidiagonalJensenPencil alpha beta 2
          (2 * p.coeff 0 / p.coeff 1)).coeff 1)
        ((bidiagonalJensenPencil alpha beta 2
          (2 * p.coeff 0 / p.coeff 1)).coeff 0) +
        4 * alpha 0 * alpha 2 *
          (p.coeff 1 ^ 2 - 4 * p.coeff 0 * p.coeff 2) := by
  have hpencil0 :
      (bidiagonalJensenPencil alpha beta 2
        (2 * p.coeff 0 / p.coeff 1)).coeff 0 = alpha 0 := by
    simp [bidiagonalJensenPencil, mul_assoc, coeff_jensenPolynomial]
  have hpencil1 :
      (bidiagonalJensenPencil alpha beta 2
        (2 * p.coeff 0 / p.coeff 1)).coeff 1 =
          2 * alpha 1 + (2 * p.coeff 0 / p.coeff 1) * beta 0 := by
    simp [bidiagonalJensenPencil, mul_assoc, coeff_jensenPolynomial]
  have hpencil2 :
      (bidiagonalJensenPencil alpha beta 2
        (2 * p.coeff 0 / p.coeff 1)).coeff 2 =
          alpha 2 + 2 * (2 * p.coeff 0 / p.coeff 1) * beta 1 := by
    simp [bidiagonalJensenPencil, mul_assoc, coeff_jensenPolynomial]
    ring
  rw [hpencil0, hpencil1, hpencil2]
  simp only [coeff_bidiagonalOperator_succ, Nat.reduceAdd, zero_add,
    coeff_bidiagonalOperator_zero]
  unfold discrim
  field_simp [hp1]
  ring

/-- In degree two, the one-sided Jensen-pencil certificate is sufficient when
the last subdiagonal coefficient vanishes. -/
theorem jensenPencilBidiagonalPreserver_two_of_beta_two_eq_zero
    {alpha beta : ℕ → ℝ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta 2)
    (hbeta2 : beta 2 = 0) :
    BidiagonalPFPreserver alpha beta 2 := by
  intro p hp hdeg
  have halpha : ∀ k, k ≤ 2 → 0 ≤ alpha k :=
    fun k hk ↦ hcert.alpha_nonneg_of_le hk
  have hbeta : ∀ k, k ≤ 2 → 0 ≤ beta k :=
    fun k hk ↦ hcert.beta_nonneg_of_le hk
  have hout_nonneg : HasNonnegCoeffs (bidiagonalOperator alpha beta p) :=
    hp.hasNonnegCoeffs.bidiagonalOperator_of_degree_le hdeg halpha hbeta
  apply IsPFPolynomial.of_realRooted_nonneg hout_nonneg
  have hout_deg : (bidiagonalOperator alpha beta p).natDegree ≤ 2 :=
    natDegree_bidiagonalOperator_le_of_beta_eq_zero hdeg hbeta2
  have hp_disc : 4 * (p.coeff 0 * p.coeff 2) ≤ p.coeff 1 ^ 2 :=
    disc_nonneg_of_isPolyaFreqSeq_natDegree_le_two hp.to_sequence hdeg
  have hout_discrim : 0 ≤ discrim
      ((bidiagonalOperator alpha beta p).coeff 2)
      ((bidiagonalOperator alpha beta p).coeff 1)
      ((bidiagonalOperator alpha beta p).coeff 0) := by
    by_cases hp1 : p.coeff 1 = 0
    · have hp02 : p.coeff 0 * p.coeff 2 = 0 := by
        have hp0 := hp.hasNonnegCoeffs 0
        have hp2 := hp.hasNonnegCoeffs 2
        rw [hp1] at hp_disc
        nlinarith
      rcases mul_eq_zero.mp hp02 with hp0 | hp2
      · simp [coeff_bidiagonalOperator_succ, hp1, hp0, discrim]
      · simpa [coeff_bidiagonalOperator_succ, hp1, hp2, discrim] using
          sq_nonneg (beta 0 * p.coeff 0)
    · have hp1_pos : 0 < p.coeff 1 :=
        lt_of_le_of_ne (hp.hasNonnegCoeffs 1) (Ne.symm hp1)
      let lam : ℝ := 2 * p.coeff 0 / p.coeff 1
      have hlam : 0 ≤ lam := div_nonneg
        (mul_nonneg (by norm_num) (hp.hasNonnegCoeffs 0)) hp1_pos.le
      have hpencil := hcert.2.2 lam hlam
      have hpencil_deg :
          (bidiagonalJensenPencil alpha beta 2 lam).natDegree ≤ 2 :=
        natDegree_bidiagonalJensenPencil_le_of_beta_eq_zero hbeta2
      have hpencil_disc : 4 *
          ((bidiagonalJensenPencil alpha beta 2 lam).coeff 0 *
            (bidiagonalJensenPencil alpha beta 2 lam).coeff 2) ≤
          (bidiagonalJensenPencil alpha beta 2 lam).coeff 1 ^ 2 :=
        disc_nonneg_of_isPolyaFreqSeq_natDegree_le_two
          hpencil.to_sequence hpencil_deg
      have hpencil_discrim : 0 ≤ discrim
          ((bidiagonalJensenPencil alpha beta 2 lam).coeff 2)
          ((bidiagonalJensenPencil alpha beta 2 lam).coeff 1)
          ((bidiagonalJensenPencil alpha beta 2 lam).coeff 0) := by
        unfold discrim
        linarith
      have hinput_discrim :
          0 ≤ p.coeff 1 ^ 2 - 4 * p.coeff 0 * p.coeff 2 := by
        linarith
      have hfour_alpha02 : 0 ≤ 4 * alpha 0 * alpha 2 :=
        mul_nonneg
          (mul_nonneg (by norm_num) (halpha 0 (by norm_num)))
          (halpha 2 (by norm_num))
      have hidentity :=
        four_mul_bidiagonalOperator_discrim_eq_jensenPencil_two
          (alpha := alpha) (beta := beta) hp1
      have hpencil_discrim' : 0 ≤ discrim
          ((bidiagonalJensenPencil alpha beta 2
            (2 * p.coeff 0 / p.coeff 1)).coeff 2)
          ((bidiagonalJensenPencil alpha beta 2
            (2 * p.coeff 0 / p.coeff 1)).coeff 1)
          ((bidiagonalJensenPencil alpha beta 2
            (2 * p.coeff 0 / p.coeff 1)).coeff 0) := by
        simpa [lam] using hpencil_discrim
      have hrhs_nonneg : 0 ≤
          p.coeff 1 ^ 2 * discrim
            ((bidiagonalJensenPencil alpha beta 2
              (2 * p.coeff 0 / p.coeff 1)).coeff 2)
            ((bidiagonalJensenPencil alpha beta 2
              (2 * p.coeff 0 / p.coeff 1)).coeff 1)
            ((bidiagonalJensenPencil alpha beta 2
              (2 * p.coeff 0 / p.coeff 1)).coeff 0) +
            4 * alpha 0 * alpha 2 *
              (p.coeff 1 ^ 2 - 4 * p.coeff 0 * p.coeff 2) := add_nonneg
        (mul_nonneg (sq_nonneg _) hpencil_discrim')
        (mul_nonneg hfour_alpha02 hinput_discrim)
      nlinarith [hidentity]
  rw [Polynomial.eq_quadratic_of_degree_le_two
    (Polynomial.degree_le_of_natDegree_le hout_deg)]
  exact quadraticPoly_splits_of_discrim_nonneg_or_linear hout_discrim


end RealRooted
