import RealRooted.NarayanaTransformation.Recurrences.Identities

/-!
# Generalized Narayana recurrence interlacing
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

theorem narayanaPolynomial_no_common_root (m : ℕ) :
    ∀ (n : ℕ) (r : ℝ), (narayanaPolynomial m (n + 1)).IsRoot r →
      ¬ (narayanaPolynomial m n).IsRoot r := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      intro r hr₂ hr₁
      have hr_ne : r ≠ 1 := fun h => (narayanaPolynomial_eval_one_pos m (n + 1)).ne' (h ▸ hr₁)
      have : (C ((n : ℝ) + 2 * m + 2) * narayanaPolynomial m (n + 2)).eval r =
          (C ((2 * n : ℝ) + 2 * m + 3) * ((1 + X) * narayanaPolynomial m (n + 1)) -
            C ((n : ℝ) + 1) * ((1 - X) ^ 2 * narayanaPolynomial m n)).eval r :=
        congrArg (eval r) (narayanaPolynomial_pure_rec m n)
      simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_one, eval_X] at this
      rw [hr₂, hr₁] at this
      have : (1 - r) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hr_ne))
      have : ((n : ℝ) + 1) ≠ 0 := by positivity
      simp_all

theorem prec_narayanaPolynomial_one_two (m : ℕ) :
    Prec (narayanaPolynomial m 1) (narayanaPolynomial m 2) := by
  have hm₁ : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set c : ℝ := 2 * ((m : ℝ) + 2) / ((m : ℝ) + 1) with hcdef
  have hcgt : 2 < c := by
    rw [hcdef, lt_div_iff₀ hm₁]
    linarith
  have hN₁ : narayanaPolynomial m 1 = X + C 1 := narayanaPolynomial_one m
  have hN₂ : narayanaPolynomial m 2 = X ^ 2 + C c * X + C 1 := narayanaPolynomial_two m
  have hdisc : (0 : ℝ) ≤ discrim 1 c 1 := by
    rw [discrim]
    nlinarith [hcgt]
  have hN₂_form : narayanaPolynomial m 2 = C (1 : ℝ) * X ^ 2 + C c * X + C 1 := by simp [hN₂]
  have hsplit₂ : (narayanaPolynomial m 2).Splits := by
    rw [hN₂_form]
    exact quadraticPoly_splits_of_discrim_nonneg one_ne_zero hdisc
  have hsplit₁ : (narayanaPolynomial m 1).Splits := by
    rw [hN₁]
    have : (X + C 1 : ℝ[X]) = X - C (-1) := by simp
    rw [this]
    exact Splits.X_sub_C (-1)
  set d : ℝ := Real.sqrt (discrim 1 c 1) with hddef
  set r₁ : ℝ := (-c - d) / 2 with hr₁_def
  set r₂ : ℝ := (-c + d) / 2 with hr₂_def
  have hr₁₂ : r₁ ≤ r₂ := by
    rw [hr₁_def, hr₂_def]
    have : 0 ≤ d := Real.sqrt_nonneg _
    linarith
  have hd_sq : d ^ 2 = c ^ 2 - 4 := by
    rw [hddef, discrim]
    have := Real.sq_sqrt hdisc
    rw [discrim] at this
    linarith
  have hsum : r₁ + r₂ = -c := by
    rw [hr₁_def, hr₂_def]
    ring
  have hprod : r₁ * r₂ = 1 := by
    rw [hr₁_def, hr₂_def]
    nlinarith [hd_sq]
  have hfactor : narayanaPolynomial m 2 = (X - C r₁) * (X - C r₂) := by
    rw [hN₂]
    symm
    calc (X - C r₁) * (X - C r₂)
      _ = X ^ 2 - C (r₁ + r₂) * X + C (r₁ * r₂) := by
          simp only [map_add, map_mul]
          ring
      _ = X ^ 2 + C c * X + C 1 := by
          rw [hsum, hprod]
          simp
  have hprod_neg : ((-1 : ℝ) - r₁) * ((-1 : ℝ) - r₂) < 0 := by
    calc ((-1 : ℝ) - r₁) * ((-1 : ℝ) - r₂)
      _ = 2 - c := by
          have : ((-1 : ℝ) - r₁) * ((-1 : ℝ) - r₂) =
              1 + (r₁ + r₂) + r₁ * r₂ := by
            ring
          rw [this, hsum, hprod]
          ring
      _ < 0 := by linarith [hcgt]
  have hbetween : r₁ ≤ -1 ∧ -1 ≤ r₂ := by
    constructor
    · rw [hr₁_def]
      linarith [hcgt]
    · by_contra h
      have : r₂ < -1 := not_le.mp h
      nlinarith [hprod_neg, hr₁₂, this]
  refine ⟨⟨narayanaPolynomial_ne_zero m 1, hsplit₁⟩,
    ⟨narayanaPolynomial_ne_zero m 2, hsplit₂⟩, [(-1 : ℝ)], [r₁, r₂],
    ?_, ?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · exact List.pairwise_singleton _ _
  · simp [hr₁₂]
  · have : (X + C (1 : ℝ)) = X - C (-1) := by simp
    rw [hN₁, this, Polynomial.roots_X_sub_C]
    rfl
  · rw [hfactor, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
      roots_X_sub_C, roots_X_sub_C]
    rfl
  · simp
  · exact ⟨hbetween.1, hbetween.2, trivial⟩

lemma two_mul_sub_two_mul_sq_nonpos_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2).eval r ≤ 0 := by
  simp only [eval_mul, eval_C, eval_sub, eval_pow, eval_X]
  nlinarith

/-- Consecutive positive-degree generalized Narayana polynomials are in proper
position.  This exposes the full Liu--Wang conclusion already constructed by
the recurrence proof below, rather than retaining only real-rootedness. -/
theorem prec_narayanaPolynomial_succ (m n : ℕ) :
    Prec (narayanaPolynomial m (n + 1)) (narayanaPolynomial m (n + 2)) := by
  set P : ℕ → ℝ[X] := fun k => narayanaPolynomial m (k + 1) with hP
  have hpos (k : ℕ) : HasPosLeadingCoeff (P k) :=
    hasPosLeadingCoeff_narayanaPolynomial m (k + 1)
  have hdeg_succ (k : ℕ) : (P k).natDegree + 1 = (P (k + 1)).natDegree := by
    simp only [hP, natDegree_narayanaPolynomial]
  have hdeg_two (k : ℕ) : 2 ≤ (P (k + 1)).natDegree := by
    rw [hP, natDegree_narayanaPolynomial]
    lia
  have hno (k : ℕ) (r : ℝ) (hr : (P (k + 1)).IsRoot r) : ¬ (P k).IsRoot r :=
    narayanaPolynomial_no_common_root m (k + 1) r hr
  have hrec (k : ℕ) :
      P (k + 2) =
        (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ *
          (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)
            + C ((3 * (k + 1 : ℕ) : ℝ) + 2 * m + 4) * X)) * P (k + 1)
        + (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ *
            (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2)) *
            (P (k + 1)).derivative
        + 0 * P k := by
    grind [narayanaPolynomial_deriv_lag_rec m (k + 1)]
  have hbase : Prec (P 0) (P 1) := prec_narayanaPolynomial_one_two m
  have hV_nonpos (k : ℕ) (r : ℝ) (hr : (P (k + 1)).IsRoot r) :
      (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ *
        (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2)).eval r ≤ 0 := by
    rw [eval_mul, eval_C]
    have : 0 ≤ (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos this
      (two_mul_sub_two_mul_sq_nonpos_of_nonpos (narayanaPolynomial_root_nonpos hr))
  have hW_nonpos (k : ℕ) (r : ℝ) (_ : (P (k + 1)).IsRoot r) :
      (0 : ℝ[X]).eval r ≤ 0 := by
    simp
  have hbuild := prec_lw_derivative_lag_sequence
    (P := P)
    (U := fun k ↦ C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ *
      (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2) +
        C ((3 * (k + 1 : ℕ) : ℝ) + 2 * m + 4) * X))
    (V := fun k => C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ *
      (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2))
    (W := fun _ => 0)
    hbase hpos hdeg_two hrec hV_nonpos hW_nonpos hdeg_succ hno
  simpa [P] using hbuild n

end RealRooted
