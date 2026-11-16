module

public import RealRooted.VeroneseRecognition

/-!
# Affine recognition of Veronese product parents

This module transports the product-parent recognition theorem through the
affine change of variable `t ↦ α + βt`.  It gives the explicit seed from
issue #2116 and retains uniqueness of the scalar parent.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Normalize a polynomial sequence by the inverse affine substitution
`t ↦ (t - α) / β`. -/
@[expose] def affineNormalizeSequence (α β : ℝ) (P : ℕ → ℝ[X]) : ℕ → ℝ[X] :=
  fun n ↦ (P n).comp (C β⁻¹ * (X - C α))

/-- The indexed difference operator commutes with inverse affine
normalization of every row. -/
theorem sequenceDelta_affineNormalizeSequence (a b : ℕ → ℝ)
    (α β : ℝ) (P : ℕ → ℝ[X]) :
    sequenceDelta a b (affineNormalizeSequence α β P) =
      affineNormalizeSequence α β (sequenceDelta a b P) := by
  funext n
  simp [sequenceDelta, affineNormalizeSequence]

/-- Every iterate of the indexed difference operator commutes with inverse
affine normalization. -/
theorem iterate_sequenceDelta_affineNormalizeSequence (a b : ℕ → ℝ)
    (α β : ℝ) (P : ℕ → ℝ[X]) (k : ℕ) :
    (sequenceDelta a b)^[k] (affineNormalizeSequence α β P) =
      affineNormalizeSequence α β ((sequenceDelta a b)^[k] P) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih,
        sequenceDelta_affineNormalizeSequence]
      rw [Function.iterate_succ_apply']

/-- Inverse affine normalization followed by the original affine
substitution recovers a polynomial. -/
theorem comp_affineNormalize_comp_affine {p : ℝ[X]} {α β : ℝ}
    (hβ : β ≠ 0) :
    (p.comp (C β⁻¹ * (X - C α))).comp (C α + C β * X) = p := by
  rw [comp_assoc]
  convert p.comp_X using 2
  simp only [mul_comp, sub_comp, X_comp, C_comp]
  rw [show C α + C β * X - C α = C β * X by ring]
  rw [← mul_assoc, ← Polynomial.C_mul]
  simp [hβ]

/-- The original affine substitution followed by inverse normalization
recovers a polynomial. -/
theorem comp_affine_comp_affineNormalize {p : ℝ[X]} {α β : ℝ}
    (hβ : β ≠ 0) :
    (p.comp (C α + C β * X)).comp (C β⁻¹ * (X - C α)) = p := by
  rw [comp_assoc]
  convert p.comp_X using 2
  simp only [mul_comp, X_comp, C_comp, add_comp]
  rw [← mul_assoc, ← Polynomial.C_mul]
  simp [hβ]

/-- A product-parent residue row evaluated at the affine variable
`α + βt`. -/
@[expose] def affineVeroneseProductRow (r j : ℕ) (α β : ℝ)
    (a b : ℕ → ℝ) (H : ℝ[X]) (n : ℕ) : ℝ[X] :=
  (veroneseProductRow r j a b H n).comp (C α + C β * X)

/-- The explicit scalar seed reconstructed after inverse affine
normalization. -/
@[expose] def reconstructedAffineVeroneseSeed (r : ℕ) (α β : ℝ)
    (a b : ℕ → ℝ) (P : ℕ → ℝ[X]) : ℝ[X] :=
  reconstructedVeroneseParent r a b (affineNormalizeSequence α β P) 0

/-- The affine reconstructed seed is the sum of the first iterated
differences evaluated at `(X ^ r - α) / β`. -/
theorem reconstructedAffineVeroneseSeed_eq_sum
    (r : ℕ) (α β : ℝ) (a b : ℕ → ℝ) (P : ℕ → ℝ[X]) :
    reconstructedAffineVeroneseSeed r α β a b P =
      ∑ j ∈ Finset.range r, X ^ j *
        (((sequenceDelta a b)^[r - 1 - j] P) 0).comp
          (C β⁻¹ * (X ^ r - C α)) := by
  simp only [reconstructedAffineVeroneseSeed, reconstructedVeroneseParent,
    veroneseResidueTerm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [congrFun (iterate_sequenceDelta_affineNormalizeSequence a b α β P
    (r - 1 - j)) 0]
  simp only [affineNormalizeSequence, comp_assoc]
  congr 2
  simp [mul_comp, sub_comp]

private theorem affine_cycle_iff_normalized_cycle {r : ℕ}
    {a b : ℕ → ℝ} {P : ℕ → ℝ[X]} {α β : ℝ} (hβ : β ≠ 0) :
    (∀ n, ((sequenceDelta a b)^[r] P) n =
      (C α + C β * X) * P n) ↔
      ∀ n, ((sequenceDelta a b)^[r]
        (affineNormalizeSequence α β P)) n =
          X * affineNormalizeSequence α β P n := by
  constructor
  · intro hcycle n
    rw [congrFun (iterate_sequenceDelta_affineNormalizeSequence a b α β P r) n,
      affineNormalizeSequence, hcycle]
    simp only [mul_comp, add_comp, C_comp, X_comp]
    congr 1
    rw [← mul_assoc, ← Polynomial.C_mul]
    simp [hβ]
  · intro hcycle n
    have hn := hcycle n
    rw [congrFun (iterate_sequenceDelta_affineNormalizeSequence a b α β P r) n,
      affineNormalizeSequence] at hn
    have hn' := congrArg (fun p : ℝ[X] ↦ p.comp (C α + C β * X)) hn
    rw [comp_affineNormalize_comp_affine hβ, mul_comp, X_comp] at hn'
    have hrecover :
        (affineNormalizeSequence α β P n).comp (C α + C β * X) = P n := by
      exact comp_affineNormalize_comp_affine hβ
    rw [hrecover] at hn'
    exact hn'

private theorem existsUnique_affineProductRow_iff_normalized
    {r : ℕ} {a b : ℕ → ℝ} {P : ℕ → ℝ[X]} {α β : ℝ}
    (hβ : β ≠ 0) :
    (∃! H : ℝ[X], ∀ n,
      affineVeroneseProductRow r (r - 1) α β a b H n = P n) ↔
      ∃! H : ℝ[X], ∀ n,
        veroneseProductRow r (r - 1) a b H n =
          affineNormalizeSequence α β P n := by
  constructor
  · rintro ⟨H, hH, huniq⟩
    refine ⟨H, ?_, ?_⟩
    · intro n
      have hn := congrArg
        (fun p : ℝ[X] ↦ p.comp (C β⁻¹ * (X - C α))) (hH n)
      simpa [affineVeroneseProductRow, affineNormalizeSequence,
        comp_affine_comp_affineNormalize hβ] using hn
    · intro K hK
      apply huniq K
      intro n
      have hn := congrArg
        (fun p : ℝ[X] ↦ p.comp (C α + C β * X)) (hK n)
      simpa [affineVeroneseProductRow, affineNormalizeSequence,
        comp_affineNormalize_comp_affine hβ] using hn
  · rintro ⟨H, hH, huniq⟩
    refine ⟨H, ?_, ?_⟩
    · intro n
      have hn := congrArg
        (fun p : ℝ[X] ↦ p.comp (C α + C β * X)) (hH n)
      simpa [affineVeroneseProductRow, affineNormalizeSequence,
        comp_affineNormalize_comp_affine hβ] using hn
    · intro K hK
      apply huniq K
      intro n
      have hn := congrArg
        (fun p : ℝ[X] ↦ p.comp (C β⁻¹ * (X - C α))) (hK n)
      simpa [affineVeroneseProductRow, affineNormalizeSequence,
        comp_affine_comp_affineNormalize hβ] using hn

/-- **Affine product-parent recognition criterion.**  The equation
`Δ^r P = (α + βX) P`, with nonzero `β`, is equivalent to existence of a
unique scalar product parent whose last section is evaluated at `α + βX`.
The unique seed is `reconstructedAffineVeroneseSeed`. -/
theorem iterate_sequenceDelta_eq_affine_mul_iff_existsUnique_seed
    {r : ℕ} (hr : 0 < r) {a b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0)
    {α β : ℝ} (hβ : β ≠ 0) (P : ℕ → ℝ[X]) :
    (∀ n, ((sequenceDelta a b)^[r] P) n =
      (C α + C β * X) * P n) ↔
      ∃! H : ℝ[X], ∀ n,
        affineVeroneseProductRow r (r - 1) α β a b H n = P n := by
  rw [affine_cycle_iff_normalized_cycle hβ,
    iterate_sequenceDelta_eq_X_mul_iff_existsUnique_seed hr hb,
    existsUnique_affineProductRow_iff_normalized hβ]

/-- Any seed giving the affine product-parent rows equals the explicit
reconstructed affine seed. -/
theorem eq_reconstructedAffineVeroneseSeed_of_affineProductRow_eq
    {r : ℕ} (hr : 0 < r) {a b : ℕ → ℝ} (hb : ∀ n, b n ≠ 0)
    {α β : ℝ} (hβ : β ≠ 0) {P : ℕ → ℝ[X]} {H : ℝ[X]}
    (hrow : ∀ n,
      affineVeroneseProductRow r (r - 1) α β a b H n = P n) :
    H = reconstructedAffineVeroneseSeed r α β a b P := by
  apply eq_reconstructedVeroneseParent_zero_of_productRow_eq hr hb
  intro n
  have hn := congrArg
    (fun p : ℝ[X] ↦ p.comp (C β⁻¹ * (X - C α))) (hrow n)
  simpa [affineVeroneseProductRow, affineNormalizeSequence,
    reconstructedAffineVeroneseSeed,
    comp_affine_comp_affineNormalize hβ] using hn

/-- A nonnegative splitting affine seed and nonnegative product factors
certify that every row in the affine recognition equation is zero or splits
over the reals. -/
theorem sequenceDelta_affine_row_eq_zero_or_splits
    {r : ℕ} (hr : 0 < r) {a b : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n) {α β : ℝ} (hβ : 0 < β)
    {P : ℕ → ℝ[X]}
    (hcycle : ∀ n, ((sequenceDelta a b)^[r] P) n =
      (C α + C β * X) * P n)
    (hseednn : HasNonnegCoeffs
      (reconstructedAffineVeroneseSeed r α β a b P))
    (hseedsplits : (reconstructedAffineVeroneseSeed r α β a b P).Splits)
    (n : ℕ) :
    P n = 0 ∨ (P n).Splits := by
  have hcycle' := (affine_cycle_iff_normalized_cycle hβ.ne').mp hcycle
  have hrow := sequenceDelta_row_eq_zero_or_splits hr ha hb hcycle'
    (by simpa [reconstructedAffineVeroneseSeed] using hseednn)
    (by simpa [reconstructedAffineVeroneseSeed] using hseedsplits) n
  have hrecover :
      (affineNormalizeSequence α β P n).comp (C α + C β * X) = P n :=
    comp_affineNormalize_comp_affine hβ.ne'
  rcases hrow with hzero | hsplits
  · left
    rw [← hrecover, hzero]
    simp
  · right
    rw [← hrecover]
    exact hsplits.comp_of_natDegree_le_one (by simp [hβ.ne'])

/-! ## Constant second-order recurrences -/

/-- A constant second-order recurrence has a unique affine Veronese product
parent.  The normalization uses `a = A / 2`,
`α = c + A ^ 2 / 4`, and `β = B`. -/
theorem existsUnique_affineVeroneseProductRow_of_orderTwo_recurrence
    (A B c : ℝ) (hB : B ≠ 0) (P : ℕ → ℝ[X])
    (hrec : ∀ n, P (n + 2) = C A * P (n + 1) +
      (C B * X + C c) * P n) :
    ∃! H : ℝ[X], ∀ n,
      affineVeroneseProductRow 2 1 (c + A ^ 2 / 4) B
        (fun _ ↦ A / 2) (fun _ ↦ 1) H n = P n := by
  apply (iterate_sequenceDelta_eq_affine_mul_iff_existsUnique_seed
    (r := 2) (by norm_num) (a := fun _ ↦ A / 2) (b := fun _ ↦ 1)
    (by simp) hB P).mp
  intro n
  change sequenceDelta (fun _ ↦ A / 2) (fun _ ↦ 1)
    (sequenceDelta (fun _ ↦ A / 2) (fun _ ↦ 1) P) n = _
  simp only [sequenceDelta]
  rw [show n + 1 + 1 = n + 2 by lia, hrec n]
  simp only [inv_one, map_one, one_mul, map_add]
  have hdouble : (C A : ℝ[X]) = C (A / 2) + C (A / 2) := by
    rw [← Polynomial.C_add]
    congr 1
    ring
  have hsquare : (C (A / 2) : ℝ[X]) ^ 2 = C (A ^ 2 / 4) := by
    rw [← Polynomial.C_pow]
    congr 1
    ring
  rw [hdouble, ← hsquare]
  ring

/-- For order two, the reconstructed affine seed is determined by the first
two rows via the formula from issue #2116. -/
theorem reconstructedAffineVeroneseSeed_orderTwo_eq
    (A B c : ℝ) (P : ℕ → ℝ[X]) :
    reconstructedAffineVeroneseSeed 2 (c + A ^ 2 / 4) B
      (fun _ ↦ A / 2) (fun _ ↦ 1) P =
        (P 1).comp (C B⁻¹ * (X ^ 2 - C (c + A ^ 2 / 4))) +
          (X - C (A / 2)) *
            (P 0).comp (C B⁻¹ * (X ^ 2 - C (c + A ^ 2 / 4))) := by
  rw [reconstructedAffineVeroneseSeed_eq_sum]
  norm_num [Finset.sum_range_succ, Function.iterate_succ_apply',
    sequenceDelta]
  ring

/-- **Quadratic reconstruction.**  A sequence satisfying
`P_(n+2) = A P_(n+1) + (B X + c) P_n` is the affine last section of the
product parent with the explicit seed determined by `P_0` and `P_1`. -/
theorem affineVeroneseProductRow_orderTwo_eq_of_recurrence
    (A B c : ℝ) (hB : B ≠ 0) (P : ℕ → ℝ[X])
    (hrec : ∀ n, P (n + 2) = C A * P (n + 1) +
      (C B * X + C c) * P n) (n : ℕ) :
    affineVeroneseProductRow 2 1 (c + A ^ 2 / 4) B
      (fun _ ↦ A / 2) (fun _ ↦ 1)
      ((P 1).comp (C B⁻¹ * (X ^ 2 - C (c + A ^ 2 / 4))) +
        (X - C (A / 2)) *
          (P 0).comp (C B⁻¹ * (X ^ 2 - C (c + A ^ 2 / 4)))) n = P n := by
  obtain ⟨H, hH, _⟩ :=
    existsUnique_affineVeroneseProductRow_of_orderTwo_recurrence
      A B c hB P hrec
  have hseed := eq_reconstructedAffineVeroneseSeed_of_affineProductRow_eq
    (r := 2) (by norm_num) (a := fun _ ↦ A / 2) (b := fun _ ↦ 1)
    (by simp) hB hH
  rw [reconstructedAffineVeroneseSeed_orderTwo_eq] at hseed
  rw [← hseed]
  exact hH n

/-- Fibonacci-type rows with `P₀ = P₁ = 1` are affine odd sections of
successive powers of `X + 1 / 2`. -/
theorem _root_.RealRooted.VeroneseRecognition.section_X_add_half_pow_comp_eq_of_fibonacci_recurrence
    (P : ℕ → ℝ[X]) (hzero : P 0 = 1) (hone : P 1 = 1)
    (hrec : ∀ n, P (n + 2) = P (n + 1) + X * P n) (n : ℕ) :
    (veroneseSectionPolynomial 2 1 ((X + C (1 / 2 : ℝ)) ^ (n + 1))).comp
      (C (1 / 4 : ℝ) + X) = P n := by
  have h := affineVeroneseProductRow_orderTwo_eq_of_recurrence
    1 1 0 one_ne_zero P (by simpa using hrec) n
  have hseed : (1 : ℝ[X]) + (X - C (1 / 2 : ℝ)) =
      X + C (1 / 2 : ℝ) := by
    rw [show (1 : ℝ[X]) = C 1 by simp,
      show (1 : ℝ) = 1 / 2 + 1 / 2 by norm_num, map_add]
    ring
  have hfactor : C (1 / 2 : ℝ) + X = X + C (1 / 2 : ℝ) := by ring
  rw [hzero, hone] at h
  simp only [one_comp, mul_one] at h
  rw [hseed] at h
  simp only [affineVeroneseProductRow, veroneseProductRow,
    veroneseProductParent, Finset.prod_const, Finset.card_range] at h
  simp only [map_one, one_mul, one_pow, zero_add] at h
  rw [hfactor] at h
  simpa [pow_succ'] using h

end RealRooted
