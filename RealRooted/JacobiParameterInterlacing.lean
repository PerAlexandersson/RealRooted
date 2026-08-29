import RealRooted.Bezoutian
import RealRooted.Derivative
import RealRooted.Jacobi
import RealRooted.Linear

/-!
# Parameter interlacing for shifted Jacobi polynomials

This file develops the ordered cross-parameter root comparisons needed for
the A390883 formalization. The first comparison is the derivative case, where
both parameters increase by one and the degree drops by one.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A shifted Jacobi polynomial has an increasing enumeration of all its
roots, and every enumerated root lies in the open unit interval. -/
theorem exists_shiftedJacobi_orderedRoots (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    ∃ r : Fin n → ℝ,
      StrictMono r ∧
      (∀ i, (shiftedJacobi n α β).IsRoot (r i)) ∧
      ∀ i, r i ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨r, hr_mono, hr_roots⟩ := Polynomial.exists_strictMono_roots
    (shiftedJacobi_splits n hα hβ)
    (natDegree_shiftedJacobi n hα hβ)
    (shiftedJacobi_roots_nodup n hα hβ)
  exact ⟨r, hr_mono, hr_roots, fun i =>
    shiftedJacobi_isRoot_mem_Ioo n hα hβ (hr_roots i)⟩

/-- Increasing both Jacobi parameters by one while lowering the degree by one
gives the derivative interlacer. -/
theorem shiftedJacobi_interlaces_shift_both (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    Interlaces (shiftedJacobi n (α + 1) (β + 1))
      (shiftedJacobi (n + 1) α β) := by
  cases n with
  | zero =>
      have hzero : shiftedJacobi 0 (α + 1) (β + 1) = 1 := by
        simp [shiftedJacobi]
      rw [hzero]
      exact interlaces_one_linear (natDegree_shiftedJacobi 1 hα hβ)
  | succ n =>
      let c : ℝ := -(n + 1 + α + β + 2)
      have hc : c ≠ 0 := by
        dsimp [c]
        linarith
      have hderivative :
          (shiftedJacobi (n + 1 + 1) α β).derivative =
            C c * shiftedJacobi (n + 1) (α + 1) (β + 1) := by
        simpa [c, Nat.cast_add, Nat.cast_one] using
          derivative_shiftedJacobi (n + 1) α β
      have hscaled :
          Prec (C c * shiftedJacobi (n + 1) (α + 1) (β + 1))
            (shiftedJacobi (n + 1 + 1) α β) := by
        rw [← hderivative]
        exact (derivative_interlaces
          (shiftedJacobi_splits (n + 1 + 1) hα hβ) (by
            rw [natDegree_shiftedJacobi (n + 1 + 1) hα hβ]
            lia)).toPrec
      have hunscaled := hscaled.C_mul_left (inv_ne_zero hc)
      have hprec :
          Prec (shiftedJacobi (n + 1) (α + 1) (β + 1))
            (shiftedJacobi (n + 1 + 1) α β) := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul] at hunscaled
        exact hunscaled
      apply hprec.toInterlaces
      rw [natDegree_shiftedJacobi (n + 1) (by linarith) (by linarith),
        natDegree_shiftedJacobi (n + 1 + 1) hα hβ]

/-- A unit increase in the second parameter expresses the old monic Jacobi
polynomial as a positive multiple of the new one plus a strictly negative
multiple of the preceding new polynomial. -/
theorem exists_shiftedJacobiMonic_beta_add_one_linearCombination
    (m : ℕ) {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    ∃ a b : ℝ,
      0 < a ∧ b < 0 ∧
      shiftedJacobiMonic (m + 1) α β =
        C a * shiftedJacobiMonic (m + 1) α (β + 1) +
          C b * shiftedJacobiMonic m α (β + 1) := by
  let n : ℕ := m + 1
  let p₀ : ℝ := Ring.choose (n + α + β + n) n
  let p₁ : ℝ := Ring.choose (n + α + (β + 1) + n) n
  let pₘ : ℝ := Ring.choose (m + α + (β + 1) + m) m
  let l₀ : ℝ := (-1 : ℝ) ^ n * p₀
  let l₁ : ℝ := (-1 : ℝ) ^ n * p₁
  let lₘ : ℝ := (-1 : ℝ) ^ m * pₘ
  let A : ℝ := 2 * n + α + β + 1
  let B : ℝ := n + α + β + 1
  let D : ℝ := n + α
  let a : ℝ := B * l₁ / (A * l₀)
  let b : ℝ := D * lₘ / (A * l₀)
  have hp₀ : 0 < p₀ := by
    apply Polynomial.ring_choose_pos
    simp only [n]
    push_cast
    linarith
  have hp₁ : 0 < p₁ := by
    apply Polynomial.ring_choose_pos
    simp only [n]
    push_cast
    linarith
  have hpₘ : 0 < pₘ := by
    apply Polynomial.ring_choose_pos
    linarith
  have hA : 0 < A := by
    simp only [A, n]
    push_cast
    linarith
  have hB : 0 < B := by
    simp only [B, n]
    push_cast
    linarith
  have hD : 0 < D := by
    simp only [D, n]
    push_cast
    linarith
  have hsign : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  have ha_eq : a = B * p₁ / (A * p₀) := by
    simp only [a, l₀, l₁, n, pow_succ]
    field_simp [hsign, hp₀.ne', hp₁.ne', hA.ne']
  have hb_eq : b = -(D * pₘ / (A * p₀)) := by
    simp only [b, l₀, lₘ, n, pow_succ]
    field_simp [hsign, hp₀.ne', hpₘ.ne', hA.ne']
  have hl₀ : l₀ ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero n (by norm_num)) hp₀.ne'
  have hl₁ : l₁ ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero n (by norm_num)) hp₁.ne'
  have hlₘ : lₘ ≠ 0 := by
    exact mul_ne_zero hsign hpₘ.ne'
  have ha_scalar : (A * l₀)⁻¹ * B = a * l₁⁻¹ := by
    simp only [a]
    field_simp [hA.ne', hl₀, hl₁]
  have hb_scalar : (A * l₀)⁻¹ * D = b * lₘ⁻¹ := by
    simp only [b]
    field_simp [hA.ne', hl₀, hlₘ]
  refine ⟨a, b, ?_, ?_, ?_⟩
  · rw [ha_eq]
    exact div_pos (mul_pos hB hp₁) (mul_pos hA hp₀)
  · rw [hb_eq]
    exact neg_neg_of_pos (div_pos (mul_pos hD hpₘ) (mul_pos hA hp₀))
  · have hraw :
        C A * shiftedJacobi n α β =
          C B * shiftedJacobi n α (β + 1) +
            C D * shiftedJacobi (n - 1) α (β + 1) := by
      simpa only [A, B, D] using
        shiftedJacobi_beta_add_one n α β (by simp [n])
    change shiftedJacobiMonic n α β =
      C a * shiftedJacobiMonic n α (β + 1) +
        C b * shiftedJacobiMonic (n - 1) α (β + 1)
    have ha_poly :
        C ((A * l₀)⁻¹ * B) * shiftedJacobi n α (β + 1) =
          C a * shiftedJacobiMonic n α (β + 1) := by
      rw [shiftedJacobiMonic]
      change C ((A * l₀)⁻¹ * B) * shiftedJacobi n α (β + 1) =
        C a * (C l₁⁻¹ * shiftedJacobi n α (β + 1))
      calc
        C ((A * l₀)⁻¹ * B) * shiftedJacobi n α (β + 1) =
            C (a * l₁⁻¹) * shiftedJacobi n α (β + 1) := by rw [ha_scalar]
        _ = (C a * C l₁⁻¹) * shiftedJacobi n α (β + 1) := by rw [C_mul]
        _ = C a * (C l₁⁻¹ * shiftedJacobi n α (β + 1)) := by rw [mul_assoc]
    have hb_poly :
        C ((A * l₀)⁻¹ * D) * shiftedJacobi (n - 1) α (β + 1) =
          C b * shiftedJacobiMonic (n - 1) α (β + 1) := by
      rw [shiftedJacobiMonic]
      change C ((A * l₀)⁻¹ * D) * shiftedJacobi (n - 1) α (β + 1) =
        C b * (C lₘ⁻¹ * shiftedJacobi (n - 1) α (β + 1))
      calc
        C ((A * l₀)⁻¹ * D) * shiftedJacobi (n - 1) α (β + 1) =
            C (b * lₘ⁻¹) * shiftedJacobi (n - 1) α (β + 1) := by rw [hb_scalar]
        _ = (C b * C lₘ⁻¹) * shiftedJacobi (n - 1) α (β + 1) := by rw [C_mul]
        _ = C b * (C lₘ⁻¹ * shiftedJacobi (n - 1) α (β + 1)) := by rw [mul_assoc]
    calc
      shiftedJacobiMonic n α β =
          C ((A * l₀)⁻¹) * (C A * shiftedJacobi n α β) := by
        rw [shiftedJacobiMonic]
        change C l₀⁻¹ * shiftedJacobi n α β =
          C ((A * l₀)⁻¹) * (C A * shiftedJacobi n α β)
        rw [← mul_assoc, ← C_mul]
        congr 1
        field_simp [hA.ne', hl₀]
      _ = C ((A * l₀)⁻¹) *
          (C B * shiftedJacobi n α (β + 1) +
            C D * shiftedJacobi (n - 1) α (β + 1)) := by rw [hraw]
      _ = C ((A * l₀)⁻¹ * B) * shiftedJacobi n α (β + 1) +
          C ((A * l₀)⁻¹ * D) * shiftedJacobi (n - 1) α (β + 1) := by
        rw [mul_add]
        congr 1 <;> rw [← mul_assoc, ← C_mul]
      _ = C a * shiftedJacobiMonic n α (β + 1) +
          C b * shiftedJacobiMonic (n - 1) α (β + 1) := by
        rw [ha_poly, hb_poly]

/-- Increasing the second Jacobi parameter by one moves the roots to the left
in the shifted variable, with the new polynomial in proper position before the
old polynomial. -/
theorem shiftedJacobiMonic_prec_beta_add_one (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    Prec (shiftedJacobiMonic n α (β + 1))
      (shiftedJacobiMonic n α β) := by
  cases n with
  | zero =>
      simpa using (prec_refl (f := (1 : ℝ[X])) (by simp) (by simp))
  | succ m =>
      let f := shiftedJacobiMonic (m + 1) α (β + 1)
      let g := shiftedJacobiMonic m α (β + 1)
      let F := shiftedJacobiMonic (m + 1) α β
      obtain ⟨a, b, ha, hb, hcombination⟩ :=
        exists_shiftedJacobiMonic_beta_add_one_linearCombination m hα hβ
      change F = C a * f + C b * g at hcombination
      have hgf_prec : Prec g f := by
        dsimp only [g, f]
        exact shiftedJacobiMonic_prec_succ m (by linarith) (by linarith)
      have hgf : Interlaces g f := by
        apply hgf_prec.toInterlaces
        dsimp only [g, f]
        rw [natDegree_shiftedJacobiMonic m (by linarith) (by linarith),
          natDegree_shiftedJacobiMonic (m + 1) (by linarith) (by linarith)]
      have hg_pos : HasPosLeadingCoeff g := by
        apply hasPosLeadingCoeff_of_monic
        dsimp only [g]
        exact monic_shiftedJacobiMonic m (by linarith) (by linarith)
      have hsum_pos : HasPosLeadingCoeff (C a * f + C b * g) := by
        rw [← hcombination]
        apply hasPosLeadingCoeff_of_monic
        dsimp only [F]
        exact monic_shiftedJacobiMonic (m + 1) hα hβ
      have hsame : (C a * f + C b * g).natDegree = f.natDegree := by
        rw [← hcombination]
        dsimp only [F, f]
        rw [natDegree_shiftedJacobiMonic (m + 1) hα hβ,
          natDegree_shiftedJacobiMonic (m + 1) (by linarith) (by linarith)]
      have hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r := by
        have hrec := shiftedJacobiMonic_satisfiesFavardRecurrence
          α (β + 1) (by linarith) (by linarith)
        have hsub : ∀ k : ℕ, 0 < shiftedJacobiSubdiag (k + 1) α (β + 1) := by
          intro k
          exact shiftedJacobiSubdiag_pos (k + 1) (by lia) (by linarith) (by linarith)
        have hcommon := noCommonRoot_succ_of_favard hrec hsub m
        intro r hf hg
        exact hcommon r hg hf
      have hproper : Prec f (C a * f + C b * g) :=
        prec_of_interlaces_evalCoeff_neg_same hgf hg_pos hsum_pos hsame hno
          (fun _ _ => by simpa using hb)
      rw [← hcombination] at hproper
      exact hproper

/-- Increasing the first Jacobi parameter by one moves the roots to the right
in the shifted variable. -/
theorem shiftedJacobiMonic_prec_alpha_add_one (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    Prec (shiftedJacobiMonic n α β)
      (shiftedJacobiMonic n (α + 1) β) := by
  have hbeta := shiftedJacobiMonic_prec_beta_add_one n (α := β) (β := α) hβ hα
  have hreflected := prec_comp_one_sub_X_of_sameDegree hbeta (by
    rw [natDegree_shiftedJacobiMonic n (by linarith) hα,
      natDegree_shiftedJacobiMonic n hβ (by linarith)])
  have hsign : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hscaled := (hreflected.C_mul_left hsign).C_mul_right hsign
  rw [← shiftedJacobiMonic_reflection n α β,
    ← shiftedJacobiMonic_reflection n (α + 1) β] at hscaled
  exact hscaled

end RealRooted
