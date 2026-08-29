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

private theorem shiftedJacobi_eq_leading_mul_monic (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    shiftedJacobi n α β =
      C ((-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n) *
        shiftedJacobiMonic n α β := by
  have hchoose : 0 < Ring.choose (n + α + β + n) n := by
    cases n with
    | zero => simp
    | succ n =>
        apply Polynomial.ring_choose_pos
        push_cast
        linarith
  have hscale : (-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n ≠ 0 :=
    mul_ne_zero (pow_ne_zero n (by norm_num)) hchoose.ne'
  symm
  rw [shiftedJacobiMonic, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hscale,
    C_1, one_mul]

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

/-- Consecutive second-parameter shifts of a monic shifted Jacobi polynomial
have no common root. -/
theorem shiftedJacobiMonic_noCommonRoot_beta_add_one (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    ∀ r, (shiftedJacobiMonic n α (β + 1)).IsRoot r →
      ¬(shiftedJacobiMonic n α β).IsRoot r := by
  cases n with
  | zero => simp [Polynomial.IsRoot.def]
  | succ m =>
      obtain ⟨a, b, ha, hb, hcombination⟩ :=
        exists_shiftedJacobiMonic_beta_add_one_linearCombination m hα hβ
      have hrec := shiftedJacobiMonic_satisfiesFavardRecurrence
        α (β + 1) (by linarith) (by linarith)
      have hsub : ∀ k : ℕ, 0 < shiftedJacobiSubdiag (k + 1) α (β + 1) := by
        intro k
        exact shiftedJacobiSubdiag_pos (k + 1) (by lia) (by linarith) (by linarith)
      have hcommon := noCommonRoot_succ_of_favard hrec hsub m
      intro r hf hF
      have heval := congrArg (Polynomial.eval r) hcombination
      rw [Polynomial.IsRoot.def] at hf hF
      simp only [eval_add, eval_mul, eval_C, hf, hF, mul_zero] at heval
      have hg : (shiftedJacobiMonic m α (β + 1)).IsRoot r := by
        rw [Polynomial.IsRoot.def]
        nlinarith
      exact hcommon r hg hf

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

/-- Consecutive first-parameter shifts of a monic shifted Jacobi polynomial
have no common root. -/
theorem shiftedJacobiMonic_noCommonRoot_alpha_add_one (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    ∀ r, (shiftedJacobiMonic n α β).IsRoot r →
      ¬(shiftedJacobiMonic n (α + 1) β).IsRoot r := by
  have hnoBeta : ∀ r, (shiftedJacobiMonic n β (α + 1)).IsRoot r →
      ¬(shiftedJacobiMonic n β α).IsRoot r :=
    shiftedJacobiMonic_noCommonRoot_beta_add_one n hβ hα
  intro r hlo hhi
  have hlo' : (shiftedJacobiMonic n β α).IsRoot (1 - r) := by
    rw [Polynomial.IsRoot.def] at hlo ⊢
    have href := congrArg (Polynomial.eval r) (shiftedJacobiMonic_reflection n α β)
    simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_one, eval_X] at href
    have hsign : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    rw [hlo] at href
    exact (mul_eq_zero.mp href.symm).resolve_left hsign
  have hhi' : (shiftedJacobiMonic n β (α + 1)).IsRoot (1 - r) := by
    rw [Polynomial.IsRoot.def] at hhi ⊢
    have href := congrArg (Polynomial.eval r)
      (shiftedJacobiMonic_reflection n (α + 1) β)
    simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_one, eval_X] at href
    have hsign : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    rw [hhi] at href
    exact (mul_eq_zero.mp href.symm).resolve_left hsign
  exact hnoBeta (1 - r) hhi' hlo'

/-- The first-parameter unit comparison is strictly interleaving. -/
theorem shiftedJacobiMonic_strictPrec_alpha_add_one (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    StrictPrecSameDegree (shiftedJacobiMonic n α β)
      (shiftedJacobiMonic n (α + 1) β) := by
  apply StrictPrecSameDegree.of_prec_of_no_common
    (shiftedJacobiMonic_prec_alpha_add_one n hα hβ)
  · rw [natDegree_shiftedJacobiMonic n hα hβ,
      natDegree_shiftedJacobiMonic n (by linarith) hβ]
  · exact shiftedJacobiMonic_noCommonRoot_alpha_add_one n hα hβ

/-- At a root of the lower-parameter polynomial, the monic Jacobi
polynomials one and two first-parameter units higher have the same sign. -/
theorem shiftedJacobiMonic_eval_mul_alpha_add_one_two_pos (n : ℕ)
    {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (hx : (shiftedJacobiMonic n α β).IsRoot x) :
    0 < (shiftedJacobiMonic n (α + 1) β).eval x *
      (shiftedJacobiMonic n (α + 2) β).eval x := by
  let l₁ : ℝ := (-1 : ℝ) ^ n *
    Ring.choose (n + (α + 1) + β + n) n
  let l₂ : ℝ := (-1 : ℝ) ^ n *
    Ring.choose (n + (α + 2) + β + n) n
  have hp₁ : 0 < Ring.choose (n + (α + 1) + β + n) n :=
    Polynomial.ring_choose_pos (by linarith)
  have hp₂ : 0 < Ring.choose (n + (α + 2) + β + n) n :=
    Polynomial.ring_choose_pos (by linarith)
  have hsign : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hlprod : 0 < l₁ * l₂ := by
    calc
      l₁ * l₂ = (((-1 : ℝ) ^ n) ^ 2) *
          Ring.choose (n + (α + 1) + β + n) n *
          Ring.choose (n + (α + 2) + β + n) n := by
            simp only [l₁, l₂]
            ring
      _ > 0 := by positivity
  have hraw₀ : (shiftedJacobi n α β).IsRoot x := by
    rw [Polynomial.IsRoot.def] at hx ⊢
    rw [shiftedJacobi_eq_leading_mul_monic n hα hβ]
    simp [hx]
  have hx_pos := (shiftedJacobi_isRoot_mem_Ioo n hα hβ hraw₀).1
  have hmid_ne : (shiftedJacobiMonic n (α + 1) β).eval x ≠ 0 := by
    intro hzero
    exact shiftedJacobiMonic_noCommonRoot_alpha_add_one n hα hβ x hx
      (by simpa only [Polynomial.IsRoot.def] using hzero)
  have hraw₁ : shiftedJacobi n (α + 1) β =
      C l₁ * shiftedJacobiMonic n (α + 1) β := by
    simpa only [l₁] using
      shiftedJacobi_eq_leading_mul_monic n (by linarith : -1 < α + 1) hβ
  have hraw₂ : shiftedJacobi n (α + 2) β =
      C l₂ * shiftedJacobiMonic n (α + 2) β := by
    simpa only [l₂] using
      shiftedJacobi_eq_leading_mul_monic n (by linarith : -1 < α + 2) hβ
  have hl₁_ne : l₁ ≠ 0 := by
    exact mul_ne_zero hsign hp₁.ne'
  have hraw₁_ne : (shiftedJacobi n (α + 1) β).eval x ≠ 0 := by
    rw [hraw₁]
    simp only [eval_mul, eval_C]
    exact mul_ne_zero hl₁_ne hmid_ne
  have hid := congrArg (Polynomial.eval x)
    (Polynomial.shiftedJacobi_alpha_add_two n α β hα)
  rw [Polynomial.IsRoot.def] at hraw₀
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_X, hraw₀,
    mul_zero] at hid
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hA : 0 < (n : ℝ) + α + β + 2 := by linarith
  have hB : 0 < α + 1 + (α + β + 2 * n + 2) * x := by
    have hα1 : 0 < α + 1 := by linarith
    have hE : 0 < α + β + 2 * (n : ℝ) + 2 := by linarith
    have hEx : 0 < (α + β + 2 * (n : ℝ) + 2) * x :=
      mul_pos hE hx_pos
    linarith
  have hrawprod : 0 < (shiftedJacobi n (α + 1) β).eval x *
      (shiftedJacobi n (α + 2) β).eval x := by
    have hsq : 0 < ((shiftedJacobi n (α + 1) β).eval x) ^ 2 :=
      sq_pos_of_ne_zero hraw₁_ne
    have heq : ((n : ℝ) + α + β + 2) * x *
        (shiftedJacobi n (α + 2) β).eval x =
        (α + 1 + (α + β + 2 * (n : ℝ) + 2) * x) *
          (shiftedJacobi n (α + 1) β).eval x := by
      linarith
    have heqmul : ((n : ℝ) + α + β + 2) * x *
        ((shiftedJacobi n (α + 1) β).eval x *
          (shiftedJacobi n (α + 2) β).eval x) =
        (α + 1 + (α + β + 2 * (n : ℝ) + 2) * x) *
          ((shiftedJacobi n (α + 1) β).eval x) ^ 2 := by
      calc
        _ = (shiftedJacobi n (α + 1) β).eval x *
            (((n : ℝ) + α + β + 2) * x *
              (shiftedJacobi n (α + 2) β).eval x) := by ring
        _ = (shiftedJacobi n (α + 1) β).eval x *
            ((α + 1 + (α + β + 2 * (n : ℝ) + 2) * x) *
              (shiftedJacobi n (α + 1) β).eval x) := by rw [heq]
        _ = _ := by ring
    have hpositive : 0 < ((n : ℝ) + α + β + 2) * x *
        ((shiftedJacobi n (α + 1) β).eval x *
          (shiftedJacobi n (α + 2) β).eval x) := by
      rw [heqmul]
      exact mul_pos hB hsq
    exact pos_of_mul_pos_right hpositive (le_of_lt (mul_pos hA hx_pos))
  rw [hraw₁, hraw₂] at hrawprod
  simp only [eval_mul, eval_C] at hrawprod
  have hfactor : l₁ *
      (shiftedJacobiMonic n (α + 1) β).eval x *
      (l₂ * (shiftedJacobiMonic n (α + 2) β).eval x) =
      (l₁ * l₂) * ((shiftedJacobiMonic n (α + 1) β).eval x *
        (shiftedJacobiMonic n (α + 2) β).eval x) := by ring
  rw [hfactor] at hrawprod
  exact pos_of_mul_pos_right hrawprod (le_of_lt hlprod)

/-- A two-unit increase in the first Jacobi parameter moves every root past
the corresponding lower-parameter root. -/
theorem shiftedJacobiMonic_prec_alpha_add_two (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    Prec (shiftedJacobiMonic n α β)
      (shiftedJacobiMonic n (α + 2) β) := by
  cases n with
  | zero =>
      simpa using (prec_refl (f := (1 : ℝ[X])) (by simp) (by simp))
  | succ m =>
      let p₀ := shiftedJacobiMonic (m + 1) α β
      let p₁ := shiftedJacobiMonic (m + 1) (α + 1) β
      let p₂ := shiftedJacobiMonic (m + 1) (α + 2) β
      have hp₀_monic : p₀.Monic := by
        exact monic_shiftedJacobiMonic (m + 1) hα hβ
      have hp₁_monic : p₁.Monic := by
        exact monic_shiftedJacobiMonic (m + 1) (by linarith) hβ
      have hp₂_monic : p₂.Monic := by
        exact monic_shiftedJacobiMonic (m + 1) (by linarith) hβ
      have hp₀_pos : HasPosLeadingCoeff p₀ :=
        hasPosLeadingCoeff_of_monic hp₀_monic
      have hp₁_pos : HasPosLeadingCoeff p₁ :=
        hasPosLeadingCoeff_of_monic hp₁_monic
      have hp₂_pos : HasPosLeadingCoeff p₂ :=
        hasPosLeadingCoeff_of_monic hp₂_monic
      have hp₀_deg : p₀.natDegree = m + 1 := by
        exact natDegree_shiftedJacobiMonic (m + 1) hα hβ
      have hp₁_deg : p₁.natDegree = m + 1 := by
        exact natDegree_shiftedJacobiMonic (m + 1) (by linarith) hβ
      have hp₂_deg : p₂.natDegree = m + 1 := by
        exact natDegree_shiftedJacobiMonic (m + 1) (by linarith) hβ
      have hstrict : StrictPrecSameDegree p₀ p₁ := by
        exact shiftedJacobiMonic_strictPrec_alpha_add_one (m + 1) hα hβ
      have hroot_sign : ∀ x, p₀.IsRoot x → p₂.eval x * p₀.derivative.eval x < 0 := by
        intro x hx
        have hder_mid : p₀.derivative.eval x * p₁.eval x < 0 :=
          hstrict.derivative_mul_eval_neg hp₀_pos hp₁_pos hp₀_deg hp₁_deg hx
        have hmid_high : 0 < p₁.eval x * p₂.eval x := by
          exact shiftedJacobiMonic_eval_mul_alpha_add_one_two_pos
            (m + 1) hα hβ hx
        rcases mul_neg_iff.mp hder_mid with ⟨hder_pos, hmid_neg⟩ |
            ⟨hder_neg, hmid_pos⟩
        · rcases mul_pos_iff.mp hmid_high with ⟨hmid_pos, _⟩ |
              ⟨_, hhigh_neg⟩
          · linarith
          · exact mul_neg_of_neg_of_pos hhigh_neg hder_pos
        · rcases mul_pos_iff.mp hmid_high with ⟨_, hhigh_pos⟩ |
              ⟨hmid_neg, _⟩
          · exact mul_neg_of_pos_of_neg hhigh_pos hder_neg
          · linarith
      have hinter : Interlaces p₀.derivative p₀ :=
        interlaces_derivative_of_pos_natDegree hp₀_pos.ne_zero
          (shiftedJacobiMonic_splits (m + 1) hα hβ) hp₀_pos (by
            rw [hp₀_deg]
            lia)
      have hder_pos : HasPosLeadingCoeff p₀.derivative :=
        hp₀_pos.derivative (by rw [hp₀_deg]; lia)
      exact prec_of_interlaces_eval_mul_neg_same hinter hder_pos hp₂_pos
        (by rw [hp₂_deg, hp₀_deg]) hroot_sign

/-- The two-unit first-parameter comparison is strictly interleaving. -/
theorem shiftedJacobiMonic_strictPrec_alpha_add_two (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    StrictPrecSameDegree (shiftedJacobiMonic n α β)
      (shiftedJacobiMonic n (α + 2) β) := by
  apply StrictPrecSameDegree.of_prec_of_no_common
    (shiftedJacobiMonic_prec_alpha_add_two n hα hβ)
  · rw [natDegree_shiftedJacobiMonic n hα hβ,
      natDegree_shiftedJacobiMonic n (by linarith) hβ]
  · intro x hx hhigh
    have hpos := shiftedJacobiMonic_eval_mul_alpha_add_one_two_pos n hα hβ hx
    rw [Polynomial.IsRoot.def] at hhigh
    simp [hhigh] at hpos

/-- At a root of the degree-`m + 1` lower-parameter polynomial, the
degree-`m` polynomials at first-parameter shifts zero and two have the same
sign. -/
theorem shiftedJacobiMonic_eval_mul_alpha_add_two_degree_pred_pos (m : ℕ)
    {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (hx : (shiftedJacobiMonic (m + 1) α β).IsRoot x) :
    0 < (shiftedJacobiMonic m α β).eval x *
      (shiftedJacobiMonic m (α + 2) β).eval x := by
  let l₀ : ℝ := (-1 : ℝ) ^ m * Ring.choose (m + α + β + m) m
  let l₂ : ℝ := (-1 : ℝ) ^ m *
    Ring.choose (m + (α + 2) + β + m) m
  have hp₀ : 0 < Ring.choose (m + α + β + m) m := by
    cases m with
    | zero => simp
    | succ m =>
        apply Polynomial.ring_choose_pos
        push_cast
        linarith
  have hp₂ : 0 < Ring.choose (m + (α + 2) + β + m) m :=
    Polynomial.ring_choose_pos (by linarith)
  have hsign : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  have hlprod : 0 < l₀ * l₂ := by
    calc
      l₀ * l₂ = (((-1 : ℝ) ^ m) ^ 2) *
          Ring.choose (m + α + β + m) m *
          Ring.choose (m + (α + 2) + β + m) m := by
            simp only [l₀, l₂]
            ring
      _ > 0 := by positivity
  have hrawLow : (shiftedJacobi (m + 1) α β).IsRoot x := by
    rw [Polynomial.IsRoot.def] at hx ⊢
    rw [shiftedJacobi_eq_leading_mul_monic (m + 1) hα hβ]
    simp [hx]
  have hx_pos :=
    (shiftedJacobi_isRoot_mem_Ioo (m + 1) hα hβ hrawLow).1
  have hprev_ne : (shiftedJacobiMonic m α β).eval x ≠ 0 := by
    have hrec := shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ
    have hsub : ∀ k : ℕ, 0 < shiftedJacobiSubdiag (k + 1) α β := by
      intro k
      exact shiftedJacobiSubdiag_pos (k + 1) (by lia) hα hβ
    have hcommon := noCommonRoot_succ_of_favard hrec hsub m
    intro hzero
    exact hcommon x (by simpa only [Polynomial.IsRoot.def] using hzero) hx
  have hraw₀ : shiftedJacobi m α β =
      C l₀ * shiftedJacobiMonic m α β := by
    simpa only [l₀] using shiftedJacobi_eq_leading_mul_monic m hα hβ
  have hraw₂ : shiftedJacobi m (α + 2) β =
      C l₂ * shiftedJacobiMonic m (α + 2) β := by
    simpa only [l₂] using
      shiftedJacobi_eq_leading_mul_monic m (by linarith : -1 < α + 2) hβ
  have hl₀_ne : l₀ ≠ 0 := mul_ne_zero hsign hp₀.ne'
  have hraw₀_ne : (shiftedJacobi m α β).eval x ≠ 0 := by
    rw [hraw₀]
    simp only [eval_mul, eval_C]
    exact mul_ne_zero hl₀_ne hprev_ne
  have hid := congrArg (Polynomial.eval x)
    (Polynomial.shiftedJacobi_alpha_add_two_degree_pred m α β hα)
  rw [Polynomial.IsRoot.def] at hrawLow
  simp only [eval_add, eval_mul, eval_neg, eval_C, eval_pow, eval_X,
    hrawLow, mul_zero, zero_add] at hid
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  have hA : 0 < ((m : ℝ) + α + β + 2) *
      (α + β + 2 * (m : ℝ) + 2) := by
    have hA₁ : 0 < (m : ℝ) + α + β + 2 := by linarith
    have hA₂ : 0 < α + β + 2 * (m : ℝ) + 2 := by linarith
    exact mul_pos hA₁ hA₂
  have hc : 0 < (α + 1) * ((m : ℝ) + α + 1) := by
    have hα1 : 0 < α + 1 := by linarith
    have hmα1 : 0 < (m : ℝ) + α + 1 := by linarith
    exact mul_pos hα1 hmα1
  have heq : ((m : ℝ) + α + β + 2) *
      (α + β + 2 * (m : ℝ) + 2) * x ^ 2 *
        (shiftedJacobi m (α + 2) β).eval x =
      (α + 1) * ((m : ℝ) + α + 1) *
        (shiftedJacobi m α β).eval x := by
    nlinarith
  have hrawprod : 0 < (shiftedJacobi m α β).eval x *
      (shiftedJacobi m (α + 2) β).eval x := by
    have hsqPrev : 0 < ((shiftedJacobi m α β).eval x) ^ 2 :=
      sq_pos_of_ne_zero hraw₀_ne
    have hxSq : 0 < x ^ 2 := sq_pos_of_pos hx_pos
    have hleft : 0 < (((m : ℝ) + α + β + 2) *
        (α + β + 2 * (m : ℝ) + 2) * x ^ 2) *
          ((shiftedJacobi m α β).eval x *
            (shiftedJacobi m (α + 2) β).eval x) := by
      rw [show (((m : ℝ) + α + β + 2) *
          (α + β + 2 * (m : ℝ) + 2) * x ^ 2) *
            ((shiftedJacobi m α β).eval x *
              (shiftedJacobi m (α + 2) β).eval x) =
          (shiftedJacobi m α β).eval x *
            ((((m : ℝ) + α + β + 2) *
              (α + β + 2 * (m : ℝ) + 2) * x ^ 2) *
              (shiftedJacobi m (α + 2) β).eval x) by ring,
        heq]
      ring_nf
      nlinarith [mul_pos hc hsqPrev]
    exact pos_of_mul_pos_right hleft
      (le_of_lt (mul_pos hA hxSq))
  rw [hraw₀, hraw₂] at hrawprod
  simp only [eval_mul, eval_C] at hrawprod
  have hfactor : l₀ * (shiftedJacobiMonic m α β).eval x *
      (l₂ * (shiftedJacobiMonic m (α + 2) β).eval x) =
      (l₀ * l₂) * ((shiftedJacobiMonic m α β).eval x *
        (shiftedJacobiMonic m (α + 2) β).eval x) := by ring
  rw [hfactor] at hrawprod
  exact pos_of_mul_pos_right hrawprod (le_of_lt hlprod)

/-- Increasing the first Jacobi parameter by two in the degree-one interlacer
preserves strict interlacing with the higher-degree polynomial. -/
theorem shiftedJacobiMonic_interlaces_alpha_add_two_degree_pred (m : ℕ)
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    Interlaces (shiftedJacobiMonic m (α + 2) β)
      (shiftedJacobiMonic (m + 1) α β) := by
  let f := shiftedJacobiMonic (m + 1) α β
  let g := shiftedJacobiMonic m α β
  let F := shiftedJacobiMonic m (α + 2) β
  have hgf : Interlaces g f := by
    apply (shiftedJacobiMonic_prec_succ m hα hβ).toInterlaces
    rw [natDegree_shiftedJacobiMonic m hα hβ,
      natDegree_shiftedJacobiMonic (m + 1) hα hβ]
  obtain ⟨hf, hg, hdeg, rs, ss, hrs_sorted, hss_sorted,
    hrs_eq, hss_eq, hint⟩ := hgf
  have hrec := shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ
  have hsub : ∀ k : ℕ, 0 < shiftedJacobiSubdiag (k + 1) α β := by
    intro k
    exact shiftedJacobiSubdiag_pos (k + 1) (by lia) hα hβ
  have hcommon := noCommonRoot_succ_of_favard hrec hsub m
  have hrs_canonical : f.roots.sort (· ≤ ·) = rs := by
    rw [← hrs_eq, Multiset.coe_sort]
    exact List.mergeSort_eq_self (· ≤ ·) hrs_sorted
  have hF_ne : F ≠ 0 := shiftedJacobiMonic_ne_zero m (by linarith) hβ
  have hdeg_lt : F.natDegree < f.natDegree := by
    dsimp only [F, f]
    rw [natDegree_shiftedJacobiMonic m (by linarith) hβ,
      natDegree_shiftedJacobiMonic (m + 1) hα hβ]
    lia
  have hsign :
      let roots := f.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        roots = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    dsimp only
    intro pre r₁ r₂ rest hEq
    have hEq' : rs = pre ++ r₁ :: r₂ :: rest := hrs_canonical.symm.trans hEq
    have hr₁_root : f.IsRoot r₁ := by
      apply (Polynomial.mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr (by simp [hEq'])
    have hr₂_root : f.IsRoot r₂ := by
      apply (Polynomial.mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr (by simp [hEq'])
    have hg₁_ne : g.eval r₁ ≠ 0 := by
      intro hzero
      exact hcommon r₁ (by simpa only [Polynomial.IsRoot.def] using hzero)
        hr₁_root
    have hg₂_ne : g.eval r₂ ≠ 0 := by
      intro hzero
      exact hcommon r₂ (by simpa only [Polynomial.IsRoot.def] using hzero)
        hr₂_root
    have hg_nonpos : g.eval r₁ * g.eval r₂ ≤ 0 :=
      eval_mul_eval_nonpos_of_interlacing_consecutive hg.2 hrs_sorted
        hss_eq hint hEq'
    have hg_neg : g.eval r₁ * g.eval r₂ < 0 :=
      lt_of_le_of_ne hg_nonpos (mul_ne_zero hg₁_ne hg₂_ne)
    have hsame₁ : 0 < g.eval r₁ * F.eval r₁ := by
      exact shiftedJacobiMonic_eval_mul_alpha_add_two_degree_pred_pos
        m hα hβ hr₁_root
    have hsame₂ : 0 < g.eval r₂ * F.eval r₂ := by
      exact shiftedJacobiMonic_eval_mul_alpha_add_two_degree_pred_pos
        m hα hβ hr₂_root
    rcases mul_neg_iff.mp hg_neg with ⟨hg₁_pos, hg₂_neg⟩ |
        ⟨hg₁_neg, hg₂_pos⟩
    · have hF₁_pos : 0 < F.eval r₁ := by
        rcases mul_pos_iff.mp hsame₁ with ⟨_, hpos⟩ | ⟨hneg, _⟩
        · exact hpos
        · linarith
      have hF₂_neg : F.eval r₂ < 0 := by
        rcases mul_pos_iff.mp hsame₂ with ⟨hpos, _⟩ | ⟨_, hneg⟩
        · linarith
        · exact hneg
      exact mul_neg_of_pos_of_neg hF₁_pos hF₂_neg
    · have hF₁_neg : F.eval r₁ < 0 := by
        rcases mul_pos_iff.mp hsame₁ with ⟨hpos, _⟩ | ⟨_, hneg⟩
        · linarith
        · exact hneg
      have hF₂_pos : 0 < F.eval r₂ := by
        rcases mul_pos_iff.mp hsame₂ with ⟨_, hpos⟩ | ⟨hneg, _⟩
        · exact hpos
        · linarith
      exact mul_neg_of_neg_of_pos hF₁_neg hF₂_pos
  exact interlaces_of_consecutive_signs_of_natDegree_lt
    hf.1 hf.2 hF_ne hdeg_lt hsign

/-- Proper position form of the adjacent-degree two-unit endpoint. -/
theorem shiftedJacobiMonic_prec_alpha_add_two_degree_pred (m : ℕ)
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    Prec (shiftedJacobiMonic m (α + 2) β)
      (shiftedJacobiMonic (m + 1) α β) :=
  (shiftedJacobiMonic_interlaces_alpha_add_two_degree_pred m hα hβ).toPrec

end RealRooted
