/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import RealRooted.CenteredEulerian.ChangeBasis
public import RealRooted.CenteredEulerian.Basis

/-!
# The centered generating function and its Riccati equation

Ported from Aristotle task `61da6424-89ea-4fbf-852c-6e47d3e3aef9`,
following the compendium zig-zag proof, Appendix A.

For `c : ℝ`, `G_c(s) = √(1-s²) · (sec + tan)(c · arcsin s)` is the formal series
`qS * (rescale c eulerS).subst fS`; its coefficients are `p_n(c)`.  It satisfies the
Riccati equation `(1-s²) G' + s G = (c/2)(G² + 1 - s²)`, which determines it from
`G(0) = 1`, and the Möbius map `G ↦ (1-s²)(G+s)/(1-s²-sG)` sends solutions for `c`
to solutions for `c + 2`.
-/

@[expose] public section

open PowerSeries

namespace RealRooted.CenteredEulerian

local notation "D" => PowerSeries.derivative (R := ℝ)

/-- The Riccati equation with parameter `c`. -/
def Riccati (c : ℝ) (G : ℝ⟦X⟧) : Prop :=
  (1 - X ^ 2) * D G + X * G = C (c / 2) * (G ^ 2 + 1 - X ^ 2)

lemma coeff_sq_congr {G H : ℝ⟦X⟧} {m : ℕ} (h : ∀ i ≤ m, coeff i G = coeff i H) :
    coeff m (G ^ 2) = coeff m (H ^ 2) := by
  rw [pow_two, pow_two, coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl; intro p hp
  have := Finset.mem_antidiagonal.mp hp
  rw [h p.1 (by lia), h p.2 (by lia)]

lemma riccati_coeff {c : ℝ} {G : ℝ⟦X⟧} (hG : Riccati c G) (m : ℕ) :
    coeff (m + 1) G * (m + 1) = c / 2 * (coeff m (G ^ 2) + (if m = 0 then 1 else 0)
      - (if m = 2 then 1 else 0)) + (if 2 ≤ m then coeff (m - 1) G * (m - 1) else 0)
      - (if 1 ≤ m then coeff (m - 1) G else 0) := by
  have e := congrArg (coeff m) hG
  rw [map_add, coeff_one_sub_X_sq_mul, coeff_X_mul', coeff_C_mul, map_sub, map_add,
    coeff_one, coeff_X_pow] at e
  simp only [coeff_derivative] at e
  rcases m with _ | _ | _ | m
  · simp at e ⊢; linarith
  · simp at e ⊢; linarith
  · simp at e ⊢; norm_num at e ⊢; linarith
  · simp only [show ¬ (m + 1 + 1 + 1 = 0) by lia, show ¬ (m + 1 + 1 + 1 = 2) by lia,
      show 2 ≤ m + 1 + 1 + 1 by lia, show 1 ≤ m + 1 + 1 + 1 by lia, ite_true, ite_false,
      show m + 1 + 1 + 1 - 2 = m + 1 by lia, show m + 1 + 1 + 1 - 1 = m + 1 + 1 by lia]
      at e ⊢
    push_cast at e ⊢
    linarith

/-- Uniqueness of solutions of the Riccati equation. -/
theorem riccati_unique {c : ℝ} {G H : ℝ⟦X⟧} (hG : Riccati c G) (hH : Riccati c H)
    (h0 : constantCoeff G = constantCoeff H) : G = H := by
  have key : ∀ n, ∀ i ≤ n, coeff i G = coeff i H := by
    intro n
    induction n with
    | zero =>
      intro i hi
      rw [Nat.le_zero.mp hi, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
        h0]
    | succ m ih =>
      intro i hi
      rcases Nat.lt_or_ge i (m + 1) with h | h
      · exact ih i (by lia)
      have hi' : i = m + 1 := by lia
      subst hi'
      have eG := riccati_coeff hG m
      have eH := riccati_coeff hH m
      rw [coeff_sq_congr ih] at eG
      have hm1 : coeff (m - 1) G = coeff (m - 1) H := ih (m - 1) (by lia)
      rw [hm1] at eG
      have hne : (m : ℝ) + 1 ≠ 0 := by positivity
      have : coeff (m + 1) G * (m + 1) = coeff (m + 1) H * (m + 1) := by rw [eG, eH]
      exact mul_right_cancel₀ hne this
  ext n
  exact key n n le_rfl

/-! ### The Möbius step -/

lemma constantCoeff_mobiusDen (G : ℝ⟦X⟧) :
    constantCoeff (1 - X ^ 2 - X * G : ℝ⟦X⟧) = 1 := by
  simp

/-- If `G` solves the Riccati equation with parameter `c` and
`H · (1 - s² - sG) = (1 - s²)(G + s)`, then `H` solves it with parameter `c + 2`. -/
theorem riccati_mobius {c : ℝ} {G H : ℝ⟦X⟧} (hG : Riccati c G)
    (hH : H * (1 - X ^ 2 - X * G) = (1 - X ^ 2) * (G + X)) : Riccati (c + 2) H := by
  have hD := congrArg D hH
  have hDn : D (1 - X ^ 2 - X * G) = -2 * X - G - X * D G := by
    simp only [map_sub, Derivation.map_one_eq_zero, Derivation.leibniz_pow, Derivation.leibniz,
      derivative_X, smul_eq_mul]
    ring
  have hN : D ((1 - X ^ 2) * (G + X)) = -2 * X * (G + X) + (1 - X ^ 2) * (D G + 1) := by
    simp only [map_sub, map_add, Derivation.map_one_eq_zero, Derivation.leibniz_pow,
      Derivation.leibniz, derivative_X, smul_eq_mul]
    ring
  rw [Derivation.leibniz, hDn, hN, smul_eq_mul, smul_eq_mul] at hD
  have hne : (1 - X ^ 2 - X * G : ℝ⟦X⟧) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro h0
    have := constantCoeff_mobiusDen G
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hC : (C ((c + 2) / 2) : ℝ⟦X⟧) = C (c / 2) + 1 := by
    rw [show (c + 2) / 2 = c / 2 + 1 by ring, map_add, map_one]
  have key : (1 - X ^ 2 - X * G) ^ 2 *
      ((1 - X ^ 2) * D H + X * H - C ((c + 2) / 2) * (H ^ 2 + 1 - X ^ 2)) = 0 := by
    unfold Riccati at hG
    rw [hC]
    linear_combination (1 - X ^ 2) * (1 - X ^ 2 - X * G) * hD +
      (-(1 - X ^ 2) * (-2 * X - G - X * D G) + X * (1 - X ^ 2 - X * G) -
        (C (c / 2) + 1) * (H * (1 - X ^ 2 - X * G) + (1 - X ^ 2) * (G + X))) * hH +
      (1 - X ^ 2) * hG
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hne
  · unfold Riccati; exact sub_eq_zero.mp h

/-! ### The centered generating function -/

lemma derivative_secS : D secS = secS ^ 2 * sinS := by
  rw [secS, derivative_inv']
  have : D cosS = -sinS := derivative_cosS
  rw [this]; ring

/-- `E' = (E² + 1)/2` for `E = sec + tan`. -/
lemma derivative_eulerS : D eulerS = C (1 / 2 : ℝ) * (eulerS ^ 2 + 1) := by
  have h1 : secS * cosS = 1 := by rw [mul_comm]; exact cosS_mul_secS
  have h2 := sinS_sq_add_cosS_sq
  have hC : (C (1 / 2 : ℝ) : ℝ⟦X⟧) * 2 = 1 := by
    rw [show (2 : ℝ⟦X⟧) = C (2 : ℝ) from (map_ofNat C 2).symm, ← map_mul]; norm_num
  rw [eulerS, Derivation.leibniz, derivative_secS, smul_eq_mul, smul_eq_mul, map_add,
    Derivation.map_one_eq_zero, derivative_sinS, zero_add]
  linear_combination (-(secS ^ 2 * sinS * (1 + sinS) + secS * cosS)) * hC +
    (C (1 / 2 : ℝ)) * secS ^ 2 * h2 - (C (1 / 2 : ℝ)) * (secS * cosS - 1) * h1

/-- The centered generating function `G_c(s) = √(1-s²) (sec + tan)(c arcsin s)`. -/
noncomputable def gSeries (c : ℝ) : ℝ⟦X⟧ := qS * (rescale c eulerS).subst fS

lemma derivative_rescale (c : ℝ) (f : ℝ⟦X⟧) : D (rescale c f) = C c * rescale c (D f) := by
  ext n
  simp only [coeff_derivative, coeff_rescale, coeff_C_mul]
  ring

lemma rescale_C' (c a : ℝ) : rescale c (C a) = C a := by
  ext n
  simp only [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

lemma coeff_gSeries (c : ℝ) (n : ℕ) : coeff n (gSeries c) = (polynomial n).eval c := by
  rw [gSeries, coeff_qS_mul_subst_fS, eval_polynomial]
  apply Finset.sum_congr rfl; intro k _; rw [coeff_rescale, eulerCoeff]; ring

lemma constantCoeff_gSeries (c : ℝ) : constantCoeff (gSeries c) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_gSeries, polynomial_zero, Polynomial.eval_one]

lemma riccati_gSeries (c : ℝ) : Riccati c (gSeries c) := by
  have hf := constantCoeff_fS
  have hfs := hasSubst_of_cc_zero hf
  set Y := (rescale c eulerS).subst fS with hY
  have hcc : (C c : ℝ⟦X⟧) * C (1 / 2 : ℝ) = C (c / 2) := by rw [← map_mul]; ring_nf
  have hDY : D Y = C (c / 2) * (Y ^ 2 + 1) * invqS := by
    rw [hY, derivative_subst (R := ℝ) hfs, derivative_rescale, derivative_eulerS, derivative_fS,
      map_mul (rescale c), map_add, map_pow, map_one, rescale_C', ← coe_substAlgHom hfs,
      map_mul, map_mul, map_add, map_pow, map_one, coe_substAlgHom hfs,
      subst_C' _ hf, subst_C' _ hf, ← hcc]
    ring
  have hq := qS_ode
  rw [map_neg, map_one] at hq
  have hsq := qS_sq
  have hinv := qS_mul_invqS
  unfold Riccati
  rw [gSeries, ← hY, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  linear_combination Y * hq + (1 - X ^ 2) * qS * hDY +
    C (c / 2) * (1 - X ^ 2) * (Y ^ 2 + 1) * hinv - C (c / 2) * Y ^ 2 * hsq

lemma riccati_one_add_X : Riccati 1 (1 + X) := by
  unfold Riccati
  have hC : (C (1 / 2 : ℝ) : ℝ⟦X⟧) * 2 = 1 := by
    rw [show (2 : ℝ⟦X⟧) = C (2 : ℝ) from (map_ofNat C 2).symm, ← map_mul]; norm_num
  simp only [map_add, Derivation.map_one_eq_zero, derivative_X, zero_add]
  linear_combination (-(1 + X : ℝ⟦X⟧)) * hC

/-- A sequence starting at `1 + s` and following the Möbius recursion is `G_{2k+1}`. -/
theorem eq_gSeries_of_mobius (H : ℕ → ℝ⟦X⟧) (h0 : H 0 = 1 + X)
    (hstep : ∀ k, H (k + 1) * (1 - X ^ 2 - X * H k) = (1 - X ^ 2) * (H k + X)) (k : ℕ) :
    H k = gSeries (2 * k + 1) := by
  have hR : ∀ k : ℕ, Riccati (2 * (k : ℝ) + 1) (H k) ∧ constantCoeff (H k) = 1 := by
    intro k
    induction k with
    | zero =>
      rw [h0]; refine ⟨by simpa using riccati_one_add_X, by simp⟩
    | succ k ih =>
      refine ⟨?_, ?_⟩
      · have := riccati_mobius ih.1 (hstep k)
        have e : (2 * ((k + 1 : ℕ) : ℝ) + 1) = 2 * k + 1 + 2 := by push_cast; ring
        rw [e]; exact this
      · have := congrArg constantCoeff (hstep k)
        simpa [ih.2] using this
  exact riccati_unique (hR k).1 (riccati_gSeries _) (by rw [(hR k).2, constantCoeff_gSeries])

end RealRooted.CenteredEulerian
