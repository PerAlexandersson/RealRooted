/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CenteredEulerian.HBound
public import RealRooted.CenteredEulerian.RootCriterion
public import RealRooted.CenteredEulerian.Coefficients

/-!
# The exact change-of-basis formula (B.6)
Ported from Aristotle task `61da6424-89ea-4fbf-852c-6e47d3e3aef9`,
following the compendium zig-zag proof, Appendix B.
-/

@[expose] public section

open PowerSeries

namespace RealRooted.CenteredEulerian

lemma subst_X_right (g : ℝ⟦X⟧) : g.subst (X : ℝ⟦X⟧) = g := by
  ext i
  rw [coeff_subst_eq_sum constantCoeff_X g (le_refl i)]
  simp [coeff_X_pow]

lemma coeff_sinS_pow_self (m : ℕ) : coeff m (sinS ^ m) = 1 := by
  rw [sinS_eq_X_mul, mul_pow, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
    coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_sT, one_pow]

lemma subst_sinS_injective {g g' : ℝ⟦X⟧} (h : g.subst sinS = g'.subst sinS) : g = g' := by
  have hs := constantCoeff_sinS
  ext m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have h1 := congrArg (coeff m) h
    rw [coeff_subst_eq_sum hs g (le_refl m), coeff_subst_eq_sum hs g' (le_refl m),
      Finset.sum_range_succ, Finset.sum_range_succ, coeff_sinS_pow_self] at h1
    have h2 : ∑ j ∈ Finset.range m, coeff j g * coeff m (sinS ^ j) =
        ∑ j ∈ Finset.range m, coeff j g' * coeff m (sinS ^ j) := by
      apply Finset.sum_congr rfl; intro j hj
      rw [ih j (Finset.mem_range.mp hj)]
    linarith

lemma sinS_subst_fS : sinS.subst fS = X := by
  have hs := constantCoeff_sinS
  have hf := constantCoeff_fS
  apply subst_sinS_injective
  rw [subst_comp_subst_apply (hasSubst_of_cc_zero hf) (hasSubst_of_cc_zero hs), fS_subst_sinS,
    subst_X_right, subst_X' _ hs]

lemma secS_subst_fS : secS.subst fS = invqS := by
  have hf := constantCoeff_fS
  rw [← invqS_subst_sinS, subst_comp_subst_apply (hasSubst_of_cc_zero constantCoeff_sinS)
    (hasSubst_of_cc_zero hf), sinS_subst_fS, subst_X_right]

/-- `w(z) = (sec z - cos z)/z² = sec z sin² z / z²`. -/
noncomputable def wS : ℝ⟦X⟧ := mk (fun k => coeff (k + 2) (secS * sinS ^ 2))

lemma secS_mul_sinS_sq : secS * sinS ^ 2 = X ^ 2 * wS := by
  ext n
  rw [coeff_X_pow_mul']
  split_ifs with hn
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by lia⟩
    rw [wS, coeff_mk, Nat.add_sub_cancel]
  · rw [sinS_eq_X_mul, mul_pow, mul_left_comm, coeff_X_pow_mul', ite_eq_right (by lia)]

/-- `φ_{jk} = β_{j+2,k+2} = [z^k] w(z) sin^j z`. -/
noncomputable def phi (j k : ℕ) : ℝ := beta (j + 2) (k + 2)

lemma phi_eq (j k : ℕ) : phi j k = coeff k (wS * sinS ^ j) := by
  have : secS * sinS ^ (j + 2) = X ^ 2 * (wS * sinS ^ j) := by
    calc secS * sinS ^ (j + 2) = (secS * sinS ^ 2) * sinS ^ j := by ring
      _ = _ := by rw [secS_mul_sinS_sq]; ring
  rw [phi, beta, this, coeff_X_pow_mul', ite_eq_left (by lia), Nat.add_sub_cancel]

lemma qS_mul_wS_subst_fS : qS * wS.subst fS = hS := by
  have hf := constantCoeff_fS
  have hfs := hasSubst_of_cc_zero hf
  have key : X ^ 2 * (qS * wS.subst fS * AtS) = X ^ 2 * 1 := by
    have h1 := congrArg (fun g => g.subst fS) secS_mul_sinS_sq
    rw [subst_mul hfs, subst_mul hfs, subst_pow hfs, subst_pow hfs, sinS_subst_fS,
      secS_subst_fS, subst_X' _ hf] at h1
    calc X ^ 2 * (qS * wS.subst fS * AtS) = qS * (fS ^ 2 * wS.subst fS) := by
          rw [fS_sq_eq]; ring
      _ = qS * (invqS * X ^ 2) := by rw [h1]
      _ = X ^ 2 * 1 := by rw [← mul_assoc, qS_mul_invqS]; ring
  have hX : (X : ℝ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
  have h2 := mul_left_cancel₀ hX key
  calc qS * wS.subst fS = qS * wS.subst fS * (AtS * hS) := by rw [AtS_mul_hS, mul_one]
    _ = hS := by rw [← mul_assoc, h2, one_mul]

/-- Coefficients of `q(s) G(f(s))` in terms of `α`. -/
lemma coeff_qS_mul_subst_fS (G : ℝ⟦X⟧) (n : ℕ) :
    coeff n (qS * G.subst fS) = ∑ k ∈ Finset.range (n + 1), alpha n k * coeff k G := by
  rw [coeff_mul_subst constantCoeff_fS]
  apply Finset.sum_congr rfl; intro k _; rw [alpha]; ring

/-- `∑_k α_{nk} φ_{jk} = [s^n] h(s) s^j`. -/
lemma sum_alpha_mul_phi (n j : ℕ) :
    ∑ k ∈ Finset.range (n + 1), alpha n k * phi j k = coeff n (hS * X ^ j) := by
  have hf := constantCoeff_fS
  have hfs := hasSubst_of_cc_zero hf
  simp_rw [phi_eq]
  rw [← coeff_qS_mul_subst_fS, subst_mul hfs, subst_pow hfs, sinS_subst_fS, ← mul_assoc,
    qS_mul_wS_subst_fS]

lemma constantCoeff_wS : constantCoeff wS = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, wS, coeff_mk, ← beta, beta_self]

lemma isEvenPS_wS : IsEvenPS wS := isEvenPS_of_coeff (fun n hn => by
  rw [wS, coeff_mk, ← beta]
  exact beta_parity (by
    rcases hn with ⟨r, rfl⟩
    simp [Nat.even_add, parity_simps]))

lemma phi_zero (j : ℕ) : phi j 0 = if j = 0 then 1 else 0 := by
  rw [phi_eq]
  split_ifs with hj
  · subst hj; rw [pow_zero, mul_one, coeff_zero_eq_constantCoeff_apply, constantCoeff_wS]
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by lia⟩
    rw [coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, constantCoeff_sinS, zero_pow (by lia),
      mul_zero]

lemma phi_one (j : ℕ) : phi j 1 = if j = 1 then 1 else 0 := by
  rw [phi_eq]
  split_ifs with hj
  · subst hj
    rw [pow_one, coeff_mul, Finset.Nat.antidiagonal_succ]
    simp [coeff_sinS, constantCoeff_wS]
  · rcases Nat.lt_or_ge j 2 with h | h
    · have : j = 0 := by lia
      subst this
      rw [pow_zero, mul_one]; exact isEvenPS_wS.coeff_odd (by decide)
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by lia⟩
      rw [sinS_eq_X_mul, mul_pow, mul_left_comm, coeff_X_pow_mul', ite_eq_right (by lia)]

lemma alpha_zero_eq (n : ℕ) : alpha n 0 = coeff n qS := by rw [alpha, pow_zero, mul_one]

lemma alpha_one_eq (n : ℕ) : alpha n 1 = coeff n (qS * fS) := by rw [alpha, pow_one]

/-- The decomposition (B.6) of the matrix entries `R_{ij}`. -/
theorem rMat_decomp (i j : ℕ) :
    rMat i j = aConst * coeff (i + 2) (hS * X ^ j)
      + (if j = 0 then (2 - aConst) * coeff (i + 2) qS else 0)
      + (if j = 1 then (3 - aConst) * coeff (i + 2) (qS * fS) else 0)
      + ∑ k ∈ Finset.range (i + 1), (eulerRatio (k + 2) - aConst) * alpha (i + 2) (k + 2) *
          phi j (k + 2) := by
  have hm : rMat i j =
      ∑ k ∈ Finset.range (i + 3), eulerRatio k * alpha (i + 2) k * phi j k := by
    rw [rMat, mMat]; rfl
  have split3 : ∀ f : ℕ → ℝ, ∑ k ∈ Finset.range (i + 3), f k =
      f 0 + f 1 + ∑ k ∈ Finset.range (i + 1), f (k + 2) := by
    intro f
    rw [show i + 3 = i + 1 + 1 + 1 by ring, Finset.sum_range_succ', Finset.sum_range_succ']
    ring
  rw [hm, ← sum_alpha_mul_phi, show i + 2 + 1 = i + 3 by ring, split3, split3]
  rw [phi_zero, phi_one, eulerRatio_zero, eulerRatio_one, alpha_zero_eq, alpha_one_eq]
  have hsplit : ∀ k ∈ Finset.range (i + 1), eulerRatio (k + 2) * alpha (i + 2) (k + 2) *
      phi j (k + 2) = aConst * (alpha (i + 2) (k + 2) * phi j (k + 2)) +
        (eulerRatio (k + 2) - aConst) * alpha (i + 2) (k + 2) * phi j (k + 2) :=
    fun k _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  split_ifs with h0 h1 h1 <;> first | lia | ring

end RealRooted.CenteredEulerian
