/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CenteredEulerian.Basis

/-!
# Coefficients of `1/q`, `f/q`, `q`, `q f`, `(f/s)²` and `h = (s/f)²`

Ported from Aristotle task `61da6424-89ea-4fbf-852c-6e47d3e3aef9`,
following the compendium zig-zag proof, Appendix B.

All facts here are finite (formal) computations.
-/

@[expose] public section

open PowerSeries

namespace RealRooted.CenteredEulerian

local notation "D" => PowerSeries.derivative (R := ℝ)

/-- Sequences with `s (m+2) = (m+1)/(m+2) s m` are nonnegative and decrease along parity. -/
lemma rec_seq_props (s : ℕ → ℝ) (hrec : ∀ m, s (m + 2) = (m + 1) / (m + 2) * s m)
    (h0 : 0 ≤ s 0) (h1 : 0 ≤ s 1) : ∀ m, 0 ≤ s m ∧ s (m + 2) ≤ s m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  have hm : 0 ≤ s m := by
    rcases m with _ | _ | m
    · exact h0
    · exact h1
    · rw [hrec]; have := (ih m (by lia)).1; positivity
  refine ⟨hm, ?_⟩
  rw [hrec]
  have : (m + 1 : ℝ) / (m + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  nlinarith

/-! ### `1/q` -/

/-- Coefficients of `1/q`. -/
noncomputable def ic (n : ℕ) : ℝ := coeff n invqS

lemma ic_zero : ic 0 = 1 := by rw [ic, coeff_zero_eq_constantCoeff_apply, constantCoeff_invqS]

lemma ic_one : ic 1 = 0 := isEvenPS_invqS.coeff_odd (by decide)

lemma ic_rec (m : ℕ) : ic (m + 2) = (m + 1) / (m + 2) * ic m := by
  have h := congrArg (coeff (m + 1)) invqS_ode
  rw [coeff_one_sub_X_sq_mul, mul_assoc, coeff_C_mul, coeff_X_mul', coeff_derivative] at h
  simp only [one_mul, show 1 ≤ m + 1 by lia, ite_true, show m + 1 - 1 = m by lia] at h
  rw [ic, ic]
  rcases m with _ | m
  · simp at h; rw [coeff_zero_eq_constantCoeff_apply]; field_simp; push_cast at h ⊢; linarith
  · simp only [show 2 ≤ m + 1 + 1 by lia, ite_true, show m + 1 + 1 - 2 = m by lia,
      coeff_derivative] at h
    push_cast at h ⊢
    field_simp
    linarith

lemma ic_props (m : ℕ) : 0 ≤ ic m ∧ ic (m + 2) ≤ ic m :=
  rec_seq_props ic ic_rec (by rw [ic_zero]; norm_num) (by rw [ic_one]) m

lemma ic_le_one (m : ℕ) : ic m ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases m with _ | _ | m
  · rw [ic_zero]
  · rw [ic_one]; norm_num
  · exact (ic_props m).2.trans (ih m (by lia))

/-! ### `f = arcsin` -/

lemma coeff_fS_succ (n : ℕ) : coeff (n + 1) fS = ic n / (n + 1) := by
  rw [fS, coeff_mk, fc, ic]

lemma coeff_fS_zero : coeff 0 fS = 0 := by rw [fS, coeff_mk, fc]

lemma coeff_fS_nonneg (n : ℕ) : 0 ≤ coeff n fS := by
  rcases n with _ | n
  · rw [coeff_fS_zero]
  · rw [coeff_fS_succ]; have := (ic_props n).1; positivity

lemma coeff_fS_one : coeff 1 fS = 1 := by rw [coeff_fS_succ, ic_zero]; norm_num

/-! ### `u = f/q` -/

/-- `u = f/q = f · (1/q)`. -/
noncomputable def uS : ℝ⟦X⟧ := fS * invqS

lemma one_sub_X_sq_mul_invqS_sq : (1 - X ^ 2) * invqS ^ 2 = 1 := by
  rw [← qS_sq, ← mul_pow, qS_mul_invqS, one_pow]

lemma uS_ode : (1 - X ^ 2) * D uS = 1 + X * uS := by
  rw [uS, Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_fS]
  have h := invqS_ode
  rw [map_one, one_mul] at h
  calc (1 - X ^ 2) * (fS * D invqS + invqS * invqS)
      = fS * ((1 - X ^ 2) * D invqS) + (1 - X ^ 2) * invqS ^ 2 := by ring
    _ = 1 + X * (fS * invqS) := by rw [h, one_sub_X_sq_mul_invqS_sq]; ring

/-- Coefficients of `u`. -/
noncomputable def uc (n : ℕ) : ℝ := coeff n uS

lemma uc_zero : uc 0 = 0 := by
  rw [uc, uS, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_fS, zero_mul]

lemma uc_one : uc 1 = 1 := by
  have h := congrArg (coeff 0) uS_ode
  rw [coeff_one_sub_X_sq_mul, coeff_derivative, map_add, coeff_one, coeff_X_mul'] at h
  simp at h
  rw [uc]; linarith

lemma uc_rec (m : ℕ) : uc (m + 2) = (m + 1) / (m + 2) * uc m := by
  have h := congrArg (coeff (m + 1)) uS_ode
  rw [coeff_one_sub_X_sq_mul, coeff_derivative, map_add, coeff_one, coeff_X_mul'] at h
  simp only [show m + 1 ≠ 0 by lia, ite_false, zero_add, show 1 ≤ m + 1 by lia, ite_true,
    show m + 1 - 1 = m by lia] at h
  rw [uc, uc]
  rcases m with _ | m
  · simp at h; rw [coeff_zero_eq_constantCoeff_apply]; field_simp; push_cast at h ⊢; linarith
  · simp only [show 2 ≤ m + 1 + 1 by lia, ite_true, show m + 1 + 1 - 2 = m by lia,
      coeff_derivative] at h
    push_cast at h ⊢
    field_simp
    linarith

lemma uc_props (m : ℕ) : 0 ≤ uc m ∧ uc (m + 2) ≤ uc m :=
  rec_seq_props uc uc_rec (by rw [uc_zero]) (by rw [uc_one]; norm_num) m

lemma uc_le_one (m : ℕ) : uc m ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases m with _ | _ | m
  · rw [uc_zero]; norm_num
  · rw [uc_one]
  · exact (uc_props m).2.trans (ih m (by lia))

lemma uc_two : uc 2 = 0 := by rw [uc_rec, uc_zero, mul_zero]
lemma uc_three : uc 3 = 2 / 3 := by rw [uc_rec, uc_one]; norm_num

/-! ### `q` and `q f` -/

lemma qS_eq : qS = (1 - X ^ 2) * invqS := by
  rw [← qS_sq, pow_two, mul_assoc, qS_mul_invqS, mul_one]

lemma coeff_qS_eq (n : ℕ) : coeff n qS = ic n - (if 2 ≤ n then ic (n - 2) else 0) := by
  rw [qS_eq, coeff_one_sub_X_sq_mul, ic, ic]

lemma qS_mul_fS_eq : qS * fS = (1 - X ^ 2) * uS := by
  rw [qS_eq, uS]; ring

lemma coeff_qf_eq (n : ℕ) :
    coeff n (qS * fS) = uc n - (if 2 ≤ n then uc (n - 2) else 0) := by
  rw [qS_mul_fS_eq, coeff_one_sub_X_sq_mul, uc, uc]

/-- `∑_{n=1}^{K} |q_n| ≤ 1`. -/
lemma sum_abs_coeff_qS_le (K : ℕ) :
    ∑ n ∈ Finset.range K, |coeff (n + 1) qS| ≤ 1 := by
  have key : ∀ K, ∑ n ∈ Finset.range (K + 1), |coeff (n + 1) qS| = 1 - ic K - ic (K + 1) := by
    intro K
    induction K with
    | zero => simp [ic_zero, ic_one, coeff_qS_eq]
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, coeff_qS_eq]
      simp only [show 2 ≤ K + 1 + 1 by lia, ite_true, show K + 1 + 1 - 2 = K by lia]
      have := (ic_props K).2
      rw [abs_of_nonpos (by linarith)]
      ring
  have h1 : ∑ n ∈ Finset.range K, |coeff (n + 1) qS| ≤
      ∑ n ∈ Finset.range (K + 1), |coeff (n + 1) qS| :=
    Finset.sum_le_sum_of_subset_of_nonneg (by simp) (fun _ _ _ => abs_nonneg _)
  rw [key] at h1
  have := (ic_props K).1; have := (ic_props (K + 1)).1
  linarith

/-- `∑_{n=2}^{K+1} |(qf)_n| ≤ 1`. -/
lemma sum_abs_coeff_qf_le (K : ℕ) :
    ∑ n ∈ Finset.range K, |coeff (n + 2) (qS * fS)| ≤ 1 := by
  have key : ∀ K, ∑ n ∈ Finset.range K, |coeff (n + 2) (qS * fS)| =
      uc 0 + uc 1 - uc K - uc (K + 1) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, coeff_qf_eq]
      simp only [show 2 ≤ K + 2 by lia, ite_true, show K + 2 - 2 = K by lia]
      have := (uc_props K).2
      rw [abs_of_nonpos (by linarith)]
      ring
  rw [key, uc_zero, uc_one]
  have := (uc_props K).1; have := (uc_props (K + 1)).1
  linarith

lemma coeff_qS_two : coeff 2 qS = -1 / 2 := by
  rw [coeff_qS_eq, ite_eq_left le_rfl, ic_rec, ic_zero]; norm_num

lemma coeff_qf_three : coeff 3 (qS * fS) = -1 / 3 := by
  rw [coeff_qf_eq, ite_eq_left (by norm_num), uc_three, uc_one]; norm_num

lemma coeff_qf_two : coeff 2 (qS * fS) = 0 := by
  rw [coeff_qf_eq, ite_eq_left le_rfl, uc_two, uc_zero]; norm_num

/-! ### `(f/s)²` and `h = (s/f)²` -/

/-- `Ã = (f/s)²`. -/
noncomputable def AtS : ℝ⟦X⟧ := fT ^ 2

lemma fS_sq_eq : fS ^ 2 = X ^ 2 * AtS := by rw [fS_eq_X_mul, AtS]; ring

lemma derivative_fS_sq : D (fS ^ 2) = 2 * uS := by
  rw [sq_deriv, derivative_fS, uS]; ring

lemma coeff_AtS (m : ℕ) : coeff m AtS = 2 * uc (m + 1) / (m + 2) := by
  have h := congrArg (coeff (m + 1)) derivative_fS_sq
  rw [coeff_derivative, fS_sq_eq, coeff_X_pow_mul', ite_eq_left (by lia)] at h
  rw [show m + 1 + 1 - 2 = m by lia] at h
  rw [show (2 : ℝ⟦X⟧) = C 2 by simp [map_ofNat], coeff_C_mul] at h
  rw [uc]
  field_simp
  push_cast at h
  linarith

lemma coeff_AtS_nonneg (m : ℕ) : 0 ≤ coeff m AtS := by
  rw [coeff_AtS]; have := (uc_props (m + 1)).1; positivity

lemma coeff_AtS_le_one (m : ℕ) : coeff m AtS ≤ 1 := by
  rw [coeff_AtS, div_le_one (by positivity)]
  have := uc_le_one (m + 1); have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma constantCoeff_AtS : constantCoeff AtS = 1 := by
  rw [AtS, map_pow, constantCoeff_fT, one_pow]

lemma isEvenPS_AtS : IsEvenPS AtS := isEvenPS_of_coeff (fun n hn => by
  rw [coeff_AtS]
  obtain ⟨r, rfl⟩ := hn
  have : uc (2 * r + 1 + 1) = 0 := by
    rw [show 2 * r + 1 + 1 = 2 * (r + 1) by ring]
    have : ∀ t, uc (2 * t) = 0 := by
      intro t; induction t with
      | zero => exact uc_zero
      | succ t ih => rw [show 2 * (t + 1) = 2 * t + 2 by ring, uc_rec, ih, mul_zero]
    exact this _
  rw [this]; simp)

/-- `h = (s/f)²`. -/
noncomputable def hS : ℝ⟦X⟧ := AtS⁻¹

lemma AtS_mul_hS : AtS * hS = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_AtS]; norm_num)

lemma isEvenPS_hS : IsEvenPS hS := isEvenPS_AtS.inv (by rw [constantCoeff_AtS]; norm_num)

lemma coeff_hS_zero : coeff 0 hS = 1 := by
  have := congrArg constantCoeff AtS_mul_hS
  rw [map_mul, constantCoeff_AtS, one_mul, map_one] at this
  rw [coeff_zero_eq_constantCoeff_apply, this]

/-- The ratio recursion `A_{n+1} = r_n A_n` in the even variable. -/
noncomputable def rRat (n : ℕ) : ℝ := 2 * ((n : ℝ) + 1) ^ 2 / ((n + 2) * (2 * n + 3))

lemma coeff_AtS_even_succ (n : ℕ) :
    coeff (2 * (n + 1)) AtS = rRat n * coeff (2 * n) AtS := by
  rw [coeff_AtS, coeff_AtS, rRat, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, uc_rec]
  push_cast
  field_simp
  ring

lemma rRat_mono : Monotone rRat := by
  apply monotone_nat_of_le_succ
  intro n
  rw [rRat, rRat, div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [sq_nonneg ((n : ℝ)), mul_nonneg this (sq_nonneg (n : ℝ))]

lemma coeff_AtS_even_pos (n : ℕ) : 0 < coeff (2 * n) AtS := by
  induction n with
  | zero => rw [mul_zero, coeff_zero_eq_constantCoeff_apply, constantCoeff_AtS]; norm_num
  | succ n ih =>
    rw [coeff_AtS_even_succ]
    have : 0 < rRat n := by rw [rRat]; positivity
    positivity

/-- Abstract nonnegativity argument (B.4). -/
lemma nonneg_of_ratio (A e r : ℕ → ℝ) (hA0 : A 0 = 1) (hpos : ∀ n, 0 < A n)
    (hrat : ∀ n, A (n + 1) = r n * A n) (hmono : Monotone r)
    (hprod : ∀ n, A (n + 1) = ∑ j ∈ Finset.range (n + 1), e (j + 1) * A (n - j)) :
    ∀ n, 0 ≤ e (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | n
  · have hfirst : A 1 = e 1 := by simpa [hA0] using hprod 0
    rw [← hfirst]
    exact (hpos 1).le
  · have h1 := hprod (n + 1)
    rw [Finset.sum_range_succ, show n + 1 - (n + 1) = 0 by lia, hA0, mul_one] at h1
    have h2 : A (n + 1 + 1) =
        r (n + 1) * ∑ j ∈ Finset.range (n + 1), e (j + 1) * A (n - j) := by
      rw [hrat, hprod n]
    have h3 : ∀ j ∈ Finset.range (n + 1), e (j + 1) * A (n + 1 - j) =
        e (j + 1) * (r (n - j) * A (n - j)) := by
      intro j hj
      simp at hj
      rw [show n + 1 - j = (n - j) + 1 by lia, hrat]
    rw [Finset.sum_congr rfl h3] at h1
    have he : e (n + 1 + 1) = ∑ j ∈ Finset.range (n + 1),
        e (j + 1) * A (n - j) * (r (n + 1) - r (n - j)) := by
      rw [Finset.mul_sum] at h2
      have : ∑ j ∈ Finset.range (n + 1), e (j + 1) * A (n - j) * (r (n + 1) - r (n - j)) =
          ∑ j ∈ Finset.range (n + 1), r (n + 1) * (e (j + 1) * A (n - j)) -
          ∑ j ∈ Finset.range (n + 1), e (j + 1) * (r (n - j) * A (n - j)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      rw [this]
      linarith
    rw [he]
    apply Finset.sum_nonneg
    intro j hj
    simp at hj
    have := ih j (by lia)
    have := hpos (n - j)
    have : r (n - j) ≤ r (n + 1) := hmono (by lia)
    have : 0 ≤ r (n + 1) - r (n - j) := by linarith
    positivity

/-- `e_n = -h_{2n}`. -/
noncomputable def eh (n : ℕ) : ℝ := -coeff (2 * n) hS

lemma prod_identity (n : ℕ) :
    coeff (2 * (n + 1)) AtS =
      ∑ j ∈ Finset.range (n + 1), eh (j + 1) * coeff (2 * (n - j)) AtS := by
  have h := congrArg (coeff (2 * (n + 1))) AtS_mul_hS
  rw [coeff_mul, coeff_one, ite_eq_right (by lia)] at h
  -- reduce the antidiagonal sum to even pairs
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have hsplit : ∀ i ∈ Finset.range (2 * (n + 1) + 1),
      coeff i AtS * coeff (2 * (n + 1) - i) hS =
      if Even i then coeff i AtS * coeff (2 * (n + 1) - i) hS else 0 := by
    intro i hi
    split_ifs with he
    · rfl
    · rw [isEvenPS_AtS.coeff_odd (Nat.not_even_iff_odd.mp he), zero_mul]
  simp only at h
  rw [Finset.sum_congr rfl hsplit] at h
  -- reindex even i = 2t
  have hre : ∑ i ∈ Finset.range (2 * (n + 1) + 1),
      (if Even i then coeff i AtS * coeff (2 * (n + 1) - i) hS else 0) =
      ∑ t ∈ Finset.range (n + 2), coeff (2 * t) AtS * coeff (2 * (n + 1 - t)) hS := by
    rw [← Finset.sum_filter]
    apply Finset.sum_nbij' (fun i => i / 2) (fun t => 2 * t)
    · intro i hi; simp at hi ⊢; lia
    · intro t ht; simp at ht ⊢; lia
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨r, hr⟩ := hi.2
      lia
    · intro t _; lia
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨r, hr⟩ := hi.2
      rw [show i / 2 = r by lia, show 2 * (n + 1 - r) = 2 * (n + 1) - i by lia,
        show 2 * r = i by lia]
  rw [hre, Finset.sum_range_succ, show n + 1 - (n + 1) = 0 by lia, mul_zero,
    coeff_hS_zero, mul_one] at h
  -- the remaining sum, reversed
  have hrev : ∑ t ∈ Finset.range (n + 1), coeff (2 * t) AtS * coeff (2 * (n + 1 - t)) hS =
      -∑ j ∈ Finset.range (n + 1), eh (j + 1) * coeff (2 * (n - j)) AtS := by
    rw [← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp at hj
    rw [eh, show n + 1 - 1 - j = n - j by lia, show n + 1 - (n - j) = j + 1 by lia]
    ring
  rw [hrev] at h
  linarith

lemma eh_nonneg (n : ℕ) : 0 ≤ eh (n + 1) :=
  nonneg_of_ratio (fun n => coeff (2 * n) AtS) eh rRat
    (by simp only [mul_zero]; rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_AtS])
    coeff_AtS_even_pos coeff_AtS_even_succ rRat_mono prod_identity n

lemma eh_le (n : ℕ) : eh (n + 1) ≤ coeff (2 * (n + 1)) AtS := by
  rw [prod_identity, Finset.sum_range_succ, Nat.sub_self, mul_zero,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_AtS, mul_one]
  have h1 : 0 ≤ ∑ j ∈ Finset.range n, eh (j + 1) * coeff (2 * (n - j)) AtS :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (eh_nonneg _) (coeff_AtS_nonneg _))
  linarith

lemma coeff_hS_le_zero {n : ℕ} (hn : 1 ≤ n) : coeff n hS ≤ 0 := by
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ho
  · obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by lia⟩
    have := eh_nonneg t
    rw [eh, show 2 * (t + 1) = n by lia] at this
    linarith
  · rw [isEvenPS_hS.coeff_odd ho]

lemma abs_coeff_hS_le_one (n : ℕ) : |coeff n hS| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [coeff_hS_zero]; norm_num
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ho
  · obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by lia⟩
    have h1 := eh_nonneg t
    have h2 := eh_le t
    have h3 := coeff_AtS_le_one (2 * (t + 1))
    rw [eh, show 2 * (t + 1) = n by lia] at h1 h2
    rw [show 2 * (t + 1) = n by lia] at h3
    rw [abs_le]; constructor <;> linarith
  · rw [isEvenPS_hS.coeff_odd ho]; norm_num

lemma coeff_hS_two : coeff 2 hS = -1 / 3 := by
  have h := prod_identity 0
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, Nat.sub_zero, mul_zero,
    mul_one] at h
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_AtS, mul_one, coeff_AtS, uc_three] at h
  rw [eh, mul_one] at h
  norm_num at h
  linarith

end RealRooted.CenteredEulerian
