import RealRooted.Hadamard.Kostov.BernsteinRoots

open Polynomial

noncomputable section

namespace RealRooted
namespace Kostov

/-! ## Tangent polynomials -/

/-- `W_v = ∑ v_i X^(n-2-i)`. -/
def Wv (n : ℕ) (v : Fin (n - 1) → ℝ) : ℝ[X] :=
  ∑ i : Fin (n - 1), C (v i) * X ^ (n - 2 - i.1)

/-- The tangent polynomial `T_v = (X+1) W_v`. -/
def Tv (n : ℕ) (v : Fin (n - 1) → ℝ) : ℝ[X] := (X + 1) * Wv n v

/-- The Bernstein-side polynomial `G_v(y) = (1-y)^n T_v(y/(1-y))`. -/
def Gv (n : ℕ) (v : Fin (n - 1) → ℝ) : ℝ[X] :=
  ∑ i : Fin (n - 1), C (v i) * X ^ (n - 2 - i.1) * (1 - X) ^ (i.1 + 1)

lemma monicPolynomial_sub (n : ℕ) (v : Fin (n - 1) → ℝ) :
    monicPolynomial n v - monicPolynomial n 0 = Tv n v := by
  simp only [monicPolynomial, Tv, Wv, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero,
    add_zero]
  ring

lemma Wv_natDegree (n : ℕ) (v : Fin (n - 1) → ℝ) : (Wv n v).natDegree ≤ n - 2 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by lia)

lemma Tv_natDegree (n : ℕ) (hn : 2 ≤ n) (v : Fin (n - 1) → ℝ) :
    (Tv n v).natDegree ≤ n - 1 := by
  refine (natDegree_mul_le).trans ?_
  have : (X + 1 : ℝ[X]).natDegree = 1 := by
    rw [show (X + 1 : ℝ[X]) = X + C 1 by simp, natDegree_X_add_C]
  have := Wv_natDegree n v
  lia

lemma Wv_coeff (n : ℕ) (v : Fin (n - 1) → ℝ) (i : Fin (n - 1)) :
    (Wv n v).coeff (n - 2 - i.1) = v i := by
  rw [Wv, finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [coeff_C_mul_X_pow, ite_eq_right]
    intro h
    apply hji
    ext
    have := i.2; have := j.2
    lia
  · simp

lemma Gv_eval (n : ℕ) (hn : 2 ≤ n) (v : Fin (n - 1) → ℝ) (y : ℝ) (hy : y ≠ 1) :
    (Gv n v).eval y = (1 - y) ^ n * (Tv n v).eval (y / (1 - y)) := by
  have hy' : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  rw [Gv, Tv, Wv, eval_finsetSum, eval_mul, eval_finsetSum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.2
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one, eval_add]
  rw [show (1 - y) ^ n = (1 - y) ^ (n - 2 - i.1) * (1 - y) ^ (i.1 + 1) * (1 - y) by
    rw [← pow_add, ← pow_succ]; congr 1; lia, div_pow]
  field_simp
  ring

lemma Gv_eq_Psi (n : ℕ) (hn : 2 ≤ n) (v : Fin (n - 1) → ℝ) : Gv n v = Psi n (Tv n v) := by
  refine eq_of_eval_eq_off _ _ {1} fun y hy => ?_
  have hy' : y ≠ 1 := by simpa using hy
  rw [Gv_eval n hn v y hy', Psi_eval n _ ((Tv_natDegree n hn v).trans (by lia)) y hy']

lemma Gv_eval_one (n : ℕ) (v : Fin (n - 1) → ℝ) : (Gv n v).eval 1 = 0 := by
  rw [Gv, eval_finsetSum]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp

lemma Gv_natDegree (n : ℕ) (hn : 2 ≤ n) (v : Fin (n - 1) → ℝ) :
    (Gv n v).natDegree ≤ n - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  have hi := i.2
  refine (natDegree_mul_le).trans ?_
  refine (add_le_add (natDegree_C_mul_X_pow_le _ _) (natDegree_pow_le)).trans ?_
  rw [natDegree_one_sub_X]
  lia

lemma Tv_zero (n : ℕ) : Tv n 0 = 0 := by simp [Tv, Wv]

lemma Gv_sub_smul (n : ℕ) (u v : Fin (n - 1) → ℝ) (c : ℝ) :
    Gv n (v - c • u) = Gv n v - c • Gv n u := by
  simp only [Gv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum,
    ← Finset.sum_sub_distrib, map_sub, map_mul, smul_eq_C_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma Gv_injective (n : ℕ) (hn : 2 ≤ n) (v : Fin (n - 1) → ℝ) (h : Gv n v = 0) : v = 0 := by
  rw [Gv_eq_Psi n hn, Psi] at h
  have hc := bbsum_eq_zero n _ h
  have hT : Tv n v = 0 := by
    ext k
    by_cases hk : k ≤ n
    · rw [hc k hk, coeff_zero]
    · rw [coeff_eq_zero_of_natDegree_lt ((Tv_natDegree n hn v).trans_lt (by lia)), coeff_zero]
  have hW : Wv n v = 0 := by
    rw [Tv] at hT
    exact (mul_eq_zero.mp hT).resolve_left (by
      rw [show (X + 1 : ℝ[X]) = X + C 1 by simp]; exact X_add_C_ne_zero 1)
  funext i
  rw [← Wv_coeff n v i, hW, coeff_zero, Pi.zero_apply]

/-! ## The coefficient matrix -/

lemma coeffMatrix_mulVec (n : ℕ) (hn : 2 ≤ n) (v : Fin (n - 1) → ℝ) (i : Fin (n - 1)) :
    ((coeffMatrix n).mulVec v) i =
      (n.choose (i.1 + 1) : ℝ) * (Gv n v).eval (((i.1 : ℝ) + 1) / n) := by
  have hi := i.2
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by lia)
  have hc : (n.choose (i.1 + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show i.1 + 1 ≤ n by lia)).ne'
  have ha : ((n - 1).choose (i.1 + 1) : ℝ) =
      n.choose (i.1 + 1) * (((n : ℝ) - (i.1 + 1)) / n) := by
    have h := Nat.choose_mul_succ_eq (n - 1) (i.1 + 1)
    rw [show n - 1 + 1 = n by lia] at h
    have h' : ((n - 1).choose (i.1 + 1) : ℝ) * n =
        n.choose (i.1 + 1) * ((n : ℝ) - (i.1 + 1)) := by
      have := congrArg (fun x : ℕ => (x : ℝ)) h
      push_cast [Nat.cast_sub (show i.1 + 1 ≤ n by lia)] at this
      linarith
    field_simp
    linarith
  have hb : ((n - 1).choose i.1 : ℝ) = n.choose (i.1 + 1) * (((i.1 : ℝ) + 1) / n) := by
    have h := Nat.add_one_mul_choose_eq (n - 1) i.1
    rw [show n - 1 + 1 = n by lia] at h
    have h' : (n : ℝ) * ((n - 1).choose i.1 : ℝ) = n.choose (i.1 + 1) * ((i.1 : ℝ) + 1) := by
      exact_mod_cast h
    field_simp
    linarith
  have e1 : 1 - ((i.1 : ℝ) + 1) / n = ((n : ℝ) - (i.1 + 1)) / n := by field_simp
  simp only [Matrix.mulVec, dotProduct, coeffMatrix, Gv, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := j.2
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  rw [ha, hb, e1, mul_pow, mul_pow]
  have hexp : (n.choose (i.1 + 1) : ℝ) ^ (j.1 + 1) * (n.choose (i.1 + 1) : ℝ) ^ (n - 2 - j.1) =
      (n.choose (i.1 + 1) : ℝ) ^ (n - 2) * n.choose (i.1 + 1) := by
    rw [← pow_add, ← pow_succ]; congr 1; lia
  calc _ = ((n.choose (i.1 + 1) : ℝ) ^ (j.1 + 1) * (n.choose (i.1 + 1) : ℝ) ^ (n - 2 - j.1)) *
        (((n : ℝ) - (i.1 + 1)) / n) ^ (j.1 + 1) * (((i.1 : ℝ) + 1) / n) ^ (n - 2 - j.1) /
        (n.choose (i.1 + 1) : ℝ) ^ (n - 2) * v j := by ring
    _ = _ := by
      rw [hexp]
      field_simp

lemma coeffMatrix_det_ne_zero (n : ℕ) (hn : 2 ≤ n) : (coeffMatrix n).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  apply hv
  apply Gv_injective n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by lia)
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (Gv n v)
    (f := fun i : Fin n => ((i : ℝ) + 1) / n) ?_ ?_ ?_
  · intro a b hab
    simp only at hab
    field_simp at hab
    ext
    exact_mod_cast (show (a : ℝ) = b by linarith)
  · intro i
    by_cases hi : i.1 < n - 1
    · have := congrFun hMv ⟨i.1, hi⟩
      rw [coeffMatrix_mulVec n hn, Pi.zero_apply] at this
      have hc : (n.choose (i.1 + 1) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (show i.1 + 1 ≤ n by lia)).ne'
      exact (mul_eq_zero.mp this).resolve_left hc
    · have : ((i : ℝ) + 1) / n = 1 := by
        rw [div_eq_one_iff_eq hn0]
        have : i.1 + 1 = n := by have := i.2; lia
        exact_mod_cast this
      rw [this, Gv_eval_one]
  · simp only [Fintype.card_fin]
    have := Gv_natDegree n hn v
    lia

lemma linearPart_eq (n : ℕ) (v : Fin (n - 1) → ℝ) :
    linearPart n v = (coeffMatrix n)⁻¹.mulVec (fun i => (Tv n v).coeff (i.1 + 1)) := by
  rw [linearPart, coeffMap, coeffMap, ← Matrix.mulVec_sub]
  congr 1
  funext i
  simp only [Pi.sub_apply, interiorCoeff]
  rw [← monicPolynomial_sub, coeff_sub]
  ring

lemma bernOp_Gv_sub (n : ℕ) (hn : 2 ≤ n) (v : Fin (n - 1) → ℝ) (μ : ℝ) :
    bernOp n (Gv n v) - μ • Gv n v = ∑ k ∈ Finset.range (n + 1),
      C ((Gv n v).eval ((k : ℝ) / n) * n.choose k - μ * (Tv n v).coeff k) * bb n k := by
  have hG : μ • Gv n v = ∑ k ∈ Finset.range (n + 1), C (μ * (Tv n v).coeff k) * bb n k := by
    conv_lhs => rw [Gv_eq_Psi n hn v]
    rw [Psi, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_C_mul, C_mul, mul_assoc]
  rw [hG, bernOp_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_sub, sub_mul]

/-- Bernstein eigenvectors give eigenvectors of the linear part. -/
lemma linearPart_eigen_of_bern (n : ℕ) (hn : 2 ≤ n) (v : Fin (n - 1) → ℝ) (lam : ℝ)
    (hlam : lam ≠ 0) (hB : bernOp n (Gv n v) = lam⁻¹ • Gv n v) :
    linearPart n v = lam • v := by
  have hsum := bernOp_Gv_sub n hn v lam⁻¹
  rw [hB, sub_self] at hsum
  have hcoef := bbsum_eq_zero n _ hsum.symm
  have ht : (fun i : Fin (n - 1) => (Tv n v).coeff (i.1 + 1)) =
      lam • ((coeffMatrix n).mulVec v) := by
    funext i
    have hi := i.2
    have := hcoef (i.1 + 1) (by lia)
    rw [Pi.smul_apply, coeffMatrix_mulVec n hn, smul_eq_mul]
    push_cast at this ⊢
    field_simp at this ⊢
    linarith
  rw [linearPart_eq, ht, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (coeffMatrix_det_ne_zero n hn)),
    Matrix.one_mulVec]

lemma coeff_one_sub_X_pow (n : ℕ) : ((1 - X : ℝ[X]) ^ n).coeff n = (-1) ^ n := by
  have h1 := natDegree_pow (1 - X : ℝ[X]) n
  rw [natDegree_one_sub_X, mul_one] at h1
  have h2 := leadingCoeff_pow (1 - X : ℝ[X]) n
  rw [leadingCoeff_one_sub_X, leadingCoeff, h1] at h2
  exact h2

/-- Eigenvectors of the linear part give Bernstein eigenvectors. -/
lemma bern_of_linearPart_eigen (n : ℕ) (hn : 2 ≤ n) (v : Fin (n - 1) → ℝ) (lam : ℝ)
    (hlam : lam ≠ 0) (h : linearPart n v = lam • v) :
    bernOp n (Gv n v) = lam⁻¹ • Gv n v := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by lia)
  have ht : (fun i : Fin (n - 1) => (Tv n v).coeff (i.1 + 1)) =
      lam • ((coeffMatrix n).mulVec v) := by
    have := congrArg (Matrix.mulVec (coeffMatrix n)) h
    rw [linearPart_eq, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (coeffMatrix_det_ne_zero n hn)),
      Matrix.one_mulVec, Matrix.mulVec_smul] at this
    exact this
  set d : ℕ → ℝ := fun k =>
    (Gv n v).eval ((k : ℝ) / n) * n.choose k - lam⁻¹ * (Tv n v).coeff k with hd
  have hD := bernOp_Gv_sub n hn v lam⁻¹
  have hdk : ∀ k ∈ Finset.range (n + 1), k ≠ 0 → d k = 0 := by
    intro k hk hk0
    rw [Finset.mem_range] at hk
    by_cases hkn : k = n
    · subst hkn
      simp only [hd, div_self hn0, Gv_eval_one, zero_mul, zero_sub]
      rw [coeff_eq_zero_of_natDegree_lt ((Tv_natDegree k hn v).trans_lt (by lia)), mul_zero,
        neg_zero]
    · have := congrFun ht ⟨k - 1, by lia⟩
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [coeffMatrix_mulVec n hn, show k - 1 + 1 = k by lia] at this
      have hk1 : (((k - 1 : ℕ) : ℝ) + 1) = k := by
        rw [Nat.cast_sub (by lia)]; push_cast; ring
      rw [hk1] at this
      simp only [hd]
      rw [this]
      field_simp
      ring
  rw [Finset.sum_eq_single 0 (fun k hk hk0 => by
    have := hdk k hk hk0
    simp only [hd] at this
    rw [this, map_zero, zero_mul]) (by simp)] at hD
  have hdeg : (bernOp n (Gv n v) - lam⁻¹ • Gv n v).natDegree ≤ n - 1 := by
    have h1 := (bernOp_deg n (by lia) (n - 1) (Gv n v) (Gv_natDegree n hn v)).1
    exact (natDegree_sub_le _ _).trans (max_le h1 ((natDegree_smul_le _ _).trans
      (Gv_natDegree n hn v)))
  have hcn : (bernOp n (Gv n v) - lam⁻¹ • Gv n v).coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (by lia)
  rw [hD, bb, coeff_C_mul, pow_zero, one_mul, Nat.sub_zero, coeff_one_sub_X_pow] at hcn
  have hd0 := (mul_eq_zero.mp hcn).resolve_right (pow_ne_zero _ (by norm_num))
  rw [← sub_eq_zero, hD, hd0, map_zero, zero_mul]

lemma exists_v_of_T (n : ℕ) (hn : 2 ≤ n) (T : ℝ[X]) (hT : T.natDegree ≤ n - 1)
    (h1 : T.eval (-1) = 0) : ∃ v : Fin (n - 1) → ℝ, Tv n v = T := by
  set W := T /ₘ (X - C (-1)) with hW
  have hTW : (X - C (-1)) * W = T := mul_divByMonic_eq_iff_isRoot.mpr h1
  have hWd : W.natDegree ≤ n - 2 := by
    rw [hW, natDegree_divByMonic T (monic_X_sub_C _), natDegree_X_sub_C]
    lia
  refine ⟨fun i => W.coeff (n - 2 - i.1), ?_⟩
  have hWv : Wv n (fun i => W.coeff (n - 2 - i.1)) = W := by
    ext k
    rw [Wv, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    by_cases hk : k ≤ n - 2
    · rw [Finset.sum_eq_single ⟨n - 2 - k, by lia⟩]
      · simp only
        rw [ite_eq_left (by lia), show n - 2 - (n - 2 - k) = k by lia]
      · intro j _ hj
        rw [ite_eq_right]
        intro h
        apply hj
        ext
        simp only
        have := j.2
        lia
      · simp
    · rw [coeff_eq_zero_of_natDegree_lt (by lia)]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right (by lia)]
  rw [Tv, hWv, ← hTW]
  simp

lemma eigenvalue_spec (n k : ℕ) (hk : k < n - 1) :
    eigenvalue n k ≠ 0 ∧ (eigenvalue n k)⁻¹ = mu n (k + 1) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by lia)
  have hd : ((n - 1).descFactorial k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by lia)).ne'
  refine ⟨div_ne_zero (pow_ne_zero _ hn0) hd, ?_⟩
  have h := Nat.succ_descFactorial_succ (n - 1) k
  rw [show n - 1 + 1 = n by lia] at h
  rw [eigenvalue, mu, inv_div, h]
  push_cast
  field_simp
  ring

/-- Auxiliary construction of the first eigendirection. -/
theorem exists_first_eigenvector (n : ℕ) (hn : 2 ≤ n) :
    ∃ v : Fin (n - 1) → ℝ, v ≠ 0 ∧
      monicPolynomial n v - monicPolynomial n 0 = (X + 1) ^ (n - 1) ∧
      linearPart n v = eigenvalue n 0 • v := by
  have hX1 : (X + 1 : ℝ[X]) = X - C (-1) := by simp
  have hTd : ((X + 1 : ℝ[X]) ^ (n - 1)).natDegree ≤ n - 1 := by
    rw [hX1, natDegree_pow, natDegree_X_sub_C, mul_one]
  obtain ⟨v, hv⟩ := exists_v_of_T n hn ((X + 1) ^ (n - 1)) hTd (by
    simp [zero_pow (show n - 1 ≠ 0 by lia)])
  refine ⟨v, ?_, by rw [monicPolynomial_sub, hv], ?_⟩
  · rintro rfl
    rw [Tv_zero, hX1] at hv
    exact pow_ne_zero _ (X_sub_C_ne_zero _) hv.symm
  · have hG : Gv n v = 1 - X := by
      rw [Gv_eq_Psi n hn, hv]
      refine eq_of_eval_eq_off _ _ {1} fun y hy => ?_
      have hy' : y ≠ 1 := by simpa using hy
      have hy'' : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy')
      rw [Psi_eval n _ (hTd.trans (by lia)) y hy']
      simp only [eval_pow, eval_add, eval_X, eval_one, eval_sub]
      have e1 : y / (1 - y) + 1 = 1 / (1 - y) := by field_simp; ring
      rw [e1, show (1 - y) ^ n = (1 - y) ^ (n - 1) * (1 - y) by
        rw [← pow_succ]; congr 1; lia, mul_comm ((1 - y) ^ (n - 1)), mul_assoc, ← mul_pow,
        mul_one_div_cancel hy'', one_pow, mul_one]
    have e0 := eigenvalue_spec n 0 (by lia)
    apply linearPart_eigen_of_bern n hn v _ e0.1
    rw [e0.2, zero_add, mu_one n (by lia), hG, map_sub, bernOp_one n (by lia),
      bernOp_X n (by lia), one_smul]

/-- Auxiliary construction of the reduced eigenpolynomials. -/
theorem exists_reduced_eigenpolynomial (n j : ℕ) (hj : j + 3 ≤ n) :
    ∃ Q : ℝ[X], Q.Monic ∧ Q.natDegree = j ∧ Q.eval 0 ≠ 0 ∧
      Q.reverse = C ((-1 : ℝ) ^ j) * Q ∧ (Odd j → Q.eval 1 = 0) ∧
      ∃ v : Fin (n - 1) → ℝ, v ≠ 0 ∧
        monicPolynomial n v - monicPolynomial n 0 = X * (X + 1) ^ (n - j - 2) * Q ∧
        linearPart n v = eigenvalue n (j + 1) • v := by
  have hn : 2 ≤ n := by lia
  obtain ⟨hmon, hdeg, heig⟩ := eigPoly_spec n (j + 2) (by lia) (by lia)
  have hG0 := eigPoly_eval_zero n (j + 2) (by lia) (by lia)
  have hG1 := eigPoly_eval_one n (j + 2) (by lia) (by lia)
  have hGc1 := eigPoly_coeff_one_ne_zero n (j + 2) (by lia) (by lia)
  have hrefl := eigPoly_reflect n (j + 2) (by lia) (by lia)
  set G := eigPoly n (j + 2) with hG
  -- factor `G = X (X - 1) H`
  obtain ⟨G₁, hG₁⟩ : X ∣ G := X_dvd_iff.mpr (by rw [coeff_zero_eq_eval_zero, hG0])
  have hG₁1 : G₁.IsRoot 1 := by
    have := hG1
    rw [hG₁, eval_mul, eval_X, one_mul] at this
    exact this
  obtain ⟨H, hH⟩ := dvd_iff_isRoot.mpr hG₁1
  have hGH : G = X * (X - C 1) * H := by rw [hG₁, hH, mul_assoc]
  have hXX : (X * (X - C 1) : ℝ[X]).Monic := monic_X.mul (monic_X_sub_C 1)
  have hXXd : (X * (X - C 1) : ℝ[X]).natDegree = 2 := by
    rw [monic_X.natDegree_mul (monic_X_sub_C 1), natDegree_X, natDegree_X_sub_C]
  have hHmon : H.Monic := hXX.of_mul_monic_left (hGH ▸ hmon)
  have hHdeg : H.natDegree = j := by
    have := hXX.natDegree_mul hHmon
    rw [← hGH, hdeg, hXXd] at this
    lia
  have hH0 : H.eval 0 ≠ 0 := by
    intro h
    apply hGc1
    rw [hGH, mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul, coeff_zero_eq_eval_zero]
    simp [h]
  have hHrefl : H.comp (1 - X) = C ((-1 : ℝ) ^ j) * H := by
    apply mul_left_cancel₀ hXX.ne_zero
    have := hrefl
    rw [hGH] at this
    simp only [mul_comp, X_comp, sub_comp, C_comp] at this
    calc X * (X - C 1) * H.comp (1 - X) = (1 - X) * (1 - X - C 1) * H.comp (1 - X) := by
          simp only [map_one]; ring
      _ = C ((-1 : ℝ) ^ (j + 2)) * (X * (X - C 1) * H) := this
      _ = X * (X - C 1) * (C ((-1 : ℝ) ^ j) * H) := by
          rw [pow_add]; simp only [map_mul, map_pow, map_neg, map_one]; ring
  have hH1 : H.eval 1 ≠ 0 := by
    have := congrArg (eval 0) hHrefl
    simp only [eval_comp, eval_sub, eval_one, eval_X, sub_zero, eval_mul, eval_C] at this
    rw [this]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hH0
  -- the polynomial `Q`
  set Q₀ := Phi j H with hQ₀
  have hQ₀d : Q₀.natDegree = j := natDegree_eq_of_le_of_coeff_ne_zero (Phi_natDegree_le j H)
    (by rw [Phi_coeff_top j H hHdeg.le]; exact hH1)
  set Q := C (H.eval 1)⁻¹ * Q₀ with hQ
  have hQd : Q.natDegree = j := by rw [hQ, natDegree_C_mul (inv_ne_zero hH1), hQ₀d]
  have hQmon : Q.Monic := by
    rw [Monic, leadingCoeff, hQd, hQ, coeff_C_mul, Phi_coeff_top j H hHdeg.le,
      inv_mul_cancel₀ hH1]
  have hQ₀refl : reflect j Q₀ = C ((-1 : ℝ) ^ j) * Q₀ := by
    refine eq_of_eval_eq_off _ _ {0, -1} fun x hx => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hx1' : 1 + x ≠ 0 := by intro h; apply hx1; linarith
    have hx2 : 1 / x ≠ -1 := by
      intro h; field_simp at h; apply hx1; linarith
    rw [eval_reflect_eq Q₀ j hQ₀d.le x hx0, eval_mul, eval_C, Phi_eval j H hHdeg.le x hx1,
      Phi_eval j H hHdeg.le (1 / x) hx2]
    have key : H.eval ((1 / x) / (1 + 1 / x)) = (-1) ^ j * H.eval (x / (1 + x)) := by
      have := congrArg (eval (x / (1 + x))) hHrefl
      simp only [eval_comp, eval_sub, eval_one, eval_X, eval_mul, eval_C] at this
      rw [← this]
      congr 1
      have h3 : 1 + 1 / x = (1 + x) / x := by field_simp; ring
      rw [h3, div_div_div_cancel_right₀ hx0]
      field_simp
      ring
    rw [key]
    have e : x ^ j * (1 + 1 / x) ^ j = (1 + x) ^ j := by
      rw [← mul_pow]; congr 1; field_simp; ring
    calc x ^ j * ((1 + 1 / x) ^ j * ((-1) ^ j * H.eval (x / (1 + x))))
        = (x ^ j * (1 + 1 / x) ^ j) * ((-1) ^ j * H.eval (x / (1 + x))) := by ring
      _ = _ := by rw [e]; ring
  have hQrev : Q.reverse = C ((-1 : ℝ) ^ j) * Q := by
    rw [reverse, hQd, hQ, reflect_C_mul, hQ₀refl]
    ring
  clear_value Q
  have hQ0 : Q.eval 0 ≠ 0 := by
    have := congrArg (fun P => P.coeff 0) hQrev
    simp only [coeff_zero_reverse, hQmon.leadingCoeff, coeff_C_mul] at this
    rw [← coeff_zero_eq_eval_zero]
    intro h
    rw [h, mul_zero] at this
    exact one_ne_zero this
  have hQ1 : Odd j → Q.eval 1 = 0 := by
    intro hodd
    have := congrArg (eval 1) hQrev
    rw [reverse, hQd, eval_reflect_eq Q j hQd.le 1 one_ne_zero, one_pow, one_mul, div_one,
      eval_mul, eval_C, hodd.neg_one_pow] at this
    linarith
  refine ⟨Q, hQmon, hQd, hQ0, hQrev, hQ1, ?_⟩
  -- the eigenvector
  have hX1 : (X + 1 : ℝ[X]) = X - C (-1) := by simp
  set T := X * (X + 1) ^ (n - j - 2) * Q with hT
  have hTd : T.natDegree ≤ n - 1 := by
    refine natDegree_mul_le.trans ?_
    refine (add_le_add natDegree_mul_le le_rfl).trans ?_
    rw [hQd, natDegree_X, hX1, natDegree_pow, natDegree_X_sub_C]
    lia
  have hT1 : T.eval (-1) = 0 := by
    simp [hT, zero_pow (show n - j - 2 ≠ 0 by lia)]
  obtain ⟨v, hv⟩ := exists_v_of_T n hn T hTd hT1
  have hTne : T ≠ 0 :=
    mul_ne_zero (mul_ne_zero X_ne_zero (pow_ne_zero _ (hX1 ▸ X_sub_C_ne_zero _))) hQmon.ne_zero
  refine ⟨v, ?_, by rw [monicPolynomial_sub, hv], ?_⟩
  · rintro rfl
    rw [Tv_zero] at hv
    exact hTne hv.symm
  · have hGv : Gv n v = (-(H.eval 1)⁻¹) • G := by
      rw [Gv_eq_Psi n hn, hv]
      refine eq_of_eval_eq_off _ _ {1} fun y hy => ?_
      have hy' : y ≠ 1 := by simpa using hy
      have hy'' : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy')
      rw [Psi_eval n T (hTd.trans (by lia)) y hy']
      have ht1 : y / (1 - y) ≠ -1 := by
        intro h; field_simp at h; linarith
      simp only [hT, hQ, eval_mul, eval_X, eval_pow, eval_add, eval_one, eval_C, eval_smul,
        smul_eq_mul]
      rw [Phi_eval j H hHdeg.le _ ht1, hGH]
      simp only [eval_mul, eval_X, eval_sub, eval_C]
      have e1 : y / (1 - y) + 1 = 1 / (1 - y) := by field_simp; ring
      have e2 : 1 + y / (1 - y) = 1 / (1 - y) := by field_simp; ring
      have e3 : y / (1 - y) / (1 / (1 - y)) = y := by field_simp
      rw [e1, e2, e3, show (1 - y) ^ n = (1 - y) ^ (n - j - 2) * (1 - y) ^ j * (1 - y) ^ 2 by
        rw [← pow_add, ← pow_add]; congr 1; lia, one_div, inv_pow, inv_pow]
      field_simp
      ring
    have e := eigenvalue_spec n (j + 1) (by lia)
    apply linearPart_eigen_of_bern n hn v _ e.1
    rw [e.2, hGv, map_smul, heig, smul_comm]


end Kostov
end RealRooted
