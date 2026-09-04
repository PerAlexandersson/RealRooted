import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import RealRooted.Bezoutian.MatrixBasics

/-!
# Bezout-matrix root evaluation

Common-root obstructions, Vandermonde congruence, root-product identities, and
the forward strict-interlacing-to-positive-definiteness direction.
-/

open Polynomial Matrix

noncomputable section

namespace RealRooted

lemma bezoutMatrix.mulVec_vandermonde_eq_zero_of_common_root
    {p q : ℝ[X]} {n : ℕ} {r : ℝ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h_pr : p.eval r = 0) (h_qr : q.eval r = 0) :
    (bezoutMatrix n p q).mulVec (fun j => r ^ (j : ℕ)) = 0 := by
  set c : Fin n → ℝ := fun i => ∑ j : Fin n, bezoutMatrix n p q i j * r ^ (j : ℕ) with hc
  set P : ℝ[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ) with hP
  have h_P_eval (t : ℝ) : P.eval t = ∑ i : Fin n, ∑ j : Fin n,
      bezoutEntry p q (i : ℕ) (j : ℕ) * t ^ (i : ℕ) * r ^ (j : ℕ) := by
    rw [hP]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, hc]
    simp_rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [bezoutMatrix]
    ring
  have h_roots_ne (t : ℝ) (htr : t ≠ r) : P.eval t = 0 := by
    have : (t - r) * ∑ i : Fin n, ∑ j : Fin n,
        bezoutEntry p q i.val j.val * t ^ i.val * r ^ j.val =
        p.eval t * q.eval r - p.eval r * q.eval t :=
      bezoutEntry.bilinear_mul_sub p q t r hp hq
    rw [← h_P_eval t, h_pr, h_qr, mul_zero, zero_mul, sub_zero] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr htr)
  have h_P_zero : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := {t : ℝ | t ≠ r}) h_roots_ne
    have : {t : ℝ | t ≠ r} = (Set.univ : Set ℝ) \ {r} := by
      ext t
      simp
    rw [this]
    exact Set.Infinite.sdiff Set.infinite_univ (Set.finite_singleton r)
  have h_c_zero (i : Fin n) : c i = 0 := by
    have : P.coeff (i : ℕ) = c i := by
      rw [hP, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [coeff_C_mul, coeff_X_pow]
        split_ifs with heq
        · exfalso
          exact hj (Fin.ext heq.symm)
        · exact mul_zero _
      · intro hi_univ
        exact (hi_univ (Finset.mem_univ i)).elim
    rw [← this, h_P_zero, coeff_zero]
  funext i
  simp only [mulVec, dotProduct]
  simp_all

lemma bezoutMatrix.det_eq_zero_of_common_root
    {p q : ℝ[X]} {n : ℕ} {r : ℝ} (hn : n ≠ 0)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h_pr : p.eval r = 0) (h_qr : q.eval r = 0) :
    (bezoutMatrix n p q).det = 0 := by
  by_contra h_det
  have h_inj : Function.Injective (bezoutMatrix n p q).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h_det))
  have h_vec_ne : (fun j : Fin n => r ^ (j : ℕ)) ≠ 0 := fun h ↦
    one_ne_zero (congr_fun h ⟨0, Nat.pos_of_ne_zero hn⟩)
  have : (bezoutMatrix n p q).mulVec (fun j => r ^ (j : ℕ)) = 0 :=
    mulVec_vandermonde_eq_zero_of_common_root hp hq h_pr h_qr
  exact h_vec_ne (h_inj (this.trans (mulVec_zero _).symm))

lemma bezoutMatrix.not_posDef_of_common_root
    {p q : ℝ[X]} {n : ℕ} {r : ℝ} (hn : n ≠ 0)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h_pr : p.eval r = 0) (h_qr : q.eval r = 0) :
    ¬ (bezoutMatrix n p q).PosDef :=
  fun h_pos ↦ lt_irrefl 0
    (det_eq_zero_of_common_root hn hp hq h_pr h_qr ▸ h_pos.det_pos)

lemma bezoutMatrix.no_common_real_root_of_posDef
    {p q : ℝ[X]} {n : ℕ} (hn : n ≠ 0)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h_pos : (bezoutMatrix n p q).PosDef) (r : ℝ) :
    ¬ (p.eval r = 0 ∧ q.eval r = 0) :=
  fun ⟨h_pr, h_qr⟩ ↦ not_posDef_of_common_root hn hp hq h_pr h_qr h_pos
lemma bezoutEntry.wronskian (p q : ℝ[X]) (n : ℕ) (t : ℝ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    ∑ i : Fin n, ∑ j : Fin n,
    bezoutEntry p q i.val j.val * t ^ (i.val + j.val) =
    p.derivative.eval t * q.eval t -
    p.eval t * q.derivative.eval t := by
  have h_apply : deriv (fun t₁ ↦ (t₁ - t) * ∑ i : Fin n, ∑ j : Fin n,
        bezoutEntry p q i.val j.val * t₁ ^ i.val * t ^ j.val) t =
      deriv (fun t₁ ↦ p.eval t₁ * q.eval t - p.eval t * q.eval t₁) t :=
    Filter.EventuallyEq.deriv_eq <| Filter.Eventually.of_forall fun t₁ ↦
      bezoutEntry.bilinear_mul_sub p q t₁ t hp hq
  have h_left : deriv (fun t₁ ↦ (t₁ - t) * ∑ i : Fin n, ∑ j : Fin n,
        bezoutEntry p q i.val j.val * t₁ ^ i.val * t ^ j.val) t =
      ∑ i : Fin n, ∑ j : Fin n, bezoutEntry p q i.val j.val * t ^ i.val * t ^ j.val := by
    have h_sub : HasDerivAt (fun t₁ : ℝ ↦ t₁ - t) 1 t := by
      simpa using (hasDerivAt_id' t).sub_const t
    have h_sum : HasDerivAt
        (fun t₁ : ℝ ↦ ∑ i : Fin n, ∑ j : Fin n,
          bezoutEntry p q i.val j.val * t₁ ^ i.val * t ^ j.val)
        (∑ i : Fin n, ∑ j : Fin n,
          ((i.val : ℝ) * t ^ (i.val - 1)) * bezoutEntry p q i.val j.val * t ^ j.val) t := by
      refine HasDerivAt.fun_sum fun i _ ↦ HasDerivAt.fun_sum fun j _ ↦ ?_
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        ((hasDerivAt_pow i.val t).const_mul (bezoutEntry p q i.val j.val)).mul_const (t ^ j.val)
    simpa [sub_self, zero_mul, one_mul, mul_assoc, mul_comm, mul_left_comm, Pi.mul_def] using
      (h_sub.mul h_sum).deriv
  have h_deriv : deriv (fun t₁ ↦ p.eval t₁ * q.eval t - p.eval t * q.eval t₁) t =
      p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t :=
    HasDerivAt.deriv <| ((p.hasDerivAt t).mul_const (q.eval t)).sub
      (HasDerivAt.const_mul (p.eval t) (q.hasDerivAt t))
  grind

lemma bezoutMatrix.vandermonde_diagonal (p q : ℝ[X]) (n : ℕ) (t : ℝ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    dotProduct (fun i : Fin n ↦ t ^ (i : ℕ))
    ((bezoutMatrix n p q).mulVec (fun j : Fin n ↦ t ^ (j : ℕ))) =
    p.derivative.eval t * q.eval t -
    p.eval t * q.derivative.eval t := by
  convert bezoutEntry.wronskian p q n t hp hq using 1
  · simp only [bezoutMatrix, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc,
      mul_comm, pow_add]

lemma bezoutMatrix.vandermonde_off_diagonal (p q : ℝ[X]) (n : ℕ)
    (r : Fin n → ℝ) (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (hr_roots : ∀ k : Fin n, q.eval (r k) = 0)
    (hr_inj : Function.Injective r)
    (k l : Fin n) (hkl : k ≠ l) :
    dotProduct (fun i : Fin n ↦ r k ^ (i : ℕ))
    ((bezoutMatrix n p q).mulVec (fun j : Fin n ↦ r l ^ (j : ℕ))) = 0 := by
  have h_bezoutian : ∑ i : Fin n, ∑ j : Fin n,
      bezoutEntry p q i.val j.val * r k ^ i.val * r l ^ j.val = 0 := by
    have h_mul := bezoutEntry.bilinear_mul_sub p q (r k) (r l) hp hq
    grind
  convert h_bezoutian using 1
  · simp only [bezoutMatrix, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

lemma bezoutMatrix.vandermonde_eq_diagonal (p q : ℝ[X]) (n : ℕ)
    (r : Fin n → ℝ) (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (hr_roots : ∀ k : Fin n, q.eval (r k) = 0)
    (hr_inj : Function.Injective r) :
    (vandermonde r) * (bezoutMatrix n p q) * (vandermonde r)ᵀ =
    Matrix.diagonal (fun k ↦ p.derivative.eval (r k) * q.eval (r k) -
    p.eval (r k) * q.derivative.eval (r k)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [diagonal_apply_eq, mul_apply, vandermonde_apply, transpose_apply]
    convert bezoutMatrix.vandermonde_diagonal p q n (r i) hp hq using 1
    · have (x y : Fin n) :
          r i ^ y.val * (r i ^ x.val * bezoutMatrix n p q x y) =
          r i ^ x.val * (r i ^ y.val * bezoutMatrix n p q x y) := by
        ring
      simpa only [mul_comm, Finset.mul_sum, dotProduct, Matrix.mulVec] using
        Finset.sum_comm.trans
          (Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ this x y)
  · simp only [diagonal_apply_ne _ hij, mul_apply, vandermonde_apply, transpose_apply]
    convert bezoutMatrix.vandermonde_off_diagonal p q n r hp hq hr_roots hr_inj i j hij using 1
    · simpa only [mul_comm, Finset.mul_sum, dotProduct, Matrix.mulVec, mul_left_comm] using
        Finset.sum_comm
lemma Matrix.PosDef.of_congruent_diagonal {n : ℕ} {V : Matrix (Fin n) (Fin n) ℝ}
    {d : Fin n → ℝ} (hd : ∀ k, 0 < d k) (hV : V.det ≠ 0) :
    (Vᵀ * diagonal d * V).PosDef := by
  have h_inj : Function.Injective V.mulVec := by
    rwa [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact PosDef.conjTranspose_mul_mul_same (PosDef.diagonal hd) h_inj

lemma Matrix.PosDef.of_congruent_to_diagonal {n : ℕ}
    {V B : Matrix (Fin n) (Fin n) ℝ}
    {d : Fin n → ℝ} (hd : ∀ k, 0 < d k) (hV : V.det ≠ 0)
    (heq : V * B * Vᵀ = diagonal d) :
    B.PosDef := by
  let W := (V⁻¹)ᵀ
  have hW : W.det ≠ 0 := by simp [W, hV]
  have hB_eq : B = Wᵀ * diagonal d * W := by
    rw [show B = V⁻¹ * (V * B * Vᵀ) * (Vᵀ)⁻¹ by simp [Matrix.mul_assoc, hV], heq]
    simp [W, Matrix.transpose_nonsing_inv]
  rw [hB_eq]
  exact Matrix.PosDef.of_congruent_diagonal hd hW

lemma StrictMono.prod_sub_mul_prod_sub_pos_of_interlacing {n : ℕ}
    (s r : Fin n → ℝ) (hr : StrictMono r)
    (hint : ∀ k : Fin n, s k < r k)
    (hint' : ∀ (i j : Fin n), i < j → r i < s j)
    (k : Fin n) :
    0 < (∏ j : Fin n, (r k - s j)) *
    (∏ j ∈ Finset.univ.erase k, (r k - r j)) := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  have h_prod : 0 < (∏ j ∈ Finset.univ.erase k, (r k - r j)) *
      (∏ j ∈ Finset.univ.erase k, (r k - s j)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_pos fun x hx ↦ ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hx) with h | h
    · exact mul_pos (sub_pos.mpr (hr h)) (sub_pos.mpr (lt_trans (hint x) (hr h)))
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hr h)) (sub_neg.mpr (hint' k x h))
  nlinarith [hint k]

lemma StrictMono.prod_sub_mul_prod_sub_neg_of_interlacing {n : ℕ}
    (s r : Fin n → ℝ) (hs : StrictMono s)
    (hint : ∀ k : Fin n, s k < r k)
    (hint' : ∀ (i j : Fin n), i < j → r i < s j)
    (k : Fin n) :
    (∏ j ∈ Finset.univ.erase k, (s k - s j)) *
      (∏ j : Fin n, (s k - r j)) < 0 := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  have h_prod : 0 < (∏ j ∈ Finset.univ.erase k, (s k - s j)) *
      (∏ j ∈ Finset.univ.erase k, (s k - r j)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_pos fun x hx ↦ ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hx) with h | h
    · exact mul_pos (sub_pos.mpr (hs h)) (sub_pos.mpr (hint' x k h))
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hs h))
        (sub_neg.mpr (lt_trans (hs h) (hint x)))
  nlinarith [hint k]

lemma Polynomial.eval_derivative_prod_X_sub_C_univ_at_root {n : ℕ} (r : Fin n → ℝ)
    (k : Fin n) :
    eval (r k) (derivative (∏ j : Fin n, (X - C (r j)))) =
    ∏ j ∈ Finset.univ.erase k, (r k - r j) := by
  simp [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ k), eval_prod,
    Finset.sdiff_singleton_eq_erase]

lemma Polynomial.splits_eq_C_mul_prod {n : ℕ} {q : ℝ[X]}
    (hq_ne : q ≠ 0) (hq_deg : q.natDegree = n)
    (r : Fin n → ℝ) (hr_roots : ∀ k, q.IsRoot (r k))
    (hinj : Function.Injective r) :
    q = C q.leadingCoeff * ∏ j : Fin n, (X - C (r j)) := by
  refine eq_of_degree_sub_lt_of_eval_finset_eq (Finset.image r Finset.univ) ?_ ?_
  · refine lt_of_lt_of_eq (degree_sub_lt ?_ hq_ne ?_) ?_
    · rw [degree_eq_natDegree hq_ne, hq_deg, degree_mul, degree_C (leadingCoeff_ne_zero.mpr hq_ne),
        zero_add, degree_prod]
      simp_all [degree_X_sub_C]
    · simp [leadingCoeff_prod]
    · rw [degree_eq_natDegree hq_ne, hq_deg,
        Finset.card_image_of_injective _ hinj, Finset.card_fin]
  · simp_all [eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, hinj.eq_iff]

lemma Polynomial.roots_sort_eq_of_isRoot {n : ℕ} {p : ℝ[X]} (hp_ne : p ≠ 0)
    (hp_deg : p.natDegree = n)
    (s : Fin n → ℝ) (hs_roots : ∀ k, p.IsRoot (s k)) (hs_sorted : StrictMono s) :
    p.roots.sort (· ≤ ·) = List.map s (List.finRange n) := by
  have hp_eq : p = C p.leadingCoeff * ∏ j : Fin n, (X - C (s j)) :=
    splits_eq_C_mul_prod hp_ne hp_deg s hs_roots hs_sorted.injective
  have hp_roots_eq : p.roots = Multiset.ofList (List.map s (List.finRange n)) := by
    rw [hp_eq, roots_C_mul _ (mt leadingCoeff_eq_zero.mp hp_ne), roots_prod]
    · norm_num [List.map]
      rw [List.ofFn_eq_map]
    · grind
  rw [hp_roots_eq, Multiset.coe_sort, List.mergeSort_eq_self]
  simp only [List.pairwise_iff_get, List.get_eq_getElem, List.getElem_map,
    List.getElem_finRange, Fin.cast_mk, hs_sorted.le_iff_le, Fin.mk_le_mk,
    Fin.val_fin_le]
  grind

lemma StrictPrecSameDegree.interlacing_fin {n : ℕ}
    {p q : ℝ[X]} (h : StrictPrecSameDegree p q)
    (hq_deg : q.natDegree = n)
    (s : Fin n → ℝ) (hs_roots : ∀ k, p.IsRoot (s k)) (hs_sorted : StrictMono s)
    (r : Fin n → ℝ) (hr_roots : ∀ k, q.IsRoot (r k)) (hr_sorted : StrictMono r) :
    (∀ k : Fin n, s k < r k) ∧ (∀ (i j : Fin n), i < j → r i < s j) := by
  obtain ⟨hp, hq, hdeg, h_interlaces⟩ := h
  rw [Polynomial.roots_sort_eq_of_isRoot hp.1 (hdeg.trans hq_deg) s hs_roots hs_sorted,
      Polynomial.roots_sort_eq_of_isRoot hq.1 hq_deg r hr_roots hr_sorted] at h_interlaces
  have h_len : (List.map s (List.finRange n)).length =
    (List.map r (List.finRange n)).length := by simp
  obtain ⟨h_inter1, h_inter2⟩ := RealRooted.interlaced_of_interleaves_reverse h_len h_interlaces
  constructor
  · intro k
    have hk : k.val < (List.map s (List.finRange n)).length := by simp
    simpa only [List.getElem_map, List.getElem_finRange, Fin.cast_mk] using
      h_inter1 ⟨k.val, hk⟩
  · intro i j hij
    have hi : i.val < (List.map s (List.finRange n)).length := by simp
    have hj : j.val < (List.map s (List.finRange n)).length := by simp
    simpa only [List.getElem_map, List.getElem_finRange, Fin.cast_mk] using
      h_inter2 ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
lemma StrictPrecSameDegree.roots_nodup {p q : ℝ[X]}
    (h : StrictPrecSameDegree p q) :
    p.roots.Nodup ∧ q.roots.Nodup := by
  obtain ⟨_, _, _, h_interlacing⟩ := h
  rw [← Multiset.sort_eq p.roots (· ≤ ·), ← Multiset.sort_eq q.roots (· ≤ ·),
    Multiset.coe_nodup, Multiset.coe_nodup]
  exact ⟨(List.pairwise_reverse.mp h_interlacing.pairwise_left).nodup,
         (List.pairwise_reverse.mp h_interlacing.pairwise_right).nodup⟩

lemma Polynomial.exists_strictMono_roots {n : ℕ} {p : ℝ[X]}
    (hp_splits : p.Splits) (hp_deg : p.natDegree = n)
    (hp_nodup : p.roots.Nodup) :
    ∃ s : Fin n → ℝ, StrictMono s ∧ ∀ k, p.IsRoot (s k) := by
  have h_card : p.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hp_nodup, ← hp_deg,
      ← Splits.natDegree_eq_card_roots hp_splits]
  let e := p.roots.toFinset.orderEmbOfFin h_card
  have he : ∀ k : Fin n, e k ∈ p.roots := fun k ↦
    Multiset.mem_toFinset.mp (Finset.orderEmbOfFin_mem p.roots.toFinset h_card k)
  exact ⟨e, e.strictMono, fun k ↦ isRoot_of_mem_roots (he k)⟩

lemma Polynomial.eval_derivative_C_mul_prod_X_sub_C_univ_at_root {n : ℕ} (c : ℝ)
    (r : Fin n → ℝ) (k : Fin n) :
    eval (r k) (derivative (C c * ∏ j : Fin n, (X - C (r j)))) =
    c * ∏ j ∈ Finset.univ.erase k, (r k - r j) := by
  simp [eval_derivative_prod_X_sub_C_univ_at_root r k]

lemma Polynomial.wronskian_at_root_pos_of_interlacing {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (h : StrictPrecSameDegree p q)
    (r : Fin n → ℝ) (hr_roots : ∀ k, q.IsRoot (r k))
    (hr_sorted : StrictMono r)
    (k : Fin n) :
    0 < q.derivative.eval (r k) * p.eval (r k) := by
  obtain ⟨hp_nodup, _⟩ := h.roots_nodup
  have hp_splits := h.1.2
  obtain ⟨s, hs_mono, hs_roots⟩ := exists_strictMono_roots hp_splits hp_deg hp_nodup
  obtain ⟨c₁, hc₁⟩ :
      ∃ c₁ : ℝ, 0 < c₁ ∧ p = C c₁ * ∏ j : Fin n, (X - C (s j)) := by
    have hp_eq : p = C p.leadingCoeff * ∏ j : Fin n, (X - C (s j)) :=
      splits_eq_C_mul_prod (leadingCoeff_ne_zero.mp hp_pos.ne')
        hp_deg s hs_roots hs_mono.injective
    exact ⟨p.leadingCoeff, hp_pos, hp_eq⟩
  obtain ⟨c₂, hc₂⟩ :
      ∃ c₂ : ℝ, 0 < c₂ ∧ q = C c₂ * ∏ j : Fin n, (X - C (r j)) := by
    have hq_eq : q = C q.leadingCoeff * ∏ j : Fin n, (X - C (r j)) :=
      splits_eq_C_mul_prod (leadingCoeff_ne_zero.mp hq_pos.ne')
        hq_deg r hr_roots hr_sorted.injective
    exact ⟨q.leadingCoeff, hq_pos, hq_eq⟩
  have h_eval : q.derivative.eval (r k) * p.eval (r k) = c₂ * c₁ * (∏ j : Fin n,
    (r k - s j)) * (∏ j ∈ Finset.univ.erase k, (r k - r j)) := by
    rw [hc₂.2, hc₁.2]
    simp only [Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ k),
      derivative_mul, derivative_C, zero_mul, derivative_sub, derivative_X, sub_zero,
      mul_one, zero_add, eval_mul, eval_C, eval_add, eval_sub, eval_X, sub_self,
      mul_zero, eval_prod, Finset.sdiff_singleton_eq_erase]
    ring
  have h_prod :
      0 < (∏ j : Fin n, (r k - s j)) * (∏ j ∈ Finset.univ.erase k, (r k - r j)) := by
    have h_interlacing :=
      StrictPrecSameDegree.interlacing_fin h hq_deg s hs_roots hs_mono r
        hr_roots hr_sorted
    exact StrictMono.prod_sub_mul_prod_sub_pos_of_interlacing s r hr_sorted
      h_interlacing.1 h_interlacing.2 k
  rw [h_eval, mul_assoc]
  simp_all

/-- At every root of the left polynomial in a strict same-degree interleaving,
the derivative of the left polynomial and the value of the right polynomial
have opposite signs. -/
theorem StrictPrecSameDegree.derivative_mul_eval_neg {n : ℕ}
    {p q : ℝ[X]} (h : StrictPrecSameDegree p q)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    {x : ℝ} (hx : p.IsRoot x) :
    p.derivative.eval x * q.eval x < 0 := by
  obtain ⟨hp_nodup, hq_nodup⟩ := h.roots_nodup
  obtain ⟨s, hs_mono, hs_roots⟩ :=
    Polynomial.exists_strictMono_roots h.1.2 hp_deg hp_nodup
  obtain ⟨r, hr_mono, hr_roots⟩ :=
    Polynomial.exists_strictMono_roots h.2.1.2 hq_deg hq_nodup
  have hp_eq : p = C p.leadingCoeff * ∏ j : Fin n, (X - C (s j)) :=
    Polynomial.splits_eq_C_mul_prod (leadingCoeff_ne_zero.mp hp_pos.ne')
      hp_deg s hs_roots hs_mono.injective
  have hq_eq : q = C q.leadingCoeff * ∏ j : Fin n, (X - C (r j)) :=
    Polynomial.splits_eq_C_mul_prod (leadingCoeff_ne_zero.mp hq_pos.ne')
      hq_deg r hr_roots hr_mono.injective
  obtain ⟨k, rfl⟩ : ∃ k : Fin n, x = s k := by
    rw [Polynomial.IsRoot.def, hp_eq] at hx
    simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X] at hx
    have hprod : ∏ j : Fin n, (x - s j) = 0 :=
      (mul_eq_zero.mp hx).resolve_left (ne_of_gt hp_pos)
    rw [Finset.prod_eq_zero_iff] at hprod
    obtain ⟨k, _, hk⟩ := hprod
    exact ⟨k, sub_eq_zero.mp hk⟩
  let c₁ := p.leadingCoeff
  let c₂ := q.leadingCoeff
  have hc₁ : 0 < c₁ := hp_pos
  have hc₂ : 0 < c₂ := hq_pos
  have hp_eq' : p = C c₁ * ∏ j : Fin n, (X - C (s j)) := hp_eq
  have hq_eq' : q = C c₂ * ∏ j : Fin n, (X - C (r j)) := hq_eq
  have h_eval : p.derivative.eval (s k) * q.eval (s k) =
      c₁ * c₂ *
        (∏ j ∈ Finset.univ.erase k, (s k - s j)) *
        (∏ j : Fin n, (s k - r j)) := by
    rw [hp_eq', hq_eq']
    simp only [Polynomial.eval_derivative_C_mul_prod_X_sub_C_univ_at_root,
      eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    ring
  obtain ⟨h_inter1, h_inter2⟩ :=
    h.interlacing_fin hq_deg s hs_roots hs_mono r hr_roots hr_mono
  have hprod := StrictMono.prod_sub_mul_prod_sub_neg_of_interlacing
    s r hs_mono h_inter1 h_inter2 k
  rw [h_eval]
  calc
    c₁ * c₂ * (∏ j ∈ Finset.univ.erase k, (s k - s j)) *
        (∏ j : Fin n, (s k - r j)) =
        (c₁ * c₂) * ((∏ j ∈ Finset.univ.erase k, (s k - s j)) *
          (∏ j : Fin n, (s k - r j))) := by ring
    _ < 0 := mul_neg_of_pos_of_neg (mul_pos hc₁ hc₂) hprod

lemma StrictPrecSameDegree.bezoutMatrix_posDef_three_le
    {p q : ℝ[X]} {n : ℕ}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n + 3) (hq_deg : q.natDegree = n + 3)
    (h : StrictPrecSameDegree p q) :
    (bezoutMatrix (n + 3) q p).PosDef := by
  obtain ⟨_, hq_nodup⟩ := h.roots_nodup
  have hq_splits := h.2.1.2
  obtain ⟨s, hs_mono, hs_roots⟩ :
      ∃ s : Fin (n + 3) → ℝ, StrictMono s ∧ ∀ k, q.IsRoot (s k) :=
    Polynomial.exists_strictMono_roots hq_splits hq_deg hq_nodup
  have h_v_eq : vandermonde s * bezoutMatrix (n + 3) q p * (vandermonde s)ᵀ =
      diagonal fun k ↦ q.derivative.eval (s k) * p.eval (s k) := by
    have h_vandermonde : ∀ k : Fin (n + 3),
        p.derivative.eval (s k) * q.eval (s k) -
          p.eval (s k) * q.derivative.eval (s k) =
        q.derivative.eval (s k) * p.eval (s k) * (-1) := by
      intro k
      have hq_zero : q.eval (s k) = 0 := hs_roots k
      grind
    have h_neg : bezoutMatrix (n + 3) q p = -bezoutMatrix (n + 3) p q := by
      ext i j
      simp [bezoutMatrix, bezoutEntry]
    convert congr_arg (fun x ↦ -x)
      (bezoutMatrix.vandermonde_eq_diagonal p q (n + 3) s hp_deg.le hq_deg.le
        (by simp_all) hs_mono.injective) using 1 <;> simp_all
  refine Matrix.PosDef.of_congruent_to_diagonal ?_ ?_ h_v_eq
  · intro k
    convert Polynomial.wronskian_at_root_pos_of_interlacing hp_pos hq_pos
      hp_deg hq_deg h s hs_roots hs_mono k using 1
  · simp_all [Matrix.det_vandermonde, Finset.prod_eq_zero_iff, sub_eq_zero,
      hs_mono.injective.eq_iff]

lemma bezoutMatrix.wronskian_pos_of_posDef
    {p q : ℝ[X]} {n : ℕ}
    (hq_deg : q.natDegree ≤ n + 1) (hp_deg : p.natDegree ≤ n + 1)
    (h : (bezoutMatrix (n + 1) q p).PosDef) (t : ℝ) :
    0 < q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t := by
  have hvec_ne : (fun i : Fin (n + 1) ↦ t ^ (i : ℕ)) ≠ 0 := fun hzero ↦ by
    have h0 := congr_fun hzero 0
    simp_all
  have h_sum_pos := Matrix.PosDef.sum_pos h hvec_ne
  have h_sum_eq :
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        bezoutMatrix (n + 1) q p i j * t ^ (i : ℕ) * t ^ (j : ℕ)) =
      q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t := by
    simp_rw [bezoutMatrix, mul_assoc, ← pow_add]
    exact bezoutEntry.wronskian q p (n + 1) t hq_deg hp_deg
  simp_all

end RealRooted
