import RealRooted.Mathlib.Combinatorics.Enumerative.Excedance
import RealRooted.Mathlib.Combinatorics.Enumerative.GenPoly
import RealRooted.SymmetricDecomposition.DerangementTransform

open Finset Polynomial
open scoped BigOperators Polynomial

namespace RealRooted.DerangementStatistic

/-- The excedance generating polynomial of derangements of `Fin n`. -/
noncomputable def derangementExcGenPoly (n : ℕ) : ℝ[X] :=
  Finset.genPoly (R := ℝ)
    (Finset.univ : Finset {σ : Equiv.Perm (Fin n) // σ ∈ derangements (Fin n)})
    (fun σ => σ.1.excedanceCount)

/-- `D n k`: derangements of `Fin n` with exactly `k` excedances. -/
private def D (n k : ℕ) : ℕ :=
  (univ.filter fun σ : Equiv.Perm (Fin n) =>
    σ ∈ derangements (Fin n) ∧ σ.excedanceCount = k).card

private lemma mem_derangements_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ ∈ derangements (Fin n) ↔ ∀ i, σ i ≠ i := by
  rfl

/-- Excedances whose image is not `q` (auxiliary). -/
private def excQ {n : ℕ} (q : Fin n) (τ : Equiv.Perm (Fin n)) : ℕ :=
  (univ.filter fun x => τ x ≠ q ∧ x < τ x).card

private lemma ins_der_iff {n : ℕ} (q : Fin (n + 1)) (τ : Equiv.Perm (Fin (n + 1))) :
    (∀ i, Equiv.Perm.decomposeFin.symm (q.succ, τ) i ≠ i) ↔
      ∀ x, τ x = x → x = q := by
  rw [Fin.forall_fin_succ]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  refine ⟨fun ⟨_, h⟩ x hx => ?_, fun h => ⟨Fin.succ_ne_zero q, fun x => ?_⟩⟩
  · by_contra hne
    apply h x
    rw [hx, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero x)
      (fun e => hne (Fin.succ_injective _ e))]
  · by_cases hx : τ x = q
    · rw [hx, Equiv.swap_apply_right]
      exact (Fin.succ_ne_zero x).symm
    · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
        (fun e => hx (Fin.succ_injective _ e))]
      intro e
      exact hx (h x (Fin.succ_injective _ e) ▸ Fin.succ_injective _ e)

private lemma ins_exc {n : ℕ} (q : Fin (n + 1)) (τ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.decomposeFin.symm (q.succ, τ)).excedanceCount = excQ q τ + 1 := by
  rw [Equiv.Perm.excedanceCount, Equiv.Perm.excedanceSet, excQ, card_filter,
    card_filter, Fin.sum_univ_succ, add_comm]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Fin.succ_pos, ite_true]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : τ x = q
  · rw [hx, Equiv.swap_apply_right]
    simp
  · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
      (fun e => hx (Fin.succ_injective _ e))]
    simp [hx, Fin.succ_lt_succ_iff]

private lemma excQ_add {n : ℕ} (q : Fin n) (τ : Equiv.Perm (Fin n)) :
    excQ q τ + (if τ.symm q < q then 1 else 0) = τ.excedanceCount := by
  have h : (if τ.symm q < q then 1 else 0) =
      ∑ x, if (τ x = q ∧ x < τ x) then 1 else 0 := by
    rw [Finset.sum_eq_single (τ.symm q)]
    · simp
    · intro b _ hb
      have hne : τ b ≠ q := fun e => hb (by rw [← e]; simp)
      simp [hne]
    · simp
  rw [Equiv.Perm.excedanceCount, Equiv.Perm.excedanceSet, excQ, card_filter, card_filter,
    h, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  by_cases h1 : τ x = q <;> by_cases h2 : x < τ x <;> simp [h1, h2]

private lemma card_symm_lt {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    (univ.filter fun q => τ.symm q < q).card = τ.excedanceCount := by
  symm
  refine card_equiv τ fun i => ?_
  simp [Equiv.Perm.excedanceSet]

private lemma card_excQ {n : ℕ} (k : ℕ) (τ : Equiv.Perm (Fin n)) :
    (univ.filter fun q => excQ q τ = k).card =
      (if τ.excedanceCount = k + 1 then k + 1 else 0) +
        (if τ.excedanceCount = k then n - k else 0) := by
  have hpt : ∀ q, (if excQ q τ = k then 1 else 0) =
      (if τ.excedanceCount = k + 1 ∧ τ.symm q < q then 1 else 0) +
      (if τ.excedanceCount = k ∧ ¬ τ.symm q < q then 1 else 0) := by
    intro q
    have h := excQ_add q τ
    split_ifs at * <;> lia
  rw [card_filter, sum_congr rfl fun q _ => hpt q, sum_add_distrib, ← card_filter,
    ← card_filter]
  have h3 := card_filter_add_card_filter_not (s := univ) (fun q => τ.symm q < q)
  rw [card_symm_lt, card_univ, Fintype.card_fin] at h3
  by_cases h1 : τ.excedanceCount = k + 1
  · have h2 : τ.excedanceCount ≠ k := by lia
    simp only [h1, true_and, ite_true] at h3 ⊢
    simp [card_symm_lt, h1]
  · by_cases h2 : τ.excedanceCount = k
    · simp only [h2, true_and, ite_true, show ¬ (k = k + 1) by lia, false_and,
        filter_false, card_empty, zero_add, ite_false] at h3 ⊢
      lia
    · simp [h1, h2]

private lemma card_fix {n : ℕ} (k : ℕ) (q : Fin (n + 1)) :
    (univ.filter fun τ : Equiv.Perm (Fin (n + 1)) =>
      τ q = q ∧ (∀ x, τ x = x → x = q) ∧ τ.excedanceCount = k).card = D n k := by
  have hA : ∀ (σ : Equiv.Perm (Fin n)) i,
      σ.extendDomain (finSuccAboveEquiv q) (q.succAbove i) = q.succAbove (σ i) := by
    intro σ i
    have h := Equiv.Perm.extendDomain_apply_image σ (finSuccAboveEquiv q) i
    simpa [finSuccAboveEquiv_apply] using h
  have hB : ∀ (σ : Equiv.Perm (Fin n)),
      σ.extendDomain (finSuccAboveEquiv q) q = q := fun σ =>
    Equiv.Perm.extendDomain_apply_not_subtype σ _ (by simp)
  have hexc : ∀ σ : Equiv.Perm (Fin n),
      (σ.extendDomain (finSuccAboveEquiv q)).excedanceCount = σ.excedanceCount := by
    intro σ
    rw [Equiv.Perm.excedanceCount, Equiv.Perm.excedanceCount,
      Equiv.Perm.excedanceSet, Equiv.Perm.excedanceSet, card_filter, card_filter,
      Fin.sum_univ_succAbove _ q, hB]
    simp [hA, Fin.succAbove_lt_succAbove_iff]
  rw [D]
  symm
  refine card_bij (fun σ _ => σ.extendDomain (finSuccAboveEquiv q)) ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    refine ⟨hB σ, ?_, by rw [hexc, hσ.2]⟩
    intro x hx
    by_contra hxq
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hxq
    rw [hA] at hx
    exact hσ.1 i (Fin.succAbove_right_injective hx)
  · intro σ₁ _ σ₂ _ h
    exact Equiv.Perm.extendDomainHom_injective (finSuccAboveEquiv q) h
  · intro τ hτ
    simp only [mem_filter, mem_univ, true_and] at hτ
    obtain ⟨hq, hfix, hk⟩ := hτ
    have hiff : ∀ x, τ x ≠ q ↔ x ≠ q := by
      intro x
      refine ⟨fun h e => h (e ▸ hq), fun h e => h (τ.injective (e.trans hq.symm))⟩
    let σ : Equiv.Perm (Fin n) :=
      (finSuccAboveEquiv q).symm.permCongr (τ.subtypePerm hiff)
    have hσ : ∀ i, q.succAbove (σ i) = τ (q.succAbove i) := by
      intro i
      have h : (finSuccAboveEquiv q (σ i) : Fin (n + 1)) = τ (q.succAbove i) := by
        simp [σ, Equiv.permCongr_apply, finSuccAboveEquiv_apply]
      simpa [finSuccAboveEquiv_apply] using h
    have hext : σ.extendDomain (finSuccAboveEquiv q) = τ := by
      ext x
      by_cases hxq : x = q
      · subst hxq
        rw [hB, hq]
      · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hxq
        rw [hA, hσ]
    refine ⟨σ, ?_, hext⟩
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun i hi => ?_, by rw [← hexc, hext, hk]⟩
    have h1 := hfix (q.succAbove i) (by rw [← hσ, hi])
    exact Fin.succAbove_ne q i h1

private lemma step1 (n k : ℕ) : D (n + 2) (k + 1) = ∑ q : Fin (n + 1),
    (univ.filter fun τ : Equiv.Perm (Fin (n + 1)) =>
      (∀ x, τ x = x → x = q) ∧ excQ q τ = k).card := by
  rw [D]
  rw [card_equiv (t := univ.filter fun pt : Fin (n + 2) × Equiv.Perm (Fin (n + 1)) =>
      Equiv.Perm.decomposeFin.symm pt ∈ derangements (Fin (n + 2)) ∧
        (Equiv.Perm.decomposeFin.symm pt).excedanceCount = k + 1)
    Equiv.Perm.decomposeFin (fun σ => by simp)]
  rw [card_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have h0 : ∀ τ : Equiv.Perm (Fin (n + 1)),
      ¬ (Equiv.Perm.decomposeFin.symm ((0 : Fin (n + 2)), τ) ∈
        derangements (Fin (n + 2)) ∧
        (Equiv.Perm.decomposeFin.symm ((0 : Fin (n + 2)), τ)).excedanceCount = k + 1) :=
    fun τ h => (mem_derangements_iff _).mp h.1 0 (by simp)
  simp only [h0, ite_false, sum_const_zero, zero_add]
  refine sum_congr rfl fun q _ => ?_
  rw [card_filter]
  refine sum_congr rfl fun τ _ => ?_
  simp only [mem_derangements_iff, ins_der_iff, ins_exc, Nat.add_right_cancel_iff]

private lemma step2 {n : ℕ} (k : ℕ) (q : Fin (n + 1)) :
    (univ.filter fun τ : Equiv.Perm (Fin (n + 1)) =>
      (∀ x, τ x = x → x = q) ∧ excQ q τ = k).card =
    (univ.filter fun τ : Equiv.Perm (Fin (n + 1)) =>
      (∀ i, τ i ≠ i) ∧ excQ q τ = k).card +
    (univ.filter fun τ : Equiv.Perm (Fin (n + 1)) =>
      τ q = q ∧ (∀ x, τ x = x → x = q) ∧ τ.excedanceCount = k).card := by
  rw [card_filter, card_filter, card_filter, ← sum_add_distrib]
  refine sum_congr rfl fun τ _ => ?_
  by_cases hq : τ q = q
  · have hE : excQ q τ = τ.excedanceCount := by
      rw [Equiv.Perm.excedanceCount, Equiv.Perm.excedanceSet, excQ]
      congr 1
      refine filter_congr fun x _ =>
        ⟨fun h => h.2, fun h => ⟨fun e => ?_, h⟩⟩
      have hxq : x = q := τ.injective (e.trans hq.symm)
      subst hxq
      exact (lt_irrefl _) (hq ▸ h)
    have hnd : ¬ ∀ i, τ i ≠ i := fun h => h q hq
    simp [hE, hnd, hq]
  · have hd : (∀ x, τ x = x → x = q) ↔ ∀ i, τ i ≠ i := by
      constructor
      · intro h i hi
        exact hq (h i hi ▸ hi)
      · intro h x hx
        exact absurd hx (h x)
    simp [hd, hq]

private lemma step4 (n k : ℕ) : ∑ q : Fin (n + 1),
    (univ.filter fun τ : Equiv.Perm (Fin (n + 1)) =>
      (∀ i, τ i ≠ i) ∧ excQ q τ = k).card =
    (k + 1) * D (n + 1) (k + 1) + (n + 1 - k) * D (n + 1) k := by
  simp_rw [card_filter]
  rw [sum_comm]
  have hpt : ∀ τ : Equiv.Perm (Fin (n + 1)),
      (∑ q : Fin (n + 1),
        if (∀ i, τ i ≠ i) ∧ excQ q τ = k then 1 else 0) =
      (if (∀ i, τ i ≠ i) ∧ τ.excedanceCount = k + 1 then k + 1 else 0) +
      (if (∀ i, τ i ≠ i) ∧ τ.excedanceCount = k then n + 1 - k else 0) := by
    intro τ
    by_cases hd : ∀ i, τ i ≠ i
    · simp only [eq_true hd, true_and]
      rw [← card_filter, card_excQ]
    · simp [hd]
  rw [sum_congr rfl fun τ _ => hpt τ, sum_add_distrib, D, D,
    ← sum_filter, ← sum_filter, sum_const, sum_const, smul_eq_mul, smul_eq_mul,
    mul_comm, mul_comm (n + 1 - k)]
  simp only [mem_derangements_iff]

/-- The excedance recurrence for derangements. -/
private lemma D_succ_succ (n k : ℕ) :
    D (n + 2) (k + 1) = (k + 1) * D (n + 1) (k + 1) +
      (n + 1 - k) * D (n + 1) k + (n + 1) * D n k := by
  rw [step1]
  simp_rw [step2, card_fix, sum_add_distrib, step4]
  simp

/-- There are no derangements with zero excedances. -/
private lemma D_zero_right (n : ℕ) : D (n + 1) 0 = 0 := by
  rw [D, card_eq_zero, filter_eq_empty_iff]
  rintro σ - ⟨h, he⟩
  rw [Equiv.Perm.excedanceCount, Equiv.Perm.excedanceSet,
    card_eq_zero, filter_eq_empty_iff] at he
  exact he (mem_univ 0) (lt_of_le_of_ne (Fin.zero_le _) (h 0).symm)

private lemma coeff_derangementExcGenPoly (n k : ℕ) :
    (derangementExcGenPoly n).coeff k = D n k := by
  rw [derangementExcGenPoly, Finset.coeff_genPoly]
  have hcard :
      ((univ : Finset {σ : Equiv.Perm (Fin n) // σ ∈ derangements (Fin n)}).filter
        (fun σ => σ.1.excedanceCount = k)).card = D n k := by
    rw [D]
    symm
    refine card_bij (fun σ hσ =>
      (⟨σ, (mem_filter.mp hσ).2.1⟩ :
        {σ : Equiv.Perm (Fin n) // σ ∈ derangements (Fin n)})) ?_ ?_ ?_
    · intro σ hσ
      simp only [mem_filter, mem_univ, true_and] at hσ ⊢
      exact hσ.2
    · intro σ₁ _ σ₂ _ hσ
      exact congrArg Subtype.val hσ
    · intro σ hσ
      refine ⟨σ.1, ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and] at hσ ⊢
      exact ⟨σ.property, hσ⟩
  exact_mod_cast hcard

private lemma excedanceCount_le {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.excedanceCount ≤ n := by
  rw [Equiv.Perm.excedanceCount]
  exact (card_filter_le _ _).trans_eq (by simp)

private lemma D_eq_zero_of_lt {n k : ℕ} (h : n < k) : D n k = 0 := by
  rw [D, card_eq_zero, filter_eq_empty_iff]
  intro σ _ hσ
  have hle := excedanceCount_le σ
  rw [hσ.2] at hle
  exact (not_le_of_gt h) hle

private lemma cast_sub_mul_D (n k : ℕ) :
    ((n + 1 - k : ℕ) : ℝ) * D (n + 1) k =
      ((n + 1 : ℝ) - (k : ℝ)) * D (n + 1) k := by
  by_cases h : k ≤ n + 1
  · rw [Nat.cast_sub h]
    push_cast
    ring
  · have hz : D (n + 1) k = 0 := D_eq_zero_of_lt (by lia)
    simp [hz]

private lemma coeff_derangementExcGenPoly_recurrence (n k : ℕ) :
    (derangementExcGenPoly (n + 2)).coeff (k + 1) =
      (k + 1 : ℝ) * (derangementExcGenPoly (n + 1)).coeff (k + 1) +
        ((n + 1 : ℝ) - (k : ℝ)) *
          (derangementExcGenPoly (n + 1)).coeff k +
          (n + 1 : ℝ) * (derangementExcGenPoly n).coeff k := by
  simp_rw [coeff_derangementExcGenPoly]
  rw [D_succ_succ]
  push_cast
  rw [← cast_sub_mul_D n k]

/-- The coefficient recurrence implies the polynomial recurrence. -/
private theorem polynomial_recurrence_of_coefficients {P : ℕ → ℝ[X]} {n : ℕ}
    (hzero : (P (n + 2)).coeff 0 = 0)
    (hrec : ∀ n k : ℕ,
      (P (n + 2)).coeff (k + 1) =
        (k + 1 : ℝ) * (P (n + 1)).coeff (k + 1) +
          ((n + 1 : ℝ) - (k : ℝ)) * (P (n + 1)).coeff k +
            (n + 1 : ℝ) * (P n).coeff k) :
    P (n + 2) =
      X * (C (n + 1 : ℝ) * (P n + P (n + 1)) +
        (1 - X) * (P (n + 1)).derivative) := by
  apply Polynomial.ext
  intro j
  cases j with
  | zero =>
      rw [hzero]
      simp
  | succ k =>
      rw [coeff_X_mul]
      conv_rhs =>
        rw [coeff_add, coeff_C_mul, sub_mul, coeff_sub]
        simp only [one_mul, coeff_add]
      rw [hrec n k]
      cases k with
      | zero =>
          simp only [coeff_X_mul_zero, coeff_derivative]
          push_cast
          ring
      | succ k =>
          simp only [coeff_X_mul, coeff_derivative]
          push_cast
          ring

private lemma derangementExcGenPoly_recurrence (n : ℕ) :
    derangementExcGenPoly (n + 3) =
      X * (C (n + 2 : ℝ) * derangementExcGenPoly (n + 1) +
        C (n + 2 : ℝ) * derangementExcGenPoly (n + 2) +
          (1 - X) * (derangementExcGenPoly (n + 2)).derivative) := by
  have hzero : (derangementExcGenPoly (n + 3)).coeff 0 = 0 := by
    rw [coeff_derangementExcGenPoly]
    simpa [show n + 3 = n + 2 + 1 by lia] using D_zero_right (n + 2)
  have hrec : ∀ m k : ℕ,
      (derangementExcGenPoly (m + 2)).coeff (k + 1) =
        (k + 1 : ℝ) * (derangementExcGenPoly (m + 1)).coeff (k + 1) +
          ((m + 1 : ℝ) - (k : ℝ)) *
            (derangementExcGenPoly (m + 1)).coeff k +
            (m + 1 : ℝ) * (derangementExcGenPoly m).coeff k :=
    fun m k => coeff_derangementExcGenPoly_recurrence m k
  have h := polynomial_recurrence_of_coefficients (n := n + 1) hzero hrec
  convert h using 1
  simp only [Nat.add_assoc, Nat.cast_add, Nat.cast_one]
  ring

private lemma derangementExcGenPoly_zero : derangementExcGenPoly 0 = 1 := by
  apply Polynomial.ext
  intro k
  by_cases hk : k = 0
  · subst k
    rw [coeff_derangementExcGenPoly]
    have hD : D 0 0 = 1 := by decide
    rw [hD]
    norm_num
  · rw [coeff_derangementExcGenPoly, D_eq_zero_of_lt (Nat.pos_of_ne_zero hk)]
    simp only [coeff_one, hk, ite_false, Nat.cast_zero]

private lemma derangementExcGenPoly_one : derangementExcGenPoly 1 = 0 := by
  apply Polynomial.ext
  intro k
  rcases k with _ | _ | k
  · rw [coeff_derangementExcGenPoly, D_zero_right]
    simp
  · rw [coeff_derangementExcGenPoly]
    have hD : D 1 1 = 0 := by decide
    rw [hD]
    simp
  · rw [coeff_derangementExcGenPoly, D_eq_zero_of_lt (by lia)]
    simp

private lemma derangementExcGenPoly_two : derangementExcGenPoly 2 = X := by
  apply Polynomial.ext
  intro k
  rcases k with _ | _ | k
  · rw [coeff_derangementExcGenPoly, D_zero_right]
    simp
  · rw [coeff_derangementExcGenPoly]
    have hD : D 2 1 = 1 := by decide
    rw [hD]
    norm_num
  · by_cases hk : k = 0
    · subst k
      rw [coeff_derangementExcGenPoly]
      have hD : D 2 2 = 0 := by decide
      rw [hD]
      norm_num [coeff_X]
    · have hD : D 2 (k + 1 + 1) = 0 := D_eq_zero_of_lt (by lia)
      rw [coeff_derangementExcGenPoly, hD]
      have hne : ¬ (1 = k + 1 + 1) := by lia
      simp only [coeff_X, hne, ite_false, Nat.cast_zero]

/-- The derangement excedance generating polynomial is the repository family. -/
theorem derangementExcGenPoly_eq_polynomial :
    ∀ n, derangementExcGenPoly n = DerangementTransform.polynomial n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | n
      · rw [derangementExcGenPoly_zero,
          DerangementTransform.polynomial_zero]
      · rw [derangementExcGenPoly_one,
          DerangementTransform.polynomial_one]
      · rw [derangementExcGenPoly_two,
          DerangementTransform.polynomial_two]
      · rw [derangementExcGenPoly_recurrence,
          DerangementTransform.polynomial_recurrence]
        rw [ih (n + 1) (by lia), ih (n + 2) (by lia)]
        have hc : C (n + 2 : ℝ) = (n + 2 : ℝ[X]) := by
          simp [ofNat_def]
        rw [hc]

/-- The derangement excedance generating polynomial is real-rooted for `n ≥ 2`. -/
theorem derangementExcGenPoly_isRealRooted {n : ℕ} (hn : 2 ≤ n) :
    derangementExcGenPoly n ≠ 0 ∧ (derangementExcGenPoly n).Splits := by
  rw [derangementExcGenPoly_eq_polynomial]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  simpa [DerangementTransform.polynomial] using
    isRealRooted_sturmDerangementsExc (m + 1) (by lia)

end RealRooted.DerangementStatistic
