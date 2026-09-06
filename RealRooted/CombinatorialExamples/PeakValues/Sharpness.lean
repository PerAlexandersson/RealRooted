import RealRooted.CombinatorialExamples.PeakValues.Insertion

open scoped BigOperators

namespace RealRooted

noncomputable section

lemma castSucc_mem_peakValues_appendMaximum_iff {n : ℕ}
    (π : Equiv.Perm (Fin n)) (v : Fin n) :
    v.castSucc ∈ peakValues (insertMaximum (Fin.last n) π) ↔
      v ∈ peakValues π := by
  rw [castSucc_mem_peakValues_insertMaximum_iff]
  constructor
  · exact fun h => h.1
  · intro hv
    refine ⟨hv, (Fin.castSucc_lt_last _).ne', ?_⟩
    intro heq
    rcases mem_peakValues_iff.mp hv with ⟨i, k, hij, hjk, hi, hk⟩
    have heqval := congrArg Fin.val heq
    have hklt := k.isLt
    simp only [Fin.val_last, Fin.val_succ] at heqval
    lia

lemma peakValues_appendMaximum_eq {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    peakValues (insertMaximum (Fin.last n) π) =
      (peakValues π).image Fin.castSucc := by
  ext w
  refine Fin.lastCases ?_ (fun v => ?_) w
  · rw [last_mem_peakValues_insertMaximum_iff]
    simp
  · rw [castSucc_mem_peakValues_appendMaximum_iff]
    simp

lemma card_peakValues_appendMaximum {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    (peakValues (insertMaximum (Fin.last n) π)).card =
      (peakValues π).card := by
  rw [peakValues_appendMaximum_eq]
  exact Finset.card_image_of_injective _ (Fin.castSucc_injective n)

lemma penultimate_not_peak_after_append {n : ℕ}
    (π : Equiv.Perm (Fin n)) (j : Fin (n + 1))
    (hj : j.val + 1 = n) :
    ¬ IsPeakPosition (insertMaximum (Fin.last n) π) j := by
  rintro ⟨i, k, hij, hjk, hi, hk⟩
  have hk_last : k = Fin.last n := Fin.ext (by simp; lia)
  subst k
  rw [insertMaximum_apply_slot] at hk
  have hbadval : n < (insertMaximum (Fin.last n) π j).val := hk
  have hjlt := (insertMaximum (Fin.last n) π j).isLt
  lia

lemma castSucc_mem_peakValues_growTwo_iff {n : ℕ}
    (π : Equiv.Perm (Fin n)) (v : Fin (n + 1)) :
    v.castSucc ∈ peakValues
        (insertMaximum (Fin.last n).castSucc
          (insertMaximum (Fin.last n) π)) ↔
      v ∈ peakValues (insertMaximum (Fin.last n) π) := by
  rw [castSucc_mem_peakValues_insertMaximum_iff]
  constructor
  · exact fun h => h.1
  · intro hv
    refine ⟨hv, ?_, ?_⟩
    · intro heq
      rcases mem_peakValues_iff.mp hv with
        ⟨i, k, hij, hjk, hi, hk⟩
      have heqval := congrArg Fin.val heq
      have hklt := k.isLt
      simp only [Fin.val_castSucc, Fin.val_last] at heqval
      lia
    · intro heq
      have heqval := congrArg Fin.val heq
      simp only [Fin.val_castSucc, Fin.val_last, Fin.val_succ] at heqval
      exact penultimate_not_peak_after_append π
        ((insertMaximum (Fin.last n) π).symm v) (by lia)
        (mem_peakValues_iff.mp hv)

lemma peakValues_growTwo_eq {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) :
    peakValues
        (insertMaximum (Fin.last n).castSucc
          (insertMaximum (Fin.last n) π)) =
      insert (Fin.last (n + 1))
        ((peakValues (insertMaximum (Fin.last n) π)).image
          Fin.castSucc) := by
  ext w
  refine Fin.lastCases ?_ (fun v => ?_) w
  · have hs0 : (Fin.last n).castSucc ≠ (0 : Fin (n + 2)) := by
      intro heq
      have heqval := congrArg Fin.val heq
      simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero] at heqval
      lia
    rw [last_mem_peakValues_insertMaximum_iff]
    simp [hs0]
  · rw [castSucc_mem_peakValues_growTwo_iff]
    simp

lemma card_peakValues_growTwo {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) :
    (peakValues
        (insertMaximum (Fin.last n).castSucc
          (insertMaximum (Fin.last n) π))).card =
      (peakValues π).card + 1 := by
  rw [peakValues_growTwo_eq hn]
  have hlast :
      Fin.last (n + 1) ∉
        (peakValues (insertMaximum (Fin.last n) π)).image
          Fin.castSucc := by simp
  rw [Finset.card_insert_of_notMem hlast,
    Finset.card_image_of_injective _
      (Fin.castSucc_injective (n + 1)),
    card_peakValues_appendMaximum]

/-- The upper bound on the number of peak values is attained at every rank. -/
theorem exists_card_peakValues_eq (n : ℕ) :
    ∃ π : Equiv.Perm (Fin n),
      (peakValues π).card = (n - 1) / 2 := by
  induction n using Nat.twoStepInduction with
  | zero =>
      refine ⟨1, ?_⟩
      have h := card_peakValues_le (1 : Equiv.Perm (Fin 0))
      change (peakValues (1 : Equiv.Perm (Fin 0))).card = 0
      lia
  | one =>
      refine ⟨1, ?_⟩
      have h := card_peakValues_le (1 : Equiv.Perm (Fin 1))
      change (peakValues (1 : Equiv.Perm (Fin 1))).card = 0
      lia
  | more n hn hn1 =>
      cases n with
      | zero =>
          refine ⟨1, ?_⟩
          have h := card_peakValues_le (1 : Equiv.Perm (Fin 2))
          change (peakValues (1 : Equiv.Perm (Fin 2))).card = 0
          lia
      | succ m =>
          obtain ⟨π, hπ⟩ := hn
          refine
            ⟨insertMaximum (Fin.last (m + 1)).castSucc
              (insertMaximum (Fin.last (m + 1)) π), ?_⟩
          rw [card_peakValues_growTwo (Nat.succ_pos m), hπ]
          simp [Nat.add_div_right]

lemma prod_X_eq_monomial_sum_single {σ : Type*}
    (s : Finset σ) :
    (∏ v ∈ s, (MvPolynomial.X v : MvPolynomial σ ℝ)) =
      MvPolynomial.monomial (∑ v ∈ s, Finsupp.single v 1) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      simp [MvPolynomial.X, MvPolynomial.monomial_mul]

lemma coeff_prod_one_add_X_nonneg {σ : Type*}
    (s : Finset σ) (m : σ →₀ ℕ) :
    0 ≤ MvPolynomial.coeff m
      (∏ v ∈ s, (1 + MvPolynomial.X v : MvPolynomial σ ℝ)) := by
  classical
  rw [Finset.prod_one_add]
  simp_rw [MvPolynomial.coeff_sum]
  apply Finset.sum_nonneg
  intro t ht
  rw [prod_X_eq_monomial_sum_single]
  simp only [MvPolynomial.coeff_monomial]
  split <;> norm_num

lemma one_le_coeff_prod_one_add_X {σ : Type*}
    (s : Finset σ) :
    1 ≤ MvPolynomial.coeff (∑ v ∈ s, Finsupp.single v 1)
      (∏ v ∈ s, (1 + MvPolynomial.X v : MvPolynomial σ ℝ)) := by
  classical
  rw [Finset.prod_one_add]
  simp_rw [MvPolynomial.coeff_sum]
  calc
    1 = MvPolynomial.coeff (∑ v ∈ s, Finsupp.single v 1)
        (∏ i ∈ s, (MvPolynomial.X i : MvPolynomial σ ℝ)) := by
      rw [prod_X_eq_monomial_sum_single]
      simp
    _ ≤ ∑ t ∈ s.powerset,
        MvPolynomial.coeff (∑ v ∈ s, Finsupp.single v 1)
          (∏ i ∈ t, (MvPolynomial.X i : MvPolynomial σ ℝ)) := by
      refine Finset.single_le_sum
        (f := fun t : Finset σ =>
          MvPolynomial.coeff (∑ v ∈ s, Finsupp.single v 1)
            (∏ i ∈ t, (MvPolynomial.X i : MvPolynomial σ ℝ)))
        (s := s.powerset) (a := s) ?_ ?_
      · intro t ht
        rw [prod_X_eq_monomial_sum_single]
        simp only [MvPolynomial.coeff_monomial]
        split <;> norm_num
      · exact Finset.mem_powerset_self s

lemma one_le_coeff_peakValueTranslated {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    1 ≤ MvPolynomial.coeff
      (∑ v ∈ peakValues π, Finsupp.single v 1)
      (peakValueTranslated n) := by
  let m := ∑ v ∈ peakValues π, Finsupp.single v 1
  calc
    1 ≤ MvPolynomial.coeff m
        (∏ v ∈ peakValues π,
          (1 + MvPolynomial.X v : MvPolynomial (Fin n) ℝ)) :=
      one_le_coeff_prod_one_add_X (peakValues π)
    _ ≤ MvPolynomial.coeff m (peakValueTranslated n) := by
      unfold peakValueTranslated
      simp_rw [MvPolynomial.coeff_sum]
      refine Finset.single_le_sum
        (f := fun τ : Equiv.Perm (Fin n) =>
          MvPolynomial.coeff m
            (∏ v ∈ peakValues τ,
              (1 + MvPolynomial.X v : MvPolynomial (Fin n) ℝ)))
        (s := Finset.univ) (a := π) ?_ (Finset.mem_univ π)
      intro τ hτ
      exact coeff_prod_one_add_X_nonneg (peakValues τ) m

lemma sum_sum_single_one {σ : Type*} (s : Finset σ) :
    (∑ v ∈ s, Finsupp.single v 1).sum (fun _ e => e) = s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finsupp.sum_add_index] <;>
        simp [ih, Finset.card_insert_of_notMem ha, Nat.add_comm]

lemma card_peakValues_le_totalDegree {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    (peakValues π).card ≤ (peakValueTranslated n).totalDegree := by
  let m := ∑ v ∈ peakValues π, Finsupp.single v 1
  have hcoeff : MvPolynomial.coeff m (peakValueTranslated n) ≠ 0 := by
    have h := one_le_coeff_peakValueTranslated π
    change 1 ≤ MvPolynomial.coeff m (peakValueTranslated n) at h
    linarith
  have hm : m ∈ (peakValueTranslated n).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  calc
    (peakValues π).card = m.sum (fun _ e => e) := by
      symm
      exact sum_sum_single_one (peakValues π)
    _ ≤ (peakValueTranslated n).totalDegree :=
      MvPolynomial.le_totalDegree hm

/-- The translated peak-value polynomial has the largest possible total degree. -/
theorem totalDegree_peakValueTranslated (n : ℕ) :
    (peakValueTranslated n).totalDegree = (n - 1) / 2 := by
  apply le_antisymm (totalDegree_peakValueTranslated_le n)
  obtain ⟨π, hπ⟩ := exists_card_peakValues_eq n
  rw [← hπ]
  exact card_peakValues_le_totalDegree π

end

end RealRooted
