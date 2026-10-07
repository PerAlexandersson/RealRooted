import RealRooted.CombinatorialExamples.JacobiStirling.Descent.Comparison

/-!
# Comparison inductions for Jacobi–Stirling descent polynomials

Ma–Wang (arXiv:2610.03111), Section 4, eqs. (14)–(17).  Write `A_{k,S}` for `descentPoly k S`,
`H_{k+1} = D_{3k} A_{k,∅}` for `hPoly k`, and `E_k = A_{k,[k]}` for the second-order Eulerian
polynomials.  We prove

* (14) `A_{k,{j}} ≺ A_{k,∅}` for `1 ≤ j ≤ k`;
* (15) `A_{k,S} ≺ H_k` for `|S| = 2`;
* (16) `A_{k,S} ≺ A_{k-1,∅}` for `|S| = 3`;
* (17) `E_k ≺ A_{k,S}` for `|S| = k - 1`;
* `E_{k+1} ≺ A_{k,S}` for `|S| = k - 2`.

Each step is one or two applications of Lemma 2 (`IsGood.strictInterleave_insertion`) or
Lemma 3 (`StrictInterleave.insertion_succ`, `StrictInterleave.insertion_same`).
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace JacobiStirlingDescent

theorem IsGood.of_eq {f : ℝ[X]} {d e : ℕ} (hf : IsGood f d) (h : d = e) : IsGood f e :=
  h ▸ hf

theorem IsGood.insertion {f : ℝ[X]} {d L : ℕ} (hf : IsGood f d) (hL : d < L) :
    IsGood (insertion L f) (d + 1) :=
  (hf.insertion_and_strictInterl hL).1

/-! ### The recurrence in subset form -/

theorem descentPoly_succ_insert {k : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.Icc 1 k) :
    descentPoly (k + 1) (insert (k + 1) T) = insertion (3 * k - T.card) (descentPoly k T) := by
  have h : insert (k + 1) T ∩ Finset.Icc 1 k = T := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_Icc]
    constructor
    · rintro ⟨rfl | hx, -, h2⟩
      · lia
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, Finset.mem_Icc.mp (hT hx)⟩
  rw [descentPoly_succ_of_mem (Finset.mem_insert_self _ _), h]

theorem descentPoly_succ_of_subset {k : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.Icc 1 k) :
    descentPoly (k + 1) T =
      insertion (3 * k - T.card + 1) (insertion (3 * k - T.card) (descentPoly k T)) := by
  have hmem : k + 1 ∉ T := fun h => by
    have := Finset.mem_Icc.mp (hT h)
    lia
  rw [descentPoly_succ_of_not_mem hmem, Finset.inter_eq_left.mpr hT]

/-- A subset of `[k + 1]` either contains `k + 1` or is a subset of `[k]`. -/
theorem subset_Icc_succ_cases {k : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 (k + 1)) :
    (k + 1 ∈ S ∧ S.erase (k + 1) ⊆ Finset.Icc 1 k) ∨ S ⊆ Finset.Icc 1 k := by
  by_cases h : k + 1 ∈ S
  · refine Or.inl ⟨h, fun x hx => ?_⟩
    have h1 := Finset.mem_Icc.mp (hS (Finset.mem_of_mem_erase hx))
    have h2 := Finset.ne_of_mem_erase hx
    exact Finset.mem_Icc.mpr ⟨h1.1, by lia⟩
  · refine Or.inr fun x hx => ?_
    have h1 := Finset.mem_Icc.mp (hS hx)
    have h2 : x ≠ k + 1 := fun hx' => h (hx' ▸ hx)
    exact Finset.mem_Icc.mpr ⟨h1.1, by lia⟩

/-- `H_{k+1} = D_{3k} A_{k,∅}`: the descent polynomial after inserting `k + 1` with a bar but
before inserting the pair `(k + 1)(k + 1)`. -/
def hPoly (k : ℕ) : ℝ[X] :=
  insertion (3 * k) (descentPoly k ∅)

theorem descentPoly_succ_empty (k : ℕ) :
    descentPoly (k + 1) ∅ = insertion (3 * k + 1) (hPoly k) := by
  simp [descentPoly_succ_of_subset (Finset.empty_subset _), hPoly]

theorem hPoly_succ (k : ℕ) :
    hPoly (k + 1) = insertion (3 * k + 3) (descentPoly (k + 1) ∅) := by
  rw [hPoly]
  congr 1

theorem isGood_descentPoly_empty (k : ℕ) : IsGood (descentPoly (k + 1) ∅) (2 * k + 1) :=
  (isGood_descentPoly (Finset.empty_subset _)).of_eq (by simp; lia)

theorem isGood_hPoly (k : ℕ) : IsGood (hPoly (k + 1)) (2 * k + 2) :=
  ((isGood_descentPoly_empty k).insertion_and_strictInterl (by lia)).1

/-- `E_{k} = A_{k,[k]}`, the second-order Eulerian polynomial divided by `x`. -/
theorem descentPoly_Icc_succ (k : ℕ) :
    descentPoly (k + 1) (Finset.Icc 1 (k + 1)) =
      insertion (2 * k) (descentPoly k (Finset.Icc 1 k)) := by
  have h : insert (k + 1) (Finset.Icc 1 k) = Finset.Icc 1 (k + 1) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_Icc]
    lia
  rw [← h, descentPoly_succ_insert subset_rfl, Nat.card_Icc]
  congr 1
  lia

theorem isGood_descentPoly_Icc (k : ℕ) : IsGood (descentPoly k (Finset.Icc 1 k)) (k - 1) :=
  (isGood_descentPoly subset_rfl).of_eq (by rw [Nat.card_Icc]; lia)

/-! ### (14): one deleted letter -/

/-- **Ma–Wang, eq. (14).**  `A_{k,{j}} ≺ A_{k,∅}` for `1 ≤ j ≤ k`. -/
theorem strictInterleave_singleton {k j : ℕ} (hj : j ∈ Finset.Icc 1 k) :
    StrictInterleave (descentPoly k {j}) (descentPoly k ∅) := by
  induction k with
  | zero => simp at hj
  | succ k ih =>
    have hsing : (insert (k + 1) ∅ : Finset ℕ) = {k + 1} := rfl
    rcases eq_or_ne j (k + 1) with rfl | hjk
    · -- `A_{k+1,∅} = D_{3k+1} A_{k+1,{k+1}}`.
      have hA : descentPoly (k + 1) {k + 1} = insertion (3 * k) (descentPoly k ∅) := by
        rw [← hsing, descentPoly_succ_insert (Finset.empty_subset _), Finset.card_empty,
          Nat.sub_zero]
      have hgood : IsGood (descentPoly (k + 1) {k + 1}) (2 * k) :=
        (isGood_descentPoly (by simp)).of_eq (by simp; lia)
      have h := hgood.strictInterleave_insertion (L := 3 * k + 1) (by lia)
      have hE : descentPoly (k + 1) ∅ = insertion (3 * k + 1) (descentPoly (k + 1) {k + 1}) := by
        rw [hA, descentPoly_succ_of_subset (Finset.empty_subset _)]
        simp
      rwa [hE]
    · have hjk' : j ∈ Finset.Icc 1 k := by
        have := Finset.mem_Icc.mp hj
        exact Finset.mem_Icc.mpr ⟨this.1, by lia⟩
      have hk : 1 ≤ k := (Finset.mem_Icc.mp hjk').1.trans (Finset.mem_Icc.mp hjk').2
      have hsub : ({j} : Finset ℕ) ⊆ Finset.Icc 1 k := Finset.singleton_subset_iff.mpr hjk'
      have hf : IsGood (descentPoly k {j}) (2 * k - 2) :=
        (isGood_descentPoly hsub).of_eq (by simp; lia)
      have hg : IsGood (descentPoly k ∅) (2 * k - 2 + 1) :=
        (isGood_descentPoly (Finset.empty_subset _)).of_eq (by simp; lia)
      have h1 := (ih hjk').insertion_succ hf hg (L := 3 * k - 1) (by lia)
      have h2 := h1.insertion_succ ((hf.insertion_and_strictInterl (by lia)).1)
        ((hg.insertion_and_strictInterl (by lia)).1) (L := 3 * k - 1 + 1) (by lia)
      rw [descentPoly_succ_of_subset hsub, descentPoly_succ_of_subset (Finset.empty_subset _)]
      convert h2 using 3 <;> simp <;> lia

/-- Removing the top letter `k + 1` from `S ⊆ [k + 1]`. -/
private theorem erase_facts {k : ℕ} {S : Finset ℕ} (hmem : k + 1 ∈ S) :
    S = insert (k + 1) (S.erase (k + 1)) ∧ (S.erase (k + 1)).card = S.card - 1 :=
  ⟨(Finset.insert_erase hmem).symm, Finset.card_erase_of_mem hmem⟩

/-! ### (15): two deleted letters -/

private theorem strictInterleave_hPoly_of_mem (k : ℕ) {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 (k + 2)) (hcard : S.card = 2) (hmem : k + 2 ∈ S) :
    StrictInterleave (descentPoly (k + 2) S) (hPoly (k + 1)) := by
  obtain ⟨-, hT⟩ | hS' := subset_Icc_succ_cases (k := k + 1) hS
  · obtain ⟨hSeq, hTcard⟩ := erase_facts hmem
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hTcard.trans (by rw [hcard]))
    have haT : a ∈ Finset.Icc 1 (k + 1) := hT (ha ▸ Finset.mem_singleton_self a)
    have hf : IsGood (descentPoly (k + 1) {a}) (2 * k) :=
      (isGood_descentPoly (Finset.singleton_subset_iff.mpr haT)).of_eq (by simp; lia)
    have h := (strictInterleave_singleton haT).insertion_succ hf (isGood_descentPoly_empty k)
      (L := 3 * k + 2) (by lia)
    rw [hSeq, descentPoly_succ_insert hT, ha, Finset.card_singleton, hPoly_succ]
    convert h using 2
    lia
  · have := Finset.mem_Icc.mp (hS' hmem)
    lia

/-- **Ma–Wang, eq. (15).**  `A_{k,S} ≺ H_k` for `S ⊆ [k]` with `|S| = 2`, written at
`k + 2`. -/
theorem strictInterleave_hPoly (k : ℕ) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 (k + 2))
    (hcard : S.card = 2) : StrictInterleave (descentPoly (k + 2) S) (hPoly (k + 1)) := by
  induction k generalizing S with
  | zero =>
    by_cases hmem : 2 ∈ S
    · exact strictInterleave_hPoly_of_mem 0 hS hcard hmem
    · have hS' : S ⊆ Finset.Icc 1 1 := fun x hx => by
        have h1 := Finset.mem_Icc.mp (hS hx)
        have : x ≠ 2 := fun h => hmem (h ▸ hx)
        exact Finset.mem_Icc.mpr ⟨h1.1, by lia⟩
      have := Finset.card_le_card hS'
      simp at this
      lia
  | succ m ih =>
    by_cases hmem : m + 1 + 2 ∈ S
    · exact strictInterleave_hPoly_of_mem (m + 1) hS hcard hmem
    have hS' : S ⊆ Finset.Icc 1 (m + 2) := fun x hx => by
      have h1 := Finset.mem_Icc.mp (hS hx)
      have : x ≠ m + 3 := fun h => hmem (h ▸ hx)
      exact Finset.mem_Icc.mpr ⟨h1.1, by lia⟩
    have hf : IsGood (descentPoly (m + 2) S) (2 * m + 1) :=
      (isGood_descentPoly hS').of_eq (by rw [hcard]; lia)
    have h1 := (ih hS' hcard).insertion_same hf (isGood_hPoly m) (L := 3 * m + 4) (by lia)
    have h2 := h1.insertion_succ (hf.insertion (by lia))
      ((isGood_descentPoly_empty (m + 1)).of_eq (by lia)) (L := 3 * m + 5) (by lia)
    rw [descentPoly_succ_of_subset hS', hcard, hPoly_succ, descentPoly_succ_empty,
      show 3 * (m + 2) - 2 = 3 * m + 4 by lia, show 3 * (m + 1) + 3 = 3 * m + 5 + 1 by lia,
      show 3 * (m + 1) + 1 = 3 * m + 4 by lia]
    exact h2

/-! ### (16): three deleted letters -/

private theorem strictInterleave_three_of_mem (k : ℕ) {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 (k + 3)) (hcard : S.card = 3) (hmem : k + 3 ∈ S) :
    StrictInterleave (descentPoly (k + 3) S) (descentPoly (k + 2) ∅) := by
  obtain ⟨-, hT⟩ | hS' := subset_Icc_succ_cases (k := k + 2) hS
  · obtain ⟨hSeq, hTcard⟩ := erase_facts hmem
    rw [hcard] at hTcard
    have hf : IsGood (descentPoly (k + 2) (S.erase (k + 3))) (2 * k + 1) :=
      (isGood_descentPoly hT).of_eq (by rw [hTcard]; lia)
    have h := (strictInterleave_hPoly k hT hTcard).insertion_same hf (isGood_hPoly k)
      (L := 3 * k + 4) (by lia)
    rw [hSeq, descentPoly_succ_insert hT, hTcard, descentPoly_succ_empty]
    convert h using 2
    lia
  · have := Finset.mem_Icc.mp (hS' hmem)
    lia

/-- **Ma–Wang, eq. (16).**  `A_{k,S} ≺ A_{k-1,∅}` for `S ⊆ [k]` with `|S| = 3`, written at
`k + 3`. -/
theorem strictInterleave_three (k : ℕ) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 (k + 3))
    (hcard : S.card = 3) : StrictInterleave (descentPoly (k + 3) S) (descentPoly (k + 2) ∅) := by
  induction k generalizing S with
  | zero =>
    by_cases hmem : 3 ∈ S
    · exact strictInterleave_three_of_mem 0 hS hcard hmem
    · have hS' : S ⊆ Finset.Icc 1 2 := fun x hx => by
        have h1 := Finset.mem_Icc.mp (hS hx)
        have : x ≠ 3 := fun h => hmem (h ▸ hx)
        exact Finset.mem_Icc.mpr ⟨h1.1, by lia⟩
      have := Finset.card_le_card hS'
      simp at this
      lia
  | succ m ih =>
    by_cases hmem : m + 1 + 3 ∈ S
    · exact strictInterleave_three_of_mem (m + 1) hS hcard hmem
    have hS' : S ⊆ Finset.Icc 1 (m + 3) := fun x hx => by
      have h1 := Finset.mem_Icc.mp (hS hx)
      have : x ≠ m + 4 := fun h => hmem (h ▸ hx)
      exact Finset.mem_Icc.mpr ⟨h1.1, by lia⟩
    have hf : IsGood (descentPoly (m + 3) S) (2 * m + 2) :=
      (isGood_descentPoly hS').of_eq (by rw [hcard]; lia)
    have h1 := (ih hS' hcard).insertion_same hf
      ((isGood_descentPoly_empty (m + 1)).of_eq (by lia)) (L := 3 * m + 6) (by lia)
    have h2 := h1.insertion_same (hf.insertion (by lia))
      ((isGood_hPoly (m + 1)).of_eq (by lia)) (L := 3 * m + 7) (by lia)
    rw [descentPoly_succ_of_subset hS', hcard, descentPoly_succ_empty, hPoly_succ,
      show 3 * (m + 3) - 3 = 3 * m + 6 by lia, show 3 * (m + 2) + 1 = 3 * m + 7 by lia,
      show 3 * (m + 1) + 3 = 3 * m + 6 by lia]
    exact h2

/-! ### (17): one retained letter -/

/-- **Ma–Wang, eq. (17).**  `E_k ≺ A_{k,S}` for `S ⊆ [k]` with `|S| = k - 1`, written at
`k + 1`. -/
theorem strictInterleave_Icc_left (k : ℕ) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 (k + 1))
    (hcard : S.card = k) :
    StrictInterleave (descentPoly (k + 1) (Finset.Icc 1 (k + 1))) (descentPoly (k + 1) S) := by
  induction k generalizing S with
  | zero =>
    obtain rfl : S = ∅ := Finset.card_eq_zero.mp hcard
    have h := (isGood_descentPoly_Icc 1).strictInterleave_insertion (L := 1) (by lia)
    have hE :
        descentPoly (0 + 1) ∅ = insertion 1 (descentPoly (0 + 1) (Finset.Icc 1 (0 + 1))) := by
      rw [descentPoly_succ_empty, descentPoly_Icc_succ]
      rfl
    rw [hE]
    exact h
  | succ m ih =>
    rcases subset_Icc_succ_cases hS with ⟨hmem, hT⟩ | hS'
    · obtain ⟨hSeq, hTcard⟩ := erase_facts hmem
      rw [hcard] at hTcard
      have hTcard' : (S.erase (m + 1 + 1)).card = m := by rw [hTcard]; lia
      have hg : IsGood (descentPoly (m + 1) (S.erase (m + 1 + 1))) (m + 1) :=
        (isGood_descentPoly hT).of_eq (by rw [hTcard']; lia)
      have h := (ih hT hTcard').insertion_succ ((isGood_descentPoly_Icc (m + 1)).of_eq (by lia))
        hg (L := 2 * m + 2) (by lia)
      rw [hSeq, descentPoly_succ_insert hT, hTcard', descentPoly_Icc_succ]
      convert h using 2
      lia
    · have hSeq : S = Finset.Icc 1 (m + 1) :=
        Finset.eq_of_subset_of_card_le hS' (by rw [Nat.card_Icc, hcard]; lia)
      subst hSeq
      have hE2 : IsGood (descentPoly (m + 2) (Finset.Icc 1 (m + 2))) (m + 1) :=
        (isGood_descentPoly_Icc (m + 2)).of_eq (by lia)
      have h := hE2.strictInterleave_insertion (L := 2 * m + 3) (by lia)
      have hE : descentPoly (m + 2) (Finset.Icc 1 (m + 1)) =
          insertion (2 * m + 3) (descentPoly (m + 2) (Finset.Icc 1 (m + 2))) := by
        rw [descentPoly_succ_of_subset subset_rfl, descentPoly_Icc_succ (m + 1), Nat.card_Icc,
          show 3 * (m + 1) - (m + 1 + 1 - 1) = 2 * (m + 1) by lia,
          show 2 * (m + 1) + 1 = 2 * m + 3 by lia]
      rw [hE]
      exact h

/-! ### Two retained letters -/

private theorem strictInterleave_Icc_succ_left_of_subset (k : ℕ) {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 (k + 1)) (hcard : S.card = k) :
    StrictInterleave (descentPoly (k + 3) (Finset.Icc 1 (k + 3))) (descentPoly (k + 2) S) := by
  have hf : IsGood (descentPoly (k + 1) (Finset.Icc 1 (k + 1))) k :=
    (isGood_descentPoly_Icc (k + 1)).of_eq (by lia)
  have hg : IsGood (descentPoly (k + 1) S) (k + 1) :=
    (isGood_descentPoly hS).of_eq (by rw [hcard]; lia)
  have h1 := (strictInterleave_Icc_left k hS hcard).insertion_succ hf hg (L := 2 * k + 2)
    (by lia)
  have h2 := h1.insertion_same (hf.insertion (by lia)) (hg.insertion (by lia))
    (L := 2 * k + 4) (by lia)
  rw [descentPoly_Icc_succ (k + 2), descentPoly_Icc_succ (k + 1), descentPoly_succ_of_subset hS,
    hcard, show 2 * (k + 2) = 2 * k + 4 by lia, show 2 * (k + 1) = 2 * k + 2 by lia,
    show 3 * (k + 1) - k = 2 * k + 3 by lia]
  exact h2

/-- **Ma–Wang, Section 4.5.**  `E_{k+1} ≺ A_{k,S}` for `S ⊆ [k]` with `|S| = k - 2`, written
at `k + 2`. -/
theorem strictInterleave_Icc_succ_left (k : ℕ) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 (k + 2))
    (hcard : S.card = k) :
    StrictInterleave (descentPoly (k + 3) (Finset.Icc 1 (k + 3))) (descentPoly (k + 2) S) := by
  induction k generalizing S with
  | zero =>
    obtain rfl : S = ∅ := Finset.card_eq_zero.mp hcard
    exact strictInterleave_Icc_succ_left_of_subset 0 (Finset.empty_subset _) rfl
  | succ m ih =>
    rcases subset_Icc_succ_cases hS with ⟨hmem, hT⟩ | hS'
    · obtain ⟨hSeq, hTcard⟩ := erase_facts hmem
      have hTcard' : (S.erase (m + 1 + 1 + 1)).card = m := by rw [hTcard, hcard]; lia
      have hg : IsGood (descentPoly (m + 2) (S.erase (m + 1 + 1 + 1))) (m + 2 + 1) :=
        (isGood_descentPoly hT).of_eq (by rw [hTcard']; lia)
      have h := (ih hT hTcard').insertion_same ((isGood_descentPoly_Icc (m + 3)).of_eq (by lia))
        hg (L := 2 * m + 6) (by lia)
      rw [hSeq, descentPoly_succ_insert hT, hTcard', descentPoly_Icc_succ (m + 3),
        show 3 * (m + 1 + 1) - m = 2 * m + 6 by lia, show 2 * (m + 3) = 2 * m + 6 by lia]
      exact h
    · exact strictInterleave_Icc_succ_left_of_subset (m + 1) hS' hcard

end JacobiStirlingDescent
end RealRooted
