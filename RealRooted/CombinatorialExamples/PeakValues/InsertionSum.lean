import RealRooted.CombinatorialExamples.PeakValues.Insertion
import RealRooted.Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The fixed-permutation peak-value insertion sum

This file evaluates the sum obtained by inserting the new maximum into every
slot of one fixed permutation.  It is the combinatorial core of the
peak-value recurrence.
-/

open scoped BigOperators

namespace RealRooted

noncomputable section

open MvPolynomial

/-- The insertion slots immediately before and after an old peak position. -/
def peakDestroySlot {n : ℕ} (π : Equiv.Perm (Fin n)) :
    {v // v ∈ peakValues π} × Bool → Fin (n + 1)
  | (⟨v, _⟩, false) => (π.symm v).castSucc
  | (⟨v, _⟩, true) => (π.symm v).succ

lemma peakDestroySlot_injective {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Function.Injective (peakDestroySlot π) := by
  rintro ⟨⟨v, hv⟩, bv⟩ ⟨⟨w, hw⟩, bw⟩ h
  have hvp : IsPeakPosition π (π.symm v) := mem_peakValues_iff.mp hv
  have hwp : IsPeakPosition π (π.symm w) := mem_peakValues_iff.mp hw
  cases bv <;> cases bw
  · have hp : π.symm v = π.symm w := by
      apply Fin.ext
      simpa [peakDestroySlot] using congrArg Fin.val h
    have hvw : v = w := by simpa using congrArg π hp
    subst w
    rfl
  · have hadj : (π.symm w).val + 1 = (π.symm v).val := by
      simpa [peakDestroySlot] using (congrArg Fin.val h).symm
    exact (peakPositions_not_adjacent hwp hvp hadj).elim
  · have hadj : (π.symm v).val + 1 = (π.symm w).val := by
      simpa [peakDestroySlot] using congrArg Fin.val h
    exact (peakPositions_not_adjacent hvp hwp hadj).elim
  · have hp : π.symm v = π.symm w := by
      apply Fin.ext
      simpa [peakDestroySlot] using congrArg Fin.val h
    have hvw : v = w := by simpa using congrArg π hp
    subst w
    rfl

lemma image_peakValues_insertMaximum {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    (peakValues (insertMaximum slot π)).image
        (finSuccEquiv' (Fin.last n)) =
      (if slot = 0 ∨ slot = Fin.last n then ∅ else {none}) ∪
        ((peakValues π).filter
          (fun v => slot ≠ (π.symm v).castSucc ∧
            slot ≠ (π.symm v).succ)).image some := by
  classical
  ext o
  cases o with
  | none =>
      rw [show none ∈ (peakValues (insertMaximum slot π)).image
        (finSuccEquiv' (Fin.last n)) ↔
          Fin.last n ∈ peakValues (insertMaximum slot π) by simp]
      rw [last_mem_peakValues_insertMaximum_iff]
      by_cases hzero : slot = 0
      · simp [hzero]
      by_cases hlast : slot = Fin.last n <;> simp [hzero, hlast]
  | some v =>
      rw [show some v ∈ (peakValues (insertMaximum slot π)).image
        (finSuccEquiv' (Fin.last n)) ↔
          v.castSucc ∈ peakValues (insertMaximum slot π) by simp]
      rw [castSucc_mem_peakValues_insertMaximum_iff]
      by_cases h : slot = 0 ∨ slot = Fin.last n <;> simp [h]

/-- Identify the new maximum and retain precisely the old peaks not destroyed
by the insertion slot. -/
theorem identifyLast_peakValueMonomial_insertMaximum {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    identifyLast n (peakValueMonomial (insertMaximum slot π)) =
      (if slot = 0 ∨ slot = Fin.last n then 1 else X none) *
        ∏ v ∈ (peakValues π).filter
          (fun v => slot ≠ (π.symm v).castSucc ∧
            slot ≠ (π.symm v).succ),
          X (some v) := by
  classical
  simp only [identifyLast, peakValueMonomial, renameEquiv_apply, map_prod,
    rename_X]
  rw [← Finset.prod_image
    (finSuccEquiv' (Fin.last n)).injective.injOn]
  rw [image_peakValues_insertMaximum]
  by_cases h : slot = 0 ∨ slot = Fin.last n
  · simp [h]
  · simp [h, Finset.prod_image (Option.some_injective (Fin n)).injOn]

/-- All slots at which insertion destroys one old peak value. -/
def peakDestroySlots {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Finset (Fin (n + 1)) :=
  Finset.univ.image (peakDestroySlot π)

/-- The two endpoint insertion slots. -/
def peakEndpointSlots (n : ℕ) : Finset (Fin (n + 1)) :=
  {0, Fin.last n}

/-- Interior insertion slots that do not destroy an old peak. -/
def peakSafeSlots {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Finset (Fin (n + 1)) :=
  Finset.univ \ (peakEndpointSlots n ∪ peakDestroySlots π)

lemma peakDestroySlot_ne_zero {n : ℕ} (π : Equiv.Perm (Fin n))
    (p : {v // v ∈ peakValues π} × Bool) :
    peakDestroySlot π p ≠ 0 := by
  rintro h
  rcases p with ⟨⟨v, hv⟩, b⟩
  have hvp : IsPeakPosition π (π.symm v) := mem_peakValues_iff.mp hv
  rcases hvp with ⟨i, k, hij, hjk, hi, hk⟩
  cases b
  · have hval := congrArg Fin.val h
    simp only [peakDestroySlot, Fin.val_castSucc, Fin.val_zero] at hval
    lia
  · have hval := congrArg Fin.val h
    simp only [peakDestroySlot, Fin.val_succ, Fin.val_zero] at hval
    lia

lemma peakDestroySlot_ne_last {n : ℕ} (π : Equiv.Perm (Fin n))
    (p : {v // v ∈ peakValues π} × Bool) :
    peakDestroySlot π p ≠ Fin.last n := by
  rintro h
  rcases p with ⟨⟨v, hv⟩, b⟩
  have hvp : IsPeakPosition π (π.symm v) := mem_peakValues_iff.mp hv
  rcases hvp with ⟨i, k, hij, hjk, hi, hk⟩
  cases b
  · have hval := congrArg Fin.val h
    simp only [peakDestroySlot, Fin.val_castSucc, Fin.val_last] at hval
    have hp_lt := (π.symm v).isLt
    lia
  · have hval := congrArg Fin.val h
    simp only [peakDestroySlot, Fin.val_succ, Fin.val_last] at hval
    have hk_lt := k.isLt
    lia

lemma peakDestroySlots_disjoint_endpointSlots {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    Disjoint (peakDestroySlots π) (peakEndpointSlots n) := by
  rw [Finset.disjoint_left]
  intro slot hslot hend
  rw [peakDestroySlots, Finset.mem_image] at hslot
  rcases hslot with ⟨p, _, rfl⟩
  simp only [peakEndpointSlots, Finset.mem_insert, Finset.mem_singleton] at hend
  exact hend.elim (peakDestroySlot_ne_zero π p)
    (peakDestroySlot_ne_last π p)

lemma card_peakDestroySlots {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (peakDestroySlots π).card = 2 * (peakValues π).card := by
  rw [peakDestroySlots, Finset.card_image_of_injective]
  · simp [Fintype.card_prod, Fintype.card_coe, Nat.mul_comm]
  · exact peakDestroySlot_injective π

lemma peakDestroySlot_filter {n : ℕ} (π : Equiv.Perm (Fin n))
    (p : {v // v ∈ peakValues π} × Bool) :
    (peakValues π).filter
        (fun w => peakDestroySlot π p ≠ (π.symm w).castSucc ∧
          peakDestroySlot π p ≠ (π.symm w).succ) =
      (peakValues π).erase p.1.1 := by
  classical
  rcases p with ⟨⟨v, hv⟩, b⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hw, hbefore, hafter⟩
    refine ⟨?_, hw⟩
    intro hwv
    subst w
    cases b
    · exact hbefore rfl
    · exact hafter rfl
  · rintro ⟨hwv, hw⟩
    refine ⟨hw, ?_, ?_⟩
    · intro heq
      have heq' : peakDestroySlot π (⟨⟨v, hv⟩, b⟩) =
          peakDestroySlot π (⟨⟨w, hw⟩, false⟩) := by
        simpa [peakDestroySlot] using heq
      have hpairs := peakDestroySlot_injective π heq'
      apply hwv
      exact (congrArg (fun q => q.1.1) hpairs).symm
    · intro heq
      have heq' : peakDestroySlot π (⟨⟨v, hv⟩, b⟩) =
          peakDestroySlot π (⟨⟨w, hw⟩, true⟩) := by
        simpa [peakDestroySlot] using heq
      have hpairs := peakDestroySlot_injective π heq'
      apply hwv
      exact (congrArg (fun q => q.1.1) hpairs).symm

lemma filter_eq_peakValues_of_not_mem_peakDestroySlots {n : ℕ}
    (π : Equiv.Perm (Fin n)) (slot : Fin (n + 1))
    (hslot : slot ∉ peakDestroySlots π) :
    (peakValues π).filter
        (fun v => slot ≠ (π.symm v).castSucc ∧
          slot ≠ (π.symm v).succ) = peakValues π := by
  classical
  apply Finset.filter_eq_self.2
  intro v hv
  constructor
  · intro heq
    apply hslot
    rw [peakDestroySlots, Finset.mem_image]
    exact ⟨(⟨v, hv⟩, false), Finset.mem_univ _, heq.symm⟩
  · intro heq
    apply hslot
    rw [peakDestroySlots, Finset.mem_image]
    exact ⟨(⟨v, hv⟩, true), Finset.mem_univ _, heq.symm⟩

@[simp] lemma liftOld_peakValueMonomial {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    liftOld (peakValueMonomial π) =
      ∏ v ∈ peakValues π, X (some v) := by
  classical
  simp [liftOld, peakValueMonomial]

lemma card_peakEndpointSlots (n : ℕ) (hn : 1 ≤ n) :
    (peakEndpointSlots n).card = 2 := by
  have hne : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hval
    lia
  simp [peakEndpointSlots, hne]

lemma card_peakSafeSlots {n : ℕ} (hn : 2 ≤ n)
    (π : Equiv.Perm (Fin n)) :
    (peakSafeSlots π).card = n - 1 - 2 * (peakValues π).card := by
  rw [peakSafeSlots, Finset.card_sdiff]
  simp only [Finset.inter_univ]
  rw [Finset.card_union_of_disjoint
    (peakDestroySlots_disjoint_endpointSlots π).symm]
  rw [card_peakEndpointSlots n (by lia), card_peakDestroySlots]
  simp only [Finset.card_univ, Fintype.card_fin]
  have hcard := card_peakValues_le π
  lia

lemma identifyLast_peakValueMonomial_of_mem_endpointSlots {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n))
    (hslot : slot ∈ peakEndpointSlots n) :
    identifyLast n (peakValueMonomial (insertMaximum slot π)) =
      liftOld (peakValueMonomial π) := by
  have hnotDestroy : slot ∉ peakDestroySlots π := by
    intro hdestroy
    exact Finset.disjoint_left.mp
      (peakDestroySlots_disjoint_endpointSlots π) hdestroy hslot
  rw [identifyLast_peakValueMonomial_insertMaximum,
    filter_eq_peakValues_of_not_mem_peakDestroySlots π slot hnotDestroy,
    liftOld_peakValueMonomial]
  simp only [peakEndpointSlots, Finset.mem_insert,
    Finset.mem_singleton] at hslot
  rcases hslot with rfl | rfl <;> simp

lemma identifyLast_peakValueMonomial_of_mem_safeSlots {n : ℕ}
    (slot : Fin (n + 1)) (π : Equiv.Perm (Fin n))
    (hslot : slot ∈ peakSafeSlots π) :
    identifyLast n (peakValueMonomial (insertMaximum slot π)) =
      X none * liftOld (peakValueMonomial π) := by
  have hboth : slot ∉ peakEndpointSlots n ∧
      slot ∉ peakDestroySlots π := by
    simpa [peakSafeSlots] using hslot
  have hend := hboth.1
  have hdestroy := hboth.2
  rw [identifyLast_peakValueMonomial_insertMaximum,
    filter_eq_peakValues_of_not_mem_peakDestroySlots π slot hdestroy,
    liftOld_peakValueMonomial]
  have hzero : slot ≠ 0 := by
    intro h
    apply hend
    simp [peakEndpointSlots, h]
  have hlast : slot ≠ Fin.last n := by
    intro h
    apply hend
    simp [peakEndpointSlots, h]
  simp [hzero, hlast]

lemma identifyLast_peakValueMonomial_peakDestroySlot {n : ℕ}
    (π : Equiv.Perm (Fin n))
    (p : {v // v ∈ peakValues π} × Bool) :
    identifyLast n
        (peakValueMonomial (insertMaximum (peakDestroySlot π p) π)) =
      X none *
        ∏ v ∈ (peakValues π).erase p.1.1, X (some v) := by
  rw [identifyLast_peakValueMonomial_insertMaximum,
    peakDestroySlot_filter]
  simp [peakDestroySlot_ne_zero, peakDestroySlot_ne_last]

lemma univ_eq_peakEndpointSlots_union_peakDestroySlots_union_peakSafeSlots
    {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (Finset.univ : Finset (Fin (n + 1))) =
      (peakEndpointSlots n ∪ peakDestroySlots π) ∪ peakSafeSlots π := by
  ext slot
  simp [peakSafeSlots]

lemma peakEndpointSlots_union_peakDestroySlots_disjoint_peakSafeSlots
    {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Disjoint (peakEndpointSlots n ∪ peakDestroySlots π)
      (peakSafeSlots π) := by
  rw [Finset.disjoint_left]
  intro slot hunion hsafe
  have hnot : slot ∉ peakEndpointSlots n ∪ peakDestroySlots π := by
    simpa [peakSafeSlots] using hsafe
  exact hnot hunion

/-- The slot sum, separated into endpoint, safe-interior, and peak-destroying
contributions. -/
theorem sum_identifyLast_peakValueMonomial_insertMaximum_normal
    (n : ℕ) (hn : 2 ≤ n) (π : Equiv.Perm (Fin n)) :
    ∑ slot : Fin (n + 1),
        identifyLast n (peakValueMonomial (insertMaximum slot π)) =
      C 2 * liftOld (peakValueMonomial π) +
        C (((n - 1 - 2 * (peakValues π).card : ℕ) : ℝ)) * X none *
          liftOld (peakValueMonomial π) +
        C 2 * X none *
          ∑ v ∈ peakValues π,
            ∏ w ∈ (peakValues π).erase v, X (some w) := by
  classical
  let f : Fin (n + 1) → MvPolynomial (Option (Fin n)) ℝ :=
    fun slot => identifyLast n
      (peakValueMonomial (insertMaximum slot π))
  have hendpoint :
      ∑ slot ∈ peakEndpointSlots n, f slot =
        C 2 * liftOld (peakValueMonomial π) := by
    calc
      ∑ slot ∈ peakEndpointSlots n, f slot =
          ∑ _slot ∈ peakEndpointSlots n,
            liftOld (peakValueMonomial π) := by
        apply Finset.sum_congr rfl
        intro slot hslot
        exact identifyLast_peakValueMonomial_of_mem_endpointSlots
          slot π hslot
      _ = (peakEndpointSlots n).card •
          liftOld (peakValueMonomial π) := by simp
      _ = C 2 * liftOld (peakValueMonomial π) := by
        rw [card_peakEndpointSlots n (by lia)]
        rw [two_nsmul, map_ofNat]
        ring
  have hsafe :
      ∑ slot ∈ peakSafeSlots π, f slot =
        C (((n - 1 - 2 * (peakValues π).card : ℕ) : ℝ)) * X none *
          liftOld (peakValueMonomial π) := by
    calc
      ∑ slot ∈ peakSafeSlots π, f slot =
          ∑ _slot ∈ peakSafeSlots π,
            X none * liftOld (peakValueMonomial π) := by
        apply Finset.sum_congr rfl
        intro slot hslot
        exact identifyLast_peakValueMonomial_of_mem_safeSlots slot π hslot
      _ = (peakSafeSlots π).card •
          (X none * liftOld (peakValueMonomial π)) := by simp
      _ = C (((n - 1 - 2 * (peakValues π).card : ℕ) : ℝ)) * X none *
          liftOld (peakValueMonomial π) := by
        rw [card_peakSafeSlots hn π]
        rw [← Nat.cast_smul_eq_nsmul ℝ, MvPolynomial.smul_eq_C_mul]
        ring
  have hdestroy :
      ∑ slot ∈ peakDestroySlots π, f slot =
        C 2 * X none *
          ∑ v ∈ peakValues π,
            ∏ w ∈ (peakValues π).erase v, X (some w) := by
    rw [peakDestroySlots, Finset.sum_image
      (peakDestroySlot_injective π).injOn]
    simp only [f]
    simp_rw [identifyLast_peakValueMonomial_peakDestroySlot]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    have huniv :
        (Finset.univ : Finset {v // v ∈ peakValues π}) =
          (peakValues π).attach := by
      ext v
      simp
    rw [huniv]
    simp only [Finset.sum_add_distrib]
    have hattach :
        ∑ x ∈ (peakValues π).attach,
            (X none : MvPolynomial (Option (Fin n)) ℝ) *
              ∏ v ∈ (peakValues π).erase x.1, X (some v) =
          ∑ v ∈ peakValues π,
            (X none : MvPolynomial (Option (Fin n)) ℝ) *
              ∏ w ∈ (peakValues π).erase v, X (some w) := by
      exact Finset.sum_attach (peakValues π)
        (fun v => (X none : MvPolynomial (Option (Fin n)) ℝ) *
          ∏ w ∈ (peakValues π).erase v, X (some w))
    rw [hattach]
    rw [← Finset.mul_sum]
    rw [map_ofNat]
    ring
  change ∑ slot, f slot = _
  rw [univ_eq_peakEndpointSlots_union_peakDestroySlots_union_peakSafeSlots π,
    Finset.sum_union
      (peakEndpointSlots_union_peakDestroySlots_disjoint_peakSafeSlots π),
    Finset.sum_union
      (peakDestroySlots_disjoint_endpointSlots π).symm,
    hendpoint, hdestroy, hsafe]
  ring

lemma pderiv_finsetProd_X_some {R σ : Type*} [CommSemiring R]
    [DecidableEq σ] (j : σ) (s : Finset σ) :
    pderiv (some j)
        (∏ v ∈ s, X (some v) : MvPolynomial (Option σ) R) =
      if j ∈ s then ∏ v ∈ s.erase j, X (some v) else 0 := by
  classical
  rw [← Finset.prod_image (Option.some_injective σ).injOn]
  rw [MvPolynomial.pderiv_finsetProd_X]
  simp only [Finset.mem_image, Option.some.injEq, exists_eq_right,
    ← Finset.image_erase (Option.some_injective σ)]
  split_ifs
  · exact Finset.prod_image (Option.some_injective σ).injOn
  · rfl

/-- The differential expression removes one peak variable at a time and
subtracts the original squarefree monomial. -/
theorem sum_one_sub_X_mul_pderiv_liftOld_peakValueMonomial
    {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (∑ j : Fin n,
        (1 - X (some j)) *
          pderiv (some j) (liftOld (peakValueMonomial π))) =
      ∑ j ∈ peakValues π,
        ((∏ v ∈ (peakValues π).erase j, X (some v)) -
          liftOld (peakValueMonomial π)) := by
  classical
  rw [liftOld_peakValueMonomial]
  simp_rw [pderiv_finsetProd_X_some, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ.filter (· ∈ peakValues π)) = peakValues π := by
    ext j
    simp
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sub_mul, one_mul]
  congr 1
  exact Finset.mul_prod_erase (peakValues π)
    (fun v => X (some v)) hj

/-- The analytic side of the fixed-permutation identity has the same
endpoint/safe/destroy normal form as the insertion sum. -/
theorem differential_peakValueMonomial_eq_insertion_normal
    (n : ℕ) (hn : 2 ≤ n) (π : Equiv.Perm (Fin n)) :
    (C 2 + C (n - 1 : ℝ) * X none) *
          liftOld (peakValueMonomial π) +
        C 2 * X none *
          ∑ j : Fin n,
            (1 - X (some j)) *
              pderiv (some j) (liftOld (peakValueMonomial π)) =
      C 2 * liftOld (peakValueMonomial π) +
        C (((n - 1 - 2 * (peakValues π).card : ℕ) : ℝ)) * X none *
          liftOld (peakValueMonomial π) +
        C 2 * X none *
          ∑ j ∈ peakValues π,
            ∏ v ∈ (peakValues π).erase j, X (some v) := by
  rw [sum_one_sub_X_mul_pderiv_liftOld_peakValueMonomial,
    Finset.sum_sub_distrib, Finset.sum_const]
  have hn1 : 1 ≤ n := by lia
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1]
    norm_num
  have hcard := card_peakValues_le π
  have hcast :
      ((n - 1 - 2 * (peakValues π).card : ℕ) : ℝ) =
        (n : ℝ) - 1 - 2 * ((peakValues π).card : ℝ) := by
    rw [Nat.cast_sub hcard, Nat.cast_mul, Nat.cast_ofNat, hcastn]
  rw [hcast]
  rw [← Nat.cast_smul_eq_nsmul ℝ, MvPolynomial.smul_eq_C_mul]
  have hC :
      (C ((n : ℝ) - 1 - 2 * ((peakValues π).card : ℝ)) :
        MvPolynomial (Option (Fin n)) ℝ) =
        C ((n : ℝ) - 1) - C 2 * C ((peakValues π).card : ℝ) := by
    rw [map_sub, map_mul, map_ofNat]
  rw [hC]
  ring

/-- Fixed-permutation insertion identity underlying the peak-value
recurrence. -/
theorem sum_identifyLast_peakValueMonomial_insertMaximum
    (n : ℕ) (hn : 2 ≤ n) (π : Equiv.Perm (Fin n)) :
    ∑ slot : Fin (n + 1),
        identifyLast n (peakValueMonomial (insertMaximum slot π)) =
      (C 2 + C (n - 1 : ℝ) * X none) *
          liftOld (peakValueMonomial π) +
        C 2 * X none *
          ∑ j : Fin n,
            (1 - X (some j)) *
              pderiv (some j) (liftOld (peakValueMonomial π)) :=
  (sum_identifyLast_peakValueMonomial_insertMaximum_normal n hn π).trans
    (differential_peakValueMonomial_eq_insertion_normal n hn π).symm

lemma liftOld_peakValuePolynomial (n : ℕ) :
    liftOld (peakValuePolynomial n) =
      ∑ π : Equiv.Perm (Fin n), liftOld (peakValueMonomial π) := by
  classical
  simp [liftOld, peakValuePolynomial, map_sum]

/-- Rank recurrence for the peak-value polynomial after identifying the newly
inserted maximum with the distinguished variable `none`. -/
theorem identifyLast_peakValuePolynomial_succ
    (n : ℕ) (hn : 2 ≤ n) :
    identifyLast n (peakValuePolynomial (n + 1)) =
      (C 2 + C (n - 1 : ℝ) * X none) *
          liftOld (peakValuePolynomial n) +
        C 2 * X none *
          ∑ j : Fin n,
            (1 - X (some j)) *
              pderiv (some j) (liftOld (peakValuePolynomial n)) := by
  classical
  rw [peakValuePolynomial, identifyLast, map_sum]
  change (∑ ρ : Equiv.Perm (Fin (n + 1)),
    identifyLast n (peakValueMonomial ρ)) = _
  rw [← Equiv.sum_comp (insertMaximumEquiv n)
    (fun ρ => identifyLast n (peakValueMonomial ρ))]
  simp only [insertMaximumEquiv_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [sum_identifyLast_peakValueMonomial_insertMaximum n hn]
  simp only [Finset.sum_add_distrib]
  simp only [C_sub, map_natCast, C_1, liftOld_peakValueMonomial]
  rw [liftOld_peakValuePolynomial]
  simp_rw [liftOld_peakValueMonomial]
  simp_rw [map_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

end

end RealRooted
