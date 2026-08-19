import Mathlib.Tactic
import RealRooted.LiebSokalOperator

/-!
# Elementary symmetric differential operators

This file computes the action of an elementary symmetric polynomial in the
partial derivatives on another elementary symmetric polynomial.
-/

open BigOperators

namespace RealRooted

noncomputable section

private theorem pderiv_prod_X {R sigma : Type*} [CommSemiring R] [DecidableEq sigma]
    (x : sigma) (t : Finset sigma) :
    MvPolynomial.pderiv x
        (∏ y ∈ t, MvPolynomial.X y : MvPolynomial sigma R) =
      if x ∈ t then ∏ y ∈ t.erase x, MvPolynomial.X y else 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      by_cases hax : a = x
      · subst a
        simp [ha, ih]
      · have hxa : x ≠ a := Ne.symm hax
        by_cases hxt : x ∈ t
        · simp only [Finset.prod_insert ha, MvPolynomial.pderiv_mul,
            MvPolynomial.pderiv_X_of_ne hax, ih, hxt, if_pos, zero_mul,
            zero_add, Finset.mem_insert, hxa]
          split
          · have haerase : a ∉ t.erase x := fun h => ha (Finset.erase_subset x t h)
            rw [Finset.erase_insert_of_ne hax, Finset.prod_insert haerase]
          · rename_i h
            exact (h (Or.inr trivial)).elim
        · simp [ha, hax, hxa, hxt, ih]

private def esymmOn {R sigma : Type*} [CommSemiring R]
    (u : Finset sigma) (j : ℕ) : MvPolynomial sigma R :=
  ∑ t ∈ u.powersetCard j, ∏ x ∈ t, MvPolynomial.X x

private theorem pderiv_esymmOn {R sigma : Type*} [CommSemiring R]
    [DecidableEq sigma] (x : sigma) (u : Finset sigma) (j : ℕ) :
    MvPolynomial.pderiv x (esymmOn (R := R) u j) =
      if x ∈ u ∧ 0 < j then esymmOn (R := R) (u.erase x) (j - 1) else 0 := by
  by_cases hxu : x ∈ u
  · by_cases hj : 0 < j
    · rw [if_pos ⟨hxu, hj⟩]
      unfold esymmOn
      simp only [map_sum, pderiv_prod_X]
      rw [← Finset.sum_filter]
      apply Finset.sum_bij (fun t ht => t.erase x)
      · intro t ht
        rw [Finset.mem_filter, Finset.mem_powersetCard] at ht
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.erase_subset_erase x ht.1.1, by
          rw [Finset.card_erase_of_mem ht.2, ht.1.2]⟩
      · intro t₁ ht₁ t₂ ht₂ heq
        rw [Finset.mem_filter] at ht₁ ht₂
        calc
          t₁ = insert x (t₁.erase x) := (Finset.insert_erase ht₁.2).symm
          _ = insert x (t₂.erase x) := congrArg (insert x) heq
          _ = t₂ := Finset.insert_erase ht₂.2
      · intro s hs
        rw [Finset.mem_powersetCard] at hs
        have hxs : x ∉ s := by
          intro hxs
          exact Finset.notMem_erase x u (hs.1 hxs)
        refine ⟨insert x s, ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_powersetCard]
          exact ⟨⟨Finset.insert_subset hxu
            (hs.1.trans (Finset.erase_subset x u)), by
              rw [Finset.card_insert_of_notMem hxs, hs.2]
              lia⟩, Finset.mem_insert_self x s⟩
        · simp [hxs]
      · intro t ht
        rfl
    · rw [if_neg (by simp [hj])]
      have : j = 0 := Nat.eq_zero_of_not_pos hj
      subst j
      simp [esymmOn]
  · rw [if_neg (by simp [hxu])]
    unfold esymmOn
    simp only [map_sum, pderiv_prod_X]
    apply Finset.sum_eq_zero
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    simp [show x ∉ t from fun hxt => hxu (ht.1 hxt)]

private def listPDeriv {R sigma : Type*} [CommSemiring R]
    (l : List sigma) (P : MvPolynomial sigma R) : MvPolynomial sigma R :=
  l.foldl (fun Q x => MvPolynomial.pderiv x Q) P

@[simp] private theorem listPDeriv_zero {R sigma : Type*} [CommSemiring R]
    (l : List sigma) : listPDeriv l (0 : MvPolynomial sigma R) = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      change listPDeriv l (MvPolynomial.pderiv x 0) = 0
      rw [map_zero]
      exact ih

private theorem listPDeriv_esymmOn {R sigma : Type*} [CommSemiring R]
    [DecidableEq sigma] (l : List sigma) (hl : l.Nodup)
    (u : Finset sigma) (hlu : l.toFinset ⊆ u) (j : ℕ) :
    listPDeriv l (esymmOn (R := R) u j) =
      if l.length ≤ j then
        esymmOn (R := R) (u \ l.toFinset) (j - l.length)
      else 0 := by
  induction l generalizing u j with
  | nil => simp [listPDeriv]
  | cons x l ih =>
      have hxu : x ∈ u := hlu (by simp)
      have hl : l.Nodup := List.nodup_cons.mp hl |>.2
      have hxl : x ∉ l := List.nodup_cons.mp ‹(x :: l).Nodup› |>.1
      have hlu' : l.toFinset ⊆ u.erase x := by
        intro y hy
        rw [Finset.mem_erase]
        exact ⟨fun hyx => hxl (by simpa [hyx] using hy), hlu (by simp [hy])⟩
      change listPDeriv l (MvPolynomial.pderiv x (esymmOn (R := R) u j)) = _
      rw [pderiv_esymmOn]
      by_cases hj : 0 < j
      · rw [if_pos ⟨hxu, hj⟩, ih hl (u.erase x) hlu' (j - 1)]
        simp only [List.length_cons]
        by_cases hlen : l.length + 1 ≤ j
        · rw [if_pos hlen, if_pos (by lia)]
          have hset : (u.erase x) \ l.toFinset = u \ (x :: l).toFinset := by
            ext y
            simp [and_assoc, and_left_comm]
          have hnat : j - 1 - l.length = j - (l.length + 1) := by lia
          rw [hset, hnat]
        · rw [if_neg hlen, if_neg (by
            intro h
            apply hlen
            lia)]
      · have hj0 : j = 0 := Nat.eq_zero_of_not_pos hj
        subst j
        simp

private theorem applyMonomialDifferentialAlong_indicator
    {R sigma : Type*} [CommSemiring R] [DecidableEq sigma]
    (l : List sigma) (s : Finset sigma) (P : MvPolynomial sigma R) :
    RealRooted.applyMonomialDifferentialAlong l
        (Finsupp.indicator s (fun _ _ => 1)) P =
      listPDeriv (l.filter (· ∈ s)) P := by
  induction l generalizing P with
  | nil => rfl
  | cons x l ih =>
      change RealRooted.applyMonomialDifferentialAlong l
          (Finsupp.indicator s (fun _ _ => 1))
          (RealRooted.iteratedPDerivAt x
            ((Finsupp.indicator s (fun _ _ => 1)) x) P) = _
      by_cases hxs : x ∈ s
      · have hfilter :
            (x :: l).filter (fun y => decide (y ∈ s)) =
              x :: l.filter (fun y => decide (y ∈ s)) := by simp [hxs]
        rw [hfilter]
        simp only [Finsupp.indicator_of_mem hxs, RealRooted.iteratedPDerivAt]
        change _ = listPDeriv (l.filter (· ∈ s)) (MvPolynomial.pderiv x P)
        exact ih (MvPolynomial.pderiv x P)
      · have hfilter :
            (x :: l).filter (fun y => decide (y ∈ s)) =
              l.filter (fun y => decide (y ∈ s)) := by simp [hxs]
        rw [hfilter]
        simp only [Finsupp.indicator_of_notMem hxs,
          RealRooted.iteratedPDerivAt]
        exact ih P

private theorem applyMonomialDifferential_indicator_esymm
    {R sigma : Type*} [CommSemiring R] [Fintype sigma] [DecidableEq sigma]
    (s : Finset sigma) (j : ℕ) :
    RealRooted.applyMonomialDifferential
        (Finsupp.indicator s (fun _ _ => 1))
        (MvPolynomial.esymm sigma R j) =
      if s.card ≤ j then
        esymmOn (R := R) (Finset.univ \ s) (j - s.card)
      else 0 := by
  rw [← RealRooted.applyMonomialDifferentialAlong_differentialVariableOrder,
    applyMonomialDifferentialAlong_indicator]
  let l := (RealRooted.differentialVariableOrder sigma).filter
    (fun x => decide (x ∈ s))
  have hl : l.Nodup :=
    (RealRooted.nodup_differentialVariableOrder sigma).filter _
  have hfinset : l.toFinset = s := by
    ext x
    simp [l]
  have hlength : l.length = s.card := by rw [← hfinset, List.toFinset_card_of_nodup hl]
  change listPDeriv l (esymmOn (R := R) Finset.univ j) = _
  rw [listPDeriv_esymmOn l hl Finset.univ (by simp) j, hlength, hfinset]

private theorem powersetCard_sdiff {sigma : Type*} [DecidableEq sigma]
    (u s : Finset sigma) (k : ℕ) :
    (u \ s).powersetCard k =
      (u.powersetCard k).filter (fun t => Disjoint s t) := by
  ext t
  rw [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powersetCard]
  constructor
  · rintro ⟨htu, htcard⟩
    refine ⟨⟨?_, htcard⟩, Finset.disjoint_left.mpr ?_⟩
    · intro x hxt
      exact (Finset.mem_sdiff.mp (htu hxt)).1
    · intro x hxs hxt
      exact (Finset.mem_sdiff.mp (htu hxt)).2 hxs
  · rintro ⟨⟨htu, htcard⟩, hdisj⟩
    refine ⟨?_, htcard⟩
    intro x hxt
    exact Finset.mem_sdiff.mpr
      ⟨htu hxt, fun hxs => Finset.disjoint_left.mp hdisj hxs hxt⟩

private theorem sum_esymmOn_sdiff {R sigma : Type*} [CommSemiring R]
    [Fintype sigma] [DecidableEq sigma] (i k : ℕ) :
    ∑ s ∈ Finset.univ.powersetCard i,
        esymmOn (R := R) (Finset.univ \ s) k =
      (Fintype.card sigma - k).choose i •
        MvPolynomial.esymm sigma R k := by
  unfold esymmOn
  simp_rw [powersetCard_sdiff]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  change (∑ t ∈ Finset.univ.powersetCard k,
      ∑ s ∈ Finset.univ.powersetCard i,
        if Disjoint s t then ∏ x ∈ t, MvPolynomial.X x else 0) =
    (Fintype.card sigma - k).choose i •
      ∑ t ∈ Finset.univ.powersetCard k, ∏ x ∈ t, MvPolynomial.X x
  rw [← Finset.sum_nsmul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_powersetCard] at ht
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ.powersetCard i).filter (fun s => Disjoint s t) =
        (Finset.univ \ t).powersetCard i := by
    rw [powersetCard_sdiff]
    apply Finset.filter_congr
    intro s hs
    exact disjoint_comm
  rw [hfilter, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset (Finset.subset_univ t), Finset.card_univ,
    ht.2]

/-- The sum of all squarefree differential monomials of a fixed order. -/
def elementaryDifferential {R sigma : Type*} [CommSemiring R]
    [Fintype sigma] (i : ℕ) (P : MvPolynomial sigma R) :
    MvPolynomial sigma R :=
  ∑ s ∈ Finset.univ.powersetCard i,
    RealRooted.applyMonomialDifferential
      (Finsupp.indicator s (fun _ _ => 1)) P

/-- An elementary differential operator acting on an elementary symmetric polynomial. -/
theorem elementaryDifferential_esymm
    {R sigma : Type*} [CommSemiring R] [Fintype sigma] (i j : ℕ) :
    elementaryDifferential i (MvPolynomial.esymm sigma R j) =
      if i ≤ j then
        (Fintype.card sigma + i - j).choose i •
          MvPolynomial.esymm sigma R (j - i)
      else 0 := by
  classical
  unfold elementaryDifferential
  by_cases hij : i ≤ j
  · rw [if_pos hij]
    calc
      ∑ s ∈ Finset.univ.powersetCard i,
          RealRooted.applyMonomialDifferential
            (Finsupp.indicator s (fun _ _ => 1))
            (MvPolynomial.esymm sigma R j) =
          ∑ s ∈ Finset.univ.powersetCard i,
            esymmOn (R := R) (Finset.univ \ s) (j - i) := by
              apply Finset.sum_congr rfl
              intro s hs
              have hcard : s.card = i := (Finset.mem_powersetCard.mp hs).2
              rw [applyMonomialDifferential_indicator_esymm, if_pos (by lia), hcard]
      _ = (Fintype.card sigma - (j - i)).choose i •
          MvPolynomial.esymm sigma R (j - i) :=
            sum_esymmOn_sdiff i (j - i)
      _ = (Fintype.card sigma + i - j).choose i •
          MvPolynomial.esymm sigma R (j - i) := by
            congr 2
            lia
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro s hs
    have hcard : s.card = i := (Finset.mem_powersetCard.mp hs).2
    rw [applyMonomialDifferential_indicator_esymm, if_neg (by lia)]

private theorem applyNegDifferential_finsetSum_left
    {R sigma I : Type*} [CommRing R] [Fintype sigma]
    (s : Finset I) (F : I → MvPolynomial sigma R)
    (G : MvPolynomial sigma R) :
    RealRooted.applyNegDifferential (∑ x ∈ s, F x) G =
      ∑ x ∈ s, RealRooted.applyNegDifferential (F x) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
      rw [Finset.sum_insert hxs, RealRooted.applyNegDifferential_add_left,
        ih, Finset.sum_insert hxs]

private theorem indicator_totalDegree {sigma : Type*}
    (s : Finset sigma) :
    (Finsupp.indicator s (fun _ _ => 1)).sum (fun _ n => n) = s.card := by
  classical
  rw [Finsupp.sum_indicator_index_eq_sum_attach _ (by simp)]
  simp

/-- An elementary symmetric polynomial in the negative partial derivatives
acts as a signed elementary differential operator. -/
theorem applyNegDifferential_esymm_left
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (i : ℕ) (G : MvPolynomial sigma R) :
    RealRooted.applyNegDifferential (MvPolynomial.esymm sigma R i) G =
      MvPolynomial.C ((-1 : R) ^ i) * elementaryDifferential i G := by
  classical
  rw [MvPolynomial.esymm_eq_sum_monomial,
    applyNegDifferential_finsetSum_left]
  unfold elementaryDifferential
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hcard : s.card = i := (Finset.mem_powersetCard.mp hs).2
  rw [← Finsupp.indicator_eq_sum_single,
    RealRooted.applyNegDifferential_monomial, indicator_totalDegree, hcard]
  simp

/-- An elementary symmetric polynomial in the negative partial derivatives
acting on another elementary symmetric polynomial. -/
theorem applyNegDifferential_esymm
    {R sigma : Type*} [CommRing R] [Fintype sigma] (i j : ℕ) :
    RealRooted.applyNegDifferential
        (MvPolynomial.esymm sigma R i) (MvPolynomial.esymm sigma R j) =
      if i ≤ j then
        MvPolynomial.C ((-1 : R) ^ i) *
          ((Fintype.card sigma + i - j).choose i •
            MvPolynomial.esymm sigma R (j - i))
      else 0 := by
  rw [applyNegDifferential_esymm_left, elementaryDifferential_esymm]
  by_cases hij : i ≤ j
  · rw [if_pos hij, if_pos hij]
  · rw [if_neg hij, if_neg hij, mul_zero]

end

end RealRooted
