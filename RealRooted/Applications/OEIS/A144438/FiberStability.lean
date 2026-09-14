import RealRooted.Applications.OEIS.A144438.EligibleSupport
import RealRooted.BooleanSwapOrbit

/-!
# Stable normalized decoration fibers

This file sums comparison-bottom monomials over every eligible decoration of
a normalized Deco code. Adding one eligible start acts by a variable-swap sum.
The full Boolean orbit factors into a fixed squarefree monomial, a power of two
from inactive swaps, and one stable linear factor for each active swap.
-/

namespace RealRooted.Applications.OEIS.DecoNormalizedCode

open scoped BigOperators

noncomputable section

/-- Adding an eligible start renames its comparison-bottom monomial by the
corresponding final-label swap. -/
theorem comparisonBottomMonomial_insert {R : Type*} [CommSemiring R]
    {h : Nat} {c : DecoNormalizedCode h}
    {s : Finset (EligibleStart c)} {j : EligibleStart c} (hj : j ∉ s) :
    MinimumInsertionWord.comparisonBottomMonomial
        ((Decoration.ofEligibleFinset (insert j s)).exceptionalize.inverseWord) =
      MvPolynomial.rename (finalSwap h j.1)
        (MinimumInsertionWord.comparisonBottomMonomial
          ((Decoration.ofEligibleFinset s).exceptionalize.inverseWord) :
            MvPolynomial Nat R) := by
  rw [Decoration.insert_inverseWord_eq_swapWord hj]
  have hcomp : MinimumInsertionWord.comparisonWord
      (((Decoration.ofEligibleFinset s).exceptionalize.inverseWord).map
        (finalSwap h j.1)) =
      MinimumInsertionWord.comparisonWord
        (Decoration.ofEligibleFinset s).exceptionalize.inverseWord := by
    change MinimumInsertionWord.comparisonWord
        (swapWord h j.1
          (Decoration.ofEligibleFinset s).exceptionalize.inverseWord) = _
    rw [← Decoration.insert_inverseWord_eq_swapWord hj]
    exact Decoration.insert_inverseWord_comparisonWord_eq hj
  symm
  exact MinimumInsertionWord.rename_comparisonBottomMonomial
    (R := R) (finalSwap h j.1).toEmbedding _ hcomp

/-- The comparison-bottom monomial sum over all decorations supported in
`s`. -/
noncomputable def subsetFiberPolynomial {R : Type*} [CommSemiring R]
    {h : Nat} (c : DecoNormalizedCode h) (s : Finset (EligibleStart c)) :
    MvPolynomial Nat R :=
  ∑ t ∈ s.powerset,
    MinimumInsertionWord.comparisonBottomMonomial
      (Decoration.ofEligibleFinset t).exceptionalize.inverseWord

@[simp] theorem subsetFiberPolynomial_empty {R : Type*} [CommSemiring R]
    {h : Nat} (c : DecoNormalizedCode h) :
    subsetFiberPolynomial (R := R) c ∅ =
      MinimumInsertionWord.comparisonBottomMonomial c.toDecoCode.inverseWord := by
  simp [subsetFiberPolynomial]

/-- Inserting one allowed start applies the corresponding polynomial
swap-sum operator. -/
theorem subsetFiberPolynomial_insert {R : Type*} [CommSemiring R]
    {h : Nat} (c : DecoNormalizedCode h) {s : Finset (EligibleStart c)}
    {j : EligibleStart c} (hj : j ∉ s) :
    subsetFiberPolynomial (R := R) c (insert j s) =
      MvPolynomial.swapSum (leftLabel h j.1) (rightLabel h j.1)
        (subsetFiberPolynomial (R := R) c s) := by
  rw [subsetFiberPolynomial, Finset.powerset_insert]
  have hdisjoint : Disjoint s.powerset (Finset.image (insert j) s.powerset) := by
    rw [Finset.disjoint_left]
    intro t ht hti
    rw [Finset.mem_image] at hti
    obtain ⟨u, hu, hut⟩ := hti
    have hjt : j ∈ t := by rw [← hut]; simp
    exact hj (Finset.mem_of_subset (Finset.mem_powerset.mp ht) hjt)
  rw [Finset.sum_union hdisjoint]
  rw [Finset.sum_image]
  · rw [MvPolynomial.swapSum, subsetFiberPolynomial]
    rw [map_sum]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro t ht
    have hjt : j ∉ t := fun hmem =>
      hj (Finset.mem_of_subset (Finset.mem_powerset.mp ht) hmem)
    rw [comparisonBottomMonomial_insert hjt]
    rfl
  · intro u hu v hv huv
    have hju : j ∉ u := fun hmem =>
      hj (Finset.mem_of_subset (Finset.mem_powerset.mp hu) hmem)
    have hjv : j ∉ v := fun hmem =>
      hj (Finset.mem_of_subset (Finset.mem_powerset.mp hv) hmem)
    have herase := congrArg (fun q : Finset (EligibleStart c) => q.erase j) huv
    simpa [hju, hjv] using herase

/-- Every eligible variable swap fixes the monomial supported away from all
eligible endpoints. -/
private theorem rename_fixedBottomMonomial {R : Type*} [CommSemiring R]
    {h : Nat} (c : DecoNormalizedCode h) (j : EligibleStart c) :
    MvPolynomial.rename (Equiv.swap (leftLabel h j.1) (rightLabel h j.1))
        (MvPolynomial.finsetMonomial c.fixedBottomSupport :
          MvPolynomial Nat R) =
      MvPolynomial.finsetMonomial c.fixedBottomSupport := by
  rw [MvPolynomial.rename_swap_finsetMonomial]
  apply congrArg MvPolynomial.finsetMonomial
  apply MvPolynomial.swapFinset_eq_self_of_not_mem
  · exact j.2.leftLabel_not_mem_fixedBottomSupport
  · exact j.2.rightLabel_not_mem_fixedBottomSupport

/-- The partially processed factor belonging to an active start. -/
private noncomputable def activeFactor {R : Type*} [CommSemiring R]
    {h : Nat} {c : DecoNormalizedCode h}
    (s : Finset (EligibleStart c)) (i : EligibleStart c) :
    MvPolynomial Nat R :=
  if i ∈ s then
    MvPolynomial.X (leftLabel h i.1) +
      MvPolynomial.X (rightLabel h i.1)
  else MvPolynomial.X (leftLabel h i.1)

/-- Normal form after processing only the eligible starts in `s`. -/
private noncomputable def partialFiberNormalForm {R : Type*} [CommSemiring R]
    {h : Nat} (c : DecoNormalizedCode h) (s : Finset (EligibleStart c)) :
    MvPolynomial Nat R :=
  MvPolynomial.C ((2 : R) ^ (s \ c.activeEligibleStarts).card) *
    MvPolynomial.finsetMonomial c.fixedBottomSupport *
      ∏ i ∈ c.activeEligibleStarts, activeFactor (R := R) s i

private theorem partialFiberNormalForm_empty {R : Type*} [CommSemiring R]
    {h : Nat} (c : DecoNormalizedCode h) :
    partialFiberNormalForm (R := R) c ∅ =
      MinimumInsertionWord.comparisonBottomMonomial
        c.toDecoCode.inverseWord := by
  rw [partialFiberNormalForm]
  simp only [Finset.empty_sdiff, Finset.card_empty, pow_zero, map_one,
    one_mul, activeFactor, Finset.notMem_empty, ↓reduceIte]
  rw [MinimumInsertionWord.comparisonBottomMonomial,
    comparisonBottomSupport_eq_fixed_union_active]
  have hdisjoint : Disjoint c.fixedBottomSupport
      (c.activeEligibleStarts.map c.leftLabelEmbedding) := by
    rw [Finset.disjoint_left]
    intro x hfixed hactive
    rw [Finset.mem_map] at hactive
    obtain ⟨j, hj, hjx⟩ := hactive
    have hnot := j.2.leftLabel_not_mem_fixedBottomSupport
    apply hnot
    have hlabel : leftLabel h j.1 = x := by
      simpa [leftLabelEmbedding] using hjx
    rw [hlabel]
    exact hfixed
  unfold MvPolynomial.finsetMonomial
  rw [Finset.prod_union hdisjoint]
  congr 1
  rw [Finset.prod_map]
  rfl

private theorem rename_activeFactor_of_ne {R : Type*} [CommSemiring R]
    {h : Nat} {c : DecoNormalizedCode h} (s : Finset (EligibleStart c))
    (i j : EligibleStart c) (hij : i ≠ j) :
    MvPolynomial.rename (Equiv.swap (leftLabel h j.1) (rightLabel h j.1))
        (activeFactor (R := R) s i) =
      activeFactor (R := R) s i := by
  unfold activeFactor
  split
  · simp only [map_add, MvPolynomial.rename_X]
    rw [finalSwap_leftLabel_of_ne i j hij,
      finalSwap_rightLabel_of_ne i j hij]
  · rw [MvPolynomial.rename_X, finalSwap_leftLabel_of_ne i j hij]

private theorem rename_activeFactorProduct_erase {R : Type*} [CommSemiring R]
    {h : Nat} (c : DecoNormalizedCode h) (s : Finset (EligibleStart c))
    (j : EligibleStart c) :
    MvPolynomial.rename (Equiv.swap (leftLabel h j.1) (rightLabel h j.1))
        (∏ i ∈ c.activeEligibleStarts.erase j,
          activeFactor (R := R) s i) =
      ∏ i ∈ c.activeEligibleStarts.erase j,
        activeFactor (R := R) s i := by
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact rename_activeFactor_of_ne s i j (Finset.ne_of_mem_erase hi)

private theorem rename_activeFactorProduct_of_not_mem
    {R : Type*} [CommSemiring R] {h : Nat}
    (c : DecoNormalizedCode h) (s : Finset (EligibleStart c))
    (j : EligibleStart c) (hjactive : j ∉ c.activeEligibleStarts) :
    MvPolynomial.rename (Equiv.swap (leftLabel h j.1) (rightLabel h j.1))
        (∏ i ∈ c.activeEligibleStarts, activeFactor (R := R) s i) =
      ∏ i ∈ c.activeEligibleStarts, activeFactor (R := R) s i := by
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact rename_activeFactor_of_ne s i j (fun hij => hjactive (hij ▸ hi))

private theorem activeFactorProduct_insert_of_mem
    {R : Type*} [CommSemiring R] {h : Nat}
    (c : DecoNormalizedCode h) {s : Finset (EligibleStart c)}
    {j : EligibleStart c} (hjactive : j ∈ c.activeEligibleStarts) :
    (∏ i ∈ c.activeEligibleStarts,
        activeFactor (R := R) (insert j s) i) =
      (MvPolynomial.X (leftLabel h j.1) +
          MvPolynomial.X (rightLabel h j.1)) *
        ∏ i ∈ c.activeEligibleStarts.erase j,
          activeFactor (R := R) s i := by
  rw [← Finset.mul_prod_erase c.activeEligibleStarts
    (activeFactor (R := R) (insert j s)) hjactive]
  apply congrArg₂ (· * ·)
  · simp [activeFactor]
  · apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [activeFactor, hij]

private theorem activeFactorProduct_insert_of_not_mem
    {R : Type*} [CommSemiring R] {h : Nat}
    (c : DecoNormalizedCode h) {s : Finset (EligibleStart c)}
    {j : EligibleStart c} (hjactive : j ∉ c.activeEligibleStarts) :
    (∏ i ∈ c.activeEligibleStarts,
        activeFactor (R := R) (insert j s) i) =
      ∏ i ∈ c.activeEligibleStarts, activeFactor (R := R) s i := by
  apply Finset.prod_congr rfl
  intro i hi
  have hij : i ≠ j := fun hij => hjactive (hij ▸ hi)
  simp [activeFactor, hij]

private theorem rename_activeFactorProduct_of_mem
    {R : Type*} [CommSemiring R] {h : Nat}
    (c : DecoNormalizedCode h) {s : Finset (EligibleStart c)}
    {j : EligibleStart c} (hj : j ∉ s)
    (hjactive : j ∈ c.activeEligibleStarts) :
    MvPolynomial.rename (Equiv.swap (leftLabel h j.1) (rightLabel h j.1))
        (∏ i ∈ c.activeEligibleStarts, activeFactor (R := R) s i) =
      MvPolynomial.X (rightLabel h j.1) *
        ∏ i ∈ c.activeEligibleStarts.erase j,
          activeFactor (R := R) s i := by
  rw [← Finset.mul_prod_erase c.activeEligibleStarts
    (activeFactor (R := R) s) hjactive, map_mul,
    rename_activeFactorProduct_erase]
  rw [activeFactor, if_neg hj, MvPolynomial.rename_X,
    j.2.finalSwap_leftLabel]

/-- The partial normal form obeys the same one-swap recurrence as the
decoration subset sum. -/
private theorem partialFiberNormalForm_insert {R : Type*} [CommSemiring R]
    {h : Nat} (c : DecoNormalizedCode h) {s : Finset (EligibleStart c)}
    {j : EligibleStart c} (hj : j ∉ s) :
    partialFiberNormalForm (R := R) c (insert j s) =
      MvPolynomial.swapSum (leftLabel h j.1) (rightLabel h j.1)
        (partialFiberNormalForm (R := R) c s) := by
  by_cases hjactive : j ∈ c.activeEligibleStarts
  · have hsdiff : (insert j s) \ c.activeEligibleStarts =
        s \ c.activeEligibleStarts := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨hij | his, hinactive⟩
        · subst i
          exact (hinactive hjactive).elim
        · exact ⟨his, hinactive⟩
      · rintro ⟨his, hinactive⟩
        exact ⟨Or.inr his, hinactive⟩
    rw [partialFiberNormalForm, partialFiberNormalForm, hsdiff,
      activeFactorProduct_insert_of_mem c hjactive,
      MvPolynomial.swapSum, map_mul, map_mul, MvPolynomial.rename_C,
      rename_fixedBottomMonomial,
      rename_activeFactorProduct_of_mem c hj hjactive]
    rw [← Finset.mul_prod_erase c.activeEligibleStarts
      (activeFactor (R := R) s) hjactive]
    rw [activeFactor, if_neg hj]
    ring
  · have hsdiff : (insert j s) \ c.activeEligibleStarts =
        insert j (s \ c.activeEligibleStarts) := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨hij | his, hinactive⟩
        · exact Or.inl hij
        · exact Or.inr ⟨his, hinactive⟩
      · rintro (hij | ⟨his, hinactive⟩)
        · subst i
          exact ⟨Or.inl rfl, hjactive⟩
        · exact ⟨Or.inr his, hinactive⟩
    have hjsdiff : j ∉ s \ c.activeEligibleStarts := by
      simp [hj]
    rw [partialFiberNormalForm, partialFiberNormalForm, hsdiff,
      Finset.card_insert_of_notMem hjsdiff, MvPolynomial.swapSum,
      activeFactorProduct_insert_of_not_mem c hjactive,
      map_mul, map_mul, MvPolynomial.rename_C,
      rename_fixedBottomMonomial,
      rename_activeFactorProduct_of_not_mem c s j hjactive, pow_succ]
    rw [map_mul, map_ofNat]
    ring

/-- Every partial decoration sum equals the corresponding active/inactive
normal form. -/
private theorem subsetFiberPolynomial_eq_partialFiberNormalForm
    {R : Type*} [CommSemiring R] {h : Nat}
    (c : DecoNormalizedCode h) (s : Finset (EligibleStart c)) :
    subsetFiberPolynomial (R := R) c s =
      partialFiberNormalForm (R := R) c s := by
  induction s using Finset.induction_on with
  | empty => rw [subsetFiberPolynomial_empty, partialFiberNormalForm_empty]
  | @insert j s hj ih =>
      rw [subsetFiberPolynomial_insert c hj,
        partialFiberNormalForm_insert c hj, ih]

/-- The sum of comparison-bottom monomials over every decoration of a
normalized code. -/
noncomputable def fiberPolynomial {R : Type*} [CommSemiring R]
    {h : Nat} (c : DecoNormalizedCode h) : MvPolynomial Nat R :=
  subsetFiberPolynomial c c.allEligibleStarts

/-- The Boolean normal form determined by the active and inactive eligible
starts of a normalized code. -/
noncomputable def fiberNormalForm {R : Type*} [CommSemiring R]
    {h : Nat} (c : DecoNormalizedCode h) : MvPolynomial Nat R :=
  RealRooted.booleanSwapOrbitNormalForm c.inactiveEligibleStarts.card
    c.fixedBottomSupport c.activeEligibleStarts
    (fun j => leftLabel h j.1) (fun j => rightLabel h j.1)

/-- The normalized decoration fiber sum is exactly its Boolean swap-orbit
normal form. -/
theorem fiberPolynomial_eq_fiberNormalForm
    {R : Type*} [CommSemiring R] {h : Nat} (c : DecoNormalizedCode h) :
    fiberPolynomial (R := R) c = fiberNormalForm (R := R) c := by
  rw [fiberPolynomial, subsetFiberPolynomial_eq_partialFiberNormalForm,
    partialFiberNormalForm, fiberNormalForm,
    RealRooted.booleanSwapOrbitNormalForm_eq]
  have hinactive : c.allEligibleStarts \ c.activeEligibleStarts =
      c.inactiveEligibleStarts := rfl
  rw [hinactive]
  apply congrArg (fun q : MvPolynomial Nat R =>
    MvPolynomial.C ((2 : R) ^ c.inactiveEligibleStarts.card) *
      MvPolynomial.finsetMonomial c.fixedBottomSupport * q)
  apply Finset.prod_congr rfl
  intro i hi
  rw [activeFactor, if_pos (mem_allEligibleStarts c i)]

/-- Exact factorization of a normalized decoration fiber into its inactive
multiplicity, fixed monomial, and active linear factors. -/
theorem fiberPolynomial_eq_product
    {R : Type*} [CommSemiring R] {h : Nat} (c : DecoNormalizedCode h) :
    fiberPolynomial (R := R) c =
      MvPolynomial.C ((2 : R) ^ c.inactiveEligibleStarts.card) *
        MvPolynomial.finsetMonomial c.fixedBottomSupport *
          ∏ j ∈ c.activeEligibleStarts,
            (MvPolynomial.X (leftLabel h j.1) +
              MvPolynomial.X (rightLabel h j.1) : MvPolynomial Nat R) := by
  rw [fiberPolynomial_eq_fiberNormalForm, fiberNormalForm,
    RealRooted.booleanSwapOrbitNormalForm_eq]

/-- Every normalized Deco decoration fiber is multivariate real stable. -/
theorem fiberPolynomial_mvRealStable {h : Nat} (c : DecoNormalizedCode h) :
    MvRealStable (fiberPolynomial (R := Real) c) := by
  rw [fiberPolynomial_eq_fiberNormalForm]
  exact RealRooted.booleanSwapOrbitNormalForm_mvRealStable
    c.inactiveEligibleStarts.card c.fixedBottomSupport c.activeEligibleStarts
      (fun j => leftLabel h j.1) (fun j => rightLabel h j.1)

end

end RealRooted.Applications.OEIS.DecoNormalizedCode
