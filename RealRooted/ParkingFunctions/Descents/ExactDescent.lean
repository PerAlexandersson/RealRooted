import RealRooted.Mathlib.Combinatorics.Enumerative.BooleanLattice
import RealRooted.ParkingFunctions.Descents.DescentContainment

/-!
# Exact descent-set content enumerators

This module recovers exact descent-set enumerators from descent-containment
enumerators by Boolean-lattice Mobius inversion.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- The universal multivariate content enumerator for words whose descent set
is exactly `S`. -/
def exactDescentContentEnumerator {n : ℕ}
    (S : Finset (Fin n)) (m : ℕ) : MvPolynomial (Fin m) ℤ := by
  classical
  exact ∑ w : {w : Fin (n + 1) → Fin m // descentSet w = S},
    MvPolynomial.monomial (wordExponent w.1) 1

/-- Partition a descent-containment fiber by its actual descent set. -/
def hasDescentsAtEquivSigmaExactDescent {n m : ℕ}
    (S : Finset (Fin n)) :
    {w : Fin (n + 1) → Fin m // HasDescentsAt S w} ≃
      Σ T : {T : Finset (Fin n) // S ⊆ T},
        {w : Fin (n + 1) → Fin m // descentSet w = T.1} where
  toFun w := ⟨⟨descentSet w.1, w.2⟩, ⟨w.1, rfl⟩⟩
  invFun x := ⟨x.2.1, by
    change S ⊆ descentSet x.2.1
    rw [x.2.2]
    exact x.1.2⟩
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv x := by
    rcases x with ⟨⟨T, hST⟩, ⟨w, hw⟩⟩
    change descentSet w = T at hw
    subst T
    rfl

/-- A prescribed-descent enumerator is the sum of exact enumerators over all
descent supersets. -/
theorem hasDescentsAtContentEnumerator_eq_sum_exactDescentContentEnumerator
    {n : ℕ} (S : Finset (Fin n)) (m : ℕ) :
    hasDescentsAtContentEnumerator S m =
      ∑ T : {T : Finset (Fin n) // S ⊆ T},
        exactDescentContentEnumerator T.1 m := by
  classical
  unfold hasDescentsAtContentEnumerator exactDescentContentEnumerator
  calc
    (∑ w : {w : Fin (n + 1) → Fin m // HasDescentsAt S w},
        MvPolynomial.monomial (wordExponent w.1) (1 : ℤ)) =
        ∑ x : Σ T : {T : Finset (Fin n) // S ⊆ T},
          {w : Fin (n + 1) → Fin m // descentSet w = T.1},
          MvPolynomial.monomial (wordExponent x.2.1) (1 : ℤ) := by
      apply Fintype.sum_equiv (hasDescentsAtEquivSigmaExactDescent S)
      intro w
      rfl
    _ = ∑ T : {T : Finset (Fin n) // S ⊆ T},
        ∑ w : {w : Fin (n + 1) → Fin m // descentSet w = T.1},
          MvPolynomial.monomial (wordExponent w.1) (1 : ℤ) :=
      Fintype.sum_sigma _

/-- Descent containment is the upper zeta transform of the exact descent-set
enumerator on the full Boolean lattice. -/
theorem hasDescentsAtContentEnumerator_eq_upperZeta_exactDescent
    {n : ℕ} (S : Finset (Fin n)) (m : ℕ) :
    hasDescentsAtContentEnumerator S m =
      Finset.upperZeta Finset.univ
        (fun T => exactDescentContentEnumerator T m) S := by
  classical
  unfold Finset.upperZeta
  rw [Finset.sum_subtype]
  · exact
      hasDescentsAtContentEnumerator_eq_sum_exactDescentContentEnumerator S m
  · intro T
    simp

/-- The exact descent-set enumerator has an explicit finite signed formula in
terms of descent-containment enumerators. -/
theorem exactDescentContentEnumerator_eq_mobius_sum {n : ℕ}
    (S : Finset (Fin n)) (m : ℕ) :
    exactDescentContentEnumerator S m =
      ∑ D ∈ (Finset.univ \ S).powerset,
        (-1 : ℤ) ^ D.card •
          hasDescentsAtContentEnumerator (S ∪ D) m := by
  apply Finset.upperZeta_mobius_inversion Finset.univ S
      (fun T => exactDescentContentEnumerator T m)
      (fun T => hasDescentsAtContentEnumerator T m)
  · simp
  · intro T _
    exact hasDescentsAtContentEnumerator_eq_upperZeta_exactDescent T m

/-- Requiring every position to be a descent leaves the single strict block
enumerator. -/
@[simp]
theorem exactDescentContentEnumerator_univ (n m : ℕ) :
    exactDescentContentEnumerator (Finset.univ : Finset (Fin n)) m =
      MvPolynomial.esymm (Fin m) ℤ (n + 1) := by
  calc
    exactDescentContentEnumerator (Finset.univ : Finset (Fin n)) m =
        Finset.upperZeta Finset.univ
          (fun T => exactDescentContentEnumerator T m) Finset.univ :=
      (Finset.upperZeta_self Finset.univ
        (fun T => exactDescentContentEnumerator T m)).symm
    _ = hasDescentsAtContentEnumerator Finset.univ m :=
      (hasDescentsAtContentEnumerator_eq_upperZeta_exactDescent
        Finset.univ m).symm
    _ = MvPolynomial.esymm (Fin m) ℤ (n + 1) :=
      hasDescentsAtContentEnumerator_univ n m

/-- Exact descent-set content enumerators are invariant under alphabet
renaming. -/
theorem rename_exactDescentContentEnumerator {n : ℕ}
    (S : Finset (Fin n)) (m : ℕ) (e : Equiv.Perm (Fin m)) :
    MvPolynomial.rename e (exactDescentContentEnumerator S m) =
      exactDescentContentEnumerator S m := by
  refine Finset.upperZeta_injectiveOn (Finset.univ : Finset (Fin n))
    (F := fun U => MvPolynomial.rename e
      (exactDescentContentEnumerator U m))
    (G := fun U => exactDescentContentEnumerator U m) ?_ S (by simp)
  intro T _
  calc
    Finset.upperZeta Finset.univ
        (fun U => MvPolynomial.rename e
          (exactDescentContentEnumerator U m)) T =
        MvPolynomial.rename e
          (Finset.upperZeta Finset.univ
            (fun U => exactDescentContentEnumerator U m) T) := by
      unfold Finset.upperZeta
      rw [map_sum]
    _ = MvPolynomial.rename e (hasDescentsAtContentEnumerator T m) := by
      rw [← hasDescentsAtContentEnumerator_eq_upperZeta_exactDescent]
    _ = hasDescentsAtContentEnumerator T m :=
      rename_hasDescentsAtContentEnumerator T m e
    _ = Finset.upperZeta Finset.univ
        (fun U => exactDescentContentEnumerator U m) T :=
      hasDescentsAtContentEnumerator_eq_upperZeta_exactDescent T m

/-- A content coefficient of the exact descent-set enumerator counts the
literal words in that content fiber. -/
theorem coeff_exactDescentContentEnumerator {n m : ℕ}
    (S : Finset (Fin n)) (μ : Multiset (Fin m)) :
    MvPolynomial.coeff μ.toFinsupp
        (exactDescentContentEnumerator S m) =
      (((contentFiber (n := n + 1) μ).filter fun w =>
        descentSet w = S).card : ℤ) := by
  classical
  unfold exactDescentContentEnumerator
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  calc
    (∑ x : {w : Fin (n + 1) → Fin m // descentSet w = S},
        if wordExponent x.1 = μ.toFinsupp then 1 else 0) =
        ∑ w ∈ Finset.univ.filter (fun w : Fin (n + 1) → Fin m =>
          descentSet w = S),
          if wordExponent w = μ.toFinsupp then 1 else 0 := by
      symm
      apply Finset.sum_subtype
      intro w
      simp
    _ = (((Finset.univ.filter (fun w : Fin (n + 1) → Fin m =>
        descentSet w = S)).filter fun w =>
          wordExponent w = μ.toFinsupp).card : ℤ) := by
      rw [Finset.sum_boole]
    _ = (((contentFiber (n := n + 1) μ).filter fun w =>
        descentSet w = S).card : ℤ) := by
      have hfin :
          (Finset.univ.filter (fun w : Fin (n + 1) → Fin m =>
            descentSet w = S)).filter (fun w =>
              wordExponent w = μ.toFinsupp) =
            (contentFiber (n := n + 1) μ).filter (fun w =>
              descentSet w = S) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          mem_contentFiber_iff, wordExponent_eq_toFinsupp_wordContent]
        rw [Multiset.toFinsupp.injective.eq_iff]
        tauto
      rw [hfin]

/-- The number of words with fixed content and exact descent set depends only
on the multiplicity type of the content. -/
theorem card_contentFiber_descentSet_map_equiv {n m : ℕ}
    (μ : Multiset (Fin m)) (e : Equiv.Perm (Fin m))
    (S : Finset (Fin n)) :
    ((contentFiber (n := n + 1) (μ.map e)).filter fun w =>
      descentSet w = S).card =
    ((contentFiber (n := n + 1) μ).filter fun w =>
      descentSet w = S).card := by
  rw [← Int.ofNat_inj]
  rw [← coeff_exactDescentContentEnumerator,
    ← coeff_exactDescentContentEnumerator, toFinsupp_map_equiv]
  have h := congrArg
    (MvPolynomial.coeff (Finsupp.mapDomain e μ.toFinsupp))
    (rename_exactDescentContentEnumerator S m e)
  rw [MvPolynomial.coeff_rename_mapDomain e e.injective] at h
  exact h.symm

end

end RealRooted.ParkingFunctions
