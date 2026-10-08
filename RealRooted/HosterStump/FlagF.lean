import RealRooted.HosterStump.BoolChains

/-!
# The flag `f`-vector of a graded simplicial poset

For a graded simplicial poset, `flagF rk T = fVec rk (max T + 1) * gapMultinomial (max T + 1)
(T.erase (max T))`: a chain with ranks `T + 1` is a top element `x` of rank `max T + 1`,
together with a chain in the Boolean interval below `x`.
-/

open Finset

noncomputable section

namespace RealRooted.HosterStump

variable {P : Type*} [PartialOrder P] [Fintype P]

/-- The flag `f`-vector is the chain count for the strictly increasing rank sequence `T`. -/
theorem flagF_eq_chainCount (rk : P → ℕ) (T : Finset ℕ) :
    flagF rk T = chainCount rk (T.orderEmbOfFin rfl) := by
  classical
  unfold flagF chainCount
  congr

/-- The flag `f`-vector at the empty set is `1`: the empty chain. -/
theorem flagF_empty (rk : P → ℕ) : flagF rk ∅ = 1 := by
  rw [flagF_eq_chainCount]
  exact chainCount_zero rk _

omit [Fintype P] in
/-- In a graded simplicial poset, an order isomorphism of a lower interval with a Boolean
lattice sends an element to a set of cardinality its rank. -/
private theorem card_orderIso_eq_rk {n : ℕ} {rk : P → ℕ} (hP : IsSimplicialPoset P n rk)
    (x : P) (e : Set.Iic x ≃o Finset (Fin (rk x))) (y : Set.Iic x) : (e y).card = rk y := by
  have h1 : Nat.card (Set.Iic y.1) = 2 ^ rk y.1 := hP.natCard_Iic y.1
  have h2 : Nat.card (Set.Iic y.1) = Nat.card {z : Set.Iic x // z ≤ y} :=
    Nat.card_congr
      { toFun := fun w => ⟨⟨w.1, w.2.trans y.2⟩, w.2⟩
        invFun := fun z => ⟨z.1.1, z.2⟩
        left_inv := fun w => rfl
        right_inv := fun z => rfl }
  have h3 : Nat.card {z : Set.Iic x // z ≤ y} = Nat.card {d : Finset (Fin (rk x)) // d ≤ e y} :=
    Nat.card_congr (e.toEquiv.subtypeEquiv fun z => e.le_iff_le.symm)
  have h4 : Nat.card {d : Finset (Fin (rk x)) // d ≤ e y} = 2 ^ (e y).card := by
    rw [← Finset.card_powerset, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun d => Finset.mem_powerset.symm)
  have h5 : 2 ^ (e y).card = 2 ^ rk y.1 := by rw [← h4, ← h3, ← h2, h1]
  exact Nat.pow_right_injective (le_refl 2) h5

/-- The recursion for chain counts in a graded simplicial poset. -/
theorem chainCount_succ_of_isSimplicialPoset {n : ℕ} {rk : P → ℕ}
    (hP : IsSimplicialPoset P n rk) {k : ℕ} (s : Fin (k + 1) → ℕ) (hs : StrictMono s) :
    chainCount rk s = fVec rk (s (Fin.last k) + 1) *
      gapMultinomial (s (Fin.last k) + 1) (univ.image fun j : Fin k => s j.castSucc) := by
  classical
  rw [chainCount_succ rk s hs]
  have hstep : ∀ x ∈ (univ.filter fun x : P => rk x = s (Fin.last k) + 1),
      chainCountBelow rk (fun j : Fin k => s j.castSucc) x =
        gapMultinomial (s (Fin.last k) + 1) (univ.image fun j : Fin k => s j.castSucc) := by
    intro x hx
    have hx' : rk x = s (Fin.last k) + 1 := (Finset.mem_filter.1 hx).2
    obtain ⟨e⟩ := hP.iic x
    rw [chainCountBelow_eq_of_orderIso rk _ x e (card_orderIso_eq_rk hP x e),
      chainCount_finset_eq_gapMultinomial (rk x) (fun j : Fin k => s j.castSucc)
        (hs.comp Fin.strictMono_castSucc), hx']
  rw [Finset.sum_congr rfl hstep, Finset.sum_const, smul_eq_mul]
  rfl

/-- The chain count for a nonempty set of ranks in a graded simplicial poset. -/
theorem chainCount_eq_fVec_mul {n : ℕ} {rk : P → ℕ} (hP : IsSimplicialPoset P n rk)
    {k : ℕ} (s : Fin k → ℕ) (hs : StrictMono s) (U : Finset ℕ) (hU : U.Nonempty)
    (h : univ.image s = U) :
    chainCount rk s =
      fVec rk (U.max' hU + 1) * gapMultinomial (U.max' hU + 1) (U.erase (U.max' hU)) := by
  subst h
  cases k with
  | zero => exact absurd hU (by simp)
  | succ k =>
    rw [image_max'_eq_last hs hU, image_erase_last hs]
    exact chainCount_succ_of_isSimplicialPoset hP s hs

/-- Identity `flagF = fVec * gapMultinomial` for graded simplicial posets: a chain with ranks
`T + 1` is a top element of rank `max T + 1` together with a chain in its Boolean interval. -/
theorem flagF_eq_fVec_mul {n : ℕ} {rk : P → ℕ} (hP : IsSimplicialPoset P n rk)
    (T : Finset ℕ) (hT : T.Nonempty) :
    flagF rk T =
      fVec rk (T.max' hT + 1) * gapMultinomial (T.max' hT + 1) (T.erase (T.max' hT)) := by
  rw [flagF_eq_chainCount]
  exact chainCount_eq_fVec_mul hP _ (T.orderEmbOfFin rfl).strictMono T hT
    (Finset.image_orderEmbOfFin_univ T rfl)

end RealRooted.HosterStump

end
