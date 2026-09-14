import RealRooted.Combinatorics.ComparisonBottom

/-!
# Comparison-bottom monomials under minimum insertion

This file records insertion identities for squarefree comparison-bottom
monomials.  They are stated for generic positive words with an initial ascent,
independently of any particular combinatorial construction.
-/

namespace RealRooted.MinimumInsertionWord

/-- An exceptional pair shifts every old comparison bottom by two and adds
the new bottom `2`. -/
theorem comparisonBottomSupport_exceptional_pair {w : List Nat}
    (hw : StartsWithAscent w) :
    comparisonBottomSupport (step 0 (step 1 w)) =
      insert 2
        ((comparisonBottomSupport w).map
          (succEmbedding.trans succEmbedding)) := by
  cases w with
  | nil => simp [StartsWithAscent] at hw
  | cons a w =>
    cases w with
    | nil => simp [StartsWithAscent] at hw
    | cons b w =>
      change a < b at hw
      rw [step_exceptional_pair]
      simp only [comparisonBottomSupport]
      rw [if_pos (by lia), if_neg (by lia), if_pos (by lia)]
      simp only [List.map_cons]
      change insert 2
          (if 2 < b + 2 then
            comparisonBottomSupport ((b + 2) :: w.map (fun x => x + 2))
          else insert (b + 2)
            (comparisonBottomSupport ((b + 2) :: w.map (fun x => x + 2)))) = _
      rw [if_pos (by lia)]
      have hmap :
          (b :: w).map (fun x => x + 2) = raise (raise (b :: w)) := by
        simp [raise, Nat.add_assoc]
      change insert 2
        (comparisonBottomSupport ((b :: w).map (fun x => x + 2))) = _
      rw [hmap, comparisonBottomSupport_raise,
        comparisonBottomSupport_raise, Finset.map_map]

/-- The comparison-bottom monomial of an exceptional pair is the shifted old
monomial times the new bottom variable `X 2`. -/
theorem comparisonBottomMonomial_exceptional_pair
    {R : Type*} [CommSemiring R] {w : List Nat}
    (hpos : IsPositive w) (hw : StartsWithAscent w) :
    (comparisonBottomMonomial (step 0 (step 1 w)) : MvPolynomial Nat R) =
      MvPolynomial.X 2 *
        MvPolynomial.rename (succEmbedding.trans succEmbedding)
          (comparisonBottomMonomial w) := by
  have htwo : 2 ∉
      (comparisonBottomSupport w).map
        (succEmbedding.trans succEmbedding) := by
    intro hmem
    rw [Finset.mem_map] at hmem
    obtain ⟨x, hx, hxeq⟩ := hmem
    have hxzero : x = 0 := by
      change x + 2 = 2 at hxeq
      lia
    subst x
    exact zero_not_mem_comparisonBottomSupport hpos hx
  rw [comparisonBottomMonomial,
    comparisonBottomSupport_exceptional_pair hw,
    MvPolynomial.finsetMonomial_insert htwo]
  congr 1
  rw [comparisonBottomMonomial]
  exact (MvPolynomial.rename_finsetMonomial
    (succEmbedding.trans succEmbedding)
      (succEmbedding.trans succEmbedding).injective
        (comparisonBottomSupport w)).symm

end RealRooted.MinimumInsertionWord
