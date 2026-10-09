import RealRooted.Mathlib.Combinatorics.Enumerative.Descent
import RealRooted.BrandenVecchi.SignedWordRuns.Statistics

/-!
# Signed-word descents and the canonical descent count

`listDescentNumber_eq_descentCount` identifies the local list descent number with the canonical
`List.descentCount` of `RealRooted.Mathlib.Combinatorics.Enumerative.Descent`. The local
statistic needs only `LT`; the bridge is stated under `LinearOrder`.
-/

namespace RealRooted.BrandenVecchi

private theorem adjacentCount_eq_descentCount {α : Type*} [LinearOrder α]
    (word : List α) :
    adjacentCount (fun left right : α => right < left) word = word.descentCount := by
  induction word with
  | nil => simp [adjacentCount, List.descentCount]
  | cons a tail ih =>
      cases tail with
      | nil => simp [adjacentCount, List.descentCount]
      | cons b rest =>
          rw [adjacentCount_cons_cons, List.descentCount,
            List.descentSet_cons_cons]
          by_cases h : b < a
          · have hdisj :
                Disjoint ({0} : Finset ℕ)
                  ((b :: rest).descentSet.map
                    ⟨Nat.succ, Nat.succ_injective⟩) := by
                rw [Finset.disjoint_left]
                intro i hi hmap
                obtain ⟨j, hj, hij⟩ := Finset.mem_map.mp hmap
                subst i
                simp at hi
            simp only [ite_eq_left h, Finset.card_union_of_disjoint hdisj,
              Finset.card_singleton, Finset.card_map]
            simpa only [List.descentCount] using
              congrArg (fun x => 1 + x) ih
          · simp only [ite_eq_right h, Finset.empty_union, Finset.card_map]
            simpa only [List.descentCount, Nat.zero_add] using ih

/-! The old statistic uses only an `LT` relation; the canonical statistic has a
linear-order hypothesis, so this is the intended migration boundary. -/

/-- The local list descent number equals the canonical descent count. -/
theorem listDescentNumber_eq_descentCount {α : Type*} [LinearOrder α]
    (word : List α) :
    listDescentNumber word = word.descentCount := by
  exact adjacentCount_eq_descentCount word

end RealRooted.BrandenVecchi
