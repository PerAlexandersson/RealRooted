import RealRooted.BrandenVecchi.SmirnovChow
import RealRooted.GustafssonSolus
import Mathlib.Data.Fin.Rev

/-!
# Reversed-last-letter recurrence for finite Smirnov words

This file packages the literal last-letter refinement of finite Smirnov
descent polynomials in reverse alphabet order.  Its successor step is exactly
the Gustafsson--Solus threshold matrix with every equal-letter pivot deleted.
-/

open Polynomial

namespace RealRooted.BrandenVecchi

noncomputable section

/-- Literal unweighted Smirnov descent polynomials. -/
def smirnovDescentPolynomial (m n : ℕ) : ℝ[X] :=
  weightedSmirnovPolynomial (fun _ : Fin m => (1 : ℝ)) n

/-- Literal fixed-final-letter enumerators, stored in reverse letter order.
The index `r` counts the letters preceding the prescribed final letter. -/
def smirnovDescentRefined (m r : ℕ) (i : Fin m) : ℝ[X] :=
  weightedSmirnovEnding (fun _ : Fin m => (1 : ℝ)) r i.rev

/-- Prefixes whose appended reversed final letter makes a Smirnov word. -/
def smirnovPrefixesEnding (m r : ℕ) (i : Fin m) :
    Finset (Fin r → Fin m) := by
  classical
  exact Finset.univ.filter fun word =>
    IsSmirnovWord (r + 1) (Fin.snoc word i.rev)

@[simp]
theorem mem_smirnovPrefixesEnding_iff {m r : ℕ} {i : Fin m}
    {word : Fin r → Fin m} :
    word ∈ smirnovPrefixesEnding m r i ↔
      IsSmirnovWord (r + 1) (Fin.snoc word i.rev) := by
  classical
  simp [smirnovPrefixesEnding]

/-- The refinement is the literal finite sum over prefixes whose appended
reversed final letter makes a Smirnov word. -/
theorem smirnovDescentRefined_eq_sum (m r : ℕ) (i : Fin m) :
    smirnovDescentRefined m r i =
      ∑ word ∈ smirnovPrefixesEnding m r i,
        X ^ smirnovDescentNumber (Fin.snoc word i.rev) := by
  classical
  simp [smirnovDescentRefined, weightedSmirnovEnding,
    weightedSmirnovEndingSummand, smirnovWordWeight,
    smirnovPrefixesEnding, Finset.sum_filter]

@[simp]
theorem smirnovDescentRefined_zero (m : ℕ) (i : Fin m) :
    smirnovDescentRefined m 0 i = 1 := by
  simp [smirnovDescentRefined]

/-- Splitting on the penultimate letter gives the exact reversed threshold
recurrence: smaller reversed indices contribute `X`, and the equal-letter
pivot is absent. -/
theorem smirnovDescentRefined_succ (m r : ℕ) (i : Fin m) :
    smirnovDescentRefined m (r + 1) i =
      ∑ j : Fin m,
        gustafssonSolusEntry i true j * smirnovDescentRefined m r j := by
  rw [smirnovDescentRefined, weightedSmirnovEnding_succ]
  rw [show (∑ j : Fin m,
      if j = i.rev then 0 else
        C (1 : ℝ) * (if i.rev < j then X else 1) *
          weightedSmirnovEnding (fun _ : Fin m => (1 : ℝ)) r j) =
      ∑ j : Fin m,
        if j.rev = i.rev then 0 else
          C (1 : ℝ) * (if i.rev < j.rev then X else 1) *
            weightedSmirnovEnding
              (fun _ : Fin m => (1 : ℝ)) r j.rev by
    exact (Fintype.sum_equiv Fin.revPerm
      (fun j : Fin m =>
        if j.rev = i.rev then 0 else
          C (1 : ℝ) * (if i.rev < j.rev then X else 1) *
            weightedSmirnovEnding
              (fun _ : Fin m => (1 : ℝ)) r j.rev)
      (fun j : Fin m =>
        if j = i.rev then 0 else
          C (1 : ℝ) * (if i.rev < j then X else 1) *
            weightedSmirnovEnding
              (fun _ : Fin m => (1 : ℝ)) r j)
      (fun _ => rfl)).symm]
  apply Fintype.sum_congr
  intro j
  simp only [Fin.rev_inj, Fin.rev_lt_rev,
    smirnovDescentRefined]
  by_cases hji : j = i
  · subst j
    simp [gustafssonSolusEntry]
  · by_cases hjiLt : j < i
    · simp [gustafssonSolusEntry, hji, hjiLt]
    · have hij : i < j := lt_of_le_of_ne (not_lt.mp hjiLt) (Ne.symm hji)
      simp [gustafssonSolusEntry, hji, hjiLt]

/-- The reversed literal refinement as a finite list. -/
def smirnovDescentRefinedList (m r : ℕ) : List ℝ[X] :=
  List.ofFn (smirnovDescentRefined m r)

@[simp]
theorem length_smirnovDescentRefinedList (m r : ℕ) :
    (smirnovDescentRefinedList m r).length = m := by
  simp [smirnovDescentRefinedList]

/-- The length-one refined vector is the all-ones vector. -/
theorem smirnovDescentRefinedList_zero (m : ℕ) :
    smirnovDescentRefinedList m 0 = List.replicate m 1 := by
  change List.ofFn (smirnovDescentRefined m 0) = List.replicate m 1
  rw [show smirnovDescentRefined m 0 = fun _ => 1 by
    funext i
    exact smirnovDescentRefined_zero m i]
  exact List.ofFn_const m 1

private theorem zipWith_mul_ofFn {m : ℕ} (f g : Fin m → ℝ[X]) :
    (List.ofFn f).zipWith (· * ·) (List.ofFn g) =
      List.ofFn (fun i => f i * g i) := by
  apply List.ext_get
  · simp
  · intro k hkLeft hkRight
    let i : Fin m := ⟨k, by simpa using hkRight⟩
    simp

/-- Matrix-action form of the literal successor recurrence. -/
theorem smirnovDescentRefinedList_succ (m r : ℕ) :
    smirnovDescentRefinedList m (r + 1) =
      gustafssonSolusAction id (fun _ : Fin m => true)
        (smirnovDescentRefinedList m r) := by
  apply List.ext_get
  · simp [smirnovDescentRefinedList, gustafssonSolusAction]
  · intro k hkLeft hkRight
    let i : Fin m :=
      ⟨k, by simpa [smirnovDescentRefinedList] using hkLeft⟩
    rw [show (smirnovDescentRefinedList m (r + 1)).get ⟨k, hkLeft⟩ =
        smirnovDescentRefined m (r + 1) i by
      simp [smirnovDescentRefinedList, i]]
    rw [smirnovDescentRefined_succ]
    simp [gustafssonSolusAction, matPolyAction,
      gustafssonSolusMatrix, gustafssonSolusRow,
      smirnovDescentRefinedList, zipWith_mul_ofFn, List.sum_ofFn, i]

/-- Every nonempty literal Smirnov polynomial is the sum of the reversed
last-letter refinement. -/
theorem smirnovDescentPolynomial_succ (m r : ℕ) :
    smirnovDescentPolynomial m (r + 1) =
      (smirnovDescentRefinedList m r).sum := by
  rw [smirnovDescentPolynomial, weightedSmirnovPolynomial_succ,
    smirnovDescentRefinedList]
  rw [List.sum_ofFn]
  symm
  exact Fintype.sum_equiv Fin.revPerm
    (fun i : Fin m => smirnovDescentRefined m r i)
    (fun i : Fin m =>
      weightedSmirnovEnding (fun _ : Fin m => (1 : ℝ)) r i)
    (fun i => by simp [smirnovDescentRefined])

end

end RealRooted.BrandenVecchi
