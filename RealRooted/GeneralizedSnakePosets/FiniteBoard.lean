import RealRooted.FolkloreLemma

/-!
# Finite non-nesting rook boards

This module contains the finite-board and basic non-nesting rook-polynomial API
used by the Braun--Jal generalized snake poset development.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-! ## Board and rook-polynomial interfaces -/

/-- A finite skew board, represented only by its finite set of cells.

This intentionally avoids committing to a Ferrers or squarecase coordinate
system.  Concrete squarecase encodings can later prove that their cell sets
agree with this finite model. -/
structure FiniteSkewBoard where
  cells : Finset (ℕ × ℕ)
  deriving DecidableEq

namespace FiniteSkewBoard

/-- The empty finite skew board. -/
def empty : FiniteSkewBoard :=
  ⟨∅⟩

/-- A rook placement is non-nesting if all cells lie in the board, no two
rooks share a row, and columns strictly decrease as rows increase. -/
def IsNonNestingPlacement (B : FiniteSkewBoard) (P : Finset (ℕ × ℕ)) : Prop :=
  P ⊆ B.cells ∧
    (∀ a ∈ P, ∀ b ∈ P, a ≠ b → a.1 ≠ b.1) ∧
    (∀ a ∈ P, ∀ b ∈ P, a.1 < b.1 → b.2 < a.2)

/-- The non-nesting rook polynomial of a finite skew board. -/
def rookPolynomial (B : FiniteSkewBoard) : ℝ[X] := by
  classical
  exact (B.cells.powerset.filter (fun P => B.IsNonNestingPlacement P)).sum
    (fun P => X ^ P.card)

/-- The finite set of non-nesting placements on a finite skew board. -/
def nonNestingPlacements (B : FiniteSkewBoard) : Finset (Finset (ℕ × ℕ)) := by
  classical
  exact B.cells.powerset.filter fun P => B.IsNonNestingPlacement P

/-- The finite set of non-nesting placements containing a specified cell. -/
def nonNestingPlacementsWithCell (B : FiniteSkewBoard) (a : ℕ × ℕ) :
    Finset (Finset (ℕ × ℕ)) := by
  classical
  exact B.nonNestingPlacements.filter fun P => a ∈ P

/-- Membership in the finite set of non-nesting placements. -/
@[simp] theorem mem_nonNestingPlacements {B : FiniteSkewBoard}
    {P : Finset (ℕ × ℕ)} :
    P ∈ B.nonNestingPlacements ↔ B.IsNonNestingPlacement P := by
  classical
  rw [nonNestingPlacements, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- Membership in the finite set of non-nesting placements containing a
specified cell. -/
@[simp] theorem mem_nonNestingPlacementsWithCell {B : FiniteSkewBoard}
    {P : Finset (ℕ × ℕ)} {a : ℕ × ℕ} :
    P ∈ B.nonNestingPlacementsWithCell a ↔
      B.IsNonNestingPlacement P ∧ a ∈ P := by
  classical
  simp [nonNestingPlacementsWithCell]

/-- The rook polynomial as a sum over the named finite set of non-nesting
placements. -/
theorem rookPolynomial_eq_nonNestingPlacements_sum (B : FiniteSkewBoard) :
    B.rookPolynomial =
      B.nonNestingPlacements.sum fun P => (X : ℝ[X]) ^ P.card := by
  classical
  rw [rookPolynomial, nonNestingPlacements]

/-- The empty placement is non-nesting on every finite skew board. -/
@[simp] theorem isNonNestingPlacement_empty (B : FiniteSkewBoard) :
    B.IsNonNestingPlacement ∅ := by
  simp [IsNonNestingPlacement]

/-- A singleton cell is a non-nesting placement when it lies in the board. -/
theorem isNonNestingPlacement_singleton {B : FiniteSkewBoard} {a : ℕ × ℕ}
    (ha : a ∈ B.cells) :
    B.IsNonNestingPlacement ({a} : Finset (ℕ × ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    exact ha
  · intro x hx y hy hne
    rw [Finset.mem_singleton] at hx hy
    rw [hx, hy] at hne
    exact (hne rfl).elim
  · intro x hx y hy hlt
    rw [Finset.mem_singleton] at hx hy
    rw [hx, hy] at hlt
    exact (Nat.lt_irrefl _ hlt).elim

/-- A two-cell set is a non-nesting placement when the two cells lie in the
board, are in different rows, and satisfy the decreasing-column condition. -/
theorem isNonNestingPlacement_pair {B : FiniteSkewBoard} (a b : ℕ × ℕ)
    (ha : a ∈ B.cells) (hb : b ∈ B.cells) (hrow : a.1 ≠ b.1)
    (hcol_ab : a.1 < b.1 → b.2 < a.2)
    (hcol_ba : b.1 < a.1 → a.2 < b.2) :
    B.IsNonNestingPlacement ({a, b} : Finset (ℕ × ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · intro x hx y hy hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl
      · exact (hne rfl).elim
      · exact hrow
    · rcases hy with rfl | rfl
      · exact hrow.symm
      · exact (hne rfl).elim
  · intro x hx y hy hlt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl
      · exact (Nat.lt_irrefl _ hlt).elim
      · exact hcol_ab hlt
    · rcases hy with rfl | rfl
      · exact hcol_ba hlt
      · exact (Nat.lt_irrefl _ hlt).elim

private def finsetAllBool {α : Type*} (s : Finset α) (p : α → Bool) : Bool :=
  s.fold (fun a b => a && b) true p

private lemma finsetAllBool_iff {α : Type*} (s : Finset α) (p : α → Bool) :
    finsetAllBool s p ↔ ∀ a ∈ s, p a := by
  classical
  induction s using Finset.induction with
  | empty => simp [finsetAllBool]
  | insert a s ha ih =>
      rw [finsetAllBool, Finset.fold_insert ha, Bool.and_eq_true_iff]
      constructor
      · rintro ⟨hpa, hall⟩ b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact hpa
        · exact ih.mp hall b hb
      · intro hall
        exact ⟨hall a (Finset.mem_insert_self a s), ih.mpr fun b hb =>
          hall b (Finset.mem_insert_of_mem hb)⟩

def isNonNestingPlacementBool (B : FiniteSkewBoard)
    (P : Finset (ℕ × ℕ)) : Bool :=
  finsetAllBool P (fun a => decide (a ∈ B.cells)) &&
    finsetAllBool P (fun a =>
      finsetAllBool P (fun b =>
        decide ((a.1 = b.1 → a.2 ≠ b.2) → a.1 ≠ b.1))) &&
    finsetAllBool P (fun a =>
      finsetAllBool P (fun b => decide (a.1 < b.1 → b.2 < a.2)))

theorem isNonNestingPlacementBool_iff (B : FiniteSkewBoard)
    (P : Finset (ℕ × ℕ)) :
    isNonNestingPlacementBool B P ↔ B.IsNonNestingPlacement P := by
  simp only [isNonNestingPlacementBool, ne_eq, decide_implies, decide_not,
    dite_eq_ite, Bool.if_true_right, Bool.not_or, Bool.not_not,
    Bool.and_eq_true, finsetAllBool_iff, decide_eq_true_eq, Prod.forall,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, not_lt, IsNonNestingPlacement,
    Finset.subset_iff, Prod.mk.injEq, not_and]
  constructor
  · rintro ⟨⟨hsub, hrow⟩, hnest⟩
    refine ⟨hsub, ?_, ?_⟩
    · intro a b hab c d hcd hne
      rcases hrow a b hab c d hcd with hEq | hrow_ne
      · exact (hne hEq.1 hEq.2).elim
      · exact hrow_ne
    · intro a b hab c d hcd hlt
      rcases hnest a b hab c d hcd with hle | hcol
      · exact (False.elim ((not_lt_of_ge hle) hlt))
      · exact hcol
  · rintro ⟨hsub, hrow, hnest⟩
    refine ⟨⟨hsub, ?_⟩, ?_⟩
    · intro a b hab c d hcd
      by_cases ha : a = c
      · by_cases hb : b = d
        · exact Or.inl ⟨ha, hb⟩
        · exact Or.inr (hrow a b hab c d hcd (by intro _; exact hb))
      · exact Or.inr ha
    · intro a b hab c d hcd
      by_cases hlt : a < c
      · exact Or.inr (hnest a b hab c d hcd hlt)
      · exact Or.inl (le_of_not_gt hlt)

/-- Powers of `X` have nonnegative coefficients. -/
private lemma xPow_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs ((X : ℝ[X]) ^ n) := by
  intro k
  by_cases hk : k = n
  · subst k
    simp
  · simp [coeff_X_pow, hk]

/-- The empty board has rook polynomial `1`. -/
@[simp] theorem rookPolynomial_empty :
    empty.rookPolynomial = 1 := by
  classical
  have hpowerset :
      empty.cells.powerset = ({∅} : Finset (Finset (ℕ × ℕ))) := by
    simp [empty]
  have hfilter :
      empty.cells.powerset.filter (fun P => empty.IsNonNestingPlacement P) =
        ({∅} : Finset (Finset (ℕ × ℕ))) := by
    rw [hpowerset]
    apply Finset.filter_true_of_mem
    intro P hP
    have hPempty : P = ∅ := by
      simpa using hP
    subst P
    simp [IsNonNestingPlacement, empty]
  simp [rookPolynomial, hfilter]

/-- Finite skew board rook polynomials have nonnegative coefficients. -/
theorem rookPolynomial_hasNonnegCoeffs (B : FiniteSkewBoard) :
    HasNonnegCoeffs B.rookPolynomial := by
  classical
  unfold rookPolynomial
  intro k
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun (P : Finset (ℕ × ℕ)) _ =>
    xPow_hasNonnegCoeffs P.card k

/-- The empty placement gives the constant coefficient of a finite skew board
rook polynomial. -/
@[simp] theorem rookPolynomial_coeff_zero (B : FiniteSkewBoard) :
    B.rookPolynomial.coeff 0 = 1 := by
  classical
  rw [rookPolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single ∅]
  · simp
  · intro P _hP hne
    have hP_nonzero : P.card ≠ 0 := by
      rwa [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]
    have hzero : ¬ 0 = P.card := fun h => hP_nonzero h.symm
    simp [Polynomial.coeff_X_pow, hzero]
  · intro hnot
    simp at hnot

/-- Finite skew board rook polynomials are nonzero. -/
theorem rookPolynomial_ne_zero (B : FiniteSkewBoard) :
    B.rookPolynomial ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) hzero
  rw [rookPolynomial_coeff_zero] at hcoeff
  norm_num at hcoeff

end FiniteSkewBoard

end GeneralizedSnakePosets
end RealRooted
