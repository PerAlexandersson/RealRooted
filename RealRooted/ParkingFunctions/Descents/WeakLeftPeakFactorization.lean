import RealRooted.ParkingFunctions.Descents.WeakLeftPeakRecurrence

/-!
# Real factorization of the weak-left-peak recurrence

This module casts the terminal-state recurrence to real polynomials and
packages its pair-mix followed by prefix/strict-suffix factorization. It makes
no interlacing-preservation claim.
-/

open Polynomial

namespace RealRooted.ParkingFunctions

noncomputable section

/-- Real cast of the terminal non-descent refinement. -/
def terminalNonDescentReal (m r : ℕ) (j : Fin m) : ℝ[X] :=
  (literalWordWeakLeftPeakTerminalNonDescentRefined m r j).map
    (Int.castRingHom ℝ)

/-- Real cast of the terminal descent refinement. -/
def terminalDescentReal (m r : ℕ) (j : Fin m) : ℝ[X] :=
  (literalWordWeakLeftPeakTerminalDescentRefined m r j).map
    (Int.castRingHom ℝ)

/-- The unmarked pair mix `P_j = N_j + D_j`. -/
def terminalPairMixReal (m r : ℕ) (j : Fin m) : ℝ[X] :=
  terminalNonDescentReal m r j + terminalDescentReal m r j

/-- The marked pair mix `Q_j = X * N_j + D_j`. -/
def terminalXPairMixReal (m r : ℕ) (j : Fin m) : ℝ[X] :=
  X * terminalNonDescentReal m r j + terminalDescentReal m r j

/-- The prefix reconstruction of the next non-descent terminal state. -/
def terminalPrefixPairMixReal (m r : ℕ) (j : Fin m) : ℝ[X] :=
  ∑ i : Fin m, if i ≤ j then terminalPairMixReal m r i else 0

/-- The strict-suffix reconstruction of the next descent terminal state. -/
def terminalStrictSuffixXPairMixReal (m r : ℕ) (j : Fin m) : ℝ[X] :=
  ∑ i : Fin m, if j < i then terminalXPairMixReal m r i else 0

theorem terminalPairMixReal_eq (m r : ℕ) (j : Fin m) :
    terminalPairMixReal m r j =
      terminalNonDescentReal m r j + terminalDescentReal m r j :=
  rfl

theorem terminalXPairMixReal_eq (m r : ℕ) (j : Fin m) :
    terminalXPairMixReal m r j =
      X * terminalNonDescentReal m r j + terminalDescentReal m r j :=
  rfl

/-- Casting the checked non-descent recurrence gives its real prefix form. -/
theorem terminalNonDescentReal_succ (m r : ℕ) (j : Fin m) :
    terminalNonDescentReal m (r + 1) j =
      terminalPrefixPairMixReal m r j := by
  unfold terminalNonDescentReal terminalPrefixPairMixReal terminalPairMixReal
    terminalDescentReal
  rw [literalWordWeakLeftPeakTerminalNonDescentRefined_succ,
    Polynomial.map_sum]
  apply Fintype.sum_congr
  intro i
  by_cases hij : i ≤ j <;> simp [hij, terminalNonDescentReal]

/-- Casting the checked descent recurrence gives its real strict-suffix form. -/
theorem terminalDescentReal_succ (m r : ℕ) (j : Fin m) :
    terminalDescentReal m (r + 1) j =
      terminalStrictSuffixXPairMixReal m r j := by
  unfold terminalDescentReal terminalStrictSuffixXPairMixReal
    terminalXPairMixReal terminalNonDescentReal
  rw [literalWordWeakLeftPeakTerminalDescentRefined_succ,
    Polynomial.map_sum]
  apply Fintype.sum_congr
  intro i
  by_cases hji : j < i <;> simp [hji, terminalDescentReal]

/-- The largest final letter can never be the bottom of a terminal descent. -/
theorem terminalDescentReal_last (m r : ℕ) :
    terminalDescentReal (m + 1) r (Fin.last m) = 0 := by
  unfold terminalDescentReal literalWordWeakLeftPeakTerminalDescentRefined
  rw [Polynomial.map_sum]
  apply Finset.sum_eq_zero
  intro u _
  have hnot : ¬Fin.last m < u (Fin.last r) :=
    not_lt_of_ge (Fin.le_last _)
  simp [hnot]

/-- The outer real terminal-state sum is zero over an empty alphabet. -/
theorem sum_terminalPairMixReal_empty (r : ℕ) :
    (∑ j : Fin 0, terminalPairMixReal 0 r j) = 0 := by
  simp

/-- The non-descent block followed by the reversed descent block. -/
def terminalNDOrderReal (m r : ℕ) : List ℝ[X] :=
  List.ofFn (terminalNonDescentReal m r) ++
    (List.ofFn (terminalDescentReal m r)).reverse

/-- The reversed `P` block followed by the `Q` block. -/
def terminalPQOrderReal (m r : ℕ) : List ℝ[X] :=
  (List.ofFn (terminalPairMixReal m r)).reverse ++
    List.ofFn (terminalXPairMixReal m r)

@[simp]
theorem length_terminalNDOrderReal (m r : ℕ) :
    (terminalNDOrderReal m r).length = 2 * m := by
  simp [terminalNDOrderReal, two_mul]

@[simp]
theorem length_terminalPQOrderReal (m r : ℕ) :
    (terminalPQOrderReal m r).length = 2 * m := by
  simp [terminalPQOrderReal, two_mul]

/-- The next ordered terminal family is exactly the prefix/strict-suffix
reconstruction of the current `P,Q` pair mix. -/
theorem terminalNDOrderReal_succ (m r : ℕ) :
    terminalNDOrderReal m (r + 1) =
      List.ofFn (terminalPrefixPairMixReal m r) ++
        (List.ofFn (terminalStrictSuffixXPairMixReal m r)).reverse := by
  have hN : List.ofFn (terminalNonDescentReal m (r + 1)) =
      List.ofFn (terminalPrefixPairMixReal m r) := by
    exact congrArg List.ofFn <| funext fun j =>
      terminalNonDescentReal_succ m r j
  have hD : List.ofFn (terminalDescentReal m (r + 1)) =
      List.ofFn (terminalStrictSuffixXPairMixReal m r) := by
    exact congrArg List.ofFn <| funext fun j =>
      terminalDescentReal_succ m r j
  simp [terminalNDOrderReal, hN, hD]

end

end RealRooted.ParkingFunctions
