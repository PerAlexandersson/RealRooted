import RealRooted.HosterStump.Permutation

/-!
# Graded simplicial posets and their flag vectors

Definitions for the poset-level form of identity (1.3) of Hoster and Stump, *Chow polynomials
of simplicial posets with positive h-vector are real-rooted* (arXiv:2508.15538), after
Stanley, *Combinatorics and commutative algebra*, III.6.

* `IsSimplicialPoset P n rk`: every lower interval `Iic x` is a Boolean lattice of rank `rk x`,
  ranks are at most `n`, and every element lies below one of rank `n`.
* `fVec rk i`: the number of elements of rank `i` (the paper's `f_{i-1}`).
* `hVec n rk`: the `h`-vector, the coefficients of `∑ i, f_i x^i (1 - x)^(n - i)`.
* `flagF rk T`: the number of chains with exactly the ranks `T + 1` (positions are `0`-based:
  position `s` is rank `s + 1`; these are the chains of `P̂` with ranks in `T` selected).
* `flagH rk S`: the flag `h`-vector, `∑ T ⊆ S, (-1)^|S \ T| flagF rk T`.
* `boolChains r U` and `gapMultinomial r U`: chains of subsets of `Fin r` with sizes `U + 1`,
  and their number by recursion on `max U`.
* `desLeCount n k E`: permutations of `n + 1` letters with `w 0 = k` and descent set in `E`.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted.HosterStump

/-- A finite graded simplicial poset of rank `n` with rank function `rk`: every lower interval
is a Boolean lattice of rank `rk x`, ranks are at most `n`, and every element lies below an
element of rank `n`. -/
structure IsSimplicialPoset (P : Type*) [PartialOrder P] (n : ℕ) (rk : P → ℕ) : Prop where
  iic : ∀ x : P, Nonempty (Set.Iic x ≃o Finset (Fin (rk x)))
  rk_le : ∀ x, rk x ≤ n
  graded : ∀ x, ∃ y, x ≤ y ∧ rk y = n

/-- In a simplicial poset the lower interval of `x` has `2 ^ rk x` elements. -/
theorem IsSimplicialPoset.natCard_Iic {P : Type*} [PartialOrder P] {n : ℕ} {rk : P → ℕ}
    (hP : IsSimplicialPoset P n rk) (x : P) : Nat.card (Set.Iic x) = 2 ^ rk x := by
  obtain ⟨f⟩ := hP.iic x
  rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]

variable {P : Type*} [Fintype P]

open scoped Classical in
/-- The number of elements of rank `i` (the paper's `f_{i-1}`). -/
def fVec (rk : P → ℕ) (i : ℕ) : ℕ := (univ.filter fun x => rk x = i).card

/-- The `h`-vector: `∑ k, h_k x^k = ∑ i ≤ n, f_i x^i (1 - x)^(n - i)`. -/
def hVec (n : ℕ) (rk : P → ℕ) (k : ℕ) : ℝ :=
  (∑ i ∈ range (n + 1), C (fVec rk i : ℝ) * X ^ i * (1 - X) ^ (n - i)).coeff k

open scoped Classical in
/-- The flag `f`-vector: chains `c 0 < c 1 < …` with ranks `T + 1` in increasing order
(positions are `0`-based, position `s` is rank `s + 1`). -/
def flagF [PartialOrder P] (rk : P → ℕ) (T : Finset ℕ) : ℕ :=
  (univ.filter fun c : Fin T.card → P =>
    StrictMono c ∧ ∀ j, rk (c j) = T.orderEmbOfFin rfl j + 1).card

/-- The flag `h`-vector, by inclusion–exclusion from the flag `f`-vector. -/
def flagH [PartialOrder P] (rk : P → ℕ) (S : Finset ℕ) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card * (flagF rk T : ℝ)

end RealRooted.HosterStump

end

namespace RealRooted.HosterStump

open Finset

/-- Chains of subsets of `Fin r` with sizes `U + 1` in increasing order. -/
def boolChains (r : ℕ) (U : Finset ℕ) : Finset (Fin U.card → Finset (Fin r)) :=
  univ.filter fun c => StrictMono c ∧ ∀ j, (c j).card = U.orderEmbOfFin rfl j + 1

/-- The number of chains of subsets of an `r`-set with sizes `U + 1`: choose the top set,
of size `max U + 1`, then a chain inside it. -/
def gapMultinomial (r : ℕ) (U : Finset ℕ) : ℕ :=
  if h : U.Nonempty then
    Nat.choose r (U.max' h + 1) * gapMultinomial (U.max' h + 1) (U.erase (U.max' h))
  else 1
termination_by U.card
decreasing_by exact Finset.card_erase_lt_of_mem (Finset.max'_mem U h)

/-- Permutations of `n + 1` letters with `w 0 = k` whose descent set lies in `E`. -/
def desLeCount (n k : ℕ) (E : Finset ℕ) : ℕ :=
  (univ.filter fun w : Equiv.Perm (Fin (n + 1)) => (w 0 : ℕ) = k ∧ desSet w ⊆ E).card

end RealRooted.HosterStump
