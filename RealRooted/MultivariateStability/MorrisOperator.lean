module

public import RealRooted.Mathlib.RingTheory.MvPolynomial.DividedDifference
public import RealRooted.Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Data.List.GetD
public import RealRooted.Mathlib.RingTheory.MvPolynomial.Symmetric.Homogeneous
public import RealRooted.Mathlib.RingTheory.MvPolynomial.Symmetric.ElementaryMonomial
public import RealRooted.Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import RealRooted.Mathlib.LinearAlgebra.TriangularBasis
public import RealRooted.Multiaffine
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Tactic.LinearCombination

/-!
# The Morris differential operator on symmetric polynomials

For `q` variables, Liu--Zhang, arXiv:2609.15201v2, Section 1.2, define

`A_q = ∑ i, x_i ^ 2 * ∂_i ^ 2`,

`B_q = 2 * ∑ i < j, (x_i ^ 2 * ∂_i - x_j ^ 2 * ∂_j) / (x_i - x_j)`,

and `D_q = B_q - A_q`.  This file realizes those formulas as linear maps.
-/

@[expose] public section

namespace RealRooted.LiuZhang

open MvPolynomial
open Finset

noncomputable section

variable {R : Type*} [CommRing R]

private theorem X_sub_X_mul_left_injective {σ : Type*} (i j : σ) (hij : i ≠ j) :
    Function.Injective (fun P : MvPolynomial σ R => (X i - X j) * P) := by
  classical
  intro P Q hPQ
  apply (asPolynomial (R := R) i).injective
  apply (Polynomial.monic_X_sub_C (X ⟨j, hij.symm⟩)).isRegular.left
  simpa only [map_mul, map_sub, asPolynomial_X_self,
    asPolynomial_X_of_ne i j hij.symm] using
      congrArg (asPolynomial (R := R) i) hPQ

/-- Swap divided differences on finitely many variables commute with
permutations of those variables. -/
theorem rename_swapDividedDifference_fin {q : ℕ}
    (e : Equiv.Perm (Fin q)) (i j : Fin q) (hij : i ≠ j)
    (P : MvPolynomial (Fin q) R) :
    rename e (swapDividedDifference i j hij P) =
      swapDividedDifference (e i) (e j) (e.injective.ne hij) (rename e P) := by
  classical
  have hfun : e ∘ Equiv.swap i j = Equiv.swap (e i) (e j) ∘ e := by
    funext k; change e (Equiv.swap i j k) = Equiv.swap (e i) (e j) (e k)
    rcases eq_or_ne k i with rfl | hki
    · simp
    · rcases eq_or_ne k j with rfl | hkj
      · simp
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj,
          Equiv.swap_apply_of_ne_of_ne (e.injective.ne hki)
            (e.injective.ne hkj)]
  have hswap : rename e (rename (Equiv.swap i j) P) =
      rename (Equiv.swap (e i) (e j)) (rename e P) := by
    rw [rename_rename, rename_rename, hfun]
  apply X_sub_X_mul_left_injective (R := R) (e i) (e j) (e.injective.ne hij)
  calc
    (X (e i) - X (e j)) * rename e (swapDividedDifference i j hij P) =
        rename e ((X i - X j) * swapDividedDifference i j hij P) := by
      rw [map_mul, map_sub, rename_X, rename_X]
    _ = rename e (P - rename (Equiv.swap i j) P) := by
      rw [X_sub_X_mul_swapDividedDifference]
    _ = rename e P - rename (Equiv.swap (e i) (e j)) (rename e P) := by
      rw [map_sub, hswap]
    _ = (X (e i) - X (e j)) *
        swapDividedDifference (e i) (e j) (e.injective.ne hij) (rename e P) := by
      rw [X_sub_X_mul_swapDividedDifference]

/-- The operator `A_q = ∑ i, x_i ^ 2 * ∂_i ^ 2` from
Liu--Zhang, arXiv:2609.15201v2, equation (4.9). -/
def morrisA (q : ℕ) :
    MvPolynomial (Fin q) R →ₗ[R] MvPolynomial (Fin q) R :=
  ∑ i, (squaredPDeriv i).comp (pderiv i).toLinearMap

@[simp]
theorem morrisA_apply (q : ℕ) (P : MvPolynomial (Fin q) R) :
    morrisA q P = ∑ i, X i ^ 2 * pderiv i (pderiv i P) := by
  simp [morrisA, squaredPDeriv_apply]

/-- Bijective renaming transports a coordinate second-derivative summand to
the corresponding renamed coordinate. -/
theorem rename_squaredPDeriv_pderiv {σ τ : Type*}
    (e : σ ≃ τ) (i : σ) (P : MvPolynomial σ R) :
    rename e (squaredPDeriv i (pderiv i P)) =
      squaredPDeriv (e i) (pderiv (e i) (rename e P)) := by
  rw [squaredPDeriv_apply, squaredPDeriv_apply, map_mul, map_pow, rename_X,
    ← pderiv_rename (R := R) e.injective i (pderiv i P),
    ← pderiv_rename (R := R) e.injective i P]

/-- Bijective renaming transports a coordinate first-derivative summand to
the corresponding renamed coordinate. -/
theorem rename_squaredPDeriv {σ τ : Type*}
    (e : σ ≃ τ) (i : σ) (P : MvPolynomial σ R) :
    rename e (squaredPDeriv i P) = squaredPDeriv (e i) (rename e P) := by
  rw [squaredPDeriv_apply, squaredPDeriv_apply, map_mul, map_pow, rename_X,
    ← pderiv_rename (R := R) e.injective i P]

/-- The operator `A_q` maps symmetric polynomials to symmetric polynomials. -/
theorem IsSymmetric.morrisA {q : ℕ} {P : MvPolynomial (Fin q) R}
    (hP : P.IsSymmetric) : (morrisA q P).IsSymmetric := by
  intro e
  rw [morrisA_apply, map_sum]
  simp_rw [← squaredPDeriv_apply, rename_squaredPDeriv_pderiv]
  rw [hP e]
  exact Equiv.sum_comp e fun i => squaredPDeriv i (pderiv i P)

/-- The restriction of `A_q` to the symmetric polynomial ring, as in
Liu--Zhang, arXiv:2609.15201v2, equation (4.9). -/
def morrisAOnSymmetric (q : ℕ) :
    symmetricSubalgebra (Fin q) R →ₗ[R]
      symmetricSubalgebra (Fin q) R :=
  ((morrisA q).domRestrict (symmetricSubalgebra (Fin q) R).toSubmodule).codRestrict
    (symmetricSubalgebra (Fin q) R).toSubmodule fun P =>
      IsSymmetric.morrisA P.2

@[simp]
theorem morrisAOnSymmetric_apply (q : ℕ)
    (P : symmetricSubalgebra (Fin q) R) :
    (morrisAOnSymmetric q P : MvPolynomial (Fin q) R) = morrisA q P :=
  rfl

/-- A coordinate second-derivative summand acts diagonally on a monomial. -/
theorem squaredPDeriv_pderiv_monomial {σ : Type*}
    (i : σ) (d : σ →₀ ℕ) (r : R) :
    X i ^ 2 * pderiv i (pderiv i (monomial d r)) =
      (d i * (d i - 1)) • monomial d r := by
  have heuler : X i * pderiv i (monomial d r) = d i • monomial d r :=
    X_mul_pderiv_monomial
  have heuler' : X i * pderiv i (monomial d r) =
      (d i : MvPolynomial σ R) * monomial d r := by
    simpa only [nsmul_eq_mul] using heuler
  have heuler2 := congrArg (fun P => X i * pderiv i P) heuler
  have hrhs : X i * pderiv i (d i • monomial d r) =
      d i • (d i • monomial d r) := by
    rw [map_nsmul]
    simp only [nsmul_eq_mul]
    rw [← mul_assoc, mul_comm (X i) (d i : MvPolynomial σ R),
      mul_assoc, heuler']
  have hid :
      X i * pderiv i (X i * pderiv i (monomial d r)) =
        X i * pderiv i (monomial d r) +
          X i ^ 2 * pderiv i (pderiv i (monomial d r)) := by
    rw [pderiv_mul, pderiv_X_self]; ring
  rw [hid, heuler, hrhs] at heuler2
  cases hdi : d i with
  | zero => simp [hdi]
  | succ n =>
      simp only [hdi, Nat.succ_sub_one, nsmul_eq_mul] at heuler2 ⊢
      push_cast at heuler2 ⊢; linear_combination heuler2

/-- The operator `A_q` acts diagonally on a monomial, with eigenvalue the sum
of `d_i * (d_i - 1)` over its exponents. -/
theorem morrisA_monomial {q : ℕ} (d : Fin q →₀ ℕ) (r : R) :
    morrisA q (monomial d r) =
      (∑ i, d i * (d i - 1)) • monomial d r := by
  rw [morrisA_apply]
  simp_rw [squaredPDeriv_pderiv_monomial]
  simpa using Finset.sum_nsmul_assoc Finset.univ
    (fun i => d i * (d i - 1)) (monomial d r)

/-- A product of variables indexed by a multiset is the monomial whose
exponent vector records the multiplicities in that multiset. -/
theorem prod_map_X_eq_monomial_toFinsupp {σ : Type*} [DecidableEq σ]
    (s : Multiset σ) :
    (s.map (X : σ → MvPolynomial σ R)).prod =
      monomial s.toFinsupp 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, ih]
      rw [show Multiset.toFinsupp (a ::ₘ s) =
          Finsupp.single a 1 + Multiset.toFinsupp s by
        rw [← Multiset.toFinsupp_singleton, ← Multiset.toFinsupp_add]; rfl]
      rw [X, monomial_mul_monomial]; simp only [one_mul]

/-- The diagonal eigenvalue `∑ i, mu_i * (mu_i - 1)` of `A_q` on the
monomial-symmetric polynomial indexed by `mu`. -/
def morrisAWeight {n : ℕ} (mu : n.Partition) : ℕ :=
  (mu.parts.map fun k => k * (k - 1)).sum

/-- The `i`-th row length of a partition, after arranging its parts in
weakly decreasing order and padding with zeros. The index is zero-based. -/
def partitionRow {n : ℕ} (mu : n.Partition) (i : ℕ) : ℕ :=
  (mu.parts.sort (· ≥ ·)).getD i 0

/-- The eigenvalue from Lemma 4.10 of Liu--Zhang,
arXiv:2609.15201v2:
`epsilon_mu = 2 * ∑ (i,j) in [mu], (q + 1 - i - j)`.

The two finite-range indices in this definition are zero-based, so its
summand is `q + 1 - (i + 1) - (j + 1)`. When `mu` has at most `q` parts,
this is exactly the displayed sum over its Ferrers diagram. -/
def morrisEigenvalue (q : ℕ) {n : ℕ} (mu : n.Partition) : ℤ :=
  2 * (Finset.range q).sum fun i =>
    (Finset.range (partitionRow mu i)).sum fun j =>
      (q : ℤ) + 1 - ((i : ℕ) : ℤ) - 1 - ((j : ℕ) : ℤ) - 1

/-- The coordinate-multiplicity expression for a symmetric monomial equals
the partition statistic `morrisAWeight` of its shape. -/
theorem sum_toFinsupp_mul_pred_eq_morrisAWeight_ofSym
    {n q : ℕ} (s : Sym (Fin q) n) :
    (∑ i, s.1.toFinsupp i * (s.1.toFinsupp i - 1)) =
      morrisAWeight (Nat.Partition.ofSym s) := by
  classical
  simp only [morrisAWeight, Nat.Partition.ofSym,
    Multiset.toFinsupp_apply, Multiset.map_map]
  change Finset.univ.sum (fun i => s.1.count i * (s.1.count i - 1)) =
    s.1.toFinset.sum (fun i => s.1.count i * (s.1.count i - 1))
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  rw [Multiset.count_eq_zero.mpr (by simpa using hi), zero_mul]

/-- The action of `A_q` on the monomial-symmetric basis is diagonal, with
coefficient `∑ i, mu_i * (mu_i - 1)` as in Lemma 4.10 of Liu--Zhang,
arXiv:2609.15201v2. -/
theorem morrisA_msymm {n q : ℕ} (mu : n.Partition) :
    morrisA q (msymm (Fin q) R mu) =
      morrisAWeight mu • msymm (Fin q) R mu := by
  rw [msymm, map_sum]
  simp_rw [prod_map_X_eq_monomial_toFinsupp, morrisA_monomial,
    sum_toFinsupp_mul_pred_eq_morrisAWeight_ofSym]
  have hshape (s : {a : Sym (Fin q) n // Nat.Partition.ofSym a = mu}) :
      morrisAWeight (Nat.Partition.ofSym s.1) = morrisAWeight mu := by
    rw [s.2]
  simp_rw [hshape]
  exact Finset.smul_sum.symm

/-- Bijective renaming transports a pair summand of the Morris operator to
the pair indexed by the renamed coordinates. -/
theorem rename_squaredPDerivDividedDifference {q : ℕ}
    (e : Equiv.Perm (Fin q)) (i j : Fin q) (hij : i ≠ j)
    (P : MvPolynomial (Fin q) R) :
    rename e (squaredPDerivDividedDifference i j hij P) =
      squaredPDerivDividedDifference (e i) (e j) (e.injective.ne hij)
        (rename e P) := by
  rw [squaredPDerivDividedDifference, LinearMap.comp_apply,
    rename_swapDividedDifference_fin, squaredPDerivDividedDifference, LinearMap.comp_apply,
    rename_squaredPDeriv]

/-- On a symmetric polynomial, the pair summand of the Morris operator does
not depend on the orientation of the pair. -/
theorem squaredPDerivDividedDifference_comm_of_isSymmetric
    {q : ℕ} {P : MvPolynomial (Fin q) R} (hP : P.IsSymmetric)
    (i j : Fin q) (hij : i ≠ j) :
    squaredPDerivDividedDifference i j hij P =
      squaredPDerivDividedDifference j i hij.symm P := by
  apply X_sub_X_mul_left_injective (R := R) i j hij
  change (X i - X j) * squaredPDerivDividedDifference i j hij P =
    (X i - X j) * squaredPDerivDividedDifference j i hij.symm P
  rw [X_sub_X_mul_squaredPDerivDividedDifference_of_isSymmetric hP]
  have hreverse :=
    X_sub_X_mul_squaredPDerivDividedDifference_of_isSymmetric hP j i hij.symm
  rw [show (X i - X j) * squaredPDerivDividedDifference j i hij.symm P =
      -((X j - X i) * squaredPDerivDividedDifference j i hij.symm P) by ring,
    hreverse]
  ring

/-- A pair summand of `B_q` obeys the Leibniz rule on symmetric
polynomials. This is the polynomial form of equation (4.10) in Liu--Zhang,
arXiv:2609.15201v2. -/
theorem squaredPDerivDividedDifference_mul_of_isSymmetric
    {q : ℕ} {P Q : MvPolynomial (Fin q) R}
    (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (i j : Fin q) (hij : i ≠ j) :
    squaredPDerivDividedDifference i j hij (P * Q) =
      squaredPDerivDividedDifference i j hij P * Q +
        P * squaredPDerivDividedDifference i j hij Q := by
  apply X_sub_X_mul_left_injective (R := R) i j hij
  change (X i - X j) * squaredPDerivDividedDifference i j hij (P * Q) =
    (X i - X j) *
      (squaredPDerivDividedDifference i j hij P * Q +
        P * squaredPDerivDividedDifference i j hij Q)
  rw [X_sub_X_mul_squaredPDerivDividedDifference_of_isSymmetric
    (hP.mul hQ)]
  have hP' :=
    X_sub_X_mul_squaredPDerivDividedDifference_of_isSymmetric hP i j hij
  have hQ' :=
    X_sub_X_mul_squaredPDerivDividedDifference_of_isSymmetric hQ i j hij
  simp only [pderiv_mul]
  calc
    _ = (X i ^ 2 * pderiv i P - X j ^ 2 * pderiv j P) * Q +
        P * (X i ^ 2 * pderiv i Q - X j ^ 2 * pderiv j Q) := by
      ring
    _ = _ := by rw [← hP', ← hQ']; ring

/-- The operator
`B_q = 2 * ∑ i < j, (x_i ^ 2 * ∂_i - x_j ^ 2 * ∂_j) / (x_i - x_j)`
from Liu--Zhang, arXiv:2609.15201v2, equation (4.9). -/
def morrisB (q : ℕ) :
    MvPolynomial (Fin q) R →ₗ[R] MvPolynomial (Fin q) R :=
  2 • ∑ i, ∑ j, if hij : i < j then
    squaredPDerivDividedDifference i j hij.ne else 0

/-- The ordered-pair form of `B_q`; on symmetric polynomials it equals the
paper's twice-unordered-pair formula `morrisB`. -/
def morrisBOrdered (q : ℕ) :
    MvPolynomial (Fin q) R →ₗ[R] MvPolynomial (Fin q) R :=
  ∑ i, ∑ j, if hij : i ≠ j then
    squaredPDerivDividedDifference i j hij else 0

@[simp]
theorem morrisB_apply (q : ℕ) (P : MvPolynomial (Fin q) R) :
    morrisB q P = 2 • ∑ i, ∑ j, if hij : i < j then
      squaredPDerivDividedDifference i j hij.ne P else 0 := by
  simp only [morrisB, LinearMap.smul_apply, LinearMap.sum_apply]
  apply congrArg (2 • ·)
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> rfl

@[simp]
theorem morrisBOrdered_apply (q : ℕ) (P : MvPolynomial (Fin q) R) :
    morrisBOrdered q P = ∑ i, ∑ j, if hij : i ≠ j then
      squaredPDerivDividedDifference i j hij P else 0 := by
  simp only [morrisBOrdered, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> rfl

/-- On symmetric polynomials, the paper's sum over unordered pairs equals the
equivalent sum over all ordered pairs. -/
theorem morrisB_eq_morrisBOrdered_of_isSymmetric
    {q : ℕ} {P : MvPolynomial (Fin q) R} (hP : P.IsSymmetric) :
    morrisB q P = morrisBOrdered q P := by
  rw [morrisB_apply, morrisBOrdered_apply]
  have hsplit :
      (∑ i, ∑ j, if hij : i ≠ j then
        squaredPDerivDividedDifference i j hij P else 0) =
        (∑ i, ∑ j, if hij : i < j then
          squaredPDerivDividedDifference i j hij.ne P else 0) +
        ∑ i, ∑ j, if hji : j < i then
          squaredPDerivDividedDifference i j hji.ne.symm P else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hne : i ≠ j
    · rcases lt_or_gt_of_ne hne with hij | hji
      · rw [dite_eq_left hne, dite_eq_left hij,
          dite_eq_right (not_lt_of_ge (le_of_lt hij)), add_zero]
      · rw [dite_eq_left hne,
          dite_eq_right (not_lt_of_ge (le_of_lt hji)), dite_eq_left hji,
          zero_add]
    · have hij : i = j := not_ne_iff.mp hne
      subst j
      rw [dite_eq_right (not_ne_iff.mpr rfl), dite_eq_right (lt_irrefl i),
        zero_add]
  have hreverse :
      (∑ i, ∑ j, if hji : j < i then
        squaredPDerivDividedDifference i j hji.ne.symm P else 0) =
        ∑ i, ∑ j, if hij : i < j then
          squaredPDerivDividedDifference i j hij.ne P else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · exact (squaredPDerivDividedDifference_comm_of_isSymmetric hP i j hij.ne).symm
    · rfl
  rw [hsplit, hreverse, two_smul]

/-- The ordered-pair form of `B_q` maps symmetric polynomials to symmetric
polynomials. -/
theorem IsSymmetric.morrisBOrdered {q : ℕ} {P : MvPolynomial (Fin q) R}
    (hP : P.IsSymmetric) : (morrisBOrdered q P).IsSymmetric := by
  intro e
  rw [morrisBOrdered_apply, map_sum]
  simp_rw [map_sum]
  have hrename :
      (∑ i, ∑ j, rename e (if hij : i ≠ j then
        squaredPDerivDividedDifference i j hij P else 0)) =
        ∑ i, ∑ j, if hij : i ≠ j then
          squaredPDerivDividedDifference (e i) (e j) (e.injective.ne hij)
            (rename e P) else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · exact rename_squaredPDerivDividedDifference e i j hij P
    · exact map_zero (rename (R := R) e)
  rw [hrename]
  let f := fun i j => if hij : i ≠ j then
    squaredPDerivDividedDifference i j hij (rename e P) else 0
  have htoF :
      (∑ i, ∑ j, if hij : i ≠ j then
        squaredPDerivDividedDifference (e i) (e j) (e.injective.ne hij)
          (rename e P) else 0) = ∑ i, ∑ j, f (e i) (e j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only [f]
    by_cases hij : i ≠ j <;> simp_all
  rw [htoF]
  rw [Equiv.sum_comp e fun i => ∑ j, f i (e j)]
  simp_rw [Equiv.sum_comp e]
  dsimp only [f]
  rw [hP e]

/-- The operator `B_q` maps symmetric polynomials to symmetric polynomials. -/
theorem IsSymmetric.morrisB {q : ℕ} {P : MvPolynomial (Fin q) R}
    (hP : P.IsSymmetric) : (morrisB q P).IsSymmetric := by
  rw [morrisB_eq_morrisBOrdered_of_isSymmetric hP]
  exact IsSymmetric.morrisBOrdered hP

/-- The restriction of `B_q` to the symmetric polynomial ring, as in
Liu--Zhang, arXiv:2609.15201v2, equation (4.9). -/
def morrisBOnSymmetric (q : ℕ) :
    symmetricSubalgebra (Fin q) R →ₗ[R]
      symmetricSubalgebra (Fin q) R :=
  ((morrisB q).domRestrict (symmetricSubalgebra (Fin q) R).toSubmodule).codRestrict
    (symmetricSubalgebra (Fin q) R).toSubmodule fun P =>
      IsSymmetric.morrisB P.2

@[simp]
theorem morrisBOnSymmetric_apply (q : ℕ)
    (P : symmetricSubalgebra (Fin q) R) :
    (morrisBOnSymmetric q P : MvPolynomial (Fin q) R) = morrisB q P :=
  rfl

/-- The operator `B_q` obeys the derivation rule on symmetric polynomials,
as asserted in equation (4.10) of Liu--Zhang, arXiv:2609.15201v2. -/
theorem morrisB_mul_of_isSymmetric {q : ℕ}
    {P Q : MvPolynomial (Fin q) R}
    (hP : P.IsSymmetric) (hQ : Q.IsSymmetric) :
    morrisB q (P * Q) = morrisB q P * Q + P * morrisB q Q := by
  rw [morrisB_eq_morrisBOrdered_of_isSymmetric (hP.mul hQ),
    morrisBOrdered_apply]
  have hsplit :
      (∑ i, ∑ j, if hij : i ≠ j then
        squaredPDerivDividedDifference i j hij (P * Q) else 0) =
        (∑ i, ∑ j, if hij : i ≠ j then
          squaredPDerivDividedDifference i j hij P else 0) * Q +
        P * ∑ i, ∑ j, if hij : i ≠ j then
          squaredPDerivDividedDifference i j hij Q else 0 := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i ≠ j
    · simp only [dite_eq_left hij]
      rw [squaredPDerivDividedDifference_mul_of_isSymmetric hP hQ]
    · simp only [dite_eq_right hij, zero_mul, mul_zero, add_zero]
  rw [hsplit]
  rw [← morrisBOrdered_apply, ← morrisBOrdered_apply,
    ← morrisB_eq_morrisBOrdered_of_isSymmetric hP,
    ← morrisB_eq_morrisBOrdered_of_isSymmetric hQ]

/-- The paper's `B_q`, bundled as a derivation of the symmetric polynomial
ring; see Liu--Zhang, arXiv:2609.15201v2, equation (4.10). -/
def morrisBDerivation (q : ℕ) :
    Derivation R (symmetricSubalgebra (Fin q) R)
      (symmetricSubalgebra (Fin q) R) :=
  Derivation.mk' (morrisBOnSymmetric q) fun P Q => by
    apply Subtype.ext
    change morrisB q
      ((P : MvPolynomial (Fin q) R) * (Q : MvPolynomial (Fin q) R)) =
        (P : MvPolynomial (Fin q) R) * morrisB q Q +
          (Q : MvPolynomial (Fin q) R) * morrisB q P
    rw [morrisB_mul_of_isSymmetric P.2 Q.2]
    ring

@[simp]
theorem morrisBDerivation_apply (q : ℕ)
    (P : symmetricSubalgebra (Fin q) R) :
    (morrisBDerivation q P : MvPolynomial (Fin q) R) = morrisB q P :=
  rfl

private theorem rename_swap_eq_self_of_not_mem_vars
    {q : ℕ} {P : MvPolynomial (Fin q) R} (i j : Fin q)
    (hi : i ∉ P.vars) (hj : j ∉ P.vars) :
    rename (Equiv.swap i j) P = P := by
  apply MvPolynomial.hom_congr_vars
    (f₁ := (rename (R := R) (Equiv.swap i j)).toRingHom)
    (f₂ := RingHom.id _)
    (p₁ := P) (p₂ := P)
  · ext r
    simp
  · intro k hk _
    rw [RingHom.id_apply]
    calc
      (rename (R := R) (Equiv.swap i j)).toRingHom (X k) =
          X (Equiv.swap i j k) := rename_X _ _
      _ = X k := by
        rw [Equiv.swap_apply_of_ne_of_ne]
        · exact fun hki => hi (hki ▸ hk)
        · exact fun hkj => hj (hkj ▸ hk)
  · rfl

/-- On a symmetric multiaffine polynomial, the difference between two
first derivatives is controlled by the corresponding mixed derivative. -/
theorem pderiv_sub_pderiv_of_isSymmetric_of_isMultiaffine
    {q : ℕ} {P : MvPolynomial (Fin q) R}
    (hP : P.IsSymmetric) (hma : P.IsMultiaffine)
    (i j : Fin q) :
    pderiv j P - pderiv i P =
      (X i - X j) * pderiv i (pderiv j P) := by
  have hrename :
      rename (Equiv.swap i j) (pderiv i P) = pderiv j P := by
    rw [← pderiv_rename (R := R) (Equiv.swap i j).injective i P,
      Equiv.swap_apply_left, hP (Equiv.swap i j)]
  have hconst :
      specializeZero i (pderiv j P) =
        specializeZero j (pderiv i P) := by
    have hs := specializeZero_rename (S := R) (Equiv.swap i j)
      (Equiv.swap i j).injective j (pderiv i P)
    rw [Equiv.swap_apply_right, hrename] at hs
    rw [hs]
    apply rename_swap_eq_self_of_not_mem_vars i j
    · intro hi
      exact hma.notMem_vars_pderiv_self i
        (Finset.mem_of_mem_erase
          (vars_specializeZero_subset_erase (pderiv i P) j hi))
    · intro hj
      exact Finset.notMem_erase j _
        (vars_specializeZero_subset_erase (pderiv i P) j hj)
  have hi := (hma.pderiv j).eq_specializeZero_add_X_mul_pderiv i
  have hj := (hma.pderiv i).eq_specializeZero_add_X_mul_pderiv j
  rw [hconst] at hi
  rw [pderiv_comm] at hj
  linear_combination hi - hj

/-- The pair summand in `B_q` has an Euler-operator formula on symmetric
multiaffine polynomials. -/
theorem squaredPDerivDividedDifference_eq_of_isMultiaffine
    {q : ℕ} {P : MvPolynomial (Fin q) R}
    (hP : P.IsSymmetric) (hma : P.IsMultiaffine)
    (i j : Fin q) (hij : i ≠ j) :
    squaredPDerivDividedDifference i j hij P =
      X i * pderiv i P + X j * pderiv j P -
        X i * X j * pderiv i (pderiv j P) := by
  apply X_sub_X_mul_left_injective (R := R) i j hij
  change (X i - X j) * squaredPDerivDividedDifference i j hij P =
    (X i - X j) *
      (X i * pderiv i P + X j * pderiv j P -
        X i * X j * pderiv i (pderiv j P))
  rw [X_sub_X_mul_squaredPDerivDividedDifference_of_isSymmetric hP]
  linear_combination -X i * X j *
    pderiv_sub_pderiv_of_isSymmetric_of_isMultiaffine hP hma i j

private theorem sum_dite_ne_eq_pred_nsmul {q : ℕ} (i : Fin q)
    (A : MvPolynomial (Fin q) R) :
    (∑ j, if _hij : i ≠ j then A else 0) = (q - 1) • A := by
  classical
  calc
    (∑ j, if _hij : i ≠ j then A else 0) =
        (Finset.univ.filter fun j : Fin q => i ≠ j).sum (fun _ => A) := by
      symm
      exact Finset.sum_filter (s := Finset.univ) (fun j : Fin q => i ≠ j)
        (fun _ => A)
    _ = (q - 1) • A := by rw [Finset.filter_ne]; simp

private theorem sum_dite_ne_eq_pred_nsmul' {q : ℕ} (i : Fin q)
    (A : MvPolynomial (Fin q) R) :
    (∑ j, if _hji : j ≠ i then A else 0) = (q - 1) • A := by
  simpa only [ne_comm] using sum_dite_ne_eq_pred_nsmul i A

/-- The elementary-eigenvalue calculation used in Liu--Zhang,
arXiv:2609.15201v2, equation (4.11), in a reusable homogeneous form. -/
theorem morrisB_eq_smul_of_isSymmetric_of_isMultiaffine_of_isHomogeneous
    {q n : ℕ} {P : MvPolynomial (Fin q) R}
    (hP : P.IsSymmetric) (hma : P.IsMultiaffine)
    (hhom : P.IsHomogeneous n) (hnq : n ≤ q) :
    morrisB q P = (n * (2 * q - n - 1)) • P := by
  have hleft :
      (∑ i, ∑ j, if _hij : i ≠ j then X i * pderiv i P else 0) =
        (q - 1) • ∑ i, X i * pderiv i P := by
    simpa only [sum_dite_ne_eq_pred_nsmul] using Finset.smul_sum.symm
  have hright :
      (∑ i, ∑ j, if _hij : i ≠ j then X j * pderiv j P else 0) =
        (q - 1) • ∑ i, X i * pderiv i P := by
    rw [Finset.sum_comm]
    simp_rw [sum_dite_ne_eq_pred_nsmul']
    exact Finset.smul_sum.symm
  have hcross :
      (∑ i, ∑ j, if hij : i ≠ j then
        X i * X j * pderiv i (pderiv j P) else 0) =
        (n - 1) • ∑ i, X i * pderiv i P := by
    calc
      (∑ i, ∑ j, if hij : i ≠ j then
          X i * X j * pderiv i (pderiv j P) else 0) =
          ∑ i, X i * (∑ j, X j * pderiv j (pderiv i P)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hij : i ≠ j
        · rw [dite_eq_left hij, pderiv_comm]
          ring
        · rw [not_ne_iff.mp hij, dite_eq_right (not_ne_iff.mpr rfl),
            hma.pderiv_pderiv_self_eq_zero]
          simp
      _ = ∑ i, X i * ((n - 1) • pderiv i P) := by
        exact Finset.sum_congr rfl fun i _ =>
          congrArg (X i * ·) (hhom.pderiv (i := i)).sum_X_mul_pderiv
      _ = (n - 1) • ∑ i, X i * pderiv i P := by
        simp only [Finset.smul_sum, nsmul_eq_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
  rw [morrisB_eq_morrisBOrdered_of_isSymmetric hP,
    morrisBOrdered_apply]
  have hexpand :
      (∑ i, ∑ j, if hij : i ≠ j then
        squaredPDerivDividedDifference i j hij P else 0) =
        (∑ i, ∑ j, if _hij : i ≠ j then
          X i * pderiv i P else 0) +
        (∑ i, ∑ j, if _hij : i ≠ j then
          X j * pderiv j P else 0) -
        ∑ i, ∑ j, if hij : i ≠ j then
          X i * X j * pderiv i (pderiv j P) else 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i ≠ j
    · simp only [dite_eq_left hij]
      rw [squaredPDerivDividedDifference_eq_of_isMultiaffine hP hma i j hij]
    · simp [hij]
  rw [hexpand, hleft, hright, hcross, hhom.sum_X_mul_pderiv]
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hqpos : 0 < q := hnpos.trans_le hnq
  have hn2q : n ≤ 2 * q := by lia
  have hone : 1 ≤ 2 * q - n := by lia
  simp only [nsmul_eq_mul]
  push_cast [Nat.cast_sub hqpos, Nat.cast_sub hnpos,
    Nat.cast_sub hn2q, Nat.cast_sub hone]
  ring

/-- Equation (4.11) of Liu--Zhang, arXiv:2609.15201v2. -/
theorem morrisB_esymm [Nontrivial R] (q n : ℕ) (hnq : n ≤ q) :
    morrisB q (esymm (Fin q) R n) =
      (n * (2 * q - n - 1)) • esymm (Fin q) R n :=
  morrisB_eq_smul_of_isSymmetric_of_isMultiaffine_of_isHomogeneous
    (esymm_isSymmetric (Fin q) R n) (MvPolynomial.IsMultiaffine.esymm n)
    (isHomogeneous_esymm n) hnq

/-- The eigenvalue of `B_q` on an elementary-symmetric product. -/
def morrisBWeight (q : ℕ) {N : ℕ} (mu : N.Partition) : ℕ :=
  (mu.parts.map fun k => k * (2 * q - k - 1)).sum

private theorem isSymmetric_prod_esymm (q : ℕ) (s : Multiset ℕ) :
    ((s.map (esymm (Fin q) R)).prod).IsSymmetric := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons k s ih =>
      simpa using (esymm_isSymmetric (Fin q) R k).mul ih

private theorem morrisB_prod_esymm_multiset [Nontrivial R]
    (q : ℕ) (s : Multiset ℕ)
    (hs : ∀ k ∈ s, k ≤ q) :
    morrisB q (s.map (esymm (Fin q) R)).prod =
      (s.map fun k => k * (2 * q - k - 1)).sum •
        (s.map (esymm (Fin q) R)).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      simp [morrisB_apply, squaredPDerivDividedDifference,
        squaredPDeriv_apply]
  | @cons k s ih =>
      have hkq : k ≤ q := hs k (by simp)
      have hsq : ∀ l ∈ s, l ≤ q := fun l hl => hs l (by simp [hl])
      rw [Multiset.map_cons, Multiset.prod_cons,
        morrisB_mul_of_isSymmetric
          (esymm_isSymmetric (Fin q) R k)
          (isSymmetric_prod_esymm q s),
        morrisB_esymm q k hkq, ih hsq]
      simp only [Multiset.map_cons, Multiset.sum_cons, nsmul_eq_mul]
      push_cast
      ring

/-- The `B_q` eigenvalue of a product of elementary symmetric polynomials.
This is the derivation step in the proof of Lemma 4.10 of Liu--Zhang,
arXiv:2609.15201v2. -/
theorem morrisB_esymmPart [Nontrivial R] {N : ℕ}
    (q : ℕ) (mu : N.Partition)
    (hmu : ∀ k ∈ mu.parts, k ≤ q) :
    morrisB q (esymmPart (Fin q) R mu) =
      morrisBWeight q mu • esymmPart (Fin q) R mu :=
  morrisB_prod_esymm_multiset (R := R) q mu.parts hmu

/-- The product `E_mu` in equation (4.3) of Liu--Zhang,
arXiv:2609.15201v2. -/
def morrisElementary (q : ℕ) {N : ℕ} (mu : N.Partition) :
    MvPolynomial (Fin q) R :=
  esymmPart (Fin q) R mu.conjugate

/-- The action of `B_q` on the elementary product `E_mu`, as used in
equation (4.20) of Liu--Zhang, arXiv:2609.15201v2. -/
theorem morrisB_morrisElementary [Nontrivial R] {N : ℕ}
    (q : ℕ) (mu : N.Partition)
    (hmu : mu.parts.card ≤ q) :
    morrisB q (morrisElementary (R := R) q mu) =
      morrisBWeight q mu.conjugate • morrisElementary (R := R) q mu :=
  morrisB_esymmPart q mu.conjugate fun _ hk =>
    (mu.le_card_parts_of_mem_conjugate_parts hk).trans hmu

private theorem morrisElementary_sub_msymm_mem_lowerSpan
    [Nontrivial R] {N q : ℕ}
    (lambda : {mu : N.Partition // mu.parts.card ≤ q}) :
    morrisElementary (R := R) q lambda.1 - msymm (Fin q) R lambda.1 ∈
      LinearMap.lowerSpan (R := R)
        (fun mu : {mu : N.Partition // mu.parts.card ≤ q} =>
          msymm (Fin q) R mu.1) lambda := by
  rw [morrisElementary,
    esymmPart_conjugate_eq_msymm_add_lower lambda.1 lambda.2]
  simp only [add_sub_cancel_left]
  apply Submodule.sum_mem
  intro mu hmu
  by_cases hlen : mu.parts.card ≤ q
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨⟨mu, hlen⟩, ?_, rfl⟩
    exact Nat.Partition.mem_erase_dominanceDownset.mp hmu
  · have hcard : Fintype.card (Fin q) < mu.parts.card := by
      simpa using Nat.lt_of_not_ge hlen
    simp [msymm_eq_zero_of_card_lt mu hcard]

private theorem msymm_sub_morrisElementary_mem_lowerSpan
    [Nontrivial R] {N q : ℕ}
    (lambda : {mu : N.Partition // mu.parts.card ≤ q}) :
    msymm (Fin q) R lambda.1 - morrisElementary (R := R) q lambda.1 ∈
      LinearMap.lowerSpan (R := R)
        (fun mu : {mu : N.Partition // mu.parts.card ≤ q} =>
          morrisElementary (R := R) q mu.1) lambda := by
  apply Submodule.span_mono _
    (msymm_sub_esymmPart_conjugate_mem_span_lower
      (K := R) lambda.1 lambda.2)
  rintro _ ⟨mu, hmu, rfl⟩
  change mu ∈ strictDominanceDownset q lambda.1 at hmu
  rw [mem_strictDominanceDownset] at hmu
  exact ⟨⟨mu, hmu.2⟩, hmu.1, rfl⟩

/-- The action of `B_q` on monomial symmetric polynomials is triangular in
dominance order, with the elementary-product eigenvalue on the diagonal. This
is the `B_q` part of Lemma 4.10 of Liu--Zhang,
arXiv:2609.15201v2. -/
theorem morrisB_isTriangularOn_msymm [Nontrivial R] {N q : ℕ} :
    (morrisB q).IsTriangularOn
      (fun mu : {mu : N.Partition // mu.parts.card ≤ q} =>
        msymm (Fin q) R mu.1)
      (fun mu => (morrisBWeight q mu.1.conjugate : R)) := by
  let b := fun mu : {mu : N.Partition // mu.parts.card ≤ q} =>
    morrisElementary (R := R) q mu.1
  have hb : (morrisB q).IsTriangularOn b
      (fun mu => (morrisBWeight q mu.1.conjugate : R)) := by
    intro mu
    rw [show b mu = morrisElementary (R := R) q mu.1 by rfl,
      morrisB_morrisElementary q mu.1 mu.2]
    change morrisBWeight q mu.1.conjugate • b mu -
      (morrisBWeight q mu.1.conjugate : R) • b mu ∈ _
    rw [← Nat.cast_smul_eq_nsmul R]
    simpa only [sub_self] using Submodule.zero_mem _
  exact hb.change_generators_of_unitriangular
    morrisElementary_sub_msymm_mem_lowerSpan msymm_sub_morrisElementary_mem_lowerSpan

private theorem partitionRow_eq_rowLen {N : ℕ}
    (mu : N.Partition) (i : ℕ) :
    partitionRow mu i = (YoungDiagram.ofPartition mu).rowLen i := by
  rw [partitionRow, ← YoungDiagram.rowLens_ofPartition_eq_sort_parts]
  by_cases hi : i < (YoungDiagram.ofPartition mu).rowLens.length
  · rw [List.getD_eq_getElem _ _ hi, YoungDiagram.get_rowLens]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    symm
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact hi (by
      rw [YoungDiagram.length_rowLens]
      exact YoungDiagram.mem_iff_lt_colLen.mp
        (YoungDiagram.mem_iff_lt_rowLen.mpr hpos))

private theorem cast_column_weight_eq_sum (q c : ℕ) (hc : c ≤ q) :
    ((c * (2 * q - c - 1) : ℕ) : ℤ) =
      ∑ i ∈ range c, 2 * ((q : ℤ) - (i : ℤ) - 1) := by
  induction c with
  | zero => simp
  | succ c ih =>
      have hc' : c ≤ q := (Nat.le_succ c).trans hc
      rw [sum_range_succ, ← ih hc']
      have hfirst : c + 1 ≤ 2 * q := by lia
      have hsecond : 1 ≤ 2 * q - (c + 1) := by lia
      have hfirst' : c ≤ 2 * q := by lia
      have hsecond' : 1 ≤ 2 * q - c := by lia
      push_cast [Nat.cast_sub hsecond, Nat.cast_sub hfirst,
        Nat.cast_sub hsecond', Nat.cast_sub hfirst']
      ring

private theorem cast_row_weight_eq_sum (c : ℕ) :
    ((c * (c - 1) : ℕ) : ℤ) =
      ∑ j ∈ range c, (2 : ℤ) * j := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [sum_range_succ, ← ih]
      cases c with
      | zero => simp
      | succ c =>
          push_cast [Nat.cast_sub (Nat.succ_le_succ (Nat.zero_le c))]
          ring

private theorem cast_morrisBWeight_conjugate_eq_sum_cells
    {N q : ℕ} (mu : N.Partition) (hmu : mu.parts.card ≤ q) :
    (morrisBWeight q mu.conjugate : ℤ) =
      ∑ c ∈ (YoungDiagram.ofPartition mu).cells,
        2 * ((q : ℤ) - (c.1 : ℤ) - 1) := by
  let Y := YoungDiagram.ofPartition mu
  have hheight : Y.colLen 0 ≤ q := by
    rw [← YoungDiagram.length_rowLens,
      YoungDiagram.rowLens_ofPartition_eq_sort_parts]
    simpa [Y] using hmu
  have hcols (j : ℕ) : Y.colLen j ≤ q :=
    (Y.colLen_anti 0 j (Nat.zero_le j)).trans hheight
  calc
    (morrisBWeight q mu.conjugate : ℤ) =
        ∑ j ∈ range (Y.rowLen 0),
          ((Y.colLen j * (2 * q - Y.colLen j - 1) : ℕ) : ℤ) := by
      norm_cast
      unfold morrisBWeight Nat.Partition.conjugate
        YoungDiagram.toPartition YoungDiagram.rowLens
      rw [Finset.sum_eq_multiset_sum, Finset.range_val,
        Multiset.range, Multiset.map_coe, Multiset.sum_coe]
      rw [Multiset.map_coe, Multiset.sum_coe]
      rw [YoungDiagram.colLen_transpose]
      have hf :
          (fun k => k * (2 * q - k - 1)) ∘
              (YoungDiagram.ofPartition mu).transpose.rowLen =
            fun j => Y.colLen j * (2 * q - Y.colLen j - 1) := by
        funext j
        rw [Function.comp_apply, YoungDiagram.rowLen_transpose]
      rw [List.map_map, hf]
    _ = ∑ j ∈ range (Y.rowLen 0),
          ∑ i ∈ range (Y.colLen j),
            2 * ((q : ℤ) - (i : ℤ) - 1) := by
      exact sum_congr rfl fun j _ => cast_column_weight_eq_sum q (Y.colLen j) (hcols j)
    _ = ∑ c ∈ Y.cells, 2 * ((q : ℤ) - (c.1 : ℤ) - 1) := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun c : ℕ × ℕ => c.2) (t := range (Y.rowLen 0))
        (fun c hc => by
          rw [mem_range, ← YoungDiagram.mem_iff_lt_rowLen]
          exact Y.up_left_mem (Nat.zero_le c.1) le_rfl hc)]
      refine sum_congr rfl fun j _ => ?_
      change (∑ i ∈ range (Y.colLen j),
          2 * ((q : ℤ) - (i : ℤ) - 1)) =
        ∑ c ∈ Y.col j, 2 * ((q : ℤ) - (c.1 : ℤ) - 1)
      rw [YoungDiagram.col_eq_prod]; simp

private theorem cast_morrisAWeight_eq_sum_cells
    {N : ℕ} (mu : N.Partition) :
    (morrisAWeight mu : ℤ) =
      ∑ c ∈ (YoungDiagram.ofPartition mu).cells, (2 : ℤ) * c.2 := by
  let Y := YoungDiagram.ofPartition mu
  have hparts : mu.parts = (Y.rowLens : Multiset ℕ) := by
    dsimp [Y]
    rw [YoungDiagram.rowLens_ofPartition_eq_sort_parts]
    exact (Multiset.sort_eq _ _).symm
  calc
    (morrisAWeight mu : ℤ) =
        ∑ i ∈ range (Y.colLen 0),
          ((Y.rowLen i * (Y.rowLen i - 1) : ℕ) : ℤ) := by
      norm_cast
      rw [morrisAWeight, hparts]
      unfold YoungDiagram.rowLens
      rw [Finset.sum_eq_multiset_sum, Finset.range_val,
        Multiset.range, Multiset.map_coe, Multiset.sum_coe]
      rw [Multiset.map_coe, Multiset.sum_coe, List.map_map]
      rfl
    _ = ∑ i ∈ range (Y.colLen 0),
          ∑ j ∈ range (Y.rowLen i), (2 : ℤ) * j := by
      exact sum_congr rfl fun i _ => cast_row_weight_eq_sum (Y.rowLen i)
    _ = ∑ c ∈ Y.cells, (2 : ℤ) * c.2 := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun c : ℕ × ℕ => c.1) (t := range (Y.colLen 0))
        (fun c hc => by
          rw [mem_range, ← YoungDiagram.mem_iff_lt_colLen]
          exact Y.up_left_mem le_rfl (Nat.zero_le c.2) hc)]
      refine sum_congr rfl fun i _ => ?_
      change (∑ j ∈ range (Y.rowLen i), (2 : ℤ) * j) =
        ∑ c ∈ Y.row i, (2 : ℤ) * c.2
      rw [YoungDiagram.row_eq_prod]; simp

private theorem morrisEigenvalue_eq_sum_cells
    {N q : ℕ} (mu : N.Partition) (hmu : mu.parts.card ≤ q) :
    morrisEigenvalue q mu =
      ∑ c ∈ (YoungDiagram.ofPartition mu).cells,
        2 * ((q : ℤ) - (c.1 : ℤ) - (c.2 : ℤ) - 1) := by
  let Y := YoungDiagram.ofPartition mu
  have hheight : Y.colLen 0 ≤ q := by
    rw [← YoungDiagram.length_rowLens,
      YoungDiagram.rowLens_ofPartition_eq_sort_parts]
    simpa [Y] using hmu
  calc
    morrisEigenvalue q mu =
        ∑ i ∈ range q, ∑ j ∈ range (Y.rowLen i),
          2 * ((q : ℤ) - (i : ℤ) - (j : ℤ) - 1) := by
      rw [morrisEigenvalue, Finset.mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [partitionRow_eq_rowLen, Finset.mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ = ∑ c ∈ Y.cells,
          2 * ((q : ℤ) - (c.1 : ℤ) - (c.2 : ℤ) - 1) := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun c : ℕ × ℕ => c.1) (t := range q)
        (fun c hc => by
          rw [mem_range]
          have hcell : (c.1, 0) ∈ Y :=
            Y.up_left_mem le_rfl (Nat.zero_le c.2) hc
          exact (YoungDiagram.mem_iff_lt_colLen.mp hcell).trans_le hheight)]
      refine sum_congr rfl fun i _ => ?_
      change (∑ j ∈ range (Y.rowLen i),
          2 * ((q : ℤ) - (i : ℤ) - (j : ℤ) - 1)) =
        ∑ c ∈ Y.row i,
          2 * ((q : ℤ) - (c.1 : ℤ) - (c.2 : ℤ) - 1)
      rw [YoungDiagram.row_eq_prod]; simp

private def morrisTwiceIndexSum (q : ℕ) {N : ℕ}
    (mu : N.Partition) : ℤ :=
  ∑ i ∈ range q, (∑ j ∈ range (partitionRow mu i),
    (2 * (i : ℤ) + 2 * (j : ℤ)))

private theorem sum_partitionRow_eq_size {N q : ℕ}
    (mu : N.Partition) (hmu : mu.parts.card ≤ q) :
    ∑ i ∈ range q, partitionRow mu i = N := by
  have hp : mu.prefixSum q = N := by
    rw [Nat.Partition.prefixSum_eq_sum_take_sort_parts,
      List.take_of_length_le (by simpa using hmu)]
    rw [← Multiset.sum_coe, Multiset.sort_eq, mu.parts_sum]
  simpa only [Nat.Partition.prefixSum, partitionRow_eq_rowLen,
    Nat.Partition.part] using hp

private theorem sum_twice_indices (i n : ℕ) :
    (∑ j ∈ range n, (2 * (i : ℤ) + 2 * (j : ℤ))) =
      (n : ℤ) * (2 * (i : ℤ) + (n : ℤ) - 1) := by
  induction n with
  | zero => simp only [range_zero, sum_empty, Nat.cast_zero, zero_mul]
  | succ n ih =>
      rw [sum_range_succ, ih]; push_cast; ring

private theorem morrisEigenvalue_eq_constant_sub_twiceIndexSum
    {N q : ℕ} (mu : N.Partition) (hmu : mu.parts.card ≤ q) :
    morrisEigenvalue q mu =
      (N : ℤ) * (2 * ((q : ℤ) - 1)) -
        morrisTwiceIndexSum q mu := by
  have hrow (i n : ℕ) :
      2 * ∑ j ∈ range n,
          ((q : ℤ) + 1 - (i : ℤ) - 1 - (j : ℤ) - 1) =
        (n : ℤ) * (2 * ((q : ℤ) - 1)) -
          ∑ j ∈ range n, (2 * (i : ℤ) + 2 * (j : ℤ)) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [sum_range_succ, sum_range_succ, mul_add, ih]
        push_cast
        ring
  rw [morrisEigenvalue, Finset.mul_sum, morrisTwiceIndexSum]
  conv_lhs =>
    enter [2, i]
    rw [hrow i]
  rw [sum_sub_distrib, ← sum_mul]
  norm_cast
  rw [sum_partitionRow_eq_size mu hmu]

private theorem row_twiceIndexSum_gap_lower (i l m : ℕ) :
    (m : ℤ) * (2 * (i : ℤ) + (m : ℤ) - 1) -
        (l : ℤ) * (2 * (i : ℤ) + (l : ℤ) - 1) ≥
      2 * (((m : ℤ) - (l : ℤ)) * ((i : ℤ) + (l : ℤ)) +
        ((l - m : ℕ) : ℤ)) := by
  rcases lt_trichotomy l m with hlt | rfl | hgt
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
    have hc : (l : ℤ) < (m : ℤ) := by exact_mod_cast hlt
    have hp := mul_nonneg (show 0 ≤ (m : ℤ) - l by lia)
      (show 0 ≤ (m : ℤ) - l - 1 by lia)
    ring_nf at hp ⊢
    nlinarith
  · simp
  · rw [Nat.cast_sub (Nat.le_of_lt hgt)]
    have hc : (m : ℤ) < (l : ℤ) := by exact_mod_cast hgt
    have hp := mul_nonneg (show 0 ≤ (l : ℤ) - m by lia)
      (show 0 ≤ (l : ℤ) - m - 1 by lia)
    ring_nf at hp ⊢
    nlinarith

private theorem sum_mul_nonpos_of_prefix_nonneg_of_monotone
    (q : ℕ) (d b : ℕ → ℤ)
    (hprefix : ∀ k, k ≤ q → 0 ≤ ∑ i ∈ range k, d i)
    (htotal : ∑ i ∈ range q, d i = 0)
    (hmono : ∀ i, i + 1 < q → b i ≤ b (i + 1)) :
    ∑ i ∈ range q, d i * b i ≤ 0 := by
  have hparts := Finset.sum_range_by_parts' d b q
  simp only [smul_eq_mul] at hparts
  rw [hparts, htotal, zero_mul, zero_sub]
  refine neg_nonpos.mpr (sum_nonneg fun i hi => ?_)
  have hi := mem_range.mp hi
  exact mul_nonneg (hprefix (i + 1) (by lia))
    (sub_nonneg.mpr (hmono i (by lia)))

private theorem partitionPart_eq_zero_of_card_le {N q : ℕ}
    (mu : N.Partition) (hmu : mu.parts.card ≤ q)
    {i : ℕ} (hi : q ≤ i) : mu.part i = 0 := by
  change (YoungDiagram.ofPartition mu).rowLen i = 0
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have hiheight : i < (YoungDiagram.ofPartition mu).colLen 0 :=
    YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hpos)
  have hheight : (YoungDiagram.ofPartition mu).colLen 0 ≤ q := by
    simpa [← YoungDiagram.length_rowLens,
      YoungDiagram.rowLens_ofPartition_eq_sort_parts] using hmu
  lia

private theorem removedRows_pos_of_lt {N q : ℕ}
    {mu lambda : N.Partition} (hlambda : lambda.parts.card ≤ q)
    (hdom : mu < lambda) :
    0 < ∑ i ∈ range q, (lambda.part i - mu.part i) := by
  have hstrict : ∃ k, mu.prefixSum k < lambda.prefixSum k := by
    by_contra h
    exact hdom.2 fun k => Nat.le_of_not_gt fun hk => h ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hstrict
  have hrow : ∃ i ∈ range k, mu.part i < lambda.part i := by
    by_contra h
    exact (Nat.not_le_of_lt hk) <| sum_le_sum fun i hi =>
      Nat.le_of_not_gt fun hil => h ⟨i, hi, hil⟩
  obtain ⟨i, _, hi⟩ := hrow
  have hiq : i < q := by
    by_contra hiq
    rw [partitionPart_eq_zero_of_card_le lambda hlambda
      (Nat.le_of_not_gt hiq)] at hi
    exact Nat.not_lt_zero _ hi
  exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
    ⟨i, mem_range.mpr hiq, Nat.sub_pos_of_lt hi⟩

/-- Lemma 4.11 of Liu--Zhang, arXiv:2609.15201v2. If the adjacent
parts of `lambda` drop by at most one, then its Morris eigenvalue is
strictly larger than that of every strictly dominated partition. -/
theorem morrisEigenvalue_lt_of_lt_of_adjacent_drop {N q : ℕ}
    {mu lambda : N.Partition} (hmu : mu.parts.card ≤ q)
    (hlambda : lambda.parts.card ≤ q)
    (hadj : ∀ i, i + 1 < q →
      lambda.part i - lambda.part (i + 1) ≤ 1)
    (hdom : mu < lambda) :
    morrisEigenvalue q mu < morrisEigenvalue q lambda := by
  let d : ℕ → ℤ := fun i => (lambda.part i : ℤ) - (mu.part i : ℤ)
  let b : ℕ → ℤ := fun i => (i : ℤ) + (lambda.part i : ℤ)
  let removed : ℤ :=
    ∑ i ∈ range q, (((lambda.part i - mu.part i : ℕ) : ℤ))
  have hprefix : ∀ k, k ≤ q → 0 ≤ ∑ i ∈ range k, d i := by
    intro k _
    simp only [d, sum_sub_distrib]
    rw [sub_nonneg]
    exact_mod_cast hdom.le k
  have htotal : ∑ i ∈ range q, d i = 0 := by
    simp only [d, sum_sub_distrib]
    have hls := sum_partitionRow_eq_size lambda hlambda
    have hms := sum_partitionRow_eq_size mu hmu
    simp only [partitionRow_eq_rowLen] at hls hms
    rw [sub_eq_zero]
    exact_mod_cast hls.trans hms.symm
  have hmono : ∀ i, i + 1 < q → b i ≤ b (i + 1) := by
    intro i hi
    simp only [b]
    have ha : (lambda.part i : ℤ) ≤ (lambda.part (i + 1) : ℤ) + 1 := by
      exact_mod_cast (by simpa [add_comm] using Nat.sub_le_iff_le_add.mp (hadj i hi))
    push_cast
    lia
  have hweighted : ∑ i ∈ range q, d i * b i ≤ 0 :=
    sum_mul_nonpos_of_prefix_nonneg_of_monotone q d b hprefix htotal hmono
  have hrow (i : ℕ) :
      -2 * d i * b i + 2 * ((lambda.part i - mu.part i : ℕ) : ℤ) ≤
        (mu.part i : ℤ) *
            (2 * (i : ℤ) + (mu.part i : ℤ) - 1) -
          (lambda.part i : ℤ) *
            (2 * (i : ℤ) + (lambda.part i : ℤ) - 1) := by
    dsimp only [d, b]
    nlinarith [row_twiceIndexSum_gap_lower i (lambda.part i) (mu.part i)]
  have hrows := sum_le_sum fun i (_ : i ∈ range q) => hrow i
  have hindex :
      morrisTwiceIndexSum q mu - morrisTwiceIndexSum q lambda =
        ∑ i ∈ range q,
          ((mu.part i : ℤ) *
              (2 * (i : ℤ) + (mu.part i : ℤ) - 1) -
            (lambda.part i : ℤ) *
              (2 * (i : ℤ) + (lambda.part i : ℤ) - 1)) := by
    rw [morrisTwiceIndexSum, morrisTwiceIndexSum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [sum_twice_indices, sum_twice_indices]
    rw [partitionRow_eq_rowLen, partitionRow_eq_rowLen]
    change (mu.part i : ℤ) *
        (2 * (i : ℤ) + (mu.part i : ℤ) - 1) -
      (lambda.part i : ℤ) *
        (2 * (i : ℤ) + (lambda.part i : ℤ) - 1) = _
    rfl
  have hweighted' :
      0 ≤ ∑ i ∈ range q, (-2 * d i * b i) := by
    calc
      (0 : ℤ) ≤ -2 * ∑ i ∈ range q, (d i * b i) :=
        mul_nonneg_of_nonpos_of_nonpos (by norm_num) hweighted
      _ = _ := by
        rw [Finset.mul_sum]
        exact sum_congr rfl fun _ _ => by ring
  have hlower : (2 : ℤ) * removed ≤
      morrisTwiceIndexSum q mu - morrisTwiceIndexSum q lambda := by
    rw [hindex]
    calc
      (2 : ℤ) * removed ≤
          ∑ i ∈ range q,
            (-2 * d i * b i +
              2 * ((lambda.part i - mu.part i : ℕ) : ℤ)) := by
        simp only [removed, sum_add_distrib, ← Finset.mul_sum]
        nlinarith [hweighted']
      _ ≤ _ := hrows
  have hremoved : 0 < removed := by
    dsimp only [removed]
    exact_mod_cast removedRows_pos_of_lt hlambda hdom
  rw [morrisEigenvalue_eq_constant_sub_twiceIndexSum lambda hlambda,
    morrisEigenvalue_eq_constant_sub_twiceIndexSum mu hmu]
  nlinarith

/-- The column eigenvalue of `B_q` minus the monomial eigenvalue of `A_q`
is the signed Ferrers-diagram weight from Lemma 4.10 of Liu--Zhang,
arXiv:2609.15201v2. -/
theorem morrisBWeight_conjugate_sub_morrisAWeight {N q : ℕ}
    (mu : N.Partition) (hmu : mu.parts.card ≤ q) :
    (morrisBWeight q mu.conjugate : ℤ) - (morrisAWeight mu : ℤ) =
      morrisEigenvalue q mu := by
  rw [cast_morrisBWeight_conjugate_eq_sum_cells mu hmu,
    cast_morrisAWeight_eq_sum_cells mu,
    morrisEigenvalue_eq_sum_cells mu hmu,
    ← Finset.sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring

/-- The operator `D_q = B_q - A_q` from
Liu--Zhang, arXiv:2609.15201v2, equation (4.9). -/
def morrisD (q : ℕ) :
    MvPolynomial (Fin q) R →ₗ[R] MvPolynomial (Fin q) R :=
  morrisB q - morrisA q

@[simp]
theorem morrisD_apply (q : ℕ) (P : MvPolynomial (Fin q) R) :
    morrisD q P = morrisB q P - morrisA q P :=
  rfl

/-- On a monomial-symmetric polynomial, the `A_q` contribution to `D_q` is
the diagonal term with coefficient `morrisAWeight`. -/
theorem morrisD_msymm {n q : ℕ} (mu : n.Partition) :
    morrisD q (msymm (Fin q) R mu) =
      morrisB q (msymm (Fin q) R mu) -
        morrisAWeight mu • msymm (Fin q) R mu := by
  rw [morrisD_apply, morrisA_msymm]

/-- Lemma 4.10 of Liu--Zhang, arXiv:2609.15201v2: the Morris operator
`D_q` is triangular on monomial symmetric polynomials in dominance order,
with diagonal given by the signed Ferrers-diagram weight. -/
theorem morrisD_isTriangularOn_msymm [Nontrivial R] {N q : ℕ} :
    (morrisD q).IsTriangularOn
      (fun mu : {mu : N.Partition // mu.parts.card ≤ q} =>
        msymm (Fin q) R mu.1)
      (fun mu => (morrisEigenvalue q mu.1 : R)) := by
  intro mu
  change morrisD q (msymm (Fin q) R mu.1) -
      (morrisEigenvalue q mu.1 : R) • msymm (Fin q) R mu.1 ∈ _
  have hb := morrisB_isTriangularOn_msymm
    (R := R) (N := N) (q := q) mu
  have hz := morrisBWeight_conjugate_sub_morrisAWeight mu.1 mu.2
  have hweight : (morrisEigenvalue q mu.1 : R) =
      (morrisBWeight q mu.1.conjugate : R) -
        (morrisAWeight mu.1 : R) := by
    have hr := congrArg (fun z : ℤ => (z : R)) hz
    simpa only [Int.cast_sub, Int.cast_natCast] using hr.symm
  rw [morrisD_apply, morrisA_msymm,
    ← Nat.cast_smul_eq_nsmul R, hweight, sub_smul]
  convert hb using 1; abel

/-- The Morris operator `D_q` maps symmetric polynomials to symmetric
polynomials. -/
theorem IsSymmetric.morrisD {q : ℕ} {P : MvPolynomial (Fin q) R}
    (hP : P.IsSymmetric) : (morrisD q P).IsSymmetric := by
  simpa only [morrisD_apply] using
    (IsSymmetric.morrisB hP).sub (IsSymmetric.morrisA hP)

/-- The restriction of `D_q = B_q - A_q` to the symmetric polynomial ring,
as in Liu--Zhang, arXiv:2609.15201v2, equation (4.9). -/
def morrisDOnSymmetric (q : ℕ) :
    symmetricSubalgebra (Fin q) R →ₗ[R]
      symmetricSubalgebra (Fin q) R :=
  ((morrisD q).domRestrict (symmetricSubalgebra (Fin q) R).toSubmodule).codRestrict
    (symmetricSubalgebra (Fin q) R).toSubmodule fun P =>
      IsSymmetric.morrisD P.2

@[simp]
theorem morrisDOnSymmetric_apply (q : ℕ)
    (P : symmetricSubalgebra (Fin q) R) :
    (morrisDOnSymmetric q P : MvPolynomial (Fin q) R) = morrisD q P :=
  rfl

end
end RealRooted.LiuZhang
