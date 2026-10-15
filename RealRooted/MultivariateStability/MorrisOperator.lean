import RealRooted.Mathlib.RingTheory.MvPolynomial.DividedDifference
import RealRooted.Mathlib.RingTheory.MvPolynomial.EulerIdentity
import RealRooted.Mathlib.RingTheory.MvPolynomial.Symmetric.Homogeneous
import RealRooted.Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import RealRooted.Multiaffine
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.LinearCombination

/-!
# The Morris differential operator on symmetric polynomials

For `q` variables, Liu--Zhang, arXiv:2609.15201v2, Section 1.2, define

`A_q = ∑ i, x_i ^ 2 * ∂_i ^ 2`,

`B_q = 2 * ∑ i < j, (x_i ^ 2 * ∂_i - x_j ^ 2 * ∂_j) / (x_i - x_j)`,

and `D_q = B_q - A_q`.  This file realizes those formulas as linear maps.
-/

namespace RealRooted.LiuZhang

open MvPolynomial

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
    funext k
    change e (Equiv.swap i j k) = Equiv.swap (e i) (e j) (e k)
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
  simp only [morrisA, LinearMap.sum_apply, LinearMap.comp_apply,
    squaredPDeriv_apply]
  rfl

/-- Bijective renaming transports a coordinate second-derivative summand to
the corresponding renamed coordinate. -/
theorem rename_squaredPDeriv_pderiv {σ τ : Type*}
    (e : σ ≃ τ) (i : σ) (P : MvPolynomial σ R) :
    rename e (squaredPDeriv i (pderiv i P)) =
      squaredPDeriv (e i) (pderiv (e i) (rename e P)) := by
  rw [squaredPDeriv_apply, squaredPDeriv_apply, map_mul, map_pow, rename_X]
  rw [← pderiv_rename (R := R) e.injective i (pderiv i P),
    ← pderiv_rename (R := R) e.injective i P]

/-- Bijective renaming transports a coordinate first-derivative summand to
the corresponding renamed coordinate. -/
theorem rename_squaredPDeriv {σ τ : Type*}
    (e : σ ≃ τ) (i : σ) (P : MvPolynomial σ R) :
    rename e (squaredPDeriv i P) = squaredPDeriv (e i) (rename e P) := by
  rw [squaredPDeriv_apply, squaredPDeriv_apply, map_mul, map_pow, rename_X]
  rw [← pderiv_rename (R := R) e.injective i P]

/-- The operator `A_q` maps symmetric polynomials to symmetric polynomials. -/
theorem IsSymmetric.morrisA {q : ℕ} {P : MvPolynomial (Fin q) R}
    (hP : P.IsSymmetric) : (morrisA q P).IsSymmetric := by
  intro e
  rw [morrisA_apply, map_sum]
  simp_rw [← squaredPDeriv_apply]
  rw [show (∑ i, rename e (squaredPDeriv i (pderiv i P))) =
      ∑ i, squaredPDeriv (e i) (pderiv (e i) (rename e P)) by
    apply Finset.sum_congr rfl
    intro i _
    exact rename_squaredPDeriv_pderiv e i P]
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
    rw [pderiv_mul, pderiv_X_self]
    ring
  rw [hid, heuler, hrhs] at heuler2
  have hresult : X i ^ 2 * pderiv i (pderiv i (monomial d r)) =
      d i • (d i • monomial d r) - d i • monomial d r := by
    calc
      X i ^ 2 * pderiv i (pderiv i (monomial d r)) =
          (d i • monomial d r +
            X i ^ 2 * pderiv i (pderiv i (monomial d r))) -
            d i • monomial d r := by
        ring
      _ = d i • (d i • monomial d r) - d i • monomial d r := by
        rw [heuler2]
  rw [hresult]
  cases hdi : d i with
  | zero => simp
  | succ n =>
      simp only [Nat.succ_sub_one, nsmul_eq_mul]
      push_cast
      ring

/-- The operator `A_q` acts diagonally on a monomial, with eigenvalue the sum
of `d_i * (d_i - 1)` over its exponents. -/
theorem morrisA_monomial {q : ℕ} (d : Fin q →₀ ℕ) (r : R) :
    morrisA q (monomial d r) =
      (∑ i, d i * (d i - 1)) • monomial d r := by
  rw [morrisA_apply]
  simp_rw [squaredPDeriv_pderiv_monomial]
  change Finset.univ.sum (fun i =>
      (d i * (d i - 1)) • monomial d r) =
    Finset.univ.sum (fun i => d i * (d i - 1)) • monomial d r
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
        rw [← Multiset.toFinsupp_singleton, ← Multiset.toFinsupp_add]
        rfl]
      rw [X, monomial_mul_monomial]
      simp only [one_mul]

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
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hnotmem : i ∉ s.1 := by simpa using hi
  have hcount : s.1.count i = 0 := Multiset.count_eq_zero.mpr hnotmem
  rw [hcount, zero_mul]

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
    rename_swapDividedDifference_fin]
  rw [squaredPDerivDividedDifference, LinearMap.comp_apply,
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
  symm
  calc
    (X i - X j) * squaredPDerivDividedDifference j i hij.symm P =
        -((X j - X i) * squaredPDerivDividedDifference j i hij.symm P) := by
      ring
    _ = -(X j ^ 2 * pderiv j P - X i ^ 2 * pderiv i P) := by
      rw [hreverse]
    _ = X i ^ 2 * pderiv i P - X j ^ 2 * pderiv j P := by
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
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

@[simp]
theorem morrisBOrdered_apply (q : ℕ) (P : MvPolynomial (Fin q) R) :
    morrisBOrdered q P = ∑ i, ∑ j, if hij : i ≠ j then
      squaredPDerivDividedDifference i j hij P else 0 := by
  simp only [morrisBOrdered, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
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
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
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
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij
    · exact (squaredPDerivDividedDifference_comm_of_isSymmetric
        hP i j hij.ne).symm
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
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
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
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [f]
    by_cases hij : i ≠ j
    · rw [dite_eq_left hij, dite_eq_left (e.injective.ne hij)]
    · have heq : i = j := not_ne_iff.mp hij
      subst j
      rw [dite_eq_right (not_ne_iff.mpr rfl),
        dite_eq_right (not_ne_iff.mpr rfl)]
  rw [htoF]
  calc
    (∑ i, ∑ j, f (e i) (e j)) = ∑ i, ∑ j, f i (e j) :=
      Equiv.sum_comp e fun i => ∑ j, f i (e j)
    _ = ∑ i, ∑ j, f i j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp e (f i)
    _ = ∑ i, ∑ j, if hij : i ≠ j then
        squaredPDerivDividedDifference i j hij P else 0 := by
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
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
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
  have hd := pderiv_sub_pderiv_of_isSymmetric_of_isMultiaffine hP hma i j
  linear_combination -X i * X j * hd

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
    simp_rw [sum_dite_ne_eq_pred_nsmul]
    exact Finset.smul_sum.symm
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
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i ≠ j
        · rw [dite_eq_left hij, pderiv_comm]
          ring
        · have hji : j = i := (not_ne_iff.mp hij).symm
          subst j
          rw [dite_eq_right (not_ne_iff.mpr rfl),
            hma.pderiv_pderiv_self_eq_zero]
          simp
      _ = ∑ i, X i * ((n - 1) • pderiv i P) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(hhom.pderiv (i := i)).sum_X_mul_pderiv]
      _ = (n - 1) • ∑ i, X i * pderiv i P := by
        simp only [Finset.smul_sum, nsmul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
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
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
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
      have hsq : ∀ l ∈ s, l ≤ q := by
        intro l hl
        exact hs l (by simp [hl])
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
      morrisBWeight q mu • esymmPart (Fin q) R mu := by
  simpa only [esymmPart, morrisBWeight] using
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
      morrisBWeight q mu.conjugate • morrisElementary (R := R) q mu := by
  apply morrisB_esymmPart q mu.conjugate
  intro k hk
  exact (mu.le_card_parts_of_mem_conjugate_parts hk).trans hmu

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

/-- The Morris operator `D_q` maps symmetric polynomials to symmetric
polynomials. -/
theorem IsSymmetric.morrisD {q : ℕ} {P : MvPolynomial (Fin q) R}
    (hP : P.IsSymmetric) : (morrisD q P).IsSymmetric := by
  rw [morrisD_apply]
  exact (IsSymmetric.morrisB hP).sub (IsSymmetric.morrisA hP)

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
