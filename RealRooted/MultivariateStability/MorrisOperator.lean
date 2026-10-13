import RealRooted.Mathlib.RingTheory.MvPolynomial.DividedDifference
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

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
Liu--Zhang, arXiv:2609.15201v2, Section 1.2. -/
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

/-- The operator
`B_q = 2 * ∑ i < j, (x_i ^ 2 * ∂_i - x_j ^ 2 * ∂_j) / (x_i - x_j)`
from Liu--Zhang, arXiv:2609.15201v2, Section 1.2. -/
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

/-- The operator `D_q = B_q - A_q` from
Liu--Zhang, arXiv:2609.15201v2, Section 1.2. -/
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

end


end RealRooted.LiuZhang
