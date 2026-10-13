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

/-- The Morris operator `D_q` maps symmetric polynomials to symmetric
polynomials. -/
theorem IsSymmetric.morrisD {q : ℕ} {P : MvPolynomial (Fin q) R}
    (hP : P.IsSymmetric) : (morrisD q P).IsSymmetric := by
  rw [morrisD_apply]
  exact (IsSymmetric.morrisB hP).sub (IsSymmetric.morrisA hP)

end


end RealRooted.LiuZhang
