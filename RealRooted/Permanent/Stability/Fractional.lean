module

public import RealRooted.Permanent.Ferrers

/-!
# Fractional substitution for the column permanent

This file isolates the simultaneous substitution from Section 3 of
Brändén--Haglund--Visontai--Wagner, arXiv:1010.2565v2.
-/

public section

open scoped BigOperators

namespace RealRooted

noncomputable section

/-- Evaluation of a complexified real multivariate polynomial commutes with
complex conjugation. -/
theorem eval_complexifyMv_conj {sigma : Type*}
    (P : MvPolynomial sigma Real) (z : sigma → Complex) :
    MvPolynomial.eval z (complexifyMv P) =
      starRingEnd Complex
        (MvPolynomial.eval (fun i => starRingEnd Complex (z i))
          (complexifyMv P)) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [complexifyMv]
  | add P Q hP hQ =>
      unfold complexifyMv at hP hQ ⊢
      rw [map_add, MvPolynomial.eval_add, MvPolynomial.eval_add,
        map_add, hP, hQ]
  | mul_X P i hP =>
      unfold complexifyMv at hP ⊢
      rw [map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul,
        map_mul, hP]
      simp

/-- A real stable polynomial is nonzero when every coordinate lies in the
open lower half-plane. -/
theorem MvRealStable.eval_ne_zero_of_im_neg
    {sigma : Type*} {P : MvPolynomial sigma Real}
    (hP : MvRealStable P) (z : sigma → Complex)
    (hz : ∀ i, (z i).im < 0) :
    MvPolynomial.eval z (complexifyMv P) ≠ 0 := by
  let w : sigma → Complex := fun i => starRingEnd Complex (z i)
  have hw : ∀ i, 0 < (w i).im := by
    intro i
    simpa [w] using hz i
  have hne := hP w hw
  intro hzero
  apply hne
  have heval := eval_complexifyMv_conj P z
  have hwEq : (fun i => starRingEnd Complex (z i)) = w := rfl
  rw [hwEq] at heval
  rw [heval] at hzero
  simpa using hzero

namespace Permanent

/-- Evaluating every variable of the one-alphabet Ferrers polynomial at one
gives the number of permutations. -/
theorem eval_one_ferrersColumnPolynomial {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) :
    MvPolynomial.eval (fun _ => 1) (ferrersColumnPolynomial A) =
      n.factorial := by
  classical
  unfold ferrersColumnPolynomial Matrix.permanent
  simp only [map_sum, map_prod]
  calc
    ∑ pi : Equiv.Perm (Fin n),
        ∏ i, MvPolynomial.eval (fun _ => 1)
          (MvPolynomial.C (A (pi i) i) * MvPolynomial.X i +
            MvPolynomial.C (1 - A (pi i) i)) =
        ∑ _pi : Equiv.Perm (Fin n), (1 : Real) := by
      apply Finset.sum_congr rfl
      intro pi hpi
      simp
    _ = n.factorial := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin]
      simp

/-- The one-alphabet Ferrers polynomial is nonzero. -/
theorem ferrersColumnPolynomial_ne_zero {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) :
    ferrersColumnPolynomial A ≠ 0 := by
  intro hzero
  have heval := congrArg (MvPolynomial.eval (fun _ => (1 : Real))) hzero
  rw [eval_one_ferrersColumnPolynomial] at heval
  have hpositive : (0 : Real) < n.factorial := by positivity
  exact hpositive.ne' heval

/-- Pointwise fractional-substitution identity relating the one-alphabet
Ferrers polynomial and the multivariate column permanent. -/
theorem eval_columnPermanent_eq_prod_mul_eval_ferrersColumnPolynomial
    {n : Nat} (A : Matrix (Fin n) (Fin n) Real)
    (z : Fin n → Complex) (hz : ∀ j, z j ≠ 0) :
    MvPolynomial.eval z (complexifyMv (columnPermanent A)) =
      (∏ j, z j) *
        MvPolynomial.eval (fun j => 1 + (z j)⁻¹)
          (complexifyMv (ferrersColumnPolynomial A)) := by
  classical
  unfold columnPermanent ferrersColumnPolynomial Matrix.permanent
    complexifyMv
  simp only [map_sum, map_prod, map_add, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pi hpi
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hzj := hz j
  rw [map_sub, map_one]
  field_simp
  ring

/-- Stability of the specialized one-alphabet Ferrers polynomial implies
stability of `per(z_j+a_ij)` by simultaneous fractional substitution. -/
theorem columnPermanent_mvRealStable_of_ferrersColumnPolynomial_stable
    {n : Nat} (A : Matrix (Fin n) (Fin n) Real)
    (hP : MvRealStable (ferrersColumnPolynomial A)) :
    MvRealStable (columnPermanent A) := by
  intro z hz
  have hz0 : ∀ j, z j ≠ 0 := by
    intro j hzero
    have hpos := hz j
    rw [hzero] at hpos
    simp at hpos
  rw [eval_columnPermanent_eq_prod_mul_eval_ferrersColumnPolynomial A z hz0]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun j hj => hz0 j
  · apply hP.eval_ne_zero_of_im_neg
    intro j
    simp only [Complex.add_im, Complex.one_im, zero_add, Complex.inv_im]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (hz j))
      (Complex.normSq_pos.mpr (hz0 j))

end Permanent

end

end RealRooted
