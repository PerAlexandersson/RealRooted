import RealRooted.CombinatorialExamples.MultisetEulerianNarayana
import Mathlib.Basic.Real.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Bidiagonal
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul

/-!
# Finite bidiagonal factors for multiset Eulerian--Narayana transitions

Zhang--Zhao, Theorem 1.3, writes the coefficient transition matrix for a block
of `r` maximal labels as a product of the coefficient matrices of the operators
`E_{d,a}`.  This file records the finite padded factors and proves their total
nonnegativity.  The final identification with the paper's closed binomial
formula is kept separate: it is the coefficient calculation in their Lemma
4.3 and Proposition 4.1.
-/

open Polynomial

namespace RealRooted
namespace MultisetEulerianNarayana

noncomputable section

private def factorDiagonal (d : ℕ) (a : ℝ) (i : ℕ) : ℝ :=
  if i ≤ d then ((i : ℝ) + a) / a else 1

private def factorSubdiagonal (d : ℕ) (a : ℝ) (j : ℕ) : ℝ :=
  if j ≤ d then ((d : ℝ) + a - j) / a else 0

/-- The square padded coefficient matrix of `E_{d,a}`.

The identity continuation above degree `d + 1` makes all factors square, so
that the product theorem for totally nonnegative matrices applies directly.
-/
def coefficientFactor (N d : ℕ) (a : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.lowerBidiagonalFin N (factorDiagonal d a) (factorSubdiagonal d a)

/-- The first `N` coefficients of a polynomial, indexed by `Fin N`. -/
def coefficientVector (N : ℕ) (f : ℝ[X]) : Fin N → ℝ :=
  fun i => f.coeff i

private theorem lowerBidiagonalFin_mulVec {N : ℕ} (d s : ℕ → ℝ) (v : Fin N → ℝ)
    (i : Fin N) :
    (Matrix.lowerBidiagonalFin N d s).mulVec v i =
      d i * v i + if i.val = 0 then 0 else
        s (i.val - 1) * v ⟨i.val - 1, by lia⟩ := by
  classical
  cases N with
  | zero => exact Fin.elim0 i
  | succ N =>
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · simp [Matrix.mulVec, dotProduct, Matrix.lowerBidiagonalFin_apply]
      · simp only [Matrix.mulVec, dotProduct, Matrix.lowerBidiagonalFin_apply]
        have hsplit (x : Fin (N + 1)) :
            (if i.succ = x then d (i.val + 1)
              else if i.succ.val = x.val + 1 then s x.val else 0) * v x =
              (if i.succ = x then d (i.val + 1) * v x else 0) +
                (if i.succ.val = x.val + 1 then s x.val * v x else 0) := by
          by_cases h₁ : i.succ = x
          · simp [h₁]
          · simp [h₁]
        have hsum :
            (∑ x : Fin (N + 1),
                (if i.succ = x then d (i.val + 1)
                  else if i.succ.val = x.val + 1 then s x.val else 0) * v x) =
              ∑ x : Fin (N + 1),
                ((if i.succ = x then d (i.val + 1) * v x else 0) +
                  (if i.succ.val = x.val + 1 then s x.val * v x else 0)) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hsplit x
        change (∑ x : Fin (N + 1),
            (if i.succ = x then d (i.val + 1)
              else if i.succ.val = x.val + 1 then s x.val else 0) * v x) = _
        rw [hsum]
        rw [Finset.sum_add_distrib]
        have hfirst :
            (∑ x : Fin (N + 1),
                if i.succ = x then d (i.val + 1) * v x else 0) =
              d (i.val + 1) * v i.succ := by
          rw [Finset.sum_eq_single i.succ]
          · simp
          · intro b hb hbi
            simp only [ite_eq_right (Ne.symm hbi)]
          · simp
        have hsecond :
            (∑ x : Fin (N + 1),
                if i.succ.val = x.val + 1 then s x.val * v x else 0) =
              s i.val * v i.castSucc := by
          rw [Finset.sum_eq_single i.castSucc]
          · simp
          · intro b hb hbi
            have hne : i.val ≠ b.val := by
              intro h
              apply hbi
              apply Fin.ext
              simpa using h.symm
            have hne' : ¬i.succ.val = b.val + 1 := by
              intro h
              have h' : i.val + 1 = b.val + 1 := by simpa using h
              apply hne
              lia
            simp only [ite_eq_right hne']
          · simp
        rw [hfirst, hsecond]
        have hfin : v i.castSucc = v ⟨i.val, by lia⟩ := by
          congr 1
        simp [Fin.val_succ, hfin]

private theorem factorDiagonal_nonneg {d : ℕ} {a : ℝ} (ha : 0 < a) (i : ℕ) :
    0 ≤ factorDiagonal d a i := by
  rw [factorDiagonal]
  split_ifs with hi
  · exact div_nonneg (by positivity) ha.le
  · norm_num

private theorem factorSubdiagonal_nonneg {d : ℕ} {a : ℝ} (ha : 0 < a) (j : ℕ) :
    0 ≤ factorSubdiagonal d a j := by
  rw [factorSubdiagonal]
  split_ifs with hj
  · apply div_nonneg
    · have hj' : (j : ℝ) ≤ d := by exact_mod_cast hj
      linarith
    · exact ha.le
  · norm_num

/-- Every padded coefficient factor is totally nonnegative for a positive parameter. -/
theorem coefficientFactor_isTotallyNonneg {N d : ℕ} {a : ℝ} (ha : 0 < a) :
    (coefficientFactor N d a).IsTotallyNonneg := by
  exact Matrix.isTotallyNonneg_lowerBidiagonalFin N _ _
    (factorDiagonal_nonneg ha) (factorSubdiagonal_nonneg ha)

private def factorParameter (r s : ℕ) : ℝ :=
  if s = 0 then 1 else (r - s + 1 : ℕ)

private def paddedStepWord (p r : ℕ) (f : ℝ[X]) : ℕ → ℝ[X]
  | 0 => f
  | s + 1 =>
      step (p + s - 1) (factorParameter r s) (paddedStepWord p r f s)

private theorem factorParameter_pos (r s : ℕ) : 0 < factorParameter r s := by
  rw [factorParameter]
  split_ifs with hs0
  · norm_num
  · exact_mod_cast Nat.succ_pos (r - s)

private def paddedFactorWord (p r : ℕ) : ℕ → Matrix (Fin (p + r)) (Fin (p + r)) ℝ
  | 0 => 1
  | s + 1 =>
      coefficientFactor (p + r) (p + s - 1) (factorParameter r s) *
        paddedFactorWord p r s

private theorem paddedFactorWord_isTotallyNonneg {p r s : ℕ} (hs : s ≤ r) :
    (paddedFactorWord p r s).IsTotallyNonneg := by
  induction s with
  | zero => exact Matrix.IsTotallyNonneg.one
  | succ s ih =>
      rw [paddedFactorWord]
      apply Matrix.IsTotallyNonneg.mul
      · apply coefficientFactor_isTotallyNonneg
        exact factorParameter_pos r s
      · exact ih (Nat.le_of_succ_le hs)

private def firstP (p r : ℕ) (j : Fin p) : Fin (p + r) :=
  ⟨j, by lia⟩

private theorem firstP_injective {p r : ℕ} : Function.Injective (firstP p r) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin (p + r) => z.val) h

private theorem coefficientVector_extend_firstP {p r : ℕ} {f : ℝ[X]}
    (hp : 0 < p) (hdeg : f.natDegree ≤ p - 1) :
    coefficientVector (p + r) f =
      Function.extend (firstP p r) (coefficientVector p f) 0 := by
  funext i
  by_cases hi : i.val < p
  · let j : Fin p := ⟨i.val, hi⟩
    have hij : firstP p r j = i := by
      apply Fin.ext
      rfl
    rw [← hij, (firstP_injective (p := p) (r := r)).extend_apply]
    rfl
  · have hzero : f.coeff i.val = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
    have hnot : i ∉ Set.range (firstP p r) := by
      intro hi'
      obtain ⟨j, rfl⟩ := hi'
      exact hi j.isLt
    rw [Function.extend_apply' _ _ _ hnot, Pi.zero_apply]
    change f.coeff i.val = 0
    exact hzero

private theorem mulVec_extend_firstP {p r : ℕ}
    (A : Matrix (Fin (p + r)) (Fin (p + r)) ℝ) (v : Fin p → ℝ) :
    A.mulVec (Function.extend (firstP p r) v 0) =
      (A.submatrix id (firstP p r)).mulVec v := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq]
  symm
  apply Fintype.sum_of_injective (firstP p r) (firstP_injective (p := p) (r := r))
  · intro j hj
    rw [Function.extend_apply' v (0 : Fin (p + r) → ℝ) j hj, Pi.zero_apply,
      mul_zero]
  · intro j
    rw [(firstP_injective (p := p) (r := r)).extend_apply v (0 : Fin (p + r) → ℝ) j]

/-- The rectangular transition matrix obtained from the padded factor word. -/
def coefficientTransitionMatrix (p r : ℕ) : Matrix (Fin (p + r)) (Fin p) ℝ :=
  (paddedFactorWord p r r).submatrix id (firstP p r)

/-- The closed entry formula for Zhang--Zhao's matrix, in zero-based indices. -/
def closedTransitionEntry (p r k ell : ℕ) : ℝ :=
  if ell ≤ k ∧ k ≤ ell + r then
    (Nat.choose (p - ell + r) (k - ell) : ℝ) *
      (Nat.choose (ell + 1 + r) (r - (k - ell)) : ℝ) *
        (((ell + 1 : ℝ) * (p - ell + r - (k - ell)) +
            (p - ell) * (k - ell)) /
          ((ell + 1 + r) * (p - ell + r)))
  else 0

/-- Zhang--Zhao's closed-form transition matrix, with zero-based indices. -/
def closedTransitionMatrix (p r : ℕ) : Matrix (Fin (p + r)) (Fin p) ℝ :=
  fun k ell => closedTransitionEntry p r k.val ell.val

/-- The padded product gives a totally nonnegative rectangular transition matrix. -/
theorem coefficientTransitionMatrix_isTotallyNonneg {p r : ℕ} :
    (coefficientTransitionMatrix p r).IsTotallyNonnegRect := by
  apply (paddedFactorWord_isTotallyNonneg (le_refl r)).toRect.submatrix
  · exact Fin.val_strictMono
  · intro i j hij
    exact hij

/-- Theorem 1.3 for the closed form, conditional on the coefficient identity. -/
theorem closedTransitionMatrix_isTotallyNonneg_of_factorization
    {p r : ℕ} (hK : coefficientTransitionMatrix p r = closedTransitionMatrix p r) :
    (closedTransitionMatrix p r).IsTotallyNonnegRect := by
  rw [← hK]
  exact coefficientTransitionMatrix_isTotallyNonneg

private theorem coefficientFactor_apply_active {N d : ℕ} {a : ℝ} (j : Fin N)
    (i : Fin N) (hj : j.val ≤ d) (hi : i.val ≤ d + 1) :
    coefficientFactor N d a i j =
      if i.val = j.val then ((j.val : ℝ) + a) / a
      else if i.val = j.val + 1 then ((d : ℝ) + a - j.val) / a else 0 := by
  rw [coefficientFactor, Matrix.lowerBidiagonalFin_apply]
  by_cases hij : i = j
  · subst i
    simp [factorDiagonal, hj]
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases hsucc : i.val = j.val + 1
    · simp [hij, hsucc, factorSubdiagonal, hj]
    · simp [hij, hval, hsucc]

private theorem step_coeff_zero {d : ℕ} {a : ℝ} {f : ℝ[X]} (ha : 0 < a) :
    (step d a f).coeff 0 = f.coeff 0 := by
  simp only [step, coeff_C_mul]
  rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, darbouxOperator_eval_zero]
  field_simp

private theorem step_coeff_succ {d k : ℕ} {a : ℝ} {f : ℝ[X]} (ha : 0 < a) :
    (step d a f).coeff (k + 1) =
      ((k + 1 + a) / a) * f.coeff (k + 1) +
        (((d : ℝ) + a - k) / a) * f.coeff k := by
  simp only [step, coeff_C_mul]
  rw [coeff_darbouxOperator_succ]
  field_simp
  ring

/-- `coefficientFactor` acts on coefficient vectors as the factorization step `E_{d,a}`.

The input has degree at most `d`, and `d + 1 < N` leaves room for the output
coefficient vector.  Above the active range, the padded factor is the identity
and both polynomial coefficient vectors vanish.
-/
theorem coefficientFactor_mulVec_coefficientVector {N d : ℕ} {a : ℝ} (ha : 0 < a)
    (hN : d + 1 < N) {f : ℝ[X]} (hdeg : f.natDegree ≤ d) :
    (coefficientFactor N d a).mulVec (coefficientVector N f) =
      coefficientVector N (step d a f) := by
  funext i
  rw [coefficientFactor, lowerBidiagonalFin_mulVec]
  cases N with
  | zero => lia
  | succ N =>
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · simp only [coefficientVector]
        simp [factorDiagonal, step_coeff_zero ha, ha.ne']
      · by_cases hi : i.val ≤ d
        · simp only [coefficientVector]
          by_cases hid : d ≤ i.val
          · have hfi1 : f.coeff (i.val + 1) = 0 :=
              coeff_eq_zero_of_natDegree_lt (by lia)
            simp [factorDiagonal, factorSubdiagonal, hi, hfi1,
              step_coeff_succ ha]
          · have hle : i.val + 1 ≤ d := by lia
            simp [factorDiagonal, factorSubdiagonal, hi, hle,
              step_coeff_succ ha]
        · have hfi : f.coeff i.val = 0 :=
            coeff_eq_zero_of_natDegree_lt (by lia)
          have hfi1 : f.coeff (i.val + 1) = 0 :=
            coeff_eq_zero_of_natDegree_lt (by lia)
          simp only [coefficientVector]
          simp [factorDiagonal, factorSubdiagonal, hi, hfi, hfi1,
            step_coeff_succ ha]

/-- The full padded factor product acts as the corresponding composite step word.

For each `t ≤ s`, the supplied degree bound is the exact range needed by the
faithfulness theorem for the next factor.  This square-vector statement is the
composition law behind the rectangular transition matrix.
-/
theorem paddedFactorWord_mulVec_coefficientVector {p r s : ℕ} (hp : 0 < p)
    (hs : s ≤ r)
    {f : ℝ[X]}
    (hdeg : ∀ t ≤ s, (paddedStepWord p r f t).natDegree ≤ p + t - 1) :
    (paddedFactorWord p r s).mulVec (coefficientVector (p + r) f) =
      coefficientVector (p + r) (paddedStepWord p r f s) := by
  induction s with
  | zero => simp [paddedFactorWord, paddedStepWord]
  | succ s ih =>
      rw [paddedFactorWord, ← Matrix.mulVec_mulVec]
      rw [ih (Nat.le_of_succ_le hs) (fun t ht => hdeg t (by lia))]
      rw [paddedStepWord]
      exact coefficientFactor_mulVec_coefficientVector
        (factorParameter_pos r s) (by lia) (hdeg s (by lia))

/-- The rectangular transition acts on the first `p` coefficients as the block operator.

The explicit hypothesis `hdeg` supplies the degree bound required at each
intermediate factor; no combinatorial tree interpretation is assumed here.
-/
theorem coefficientTransitionMatrix_mulVec_coefficientVector {p r : ℕ} (hp : 0 < p)
    {f : ℝ[X]} (hdeg : f.natDegree ≤ p - 1)
    (hsteps : ∀ t ≤ r,
      (paddedStepWord p r f t).natDegree ≤ p + t - 1) :
    (coefficientTransitionMatrix p r).mulVec (coefficientVector p f) =
      coefficientVector (p + r) (paddedStepWord p r f r) := by
  rw [coefficientTransitionMatrix, ← mulVec_extend_firstP]
  rw [← coefficientVector_extend_firstP hp hdeg]
  exact paddedFactorWord_mulVec_coefficientVector hp (le_refl r) hsteps

end

end MultisetEulerianNarayana
end RealRooted
