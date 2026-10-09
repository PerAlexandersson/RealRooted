import RealRooted.CombinatorialExamples.MultisetEulerianNarayana
import Mathlib.Basic.Real.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Bidiagonal
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul

/-!
# Finite bidiagonal factors for multiset Eulerian--Narayana transitions

Zhang--Zhao, Theorem 1.3, writes the coefficient transition matrix for a block
of `r` maximal labels as a product of the coefficient matrices of the operators
`E_{d,a}`.  This file records the finite padded factors and proves their total
nonnegativity.  The identification with Zhang--Zhao's closed binomial formula
is proved below from their Lemma 4.3 and Proposition 4.1.
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



/-- Auxiliary binomial/falling-factorial term. -/
private def gTerm (A B s m : ℕ) : ℝ :=
  (s.choose m : ℝ) * (A.descFactorial (s - m) : ℝ) * (B.descFactorial m : ℝ)

private lemma cast_descFactorial_succ (n k : ℕ) :
    ((n.descFactorial (k + 1) : ℕ) : ℝ) = (n.descFactorial k : ℝ) * ((n : ℝ) - k) := by
  rcases le_or_gt k n with h | h
  · rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub h]; ring
  · rw [(Nat.descFactorial_eq_zero_iff_lt).2 h, (Nat.descFactorial_eq_zero_iff_lt).2 (by lia)]
    simp

private lemma gTerm_succ_zero (A B s : ℕ) :
    gTerm A B (s + 1) 0 = ((A : ℝ) - s) * gTerm A B s 0 := by
  unfold gTerm
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.descFactorial_zero]
  rw [cast_descFactorial_succ]; push_cast; ring

private lemma gTerm_succ_succ (A B s m : ℕ) :
    gTerm A B (s + 1) (m + 1) =
      ((A : ℝ) - s + (m + 1)) * gTerm A B s (m + 1) + ((B : ℝ) - m) * gTerm A B s m := by
  unfold gTerm
  rcases lt_trichotomy m s with h | rfl | h
  · obtain ⟨t, rfl⟩ : ∃ t, s = m + 1 + t := ⟨s - m - 1, by lia⟩
    have e1 : m + 1 + t + 1 - (m + 1) = t + 1 := by lia
    have e2 : m + 1 + t - (m + 1) = t := by lia
    have e3 : m + 1 + t - m = t + 1 := by lia
    rw [e1, e2, e3, Nat.choose_succ_succ', cast_descFactorial_succ, cast_descFactorial_succ]
    push_cast; ring
  · simp only [Nat.sub_self, Nat.choose_self, Nat.choose_succ_self, Nat.descFactorial_zero,
      show m - (m + 1) = 0 by lia]
    rw [cast_descFactorial_succ]; push_cast; ring
  · rw [Nat.choose_eq_zero_of_lt (by lia : s + 1 < m + 1),
      Nat.choose_eq_zero_of_lt (by lia : s < m + 1), Nat.choose_eq_zero_of_lt (by lia : s < m)]
    simp

private lemma gTerm_eq_zero (A B s m : ℕ) (h : s < m) : gTerm A B s m = 0 := by
  simp [gTerm, Nat.choose_eq_zero_of_lt h]

/-- The explicit value of column `ell` after the first `s + 1` factors. -/
private def colVal (p r ell s k : ℕ) : ℝ :=
  if ell ≤ k then
    (((ell : ℝ) + 1) * gTerm (ell + r) (p - ell + r) s (k - ell) +
      ((p - ell : ℕ) : ℝ) *
        (if k - ell = 0 then 0 else gTerm (ell + r + 1) (p - ell + r - 1) s (k - ell - 1))) /
      (r.descFactorial s : ℝ)
  else 0

private lemma colVal_eq_zero_of_lt (p r ell s k : ℕ) (h : ell + s + 1 < k) :
    colVal p r ell s k = 0 := by
  unfold colVal
  rw [ite_eq_left (by lia), gTerm_eq_zero _ _ _ _ (by lia), gTerm_eq_zero _ _ _ _ (by lia)]
  simp

private lemma colVal_add (p r ell s j : ℕ) :
    colVal p r ell s (ell + j) =
      (((ell : ℝ) + 1) * gTerm (ell + r) (p - ell + r) s j +
        ((p - ell : ℕ) : ℝ) *
          (if j = 0 then 0 else gTerm (ell + r + 1) (p - ell + r - 1) s (j - 1))) /
        (r.descFactorial s : ℝ) := by
  simp [colVal]

private lemma colVal_step (p r ell s k : ℕ) (hs : s < r) (hp : ell ≤ p) :
    colVal p r ell (s + 1) k * ((r - s : ℕ) : ℝ) =
      ((k : ℝ) + ((r - s : ℕ) : ℝ)) * colVal p r ell s k +
        (if 1 ≤ k then
          (((p + s : ℕ) : ℝ) + ((r - s : ℕ) : ℝ) - ((k - 1 : ℕ) : ℝ)) *
            colVal p r ell s (k - 1)
        else 0) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = ell + q := ⟨p - ell, by lia⟩
  have hq : ell + q - ell = q := by lia
  have hrs : ((r - s : ℕ) : ℝ) = r - s := by rw [Nat.cast_sub hs.le]
  have hdf : (r.descFactorial (s + 1) : ℝ) = r.descFactorial s * ((r : ℝ) - s) :=
    cast_descFactorial_succ r s
  have hpos : (r.descFactorial s : ℝ) ≠ 0 := by
    have := (Nat.descFactorial_eq_zero_iff_lt (n := r) (k := s)).not.2 (by lia)
    exact_mod_cast this
  have hrs0 : (r : ℝ) - s ≠ 0 := by
    have : (s : ℝ) < r := by exact_mod_cast hs
    linarith
  have hqr : ((q + r - 1 : ℕ) : ℝ) = q + r - 1 := by
    rw [Nat.cast_sub (by lia : 1 ≤ q + r)]; push_cast; ring
  rcases lt_trichotomy k ell with h | h | h
  · have h1 : ¬ ell ≤ k := by lia
    have h2 : ¬ ell ≤ k - 1 := by lia
    simp [colVal, h1, h2]
  · subst h
    have h0 : (if 1 ≤ k then
          (((k + q + s : ℕ) : ℝ) + ((r - s : ℕ) : ℝ) - ((k - 1 : ℕ) : ℝ)) *
            colVal (k + q) r k s (k - 1) else 0) = 0 := by
      split_ifs with hk
      · simp [colVal, show ¬ k ≤ k - 1 by lia]
      · rfl
    have e1 := colVal_add (k + q) r k (s + 1) 0
    have e2 := colVal_add (k + q) r k s 0
    simp only [Nat.add_zero] at e1 e2
    rw [h0, e1, e2]
    simp only [ite_true, hq]
    rw [gTerm_succ_zero, hdf, hrs]
    field_simp
    push_cast
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, k = ell + (m + 1) := ⟨k - ell - 1, by lia⟩
    have hk1 : ell + (m + 1) - 1 = ell + m := by lia
    rw [ite_eq_left (by lia), hk1, colVal_add, colVal_add, colVal_add]
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, hq]
    rw [gTerm_succ_succ, hdf, hrs]
    rcases m with _ | m
    · simp only [ite_true, gTerm_succ_zero]
      field_simp
      push_cast [hqr]
      ring
    · simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, gTerm_succ_succ]
      field_simp
      push_cast [hqr]
      ring

private lemma coefficientFactor_mul_apply {N N' : ℕ} (d : ℕ) (a : ℝ)
    (M : Matrix (Fin N) (Fin N') ℝ)
    (k : Fin N) (j : Fin N') :
    (coefficientFactor N d a * M) k j = factorDiagonal d a k.val * M k j +
      (if h : 1 ≤ k.val then
        factorSubdiagonal d a (k.val - 1) * M ⟨k.val - 1, by lia⟩ j else 0) := by
  rw [Matrix.mul_apply]
  have hsplit : ∀ i : Fin N, coefficientFactor N d a k i * M i j =
      (if k = i then factorDiagonal d a k.val * M k j else 0) +
      (if k.val = i.val + 1 then factorSubdiagonal d a i.val * M i j else 0) := by
    intro i
    unfold coefficientFactor
    by_cases h1 : k = i
    · subst h1; simp
    · simp only [h1, ite_false, zero_add]
      split_ifs <;> simp_all
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  split_ifs with hk
  · rw [Finset.sum_eq_single ⟨k.val - 1, by lia⟩]
    · rw [ite_eq_left (by lia)]
    · intro b _ hb
      rw [ite_eq_right]
      intro h
      apply hb
      ext
      lia
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right]
    lia

private lemma paddedFactorWord_apply (p r ell : ℕ) (hl : ell < p) :
    ∀ s, s < r → ∀ k : Fin (p + r),
      paddedFactorWord p r (s + 1) k ⟨ell, by lia⟩ = colVal p r ell s k.val := by
  intro s
  induction s with
  | zero =>
    intro _ k
    change (coefficientFactor (p + r) (p + 0 - 1) (factorParameter r 0) *
      (1 : Matrix (Fin (p + r)) (Fin (p + r)) ℝ)) k _ = _
    rw [coefficientFactor_mul_apply]
    obtain ⟨k, hk⟩ := k
    simp only [factorParameter, ite_true, Matrix.one_apply, Fin.mk.injEq]
    rcases lt_or_ge k ell with h | h
    · have h1 : ¬ ell ≤ k := by lia
      simp only [colVal, h1, ite_false, show k ≠ ell by lia, show k - 1 ≠ ell by lia]
      simp
    · obtain ⟨j, rfl⟩ : ∃ j, k = ell + j := ⟨k - ell, by lia⟩
      rw [colVal_add]
      rcases j with _ | _ | j
      · simp only [Nat.add_zero, ite_true]
        simp only [factorDiagonal, show ell ≤ p - 1 by lia, ↓reduceIte, div_one, mul_one,
          mul_ite, mul_zero, dite_eq_ite, gTerm, Nat.choose_self, Nat.cast_one, tsub_self,
          Nat.descFactorial_zero, add_zero, add_eq_left, ite_eq_right_iff]
        intro h1 h2
        lia
      · simp only [show ell + (0 + 1) ≠ ell by lia, show ell + (0 + 1) - 1 = ell by lia,
          ite_true, ite_false]
        simp only [add_zero, zero_add, mul_zero, le_add_iff_nonneg_left, zero_le, ↓reduceDIte,
          factorSubdiagonal, show ell ≤ p - 1 by lia, ↓reduceIte, div_one, mul_one, gTerm,
          Nat.choose_succ_self, CharP.cast_eq_zero, zero_tsub, Nat.descFactorial_zero,
          Nat.cast_one, Nat.descFactorial_succ, tsub_zero, Nat.cast_add, zero_mul, one_ne_zero,
          tsub_self, Nat.choose_self]
        rw [Nat.cast_sub (by lia), Nat.cast_sub (by lia)]
        push_cast
        ring
      · simp only [show ell + (j + 1 + 1) ≠ ell by lia,
          show ell + (j + 1 + 1) - 1 ≠ ell by lia, ite_false]
        simp [gTerm]
  | succ s ih =>
    intro hs k
    change (coefficientFactor (p + r) (p + (s + 1) - 1) (factorParameter r (s + 1)) *
      paddedFactorWord p r (s + 1)) k _ = _
    rw [coefficientFactor_mul_apply, ih (by lia) k]
    have ha : factorParameter r (s + 1) = ((r - s : ℕ) : ℝ) := by
      simp only [factorParameter, Nat.add_one_ne_zero, ite_false]
      congr 1
      lia
    have hd : p + (s + 1) - 1 = p + s := by lia
    rw [ha, hd]
    have ha0 : ((r - s : ℕ) : ℝ) ≠ 0 := by
      have : 0 < r - s := by lia
      exact_mod_cast this.ne'
    have hdiag : factorDiagonal (p + s) ((r - s : ℕ) : ℝ) k.val * colVal p r ell s k.val =
        ((k.val : ℝ) + ((r - s : ℕ) : ℝ)) / ((r - s : ℕ) : ℝ) *
          colVal p r ell s k.val := by
      unfold factorDiagonal
      split_ifs with h
      · rfl
      · rw [colVal_eq_zero_of_lt _ _ _ _ _ (by lia)]; simp
    have hsub :
        (if h : 1 ≤ k.val then
          factorSubdiagonal (p + s) ((r - s : ℕ) : ℝ) (k.val - 1) *
          paddedFactorWord p r (s + 1) ⟨k.val - 1, by lia⟩ ⟨ell, by lia⟩ else 0) =
        (if 1 ≤ k.val then
          (((p + s : ℕ) : ℝ) + ((r - s : ℕ) : ℝ) - ((k.val - 1 : ℕ) : ℝ)) /
            ((r - s : ℕ) : ℝ) *
            colVal p r ell s (k.val - 1) else 0) := by
      split_ifs with h
      · rw [ih (by lia)]
        unfold factorSubdiagonal
        split_ifs with h'
        · rfl
        · rw [colVal_eq_zero_of_lt _ _ _ _ _ (by simp only at *; lia)]; simp
      · rfl
    rw [hdiag, hsub]
    have key := colVal_step p r ell s k.val (by lia) hl.le
    split_ifs at key ⊢ with h
    · field_simp
      linear_combination -key
    · field_simp
      linear_combination -key

private lemma gTerm_eq_choose (A B s m : ℕ) (h : m ≤ s) :
    gTerm A B s m = (s.factorial : ℝ) * (A.choose (s - m) : ℝ) * (B.choose m : ℝ) := by
  unfold gTerm
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  have h' : (s.choose m : ℝ) * (m.factorial : ℝ) * ((s - m).factorial : ℝ) = s.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  rw [← h']
  push_cast
  ring

private lemma cast_descFactorial_succ_self (s : ℕ) :
    ((s + 1).descFactorial s : ℝ) = ((s + 1).factorial : ℝ) := by
  have := Nat.factorial_mul_descFactorial (n := s + 1) (k := s) (by lia)
  rw [show s + 1 - s = 1 by lia] at this
  simp only [Nat.factorial_one, one_mul] at this
  rw [this]

private lemma cast_choose_succ (N k : ℕ) :
    (N.choose k : ℝ) = ((N + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) / ((N : ℝ) + 1) := by
  have h := Nat.add_one_mul_choose_eq N k
  have h' : ((N : ℝ) + 1) * (N.choose k : ℝ) =
      ((N + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
    exact_mod_cast h
  rw [eq_div_iff (by positivity)]
  linarith

private lemma final_identity_main (ell q m n : ℕ) :
    (((ell : ℝ) + 1) * gTerm (ell + m + n + 1) (q + m + n + 1) (m + n) m +
        (q : ℝ) * (if m = 0 then 0 else gTerm (ell + m + n + 2) (q + m + n) (m + n) (m - 1))) /
        ((m + n + 1).descFactorial (m + n) : ℝ) =
      ((q + m + n + 1).choose m : ℝ) * ((ell + m + n + 2).choose (n + 1) : ℝ) *
        ((((ell : ℝ) + 1) * (q + n + 1) + q * m) / ((ell + m + n + 2) * (q + m + n + 1))) := by
  rw [cast_descFactorial_succ_self, gTerm_eq_choose _ _ _ _ (by lia),
    show m + n - m = n by lia, Nat.factorial_succ]
  have hC1 := cast_choose_succ (ell + m + n + 1) n
  rw [show ell + m + n + 1 + 1 = ell + m + n + 2 by lia] at hC1
  rw [hC1]
  rcases m with _ | m
  · simp only [ite_true]
    push_cast
    field_simp
    ring
  · simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    rw [gTerm_eq_choose _ _ _ _ (by lia), show m + 1 + n - m = n + 1 by lia]
    have hC2 := cast_choose_succ (q + (m + 1) + n) m
    rw [hC2]
    push_cast
    field_simp
    ring

private lemma final_identity_top (ell q t : ℕ) :
    ((q : ℝ) * gTerm (ell + t + 2) (q + t) t t) / ((t + 1).descFactorial t : ℝ) =
      ((q + t + 1).choose (t + 1) : ℝ) * ((ell + t + 2).choose 0 : ℝ) *
        ((((ell : ℝ) + 1) * q + q * (t + 1)) / ((ell + t + 2) * (q + t + 1))) := by
  rw [cast_descFactorial_succ_self, gTerm_eq_choose _ _ _ _ le_rfl, Nat.sub_self,
    Nat.factorial_succ, cast_choose_succ (q + t) t]
  push_cast
  field_simp
  ring

private lemma colVal_last (p r ell k : ℕ) (hr : 0 < r) (hl : ell < p) :
    colVal p r ell (r - 1) k = closedTransitionEntry p r k ell := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by lia⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = ell + q := ⟨p - ell, by lia⟩
  rw [Nat.add_sub_cancel]
  rcases lt_or_ge k ell with h | h
  · simp [colVal, closedTransitionEntry, show ¬ ell ≤ k by lia]
  · obtain ⟨m, rfl⟩ : ∃ m, k = ell + m := ⟨k - ell, by lia⟩
    rw [colVal_add]
    simp only [closedTransitionEntry, Nat.add_sub_cancel_left]
    rcases lt_or_ge t m with hm | hm
    · rcases Nat.lt_or_ge (t + 1) m with hm' | hm'
      · rw [ite_eq_right (show ¬(ell ≤ ell + m ∧ ell + m ≤ ell + (t + 1)) by lia),
          ite_eq_right (show m ≠ 0 by lia), gTerm_eq_zero _ _ _ _ (by lia),
          gTerm_eq_zero _ _ _ _ (by lia)]
        simp
      · obtain rfl : m = t + 1 := by lia
        rw [ite_eq_left (show ell ≤ ell + (t + 1) ∧ ell + (t + 1) ≤ ell + (t + 1) by lia),
          ite_eq_right (show t + 1 ≠ 0 by lia), gTerm_eq_zero _ _ t (t + 1) (by lia),
          Nat.add_sub_cancel, Nat.sub_self, mul_zero, zero_add,
          show ell + (t + 1) + 1 = ell + t + 2 by lia, show q + (t + 1) - 1 = q + t by lia,
          final_identity_top ell q t, show q + (t + 1) = q + t + 1 by lia,
          show ell + 1 + (t + 1) = ell + t + 2 by lia]
        congr 1
        push_cast
        ring
    · obtain ⟨n, rfl⟩ : ∃ n, t = m + n := ⟨t - m, by lia⟩
      rw [ite_eq_left (show ell ≤ ell + m ∧ ell + m ≤ ell + (m + n + 1) by lia)]
      rw [show ell + (m + n + 1) = ell + m + n + 1 by lia,
        show q + (m + n + 1) = q + m + n + 1 by lia,
        show ell + m + n + 1 + 1 = ell + m + n + 2 by lia,
        show q + m + n + 1 - 1 = q + m + n by lia, final_identity_main ell q m n,
        show m + n + 1 - m = n + 1 by lia, show ell + 1 + (m + n + 1) = ell + m + n + 2 by lia]
      congr 1
      push_cast
      ring

/-- Zhang--Zhao's Lemma 4.3 and Proposition 4.1 identify the transition matrix. -/
theorem coefficientTransitionMatrix_eq_closedTransitionMatrix {p r : ℕ} (hr : 0 < r) :
    coefficientTransitionMatrix p r = closedTransitionMatrix p r := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by lia⟩
  ext k ell
  have h1 := paddedFactorWord_apply p (t + 1) ell.val ell.isLt t (by lia) k
  have h2 := colVal_last p (t + 1) ell.val k.val (by lia) ell.isLt
  rw [Nat.add_sub_cancel] at h2
  simp only [coefficientTransitionMatrix, closedTransitionMatrix, Matrix.submatrix_apply, id]
  rw [show firstP p (t + 1) ell = ⟨ell.val, by lia⟩ from rfl, h1, h2]


/-- Zhang--Zhao's closed binomial transition matrix is totally nonnegative. -/
theorem closedTransitionMatrix_isTotallyNonneg {p r : ℕ} (hr : 0 < r) :
    (closedTransitionMatrix p r).IsTotallyNonnegRect := by
  rw [← coefficientTransitionMatrix_eq_closedTransitionMatrix hr]
  exact coefficientTransitionMatrix_isTotallyNonneg

end

end MultisetEulerianNarayana
end RealRooted
