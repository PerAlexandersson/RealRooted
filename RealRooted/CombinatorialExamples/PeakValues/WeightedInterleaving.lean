import RealRooted.CombinatorialExamples.PeakValues.Stability
import RealRooted.SamePhaseInterlacing

/-!
# Weighted interleaving of peak-value polynomials

Positive weighted diagonal restrictions of consecutive peak-value enumerators
are in proper position.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- Weighted diagonal specialization of the rank-`n` peak-value enumerator. -/
def peakValueWeightedDiagonal {n : ℕ} (wt : Fin n → ℝ) : ℝ[X] :=
  commonPhaseRestriction wt (peakValuePolynomial n)

theorem peakValueMonomial_isMultiaffine {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    MvPolynomial.IsMultiaffine (peakValueMonomial π) := by
  classical
  exact MvPolynomial.IsMultiaffine.prod_X (peakValues π)

theorem peakValuePolynomial_isMultiaffine (n : ℕ) :
    MvPolynomial.IsMultiaffine (peakValuePolynomial n) := by
  classical
  unfold peakValuePolynomial
  apply MvPolynomial.IsMultiaffine.sum
  intro π _
  exact peakValueMonomial_isMultiaffine π

theorem peakValuePolynomial_hasNonnegCoeffs (n : ℕ) :
    MvPolynomial.HasNonnegCoeffs (peakValuePolynomial n) := by
  classical
  unfold peakValuePolynomial peakValueMonomial
  apply MvPolynomial.HasNonnegCoeffs.sum
  intro π _
  apply MvPolynomial.HasNonnegCoeffs.prod
  intro v _
  exact MvPolynomial.HasNonnegCoeffs.X v

@[simp] theorem eval_one_peakValuePolynomial (n : ℕ) :
    MvPolynomial.eval (fun _ => 1) (peakValuePolynomial n) = n.factorial := by
  classical
  simp [peakValuePolynomial, peakValueMonomial, Fintype.card_perm]

theorem peakValuePolynomial_ne_zero (n : ℕ) :
    peakValuePolynomial n ≠ 0 := by
  intro hzero
  have h := congrArg (MvPolynomial.eval (fun _ => (1 : ℝ))) hzero
  simp only [eval_one_peakValuePolynomial, map_zero] at h
  have hfac : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  exact hfac h

theorem identifyLast_peakValuePolynomial_hasNonnegCoeffs (n : ℕ) :
    MvPolynomial.HasNonnegCoeffs
      (identifyLast n (peakValuePolynomial (n + 1))) := by
  apply MvPolynomial.HasNonnegCoeffs.rename_of_injective
    (peakValuePolynomial_hasNonnegCoeffs (n + 1))
  exact (finSuccEquiv' (Fin.last n)).injective

theorem identifyLast_peakValuePolynomial_ne_zero (n : ℕ) :
    identifyLast n (peakValuePolynomial (n + 1)) ≠ 0 := by
  exact (MvPolynomial.renameEquiv ℝ
    (finSuccEquiv' (Fin.last n))).injective.ne
      (peakValuePolynomial_ne_zero (n + 1))

theorem identifyLast_peakValuePolynomial_isMultiaffine (n : ℕ) :
    MvPolynomial.IsMultiaffine
      (identifyLast n (peakValuePolynomial (n + 1))) := by
  exact (peakValuePolynomial_isMultiaffine (n + 1)).rename
    (finSuccEquiv' (Fin.last n)).injective

theorem pderiv_none_identifyLast_peakValuePolynomial_ne_zero
    (n : ℕ) (hn : 2 ≤ n) :
    MvPolynomial.pderiv none
      (identifyLast n (peakValuePolynomial (n + 1))) ≠ 0 := by
  let Q := identifyLast n (peakValuePolynomial (n + 1))
  let z : Option (Fin n) → ℝ := fun _ => 1
  let z0 := Function.update z none 0
  have hrec := identifyLast_peakValuePolynomial_succ n hn
  have hQ1 := congrArg (MvPolynomial.eval z) hrec
  have hQ0 := congrArg (MvPolynomial.eval z0) hrec
  have hevalOld :
      MvPolynomial.eval z (liftOld (peakValuePolynomial n)) = n.factorial := by
    simp [z, liftOld, MvPolynomial.eval_rename, Function.comp_def]
  have hevalOld0 :
      MvPolynomial.eval z0 (liftOld (peakValuePolynomial n)) = n.factorial := by
    simp [z0, z, liftOld, MvPolynomial.eval_rename, Function.comp_def]
  simp only [map_add, map_mul, map_sum, MvPolynomial.eval_C,
    MvPolynomial.eval_X] at hQ1 hQ0
  simp only [mul_one, hevalOld, map_sub, map_one, MvPolynomial.eval_X,
    sub_self, zero_mul, Finset.sum_const_zero, mul_zero, add_zero,
    Function.update_self, hevalOld0, ne_eq, reduceCtorEq, not_false_eq_true,
    Function.update_of_ne, z, z0] at hQ1 hQ0
  have haff := MvPolynomial.IsMultiaffine.eval_update_eq_eval_pderiv_mul_add
    (identifyLast_peakValuePolynomial_isMultiaffine n) none z 1
  have hzself : Function.update z none 1 = z := by
    funext j
    by_cases hj : j = none <;> simp [z, hj]
  rw [hzself] at haff
  change MvPolynomial.eval z Q =
    MvPolynomial.eval z (MvPolynomial.pderiv none Q) * 1 +
      MvPolynomial.eval z0 Q at haff
  change MvPolynomial.eval z Q = _ at hQ1
  change MvPolynomial.eval z0 Q = _ at hQ0
  intro hpzero
  rw [hpzero] at haff
  simp only [map_zero, zero_mul, zero_add] at haff
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have hnminus : 0 < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (by lia : 1 < n)
  have hprod : 0 < ((n - 1 : ℕ) : ℝ) * (n.factorial : ℝ) :=
    mul_pos hnminus hfac
  have hnsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by lia : 1 ≤ n)]
    norm_num
  rw [hnsub] at hprod
  nlinarith

def peakValueOptionWeights (n : ℕ) (wt : Fin (n + 1) → ℝ) :
    Option (Fin n) → ℝ
  | none => wt (Fin.last n)
  | some j => wt j.castSucc

@[simp] theorem peakValueOptionWeights_none (n : ℕ)
    (wt : Fin (n + 1) → ℝ) :
    peakValueOptionWeights n wt none = wt (Fin.last n) := rfl

@[simp] theorem peakValueOptionWeights_some (n : ℕ)
    (wt : Fin (n + 1) → ℝ) (j : Fin n) :
    peakValueOptionWeights n wt (some j) = wt j.castSucc := rfl

theorem commonPhaseRestriction_identifyLast (n : ℕ)
    (wt : Fin (n + 1) → ℝ) (P : MvPolynomial (Fin (n + 1)) ℝ) :
    commonPhaseRestriction (peakValueOptionWeights n wt)
        (identifyLast n P) =
      commonPhaseRestriction wt P := by
  rw [identifyLast, MvPolynomial.renameEquiv_apply,
    commonPhaseRestriction_rename]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [peakValueOptionWeights]
  · change peakValueOptionWeights n wt
      ((finSuccEquiv' (Fin.last n)) k.castSucc) = wt k.castSucc
    rw [finSuccEquiv'_last_apply_castSucc]
    rfl

theorem commonPhaseRestriction_update_none_identifyLast_peakValue
    (n : ℕ) (hn : 2 ≤ n) (wt : Fin (n + 1) → ℝ) :
    commonPhaseRestriction
        (Function.update (peakValueOptionWeights n wt) none 0)
        (identifyLast n (peakValuePolynomial (n + 1))) =
      Polynomial.C 2 *
        peakValueWeightedDiagonal (fun j : Fin n => wt j.castSucc) := by
  have h := congrArg
    (commonPhaseRestriction
      (Function.update (peakValueOptionWeights n wt) none 0))
    (identifyLast_peakValuePolynomial_succ n hn)
  simp only [commonPhaseRestriction_add,
    commonPhaseRestriction_mul, commonPhaseRestriction_C,
    commonPhaseRestriction_X] at h
  have hlift :
      commonPhaseRestriction
          (Function.update (peakValueOptionWeights n wt) none 0)
          (liftOld (peakValuePolynomial n)) =
        peakValueWeightedDiagonal (fun j : Fin n => wt j.castSucc) := by
    rw [liftOld, commonPhaseRestriction_rename]
    rfl
  rw [hlift] at h
  simpa [peakValueOptionWeights, Function.update_self] using h

theorem peakValueWeightedDiagonal_consecutive_prec_of_stable
    (n : ℕ) (hn : 2 ≤ n) (wt : Fin (n + 1) → ℝ)
    (hwt : ∀ j, 0 < wt j)
    (hstable : MvRealStable (peakValuePolynomial (n + 1))) :
    Prec
      (peakValueWeightedDiagonal (fun j : Fin n => wt j.castSucc))
      (peakValueWeightedDiagonal wt) := by
  let Q := identifyLast n (peakValuePolynomial (n + 1))
  let w := peakValueOptionWeights n wt
  let A := commonPhaseRestriction (Function.update w none 0) Q
  let D := Polynomial.C (w none) *
    commonPhaseRestriction w (MvPolynomial.pderiv none Q)
  have hwpos : ∀ j, 0 < w j := by
    intro j
    cases j with
    | none => exact hwt (Fin.last n)
    | some j => exact hwt j.castSucc
  have hQnn : MvPolynomial.HasNonnegCoeffs Q := by
    exact identifyLast_peakValuePolynomial_hasNonnegCoeffs n
  have hQ0 : Q ≠ 0 := identifyLast_peakValuePolynomial_ne_zero n
  have hDQnn : MvPolynomial.HasNonnegCoeffs (MvPolynomial.pderiv none Q) :=
    MvPolynomial.HasNonnegCoeffs.pderiv hQnn none
  have hDQ0 : MvPolynomial.pderiv none Q ≠ 0 :=
    pderiv_none_identifyLast_peakValuePolynomial_ne_zero n hn
  have hAnn : HasNonnegCoeffs A := by
    exact commonPhaseRestriction_hasNonnegCoeffs hQnn _ fun j => by
      by_cases hj : j = none
      · subst j
        simp
      · rw [Function.update_of_ne hj]
        exact (hwpos j).le
  have hAeq : A = Polynomial.C 2 *
      peakValueWeightedDiagonal (fun j : Fin n => wt j.castSucc) := by
    exact commonPhaseRestriction_update_none_identifyLast_peakValue n hn wt
  have hlowerNN : HasNonnegCoeffs
      (peakValueWeightedDiagonal (fun j : Fin n => wt j.castSucc)) := by
    exact commonPhaseRestriction_hasNonnegCoeffs
      (peakValuePolynomial_hasNonnegCoeffs n) _
      (fun j => (hwt j.castSucc).le)
  have hlower0 :
      peakValueWeightedDiagonal (fun j : Fin n => wt j.castSucc) ≠ 0 := by
    exact commonPhaseRestriction_ne_zero
      (peakValuePolynomial_hasNonnegCoeffs n)
      (peakValuePolynomial_ne_zero n) _ (fun j => hwt j.castSucc)
  have hA0 : A ≠ 0 := by rw [hAeq]; exact mul_ne_zero (by norm_num) hlower0
  have hApos : HasPosLeadingCoeff A := hAnn.pos_leadingCoeff hA0
  have hDnn : HasNonnegCoeffs D := by
    exact nonnegCoeffs_C_mul (hwpos none).le
      (commonPhaseRestriction_hasNonnegCoeffs hDQnn w
        fun j => (hwpos j).le)
  have hD0 : D ≠ 0 := by
    apply mul_ne_zero
    · exact Polynomial.C_ne_zero.mpr (hwpos none).ne'
    · exact commonPhaseRestriction_ne_zero hDQnn hDQ0 w hwpos
  have hDpos : HasPosLeadingCoeff D := hDnn.pos_leadingCoeff hD0
  have hQstable : MvRealStable Q := by
    exact hstable.rename
      (finSuccEquiv' (Fin.last n))
  have hDA : Prec D A := by
    exact hQstable.prec_commonPhaseRestriction_pderiv
      (identifyLast_peakValuePolynomial_isMultiaffine n)
      none w hwpos hApos hDpos
  have hAXD : Prec A (Polynomial.X * D) :=
    prec_mul_X_of_prec_of_nonneg hDA hDnn hAnn
  have hAfull : Prec A (A + Polynomial.X * D) :=
    prec_add_X_mul_of_prec hAXD hApos hDpos
  have hdecomp :
      commonPhaseRestriction w Q = A + Polynomial.X * D := by
    exact commonPhaseRestriction_eq_constant_add_X_mul_pderiv
      (identifyLast_peakValuePolynomial_isMultiaffine n) none w
  have hfull : commonPhaseRestriction w Q =
      peakValueWeightedDiagonal wt := by
    exact commonPhaseRestriction_identifyLast n wt
      (peakValuePolynomial (n + 1))
  rw [← hdecomp, hfull, hAeq] at hAfull
  have hscaled := prec_C_mul_left hAfull (by norm_num : (2 : ℝ)⁻¹ ≠ 0)
  simpa only [← mul_assoc, ← Polynomial.C_mul,
    inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), Polynomial.C_1,
    one_mul] using hscaled

theorem peakValues_eq_empty_of_le_two {n : ℕ} (hn : n ≤ 2)
    (π : Equiv.Perm (Fin n)) : peakValues π = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hv2 := two_le_value_of_mem_peakValues hv
  have hvlt := v.isLt
  lia

theorem peakValuePolynomial_eq_C_factorial_of_le_two
    (n : ℕ) (hn : n ≤ 2) :
    peakValuePolynomial n = MvPolynomial.C (n.factorial : ℝ) := by
  classical
  simp [peakValuePolynomial, peakValueMonomial,
    peakValues_eq_empty_of_le_two hn, Fintype.card_perm]

theorem peakValueWeightedDiagonal_one (wt : Fin 1 → ℝ) :
    peakValueWeightedDiagonal wt = 1 := by
  rw [peakValueWeightedDiagonal,
    peakValuePolynomial_eq_C_factorial_of_le_two 1 (by norm_num)]
  simp [commonPhaseRestriction]

theorem peakValueWeightedDiagonal_two (wt : Fin 2 → ℝ) :
    peakValueWeightedDiagonal wt = Polynomial.C 2 := by
  rw [peakValueWeightedDiagonal,
    peakValuePolynomial_eq_C_factorial_of_le_two 2 (by norm_num)]
  simp [commonPhaseRestriction]

theorem peakValueWeightedDiagonal_consecutive_prec_of_stable_all_ranks
    (n : ℕ) (hn : 1 ≤ n) (wt : Fin (n + 1) → ℝ)
    (hwt : ∀ j, 0 < wt j)
    (hstable : MvRealStable (peakValuePolynomial (n + 1))) :
    Prec
      (peakValueWeightedDiagonal (fun j : Fin n => wt j.castSucc))
      (peakValueWeightedDiagonal wt) := by
  by_cases hn2 : 2 ≤ n
  · exact peakValueWeightedDiagonal_consecutive_prec_of_stable
      n hn2 wt hwt hstable
  · have hn1 : n = 1 := by lia
    subst n
    rw [peakValueWeightedDiagonal_one,
      peakValueWeightedDiagonal_two]
    have hprec := prec_C_mul_right
      (prec_refl (by norm_num : (1 : ℝ[X]) ≠ 0)
        (by exact Polynomial.Splits.one))
      (by norm_num : (2 : ℝ) ≠ 0)
    simpa using hprec

/-- Positive weighted diagonal specializations of consecutive peak-value
enumerators are in proper position. -/
theorem peakValueWeightedDiagonal_consecutive_prec
    (n : ℕ) (hn : 1 ≤ n) (wt : Fin (n + 1) → ℝ)
    (hwt : ∀ j, 0 < wt j) :
    Prec
      (peakValueWeightedDiagonal (fun j : Fin n => wt j.castSucc))
      (peakValueWeightedDiagonal wt) := by
  exact peakValueWeightedDiagonal_consecutive_prec_of_stable_all_ranks n hn wt hwt
    (peakValuePolynomial_mvRealStable (n + 1))

end

end RealRooted
