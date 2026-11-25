module

public import RealRooted.Basic
public import RealRooted.CombinatorialExamples.CoefficientHelpers
import RealRooted.Linear
public import RealRooted.MaWang
public import RealRooted.Wagner
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic
import RealRooted.WagnerX.AffineFactors
public import RealRooted.Basic.ProperPosition
import RealRooted.Basic.PolynomialFacts
import RealRooted.Mathlib.Data.Nat.Choose.Cast

/-!
# One-Descent Gamma Family

Base-case interlacing and real-rootedness facts for the normalized one-descent
gamma polynomials.
-/

@[expose] public section

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted

/-- The monomial summand in the one-descent `\Gamma`-family. -/
def oneDescentGammaTerm (d m j r : Nat) : ℝ[X] :=
  C ((Nat.choose m r * Nat.choose d (r - j) : Nat) : ℝ) * X ^ (m - r)

/-- The refined one-descent family
`Γ_{d,j}^{(m)}(x) = ∑_{r=j}^m binom(m,r) binom(d, r-j) x^(m-r)`. -/
def oneDescentGamma (d m j : Nat) : ℝ[X] :=
  Finset.sum (Finset.Icc j m) (fun r => oneDescentGammaTerm d m j r)

/-- The monomial correction `x^(m-1)` occurring in the normalized reversed
family `Q_d^(m)`. We package it with a separate definition so that the `m = 0`
edge case stays harmless. -/
def oneDescentCorrection : Nat → ℝ[X]
  | 0 => 0
  | m + 1 => X ^ m

/-- The normalized reversed one-descent polynomial
`Q_d^(m) = Γ_{d,0}^{(m)} - x^(m-1)`. -/
def oneDescentQ (d m : Nat) : ℝ[X] :=
  oneDescentGamma d m 0 - oneDescentCorrection m

@[simp] lemma oneDescentCorrection_zero :
    oneDescentCorrection 0 = 0 := rfl

@[simp] lemma oneDescentCorrection_succ (m : Nat) :
    oneDescentCorrection (m + 1) = X ^ m := rfl

lemma choose_cast_succ_eq_ratio (m j : Nat) :
    ((Nat.choose m (j + 1) : Nat) : ℝ) =
      ((Nat.choose m j : Nat) : ℝ) * (((m - j : Nat) : ℝ) / ((j + 1 : Nat) : ℝ)) := by
  have hj1_ne : ((j + 1 : Nat) : ℝ) ≠ 0 := by positivity
  rw [← mul_div_assoc]
  apply (eq_div_iff hj1_ne).2
  simpa [Nat.cast_add, Nat.cast_one] using Nat.cast_choose_succ_right_eq (R := ℝ) m j

lemma oneDescentGamma_linearShift_nonneg (m j : Nat) :
    0 ≤ (((m - j : Nat) : ℝ) / ((j + 1 : Nat) : ℝ)) := by
  positivity

private lemma isRealRooted_X_pow :
    ∀ n : Nat, (((X : ℝ[X]) ^ n) ≠ 0 ∧ ((X : ℝ[X]) ^ n).Splits) := by
  simp

lemma strictInterl_X_add_C_to_X_mul_X_add_C {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    StrictInterl (X + C a) (X * (X + C b)) := by
  exact strictInterl_mul_X_of_strictInterl_of_nonneg
    (StrictInterl.X_add_C_iff.mpr hab)
    (hasNonnegCoeffs_X.add (hasNonnegCoeffs_C (ha.trans hab)))
    (hasNonnegCoeffs_X.add (hasNonnegCoeffs_C ha))

/-- A shared monomial and nonzero scalars transport the affine comparison. -/
private lemma strictInterl_scaled_X_pow_affine {a b c e : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : c ≠ 0) (he : e ≠ 0) (n : ℕ) :
    StrictInterl (C c * X ^ n * (X + C a))
      (C e * X ^ (n + 1) * (X + C b)) := by
  have h := ((strictInterl_X_add_C_to_X_mul_X_add_C ha hab).C_mul_left hc).C_mul_right he
  simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
    h.mul_common_factor (pow_ne_zero n X_ne_zero) (by simp)

lemma oneDescentGammaTerm_succ
    (d m j r : Nat) (hjr : j < r) :
    oneDescentGammaTerm (d + 1) m j r =
      oneDescentGammaTerm d m j r + oneDescentGammaTerm d m (j + 1) r := by
  unfold oneDescentGammaTerm
  have hrj : r - j = (r - (j + 1)) + 1 := by lia
  rw [hrj, Nat.choose_succ_succ', Nat.mul_add]
  grind

lemma oneDescentGamma_zero
    (m j : Nat) (hjm : j ≤ m) :
    oneDescentGamma 0 m j =
      C ((Nat.choose m j : Nat) : ℝ) * X ^ (m - j) := by
  unfold oneDescentGamma
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_Icc.mpr ⟨le_rfl, hjm⟩)]
  · unfold oneDescentGammaTerm
    simp
  · intro r hr hrj
    unfold oneDescentGammaTerm
    have hjr : j < r := lt_of_le_of_ne (Finset.mem_Icc.mp hr).1 (Ne.symm hrj)
    have hchoose : Nat.choose 0 (r - j) = 0 := by grind
    simp [hchoose]

lemma oneDescentGamma_recurrence
    (d m j : Nat) (hjm : j ≤ m) :
    oneDescentGamma (d + 1) m j =
      oneDescentGamma d m j + oneDescentGamma d m (j + 1) := by
  unfold oneDescentGamma
  conv_lhs =>
    rw [Finset.Icc_eq_cons_Ioc hjm, Finset.sum_cons]
  conv_rhs =>
    rw [Finset.Icc_eq_cons_Ioc hjm, Finset.sum_cons]
  have hsucc : Finset.Icc (j + 1) m = Finset.Ioc j m := by grind
  have hhead :
      oneDescentGammaTerm (d + 1) m j j = oneDescentGammaTerm d m j j := by
    unfold oneDescentGammaTerm
    simp
  rw [hsucc, hhead, add_assoc]
  congr 1
  calc
    ∑ r ∈ Finset.Ioc j m, oneDescentGammaTerm (d + 1) m j r
      = ∑ r ∈ Finset.Ioc j m,
          (oneDescentGammaTerm d m j r + oneDescentGammaTerm d m (j + 1) r) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact oneDescentGammaTerm_succ d m j r (Finset.mem_Ioc.mp hr).1
    _ = (∑ r ∈ Finset.Ioc j m, oneDescentGammaTerm d m j r) +
          ∑ r ∈ Finset.Ioc j m, oneDescentGammaTerm d m (j + 1) r := by rw [Finset.sum_add_distrib]

@[simp] lemma oneDescentGamma_diag (d m : Nat) :
    oneDescentGamma d m m = 1 := by
  unfold oneDescentGamma
  rw [Finset.Icc_self, Finset.sum_singleton]
  simp [oneDescentGammaTerm]

lemma oneDescentGamma_one
    (m j : Nat) (hjm : j < m) :
    oneDescentGamma 1 m j =
      C ((Nat.choose m j : Nat) : ℝ) * X ^ (m - j - 1) *
        (X + C (((m - j : Nat) : ℝ) / ((j + 1 : Nat) : ℝ))) := by
  have hjm_le : j ≤ m := Nat.le_of_lt hjm
  have hj1m_le : j + 1 ≤ m := Nat.succ_le_of_lt hjm
  rw [oneDescentGamma_recurrence 0 m j hjm_le]
  rw [oneDescentGamma_zero m j hjm_le, oneDescentGamma_zero m (j + 1) hj1m_le]
  have hsub1 : m - (j + 1) = m - j - 1 := by lia
  rw [hsub1]
  have hpow : (X : ℝ[X]) ^ (m - j) = X ^ (m - j - 1) * X := by
    have hpred : Nat.succ (m - j - 1) - 1 = m - j - 1 := by lia
    rw [show m - j = Nat.succ (m - j - 1) by lia, pow_succ, hpred]
  rw [hpow]
  have hchoose :
      C ((Nat.choose m (j + 1) : Nat) : ℝ) =
        C ((Nat.choose m j : Nat) : ℝ) *
          C ((((m - j : Nat) : ℝ) / ((j + 1 : Nat) : ℝ))) := by
    rw [choose_cast_succ_eq_ratio, C_mul]
  grind

lemma oneDescentQ_zero (m : Nat) :
    oneDescentQ 0 m = X ^ m - oneDescentCorrection m := by
  unfold oneDescentQ
  rw [oneDescentGamma_zero m 0 (Nat.zero_le m)]
  simp

lemma oneDescentQ_recurrence (d m : Nat) :
    oneDescentQ (d + 1) m =
      oneDescentQ d m + oneDescentGamma d m 1 := by
  unfold oneDescentQ
  rw [oneDescentGamma_recurrence d m 0 (Nat.zero_le m)]
  ring

lemma oneDescentQ_one_succ (m : Nat) :
    oneDescentQ 1 (m + 1) = X ^ m * (X + C (m : ℝ)) := by
  rw [oneDescentQ_recurrence 0 (m + 1), oneDescentQ_zero (m + 1),
    oneDescentGamma_zero (m + 1) 1 (Nat.succ_le_succ (Nat.zero_le m))]
  have hpow : (X : ℝ[X]) ^ (m + 1) = X * X ^ m := by grind
  rw [oneDescentCorrection_succ m, hpow]
  have hexp : m + 1 - 1 = m := by lia
  rw [hexp]
  have hchoose : C ((Nat.choose (m + 1) 1 : Nat) : ℝ) = C ((m + 1 : Nat) : ℝ) := by simp
  grind

lemma strictInterl_one_X_add_C (a : ℝ) :
    StrictInterl (1 : ℝ[X]) (X + C a) :=
  (interlaces_one_linear (p := X + C a) (by simp)).toStrictInterl

lemma oneDescentQ_one (m : Nat) (hm : 0 < m) :
    oneDescentQ 1 m = X ^ (m - 1) * (X + C ((m - 1 : Nat) : ℝ)) := by
  cases m with
  | zero =>
      lia
  | succ n =>
      simpa using oneDescentQ_one_succ n

lemma oneDescentGamma_adjacent_linearShift_le
    (m j : Nat) (hj : j + 1 < m) :
    (((m - (j + 1) : Nat) : ℝ) / ((j + 2 : Nat) : ℝ)) ≤
      (((m - j : Nat) : ℝ) / ((j + 1 : Nat) : ℝ)) := by
  have hj1_pos : 0 < ((j + 1 : Nat) : ℝ) := by positivity
  have hj2_pos : 0 < ((j + 2 : Nat) : ℝ) := by positivity
  have hstep : ((m - j : Nat) : ℝ) = ((m - (j + 1) : Nat) : ℝ) + 1 := by
    simpa [Nat.cast_add, Nat.cast_one] using
      congrArg (fun r : ℕ => (r : ℝ)) (show m - j = m - (j + 1) + 1 by lia)
  have hsucc : ((j + 2 : Nat) : ℝ) = ((j + 1 : Nat) : ℝ) + 1 := by grind
  field_simp [hj1_pos.ne', hj2_pos.ne']
  nlinarith [hstep, hsucc]

lemma oneDescent_strictInterl_gamma_one_top (m : Nat) (hm : 0 < m) :
    StrictInterl (oneDescentGamma 1 m m) (oneDescentGamma 1 m (m - 1)) := by
  have hpred_lt : m - 1 < m := by lia
  rw [oneDescentGamma_diag, oneDescentGamma_one m (m - 1) hpred_lt]
  have hpow0 : m - (m - 1) - 1 = 0 := by lia
  rw [hpow0, pow_zero]
  have hchoose_ne : (((Nat.choose m (m - 1) : Nat) : ℝ)) ≠ 0 :=
    Nat.cast_choose_ne_zero (R := ℝ) (Nat.sub_le m 1)
  have hstrictInterl :=
    StrictInterl.C_mul_right
      (strictInterl_one_X_add_C ((((m - (m - 1) : Nat) : ℝ) / (((m - 1) + 1 : Nat) : ℝ))))
      hchoose_ne
  lia

lemma oneDescent_strictInterl_gamma_one_adjacent
    (m j : Nat) (hj : j + 1 < m) :
    StrictInterl (oneDescentGamma 1 m (j + 1)) (oneDescentGamma 1 m j) := by
  rw [oneDescentGamma_one m (j + 1) hj, oneDescentGamma_one m j (by lia)]
  have hleft : m - (j + 1) - 1 = m - j - 2 := by lia
  have hright : m - j - 1 = m - j - 2 + 1 := by lia
  rw [hleft, hright]
  exact strictInterl_scaled_X_pow_affine
    (oneDescentGamma_linearShift_nonneg m (j + 1))
    (by simpa only [Nat.add_assoc] using oneDescentGamma_adjacent_linearShift_le m j hj)
    (Nat.cast_choose_ne_zero (R := ℝ) (by lia))
    (Nat.cast_choose_ne_zero (R := ℝ) (by lia)) _

lemma oneDescent_strictInterl_gamma_one_terminal (m : Nat) (hm : 1 < m) :
    StrictInterl (oneDescentGamma 1 m 1) (oneDescentQ 1 m) := by
  rw [oneDescentGamma_one m 1 hm, oneDescentQ_one m (by lia)]
  have hpow : (X : ℝ[X]) ^ (m - 1) = X ^ (m - 2 + 1) := by congr 1; lia
  have hleft : m - 1 - 1 = m - 2 := by lia
  rw [hpow, hleft]
  simpa only [Nat.cast_one, C_1, one_mul] using
    strictInterl_scaled_X_pow_affine (b := ((m - 1 : ℕ) : ℝ)) (e := 1)
      (oneDescentGamma_linearShift_nonneg m 1)
      (by norm_num)
      (Nat.cast_choose_ne_zero (R := ℝ) (by lia : 1 ≤ m)) one_ne_zero (m - 2)

/-- Uniform adjacent comparison in the base `d = 1` Gamma chain:
`Γ_{1,j+1}^{(m)} ≪ Γ_{1,j}^{(m)}` for every admissible `j`. -/
theorem oneDescent_strictInterl_gamma_one_adjacent_chain
    (m j : Nat) (hj : j < m) :
    StrictInterl (oneDescentGamma 1 m (j + 1)) (oneDescentGamma 1 m j) := by
  by_cases htop : j + 1 = m
  · rw [htop, show j = m - 1 by lia]
    exact oneDescent_strictInterl_gamma_one_top m (by lia)
  · have hj_strict : j + 1 < m := by lia
    exact oneDescent_strictInterl_gamma_one_adjacent m j hj_strict

/-- Terminal comparison in the base `d = 1` Gamma chain:
`Γ_{1,1}^{(m)} ≪ Q_1^{(m)}`. -/
theorem oneDescent_strictInterl_gamma_one_terminal_chain
    (m : Nat) (hm : 0 < m) :
    StrictInterl (oneDescentGamma 1 m 1) (oneDescentQ 1 m) := by
  by_cases hm_large : 1 < m
  · exact oneDescent_strictInterl_gamma_one_terminal m hm_large
  · have hm_eq : m = 1 := by lia
    subst hm_eq
    rw [oneDescentGamma_diag, oneDescentQ_one]
    · simpa using strictInterl_one_X_add_C (0 : ℝ)
    · lia

/-- Every polynomial in the base `d = 1` Gamma family is real-rooted. -/
theorem oneDescentGamma_one_isRealRooted
    (m j : Nat) (hj : j ≤ m) :
    ((oneDescentGamma 1 m j) ≠ 0 ∧ (oneDescentGamma 1 m j).Splits) := by
  by_cases htop : j = m
  · simp_all
  · have hjm : j < m := lt_of_le_of_ne hj htop
    rw [oneDescentGamma_one m j hjm]
    exact ⟨mul_ne_zero
      (mul_ne_zero (C_ne_zero.mpr (Nat.cast_choose_ne_zero (R := ℝ) hj))
        (pow_ne_zero _ X_ne_zero)) (X_add_C_ne_zero _),
      ((Splits.C _).mul (Splits.X.pow _)).mul (Splits.of_natDegree_le_one (by simp))⟩

/-- The base `d = 1` normalized one-descent polynomial is real-rooted. -/
theorem oneDescentQ_one_isRealRooted
    (m : Nat) (hm : 0 < m) : ((oneDescentQ 1 m) ≠ 0 ∧ (oneDescentQ 1 m).Splits) := by
  rw [oneDescentQ_one m hm]
  exact ⟨mul_ne_zero (pow_ne_zero _ X_ne_zero) (X_add_C_ne_zero _),
    (Splits.X.pow _).mul (Splits.of_natDegree_le_one (natDegree_X_add_C _).le)⟩

end RealRooted
