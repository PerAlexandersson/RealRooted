import RealRooted.Basic
import RealRooted.CombinatorialExamples.Common
import RealRooted.Linear
import RealRooted.MaWang
import RealRooted.Wagner
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# One-Descent Gamma Family

Base-case interlacing and real-rootedness facts for the normalized one-descent
gamma polynomials.
-/

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
  have hj1_ne : ((j + 1 : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero j)
  rw [← mul_div_assoc]
  apply (eq_div_iff hj1_ne).2
  exact_mod_cast (Nat.choose_succ_right_eq m j)

lemma oneDescentGamma_linearShift_nonneg (m j : Nat) :
    0 ≤ (((m - j : Nat) : ℝ) / ((j + 1 : Nat) : ℝ)) := by
  positivity

lemma hasNonnegCoeffs_X_add_C {t : ℝ} (ht : 0 ≤ t) :
    HasNonnegCoeffs (X + C t) := by
  simpa [sub_eq_add_neg] using
    (hasNonnegCoeffs_X_sub_C (r := -t) (by linarith : -t ≤ 0))

lemma oneDescent_hasNonnegCoeffs_X : HasNonnegCoeffs (X : ℝ[X]) := by
  intro n
  cases n with
  | zero =>
      simp [coeff_X_zero]
  | succ n =>
      cases n with
      | zero =>
          simp [coeff_X]
      | succ n =>
          simp [coeff_X]

lemma isRealRooted_X_pow : ∀ n : Nat, (((X : ℝ[X]) ^ n) ≠ 0 ∧ ((X : ℝ[X]) ^ n).Splits) := by
  simp

lemma prec_X_add_C_to_X_mul_X_add_C {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    Prec (X + C a) (X * (X + C b)) := by
  have hdeg_a : (X + C a).natDegree = 1 := by
    rw [show X + C a = C (1 : ℝ) * X + C a by simp]
    exact Polynomial.natDegree_linear (a := (1 : ℝ)) (b := a) one_ne_zero
  have hdeg_b : (X + C b).natDegree = 1 := by
    rw [show X + C b = C (1 : ℝ) * X + C b by simp]
    exact Polynomial.natDegree_linear (a := (1 : ℝ)) (b := b) one_ne_zero
  have hrr_a : ((X + C a) ≠ 0 ∧ (X + C a).Splits) := isRealRooted_of_degree_one hdeg_a
  have hrr_b : ((X + C b) ≠ 0 ∧ (X + C b).Splits) := isRealRooted_of_degree_one hdeg_b
  have hrr_q : ((X * (X + C b)) ≠ 0 ∧ (X * (X + C b)).Splits) := isRealRooted_X_mul hrr_b
  have hdeg_q : (X * (X + C b)).natDegree = 2 := by
    rw [natDegree_mul X_ne_zero hrr_b.1, hdeg_b]
    norm_num
  have hb_nonneg : 0 ≤ b := by
    linarith
  have hrs_sorted : ([-b, (0 : ℝ)] : List ℝ).Pairwise (· ≤ ·) := by
    simp [hb_nonneg]
  have hss_sorted : ([-a] : List ℝ).Pairwise (· ≤ ·) := by
    simp
  have hrs_eq : (↑([-b, (0 : ℝ)] : List ℝ) : Multiset ℝ) = (X * (X + C b)).roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hrr_b.1), roots_X]
    have hlin_roots : (X + C b).roots = {(-b : ℝ)} := by
      rw [show X + C b = X - C (-b) by simp [sub_eq_add_neg], roots_X_sub_C]
    rw [hlin_roots]
    rw [Multiset.add_comm]
    rfl
  have hss_eq : (↑([-a] : List ℝ) : Multiset ℝ) = (X + C a).roots := by
    rw [show X + C a = X - C (-a) by simp [sub_eq_add_neg], roots_X_sub_C]
    rfl
  have hint : ListInterlaces ([-a] : List ℝ) [-b, (0 : ℝ)] := by
    change -b ≤ -a ∧ -a ≤ (0 : ℝ) ∧ True
    constructor
    · linarith
    constructor
    · linarith
    · trivial
  exact
    (show Interlaces (X + C a) (X * (X + C b)) by
      refine ⟨hrr_q, hrr_a, ?_, ?_⟩
      · simp [hdeg_a, hdeg_q]
      · exact ⟨[-b, (0 : ℝ)], [-a], hrs_sorted, hss_sorted, hrs_eq, hss_eq, hint⟩).toPrec

lemma oneDescentGammaTerm_succ
    (d m j r : Nat) (hjr : j < r) :
    oneDescentGammaTerm (d + 1) m j r =
      oneDescentGammaTerm d m j r + oneDescentGammaTerm d m (j + 1) r := by
  unfold oneDescentGammaTerm
  have hrj : r - j = (r - (j + 1)) + 1 := by
    lia
  rw [hrj, Nat.choose_succ_succ', Nat.mul_add]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  rw [C_add, add_mul]
  simp [add_comm]

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
    have hchoose : Nat.choose 0 (r - j) = 0 := by
      exact Nat.choose_eq_zero_of_lt (Nat.sub_pos_of_lt hjr)
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
  have hsucc : Finset.Icc (j + 1) m = Finset.Ioc j m := by
    simpa [Nat.succ_eq_add_one] using (Finset.Icc_succ_left_eq_Ioc j m)
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
          ∑ r ∈ Finset.Ioc j m, oneDescentGammaTerm d m (j + 1) r := by
            rw [Finset.sum_add_distrib]

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
  have hsub1 : m - (j + 1) = m - j - 1 := by
    lia
  rw [hsub1]
  have hpow : (X : ℝ[X]) ^ (m - j) = X ^ (m - j - 1) * X := by
    have hpred : Nat.succ (m - j - 1) - 1 = m - j - 1 := by
      simp
    rw [show m - j = Nat.succ (m - j - 1) by lia, pow_succ, hpred]
  rw [hpow]
  have hchoose :
      C ((Nat.choose m (j + 1) : Nat) : ℝ) =
        C ((Nat.choose m j : Nat) : ℝ) *
          C ((((m - j : Nat) : ℝ) / ((j + 1 : Nat) : ℝ))) := by
    rw [choose_cast_succ_eq_ratio, C_mul]
  calc
    C ((Nat.choose m j : Nat) : ℝ) * (X ^ (m - j - 1) * X) +
        C ((Nat.choose m (j + 1) : Nat) : ℝ) * X ^ (m - j - 1)
      = C ((Nat.choose m j : Nat) : ℝ) * X ^ (m - j - 1) * X +
          C ((Nat.choose m (j + 1) : Nat) : ℝ) * X ^ (m - j - 1) := by
            ring
    _ = C ((Nat.choose m j : Nat) : ℝ) * X ^ (m - j - 1) * X +
          (C ((Nat.choose m j : Nat) : ℝ) *
            C ((((m - j : Nat) : ℝ) / ((j + 1 : Nat) : ℝ)))) * X ^ (m - j - 1) := by
            rw [hchoose]
    _ = C ((Nat.choose m j : Nat) : ℝ) * X ^ (m - j - 1) *
          (X + C (((m - j : Nat) : ℝ) / ((j + 1 : Nat) : ℝ))) := by
            ring

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
  have hpow : (X : ℝ[X]) ^ (m + 1) = X * X ^ m := by
    rw [pow_succ']
  rw [oneDescentCorrection_succ m, hpow]
  have hexp : m + 1 - 1 = m := by
    lia
  rw [hexp]
  have hchoose : C ((Nat.choose (m + 1) 1 : Nat) : ℝ) = C ((m + 1 : Nat) : ℝ) := by
    rw [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
  rw [hchoose]
  rw [Nat.cast_add, Nat.cast_one, C_add, C_1]
  ring

lemma prec_one_X_add_C (a : ℝ) :
    Prec (1 : ℝ[X]) (X + C a) := by
  have hdeg : (X + C a).natDegree = 1 := by
    rw [show X + C a = C (1 : ℝ) * X + C a by simp]
    exact Polynomial.natDegree_linear (a := (1 : ℝ)) (b := a) one_ne_zero
  exact (interlaces_one_linear (p := X + C a) hdeg).toPrec

lemma oneDescentQ_one (m : Nat) (hm : 0 < m) :
    oneDescentQ 1 m = X ^ (m - 1) * (X + C ((m - 1 : Nat) : ℝ)) := by
  cases m with
  | zero =>
      cases hm
  | succ n =>
      simpa using oneDescentQ_one_succ n

lemma oneDescentGamma_adjacent_linearShift_le
    (m j : Nat) (hj : j + 1 < m) :
    (((m - (j + 1) : Nat) : ℝ) / ((j + 2 : Nat) : ℝ)) ≤
      (((m - j : Nat) : ℝ) / ((j + 1 : Nat) : ℝ)) := by
  have hj1_pos : 0 < ((j + 1 : Nat) : ℝ) := by
    positivity
  have hj2_pos : 0 < ((j + 2 : Nat) : ℝ) := by
    positivity
  have hstep : ((m - j : Nat) : ℝ) = ((m - (j + 1) : Nat) : ℝ) + 1 := by
    exact_mod_cast (show m - j = m - (j + 1) + 1 by lia)
  have hsucc : ((j + 2 : Nat) : ℝ) = ((j + 1 : Nat) : ℝ) + 1 := by
    exact_mod_cast (show j + 2 = (j + 1) + 1 by lia)
  field_simp [hj1_pos.ne', hj2_pos.ne']
  nlinarith [hstep, hsucc]

lemma oneDescent_prec_gamma_one_top (m : Nat) (hm : 0 < m) :
    Prec (oneDescentGamma 1 m m) (oneDescentGamma 1 m (m - 1)) := by
  have hpred_lt : m - 1 < m := by
    lia
  rw [oneDescentGamma_diag, oneDescentGamma_one m (m - 1) hpred_lt]
  have hpow0 : m - (m - 1) - 1 = 0 := by
    lia
  rw [hpow0, pow_zero]
  have hchoose_ne : (((Nat.choose m (m - 1) : Nat) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (Nat.sub_le m 1)
  have hprec :=
    prec_C_mul_right
      (prec_one_X_add_C ((((m - (m - 1) : Nat) : ℝ) / (((m - 1) + 1 : Nat) : ℝ))))
      hchoose_ne
  simpa [pow_zero, mul_assoc, mul_left_comm, mul_comm] using hprec

lemma oneDescent_prec_gamma_one_adjacent
    (m j : Nat) (hj : j + 1 < m) :
    Prec (oneDescentGamma 1 m (j + 1)) (oneDescentGamma 1 m j) := by
  have hjm : j < m := by
    lia
  have hsub_left : m - (j + 1) - 1 = m - j - 2 := by
    lia
  have hpow : (X : ℝ[X]) ^ (m - j - 1) = X ^ (m - j - 2) * X := by
    rw [show m - j - 1 = Nat.succ (m - j - 2) by lia, pow_succ]
  let a : ℝ := (((m - (j + 1) : Nat) : ℝ) / ((((j + 1) + 1 : Nat) : ℝ)))
  let b : ℝ := (((m - j : Nat) : ℝ) / ((j + 1 : Nat) : ℝ))
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.cast_add, Nat.cast_one] using
      oneDescentGamma_adjacent_linearShift_le m j hj
  have hbase : Prec (X + C a) (X * (X + C b)) :=
    prec_X_add_C_to_X_mul_X_add_C ha hab
  have hleft_ne : (((Nat.choose m (j + 1) : Nat) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (Nat.le_of_lt hj)
  have hright_ne : (((Nat.choose m j : Nat) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (Nat.le_of_lt hjm)
  have hscaled :
      Prec
        (C ((Nat.choose m (j + 1) : Nat) : ℝ) * (X + C a))
        (C ((Nat.choose m j : Nat) : ℝ) * (X * (X + C b))) := by
    exact prec_C_mul_right (prec_C_mul_left hbase hleft_ne) hright_ne
  have hpow_rr : (((X : ℝ[X]) ^ (m - j - 2)) ≠ 0 ∧ ((X : ℝ[X]) ^ (m - j - 2)).Splits) :=
    isRealRooted_X_pow (m - j - 2)
  rw [oneDescentGamma_one m (j + 1) hj, oneDescentGamma_one m j hjm, hsub_left, hpow]
  simpa [a, b, mul_assoc, mul_left_comm, mul_comm] using
    (prec_mul_common_factor hpow_rr hscaled)

lemma oneDescent_prec_gamma_one_terminal (m : Nat) (hm : 1 < m) :
    Prec (oneDescentGamma 1 m 1) (oneDescentQ 1 m) := by
  have hm_pos : 0 < m := by
    lia
  have hpow : (X : ℝ[X]) ^ (m - 1) = X ^ (m - 2) * X := by
    rw [show m - 1 = Nat.succ (m - 2) by lia, pow_succ]
  let a : ℝ := (((m - 1 : Nat) : ℝ) / (((1 + 1 : Nat) : ℝ)))
  let b : ℝ := ((m - 1 : Nat) : ℝ)
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    have hm1_nonneg : 0 ≤ ((m - 1 : Nat) : ℝ) := by
      positivity
    nlinarith
  have hbase : Prec (X + C a) (X * (X + C b)) := by
    exact prec_X_add_C_to_X_mul_X_add_C ha hab
  have hchoose_ne : (((Nat.choose m 1 : Nat) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show 1 ≤ m by lia)
  have hscaled :
      Prec
        (C ((Nat.choose m 1 : Nat) : ℝ) * (X + C a))
        (X * (X + C b)) := by
    exact prec_C_mul_left hbase hchoose_ne
  have hpow_rr : (((X : ℝ[X]) ^ (m - 2)) ≠ 0 ∧ ((X : ℝ[X]) ^ (m - 2)).Splits) :=
    isRealRooted_X_pow (m - 2)
  rw [oneDescentGamma_one m 1 hm, oneDescentQ_one m hm_pos, hpow]
  simpa [a, b, Nat.choose_one_right, mul_assoc, mul_left_comm, mul_comm] using
    (prec_mul_common_factor hpow_rr hscaled)

/-- Uniform adjacent comparison in the base `d = 1` Gamma chain:
`Γ_{1,j+1}^{(m)} ≪ Γ_{1,j}^{(m)}` for every admissible `j`. -/
theorem oneDescent_prec_gamma_one_adjacent_chain
    (m j : Nat) (hj : j < m) :
    Prec (oneDescentGamma 1 m (j + 1)) (oneDescentGamma 1 m j) := by
  by_cases htop : j + 1 = m
  · have hm_pos : 0 < m := by lia
    have hj_eq : j = m - 1 := by lia
    rw [htop, hj_eq]
    exact oneDescent_prec_gamma_one_top m hm_pos
  · have hj_strict : j + 1 < m := by lia
    exact oneDescent_prec_gamma_one_adjacent m j hj_strict

/-- Terminal comparison in the base `d = 1` Gamma chain:
`Γ_{1,1}^{(m)} ≪ Q_1^{(m)}`. -/
theorem oneDescent_prec_gamma_one_terminal_chain
    (m : Nat) (hm : 0 < m) :
    Prec (oneDescentGamma 1 m 1) (oneDescentQ 1 m) := by
  by_cases hm_large : 1 < m
  · exact oneDescent_prec_gamma_one_terminal m hm_large
  · have hm_eq : m = 1 := by lia
    subst hm_eq
    rw [oneDescentGamma_diag, oneDescentQ_one]
    · simpa using prec_one_X_add_C (0 : ℝ)
    · norm_num

/-- Every polynomial in the base `d = 1` Gamma family is real-rooted. -/
theorem oneDescentGamma_one_isRealRooted
    (m j : Nat) (hj : j ≤ m) : ((oneDescentGamma 1 m j) ≠ 0 ∧ (oneDescentGamma 1 m j).Splits) := by
  by_cases htop : j = m
  · subst htop
    simp
  · have hjm : j < m := lt_of_le_of_ne hj htop
    rw [oneDescentGamma_one m j hjm]
    let a : ℝ := (((m - j : Nat) : ℝ) / ((j + 1 : Nat) : ℝ))
    have hlin_deg : (X + C a).natDegree = 1 := by
      simp
    have hlin_rr : ((X + C a) ≠ 0 ∧ (X + C a).Splits) := isRealRooted_of_degree_one hlin_deg
    have hprod_rr : ((X ^ (m - j - 1) * (X + C a)) ≠ 0 ∧ (X ^ (m - j - 1) * (X + C a)).Splits) :=
      isRealRooted_mul (isRealRooted_X_pow (m - j - 1)) hlin_rr
    have hchoose_ne : (((Nat.choose m j : Nat) : ℝ)) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hj
    simpa [a, mul_assoc] using
      isRealRooted_C_mul hprod_rr hchoose_ne

/-- The base `d = 1` normalized one-descent polynomial is real-rooted. -/
theorem oneDescentQ_one_isRealRooted
    (m : Nat) (hm : 0 < m) : ((oneDescentQ 1 m) ≠ 0 ∧ (oneDescentQ 1 m).Splits) := by
  rw [oneDescentQ_one m hm]
  let a : ℝ := ((m - 1 : Nat) : ℝ)
  have hlin_deg : (X + C a).natDegree = 1 := by
    simp
  have hlin_rr : ((X + C a) ≠ 0 ∧ (X + C a).Splits) := isRealRooted_of_degree_one hlin_deg
  simpa [a] using
    isRealRooted_mul (isRealRooted_X_pow (m - 1)) hlin_rr

end RealRooted
