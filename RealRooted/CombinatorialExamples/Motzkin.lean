import RealRooted.CombinatorialExamples.Common
import Mathlib.Tactic

/-!
# Shifted Motzkin Polynomials

Interlacing and root-bound facts for the shifted Motzkin recurrence.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

/-- The right-endpoint shift in the Motzkin recurrence. -/
def motzkinShift : ℝ := 1 / 4

/-- The scalar coefficient of `M_{n+1}` in the shifted Motzkin recurrence. -/
def motzkinCoeffA (n : Nat) : ℝ :=
  ((2 * n + 5 : Nat) : ℝ) / (n + 4)

/-- The scalar coefficient of `(X - 1/4) M_n` in the shifted Motzkin recurrence. -/
def motzkinCoeffB (n : Nat) : ℝ :=
  ((4 * (n + 1) : Nat) : ℝ) / (n + 4)

/-- Shifted Motzkin polynomials: `motzkin n` is the Motzkin polynomial `M_{n+1}`
from the note, so the recursion starts at `n = 0, 1`. -/
def motzkin : Nat → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      C (motzkinCoeffA n) * motzkin (n + 1) +
        C (motzkinCoeffB n) * (X - C motzkinShift) * motzkin n

@[simp] lemma motzkin_zero : motzkin 0 = 1 := rfl

@[simp] lemma motzkin_one : motzkin 1 = 1 + X := rfl

lemma motzkin_succ_succ (n : Nat) :
    motzkin (n + 2) =
      C (motzkinCoeffA n) * motzkin (n + 1) +
        C (motzkinCoeffB n) * (X - C motzkinShift) * motzkin n := rfl

lemma coeff_X_sub_C_mul (r : ℝ) (m : Nat) (p : ℝ[X]) :
    coeff ((X - C r) * p) (m + 1) =
      coeff p m - r * coeff p (m + 1) := by
  rw [sub_mul, coeff_sub, coeff_X_mul]
  have hC : coeff (C r * p) (m + 1) = r * coeff p (m + 1) := by
    simp
  rw [hC]

lemma coeff_motzkin_succ_succ (n m : Nat) :
    coeff (motzkin (n + 2)) (m + 1) =
      motzkinCoeffA n * coeff (motzkin (n + 1)) (m + 1) +
        motzkinCoeffB n *
          (coeff (motzkin n) m - motzkinShift * coeff (motzkin n) (m + 1)) := by
  rw [motzkin_succ_succ, coeff_add]
  rw [show C (motzkinCoeffB n) * (X - C motzkinShift) * motzkin n =
      C (motzkinCoeffB n) * ((X - C motzkinShift) * motzkin n) by rw [mul_assoc]]
  have hA :
      coeff (C (motzkinCoeffA n) * motzkin (n + 1)) (m + 1) =
        motzkinCoeffA n * coeff (motzkin (n + 1)) (m + 1) := by
    simp
  have hB :
      coeff (C (motzkinCoeffB n) * ((X - C motzkinShift) * motzkin n)) (m + 1) =
        motzkinCoeffB n *
          coeff ((X - C motzkinShift) * motzkin n) (m + 1) := by
    simp
  rw [hA, hB, coeff_X_sub_C_mul]

lemma coeff_motzkin_top_pos_and_above :
    ∀ n : Nat,
      0 < coeff (motzkin n) ((n + 1) / 2) ∧
      ∀ m > (n + 1) / 2, coeff (motzkin n) m = 0
  | 0 => by
      constructor
      · simp [motzkin_zero]
      · intro m hm
        rw [motzkin_zero, coeff_one, if_neg hm.ne']
  | 1 => by
      constructor
      · rw [motzkin_one, coeff_add, coeff_one, coeff_X]
        norm_num
      · intro m hm
        cases m with
        | zero =>
            lia
        | succ k =>
            cases k with
            | zero =>
                lia
            | succ k =>
                rw [motzkin_one, coeff_add, coeff_one, coeff_X]
                simp
  | n + 2 => by
      rcases coeff_motzkin_top_pos_and_above n with ⟨hlow_top, hlow_above⟩
      rcases coeff_motzkin_top_pos_and_above (n + 1) with ⟨hprev_top, hprev_above⟩
      constructor
      · rw [show (n + 3) / 2 = ((n + 3) / 2 - 1) + 1 by lia, coeff_motzkin_succ_succ]
        rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
        · have hprev_pos :
              0 < coeff (motzkin (n + 1)) ((n + 3) / 2) := by
            have hprev_top' := hprev_top
            rw [show (n + 1 + 1) / 2 = (n + 3) / 2 by lia] at hprev_top'
            exact hprev_top'
          have hlow_pos :
              0 < coeff (motzkin n) ((n + 3) / 2 - 1) := by
            have hlow_top' := hlow_top
            rw [show (n + 1) / 2 = (n + 3) / 2 - 1 by lia] at hlow_top'
            exact hlow_top'
          have hlow_zero :
              coeff (motzkin n) ((n + 3) / 2) = 0 := by
            apply hlow_above
            lia
          have hcoeff_eq :
              ((n + 3) / 2 - 1 + 1 : Nat) = (n + 3) / 2 := by
            lia
          rw [hcoeff_eq, hlow_zero]
          have hA_pos : 0 < motzkinCoeffA n := by
            unfold motzkinCoeffA
            positivity
          have hB_pos : 0 < motzkinCoeffB n := by
            unfold motzkinCoeffB
            positivity
          have hshift_nonneg : 0 ≤ motzkinShift := by
            unfold motzkinShift
            positivity
          nlinarith
        · have hprev_zero :
              coeff (motzkin (n + 1)) ((n + 3) / 2) = 0 := by
            apply hprev_above
            lia
          have hlow_pos :
              0 < coeff (motzkin n) ((n + 3) / 2 - 1) := by
            simpa [show (n + 3) / 2 - 1 = (n + 1) / 2 by lia] using hlow_top
          have hlow_zero :
              coeff (motzkin n) ((n + 3) / 2) = 0 := by
            apply hlow_above
            lia
          have hcoeff_eq :
              ((n + 3) / 2 - 1 + 1 : Nat) = (n + 3) / 2 := by
            lia
          rw [hcoeff_eq, hprev_zero, hlow_zero]
          have hB_pos : 0 < motzkinCoeffB n := by
            unfold motzkinCoeffB
            positivity
          have hshift_nonneg : 0 ≤ motzkinShift := by
            unfold motzkinShift
            positivity
          nlinarith
      · intro m hm
        cases m with
        | zero =>
            lia
        | succ k =>
            rw [show k + 1 = k + 0 + 1 by lia, coeff_motzkin_succ_succ]
            have hprev_zero :
                coeff (motzkin (n + 1)) (k + 1) = 0 := by
              apply hprev_above
              lia
            have hlow_zero :
                coeff (motzkin n) k = 0 := by
              apply hlow_above
              lia
            have hlow_succ_zero :
                coeff (motzkin n) (k + 1) = 0 := by
              apply hlow_above
              lia
            simp [hprev_zero, hlow_zero, hlow_succ_zero]

lemma natDegree_motzkin (n : Nat) :
    (motzkin n).natDegree = (n + 1) / 2 := by
  rcases coeff_motzkin_top_pos_and_above n with ⟨htop, habove⟩
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)
  · exact ne_of_gt htop

lemma motzkin_nonzero (n : Nat) :
    motzkin n ≠ 0 := by
  rcases coeff_motzkin_top_pos_and_above n with ⟨htop, _⟩
  exact fun h0 => by simp [h0] at htop

lemma motzkin_posLeadingCoeff (n : Nat) :
    HasPosLeadingCoeff (motzkin n) := by
  unfold HasPosLeadingCoeff
  rw [leadingCoeff, natDegree_motzkin]
  exact (coeff_motzkin_top_pos_and_above n).1

lemma hasPosLeadingCoeff_C_mul_motzkin {a : ℝ} (ha : 0 < a) {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (C a * p) := by
  unfold HasPosLeadingCoeff at hp ⊢
  rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr ha.ne')]
  exact mul_pos ha hp

lemma prec_self_mul_X_sub_C_of_roots_le {r : ℝ} {f : ℝ[X]}
    (hf : f ≠ 0 ∧ f.roots.card = f.natDegree) (hf_pos : HasPosLeadingCoeff f)
    (hf_le : ∀ s ∈ f.roots, s ≤ r) :
    Prec f ((X - C r) * f) := by
  have hXf : (((X - C r) * f) ≠ 0 ∧ ((X - C r) * f).roots.card = ((X - C r) * f).natDegree) := by
    exact isRealRooted_mul (isRealRooted_X_sub_C r) hf
  have hXf_pos : HasPosLeadingCoeff ((X - C r) * f) :=
    hasPosLeadingCoeff_X_sub_C_mul hf_pos
  have hXf_le : ∀ s ∈ ((X - C r) * f).roots, s ≤ r :=
    roots_le_X_sub_C_mul hf hf_le
  have hdeg : f.natDegree + 1 = ((X - C r) * f).natDegree := by
    rw [natDegree_mul (X_sub_C_ne_zero r) hf.1, natDegree_X_sub_C]
    lia
  have hself : Prec ((X - C r) * f) ((X - C r) * f) := prec_refl hXf
  exact
    (prec_iff_prec_mul_X_sub_C_of_roots_le r hf hXf hf_pos hXf_pos hf_le hXf_le hdeg).mpr hself

lemma motzkin_bound_zero :
    ∀ r ∈ (motzkin 0).roots, r ≤ motzkinShift := by
  intro r hr
  have : False := by
    simp [motzkin_zero] at hr
  exact False.elim this

lemma motzkin_bound_one :
    ∀ r ∈ (motzkin 1).roots, r ≤ motzkinShift := by
  intro r hr
  have hr_root : (1 + X : ℝ[X]).IsRoot r := by
    simpa [motzkin_one] using (mem_roots (motzkin_nonzero 1)).mp hr
  have hr_eq : r = -1 := by
    rw [Polynomial.IsRoot.def, eval_add, eval_one, eval_X] at hr_root
    linarith
  rw [hr_eq, motzkinShift]
  norm_num

lemma prec_motzkin_zero_one :
    Prec (motzkin 0) (motzkin 1) := by
  simpa [motzkin_zero, motzkin_one] using
    (interlaces_one_linear (p := (1 + X : ℝ[X])) (by
      simpa [add_comm] using
        (Polynomial.natDegree_linear (a := (1 : ℝ)) (b := (1 : ℝ)) (by norm_num)))).toPrec

lemma prec_motzkin_shifted_succ {n : Nat}
    (hprev : Prec (motzkin n) (motzkin (n + 1)))
    (hle_n : ∀ r ∈ (motzkin n).roots, r ≤ motzkinShift)
    (hle_succ : ∀ r ∈ (motzkin (n + 1)).roots, r ≤ motzkinShift) :
    Prec (motzkin (n + 2)) ((X - C motzkinShift) * motzkin (n + 1)) := by
  have hscalarA_pos : 0 < motzkinCoeffA n := by
    unfold motzkinCoeffA
    positivity
  have hscalarB_pos : 0 < motzkinCoeffB n := by
    unfold motzkinCoeffB
    positivity
  have hleft :
      Prec (C (motzkinCoeffA n) * motzkin (n + 1))
        ((X - C motzkinShift) * motzkin (n + 1)) := by
    exact
      prec_C_mul_left
        (prec_self_mul_X_sub_C_of_roots_le
          hprev.2.1 (motzkin_posLeadingCoeff (n + 1)) hle_succ)
        hscalarA_pos.ne'
  have hright_core :
      Prec ((X - C motzkinShift) * motzkin n)
        ((X - C motzkinShift) * motzkin (n + 1)) := by
    exact prec_mul_X_sub_C_both_of_roots_le motzkinShift hprev hle_n hle_succ
  have hright :
      Prec (C (motzkinCoeffB n) * ((X - C motzkinShift) * motzkin n))
        ((X - C motzkinShift) * motzkin (n + 1)) := by
    exact prec_C_mul_left hright_core hscalarB_pos.ne'
  have hleft_pos :
      HasPosLeadingCoeff (C (motzkinCoeffA n) * motzkin (n + 1)) :=
    hasPosLeadingCoeff_C_mul_motzkin hscalarA_pos (motzkin_posLeadingCoeff (n + 1))
  have hright_pos :
      HasPosLeadingCoeff
        (C (motzkinCoeffB n) * ((X - C motzkinShift) * motzkin n)) :=
    hasPosLeadingCoeff_C_mul_motzkin hscalarB_pos
      (hasPosLeadingCoeff_X_sub_C_mul (motzkin_posLeadingCoeff n))
  have hsum :
      Prec
        (C (motzkinCoeffA n) * motzkin (n + 1) +
          C (motzkinCoeffB n) * ((X - C motzkinShift) * motzkin n))
        ((X - C motzkinShift) * motzkin (n + 1)) :=
    prec_add_of_prec_right_of_posLeadingCoeff hleft hright hleft_pos hright_pos
  simpa [motzkin_succ_succ, add_comm, add_left_comm, add_assoc, mul_assoc] using hsum

lemma prec_motzkin_succ_of_shifted_even {n : Nat} (heven : n % 2 = 0)
    (hshift : Prec (motzkin (n + 1)) ((X - C motzkinShift) * motzkin n))
    (hle_n : ∀ r ∈ (motzkin n).roots, r ≤ motzkinShift)
    (hle_succ : ∀ r ∈ (motzkin (n + 1)).roots, r ≤ motzkinShift) :
    Prec (motzkin n) (motzkin (n + 1)) := by
  have hf : ((motzkin n) ≠ 0 ∧ (motzkin n).roots.card = (motzkin n).natDegree) := by
    exact
      isRealRooted_of_dvd hshift.2.1 (motzkin_nonzero n)
        ⟨X - C motzkinShift, by rw [mul_comm]⟩
  have hg : ((motzkin (n + 1)) ≠ 0 ∧ (motzkin (n + 1)).roots.card = (motzkin (n + 1)).natDegree) := hshift.1
  have hdeg : (motzkin n).natDegree + 1 = (motzkin (n + 1)).natDegree := by
    rw [natDegree_motzkin, natDegree_motzkin]
    lia
  exact
    (prec_iff_prec_mul_X_sub_C_of_roots_le motzkinShift
      hf hg (motzkin_posLeadingCoeff n) (motzkin_posLeadingCoeff (n + 1))
      hle_n hle_succ hdeg).mpr hshift

lemma prec_motzkin_succ_of_shifted_odd {n : Nat} (hodd : n % 2 = 1)
    (hshift : Prec (motzkin (n + 1)) ((X - C motzkinShift) * motzkin n))
    (hle_n : ∀ r ∈ (motzkin n).roots, r ≤ motzkinShift) :
    Prec (motzkin n) (motzkin (n + 1)) := by
  set f' := (motzkin n).comp (X + C motzkinShift)
  set g' := (motzkin (n + 1)).comp (X + C motzkinShift)
  have hshift' : Prec g' (X * f') := by
    have htmp := (prec_comp_X_add_C hshift motzkinShift)
    simpa [f', g', mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg, comp_assoc,
      add_assoc, add_left_comm, add_comm, mul_assoc] using htmp
  have hf'_nonpos : ∀ s ∈ f'.roots, s ≤ 0 := by
    intro s hs
    simp only [f', roots_comp_X_add_C motzkinShift] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    linarith [hle_n t ht]
  have hdeg' : f'.natDegree = g'.natDegree := by
    rw [show f' = (motzkin n).comp (X + C motzkinShift) by rfl,
      show g' = (motzkin (n + 1)).comp (X + C motzkinShift) by rfl]
    simp [natDegree_comp, natDegree_motzkin]
    lia
  have hprec' :
      Prec f' g' :=
    prec_of_prec_mul_X_of_sameDegree_of_roots_nonpos hshift' hdeg' hf'_nonpos
  exact (prec_comp_X_add_C_iff (f := motzkin n) (g := motzkin (n + 1)) motzkinShift).1 hprec'

/-- Consecutive Motzkin polynomials satisfy the generalized interlacing relation `Prec`. -/
theorem prec_motzkin_succ_and_roots_le :
    ∀ n : Nat,
      Prec (motzkin n) (motzkin (n + 1)) ∧
      (∀ r ∈ (motzkin n).roots, r ≤ motzkinShift) ∧
      (∀ r ∈ (motzkin (n + 1)).roots, r ≤ motzkinShift)
  | 0 => by
      exact ⟨prec_motzkin_zero_one, motzkin_bound_zero, motzkin_bound_one⟩
  | n + 1 => by
      rcases prec_motzkin_succ_and_roots_le n with ⟨hprev, hle_n, hle_succ⟩
      have hshift :
          Prec (motzkin (n + 2)) ((X - C motzkinShift) * motzkin (n + 1)) :=
        prec_motzkin_shifted_succ hprev hle_n hle_succ
      have hright_le :
          ∀ r ∈ ((X - C motzkinShift) * motzkin (n + 1)).roots, r ≤ motzkinShift :=
        roots_le_X_sub_C_mul hprev.2.1 hle_succ
      have hle_next :
          ∀ r ∈ (motzkin (n + 2)).roots, r ≤ motzkinShift :=
        roots_le_of_prec_right hshift hright_le
      have hnext : Prec (motzkin (n + 1)) (motzkin (n + 2)) := by
        rcases Nat.mod_two_eq_zero_or_one (n + 1) with hpar | hpar
        · exact prec_motzkin_succ_of_shifted_even hpar hshift hle_succ hle_next
        · exact prec_motzkin_succ_of_shifted_odd hpar hshift hle_succ
      exact ⟨hnext, hle_succ, hle_next⟩

theorem prec_motzkin_succ (n : Nat) :
    Prec (motzkin n) (motzkin (n + 1)) :=
  (prec_motzkin_succ_and_roots_le n).1

theorem roots_le_motzkinShift_motzkin (n : Nat) :
    ∀ r ∈ (motzkin n).roots, r ≤ motzkinShift :=
  (prec_motzkin_succ_and_roots_le n).2.1

theorem isRealRooted_motzkin : ∀ n : Nat, ((motzkin n) ≠ 0 ∧ (motzkin n).roots.card = (motzkin n).natDegree)
  | 0 => by
      simpa [motzkin_zero] using
        isRealRooted_of_deg_zero (p := (1 : ℝ[X])) one_ne_zero (by simp)
  | n + 1 => (prec_motzkin_succ n).2.1

theorem interlaces_motzkin_succ_of_even {n : Nat} (heven : n % 2 = 0) :
    Interlaces (motzkin n) (motzkin (n + 1)) := by
  apply (prec_motzkin_succ n).toInterlaces
  rw [natDegree_motzkin, natDegree_motzkin]
  lia

/-- The descending prefix `[M_n, M_{n-1}, ..., M_1]` of the shifted Motzkin sequence. -/
def motzkinPrefix : Nat → List ℝ[X]
  | 0 => [motzkin 0]
  | n + 1 => motzkin (n + 1) :: motzkinPrefix n

@[simp] lemma motzkinPrefix_zero :
    motzkinPrefix 0 = [motzkin 0] := rfl

@[simp] lemma motzkinPrefix_succ (n : Nat) :
    motzkinPrefix (n + 1) = motzkin (n + 1) :: motzkinPrefix n := rfl

theorem isGeneralizedSturmSeq_motzkinPrefix :
    ∀ n : Nat, IsGeneralizedSturmSeq (motzkinPrefix n) := by
  intro n
  induction n with
  | zero =>
      simp [motzkinPrefix, IsGeneralizedSturmSeq]
  | succ n ih =>
      cases n with
      | zero =>
          simpa [motzkinPrefix, IsGeneralizedSturmSeq] using prec_motzkin_zero_one
      | succ n =>
          simpa [motzkinPrefix, IsGeneralizedSturmSeq] using
            And.intro (prec_motzkin_succ (n + 1)) ih

end
end RealRooted
