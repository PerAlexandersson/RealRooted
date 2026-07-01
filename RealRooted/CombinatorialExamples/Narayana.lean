import RealRooted.MaWang
import RealRooted.Linear
import RealRooted.CombinatorialExamples.Common
import Mathlib.Tactic

/-!
# Narayana Polynomials

Conditional Liu--Wang/Sturm-sequence package for Narayana polynomials, proved
through the quotient sequence obtained by removing the common `X` factor.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The linear coefficient block in the normalized Narayana recurrence. -/
def narayanaCoeffA (n : Nat) : ℝ[X] :=
  C (((2 * n + 3 : ℝ) / (n + 3 : ℝ))) * (1 + X)

/-- The quadratic coefficient block in the normalized Narayana recurrence. -/
def narayanaCoeffB (n : Nat) : ℝ[X] :=
  C ((-(n : ℝ)) / (n + 3 : ℝ)) * (1 - X) ^ 2

/-- The quotient Narayana sequence `Q_n = P_n / X`, defined recursively from

`(n+3) Q_{n+2} = (2n+3) (1 + X) Q_{n+1} - n (1 - X)^2 Q_n`

with `Q_1 = 1`. -/
def narayanaQuot : Nat → ℝ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => narayanaCoeffA n * narayanaQuot (n + 1) + narayanaCoeffB n * narayanaQuot n

/-- The original Narayana sequence `P_n = X * Q_n`. -/
def narayana (n : Nat) : ℝ[X] :=
  X * narayanaQuot n

@[simp] lemma narayanaQuot_zero : narayanaQuot 0 = 0 := rfl

@[simp] lemma narayanaQuot_one : narayanaQuot 1 = 1 := rfl

@[simp] lemma narayanaQuot_succ_succ (n : Nat) :
    narayanaQuot (n + 2) =
      narayanaCoeffA n * narayanaQuot (n + 1) + narayanaCoeffB n * narayanaQuot n := by
  simp [narayanaQuot]

@[simp] lemma narayana_zero : narayana 0 = 0 := by
  simp [narayana]

@[simp] lemma narayana_one : narayana 1 = X := by
  simp [narayana]

lemma narayanaQuot_two : narayanaQuot 2 = 1 + X := by
  simp [narayanaQuot, narayanaCoeffA, narayanaCoeffB]

lemma narayana_two : narayana 2 = X + X ^ 2 := by
  rw [narayana, narayanaQuot_two]
  ring

lemma narayana_succ_succ (n : Nat) :
    narayana (n + 2) =
      narayanaCoeffA n * narayana (n + 1) + narayanaCoeffB n * narayana n := by
  rw [narayana, narayana, narayana, narayanaQuot_succ_succ]
  ring

private lemma narayanaCoeffA_natDegree (n : Nat) :
    (narayanaCoeffA n).natDegree = 1 := by
  unfold narayanaCoeffA
  rw [mul_add, mul_one]
  simpa [add_comm] using
    (Polynomial.natDegree_linear
      (a := (((2 * n + 3 : ℝ) / (n + 3 : ℝ))))
      (b := (((2 * n + 3 : ℝ) / (n + 3 : ℝ))))
      (by positivity))

private lemma narayanaCoeffA_leadingCoeff (n : Nat) :
    (narayanaCoeffA n).leadingCoeff = ((2 * n + 3 : ℝ) / (n + 3 : ℝ)) := by
  unfold narayanaCoeffA
  rw [mul_add, mul_one]
  simpa [add_comm] using
    (Polynomial.leadingCoeff_linear
      (a := (((2 * n + 3 : ℝ) / (n + 3 : ℝ))))
      (b := (((2 * n + 3 : ℝ) / (n + 3 : ℝ))))
      (by positivity))

private lemma natDegree_one_sub_X :
    ((1 - X : ℝ[X])).natDegree = 1 := by
  simpa [sub_eq_add_neg, add_comm] using
    (Polynomial.natDegree_linear (a := (-1 : ℝ)) (b := (1 : ℝ)) (by simp))

private lemma leadingCoeff_one_sub_X :
    ((1 - X : ℝ[X])).leadingCoeff = -1 := by
  simpa [sub_eq_add_neg, add_comm] using
    (Polynomial.leadingCoeff_linear (a := (-1 : ℝ)) (b := (1 : ℝ)) (by simp))

private lemma natDegree_one_sub_X_sq :
    ((1 - X : ℝ[X]) ^ 2).natDegree = 2 := by
  have hmul_ne :
      ((1 - X : ℝ[X])).leadingCoeff * ((1 - X : ℝ[X])).leadingCoeff ≠ 0 := by
    simp [leadingCoeff_one_sub_X]
  rw [pow_two, natDegree_mul' hmul_ne, natDegree_one_sub_X]

private lemma leadingCoeff_one_sub_X_sq :
    ((1 - X : ℝ[X]) ^ 2).leadingCoeff = 1 := by
  have hmul_ne :
      ((1 - X : ℝ[X])).leadingCoeff * ((1 - X : ℝ[X])).leadingCoeff ≠ 0 := by
    simp [leadingCoeff_one_sub_X]
  rw [pow_two, leadingCoeff_mul' hmul_ne, leadingCoeff_one_sub_X]
  norm_num

private lemma narayanaCoeffB_natDegree (n : Nat) (hn : 1 ≤ n) :
    (narayanaCoeffB n).natDegree = 2 := by
  unfold narayanaCoeffB
  have hcoeff_ne : ((-(n : ℝ)) / (n + 3 : ℝ)) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast Nat.ne_of_gt hn)) (by positivity)
  have hmul_ne :
      (C ((-(n : ℝ)) / (n + 3 : ℝ))).leadingCoeff *
        ((1 - X : ℝ[X]) ^ 2).leadingCoeff ≠ 0 := by
    rw [leadingCoeff_C, leadingCoeff_one_sub_X_sq]
    simpa using hcoeff_ne
  rw [natDegree_mul' hmul_ne, natDegree_C, natDegree_one_sub_X_sq]

private lemma narayanaCoeffB_leadingCoeff (n : Nat) (hn : 1 ≤ n) :
    (narayanaCoeffB n).leadingCoeff = ((-(n : ℝ)) / (n + 3 : ℝ)) := by
  unfold narayanaCoeffB
  have hcoeff_ne : ((-(n : ℝ)) / (n + 3 : ℝ)) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast Nat.ne_of_gt hn)) (by positivity)
  have hmul_ne :
      (C ((-(n : ℝ)) / (n + 3 : ℝ))).leadingCoeff *
        ((1 - X : ℝ[X]) ^ 2).leadingCoeff ≠ 0 := by
    rw [leadingCoeff_C, leadingCoeff_one_sub_X_sq]
    simpa using hcoeff_ne
  rw [leadingCoeff_mul' hmul_ne, leadingCoeff_C, leadingCoeff_one_sub_X_sq]
  lia

private lemma natDegree_leadingCoeff_narayanaQuot_step (n : Nat) (hn : 1 ≤ n)
    (hdeg_succ : (narayanaQuot (n + 1)).natDegree = n)
    (hlc_succ : (narayanaQuot (n + 1)).leadingCoeff = 1)
    (hdeg : (narayanaQuot n).natDegree = n - 1)
    (hlc : (narayanaQuot n).leadingCoeff = 1) :
    (narayanaQuot (n + 2)).natDegree = n + 1 ∧
      (narayanaQuot (n + 2)).leadingCoeff = 1 := by
  let A : ℝ[X] := narayanaCoeffA n * narayanaQuot (n + 1)
  let B : ℝ[X] := narayanaCoeffB n * narayanaQuot n
  have hA_lc_ne : (narayanaCoeffA n).leadingCoeff * (narayanaQuot (n + 1)).leadingCoeff ≠ 0 := by
    rw [narayanaCoeffA_leadingCoeff, hlc_succ]
    positivity
  have hA_natDegree : A.natDegree = n + 1 := by
    dsimp [A]
    rw [natDegree_mul' hA_lc_ne, narayanaCoeffA_natDegree, hdeg_succ]
    lia
  have hA_leadingCoeff : A.leadingCoeff = ((2 * n + 3 : ℝ) / (n + 3 : ℝ)) := by
    dsimp [A]
    rw [leadingCoeff_mul' hA_lc_ne, narayanaCoeffA_leadingCoeff, hlc_succ]
    lia
  have hB_lc_ne : (narayanaCoeffB n).leadingCoeff * (narayanaQuot n).leadingCoeff ≠ 0 := by
    rw [narayanaCoeffB_leadingCoeff n hn, hlc]
    exact mul_ne_zero
      (div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast Nat.ne_of_gt hn)) (by positivity))
      one_ne_zero
  have hB_natDegree : B.natDegree = n + 1 := by
    dsimp [B]
    rw [natDegree_mul' hB_lc_ne, narayanaCoeffB_natDegree n hn, hdeg]
    lia
  have hB_leadingCoeff : B.leadingCoeff = ((-(n : ℝ)) / (n + 3 : ℝ)) := by
    dsimp [B]
    rw [leadingCoeff_mul' hB_lc_ne, narayanaCoeffB_leadingCoeff n hn, hlc]
    lia
  have hA_ne : A ≠ 0 := leadingCoeff_ne_zero.mp (by rw [hA_leadingCoeff]; positivity)
  have hB_ne : B ≠ 0 := leadingCoeff_ne_zero.mp <| by
    rw [hB_leadingCoeff]
    exact div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast Nat.ne_of_gt hn)) (by positivity)
  have hA_degree : A.degree = n + 1 := by
    rw [degree_eq_natDegree hA_ne, hA_natDegree]
    lia
  have hB_degree : B.degree = n + 1 := by
    rw [degree_eq_natDegree hB_ne, hB_natDegree]
    lia
  have hsum_lc : A.leadingCoeff + B.leadingCoeff = 1 := by grind
  have hsum_lc_ne : A.leadingCoeff + B.leadingCoeff ≠ 0 := by simp_all
  have hsum_degree : (A + B).degree = n + 1 := by
    rw [Polynomial.degree_add_eq_of_leadingCoeff_add_ne_zero hsum_lc_ne, hA_degree, hB_degree,
      max_eq_left le_rfl]
  have hsum_natDegree : (A + B).natDegree = n + 1 :=
    natDegree_eq_of_degree_eq_some hsum_degree
  have hsum_leadingCoeff : (A + B).leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff_add_of_degree_eq (hA_degree.trans hB_degree.symm) hsum_lc_ne]
    lia
  simpa [narayanaQuot_succ_succ, A, B] using ⟨hsum_natDegree, hsum_leadingCoeff⟩

private lemma natDegree_leadingCoeff_narayanaQuot :
    ∀ n : Nat, 1 ≤ n →
      (narayanaQuot n).natDegree = n - 1 ∧
        (narayanaQuot n).leadingCoeff = 1
  | 0, hn => by
      lia
  | 1, _ => by
      simp [narayanaQuot]
  | 2, _ => by
      rw [narayanaQuot_two]
      exact
        ⟨by simpa [add_comm] using Polynomial.natDegree_X_add_C (x := (1 : ℝ)),
          by simpa [add_comm] using Polynomial.leadingCoeff_X_add_C (r := (1 : ℝ))⟩
  | n + 3, _ => by
      have hprev_succ := natDegree_leadingCoeff_narayanaQuot (n + 2) (by lia)
      have hprev := natDegree_leadingCoeff_narayanaQuot (n + 1) (by lia)
      have hstep :=
        natDegree_leadingCoeff_narayanaQuot_step (n + 1) (by lia)
          hprev_succ.1 hprev_succ.2 hprev.1 hprev.2
      lia

lemma natDegree_narayanaQuot (n : Nat) (hn : 1 ≤ n) :
    (narayanaQuot n).natDegree = n - 1 :=
  (natDegree_leadingCoeff_narayanaQuot n hn).1

lemma leadingCoeff_narayanaQuot (n : Nat) (hn : 1 ≤ n) :
    (narayanaQuot n).leadingCoeff = 1 :=
  (natDegree_leadingCoeff_narayanaQuot n hn).2

lemma narayanaQuot_ne_zero (n : Nat) (hn : 1 ≤ n) :
    narayanaQuot n ≠ 0 := by
  intro hzero
  have hcoeff : (narayanaQuot n).leadingCoeff = 0 := by simp [hzero]
  rw [leadingCoeff_narayanaQuot n hn] at hcoeff
  simp_all

lemma narayanaQuot_posLeadingCoeff (n : Nat) (hn : 1 ≤ n) :
    HasPosLeadingCoeff (narayanaQuot n) := by
  simp [HasPosLeadingCoeff, leadingCoeff_narayanaQuot n hn]

lemma natDegree_narayana (n : Nat) (hn : 1 ≤ n) :
    (narayana n).natDegree = n := by
  unfold narayana
  have hmul_ne : X.leadingCoeff * (narayanaQuot n).leadingCoeff ≠ 0 := by
    simp [leadingCoeff_narayanaQuot n hn]
  rw [natDegree_mul' hmul_ne, natDegree_X, natDegree_narayanaQuot n hn]
  lia

lemma narayanaQuot_one_two_interlaces :
    Interlaces (narayanaQuot 1) (narayanaQuot 2) := by
  rw [narayanaQuot_one, narayanaQuot_two]
  simpa [add_comm] using
    interlaces_one_linear (p := X + C (1 : ℝ))
      (Polynomial.natDegree_X_add_C (x := (1 : ℝ)))

private lemma prec_narayanaQuot_step (n : Nat) (hn : 1 ≤ n)
    (hInter : Interlaces (narayanaQuot n) (narayanaQuot (n + 1)))
    (hnonneg : HasNonnegCoeffs (narayanaQuot (n + 1))) :
    Prec (narayanaQuot (n + 1)) (narayanaQuot (n + 2)) := by
  have hg_pos : HasPosLeadingCoeff (narayanaQuot n) :=
    narayanaQuot_posLeadingCoeff n hn
  have hF_pos : HasPosLeadingCoeff (narayanaQuot (n + 2)) :=
    narayanaQuot_posLeadingCoeff (n + 2) (by lia)
  have hdeg_lo :
      (narayanaQuot (n + 1)).natDegree ≤
        (narayanaCoeffA n * narayanaQuot (n + 1) +
          narayanaCoeffB n * narayanaQuot n).natDegree := by
    rw [← narayanaQuot_succ_succ, natDegree_narayanaQuot (n + 1) (by lia),
      natDegree_narayanaQuot (n + 2) (by lia)]
    lia
  have hdeg_hi :
      (narayanaCoeffA n * narayanaQuot (n + 1) +
          narayanaCoeffB n * narayanaQuot n).natDegree ≤
        (narayanaQuot (n + 1)).natDegree + 1 := by
    rw [← narayanaQuot_succ_succ, natDegree_narayanaQuot (n + 1) (by lia),
      natDegree_narayanaQuot (n + 2) (by lia)]
    lia
  have hb_nonpos :
      ∀ r, (narayanaQuot (n + 1)).IsRoot r → (narayanaCoeffB n).eval r ≤ 0 := by
    intro r hr
    have hr_nonpos :
        r ≤ 0 := roots_nonpos_of_nonneg_coeffs hInter.1.2 hnonneg r
          ((mem_roots hInter.1.1).mpr hr)
    have hcoef_nonpos : (((-(n : ℝ)) / (n + 3 : ℝ)) : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by simp) (by positivity)
    have : (((-(n : ℝ)) / (n + 3 : ℝ)) : ℝ) * (1 - r) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoef_nonpos (sq_nonneg (1 - r))
    simpa [narayanaCoeffB, eval_mul, eval_sub, eval_one, eval_X] using this
  simpa [narayanaQuot_succ_succ] using
    (prec_of_interlaces_evalCoeff_nonpos
      (f := narayanaQuot (n + 1))
      (g := narayanaQuot n)
      (a := narayanaCoeffA n)
      (b := narayanaCoeffB n)
      hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos)

/-- Conditional oriented interlacing for the quotient Narayana sequence. Once
nonnegative coefficients are known, the three-term recurrence is an immediate
weak Liu--Wang induction. -/
theorem prec_narayanaQuot_succ_of_nonnegCoeffs :
    ∀ n : Nat, 1 ≤ n →
      (∀ m : Nat, HasNonnegCoeffs (narayanaQuot m)) →
      Prec (narayanaQuot n) (narayanaQuot (n + 1))
  | 0, hn, _ => by
      lia
  | 1, _, _ => narayanaQuot_one_two_interlaces.toPrec
  | n + 2, _, hnonneg => by
      have hprev : Prec (narayanaQuot (n + 1)) (narayanaQuot (n + 2)) :=
        prec_narayanaQuot_succ_of_nonnegCoeffs (n + 1) (by lia) hnonneg
      have hInter : Interlaces (narayanaQuot (n + 1)) (narayanaQuot (n + 2)) :=
        hprev.toInterlaces <| by
          rw [natDegree_narayanaQuot (n + 2) (by lia),
            natDegree_narayanaQuot (n + 1) (by lia)]
          lia
      exact prec_narayanaQuot_step (n + 1) (by lia) hInter (hnonneg (n + 2))

theorem interlaces_narayanaQuot_succ_of_nonnegCoeffs (n : Nat) (hn : 1 ≤ n)
    (hnonneg : ∀ m : Nat, HasNonnegCoeffs (narayanaQuot m)) :
    Interlaces (narayanaQuot n) (narayanaQuot (n + 1)) :=
  (prec_narayanaQuot_succ_of_nonnegCoeffs n hn hnonneg).toInterlaces <| by
    rw [natDegree_narayanaQuot (n + 1) (by lia), natDegree_narayanaQuot n hn]
    lia

/-- Conditional real-rootedness of the quotient Narayana sequence. -/
theorem isRealRooted_narayanaQuot_of_nonnegCoeffs :
    ∀ n : Nat, 1 ≤ n →
      (∀ m : Nat, HasNonnegCoeffs (narayanaQuot m)) →
      ((narayanaQuot n) ≠ 0 ∧ (narayanaQuot n).Splits)
  | 0, hn, _ => by lia
  | 1, _, _ => by simp
  | n + 2, _, hnonneg =>
      (prec_narayanaQuot_succ_of_nonnegCoeffs (n + 1) (by lia) hnonneg).2.1

/-- Conditional interlacing for the original Narayana sequence. This is just
the quotient result with the common `X` factor reattached on both sides. -/
theorem interlaces_narayana_succ_of_nonnegCoeffs (n : Nat) (hn : 1 ≤ n)
    (hnonneg : ∀ m : Nat, HasNonnegCoeffs (narayanaQuot m)) :
    Interlaces (narayana n) (narayana (n + 1)) := by
  have hprecQ : Prec (narayanaQuot n) (narayanaQuot (n + 1)) :=
    prec_narayanaQuot_succ_of_nonnegCoeffs n hn hnonneg
  have hq_nonpos : ∀ r ∈ (narayanaQuot n).roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hprecQ.1.2 (hnonneg n)
  have hq_succ_nonpos : ∀ r ∈ (narayanaQuot (n + 1)).roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hprecQ.2.1.2 (hnonneg (n + 1))
  have hprec : Prec (narayana n) (narayana (n + 1)) := by
    simpa [narayana] using
      prec_mul_X_both_of_roots_nonpos hprecQ hq_nonpos hq_succ_nonpos
  exact hprec.toInterlaces (by
    rw [natDegree_narayana (n + 1) (by lia), natDegree_narayana n hn])

/-- Conditional real-rootedness of the original Narayana sequence. -/
theorem isRealRooted_narayana_of_nonnegCoeffs :
    ∀ n : Nat, 1 ≤ n →
      (∀ m : Nat, HasNonnegCoeffs (narayanaQuot m)) →
      ((narayana n) ≠ 0 ∧ (narayana n).Splits)
  | 0, hn, _ => by lia
  | 1, _, _ => by simp
  | n + 2, _, hnonneg =>
      (interlaces_narayana_succ_of_nonnegCoeffs (n + 1) (by lia) hnonneg).1

/-- The descending prefix `[P_{n+1}, P_n, ..., P_1]` of the original Narayana
sequence. -/
def narayanaPrefix : Nat → List ℝ[X]
  | 0 => [narayana 1]
  | n + 1 => narayana (n + 2) :: narayanaPrefix n

@[simp] lemma narayanaPrefix_zero : narayanaPrefix 0 = [narayana 1] := rfl

@[simp] lemma narayanaPrefix_succ (n : Nat) :
    narayanaPrefix (n + 1) = narayana (n + 2) :: narayanaPrefix n := rfl

/-- Conditional Sturm-sequence package for the original Narayana polynomials. -/
theorem isSturmSeq_narayanaPrefix_of_nonnegCoeffs
    (hnonneg : ∀ m : Nat, HasNonnegCoeffs (narayanaQuot m)) :
    ∀ n : Nat, IsSturmSeq (narayanaPrefix n) := by
  intro n
  induction n with
  | zero =>
      simp [narayanaPrefix, IsSturmSeq]
  | succ n ih =>
      cases n with
      | zero =>
          simpa [narayanaPrefix, IsSturmSeq] using
            interlaces_narayana_succ_of_nonnegCoeffs 1 (by lia) hnonneg
      | succ n =>
          simpa [narayanaPrefix, IsSturmSeq] using
            And.intro (interlaces_narayana_succ_of_nonnegCoeffs (n + 2) (by lia) hnonneg) ih

end RealRooted
