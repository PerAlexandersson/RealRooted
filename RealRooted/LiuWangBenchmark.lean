import RealRooted.MaWang
import RealRooted.Linear
import RealRooted.CombinatorialExamples.Common
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# A Liu--Wang benchmark family

For a fixed parameter `d : ℕ`, define

`P_d,n(X) = ∑_{m=0}^{n-1} (n.choose m * d.choose (n - m - 1) : ℝ) X^m`.

Equivalently,

`P_d,n(X) = ∑_{r=1}^n (n.choose r * d.choose (r - 1) : ℝ) X^(n-r)`.

This file develops the basic coefficient/degree/positivity facts needed to use
the family as a benchmark for the Liu--Wang / Ma--Wang machinery.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- The binomial family attached to a fixed `d`. -/
def liuWangPoly (d n : Nat) : ℝ[X] :=
  Finset.sum (Finset.range n) fun m =>
    Polynomial.monomial m ((Nat.choose n m * Nat.choose d (n - m - 1) : ℕ) : ℝ)

/-- The same family, defined recursively from the Liu--Wang recurrence:

`(n - 1) P_n = (d + 2 - n + 2 (n - 1) X) P_{n-1} + (n - 1) X (1 - X) P_{n-2}`.

We normalize by dividing through by `n - 1`, which is harmless over `ℝ`. -/
def liuWangRec (d : Nat) : Nat → ℝ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      (C (((d : ℝ) - n) / (n + 1 : ℝ)) + C (2 : ℝ) * X) * liuWangRec d (n + 1) +
        X * (1 - X) * liuWangRec d n

@[simp] lemma liuWangRec_zero (d : Nat) : liuWangRec d 0 = 0 := rfl

@[simp] lemma liuWangRec_one (d : Nat) : liuWangRec d 1 = 1 := rfl

@[simp] lemma liuWangRec_succ_succ (d n : Nat) :
    liuWangRec d (n + 2) =
      (C (((d : ℝ) - n) / (n + 1 : ℝ)) + C (2 : ℝ) * X) * liuWangRec d (n + 1) +
        X * (1 - X) * liuWangRec d n := by
  simp [liuWangRec]

lemma liuWangRec_two (d : Nat) :
    liuWangRec d 2 = C (d : ℝ) + C (2 : ℝ) * X := by
  simp

lemma eval_zero_liuWangRec_succ_succ (d n : Nat) :
    (liuWangRec d (n + 2)).eval 0 =
      (((d : ℝ) - n) / (n + 1 : ℝ)) * (liuWangRec d (n + 1)).eval 0 := by
  simp [liuWangRec_succ_succ, eval_add, eval_mul]

lemma eval_zero_liuWangRec_threshold (d : Nat) :
    (liuWangRec d (d + 2)).eval 0 = 0 := by
  simp

lemma X_dvd_liuWangRec_threshold (d : Nat) :
    X ∣ liuWangRec d (d + 2) := by
  simpa using
    ((dvd_iff_isRoot).2 (show (liuWangRec d (d + 2)).IsRoot 0 by
      simp))

lemma X_dvd_liuWangRec_of_ge_threshold (d n : Nat) (hn : d + 2 ≤ n) :
    X ∣ liuWangRec d n := by
  revert hn
  refine Nat.strong_induction_on n ?_
  intro n ihn hn
  rcases Nat.eq_or_lt_of_le hn with rfl | hlt
  · exact X_dvd_liuWangRec_threshold d
  have htwo : 2 ≤ n := by lia
  rcases Nat.exists_eq_add_of_lt htwo with ⟨m, rfl⟩
  have hm2 : 1 + m + 1 = m + 2 := by lia
  rw [hm2, liuWangRec_succ_succ]
  refine dvd_add ?_ ?_
  · have hprev : d + 2 ≤ m + 1 := by lia
    obtain ⟨q, hq⟩ := ihn (m + 1) (by lia) hprev
    refine ⟨(C (((d : ℝ) - m) / (m + 1 : ℝ)) + C (2 : ℝ) * X) * q, by
      grind⟩
  · simp [mul_assoc]

lemma eval_zero_liuWangRec_of_ge_threshold (d n : Nat) (hn : d + 2 ≤ n) :
    (liuWangRec d n).eval 0 = 0 := by
  obtain ⟨q, hq⟩ := X_dvd_liuWangRec_of_ge_threshold d n hn
  simp_all

lemma zero_isRoot_liuWangRec_of_ge_threshold (d n : Nat) (hn : d + 2 ≤ n) :
    (liuWangRec d n).IsRoot 0 := by
  rw [Polynomial.IsRoot.def, eval_zero_liuWangRec_of_ge_threshold d n hn]

@[simp] lemma liuWangPoly_zero (d : Nat) : liuWangPoly d 0 = 0 := by
  simp [liuWangPoly]

@[simp] lemma liuWangPoly_one (d : Nat) : liuWangPoly d 1 = 1 := by
  ext m
  cases m <;> simp [liuWangPoly]

lemma coeff_liuWangPoly (d n m : Nat) :
    coeff (liuWangPoly d n) m =
      if m < n then
        ((Nat.choose n m * Nat.choose d (n - m - 1) : ℕ) : ℝ)
      else 0 := by
  rw [liuWangPoly, finsetSum_coeff]
  by_cases hm : m < n
  · rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr hm)]
    · simp [hm]
    · intro k hk hkm
      simp [Polynomial.coeff_monomial, hkm]
  · simp only [hm, ↓reduceIte]
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hkm : k ≠ m := by
      grind
    simp [Polynomial.coeff_monomial, hkm]

lemma coeff_liuWangPoly_of_lt (d n m : Nat) (hm : m < n) :
    coeff (liuWangPoly d n) m =
      ((Nat.choose n m * Nat.choose d (n - m - 1) : ℕ) : ℝ) := by
  simp [coeff_liuWangPoly, hm]

lemma coeff_liuWangPoly_of_ge (d n m : Nat) (hm : n ≤ m) :
    coeff (liuWangPoly d n) m = 0 := by
  simp [coeff_liuWangPoly, not_lt_of_ge hm]

lemma liuWangPoly_two (d : Nat) :
    liuWangPoly d 2 = C (d : ℝ) + C (2 : ℝ) * X := by
  ext m
  cases m with
  | zero =>
      rw [coeff_liuWangPoly_of_lt _ _ _ (by lia)]
      simp
  | succ m =>
      cases m with
      | zero =>
          rw [coeff_liuWangPoly_of_lt _ _ _ (by lia)]
          simp
      | succ m =>
          have hm : 2 ≤ m + 2 := by lia
          rw [coeff_liuWangPoly_of_ge _ _ _ hm]
          simp [coeff_add]

lemma coeff_zero_liuWangPoly (d n : Nat) :
    coeff (liuWangPoly d n) 0 =
      if 0 < n then ((Nat.choose d (n - 1) : ℕ) : ℝ) else 0 := by
  by_cases hn : 0 < n
  · have hlt : 0 < n := hn
    simp [coeff_liuWangPoly_of_lt _ _ _ hlt, hn]
  · simp_all

lemma coeff_top_liuWangPoly (d n : Nat) (hn : 0 < n) :
    coeff (liuWangPoly d n) (n - 1) = (n : ℝ) := by
  have hlt : n - 1 < n := Nat.sub_lt (Nat.zero_lt_of_lt hn) (by lia)
  rw [coeff_liuWangPoly_of_lt _ _ _ hlt]
  simp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp [Nat.choose_succ_self_right]

lemma coeff_above_liuWangPoly (d n m : Nat) (hm : n ≤ m) :
    coeff (liuWangPoly d n) m = 0 :=
  coeff_liuWangPoly_of_ge d n m hm

lemma natDegree_liuWangPoly (d n : Nat) (hn : 0 < n) :
    (liuWangPoly d n).natDegree = n - 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr (fun m hm =>
      coeff_above_liuWangPoly d n m (by lia))
  · rw [coeff_top_liuWangPoly d n hn]
    exact_mod_cast hn.ne'

lemma liuWangPoly_ne_zero (d n : Nat) (hn : 0 < n) :
    liuWangPoly d n ≠ 0 := by
  intro hzero
  have hcoeff : coeff (liuWangPoly d n) (n - 1) = 0 := by simp [hzero]
  rw [coeff_top_liuWangPoly d n hn] at hcoeff
  simp_all

lemma liuWangPoly_posLeadingCoeff (d n : Nat) (hn : 0 < n) :
    HasPosLeadingCoeff (liuWangPoly d n) := by
  unfold HasPosLeadingCoeff
  rw [leadingCoeff, natDegree_liuWangPoly d n hn, coeff_top_liuWangPoly d n hn]
  simp_all

lemma liuWangPoly_nonnegCoeffs (d n : Nat) :
    HasNonnegCoeffs (liuWangPoly d n) := by
  intro m
  by_cases hm : m < n
  · have h :
        0 ≤ ((Nat.choose n m * Nat.choose d (n - m - 1) : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_le (Nat.choose n m * Nat.choose d (n - m - 1))
    simpa [coeff_liuWangPoly, hm] using h
  · simp [coeff_liuWangPoly, hm]

private lemma coeff_zero_liuWangPoly_succ_succ (d n : Nat) :
    coeff (liuWangPoly d (n + 2)) 0 =
      (((d : ℝ) - n) / (n + 1 : ℝ)) * coeff (liuWangPoly d (n + 1)) 0 := by
  rw [coeff_zero_liuWangPoly, coeff_zero_liuWangPoly]
  have hn1 : 0 < n + 1 := by lia
  have hn2 : 0 < n + 2 := by lia
  rw [if_pos hn2, if_pos hn1]
  by_cases hnd : n ≤ d
  · have hchoose :
        ((Nat.choose d (n + 1) : ℕ) : ℝ) * (n + 1 : ℝ) =
          ((Nat.choose d n : ℕ) : ℝ) * ((d - n : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_succ_right_eq d n
    rw [Nat.cast_sub hnd] at hchoose
    grind
  · have hz_n : Nat.choose d n = 0 := Nat.choose_eq_zero_of_lt (lt_of_not_ge hnd)
    have hz_succ : Nat.choose d (n + 1) = 0 := Nat.choose_eq_zero_of_lt (lt_of_not_ge (by lia))
    simp [hz_n, hz_succ]

lemma coeff_zero_liuWangPoly_pos (d n : Nat) (hn : 1 ≤ n) (hnd : n ≤ d + 1) :
    0 < coeff (liuWangPoly d n) 0 := by
  rw [coeff_zero_liuWangPoly]
  have hn' : 0 < n := by lia
  rw [if_pos hn']
  have hchoose_pos : 0 < Nat.choose d (n - 1) := by
    apply Nat.choose_pos
    lia
  simp_all

lemma zero_not_isRoot_liuWangPoly (d n : Nat) (hn : 1 ≤ n) (hnd : n ≤ d + 1) :
    ¬ (liuWangPoly d n).IsRoot 0 := by
  intro hroot
  have hcoeff0 : 0 < coeff (liuWangPoly d n) 0 :=
    coeff_zero_liuWangPoly_pos d n hn hnd
  have hcoeff_zero : coeff (liuWangPoly d n) 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp_all
  linarith

lemma roots_neg_liuWangPoly_of_isRealRooted {d n : Nat} (hrr : (liuWangPoly d n).Splits)
    (hn : 1 ≤ n) (hnd : n ≤ d + 1) :
    ∀ r ∈ (liuWangPoly d n).roots, r < 0 := by
  intro r hr
  have hnonpos : r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hrr (liuWangPoly_nonnegCoeffs d n) r hr
  by_contra hnot
  have hzero : r = 0 := by grind
  have hr0 : (liuWangPoly d n).IsRoot 0 := by
    simp_all
  exact zero_not_isRoot_liuWangPoly d n hn hnd hr0

/-- The degree-`1` base case is immediate. -/
lemma isRealRooted_liuWangPoly_two (d : Nat) :
    ((liuWangPoly d 2) ≠ 0 ∧ (liuWangPoly d 2).Splits) := by
  exact isRealRooted_of_degree_one (natDegree_liuWangPoly d 2 (by lia))

private lemma natDegree_liuWangRec_affine (d n : Nat) :
    (C (((d : ℝ) - n) / (n + 1 : ℝ)) + C (2 : ℝ) * X).natDegree = 1 := by
  simp

private lemma leadingCoeff_liuWangRec_affine (d n : Nat) :
    (C (((d : ℝ) - n) / (n + 1 : ℝ)) + C (2 : ℝ) * X).leadingCoeff = 2 := by
  simpa [add_comm] using
    (Polynomial.leadingCoeff_linear (a := (2 : ℝ))
      (b := (((d : ℝ) - n) / (n + 1 : ℝ))) (by simp))

private lemma liuWangRec_X_one_sub_X :
    X * (1 - X : ℝ[X]) = -X ^ 2 + X := by
  ring

private lemma natDegree_liuWangRec_X_one_sub_X :
    (X * (1 - X : ℝ[X])).natDegree = 2 := by
  rw [liuWangRec_X_one_sub_X]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (Polynomial.natDegree_quadratic (a := (-1 : ℝ)) (b := (1 : ℝ)) (c := (0 : ℝ))
      (by simp))

private lemma leadingCoeff_liuWangRec_X_one_sub_X :
    (X * (1 - X : ℝ[X])).leadingCoeff = -1 := by
  rw [liuWangRec_X_one_sub_X]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (Polynomial.leadingCoeff_quadratic (a := (-1 : ℝ)) (b := (1 : ℝ)) (c := (0 : ℝ))
      (by simp))

private lemma natDegree_leadingCoeff_liuWangRec_step (d n : Nat) (hn : 1 ≤ n)
    (hdeg_succ : (liuWangRec d (n + 1)).natDegree = n)
    (hlc_succ : (liuWangRec d (n + 1)).leadingCoeff = n + 1)
    (hdeg : (liuWangRec d n).natDegree = n - 1)
    (hlc : (liuWangRec d n).leadingCoeff = n) :
    (liuWangRec d (n + 2)).natDegree = n + 1 ∧
      (liuWangRec d (n + 2)).leadingCoeff = n + 2 := by
  let A : ℝ[X] :=
    (C (((d : ℝ) - n) / (n + 1 : ℝ)) + C (2 : ℝ) * X) * liuWangRec d (n + 1)
  let B : ℝ[X] := (X * (1 - X)) * liuWangRec d n
  have hA_lc_nz :
      (C (((d : ℝ) - n) / (n + 1 : ℝ)) + C (2 : ℝ) * X).leadingCoeff *
          (liuWangRec d (n + 1)).leadingCoeff ≠ 0 := by
    rw [leadingCoeff_liuWangRec_affine, hlc_succ]
    positivity
  have hA_natDegree : A.natDegree = n + 1 := by
    dsimp [A]
    rw [natDegree_mul' hA_lc_nz, natDegree_liuWangRec_affine, hdeg_succ]
    lia
  have hA_leadingCoeff : A.leadingCoeff = 2 * (n + 1 : ℝ) := by
    dsimp [A]
    rw [leadingCoeff_mul' hA_lc_nz, leadingCoeff_liuWangRec_affine, hlc_succ]
  have hB_lc_nz : (X * (1 - X : ℝ[X])).leadingCoeff * (liuWangRec d n).leadingCoeff ≠ 0 := by
    rw [leadingCoeff_liuWangRec_X_one_sub_X, hlc]
    positivity
  have hB_natDegree : B.natDegree = n + 1 := by
    dsimp [B]
    rw [natDegree_mul' hB_lc_nz, natDegree_liuWangRec_X_one_sub_X, hdeg]
    lia
  have hB_leadingCoeff : B.leadingCoeff = -(n : ℝ) := by
    dsimp [B]
    rw [leadingCoeff_mul' hB_lc_nz, leadingCoeff_liuWangRec_X_one_sub_X, hlc]
    ring
  have hA_ne : A ≠ 0 := by
    exact leadingCoeff_ne_zero.mp (by simp_all)
  have hB_ne : B ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    simp_all
  have hA_degree : A.degree = n + 1 := by
    rw [degree_eq_natDegree hA_ne, hA_natDegree]
    lia
  have hB_degree : B.degree = n + 1 := by
    rw [degree_eq_natDegree hB_ne, hB_natDegree]
    lia
  have hsum_lc_ne : A.leadingCoeff + B.leadingCoeff ≠ 0 := by
    grind
  have hsum_degree : (A + B).degree = n + 1 := by
    rw [Polynomial.degree_add_eq_of_leadingCoeff_add_ne_zero hsum_lc_ne, hA_degree, hB_degree,
      max_eq_left le_rfl]
  have hsum_natDegree : (A + B).natDegree = n + 1 :=
    natDegree_eq_of_degree_eq_some hsum_degree
  have hsum_leadingCoeff : (A + B).leadingCoeff = n + 2 := by
    rw [Polynomial.leadingCoeff_add_of_degree_eq (hA_degree.trans hB_degree.symm) hsum_lc_ne,
      hA_leadingCoeff, hB_leadingCoeff]
    ring
  simpa [liuWangRec_succ_succ, A, B] using ⟨hsum_natDegree, hsum_leadingCoeff⟩

private lemma natDegree_leadingCoeff_liuWangRec (d n : Nat) (hn : 1 ≤ n) :
    (liuWangRec d n).natDegree = n - 1 ∧
      (liuWangRec d n).leadingCoeff = n := by
    revert hn
    refine Nat.strong_induction_on n ?_
    intro n ih hn
    cases n with
    | zero =>
        lia
    | succ n =>
        cases n with
        | zero =>
            simp
        | succ n =>
            cases n with
            | zero =>
                rw [liuWangRec_two]
                constructor
                · simpa [add_comm] using
                    (Polynomial.natDegree_linear (a := (2 : ℝ)) (b := (d : ℝ)) (by simp))
                · simpa [add_comm] using
                    (Polynomial.leadingCoeff_linear (a := (2 : ℝ)) (b := (d : ℝ)) (by simp))
            | succ n =>
                have hprev_succ := ih (n + 2) (by lia) (by lia)
                have hprev := ih (n + 1) (by lia) (by lia)
                have hprev_succ_deg :
                    (liuWangRec d ((n + 1) + 1)).natDegree = n + 1 := by
                  lia
                have hprev_succ_lc :
                    (liuWangRec d ((n + 1) + 1)).leadingCoeff = ((n + 1 : ℕ) : ℝ) + 1 := by
                  grind
                have hprev_deg :
                    (liuWangRec d (n + 1)).natDegree = (n + 1) - 1 := by
                  lia
                have hprev_lc :
                    (liuWangRec d (n + 1)).leadingCoeff = ((n + 1 : ℕ) : ℝ) := by
                  lia
                have hstep :=
                  natDegree_leadingCoeff_liuWangRec_step d (n + 1) (by lia)
                    hprev_succ_deg hprev_succ_lc hprev_deg hprev_lc
                grind

lemma natDegree_liuWangRec (d n : Nat) (hn : 1 ≤ n) :
    (liuWangRec d n).natDegree = n - 1 := by
  exact (natDegree_leadingCoeff_liuWangRec d n hn).1

lemma liuWangRec_ne_zero (d n : Nat) (hn : 1 ≤ n) :
    liuWangRec d n ≠ 0 := by
  intro hzero
  have hcoeff : (liuWangRec d n).leadingCoeff = 0 := by simp [hzero]
  rw [(natDegree_leadingCoeff_liuWangRec d n hn).2] at hcoeff
  simp_all

lemma liuWangRec_leadingCoeff (d n : Nat) (hn : 1 ≤ n) :
    (liuWangRec d n).leadingCoeff = n := by
  exact (natDegree_leadingCoeff_liuWangRec d n hn).2

lemma liuWangRec_posLeadingCoeff (d n : Nat) (hn : 1 ≤ n) :
    HasPosLeadingCoeff (liuWangRec d n) := by
  unfold HasPosLeadingCoeff
  rw [liuWangRec_leadingCoeff d n hn]
  exact_mod_cast hn

lemma eval_zero_liuWangRec_pos (d n : Nat) (hn : 1 ≤ n) (hnd : n ≤ d + 1) :
    0 < (liuWangRec d n).eval 0 := by
  revert hn hnd
  refine Nat.strong_induction_on n ?_
  intro n ih hn hnd
  cases n with
  | zero =>
      lia
  | succ n =>
      cases n with
      | zero =>
          simp
      | succ n =>
          rw [eval_zero_liuWangRec_succ_succ]
          have hfactor : 0 < (((d : ℝ) - n) / (n + 1 : ℝ)) := by
            have hlt_nat : n < d := by lia
            have hnum : 0 < ((d : ℝ) - n) := by
              simp_all
            have hden : 0 < (n + 1 : ℝ) := by grind
            simp_all
          have hprev : 0 < (liuWangRec d (n + 1)).eval 0 :=
            ih (n + 1) (by lia) (by lia) (by lia)
          simp_all

lemma zero_not_isRoot_liuWangRec (d n : Nat) (hn : 1 ≤ n) (hnd : n ≤ d + 1) :
    ¬ (liuWangRec d n).IsRoot 0 := by
  intro hroot
  have hpos := eval_zero_liuWangRec_pos d n hn hnd
  simp_all

lemma interlaces_liuWangRec_one_two (d : Nat) :
    Interlaces (liuWangRec d 1) (liuWangRec d 2) := by
  refine interlaces_one_linear ?_
  rw [liuWangRec_two]
  simpa [add_comm] using
    (Polynomial.natDegree_linear (a := (2 : ℝ)) (b := (d : ℝ)) (by simp))

private lemma list_prod_pos_of_forall_pos :
    ∀ {l : List ℝ}, (∀ x ∈ l, 0 < x) → 0 < l.prod
  | [], _ => by simp
  | x :: xs, h => by
      have hx : 0 < x := h x (by simp)
      have hxs : 0 < xs.prod := list_prod_pos_of_forall_pos (fun y hy => h y (by simp [hy]))
      simp_all

private lemma listInterlaces_dropLast_lt_zero_of_forall_lt_zero :
    ∀ {ss rs : List ℝ},
      ListInterlaces ss rs →
      (∀ s ∈ ss, s < 0) →
      ∀ r ∈ rs.dropLast, r < 0
  | [], [], _, _, _, hr => by simp at hr
  | [], [_], _, _, _, hr => by simp at hr
  | s :: ss, r₁ :: r₂ :: rs, hint, hss, r, hr => by
      obtain ⟨hr₁s, _, htail⟩ := hint
      rw [List.dropLast_cons_cons] at hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact lt_of_le_of_lt hr₁s (hss s (by simp))
      · exact listInterlaces_dropLast_lt_zero_of_forall_lt_zero htail
          (fun x hx => hss x (by simp [hx])) r hr'
  | [], _ :: _ :: _, hint, _, _, _ => by simp [ListInterlaces] at hint
  | _ :: _, [], hint, _, _, _ => by simp [ListInterlaces] at hint
  | _ :: _, [_], hint, _, _, _ => by simp [ListInterlaces] at hint

private lemma roots_neg_of_interlaces_of_eval_zero_pos {g f : ℝ[X]}
    (hgf : Interlaces g f)
    (hf_pos : HasPosLeadingCoeff f)
    (hf_zero : 0 < f.eval 0)
    (hg_neg : ∀ r, g.IsRoot r → r < 0) :
    ∀ r, f.IsRoot r → r < 0 := by
  obtain ⟨hf, hg, hdeg, rs, ss, hrs_sorted, _, hrs_eq, hss_eq, hint⟩ := hgf
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2]
  have hrs_ne : rs ≠ [] := by
    grind
  have hss_neg : ∀ s ∈ ss, s < 0 := by
    intro s hs
    have hs_root : g.IsRoot s := by
      apply (mem_roots hg.1).mp
      rw [← hss_eq]
      exact Multiset.mem_coe.mpr hs
    simp_all
  have hrs_drop_neg : ∀ r ∈ rs.dropLast, r < 0 :=
    listInterlaces_dropLast_lt_zero_of_forall_lt_zero hint hss_neg
  have h_eval :
      f.eval 0 = f.leadingCoeff * (rs.map (0 - ·)).prod := by
    rw [eval_eq_leadingCoeff_mul_prod_sub hf.1 hf.2 0, ← hrs_eq]
    simp
  have hrs_drop_prod_pos : 0 < (rs.dropLast.map (0 - ·)).prod := by
    apply list_prod_pos_of_forall_pos
    grind
  have hlast_neg : rs.getLast hrs_ne < 0 := by
    have hf_zero' := hf_zero
    rw [h_eval, ← List.dropLast_append_getLast hrs_ne, List.map_append,
      List.prod_append] at hf_zero'
    simp only [List.map] at hf_zero'
    simp only [List.prod_singleton] at hf_zero'
    have hmid :
        0 < (rs.dropLast.map (0 - ·)).prod * (0 - rs.getLast hrs_ne) := by
      exact (mul_pos_iff_of_pos_left hf_pos).mp hf_zero'
    have hfactor :
        0 < 0 - rs.getLast hrs_ne := by
      exact (mul_pos_iff_of_pos_left hrs_drop_prod_pos).mp hmid
    linarith
  intro r hr
  have hr_mem : r ∈ rs := by
    apply Multiset.mem_coe.mp
    simp_all
  by_cases hr_last : r = rs.getLast hrs_ne
  · lia
  · have hr_drop : r ∈ rs.dropLast := by
      exact List.mem_dropLast_of_mem_of_ne_getLast hr_mem hr_last
    simp_all

private lemma eval_liuWangRec_mul_prev_of_isRoot {d n : Nat} {r : ℝ}
    (hr : (liuWangRec d (n + 1)).IsRoot r) :
    (liuWangRec d (n + 2)).eval r * (liuWangRec d n).eval r =
      (r * (1 - r)) * ((liuWangRec d n).eval r) ^ 2 := by
  have hf0 : (liuWangRec d (n + 1)).eval r = 0 := by
    simp_all
  rw [liuWangRec_succ_succ]
  calc
    (((C (((d : ℝ) - n) / (n + 1 : ℝ)) + C (2 : ℝ) * X) * liuWangRec d (n + 1) +
          X * (1 - X) * liuWangRec d n).eval r) * (liuWangRec d n).eval r
      = ((((C (((d : ℝ) - n) / (n + 1 : ℝ)) + C (2 : ℝ) * X).eval r) *
            (liuWangRec d (n + 1)).eval r +
          (X * (1 - X : ℝ[X])).eval r * (liuWangRec d n).eval r) *
          (liuWangRec d n).eval r) := by
            simp [eval_add, eval_mul]
    _ = ((r * (1 - r)) * (liuWangRec d n).eval r) * (liuWangRec d n).eval r := by
          simp [hf0]
    _ = (r * (1 - r)) * ((liuWangRec d n).eval r) ^ 2 := by
          ring

private theorem strictData_liuWangRec (d : Nat) :
    ∀ n, 1 ≤ n → n + 1 ≤ d + 1 →
      Interlaces (liuWangRec d n) (liuWangRec d (n + 1)) ∧
        (∀ r, (liuWangRec d (n + 1)).IsRoot r → ¬ (liuWangRec d n).IsRoot r) ∧
        (∀ r, (liuWangRec d (n + 1)).IsRoot r → r < 0)
  | 0, hn, _ => by lia
  | 1, _, hnd => by
      have hInter : Interlaces (liuWangRec d 1) (liuWangRec d 2) :=
        interlaces_liuWangRec_one_two d
      have hOne_no_root : ∀ r, ¬ (liuWangRec d 1).IsRoot r := by
        simp
      have hNoCommon : ∀ r, (liuWangRec d 2).IsRoot r → ¬ (liuWangRec d 1).IsRoot r := by
        simp
      have hNeg : ∀ r, (liuWangRec d 2).IsRoot r → r < 0 := by
        exact roots_neg_of_interlaces_of_eval_zero_pos hInter
          (liuWangRec_posLeadingCoeff d 2 (by lia))
          (eval_zero_liuWangRec_pos d 2 (by lia) hnd)
          (fun r hr => False.elim ((hOne_no_root r) hr))
      lia
  | n + 2, hn, hnd => by
      have hprev := strictData_liuWangRec d (n + 1) (by lia) (by lia)
      have hInter : Interlaces (liuWangRec d (n + 1)) (liuWangRec d (n + 2)) := hprev.1
      have hNoCommon :
          ∀ r, (liuWangRec d (n + 2)).IsRoot r → ¬ (liuWangRec d (n + 1)).IsRoot r := hprev.2.1
      have hNeg :
          ∀ r, (liuWangRec d (n + 2)).IsRoot r → r < 0 := hprev.2.2
      have hdeg :
          (liuWangRec d (n + 3)).natDegree = (liuWangRec d (n + 2)).natDegree + 1 := by
        rw [natDegree_liuWangRec d (n + 3) (by lia), natDegree_liuWangRec d (n + 2) (by lia)]
        lia
      have hPrec : Prec (liuWangRec d (n + 2)) (liuWangRec d (n + 3)) :=
        prec_of_interlaces_evalCoeff_neg_succ hInter
          (liuWangRec_posLeadingCoeff d (n + 1) (by lia))
          (liuWangRec_posLeadingCoeff d (n + 3) (by lia))
          hdeg
          hNoCommon
          (by
            intro r hr
            have hr_neg : r < 0 := hNeg r hr
            have : (r : ℝ) * (1 - r) < 0 := by
              nlinarith
            simp_all)
      have hInter' : Interlaces (liuWangRec d (n + 2)) (liuWangRec d (n + 3)) :=
        hPrec.toInterlaces hdeg.symm
      have hNoCommon' :
          ∀ r, (liuWangRec d (n + 3)).IsRoot r → ¬ (liuWangRec d (n + 2)).IsRoot r := by
        intro r hrootF hrootf
        have : (liuWangRec d (n + 3)).eval r * (liuWangRec d (n + 1)).eval r < 0 := by
          have hcoeff_neg : r * (1 - r) < 0 := by
            have hr_neg : r < 0 := hNeg r hrootf
            nlinarith
          have hg_ne : (liuWangRec d (n + 1)).eval r ≠ 0 := by
            simp_all
          have hsq_pos : 0 < ((liuWangRec d (n + 1)).eval r) ^ 2 := by
            exact sq_pos_iff.mpr hg_ne
          rw [eval_liuWangRec_mul_prev_of_isRoot hrootf]
          exact mul_neg_of_neg_of_pos hcoeff_neg hsq_pos
        have hEq : (liuWangRec d (n + 3)).eval r = 0 := by
          simp_all
        grind
      have hNeg' :
          ∀ r, (liuWangRec d (n + 3)).IsRoot r → r < 0 := by
        exact roots_neg_of_interlaces_of_eval_zero_pos hInter'
          (liuWangRec_posLeadingCoeff d (n + 3) (by lia))
          (eval_zero_liuWangRec_pos d (n + 3) (by lia) hnd)
          hNeg
      lia

lemma interlaces_liuWangRec_of_lt_threshold (d n : Nat)
    (hn : 1 ≤ n) (hnd : n + 1 ≤ d + 1) :
    Interlaces (liuWangRec d n) (liuWangRec d (n + 1)) :=
  (strictData_liuWangRec d n hn hnd).1

lemma roots_neg_liuWangRec_of_lt_threshold (d n : Nat)
    (hn : 1 ≤ n) (hnd : n ≤ d + 1) :
    ∀ r, (liuWangRec d n).IsRoot r → r < 0 := by
  cases n with
  | zero =>
      lia
  | succ n =>
      cases n with
      | zero =>
          simp
      | succ n =>
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (strictData_liuWangRec d (n + 1) (by lia) hnd).2.2

private lemma roots_nonpos_of_interlaces_of_zero_root_of_roots_neg {g f : ℝ[X]}
    (hgf : Interlaces g f)
    (hzero : f.IsRoot 0)
    (hg_neg : ∀ r, g.IsRoot r → r < 0) :
    ∀ r, f.IsRoot r → r ≤ 0 := by
  obtain ⟨hf, hg, _, rs, ss, _, _, hrs_eq, hss_eq, hint⟩ := hgf
  have hzero_mem : 0 ∈ rs := by
    apply Multiset.mem_coe.mp
    simp_all
  have hrs_ne : rs ≠ [] := by
    grind
  have hss_neg : ∀ s ∈ ss, s < 0 := by
    intro s hs
    have hs_root : g.IsRoot s := by
      apply (mem_roots hg.1).mp
      rw [← hss_eq]
      exact Multiset.mem_coe.mpr hs
    simp_all
  have hrs_drop_neg : ∀ r ∈ rs.dropLast, r < 0 :=
    listInterlaces_dropLast_lt_zero_of_forall_lt_zero hint hss_neg
  have hlast_zero : rs.getLast hrs_ne = 0 := by
    by_contra hlast_ne
    have hzero_drop : 0 ∈ rs.dropLast := by
      exact List.mem_dropLast_of_mem_of_ne_getLast hzero_mem (by
        lia)
    grind
  intro r hr
  have hr_mem : r ∈ rs := by
    apply Multiset.mem_coe.mp
    simp_all
  by_cases hr_last : r = rs.getLast hrs_ne
  · simp [hr_last, hlast_zero]
  · have hr_drop : r ∈ rs.dropLast := by
      exact List.mem_dropLast_of_mem_of_ne_getLast hr_mem hr_last
    grind

private lemma listInterlaces_left_lt_of_right_lt :
    ∀ {ss rs : List ℝ},
      ListInterlaces ss rs →
      (∀ r ∈ rs, r < 0) →
      ∀ s ∈ ss, s < 0
  | [], [], _, _, _, hs => by simp at hs
  | [], [_], _, _, _, hs => by simp at hs
  | s :: ss, r₁ :: r₂ :: rs, hint, hrs_neg, t, ht => by
      obtain ⟨_, hs_r₂, htail⟩ := hint
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact lt_of_le_of_lt hs_r₂ (hrs_neg r₂ (by simp))
      · exact listInterlaces_left_lt_of_right_lt htail
          (fun u hu => hrs_neg u (by simp [hu])) t ht'
  | [], _ :: _ :: _, hint, _, _, _ => by
      simp_all
  | _ :: _, [], hint, _, _, _ => by
      cases hint
  | _ :: _, [_], hint, _, _, _ => by
      cases hint

private lemma listAlternates_left_lt_of_right_lt :
    ∀ {ss rs : List ℝ},
      ListAlternates ss rs →
      (∀ r ∈ rs, r < 0) →
      ∀ s ∈ ss, s < 0
  | [], [], _, _, _, hs => by simp at hs
  | s :: ss, r :: rs, halt, hrs_neg, t, ht => by
      obtain ⟨hsr, hint⟩ := halt
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact lt_of_le_of_lt hsr (hrs_neg r (by simp))
      · exact listInterlaces_left_lt_of_right_lt hint
          (fun u hu => hrs_neg u (by lia)) t ht'
  | [], _ :: _, halt, _, _, _ => by
      simp_all
  | _ :: _, [], halt, _, _, _ => by
      cases halt

private lemma roots_neg_of_prec_same_of_roots_neg {g f : ℝ[X]}
    (hgf : Prec g f)
    (hdeg : g.natDegree = f.natDegree)
    (hf_neg : ∀ r, f.IsRoot r → r < 0) :
    ∀ r, g.IsRoot r → r < 0 := by
  obtain ⟨hg, hf, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩ := hgf
  have hss_len : ss.length = g.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hg.2]
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2]
  rcases hshape with ⟨_, hint⟩ | ⟨_, halt⟩
  · lia
  · have hrs_neg : ∀ s ∈ rs, s < 0 := by
      intro s hs
      apply hf_neg s
      apply (mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr hs
    have hss_neg : ∀ s ∈ ss, s < 0 :=
      listAlternates_left_lt_of_right_lt halt hrs_neg
    intro r hr
    apply hss_neg r
    apply Multiset.mem_coe.mp
    simp_all

lemma interlaces_liuWangRec_threshold (d : Nat) :
    Interlaces (liuWangRec d (d + 1)) (liuWangRec d (d + 2)) := by
  cases d with
  | zero =>
      simpa using interlaces_liuWangRec_one_two 0
  | succ d =>
      have hprev := strictData_liuWangRec (d + 1) (d + 1) (by lia) (by lia)
      have hInter : Interlaces (liuWangRec (d + 1) (d + 1)) (liuWangRec (d + 1) (d + 2)) :=
        hprev.1
      have hNoCommon :
          ∀ r,
            (liuWangRec (d + 1) (d + 2)).IsRoot r →
              ¬ (liuWangRec (d + 1) (d + 1)).IsRoot r :=
        hprev.2.1
      have hNeg :
          ∀ r, (liuWangRec (d + 1) (d + 2)).IsRoot r → r < 0 :=
        hprev.2.2
      have hdeg :
          (liuWangRec (d + 1) (d + 3)).natDegree =
            (liuWangRec (d + 1) (d + 2)).natDegree + 1 := by
        rw [natDegree_liuWangRec (d + 1) (d + 3) (by lia),
          natDegree_liuWangRec (d + 1) (d + 2) (by lia)]
        lia
      have hPrec : Prec (liuWangRec (d + 1) (d + 2)) (liuWangRec (d + 1) (d + 3)) :=
        prec_of_interlaces_evalCoeff_neg_succ hInter
          (liuWangRec_posLeadingCoeff (d + 1) (d + 1) (by lia))
          (liuWangRec_posLeadingCoeff (d + 1) (d + 3) (by lia))
          hdeg
          hNoCommon
          (by
            intro r hr
            have hr_neg : r < 0 := hNeg r hr
            have : (r : ℝ) * (1 - r) < 0 := by
              nlinarith
            simp_all)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hPrec.toInterlaces hdeg.symm

lemma roots_nonpos_liuWangRec_threshold (d : Nat) :
    ∀ r, (liuWangRec d (d + 2)).IsRoot r → r ≤ 0 := by
  have hInter := interlaces_liuWangRec_threshold d
  have hzero : (liuWangRec d (d + 2)).IsRoot 0 := by
    simp
  have hneg :
      ∀ r, (liuWangRec d (d + 1)).IsRoot r → r < 0 := by
    have hbound : d + 1 ≤ d + 1 := le_rfl
    exact roots_neg_liuWangRec_of_lt_threshold d (d + 1) (by lia) hbound
  exact roots_nonpos_of_interlaces_of_zero_root_of_roots_neg hInter hzero hneg

private lemma weakPrec_liuWangRec_step (d n : Nat) (hn : 1 ≤ n)
    (hInter : Interlaces (liuWangRec d n) (liuWangRec d (n + 1)))
    (hnonpos : ∀ r, (liuWangRec d (n + 1)).IsRoot r → r ≤ 0) :
    Prec (liuWangRec d (n + 1)) (liuWangRec d (n + 2)) := by
  have hg_pos : HasPosLeadingCoeff (liuWangRec d n) :=
    liuWangRec_posLeadingCoeff d n hn
  have hF_pos : HasPosLeadingCoeff (liuWangRec d (n + 2)) :=
    liuWangRec_posLeadingCoeff d (n + 2) (by lia)
  have hdeg_lo :
      (liuWangRec d (n + 1)).natDegree ≤
        (((C (((d : ℝ) - n) / (n + 1 : ℝ)) + C (2 : ℝ) * X) * liuWangRec d (n + 1)) +
          X * (1 - X) * liuWangRec d n).natDegree := by
    rw [← liuWangRec_succ_succ, natDegree_liuWangRec d (n + 1) (by lia),
      natDegree_liuWangRec d (n + 2) (by lia)]
    lia
  have hdeg_hi :
      (((C (((d : ℝ) - n) / (n + 1 : ℝ)) + C (2 : ℝ) * X) * liuWangRec d (n + 1)) +
          X * (1 - X) * liuWangRec d n).natDegree ≤
        (liuWangRec d (n + 1)).natDegree + 1 := by
    rw [← liuWangRec_succ_succ, natDegree_liuWangRec d (n + 1) (by lia),
      natDegree_liuWangRec d (n + 2) (by lia)]
    lia
  have hb_nonpos :
      ∀ r, (liuWangRec d (n + 1)).IsRoot r →
        (X * (1 - X : ℝ[X])).eval r ≤ 0 := by
    intro r hr
    have hr_nonpos : r ≤ 0 := hnonpos r hr
    have : r * (1 - r) ≤ 0 := by
      nlinarith
    simp_all
  simpa [liuWangRec_succ_succ] using
    (prec_of_interlaces_evalCoeff_nonpos
      (f := liuWangRec d (n + 1))
      (g := liuWangRec d n)
      (a := C (((d : ℝ) - n) / (n + 1 : ℝ)) + C (2 : ℝ) * X)
      (b := X * (1 - X))
      hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos)

lemma interlaces_liuWangRec_threshold_succ (d : Nat) :
    Interlaces (liuWangRec d (d + 2)) (liuWangRec d (d + 3)) := by
  have hPrec : Prec (liuWangRec d (d + 2)) (liuWangRec d (d + 3)) :=
    weakPrec_liuWangRec_step d (d + 1) (by lia)
      (interlaces_liuWangRec_threshold d) (roots_nonpos_liuWangRec_threshold d)
  have hdeg :
      (liuWangRec d (d + 3)).natDegree =
        (liuWangRec d (d + 2)).natDegree + 1 := by
    rw [natDegree_liuWangRec d (d + 3) (by lia),
      natDegree_liuWangRec d (d + 2) (by lia)]
    lia
  exact hPrec.toInterlaces hdeg.symm

private lemma prec_of_interlaces_X_mul_of_roots_nonpos {f g : ℝ[X]}
    (h : Interlaces g (X * f))
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0) :
    Prec f g := by
  obtain ⟨hXf, hg, _, rs_xf, ss_g, hrs_xf, hss_g, hrs_xf_eq, hss_g_eq, hint⟩ := h
  have hf : (f ≠ 0 ∧ f.Splits) := by simp_all
  set rs_f := f.roots.sort (· ≤ ·)
  have hrs_f_eq : (↑rs_f : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_f_sorted : rs_f.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_f_nonpos : ∀ r ∈ rs_f, r ≤ 0 := by
    intro r hr
    exact hf_nonpos r (by rw [← hrs_f_eq]; exact Multiset.mem_coe.mpr hr)
  have hrs_f0_sorted : (rs_f ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by
    grind
  have hrs_xf_is : rs_xf = rs_f ++ [(0 : ℝ)] := by
    have hmultiset_eq : (↑rs_xf : Multiset ℝ) = ↑(rs_f ++ [(0 : ℝ)]) := by
      rw [hrs_xf_eq, roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X,
        ← hrs_f_eq, ← Multiset.coe_add]
      simp [add_comm]
    exact List.Perm.eq_of_pairwise' hrs_xf hrs_f0_sorted (Multiset.coe_eq_coe.mp hmultiset_eq)
  rw [hrs_xf_is] at hint
  have hlen : ss_g.length + 1 = (rs_f ++ [(0 : ℝ)]).length := by
    have hss_len : ss_g.length = g.natDegree := by
      rw [← Multiset.coe_card, hss_g_eq, card_roots_of_splits hg.2]
    have hrs_len : (rs_f ++ [(0 : ℝ)]).length = (X * f).natDegree := by
      rw [← hrs_xf_is, ← Multiset.coe_card, hrs_xf_eq, card_roots_of_splits hXf.2]
    lia
  have hlen_eq : rs_f.length = ss_g.length := by
    simp_all
  have hrs_f0_nonpos : ∀ r ∈ rs_f ++ [(0 : ℝ)], r ≤ 0 := by
    grind
  have halt0 : ListAlternates (rs_f ++ [(0 : ℝ)]) (ss_g ++ [(0 : ℝ)]) :=
    listAlternates_append_zero ss_g (rs_f ++ [(0 : ℝ)]) hlen hint hrs_f0_nonpos
  have halt : ListAlternates rs_f ss_g :=
    listAlternates_of_append_zero_both rs_f ss_g hlen_eq halt0
  exact
    ⟨hf, hg, rs_f, ss_g, hrs_f_sorted, hss_g, hrs_f_eq, hss_g_eq,
      Or.inr ⟨hlen_eq, halt⟩⟩

private lemma prec_threshold_divX (d : Nat) :
    Prec ((liuWangRec d (d + 2)) /ₘ X) (liuWangRec d (d + 1)) := by
  let q : ℝ[X] := (liuWangRec d (d + 2)) /ₘ X
  have hroot0 : (liuWangRec d (d + 2)).IsRoot 0 := by
    simp
  have hmul : X * q = liuWangRec d (d + 2) := by
    subst q
    simpa using (mul_divByMonic_eq_iff_isRoot (p := liuWangRec d (d + 2)) (a := (0 : ℝ))).2 hroot0
  have hInter : Interlaces (liuWangRec d (d + 1)) (X * q) := by
    have hInter' := interlaces_liuWangRec_threshold d
    lia
  have hq_nonpos : ∀ r ∈ q.roots, r ≤ 0 := by
    intro r hr
    have hq_ne : q ≠ 0 := by
      simp_all
    have hr_root_q : q.IsRoot r := (mem_roots hq_ne).mp hr
    have hr_root_p : (liuWangRec d (d + 2)).IsRoot r := by
      have hq0 : q.eval r = 0 := by
        simp_all
      rw [Polynomial.IsRoot.def]
      calc
        (liuWangRec d (d + 2)).eval r = (X * q).eval r := by lia
        _ = r * q.eval r := by simp
        _ = 0 := by simp_all
    exact roots_nonpos_liuWangRec_threshold d r hr_root_p
  simpa [q] using prec_of_interlaces_X_mul_of_roots_nonpos hInter hq_nonpos

private lemma roots_neg_threshold_divX (d : Nat) :
    ∀ r, (((liuWangRec d (d + 2)) /ₘ X)).IsRoot r → r < 0 := by
  have hPrec := prec_threshold_divX d
  have hdeg :
      (((liuWangRec d (d + 2)) /ₘ X)).natDegree = (liuWangRec d (d + 1)).natDegree := by
    rw [natDegree_divByMonic _ (monic_X : (X : ℝ[X]).Monic),
      natDegree_liuWangRec d (d + 2) (by lia),
      natDegree_liuWangRec d (d + 1) (by lia)]
    simp
  have hneg :
      ∀ r, (liuWangRec d (d + 1)).IsRoot r → r < 0 := by
    exact roots_neg_liuWangRec_of_lt_threshold d (d + 1) (by lia) (by lia)
  exact roots_neg_of_prec_same_of_roots_neg hPrec hdeg hneg

/-- The recurrence family is real-rooted throughout the strict range
`1 ≤ n ≤ d + 1`, and also at the threshold step `n = d + 2`. -/
lemma isRealRooted_liuWangRec_of_le_threshold (d n : Nat)
    (hn : 1 ≤ n) (hnd : n ≤ d + 2) : ((liuWangRec d n) ≠ 0 ∧ (liuWangRec d n).Splits) := by
  rcases Nat.eq_or_lt_of_le hnd with hEq | hlt
  · subst hEq
    exact (interlaces_liuWangRec_threshold d).1
  rcases hn.eq_or_lt with rfl | hn_lt
  · simp
  · have hInter :
        Interlaces (liuWangRec d (n - 1)) (liuWangRec d n) := by
      have hn_sub : 1 ≤ n - 1 := by lia
      have hlt' : (n - 1) + 1 ≤ d + 1 := by lia
      have hEq' : n - 1 + 1 = n := Nat.sub_add_cancel hn
      simpa [hEq'] using interlaces_liuWangRec_of_lt_threshold d (n - 1) hn_sub hlt'
    exact hInter.1

/-- Every root of the recurrence family is nonpositive through the same range:
the strict regime gives negative roots, and the threshold step adds the first
root at `0`. -/
lemma roots_nonpos_liuWangRec_of_le_threshold (d n : Nat)
    (hn : 1 ≤ n) (hnd : n ≤ d + 2) :
    ∀ r, (liuWangRec d n).IsRoot r → r ≤ 0 := by
  rcases Nat.eq_or_lt_of_le hnd with hEq | hlt
  · subst hEq
    exact roots_nonpos_liuWangRec_threshold d
  · intro r hr
    have hlt' : n ≤ d + 1 := by lia
    exact le_of_lt (roots_neg_liuWangRec_of_lt_threshold d n hn hlt' r hr)

/-- If the recurrence family is known to have nonnegative coefficients, then the
weak Liu--Wang theorem propagates interlacing through the entire post-threshold
range `n ≥ d + 1`. -/
lemma interlaces_liuWangRec_of_ge_threshold_of_nonnegCoeffs (d k : Nat)
    (hnonneg : ∀ n, HasNonnegCoeffs (liuWangRec d n)) :
    Interlaces (liuWangRec d (d + 1 + k)) (liuWangRec d (d + 2 + k)) := by
  induction k with
  | zero =>
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using interlaces_liuWangRec_threshold d
  | succ k ih =>
      have hInter :
          Interlaces (liuWangRec d (d + 1 + k)) (liuWangRec d ((d + 1 + k) + 1)) := by
        lia
      have hnonpos :
          ∀ r, (liuWangRec d ((d + 1 + k) + 1)).IsRoot r → r ≤ 0 := by
        intro r hr
        exact roots_nonpos_of_nonneg_coeffs hInter.1.2 (hnonneg ((d + 1 + k) + 1)) r
          ((mem_roots hInter.1.1).mpr hr)
      have hPrec :
          Prec (liuWangRec d (d + 2 + k)) (liuWangRec d (d + 3 + k)) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          weakPrec_liuWangRec_step d (d + 1 + k) (by lia) hInter hnonpos
      have hdeg :
          (liuWangRec d (d + 3 + k)).natDegree =
            (liuWangRec d (d + 2 + k)).natDegree + 1 := by
        rw [natDegree_liuWangRec d (d + 3 + k) (by lia),
          natDegree_liuWangRec d (d + 2 + k) (by lia)]
        lia
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hPrec.toInterlaces hdeg.symm

/-- Conditional global interlacing statement for the recurrence family: once
nonnegative coefficients are available, the weak Liu--Wang induction extends
the threshold result to all `n ≥ 1`. -/
lemma interlaces_liuWangRec_of_nonnegCoeffs (d n : Nat)
    (hn : 1 ≤ n)
    (hnonneg : ∀ m, HasNonnegCoeffs (liuWangRec d m)) :
    Interlaces (liuWangRec d n) (liuWangRec d (n + 1)) := by
  by_cases hthr : n + 1 ≤ d + 2
  · rcases Nat.lt_or_eq_of_le hthr with hlt | hEq
    · have hlt' : n + 1 ≤ d + 1 := by lia
      exact interlaces_liuWangRec_of_lt_threshold d n hn hlt'
    · have hn_eq : n = d + 1 := by lia
      subst hn_eq
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using interlaces_liuWangRec_threshold d
  · have hge : d + 2 ≤ n + 1 := by lia
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hge
    have hn_eq : n = d + 1 + k := by lia
    subst hn_eq
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      interlaces_liuWangRec_of_ge_threshold_of_nonnegCoeffs d k hnonneg

/-- Conditional global real-rootedness statement for the recurrence family. -/
lemma isRealRooted_liuWangRec_of_nonnegCoeffs (d n : Nat)
    (hn : 1 ≤ n)
    (hnonneg : ∀ m, HasNonnegCoeffs (liuWangRec d m)) :
    ((liuWangRec d n) ≠ 0 ∧ (liuWangRec d n).Splits) := by
  rcases hn.eq_or_lt with rfl | hn_lt
  · simp
  have hInter : Interlaces (liuWangRec d (n - 1)) (liuWangRec d n) := by
    have hn_sub : 1 ≤ n - 1 := by lia
    have hEq : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simpa [hEq] using interlaces_liuWangRec_of_nonnegCoeffs d (n - 1) hn_sub hnonneg
  exact hInter.1

end RealRooted
