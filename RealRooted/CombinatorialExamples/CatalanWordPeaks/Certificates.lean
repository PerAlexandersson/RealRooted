/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.Basic
public import RealRooted.CombinatorialExamples.LongCycleDescents.Boundary
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-!
# Compact exact certificates for Catalan strict peaks

We reconstruct the shifted coefficients by integer division and check its
exactness before using any signs. Endpoint evaluation reuses the homogenized
integer Horner kernel of `LongCycleDescents`. No packed evaluation or coefficient
table is trusted or stored. Only small dyadic isolating intervals are supplied.
-/

@[expose] public noncomputable section

namespace RealRooted.CatalanWordPeaks

open Polynomial Finset
open LongCycleDescents.Necklace

local notation "GridPoint" => LongCycleDescents.Necklace.Dyadic

/-- The numerator in the shifted binomial coefficient formula. -/
def shiftedNumerator (n i : ℕ) : ℕ :=
  Nat.fast_choose (n - i) i * Nat.fast_choose (2 * n - 3 * i) (n - 2 * i - 1)

/-- Candidate integral shifted coefficients, reconstructed rather than stored. -/
def integerCoefficients (n : ℕ) : List ℤ :=
  if n = 0 then [1] else
    List.ofFn fun i : Fin (rowDegree n + 1) ↦ (shiftedNumerator n i / (n - i) : ℕ)

/-- Check the divisions in the coefficient formula using integer multiplication. -/
def checkCoefficients (n : ℕ) : Bool :=
  (List.range (rowDegree n + 1)).all fun i ↦
    decide (n = 0 ∨ (0 < n - i ∧
      shiftedNumerator n i = (n - i) * (shiftedNumerator n i / (n - i))))

/-- The candidate coefficient list always has the prescribed size. -/
theorem length_integerCoefficients (n : ℕ) :
    (integerCoefficients n).length = rowDegree n + 1 := by
  unfold integerCoefficients
  split
  · next h => simp only [h, rowDegree, Nat.zero_sub, Nat.zero_div, List.length_singleton]
  · exact List.length_ofFn

private theorem coefficient_checked {n : ℕ} (hn : n ≠ 0)
    (h : checkCoefficients n = true) {i : ℕ} (hi : i < rowDegree n + 1) :
    shiftedCoefficient n i = ((integerCoefficients n)[i]?.getD 0 : ℤ) := by
  have hc := of_decide_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr hi))
  rcases hc with hz | ⟨hd, he⟩
  · exact (hn hz).elim
  · have hcast : (shiftedNumerator n i : ℚ) =
        (n - i : ℕ) * (shiftedNumerator n i / (n - i) : ℕ) := by exact_mod_cast he
    rw [integerCoefficients, ite_eq_right hn, List.getElem?_eq_getElem
      (by simpa only [List.length_ofFn] using hi), Option.getD_some, List.getElem_ofFn]
    rw [shiftedCoefficient, ← Nat.cast_mul]
    change (shiftedNumerator n i : ℚ) / (n - i : ℕ) = _
    rw [hcast, mul_div_cancel_left₀ _ (by exact_mod_cast hd.ne')]
    norm_cast

/-- Checked integer coefficients evaluate the defining rational formula exactly. -/
theorem eval_polynomial_of_checkCoefficients {n : ℕ} (h : checkCoefficients n = true)
    (x : ℝ) : (polynomial n).eval x =
      (coefficientPolynomial (integerCoefficients n)).eval (x - 1) := by
  by_cases hn : n = 0
  · subst n
    simp only [polynomial, ite_true, eval_one, integerCoefficients, coefficientPolynomial,
      Int.cast_one, eval_C, mul_zero, add_zero]
  · rw [Polynomial.eval_eq_sum_range' (p := coefficientPolynomial (integerCoefficients n))
      (n := rowDegree n + 1) (by
      have hd := natDegree_coefficientPolynomial_le (integerCoefficients n)
      rw [length_integerCoefficients] at hd
      lia)]
    simp only [polynomial, ite_eq_right hn, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub,
      eval_X, eval_one]
    apply sum_congr rfl
    intro i hi
    rw [coeff_coefficientPolynomial]
    have hc := congrArg (fun q : ℚ ↦ (q : ℝ)) (coefficient_checked hn h (mem_range.mp hi))
    push_cast at hc
    rw [hc]

/-- Denominator-cleared evaluation at a dyadic point in the original variable. -/
def integerValue (n : ℕ) (x : GridPoint) : ℤ :=
  homogeneous ⟨x.numer - 2 ^ x.shift, x.shift⟩ (integerCoefficients n)

/-- Integer evaluation has the same sign as the real polynomial value. -/
theorem integerValue_eq {n : ℕ} (h : checkCoefficients n = true) (x : GridPoint) :
    (integerValue n x : ℝ) =
      (2 : ℝ) ^ (x.shift * (rowDegree n + 1)) * (polynomial n).eval x.value := by
  rw [integerValue, homogeneous_eq_eval, length_integerCoefficients,
    eval_polynomial_of_checkCoefficients h]
  congr 2
  simp only [LongCycleDescents.Necklace.Dyadic.value, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
  field_simp

/-- Lower endpoint of a width-two interval on its dyadic grid. -/
def lower (centers : Array GridPoint) (i : ℕ) : GridPoint :=
  let x := centers.getD i LongCycleDescents.Necklace.Dyadic.zero
  ⟨x.numer - 1, x.shift⟩

/-- Upper endpoint of a width-two interval on its dyadic grid. -/
def upper (centers : Array GridPoint) (i : ℕ) : GridPoint :=
  let x := centers.getD i LongCycleDescents.Necklace.Dyadic.zero
  ⟨x.numer + 1, x.shift⟩

/-- One exact row certificate checks coefficients, nonvanishing, interval order,
negative endpoints and strict sign changes. -/
def checkRow (n : ℕ) (centers : Array GridPoint) : Bool :=
  checkCoefficients n && decide (centers.size = rowDegree n) &&
    decide (0 < integerValue n LongCycleDescents.Necklace.Dyadic.zero) &&
    (List.range (rowDegree n)).all (fun i ↦
      (upper centers i).less LongCycleDescents.Necklace.Dyadic.zero &&
      decide (integerValue n (lower centers i) * integerValue n (upper centers i) < 0)) &&
    (List.range (rowDegree n - 1)).all (fun i ↦
      (upper centers i).less (lower centers (i + 1)))

/-- A checked row is nonzero. -/
theorem polynomial_ne_zero_of_checkRow {n : ℕ} {centers : Array GridPoint}
    (h : checkRow n centers = true) : polynomial n ≠ 0 := by
  have hc := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp h).1).1).1).1
  have hz := of_decide_eq_true (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).2
  intro heq
  have hv := integerValue_eq hc LongCycleDescents.Necklace.Dyadic.zero
  rw [heq, eval_zero, mul_zero] at hv
  exact (ne_of_gt hz) (Int.cast_eq_zero.mp hv)

/-- Adjacent disjoint intervals remain separated across any number of gaps. -/
private theorem intervals_separated {m : ℕ} (l u : ℕ → ℝ)
    (hw : ∀ i, i < m → l i < u i) (hstep : ∀ i, i + 1 < m → u i ≤ l (i + 1)) :
    ∀ i j, i < j → j < m → u i ≤ l j := by
  intro i j
  induction j with
  | zero => intro hij; exact (Nat.not_lt_zero _ hij).elim
  | succ j ih =>
    intro hij hj
    by_cases heq : i = j
    · subst i; exact hstep j hj
    · have hij' : i < j := lt_of_le_of_ne (Nat.le_of_lt_succ hij) heq
      have hj' : j < m := Nat.lt_of_succ_lt hj
      exact (ih hij' hj').trans ((hw j hj').le.trans (hstep j hj))

/-- A checked row has an increasing complete root list in its disjoint negative intervals. -/
theorem roots_of_checkRow {n : ℕ} {centers : Array GridPoint}
    (h : checkRow n centers = true) :
    ∃ r : Fin (rowDegree n) → ℝ, StrictMono r ∧
      (∀ i : Fin (rowDegree n),
        (lower centers i).value < r i ∧ r i < (upper centers i).value) ∧
      (↑(List.ofFn r) : Multiset ℝ) = (polynomial n).roots ∧
      (polynomial n).Splits ∧ (polynomial n).natDegree = rowDegree n := by
  have ⟨h₁, ho⟩ := Bool.and_eq_true_iff.mp h
  have ⟨h₂, hv⟩ := Bool.and_eq_true_iff.mp h₁
  have ⟨h₃, _⟩ := Bool.and_eq_true_iff.mp h₂
  have ⟨hc, _⟩ := Bool.and_eq_true_iff.mp h₃
  have hstep (i : Fin (rowDegree n - 1)) :
      (upper centers i).value ≤ (lower centers (i.val + 1)).value := by
    exact ((LongCycleDescents.Necklace.Dyadic.less_iff _ _).mp
      (List.all_eq_true.mp ho i (List.mem_range.mpr i.isLt))).le
  have hw (i : Fin (rowDegree n)) :
      (lower centers i).value < (upper centers i).value := by
    simp only [lower, upper, LongCycleDescents.Necklace.Dyadic.value]
    apply div_lt_div_of_pos_right _ (by positivity)
    push_cast
    linarith only
  have hsep := intervals_separated (fun i ↦ (lower centers i).value)
    (fun i ↦ (upper centers i).value) (fun i hi ↦ hw ⟨i, hi⟩)
    (fun i hi ↦ hstep ⟨i, Nat.lt_sub_of_add_lt hi⟩)
  refine roots_of_intervals (polynomial_ne_zero_of_checkRow h) (natDegree_polynomial_le n)
    (fun i ↦ (lower centers i).value) (fun i ↦ (upper centers i).value) hw ?_ ?_
  · intro i j hij
    exact hsep i j hij j.isLt
  · intro i
    have hb := of_decide_eq_true (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp hv i (List.mem_range.mpr i.isLt))).2
    have hb' : (integerValue n (lower centers i) : ℝ) *
        (integerValue n (upper centers i) : ℝ) < 0 := by exact_mod_cast hb
    rw [integerValue_eq hc, integerValue_eq hc] at hb'
    have hp : 0 < (2 : ℝ) ^ ((centers.getD i LongCycleDescents.Necklace.Dyadic.zero).shift *
        (rowDegree n + 1)) := by positivity
    change (_ * (polynomial n).eval _) * (_ * (polynomial n).eval _) < 0 at hb'
    rw [mul_mul_mul_comm] at hb'
    exact neg_of_mul_neg_right hb' (mul_pos hp hp).le

/-- Checked rows split with simple negative roots and have their exact expected degree. -/
theorem polynomial_roots_of_checkRow {n : ℕ} {centers : Array GridPoint}
    (h : checkRow n centers = true) :
    (polynomial n).Splits ∧ HasSimpleRoots (polynomial n) ∧
      (polynomial n).natDegree = rowDegree n ∧ ∀ x ∈ (polynomial n).roots, x < 0 := by
  obtain ⟨r, hr, hb, heq, hsplit, hd⟩ := roots_of_checkRow h
  refine ⟨hsplit, hasSimpleRoots_of_root_list (polynomial_ne_zero_of_checkRow h) hr heq, hd, ?_⟩
  intro x hx
  rw [← heq] at hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hx)
  have hi := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2 i
    (List.mem_range.mpr i.isLt))).1
  exact (hb i).2.trans (by
    simpa only [LongCycleDescents.Necklace.Dyadic.value_zero] using
      (LongCycleDescents.Necklace.Dyadic.less_iff _ _).mp hi)

/-- Check the directed order of the old and new isolating intervals. -/
def checkPair (n : ℕ) (old new : Array GridPoint) : Bool :=
  (List.range (rowDegree n)).all fun i ↦
    let j := i + (rowDegree (n + 1) - rowDegree n)
    (upper old i).less (lower new j) &&
      (if 0 < j then (upper new (j - 1)).less (lower old i) else true)

/-- Checked interval separation yields standard interlacing, no common roots,
and a strictly larger rightmost root when the old polynomial is nonconstant. -/
theorem strictInterl_of_checkPair {n : ℕ} {old new : Array GridPoint}
    (ho : checkRow n old = true) (hn : checkRow (n + 1) new = true)
    (hp : checkPair n old new = true) :
    StrictInterl (polynomial n) (polynomial (n + 1)) ∧
      (∀ x, ¬ ((polynomial n).IsRoot x ∧ (polynomial (n + 1)).IsRoot x)) ∧
      (rowDegree n ≠ 0 → ∃ y ∈ (polynomial (n + 1)).roots,
        (∀ x ∈ (polynomial n).roots, x < y) ∧
        ∀ z ∈ (polynomial (n + 1)).roots, z ≤ y) := by
  obtain ⟨r, hr, hb, heq, hsplit, _⟩ := roots_of_checkRow ho
  obtain ⟨s, hs, hbs, heqs, hsplits, _⟩ := roots_of_checkRow hn
  have hright (i : Fin (rowDegree n)) (j : Fin (rowDegree (n + 1)))
      (hij : j.val = i.val + (rowDegree (n + 1) - rowDegree n)) : r i < s j := by
    have h := (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp hp i (List.mem_range.mpr i.isLt))).1
    rw [← hij] at h
    have hreal := ((LongCycleDescents.Necklace.Dyadic.less_iff _ _).mp h).le
    exact (hb i).2.trans (hreal.trans_lt (hbs j).1)
  have hleft (i : Fin (rowDegree n)) (j : Fin (rowDegree (n + 1)))
      (hij : j.val + 1 = i.val + (rowDegree (n + 1) - rowDegree n)) : s j < r i := by
    have h := (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp hp i (List.mem_range.mpr i.isLt))).2
    rw [← hij] at h
    rw [ite_eq_left (Nat.succ_pos _), Nat.add_sub_cancel] at h
    have hreal := ((LongCycleDescents.Necklace.Dyadic.less_iff _ _).mp h).le
    exact (hbs j).2.trans (hreal.trans_lt (hb i).1)
  have hpo := polynomial_ne_zero_of_checkRow ho
  have hpn := polynomial_ne_zero_of_checkRow hn
  exact ⟨strictInterl_of_root_lists hpo hpn hsplit hsplits r s hr hs heq heqs
      (rowDegree_succ n) hright hleft,
    no_common_root_of_root_lists hpo hpn (rowDegree_succ n) r s hs heq heqs hright hleft,
    fun hm ↦ exists_root_above_of_root_lists hm (rowDegree_succ n) r s hs heq heqs hright⟩

end RealRooted.CatalanWordPeaks
