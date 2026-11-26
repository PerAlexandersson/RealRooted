/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Binomial
public import RealRooted.CombinatorialExamples.LongCycleDescents.Counting
public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetTransform
public import RealRooted.IntervalDifferential.EulerRecurrence
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Euler recurrences for the alphabet

The necklace product gives a formal Euler differential equation. Reflection in the
size parameter expresses its coefficients through the degree-loss kernel.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0).
-/

@[expose] public noncomputable section

open Polynomial Finset
open scoped ArithmeticFunction.Moebius

namespace RealRooted.LongCycleDescents.Structural

open Necklace Words

/-- The rational primitive-necklace polynomial. -/
def necklacePolynomial (j : ℕ) : ℚ[X] :=
  C ((j : ℚ)⁻¹) * ∑ d ∈ j.divisors, C (μ d : ℚ) * X ^ (j / d)

/-- The multiset profile alphabet polynomial, with its genuine cutoff. -/
def cycleAlphabet (n k : ℕ) : ℚ[X] :=
  ∑ p : PositiveLengthProfile n k, ∏ i : Fin n,
    Ring.multichoose (necklacePolynomial (i.val + 1)) (p.val i).val

/-- Primitive-necklace evaluation is the already proved integer Möbius count. -/
theorem necklacePolynomial_eval_nat {j : ℕ} (hj : 0 < j) (q : ℕ) :
    (necklacePolynomial j).eval (q : ℚ) = (Fintype.card (PrimitiveNecklace j q) : ℚ) := by
  simp only [necklacePolynomial, eval_mul, eval_C, eval_finsetSum, eval_pow, eval_X]
  have h : (j : ℚ) * (Fintype.card (PrimitiveNecklace j q) : ℚ) =
      ∑ d ∈ j.divisors, (μ d : ℚ) * (q : ℚ) ^ (j / d) := by
    exact_mod_cast card_primitiveNecklace_mul hj q
  rw [← h, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hj.ne'), one_mul]

private theorem multichoose_natCast (q b : ℕ) :
    Ring.multichoose (q : ℚ) b = (Nat.multichoose q b : ℚ) := by
  cases b with
  | zero => simp
  | succ b =>
    rw [Ring.multichoose_eq, Nat.multichoose_eq]
    have he : (q : ℚ) + (b + 1 : ℕ) - 1 = ((q + (b + 1) - 1 : ℕ) : ℚ) := by
      rw [show q + (b + 1) - 1 = q + b by lia]
      push_cast
      ring
    rw [he, Ring.choose_natCast]

/-- The rational product evaluates to the actual necklace-content cardinality. -/
theorem cycleAlphabet_eval_nat (n k q : ℕ) :
    (cycleAlphabet n k).eval (q : ℚ) = (Nat.card (NecklaceContent n q k) : ℚ) := by
  rw [card_necklaceContent_eq_positive_sum]
  push_cast
  simp only [cycleAlphabet, eval_finsetSum]
  apply sum_congr rfl
  intro p _
  rw [eval_prod]
  apply prod_congr rfl
  intro i _
  change (evalRingHom (q : ℚ)) (Ring.multichoose _ _) = _
  rw [Ring.map_multichoose]
  change Ring.multichoose ((necklacePolynomial (i.val + 1)).eval (q : ℚ)) _ = _
  rw [necklacePolynomial_eval_nat (Nat.succ_pos _), multichoose_natCast]

/-- The rational product is faithfully the original permutation alphabet polynomial. -/
theorem map_cycleAlphabet {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (cycleAlphabet n k).map (Rat.castHom ℝ) = descentAlphabetPolynomial n k := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun q : ℕ => ((q + 1 : ℕ) : ℝ)) := by
    intro a b h
    exact Nat.succ.inj (Nat.cast_injective h)
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨q, rfl⟩
  change ((cycleAlphabet n k).map (Rat.castHom ℝ)).eval ((q + 1 : ℕ) : ℝ) =
    (descentAlphabetPolynomial n k).eval ((q + 1 : ℕ) : ℝ)
  rw [descentAlphabetPolynomial_eval_nat _ _ _ (Nat.succ_pos _)]
  have he := cycleAlphabet_eval_nat n k (q + 1)
  have hc := letters_eq_necklace_content hn (q + 1) k
  rw [hc]
  have hm : ((cycleAlphabet n k).map (Rat.castHom ℝ)).eval ((q + 1 : ℕ) : ℝ) =
      (((cycleAlphabet n k).eval ((q + 1 : ℕ) : ℚ) : ℚ) : ℝ) := by
    rw [eval_map]
    simpa using (eval₂_at_apply (p := cycleAlphabet n k) (Rat.castHom ℝ) ((q + 1 : ℕ) : ℚ))
  rw [hm, he]
  norm_cast

end RealRooted.LongCycleDescents.Structural

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [BinomialRing R]

private theorem multichoose_step (M : R) (a : ℕ) :
    ((a + 1 : ℕ) : R) * Ring.multichoose M (a + 1) =
      (M + (a : R)) * Ring.multichoose M a := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer M (a + 1)
  have g := Ring.factorial_nsmul_multichoose_eq_ascPochhammer M a
  simp only [nsmul_eq_mul, ascPochhammer_smeval_eq_eval] at h g
  rw [ascPochhammer_succ_right] at h
  simp only [eval_mul, eval_add, eval_X, eval_natCast, ← g, Nat.factorial_succ,
    Nat.cast_mul] at h
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a) :
    (a.factorial : R) ≠ 0)
  linear_combination h

private theorem multichoose_sum (M : R) (a : ℕ) :
    (a : R) * Ring.multichoose M a = (∑ i ∈ range a, Ring.multichoose M i) * M := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [multichoose_step, sum_range_succ]
    linear_combination ih

/-- The finite multiset factor with multiplicities through H. -/
def inventoryFactor (H : ℕ) (M : R) : R[X] :=
  ∑ i ∈ range (H + 1), monomial i (Ring.multichoose M i)

/-- The Euler logarithmic kernel of one finite multiset factor. -/
def inventoryKernel (H : ℕ) (M : R) : R[X] :=
  ∑ i ∈ range (H + 1), monomial i (if i = 0 then 0 else M)

omit [IsDomain R] [CharZero R] in
@[simp] theorem coeff_inventoryFactor {H i : ℕ} (hi : i ≤ H) (M : R) :
    (inventoryFactor H M).coeff i = Ring.multichoose M i := by
  rw [inventoryFactor, finsetSum_coeff]
  simp only [coeff_monomial_apply]
  simp [mem_range.mpr (Nat.lt_succ_of_le hi)]

omit [IsDomain R] [CharZero R] [BinomialRing R] in
@[simp] theorem coeff_inventoryKernel {H i : ℕ} (hi : i ≤ H) (M : R) :
    (inventoryKernel H M).coeff i = if i = 0 then 0 else M := by
  rw [inventoryKernel, finsetSum_coeff]
  simp only [coeff_monomial_apply]
  simp [mem_range.mpr (Nat.lt_succ_of_le hi)]

/-- The multiset factor solves the Euler equation through the truncation degree. -/
theorem inventoryFactor_equation (H : ℕ) (M : R) :
    X ^ (H + 1) ∣ inventoryKernel H M * inventoryFactor H M -
      X * (inventoryFactor H M).derivative := by
  apply X_pow_dvd_iff.mpr
  intro n hn
  rw [coeff_sub, coeff_X_mul_derivative, mul_comm (inventoryKernel H M), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ]
  simp only [Nat.sub_self, coeff_inventoryKernel (Nat.zero_le H), ite_true,
    mul_zero, add_zero, coeff_inventoryFactor (Nat.le_of_lt_succ hn)]
  apply sub_eq_zero.mpr
  rw [multichoose_sum, sum_mul]
  apply sum_congr rfl
  intro i hi
  have hin := mem_range.mp hi
  rw [coeff_inventoryFactor (by lia : i ≤ H), coeff_inventoryKernel (by lia : n - i ≤ H),
    ite_eq_right (by lia)]

omit [IsDomain R] [CharZero R] [BinomialRing R] in
private theorem expanded_euler {j : ℕ} (hj : 0 < j) (F : R[X]) :
    X * (expand R j F).derivative = (j : R[X]) * expand R j (X * F.derivative) := by
  simp only [derivative_expand, map_mul, expand_X]
  have hx : (X : R[X]) ^ j = X * X ^ (j - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hj]
  rw [hx]
  ring

/-- Expanding the length variable preserves the truncated inventory equation. -/
theorem expand_inventoryFactor_equation (H : ℕ) {j : ℕ} (hj : 0 < j) (M : R) :
    X ^ (H + 1) ∣ ((j : R[X]) * expand R j (inventoryKernel H M)) *
      expand R j (inventoryFactor H M) - X * (expand R j (inventoryFactor H M)).derivative := by
  obtain ⟨P, hP⟩ := inventoryFactor_equation H M
  have he := congrArg (expand R j) hP
  simp only [map_sub, map_mul, map_pow, expand_X, ← pow_mul] at he
  have hle : H + 1 ≤ j * (H + 1) := Nat.le_mul_of_pos_left _ hj
  rw [expanded_euler hj, mul_assoc, ← mul_sub]
  simp only [map_mul, expand_X]
  rw [he]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (pow_dvd_pow X hle) _) _

omit [IsDomain R] [CharZero R] [BinomialRing R] in
/-- Truncated logarithmic kernels add when the inventory factors multiply. -/
theorem prod_inventoryFactor_equation {ι : Type*} (s : Finset ι) (F K : ι → R[X]) (H : ℕ)
    (h : ∀ i ∈ s, X ^ (H + 1) ∣ K i * F i - X * (F i).derivative) :
    X ^ (H + 1) ∣ (∑ i ∈ s, K i) * (∏ i ∈ s, F i) - X * (∏ i ∈ s, F i).derivative := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [sum_insert hi, prod_insert hi, derivative_mul]
    have u := h i (mem_insert_self i t)
    have v := ih (fun j hj => h j (mem_insert_of_mem hj))
    have w := dvd_add (dvd_mul_of_dvd_left u (∏ j ∈ t, F j))
      (dvd_mul_of_dvd_right v (F i))
    convert w using 1; ring

end Generic

/-- The actual rational alphabet product, with a fixed finite jet bound. -/
def alphabetProduct (H k : ℕ) : ℚ[X][X] :=
  ∏ i : Fin H, expand ℚ[X] (i.val + 1)
    (inventoryFactor H (if i.val + 1 < k then 0 else necklacePolynomial (i.val + 1)))

/-- The sum of the length-wise Euler kernels of the rational alphabet product. -/
def alphabetProductKernel (H k : ℕ) : ℚ[X][X] :=
  ∑ i : Fin H, ((i.val + 1 : ℕ) : ℚ[X][X]) * expand ℚ[X] (i.val + 1)
    (inventoryKernel H (if i.val + 1 < k then 0 else necklacePolynomial (i.val + 1)))

/-- The rational product has the exact logarithmic kernel through H. -/
theorem alphabetProduct_equation (H k : ℕ) :
    X ^ (H + 1) ∣ alphabetProductKernel H k * alphabetProduct H k -
      X * (alphabetProduct H k).derivative :=
  prod_inventoryFactor_equation univ _ _ H
    (fun i _ => expand_inventoryFactor_equation H (Nat.succ_pos i.val) _)

private theorem expand_inventoryFactor (n j : ℕ) (M : ℚ[X]) :
    expand ℚ[X] j (inventoryFactor n M) =
      ∑ a : Fin (n + 1), monomial (j * a.val) (Ring.multichoose M a.val) := by
  rw [Fin.sum_univ_eq_sum_range (fun a => monomial (j * a) (Ring.multichoose M a))]
  simp only [inventoryFactor, map_sum, expand_monomial]
  apply sum_congr rfl
  intro a _
  rw [Nat.mul_comm]

private theorem prod_monomial {ι : Type*} (s : Finset ι) (e : ι → ℕ) (c : ι → ℚ[X]) :
    (∏ i ∈ s, monomial (e i) (c i)) = monomial (∑ i ∈ s, e i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [prod_insert hi, sum_insert hi, ih, monomial_mul_monomial]

/-- Extracting the diagonal coefficient recovers the genuine alphabet polynomial. -/
theorem alphabetProduct_coeff (n k : ℕ) : (alphabetProduct n k).coeff n = cycleAlphabet n k := by
  classical
  simp only [alphabetProduct, expand_inventoryFactor, Fintype.prod_sum, prod_monomial,
    finsetSum_coeff, coeff_monomial_apply]
  let valid (f : Fin n → Fin (n + 1)) : Prop :=
    (∑ i, (i.val + 1) * (f i).val) = n ∧ ∀ i, i.val + 1 < k → f i = 0
  let weight (f : Fin n → Fin (n + 1)) :=
    ∏ i, Ring.multichoose (necklacePolynomial (i.val + 1)) (f i).val
  have he : cycleAlphabet n k = ∑ f ∈ univ.filter valid, weight f := by
    exact (Finset.sum_subtype (p := valid) (univ.filter valid)
      (fun _ => by simp only [mem_filter, mem_univ, true_and]) weight).symm
  rw [he, sum_filter]
  apply sum_congr rfl
  intro f _
  by_cases total : (∑ i, (i.val + 1) * (f i).val) = n
  · by_cases cutoff : ∀ i : Fin n, i.val + 1 < k → f i = 0
    · rw [ite_eq_left total, ite_eq_left (show valid f from ⟨total, cutoff⟩)]
      apply prod_congr rfl
      intro i _
      by_cases hc : i.val + 1 < k
      · simp [hc, cutoff i hc]
      · rw [ite_eq_right hc]
    · rw [ite_eq_left total, ite_eq_right (show ¬valid f from fun h => cutoff h.2)]
      push Not at cutoff
      obtain ⟨i, hi, ha⟩ := cutoff
      apply Finset.prod_eq_zero (mem_univ i)
      have hn : (f i).val ≠ 0 := fun hh => ha (Fin.ext hh)
      obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp [hi, hv, Ring.multichoose_zero_succ]
  · rw [ite_eq_right total, ite_eq_right (show ¬valid f from fun h => total h.1)]

end RealRooted.LongCycleDescents.Structural

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

/-- The length-divisor kernel at a fixed outer degree. -/
def alphabetKernel (k i : ℕ) : ℚ[X] :=
  ∑ j ∈ range i, if k ≤ j + 1 ∧ j + 1 ∣ i then
    ((j + 1 : ℕ) : ℚ[X]) * necklacePolynomial (j + 1) else 0

private theorem coeff_expanded_inventoryKernel {H j i : ℕ} (hj : 0 < j) (hi : i ≤ H)
    (M : ℚ[X]) :
    (expand ℚ[X] j (inventoryKernel H M)).coeff i =
      if i = 0 then 0 else if j ∣ i then M else 0 := by
  rw [coeff_expand hj, coeff_inventoryKernel ((Nat.div_le_self i j).trans hi)]
  by_cases hz : i = 0
  · simp [hz]
  · by_cases hd : j ∣ i
    · rw [ite_eq_left hd, ite_eq_right hz,
        ite_eq_right (Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hd) hj)),
        ite_eq_left hd]
    · simp [hz, hd]

/-- Every finite jet has the same kernel coefficients in its valid degree range. -/
theorem coeff_alphabetProductKernel {H i : ℕ} (hi : i ≤ H) (k : ℕ) :
    (alphabetProductKernel H k).coeff i = alphabetKernel k i := by
  classical
  simp only [alphabetProductKernel, finsetSum_coeff]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    (((j + 1 : ℕ) : ℚ[X][X]) * expand ℚ[X] (j + 1)
      (inventoryKernel H (if j + 1 < k then 0 else necklacePolynomial (j + 1)))).coeff i)]
  have he (j : ℕ) :
      (((j + 1 : ℕ) : ℚ[X][X]) * expand ℚ[X] (j + 1)
        (inventoryKernel H (if j + 1 < k then 0 else necklacePolynomial (j + 1)))).coeff i =
      if i = 0 then 0 else if k ≤ j + 1 ∧ j + 1 ∣ i then
        ((j + 1 : ℕ) : ℚ[X]) * necklacePolynomial (j + 1) else 0 := by
    rw [← C_eq_natCast, coeff_C_mul,
      coeff_expanded_inventoryKernel (Nat.succ_pos _) hi]
    by_cases hz : i = 0
    · simp [hz]
    · by_cases hd : j + 1 ∣ i <;> by_cases hk : j + 1 < k <;> simp [hz, hd, hk, not_lt.mp]
  simp_rw [he]
  by_cases hz : i = 0
  · simp [hz, alphabetKernel]
  · simp only [ite_eq_right hz]
    unfold alphabetKernel
    symm
    apply sum_subset (range_mono hi)
    intro j _ hj
    apply ite_eq_right
    rintro ⟨_, hd⟩
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hd
    have hn : i ≤ j := by simpa only [mem_range, not_lt] using hj
    lia

/-- Rational alphabet coefficients defined by their Euler recurrence. -/
def alphabetRow (k n : ℕ) : ℚ[X] :=
  match n with
  | 0 => 1
  | m + 1 => C (((m + 1 : ℕ) : ℚ)⁻¹) *
      ∑ i : Fin (m + 1), alphabetKernel k (m + 1 - i.val) * alphabetRow k i.val
termination_by n

@[simp] theorem alphabetRow_zero (k : ℕ) : alphabetRow k 0 = 1 := by rw [alphabetRow]

/-- The defining recurrence with its positive integer denominator cleared. -/
theorem alphabetRow_equation (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (n : ℚ[X]) * alphabetRow k n =
      ∑ i ∈ range n, alphabetKernel k (n - i) * alphabetRow k i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [alphabetRow, ← C_eq_natCast, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ (by positivity : ((m + 1 : ℕ) : ℚ) ≠ 0), C_1, one_mul,
    Fin.sum_univ_eq_sum_range (fun i => alphabetKernel k (m + 1 - i) * alphabetRow k i)]

private theorem alphabetProduct_coeff_zero (H k : ℕ) : (alphabetProduct H k).coeff 0 = 1 := by
  rw [alphabetProduct, coeff_zero_prod]
  apply prod_eq_one
  intro i _
  rw [coeff_expand (Nat.succ_pos _)]
  simp [coeff_inventoryFactor]

/-- Euler uniqueness identifies every finite-product jet with the canonical row. -/
theorem alphabetProduct_coeff_eq_row {H n : ℕ} (hn : n ≤ H) (k : ℕ) :
    (alphabetProduct H k).coeff n = alphabetRow k n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hz : n = 0
    · subst n
      rw [alphabetProduct_coeff_zero, alphabetRow_zero]
    · have hp := X_pow_dvd_iff.mp (alphabetProduct_equation H k) n (by lia)
      rw [coeff_sub, coeff_X_mul_derivative, mul_comm (alphabetProductKernel H k), coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
        Nat.sub_self, coeff_alphabetProductKernel (Nat.zero_le H)] at hp
      simp only [alphabetKernel, range_zero, sum_empty, mul_zero, add_zero] at hp
      have he : (∑ i ∈ range n, (alphabetProduct H k).coeff i *
          (alphabetProductKernel H k).coeff (n - i)) =
          ∑ i ∈ range n, alphabetKernel k (n - i) * alphabetRow k i := by
        apply sum_congr rfl
        intro i hi
        have hin := mem_range.mp hi
        rw [ih i hin (by lia), coeff_alphabetProductKernel (by lia : n - i ≤ H)]
        ring
      rw [he] at hp
      apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hz : (n : ℚ[X]) ≠ 0)
      exact (sub_eq_zero.mp hp).symm.trans (alphabetRow_equation k hz).symm

/-- The canonical row is the genuine rational Gessel--Reutenauer alphabet polynomial. -/
theorem alphabetRow_eq_cycleAlphabet (n k : ℕ) : alphabetRow k n = cycleAlphabet n k := by
  rw [← alphabetProduct_coeff_eq_row le_rfl, alphabetProduct_coeff]

/-- The recurrence computes the original real alphabet polynomial for every positive size. -/
theorem map_alphabetRow {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (alphabetRow k n).map (Rat.castHom ℝ) = descentAlphabetPolynomial n k := by
  rw [alphabetRow_eq_cycleAlphabet, map_cycleAlphabet hn]

end RealRooted.LongCycleDescents.Structural

open Polynomial Finset
open scoped ArithmeticFunction.Moebius

namespace RealRooted.LongCycleDescents.Structural

private theorem reflect_sum {R ι : Type*} [Semiring R] (s : Finset ι)
    (f : ι → R[X]) (n : ℕ) :
    reflect n (∑ i ∈ s, f i) = ∑ i ∈ s, reflect n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [sum_insert ha, reflect_add, ih, sum_insert ha]

/-- Degree bound for a primitive-necklace polynomial. -/
theorem natDegree_necklacePolynomial_le (j : ℕ) :
    (necklacePolynomial j).natDegree ≤ j := by
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_sum_le_of_forall_le
  intro d _
  exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le _).trans (Nat.div_le_self _ _))

/-- The alphabet recurrence kernel has degree at most its outer degree. -/
theorem natDegree_alphabetKernel_le (k i : ℕ) : (alphabetKernel k i).natDegree ≤ i := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  by_cases h : k ≤ j + 1 ∧ j + 1 ∣ i
  · simp only [ite_eq_left h]
    rw [← C_eq_natCast]
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_necklacePolynomial_le _).trans (by simpa using mem_range.mp hj))
  · simp [h]

/-- The faithful alphabet row is supported in degrees at most its size. -/
theorem natDegree_alphabetRow_le (n k : ℕ) : (alphabetRow k n).natDegree ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [← natDegree_map_eq_of_injective (Rat.castHom ℝ).injective,
      map_alphabetRow (Nat.pos_of_ne_zero hn)]
    exact natDegree_descentAlphabetPolynomial_le n k

/-- The alphabet polynomial reflected at the permutation size. -/
def lossRow (k n : ℕ) : ℚ[X] := reflect n (alphabetRow k n)

/-- Reflection at the permutation size keeps the degree at most that size. -/
theorem natDegree_lossRow_le (k n : ℕ) : (lossRow k n).natDegree ≤ n := by
  exact natDegree_reflect_le.trans (max_le le_rfl (natDegree_alphabetRow_le n k))

/-- The reflected divisor kernel, written without rational denominators. -/
def lossKernel (k i : ℕ) : ℚ[X] :=
  ∑ j ∈ range i, if k ≤ j + 1 ∧ j + 1 ∣ i then
    ∑ d ∈ (j + 1).divisors, C (μ d : ℚ) * X ^ (i - (j + 1) / d) else 0

/-- Reflection cancels the length denominator in each necklace polynomial. -/
theorem reflect_alphabetKernel (k i : ℕ) : reflect i (alphabetKernel k i) = lossKernel k i := by
  rw [alphabetKernel, reflect_sum, lossKernel]
  apply sum_congr rfl
  intro j hj
  by_cases h : k ≤ j + 1 ∧ j + 1 ∣ i
  · rw [ite_eq_left h, ite_eq_left h, ← C_eq_natCast, necklacePolynomial, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ (by positivity : ((j + 1 : ℕ) : ℚ) ≠ 0), C_1, one_mul, reflect_sum]
    apply sum_congr rfl
    intro d _
    rw [reflect_C_mul_X_pow, revAt_le]
    exact (Nat.div_le_self _ _).trans (by simpa using mem_range.mp hj)
  · simp [h]

@[simp] theorem lossRow_zero (k : ℕ) : lossRow k 0 = 1 := by simp [lossRow]

/-- The exact recurrence in degree-loss coordinates. -/
theorem lossRow_equation (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (n : ℚ[X]) * lossRow k n =
      ∑ i ∈ range n, lossKernel k (n - i) * lossRow k i := by
  have he := congrArg (reflect n) (alphabetRow_equation k hn)
  rw [← C_eq_natCast, reflect_C_mul, reflect_sum] at he
  rw [← C_eq_natCast]
  change C (n : ℚ) * lossRow k n = _ at he
  refine he.trans (sum_congr rfl ?_)
  intro i hi
  have hin := mem_range.mp hi
  conv_lhs => arg 1; rw [show n = (n - i) + i by lia]
  rw [reflect_mul _ _ (natDegree_alphabetKernel_le _ _)
    (natDegree_alphabetRow_le _ _), reflect_alphabetKernel]
  rfl

/-- The faithful alphabet recurrence is the canonical Euler coefficient row. -/
theorem lossRow_eq_eulerCoeff (k : ℕ) :
    lossRow k = PowerSeries.eulerCoeff (lossKernel k) := by
  apply PowerSeries.eulerCoeff_unique
  · exact lossRow_zero k
  · intro n hn
    simpa only [smul_eq_C_mul, C_eq_natCast] using lossRow_equation k hn

end RealRooted.LongCycleDescents.Structural
