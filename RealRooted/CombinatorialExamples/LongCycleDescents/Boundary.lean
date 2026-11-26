/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

import RealRooted.Applications.EulerianCompendium.DerangementReciprocal
public import RealRooted.Basic.Coefficients
import RealRooted.CombinatorialExamples.EulerianStatistic
public import RealRooted.CombinatorialExamples.LongCycleDescents.Coefficients
public import RealRooted.CombinatorialExamples.LongCycleDescents.Words
public import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
import Mathlib.Tactic

/-!
# Classical cutoffs and checked negative grids

Eulerian and derangement descent theorems handle cutoffs one and two. Nonnegative
coefficients prove nonvanishing and root signs. A checked negative grid proves
splitting and simplicity for every nonzero nonnegative mixture on that grid.
The exceptional rows at sizes four and five have explicit factorizations.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0).
-/

@[expose] public noncomputable section

namespace RealRooted.LongCycleDescents

open Polynomial Finset

/-- The original integer permutation sum, with real coefficients. -/
def realDescentPolynomial (n k : ℕ) : ℝ[X] :=
  (descentPolynomial n k).map (Int.castRingHom ℝ)

/-- Nonnegative combinations over all the cutoffs in the manuscript's second theorem. -/
def mixture (n : ℕ) (w : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Icc 1 n, C (w k) * realDescentPolynomial n k

/-- Cutoff one imposes no cycle restriction. -/
theorem hasLongCycles_one {n : ℕ} (σ : Equiv.Perm (Fin n)) : HasLongCycles 1 σ := by
  intro x j hj hk
  lia

/-- Cutoff two is exactly the derangement condition on the original labels. -/
theorem hasLongCycles_two_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    HasLongCycles 2 σ ↔ ∀ i, σ i ≠ i := by
  refine ⟨fun h ↦ ne_fixed_of_allowed h (by decide), ?_⟩
  intro h i j hj hk
  have eq : j = 1 := by lia
  simpa only [eq, pow_one] using h i

/-- The full cyclic rotation is allowed whenever the cutoff is at most the size. -/
theorem hasLongCycles_finRotate {n k : ℕ} (hk : k ≤ n) :
    HasLongCycles k (finRotate n) := by
  by_cases hn : 2 ≤ n
  · have support := support_finRotate_of_le hn
    have cycle := isCycle_finRotate_of_le hn
    have order : orderOf (finRotate n) = n := by
      rw [cycle.orderOf, support, card_univ, Fintype.card_fin]
    intro x j hj hjk
    have hx : x ∈ (finRotate n).support := by rw [support]; exact mem_univ _
    rw [← cycle.support_pow_of_pos_of_lt_orderOf hj (by rw [order]; exact hjk.trans_le hk),
      Equiv.Perm.mem_support] at hx
    exact hx
  · intro x j hj hjk
    lia

/-- Every coefficient counts a set of original permutations and is nonnegative. -/
theorem realDescentPolynomial_hasNonnegCoeffs (n k : ℕ) :
    HasNonnegCoeffs (realDescentPolynomial n k) := by
  classical
  intro i
  rw [realDescentPolynomial, coeff_map, coeff_descentPolynomial]
  change 0 ≤ (↑(∑ σ : Equiv.Perm (Fin n),
    if HasLongCycles k σ ∧ σ.descentCount = i then (1 : ℤ) else 0) : ℝ)
  exact_mod_cast (sum_nonneg (fun σ (_ : σ ∈ univ) ↦
    show (0 : ℤ) ≤ if HasLongCycles k σ ∧ σ.descentCount = i then 1 else 0 from by
      split <;> norm_num))

open Classical in
/-- Evaluation at one counts exactly the permutations satisfying the cycle cutoff. -/
theorem realDescentPolynomial_eval_one (n k : ℕ) :
    (realDescentPolynomial n k).eval 1 =
      ((univ.filter fun σ : Equiv.Perm (Fin n) ↦ HasLongCycles k σ).card : ℝ) := by
  classical
  simp only [realDescentPolynomial, descentPolynomial, Polynomial.map_sum,
    Polynomial.eval_finsetSum]
  simp only [apply_ite, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_zero,
    eval_pow, eval_X, one_pow, eval_zero]
  simp only [sum_boole]

/-- There is at least one allowed permutation at every cutoff up to the size. -/
theorem realDescentPolynomial_eval_one_pos {n k : ℕ} (hk : k ≤ n) :
    0 < (realDescentPolynomial n k).eval 1 := by
  classical
  rw [realDescentPolynomial_eval_one]
  exact_mod_cast (card_pos.mpr ⟨finRotate n,
    mem_filter.mpr ⟨mem_univ _, hasLongCycles_finRotate hk⟩⟩)

/-- Every original row with a cutoff up to the size is nonzero. -/
theorem realDescentPolynomial_ne_zero {n k : ℕ} (hk : k ≤ n) :
    realDescentPolynomial n k ≠ 0 := by
  intro hz
  have pos := realDescentPolynomial_eval_one_pos hk
  rw [hz, eval_zero] at pos
  exact lt_irrefl _ pos

/-- Every real root of an original row is nonpositive, independently of splitting. -/
theorem realDescentPolynomial_roots_nonpos (n k : ℕ) :
    ∀ z ∈ (realDescentPolynomial n k).roots, z ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs (realDescentPolynomial_hasNonnegCoeffs n k)

/-- Nonnegative weights preserve the nonnegative coefficient property. -/
theorem mixture_hasNonnegCoeffs {n : ℕ} {w : ℕ → ℝ}
    (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) : HasNonnegCoeffs (mixture n w) := by
  apply hasNonnegCoeffs_finsetSum
  intro k hk
  exact (hasNonnegCoeffs_C (hw k hk)).mul (realDescentPolynomial_hasNonnegCoeffs n k)

/-- A nonzero nonnegative choice of weights gives a nonzero original mixture. -/
theorem mixture_ne_zero {n : ℕ} {w : ℕ → ℝ}
    (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) (pos : ∃ k ∈ Icc 1 n, 0 < w k) :
    mixture n w ≠ 0 := by
  have atOne : 0 < (mixture n w).eval 1 := by
    simp only [mixture, Polynomial.eval_finsetSum, eval_mul, eval_C]
    apply sum_pos'
    · intro k hk
      exact mul_nonneg (hw k hk) (realDescentPolynomial_eval_one_pos (mem_Icc.mp hk).2).le
    · obtain ⟨k, hk, hp⟩ := pos
      exact ⟨k, hk, mul_pos hp (realDescentPolynomial_eval_one_pos (mem_Icc.mp hk).2)⟩
  intro hz
  rw [hz, eval_zero] at atOne
  exact lt_irrefl _ atOne

/-- Every real root of every nonnegative original mixture is nonpositive. -/
theorem mixture_roots_nonpos {n : ℕ} {w : ℕ → ℝ}
    (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) : ∀ z ∈ (mixture n w).roots, z ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs (mixture_hasNonnegCoeffs hw)

/-- Cutoff one splits by the existing permutation Eulerian theorem. -/
theorem realDescentPolynomial_one_splits {n : ℕ} (hn : 0 < n) :
    (realDescentPolynomial n 1).Splits := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have eq : realDescentPolynomial (m + 1) 1 =
      ((univ : Finset (Equiv.Perm (Fin (m + 1)))).genPoly
        Equiv.Perm.descentCount : ℝ[X]) := by
    classical
    simp only [realDescentPolynomial, descentPolynomial, hasLongCycles_one, ite_true,
      Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X, genPoly]
  rw [eq]
  exact (isRealRooted_genPoly_univ_descentCount m).2

/-- Cutoff two splits by the existing theorem for actual derangement descents. -/
theorem realDescentPolynomial_two_splits {n : ℕ} (hn : 2 ≤ n) :
    (realDescentPolynomial n 2).Splits := by
  have eq : realDescentPolynomial n 2 = EulerianCompendium.derangementDescentPolynomial n := by
    classical
    simp only [realDescentPolynomial, descentPolynomial, Polynomial.map_sum,
      EulerianCompendium.derangementDescentPolynomial, hasLongCycles_two_iff,
      apply_ite, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_zero]
  rw [eq]
  exact EulerianCompendium.derangementDescentPolynomial_splits n hn

end RealRooted.LongCycleDescents

namespace RealRooted.LongCycleDescents.Necklace

open Polynomial Finset

/-- An exact rational with a denominator that is a power of two. -/
structure Dyadic where
  /-- The signed numerator. -/
  numer : ℤ
  /-- The exponent of the power-of-two denominator. -/
  shift : ℕ
  deriving Inhabited

namespace Dyadic

/-- The zero dyadic number. -/
def zero : Dyadic := ⟨0, 0⟩

/-- Interpret a dyadic number as a real number. -/
noncomputable def value (x : Dyadic) : ℝ := (x.numer : ℝ) / (2 : ℝ) ^ x.shift

/-- The zero dyadic number represents real zero. -/
@[simp] theorem value_zero : zero.value = 0 := by simp [zero, value]

/-- Compare dyadic numbers by exact shifted-integer cross multiplication. -/
def less (a b : Dyadic) : Bool :=
  decide ((a.numer <<< b.shift) < (b.numer <<< a.shift))

/-- The shifted-integer comparison agrees with the real order. -/
theorem less_iff (a b : Dyadic) : a.less b = true ↔ a.value < b.value := by
  simp only [less, decide_eq_true_eq, value, lt_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ b.shift)]
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ a.shift)]
  simp only [Int.shiftLeft_eq]
  exact_mod_cast (Iff.rfl :
    (a.numer : ℝ) * (2 : ℝ) ^ b.shift < (b.numer : ℝ) * (2 : ℝ) ^ a.shift ↔ _)

end Dyadic

/-- Homogenized Horner recursion with a supplied exponent for the denominator. -/
def dyadicHorner (x : Dyadic) : ℕ → List ℤ → ℤ
  | _, [] => 0
  | n, a :: as => (a <<< (x.shift * n)) + x.numer * dyadicHorner x (n - 1) as

/-- Integer Horner evaluation with denominator `2 ^ (x.shift * cs.length)`. -/
def homogeneous (x : Dyadic) (cs : List ℤ) : ℤ := dyadicHorner x cs.length cs

/-- Homogenized integer Horner evaluation clears a positive dyadic denominator. -/
theorem homogeneous_eq_eval (x : Dyadic) (cs : List ℤ) :
    (homogeneous x cs : ℝ) = (2 : ℝ) ^ (x.shift * cs.length) * (coefficientPolynomial cs).eval
      x.value := by
  induction cs with
  | nil => simp [homogeneous, dyadicHorner, coefficientPolynomial]
  | cons a as ih =>
    change (↑((a <<< (x.shift * (as.length + 1))) + x.numer * homogeneous x as) : ℝ) = _
    rw [Int.shiftLeft_eq]
    push_cast
    rw [ih]
    simp only [List.length_cons, coefficientPolynomial, eval_add, eval_C, eval_mul, eval_X,
      Dyadic.value]
    rw [Nat.mul_succ, pow_add]
    have hd : (2 : ℝ) ^ x.shift ≠ 0 := by positivity
    field_simp

/-- Check a prescribed strict sign using only integer arithmetic. -/
def positiveAt (negative : Bool) (cs : List ℤ) (x : Dyadic) : Bool :=
  if negative then decide (homogeneous x cs < 0) else decide (0 < homogeneous x cs)

/-- The integer sign checker has exactly the prescribed real-evaluation meaning. -/
theorem positiveAt_iff (negative : Bool) (cs : List ℤ) (x : Dyadic) :
    positiveAt negative cs x = true ↔
      if negative then (coefficientPolynomial cs).eval x.value < 0 else 0 <
        (coefficientPolynomial cs).eval x.value := by
  have hp : 0 < (2 : ℝ) ^ (x.shift * cs.length) := by positivity
  cases negative <;> simp only [positiveAt, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
  · rw [← Int.cast_pos (R := ℝ), homogeneous_eq_eval]
    exact mul_pos_iff_of_pos_left hp
  · rw [← Int.cast_lt (R := ℝ), Int.cast_zero, homogeneous_eq_eval]
    exact ⟨fun h ↦ (mul_neg_iff.mp h).elim (fun H ↦ H.2)
      (fun H ↦ ((not_lt_of_ge hp.le) H.1).elim), mul_neg_of_pos_of_neg hp⟩

/-- An ascending list bounds its polynomial degree by one less than its length. -/
theorem natDegree_coefficientPolynomial_le (cs : List ℤ) : (coefficientPolynomial cs).natDegree
  ≤ cs.length - 1 := by
  induction cs with
  | nil => simp [coefficientPolynomial]
  | cons a as ih =>
    cases as with
    | nil => simp [coefficientPolynomial]
    | cons b bs =>
      rw [coefficientPolynomial]
      apply (natDegree_add_le _ _).trans
      rw [Polynomial.natDegree_C, max_eq_right (Nat.zero_le _)]
      have h := natDegree_mul_le (p := (X : Polynomial ℝ)) (q := coefficientPolynomial (b :: bs))
      simp only [natDegree_X, List.length_cons] at h ih ⊢
      lia

/-- Check the signs, strict order, and negative location of a complete quotient grid. -/
def negativeMesh (cs : List ℤ) (nodes : Array Dyadic) : Bool :=
  decide (0 < nodes.size ∧ nodes.size = cs.length) &&
  positiveAt false cs Dyadic.zero &&
  (List.range nodes.size).all (fun i ↦
    (nodes.getD i Dyadic.zero).less Dyadic.zero &&
      positiveAt (decide ((nodes.size - 1 - i) % 2 = 1)) cs
        (nodes.getD i Dyadic.zero)) &&
  (List.range (nodes.size - 1)).all (fun i ↦
    (nodes.getD i Dyadic.zero).less (nodes.getD (i + 1) Dyadic.zero))

/-- A successful grid check makes the quotient positive at zero. -/
theorem negativeMesh_eval_zero_pos {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) : 0 < (coefficientPolynomial cs).eval 0 := by
  have hz := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).2
  simpa only [Bool.false_eq_true, ite_false, Dyadic.value_zero] using
    (positiveAt_iff false cs Dyadic.zero).mp hz

/-- Every checked grid value has the prescribed alternating strict sign. -/
theorem negativeMesh_sign {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) {i : ℕ} (hi : i < nodes.size) :
    if (nodes.size - 1 - i) % 2 = 1 then
      (coefficientPolynomial cs).eval (nodes.getD i Dyadic.zero).value < 0 else
      0 < (coefficientPolynomial cs).eval (nodes.getD i Dyadic.zero).value := by
  have values := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  have sign := (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp values i (List.mem_range.mpr hi))).2
  simpa only [decide_eq_true_eq] using (positiveAt_iff _ _ _).mp sign

/-- The number of checked nodes equals the coefficient-list length and is positive. -/
theorem negativeMesh_size {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) : 0 < nodes.size ∧ nodes.size = cs.length := by
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).1

/-- Every checked mesh node lies strictly to the left of zero. -/
theorem negativeMesh_node_neg {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) {i : ℕ} (hi : i < nodes.size) :
    (nodes.getD i Dyadic.zero).value < 0 := by
  have values := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  have neg := (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp values i (List.mem_range.mpr hi))).1
  simpa only [Dyadic.value_zero] using (Dyadic.less_iff _ _).mp neg

/-- A checked mesh is strictly increasing when indexed by the interval endpoints. -/
theorem negativeMesh_strictMono {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) :
    StrictMono (fun i : Fin (nodes.size - 1 + 1) ↦
      (nodes.getD i.val Dyadic.zero).value) := by
  have order := (Bool.and_eq_true_iff.mp h).2
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact (Dyadic.less_iff _ _).mp
    (List.all_eq_true.mp order i.val (List.mem_range.mpr i.isLt))

/-- Alternating strict signs on the dyadic grid give opposite signs across every gap. -/
theorem eval_mul_eval_neg_of_alternating_signs {p : ℝ[X]} {nodes : Array Dyadic}
    (sign : ∀ i < nodes.size, if (nodes.size - 1 - i) % 2 = 1 then
      p.eval (nodes.getD i Dyadic.zero).value < 0 else
      0 < p.eval (nodes.getD i Dyadic.zero).value) (i : Fin (nodes.size - 1)) :
    p.eval (nodes.getD i.val Dyadic.zero).value *
      p.eval (nodes.getD (i.val + 1) Dyadic.zero).value < 0 := by
  have hi := i.isLt
  have a := sign i.val (by lia)
  have b := sign (i.val + 1) (by lia)
  by_cases parity : (nodes.size - 1 - i.val) % 2 = 1
  · have next : (nodes.size - 1 - (i.val + 1)) % 2 ≠ 1 := by lia
    rw [ite_eq_left parity] at a
    rw [ite_eq_right next] at b
    exact mul_neg_of_neg_of_pos a b
  · have next : (nodes.size - 1 - (i.val + 1)) % 2 = 1 := by lia
    rw [ite_eq_right parity] at a
    rw [ite_eq_left next] at b
    exact mul_neg_of_pos_of_neg a b

/-- A checked quotient has exactly one root in each open interval of the common grid. -/
theorem negativeMesh_ordered_roots {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) :
    ∃ r : Fin (nodes.size - 1) → ℝ, StrictMono r ∧
      (∀ i, (nodes.getD i.val Dyadic.zero).value < r i ∧
        r i < (nodes.getD (i.val + 1) Dyadic.zero).value ∧
        (coefficientPolynomial cs).IsRoot (r i)) ∧
      ∀ z ∈ (coefficientPolynomial cs).roots, ∃ i, z = r i := by
  have pos := negativeMesh_eval_zero_pos h
  have nonzero : coefficientPolynomial cs ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at pos
    exact lt_irrefl _ pos
  exact (Polynomial.splits_nodup_ordered_roots_of_strict_sign_changes nonzero
    ((natDegree_coefficientPolynomial_le cs).trans_eq
      (congrArg (· - 1) (negativeMesh_size h).2.symm)) _
    (negativeMesh_strictMono h) (eval_mul_eval_neg_of_alternating_signs (fun _ hi ↦
      negativeMesh_sign h hi))).2

/-- A sound sign grid yields all simple negative roots of its quotient polynomial. -/
theorem negativeMesh_splits {cs : List ℤ} {nodes : Array Dyadic}
    (h : negativeMesh cs nodes = true) :
    (coefficientPolynomial cs).natDegree = nodes.size - 1 ∧
      (coefficientPolynomial cs).Splits ∧ (coefficientPolynomial cs).roots.Nodup ∧
      ∀ z ∈ (coefficientPolynomial cs).roots, z < 0 := by
  have pos := negativeMesh_eval_zero_pos h
  have nonzero : coefficientPolynomial cs ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at pos
    exact lt_irrefl _ pos
  have result := Polynomial.splits_nodup_roots_of_strict_sign_changes nonzero
    ((natDegree_coefficientPolynomial_le cs).trans_eq
      (congrArg (· - 1) (negativeMesh_size h).2.symm)) _
    (negativeMesh_strictMono h) (eval_mul_eval_neg_of_alternating_signs (fun _ hi ↦
      negativeMesh_sign h hi))
  refine ⟨result.1, result.2.1, result.2.2.1, ?_⟩
  intro z hz
  exact (result.2.2.2 z hz).2.trans
    (negativeMesh_node_neg h (Nat.sub_lt (negativeMesh_size h).1 (by decide)))

end RealRooted.LongCycleDescents.Necklace

namespace RealRooted.LongCycleDescents.Necklace

open Polynomial Finset

/-- Quotient coefficients, reconstructed afresh rather than supplied as certificate data. -/
def quotientCoefficients (n k : ℕ) : List ℤ :=
  ((packedDescentRow n k).drop 1).take (n - 2)

/-- Check the two zero endpoint coefficients and the common negative quotient grid. -/
def descentMesh (n k : ℕ) (nodes : Array Dyadic) : Bool :=
  let cs := quotientCoefficients n k
  decide (packedDescentRow n k = (0 :: cs) ++ [0]) && negativeMesh cs nodes

/-- A successful check identifies the coefficients of the original permutation row. -/
theorem descentMesh_coefficients {n k : ℕ} {nodes : Array Dyadic}
    (h : descentMesh n k nodes = true) :
    descentRowDP n k = (0 :: quotientCoefficients n k) ++ [0] := by
  have eq := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  rwa [packedDescentRow_eq] at eq

/-- A checked row has a simple zero and all remaining zeros simple and negative. -/
theorem descentMesh_splits {n k : ℕ} (hn : 0 < n) {nodes : Array Dyadic}
    (h : descentMesh n k nodes = true) :
    let p := (descentPolynomial n k).map (Int.castRingHom ℝ)
    p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧
      p.natDegree = nodes.size ∧ (∀ z ∈ p.roots, z ≤ 0) := by
  have mesh := (Bool.and_eq_true_iff.mp h).2
  have eq := row_eq_of_checkedCoeffs hn (descentMesh_coefficients h)
  rw [eq]
  have result := negativeMesh_splits mesh
  have pos := negativeMesh_eval_zero_pos mesh
  have ne : coefficientPolynomial (quotientCoefficients n k) ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at pos
    exact lt_irrefl _ pos
  have notRoot : (0 : ℝ) ∉ (coefficientPolynomial (quotientCoefficients n k)).roots := by
    intro hz
    have zero := (mem_roots ne).mp hz
    exact pos.ne' zero
  have roots : (X * coefficientPolynomial (quotientCoefficients n k)).roots =
      {0} + (coefficientPolynomial (quotientCoefficients n k)).roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero ne), roots_X]
  refine ⟨Splits.X.mul result.2.1, ?_, ?_, ?_, ?_⟩
  · rw [roots, Multiset.singleton_add, Multiset.nodup_cons]
    exact ⟨notRoot, result.2.2.1⟩
  · rw [roots]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self 0))
  · rw [natDegree_mul (X_ne_zero) ne, natDegree_X, result.1]
    have sizes := (negativeMesh_size mesh).1
    lia
  · intro z hz
    rw [roots, Multiset.mem_add, Multiset.mem_singleton] at hz
    exact hz.elim (fun e ↦ e ▸ le_rfl) (fun e ↦ (result.2.2.2 z e).le)

end RealRooted.LongCycleDescents.Necklace

namespace RealRooted.LongCycleDescents.Necklace

open Polynomial Finset

/-- The quotient sum is positive at zero and has the same alternating signs as every row. -/
private theorem quotient_sum_signs {n : ℕ} {s : Finset ℕ} {cutoff : ℕ → ℕ} {nodes : Array Dyadic}
    (mesh : ∀ k ∈ s, descentMesh n (cutoff k) nodes = true) {w : ℕ → ℝ}
    (hw : ∀ k ∈ s, 0 ≤ w k) (pos : ∃ k ∈ s, 0 < w k) :
    let q := ∑ k ∈ s, C (w k) * coefficientPolynomial (quotientCoefficients n (cutoff k))
    0 < q.eval 0 ∧ ∀ i < nodes.size, if (nodes.size - 1 - i) % 2 = 1 then
      q.eval (nodes.getD i Dyadic.zero).value < 0 else
      0 < q.eval (nodes.getD i Dyadic.zero).value := by
  dsimp only
  have checked k hk := (Bool.and_eq_true_iff.mp (mesh k hk)).2
  have hz k hk := negativeMesh_eval_zero_pos (checked k hk)
  constructor
  · simp only [Polynomial.eval_finsetSum, eval_mul, eval_C]
    exact sum_pos' (fun k hk ↦ mul_nonneg (hw k hk) (hz k hk).le)
      (pos.imp fun k hk ↦ ⟨hk.1, mul_pos hk.2 (hz k hk.1)⟩)
  · intro i hi
    have signs k hk := negativeMesh_sign (checked k hk) hi
    by_cases parity : (nodes.size - 1 - i) % 2 = 1
    · simp only [ite_eq_left parity, Polynomial.eval_finsetSum, eval_mul, eval_C] at signs ⊢
      exact sum_neg' (fun k hk ↦ mul_nonpos_of_nonneg_of_nonpos (hw k hk) (signs k hk).le)
        (pos.imp fun k hk ↦ ⟨hk.1, mul_neg_of_pos_of_neg hk.2 (signs k hk.1)⟩)
    · simp only [ite_eq_right parity, Polynomial.eval_finsetSum, eval_mul, eval_C] at signs ⊢
      exact sum_pos' (fun k hk ↦ mul_nonneg (hw k hk) (signs k hk).le)
        (pos.imp fun k hk ↦ ⟨hk.1, mul_pos hk.2 (signs k hk.1)⟩)

/-- All nonzero nonnegative mixtures on a checked common grid split with simple roots. -/
theorem descentMesh_sum_splits {n : ℕ} (hn : 0 < n) {s : Finset ℕ}
    {nodes : Array Dyadic} {cutoff : ℕ → ℕ} (mesh : ∀ k ∈ s, descentMesh n (cutoff k) nodes = true)
    {w : ℕ → ℝ} (hw : ∀ k ∈ s, 0 ≤ w k) (pos : ∃ k ∈ s, 0 < w k) :
    let p := ∑ k ∈ s, C (w k) * (descentPolynomial n (cutoff k)).map (Int.castRingHom ℝ)
    p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ (∀ z ∈ p.roots, z ≤ 0) := by
  classical
  let q := ∑ k ∈ s, C (w k) * coefficientPolynomial (quotientCoefficients n (cutoff k))
  have checked k hk := (Bool.and_eq_true_iff.mp (mesh k hk)).2
  have signs := quotient_sum_signs mesh hw pos
  obtain ⟨k, hk, _⟩ := pos
  have nodePos := (negativeMesh_size (checked k hk)).1
  have ne : q ≠ 0 := by
    intro hz
    have atZero := signs.1
    change 0 < q.eval 0 at atZero
    rw [hz, eval_zero] at atZero
    exact lt_irrefl _ atZero
  have bound : q.natDegree ≤ nodes.size - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_C_mul_le _ _).trans ((natDegree_coefficientPolynomial_le _).trans_eq
      (congrArg (· - 1) (negativeMesh_size (checked j hj)).2.symm))
  have roots := Polynomial.splits_nodup_roots_of_strict_sign_changes ne bound _
    (negativeMesh_strictMono (checked k hk))
    (eval_mul_eval_neg_of_alternating_signs signs.2)
  have location {z : ℝ} (hz : z ∈ q.roots) : z < 0 :=
    (roots.2.2.2 z hz).2.trans
      (negativeMesh_node_neg (checked k hk) (Nat.sub_lt nodePos (by decide)))
  have zeroNot : (0 : ℝ) ∉ q.roots := fun hz ↦ (lt_irrefl _) (location hz)
  have eq : (∑ j ∈ s, C (w j) * (descentPolynomial n (cutoff j)).map (Int.castRingHom ℝ)) =
      X * q := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [row_eq_of_checkedCoeffs hn
      (descentMesh_coefficients (mesh j hj))]
    ring
  rw [eq]
  have rootEq : (X * q).roots = {0} + q.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero ne), roots_X]
  refine ⟨Splits.X.mul roots.2.1, ?_, ?_, ?_⟩
  · rw [rootEq, Multiset.singleton_add, Multiset.nodup_cons]
    exact ⟨zeroNot, roots.2.2.1⟩
  · rw [rootEq]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self 0))
  · intro z hz
    rw [rootEq, Multiset.mem_add, Multiset.mem_singleton] at hz
    exact hz.elim (fun e ↦ e ▸ le_rfl) (fun e ↦ (location e).le)

end RealRooted.LongCycleDescents.Necklace

namespace RealRooted.LongCycleDescents

open Polynomial Necklace

/-- Four-letter derangements have a double root at minus two. -/
theorem realDescentPolynomial_four_two :
    realDescentPolynomial 4 2 = X * (X + C 2) ^ 2 := by
  have counts : descentRowDP 4 2 = [0, 4, 4, 1] := by decide +kernel
  rw [realDescentPolynomial, ← coefficientPolynomial_descentRowDP (by decide) 2, counts]
  simp only [coefficientPolynomial, Int.cast_ofNat, Int.cast_zero, C_0, zero_add,
    mul_zero, add_zero, Int.cast_one, C_1, C_ofNat]
  ring

/-- Every cutoff from three through five gives the same five-letter polynomial. -/
theorem realDescentPolynomial_five {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 5) :
    realDescentPolynomial 5 k = C 6 * X * (X + C 1) ^ 2 := by
  have counts : ∀ i : Fin 3, descentRowDP 5 (i.val + 3) = [0, 6, 12, 6, 0] := by
    decide +kernel
  let i : Fin 3 := ⟨k - 3, by lia⟩
  have ki : i.val + 3 = k := Nat.sub_add_cancel hk
  have row := counts i
  rw [ki] at row
  rw [realDescentPolynomial, ← coefficientPolynomial_descentRowDP (by decide) k, row]
  simp only [coefficientPolynomial, Int.cast_ofNat, Int.cast_zero, C_0, zero_add,
    mul_zero, add_zero, C_1, C_ofNat]
  ring

/-- The exceptional five-letter row still splits over the reals. -/
theorem realDescentPolynomial_five_splits {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 5) :
    (realDescentPolynomial 5 k).Splits := by
  rw [realDescentPolynomial_five hk kn]
  exact ((Splits.C _).mul Splits.X).mul ((Splits.X_add_C _).pow _)

/-- The exceptional four-letter derangement row has exactly the asserted repeated root. -/
theorem realDescentPolynomial_four_two_roots :
    (realDescentPolynomial 4 2).roots = {0} + 2 • ({-2} : Multiset ℝ) := by
  rw [realDescentPolynomial_four_two,
    roots_mul (mul_ne_zero X_ne_zero (pow_ne_zero _ (monic_X_add_C 2).ne_zero)),
    roots_X, roots_pow, roots_X_add_C]

/-- The exceptional five-letter row has exactly one double negative root and one zero. -/
theorem realDescentPolynomial_five_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 5) :
    (realDescentPolynomial 5 k).roots = {0} + 2 • ({-1} : Multiset ℝ) := by
  rw [realDescentPolynomial_five hk kn, mul_assoc, roots_C_mul _ (by norm_num),
    roots_mul (mul_ne_zero X_ne_zero (pow_ne_zero _ (monic_X_add_C 1).ne_zero)),
    roots_X, roots_pow, roots_X_add_C]

end RealRooted.LongCycleDescents
