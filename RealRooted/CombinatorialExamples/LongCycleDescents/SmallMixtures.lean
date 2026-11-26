/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Boundary
import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic

/-!
# All-cutoff mixtures at the exceptional sizes

Exact small-size rows and a degree-counting argument classify repeated roots
for arbitrary nonnegative weights at sizes four and five.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0,
`DescentBoundarySmallRows`, `Windows`, `SmallRoots`, and `Exceptions` (Apache-2.0).
-/

public section

noncomputable section

namespace RealRooted.LongCycleDescents

open Finset Polynomial Necklace Filter

private theorem root_between (p : ℝ[X]) {a b : ℝ} (hab : a < b)
    (hs : p.eval a * p.eval b < 0) :
    ∃ x, a < x ∧ x < b ∧ p.eval x = 0 := by
  rcases mul_neg_iff.mp hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨x, hx, hz⟩ := intermediate_value_Ioo' hab.le p.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Ioo (p.eval b) (p.eval a) from ⟨hb, ha⟩)
    exact ⟨x, hx.1, hx.2, hz⟩
  · obtain ⟨x, hx, hz⟩ := intermediate_value_Ioo hab.le p.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) from ⟨ha, hb⟩)
    exact ⟨x, hx.1, hx.2, hz⟩

private theorem checked {n k : ℕ} (hn : 0 < n) {c : List ℤ} (h : descentRowDP n k = c) :
    realDescentPolynomial n k = coefficientPolynomial c :=
  (coefficientPolynomial_descentRowDP hn k).symm.trans (congrArg coefficientPolynomial h)

private theorem four_one : realDescentPolynomial 4 1 = 1 + 11*X + 11*X^2 + X^3 := by
  rw [checked (by decide) (c := [1,11,11,1]) (by decide +kernel)]
  simp only [coefficientPolynomial, Int.cast_one, map_one, Int.cast_ofNat, C_ofNat, mul_zero,
    add_zero, mul_one]
  ring

private theorem four_two : realDescentPolynomial 4 2 = X * (X-C (-2))^2 := by
  rw [checked (by decide) (c := [0,4,4,1]) (by decide +kernel)]
  simp only [coefficientPolynomial, Int.cast_zero, map_zero, Int.cast_ofNat, C_ofNat, Int.cast_one,
    map_one, mul_zero, add_zero, mul_one, zero_add, map_neg, sub_neg_eq_add, mul_eq_mul_left_iff,
    X_ne_zero, or_false]
  ring

private theorem four_long {k : ℕ} (lo : 3 ≤ k) (hi : k ≤ 4) :
    realDescentPolynomial 4 k = 3*X*(1+X) := by
  have h : descentRowDP 4 k = [0,3,3,0] := by interval_cases k <;> decide +kernel
  rw [checked (by decide) h]
  simp only [coefficientPolynomial, Int.cast_zero, map_zero, Int.cast_ofNat, C_ofNat, mul_zero,
    add_zero, zero_add]
  ring

private theorem five_one : realDescentPolynomial 5 1 = 1 + 26*X + 66*X^2 + 26*X^3 + X^4 := by
  rw [checked (by decide) (c := [1,26,66,26,1]) (by decide +kernel)]
  simp only [coefficientPolynomial, Int.cast_one, map_one, Int.cast_ofNat, C_ofNat, mul_zero,
    add_zero, mul_one]
  ring

private theorem five_two : realDescentPolynomial 5 2 = 8*X + 24*X^2 + 12*X^3 := by
  rw [checked (by decide) (c := [0,8,24,12,0]) (by decide +kernel)]
  simp only [coefficientPolynomial, Int.cast_zero, map_zero, Int.cast_ofNat, C_ofNat, mul_zero,
    add_zero, zero_add]
  ring

private theorem five_long {k : ℕ} (lo : 3 ≤ k) (hi : k ≤ 5) :
    realDescentPolynomial 5 k = 6*X*(1+X)^2 := by
  have h : descentRowDP 5 k = [0,6,12,6,0] := by interval_cases k <;> decide +kernel
  rw [checked (by decide) h]
  simp only [coefficientPolynomial, Int.cast_zero, map_zero, Int.cast_ofNat, C_ofNat, mul_zero,
    add_zero, zero_add]
  ring

private theorem four_mixture (w : ℕ → ℝ) :
    mixture 4 w = C (w 1) * (1 + 11*X + 11*X^2 + X^3) +
      C (w 2) * (X*(X-C (-2))^2) + C (w 3+w 4) * (3*X*(1+X)) := by
  unfold mixture
  rw [show Icc 1 4 = ({1,2,3,4} : Finset ℕ) by decide]
  norm_num [four_one, four_two, four_long, map_add]
  ring

private theorem five_mixture (w : ℕ → ℝ) :
    mixture 5 w = C (w 1) * (1 + 26*X + 66*X^2 + 26*X^3 + X^4) +
      C (w 2) * (8*X + 24*X^2 + 12*X^3) + C (w 3+w 4+w 5) * (6*X*(1+X)^2) := by
  unfold mixture
  rw [show Icc 1 5 = ({1,2,3,4,5} : Finset ℕ) by decide]
  norm_num [five_one, five_two, five_long, map_add]
  ring

/-- The sign of the leading term gives a root to the left of a point of opposite sign. -/
private theorem root_left_of_leading_sign {p : ℝ[X]} {a : ℝ} (lead : 0 < p.leadingCoeff)
    (sign : (-1 : ℝ) ^ p.natDegree * p.eval a < 0) :
    ∃ x, x < a ∧ p.eval x = 0 := by
  have eventuallyFlip : ∀ᶠ x in atBot, p.eval x * p.eval a < 0 := by
    rcases p.natDegree.even_or_odd with parity | parity
    · rw [parity.neg_one_pow, one_mul] at sign
      have positive := p.isEquivalent_atBot_lead.eventually_pos
        ((eventually_lt_atBot (0:ℝ)).mono fun x hx ↦ mul_pos lead (parity.pow_pos hx.ne))
      exact positive.mono fun _ h ↦ mul_neg_of_pos_of_neg h sign
    · rw [parity.neg_one_pow, neg_one_mul, neg_lt_zero] at sign
      have negative := p.isEquivalent_atBot_lead.eventually_neg
        ((eventually_lt_atBot (0:ℝ)).mono fun x hx ↦ mul_neg_of_pos_of_neg lead (parity.pow_neg hx))
      exact negative.mono fun _ h ↦ mul_neg_of_neg_of_pos h sign
  obtain ⟨z, hza, flip⟩ := ((eventually_lt_atBot a).and eventuallyFlip).exists
  obtain ⟨x, _, hxa, hx⟩ := root_between p hza flip
  exact ⟨x, hxa, hx⟩

private theorem simple_nonpositive_of_witnesses {p : ℝ[X]} (hp : p ≠ 0) (s : Finset ℝ)
    (cap : p.natDegree ≤ s.card) (zeros : ∀ x ∈ s, p.eval x = 0)
    (nonpos : ∀ x ∈ s, x ≤ 0) :
    p.Splits ∧ p.roots.Nodup ∧ ∀ x ∈ p.roots, x ≤ 0 := by
  have equal := roots_eq_of_natDegree_le_card_of_ne_zero (S := s) zeros cap hp
  have cards : p.roots.card = s.card := congrArg Multiset.card equal
  exact ⟨splits_iff_card_roots.mpr (le_antisymm p.card_roots' (cap.trans_eq cards.symm)),
    equal ▸ s.nodup, fun x hx ↦ nonpos x (by rwa [equal] at hx)⟩

/-- Intervals (aᵢ,bᵢ] may share endpoints. A zero at the right endpoint counts only once. -/
private theorem simple_nonpositive_from_windows {d : ℕ} {p : ℝ[X]} (hp : p ≠ 0)
    (a b : Fin d → ℝ) (lt : ∀ i, a i < b i) (right : ∀ i, b i ≤ 0)
    (sep : ∀ i j, i < j → b i ≤ a j) (leftNZ : ∀ i, p.eval (a i) ≠ 0)
    (flip : ∀ i, p.eval (a i) * p.eval (b i) ≤ 0)
    (degree : p.natDegree ≤ d ∨
      (p.natDegree ≤ d + 1 ∧ ∃ x, x ≤ 0 ∧ (∀ i, x ≤ a i) ∧ p.eval x = 0)) :
    p.Splits ∧ p.roots.Nodup ∧ ∀ x ∈ p.roots, x ≤ 0 := by
  classical
  have bracket (i : Fin d) : ∃ x, a i < x ∧ x ≤ b i ∧ p.eval x = 0 := by
    by_cases z : p.eval (b i) = 0
    · exact ⟨b i,lt i,le_rfl,z⟩
    · obtain ⟨x,h,l,e⟩ := root_between p (lt i)
        (lt_of_le_of_ne (flip i) (mul_ne_zero (leftNZ i) z))
      exact ⟨x,h,l.le,e⟩
  choose r located using bracket
  have sorted : StrictMono r := fun i j lt ↦
    ((located i).2.1.trans (sep i j lt)).trans_lt (located j).1
  let s := (univ : Finset (Fin d)).map ⟨r, sorted.injective⟩
  have size : s.card = d := by simp [s]
  have members {x} (h : x ∈ s) : ∃ i, r i = x := by
    obtain ⟨i,_,hi⟩ := mem_map.mp h
    exact ⟨i,hi⟩
  have roots (x) (hx : x ∈ s) : p.eval x = 0 := by
    obtain ⟨i,rfl⟩ := members hx
    exact (located i).2.2
  have nonpos (x) (hx : x ∈ s) : x ≤ 0 := by
    obtain ⟨i,rfl⟩ := members hx
    exact (located i).2.1.trans (right i)
  rcases degree with cap | ⟨cap, x, xn, outer, ex⟩
  · exact simple_nonpositive_of_witnesses hp s (cap.trans_eq size.symm) roots nonpos
  · have newPoint : x ∉ s := by
      intro h
      obtain ⟨i,eq⟩ := members h
      exact (not_lt_of_ge (outer i)) (eq ▸ (located i).1)
    apply simple_nonpositive_of_witnesses hp (insert x s)
    · simpa [newPoint, size] using cap
    · exact (forall_mem_insert _ _ _).mpr ⟨ex, roots⟩
    · exact (forall_mem_insert _ _ _).mpr ⟨xn, nonpos⟩

/-- A zero highest coefficient lowers the degree; a positive one supplies the far-left root. -/
private theorem simple_nonpositive_from_leading_window {d : ℕ} {p : ℝ[X]} (a b : Fin d → ℝ)
    (lt : ∀ i, a i < b i) (right : ∀ i, b i ≤ 0) (sep : ∀ i j, i < j → b i ≤ a j)
    (leftNZ : ∀ i, p.eval (a i) ≠ 0) (flip : ∀ i, p.eval (a i) * p.eval (b i) ≤ 0)
    (first : Fin d) (minLeft : ∀ i, a first ≤ a i)
    (farSign : (-1 : ℝ) ^ (d + 1) * p.eval (a first) < 0)
    (cap : p.natDegree ≤ d + 1) (top : 0 ≤ p.coeff (d + 1)) :
    p.Splits ∧ p.roots.Nodup ∧ ∀ x ∈ p.roots, x ≤ 0 := by
  have hp : p ≠ 0 := by intro h; exact leftNZ first (by simp only [h, eval_zero])
  apply simple_nonpositive_from_windows hp a b lt right sep leftNZ flip
  by_cases small : p.natDegree ≤ d
  · exact Or.inl small
  · have eq : p.natDegree = d+1 := by lia
    have lead : 0 < p.leadingCoeff := lt_of_le_of_ne (by rwa [leadingCoeff, eq])
      (Ne.symm (leadingCoeff_ne_zero.mpr hp))
    obtain ⟨x, hx, ex⟩ := root_left_of_leading_sign lead (by rwa [eq])
    exact Or.inr ⟨cap, x, (hx.trans (lt first)).le.trans (right first),
      fun i ↦ hx.le.trans (minLeft i), ex⟩

private theorem four_simple (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 4, 0 ≤ w k)
    (regular : 0 < w 1 + (w 3 + w 4)) :
    (mixture 4 w).Splits ∧ (mixture 4 w).roots.Nodup ∧ ∀ x ∈ (mixture 4 w).roots, x ≤ 0 := by
  have a := hw 1 (by decide)
  have b := hw 2 (by decide)
  have c := hw 3 (by decide)
  have e := hw 4 (by decide)
  have pos : 0 < (mixture 4 w).eval (-2) := by
    norm_num [four_mixture]; linarith
  have neg : (mixture 4 w).eval (-(1/2:ℝ)) < 0 := by
    norm_num [four_mixture]; linarith
  have origin : 0 ≤ (mixture 4 w).eval 0 := by simpa [four_mixture] using a
  let lower : Fin 2 → ℝ := ![-2, -(1/2)]
  let upper : Fin 2 → ℝ := ![-(1/2), 0]
  apply simple_nonpositive_from_leading_window lower upper (first := 0)
  · intro i; fin_cases i <;> norm_num [lower, upper]
  · intro i; fin_cases i <;> norm_num [upper]
  · intro i j h; fin_cases i <;> fin_cases j <;> norm_num [lower, upper] at *
  · intro i; fin_cases i
    · exact pos.ne'
    · exact neg.ne
  · intro i; fin_cases i
    · exact (mul_neg_of_pos_of_neg pos neg).le
    · exact mul_nonpos_of_nonpos_of_nonneg neg.le origin
  · intro i; fin_cases i <;> norm_num [lower]
  · norm_num [lower]; exact pos
  · rw [four_mixture]
    compute_degree
  · exact mixture_hasNonnegCoeffs hw _

private theorem five_simple (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 5, 0 ≤ w k)
    (regular : 0 < w 1 + w 2) :
    (mixture 5 w).Splits ∧ (mixture 5 w).roots.Nodup ∧ ∀ x ∈ (mixture 5 w).roots, x ≤ 0 := by
  have a := hw 1 (by decide)
  have b := hw 2 (by decide)
  have c := hw 3 (by decide)
  have e := hw 4 (by decide)
  have f := hw 5 (by decide)
  have negL : (mixture 5 w).eval (-4) < 0 := by
    norm_num [five_mixture]; linarith
  have pos : 0 < (mixture 5 w).eval (-1) := by
    norm_num [five_mixture]; linarith
  have negR : (mixture 5 w).eval (-(1/4:ℝ)) < 0 := by
    norm_num [five_mixture]; linarith
  have origin : 0 ≤ (mixture 5 w).eval 0 := by simpa [five_mixture] using a
  let lower : Fin 3 → ℝ := ![-4,-1,-(1/4)]
  let upper : Fin 3 → ℝ := ![-1,-(1/4),0]
  apply simple_nonpositive_from_leading_window lower upper (first := 0)
  · intro i; fin_cases i <;> norm_num [lower, upper]
  · intro i; fin_cases i <;> norm_num [upper]
  · intro i j h; fin_cases i <;> fin_cases j <;> norm_num [lower, upper] at *
  · intro i; fin_cases i
    · exact negL.ne
    · exact pos.ne'
    · exact negR.ne
  · intro i; fin_cases i
    · exact (mul_neg_of_neg_of_pos negL pos).le
    · exact (mul_neg_of_pos_of_neg pos negR).le
    · exact mul_nonpos_of_nonpos_of_nonneg negR.le origin
  · intro i; fin_cases i <;> norm_num [lower]
  · norm_num [lower]; exact negL
  · rw [five_mixture]
    compute_degree
  · exact mixture_hasNonnegCoeffs hw _

private theorem scaled_double {a t : ℝ} (ha : 0 < a) :
    let p : ℝ[X] := C a * (X*(X-C t)^2)
    p.Splits ∧ p.roots = ({0}:Multiset ℝ) + 2 • ({t}:Multiset ℝ) := by
  dsimp only
  refine ⟨(Splits.C _).mul (Splits.X.mul ((Splits.X_sub_C t).pow 2)), ?_⟩
  have nz : (X:ℝ[X])*(X-C t)^2 ≠ 0 := mul_ne_zero X_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _))
  rw [roots_C_mul _ ha.ne', roots_mul nz, roots_X, roots_pow, roots_X_sub_C]

private theorem exceptional_properties {p : ℝ[X]} {t : ℝ} (ht : t < 0)
    (hr : p.roots = ({0} : Multiset ℝ) + 2 • ({t} : Multiset ℝ)) :
    ¬ p.roots.Nodup ∧ (∀ x ∈ p.roots, x ≤ 0) ∧ p.rootMultiplicity t = 2 := by
  have distinct := ht.ne
  rw [← count_roots, hr]
  constructor
  · simp [two_nsmul]
  constructor
  · intro x hx
    simp only [two_nsmul, Multiset.singleton_add, Multiset.add_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at hx
    rcases hx with h | h
    · grind
    · grind
  · simp [two_nsmul, distinct, distinct.symm]

private theorem four_exception (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 4, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 4, 0 < w k) (support : w 1 + (w 3 + w 4) = 0) :
    (mixture 4 w).Splits ∧ (mixture 4 w).roots = ({0}:Multiset ℝ) + 2 • ({-2}:Multiset ℝ) := by
  have a := hw 1 (by decide)
  have c := hw 3 (by decide)
  have e := hw 4 (by decide)
  have za : w 1 = 0 := by linarith
  have zc : w 3 = 0 := by linarith
  have ze : w 4 = 0 := by linarith
  have hb : 0 < w 2 := by
    obtain ⟨k, hk, positive⟩ := pos
    obtain ⟨lo,hi⟩ := mem_Icc.mp hk
    interval_cases k <;> simp_all
  rw [four_mixture, za, zc, ze]
  simpa using scaled_double (t := -2) hb

private theorem five_exception (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 5, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 5, 0 < w k) (support : w 1 + w 2 = 0) :
    (mixture 5 w).Splits ∧ (mixture 5 w).roots = ({0}:Multiset ℝ) + 2 • ({-1}:Multiset ℝ) := by
  have a := hw 1 (by decide)
  have b := hw 2 (by decide)
  have c := hw 3 (by decide)
  have e := hw 4 (by decide)
  have f := hw 5 (by decide)
  have za : w 1 = 0 := by linarith
  have zb : w 2 = 0 := by linarith
  have hc : 0 < w 3+w 4+w 5 := by
    obtain ⟨k, hk, positive⟩ := pos
    obtain ⟨lo,hi⟩ := mem_Icc.mp hk
    interval_cases k <;> linarith
  have eq : mixture 5 w = C (6*(w 3+w 4+w 5)) * (X*(X-C (-1))^2) := by
    rw [five_mixture, za, zb]
    simp only [map_zero, zero_mul, add_zero, map_add, zero_add, map_mul, C_ofNat, map_neg, map_one,
      sub_neg_eq_add]
    ring
  rw [eq]
  exact scaled_double (by positivity)

/-- The four-letter mixture splits; only the pure derangement support repeats a root. -/
theorem mixture_four_roots (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 4, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 4, 0 < w k) :
    let p := mixture 4 w
    p.Splits ∧ (∀ x ∈ p.roots, x ≤ 0) ∧ (p.roots.Nodup ↔ 0 < w 1 + (w 3+w 4)) ∧
      (w 1 + (w 3+w 4) = 0 → p.rootMultiplicity (-2) = 2) := by
  by_cases good : 0 < w 1 + (w 3+w 4)
  · obtain ⟨splits, simple, roots⟩ := four_simple w hw good
    exact ⟨splits, roots, iff_of_true simple good, fun eq ↦ (good.ne' eq).elim⟩
  · have zero := le_antisymm (le_of_not_gt good)
      (add_nonneg (hw 1 (by decide)) (add_nonneg (hw 3 (by decide)) (hw 4 (by decide))))
    obtain ⟨splits, hr⟩ := four_exception w hw pos zero
    obtain ⟨dup, roots, mult⟩ := exceptional_properties (by norm_num : (-2:ℝ)<0) hr
    exact ⟨splits, roots, iff_of_false dup good, fun _ ↦ mult⟩

/-- The five-letter mixture splits; only long-cutoff support repeats a root. -/
theorem mixture_five_roots (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 5, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 5, 0 < w k) :
    let p := mixture 5 w
    p.Splits ∧ (∀ x ∈ p.roots, x ≤ 0) ∧ (p.roots.Nodup ↔ 0 < w 1+w 2) ∧
      (w 1+w 2 = 0 → p.rootMultiplicity (-1) = 2) := by
  by_cases good : 0 < w 1+w 2
  · obtain ⟨splits, simple, roots⟩ := five_simple w hw good
    exact ⟨splits, roots, iff_of_true simple good, fun eq ↦ (good.ne' eq).elim⟩
  · have zero := le_antisymm (le_of_not_gt good) (add_nonneg (hw 1 (by decide)) (hw 2 (by decide)))
    obtain ⟨splits, hr⟩ := five_exception w hw pos zero
    obtain ⟨dup, roots, mult⟩ := exceptional_properties (by norm_num : (-1:ℝ)<0) hr
    exact ⟨splits, roots, iff_of_false dup good, fun _ ↦ mult⟩

private theorem one_all_weights (w : ℕ → ℝ) :
    (mixture 1 w).Splits ∧ (mixture 1 w).roots.Nodup ∧ ∀ x ∈ (mixture 1 w).roots, x ≤ 0 := by
  have row1 : realDescentPolynomial 1 1 = 1 := by
    rw [realDescentPolynomial, ← coefficientPolynomial_descentRowDP (by decide),
      show descentRowDP 1 1 = [1] by decide +kernel]
    simp [coefficientPolynomial]
  have h : mixture 1 w = C (w 1) := by simp [mixture, row1]
  simp [h, Splits.C]

private theorem two_all_weights (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 2, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 2, 0 < w k) :
    (mixture 2 w).Splits ∧ (mixture 2 w).roots.Nodup ∧ ∀ x ∈ (mixture 2 w).roots, x ≤ 0 := by
  have row1 : realDescentPolynomial 2 1 = 1+X := by
    rw [realDescentPolynomial, ← coefficientPolynomial_descentRowDP (by decide),
      show descentRowDP 2 1 = [1,1] by decide +kernel]
    simp [coefficientPolynomial]
  have row2 : realDescentPolynomial 2 2 = X := by
    rw [realDescentPolynomial, ← coefficientPolynomial_descentRowDP (by decide),
      show descentRowDP 2 2 = [0,1] by decide +kernel]
    simp [coefficientPolynomial]
  have sumPos := sum_pos' hw pos
  have ix : Icc 1 2 = ({1,2}:Finset ℕ) := by decide
  have ab : 0 < w 1+w 2 := by simpa [ix] using sumPos
  have poly : mixture 2 w = C (w 1+w 2)*X + C (w 1) := by
    simp only [mixture, ix, mem_singleton, OfNat.one_ne_ofNat, not_false_eq_true, sum_insert, row1,
      sum_singleton, row2, map_add]; ring
  let r := -(w 1/(w 1+w 2))
  have root : (mixture 2 w).eval r = 0 := by
    rw [poly]; simp only [map_add, eval_add, eval_mul, eval_C, eval_X, mul_neg, r]; field_simp; ring
  have hne : mixture 2 w ≠ 0 := by
    intro h
    have v := congrArg (fun f : ℝ[X] ↦ f.coeff 1) h
    rw [poly] at v
    simpa using ab.ne' (by simpa using v)
  apply simple_nonpositive_of_witnesses hne {r}
  · simp only [card_singleton]
    rw [poly]
    compute_degree
  · simpa using root
  · simpa [r] using neg_nonpos.mpr (div_nonneg (hw 1 (by decide)) ab.le)

private theorem three_all_weights (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 3, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 3, 0 < w k) :
    (mixture 3 w).Splits ∧ (mixture 3 w).roots.Nodup ∧
      ∀ x ∈ (mixture 3 w).roots, x ≤ 0 := by
  have row1 : realDescentPolynomial 3 1 = 1 + 4 * X + X ^ 2 := by
    rw [realDescentPolynomial, ← coefficientPolynomial_descentRowDP (by decide),
      show descentRowDP 3 1 = [1, 4, 1] by decide +kernel]
    simp only [coefficientPolynomial, Int.cast_one, map_one, Int.cast_ofNat, C_ofNat, mul_zero,
      add_zero, mul_one]
    ring
  have row2 (k : ℕ) (lo : 2 ≤ k) (hi : k ≤ 3) :
      realDescentPolynomial 3 k = 2 * X := by
    have h : descentRowDP 3 k = [0, 2, 0] := by interval_cases k <;> decide +kernel
    rw [realDescentPolynomial, ← coefficientPolynomial_descentRowDP (by decide), h]
    simp [coefficientPolynomial, C_ofNat, mul_comm]
  have ix : Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  have poly : mixture 3 w = C (w 1) * (1 + 4 * X + X ^ 2) +
      C (w 2 + w 3) * (2 * X) := by
    simp only [mixture, ix, mem_insert, OfNat.one_ne_ofNat, mem_singleton, or_self,
      not_false_eq_true, sum_insert, row1, Nat.reduceEqDiff, Std.le_refl, Nat.reduceLeDiff, row2,
      sum_singleton, map_add, add_right_inj]
    ring
  have sumPos : 0 < w 1 + w 2 + w 3 := by simpa [ix, add_assoc] using sum_pos' hw pos
  have neg : (mixture 3 w).eval (-1) < 0 := by
    norm_num [poly]
    linarith
  have origin : 0 ≤ (mixture 3 w).eval 0 := by
    simpa [poly] using hw 1 (by decide)
  apply simple_nonpositive_from_leading_window (fun _ : Fin 1 => -1)
    (fun _ => 0) (first := 0)
  · intro i; norm_num
  · intro i; exact le_rfl
  · intro i j hij; have := i.isLt; have := j.isLt; change i.val < j.val at hij; lia
  · intro i; exact neg.ne
  · intro i; exact mul_nonpos_of_nonpos_of_nonneg neg.le origin
  · intro i; exact le_rfl
  · simpa using neg
  · rw [poly]; compute_degree
  · exact mixture_hasNonnegCoeffs hw _

/-- At sizes at most five, all nonnegative nonzero mixtures have nonpositive real
roots, and their roots are simple exactly outside the two exceptional supports. -/
theorem mixture_roots_of_le_five {n : ℕ} (hn : 1 ≤ n) (h5 : n ≤ 5) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) (pos : ∃ k ∈ Icc 1 n, 0 < w k) :
    mixture n w ≠ 0 ∧ (mixture n w).Splits ∧
      (∀ x ∈ (mixture n w).roots, x ≤ 0) ∧
      ((mixture n w).roots.Nodup ↔
        ¬((n = 4 ∧ w 1 = 0 ∧ w 3 = 0 ∧ w 4 = 0) ∨
          (n = 5 ∧ w 1 = 0 ∧ w 2 = 0))) := by
  refine ⟨mixture_ne_zero hw pos, ?_⟩
  interval_cases n
  · have h := one_all_weights w
    exact ⟨h.1, h.2.2, by simpa using h.2.1⟩
  · have h := two_all_weights w hw pos
    exact ⟨h.1, h.2.2, by simpa using h.2.1⟩
  · have h := three_all_weights w hw pos
    exact ⟨h.1, h.2.2, by simpa using h.2.1⟩
  · have h := mixture_four_roots w hw pos
    have a := hw 1 (by decide)
    have c := hw 3 (by decide)
    have e := hw 4 (by decide)
    refine ⟨h.1, h.2.1, ?_⟩
    rw [h.2.2.1]
    simp only [show (4 : ℕ) ≠ 5 from by decide, false_and, or_false, true_and]
    constructor
    · rintro hp ⟨ha, hc, he⟩
      simp_all
    · intro hh
      by_contra! hp
      apply hh
      exact ⟨by linarith, by linarith, by linarith⟩
  · have h := mixture_five_roots w hw pos
    have a := hw 1 (by decide)
    have b := hw 2 (by decide)
    refine ⟨h.1, h.2.1, ?_⟩
    rw [h.2.2.1]
    simp only [show (5 : ℕ) ≠ 4 from by decide, false_and, false_or, true_and]
    constructor
    · rintro hp ⟨ha, hb⟩
      simp_all
    · intro hh
      by_contra! hp
      apply hh
      exact ⟨by linarith, by linarith⟩

end RealRooted.LongCycleDescents
