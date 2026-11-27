/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic
public import RealRooted.Basic.ProperPosition
public import RealRooted.SimpleRoots
import RealRooted.MaWang.StrictSigns.RootSigns
import Mathlib.Data.List.OfFn


/-!
# Catalan strict-peak polynomials by their coefficient formula

We define the family algebraically, without a word model. For positive `n`,
`C_n(t) = ∑ i, choose(n-i,i) choose(2n-3i,n-2i-1) (t-1)^i / (n-i)`.
The empty row is one. The degree bound is `floor((n-1)/2)`.
The same module supplies interval root lists and the translated top coefficients.

Source: ProgramComputer, *Strict peaks in Catalan words*, coefficient formula
and finite-certificate method, ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

@[expose] public noncomputable section

namespace RealRooted.CatalanWordPeaks

open Polynomial Finset

/-- The degree of the length-`n` row, including the constant initial rows. -/
def rowDegree (n : ℕ) : ℕ := (n - 1) / 2

/-- The coefficient of `(t - 1)^i`, evaluated in exact rational arithmetic. -/
def shiftedCoefficient (n i : ℕ) : ℚ :=
  (Nat.fast_choose (n - i) i : ℚ) * Nat.fast_choose (2 * n - 3 * i) (n - 2 * i - 1) /
    (n - i : ℕ)

/-- The strict-peak row defined by the explicit coefficient formula. -/
def polynomial (n : ℕ) : ℝ[X] :=
  if n = 0 then 1 else
    ∑ i ∈ range (rowDegree n + 1), C (shiftedCoefficient n i : ℝ) * (X - 1) ^ i

/-- The executable coefficient is exactly the stated binomial expression. -/
theorem shiftedCoefficient_eq (n i : ℕ) :
    shiftedCoefficient n i =
      ((n - i).choose i : ℚ) * (2 * n - 3 * i).choose (n - 2 * i - 1) / (n - i : ℕ) := by
  simp only [shiftedCoefficient, ← Nat.choose_eq_fast_choose]

/-- Every row has degree at most the size predicted by the formula. -/
theorem natDegree_polynomial_le (n : ℕ) : (polynomial n).natDegree ≤ rowDegree n := by
  unfold polynomial
  split
  · simp only [natDegree_one, zero_le]
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    refine (natDegree_mul_le.trans ?_).trans (Nat.le_of_lt_succ (mem_range.mp hi))
    simp only [natDegree_C, zero_add, natDegree_pow]
    have hlin : (X - 1 : ℝ[X]).natDegree = 1 := by
      simpa only [map_one] using natDegree_X_sub_C (1 : ℝ)
    simp only [hlin, Nat.mul_one, le_refl]

/-- Every shifted coefficient in the stated range is strictly positive. -/
theorem shiftedCoefficient_pos {n i : ℕ} (hn : n ≠ 0) (hi : i ≤ rowDegree n) :
    0 < shiftedCoefficient n i := by
  have hi' : 2 * i ≤ n - 1 := by unfold rowDegree at hi; lia
  rw [shiftedCoefficient_eq]
  exact div_pos (mul_pos (by exact_mod_cast Nat.choose_pos (show i ≤ n - i by lia))
    (by exact_mod_cast Nat.choose_pos (show n - 2 * i - 1 ≤ 2 * n - 3 * i by lia)))
    (by exact_mod_cast (show 0 < n - i by lia))

/-- The highest prospective coefficient of a positive-length row. -/
theorem coeff_polynomial_rowDegree {n : ℕ} (hn : n ≠ 0) :
    (polynomial n).coeff (rowDegree n) = (shiftedCoefficient n (rowDegree n) : ℝ) := by
  rw [polynomial, ite_eq_right hn, sum_range_succ, coeff_add, finsetSum_coeff]
  have hzero : ∑ i ∈ range (rowDegree n),
      (C (shiftedCoefficient n i : ℝ) * (X - 1) ^ i).coeff (rowDegree n) = 0 := by
    apply sum_eq_zero
    intro i hi
    apply coeff_eq_zero_of_natDegree_lt
    refine lt_of_le_of_lt (natDegree_mul_le.trans ?_) (mem_range.mp hi)
    simp only [natDegree_C, zero_add, natDegree_pow]
    have hlin : (X - 1 : ℝ[X]).natDegree = 1 := by
      simpa only [map_one] using natDegree_X_sub_C (1 : ℝ)
    simp only [hlin, Nat.mul_one, le_refl]
  rw [hzero, zero_add, coeff_C_mul]
  have htop : ((X - 1 : ℝ[X]) ^ rowDegree n).coeff (rowDegree n) = 1 := by
    have hlin : (X - 1 : ℝ[X]).natDegree = 1 := by
      simpa only [map_one] using natDegree_X_sub_C (1 : ℝ)
    have hlead : (X - 1 : ℝ[X]).leadingCoeff = 1 := by
      simpa only [map_one] using (monic_X_sub_C (1 : ℝ)).leadingCoeff
    have h := coeff_pow_mul_natDegree (X - 1 : ℝ[X]) (rowDegree n)
    simpa only [hlin, Nat.mul_one, hlead, one_pow] using h
  rw [htop, mul_one]

/-- The formula attains its degree bound at every length. -/
theorem natDegree_polynomial (n : ℕ) : (polynomial n).natDegree = rowDegree n := by
  by_cases hn : n = 0
  · subst n
    simp only [polynomial, ite_true, natDegree_one, rowDegree, Nat.zero_sub, Nat.zero_div]
  · apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_polynomial_le n)
    rw [coeff_polynomial_rowDegree hn]
    exact ne_of_gt (by exact_mod_cast shiftedCoefficient_pos hn (le_refl (rowDegree n)))

/-- The leading coefficient is positive, including the constant initial rows. -/
theorem leadingCoeff_polynomial_pos (n : ℕ) : 0 < (polynomial n).leadingCoeff := by
  by_cases hn : n = 0
  · subst n
    simp only [polynomial, ite_true, leadingCoeff_one, zero_lt_one]
  · rw [leadingCoeff, natDegree_polynomial, coeff_polynomial_rowDegree hn]
    exact_mod_cast shiftedCoefficient_pos hn (le_refl (rowDegree n))

/-- Consecutive rows have equal degree bounds or differ by one. -/
theorem rowDegree_succ (n : ℕ) :
    rowDegree (n + 1) = rowDegree n ∨ rowDegree (n + 1) = rowDegree n + 1 := by
  unfold rowDegree
  lia

/-- Disjoint sign-changing intervals exhaust the roots of a polynomial whose
 degree is bounded by their number. The returned root list is increasing. -/
theorem roots_of_intervals {p : ℝ[X]} {m : ℕ} (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ m) (l u : Fin m → ℝ)
    (hwidth : ∀ i, l i < u i)
    (hsep : ∀ i j, i < j → u i ≤ l j)
    (hsign : ∀ i, p.eval (l i) * p.eval (u i) < 0) :
    ∃ r : Fin m → ℝ, StrictMono r ∧
      (∀ i, l i < r i ∧ r i < u i) ∧
      (↑(List.ofFn r) : Multiset ℝ) = p.roots ∧ p.Splits ∧ p.natDegree = m := by
  classical
  choose r hr using fun i ↦ MaWang.exists_isRoot_between_of_eval_mul_neg (hwidth i) (hsign i)
  have hmono : StrictMono r := fun i j hij ↦
    (hr i).2.1.trans_le (hsep i j hij) |>.trans (hr j).1
  have hn : (List.ofFn r).Nodup :=
    List.pairwise_ofFn.mpr (fun _ _ h ↦ (hmono h).ne)
  have hsub : (↑(List.ofFn r) : Multiset ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hn)]
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hx)
    exact (mem_roots hp).mpr (hr i).2.2
  have heq : (↑(List.ofFn r) : Multiset ℝ) = p.roots := by
    apply Multiset.eq_of_le_of_card_le hsub
    exact (card_roots' p).trans (by simpa only [Multiset.coe_card, List.length_ofFn] using hdeg)
  have hd : p.natDegree = m := by
    have hc := Multiset.card_le_card hsub
    simp only [Multiset.coe_card, List.length_ofFn] at hc
    exact le_antisymm hdeg (hc.trans (card_roots' p))
  refine ⟨r, hmono, fun i ↦ ⟨(hr i).1, (hr i).2.1⟩, heq, ?_, hd⟩
  exact splits_iff_card_roots.mpr (by rw [← heq, Multiset.coe_card, List.length_ofFn, hd])

/-- A complete injective root enumeration gives simple real roots. -/
theorem hasSimpleRoots_of_root_list {p : ℝ[X]} {m : ℕ} (hp : p ≠ 0)
    {r : Fin m → ℝ} (hr : StrictMono r)
    (heq : (↑(List.ofFn r) : Multiset ℝ) = p.roots) : HasSimpleRoots p := by
  classical
  have hn : p.roots.Nodup := by
    rw [← heq, Multiset.coe_nodup]
    exact List.pairwise_ofFn.mpr (fun _ _ h ↦ (hr h).ne)
  exact HasSimpleRoots.of_roots_nodup hp hn

/-- Strictly separated complete root lists imply the standard oriented interlacing
relation for either of the two permitted degree patterns. -/
theorem strictInterl_of_root_lists {p q : ℝ[X]} {m d : ℕ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hps : p.Splits) (hqs : q.Splits)
    (r : Fin m → ℝ) (s : Fin d → ℝ) (hr : StrictMono r) (hs : StrictMono s)
    (heqp : (↑(List.ofFn r) : Multiset ℝ) = p.roots)
    (heqq : (↑(List.ofFn s) : Multiset ℝ) = q.roots)
    (hd : d = m ∨ d = m + 1)
    (hright : ∀ i j, j.val = i.val + (d - m) → r i < s j)
    (hleft : ∀ i j, j.val + 1 = i.val + (d - m) → s j < r i) :
    StrictInterl p q := by
  refine ⟨⟨hp, hps⟩, ⟨hq, hqs⟩, List.ofFn r, List.ofFn s,
    List.pairwise_ofFn.mpr (fun _ _ h ↦ (hr h).le),
    List.pairwise_ofFn.mpr (fun _ _ h ↦ (hs h).le), heqp, heqq, ?_⟩
  rcases hd with rfl | rfl
  · right
    refine ⟨by simp only [List.length_ofFn], listAlternates_of_interleaves_of_length
      (by simp only [List.length_ofFn]) (List.interleaves_ofFn_even.mpr ⟨?_, ?_⟩)⟩
    · intro i
      exact (hright i i (by simp only [Nat.sub_self, Nat.add_zero])).le
    · intro i hi
      exact (hleft ⟨i + 1, hi⟩ ⟨i, by lia⟩ (by simp only [Nat.sub_self, Nat.add_zero])).le
  · left
    refine ⟨by simp only [List.length_ofFn], listInterlaces_of_interleaves_of_length
      (by simp only [List.length_ofFn]) (List.interleaves_ofFn_odd.mpr ⟨?_, ?_⟩)⟩
    · intro i
      exact (hright i i.succ (by simp only [Nat.add_sub_cancel_left, Fin.val_succ])).le
    · intro i
      exact (hleft i i.castSucc (by simp only [Nat.add_sub_cancel_left, Fin.val_castSucc])).le

/-- Strict cross-list inequalities exclude every common root. -/
theorem no_common_root_of_root_lists {p q : ℝ[X]} {m d : ℕ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hd : d = m ∨ d = m + 1)
    (r : Fin m → ℝ) (s : Fin d → ℝ) (hs : StrictMono s)
    (heqp : (↑(List.ofFn r) : Multiset ℝ) = p.roots)
    (heqq : (↑(List.ofFn s) : Multiset ℝ) = q.roots)
    (hright : ∀ i j, j.val = i.val + (d - m) → r i < s j)
    (hleft : ∀ i j, j.val + 1 = i.val + (d - m) → s j < r i) :
    ∀ x, ¬ (p.IsRoot x ∧ q.IsRoot x) := by
  intro x ⟨hx, hy⟩
  have hx' := (mem_roots hp).mpr hx
  have hy' := (mem_roots hq).mpr hy
  rw [← heqp] at hx'
  rw [← heqq] at hy'
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hx')
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hy')
  by_cases hij : i.val + (d - m) ≤ j.val
  · let k : Fin d := ⟨i.val + (d - m), lt_of_le_of_lt hij j.isLt⟩
    have hlt := (hright i k rfl).trans_le (hs.monotone hij)
    exact hlt.ne hj.symm
  · have hi := i.isLt
    have hk : i.val + (d - m) - 1 < d := by rcases hd with rfl | rfl <;> lia
    let k : Fin d := ⟨i.val + (d - m) - 1, hk⟩
    have hlt := (hs.monotone (show j ≤ k by change j.val ≤ k.val; dsimp [k]; lia)).trans_lt
      (hleft i k (by dsimp [k]; lia))
    exact hlt.ne hj

/-- In the strict orientation, every old root lies below a new root; in particular
 the new rightmost root is strictly farther right whenever the old row is nonconstant. -/
theorem exists_root_above_of_root_lists {p q : ℝ[X]} {m d : ℕ}
    (hm : m ≠ 0) (hd : d = m ∨ d = m + 1)
    (r : Fin m → ℝ) (s : Fin d → ℝ) (hs : StrictMono s)
    (heqp : (↑(List.ofFn r) : Multiset ℝ) = p.roots)
    (heqq : (↑(List.ofFn s) : Multiset ℝ) = q.roots)
    (hright : ∀ i j, j.val = i.val + (d - m) → r i < s j) :
    ∃ y ∈ q.roots, (∀ x ∈ p.roots, x < y) ∧ ∀ z ∈ q.roots, z ≤ y := by
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> lia
  let last : Fin d := ⟨d - 1, by lia⟩
  refine ⟨s last, ?_, ?_, ?_⟩
  · rw [← heqq]
    exact Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨last, rfl⟩)
  · intro x hx
    rw [← heqp] at hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hx)
    have hi := i.isLt
    have hk : i.val + (d - m) < d := by rcases hd with rfl | rfl <;> lia
    exact (hright i ⟨_, hk⟩ rfl).trans_le (hs.monotone (by change _ ≤ d - 1; lia))
  · intro z hz
    rw [← heqq] at hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hz)
    exact hs.monotone (by change i.val ≤ d - 1; have hi := i.isLt; lia)

end RealRooted.CatalanWordPeaks

namespace RealRooted.CatalanWordPeaks.TopCoefficients

open Polynomial Finset

/-- Shifting by one extracts the defining coefficient without lower-degree terms. -/
theorem coeff_comp_add_one {n k : ℕ} (hn : n ≠ 0) (hk : k ≤ rowDegree n) :
    ((polynomial n).comp (X + 1)).coeff k = (shiftedCoefficient n k : ℝ) := by
  have hc : (polynomial n).comp (X + 1) =
      ∑ i ∈ range (rowDegree n + 1), C (shiftedCoefficient n i : ℝ) * X ^ i := by
    rw [polynomial, ite_eq_right hn, Polynomial.sum_comp]
    apply sum_congr rfl
    intro i _
    simp only [mul_comp, C_comp, pow_comp, sub_comp, X_comp, one_comp,
      add_sub_cancel_right]
  rw [hc, finsetSum_coeff]
  simp [Nat.lt_succ_of_le hk]

private lemma choose_asc (k r : ℕ) :
    ((k + r).choose r : ℝ) = ((k + 1).ascFactorial r : ℝ) / (r.factorial : ℝ) := by
  rw [eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero r), mul_comm]
  exact_mod_cast (Nat.ascFactorial_eq_factorial_mul_choose k r).symm

/-- A uniform formula for the coefficient at defect r, with positive defect. -/
theorem coeff_comp_add_one_defect (r k : ℕ) (hr : r ≠ 0) :
    ((polynomial (r + 2 * k)).comp (X + 1)).coeff k =
      ((k + 1).ascFactorial (r - 1) : ℝ) *
        ((k + r + 2).ascFactorial (r - 1) : ℝ) /
          (r.factorial * (r - 1).factorial : ℕ) := by
  rw [coeff_comp_add_one (by lia) (by unfold rowDegree; lia)]
  simp only [shiftedCoefficient_eq, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
  rw [show r + 2 * k - k = k + r by lia,
    show 2 * (r + 2 * k) - 3 * k = k + 2 * r by lia,
    show r + 2 * k - 2 * k - 1 = r - 1 by lia, Nat.choose_symm_add,
    choose_asc k r, show k + 2 * r = (k + r + 1) + (r - 1) by lia, choose_asc]
  have hrec : (k + 1).ascFactorial r = (k + r) * (k + 1).ascFactorial (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 by lia]
    rw [Nat.ascFactorial_succ]
    congr 1
    lia
  rw [hrec]
  have hkr : (k : ℝ) + r ≠ 0 := by exact_mod_cast (by lia : k + r ≠ 0)
  push_cast
  field_simp [hkr]

/-- The odd top coefficient, directly from the formula. -/
theorem coeff_odd_top (m : ℕ) :
    ((polynomial (2*m+1)).comp (X+1)).coeff m = 1 := by
  rw [show 2 * m + 1 = 1 + 2 * m by lia,
    coeff_comp_add_one_defect 1 m (by decide)]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial]

/-- The even top coefficient, directly from the formula. -/
theorem coeff_even_top (m : ℕ) :
    ((polynomial (2*m+2)).comp (X+1)).coeff m = ((m:ℝ)+1)*((m:ℝ)+4)/2 := by
  rw [show 2 * m + 2 = 2 + 2 * m by lia,
    coeff_comp_add_one_defect 2 m (by decide)]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial, add_assoc]

/-- The odd next coefficient, directly from the formula. -/
theorem coeff_odd_next (m : ℕ) (hm : 1 ≤ m) :
    ((polynomial (2*m+1)).comp (X+1)).coeff (m-1) =
      (m:ℝ)*((m:ℝ)+1)*((m:ℝ)+4)*((m:ℝ)+5)/12 := by
  rw [show 2 * m + 1 = 3 + 2 * (m - 1) by lia,
    coeff_comp_add_one_defect 3 (m - 1) (by decide)]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial, Nat.cast_sub hm]
  ring

/-- The even next coefficient, directly from the formula. -/
theorem coeff_even_next (m : ℕ) (hm : 1 ≤ m) :
    ((polynomial (2*m+2)).comp (X+1)).coeff (m-1) =
      (m:ℝ)*((m:ℝ)+1)*((m:ℝ)+2)*((m:ℝ)+5)*((m:ℝ)+6)*((m:ℝ)+7)/144 := by
  rw [show 2 * m + 2 = 4 + 2 * (m - 1) by lia,
    coeff_comp_add_one_defect 4 (m - 1) (by decide)]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial, Nat.cast_sub hm]
  ring

/-- The odd next two coefficient, directly from the formula. -/
theorem coeff_odd_next_two (m : ℕ) (hm : 2 ≤ m) :
    ((polynomial (2*m+1)).comp (X+1)).coeff (m-2) =
      ((m:ℝ)-1)*(m:ℝ)*((m:ℝ)+1)*((m:ℝ)+2)*
      ((m:ℝ)+5)*((m:ℝ)+6)*((m:ℝ)+7)*((m:ℝ)+8)/2880 := by
  rw [show 2 * m + 1 = 5 + 2 * (m - 2) by lia,
    coeff_comp_add_one_defect 5 (m - 2) (by decide)]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial, Nat.cast_sub hm]
  ring

/-- The even next two coefficient, directly from the formula. -/
theorem coeff_even_next_two (m : ℕ) (hm : 2 ≤ m) :
    ((polynomial (2*m+2)).comp (X+1)).coeff (m-2) =
      ((m:ℝ)-1)*(m:ℝ)*((m:ℝ)+1)*((m:ℝ)+2)*((m:ℝ)+3)*((m:ℝ)+6)*((m:ℝ)+7)*
        ((m:ℝ)+8)*((m:ℝ)+9)*((m:ℝ)+10)/86400 := by
  rw [show 2 * m + 2 = 6 + 2 * (m - 2) by lia,
    coeff_comp_add_one_defect 6 (m - 2) (by decide)]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.factorial, Nat.cast_sub hm]
  ring

end RealRooted.CatalanWordPeaks.TopCoefficients
