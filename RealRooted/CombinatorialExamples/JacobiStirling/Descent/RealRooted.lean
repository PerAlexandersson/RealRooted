import RealRooted.CombinatorialExamples.JacobiStirling.Descent.Families
import RealRooted.WagnerRightSum
import RealRooted.Wagner.LeftSum

/-!
# Real-rootedness of Jacobi–Stirling descent polynomials

Ma–Wang (arXiv:2610.03111), Theorem 2 and Corollary 2.  For
`i ∈ {1, 2, 3, k - 2, k - 1}`, every nonzero nonnegative combination
`F_{k,i} = ∑_{|S| = i} c_S A_{k,S}` has only simple negative zeros; in particular
`A_{k,i} = ∑_{|S| = i} A_{k,S}` is real-rooted.  Moreover

`F_{k,1} ≺ A_{k,∅}`, `F_{k,2} ≺ H_k`, `F_{k,3} ≺ A_{k-1,∅}`, `E_k ≺ F_{k,k-1}` and
`E_{k+1} ≺ F_{k,k-2}`.

These cases verify five infinite families of Gessel–Lin–Zeng's Conjecture 15 for the
recurrence-defined polynomials (the combinatorial model is not formalized; see
`RealRooted.CombinatorialExamples.JacobiStirling.Descent.Basic`).
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace JacobiStirlingDescent

/-! ### Nonnegative combinations -/

section Combination

variable {ι : Type*} {s : Finset ι} {c : ι → ℝ} {p : ι → ℝ[X]} {h : ℝ[X]} {d : ℕ}

private theorem coeff_sum_C_mul (k : ℕ) :
    (∑ i ∈ s, C (c i) * p i).coeff k = ∑ i ∈ s, c i * (p i).coeff k := by
  simp [coeff_C_mul]

/-- Degree and coefficient data of a positive combination of polynomials of one degree. -/
private theorem sum_facts (hs : s.Nonempty) (hc : ∀ i ∈ s, 0 < c i)
    (hp : ∀ i ∈ s, IsGood (p i) d) :
    (∑ i ∈ s, C (c i) * p i).natDegree = d ∧
      HasPosLeadingCoeff (∑ i ∈ s, C (c i) * p i) ∧
      HasNonnegCoeffs (∑ i ∈ s, C (c i) * p i) ∧
      0 < (∑ i ∈ s, C (c i) * p i).coeff 0 := by
  have hlead : 0 < (∑ i ∈ s, C (c i) * p i).coeff d := by
    rw [coeff_sum_C_mul]
    refine Finset.sum_pos (fun i hi => mul_pos (hc i hi) ?_) hs
    have := (hp i hi).pos
    rwa [HasPosLeadingCoeff, leadingCoeff, (hp i hi).natDegree_eq] at this
  have hdeg : (∑ i ∈ s, C (c i) * p i).natDegree = d := by
    refine natDegree_eq_of_le_of_coeff_ne_zero
      ((natDegree_le_iff_coeff_eq_zero).mpr fun k hk => ?_) hlead.ne'
    rw [coeff_sum_C_mul]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [coeff_eq_zero_of_natDegree_lt (by rw [(hp i hi).natDegree_eq]; exact_mod_cast hk),
      mul_zero]
  refine ⟨hdeg, by rw [HasPosLeadingCoeff, leadingCoeff, hdeg]; exact hlead, fun k => ?_, ?_⟩
  · rw [coeff_sum_C_mul]
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi).le ((hp i hi).nonneg k)
  · rw [coeff_sum_C_mul]
    exact Finset.sum_pos (fun i hi => mul_pos (hc i hi) (hp i hi).coeff_zero_pos) hs

private theorem strictInterl_sum_right (hs : s.Nonempty) (hc : ∀ i ∈ s, 0 < c i)
    (hp : ∀ i ∈ s, IsGood (p i) d) (hph : ∀ i ∈ s, StrictInterl (p i) h) :
    StrictInterl (∑ i ∈ s, C (c i) * p i) h := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using (hph a (by simp)).C_mul_left (hc a (by simp)).ne'
  | cons a t ha ht ih =>
    rw [Finset.sum_cons]
    have hc' : ∀ i ∈ t, 0 < c i := fun i hi => hc i (Finset.mem_cons_of_mem hi)
    have hp' : ∀ i ∈ t, IsGood (p i) d := fun i hi => hp i (Finset.mem_cons_of_mem hi)
    exact StrictInterl.add_of_right_of_posLeadingCoeff
      ((hph a (by simp)).C_mul_left (hc a (by simp)).ne')
      (ih hc' hp' fun i hi => hph i (Finset.mem_cons_of_mem hi))
      (hasPosLeadingCoeff_C_mul (hc a (by simp)) (hp a (by simp)).pos)
      (sum_facts ht hc' hp').2.1

private theorem strictInterl_sum_left (hs : s.Nonempty) (hc : ∀ i ∈ s, 0 < c i)
    (hp : ∀ i ∈ s, IsGood (p i) d) (hhp : ∀ i ∈ s, StrictInterl h (p i)) :
    StrictInterl h (∑ i ∈ s, C (c i) * p i) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using (hhp a (by simp)).C_mul_right (hc a (by simp)).ne'
  | cons a t ha ht ih =>
    rw [Finset.sum_cons]
    have hc' : ∀ i ∈ t, 0 < c i := fun i hi => hc i (Finset.mem_cons_of_mem hi)
    have hp' : ∀ i ∈ t, IsGood (p i) d := fun i hi => hp i (Finset.mem_cons_of_mem hi)
    exact StrictInterl.add_of_left
      ((hhp a (by simp)).C_mul_right (hc a (by simp)).ne')
      (ih hc' hp' fun i hi => hhp i (Finset.mem_cons_of_mem hi))
      (hasPosLeadingCoeff_C_mul (hc a (by simp)) (hp a (by simp)).pos)
      (sum_facts ht hc' hp').2.1

/-- Restricting a nonnegative combination to its positive weights. -/
private theorem sum_eq_sum_pos (hc : ∀ i ∈ s, 0 ≤ c i) :
    ∑ i ∈ s, C (c i) * p i = ∑ i ∈ s with 0 < c i, C (c i) * p i := by
  classical
  refine (Finset.sum_filter_of_ne fun i hi hne => lt_of_le_of_ne (hc i hi) ?_).symm
  rintro h0
  rw [← h0, map_zero, zero_mul] at hne
  exact hne rfl

/-- A nonzero nonnegative combination of polynomials that all strictly interleave a common
`h` on the left keeps the invariant and strictly interleaves `h`. -/
theorem isGood_sum_of_strictInterleave_right (hp : ∀ i ∈ s, IsGood (p i) d)
    (hh : IsGood h (d + 1)) (hph : ∀ i ∈ s, StrictInterleave (p i) h)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hpos : ∃ i ∈ s, 0 < c i) :
    IsGood (∑ i ∈ s, C (c i) * p i) d ∧ StrictInterleave (∑ i ∈ s, C (c i) * p i) h := by
  classical
  rw [sum_eq_sum_pos hc]
  set t := s.filter (fun i => 0 < c i)
  obtain ⟨i₀, hi₀, hci₀⟩ := hpos
  have ht : t.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hci₀⟩⟩
  have htc : ∀ i ∈ t, 0 < c i := fun i hi => (Finset.mem_filter.mp hi).2
  have htp : ∀ i ∈ t, IsGood (p i) d := fun i hi => hp i (Finset.mem_filter.mp hi).1
  have htph : ∀ i ∈ t, StrictInterleave (p i) h :=
    fun i hi => hph i (Finset.mem_filter.mp hi).1
  obtain ⟨hdeg, hlc, hnn, h0⟩ := sum_facts ht htc htp
  have hint := strictInterl_sum_right ht htc htp fun i hi => (htph i hi).1
  have hno : ∀ r, h.IsRoot r → ¬ (∑ i ∈ t, C (c i) * p i).IsRoot r := by
    intro r hr hFr
    have hsum : 0 < h.derivative.eval r * (∑ i ∈ t, C (c i) * p i).eval r := by
      rw [eval_finsetSum, Finset.mul_sum]
      refine Finset.sum_pos (fun i hi => ?_) ht
      have hw := (htph i hi).wronskian_pos (htp i hi) hh r
      rw [hr.eq_zero, zero_mul, sub_zero] at hw
      rw [eval_mul, eval_C]
      nlinarith [htc i hi]
    rw [hFr.eq_zero, mul_zero] at hsum
    exact lt_irrefl _ hsum
  exact ⟨⟨hdeg, hlc, hnn, h0, hint.1.2,
    (hint.hasSimpleRoots_of_no_common_root fun r hr => hno r hr.2 hr.1).1⟩,
    hint, fun r hF hh' => hno r hh' hF⟩

/-- A nonzero nonnegative combination of polynomials that are all strictly interleaved by a
common `h` keeps the invariant and is strictly interleaved by `h`. -/
theorem isGood_sum_of_strictInterleave_left (hp : ∀ i ∈ s, IsGood (p i) (d + 1))
    (hh : IsGood h d) (hhp : ∀ i ∈ s, StrictInterleave h (p i))
    (hc : ∀ i ∈ s, 0 ≤ c i) (hpos : ∃ i ∈ s, 0 < c i) :
    IsGood (∑ i ∈ s, C (c i) * p i) (d + 1) ∧
      StrictInterleave h (∑ i ∈ s, C (c i) * p i) := by
  classical
  rw [sum_eq_sum_pos hc]
  set t := s.filter (fun i => 0 < c i)
  obtain ⟨i₀, hi₀, hci₀⟩ := hpos
  have ht : t.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hci₀⟩⟩
  have htc : ∀ i ∈ t, 0 < c i := fun i hi => (Finset.mem_filter.mp hi).2
  have htp : ∀ i ∈ t, IsGood (p i) (d + 1) := fun i hi => hp i (Finset.mem_filter.mp hi).1
  have hthp : ∀ i ∈ t, StrictInterleave h (p i) :=
    fun i hi => hhp i (Finset.mem_filter.mp hi).1
  obtain ⟨hdeg, hlc, hnn, h0⟩ := sum_facts ht htc htp
  have hint := strictInterl_sum_left ht htc htp fun i hi => (hthp i hi).1
  have hno : ∀ r, h.IsRoot r → ¬ (∑ i ∈ t, C (c i) * p i).IsRoot r := by
    intro r hr hFr
    have hsum : h.derivative.eval r * (∑ i ∈ t, C (c i) * p i).eval r < 0 := by
      rw [eval_finsetSum, Finset.mul_sum]
      refine Finset.sum_neg (fun i hi => ?_) ht
      have hw := (hthp i hi).wronskian_pos hh (htp i hi) r
      rw [hr.eq_zero, mul_zero, zero_sub] at hw
      rw [eval_mul, eval_C]
      nlinarith [htc i hi]
    rw [hFr.eq_zero, mul_zero] at hsum
    exact lt_irrefl _ hsum
  exact ⟨⟨hdeg, hlc, hnn, h0, hint.2.1.2,
    (hint.hasSimpleRoots_of_no_common_root fun r hr => hno r hr.1 hr.2).2⟩,
    hint, fun r hh' hF => hno r hh' hF⟩

end Combination

/-! ### The five families -/

/-- `F_{k,i} = ∑_{|S| = i} c_S A_{k,S}`. -/
def weightedDescentSum (k i : ℕ) (c : Finset ℕ → ℝ) : ℝ[X] :=
  ∑ S ∈ (Finset.Icc 1 k).powersetCard i, C (c S) * descentPoly k S

/-- The Jacobi–Stirling descent polynomial `A_{k,i} = ∑_{|S| = i} A_{k,S}`. -/
def descentSum (k i : ℕ) : ℝ[X] :=
  ∑ S ∈ (Finset.Icc 1 k).powersetCard i, descentPoly k S

theorem descentSum_eq_weightedDescentSum (k i : ℕ) :
    descentSum k i = weightedDescentSum k i (fun _ => 1) := by
  simp [descentSum, weightedDescentSum]

variable {c : Finset ℕ → ℝ}

/-- **Ma–Wang, Corollary 2, `i = 1`.**  `F_{k,1} ≺ A_{k,∅}`, written at `k + 1`. -/
theorem isGood_weightedDescentSum_one (k : ℕ)
    (hc : ∀ S ∈ (Finset.Icc 1 (k + 1)).powersetCard 1, 0 ≤ c S)
    (hpos : ∃ S ∈ (Finset.Icc 1 (k + 1)).powersetCard 1, 0 < c S) :
    IsGood (weightedDescentSum (k + 1) 1 c) (2 * k) ∧
      StrictInterleave (weightedDescentSum (k + 1) 1 c) (descentPoly (k + 1) ∅) := by
  refine isGood_sum_of_strictInterleave_right (fun S hS => ?_) (isGood_descentPoly_empty k)
    (fun S hS => ?_) hc hpos <;> obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  · exact (isGood_descentPoly hsub).of_eq (by rw [hcard]; lia)
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
    exact strictInterleave_singleton (hsub (Finset.mem_singleton_self j))

/-- **Ma–Wang, Corollary 2, `i = 2`.**  `F_{k,2} ≺ H_k`, written at `k + 2`. -/
theorem isGood_weightedDescentSum_two (k : ℕ)
    (hc : ∀ S ∈ (Finset.Icc 1 (k + 2)).powersetCard 2, 0 ≤ c S)
    (hpos : ∃ S ∈ (Finset.Icc 1 (k + 2)).powersetCard 2, 0 < c S) :
    IsGood (weightedDescentSum (k + 2) 2 c) (2 * k + 1) ∧
      StrictInterleave (weightedDescentSum (k + 2) 2 c) (hPoly (k + 1)) := by
  refine isGood_sum_of_strictInterleave_right (fun S hS => ?_) (isGood_hPoly k)
    (fun S hS => ?_) hc hpos <;> obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  · exact (isGood_descentPoly hsub).of_eq (by rw [hcard]; lia)
  · exact strictInterleave_hPoly k hsub hcard

/-- **Ma–Wang, Corollary 2, `i = 3`.**  `F_{k,3} ≺ A_{k-1,∅}`, written at `k + 3`. -/
theorem isGood_weightedDescentSum_three (k : ℕ)
    (hc : ∀ S ∈ (Finset.Icc 1 (k + 3)).powersetCard 3, 0 ≤ c S)
    (hpos : ∃ S ∈ (Finset.Icc 1 (k + 3)).powersetCard 3, 0 < c S) :
    IsGood (weightedDescentSum (k + 3) 3 c) (2 * k + 2) ∧
      StrictInterleave (weightedDescentSum (k + 3) 3 c) (descentPoly (k + 2) ∅) := by
  refine isGood_sum_of_strictInterleave_right (fun S hS => ?_)
    ((isGood_descentPoly_empty (k + 1)).of_eq (by lia)) (fun S hS => ?_) hc hpos <;>
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  · exact (isGood_descentPoly hsub).of_eq (by rw [hcard]; lia)
  · exact strictInterleave_three k hsub hcard

/-- **Ma–Wang, Corollary 2, `i = k - 1`.**  `E_k ≺ F_{k,k-1}`, written at `k + 1`. -/
theorem isGood_weightedDescentSum_sub_one (k : ℕ)
    (hc : ∀ S ∈ (Finset.Icc 1 (k + 1)).powersetCard k, 0 ≤ c S)
    (hpos : ∃ S ∈ (Finset.Icc 1 (k + 1)).powersetCard k, 0 < c S) :
    IsGood (weightedDescentSum (k + 1) k c) (k + 1) ∧
      StrictInterleave (descentPoly (k + 1) (Finset.Icc 1 (k + 1)))
        (weightedDescentSum (k + 1) k c) := by
  refine isGood_sum_of_strictInterleave_left (fun S hS => ?_)
    ((isGood_descentPoly_Icc (k + 1)).of_eq (by lia)) (fun S hS => ?_) hc hpos <;>
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  · exact (isGood_descentPoly hsub).of_eq (by rw [hcard]; lia)
  · exact strictInterleave_Icc_left k hsub hcard

/-- **Ma–Wang, Corollary 2, `i = k - 2`.**  `E_{k+1} ≺ F_{k,k-2}`, written at `k + 2`. -/
theorem isGood_weightedDescentSum_sub_two (k : ℕ)
    (hc : ∀ S ∈ (Finset.Icc 1 (k + 2)).powersetCard k, 0 ≤ c S)
    (hpos : ∃ S ∈ (Finset.Icc 1 (k + 2)).powersetCard k, 0 < c S) :
    IsGood (weightedDescentSum (k + 2) k c) (k + 3) ∧
      StrictInterleave (descentPoly (k + 3) (Finset.Icc 1 (k + 3)))
        (weightedDescentSum (k + 2) k c) := by
  refine isGood_sum_of_strictInterleave_left (fun S hS => ?_)
    ((isGood_descentPoly_Icc (k + 3)).of_eq (by lia)) (fun S hS => ?_) hc hpos <;>
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  · exact (isGood_descentPoly hsub).of_eq (by rw [hcard]; lia)
  · exact strictInterleave_Icc_succ_left k hsub hcard

/-- **Ma–Wang, Theorem 2 / Corollary 2.**  For `i ∈ {1, 2, 3, k - 2, k - 1}`, every nonzero
nonnegative combination `∑_{|S| = i} c_S A_{k,S}` has only real, simple, negative zeros. -/
theorem weightedDescentSum_splits_simple_neg {k i : ℕ}
    (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i + 2 = k ∨ i + 1 = k)
    (hc : ∀ S ∈ (Finset.Icc 1 k).powersetCard i, 0 ≤ c S)
    (hpos : ∃ S ∈ (Finset.Icc 1 k).powersetCard i, 0 < c S) :
    (weightedDescentSum k i c).Splits ∧ HasSimpleRoots (weightedDescentSum k i c) ∧
      ∀ r, (weightedDescentSum k i c).IsRoot r → r < 0 := by
  suffices h : ∃ d, IsGood (weightedDescentSum k i c) d by
    obtain ⟨d, hd⟩ := h
    exact ⟨hd.splits, hd.simple, fun r hr => hd.isRoot_neg hr⟩
  have hik : i ≤ k := by
    obtain ⟨S, hS, -⟩ := hpos
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
    simpa [hcard] using Finset.card_le_card hsub
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by lia⟩
    exact ⟨_, (isGood_weightedDescentSum_one k hc hpos).1⟩
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by lia⟩
    exact ⟨_, (isGood_weightedDescentSum_two k hc hpos).1⟩
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by lia⟩
    exact ⟨_, (isGood_weightedDescentSum_three k hc hpos).1⟩
  · exact ⟨_, (isGood_weightedDescentSum_sub_two i hc hpos).1⟩
  · exact ⟨_, (isGood_weightedDescentSum_sub_one i hc hpos).1⟩

/-- **Ma–Wang, Theorem 2.**  For `1 ≤ i ≤ k` with `i ∈ {1, 2, 3, k - 2, k - 1}`, the
Jacobi–Stirling descent polynomial `A_{k,i}` has only real, simple, negative zeros. -/
theorem descentSum_splits_simple_neg {k i : ℕ}
    (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i + 2 = k ∨ i + 1 = k) (hik : i ≤ k) :
    (descentSum k i).Splits ∧ HasSimpleRoots (descentSum k i) ∧
      ∀ r, (descentSum k i).IsRoot r → r < 0 := by
  rw [descentSum_eq_weightedDescentSum]
  obtain ⟨S, hS⟩ := (Finset.powersetCard_nonempty (n := i) (s := Finset.Icc 1 k)).mpr
    (by rw [Nat.card_Icc]; lia)
  exact weightedDescentSum_splits_simple_neg hi (fun _ _ => zero_le_one) ⟨S, hS, one_pos⟩

end JacobiStirlingDescent
end RealRooted
