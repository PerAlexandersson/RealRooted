module

public import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.SecondOrder
public import RealRooted.Mathlib.Algebra.Polynomial.Splits.Derivative
public import RealRooted.Wronskian.Algebra

/-!
# Root exclusion from a second-order polynomial ODE

This file isolates the Laguerre-discriminant argument used to exclude a
rightmost root from an interval: if `a p'' + b p' = λ p` and
`b² + 4aλ > 0` on `[L, U]`, then the identity
`(2ap' + bp)² = (b² + 4aλ)p² + 4a²(p'² - pp'')` and Laguerre's inequality
keep `2ap' + bp` away from zero there, so no root of `p` lies in `[L, U]`
once the sign at `U` is fixed (issue #1327).
-/

public section

open Polynomial

namespace RealRooted

/-- The square identity associated with the polynomial ODE
`a * p'' + b * p' - λ * p = 0`. -/
theorem second_order_ode_auxiliary_sq {p a b : ℝ[X]} {lam x : ℝ}
    (hode : a * p.derivative.derivative + b * p.derivative - C lam * p = 0) :
    (2 * a.eval x * p.derivative.eval x + b.eval x * p.eval x) ^ 2 =
      (b.eval x ^ 2 + 4 * a.eval x * lam) * p.eval x ^ 2 +
        4 * a.eval x ^ 2 *
          (p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x) := by
  have hode_eval := congrArg (eval x) hode
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_zero] at hode_eval
  calc
    (2 * a.eval x * p.derivative.eval x + b.eval x * p.eval x) ^ 2 =
        (b.eval x ^ 2 + 4 * a.eval x * lam) * p.eval x ^ 2 +
          4 * a.eval x ^ 2 *
            (p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x) +
          4 * a.eval x * p.eval x *
            (a.eval x * p.derivative.derivative.eval x +
              b.eval x * p.derivative.eval x - lam * p.eval x) := by
      ring
    _ = (b.eval x ^ 2 + 4 * a.eval x * lam) * p.eval x ^ 2 +
        4 * a.eval x ^ 2 *
          (p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x) := by
      rw [hode_eval, mul_zero, add_zero]

/-- Under strict positivity of the ODE discriminant, the auxiliary expression
`2 a p' + b p` cannot vanish away from the roots of a splitting polynomial. -/
theorem second_order_ode_auxiliary_ne_zero {p a b : ℝ[X]} {lam x : ℝ}
    (hp : p.Splits)
    (hode : a * p.derivative.derivative + b * p.derivative - C lam * p = 0)
    (hdisc : 0 < b.eval x ^ 2 + 4 * a.eval x * lam)
    (hpx : p.eval x ≠ 0) :
    2 * a.eval x * p.derivative.eval x + b.eval x * p.eval x ≠ 0 := by
  have hlag := laguerre_form_nonneg hp x
  have hfirst :
      0 < (b.eval x ^ 2 + 4 * a.eval x * lam) * p.eval x ^ 2 :=
    mul_pos hdisc (by positivity)
  have hsecond :
      0 ≤ 4 * a.eval x ^ 2 *
        (p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x) :=
    mul_nonneg (by positivity) hlag
  have hsq :
      0 < (2 * a.eval x * p.derivative.eval x + b.eval x * p.eval x) ^ 2 := by
    rw [second_order_ode_auxiliary_sq hode]
    exact add_pos_of_pos_of_nonneg hfirst hsecond
  intro hzero
  rw [hzero] at hsq
  norm_num at hsq

/-- A rightmost root of a splitting polynomial satisfying
`a * p'' + b * p' - λ * p = 0` lies to the left of `L` when the ODE
discriminant is positive on `[L, U]` and `2 a p' + b p` changes from negative
at the root to positive at `U`. -/
theorem isRoot_lt_of_second_order_ode {p a b : ℝ[X]} {lam L U r : ℝ}
    (hp : p.Splits)
    (hode : a * p.derivative.derivative + b * p.derivative - C lam * p = 0)
    (hr : p.IsRoot r)
    (hrightmost : ∀ s, p.IsRoot s → s ≤ r)
    (hrU : r ≤ U)
    (hdisc : ∀ x ∈ Set.Icc L U, 0 < b.eval x ^ 2 + 4 * a.eval x * lam)
    (hroot_sign : 2 * a.eval r * p.derivative.eval r < 0)
    (hU_sign :
      0 < 2 * a.eval U * p.derivative.eval U + b.eval U * p.eval U) :
    r < L := by
  by_contra hrL
  have hLr : L ≤ r := le_of_not_gt hrL
  let H : ℝ[X] := C 2 * a * p.derivative + b * p
  have hHr : H.eval r < 0 := by
    simp only [H, eval_add, eval_mul, eval_C]
    rw [Polynomial.IsRoot.def.mp hr, mul_zero, add_zero]
    exact hroot_sign
  have hHU : 0 < H.eval U := by
    simpa only [H, eval_add, eval_mul, eval_C] using hU_sign
  obtain ⟨s, hs, hHs⟩ := intermediate_value_Icc hrU H.continuous.continuousOn
    ⟨hHr.le, hHU.le⟩
  have hrs : r < s := by
    refine lt_of_le_of_ne hs.1 ?_
    intro hsr
    subst s
    linarith
  have hps : p.eval s ≠ 0 := by
    intro hps
    have hsroot : p.IsRoot s := Polynomial.IsRoot.def.mpr hps
    linarith [hrightmost s hsroot]
  have hHne : H.eval s ≠ 0 := by
    simpa only [H, eval_add, eval_mul, eval_C] using
      second_order_ode_auxiliary_ne_zero hp hode
        (hdisc s ⟨hLr.trans hs.1, hs.2⟩) hps
  exact hHne hHs

/-- A positive-leading-coefficient version of
`isRoot_lt_of_second_order_ode`.  Negativity of `a` at the rightmost root
forces the required sign because the ODE ordinary-point lemma makes that root
simple, and the derivative is positive at a simple rightmost root. -/
theorem isRoot_lt_of_second_order_ode_of_leadingCoeff_pos
    {p a b : ℝ[X]} {lam L U r : ℝ}
    (hp : p.Splits)
    (hpos : 0 < p.leadingCoeff)
    (hode : a * p.derivative.derivative + b * p.derivative - C lam * p = 0)
    (hr : p.IsRoot r)
    (hrightmost : ∀ s, p.IsRoot s → s ≤ r)
    (hrU : r ≤ U)
    (har : a.eval r < 0)
    (hdisc : ∀ x ∈ Set.Icc L U, 0 < b.eval x ^ 2 + 4 * a.eval x * lam)
    (hU_sign :
      0 < 2 * a.eval U * p.derivative.eval U + b.eval U * p.eval U) :
    r < L := by
  have hp_ne : p ≠ 0 := by
    intro hp_zero
    subst p
    simp at hpos
  have hode' :
      a * p.derivative.derivative + b * p.derivative + (-C lam) * p = 0 := by
    simpa only [sub_eq_add_neg, neg_mul] using hode
  have hder_ne : p.derivative.eval r ≠ 0 :=
    Polynomial.eval_derivative_ne_zero_of_second_order_ode hp_ne hode' hr har.ne
  have hmult : p.rootMultiplicity r = 1 := by
    have hmult_pos : 0 < p.rootMultiplicity r :=
      (rootMultiplicity_pos hp_ne).mpr hr
    have hmult_le : p.rootMultiplicity r ≤ 1 := by
      by_contra hle
      have hmultiple : 1 < p.rootMultiplicity r := by lia
      have hder_root :=
        ((one_lt_rootMultiplicity_iff_isRoot hp_ne).mp hmultiple).2
      exact hder_ne hder_root.eq_zero
    lia
  have hr_mem : r ∈ p.roots := (mem_roots hp_ne).mpr hr
  have hcount : p.roots.count r = 1 := by
    rw [count_roots]
    exact hmult
  have hder_pos : 0 < p.derivative.eval r := by
    rw [hp.eval_derivative_at_root_of_roots_count_one r hr_mem hcount]
    apply mul_pos hpos
    apply Multiset.prod_pos
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hy
    have hs_mem : s ∈ p.roots := Multiset.mem_of_mem_erase hs
    have hsr : s ≤ r := hrightmost s ((mem_roots hp_ne).mp hs_mem)
    have hsr_ne : s ≠ r := by
      intro hsr_eq
      subst s
      have hcount_pos : 0 < (p.roots.erase r).count r :=
        Multiset.count_pos.mpr hs
      rw [Multiset.count_erase_self, hcount] at hcount_pos
      norm_num at hcount_pos
    exact sub_pos.mpr (lt_of_le_of_ne hsr hsr_ne)
  apply isRoot_lt_of_second_order_ode hp hode hr hrightmost hrU hdisc
  · nlinarith
  · exact hU_sign

/-- Every root lies to the left of `L` if all roots are at most `U`, `a` is
negative at any root in `[L, U]`, the ODE discriminant is positive throughout
that interval, and `2 a p' + b p` is positive at `U`. -/
theorem roots_lt_of_second_order_ode {p a b : ℝ[X]} {lam L U : ℝ}
    (hp : p.Splits)
    (hpos : 0 < p.leadingCoeff)
    (hode : a * p.derivative.derivative + b * p.derivative - C lam * p = 0)
    (hroots_le : ∀ r, p.IsRoot r → r ≤ U)
    (ha_neg : ∀ r, p.IsRoot r → L ≤ r → a.eval r < 0)
    (hdisc : ∀ x ∈ Set.Icc L U, 0 < b.eval x ^ 2 + 4 * a.eval x * lam)
    (hU_sign :
      0 < 2 * a.eval U * p.derivative.eval U + b.eval U * p.eval U) :
    ∀ r, p.IsRoot r → r < L := by
  intro r hr
  have hp_ne : p ≠ 0 := by
    intro hp_zero
    subst p
    simp at hpos
  have hdeg : 1 ≤ p.natDegree := by
    have hdegree_pos : 0 < p.degree := degree_pos_of_root hp_ne hr
    have hnatDegree_pos : 0 < p.natDegree :=
      natDegree_pos_iff_degree_pos.mpr hdegree_pos
    lia
  obtain ⟨s, hsroot, hsmax_mem⟩ :=
    exists_rightmost_root_of_isRealRooted hp_ne hp hdeg
  have hsmax : ∀ t, p.IsRoot t → t ≤ s := by
    intro t ht
    exact hsmax_mem t ((mem_roots hp_ne).mpr ht)
  have hrs : r ≤ s := hsmax r hr
  have hsU : s ≤ U := hroots_le s hsroot
  by_contra hrL
  have hLr : L ≤ r := le_of_not_gt hrL
  have hLs : L ≤ s := hLr.trans hrs
  have hsL := isRoot_lt_of_second_order_ode_of_leadingCoeff_pos hp hpos hode
    hsroot hsmax hsU (ha_neg s hsroot hLs) hdisc hU_sign
  exact (not_lt_of_ge hLs) hsL

end RealRooted
