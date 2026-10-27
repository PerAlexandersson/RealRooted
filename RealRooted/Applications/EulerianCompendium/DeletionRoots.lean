module

public import RealRooted.Applications.EulerianCompendium.DeletionFamily
import RealRooted.Compatibility.Three
import RealRooted.EulerianMixedCompatibility
import RealRooted.EulerianCompletion
import RealRooted.CommonInterleaver.SuccDegreeLowDegree
import RealRooted.Compatibility.Basic
public import RealRooted.PFPolynomial
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Linear

/-!
# Real-rootedness of the deletion-stable family

The two-summand decomposition of `Q_r^(a)` is treated by compatibility,
following the three-component induction in paper `thm:largerFamily`.
-/

@[expose] public section

open Polynomial RealRooted

noncomputable section

namespace RealRooted.EulerianCompendium

/-- The first summand `E_{1, a+k} Q_k^(a)` in the two-summand decomposition of `Q_{k+2}^(a)`. -/
def deletionFirst (a k : ℕ) : ℝ[X] :=
  eulerInsertionStep 1 (a + k) (deletionPolynomial a k)

/-- The second summand `E_{0, a+k+1} Q_{k+1}^(a)` in the two-summand decomposition of
`Q_{k+2}^(a)`. -/
def deletionSecond (a k : ℕ) : ℝ[X] :=
  eulerInsertionStep 0 (a + k + 1) (deletionPolynomial a (k + 1))

private theorem deletionFirst_add_second (a k : ℕ) :
    deletionFirst a k + deletionSecond a k = deletionPolynomial a (k + 2) :=
  rfl

private theorem deletionFirst_degree_pos (a k : ℕ) :
    (deletionFirst a k).natDegree = k + 1 ∧
      HasPosLeadingCoeff (deletionFirst a k) := by
  have h := deletionPolynomial_degree_nonneg a k
  simpa [deletionFirst, h.1] using
    (eulerInsertionStep_degree_pos (c := (1 : ℝ))
      (d := a + k) (p := deletionPolynomial a k)
      (by rw [h.1]; lia) h.2.1)

private theorem deletionSecond_degree_pos (a k : ℕ) :
    (deletionSecond a k).natDegree = k + 2 ∧
      HasPosLeadingCoeff (deletionSecond a k) := by
  have h := deletionPolynomial_degree_nonneg a (k + 1)
  simpa [deletionSecond, h.1] using
    (eulerInsertionStep_degree_pos (c := (0 : ℝ))
      (d := a + k + 1) (p := deletionPolynomial a (k + 1))
      (by rw [h.1]; lia) h.2.1)

private theorem deletionFirst_nonneg (a k : ℕ) :
    HasNonnegCoeffs (deletionFirst a k) := by
  have h := deletionPolynomial_degree_nonneg a k
  exact h.2.2.eulerInsertionStep (by norm_num) (by rw [h.1]; lia)

private theorem deletionSecond_nonneg (a k : ℕ) :
    HasNonnegCoeffs (deletionSecond a k) := by
  have h := deletionPolynomial_degree_nonneg a (k + 1)
  exact h.2.2.eulerInsertionStep (by norm_num) (by rw [h.1]; lia)

private theorem deletionFirst_completion (a k : ℕ) :
    deletionFirst a k = deletionPolynomial a (k + 1) -
      C ((-1 : ℝ) ^ (k + 1)) := by
  rw [deletionPolynomial_recurrence]
  unfold deletionFirst
  ring

private theorem deletionFirst_zero (a : ℕ) :
    deletionFirst a 0 = 1 + C ((a : ℝ) + 1) * X := by
  simp [deletionFirst, deletionPolynomial, eulerInsertionStep]

private theorem deletionSecond_zero (a : ℕ) :
    deletionSecond a 0 =
      C ((a : ℝ) + 1) * (X * deletionFirst a 0) := by
  rw [deletionFirst_zero]
  simp [deletionSecond, deletionPolynomial, eulerInsertionStep]
  ring

/-- The initial compatible pair in `thm:largerFamily`, valid for every
parameter `a ≥ 1`. -/
private theorem deletionComponents_zero_compatible (a : ℕ) :
    Compatible (deletionFirst a 0) (deletionSecond a 0) := by
  have hfirst := deletionFirst_degree_pos a 0
  have hnonneg := deletionFirst_nonneg a 0
  have hsplit : (deletionFirst a 0).Splits := by
    exact (isRealRooted_of_degree_one hfirst.1).2
  have hinter : StrictInterl (deletionFirst a 0)
      (X * deletionFirst a 0) :=
    strictInterl_self_X_mul_of_nonneg hfirst.2.ne_zero hsplit hnonneg
  have hscaled := StrictInterl.C_mul_right hinter (by
    have ha : 0 < (a : ℝ) + 1 := by positivity
    exact ha.ne')
  rw [← deletionSecond_zero] at hscaled
  exact Compatible.of_strictInterl hscaled

private theorem deletionPolynomial_pf_of_components (a k : ℕ)
    (hcomp : Compatible (deletionFirst a k) (deletionSecond a k)) :
    IsPFPolynomial (deletionPolynomial a (k + 2)) := by
  have hpos := (deletionPolynomial_degree_nonneg a (k + 2)).2.1
  have hsplit : (deletionPolynomial a (k + 2)).Splits := by
    rw [← deletionFirst_add_second]
    exact hcomp.splits_add (by
      rw [deletionFirst_add_second]
      exact hpos.ne_zero)
  exact IsPFPolynomial.of_realRooted_nonneg
    (deletionPolynomial_degree_nonneg a (k + 2)).2.2 hsplit

private theorem deletionFirst_pf_of_components (a k : ℕ)
    (hcomp : Compatible (deletionFirst a k) (deletionSecond a k)) :
    IsPFPolynomial (deletionFirst a k) := by
  have hpos := (deletionFirst_degree_pos a k).2
  exact IsPFPolynomial.of_realRooted_nonneg (deletionFirst_nonneg a k)
    (hcomp.isRealRooted_left hpos).2

private theorem deletionSecond_pf_of_components (a k : ℕ)
    (hcomp : Compatible (deletionFirst a k) (deletionSecond a k)) :
    IsPFPolynomial (deletionSecond a k) := by
  have hpos := (deletionSecond_degree_pos a k).2
  exact IsPFPolynomial.of_realRooted_nonneg (deletionSecond_nonneg a k)
    (hcomp.isRealRooted_right hpos).2

private theorem deletionPolynomial_one_pf (a : ℕ) :
    IsPFPolynomial (deletionPolynomial a 1) := by
  have h := deletionPolynomial_degree_nonneg a 1
  exact IsPFPolynomial.of_realRooted_nonneg h.2.2
    (isRealRooted_of_degree_one h.1).2

private theorem deletionCompatible_first_sum_of_three
    {x y z : ℝ[X]}
    (hx : x ≠ 0 ∧ x.Splits) (hy : y ≠ 0 ∧ y.Splits)
    (hz : z ≠ 0 ∧ z.Splits)
    (hxpos : HasPosLeadingCoeff x) (hypos : HasPosLeadingCoeff y)
    (hzpos : HasPosLeadingCoeff z)
    (hxy : Compatible x y) (hxz : Compatible x z)
    (hyz : Compatible y z) : Compatible x (y + z) := by
  have h := Compatible.add_C_mul_left_of_pairwise_three
    (a := y) (b := z) (c := x) (r := 1)
    (by norm_num) hy hz hx hypos hzpos hxpos hyz hxy.comm hxz.comm
  simpa using h.comm

private theorem deletionFirst_one_eq (a : ℕ) :
    deletionFirst a 1 =
      C ((a : ℝ) + 1) * (X * (C 2 + C ((a : ℝ) + 1) * X)) := by
  simp [deletionFirst, deletionPolynomial, eulerInsertionStep]
  simp only [map_ofNat]
  ring

private theorem deletionFirst_zero_second_step_eq (a : ℕ) :
    eulerInsertionStep 0 (a + 2) (deletionFirst a 0) =
      C ((a : ℝ) + 2) * (X * (C 2 + C ((a : ℝ) + 1) * X)) := by
  rw [deletionFirst_zero]
  simp [eulerInsertionStep]
  simp only [map_ofNat]
  ring

/-- At the one-dimensional crossing, both relevant Euler outputs are
positive multiples of the same polynomial. -/
private theorem deletionFirst_one_compatible_first_zeroStep (a : ℕ) :
    Compatible (deletionFirst a 1)
      (eulerInsertionStep 0 (a + 2) (deletionFirst a 0)) := by
  let H : ℝ[X] := X * (C 2 + C ((a : ℝ) + 1) * X)
  have hb : ((a : ℝ) + 1) ≠ 0 := by positivity
  have hlinear_deg : (C 2 + C ((a : ℝ) + 1) * X : ℝ[X]).natDegree = 1 := by
    have hlt : (C (2 : ℝ)).natDegree <
        (C ((a : ℝ) + 1) * X : ℝ[X]).natDegree := by
      rw [natDegree_C_mul hb, natDegree_X, natDegree_C]
      norm_num
    rw [natDegree_add_eq_right_of_natDegree_lt hlt,
      natDegree_C_mul hb, natDegree_X]
  have hlinear_rr := isRealRooted_of_degree_one hlinear_deg
  have hH : H.Splits := Polynomial.Splits.X.mul hlinear_rr.2
  have hH0 : H ≠ 0 := mul_ne_zero X_ne_zero hlinear_rr.1
  intro α β _ _
  rw [deletionFirst_one_eq, deletionFirst_zero_second_step_eq]
  have heq : C α * (C ((a : ℝ) + 1) * H) +
      C β * (C ((a : ℝ) + 2) * H) =
      C (α * ((a : ℝ) + 1) + β * ((a : ℝ) + 2)) * H := by
    simp only [map_ofNat, map_add, map_mul]
    ring
  change C α * (C ((a : ℝ) + 1) * H) +
    C β * (C ((a : ℝ) + 2) * H) = 0 ∨
      (C α * (C ((a : ℝ) + 1) * H) +
        C β * (C ((a : ℝ) + 2) * H) ≠ 0 ∧
        (C α * (C ((a : ℝ) + 1) * H) +
          C β * (C ((a : ℝ) + 2) * H)).Splits)
  rw [heq]
  by_cases hc : α * ((a : ℝ) + 1) + β * ((a : ℝ) + 2) = 0
  · left
    simp [hc]
  · right
    exact ⟨mul_ne_zero (C_ne_zero.mpr hc) hH0, hH.C_mul _⟩

/-- One pairwise-compatibility step for the two-part deletion recurrence. -/
private theorem deletionComponents_next (a j : ℕ)
    (hprev : Compatible (deletionFirst a j) (deletionSecond a j))
    (hQpf : IsPFPolynomial (deletionPolynomial a (j + 1))) :
    Compatible (deletionFirst a (j + 1)) (deletionSecond a (j + 1)) := by
  let Xp := deletionFirst a (j + 1)
  let Yp := eulerInsertionStep 0 (a + j + 2) (deletionFirst a j)
  let Zp := eulerInsertionStep 0 (a + j + 2) (deletionSecond a j)
  have hQinfo := deletionPolynomial_degree_nonneg a (j + 1)
  have hPpf := deletionFirst_pf_of_components a j hprev
  have hCpf := deletionSecond_pf_of_components a j hprev
  have hPinfo := deletionFirst_degree_pos a j
  have hCinfo := deletionSecond_degree_pos a j
  have hXpos : HasPosLeadingCoeff Xp := (deletionFirst_degree_pos a (j + 1)).2
  have hYstep := eulerInsertionStep_degree_pos (c := (0 : ℝ))
    (d := a + j + 2) (p := deletionFirst a j)
    (by rw [hPinfo.1]; lia) hPinfo.2
  have hZstep := eulerInsertionStep_degree_pos (c := (0 : ℝ))
    (d := a + j + 2) (p := deletionSecond a j)
    (by rw [hCinfo.1]; lia) hCinfo.2
  have hYpos : HasPosLeadingCoeff Yp := hYstep.2
  have hZpos : HasPosLeadingCoeff Zp := hZstep.2
  have hXrr : Xp ≠ 0 ∧ Xp.Splits := by
    refine ⟨hXpos.ne_zero, ?_⟩
    exact splits_eulerInsertionStep hQpf.hasNonnegCoeffs hQinfo.2.1
      (hQpf.ne_zero_and_splits hQinfo.2.1.ne_zero).2
      (by rw [hQinfo.1]; lia)
  have hYrr : Yp ≠ 0 ∧ Yp.Splits := by
    refine ⟨hYpos.ne_zero, ?_⟩
    exact splits_eulerInsertionStep hPpf.hasNonnegCoeffs hPinfo.2
      (hPpf.ne_zero_and_splits hPinfo.2.ne_zero).2
      (by rw [hPinfo.1]; lia)
  have hZrr : Zp ≠ 0 ∧ Zp.Splits := by
    refine ⟨hZpos.ne_zero, ?_⟩
    exact splits_eulerInsertionStep hCpf.hasNonnegCoeffs hCinfo.2
      (hCpf.ne_zero_and_splits hCinfo.2.ne_zero).2
      (by rw [hCinfo.1]; lia)
  have hYZ : Compatible Yp Zp := by
    exact hprev.map_eulerInsertionStep
      (deletionFirst_nonneg a j) (deletionSecond_nonneg a j)
      (by rw [hPinfo.1]; lia) (by rw [hCinfo.1]; lia)
  have hQ_C : StrictInterl (deletionPolynomial a (j + 1))
      (deletionSecond a j) := by
    exact strictInterl_eulerInsertionStep hQinfo.2.2 hQinfo.2.1
      (hQpf.ne_zero_and_splits hQinfo.2.1.ne_zero).2
      (by rw [hQinfo.1]; lia)
  have hXZ : Compatible Xp Zp := by
    exact compatible_eulerInsertionStep_one_zero_succ hQ_C
      (deletionSecond_nonneg a j) hQinfo.2.2 hCinfo.2 hQinfo.2.1
      (by rw [hQinfo.1, hCinfo.1])
      (by rw [hCinfo.1]; lia)
  have hXY : Compatible Xp Yp := by
    by_cases hj0 : j = 0
    · subst j
      simpa [Xp, Yp] using deletionFirst_one_compatible_first_zeroStep a
    · have hj : 1 ≤ j := by lia
      have hMtwo : a + j + 3 - 2 = a + j + 1 := by lia
      have hMone : a + j + 3 - 1 = a + j + 2 := by lia
      have hcompletion := deletionFirst_completion a j
      rcases neg_one_pow_eq_or ℝ (j + 1) with hsign | hsign
      · have hQeq : deletionPolynomial a (j + 1) = deletionFirst a j + 1 := by
          rw [hsign] at hcompletion
          simp only [map_one] at hcompletion
          rw [hcompletion]
          ring
        obtain ⟨w, hw⟩ :=
          crossedEulerCompletion_commonLeftInterleaver
            (D := j + 1) (M := a + j + 3)
            (by lia) (by lia) hPpf
            (by simpa [← hQeq] using hQpf) hPinfo.1
        apply Compatible.of_commonLeftInterleaver
          (h := w) (hf_pos := hXpos) (hg_pos := hYpos)
        · apply hw Xp
          simp only [List.mem_cons, List.mem_nil_iff, or_false]
          right; left
          change eulerInsertionStep 1 (a + (j + 1))
            (deletionPolynomial a (j + 1)) =
            eulerInsertionStep 1 (a + j + 3 - 2) (deletionFirst a j + 1)
          rw [hMtwo, hQeq]
          congr 1
        · apply hw Yp
          simp only [List.mem_cons, List.mem_nil_iff, or_false]
          right; right; left
          simp [Yp, hMone]
      · have hPeq : deletionFirst a j = deletionPolynomial a (j + 1) + 1 := by
          rw [hsign] at hcompletion
          simpa using hcompletion
        obtain ⟨w, hw⟩ :=
          crossedEulerCompletion_commonLeftInterleaver
            (D := j + 1) (M := a + j + 3)
            (by lia) (by lia) hQpf
            (by simpa [← hPeq] using hPpf) hQinfo.1
        apply Compatible.of_commonLeftInterleaver
          (h := w) (hf_pos := hXpos) (hg_pos := hYpos)
        · apply hw Xp
          simp only [List.mem_cons, List.mem_nil_iff, or_false]
          left
          dsimp only [Xp, deletionFirst]
          congr 1
        · apply hw Yp
          simp only [List.mem_cons, List.mem_nil_iff, or_false]
          right; right; right
          rw [← hPeq]
          dsimp only [Yp]
          congr 1
  have htriple : Compatible Xp (Yp + Zp) :=
    deletionCompatible_first_sum_of_three hXrr hYrr hZrr
      hXpos hYpos hZpos hXY hXZ hYZ
  have hsecond : deletionSecond a (j + 1) = Yp + Zp := by
    change eulerInsertionStep 0 (a + j + 2) (deletionPolynomial a (j + 2)) =
      eulerInsertionStep 0 (a + j + 2) (deletionFirst a j) +
        eulerInsertionStep 0 (a + j + 2) (deletionSecond a j)
    rw [← eulerInsertionStep_add, deletionFirst_add_second]
  rw [hsecond]
  exact htriple

/-- Every adjacent pair of summands in the deletion-family recurrence is
compatible. This is the induction behind paper `thm:largerFamily`. -/
theorem deletionComponents_compatible (a k : ℕ) :
    Compatible (deletionFirst a k) (deletionSecond a k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => exact deletionComponents_zero_compatible a
    | succ j =>
      have hprev : Compatible (deletionFirst a j) (deletionSecond a j) :=
        ih j (by lia)
      have hQpf : IsPFPolynomial (deletionPolynomial a (j + 1)) := by
        cases j with
        | zero => simpa using deletionPolynomial_one_pf a
        | succ i =>
          have hi : Compatible (deletionFirst a i) (deletionSecond a i) :=
            ih i (by lia)
          simpa [Nat.succ_eq_add_one] using
            deletionPolynomial_pf_of_components a i hi
      exact deletionComponents_next a j hprev hQpf

/-- The deletion-stable family of paper `thm:largerFamily` is PF, hence has
only real nonpositive roots. -/
theorem deletionPolynomial_isPF (a r : ℕ) :
    IsPFPolynomial (deletionPolynomial a r) := by
  cases r with
  | zero => simpa [deletionPolynomial] using (IsPFPolynomial.one :
      IsPFPolynomial (1 : ℝ[X]))
  | succ r =>
    cases r with
    | zero => simpa using deletionPolynomial_one_pf a
    | succ k =>
      simpa [Nat.succ_eq_add_one] using
        deletionPolynomial_pf_of_components a k
          (deletionComponents_compatible a k)

end RealRooted.EulerianCompendium
