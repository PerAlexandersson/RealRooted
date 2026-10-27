module

public import RealRooted.CoefficientDominance.Symmetric
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Sort
import RealRooted.CoefficientDominance.Symmetric.Polynomial
public import RealRooted.CoefficientDominance.Symmetric.Finite

/-!
# Local Newton defects and individual positive root parameters

This file proves the finite elementary-symmetric estimate behind local bounds
for the ordered parameters in a product `a₀ ∏ i, (1 + X / η i)`.  If
`λ i = (η i)⁻¹` is decreasing, `e k` is its `k`-th elementary symmetric sum,
and `L k = λ 0 * ... * λ (k - 1)`, then

`(1 - 2 * e (k - 1) * e (k + 1) / e k ^ 2) * e k ≤ L k ≤ e k`.

The ratio `τ k = L k / e k` therefore controls each individual parameter via
`η i / (e (i - 1) / e i) = τ (i - 1) / τ i`.  A quadratic refinement follows
from the collision probability of the normalized subset products.
-/

@[expose] public section

namespace RealRooted.NewtonDefectRoots

open Finset
open Filter
open CoefficientDominance.Symmetric

open scoped Asymptotics Topology

private theorem esym_nonneg (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) (n k : ℕ) :
    0 ≤ esym x n k := by
  rw [esym_eq_sum]
  exact sum_nonneg fun S _ ↦ prod_nonneg fun i _ ↦ hx i

private theorem esym_no_vars_succ (x : ℕ → ℝ) (k : ℕ) : esym x 0 (k + 1) = 0 := by
  rw [esym_eq_sum, powersetCard_eq_empty.mpr (by simp)]
  simp

private theorem esym_sq_sub_sq_esym_succ_le
    (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) (n k : ℕ) :
    esym x n (k + 1) ^ 2 - esym (fun i => x i ^ 2) n (k + 1) ≤
      2 * esym x n k * esym x n (k + 2) := by
  induction n generalizing k with
  | zero =>
      rw [esym_no_vars_succ x k, esym_no_vars_succ (fun i => x i ^ 2) k]
      have hleft := esym_nonneg x hx 0 k
      have hright := esym_nonneg x hx 0 (k + 2)
      nlinarith [mul_nonneg hleft hright]
  | succ n ih =>
      cases k with
      | zero =>
          have hmain := ih 0
          have hxn := hx n
          have he2 := esym_nonneg x hx n 2
          rw [esym_succ x n 0, esym_succ (fun i => x i ^ 2) n 0,
            esym_zero, esym_succ x n 1]
          simp only [esym_zero, mul_one]
          norm_num at hmain ⊢
          nlinarith
      | succ k =>
          have hhigh := ih (k + 1)
          have hlow := ih k
          have hxn := hx n
          have hcross : 0 ≤ x n * esym x n k * esym x n (k + 3) :=
            mul_nonneg (mul_nonneg hxn (esym_nonneg x hx n k))
              (esym_nonneg x hx n (k + 3))
          simp only [Nat.add_assoc] at hhigh hlow ⊢
          rw [esym_succ x n (k + 1), esym_succ (fun i => x i ^ 2) n (k + 1),
            esym_succ x n k, esym_succ x n (k + 2)]
          nlinarith

/-- The off-diagonal mass of the `k`-subset products is bounded by twice the
product of the adjacent elementary symmetric sums. -/
theorem esym_sq_sub_sq_esym_le (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) (n k : ℕ) :
    esym x n k ^ 2 - esym (fun i => x i ^ 2) n k ≤
      2 * esym x n (k - 1) * esym x n (k + 1) := by
  cases k with
  | zero =>
      rw [esym_zero, esym_zero]
      have hnext := esym_nonneg x hx n 1
      nlinarith
  | succ k =>
      simpa only [Nat.succ_sub_one, Nat.succ_eq_add_one] using
        esym_sq_sub_sq_esym_succ_le x hx n k

private theorem subset_prod_le_topProd
    (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) (hanti : Antitone x)
    {S : Finset ℕ} {k : ℕ} (hcard : S.card = k) :
    ∏ i ∈ S, x i ≤ topProd x k := by
  let e : Fin k ↪o ℕ := S.orderEmbOfFin hcard
  have hindex : ∀ i : Fin k, (i : ℕ) ≤ e i := by
    cases k with
    | zero => exact fun i => Fin.elim0 i
    | succ k =>
        intro i
        induction i using Fin.induction with
        | zero => exact Nat.zero_le _
        | succ i ih =>
            exact Nat.succ_le_of_lt (ih.trans_lt (e.strictMono i.castSucc_lt_succ))
  have hreindex : ∏ i ∈ S, x i = ∏ i : Fin k, x (e i) := by
    rw [← Finset.prod_coe_sort]
    symm
    exact Fintype.prod_equiv (S.orderIsoOfFin hcard).toEquiv _ _ fun _ => rfl
  rw [hreindex, topProd, ← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_le_prod₀ (fun i _ => hx (e i)) fun i _ => hanti (hindex i)

/-- The sum of the squared `k`-subset products is at most the largest subset
product times their sum. -/
theorem sq_esym_le_topProd_mul_esym
    (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) (hanti : Antitone x) (n k : ℕ) :
    esym (fun i => x i ^ 2) n k ≤ topProd x k * esym x n k := by
  rw [esym_eq_sum, esym_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun S hS => ?_
  rw [Finset.prod_pow]
  have hcard : S.card = k := (mem_powersetCard.mp hS).2
  have hprod_nonneg : 0 ≤ ∏ i ∈ S, x i := prod_nonneg fun i _ => hx i
  have hprod_le := subset_prod_le_topProd x hx hanti hcard
  nlinarith

private theorem sq_esym_le_topProd_sq_add_rest_sq
    (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) {n k : ℕ} (hkn : k ≤ n) :
    esym (fun i => x i ^ 2) n k ≤
      topProd x k ^ 2 + (esym x n k - topProd x k) ^ 2 := by
  let A := (range n).powersetCard k
  let T := range k
  let w : Finset ℕ → ℝ := fun S => ∏ i ∈ S, x i
  have hT : T ∈ A := by
    rw [mem_powersetCard]
    exact ⟨range_mono hkn, card_range k⟩
  have hsq : esym (fun i => x i ^ 2) n k =
      w T ^ 2 + ∑ S ∈ A.erase T, w S ^ 2 := by
    rw [esym_eq_sum]
    simpa only [A, T, w, Finset.prod_pow] using
      (A.add_sum_erase (fun S => w S ^ 2) hT).symm
  have hsum : esym x n k = w T + ∑ S ∈ A.erase T, w S := by
    rw [esym_eq_sum]
    simpa only [A, T, w] using (A.add_sum_erase w hT).symm
  have hwT : w T = topProd x k := by rfl
  have hrest := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := A.erase T) (f := w) (fun S _ => prod_nonneg fun i _ => hx i)
  rw [hsq, hsum, hwT]
  nlinarith

/-- Cross-multiplied linear lower bound for the leading-subset ratio. -/
theorem one_sub_two_mul_defect_mul_esym_le_topProd
    (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) (hanti : Antitone x) (n k : ℕ) :
    esym x n k ^ 2 - 2 * esym x n (k - 1) * esym x n (k + 1) ≤
      topProd x k * esym x n k := by
  have hoff := esym_sq_sub_sq_esym_le x hx n k
  have hdiag := sq_esym_le_topProd_mul_esym x hx hanti n k
  linarith

/-- The leading subset and the complementary subset mass satisfy the sharp
quadratic Newton-defect estimate. -/
theorem topProd_mul_esym_sub_topProd_le_adjacent_esym
    (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) {n k : ℕ} (hkn : k ≤ n) :
    topProd x k * (esym x n k - topProd x k) ≤
      esym x n (k - 1) * esym x n (k + 1) := by
  have hoff := esym_sq_sub_sq_esym_le x hx n k
  have hdiag := sq_esym_le_topProd_sq_add_rest_sq x hx hkn
  nlinarith

/-- The leading-subset mass as a fraction of the corresponding elementary
symmetric sum. -/
noncomputable def leadingRatio (x : ℕ → ℝ) (n k : ℕ) : ℝ :=
  topProd x k / esym x n k

/-- The local Newton defect, extended by zero at indices `0` and `n`. -/
noncomputable def localDefect (x : ℕ → ℝ) (n k : ℕ) : ℝ :=
  if k = 0 ∨ n ≤ k then 0
  else esym x n (k - 1) * esym x n (k + 1) / esym x n k ^ 2

/-- The upper branch of the quadratic equation `c * (1 - c) = u`. -/
noncomputable def defectConstant (u : ℝ) : ℝ :=
  (1 + Real.sqrt (1 - 4 * u)) / 2

private theorem esym_self (x : ℕ → ℝ) (n : ℕ) : esym x n n = topProd x n := by
  rw [esym_eq_sum]
  have hpower : (range n).powersetCard n = {range n} := by
    simpa only [card_range] using powersetCard_self (range n)
  rw [hpower]
  simp only [sum_singleton, topProd]

/-- The leading-subset ratio lies between the local linear Newton bound and
one, including the endpoint convention that the defect is zero. -/
theorem leadingRatio_mem_linear_box
    (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hanti : Antitone x)
    {n k : ℕ} (hkn : k ≤ n) :
    1 - 2 * localDefect x n k ≤ leadingRatio x n k ∧
      leadingRatio x n k ≤ 1 := by
  have hepos : 0 < esym x n k := esym_pos hpos hkn
  have htop := topProd_le_esym (x := x) (fun i => (hpos i).le) hkn
  constructor
  · by_cases hk0 : k = 0
    · subst k
      norm_num [localDefect, leadingRatio, topProd, esym_zero]
    · by_cases hnk : n ≤ k
      · have hkn' : k = n := Nat.le_antisymm hkn hnk
        subst k
        rw [localDefect, ite_eq_left (Or.inr le_rfl), mul_zero, sub_zero,
          leadingRatio, esym_self, div_self (ne_of_gt (topProd_pos hpos n))]
      · rw [localDefect, ite_eq_right (not_or_intro hk0 hnk), leadingRatio]
        have hcross := one_sub_two_mul_defect_mul_esym_le_topProd
          x (fun i => (hpos i).le) hanti n k
        calc
          1 - 2 *
              (esym x n (k - 1) * esym x n (k + 1) / esym x n k ^ 2) =
              (esym x n k ^ 2 -
                2 * esym x n (k - 1) * esym x n (k + 1)) /
                esym x n k ^ 2 := by field_simp
          _ ≤ (topProd x k * esym x n k) / esym x n k ^ 2 :=
            (div_le_div_iff_of_pos_right (sq_pos_of_pos hepos)).2 hcross
          _ = topProd x k / esym x n k := by field_simp
  · exact (div_le_one hepos).2 htop

/-- Under a quarter-defect hypothesis, the quadratic constant bounds the
leading-subset ratio from below. -/
theorem defectConstant_le_leadingRatio
    (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hanti : Antitone x)
    {n k : ℕ} (hkn : k ≤ n) (hquarter : localDefect x n k ≤ 1 / 4) :
    defectConstant (localDefect x n k) ≤ leadingRatio x n k := by
  by_cases hk0 : k = 0
  · subst k
    norm_num [localDefect, leadingRatio, topProd, esym_zero, defectConstant]
  · by_cases hnk : n ≤ k
    · have hkn' : k = n := Nat.le_antisymm hkn hnk
      subst k
      rw [localDefect, ite_eq_left (Or.inr le_rfl), leadingRatio, esym_self,
        div_self (ne_of_gt (topProd_pos hpos n)), defectConstant]
      norm_num
    · have hbox := leadingRatio_mem_linear_box x hpos hanti hkn
      have hepos : 0 < esym x n k := esym_pos hpos hkn
      have hquad_cross := topProd_mul_esym_sub_topProd_le_adjacent_esym
        x (fun i => (hpos i).le) hkn
      have hquad : leadingRatio x n k * (1 - leadingRatio x n k) ≤
          localDefect x n k := by
        rw [localDefect, ite_eq_right (not_or_intro hk0 hnk), leadingRatio]
        calc
          (topProd x k / esym x n k) * (1 - topProd x k / esym x n k) =
              (topProd x k * (esym x n k - topProd x k)) /
                esym x n k ^ 2 := by field_simp
          _ ≤ (esym x n (k - 1) * esym x n (k + 1)) / esym x n k ^ 2 :=
            (div_le_div_iff_of_pos_right (sq_pos_of_pos hepos)).2 hquad_cross
      have hhalf : 1 / 2 ≤ leadingRatio x n k := by
        nlinarith [hbox.1]
      have hsqrt : Real.sqrt (1 - 4 * localDefect x n k) ≤
          2 * leadingRatio x n k - 1 := by
        apply (Real.sqrt_le_left (by linarith)).2
        nlinarith
      rw [defectConstant]
      linarith

/-- The coefficient-ratio scale associated with the `(i + 1)`-st parameter. -/
noncomputable def coefficientRatio (x : ℕ → ℝ) (n i : ℕ) : ℝ :=
  esym x n i / esym x n (i + 1)

/-- The positive factor parameter corresponding to a reciprocal variable. -/
noncomputable def rootParameter (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  (x i)⁻¹

private theorem rootParameter_eq_coefficientRatio_mul_leadingRatio
    (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) {n i : ℕ} (hi : i < n) :
    rootParameter x i = coefficientRatio x n i *
      (leadingRatio x n i / leadingRatio x n (i + 1)) := by
  have hei : esym x n i ≠ 0 := ne_of_gt (esym_pos hpos hi.le)
  have hei1 : esym x n (i + 1) ≠ 0 := ne_of_gt (esym_pos hpos hi)
  have hpi : topProd x i ≠ 0 := ne_of_gt (topProd_pos hpos i)
  have hxi : x i ≠ 0 := ne_of_gt (hpos i)
  have hprod : topProd x (i + 1) = topProd x i * x i := by
    simp only [topProd, prod_range_succ]
  simp only [rootParameter, coefficientRatio, leadingRatio, hprod]
  field_simp

private theorem coefficientRatio_mul_le_rootParameter_of_le_leadingRatio
    (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hanti : Antitone x)
    {n i : ℕ} (hi : i < n) (c : ℝ) (hc : c ≤ leadingRatio x n i) :
    c * coefficientRatio x n i ≤ rootParameter x i := by
  rw [rootParameter_eq_coefficientRatio_mul_leadingRatio x hpos hi]
  have htiPos : 0 < leadingRatio x n i :=
    div_pos (topProd_pos hpos i) (esym_pos hpos hi.le)
  have hti1Pos : 0 < leadingRatio x n (i + 1) :=
    div_pos (topProd_pos hpos (i + 1)) (esym_pos hpos hi)
  have hratio : c ≤ leadingRatio x n i / leadingRatio x n (i + 1) := hc.trans (by
    apply (le_div_iff₀ hti1Pos).2
    nlinarith [mul_nonneg htiPos.le
      (sub_nonneg.mpr (leadingRatio_mem_linear_box x hpos hanti hi).2)])
  calc
    c * coefficientRatio x n i = coefficientRatio x n i * c := mul_comm _ _
    _ ≤ coefficientRatio x n i *
        (leadingRatio x n i / leadingRatio x n (i + 1)) :=
      mul_le_mul_of_nonneg_left hratio
        (div_pos (esym_pos hpos hi.le) (esym_pos hpos hi)).le

private theorem rootParameter_le_coefficientRatio_div_of_le_leadingRatio
    (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hanti : Antitone x)
    {n i : ℕ} (hi : i < n) (c : ℝ) (hcPos : 0 < c)
    (hc : c ≤ leadingRatio x n (i + 1)) :
    rootParameter x i ≤ coefficientRatio x n i / c := by
  rw [rootParameter_eq_coefficientRatio_mul_leadingRatio x hpos hi]
  have hti1Pos : 0 < leadingRatio x n (i + 1) :=
    div_pos (topProd_pos hpos (i + 1)) (esym_pos hpos hi)
  have hratio : leadingRatio x n i / leadingRatio x n (i + 1) ≤ 1 / c := by
    apply (div_le_div_iff₀ hti1Pos hcPos).2
    nlinarith [mul_le_mul_of_nonneg_right
      (leadingRatio_mem_linear_box x hpos hanti hi.le).2 hcPos.le]
  calc
    coefficientRatio x n i *
        (leadingRatio x n i / leadingRatio x n (i + 1)) ≤
        coefficientRatio x n i * (1 / c) :=
      mul_le_mul_of_nonneg_left hratio
        (div_pos (esym_pos hpos hi.le) (esym_pos hpos hi)).le
    _ = coefficientRatio x n i / c := by ring

/-- The two-sided linear local-defect box for the `(i + 1)`-st ordered
positive factor parameter.  The upper estimate needs the displayed positive
denominator. -/
theorem rootParameter_mem_linear_box
    (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hanti : Antitone x)
    {n i : ℕ} (hi : i < n)
    (hright : 0 < 1 - 2 * localDefect x n (i + 1)) :
    (1 - 2 * localDefect x n i) * coefficientRatio x n i ≤
        rootParameter x i ∧
      rootParameter x i ≤ coefficientRatio x n i /
        (1 - 2 * localDefect x n (i + 1)) := by
  exact ⟨coefficientRatio_mul_le_rootParameter_of_le_leadingRatio
      x hpos hanti hi _ (leadingRatio_mem_linear_box x hpos hanti hi.le).1,
    rootParameter_le_coefficientRatio_div_of_le_leadingRatio
      x hpos hanti hi _ hright (leadingRatio_mem_linear_box x hpos hanti hi).1⟩

private theorem defectConstant_pos (u : ℝ) : 0 < defectConstant u := by
  rw [defectConstant]
  positivity

private theorem defectConstant_mul_coefficientRatio_le_rootParameter
    (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hanti : Antitone x)
    {n i : ℕ} (hi : i < n) (hquarter : localDefect x n i ≤ 1 / 4) :
    defectConstant (localDefect x n i) * coefficientRatio x n i ≤
      rootParameter x i := by
  exact coefficientRatio_mul_le_rootParameter_of_le_leadingRatio
    x hpos hanti hi _
      (defectConstant_le_leadingRatio x hpos hanti hi.le hquarter)

private theorem rootParameter_le_coefficientRatio_div_defectConstant
    (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hanti : Antitone x)
    {n i : ℕ} (hi : i < n) (hquarter : localDefect x n (i + 1) ≤ 1 / 4) :
    rootParameter x i ≤ coefficientRatio x n i /
      defectConstant (localDefect x n (i + 1)) := by
  exact rootParameter_le_coefficientRatio_div_of_le_leadingRatio
    x hpos hanti hi _ (defectConstant_pos _)
      (defectConstant_le_leadingRatio x hpos hanti hi hquarter)

/-- The two-sided `C(δ)` refinement for the `(i + 1)`-st ordered positive
factor parameter. -/
theorem rootParameter_mem_quadratic_box
    (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hanti : Antitone x)
    {n i : ℕ} (hi : i < n)
    (hleftQuarter : localDefect x n i ≤ 1 / 4)
    (hrightQuarter : localDefect x n (i + 1) ≤ 1 / 4) :
    defectConstant (localDefect x n i) * coefficientRatio x n i ≤
        rootParameter x i ∧
      rootParameter x i ≤ coefficientRatio x n i /
        defectConstant (localDefect x n (i + 1)) := by
  exact ⟨defectConstant_mul_coefficientRatio_le_rootParameter
      x hpos hanti hi hleftQuarter,
    rootParameter_le_coefficientRatio_div_defectConstant
      x hpos hanti hi hrightQuarter⟩

/-- The quadratic constant satisfies its defining equation on the real branch
where the defect is at most `1 / 4`. -/
theorem defectConstant_mul_one_sub (u : ℝ) (hu : u ≤ 1 / 4) :
    defectConstant u * (1 - defectConstant u) = u := by
  have hrad : 0 ≤ 1 - 4 * u := by linarith
  have hsqrt := Real.sq_sqrt hrad
  rw [defectConstant]
  nlinarith

private theorem localDefect_eq_coefficientRatio_div
    (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) {n i : ℕ} (hi : i + 1 < n) :
    localDefect x n (i + 1) =
      coefficientRatio x n i / coefficientRatio x n (i + 1) := by
  have hei : esym x n i ≠ 0 := ne_of_gt (esym_pos hpos (by lia))
  have hei1 : esym x n (i + 1) ≠ 0 := ne_of_gt (esym_pos hpos hi.le)
  have hei2 : esym x n (i + 2) ≠ 0 := ne_of_gt (esym_pos hpos hi)
  rw [localDefect, ite_eq_right]
  · simp only [coefficientRatio, Nat.add_sub_cancel]
    field_simp
  · exact not_or_intro (by lia) (Nat.not_le_of_lt hi)

/-- Adjacent ordered factor parameters are separated by the local quadratic
Newton defect. -/
theorem rootParameter_div_succ_le
    (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hanti : Antitone x)
    {n i : ℕ} (hi : i + 1 < n)
    (hquarter : localDefect x n (i + 1) ≤ 1 / 4) :
    rootParameter x i / rootParameter x (i + 1) ≤
      (1 - defectConstant (localDefect x n (i + 1))) /
        defectConstant (localDefect x n (i + 1)) := by
  let d := localDefect x n (i + 1)
  let c := defectConstant d
  have hc : 0 < c := defectConstant_pos d
  have hd : 0 ≤ d := by
    dsimp only [d]
    rw [localDefect, ite_eq_right]
    · exact div_nonneg
        (mul_nonneg (esym_nonneg x (fun j => (hpos j).le) n (i + 1 - 1))
          (esym_nonneg x (fun j => (hpos j).le) n (i + 1 + 1)))
        (sq_nonneg _)
    · exact not_or_intro (by lia) (Nat.not_le_of_lt hi)
  have hceq : c * (1 - c) = d := defectConstant_mul_one_sub d hquarter
  have hcle : 0 ≤ 1 - c := by nlinarith
  have hrho : 0 < coefficientRatio x n (i + 1) :=
    div_pos (esym_pos hpos hi.le) (esym_pos hpos hi)
  have hdRatio := localDefect_eq_coefficientRatio_div x hpos hi
  have hscale : coefficientRatio x n i / c =
      (1 - c) * coefficientRatio x n (i + 1) := by
    apply (div_eq_iff (ne_of_gt hc)).2
    calc
      coefficientRatio x n i =
          c * (1 - c) * coefficientRatio x n (i + 1) :=
        ((eq_div_iff hrho.ne').mp
          (hceq.trans (by simpa only [d] using hdRatio))).symm
      _ = (1 - c) * coefficientRatio x n (i + 1) * c := by ring
  have hu := rootParameter_le_coefficientRatio_div_defectConstant
    x hpos hanti (Nat.lt_trans (Nat.lt_succ_self i) hi) hquarter
  have hl := defectConstant_mul_coefficientRatio_le_rootParameter
    x hpos hanti hi hquarter
  have hrootPos : 0 < rootParameter x (i + 1) := inv_pos.mpr (hpos (i + 1))
  apply (div_le_div_iff₀ hrootPos hc).2
  have hu' : rootParameter x i ≤
      (1 - c) * coefficientRatio x n (i + 1) := by
    simpa only [c, d, hscale] using hu
  nlinarith [mul_le_mul_of_nonneg_right hu' hc.le,
    mul_le_mul_of_nonneg_left (by simpa only [c, d] using hl) hcle]

open Polynomial

/-- A polynomial presented by its positive constant term and ordered positive
reciprocal factor parameters. -/
noncomputable def factorPolynomial (a₀ : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  C a₀ * ∏ j ∈ range n, (1 + C (x j) * X)

/-- Coefficients of the positive reciprocal-factor presentation. -/
theorem coeff_factorPolynomial (a₀ : ℝ) (x : ℕ → ℝ) (n k : ℕ) :
    (factorPolynomial a₀ x n).coeff k = a₀ * esym x n k := by
  rw [factorPolynomial, coeff_C_mul, coeff_prod_one_add]

/-- Coefficient ratios of a polynomial.  Index `i` corresponds to the
one-based ratio `ρ_(i+1) = a_i / a_(i+1)`. -/
noncomputable def polynomialCoefficientRatio (p : ℝ[X]) (i : ℕ) : ℝ :=
  p.coeff i / p.coeff (i + 1)

/-- Endpoint-aware Newton defects expressed directly in polynomial
coefficients. -/
noncomputable def polynomialLocalDefect (p : ℝ[X]) (n k : ℕ) : ℝ :=
  if k = 0 ∨ n ≤ k then 0
  else p.coeff (k - 1) * p.coeff (k + 1) / p.coeff k ^ 2

private theorem polynomialCoefficientRatio_factorPolynomial
    (a₀ : ℝ) (ha₀ : a₀ ≠ 0) (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i)
    {n i : ℕ} (hi : i < n) :
    polynomialCoefficientRatio (factorPolynomial a₀ x n) i =
      coefficientRatio x n i := by
  have hei : esym x n i ≠ 0 := ne_of_gt (esym_pos hpos hi.le)
  have hei1 : esym x n (i + 1) ≠ 0 := ne_of_gt (esym_pos hpos hi)
  rw [polynomialCoefficientRatio, coeff_factorPolynomial,
    coeff_factorPolynomial, coefficientRatio]
  field_simp

private theorem polynomialLocalDefect_factorPolynomial
    (a₀ : ℝ) (ha₀ : a₀ ≠ 0) (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i)
    (n k : ℕ) :
    polynomialLocalDefect (factorPolynomial a₀ x n) n k =
      localDefect x n k := by
  by_cases hend : k = 0 ∨ n ≤ k
  · rw [polynomialLocalDefect, ite_eq_left hend, localDefect, ite_eq_left hend]
  · have hklt : k < n := Nat.lt_of_not_ge (not_or.mp hend).2
    have hek : esym x n k ≠ 0 := ne_of_gt (esym_pos hpos hklt.le)
    rw [polynomialLocalDefect, ite_eq_right hend, localDefect, ite_eq_right hend,
      coeff_factorPolynomial, coeff_factorPolynomial, coeff_factorPolynomial]
    field_simp

/-- The displayed parameter is a root magnitude of its factor polynomial. -/
theorem factorPolynomial_isRoot_neg_rootParameter
    (a₀ : ℝ) (x : ℕ → ℝ) {n i : ℕ} (hi : i < n) (hxi : x i ≠ 0) :
    (factorPolynomial a₀ x n).IsRoot (-(rootParameter x i)) := by
  rw [Polynomial.IsRoot.def, factorPolynomial, eval_mul, eval_C, eval_prod]
  apply mul_eq_zero_of_right a₀
  apply Finset.prod_eq_zero (mem_range.mpr hi)
  simp only [eval_add, eval_one, eval_mul, eval_C, eval_X, rootParameter]
  field_simp
  norm_num

/-- Reciprocal factor parameters are weakly increasing when the reciprocal
variables are positive and weakly decreasing. -/
theorem rootParameter_mono
    (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hanti : Antitone x) :
    Monotone (rootParameter x) := by
  intro i j hij
  rw [rootParameter, rootParameter]
  exact (inv_le_inv₀ (hpos i) (hpos j)).2 (hanti hij)

/-- Polynomial-coefficient form of the two-sided linear local-defect box. -/
theorem factorPolynomial_rootParameter_mem_linear_box
    (a₀ : ℝ) (ha₀ : 0 < a₀) (x : ℕ → ℝ)
    (hpos : ∀ i, 0 < x i) (hanti : Antitone x)
    {n i : ℕ} (hi : i < n)
    (hright : 0 < 1 - 2 * polynomialLocalDefect
      (factorPolynomial a₀ x n) n (i + 1)) :
    (1 - 2 * polynomialLocalDefect (factorPolynomial a₀ x n) n i) *
        polynomialCoefficientRatio (factorPolynomial a₀ x n) i ≤
        rootParameter x i ∧
      rootParameter x i ≤
        polynomialCoefficientRatio (factorPolynomial a₀ x n) i /
          (1 - 2 * polynomialLocalDefect
            (factorPolynomial a₀ x n) n (i + 1)) := by
  rw [polynomialLocalDefect_factorPolynomial a₀ ha₀.ne' x hpos n (i + 1)] at hright
  simpa only [polynomialLocalDefect_factorPolynomial a₀ ha₀.ne' x hpos,
    polynomialCoefficientRatio_factorPolynomial a₀ ha₀.ne' x hpos hi] using
    rootParameter_mem_linear_box x hpos hanti hi hright

/-- Polynomial-coefficient form of the two-sided quadratic `C(δ)` box. -/
theorem factorPolynomial_rootParameter_mem_quadratic_box
    (a₀ : ℝ) (ha₀ : 0 < a₀) (x : ℕ → ℝ)
    (hpos : ∀ i, 0 < x i) (hanti : Antitone x)
    {n i : ℕ} (hi : i < n)
    (hleftQuarter : polynomialLocalDefect (factorPolynomial a₀ x n) n i ≤ 1 / 4)
    (hrightQuarter : polynomialLocalDefect
      (factorPolynomial a₀ x n) n (i + 1) ≤ 1 / 4) :
    defectConstant (polynomialLocalDefect (factorPolynomial a₀ x n) n i) *
        polynomialCoefficientRatio (factorPolynomial a₀ x n) i ≤
        rootParameter x i ∧
      rootParameter x i ≤
        polynomialCoefficientRatio (factorPolynomial a₀ x n) i /
          defectConstant (polynomialLocalDefect
            (factorPolynomial a₀ x n) n (i + 1)) := by
  rw [polynomialLocalDefect_factorPolynomial a₀ ha₀.ne' x hpos n
    i] at hleftQuarter
  rw [polynomialLocalDefect_factorPolynomial a₀ ha₀.ne' x hpos n
    (i + 1)] at hrightQuarter
  simpa only [polynomialLocalDefect_factorPolynomial a₀ ha₀.ne' x hpos,
    polynomialCoefficientRatio_factorPolynomial a₀ ha₀.ne' x hpos hi] using
    rootParameter_mem_quadratic_box x hpos hanti hi hleftQuarter hrightQuarter

/-- Polynomial-coefficient form of the adjacent-parameter separation bound. -/
theorem factorPolynomial_rootParameter_div_succ_le
    (a₀ : ℝ) (ha₀ : 0 < a₀) (x : ℕ → ℝ)
    (hpos : ∀ i, 0 < x i) (hanti : Antitone x)
    {n i : ℕ} (hi : i + 1 < n)
    (hquarter : polynomialLocalDefect
      (factorPolynomial a₀ x n) n (i + 1) ≤ 1 / 4) :
    rootParameter x i / rootParameter x (i + 1) ≤
      (1 - defectConstant (polynomialLocalDefect
        (factorPolynomial a₀ x n) n (i + 1))) /
        defectConstant (polynomialLocalDefect
          (factorPolynomial a₀ x n) n (i + 1)) := by
  rw [polynomialLocalDefect_factorPolynomial a₀ ha₀.ne' x hpos n (i + 1)] at hquarter
  simpa only [polynomialLocalDefect_factorPolynomial a₀ ha₀.ne' x hpos] using
    rootParameter_div_succ_le x hpos hanti hi hquarter

/-- If a fixed local defect tends to zero, then its leading-subset ratio tends
to one, uniformly in the ambient degree. -/
theorem leadingRatio_tendsto_one
    {α : Type*} {l : Filter α} (x : α → ℕ → ℝ) (n : α → ℕ) (k : ℕ)
    (hpos : ∀ a i, 0 < x a i) (hanti : ∀ a, Antitone (x a))
    (hkn : ∀ᶠ a in l, k ≤ n a)
    (hdefect : Filter.Tendsto (fun a => localDefect (x a) (n a) k) l (𝓝 0)) :
    Filter.Tendsto (fun a => leadingRatio (x a) (n a) k) l (𝓝 1) := by
  have hlower : Filter.Tendsto
      (fun a => 1 - 2 * localDefect (x a) (n a) k) l (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hdefect)
  apply hlower.squeeze' tendsto_const_nhds
  · filter_upwards [hkn] with a ha
    exact (leadingRatio_mem_linear_box (x a) (hpos a) (hanti a) ha).1
  · filter_upwards [hkn] with a ha
    exact (leadingRatio_mem_linear_box (x a) (hpos a) (hanti a) ha).2

/-- Sequence corollary: vanishing defects at the two adjacent coefficient
indices make the fixed ordered factor parameter asymptotic to its coefficient
ratio, without any bound on the growing degrees. -/
theorem rootParameter_isEquivalent_coefficientRatio
    {α : Type*} {l : Filter α} (x : α → ℕ → ℝ) (n : α → ℕ) (i : ℕ)
    (hpos : ∀ a j, 0 < x a j) (hanti : ∀ a, Antitone (x a))
    (hi : ∀ᶠ a in l, i < n a)
    (hleft : Filter.Tendsto (fun a => localDefect (x a) (n a) i) l (𝓝 0))
    (hright : Filter.Tendsto
      (fun a => localDefect (x a) (n a) (i + 1)) l (𝓝 0)) :
    (fun a => rootParameter (x a) i) ~[l]
      (fun a => coefficientRatio (x a) (n a) i) := by
  have hile : ∀ᶠ a in l, i ≤ n a := hi.mono fun _ h => h.le
  have hi1le : ∀ᶠ a in l, i + 1 ≤ n a := hi.mono fun _ h => h
  have hti := leadingRatio_tendsto_one x n i hpos hanti hile hleft
  have hti1 := leadingRatio_tendsto_one x n (i + 1) hpos hanti hi1le hright
  have hquot : Filter.Tendsto
      ((fun a => leadingRatio (x a) (n a) i) /
        fun a => leadingRatio (x a) (n a) (i + 1)) l (𝓝 1) := by
    simpa only [div_one] using hti.div hti1 (by norm_num)
  apply Asymptotics.isEquivalent_of_tendsto_one
  apply hquot.congr'
  filter_upwards [hi] with a ha
  have hrho : coefficientRatio (x a) (n a) i ≠ 0 := ne_of_gt
    (div_pos (esym_pos (hpos a) ha.le) (esym_pos (hpos a) ha))
  simp only [Pi.div_apply]
  rw [rootParameter_eq_coefficientRatio_mul_leadingRatio (x a) (hpos a) ha]
  field_simp

/-- Polynomial-coefficient sequence corollary for factorized PF polynomials:
vanishing adjacent Newton defects imply that the fixed ordered root parameter
is asymptotic to the corresponding consecutive-coefficient ratio. -/
theorem factorPolynomial_rootParameter_isEquivalent_coefficientRatio
    {α : Type*} {l : Filter α} (a₀ : α → ℝ) (x : α → ℕ → ℝ)
    (n : α → ℕ) (i : ℕ) (ha₀ : ∀ a, 0 < a₀ a)
    (hpos : ∀ a j, 0 < x a j) (hanti : ∀ a, Antitone (x a))
    (hi : ∀ᶠ a in l, i < n a)
    (hleft : Filter.Tendsto
      (fun a => polynomialLocalDefect (factorPolynomial (a₀ a) (x a) (n a)) (n a) i)
      l (𝓝 0))
    (hright : Filter.Tendsto
      (fun a => polynomialLocalDefect
        (factorPolynomial (a₀ a) (x a) (n a)) (n a) (i + 1)) l (𝓝 0)) :
    (fun a => rootParameter (x a) i) ~[l]
      (fun a => polynomialCoefficientRatio
        (factorPolynomial (a₀ a) (x a) (n a)) i) := by
  have hleft' : Filter.Tendsto (fun a => localDefect (x a) (n a) i) l (𝓝 0) :=
    hleft.congr' <| Eventually.of_forall fun a =>
      polynomialLocalDefect_factorPolynomial
        (a₀ a) (ha₀ a).ne' (x a) (hpos a) (n a) i
  have hright' : Filter.Tendsto
      (fun a => localDefect (x a) (n a) (i + 1)) l (𝓝 0) :=
    hright.congr' <| Eventually.of_forall fun a =>
      polynomialLocalDefect_factorPolynomial
        (a₀ a) (ha₀ a).ne' (x a) (hpos a) (n a) (i + 1)
  have hresult := rootParameter_isEquivalent_coefficientRatio
    x n i hpos hanti hi hleft' hright'
  apply hresult.congr_right
  filter_upwards [hi] with a hai
  exact (polynomialCoefficientRatio_factorPolynomial
    (a₀ a) (ha₀ a).ne' (x a) (hpos a) hai).symm

/-! ## Regression examples -/

example : (factorPolynomial 1 (fun _ => (1 : ℝ)) 2).IsRoot (-1) := by
  simpa [rootParameter] using factorPolynomial_isRoot_neg_rootParameter
    (a₀ := 1) (x := fun _ => (1 : ℝ)) (n := 2) (i := 0)
    (by norm_num) (by norm_num)

private def separatedReciprocal (i : ℕ) : ℝ :=
  if i = 0 then 100 else if i = 1 then 10 else 1

example :
    (factorPolynomial 1 separatedReciprocal 3).IsRoot (-(1 / 100)) ∧
      (factorPolynomial 1 separatedReciprocal 3).IsRoot (-(1 / 10)) ∧
      (factorPolynomial 1 separatedReciprocal 3).IsRoot (-1) := by
  have h0 := factorPolynomial_isRoot_neg_rootParameter
    (a₀ := 1) (x := separatedReciprocal) (n := 3) (i := 0) (by norm_num)
    (by norm_num [separatedReciprocal])
  have h1 := factorPolynomial_isRoot_neg_rootParameter
    (a₀ := 1) (x := separatedReciprocal) (n := 3) (i := 1) (by norm_num)
    (by norm_num [separatedReciprocal])
  have h2 := factorPolynomial_isRoot_neg_rootParameter
    (a₀ := 1) (x := separatedReciprocal) (n := 3) (i := 2) (by norm_num)
    (by norm_num [separatedReciprocal])
  norm_num [rootParameter, separatedReciprocal] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

end RealRooted.NewtonDefectRoots
