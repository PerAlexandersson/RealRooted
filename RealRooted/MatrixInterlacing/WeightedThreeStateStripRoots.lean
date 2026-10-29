module

public import RealRooted.MatrixInterlacing.WeightedThreeStateStrip
public import RealRooted.MatrixInterlacing.WeightedThreeStateRows
import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges

/-!
# Roots of the weighted three-state half-height strip

This file continues the characteristic-root proof from RealRooted issue #2089.
It first establishes the exact coefficient support and degree of the normalized
rows `weightedStripRow`.  The proof uses the positive three-coordinate
recurrence from `RealRooted.MatrixInterlacing.WeightedThreeState`.  It also
packages the finite sign-change root-count criterion, proves two concrete
rows, and identifies the exact rescaling to the physical `(a,b,c,eta)` family.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The three recurrence coordinates have their expected positive coefficient
support on the half-height strip. -/
private theorem weightedThreeState_coeff_support {rho e : ℝ}
    (hrho : 0 ≤ rho) (he : e ≤ 1 / 2) :
    ∀ n : ℕ,
      HasNonnegCoeffs (weightedThreeState rho 0 1 e n).R ∧
      HasNonnegCoeffs (weightedThreeState rho 0 1 e n).P ∧
      HasNonnegCoeffs (weightedThreeState rho 0 1 e n).D ∧
      (∀ k ≤ n / 2, 0 < (weightedThreeState rho 0 1 e n).R.coeff k) ∧
      (∀ k ≤ n / 2, 0 < (weightedThreeState rho 0 1 e n).P.coeff k) ∧
      (weightedThreeState rho 0 1 e n).D.coeff 0 = 0 ∧
      (∀ k, 0 < k → k ≤ (n + 1) / 2 →
        0 < (weightedThreeState rho 0 1 e n).D.coeff k) ∧
      (∀ k > n / 2, (weightedThreeState rho 0 1 e n).R.coeff k = 0) ∧
      (∀ k > n / 2, (weightedThreeState rho 0 1 e n).P.coeff k = 0) ∧
      (∀ k > (n + 1) / 2, (weightedThreeState rho 0 1 e n).D.coeff k = 0) := by
  intro n
  induction n with
  | zero =>
      simp only [weightedThreeState]
      refine ⟨hasNonnegCoeffs_C (by linarith), hasNonnegCoeffs_one,
        hasNonnegCoeffs_zero, ?_, ?_, by simp, ?_, ?_, ?_, ?_⟩
      · intro k hk
        have hk0 : k = 0 := by lia
        subst k
        simp
        linarith
      · intro k hk
        have hk0 : k = 0 := by lia
        subst k
        simp
      · intro k hk hbound
        lia
      · intro k hk
        simp [coeff_C, coeff_one, show k ≠ 0 by lia]
      · intro k hk
        simp [coeff_one, show k ≠ 0 by lia]
      · intro k hk
        simp
  | succ n ih =>
      rcases ih with
        ⟨hRnn, hPnn, hDnn, hRpos, hPpos, hDzero, hDpos,
          hRzero, hPzero, hDhigh⟩
      simp only [weightedThreeState, weightedThreeStateStep, C_0, C_1,
        zero_mul, one_mul, add_zero]
      have hRnextnn : HasNonnegCoeffs
          ((weightedThreeState rho 0 1 e n).R +
            C rho * (weightedThreeState rho 0 1 e n).P +
            (weightedThreeState rho 0 1 e n).D) :=
        (hRnn.add ((hasNonnegCoeffs_C hrho).mul hPnn)).add
          hDnn
      have hPnextnn : HasNonnegCoeffs
          ((weightedThreeState rho 0 1 e n).P +
            (weightedThreeState rho 0 1 e n).D) := hPnn.add hDnn
      have hDnextnn : HasNonnegCoeffs
          (X * (weightedThreeState rho 0 1 e n).R +
            (weightedThreeState rho 0 1 e n).D) :=
        (hasNonnegCoeffs_X.mul hRnn).add hDnn
      refine ⟨hRnextnn, hPnextnn, hDnextnn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk
        simp only [coeff_add, coeff_C_mul]
        by_cases hkn : k ≤ n / 2
        · have hbase := hRpos k hkn
          have hmiddle := hPnn k
          have hdiff := hDnn k
          nlinarith [mul_nonneg hrho hmiddle]
        · have hkpos : 0 < k := by lia
          have hktop : k ≤ (n + 1) / 2 := by lia
          have hdiff := hDpos k hkpos hktop
          have hbase := hRnn k
          have hmiddle := hPnn k
          nlinarith [mul_nonneg hrho hmiddle]
      · intro k hk
        simp only [coeff_add]
        by_cases hkn : k ≤ n / 2
        · nlinarith [hPpos k hkn, hDnn k]
        · have hkpos : 0 < k := by lia
          have hktop : k ≤ (n + 1) / 2 := by lia
          nlinarith [hPnn k, hDpos k hkpos hktop]
      · simp [hDzero]
      · intro k hkpos hk
        rcases k with _ | k
        · simp at hkpos
        · simp only [coeff_add, coeff_X_mul]
          have hkR : k ≤ n / 2 := by lia
          have hmain := hRpos k hkR
          have hdiff := hDnn (k + 1)
          simp
          nlinarith
      · intro k hk
        simp only [coeff_add, coeff_C_mul]
        rw [hRzero k (by lia), hPzero k (by lia), hDhigh k (by lia)]
        ring
      · intro k hk
        simp only [coeff_add]
        rw [hPzero k (by lia), hDhigh k (by lia)]
        ring
      · intro k hk
        rcases k with _ | k
        · simp at hk
        · simp only [coeff_add, coeff_X_mul]
          rw [hRzero k (by lia), hDhigh (k + 1) (by lia)]
          simp

/-- Every normalized row in the half-height strip has nonnegative
coefficients. -/
theorem weightedStripRow_hasNonnegCoeffs {rho e : ℝ}
    (hrho : 0 ≤ rho) (he : e ≤ 1 / 2) (n : ℕ) :
    HasNonnegCoeffs (weightedStripRow rho e n) := by
  exact (weightedThreeState_coeff_support hrho he n).2.1

/-- The constant coefficient of every normalized row is one. -/
theorem weightedStripRow_coeff_zero (rho e : ℝ) (n : ℕ) :
    (weightedStripRow rho e n).coeff 0 = 1 := by
  simpa [weightedStripRow] using weightedThreeState_P_coeff_zero rho 0 1 e n

/-- The coefficients above `n / 2` vanish, while every coefficient through
`n / 2` is positive. -/
theorem weightedStripRow_coeff_support {rho e : ℝ}
    (hrho : 0 ≤ rho) (he : e ≤ 1 / 2) (n : ℕ) :
    (∀ k ≤ n / 2, 0 < (weightedStripRow rho e n).coeff k) ∧
      (∀ k > n / 2, (weightedStripRow rho e n).coeff k = 0) := by
  have h := weightedThreeState_coeff_support hrho he n
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

/-- The normalized row indexed by `n` has degree `n / 2`. -/
theorem weightedStripRow_natDegree {rho e : ℝ}
    (hrho : 0 ≤ rho) (he : e ≤ 1 / 2) (n : ℕ) :
    (weightedStripRow rho e n).natDegree = n / 2 := by
  rcases weightedStripRow_coeff_support hrho he n with ⟨hpos, hzero⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun k hk => hzero k hk)
    (hpos (n / 2) le_rfl).ne'

/-- Every normalized row in the half-height strip has positive leading
coefficient. -/
theorem weightedStripRow_hasPosLeadingCoeff {rho e : ℝ}
    (hrho : 0 ≤ rho) (he : e ≤ 1 / 2) (n : ℕ) :
    HasPosLeadingCoeff (weightedStripRow rho e n) := by
  rw [HasPosLeadingCoeff, leadingCoeff, weightedStripRow_natDegree hrho he n]
  exact (weightedStripRow_coeff_support hrho he n).1 (n / 2) le_rfl

/-- Three initial cases and a three-step recurrence prove a statement for all
natural indices. -/
private theorem nat_threeStepInduction_local {motive : ℕ → Prop}
    (zero : motive 0) (one : motive 1) (two : motive 2)
    (more : ∀ n, motive n → motive (n + 1) → motive (n + 2) → motive (n + 3)) :
    ∀ n, motive n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · exact zero
      rcases n with _ | n
      · exact one
      rcases n with _ | n
      · exact two
      exact more n (ih n (by lia)) (ih (n + 1) (by lia)) (ih (n + 2) (by lia))

/-- A three-state middle coordinate with total `X`-weight `A` is a normalized
strip row after the variable rescaling `X ↦ A X`. -/
theorem weightedThreeState_P_eq_strip_comp {A B E alpha d : ℝ}
    (hA : A ≠ 0) (hsum : alpha + d = A) (n : ℕ) :
    (weightedThreeState B alpha d E n).P =
      (weightedStripRow (B / A) (E / A) n).comp (C A * X) := by
  have hp := weightedThreeState_P_initial B alpha d E
  have hq := weightedStripRow_initial (B / A) (E / A)
  have hEA : (1 - E / A) * A = A - E := by
    field_simp [hA]
  have hBA : (B / A - 1) * A = B - A := by
    field_simp [hA]
  have hscaleE : C (1 - E / A) * (C A * X) = C (A - E) * X := by
    rw [← mul_assoc, ← C_mul, hEA]
  have hscaleB : C (B / A - 1) * (C A * X) = C (B - A) * X := by
    rw [← mul_assoc, ← C_mul, hBA]
  induction n using nat_threeStepInduction_local with
  | zero => simp [hp.1, hq.1]
  | one => simp [hp.2.1, hq.2.1]
  | two =>
      rw [hp.2.2, hq.2.2]
      simp only [add_comp, one_comp, mul_comp, C_comp, X_comp]
      rw [hsum, hscaleE]
  | more n hn hn1 hn2 =>
      rw [weightedThreeState_P_add_three, weightedStripRow_add_three]
      simp only [add_comp, sub_comp, mul_comp, C_comp, X_comp, one_comp,
        ofNat_comp]
      rw [hscaleB, hn, hn1, hn2, hsum]
      ring

/-- The physical `(a,b,c,eta)` row is the normalized strip row with
`rho=b/(ac)`, `e=eta/a`, variable scale `a/c²`, and row scale `cⁿ`. -/
theorem weightedThreeStateRow_eq_strip_comp {a b c eta : ℝ}
    (ha : a ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    weightedThreeStateRow a b c eta n =
      C (c ^ n) *
        (weightedStripRow (b / (a * c)) (eta / a) n).comp
          (C (a / c ^ 2) * X) := by
  have hrho : (b / c ^ 3) / (a / c ^ 2) = b / (a * c) := by
    field_simp [ha, hc]
  have he : (eta / c ^ 2) / (a / c ^ 2) = eta / a := by
    field_simp [ha, hc]
  rw [weightedThreeStateRow]
  rw [weightedThreeState_P_eq_strip_comp (A := a / c ^ 2)
    (hA := div_ne_zero ha (pow_ne_zero 2 hc))
    (hsum := by ring)]
  rw [hrho, he]

/-- Physical rows in the half-height strip have nonnegative coefficients. -/
theorem weightedThreeStateRow_hasNonnegCoeffs_halfHeight
    {a b c eta : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c)
    (heta : eta ≤ a / 2) (n : ℕ) :
    HasNonnegCoeffs (weightedThreeStateRow a b c eta n) := by
  have hrho : 0 ≤ b / (a * c) := div_nonneg hb (mul_nonneg ha.le hc.le)
  have he : eta / a ≤ 1 / 2 := by
    rw [div_le_iff₀ ha]
    nlinarith
  rw [weightedThreeStateRow_eq_strip_comp ha.ne' hc.ne' n]
  intro k
  rw [coeff_C_mul, comp_C_mul_X_coeff]
  exact mul_nonneg (pow_nonneg hc.le n)
    (mul_nonneg ((weightedStripRow_hasNonnegCoeffs hrho he n) k)
      (pow_nonneg (div_nonneg ha.le (sq_nonneg c)) k))

/-- Physical rows in the half-height strip have degree `n / 2`. -/
theorem weightedThreeStateRow_natDegree_halfHeight
    {a b c eta : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c)
    (heta : eta ≤ a / 2) (n : ℕ) :
    (weightedThreeStateRow a b c eta n).natDegree = n / 2 := by
  have hrho : 0 ≤ b / (a * c) := div_nonneg hb (mul_nonneg ha.le hc.le)
  have he : eta / a ≤ 1 / 2 := by
    rw [div_le_iff₀ ha]
    nlinarith
  rw [weightedThreeStateRow_eq_strip_comp ha.ne' hc.ne' n,
    natDegree_C_mul (pow_ne_zero n hc.ne'), Polynomial.natDegree_comp,
    weightedStripRow_natDegree hrho he n,
    natDegree_C_mul_X (a / c ^ 2) (div_ne_zero ha.ne' (pow_ne_zero 2 hc.ne'))]
  simp

/-- Every real root of a normalized half-height-strip row is strictly
negative. -/
theorem weightedStripRow_root_neg {rho e : ℝ}
    (hrho : 0 ≤ rho) (he : e ≤ 1 / 2) (n : ℕ) {r : ℝ}
    (hr : (weightedStripRow rho e n).IsRoot r) : r < 0 := by
  have hnonpos := roots_nonpos_of_hasNonnegCoeffs
    (weightedStripRow_hasNonnegCoeffs hrho he n) r
    ((mem_roots (weightedStripRow_hasPosLeadingCoeff hrho he n).ne_zero).mpr hr)
  apply lt_of_le_of_ne hnonpos
  intro hrzero
  subst r
  rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero,
    weightedStripRow_coeff_zero] at hr
  norm_num at hr

/-- A strict sign-change grid with one gap per expected root proves that a
normalized row splits with simple roots, all lying in the grid band.

This is the finite root-count criterion consumed by the continuous
first-passage construction in RealRooted issue #2089.
-/
theorem weightedStripRow_roots_of_sign_changes {rho e : ℝ}
    (hrho : 0 ≤ rho) (he : e ≤ 1 / 2) (n : ℕ)
    (x : Fin (n / 2 + 1) → ℝ) (hx : StrictMono x)
    (hsign : ∀ i : Fin (n / 2),
      (weightedStripRow rho e n).eval (x i.castSucc) *
        (weightedStripRow rho e n).eval (x i.succ) < 0) :
    (weightedStripRow rho e n).Splits ∧
      (weightedStripRow rho e n).roots.Nodup ∧
      ∀ z ∈ (weightedStripRow rho e n).roots,
        x 0 < z ∧ z < x (Fin.last (n / 2)) := by
  have h := Polynomial.splits_nodup_roots_of_strict_sign_changes
    (weightedStripRow_hasPosLeadingCoeff hrho he n).ne_zero
    (weightedStripRow_natDegree hrho he n).le x hx hsign
  exact h.2

/-- The fourth row at `(rho,e)=(1/4,1/2)` has two simple roots in `(-8,0)`. -/
theorem weightedStripRow_one_fourth_half_four_roots :
    (weightedStripRow (1 / 4) (1 / 2) 4).Splits ∧
      (weightedStripRow (1 / 4) (1 / 2) 4).roots.Nodup ∧
      ∀ z ∈ (weightedStripRow (1 / 4) (1 / 2) 4).roots,
        -8 < z ∧ z < 0 := by
  let x : Fin 3 → ℝ := ![-8, -1, 0]
  have hx : StrictMono x := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> norm_num [x]
  have hsign : ∀ i : Fin 2,
      (weightedStripRow (1 / 4) (1 / 2) 4).eval (x i.castSucc) *
        (weightedStripRow (1 / 4) (1 / 2) 4).eval (x i.succ) < 0 := by
    intro i
    fin_cases i <;>
      norm_num [x, weightedStripRow, weightedThreeState, weightedThreeStateStep]
  simpa [x] using weightedStripRow_roots_of_sign_changes
    (rho := (1 / 4 : ℝ)) (e := (1 / 2 : ℝ)) (n := 4)
    (by norm_num) (by norm_num) x hx hsign

/-- The fifth row at `(rho,e)=(1/4,1/2)` has two simple roots in `(-3,0)`. -/
theorem weightedStripRow_one_fourth_half_five_roots :
    (weightedStripRow (1 / 4) (1 / 2) 5).Splits ∧
      (weightedStripRow (1 / 4) (1 / 2) 5).roots.Nodup ∧
      ∀ z ∈ (weightedStripRow (1 / 4) (1 / 2) 5).roots,
        -3 < z ∧ z < 0 := by
  let x : Fin 3 → ℝ := ![-3, -1, 0]
  have hx : StrictMono x := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> norm_num [x]
  have hsign : ∀ i : Fin 2,
      (weightedStripRow (1 / 4) (1 / 2) 5).eval (x i.castSucc) *
        (weightedStripRow (1 / 4) (1 / 2) 5).eval (x i.succ) < 0 := by
    intro i
    fin_cases i <;>
      norm_num [x, weightedStripRow, weightedThreeState, weightedThreeStateStep]
  simpa [x] using weightedStripRow_roots_of_sign_changes
    (rho := (1 / 4 : ℝ)) (e := (1 / 2 : ℝ)) (n := 5)
    (by norm_num) (by norm_num) x hx hsign

end RealRooted
