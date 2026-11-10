module

public import RealRooted.RootLocation.Basic
public import RealRooted.SimpleRoots
public import RealRooted.Basic.ProperPosition

import RealRooted.IntervalDifferential.LinearInsertion
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Binomial perturbations of a centered Euler-operator orbit

We study the operator
`f ↦ X f + α (X² - 1) f'` and its orbit starting at `1`.  The inverse
Bernstein estimate used later is deliberately kept as an explicit hypothesis;
see RealRooted issue #2513.
-/

@[expose] public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- The centered Euler step `f ↦ X f + α (X² - 1) f'`. -/
def centeredEulerStep (α : ℝ) (f : ℝ[X]) : ℝ[X] :=
  X * f + C α * (X ^ 2 - 1) * f.derivative

/-- The orbit of the centered Euler step starting from the constant polynomial `1`. -/
def centeredEulerOrbit (α : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => centeredEulerStep α (centeredEulerOrbit α n)

@[simp] theorem centeredEulerOrbit_zero (α : ℝ) : centeredEulerOrbit α 0 = 1 := rfl

@[simp] theorem centeredEulerOrbit_succ (α : ℝ) (n : ℕ) :
    centeredEulerOrbit α (n + 1) = centeredEulerStep α (centeredEulerOrbit α n) := rfl

@[simp] theorem centeredEulerStep_eval (α x : ℝ) (f : ℝ[X]) :
    (centeredEulerStep α f).eval x =
      x * f.eval x + α * (x ^ 2 - 1) * f.derivative.eval x := by
  simp [centeredEulerStep]

theorem centeredEulerStep_eval_one (α : ℝ) (f : ℝ[X]) :
    (centeredEulerStep α f).eval 1 = f.eval 1 := by
  simp [centeredEulerStep_eval]

theorem centeredEulerStep_eval_neg_one (α : ℝ) (f : ℝ[X]) :
    (centeredEulerStep α f).eval (-1) = -f.eval (-1) := by
  simp [centeredEulerStep_eval]

theorem centeredEulerStep_coeff_succ_natDegree
    (α : ℝ) (f : ℝ[X]) :
    (centeredEulerStep α f).coeff (f.natDegree + 1) =
      (1 + α * f.natDegree) * f.leadingCoeff := by
  rw [show centeredEulerStep α f =
      X * (C 1 * f + (C 0 + C α * X) * f.derivative) - C α * f.derivative by
    simp [centeredEulerStep]
    ring]
  rw [coeff_sub, coeff_X_mul, coeff_C_mul_add_affine_mul_derivative_natDegree,
    coeff_C_mul, coeff_derivative,
    coeff_eq_zero_of_natDegree_lt (by lia : f.natDegree < f.natDegree + 1 + 1)]
  simp

/-- Exact degree and leading coefficient of one centered Euler step. -/
theorem centeredEulerStep_degree_leadingCoeff
    {α : ℝ} {f : ℝ[X]} (hf : f ≠ 0) (hfactor : 0 < 1 + α * f.natDegree) :
    (centeredEulerStep α f).natDegree = f.natDegree + 1 ∧
      (centeredEulerStep α f).leadingCoeff =
        (1 + α * f.natDegree) * f.leadingCoeff := by
  let A : ℝ[X] := C 1 * f + (C 0 + C α * X) * f.derivative
  have htop : (1 + α * (f.natDegree : ℝ)) * f.leadingCoeff ≠ 0 :=
    mul_ne_zero hfactor.ne' (leadingCoeff_ne_zero.mpr hf)
  have hA := natDegree_and_leadingCoeff_C_mul_add_affine_mul_derivative
    f 1 0 α (by simpa using htop)
  have hA0 : A ≠ 0 := by
    intro hzero
    have h := congrArg leadingCoeff hzero
    rw [show A.leadingCoeff = (1 + α * (f.natDegree : ℝ)) * f.leadingCoeff by
      simpa [A] using hA.2] at h
    simpa using htop h
  have hAdeg : A.natDegree = f.natDegree := by simpa [A] using hA.1
  have hrewrite : centeredEulerStep α f = X * A - C α * f.derivative := by
    simp [centeredEulerStep, A]
    ring
  have hsmall : (C α * f.derivative).natDegree < (X * A).natDegree := by
    have hder : (C α * f.derivative).natDegree ≤ f.natDegree - 1 := by
      exact (natDegree_C_mul_le _ _).trans_eq f.natDegree_derivative
    have hlt : (C α * f.derivative).natDegree < f.natDegree + 1 := by lia
    have hXA : (X * A).natDegree = f.natDegree + 1 := by
      simpa [hAdeg] using natDegree_X_mul hA0
    rwa [hXA]
  rw [hrewrite, natDegree_sub_eq_left_of_natDegree_lt hsmall,
    natDegree_X_mul hA0, hAdeg]
  constructor
  · rfl
  · rw [leadingCoeff_sub_of_degree_lt (degree_lt_degree hsmall)]
    simpa [A] using hA.2

/-- A positive centered Euler step raises the degree and preserves the leading sign. -/
theorem centeredEulerStep_hasPosLeadingCoeff
    {α : ℝ} {f : ℝ[X]} (hα : 0 < α) (hf : HasPosLeadingCoeff f) :
    HasPosLeadingCoeff (centeredEulerStep α f) := by
  rw [HasPosLeadingCoeff, (centeredEulerStep_degree_leadingCoeff hf.ne_zero (by positivity)).2]
  exact mul_pos (by positivity) hf

/-- One centered Euler step inserts one simple root in every gap and keeps all
roots in `(-1,1)`. -/
theorem centeredEulerStep_roots
    {α : ℝ} {f : ℝ[X]} (hα : 0 < α)
    (hf : IsRealRootedIn (Ioo (-1 : ℝ) 1) f) (hsimple : HasSimpleRoots f)
    (hf_pos : HasPosLeadingCoeff f) :
    IsRealRootedIn (Ioo (-1 : ℝ) 1) (centeredEulerStep α f) ∧
      HasSimpleRoots (centeredEulerStep α f) := by
  have hdegree := (centeredEulerStep_degree_leadingCoeff hf.ne_zero (by positivity)).1
  have hnd := hsimple.roots_nodup
  have hinside : ∀ z ∈ f.roots, -1 < z ∧ z < 1 := hf.2.2
  have hresult := IntervalDifferential.splits_nodup_interval_of_root_derivative_signs
    hf.splits hf.ne_zero hnd hinside hdegree
    (fun z hz => by
      rw [centeredEulerStep_eval]
      have hz0 : f.eval z = 0 := ((mem_roots hf.ne_zero).mp hz).eq_zero
      rw [hz0]
      have hzmem := hinside z hz
      have hsquare : z ^ 2 - 1 < 0 := by
        nlinarith [mul_pos (sub_pos.mpr hzmem.2) (by linarith : 0 < 1 + z)]
      have hder : f.derivative.eval z ≠ 0 :=
        hsimple.eval_derivative_ne_zero ((mem_roots hf.ne_zero).mp hz)
      have haf : α * (z ^ 2 - 1) < 0 := mul_neg_of_pos_of_neg hα hsquare
      nlinarith [mul_neg_of_neg_of_pos haf (sq_pos_of_ne_zero hder)])
    (by
      rw [centeredEulerStep_eval_neg_one]
      have hne : f.eval (-1) ≠ 0 := by
        intro hzero
        have hroot : f.IsRoot (-1) := hzero
        exact (lt_irrefl (-1 : ℝ)) (hf.mem_of_isRoot hroot).1
      nlinarith [sq_pos_of_ne_zero hne])
    (by
      rw [centeredEulerStep_eval_one]
      have hne : f.eval 1 ≠ 0 := by
        intro hzero
        have hroot : f.IsRoot 1 := hzero
        exact (lt_irrefl (1 : ℝ)) (hf.mem_of_isRoot hroot).2
      nlinarith [sq_pos_of_ne_zero hne])
  refine ⟨⟨(centeredEulerStep_hasPosLeadingCoeff hα hf_pos).ne_zero,
    hresult.1, hresult.2.2⟩, ?_⟩
  exact HasSimpleRoots.of_roots_nodup
    (centeredEulerStep_hasPosLeadingCoeff hα hf_pos).ne_zero hresult.2.1

@[simp] theorem centeredEulerOrbit_eval_one (α : ℝ) (n : ℕ) :
    (centeredEulerOrbit α n).eval 1 = 1 := by
  induction n with
  | zero => simp
  | succ n ih => simpa using congrArg (fun x : ℝ => x) ih

@[simp] theorem centeredEulerOrbit_eval_neg_one (α : ℝ) (n : ℕ) :
    (centeredEulerOrbit α n).eval (-1) = (-1 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- Every row of the centered Euler orbit has positive leading coefficient. -/
theorem centeredEulerOrbit_hasPosLeadingCoeff {α : ℝ} (hα : 0 < α) (n : ℕ) :
    HasPosLeadingCoeff (centeredEulerOrbit α n) := by
  induction n with
  | zero => simp [HasPosLeadingCoeff]
  | succ n ih => exact centeredEulerStep_hasPosLeadingCoeff hα ih

/-- The centered Euler orbit has exact degree equal to its index. -/
theorem centeredEulerOrbit_natDegree {α : ℝ} (hα : 0 < α) (n : ℕ) :
    (centeredEulerOrbit α n).natDegree = n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [centeredEulerOrbit_succ,
        (centeredEulerStep_degree_leadingCoeff
          (centeredEulerOrbit_hasPosLeadingCoeff hα n).ne_zero (by positivity)).1, ih]

/-- Every row of the centered Euler orbit has simple roots in `(-1,1)`. -/
theorem centeredEulerOrbit_roots {α : ℝ} (hα : 0 < α) (n : ℕ) :
    IsRealRootedIn (Ioo (-1 : ℝ) 1) (centeredEulerOrbit α n) ∧
      HasSimpleRoots (centeredEulerOrbit α n) := by
  induction n with
  | zero =>
      exact ⟨IsRealRootedIn.one, hasSimpleRoots_of_natDegree_le_one one_ne_zero (by simp)⟩
  | succ n ih =>
      exact centeredEulerStep_roots hα ih.1 ih.2
        (centeredEulerOrbit_hasPosLeadingCoeff hα n)

/-- Degree, leading sign, root location, simplicity, and endpoint normalization
for the centered Euler orbit in the parameter range of issue #2513. -/
theorem centeredEulerOrbit_package {α : ℝ} (hα : 1 / 2 ≤ α) (n : ℕ) :
    (centeredEulerOrbit α n).natDegree = n ∧
      HasPosLeadingCoeff (centeredEulerOrbit α n) ∧
      IsRealRootedIn (Ioo (-1 : ℝ) 1) (centeredEulerOrbit α n) ∧
      HasSimpleRoots (centeredEulerOrbit α n) ∧
      (centeredEulerOrbit α n).eval 1 = 1 ∧
      (centeredEulerOrbit α n).eval (-1) = (-1 : ℝ) ^ n := by
  have hαpos : 0 < α := lt_of_lt_of_le (by norm_num) hα
  exact ⟨centeredEulerOrbit_natDegree hαpos n,
    centeredEulerOrbit_hasPosLeadingCoeff hαpos n,
    (centeredEulerOrbit_roots hαpos n).1,
    (centeredEulerOrbit_roots hαpos n).2,
    centeredEulerOrbit_eval_one α n,
    centeredEulerOrbit_eval_neg_one α n⟩

end RealRooted
