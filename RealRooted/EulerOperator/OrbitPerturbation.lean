module

public import RealRooted.RootLocation.Basic
public import RealRooted.SimpleRoots
public import RealRooted.Basic.ProperPosition

import RealRooted.IntervalDifferential.LinearInsertion
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import RealRooted.Mathlib.Analysis.Polynomial.InverseBernstein
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
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

/-- The first centered Euler orbit polynomial. -/
private theorem centeredEulerOrbit_one (α : ℝ) :
    centeredEulerOrbit α 1 = X := by
  simp [centeredEulerOrbit, centeredEulerStep]

/-- The second centered Euler orbit polynomial. -/
private theorem centeredEulerOrbit_two (α : ℝ) :
    centeredEulerOrbit α 2 = C (α + 1) * X ^ 2 - C α := by
  rw [show centeredEulerOrbit α 2 = centeredEulerStep α (centeredEulerOrbit α 1) by rfl,
    centeredEulerOrbit_one]
  simp [centeredEulerStep]
  ring

/-- The third centered Euler orbit polynomial. -/
private theorem centeredEulerOrbit_three (α : ℝ) :
    centeredEulerOrbit α 3 = C (2 * α ^ 2 + 3 * α + 1) * X ^ 3 -
      C (2 * α ^ 2 + 3 * α) * X := by
  rw [show centeredEulerOrbit α 3 = centeredEulerStep α (centeredEulerOrbit α 2) by rfl,
    centeredEulerOrbit_two]
  simp [centeredEulerStep, derivative_sub, derivative_mul, derivative_pow, map_ofNat]
  ring

/-- The fourth centered Euler orbit polynomial. -/
private theorem centeredEulerOrbit_four (α : ℝ) :
    centeredEulerOrbit α 4 =
      C (6 * α ^ 3 + 11 * α ^ 2 + 6 * α + 1) * X ^ 4 -
      C (8 * α ^ 3 + 14 * α ^ 2 + 6 * α) * X ^ 2 +
      C (2 * α ^ 3 + 3 * α ^ 2) := by
  rw [show centeredEulerOrbit α 4 = centeredEulerStep α (centeredEulerOrbit α 3) by rfl,
    centeredEulerOrbit_three]
  simp [centeredEulerStep, derivative_sub, derivative_mul, derivative_pow, map_ofNat]
  ring

/-- The explicit degree-five polynomial in the centered Euler orbit. -/
theorem centeredEulerOrbit_five (α : ℝ) :
    centeredEulerOrbit α 5 =
      C (24 * α ^ 4 + 50 * α ^ 3 + 35 * α ^ 2 + 10 * α + 1) * X ^ 5 -
      C (40 * α ^ 4 + 80 * α ^ 3 + 50 * α ^ 2 + 10 * α) * X ^ 3 +
      C (16 * α ^ 4 + 30 * α ^ 3 + 15 * α ^ 2) * X := by
  rw [show centeredEulerOrbit α 5 = centeredEulerStep α (centeredEulerOrbit α 4) by rfl,
    centeredEulerOrbit_four]
  simp [centeredEulerStep, derivative_add, derivative_sub, derivative_mul, derivative_pow,
    map_ofNat]
  ring

/-- At six fixed points, the degree-five centered Euler orbit has alternating
values of absolute value at least one. -/
theorem centeredEulerOrbit_five_alternation {α : ℝ} (hα : 1 / 2 ≤ α) (i : Fin 6) :
    1 ≤ (-1 : ℝ) ^ (5 - (i : ℕ)) * (centeredEulerOrbit α 5).eval
      (![-1, -5 / 6, -1 / 3, 1 / 3, 5 / 6, 1] i) := by
  let β := α - 1 / 2
  have hβ : 0 ≤ β := by
    dsimp [β]
    linarith
  have hβ_two : 0 ≤ β ^ 2 := pow_nonneg hβ 2
  have hβ_three : 0 ≤ β ^ 3 := pow_nonneg hβ 3
  have hβ_four : 0 ≤ β ^ 4 := pow_nonneg hβ 4
  have hα_eq : α = 1 / 2 + β := by
    dsimp [β]
    ring
  rw [centeredEulerOrbit_five]
  fin_cases i <;> norm_num [hα_eq] <;>
    nlinarith [hβ_two, hβ_three, hβ_four]

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

/-! ### Propagation of large critical values -/

/-- Roots in `(-1, 1)` in the `IsRealRootedIn` form give the root count used by the inverse
Bernstein inequality. -/
theorem card_roots_filter_Ioo_of_isRealRootedIn {f : ℝ[X]}
    (hf : IsRealRootedIn (Ioo (-1 : ℝ) 1) f) :
    (f.roots.filter (· ∈ Ioo (-1 : ℝ) 1)).card = f.natDegree := by
  rw [Multiset.filter_eq_self.mpr hf.2.2, ← hf.2.1.natDegree_eq_card_roots]

/-- Signed form of alternation points ending at `p (C n) = 1`. -/
private theorem signed_alternation {p : ℝ[X]} {n : ℕ} {C : ℕ → ℝ} (hCn : C n = 1)
    (hone : p.eval 1 = 1) (hcrit : ∀ k ≤ n, 1 ≤ |p.eval (C k)|)
    (hprod : ∀ k < n, p.eval (C k) * p.eval (C (k + 1)) < 0) :
    ∀ k ≤ n, 1 ≤ (-1 : ℝ) ^ (n - k) * p.eval (C k) := by
  have key : ∀ d k, k + d = n → 1 ≤ (-1 : ℝ) ^ (n - k) * p.eval (C k) := by
    intro d
    induction d with
    | zero =>
        intro k hk
        rw [show k = n by lia, Nat.sub_self, pow_zero, one_mul, hCn, hone]
    | succ d ih =>
        intro k hk
        have h1 := ih (k + 1) (by lia)
        have h2 := hprod k (by lia)
        have h3 := hcrit k (by lia)
        rw [show n - k = n - (k + 1) + 1 by lia, pow_succ]
        rcases neg_one_pow_eq_or ℝ (n - (k + 1)) with he | he <;> rw [he] at h1 ⊢
        · have hneg : p.eval (C k) < 0 := by nlinarith
          rw [abs_of_neg hneg] at h3
          linarith
        · have hpos : 0 < p.eval (C k) := by nlinarith
          rw [abs_of_pos hpos] at h3
          linarith
  intro k hk
  exact key (n - k) k (by lia)

/-- On each monotone branch `(C k, C (k + 1))` of `p` there is a point where the centered Euler
step has the sign `(-1) ^ (n - k)` and absolute value at least one, provided `α n ≥ 1`. -/
private theorem exists_branch_point {α : ℝ} (hα : 0 ≤ α) {p : ℝ[X]} {n : ℕ} (hn : 0 < n)
    (hdeg : p.natDegree = n) (hroots : (p.roots.filter (· ∈ Ioo (-1 : ℝ) 1)).card = n)
    (hsimple : p.roots.Nodup) (hone : p.eval 1 = 1) (hmone : p.eval (-1) = (-1) ^ n)
    (hcrit : ∀ c ∈ Ioo (-1 : ℝ) 1, p.derivative.eval c = 0 → 1 ≤ |p.eval c|)
    (hαn : 1 ≤ α * n) {C : ℕ → ℝ} (hC0 : C 0 = -1) (hCn : C n = 1)
    (hstep : ∀ k < n, C k < C (k + 1))
    (hnoz : ∀ k < n, ∀ x ∈ Ioo (C k) (C (k + 1)), p.derivative.eval x ≠ 0)
    (hsigned : ∀ k ≤ n, 1 ≤ (-1 : ℝ) ^ (n - k) * p.eval (C k)) {k : ℕ} (hk : k < n) :
    ∃ ξ ∈ Ioo (C k) (C (k + 1)),
      1 ≤ (-1 : ℝ) ^ (n - k) * (centeredEulerStep α p).eval ξ := by
  have hmono : ∀ a b, a ≤ b → b ≤ n → C a ≤ C b := by
    intro a b hab hbn
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact (ih (by lia)).trans (hstep b (by lia)).le
  have hCk1 : C k < 1 := hCn ▸ (hstep k hk).trans_le (hmono (k + 1) n hk le_rfl)
  have hCk2 : -1 < C (k + 1) := hC0 ▸ (hmono 0 k (Nat.zero_le _) hk.le).trans_lt (hstep k hk)
  have hs0 := hsigned k hk.le
  have hs1 := hsigned (k + 1) hk
  have hnk : n - k = n - (k + 1) + 1 := by lia
  have hIB : ∀ ξ ∈ Ioo (C k) (C (k + 1)), (n : ℝ) ^ 2 * (1 - p.eval ξ ^ 2) ≤
      (1 - ξ ^ 2) * p.derivative.eval ξ ^ 2 := fun ξ hξ ↦
    Polynomial.sq_mul_one_sub_sq_le_of_abs_eval_critical hn hdeg hroots hsimple hone hmone hcrit
      ⟨(hC0 ▸ hmono 0 k (Nat.zero_le _) hk.le).trans hξ.1.le,
        hξ.2.le.trans (hCn ▸ hmono (k + 1) n hk le_rfl)⟩
  have hξsq : ∀ ξ ∈ Ioo (C k) (C (k + 1)), 0 < 1 - ξ ^ 2 := by
    intro ξ hξ
    have h1 : -1 < ξ := hC0 ▸ (hmono 0 k (Nat.zero_le _) hk.le).trans_lt hξ.1
    have h2 : ξ < 1 := hξ.2.trans_le (hCn ▸ hmono (k + 1) n hk le_rfl)
    nlinarith
  rw [hnk, pow_succ] at hs0 ⊢
  rcases neg_one_pow_eq_or ℝ (n - (k + 1)) with he | he <;> rw [he] at hs0 hs1 ⊢
  · -- increasing branch: `p (C k) ≤ -1`, `p (C (k + 1)) ≥ 1`; take `p ξ = -ξ`
    obtain ⟨ξ, hξ, hξ0⟩ := exists_Ioo_eq_zero_of_mul_neg
      (f := fun t ↦ p.eval t + t) (p.continuous.add continuous_id) (hstep k hk)
      (show (p.eval (C k) + C k) * (p.eval (C (k + 1)) + C (k + 1)) < 0 by nlinarith)
    have hpξ : p.eval ξ = -ξ := by
      have h : p.eval ξ + ξ = 0 := hξ0
      linarith
    have hder : 0 < p.derivative.eval ξ := by
      rcases Polynomial.derivative_pos_or_neg_of_ne_zero (hnoz k hk) with h | h
      · exact h ξ hξ
      · exfalso
        have hanti : StrictAntiOn (fun z ↦ p.eval z) (Icc (C k) (C (k + 1))) := by
          refine strictAntiOn_of_deriv_neg (convex_Icc _ _) p.continuous.continuousOn
            fun z hz ↦ ?_
          rw [interior_Icc] at hz
          simpa [Polynomial.deriv] using h z hz
        have := hanti ⟨le_rfl, (hstep k hk).le⟩ ⟨(hstep k hk).le, le_rfl⟩ (hstep k hk)
        simp only at this
        linarith
    have hsq := hξsq ξ hξ
    have hIBξ := hIB ξ hξ
    rw [hpξ, neg_sq] at hIBξ
    have hn2 : (n : ℝ) ^ 2 ≤ p.derivative.eval ξ ^ 2 := by nlinarith
    have hnd : (n : ℝ) ≤ p.derivative.eval ξ := by
      have := sq_le_sq.mp hn2
      rwa [abs_of_nonneg (Nat.cast_nonneg n), abs_of_pos hder] at this
    refine ⟨ξ, hξ, ?_⟩
    rw [centeredEulerStep_eval, hpξ]
    nlinarith [mul_le_mul_of_nonneg_left hnd (mul_nonneg hα hsq.le)]
  · -- decreasing branch: `p (C k) ≥ 1`, `p (C (k + 1)) ≤ -1`; take `p ξ = ξ`
    obtain ⟨ξ, hξ, hξ0⟩ := exists_Ioo_eq_zero_of_mul_neg
      (f := fun t ↦ p.eval t - t) (p.continuous.sub continuous_id) (hstep k hk)
      (show (p.eval (C k) - C k) * (p.eval (C (k + 1)) - C (k + 1)) < 0 by nlinarith)
    have hpξ : p.eval ξ = ξ := by
      have h : p.eval ξ - ξ = 0 := hξ0
      linarith
    have hder : p.derivative.eval ξ < 0 := by
      rcases Polynomial.derivative_pos_or_neg_of_ne_zero (hnoz k hk) with h | h
      · exfalso
        have hmono' : StrictMonoOn (fun z ↦ p.eval z) (Icc (C k) (C (k + 1))) := by
          refine strictMonoOn_of_deriv_pos (convex_Icc _ _) p.continuous.continuousOn
            fun z hz ↦ ?_
          rw [interior_Icc] at hz
          simpa [Polynomial.deriv] using h z hz
        have := hmono' ⟨le_rfl, (hstep k hk).le⟩ ⟨(hstep k hk).le, le_rfl⟩ (hstep k hk)
        simp only at this
        linarith
      · exact h ξ hξ
    have hsq := hξsq ξ hξ
    have hIBξ := hIB ξ hξ
    rw [hpξ] at hIBξ
    have hn2 : (n : ℝ) ^ 2 ≤ p.derivative.eval ξ ^ 2 := by nlinarith
    have hnd : (n : ℝ) ≤ -p.derivative.eval ξ := by
      have := sq_le_sq.mp hn2
      rwa [abs_of_nonneg (Nat.cast_nonneg n), abs_of_neg hder] at this
    refine ⟨ξ, hξ, ?_⟩
    rw [centeredEulerStep_eval, hpξ]
    nlinarith [mul_le_mul_of_nonneg_left hnd (mul_nonneg hα hsq.le)]

/-- Signed alternation `(-1) ^ (N - i) q (η i) ≥ 1` gives the absolute-value and sign-change
hypotheses of `Polynomial.one_le_abs_eval_critical_of_alternation`. -/
private theorem alternation_of_signed {q : ℝ[X]} {N : ℕ} {η : ℕ → ℝ}
    (h : ∀ i ≤ N, 1 ≤ (-1 : ℝ) ^ (N - i) * q.eval (η i)) :
    (∀ i ≤ N, 1 ≤ |q.eval (η i)|) ∧ (∀ i < N, q.eval (η i) * q.eval (η (i + 1)) < 0) := by
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · have := h i hi
    rcases neg_one_pow_eq_or ℝ (N - i) with he | he <;> rw [he] at this
    · exact le_abs.mpr (Or.inl (by linarith))
    · exact le_abs.mpr (Or.inr (by linarith))
  · have h1 := h i hi.le
    have h2 := h (i + 1) hi
    rw [show N - i = N - (i + 1) + 1 by lia, pow_succ] at h1
    rcases neg_one_pow_eq_or ℝ (N - (i + 1)) with he | he <;> rw [he] at h1 h2 <;> nlinarith

/-- **Propagation.** If `p` has degree `n > 0`, simple roots in `(-1, 1)`, `p 1 = 1`,
`p (-1) = (-1) ^ n`, and all critical values of absolute value at least one, then so does the
centered Euler step `X p + α (X² - 1) p'` whenever `α n ≥ 1`. -/
theorem centeredEulerStep_critical_values {α : ℝ} (hα : 0 < α) {p : ℝ[X]} {n : ℕ} (hn : 0 < n)
    (hp : IsRealRootedIn (Ioo (-1 : ℝ) 1) p) (hsimple : HasSimpleRoots p)
    (hdeg : p.natDegree = n) (hpos : HasPosLeadingCoeff p) (hone : p.eval 1 = 1)
    (hmone : p.eval (-1) = (-1) ^ n)
    (hcrit : ∀ c ∈ Ioo (-1 : ℝ) 1, p.derivative.eval c = 0 → 1 ≤ |p.eval c|)
    (hαn : 1 ≤ α * n) :
    ∀ c ∈ Ioo (-1 : ℝ) 1, (centeredEulerStep α p).derivative.eval c = 0 →
      1 ≤ |(centeredEulerStep α p).eval c| := by
  have hroots := card_roots_filter_Ioo_of_isRealRootedIn hp
  rw [hdeg] at hroots
  have hnd := hsimple.roots_nodup
  obtain ⟨C, hC0, hCn, hstep, hcritC, hprod, hnoz⟩ :=
    Polynomial.exists_alternation_points hn hdeg hroots hnd hone hmone hcrit
  have hsigned := signed_alternation hCn hone hcritC hprod
  have hbr : ∀ k < n, ∃ ξ ∈ Ioo (C k) (C (k + 1)),
      1 ≤ (-1 : ℝ) ^ (n - k) * (centeredEulerStep α p).eval ξ := fun k hk ↦
    exists_branch_point hα.le hn hdeg hroots hnd hone hmone hcrit hαn hC0 hCn hstep hnoz
      hsigned hk
  choose! ξ hξ hξv using hbr
  set q := centeredEulerStep α p with hq
  have hqdeg : q.natDegree = n + 1 := by
    rw [hq, (centeredEulerStep_degree_leadingCoeff hp.1 (by positivity)).1, hdeg]
  have hqroots := centeredEulerStep_roots hα hp hsimple hpos
  set η : ℕ → ℝ := fun i ↦ if i = 0 then -1 else if i ≤ n then ξ (i - 1) else 1 with hη
  have hsignedq : ∀ i ≤ n + 1, 1 ≤ (-1 : ℝ) ^ (n + 1 - i) * q.eval (η i) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [hη, ↓reduceIte, Nat.sub_zero, hq, centeredEulerStep_eval_neg_one, hmone]
      have h2 : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have h3 : (-1 : ℝ) ^ (n + 1) * -(-1) ^ n = ((-1 : ℝ) ^ n) ^ 2 := by ring
      rw [h3, h2]
    by_cases hin : i ≤ n
    · simp only [hη, hi0.ne', hin, ↓reduceIte]
      rw [show n + 1 - i = n - (i - 1) by lia]
      exact hξv (i - 1) (by lia)
    · have : i = n + 1 := by lia
      subst this
      simp only [hη, show n + 1 ≠ 0 by lia, show ¬ n + 1 ≤ n by lia, ↓reduceIte, Nat.sub_self,
        pow_zero, one_mul, hq, centeredEulerStep_eval_one, hone, le_refl]
  obtain ⟨halt, hprodq⟩ := alternation_of_signed hsignedq
  have hηinc : ∀ i < n + 1, η i < η (i + 1) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [hη, ↓reduceIte, show (0 + 1 : ℕ) ≠ 0 by lia, show 0 + 1 ≤ n by lia,
        Nat.add_sub_cancel]
      exact hC0 ▸ (hξ 0 hn).1
    by_cases hin : i + 1 ≤ n
    · simp only [hη, hi0.ne', show i ≤ n by lia, hin, show i + 1 ≠ 0 by lia, ↓reduceIte,
        Nat.add_sub_cancel]
      have h1 := (hξ (i - 1) (by lia)).2
      rw [show i - 1 + 1 = i by lia] at h1
      exact h1.trans (hξ i (by lia)).1
    · have hin' : i = n := by lia
      subst hin'
      simp only [hη, hi0.ne', le_refl, show ¬ i + 1 ≤ i by lia, show i + 1 ≠ 0 by lia,
        ↓reduceIte]
      have h1 := (hξ (i - 1) (by lia)).2
      rwa [show i - 1 + 1 = i by lia, hCn] at h1
  exact Polynomial.one_le_abs_eval_critical_of_alternation (by lia) hqdeg
    (by rw [card_roots_filter_Ioo_of_isRealRootedIn hqroots.1, hqdeg]) hqroots.2.roots_nodup
    (by simp [hη]) (by simp [hη]) hηinc halt hprodq

end RealRooted
