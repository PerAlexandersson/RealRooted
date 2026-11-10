module

public import RealRooted.EulerOperator.OrbitPerturbation
import RealRooted.EulerOperator.OrbitPerturbationInterlacing
import RealRooted.Linear
import RealRooted.MaWang.Weak.DerivativeSign
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A three-term θ-recurrence family with interlacing rows

Let `s ≥ 1` and `κ ≥ s + 4`, and let `Q 0 = 1`, `Q 1 = 1 + 2 u`, `Q 2 = 1 + κ u + κ u²` and,
for `n ≥ 3`, with `θ = u d/du`,

    (n - 2) Q n = ((2 n - 3) (2 u + 1) + (n - 2) s (u + 1) θ) Q (n - 1)
                  - (n - 1) (2 u + 1) ((2 u + 1) + s (u + 1) θ) Q (n - 2).

Then every `Q n` has simple roots in `(-1, 0)` and `Q n` strictly interlaces `Q (n + 1)`
(`strictInterl_of_orbitPerturbation_recurrence`).  This covers OEIS A141689 `(s, κ) = (1, 5)`,
A141690 `(1, 8)`, A141696 `(1, 10)`, A141697 `(1, 18)` and A147565 `(2, 6)` after the Eulerian
Möbius substitution (RealRooted #2513, Theorem 1).

With `x = 2 u + 1`, `α = s / 2` and `r = (κ - 4) / (2 s) ≥ 1 / 2`, the rows are
`Q n = r p n (x) + (1 - r) x ^ n`, where `p n` is the centered Euler orbit; the interlacing comes
from `centeredEulerOrbit_add_monomial`.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- One centered Euler step, read in the variable `u` with `x = 2 u + 1`. -/
theorem centeredEulerStep_comp_two_mul_X_add_one (α : ℝ) (f : ℝ[X]) :
    (centeredEulerStep α f).comp (C 2 * X + C 1) =
      (C 2 * X + C 1) * f.comp (C 2 * X + C 1) +
        C (2 * α) * (X + 1) * (X * (f.comp (C 2 * X + C 1)).derivative) := by
  simp [centeredEulerStep, derivative_comp, map_ofNat]
  ring

/-- The rows `r p n (2 u + 1) + (1 - r) (2 u + 1) ^ n` of the centered Euler orbit perturbed
by a monomial, in the variable `u`. -/
def orbitPerturbationRow (α r : ℝ) (n : ℕ) : ℝ[X] :=
  (C r * centeredEulerOrbit α n + (1 - C r) * X ^ n).comp (C 2 * X + C 1)

/-- The perturbed rows expanded: `Q n = r p n (2 u + 1) + (1 - r) (2 u + 1) ^ n`. -/
theorem orbitPerturbationRow_eq (α r : ℝ) (n : ℕ) :
    orbitPerturbationRow α r n = C r * (centeredEulerOrbit α n).comp (C 2 * X + C 1) +
      C (1 - r) * (C 2 * X + C 1) ^ n := by
  simp [orbitPerturbationRow]

/-- The perturbed rows as a multiple of `h n = p n + b X ^ n` with `b = (1 - r) / r`. -/
theorem orbitPerturbationRow_eq_C_mul {α r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    orbitPerturbationRow α r n =
      C r * (centeredEulerOrbit α n + C ((1 - r) / r) * X ^ n).comp (C 2 * X + C 1) := by
  rw [orbitPerturbationRow, ← C_mul_comp, mul_add, ← mul_assoc, ← C_mul,
    show r * ((1 - r) / r) = 1 - r by field_simp, map_sub, map_one]

/-- The perturbed rows satisfy the three-term θ-recurrence of the family with `s = 2 α`. -/
theorem orbitPerturbationRow_recurrence (α r : ℝ) (n : ℕ) :
    ((n : ℝ[X]) + 1) * orbitPerturbationRow α r (n + 3) =
      (2 * (n : ℝ[X]) + 3) * (C 2 * X + 1) * orbitPerturbationRow α r (n + 2) +
        ((n : ℝ[X]) + 1) * C (2 * α) * (X + 1) *
          (X * (orbitPerturbationRow α r (n + 2)).derivative) -
        ((n : ℝ[X]) + 2) * (C 2 * X + 1) *
          ((C 2 * X + 1) * orbitPerturbationRow α r (n + 1) +
            C (2 * α) * (X + 1) * (X * (orbitPerturbationRow α r (n + 1)).derivative)) := by
  have hstep : ∀ k, (centeredEulerOrbit α (k + 1)).comp (C 2 * X + C 1) =
      (C 2 * X + C 1) * (centeredEulerOrbit α k).comp (C 2 * X + C 1) +
        C (2 * α) * (X + 1) * (X * ((centeredEulerOrbit α k).comp (C 2 * X + C 1)).derivative) :=
    fun k ↦ by rw [centeredEulerOrbit_succ, centeredEulerStep_comp_two_mul_X_add_one]
  have h3 : (centeredEulerOrbit α (n + 3)).comp (C 2 * X + C 1) = _ := hstep (n + 2)
  have h2 : (centeredEulerOrbit α (n + 2)).comp (C 2 * X + C 1) = _ := hstep (n + 1)
  simp only [orbitPerturbationRow, add_comp, mul_comp, sub_comp, C_comp, one_comp, X_pow_comp]
  generalize (centeredEulerOrbit α (n + 3)).comp (C 2 * X + C 1) = P3 at *
  generalize (centeredEulerOrbit α (n + 2)).comp (C 2 * X + C 1) = P2 at *
  generalize (centeredEulerOrbit α (n + 1)).comp (C 2 * X + C 1) = P1 at *
  clear hstep
  simp only [derivative_add, derivative_mul, derivative_sub, derivative_C, derivative_one,
    derivative_pow, derivative_X, derivative_ofNat, map_one, map_ofNat] at h2 h3 ⊢
  push_cast at h2 h3 ⊢
  simp only [map_add, map_natCast, map_ofNat, map_one] at h2 h3 ⊢
  linear_combination ((n : ℝ[X]) + 1) * C r * h3 - ((n : ℝ[X]) + 2) * (2 * X + 1) * C r * h2

@[simp] theorem orbitPerturbationRow_zero (α r : ℝ) : orbitPerturbationRow α r 0 = 1 := by
  simp [orbitPerturbationRow]

theorem orbitPerturbationRow_one (α r : ℝ) : orbitPerturbationRow α r 1 = C 2 * X + 1 := by
  simp [orbitPerturbationRow, centeredEulerStep]
  ring

/-- For `α ≥ 1 / 2` and `r ≥ 1 / 2`, the perturbed rows have simple roots in `(-1, 0)` and
consecutive rows interlace strictly. -/
theorem orbitPerturbationRow_package {α r : ℝ} (hαhalf : 1 / 2 ≤ α) (hrhalf : 1 / 2 ≤ r)
    (n : ℕ) :
    IsRealRootedIn (Ioo (-1 : ℝ) 0) (orbitPerturbationRow α r n) ∧
      HasSimpleRoots (orbitPerturbationRow α r n) ∧
      StrictInterl (orbitPerturbationRow α r n) (orbitPerturbationRow α r (n + 1)) := by
  have hrpos : 0 < r := by linarith
  -- Transfer from the centered coordinates.
  have hloc : (fun x : ℝ ↦ 2 * x + 1) ⁻¹' Ioo (-1 : ℝ) 1 = Ioo (-1 : ℝ) 0 := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hcomp : ∀ f : ℝ[X], f.comp (C 2 * X + C 1) = (f.comp (C 2 * X)).comp (X + C (1 / 2)) := by
    intro f
    rw [comp_assoc]
    congr 1
    simp only [mul_comp, C_comp, X_comp]
    rw [mul_add, ← C_mul]
    norm_num
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [orbitPerturbationRow_zero α r]
    refine ⟨IsRealRootedIn.one, hasSimpleRoots_of_natDegree_le_one one_ne_zero (by simp), ?_⟩
    rw [zero_add, orbitPerturbationRow_one α r]
    exact StrictInterl.of_natDegree_eq_zero_left one_ne_zero (by simp)
      (by
        intro h
        have h' := congrArg (fun p ↦ p.coeff 1) h
        simp [coeff_one, coeff_C] at h')
      (by compute_degree!)
  have hb : -1 < (1 - r) / r := by
    rw [lt_div_iff₀ hrpos]
    linarith
  have hb1 : (1 - r) / r ≤ 1 := by
    rw [div_le_iff₀ hrpos]
    linarith
  obtain ⟨-, -, hroot, hsimple, hint⟩ := centeredEulerOrbit_add_monomial hαhalf hb hb1 hn
  rw [orbitPerturbationRow_eq_C_mul hrpos.ne', orbitPerturbationRow_eq_C_mul hrpos.ne']
  refine ⟨?_, ?_, ?_⟩
  · refine IsRealRootedIn.C_mul hrpos.ne' ?_
    rw [← hloc]
    exact hroot.comp_C_mul_X_add_C 1 two_ne_zero
  · exact (hsimple.comp_C_mul_X_add_C two_ne_zero).C_mul hrpos.ne'
  · rw [hcomp, hcomp]
    exact (((hint.comp_C_mul_X two_pos).comp_X_add_C _).C_mul_left hrpos.ne').C_mul_right
      hrpos.ne'

/-- **A θ-recurrence family with interlacing rows** (RealRooted #2513, Theorem 1).  Let `s ≥ 1`
and `κ ≥ s + 4`, and let `Q` satisfy `Q 0 = 1`, `Q 1 = 2 u + 1`, `Q 2 = κ u² + κ u + 1` and
`(n + 1) Q (n + 3) = (2 n + 3) (2 u + 1) Q (n + 2) + (n + 1) s (u + 1) θ Q (n + 2)
  - (n + 2) (2 u + 1) ((2 u + 1) Q (n + 1) + s (u + 1) θ Q (n + 1))` with `θ = u d/du`.
Then every `Q n` has simple roots in `(-1, 0)` and `Q n` strictly interlaces `Q (n + 1)`. -/
theorem strictInterl_of_orbitPerturbation_recurrence {s κ : ℝ} (hs : 1 ≤ s) (hκ : s + 4 ≤ κ)
    {Q : ℕ → ℝ[X]} (h0 : Q 0 = 1) (h1 : Q 1 = C 2 * X + 1)
    (h2 : Q 2 = C κ * X ^ 2 + C κ * X + 1)
    (hrec : ∀ n : ℕ, ((n : ℝ[X]) + 1) * Q (n + 3) =
      (2 * (n : ℝ[X]) + 3) * (C 2 * X + 1) * Q (n + 2) +
        ((n : ℝ[X]) + 1) * C s * (X + 1) * (X * (Q (n + 2)).derivative) -
        ((n : ℝ[X]) + 2) * (C 2 * X + 1) *
          ((C 2 * X + 1) * Q (n + 1) + C s * (X + 1) * (X * (Q (n + 1)).derivative))) (n : ℕ) :
    IsRealRootedIn (Ioo (-1 : ℝ) 0) (Q n) ∧ HasSimpleRoots (Q n) ∧
      StrictInterl (Q n) (Q (n + 1)) := by
  set α := s / 2 with hα
  set r := (κ - 4) / (2 * s) with hr
  have hspos : 0 < s := by linarith
  have hs2 : 2 * α = s := by rw [hα]; ring
  have hαhalf : 1 / 2 ≤ α := by rw [hα]; linarith
  have hrhalf : 1 / 2 ≤ r := by
    rw [hr, le_div_iff₀ (by positivity)]
    linarith
  have hrpos : 0 < r := by linarith
  have hκr : κ = 4 * (r * α) + 4 := by
    rw [hr, hα]
    field_simp
    ring
  -- The sequence is the perturbed orbit.
  have hR0 := orbitPerturbationRow_zero α r
  have hR1 := orbitPerturbationRow_one α r
  have hR2 : orbitPerturbationRow α r 2 = C κ * X ^ 2 + C κ * X + 1 := by
    simp [orbitPerturbationRow, centeredEulerStep, hκr, map_ofNat]
    ring
  have hQ : ∀ m, Q m = orbitPerturbationRow α r m ∧ Q (m + 1) = orbitPerturbationRow α r (m + 1) ∧
      Q (m + 2) = orbitPerturbationRow α r (m + 2) := by
    intro m
    induction m with
    | zero => exact ⟨h0.trans hR0.symm, h1.trans hR1.symm, h2.trans hR2.symm⟩
    | succ m ih =>
        refine ⟨ih.2.1, ih.2.2, ?_⟩
        have hne : ((m : ℝ[X]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        apply mul_left_cancel₀ hne
        change ((m : ℝ[X]) + 1) * Q (m + 3) = ((m : ℝ[X]) + 1) * orbitPerturbationRow α r (m + 3)
        rw [hrec m, orbitPerturbationRow_recurrence, ih.2.1, ih.2.2, hs2]
  rw [(hQ n).1, (hQ (n + 1)).1]
  exact orbitPerturbationRow_package hαhalf hrhalf n

end RealRooted
