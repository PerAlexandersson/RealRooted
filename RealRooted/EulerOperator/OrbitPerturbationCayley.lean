module

public import RealRooted.EulerOperator.OrbitPerturbationFamily
public import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Basic
public import RealRooted.GeneralizedEulerian
import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Algebra
import RealRooted.PolynomialValueEulerNumerator.Interlacing
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

/-!
# The perturbed centered Euler orbit in Eulerian coordinates

The Cayley transform `T_n f = (1 - X) ^ n f (X / (1 - X))` maps the rows `Q n` of
`RealRooted.EulerOperator.OrbitPerturbationFamily` to Eulerian-type rows.  With `s = 2 α`, the
transformed orbit `E n = T_n (p n (2 u + 1))` satisfies `E 0 = 1` and

    E (n + 1) = (1 + (1 + s n) X) E n + s X (1 - X) E n'

(for `s = 1` these are the Eulerian polynomials), and `T_n (2 u + 1) ^ n = (1 + X) ^ n`.  Hence
for `s ≥ 1` and `c ≥ 1 / 2` the rows `c E n + (1 - c) (1 + X) ^ n` are real-rooted
(`splits_C_mul_add_C_mul_one_add_X_pow_of_recurrence`).  This is the form of RealRooted #2513,
Theorem 1, that matches the OEIS triangles A141689, A141690, A141696, A141697 (`s = 1`,
`c = 1/2, 2, 3, 7`) and A147565 (`s = 2`, `c = 1/2`).
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- The centered Euler orbit in Eulerian coordinates: the degree-`n` Cayley transform of
`p n (2 u + 1)`. -/
def cayleyEulerOrbit (α : ℝ) (n : ℕ) : ℝ[X] :=
  cayleyTransform n ((centeredEulerOrbit α n).comp (C 2 * X + C 1))

/-- The orbit in the variable `u` has degree at most `n`. -/
private theorem natDegree_centeredEulerOrbit_comp_le {α : ℝ} (hα : 0 < α) (n : ℕ) :
    ((centeredEulerOrbit α n).comp (C 2 * X + C 1)).natDegree ≤ n := by
  refine natDegree_comp_le.trans ?_
  rw [centeredEulerOrbit_natDegree hα n]
  have h : (C 2 * X + C 1 : ℝ[X]).natDegree ≤ 1 := by compute_degree
  nlinarith

@[simp] theorem cayleyEulerOrbit_zero (α : ℝ) : cayleyEulerOrbit α 0 = 1 := by
  simpa [cayleyEulerOrbit] using cayleyTransform_X_pow (R := ℝ) (n := 0) (k := 0) le_rfl

/-- The Eulerian-type recurrence `E (n + 1) = (1 + (1 + 2 α n) X) E n + 2 α X (1 - X) E n'`. -/
theorem cayleyEulerOrbit_succ {α : ℝ} (hα : 0 < α) (n : ℕ) :
    cayleyEulerOrbit α (n + 1) =
      (1 + C (1 + 2 * α * n) * X) * cayleyEulerOrbit α n +
        C (2 * α) * X * (1 - X) * (cayleyEulerOrbit α n).derivative := by
  have hdeg := natDegree_centeredEulerOrbit_comp_le hα n
  unfold cayleyEulerOrbit
  rw [centeredEulerOrbit_succ, centeredEulerStep_comp_two_mul_X_add_one]
  generalize (centeredEulerOrbit α n).comp (C 2 * X + C 1) = P at hdeg ⊢
  have hθ : (X * P.derivative).natDegree ≤ n := by
    by_cases hP : P.derivative = 0
    · simp [hP]
    have hlt := natDegree_derivative_lt (p := P) fun h ↦ hP (derivative_of_natDegree_zero h)
    have hX : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
    have := natDegree_mul_le (p := (X : ℝ[X])) (q := P.derivative)
    lia
  rw [show (C 2 * X + C 1) * P + C (2 * α) * (X + 1) * (X * P.derivative) =
      C 2 * (X * P) + C 1 * P + C (2 * α) * (X * (X * P.derivative) + X * P.derivative) by ring]
  rw [cayleyTransform_add, cayleyTransform_add, cayleyTransform_C_mul, cayleyTransform_C_mul,
    cayleyTransform_C_mul, cayleyTransform_add, cayleyTransform_succ_X_mul hdeg,
    cayleyTransform_succ hdeg, cayleyTransform_succ_X_mul hθ, cayleyTransform_succ hθ,
    cayleyTransform_X_mul_derivative hdeg]
  simp only [map_add, map_mul, map_one, map_natCast, map_ofNat]
  ring

/-- The Cayley transform of the perturbed row `Q n` is `c E n + (1 - c) (1 + X) ^ n`. -/
theorem cayleyTransform_orbitPerturbationRow (α c : ℝ) (n : ℕ) :
    cayleyTransform n (orbitPerturbationRow α c n) =
      C c * cayleyEulerOrbit α n + C (1 - c) * (1 + X) ^ n := by
  have hY : cayleyTransform n ((C 2 * X + C 1 : ℝ[X]) ^ n) = (1 + X) ^ n := by
    rw [show (C 2 * X + C 1 : ℝ[X]) = 1 + C 2 * X by rw [map_one]; ring]
    exact cayleyTransform_twoPascal n
  rw [orbitPerturbationRow_eq, cayleyTransform_add, cayleyTransform_C_mul, cayleyTransform_C_mul,
    hY, cayleyEulerOrbit]

/-- A sequence with the seed and recurrence of the transformed orbit is the transformed orbit. -/
private theorem eq_cayleyEulerOrbit_of_recurrence {s : ℝ} (hs : 0 < s) {E : ℕ → ℝ[X]}
    (h0 : E 0 = 1)
    (hrec : ∀ n : ℕ, E (n + 1) =
      (1 + C (1 + s * n) * X) * E n + C s * X * (1 - X) * (E n).derivative) (n : ℕ) :
    E n = cayleyEulerOrbit (s / 2) n := by
  induction n with
  | zero => rw [h0, cayleyEulerOrbit_zero]
  | succ m ih =>
      rw [hrec m, cayleyEulerOrbit_succ (by linarith), ih, show 2 * (s / 2) = s by ring]

/-- **Eulerian form of RealRooted #2513, Theorem 1.**  Let `s ≥ 1` and `c ≥ 1 / 2`, and let
`E 0 = 1` and `E (n + 1) = (1 + (1 + s n) X) E n + s X (1 - X) E n'`.  Then the rows
`A n = c E n + (1 - c) (1 + X) ^ n` are real-rooted, with roots `≤ 0`, and `A n` strictly
interlaces `A (n + 1)`. -/
theorem strictInterl_C_mul_add_C_mul_one_add_X_pow_of_recurrence {s c : ℝ} (hs : 1 ≤ s)
    (hc : 1 / 2 ≤ c) {E : ℕ → ℝ[X]} (h0 : E 0 = 1)
    (hrec : ∀ n : ℕ, E (n + 1) =
      (1 + C (1 + s * n) * X) * E n + C s * X * (1 - X) * (E n).derivative) (n : ℕ) :
    StrictInterl (C c * E n + C (1 - c) * (1 + X) ^ n)
      (C c * E (n + 1) + C (1 - c) * (1 + X) ^ (n + 1)) := by
  have hE := eq_cayleyEulerOrbit_of_recurrence (by linarith) h0 hrec
  rw [hE n, hE (n + 1), ← cayleyTransform_orbitPerturbationRow,
    ← cayleyTransform_orbitPerturbationRow]
  obtain ⟨hdeg, hroot, -, hint⟩ := orbitPerturbationRow_package (α := s / 2) (by linarith) hc n
  obtain ⟨hdeg1, hroot1, -⟩ := orbitPerturbationRow_package (α := s / 2) (by linarith) hc (n + 1)
  exact strictInterl_cayleyTransform_succ_of_roots_mem_Icc hdeg hdeg1 hint
    (fun r hr ↦ ⟨(hroot.2.2 r hr).1.le, (hroot.2.2 r hr).2.le⟩)
    (fun r hr ↦ ⟨(hroot1.2.2 r hr).1.le, (hroot1.2.2 r hr).2.le⟩)

/-- Real-rootedness in the Eulerian form of RealRooted #2513, Theorem 1: for `s ≥ 1` and
`c ≥ 1 / 2`, every row `c E n + (1 - c) (1 + X) ^ n` splits. -/
theorem splits_C_mul_add_C_mul_one_add_X_pow_of_recurrence {s c : ℝ} (hs : 1 ≤ s)
    (hc : 1 / 2 ≤ c) {E : ℕ → ℝ[X]} (h0 : E 0 = 1)
    (hrec : ∀ n : ℕ, E (n + 1) =
      (1 + C (1 + s * n) * X) * E n + C s * X * (1 - X) * (E n).derivative) (n : ℕ) :
    (C c * E n + C (1 - c) * (1 + X) ^ n).Splits :=
  (strictInterl_C_mul_add_C_mul_one_add_X_pow_of_recurrence hs hc h0 hrec n).1.2


/-- The transformed orbit is the generalized Eulerian polynomial with parameter `2 α`. -/
theorem cayleyEulerOrbit_eq_generalizedEulerian {α : ℝ} (hα : 0 < α) (n : ℕ) :
    cayleyEulerOrbit α n = generalizedEulerian (2 * α) n := by
  induction n with
  | zero => rw [cayleyEulerOrbit_zero]; rfl
  | succ n ih =>
      rw [cayleyEulerOrbit_succ hα, ih, generalizedEulerian_succ, add_comm (1 : ℝ),
        mul_assoc]

/-- Perturbed generalized Eulerian polynomials: for `s ≥ 1` and `c ≥ 1 / 2`, the rows
`c A_n^{(s)} + (1 - c) (1 + X) ^ n` interlace strictly (RealRooted #2513, Theorem 1). -/
theorem strictInterl_C_mul_generalizedEulerian_add {s c : ℝ} (hs : 1 ≤ s) (hc : 1 / 2 ≤ c)
    (n : ℕ) :
    StrictInterl (C c * generalizedEulerian s n + C (1 - c) * (1 + X) ^ n)
      (C c * generalizedEulerian s (n + 1) + C (1 - c) * (1 + X) ^ (n + 1)) :=
  strictInterl_C_mul_add_C_mul_one_add_X_pow_of_recurrence hs hc rfl
    (fun n ↦ by rw [generalizedEulerian_succ, add_comm (s * n)]) n

end RealRooted
