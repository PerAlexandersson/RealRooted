import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import RealRooted.Mathlib.Algebra.MvPolynomial.Homogenize
import RealRooted.MultivariateStability

/-!
# Homogeneous harmonic substitution

This file clears the denominators in the harmonic substitution appearing in
Brändén--Ferroni--Jochemko's stability proof for polynomial-value products.
-/

namespace MvPolynomial

noncomputable section

/-- The denominator-cleared harmonic substitution in two variables. The
adjoined `none` variable is the common auxiliary variable. -/
def harmonicClear {R : Type*} [CommSemiring R] (Q : MvPolynomial (Fin 2) R) :
    MvPolynomial (Option (Fin 2)) R :=
  aeval ![
    X (some 0) * X none * (X (some 1) + X none),
    X (some 1) * X none * (X (some 0) + X none)] Q

/-- Evaluation of `harmonicClear` is the homogeneous harmonic substitution
multiplied by its common denominator. -/
theorem eval_harmonicClear {Q : MvPolynomial (Fin 2) ℂ} {b : ℕ}
    (hQ : Q.IsHomogeneous b) (x y z : ℂ)
    (hxz : x + z ≠ 0) (hyz : y + z ≠ 0) :
    eval (fun o => Option.elim o z ![x, y]) (harmonicClear Q) =
      ((x + z) * (y + z)) ^ b *
        eval ![x * z / (x + z), y * z / (y + z)] Q := by
  let d := (x + z) * (y + z)
  let u : Fin 2 → ℂ := ![x * z / (x + z), y * z / (y + z)]
  calc
    eval (fun o => Option.elim o z ![x, y]) (harmonicClear Q) =
        eval ![x * z * (y + z), y * z * (x + z)] Q := by
      change aeval (fun o => Option.elim o z ![x, y])
          (aeval _ Q) = _
      rw [comp_aeval_apply]
      change eval _ Q = eval _ Q
      apply congrArg (fun v : Fin 2 → ℂ => eval v Q)
      funext i
      fin_cases i <;> simp
    _ = eval (fun i => d * u i) Q := by
      apply congrArg (fun v : Fin 2 → ℂ => eval v Q)
      funext i
      fin_cases i <;> simp [d, u] <;> field_simp [hxz, hyz]
    _ = d ^ b * eval u Q := hQ.eval_smul d u
    _ = ((x + z) * (y + z)) ^ b *
        eval ![x * z / (x + z), y * z / (y + z)] Q := rfl

end

end MvPolynomial

namespace RealRooted

noncomputable section

/-- Homogeneous denominator-cleared harmonic substitution preserves
upper-half-plane stability. -/
theorem MvUpperHalfPlaneStable.harmonicClear
    {Q : MvPolynomial (Fin 2) ℂ} {b : ℕ}
    (hQ : MvUpperHalfPlaneStable Q) (hhom : Q.IsHomogeneous b) :
    MvUpperHalfPlaneStable (MvPolynomial.harmonicClear Q) := by
  intro w hw
  let x := w (some 0)
  let y := w (some 1)
  let z := w none
  have hx : 0 < x.im := hw (some 0)
  have hy : 0 < y.im := hw (some 1)
  have hz : 0 < z.im := hw none
  have hxz : x + z ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp [x, z] at him
    linarith
  have hyz : y + z ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp [y, z] at him
    linarith
  have hw_eq : w = fun o => Option.elim o z ![x, y] := by
    funext o
    cases o with
    | none => rfl
    | some i => fin_cases i <;> rfl
  rw [hw_eq, MvPolynomial.eval_harmonicClear hhom x y z hxz hyz]
  apply mul_ne_zero (pow_ne_zero b (mul_ne_zero hxz hyz))
  apply hQ
  intro i
  fin_cases i
  · exact Complex.mul_div_add_im_pos hx hz
  · exact Complex.mul_div_add_im_pos hy hz

end

end RealRooted
