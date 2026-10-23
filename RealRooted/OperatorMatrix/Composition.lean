import RealRooted.OperatorMatrix.LocalToGlobal

/-!
# Composition of ordered-PF operator matrices

Matrix multiplication composes matrices of polynomial endomorphisms in the
same order as their actions on polynomial vectors.  Consequently, ordered-PF
preservers are closed under multiplication and powers.
-/

open Polynomial

noncomputable section

namespace RealRooted.OperatorMatrix

/-- The action of a product of operator matrices is the composite action. -/
theorem apply_mul {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) (Module.End ℝ ℝ[X]))
    (B : Matrix (Fin n) (Fin r) (Module.End ℝ ℝ[X]))
    (f : Fin r → ℝ[X]) :
    apply (A * B) f = apply A (apply B f) := by
  classical
  funext i
  simp only [apply, Matrix.mul_apply, Finset.sum_apply, Module.End.mul_apply,
    map_sum]
  rw [Finset.sum_comm]

/-- The identity operator matrix acts as the identity on polynomial vectors. -/
@[simp]
theorem apply_one {n : ℕ} (f : Fin n → ℝ[X]) :
    apply (1 : Matrix (Fin n) (Fin n) (Module.End ℝ ℝ[X])) f = f := by
  classical
  funext i
  simp [apply, Matrix.one_apply]

/-- The identity operator matrix preserves ordered PF vectors. -/
theorem preservesOrderedPF_one {n : ℕ} :
    PreservesOrderedPF (1 : Matrix (Fin n) (Fin n) (Module.End ℝ ℝ[X])) := by
  intro f hf
  simpa using hf

/-- A product of ordered-PF-preserving operator matrices preserves ordered PF vectors. -/
protected theorem PreservesOrderedPF.mul {m n r : ℕ}
    {A : Matrix (Fin m) (Fin n) (Module.End ℝ ℝ[X]))}
    {B : Matrix (Fin n) (Fin r) (Module.End ℝ ℝ[X]))}
    (hA : PreservesOrderedPF A) (hB : PreservesOrderedPF B) :
    PreservesOrderedPF (A * B) := by
  intro f hf
  rw [apply_mul]
  exact hA _ (hB _ hf)

/-- Every power of an ordered-PF-preserving square operator matrix preserves ordered PF vectors. -/
protected theorem PreservesOrderedPF.pow {n : ℕ}
    {M : Matrix (Fin n) (Fin n) (Module.End ℝ ℝ[X]))}
    (hM : PreservesOrderedPF M) (k : ℕ) :
    PreservesOrderedPF (M ^ k) := by
  induction k with
  | zero => simpa using (preservesOrderedPF_one (n := n))
  | succ k ih =>
      rw [pow_succ]
      exact ih.mul hM

end RealRooted.OperatorMatrix
