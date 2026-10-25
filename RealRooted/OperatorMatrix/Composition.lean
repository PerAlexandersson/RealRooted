module

public import RealRooted.OperatorMatrix.LocalToGlobal

/-!
# Composition of ordered-PF operator matrices

Matrix multiplication composes matrices of polynomial endomorphisms in the
same order as their actions on polynomial vectors.  Consequently, ordered-PF
preservers are closed under multiplication and powers.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.OperatorMatrix

/-- A two-coordinate vector is ordered PF exactly when its coordinates are PF and interlace. -/
theorem isOrderedPF_pair_iff (p q : ℝ[X]) :
    IsOrderedPF ![p, q] ↔
      IsPFPolynomial p ∧ IsPFPolynomial q ∧ Interl p q := by
  constructor
  · intro h
    exact ⟨h.1 0, h.1 1, h.2 0 1 (by decide)⟩
  · rintro ⟨hp, hq, hpq⟩
    constructor
    · intro i
      fin_cases i <;> assumption
    · intro i k hik
      fin_cases i <;> fin_cases k <;> simp_all

/-- A two-by-two operator matrix preserves ordered PF vectors exactly when its four entries
preserve ordered PF pairs. -/
theorem preservesOrderedPF_two_two_iff
    (M : Matrix (Fin 2) (Fin 2) (Module.End ℝ ℝ[X])) :
    PreservesOrderedPF M ↔ PreservesOrderedPFPair (M 0 0) (M 0 1) (M 1 0) (M 1 1) := by
  rw [preservesOrderedPF_iff_preservesBlock_of_two_le M (by decide) (by decide)]
  constructor
  · intro h
    exact h 0 1 0 1 (by decide) (by decide)
  · intro h i k j l hik hjl
    fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
      simp_all [PreservesBlock]

/-- The action of a product of operator matrices is the composite action. -/
theorem apply_mul {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) (Module.End ℝ ℝ[X]))
    (B : Matrix (Fin n) (Fin r) (Module.End ℝ ℝ[X]))
    (f : Fin r → ℝ[X]) :
    apply (A * B) f = apply A (apply B f) := by
  classical
  funext i
  simp only [apply, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply,
    map_sum]
  rw [Finset.sum_comm]

/-- The identity operator matrix acts as the identity on polynomial vectors. -/
@[simp]
theorem apply_one {n : ℕ} (f : Fin n → ℝ[X]) :
    apply (1 : Matrix (Fin n) (Fin n) (Module.End ℝ ℝ[X])) f = f := by
  classical
  funext i
  simp only [apply, Matrix.one_apply]
  calc
    (∑ j : Fin n, (if i = j then (1 : Module.End ℝ ℝ[X]) else 0) (f j)) =
        ∑ j : Fin n, if j = i then f j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp
      · have hij : i ≠ j := fun h => hji h.symm
        simp [hji, hij]
    _ = f i := by
      rw [Finset.sum_ite_eq']
      simp

/-- The identity operator matrix preserves ordered PF vectors. -/
theorem preservesOrderedPF_one {n : ℕ} :
    PreservesOrderedPF (1 : Matrix (Fin n) (Fin n) (Module.End ℝ ℝ[X])) := by
  intro f hf
  simpa using hf

/-- A product of ordered-PF-preserving operator matrices preserves ordered PF vectors. -/
protected theorem PreservesOrderedPF.mul {m n r : ℕ}
    {A : Matrix (Fin m) (Fin n) (Module.End ℝ ℝ[X])}
    {B : Matrix (Fin n) (Fin r) (Module.End ℝ ℝ[X])}
    (hA : PreservesOrderedPF A) (hB : PreservesOrderedPF B) :
    PreservesOrderedPF (A * B) := by
  intro f hf
  rw [apply_mul]
  exact hA _ (hB _ hf)

/-- Every power of an ordered-PF-preserving square operator matrix preserves ordered PF vectors. -/
protected theorem PreservesOrderedPF.pow {n : ℕ}
    {M : Matrix (Fin n) (Fin n) (Module.End ℝ ℝ[X])}
    (hM : PreservesOrderedPF M) (k : ℕ) :
    PreservesOrderedPF (M ^ k) := by
  induction k with
  | zero => simpa using (preservesOrderedPF_one (n := n))
  | succ k ih =>
      rw [pow_succ]
      exact ih.mul hM

end RealRooted.OperatorMatrix
