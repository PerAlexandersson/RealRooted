import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Reverse
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

/-!
# Laguerre's theorem on polar derivatives

For `f : R[X]` of degree `n` and `a : R`, the *polar derivative* of `f` with respect to `a` is
`D_a f = n • f + (a - X) * f'`.  Laguerre's theorem (real-line form) states that if a real
polynomial `f` splits over `ℝ`, then so does `D_a f` for every real `a`.

## Proof

Translate `a` to `0`: with `g = f.comp (X + C a)` we get
`(D_a f).comp (X + C a) = n • g - X * g'`.  On coefficients `n • g - X * g'` multiplies the
coefficient of `X ^ i` by `n - i`, so it equals `reflect (n - 1) (derivative (reflect n g))`.
Reversal preserves splitting over a field, and over `ℝ` the derivative of a split polynomial
splits by Rolle's theorem (`Polynomial.card_roots_le_derivative`).

## Main results

* `Polynomial.polarDerivative`: the polar derivative.
* `Polynomial.Splits.derivative_of_real`: Rolle's theorem in splitting form.
* `Polynomial.splits_polarDerivative_of_splits`, `Polynomial.Splits.polarDerivative`:
  Laguerre's theorem.
-/

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The polar derivative `n • f + (a - X) * f'` of `f` with respect to `a`,
where `n = f.natDegree`. -/
noncomputable def polarDerivative (a : R) (f : R[X]) : R[X] :=
  C (f.natDegree : R) * f + (C a - X) * derivative f

/-- Rolle's theorem in splitting form: the derivative of a real polynomial that splits
over `ℝ` splits. -/
theorem Splits.derivative_of_real {f : ℝ[X]} (hf : f.Splits) : (derivative f).Splits := by
  rw [splits_iff_card_roots] at hf ⊢
  have h1 := card_roots_le_derivative f
  have h2 := card_roots' (derivative f)
  have h3 := natDegree_derivative_le f
  lia

/-- The polar derivative with respect to `0`, written as a reflected derivative of a
reflection. -/
theorem C_mul_sub_X_mul_derivative_eq_reflect {g : R[X]} {n : ℕ} (hg : g.natDegree ≤ n) :
    C (n : R) * g - X * derivative g = reflect (n - 1) (derivative (reflect n g)) := by
  ext i
  rw [coeff_sub, coeff_C_mul, coeff_X_mul_derivative, coeff_reflect, coeff_derivative,
    coeff_reflect]
  rcases lt_or_ge i n with hi | hi
  · obtain ⟨k, rfl⟩ : ∃ k, n = i + k + 1 := ⟨n - i - 1, by lia⟩
    rw [Nat.add_sub_cancel, revAt_le (show i ≤ i + k by lia), Nat.add_sub_cancel_left,
      revAt_le (show k + 1 ≤ i + k + 1 by lia), show i + k + 1 - (k + 1) = i by lia]
    push_cast
    ring
  · have hr : n < revAt (n - 1) i + 1 := by
      rcases Nat.lt_or_ge (n - 1) i with h | h
      · rw [revAt_eq_self_of_lt h]
        lia
      · rw [revAt_le h]
        lia
    rw [revAt_eq_self_of_lt hr, coeff_eq_zero_of_natDegree_lt (hg.trans_lt hr), zero_mul]
    rcases hi.lt_or_eq with hi | rfl
    · rw [coeff_eq_zero_of_natDegree_lt (hg.trans_lt hi)]
      ring
    · ring

theorem polarDerivative_comp_X_add_C (a : R) (f : R[X]) :
    (polarDerivative a f).comp (X + C a) =
      C (f.natDegree : R) * f.comp (X + C a) - X * derivative (f.comp (X + C a)) := by
  simp only [polarDerivative, add_comp, mul_comp, C_comp, sub_comp, X_comp, derivative_comp,
    derivative_add, derivative_X, derivative_C, add_zero, one_mul]
  ring

/-- **Laguerre's theorem** on polar derivatives: if a real polynomial `f` splits over `ℝ`,
then so does its polar derivative with respect to any real `a`. -/
theorem splits_polarDerivative_of_splits {f : ℝ[X]} (hf : f.Splits) (a : ℝ) :
    (polarDerivative a f).Splits := by
  set g := f.comp (X + C a)
  have hdeg : g.natDegree = f.natDegree := by
    simp [g, natDegree_comp]
  have hs : ((polarDerivative a f).comp (X + C a)).Splits := by
    rw [polarDerivative_comp_X_add_C, C_mul_sub_X_mul_derivative_eq_reflect hdeg.le, ← hdeg]
    refine Splits.reflect ?_ ?_
    · exact (hf.comp_X_add_C a).reverse.derivative_of_real
    · exact (natDegree_derivative_le _).trans (Nat.sub_le_sub_right (reverse_natDegree_le g) 1)
  have h := hs.comp_X_sub_C a
  rwa [comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X] at h

/-- **Laguerre's theorem** on polar derivatives (real-line form): if `f` splits over `ℝ`,
then the polar derivative of `f` with respect to `a` is zero or splits. -/
theorem Splits.polarDerivative {f : ℝ[X]} (hf : f.Splits) (a : ℝ) :
    polarDerivative a f = 0 ∨ (polarDerivative a f).Splits :=
  Or.inr (splits_polarDerivative_of_splits hf a)

end Polynomial
