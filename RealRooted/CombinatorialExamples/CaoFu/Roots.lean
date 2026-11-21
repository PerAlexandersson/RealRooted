module

public import RealRooted.CombinatorialExamples.CaoFu.Basic
public import Mathlib.Algebra.Polynomial.Splits
import RealRooted.RootCounting.Pencil
import Mathlib.Tactic

/-!
# Cao–Fu real-rootedness reduced to strict comparisons

The reduction below formalizes Lemma 4.1 of Cao–Fu,
*Real-rooted Ehrhart h*-polynomials of crown posets and wheel and whirl matroids*,
arXiv:2610.40496v1. Its remaining hypothesis is exactly a finite grid of strict
comparisons, the analytic input supplied by Lemmas 4.2–4.5 of that paper.
The general-rank comparison estimates remain open in RealRooted issue #2189.
The polynomial conclusion, including simplicity, is derived from the grid;
no real-rootedness assumption is used.
-/

public section

open Polynomial

namespace RealRooted.CaoFu

/-- Strict comparison points on `[-1,0]` imply the full polynomial conclusion
of Cao–Fu, Theorems 1.1–1.2. Here `n` is the rank minus two. The analytic
comparison estimates remain the explicit boundary tracked in issue #2189. -/
theorem pencil_roots_of_sign_domination {n : ℕ} (hn : n ≠ 0)
    (x : Fin (n + 2) → ℝ) (hx : StrictMono x)
    (hleft : x 0 = -1) (hright : x (Fin.last (n + 1)) = 0)
    (hdom : ∀ i, |(correction n).eval (x i)| <
      (-1 : ℝ) ^ (n + 1 - i.val) * (crownPolynomial n).eval (x i))
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam₁ : lam ≤ 1) :
    (pencil n lam).natDegree = 2 * (n + 1) ∧ (pencil n lam).Splits ∧
      (pencil n lam).roots.Nodup ∧ ∀ z ∈ (pencil n lam).roots, z < 0 := by
  apply RootCounting.splits_nodup_neg_of_pencil_sign_domination
    (crownPolynomial_natDegree_le n)
    ((correction_natDegree_le n).trans (by lia))
    (by rw [← coeff_zero_eq_eval_zero, crownPolynomial_coeff_zero]; norm_num)
    (correction_eval_zero n)
    (crownPolynomial_reflect n) x hx hleft hright hdom _ hlam hlam₁
  intro i
  apply abs_correction_reflect_le hn
  · rw [← hleft]
    exact hx.monotone (Fin.zero_le i)
  · rw [← hright]
    exact hx.monotone (Fin.le_last i)

end RealRooted.CaoFu
