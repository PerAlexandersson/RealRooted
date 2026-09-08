import Mathlib.Data.Matrix.Basic

/-!
# The classical Hurwitz matrix

This file defines the infinite Hurwitz matrix of a coefficient sequence in the
constant-term-first convention. Its first rows are

```text
c 0, c 2, c 4, ...
0, c 1, c 3, ...
0, c 0, c 2, ...
0, 0, c 1, ...
```

This is the convention used in the classical Routh--Hurwitz criterion. It is
not the lower-triangular Lace-oriented matrix historically called `hurwitz` in
the `RealRooted` namespace.
-/

namespace Matrix

variable {R : Type*} [Zero R]

/-- The infinite classical Hurwitz matrix of a coefficient sequence
`c 0, c 1, ...`, with coefficients indexed from the constant term upward. -/
def hurwitz (c : ℕ → R) : Matrix ℕ ℕ R := fun i j =>
  if i ≤ 2 * j then c (2 * j - i) else 0

@[simp]
theorem hurwitz_apply (c : ℕ → R) (i j : ℕ) :
    hurwitz c i j = if i ≤ 2 * j then c (2 * j - i) else 0 :=
  rfl

@[simp]
theorem hurwitz_zero : hurwitz (0 : ℕ → R) = 0 := by
  ext i j
  simp [hurwitz]

/-- The even rows contain the even coefficients, shifted to the right. -/
theorem hurwitz_even_row_apply (c : ℕ → R) (i j : ℕ) :
    hurwitz c (2 * i) j = if i ≤ j then c (2 * (j - i)) else 0 := by
  simp only [hurwitz_apply]
  split_ifs with h₁ h₂
  · congr 1
    lia
  · lia
  · lia
  · rfl

/-- The odd rows contain the odd coefficients, shifted one place farther to
the right than the corresponding even row. -/
theorem hurwitz_odd_row_apply (c : ℕ → R) (i j : ℕ) :
    hurwitz c (2 * i + 1) j =
      if i < j then c (2 * (j - (i + 1)) + 1) else 0 := by
  simp only [hurwitz_apply]
  split_ifs with h₁ h₂
  · congr 1
    lia
  · lia
  · lia
  · rfl

/-- Entries strictly below the doubled column index staircase vanish. -/
theorem hurwitz_apply_eq_zero_of_two_mul_lt (c : ℕ → R) {i j : ℕ}
    (h : 2 * j < i) : hurwitz c i j = 0 := by
  simp [hurwitz, show ¬ i ≤ 2 * j by lia]

/-- The finite leading principal section of the infinite classical Hurwitz
matrix. -/
def hurwitzLeadingPrincipal (c : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  (hurwitz c).submatrix (fun i => i) (fun j => j)

@[simp]
theorem hurwitzLeadingPrincipal_apply (c : ℕ → R) (n : ℕ)
    (i j : Fin n) :
    hurwitzLeadingPrincipal c n i j =
      if (i : ℕ) ≤ 2 * (j : ℕ) then c (2 * (j : ℕ) - (i : ℕ)) else 0 :=
  rfl

/-- The order-`n` leading principal section depends only on coefficient
indices strictly below `2 * n`. -/
theorem hurwitzLeadingPrincipal_congr {c d : ℕ → R} {n : ℕ}
    (h : ∀ k < 2 * n, c k = d k) :
    hurwitzLeadingPrincipal c n = hurwitzLeadingPrincipal d n := by
  ext i j
  simp only [hurwitzLeadingPrincipal_apply]
  split_ifs
  · apply h
    have hj := j.isLt
    lia
  · rfl

end Matrix
