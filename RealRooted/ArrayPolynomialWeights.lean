import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace RealRooted

/-!
# Normalized inclusion-exclusion weights for the array-counting polynomials

Let `t (n, k)` be the array count behind the real-rootedness argument for
`A262704`, given by inclusion-exclusion as

```text
t (n, k) = ∑ j, (-1) ^ j * n.choose j * ((n - j).choose (k - j)) ^ 3.
```

Dividing by the cube of the falling factorial `(n)_k` turns this into a
convolution against `fun m => 1 / m ! ^ 3`, with weights

```text
cWeight n j = (-1) ^ j * (n - j)! ^ 2 / (n ! ^ 2 * j !).
```

Indeed, `n.choose j * ((n-j).choose (k-j)) ^ 3 / (n)_k ^ 3` simplifies to
`(n - j)! ^ 2 / (n ! ^ 2 * j ! * (k - j)! ^ 3)`.  So the three-term recurrence
of the normalized row polynomials,

```text
D n = D (n-1) + α n * q * D (n-2) + β n * q ^ 2 * D (n-3),
```

is inherited by linearity from a recurrence for `cWeight` alone.  This file
proves that weight recurrence.

Writing the index as `n = j + i + 3` removes every natural subtraction, and the
recurrence then collapses to the polynomial identity `cWeight_key_identity`,

```text
(i + 1) ^ 2 = (j + i + 3) ^ 2 - (2 * j + 2 * i + 5) * (j + 2) + (j + 2) * (j + 1).
```

The two low-index cases `j = 0` and `j = 1` are stated separately, because the
recurrence there refers to weights at negative index, which are zero by
convention rather than by the natural-subtraction reading of `cWeight`.  Note
that `cWeight n j` is **not** zero for `j > n`: the natural subtraction `n - j`
collapses to `0`.  Every use below keeps `j < n`, which is automatic in the
`j + i + 3` parametrization.
-/

/-- The normalized inclusion-exclusion weight
`cWeight n j = (-1) ^ j * (n - j)! ^ 2 / (n ! ^ 2 * j !)`. -/
def cWeight (n j : ℕ) : ℝ :=
  (-1) ^ j * (Nat.factorial (n - j) : ℝ) ^ 2 /
    ((Nat.factorial n : ℝ) ^ 2 * (Nat.factorial j : ℝ))

/-- First recurrence coefficient, `α n = (2 * n - 1) / (n ^ 2 * (n - 1) ^ 2)`. -/
def alphaC (n : ℕ) : ℝ :=
  (2 * (n : ℝ) - 1) / ((n : ℝ) ^ 2 * ((n : ℝ) - 1) ^ 2)

/-- Second recurrence coefficient,
`β n = 1 / (n ^ 2 * (n - 1) ^ 2 * (n - 2) ^ 2)`. -/
def betaC (n : ℕ) : ℝ :=
  1 / ((n : ℝ) ^ 2 * ((n : ℝ) - 1) ^ 2 * ((n : ℝ) - 2) ^ 2)

private theorem factorial_cast_ne_zero (m : ℕ) : (Nat.factorial m : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)

@[simp] theorem cWeight_zero_index (n : ℕ) : cWeight n 0 = 1 := by
  have h : (Nat.factorial n : ℝ) ≠ 0 := factorial_cast_ne_zero n
  unfold cWeight
  simp only [Nat.sub_zero, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, mul_one]
  exact div_self (pow_ne_zero 2 h)

/-- The weight at index one, `cWeight n 1 = -1 / n ^ 2`. -/
theorem cWeight_one_index (n : ℕ) (hn : 1 ≤ n) :
    cWeight n 1 = -1 / ((n : ℝ)) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : (Nat.factorial m : ℝ) ≠ 0 := factorial_cast_ne_zero m
  have h1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  unfold cWeight
  rw [show m + 1 - 1 = m from rfl, Nat.factorial_succ]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one, Nat.cast_mul, Nat.cast_add]
  field_simp

/-- The arithmetic core of the weight recurrence: once the factorials are
cleared, the whole identity is this polynomial identity. -/
theorem cWeight_key_identity (i j : ℕ) :
    ((i : ℝ) + 1) ^ 2
      = ((j : ℝ) + i + 3) ^ 2 - (2 * j + 2 * i + 5) * (j + 2)
          + ((j : ℝ) + 2) * (j + 1) := by
  ring

/-- The weight recurrence at index zero.  Both sides equal `1`; the shifted
terms of the general recurrence carry negative index and vanish. -/
theorem cWeight_recurrence_zero (m : ℕ) : cWeight (m + 3) 0 = cWeight (m + 2) 0 := by
  simp

/-- The weight recurrence at index one.  Only the `α` term survives, since the
`β` term of the general recurrence carries negative index. -/
theorem cWeight_recurrence_one (m : ℕ) :
    cWeight (m + 3) 1 = cWeight (m + 2) 1 + alphaC (m + 3) * cWeight (m + 1) 0 := by
  have h1 : ((m : ℝ) + 2) ≠ 0 := by positivity
  have h2 : ((m : ℝ) + 3) ≠ 0 := by positivity
  rw [cWeight_one_index (m + 3) (by omega), cWeight_one_index (m + 2) (by omega),
    cWeight_zero_index]
  have hA : alphaC (m + 3)
      = (2 * ((m : ℝ) + 3) - 1) / (((m : ℝ) + 3) ^ 2 * ((m : ℝ) + 2) ^ 2) := by
    unfold alphaC; push_cast; ring
  rw [hA]
  push_cast
  field_simp
  ring

/-- **The weight recurrence.**  For `n = j + i + 3`, so that the index `j + 2`
stays below `n`, the normalized inclusion-exclusion weights satisfy the
three-term recurrence with coefficients `alphaC` and `betaC`.  This is the step
that gives the normalized row polynomials their recurrence, by convolution
against `fun m => 1 / m ! ^ 3`. -/
theorem cWeight_recurrence (i j : ℕ) :
    cWeight (j + i + 3) (j + 2)
      = cWeight (j + i + 2) (j + 2)
        + alphaC (j + i + 3) * cWeight (j + i + 1) (j + 1)
        + betaC (j + i + 3) * cWeight (j + i) j := by
  have e1 : j + i + 3 - (j + 2) = i + 1 := by omega
  have e2 : j + i + 2 - (j + 2) = i := by omega
  have e3 : j + i + 1 - (j + 1) = i := by omega
  have e4 : j + i - j = i := by omega
  have F1 : Nat.factorial (j + i + 1) = (j + i + 1) * Nat.factorial (j + i) :=
    Nat.factorial_succ (j + i)
  have F2 : Nat.factorial (j + i + 2) = (j + i + 2) * Nat.factorial (j + i + 1) := by
    simpa using Nat.factorial_succ (j + i + 1)
  have F3 : Nat.factorial (j + i + 3) = (j + i + 3) * Nat.factorial (j + i + 2) := by
    simpa using Nat.factorial_succ (j + i + 2)
  have G1 : Nat.factorial (i + 1) = (i + 1) * Nat.factorial i := Nat.factorial_succ i
  have H1 : Nat.factorial (j + 1) = (j + 1) * Nat.factorial j := Nat.factorial_succ j
  have H2 : Nat.factorial (j + 2) = (j + 2) * Nat.factorial (j + 1) := by
    simpa using Nat.factorial_succ (j + 1)
  have c1 : ((j + i + 3 : ℕ) : ℝ) - 1 = ((j + i + 2 : ℕ) : ℝ) := by push_cast; ring
  have c2 : ((j + i + 3 : ℕ) : ℝ) - 2 = ((j + i + 1 : ℕ) : ℝ) := by push_cast; ring
  have s2 : (-1 : ℝ) ^ (j + 2) = (-1) ^ j := by rw [pow_add]; ring
  have s1 : (-1 : ℝ) ^ (j + 1) = -(-1) ^ j := by rw [pow_add]; ring
  unfold cWeight alphaC betaC
  rw [e1, e2, e3, e4, c1, c2, F3, F2, F1, G1, H2, H1, s1, s2]
  have nf : (Nat.factorial (j + i) : ℝ) ≠ 0 := factorial_cast_ne_zero _
  have ni : (Nat.factorial i : ℝ) ≠ 0 := factorial_cast_ne_zero _
  have nj : (Nat.factorial j : ℝ) ≠ 0 := factorial_cast_ne_zero _
  push_cast
  have a1 : ((j : ℝ) + i + 1) ≠ 0 := by positivity
  have a2 : ((j : ℝ) + i + 2) ≠ 0 := by positivity
  have a3 : ((j : ℝ) + i + 3) ≠ 0 := by positivity
  have b1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have b2 : ((j : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-! ### Convolution against `1 / m ! ^ 3` -/

/-- The sequence the weights are convolved against, `eCube m = 1 / m ! ^ 3`. -/
def eCube (m : ℕ) : ℝ := 1 / (Nat.factorial m : ℝ) ^ 3

/-- The normalized array coefficient, `dNorm n k = t (n, k) / (n)_k ^ 3`,
written as the convolution of `cWeight n` against `eCube`. -/
def dNorm (n k : ℕ) : ℝ := ∑ j ∈ Finset.range (k + 1), cWeight n j * eCube (k - j)

theorem dNorm_eq (n l : ℕ) :
    dNorm n l = ∑ j ∈ Finset.range (l + 1), cWeight n j * eCube (l - j) := rfl

@[simp] theorem eCube_zero : eCube 0 = 1 := by simp [eCube]

@[simp] theorem eCube_one : eCube 1 = 1 := by simp [eCube]

@[simp] theorem dNorm_zero_index (n : ℕ) : dNorm n 0 = 1 := by
  simp [dNorm]

/-- At index one the convolution is a single correction term. -/
theorem dNorm_one_index (n : ℕ) : dNorm n 1 = 1 + cWeight n 1 := by
  simp [dNorm, Finset.sum_range_succ]

/-- Peeling the two lowest terms of the convolution at index `l + 2`. -/
theorem dNorm_split_two (n l : ℕ) :
    dNorm n (l + 2)
      = (∑ j ∈ Finset.range (l + 1), cWeight n (j + 2) * eCube (l - j))
        + cWeight n 1 * eCube (l + 1) + cWeight n 0 * eCube (l + 2) := by
  have h : l + 2 - 1 = l + 1 := by omega
  rw [dNorm, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.add_sub_add_right, Nat.sub_zero, h]

/-- Peeling the lowest term of the convolution at index `l + 1`. -/
theorem dNorm_split_one (n l : ℕ) :
    dNorm n (l + 1)
      = (∑ j ∈ Finset.range (l + 1), cWeight n (j + 1) * eCube (l - j))
        + cWeight n 0 * eCube (l + 1) := by
  rw [dNorm, Finset.sum_range_succ']
  simp only [Nat.add_sub_add_right, Nat.sub_zero]

/-- The coefficient recurrence at index zero. -/
theorem dNorm_recurrence_zero (m : ℕ) : dNorm (m + 3) 0 = dNorm (m + 2) 0 := by simp

/-- The coefficient recurrence at index one. -/
theorem dNorm_recurrence_one (m : ℕ) :
    dNorm (m + 3) 1 = dNorm (m + 2) 1 + alphaC (m + 3) * dNorm (m + 1) 0 := by
  rw [dNorm_one_index, dNorm_one_index, dNorm_zero_index, cWeight_recurrence_one m,
    cWeight_zero_index]
  ring

/-- **The coefficient recurrence.**  Convolving `cWeight_recurrence` against
`eCube` gives the three-term recurrence for the normalized array coefficients.
The hypothesis `l + 2 ≤ m` is what keeps every weight index strictly below its
first argument, so that `cWeight_recurrence` applies throughout the sum. -/
theorem dNorm_recurrence (m l : ℕ) (hl : l + 2 ≤ m) :
    dNorm (m + 3) (l + 2)
      = dNorm (m + 2) (l + 2)
        + alphaC (m + 3) * dNorm (m + 1) (l + 1)
        + betaC (m + 3) * dNorm m l := by
  have key : ∀ j ∈ Finset.range (l + 1),
      cWeight (m + 3) (j + 2) * eCube (l - j)
        = cWeight (m + 2) (j + 2) * eCube (l - j)
          + alphaC (m + 3) * (cWeight (m + 1) (j + 1) * eCube (l - j))
          + betaC (m + 3) * (cWeight m j * eCube (l - j)) := by
    intro j hj
    have hjm : j ≤ m := by simp only [Finset.mem_range] at hj; omega
    have e1 : j + (m - j) + 3 = m + 3 := by omega
    have e2 : j + (m - j) + 2 = m + 2 := by omega
    have e3 : j + (m - j) + 1 = m + 1 := by omega
    have e4 : j + (m - j) = m := by omega
    have hrec := cWeight_recurrence (m - j) j
    rw [e1, e2, e3, e4] at hrec
    rw [hrec]; ring
  rw [dNorm_split_two (m + 3) l, dNorm_split_two (m + 2) l, dNorm_split_one (m + 1) l,
    dNorm_eq m l, Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, cWeight_recurrence_zero m, cWeight_recurrence_one m]
  ring

end RealRooted
