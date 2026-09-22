import RealRooted.AffineFamily
import RealRooted.ProductFamily
import RealRooted.GarloffWagner
import RealRooted.PosCombo

open Polynomial

noncomputable section

namespace RealRooted

/-!
# The coupled partial-sum induction step

Some recurrences with a negative coefficient become strictly positive after a
generating-function rearrangement that introduces the partial sums of the
sequence.  A typical resulting shape, for a sequence `A` with partial sums `S`,
is

```text
A n = A (n-2) + A (n-3) + c * X * S (n-4),     S n = S (n-1) + A n
```

with `c > 0`.  The interlacing induction for such a system needs one step
lemma, proved here: if the partial sum interlaces both of the plain terms then
the whole combination is real-rooted, and it is sandwiched between the plain
part and the `X`-shifted partial sum, which is what lets the invariant
propagate.

The three ingredients are all already available: the degree shift
`prec_to_prec_mul_X_of_nonneg`, the two-term right cone
`prec0_add_left_of_common_right_of_nonneg`, and the positive-combination
results `StrictInterl.nonneg_combo_left` / `StrictInterl.nonneg_combo_right`.
-/

/-- **The partial-sum step.**  If the partial sum `S` interlaces both plain
terms `A₁` and `A₂`, then for `c > 0` the combination `A₁ + A₂ + c * X * S` is
real-rooted and precedes `X * S`.

The other half of the sandwich, `A₁ + A₂ ≺ A₁ + A₂ + c * X * S`, is
`partialSum_step_left` below; note that it needs a coprimality hypothesis, since
`StrictInterl.nonneg_combo_left` does. -/
theorem partialSum_step
    {S A₁ A₂ : ℝ[X]} (h₁ : StrictInterl S A₁) (h₂ : StrictInterl S A₂)
    (hSnn : HasNonnegCoeffs S) (h₁nn : HasNonnegCoeffs A₁) (h₂nn : HasNonnegCoeffs A₂)
    {c : ℝ} (hc : 0 < c) :
    StrictInterl (C (1 : ℝ) * (A₁ + A₂) + C c * (X * S)) (X * S) ∧
      ((C (1 : ℝ) * (A₁ + A₂) + C c * (X * S)) ≠ 0 ∧
        (C (1 : ℝ) * (A₁ + A₂) + C c * (X * S)).Splits) := by
  -- the degree shift on each plain term
  have hA₁ : StrictInterl A₁ (X * S) := prec_to_prec_mul_X_of_nonneg h₁ hSnn h₁nn
  have hA₂ : StrictInterl A₂ (X * S) := prec_to_prec_mul_X_of_nonneg h₂ hSnn h₂nn
  -- the two-term right cone
  have hcone0 : Interl (A₁ + A₂) (X * S) :=
    prec0_add_left_of_common_right_of_nonneg hA₁.toInterl hA₂.toInterl h₁nn h₂nn
  have hA₁0 : A₁ ≠ 0 := hA₁.1.1
  have hsum0 : A₁ + A₂ ≠ 0 := by
    rw [add_comm]
    exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero h₂nn h₁nn hA₁0
  have hXS0 : X * S ≠ 0 := hA₁.2.1.1
  have hcone : StrictInterl (A₁ + A₂) (X * S) := by
    rcases hcone0 with h | h | h
    · exact absurd h hsum0
    · exact absurd h hXS0
    · exact h
  -- positive leading coefficients
  have hsum_pos : HasPosLeadingCoeff (A₁ + A₂) :=
    (h₁nn.add h₂nn).pos_leadingCoeff hsum0
  have hXS_nn : HasNonnegCoeffs (X * S) := hSnn.X_mul
  have hXS_pos : HasPosLeadingCoeff (X * S) := hXS_nn.pos_leadingCoeff hXS0
  refine ⟨?_, ?_⟩
  · exact hcone.nonneg_combo_right hsum_pos hXS_pos zero_le_one hc.le (Or.inl zero_lt_one)
  · exact hcone.isRealRooted_nonneg_combo hsum_pos hXS_pos zero_le_one hc.le
      (Or.inl zero_lt_one)

/-- The left half of the sandwich.  Unlike `partialSum_step` this needs the two
summands to be coprime, which is the hypothesis `StrictInterl.nonneg_combo_left`
carries; in applications it has to be supplied from the specific sequence. -/
theorem partialSum_step_left
    {S A₁ A₂ : ℝ[X]} (h₁ : StrictInterl S A₁) (h₂ : StrictInterl S A₂)
    (hSnn : HasNonnegCoeffs S) (h₁nn : HasNonnegCoeffs A₁) (h₂nn : HasNonnegCoeffs A₂)
    {c : ℝ} (hc : 0 < c)
    (hcop : IsCoprime (C (1 : ℝ) * (A₁ + A₂)) (C c * (X * S))) :
    StrictInterl (A₁ + A₂) (C (1 : ℝ) * (A₁ + A₂) + C c * (X * S)) := by
  have hA₁ : StrictInterl A₁ (X * S) := prec_to_prec_mul_X_of_nonneg h₁ hSnn h₁nn
  have hA₂ : StrictInterl A₂ (X * S) := prec_to_prec_mul_X_of_nonneg h₂ hSnn h₂nn
  have hcone0 : Interl (A₁ + A₂) (X * S) :=
    prec0_add_left_of_common_right_of_nonneg hA₁.toInterl hA₂.toInterl h₁nn h₂nn
  have hA₁0 : A₁ ≠ 0 := hA₁.1.1
  have hsum0 : A₁ + A₂ ≠ 0 := by
    rw [add_comm]
    exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero h₂nn h₁nn hA₁0
  have hXS0 : X * S ≠ 0 := hA₁.2.1.1
  have hcone : StrictInterl (A₁ + A₂) (X * S) := by
    rcases hcone0 with h | h | h
    · exact absurd h hsum0
    · exact absurd h hXS0
    · exact h
  have hsum_pos : HasPosLeadingCoeff (A₁ + A₂) := (h₁nn.add h₂nn).pos_leadingCoeff hsum0
  have hXS_pos : HasPosLeadingCoeff (X * S) := hSnn.X_mul.pos_leadingCoeff hXS0
  obtain ⟨hne, hsp⟩ := hcone.isRealRooted_nonneg_combo hsum_pos hXS_pos
    zero_le_one hc.le (Or.inl zero_lt_one)
  exact hcone.nonneg_combo_left hsum_pos hXS_pos zero_le_one hc.le
    (Or.inl zero_lt_one) hne hsp hcop

end RealRooted
