import RealRooted.GarloffWagner
import RealRooted.PosCombo

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Cone bounds for nonnegative combinations of an interlacing sequence

Branden--Saud Leite, *Totally nonnegative matrices, chain enumeration and zeros
of polynomials* (arXiv:2412.06595), Lemma 3.1(1): if `f 0 ≺ f 1 ≺ … ≺ f n` is
an interlacing sequence with nonnegative coefficients and the weights `lam i`
are nonnegative, then

```text
f 0  ≺  ∑ i, lam i * f i  ≺  f n.
```

The two halves are the Finset cone lemmas `prec0_finsetSum_left_of_nonneg` and
`prec0_finsetSum_right_of_nonneg`, combined with the existing scaling lemmas
`prec0_C_mul_left_of_nonneg` and `prec0_C_mul_right_of_nonneg`.  `Prec0` rather
than `Prec` is the right relation here: a vanishing weight kills a summand, and
the zero-aware convention absorbs it, so no positivity of the weights is
needed.

Note that the endpoints must be compared with themselves, so the statement also
consumes reflexivity of `Prec` on the real-rooted members.
-/

/-- Scaling by a nonnegative constant keeps nonnegative coefficients. -/
theorem hasNonnegCoeffs_C_mul {a : ℝ} {p : ℝ[X]} (ha : 0 ≤ a)
    (hp : HasNonnegCoeffs p) : HasNonnegCoeffs (C a * p) := by
  intro k
  rw [coeff_C_mul]
  exact mul_nonneg ha (hp k)

/-- **Branden--Saud Leite Lemma 3.1(1).**  A nonnegative combination of an
interlacing sequence is caught between its first and last members. -/
theorem prec0_weightedSum_cone {n : ℕ} (f : ℕ → ℝ[X]) (lam : ℕ → ℝ)
    (hprec : ∀ i j, i < j → j ≤ n → Prec (f i) (f j))
    (hrr : ∀ i, i ≤ n → f i ≠ 0 ∧ (f i).Splits)
    (hnn : ∀ i, i ≤ n → HasNonnegCoeffs (f i))
    (hlam : ∀ i, 0 ≤ lam i) :
    Prec0 (f 0) (∑ i ∈ Finset.range (n + 1), C (lam i) * f i) ∧
      Prec0 (∑ i ∈ Finset.range (n + 1), C (lam i) * f i) (f n) := by
  classical
  have hmem : ∀ i ∈ Finset.range (n + 1), i ≤ n := by
    intro i hi
    simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
  have hnn' : ∀ i ∈ Finset.range (n + 1), HasNonnegCoeffs (C (lam i) * f i) := by
    intro i hi
    exact hasNonnegCoeffs_C_mul (hlam i) (hnn i (hmem i hi))
  refine ⟨?_, ?_⟩
  · refine prec0_finsetSum_left_of_nonneg _ _ _ ?_ hnn'
    intro i hi
    have hbase : Prec0 (f 0) (f i) := by
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact (prec_refl (hrr 0 (Nat.zero_le n)).1 (hrr 0 (Nat.zero_le n)).2).toPrec0
      · exact (hprec 0 i hpos (hmem i hi)).toPrec0
    exact prec0_C_mul_right_of_nonneg hbase (hlam i)
  · refine prec0_finsetSum_right_of_nonneg _ _ _ ?_ hnn'
    intro i hi
    have hbase : Prec0 (f i) (f n) := by
      rcases eq_or_lt_of_le (hmem i hi) with rfl | hlt
      · exact (prec_refl (hrr i (hmem i hi)).1 (hrr i (hmem i hi)).2).toPrec0
      · exact (hprec i n hlt le_rfl).toPrec0
    exact prec0_C_mul_left_of_nonneg hbase (hlam i)

end RealRooted
