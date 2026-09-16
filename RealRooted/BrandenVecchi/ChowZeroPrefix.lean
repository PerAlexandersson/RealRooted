import RealRooted.BrandenLeite.Regularization
import RealRooted.BrandenVecchi.ChowInfinitePF
import RealRooted.AissenSchoenbergWhitney
import RealRooted.PolyaFrequencyConvolution.GeometricScaling
import RealRooted.QuadraticRoot

/-!
# Scalar and zero-prefix Chow data

This file isolates the algebraic and Pólya-frequency foundation for the
`C * z ^ N` boundary in the ASW--Edrei representation.  The paper's
regularization replaces `z ^ N` by `(epsilon + z) ^ N`; the definitions below
record that approximation coefficientwise and identify the rows that vanish
before the first nonzero Toeplitz coefficient.  A checked PF counterexample
also shows that the zero-prefix endpoint cannot be the raw matrix-level Chow
construction; a full theorem needs a separate normalized or projective
definition matching the paper's formal-series convention.
-/

open Filter Matrix Polynomial Topology

namespace RealRooted.BrandenVecchi

noncomputable section

private theorem chowS_eq_of_mul_eq {n : ℕ} {p q : ℝ[X]}
    (hdegree : p.natDegree ≤ n)
    (h : (X - 1) * q = p.reflect n - p) :
    Polynomial.chowS n p = q := by
  apply (monic_X_sub_C (1 : ℝ)).isRegular.left
  change (X - 1) * Polynomial.chowS n p = (X - 1) * q
  rw [Polynomial.X_sub_one_mul_chowS n p hdegree]
  exact h.symm

private theorem chowS_zero_real (n : ℕ) :
    Polynomial.chowS n (0 : ℝ[X]) = 0 :=
  chowS_eq_of_mul_eq (by simp) (by simp)

/-- Multiply a sequence by `C` after inserting `N` leading zeroes. -/
def scaledZeroPrefix (C : ℝ) (N : ℕ) (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  if N ≤ d then C * a (d - N) else 0

@[simp]
theorem scaledZeroPrefix_zero (C : ℝ) (a : ℕ → ℝ) (d : ℕ) :
    scaledZeroPrefix C 0 a d = C * a d := by
  simp [scaledZeroPrefix]

@[simp]
theorem zero_scaledZeroPrefix (N : ℕ) (a : ℕ → ℝ) :
    scaledZeroPrefix 0 N a = 0 := by
  funext d
  simp [scaledZeroPrefix]

theorem scaledZeroPrefix_eq_zero_of_lt
    (C : ℝ) (N : ℕ) (a : ℕ → ℝ) {d : ℕ} (hd : d < N) :
    scaledZeroPrefix C N a d = 0 := by
  simp [scaledZeroPrefix, Nat.not_le_of_lt hd]

@[simp]
theorem scaledZeroPrefix_self
    (C : ℝ) (N : ℕ) (a : ℕ → ℝ) :
    scaledZeroPrefix C N a N = C * a 0 := by
  simp [scaledZeroPrefix]

/-- Toeplitz formation commutes with nonnegative-independent scalar
multiplication of a sequence. -/
theorem toeplitz_const_mul_sequence (C : ℝ) (a : ℕ → ℝ) :
    toeplitz (fun d => C * a d) = C • toeplitz a := by
  ext i j
  by_cases hji : j ≤ i
  · simp [toeplitz_apply, hji]
  · simp [toeplitz_apply, hji]

/-- Nonnegative scalar multiplication preserves the PF property for arbitrary
sequences, not only polynomial coefficient sequences. -/
theorem IsPolyaFreqSeq.const_mul_sequence
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) (C : ℝ) (hC : 0 ≤ C) :
    IsPolyaFreqSeq (fun d => C * a d) := by
  rw [IsPolyaFreqSeq, toeplitz_const_mul_sequence]
  exact ha.smul C hC

/-- A nonnegative scalar multiple of a finite zero prefix remains PF. -/
theorem IsPolyaFreqSeq.scaledZeroPrefix
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) {C : ℝ} (hC : 0 ≤ C)
    (N : ℕ) :
    IsPolyaFreqSeq (scaledZeroPrefix C N a) := by
  exact IsPolyaFreqSeq.prefix_zeros
    (IsPolyaFreqSeq.const_mul_sequence ha C hC) N

/-- Exact entry formula for the Toeplitz matrix after a scalar zero prefix. -/
theorem toeplitz_scaledZeroPrefix_apply
    (C : ℝ) (N : ℕ) (a : ℕ → ℝ) (i j : ℕ) :
    toeplitz (scaledZeroPrefix C N a) i j =
      if j + N ≤ i then C * a (i - j - N) else 0 := by
  rw [toeplitz_apply]
  by_cases hji : j ≤ i
  · rw [if_pos hji]
    have hshift : N ≤ i - j ↔ j + N ≤ i := by lia
    simp only [scaledZeroPrefix, hshift]
  · have hshift : ¬j + N ≤ i := fun h => hji (by lia)
    simp [hji, hshift]

/-- Every Toeplitz entry in a row before the prefix length vanishes. -/
theorem toeplitz_scaledZeroPrefix_eq_zero_of_row_lt
    (C : ℝ) (N : ℕ) (a : ℕ → ℝ) {i : ℕ} (hi : i < N) (j : ℕ) :
    toeplitz (scaledZeroPrefix C N a) i j = 0 := by
  rw [toeplitz_scaledZeroPrefix_apply]
  simp [show ¬j + N ≤ i by lia]

/-- Chow rows strictly before the first nonzero symbol coefficient vanish. -/
theorem chowPolynomial_scaledZeroPrefix_eq_zero_of_lt
    (C : ℝ) (N : ℕ) (a : ℕ → ℝ) {n : ℕ} (hn : n < N) :
    chowPolynomial (toeplitz (scaledZeroPrefix C N a)) n = 0 := by
  rw [chowPolynomial_eq]
  apply Finset.sum_eq_zero
  intro k hk
  rw [toeplitz_scaledZeroPrefix_eq_zero_of_row_lt C N a hn]
  simp

/-- At the prefix rank, the Chow polynomial is exactly the first shifted
coefficient. -/
theorem chowPolynomial_scaledZeroPrefix_self
    (C : ℝ) (N : ℕ) (a : ℕ → ℝ) :
    chowPolynomial (toeplitz (scaledZeroPrefix C N a)) N =
      Polynomial.C (C * a 0) := by
  rw [chowPolynomial_eq, Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [toeplitz_apply, if_pos hkN,
      scaledZeroPrefix_eq_zero_of_lt C N a (by lia)]
    simp
  · simp

/-- The paper's epsilon regularization, including the outer scalar. -/
def scaledRegularizedSequence
    (C : ℝ) (N : ℕ) (a : ℕ → ℝ) (epsilon : ℝ) (d : ℕ) : ℝ :=
  C * BrandenLeite.regularizedSequence N a epsilon d

/-- At epsilon zero, the regularized sequence is the literal scaled zero
prefix. -/
theorem scaledRegularizedSequence_at_zero
    (C : ℝ) (N : ℕ) (a : ℕ → ℝ) :
    scaledRegularizedSequence C N a 0 = scaledZeroPrefix C N a := by
  funext d
  simp [scaledRegularizedSequence, scaledZeroPrefix,
    BrandenLeite.regularizedSequence_at_zero]

/-- Every fixed coefficient of the scaled epsilon regularization converges to
the corresponding zero-prefixed coefficient. -/
theorem tendsto_scaledRegularizedSequence
    {I : Type*} {l : Filter I} {epsilon : I → ℝ}
    (hepsilon : Tendsto epsilon l (𝓝 0))
    (C : ℝ) (N : ℕ) (a : ℕ → ℝ) (d : ℕ) :
    Tendsto (fun k => scaledRegularizedSequence C N a (epsilon k) d) l
      (𝓝 (scaledZeroPrefix C N a d)) := by
  simpa [scaledRegularizedSequence, scaledZeroPrefix] using
    (BrandenLeite.tendsto_regularizedSequence hepsilon N a d).const_mul C

/-- Nonnegative epsilon regularizations of a PF tail remain PF after applying
the outer nonnegative scalar. -/
theorem scaledRegularizedSequence_isPolyaFreqSeq
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) {C epsilon : ℝ}
    (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon) (N : ℕ) :
    IsPolyaFreqSeq (scaledRegularizedSequence C N a epsilon) := by
  apply IsPolyaFreqSeq.const_mul_sequence
  · exact BrandenLeite.regularizedSequence_isPolyaFreqSeq ha N hepsilon
  · exact hC

/-- Positive scalar, shift, and tail origin give the positive diagonal needed
by each epsilon approximant. -/
theorem scaledRegularizedSequence_zero_pos
    {C epsilon : ℝ} {N : ℕ} {a : ℕ → ℝ}
    (hC : 0 < C) (hepsilon : 0 < epsilon) (ha0 : 0 < a 0) :
    0 < scaledRegularizedSequence C N a epsilon 0 := by
  exact mul_pos hC
    (BrandenLeite.regularizedSequence_zero_pos hepsilon ha0)

/-- Three leading zeroes can likewise destroy matrix-level Chow splitness,
even when the PF tail is the constant-one sequence. -/
theorem chowPolynomial_three_zero_prefix_six :
    chowPolynomial
        (toeplitz (scaledZeroPrefix 1 3 (fun _ : ℕ => (1 : ℝ)))) 6 =
      X ^ 2 + X + 1 := by
  let A := toeplitz (scaledZeroPrefix 1 3 (fun _ : ℕ => (1 : ℝ)))
  have hd0 : chowDerangement A 0 = 1 := chowDerangement_zero A
  have hd1 : chowDerangement A 1 = 0 := by
    rw [chowDerangement_succ]
    simp only [Fin.sum_univ_succ]
    norm_num [A, hd0, scaledZeroPrefix, toeplitz_apply]
    rw [chowS_zero_real]
  have hd2 : chowDerangement A 2 = 0 := by
    rw [chowDerangement_succ]
    simp only [Fin.sum_univ_succ]
    norm_num [A, hd0, hd1, scaledZeroPrefix, toeplitz_apply]
    rw [chowS_zero_real]
  have hs2 : Polynomial.chowS 2 (1 : ℝ[X]) = X + 1 := by
    apply chowS_eq_of_mul_eq (by simp)
    rw [Polynomial.reflect_one]
    ring
  have hd3 : chowDerangement A 3 = X ^ 2 + X := by
    rw [chowDerangement_succ]
    simp only [Fin.sum_univ_succ]
    norm_num [A, hd0, hd1, hd2, scaledZeroPrefix, toeplitz_apply]
    rw [hs2]
    ring
  change chowPolynomial A 6 = _
  simp only [chowPolynomial, Finset.sum_range_succ]
  rw [hd0, hd1, hd2, hd3]
  norm_num [A, scaledZeroPrefix, toeplitz_apply]
  ring

/-- The three-zero-prefix counterexample still has a Pólya-frequency symbol. -/
theorem three_zero_prefix_constant_isPolyaFreqSeq :
    IsPolyaFreqSeq (scaledZeroPrefix 1 3 (fun _ : ℕ => (1 : ℝ))) := by
  convert IsPolyaFreqSeq.scaledZeroPrefix
    (geometric_isPolyaFreqSeq (1 : ℝ) (by norm_num))
    (show (0 : ℝ) ≤ 1 by norm_num) 3 using 1
  funext d
  simp [scaledZeroPrefix]

theorem chowPolynomial_three_zero_prefix_six_not_splits :
    ¬(chowPolynomial
      (toeplitz (scaledZeroPrefix 1 3 (fun _ : ℕ => (1 : ℝ)))) 6).Splits := by
  rw [chowPolynomial_three_zero_prefix_six]
  simpa using
    (quadraticPoly_not_splits_of_discrim_neg one_ne_zero
      (by norm_num [discrim]) :
        ¬((C 1 * X ^ 2 + C 1 * X + C 1) : ℝ[X]).Splits)

/-- The full ASW--Edrei coefficient sequence with outer scalar and zero
prefix. -/
def aswEdreiFullCoeff
    (C : ℝ) (N : ℕ) (gamma : ℝ) (alpha beta : ℕ → ℝ) : ℕ → ℝ :=
  scaledZeroPrefix C N (aswEdreiCoeff gamma alpha beta)

/-- The full ASW--Edrei sequence is PF for nonnegative data. -/
theorem aswEdreiFullCoeff_isPolyaFreqSeq
    {C gamma : ℝ} {N : ℕ} {alpha beta : ℕ → ℝ}
    (hC : 0 ≤ C) (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) :
    IsPolyaFreqSeq (aswEdreiFullCoeff C N gamma alpha beta) := by
  exact IsPolyaFreqSeq.scaledZeroPrefix
    (aswEdreiCoeff_isPolyaFreqSeq hgamma halpha hbeta hsum) hC N

/-- Full ASW--Edrei Chow rows below the leading power vanish. -/
theorem aswEdreiFullChow_eq_zero_of_lt
    (C : ℝ) (N : ℕ) (gamma : ℝ) (alpha beta : ℕ → ℝ)
    {n : ℕ} (hn : n < N) :
    chowPolynomial (toeplitz (aswEdreiFullCoeff C N gamma alpha beta)) n = 0 :=
  chowPolynomial_scaledZeroPrefix_eq_zero_of_lt C N _ hn

/-- The first potentially nonzero full ASW--Edrei Chow row is the scalar
constant polynomial `C`. -/
theorem aswEdreiFullChow_self
    {C gamma : ℝ} {N : ℕ} {alpha beta : ℕ → ℝ}
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) :
    chowPolynomial (toeplitz (aswEdreiFullCoeff C N gamma alpha beta)) N =
      Polynomial.C C := by
  rw [aswEdreiFullCoeff, chowPolynomial_scaledZeroPrefix_self,
    aswEdreiCoeff_zero halpha hbeta hsum, mul_one]

end

end RealRooted.BrandenVecchi
