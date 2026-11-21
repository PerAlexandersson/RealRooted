module

public import RealRooted.TotalPositivity.PFRiordan
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Negative roots of binomial rays

We realize the polynomial with coefficients `binom(N + a j, K + b j)` as a PF Riordan row.
This proves the binomial-ray result in Yu, *Confirming Two Conjectures of Su and Wang*,
arXiv:0901.0385v1, Section 2 (proof of Conjecture 1), equivalently Theorem A of
Bøgvad--Ndikubwayo--Shapiro, *Generalizing Tran's Conjecture*, arXiv:2001.09248v2.
The proof uses the existing PF Riordan theorem instead of Yu's planar strip network.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Trinomial

private theorem mk_rationalPFCoeff_replicate (r e : ℕ) :
    PowerSeries.mk (PFRiordan.rationalPFCoeff 1 r [] (List.replicate e 1)) =
      PowerSeries.X ^ r * (PowerSeries.mk (1 : ℕ → ℝ)) ^ e := by
  rw [PFRiordan.mk_rationalPFCoeff]
  simp [BrandenVecchi.finiteSupersymmetricSeries,
    BrandenVecchi.supersymmetricDenominatorFactor, PowerSeries.rescale_one]

/-- The binomial-ray polynomial, realized as a PF Riordan row with row index `N - K`. -/
def binomialRay (N K a b : ℕ) : ℝ[X] :=
  PFRiordan.rowPolynomial
    (PFRiordan.rationalPFCoeff 1 0 [] (List.replicate (K + 1) 1))
    (PFRiordan.rationalPFCoeff 1 (b - a - 1) [] (List.replicate (b - K - 1) 1)) (N - K)

/-- Coefficients of the Riordan realization are exactly the binomial coefficients on the ray. -/
theorem coeff_binomialRay {N K a b : ℕ} (hNK : K ≤ N) (hab : a < b) (hKb : K < b)
    (j : ℕ) : (binomialRay N K a b).coeff j = ((N + a * j).choose (K + b * j) : ℝ) := by
  rw [binomialRay, PFRiordan.coeff_rowPolynomial, PFRiordan.array,
    mk_rationalPFCoeff_replicate, mk_rationalPFCoeff_replicate]
  simp only [pow_zero, one_mul]
  let G : PowerSeries ℝ := PowerSeries.mk (1 : ℕ → ℝ)
  have hL : b - a - 1 + 1 = b - a := by lia
  have hE : K + 1 + (b - K - 1) = b := by lia
  have hprod : PowerSeries.X *
      (PowerSeries.X ^ (b - a - 1) * G ^ (b - K - 1)) =
      PowerSeries.X ^ (b - a) * G ^ (b - K - 1) := by
    rw [← mul_assoc, ← pow_succ', hL]
  change PowerSeries.coeff (N - K)
    ((G ^ (K + 1)) ^ (j + 1) *
      (PowerSeries.X * (PowerSeries.X ^ (b - a - 1) * G ^ (b - K - 1))) ^ j) = _
  rw [hprod]
  have hpower : (G ^ (K + 1)) ^ (j + 1) *
      (PowerSeries.X ^ (b - a) * G ^ (b - K - 1)) ^ j =
      PowerSeries.X ^ ((b - a) * j) * G ^ (K + b * j + 1) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
    calc
      _ = PowerSeries.X ^ ((b - a) * j) *
          G ^ ((K + 1) * (j + 1) + (b - K - 1) * j) := by rw [pow_add]; ring
      _ = _ := by
        congr 2
        nlinarith
  rw [hpower, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_mk]
    have htop : K + b * j + (N - K - (b - a) * j) = N + a * j := by
      have h₁ := Nat.sub_add_cancel hNK
      have h₂ := Nat.sub_add_cancel h
      have h₃ := Nat.sub_add_cancel hab.le
      nlinarith
    rw [htop]
  · have hlt : N + a * j < K + b * j := by
      have h₁ := Nat.sub_add_cancel hNK
      have h₂ := Nat.sub_add_cancel hab.le
      have h₃ : N - K < (b - a) * j := by lia
      nlinarith
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]

/-- Every binomial-ray row is a PF polynomial under the natural parameter bounds. -/
theorem binomialRay_isPFPolynomial (N K a b : ℕ) : IsPFPolynomial (binomialRay N K a b) := by
  apply PFRiordan.rowPolynomial_isPFPolynomial
  · apply PFRiordan.rationalPFCoeff_isPolyaFreqSeq (by norm_num)
    · simp
    · intro x hx
      have hx1 : x = 1 := List.eq_of_mem_replicate hx
      simp [hx1]
  · apply PFRiordan.rationalPFCoeff_isPolyaFreqSeq (by norm_num)
    · simp
    · intro x hx
      have hx1 : x = 1 := List.eq_of_mem_replicate hx
      simp [hx1]

/-- Every zero of a binomial ray with a nonzero initial binomial coefficient is negative. -/
theorem binomialRay_splits_and_roots_neg {N K a b : ℕ}
    (hNK : K ≤ N) (hab : a < b) (hKb : K < b) :
    (binomialRay N K a b).Splits ∧ ∀ r ∈ (binomialRay N K a b).roots, r < 0 := by
  have hpf := binomialRay_isPFPolynomial N K a b
  refine ⟨hpf.splits, roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hpf.hasNonnegCoeffs ?_⟩
  rw [coeff_binomialRay hNK hab hKb]
  simp only [mul_zero, add_zero]
  exact Nat.cast_ne_zero.mpr (Nat.choose_pos hNK).ne'

/-- Every complex zero of a binomial ray is a negative real number. -/
theorem eval₂_binomialRay_eq_zero {N K a b : ℕ}
    (hNK : K ≤ N) (hab : a < b) (hKb : K < b) {z : ℂ}
    (hz : (binomialRay N K a b).eval₂ Complex.ofRealHom z = 0) :
    ∃ w : ℝ, w < 0 ∧ (w : ℂ) = z := by
  have hne : binomialRay N K a b ≠ 0 := by
    intro h
    have hc := coeff_binomialRay hNK hab hKb 0
    have hp : (0 : ℝ) < N.choose K := by exact_mod_cast Nat.choose_pos hNK
    simp [h] at hc
    linarith
  have hs := binomialRay_splits_and_roots_neg hNK hab hKb
  obtain ⟨w, hw⟩ : z ∈ Complex.ofRealHom.range := hs.1.mem_range_of_isRoot hne
    (by simpa [IsRoot.def, eval_map] using hz)
  have hroot : (binomialRay N K a b).IsRoot w := by
    rw [← hw, eval₂_at_apply] at hz
    exact Complex.ofRealHom.injective (by simpa using hz)
  exact ⟨w, hs.2 w ((mem_roots hne).mpr hroot), hw⟩

end RealRooted.Trinomial
