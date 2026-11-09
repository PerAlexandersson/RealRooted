module

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
public import RealRooted.SimpleRoots
public import RealRooted.Toeplitz.ParityRows
public import RealRooted.Toeplitz.SiteWeightedRuns
public import RealRooted.Toeplitz.TP2HessenbergExamples
import RealRooted.Toeplitz.ParityStrict
import RealRooted.Toeplitz.SiteWeightedRunRoots
import RealRooted.Toeplitz.TP2HessenbergStrict

/-!
# Examples for site-weighted runs, strict Hessenberg rows and the parity lift

* The `1 × 1` matrix `[1]` has run kernel `u_k = 1`, so the site-weighted run sum is
  `Z_N(z) = ∏ᵢ (1 + zᵢ)` (`siteWeightedRuns_one_by_one`), as it must: every subset `S` has run
  weight one.
* The matrix `[[1, 1], [0, 1]]` has `det = 1 > 0`, so its Hessenberg rows have simple positive
  roots and no common roots between consecutive rows (`hessenbergRow_exampleTwo_strict`).
* The `1 × 1` matrix `[1]` (`G(w) = 1 + w`) and the regression seed
  `A = ((2,2,2,2),(1,2,2,2),(1/2,1,2,2),(0,1/2,1,2))` with `G = 1 + 8w + 16w² + 10w³ + 2w⁴`
  (not real-rooted) satisfy the hypotheses of the parity lift (`parityRow_certificate_one`,
  `parityRow_certificate_seed`).
-/

@[expose] public section

open Polynomial Matrix

noncomputable section

namespace RealRooted

/-! ### Run sums for the kernel `u ≡ 1` -/

theorem runKernel_one_by_one {R : Type*} [CommSemiring R] (k : ℕ) :
    runKernel (!![(1 : R)] : Matrix (Fin 1) (Fin 1) R) k = 1 := by
  have : (!![(1 : R)] : Matrix (Fin 1) (Fin 1) R) = 1 := by ext i j; fin_cases i; fin_cases j; rfl
  simp [runKernel, this]

/-- For the kernel `u ≡ 1` every subset has run weight `1`, so `Z_N(z) = ∏ᵢ (1 + zᵢ)`. -/
theorem siteWeightedRuns_one_by_one {R : Type*} [CommSemiring R] {N : ℕ} (z : Fin N → R) :
    siteWeightedRuns (fun _ : ℕ => (1 : R)) z = ∏ i, (1 + z i) := by
  have hk : (fun _ : ℕ => (1 : R)) = runKernel (!![(1 : R)] : Matrix (Fin 1) (Fin 1) R) :=
    funext fun k => (runKernel_one_by_one k).symm
  rw [hk, siteWeightedRuns_runKernel]
  induction N with
  | zero => simp [runVector]
  | succ N ih =>
    have h' : runVector (!![(1 : R)] : Matrix (Fin 1) (Fin 1) R) N (Fin.init z) 0 =
        ∏ i : Fin N, (1 + z i.castSucc) := ih (Fin.init z)
    rw [runVector_succ_apply, Fin.prod_univ_castSucc, ← h']
    simp
    ring

/-! ### Strict rows -/

/-- The rows of `[[1, 1], [0, 1]]` have simple positive roots and no common roots. -/
theorem hessenbergRow_exampleTwo_strict (k : ℕ) :
    HasSimpleRoots (hessenbergRow hessenbergExampleTwo k) ∧
      (∀ r, (hessenbergRow hessenbergExampleTwo k).IsRoot r → 0 < r) ∧
      ∀ r, ¬ ((hessenbergRow hessenbergExampleTwo k).IsRoot r ∧
        (hessenbergRow hessenbergExampleTwo (k + 1)).IsRoot r) := by
  have hcol : ∀ ⦃i k j : Fin 2⦄, i ≤ k → hessenbergExampleTwo k j ≤ hessenbergExampleTwo i j := by
    intro i k j h
    fin_cases i <;> fin_cases k <;> fin_cases j <;> simp_all [hessenbergExampleTwo]
  have hrow : ∀ ⦃i j : Fin 2⦄, i ≤ j → hessenbergExampleTwo i j = hessenbergExampleTwo j j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hessenbergExampleTwo]
  have hdet : 0 < hessenbergExampleTwo.det := by
    simp [hessenbergExampleTwo, Matrix.det_fin_two_of]
  exact hessenbergRow_strict hessenbergExampleTwo_isTP2 hcol hrow (by norm_num) hdet k

/-! ### The parity lift -/

/-- The `1 × 1` matrix `[1]`, with `G(w) = 1 + w`. -/
def parityExampleOne : Matrix (Fin 1) (Fin 1) ℝ := !![1]

/-- The regression seed `((2,2,2,2),(1,2,2,2),(1/2,1,2,2),(0,1/2,1,2))`, for which
`G(w) = 1 + 8 w + 16 w² + 10 w³ + 2 w⁴` is not real-rooted. -/
def parityExampleSeed : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2, 2, 2, 2; 1, 2, 2, 2; 1 / 2, 1, 2, 2; 0, 1 / 2, 1, 2]

lemma parityExampleSeed_isTP2 : parityExampleSeed.IsTP2 := by
  refine ⟨fun i j => ?_, fun i₁ i₂ j₁ j₂ hi hj => ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num [parityExampleSeed]
  · fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      simp_all [parityExampleSeed] <;> norm_num

lemma parityExampleSeed_col :
    ∀ ⦃i k j : Fin 4⦄, i ≤ k → parityExampleSeed k j ≤ parityExampleSeed i j := by
  intro i k j h
  fin_cases i <;> fin_cases k <;> fin_cases j <;> simp_all [parityExampleSeed] <;> norm_num

lemma parityExampleSeed_row :
    ∀ ⦃i j : Fin 4⦄, i ≤ j → parityExampleSeed i j = parityExampleSeed j j := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [parityExampleSeed]

/-- The parity lift applies to the regression seed although `G` is not real-rooted. -/
theorem parityRow_certificate_seed (γ : ℝ) (k : ℕ) :
    (parityRow parityExampleSeed γ k).Monic ∧ (parityRow parityExampleSeed γ k).natDegree = k ∧
      (parityRow parityExampleSeed γ k).Splits ∧ HasSimpleRoots (parityRow parityExampleSeed γ k) ∧
      Interlaces (parityRow parityExampleSeed γ k) (parityRow parityExampleSeed γ (k + 1)) ∧
      IsCoprime (parityRow parityExampleSeed γ k) (parityRow parityExampleSeed γ (k + 1)) :=
  parityRow_certificate_of_trace_ne_zero parityExampleSeed_isTP2 parityExampleSeed_col
    parityExampleSeed_row (by norm_num [Matrix.trace, Fin.sum_univ_succ, parityExampleSeed]) γ k

/-- The parity lift applies to the `1 × 1` matrix `[1]`. -/
theorem parityRow_certificate_one (γ : ℝ) (k : ℕ) :
    (parityRow parityExampleOne γ k).Monic ∧ (parityRow parityExampleOne γ k).natDegree = k ∧
      (parityRow parityExampleOne γ k).Splits ∧ HasSimpleRoots (parityRow parityExampleOne γ k) ∧
      Interlaces (parityRow parityExampleOne γ k) (parityRow parityExampleOne γ (k + 1)) ∧
      IsCoprime (parityRow parityExampleOne γ k) (parityRow parityExampleOne γ (k + 1)) := by
  have h : ∀ i j : Fin 1, parityExampleOne i j = 1 := fun i j => by
    fin_cases i; fin_cases j; rfl
  refine parityRow_certificate_of_trace_ne_zero ?_ ?_ ?_
    (by simp [Matrix.trace, parityExampleOne]) γ k
  · exact ⟨fun i j => by simp [h], fun i₁ i₂ _ _ hi =>
      absurd hi (by rw [Fin.lt_def]; lia [i₁.isLt, i₂.isLt])⟩
  · intro i k j _; simp [h]
  · intro i j _; simp [h]

end RealRooted

end
