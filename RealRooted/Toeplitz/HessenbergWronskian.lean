module

public import Mathlib.RingTheory.Polynomial.Wronskian
import RealRooted.Wronskian.CauchyBinet
import RealRooted.Wronskian.WeakForward
public import RealRooted.Toeplitz.HessenbergRows
public import RealRooted.Toeplitz.AffineVector
import RealRooted.Toeplitz.TP2Hessenberg

/-!
# Wronskians of the Hessenberg vector recursion

For the vector recursion `f_{k+1} = (A + X J) f_k` of a `TP2` matrix `A` with decreasing columns,
the Wronskian of two coordinates of `f_{k+1}` dominates every `2 × 2`-minor term of the previous
stage: for rows `i < j` and columns `a < b`,
`(A_{ia} A_{jb} - A_{ib} A_{ja}) W(f_{k,a}, f_{k,b}) ≤ W(f_{k+1,i}, f_{k+1,j})`
pointwise on `ℝ` (`le_eval_wronskian_hessenbergVector_succ`).

This is the Cauchy–Binet expansion `W((R h)_i, (R h)_j) = ∑_{c<d} det R[{i,j},{c,d}] W(h_c, h_d)`
for the constant matrix `R = [A | 𝟙]` acting on the augmented vector `h = (f_1, …, f_d, X f_1)`,
where every summand is nonnegative: the minors by `TP2`-ness of `R`, the Wronskians because `h` is
an interlacing sequence with nonnegative coefficients.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

variable {n : ℕ}

/-- The affine step as a linear combination of the augmented vector `(f_1, …, f_d, X f_1)` with the
rows of `[A | 𝟙]`. -/
lemma tp2AffineStep_eq_sum (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : ℝ)
    (f : Fin (n + 1) → ℝ[X]) (i : Fin (n + 1)) :
    tp2AffineStep A b f i =
      ∑ c : Fin (n + 2), C (tp2StepMatrix A b i.succ c) * tp2AugmentedVector f c := by
  have h := congrFun (tp2StepMatrix_mulVec A b f) i.succ
  simpa [Matrix.mulVec, dotProduct] using h.symm

/-- **Wronskian growth under the Hessenberg step.** -/
theorem le_eval_wronskian_hessenbergVector_succ {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTP2) (hcol : ∀ ⦃i k j : Fin (n + 1)⦄, i ≤ k → A k j ≤ A i j) (k : ℕ)
    {i j a b : Fin (n + 1)} (hij : i < j) (hab : a < b) (x : ℝ) :
    (A i a * A j b - A i b * A j a) *
        (wronskian (hessenbergVector A k a) (hessenbergVector A k b)).eval x ≤
      (wronskian (hessenbergVector A (k + 1) i) (hessenbergVector A (k + 1) j)).eval x := by
  set f := hessenbergVector A k with hf
  have hseq := isInterlacingSeqNonneg_hessenbergVector hA hcol k
  have haug := hseq.tp2AugmentedVector
  have hpair : ∀ ⦃c d⦄, c < d →
      StrictInterl (tp2AugmentedVector f c) (tp2AugmentedVector f d) :=
    List.pairwise_ofFn.mp (isInterlacingSeq_iff_pairwise.mp haug.2)
  have hlead : ∀ c, HasPosLeadingCoeff (tp2AugmentedVector f c) := fun c =>
    (haug.nonnegCoeffs _ (List.mem_ofFn.mpr ⟨c, rfl⟩)).pos_leadingCoeff
      (haug.realRooted _ (List.mem_ofFn.mpr ⟨c, rfl⟩)).1
  have hR := hA.tp2StepMatrix hcol zero_le_one
  have hstep : ∀ i, hessenbergVector A (k + 1) i = ∑ c : Fin (n + 2),
      C (tp2StepMatrix A 1 i.succ c) * tp2AugmentedVector f c := fun i =>
    tp2AffineStep_eq_sum A 1 f i
  have key := le_eval_wronskian_sum_sum (fun c => tp2StepMatrix A 1 i.succ c)
    (fun c => tp2StepMatrix A 1 j.succ c) (tp2AugmentedVector f) x
    (fun c d hcd => mul_nonneg (hR.minor_nonneg (Fin.succ_lt_succ_iff.mpr hij) hcd)
      (wronskian_eval_nonneg_of_strictInterl (hlead d) (hlead c) (hpair hcd) x))
    (k₀ := a.castSucc) (ℓ₀ := b.castSucc) (Fin.castSucc_lt_castSucc_iff.mpr hab)
  rw [← hstep, ← hstep] at key
  simpa using key

end RealRooted

end
