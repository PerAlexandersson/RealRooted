import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.CauchyBinet
import RealRooted.Mathlib.LinearAlgebra.Matrix.Gaussian
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegular

/-!
# Strictifying sign-consistent matrices

This file formalizes Karlin, *Total Positivity*, Vol. I, Chapter V, Section 1,
Proposition 1.2. A positive-minor left factor strictifies a full-column-rank
sign-consistent matrix. Karlin applies this with a Gaussian matrix and then
lets the Gaussian parameter tend to infinity.
-/

public section

open Filter
open scoped BigOperators Topology

namespace Matrix

/-- Positive ordered minors in a left factor strictify a full-column-rank
sign-consistent right factor. -/
theorem IsSignConsistentOrder.isStrictlySignConsistentOrder_mul_of_posMinors
    {S : Type*} [Field S] [LinearOrder S] [IsStrictOrderedRing S]
    {l n m q : ℕ} {L : Matrix (Fin l) (Fin n) S}
    {A : Matrix (Fin n) (Fin m) S}
    (hA : A.IsSignConsistentOrder q)
    (hAinj : Function.Injective A.mulVec)
    (hL : ∀ ⦃rows : Fin q → Fin l⦄ ⦃cols : Fin q → Fin n⦄,
      StrictMono rows → StrictMono cols →
        0 < (L.submatrix rows cols).det) :
    (L * A).IsStrictlySignConsistentOrder q := by
  classical
  intro rows rows' cols cols' hrows hrows' hcols hcols'
  obtain ⟨rows₀, hrows₀, href_ne⟩ :=
    exists_ordered_minor_ne_zero_of_mulVec_injective A hAinj cols hcols
  rcases lt_or_gt_of_ne href_ne with href_neg | href_pos
  · have hneg : ∀ ⦃r : Fin q → Fin l⦄ ⦃c : Fin q → Fin m⦄,
        StrictMono r → StrictMono c →
          ((L * A).submatrix r c).det < 0 := by
      intro r c hr hc
      rw [det_submatrix_mul_eq_sum_powersetCard]
      apply Finset.sum_neg'
      · intro s _
        exact mul_nonpos_of_nonneg_of_nonpos
          (hL hr (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono).le
          (hA.minor_nonpos_of_neg hrows₀ hcols href_neg
            (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono hc)
      · obtain ⟨r₁, hr₁, href₁_ne⟩ :=
          exists_ordered_minor_ne_zero_of_mulVec_injective A hAinj c hc
        have href₁_neg : (A.submatrix r₁ c).det < 0 :=
          lt_of_le_of_ne
            (hA.minor_nonpos_of_neg hrows₀ hcols href_neg hr₁ hc) href₁_ne
        let e := OrderEmbedding.ofStrictMono r₁ hr₁
        refine ⟨Set.powersetCard.ofFinEmbEquiv e, Finset.mem_univ _, ?_⟩
        simpa [e] using mul_neg_of_pos_of_neg (hL hr hr₁) href₁_neg
    exact mul_pos_of_neg_of_neg (hneg hrows hcols) (hneg hrows' hcols')
  · have hpos : ∀ ⦃r : Fin q → Fin l⦄ ⦃c : Fin q → Fin m⦄,
        StrictMono r → StrictMono c →
          0 < ((L * A).submatrix r c).det := by
      intro r c hr hc
      rw [det_submatrix_mul_eq_sum_powersetCard]
      apply Finset.sum_pos'
      · intro s _
        exact mul_nonneg
          (hL hr (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono).le
          (hA.minor_nonneg_of_pos hrows₀ hcols href_pos
            (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono hc)
      · obtain ⟨r₁, hr₁, href₁_ne⟩ :=
          exists_ordered_minor_ne_zero_of_mulVec_injective A hAinj c hc
        have href₁_pos : 0 < (A.submatrix r₁ c).det :=
          lt_of_le_of_ne
            (hA.minor_nonneg_of_pos hrows₀ hcols href_pos hr₁ hc) href₁_ne.symm
        let e := OrderEmbedding.ofStrictMono r₁ hr₁
        refine ⟨Set.powersetCard.ofFinEmbEquiv e, Finset.mem_univ _, ?_⟩
        simpa [e] using mul_pos (hL hr hr₁) href₁_pos
    exact mul_pos (hpos hrows hcols) (hpos hrows' hcols')

/-- Karlin's Gaussian left multiplier strictifies a full-column-rank
sign-consistent matrix. -/
theorem IsSignConsistentOrder.isStrictlySignConsistentOrder_gaussianMatrix_mul
    {n m q : ℕ} {A : Matrix (Fin n) (Fin m) ℝ}
    (hA : A.IsSignConsistentOrder q) (hAinj : Function.Injective A.mulVec)
    {a : ℝ} (ha : 0 < a) :
    (gaussianMatrix n a * A).IsStrictlySignConsistentOrder q := by
  apply hA.isStrictlySignConsistentOrder_mul_of_posMinors hAinj
  intro rows cols hrows hcols
  exact det_gaussianMatrix_submatrix_pos a rows cols ha hrows hcols

/-- Gaussian left multiplication converges entrywise to the original matrix. -/
theorem tendsto_gaussianMatrix_mul_atTop {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) :
    Tendsto (fun a => gaussianMatrix n a * A) atTop (𝓝 A) := by
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  have hG : ∀ k, Tendsto (fun a => gaussianMatrix n a i k) atTop
      (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i k)) := by
    intro k
    exact tendsto_pi_nhds.mp
      (tendsto_pi_nhds.mp (tendsto_gaussianMatrix_atTop n) i) k
  have hsum :
      Tendsto (fun a => ∑ k, gaussianMatrix n a i k * A k j) atTop
        (𝓝 (∑ k, (1 : Matrix (Fin n) (Fin n) ℝ) i k * A k j)) :=
    tendsto_finset_sum Finset.univ (fun k _ => (hG k).mul_const (A k j))
  rw [show (∑ k, (1 : Matrix (Fin n) (Fin n) ℝ) i k * A k j) = A i j by
    rw [← Matrix.mul_apply, Matrix.one_mul]] at hsum
  simpa only [Matrix.mul_apply] using hsum

end Matrix
