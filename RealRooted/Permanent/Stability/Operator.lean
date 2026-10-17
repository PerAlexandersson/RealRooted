import RealRooted.LiebSokalPointwise

/-!
# The stability-preserving operator in the monotone-column proof

This file isolates the analytic step in Proposition 3.3 of P. Brändén,
J. Haglund, M. Visontai, and D. G. Wagner, *Proof of the monotone column
permanent conjecture*, arXiv:1010.2565v2. The repository's pointwise
Lieb--Sokal theorem proves a weighted form of the operator directly.
-/

open scoped BigOperators

namespace RealRooted

noncomputable section

/-- If `P` is real stable, then adjoining a fresh variable by
`k P + z D_c P` preserves real stability for positive `k` and a nonnegative
direction `c`. This is the operator used in the Ferrers-matrix induction of
Brändén--Haglund--Visontai--Wagner, Proposition 3.3. -/
theorem MvRealStable.positive_C_mul_add_fresh_mul_directionalPDeriv
    {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℝ}
    (hP : MvRealStable P) (c : σ → ℝ) (hc : ∀ i, 0 ≤ c i)
    (k : ℝ) (hk : 0 < k) :
    MvRealStable
      (MvPolynomial.C k * MvPolynomial.rename some P +
        MvPolynomial.X none *
          MvPolynomial.rename some (directionalPDeriv c P)) := by
  let d : σ → ℝ := fun i => c i / k
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    exact div_nonneg (hc i) hk.le
  have hscale :
      MvPolynomial.C k * directionalPDeriv d P =
        directionalPDeriv c P := by
    unfold directionalPDeriv
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, ← MvPolynomial.C_mul]
    have hcoeff : k * (c i / k) = c i := by
      calc
        k * (c i / k) = (c i / k) * k := mul_comm _ _
        _ = c i := div_mul_cancel₀ _ hk.ne'
    rw [hcoeff]
  have hstable := (hP.directionalPDeriv_pencil d hd).C_mul hk.ne'
  have hrewrite :
      MvPolynomial.C k *
          (MvPolynomial.rename some P +
            MvPolynomial.X none *
              MvPolynomial.rename some (directionalPDeriv d P)) =
        MvPolynomial.C k * MvPolynomial.rename some P +
          MvPolynomial.X none *
            MvPolynomial.rename some (directionalPDeriv c P) := by
    rw [mul_add]
    congr 1
    calc
      MvPolynomial.C k *
            (MvPolynomial.X none *
              MvPolynomial.rename some (directionalPDeriv d P)) =
          MvPolynomial.X none *
            MvPolynomial.rename some
              (MvPolynomial.C k * directionalPDeriv d P) := by
        simp only [map_mul, MvPolynomial.rename_C]
        ac_rfl
      _ = MvPolynomial.X none *
            MvPolynomial.rename some (directionalPDeriv c P) := by
        rw [hscale]
  rw [hrewrite] at hstable
  exact hstable

end

end RealRooted
