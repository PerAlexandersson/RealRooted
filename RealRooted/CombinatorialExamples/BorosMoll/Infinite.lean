import RealRooted.BrandenLC.Infinite
import RealRooted.CombinatorialExamples.BorosMoll

/-!
# Infinite log-concavity of the Boros–Moll rows

The row result uses the Xie–Zhang real-rootedness theorem already formalized in
the repository and Brändén's preservation theorem. The cited result is P.
Brändén, “Iterated sequences and the geometry of zeros”, J. reine angew. Math.
658 (2011), 115–131. The proof here is a different stability-functional /
Laguerre argument found by Aristotle.
-/

namespace RealRooted.BorosMoll

open Polynomial Finset

/-- The generating polynomial of the Boros–Moll coefficient row `d(n)`. -/
noncomputable def borosMollRow (n : ℕ) : ℝ[X] :=
  ∑ i ∈ range (n + 1), C (bmCoeff n i) * X ^ i

private lemma borosMollRow_coeff (n i : ℕ) :
    (borosMollRow n).coeff i = if i < n + 1 then bmCoeff n i else 0 := by
  unfold borosMollRow
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

private lemma bmCoeff_nonneg (n i : ℕ) : 0 ≤ bmCoeff n i := by
  unfold bmCoeff
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro k hk
    positivity

private lemma borosMollRow_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (borosMollRow n) := by
  intro i
  rw [borosMollRow_coeff]
  split_ifs
  · exact bmCoeff_nonneg n i
  · exact le_rfl

private lemma borosMollRow_natDegree (n : ℕ) :
    (borosMollRow n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [borosMollRow_coeff, ite_eq_right]
    have : n < i := by exact_mod_cast hi
    lia
  · rw [borosMollRow_coeff, ite_eq_left (by lia)]
    exact (bmCoeff_self_pos n).ne'

private lemma logConcavityTransform_borosMollRow (n : ℕ) :
    RealRooted.Branden.logConcavityTransform (borosMollRow n) = bmM n := by
  ext i
  rw [RealRooted.Branden.coeff_logConcavityTransform, borosMollRow_natDegree]
  unfold bmM
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  by_cases hi : i ≤ n
  · have hi' : i < n + 1 := by lia
    rw [ite_eq_left hi]
    simp only [borosMollRow_coeff, ite_eq_left hi']
    by_cases hi0 : i = 0
    · subst hi0
      simp [bmL, hi]
    · simp only [ite_eq_right hi0]
      have him : i - 1 < n + 1 := by lia
      rw [ite_eq_left him]
      by_cases hilast : i + 1 = n + 1
      · have hzero : bmCoeff n (i + 1) = 0 := by
          calc
            bmCoeff n (i + 1) = bmCoeff n (n + 1) := congrArg (bmCoeff n) hilast
            _ = 0 := bmCoeff_succ_self n
        unfold bmL
        rw [ite_eq_right hi0, hzero]
        simp [hi, hilast]
      · have hip : i + 1 < n + 1 := by lia
        rw [ite_eq_left hip]
        simp [bmL, hi, hi0]
  · have hi' : ¬i < n + 1 := by lia
    rw [ite_eq_right hi, ite_eq_right (by simp [hi'])]

private lemma bmM_hasNonnegCoeffs (n : ℕ) (hn : 1 ≤ n) :
    HasNonnegCoeffs (bmM n) := by
  obtain ⟨hm0, hdeg, hs, _, hroots⟩ := bmM_roots n hn
  intro i
  rw [hs.eq_prod_roots]
  rw [coeff_C_mul]
  refine mul_nonneg ?_ (RealRooted.Branden.coeff_prod_X_sub_C_nonneg _ ?_ i)
  · rw [leadingCoeff, hdeg]
    unfold bmM
    simp only [finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [mem_range, lt_add_iff_pos_right, Order.lt_one_iff, ↓reduceIte, bmL,
        bmCoeff_succ_self, mul_zero, sub_zero]
    exact sq_nonneg _
  · intro r hr
    exact (hroots r hr).le

/-- The Boros–Moll coefficient rows are infinitely log-concave. -/
theorem borosMollRow_isInfinitelyLogConcave (n : ℕ) (hn : 1 ≤ n) :
    RealRooted.Branden.IsInfinitelyLogConcave (borosMollRow n) := by
  intro k
  cases k with
  | zero =>
    simpa only [Function.iterate_zero_apply] using borosMollRow_hasNonnegCoeffs n
  | succ k =>
    rw [Function.iterate_succ_apply, logConcavityTransform_borosMollRow]
    exact (RealRooted.Branden.IsPFPolynomial.isInfinitelyLogConcave
      (IsPFPolynomial.of_realRooted_nonneg (bmM_hasNonnegCoeffs n hn)
        (bmM_roots n hn).2.2.1)) k

end RealRooted.BorosMoll
