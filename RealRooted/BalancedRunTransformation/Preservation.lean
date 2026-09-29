import RealRooted.BalancedRunTransformation
import RealRooted.BinaryRunTransformation.PointingPencil
import RealRooted.ClassicalHurwitzMatrix.Stability.HermiteBiehler

/-!
# Stability preservation for the balanced run transformation

This file connects the balanced kernel to the normalized diagonal contraction.
The contraction backend is shared with the binary-run pointing construction.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

open BorceaBranden

private theorem balancedRun_weighted_sum
    (n m k : ℕ) (hm : m ≤ n) :
    (∑ r ∈ Finset.range (n + 1),
      Nat.choose m r * Nat.choose (n - m) r * Nat.choose r k) =
        Nat.choose m k * Nat.choose (n - k) m := by
  by_cases hkB : k ≤ n - m
  · have hrestrict :
        (∑ r ∈ Finset.range (n + 1),
          Nat.choose m r * Nat.choose (n - m) r * Nat.choose r k) =
        ∑ r ∈ Finset.range (n - m + 1),
          Nat.choose m r * Nat.choose (n - m) r * Nat.choose r k := by
      symm
      apply Finset.sum_subset (Finset.range_subset_range.mpr (by lia))
      intro r hrBig hrSmall
      have hlt : n - m < r := by
        simp only [Finset.mem_range, not_lt] at hrSmall
        lia
      rw [Nat.choose_eq_zero_of_lt hlt]
      simp
    rw [hrestrict]
    have hv := Nat.weighted_vandermonde m (n - m) (n - m) k hkB
    have hrewrite :
        (∑ r ∈ Finset.range (n - m + 1),
          Nat.choose m r * Nat.choose (n - m) r * Nat.choose r k) =
        ∑ r ∈ Finset.range (n - m + 1),
          Nat.choose m r * Nat.choose (n - m) (n - m - r) *
            Nat.choose r k := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrle : r ≤ n - m := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      rw [Nat.choose_symm hrle]
    rw [hrewrite, hv]
    by_cases hkm : k ≤ m
    · have htop : m - k + (n - m) = n - k := by lia
      rw [htop]
      have hcomp : n - k - (n - m - k) = m := by lia
      have hsym := Nat.choose_symm (by lia : n - m - k ≤ n - k)
      rw [hcomp] at hsym
      rw [← hsym]
    · have hmk : m < k := Nat.lt_of_not_ge hkm
      rw [Nat.choose_eq_zero_of_lt hmk]
      simp
  · have hBk : n - m < k := Nat.lt_of_not_ge hkB
    have hleft :
        (∑ r ∈ Finset.range (n + 1),
          Nat.choose m r * Nat.choose (n - m) r * Nat.choose r k) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      by_cases hrB : r ≤ n - m
      · rw [Nat.choose_eq_zero_of_lt (lt_of_le_of_lt hrB hBk)]
        simp
      · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hrB)]
        simp
    rw [hleft]
    by_cases hkm : k ≤ m
    · have hkn : k ≤ n := hkm.trans hm
      have hnm : n - k < m := by lia
      rw [Nat.choose_eq_zero_of_lt hnm]
      simp
    · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkm)]
      simp

private theorem choose_mul_complement (n m k : ℕ) :
    Nat.choose n k * Nat.choose (n - k) m =
      Nat.choose n m * Nat.choose (n - m) k := by
  have hk := Nat.choose_mul (n := n) (k := m + k) (s := k) (by lia)
  have hm := Nat.choose_mul (n := n) (k := m + k) (s := m) (by lia)
  have hsym : Nat.choose (m + k) m = Nat.choose (m + k) k := by
    simpa [Nat.add_sub_cancel_left] using
      Nat.choose_symm (n := m + k) (k := k) (by lia)
  calc
    Nat.choose n k * Nat.choose (n - k) m =
        Nat.choose n (m + k) * Nat.choose (m + k) k := by
          simpa using hk.symm
    _ = Nat.choose n (m + k) * Nat.choose (m + k) m := by rw [hsym]
    _ = Nat.choose n m * Nat.choose (n - m) k := by simpa using hm

/-- Coefficients of a shifted balanced run kernel.  This is the normalization
matched by `normalizedDiagonalContraction`. -/
theorem coeff_comp_balancedRunPolynomial
    (n m k : ℕ) (hm : m ≤ n) :
    ((balancedRunPolynomial n m).comp (X + 1)).coeff k =
      ((Nat.choose m k : ℝ) * (Nat.choose (n - m) k : ℝ)) /
        (Nat.choose n k : ℝ) := by
  rw [balancedRunPolynomial]
  change ((Polynomial.compRingHom (X + 1))
    (∑ r ∈ Finset.range (n + 1),
      monomial r
        (((Nat.choose m r : ℝ) * (Nat.choose (n - m) r : ℝ)) /
          (Nat.choose n m : ℝ)))).coeff k = _
  rw [map_sum]
  simp only [Polynomial.coe_compRingHom_apply, Polynomial.finsetSum_coeff,
    monomial_comp, coeff_C_mul, coeff_X_add_one_pow]
  by_cases hk : k ≤ n
  · have hdenm : (Nat.choose n m : ℝ) ≠ 0 := Nat.cast_choose_ne_zero hm
    have hdenk : (Nat.choose n k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero hk
    have hsumNat := balancedRun_weighted_sum n m k hm
    have hsumReal :
        (∑ r ∈ Finset.range (n + 1),
          (Nat.choose m r : ℝ) * (Nat.choose (n - m) r : ℝ) *
            (Nat.choose r k : ℝ)) =
          (Nat.choose m k : ℝ) * (Nat.choose (n - k) m : ℝ) := by
      exact_mod_cast hsumNat
    calc
      (∑ x ∈ Finset.range (n + 1),
          (Nat.choose m x : ℝ) * (Nat.choose (n - m) x : ℝ) /
              (Nat.choose n m : ℝ) * (Nat.choose x k : ℝ)) =
          (∑ x ∈ Finset.range (n + 1),
            (Nat.choose m x : ℝ) * (Nat.choose (n - m) x : ℝ) *
              (Nat.choose x k : ℝ)) / (Nat.choose n m : ℝ) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = ((Nat.choose m k : ℝ) * (Nat.choose (n - m) k : ℝ)) /
          (Nat.choose n k : ℝ) := by
        rw [hsumReal]
        field_simp [hdenm, hdenk]
        have hchoose := congrArg (Nat.choose m k * ·)
          (choose_mul_complement n m k)
        have hchooseReal :
            (Nat.choose m k : ℝ) *
                ((Nat.choose n k : ℝ) * (Nat.choose (n - k) m : ℝ)) =
              (Nat.choose m k : ℝ) *
                ((Nat.choose n m : ℝ) * (Nat.choose (n - m) k : ℝ)) := by
          exact_mod_cast hchoose
        simpa [mul_assoc, mul_comm, mul_left_comm] using hchooseReal
  · have hkn : n < k := Nat.lt_of_not_ge hk
    have hmk : m < k := hm.trans_lt hkn
    rw [Nat.choose_eq_zero_of_lt hmk]
    simp only [Nat.cast_zero, zero_mul, zero_div]
    apply Finset.sum_eq_zero
    intro r hr
    have hrn : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    rw [Nat.choose_eq_zero_of_lt (hrn.trans_lt hkn)]
    simp

/-- Fixed-range expansion of a shifted balanced transform. -/
theorem comp_balancedRunTransform_eq_sum_range
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) :
    (balancedRunTransform n p).comp (X + 1) =
      ∑ m ∈ Finset.range (n + 1),
        C (p.coeff m) * (balancedRunPolynomial n m).comp (X + 1) := by
  rw [balancedRunTransform, Polynomial.basisTransform, Polynomial.sum_def]
  change (Polynomial.compRingHom (X + 1))
      (∑ m ∈ p.support, C (p.coeff m) * balancedRunPolynomial n m) = _
  rw [map_sum]
  simp_rw [map_mul, Polynomial.coe_compRingHom_apply, C_comp]
  apply Finset.sum_subset
  · intro m hm
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le <|
      (Polynomial.le_natDegree_of_ne_zero
        (Polynomial.mem_support_iff.mp hm)).trans hp
  · intro m hmrange hmsupport
    rw [Polynomial.notMem_support_iff.mp hmsupport]
    simp

/-- Coefficient formula for the shifted balanced transform. -/
theorem coeff_comp_balancedRunTransform_eq_sum_range
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (k : ℕ) :
    ((balancedRunTransform n p).comp (X + 1)).coeff k =
      ∑ m ∈ Finset.range (n + 1),
        p.coeff m *
          (((Nat.choose m k : ℝ) * (Nat.choose (n - m) k : ℝ)) /
            (Nat.choose n k : ℝ)) := by
  rw [comp_balancedRunTransform_eq_sum_range hp,
    Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m hm
  rw [coeff_C_mul, coeff_comp_balancedRunPolynomial]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hm)

/-- The shifted balanced transform has degree at most `⌊n/2⌋` on the
degree-`n` input box. -/
theorem natDegree_comp_balancedRunTransform_le
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) :
    ((balancedRunTransform n p).comp (X + 1)).natDegree ≤ n / 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_comp_balancedRunTransform_eq_sum_range hp]
  apply Finset.sum_eq_zero
  intro m hm
  have hmle : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  have htwok : n < 2 * k := by lia
  by_cases hmk : k ≤ m
  · have hother : n - m < k := by lia
    rw [Nat.choose_eq_zero_of_lt hother]
    simp
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hmk)]
    simp

private theorem balancedRunHomogenizedSource_diagonal_scalar
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) {k : ℕ} (hk : k ≤ n) :
    (∑ m ∈ Finset.range (n + 1),
        p.coeff m * (Nat.choose m k : ℝ) *
          (Nat.choose (n - m) k : ℝ)) =
      (Nat.choose n k : ℝ) *
        ((balancedRunTransform n p).comp (X + 1)).coeff k := by
  rw [coeff_comp_balancedRunTransform_eq_sum_range hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hchoose : (Nat.choose n k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero hk
  field_simp

/-- Exact diagonal coefficient of the stable source used for the balanced
transform. -/
theorem sourceCoefficientGeneral_balancedRunHomogenizedSource_diagonal
    {n : ℕ} (hn : 1 ≤ n) {p : ℝ[X]} (hp : p.natDegree ≤ n)
    {k : ℕ} (hk : k ≤ n) :
    sourceCoefficientGeneral (binaryRunHomogenizedSource (n - 1) p 1)
        (binaryRunSourceIndex k k) =
      MvPolynomial.C
          ((Nat.choose n k : ℂ) *
            ((balancedRunTransform n p).comp (X + 1)).coeff k) *
        MvPolynomial.X 0 ^ (n - 2 * k) := by
  rw [sourceCoefficientGeneral_binaryRunHomogenizedSource_monomial]
  have htop : n - 1 + 2 = n + 1 := by lia
  have hsourceDegree : n - 1 + 1 = n := by lia
  rw [htop]
  simp only [coeff_scalePolynomial, one_pow, mul_one, hsourceDegree]
  have hscalar := congrArg Complex.ofReal
    (balancedRunHomogenizedSource_diagonal_scalar hp hk)
  push_cast at hscalar
  rw [hscalar, MvPolynomial.C_mul_X_pow_eq_monomial]
  have hindex : binaryRunOutputIndex (n - k - k) =
      Finsupp.single 0 (n - 2 * k) := by
    ext i
    fin_cases i
    · simp [binaryRunOutputIndex]
      lia
    · simp [binaryRunOutputIndex]
  rw [hindex]

/-- Normalized diagonal contraction of the stable source is the signed parity
lift of the shifted balanced transform. -/
theorem normalizedDiagonalContraction_balancedRunHomogenizedSource
    {n : ℕ} (hn : 1 ≤ n) {p : ℝ[X]} (hp : p.natDegree ≤ n) :
    normalizedDiagonalContraction n
        (binaryRunHomogenizedSource (n - 1) p 1) =
      (complexify (signedParityLift n
        ((balancedRunTransform n p).comp (X + 1)))).eval₂
          (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
          (MvPolynomial.X 0) := by
  rw [normalizedDiagonalContraction_eq_diagonal_sum,
    eval₂_complexify_signedParityLift_eq_sum
      (natDegree_comp_balancedRunTransform_le hp)]
  apply Fintype.sum_congr
  intro k
  have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.isLt
  rw [sourceCoefficientGeneral_balancedRunHomogenizedSource_diagonal hn hp hk]
  have hchoose : (Nat.choose n (k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hk)
  have hscalar :
      ((-1 : ℂ) ^ (k : ℕ) * (Nat.choose n (k : ℕ) : ℂ)⁻¹) *
          ((Nat.choose n (k : ℕ) : ℂ) *
            (((balancedRunTransform n p).comp (X + 1)).coeff k : ℂ)) =
        (-1 : ℂ) ^ (k : ℕ) *
          (((balancedRunTransform n p).comp (X + 1)).coeff k : ℂ) := by
    field_simp
  rw [← mul_assoc, ← MvPolynomial.C_mul, hscalar]

private theorem degreeOf_balancedRunHomogenizedSource_source_le
    (n : ℕ) (hn : 1 ≤ n) (p : ℝ[X]) (i : Fin 2) :
    (binaryRunHomogenizedSource (n - 1) p 1).degreeOf (Sum.inr i) ≤ n := by
  rw [binaryRunHomogenizedSource_eq_sum]
  refine (MvPolynomial.degreeOf_sum_le (Sum.inr i)
    (Finset.range (n - 1 + 2)) (fun m =>
      MvPolynomial.C ((scalePolynomial 1 p).coeff m : ℂ) *
        (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0)) ^ m *
          (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1)) ^
            (n - 1 + 1 - m))).trans ?_
  apply Finset.sup_le
  intro m hm
  have hmle : m ≤ n := by
    simp only [Finset.mem_range] at hm
    lia
  have hfirst :
      (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0) :
        MvPolynomial (Fin 2 ⊕ Fin 2) ℂ).degreeOf (Sum.inr i) ≤ 1 :=
    (MvPolynomial.degreeOf_add_le _ _ _).trans (by
      simp only [MvPolynomial.degreeOf_X]
      grind)
  have hsecond :
      (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1) :
        MvPolynomial (Fin 2 ⊕ Fin 2) ℂ).degreeOf (Sum.inr i) ≤ 1 :=
    (MvPolynomial.degreeOf_add_le _ _ _).trans (by
      simp only [MvPolynomial.degreeOf_X]
      grind)
  calc
    _ ≤
        (MvPolynomial.C ((scalePolynomial 1 p).coeff m : ℂ) *
          (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0)) ^ m :
            MvPolynomial (Fin 2 ⊕ Fin 2) ℂ).degreeOf (Sum.inr i) +
          ((MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 1)) ^
            (n - 1 + 1 - m) : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ).degreeOf
              (Sum.inr i) := MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ (0 + m) + (n - m) := by
      have hsub : n - 1 + 1 - m = n - m := by lia
      rw [hsub]
      exact Nat.add_le_add
        ((MvPolynomial.degreeOf_mul_le _ _ _).trans <|
          Nat.add_le_add (by simp)
            ((MvPolynomial.degreeOf_pow_le _ _ _).trans <| by
              simpa using Nat.mul_le_mul_left m hfirst))
        ((MvPolynomial.degreeOf_pow_le _ _ _).trans <| by
          simpa using Nat.mul_le_mul_left (n - m) hsecond)
    _ = n := by lia

/-- The contracted signed-parity lift of the balanced transform is stable or
zero on the increasing-degree range. -/
theorem mvUpperHalfPlaneStableOrZero_balancedRunSignedParityLift
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hp0 : p ≠ 0) (hdegree : p.natDegree ≤ (n + 1) / 2) :
    MvUpperHalfPlaneStableOrZero
      ((complexify (signedParityLift n
        ((balancedRunTransform n p).comp (X + 1)))).eval₂
          (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
          (MvPolynomial.X 0)) := by
  have hsmall : p.natDegree ≤ n - 1 := by
    exact hdegree.trans (by grind)
  have hsource :=
    (mvUpperHalfPlaneStable_binaryRunHomogenizedSource hp hp0 hsmall
      (t := 1) one_pos).orZero
  have hcontracted := hsource.normalizedDiagonalContraction
    (fun i => degreeOf_balancedRunHomogenizedSource_source_le n (by lia) p i)
  rw [normalizedDiagonalContraction_balancedRunHomogenizedSource (by lia)
    (hsmall.trans (by lia))] at hcontracted
  exact hcontracted

/-- Splitness of a signed parity lift descends to the original polynomial. -/
theorem splits_of_signedParityLift_splits
    {n : ℕ} {q : ℝ[X]} (hq : q.natDegree ≤ n / 2)
    (h : (signedParityLift n q).Splits) : q.Splits := by
  by_cases hq0 : q = 0
  · simp [hq0]
  have hlift0 : signedParityLift n q ≠ 0 :=
    fun h0 => hq0 ((signedParityLift_eq_zero_iff hq).mp h0)
  apply splits_of_forall_aeval_im_eq_zero
  intro w hw
  by_cases hw0 : w = 0
  · simp [hw0]
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z ^ 2 = -w⁻¹ := by
    obtain ⟨z, hzroot⟩ := Complex.exists_root
      (f := X ^ 2 - C (-w⁻¹))
      (by rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num)
    have hz' : z ^ 2 - (-w⁻¹) = 0 := by
      simpa [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C] using hzroot
    exact ⟨z, by linear_combination hz'⟩
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [hw0] at hz
  have hsub : -(z ^ 2)⁻¹ = w := by
    rw [hz]
    simp
  have hzroot : (signedParityLift n q).aeval z = 0 := by
    rw [aeval_signedParityLift hq hz0, hsub, hw, mul_zero]
  have hzim : z.im = 0 :=
    im_eq_zero_of_aeval_eq_zero hlift0 h hzroot
  have hsq : (z ^ 2).im = 0 := by
    rw [pow_two, Complex.mul_im, hzim]
    ring
  rw [← hsub, Complex.neg_im, Complex.inv_im, hsq]
  simp

/-- On the increasing-degree range, the balanced run transform preserves the
Pólya-frequency cone. -/
theorem IsPFPolynomial.balancedRunTransform
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hdegree : p.natDegree ≤ (n + 1) / 2) :
    IsPFPolynomial (balancedRunTransform n p) := by
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    hp.hasNonnegCoeffs.balancedRunTransform
  by_cases hp0 : p = 0
  · subst p
    simp
  right
  let q := (RealRooted.balancedRunTransform n p).comp (X + 1)
  have hqdegree : q.natDegree ≤ n / 2 := by
    exact natDegree_comp_balancedRunTransform_le
      (hdegree.trans (by grind))
  have hlift := mvUpperHalfPlaneStableOrZero_balancedRunSignedParityLift
    hn hp hp0 hdegree
  have hpencil : MvUpperHalfPlaneStableOrZero
      (bivariatePencil (signedParityLift n q) 0) := by
    simpa [bivariatePencil, q] using hlift
  have hqsplits : q.Splits := by
    rcases hpencil.eq_zero_pair_or_stablePencil with hzero | hstable
    · have hqzero : q = 0 :=
        (signedParityLift_eq_zero_iff hqdegree).mp hzero.1
      simp [hqzero]
    · have hliftStable :
          IsUpperHalfPlaneStable (complexify (signedParityLift n q)) := by
        intro z hz
        simpa using hstable z Complex.I hz (by norm_num)
      exact splits_of_signedParityLift_splits hqdegree
        hliftStable.splits_complexify
  have hback := hqsplits.comp_X_sub_C 1
  simpa [q, Polynomial.comp_assoc] using hback

end RealRooted
