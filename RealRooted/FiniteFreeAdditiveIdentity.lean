import RealRooted.FiniteFreeAdditive
import RealRooted.ElementaryDifferential
import RealRooted.LiebSokalOperator.Linearity
import RealRooted.MultiaffineReciprocal
import RealRooted.Polarization

/-!
# Finite-free additive convolution differential identity

This module contains the algebraic bridge from polarized multiaffine
polynomials to finite-free additive convolution.  Stability and
real-rootedness preservation are deliberately left to a later layer.
-/

open Polynomial BigOperators

namespace RealRooted

noncomputable section

private theorem signedMultiaffineReciprocal_polarization_eq_sum
    (d : ℕ) (p : ℂ[X]) :
    signedMultiaffineReciprocal (polarization d p) =
      ∑ i ∈ Finset.range (d + 1),
        MvPolynomial.C
          ((-1 : ℂ) ^ (d - i) * p.coeff (d - i) / (d.choose i : ℂ)) *
          MvPolynomial.esymm (Fin d) ℂ i := by
  rw [polarization_eq_sum]
  rw [signedMultiaffineReciprocal_sum]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [Nat.add_sub_cancel]
  rw [signedMultiaffineReciprocal_C_mul
      (MvPolynomial.IsMultiaffine.esymm _),
    signedMultiaffineReciprocal_esymm d (d - i) (by lia)]
  rw [Nat.sub_sub_self hi']
  rw [Nat.choose_symm hi']
  rw [← mul_assoc, ← MvPolynomial.C_mul]
  congr 1
  ring

private theorem polarization_reflect_eq_sum (d : ℕ) (p : ℂ[X]) :
    polarization d p =
      ∑ j ∈ Finset.range (d + 1),
        MvPolynomial.C (p.coeff (d - j) / (d.choose j : ℂ)) *
          MvPolynomial.esymm (Fin d) ℂ (d - j) := by
  rw [polarization_eq_sum]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [Nat.add_sub_cancel]
  rw [Nat.choose_symm hj']

private theorem diagonal_applyNegDifferential_term
    (d i j : ℕ) (hij : i + j ≤ d) (a b : ℂ) :
    diagonalProjection d
        (applyNegDifferential
          (MvPolynomial.C ((-1 : ℂ) ^ (d - i) * a / (d.choose i : ℂ)) *
            MvPolynomial.esymm (Fin d) ℂ i)
          (MvPolynomial.C (b / (d.choose j : ℂ)) *
            MvPolynomial.esymm (Fin d) ℂ (d - j))) =
      Polynomial.C
          ((-1 : ℂ) ^ d * a * b *
            ((i + j).choose j : ℂ) * (d.choose (d - i - j) : ℂ) /
              ((d.choose i : ℂ) * (d.choose j : ℂ))) *
        Polynomial.X ^ (d - i - j) := by
  have hijd : i ≤ d - j := by lia
  rw [applyNegDifferential_C_mul_left,
    applyNegDifferential_C_mul_right,
    applyNegDifferential_esymm i (d - j), if_pos hijd]
  simp only [Fintype.card_fin]
  rw [← MvPolynomial.smul_eq_C_mul, map_smul]
  rw [← MvPolynomial.smul_eq_C_mul, map_smul]
  rw [← MvPolynomial.smul_eq_C_mul, map_smul]
  rw [map_nsmul, diagonalProjection_esymm]
  rw [show d + i - (d - j) = i + j by lia]
  rw [show d - j - i = d - i - j by lia]
  rw [← Nat.choose_symm (Nat.le_add_right i j)]
  simp only [Nat.add_sub_cancel_left]
  simp only [Polynomial.smul_eq_C_mul]
  rw [nsmul_eq_mul]
  have hchoose :
      ((i + j).choose j : ℂ[X]) = Polynomial.C ((i + j).choose j : ℂ) :=
    (map_natCast (Polynomial.C : ℂ →+* ℂ[X]) _).symm
  rw [hchoose]
  have hi : i ≤ d := by lia
  have hscalar :
      ((((-1 : ℂ) ^ (d - i) * a / (d.choose i : ℂ)) *
          (b / (d.choose j : ℂ))) * (-1 : ℂ) ^ i) *
          (i + j).choose j * (d.choose (d - i - j) : ℂ) =
        (-1 : ℂ) ^ d * a * b *
          ((i + j).choose j : ℂ) * (d.choose (d - i - j) : ℂ) /
            ((d.choose i : ℂ) * (d.choose j : ℂ)) := by
    have hsign : (-1 : ℂ) ^ (d - i) * (-1 : ℂ) ^ i = (-1 : ℂ) ^ d := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    calc
      _ = ((-1 : ℂ) ^ (d - i) * (-1 : ℂ) ^ i) * a * b *
          ((i + j).choose j : ℂ) * (d.choose (d - i - j) : ℂ) /
            ((d.choose i : ℂ) * (d.choose j : ℂ)) := by ring
      _ = _ := by rw [hsign]
  rw [← mul_assoc, ← Polynomial.C_mul]
  rw [← mul_assoc, ← Polynomial.C_mul]
  rw [← mul_assoc, ← Polynomial.C_mul]
  rw [← mul_assoc, ← Polynomial.C_mul]
  rw [hscalar]

private theorem sum_square_eq_triangle
    {A : Type*} [AddCommMonoid A] (d : ℕ) (F : ℕ → ℕ → A) :
    (∑ i ∈ Finset.range (d + 1),
      ∑ j ∈ Finset.range (d + 1), if i + j ≤ d then F i j else 0) =
    ∑ i ∈ Finset.range (d + 1),
      ∑ j ∈ Finset.range (d + 1 - i), F i j := by
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hj
    lia
  · intro hj
    constructor <;> lia

private theorem C_map_finiteFreeAdditiveConvolutionCoeff
    (d k : ℕ) (p q : ℝ[X]) :
    Polynomial.C
        (Complex.ofRealHom (finiteFreeAdditiveConvolutionCoeff d p q k)) =
      ∑ i ∈ Finset.range (k + 1),
        Polynomial.C
            ((finiteFreeAdditiveConvolutionGamma d i (k - i) : ℂ) *
              (p.map Complex.ofRealHom).coeff (d - i) *
              (q.map Complex.ofRealHom).coeff (d - (k - i))) := by
  unfold finiteFreeAdditiveConvolutionCoeff
  rw [map_sum]
  rw [map_sum (Polynomial.C : ℂ →+* ℂ[X])]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.coeff_map, map_mul]
  rfl

/-- Signed reciprocal polarization followed by negative differential
evaluation and diagonal projection realizes finite-free additive convolution.
The identity is algebraic; it does not assert stability or real-rootedness. -/
theorem diagonal_applyNegDifferential_signedPolarization
    (d : ℕ) (p q : ℝ[X]) :
    diagonalProjection d
        (applyNegDifferential
          (signedMultiaffineReciprocal
            (polarization d (p.map Complex.ofRealHom)))
          (polarization d (q.map Complex.ofRealHom))) =
      Polynomial.C ((-1 : ℂ) ^ d) *
        (finiteFreeAdditiveConvolution d p q).map Complex.ofRealHom := by
  rw [signedMultiaffineReciprocal_polarization_eq_sum]
  rw [polarization_reflect_eq_sum]
  rw [applyNegDifferential_doubleSum]
  rw [map_sum]
  simp_rw [map_sum]
  have hterm (i j : ℕ) (hi : i ≤ d) (hj : j ≤ d) :
      diagonalProjection d
          (applyNegDifferential
            (MvPolynomial.C ((-1 : ℂ) ^ (d - i) *
              (p.map Complex.ofRealHom).coeff (d - i) / (d.choose i : ℂ)) *
              MvPolynomial.esymm (Fin d) ℂ i)
            (MvPolynomial.C ((q.map Complex.ofRealHom).coeff (d - j) /
              (d.choose j : ℂ)) * MvPolynomial.esymm (Fin d) ℂ (d - j))) =
        if i + j ≤ d then
          Polynomial.C
              ((-1 : ℂ) ^ d *
                (finiteFreeAdditiveConvolutionGamma d i j : ℂ) *
                (p.map Complex.ofRealHom).coeff (d - i) *
                (q.map Complex.ofRealHom).coeff (d - j)) *
            Polynomial.X ^ (d - i - j)
        else 0 := by
    by_cases hij : i + j ≤ d
    · rw [if_pos hij]
      rw [diagonal_applyNegDifferential_term d i j hij]
      have hgamma :
          (finiteFreeAdditiveConvolutionGamma d i j : ℂ) =
            ((i + j).choose j : ℂ) * (d.choose (d - i - j) : ℂ) /
              ((d.choose i : ℂ) * (d.choose j : ℂ)) := by
        rw [finiteFreeAdditiveConvolutionGamma_eq_choose_ratio d i j hij]
        have hchoose : d.choose (i + j) = d.choose (d - i - j) := by
          simpa only [Nat.sub_sub] using (Nat.choose_symm hij).symm
        rw [hchoose]
        simp only [Complex.ofReal_div, Complex.ofReal_mul,
          Complex.ofReal_natCast]
      rw [hgamma]
      congr 1
      ring
    · rw [if_neg hij]
      have hijd : ¬ i ≤ d - j := by
        intro h
        exact hij ((Nat.le_sub_iff_add_le hj).mp h)
      rw [applyNegDifferential_C_mul_left,
        applyNegDifferential_C_mul_right,
        applyNegDifferential_esymm i (d - j), if_neg hijd]
      simp
  have hsum :
      (∑ i ∈ Finset.range (d + 1),
        ∑ j ∈ Finset.range (d + 1),
          diagonalProjection d
            (applyNegDifferential
              (MvPolynomial.C ((-1 : ℂ) ^ (d - i) *
                (p.map Complex.ofRealHom).coeff (d - i) / (d.choose i : ℂ)) *
                MvPolynomial.esymm (Fin d) ℂ i)
              (MvPolynomial.C ((q.map Complex.ofRealHom).coeff (d - j) /
                (d.choose j : ℂ)) * MvPolynomial.esymm (Fin d) ℂ (d - j)))) =
      ∑ i ∈ Finset.range (d + 1),
        ∑ j ∈ Finset.range (d + 1),
          if i + j ≤ d then
            Polynomial.C
                ((-1 : ℂ) ^ d *
                  (finiteFreeAdditiveConvolutionGamma d i j : ℂ) *
                  (p.map Complex.ofRealHom).coeff (d - i) *
                  (q.map Complex.ofRealHom).coeff (d - j)) *
              Polynomial.X ^ (d - i - j)
          else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hterm i j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  rw [hsum, sum_square_eq_triangle]
  rw [← Finset.sum_range_diag_flip]
  unfold finiteFreeAdditiveConvolution
  rw [Polynomial.map_sum]
  simp_rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : m ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  calc
    ∑ k ∈ Finset.range (m + 1),
        Polynomial.C
            ((-1 : ℂ) ^ d *
              (finiteFreeAdditiveConvolutionGamma d k (m - k) : ℂ) *
              (p.map Complex.ofRealHom).coeff (d - k) *
              (q.map Complex.ofRealHom).coeff (d - (m - k))) *
          Polynomial.X ^ (d - k - (m - k)) =
        ∑ k ∈ Finset.range (m + 1),
          Polynomial.C ((-1 : ℂ) ^ d) *
            (Polynomial.C
                ((finiteFreeAdditiveConvolutionGamma d k (m - k) : ℂ) *
                  (p.map Complex.ofRealHom).coeff (d - k) *
                  (q.map Complex.ofRealHom).coeff (d - (m - k)) ) *
              Polynomial.X ^ (d - m)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Nat.sub_sub_sub_cancel_right hk']
      rw [← mul_assoc, ← Polynomial.C_mul]
      congr 1
      ring
    _ = Polynomial.C ((-1 : ℂ) ^ d) *
          ∑ k ∈ Finset.range (m + 1),
            Polynomial.C
                ((finiteFreeAdditiveConvolutionGamma d k (m - k) : ℂ) *
                  (p.map Complex.ofRealHom).coeff (d - k) *
                  (q.map Complex.ofRealHom).coeff (d - (m - k)) ) *
              Polynomial.X ^ (d - m) := by
      rw [Finset.mul_sum]
    _ = Polynomial.C ((-1 : ℂ) ^ d) *
          ((∑ k ∈ Finset.range (m + 1),
              Polynomial.C
                ((finiteFreeAdditiveConvolutionGamma d k (m - k) : ℂ) *
                  (p.map Complex.ofRealHom).coeff (d - k) *
                  (q.map Complex.ofRealHom).coeff (d - (m - k))) ) *
            Polynomial.X ^ (d - m)) := by
      rw [Finset.sum_mul]
    _ = _ := by
      rw [← C_map_finiteFreeAdditiveConvolutionCoeff]

end

end RealRooted
