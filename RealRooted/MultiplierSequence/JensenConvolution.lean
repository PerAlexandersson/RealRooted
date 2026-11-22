module

public import RealRooted.MultiplierSequence.JensenProduct
public import RealRooted.FiniteFreeAdditive
import RealRooted.FiniteFreeAdditive.Preservation
import RealRooted.Mathlib.Algebra.Polynomial.Reverse

/-!
# Finite Jensen products and additive convolution

Binomial convolution of Taylor data corresponds to finite-free additive
convolution after reflection. Consequently the splitting of the two Jensen
polynomials at a fixed degree already implies splitting of their Jensen product.
No entire-function or nonvanishing assumption is needed.
-/

public section

open Polynomial

namespace RealRooted

/-- The kernel cancels exactly against Jensen binomial normalizations. -/
private theorem finiteFreeAdditiveConvolutionGamma_mul_choose_mul_choose
    (d k i : ℕ) (hi : i ≤ k) (hk : k ≤ d) :
    finiteFreeAdditiveConvolutionGamma d i (k - i) *
        (d.choose i : ℝ) * (d.choose (k - i) : ℝ) =
      (d.choose k : ℝ) * (k.choose i : ℝ) := by
  have hid : i ≤ d := hi.trans hk
  have hkid : k - i ≤ d := (Nat.sub_le k i).trans hk
  have hi0 : (d.choose i : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hid).ne'
  have hki0 : (d.choose (k - i) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hkid).ne'
  rw [finiteFreeAdditiveConvolutionGamma_eq_choose_ratio d i (k - i)
    (by lia), Nat.add_sub_of_le hi, Nat.choose_symm hi]
  field_simp [hi0, hki0]

/-- A Jensen product is a reflected finite-free additive convolution.
No degree-exactness or nonzero assumption is needed. -/
theorem jensenProductPolynomial_eq_reflect_convolution
    (d : ℕ) (gamma delta : ℕ → ℝ) :
    jensenProductPolynomial d gamma delta =
      reflect d (finiteFreeAdditiveConvolution d
        (reflect d (jensenPolynomial d gamma))
        (reflect d (jensenPolynomial d delta))) := by
  symm
  ext k
  by_cases hk : k ≤ d
  · rw [coeff_reflect, revAt_le hk,
      coeff_finiteFreeAdditiveConvolution_of_le _ _ _ (Nat.sub_le d k),
      Nat.sub_sub_self hk, coeff_jensenProductPolynomial, ite_eq_left hk]
    unfold finiteFreeAdditiveConvolutionCoeff binomialConvolution
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hid : i ≤ d := hik.trans hk
    have hkid : k - i ≤ d := (Nat.sub_le k i).trans hk
    rw [coeff_reflect, revAt_le (Nat.sub_le d i), Nat.sub_sub_self hid,
      coeff_reflect, revAt_le (Nat.sub_le d (k - i)), Nat.sub_sub_self hkid,
      coeff_jensenPolynomial, ite_eq_left hid, coeff_jensenPolynomial, ite_eq_left hkid]
    calc
      _ = (finiteFreeAdditiveConvolutionGamma d i (k - i) *
          (d.choose i : ℝ) * (d.choose (k - i) : ℝ)) *
          gamma i * delta (k - i) := by ring
      _ = (d.choose k : ℝ) *
          ((k.choose i : ℝ) * gamma i * delta (k - i)) := by
        rw [finiteFreeAdditiveConvolutionGamma_mul_choose_mul_choose d k i hik hk]
        ring
  · rw [coeff_reflect, revAt_eq_self_of_lt (Nat.lt_of_not_ge hk),
      coeff_finiteFreeAdditiveConvolution_of_gt _ _ _ (Nat.lt_of_not_ge hk),
      coeff_jensenProductPolynomial, ite_eq_right hk]

/-- Finite product transfer: splitting of the two degree-`d` Jensen polynomials
implies splitting of their degree-`d` Jensen product. -/
theorem jensenProductPolynomial_splits
    (d : ℕ) {gamma delta : ℕ → ℝ}
    (hgamma : (jensenPolynomial d gamma).Splits)
    (hdelta : (jensenPolynomial d delta).Splits) :
    (jensenProductPolynomial d gamma delta).Splits := by
  rw [jensenProductPolynomial_eq_reflect_convolution]
  have hgd := natDegree_jensenPolynomial_le d gamma
  have hdd := natDegree_jensenPolynomial_le d delta
  have hgdr : (reflect d (jensenPolynomial d gamma)).natDegree ≤ d :=
    natDegree_reflect_le.trans (max_le le_rfl hgd)
  have hddr : (reflect d (jensenPolynomial d delta)).natDegree ≤ d :=
    natDegree_reflect_le.trans (max_le le_rfl hdd)
  apply (splits_reflect_iff (natDegree_finiteFreeAdditiveConvolution_le d _ _)).mpr
  exact splits_finiteFreeAdditiveConvolution d
    ((splits_reflect_iff hgd).mpr hgamma) ((splits_reflect_iff hdd).mpr hdelta) hgdr hddr

end RealRooted
