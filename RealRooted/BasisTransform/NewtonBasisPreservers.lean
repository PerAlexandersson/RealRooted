module

public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
public import RealRooted.NarayanaTransformation.RootGeometry

import RealRooted.BasisTransform.AppellRigidity
import RealRooted.NarayanaTransformation.Rising
import RealRooted.Linear

/-!
# Newton-basis preservers

This file records the algebra of Newton bases with arithmetic-progression
parameters.  The real-rootedness direction reuses the generalized rising-factorial
preserver theorem.
-/

public section

open Finset Polynomial

noncomputable section

namespace RealRooted

/-- The Newton basis polynomial with parameters `c 0, ..., c (n - 1)`. -/
def newtonBasisPolynomial (c : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  ∏ j ∈ Finset.range n, (X + C (c j))

@[simp] theorem newtonBasisPolynomial_zero (c : ℕ → ℝ) :
    newtonBasisPolynomial c 0 = 1 := by
  simp [newtonBasisPolynomial]

/-- Appending one parameter gives the successor Newton polynomial. -/
theorem newtonBasisPolynomial_succ (c : ℕ → ℝ) (n : ℕ) :
    newtonBasisPolynomial c (n + 1) =
      (X + C (c n)) * newtonBasisPolynomial c n := by
  simp [newtonBasisPolynomial, Finset.prod_range_succ]
  ring

private theorem newtonBasisPolynomial_monic (c : ℕ → ℝ) (n : ℕ) :
    (newtonBasisPolynomial c n).Monic := by
  unfold newtonBasisPolynomial
  exact monic_prod_of_monic _ _ fun j _ => monic_X_add_C (c j)

private theorem newtonBasisPolynomial_natDegree (c : ℕ → ℝ) (n : ℕ) :
    (newtonBasisPolynomial c n).natDegree = n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [newtonBasisPolynomial_succ,
        natDegree_mul (X_add_C_ne_zero (c n)) (newtonBasisPolynomial_monic c n).ne_zero,
        natDegree_X_add_C, ih]
      lia

private theorem newtonBasisPolynomial_coeff_sub_one
    (c : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (newtonBasisPolynomial c n).coeff (n - 1) = ∑ j ∈ range n, c j := by
  have hnext := Monic.nextCoeff_prod (range n) (fun j => X + C (c j))
    (fun j _ => monic_X_add_C (c j))
  rw [← newtonBasisPolynomial, nextCoeff, newtonBasisPolynomial_natDegree] at hnext
  split at hnext
  · next hzero => lia
  · convert hnext using 1
    apply Finset.sum_congr rfl
    intro j _
    simp [nextCoeff]

/-- The Newton-basis transform sends `X ^ n` to the `n`th Newton polynomial. -/
def newtonBasisTransform (c : ℕ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  Polynomial.basisTransformₗ (newtonBasisPolynomial c)

@[simp] theorem newtonBasisTransform_X_pow (c : ℕ → ℝ) (n : ℕ) :
    newtonBasisTransform c (X ^ n) = newtonBasisPolynomial c n := by
  simp [newtonBasisTransform]

/-- The Newton transform preserves real-rootedness on inputs whose roots are
all nonpositive. -/
@[expose] def NewtonPreservesNonposRooted (c : ℕ → ℝ) : Prop :=
  ∀ p, HasOnlyNonposRoots p → (newtonBasisTransform c p).Splits

/-- The repeated-root tests for a Newton-basis transform. -/
@[expose] def NewtonRepeatedRootTests (c : ℕ → ℝ) : Prop :=
  ∀ n r, 0 ≤ r → (newtonBasisTransform c ((X + C r) ^ n)).Splits

/-- The parameters of a Newton basis form a nondecreasing arithmetic progression. -/
@[expose] def NewtonParametersAffine (c : ℕ → ℝ) : Prop :=
  ∃ h, 0 ≤ h ∧ ∀ j, c j = c 0 + (j : ℝ) * h

/-- Preservation restricted to inputs of degree at most `N`. -/
@[expose] def NewtonPreservesNonposRootedUpTo (N : ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ p, p.natDegree ≤ N → HasOnlyNonposRoots p →
    (newtonBasisTransform c p).Splits

/-- The repeated-root tests restricted to degrees at most `N`. -/
@[expose] def NewtonRepeatedRootTestsUpTo (N : ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ n ≤ N, ∀ r, 0 ≤ r →
    (newtonBasisTransform c ((X + C r) ^ n)).Splits

/-- The first `N` parameters lie in a nondecreasing arithmetic progression. -/
@[expose] def NewtonParametersAffineUpTo (N : ℕ) (c : ℕ → ℝ) : Prop :=
  ∃ h, 0 ≤ h ∧ ∀ j < N, c j = c 0 + (j : ℝ) * h

private theorem appellCoefficient_newton_natDegree_le_half
    {N : ℕ} {c : ℕ → ℝ} (htest : NewtonRepeatedRootTestsUpTo N c)
    {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N) :
    (appellCoefficient (newtonBasisPolynomial c) k).natDegree ≤ k / 2 := by
  apply appellCoefficient_natDegree_le_of_shiftedPower_splits
    (newtonBasisPolynomial_natDegree c) (newtonBasisPolynomial_monic c) hk
  intro r hr
  rw [splits_shiftedPowerImage_iff]
  simpa only [newtonBasisTransform, Polynomial.basisTransformₗ_apply] using
    htest k hkN r hr

private theorem two_mul_appellCoefficient_two_nonneg_of_repeatedRootTestsUpTo
    {N : ℕ} {c : ℕ → ℝ} (hN : 2 ≤ N)
    (htest : NewtonRepeatedRootTestsUpTo N c) :
    0 ≤ 2 * (appellCoefficient (newtonBasisPolynomial c) 2).coeff 1 := by
  apply two_mul_coeff_one_appellCoefficient_two_nonneg_of_shiftedPower_splits
    (newtonBasisPolynomial_natDegree c) (newtonBasisPolynomial_monic c)
  intro r hr
  rw [splits_shiftedPowerImage_iff]
  simpa only [newtonBasisTransform, Polynomial.basisTransformₗ_apply] using htest 2 hN r hr

private theorem newtonBasisPolynomial_coeff_sub_one_eq_appell_of_le
    {N : ℕ} {c : ℕ → ℝ} (htest : NewtonRepeatedRootTestsUpTo N c)
    {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    (newtonBasisPolynomial c n).coeff (n - 1) =
      (appellCoefficient (newtonBasisPolynomial c) 1).coeff 0 * n +
        (2 * (appellCoefficient (newtonBasisPolynomial c) 2).coeff 1) *
          (n.choose 2 : ℝ) := by
  rw [coeff_eq_sum_descFactorial_of_isAppellExpansion
    (isAppellExpansion_appellCoefficient (newtonBasisPolynomial c)) hn]
  by_cases hn1 : n = 1
  · subst n
    norm_num
  have htwo : 2 ≤ n := by lia
  have hsubset : Icc 1 2 ⊆ Icc 1 n := Icc_subset_Icc_right htwo
  rw [← Finset.sum_subset hsubset]
  · rw [show (2 : ℕ) = 1 + 1 by norm_num,
      Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self,
      Finset.sum_singleton, Nat.descFactorial_eq_factorial_mul_choose]
    norm_num
    have hchoose : n * (n - 1) = 2 * n.choose 2 := by
      calc
        n * (n - 1) = n.descFactorial 2 := by
          simp [Nat.descFactorial, Nat.mul_comm]
        _ = 2 * n.choose 2 := by
          rw [Nat.descFactorial_eq_factorial_mul_choose]
          norm_num
    have hchooseR : (n : ℝ) * (n - 1 : ℕ) = 2 * (n.choose 2 : ℝ) := by
      exact_mod_cast hchoose
    rw [mul_comm (↑(n - 1) : ℝ) (↑n : ℝ), hchooseR]
    ring
  · intro k hkbig hksmall
    have hk := Finset.mem_Icc.mp hkbig
    have hthree : 3 ≤ k := by
      by_contra hnot
      exact hksmall (Finset.mem_Icc.mpr ⟨hk.1, by lia⟩)
    have hdeg :
        (appellCoefficient (newtonBasisPolynomial c) k).natDegree < k - 1 := by
      calc
        _ ≤ k / 2 := appellCoefficient_newton_natDegree_le_half
          htest (by lia) (hk.2.trans hnN)
        _ < k - 1 := by lia
    rw [coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]

private theorem newton_parameters_affine_data_of_repeatedRootTestsUpTo
    {N : ℕ} {c : ℕ → ℝ} (hN : 2 ≤ N)
    (htest : NewtonRepeatedRootTestsUpTo N c) :
    0 ≤ 2 * (appellCoefficient (newtonBasisPolynomial c) 2).coeff 1 ∧
      ∀ j < N, c j = c 0 +
        (j : ℝ) * (2 * (appellCoefficient (newtonBasisPolynomial c) 2).coeff 1) := by
  have hbeta :
      0 ≤ 2 * (appellCoefficient (newtonBasisPolynomial c) 2).coeff 1 :=
    two_mul_appellCoefficient_two_nonneg_of_repeatedRootTestsUpTo hN htest
  have halpha :
      (appellCoefficient (newtonBasisPolynomial c) 1).coeff 0 = c 0 := by
    rw [coeff_zero_appellCoefficient_one]
    · simp [newtonBasisPolynomial]
    · simp [newtonBasisPolynomial]
  refine ⟨hbeta, ?_⟩
  intro j hjN
  by_cases hj : j = 0
  · subst j
    simp
  have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
  have hnext := newtonBasisPolynomial_coeff_sub_one_eq_appell_of_le
    htest (n := j + 1) (by lia) (by lia)
  have hcurrent := newtonBasisPolynomial_coeff_sub_one_eq_appell_of_le
    htest hjpos (Nat.le_of_lt hjN)
  rw [newtonBasisPolynomial_coeff_sub_one c (by lia)] at hnext
  rw [newtonBasisPolynomial_coeff_sub_one c hjpos] at hcurrent
  rw [Finset.sum_range_succ, hcurrent, halpha] at hnext
  have hchoose : (j + 1).choose 2 = j.choose 2 + j := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, Nat.choose_succ_succ',
      Nat.choose_one_right]
    exact Nat.add_comm _ _
  push_cast [hchoose] at hnext
  nlinarith

private theorem newtonBasisPolynomial_eq_rising_comp
    {c : ℕ → ℝ} {h : ℝ} {n : ℕ}
    (hc : ∀ j < n, c j = c 0 + (j : ℝ) * h) :
    newtonBasisPolynomial c n =
      (risingFactorialPolynomial h n).comp (X + C (c 0)) := by
  induction n with
  | zero => simp [newtonBasisPolynomial, risingFactorialPolynomial]
  | succ n ih =>
      rw [newtonBasisPolynomial_succ, risingFactorialPolynomial_succ_mul,
        mul_comp, ih fun j hj => hc j (hj.trans (Nat.lt_succ_self n)),
        hc n (Nat.lt_succ_self n)]
      simp only [add_comp, X_comp, C_comp]
      rw [map_add]
      ring

private theorem basisTransform_eq_of_eq_on_support
    {B D : ℕ → ℝ[X]} {p : ℝ[X]}
    (h : ∀ n ∈ p.support, B n = D n) :
    basisTransform B p = basisTransform D p := by
  simp only [basisTransform, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n hn
  rw [h n hn]

private theorem basisTransform_X_pow_basis_eq_self (p : ℝ[X]) :
    basisTransform (fun n => (X : ℝ[X]) ^ n) p = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [basisTransform_add, hp, hq]
  | monomial n a =>
      rw [basisTransform_monomial, Polynomial.C_mul_X_pow_eq_monomial]

private theorem risingFactorialTransform_splits_of_nonposRoots
    {h : ℝ} (hh : 0 ≤ h) {p : ℝ[X]} (hp : HasOnlyNonposRoots p) :
    (basisTransform (risingFactorialPolynomial h) p).Splits := by
  rcases hh.eq_or_lt with rfl | hh
  · have hbasis : risingFactorialPolynomial 0 = fun n => (X : ℝ[X]) ^ n := by
      funext n
      simp [risingFactorialPolynomial]
    rw [hbasis]
    rw [basisTransform_X_pow_basis_eq_self]
    exact hp.elim (fun hp0 => by simp [hp0]) fun hp0 => hp0.1
  · rcases eq_or_ne p 0 with rfl | hp0
    · simp
    obtain ⟨hpsplits, hproots⟩ := hp.resolve_left hp0
    have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
    rcases lt_or_gt_of_ne hlc with hlcneg | hlcpos
    · have hnpsplits : (-p).Splits := hpsplits.neg
      have hnpnn : HasNonnegCoeffs (-p) :=
        ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hnpsplits).mpr
          ⟨hasPosLeadingCoeff_neg hlcneg, by simpa [Polynomial.roots_neg] using hproots⟩).1
      have hnppf : IsPFPolynomial (-p) :=
        IsPFPolynomial.of_realRooted_nonneg hnpnn hnpsplits
      have hout := (generalizedRisingFactorialPreservesPF hh hnppf).eq_zero_or_splits
      have htransform : basisTransform (risingFactorialPolynomial h) (-p) =
          -basisTransform (risingFactorialPolynomial h) p := by
        rw [show (-p : ℝ[X]) = (-1 : ℝ) • p by simp, basisTransform_smul]
        simp
      rw [htransform] at hout
      exact hout.elim (fun hz => by simp at hz; simp [hz])
        (fun hs => Polynomial.splits_neg_iff.mp hs)
    · have hpnn : HasNonnegCoeffs p :=
        ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hpsplits).mpr
          ⟨hlcpos, hproots⟩).1
      exact (generalizedRisingFactorialPreservesPF hh
        (IsPFPolynomial.of_realRooted_nonneg hpnn hpsplits)).splits

private theorem newtonBasisTransform_eq_rising_comp
    {c : ℕ → ℝ} {h : ℝ} (hc : ∀ j, c j = c 0 + (j : ℝ) * h)
    (p : ℝ[X]) :
    newtonBasisTransform c p =
      (basisTransform (risingFactorialPolynomial h) p).comp (X + C (c 0)) := by
  change basisTransform (newtonBasisPolynomial c) p = _
  have hbasis : newtonBasisPolynomial c = fun n =>
      (risingFactorialPolynomial h n).comp (X + C (c 0)) := by
    funext n
    exact newtonBasisPolynomial_eq_rising_comp fun j _ => hc j
  rw [hbasis, basisTransform_comp]

/-- Arithmetic-progression Newton parameters preserve real-rootedness for all
inputs with only nonpositive roots. -/
theorem NewtonParametersAffine.preservesNonposRooted {c : ℕ → ℝ}
    (hc : NewtonParametersAffine c) : NewtonPreservesNonposRooted c := by
  obtain ⟨h, hh, hc⟩ := hc
  intro p hp
  rw [newtonBasisTransform_eq_rising_comp hc p]
  have hsplits := risingFactorialTransform_splits_of_nonposRoots hh hp
  by_cases hzero : basisTransform (risingFactorialPolynomial h) p = 0
  · simp [hzero]
  · exact (isRealRooted_comp_X_add_C hzero hsplits (c 0)).2

/-- Preservation on all nonpositive-rooted inputs implies every repeated-root test. -/
theorem NewtonPreservesNonposRooted.repeatedRootTests {c : ℕ → ℝ}
    (hc : NewtonPreservesNonposRooted c) : NewtonRepeatedRootTests c := by
  intro n r hr
  exact hc _ ((isPFPolynomial_X_add_C hr).pow n).hasOnlyNonposRoots

/-- Arithmetic-progression parameters imply every repeated-root test. -/
theorem NewtonParametersAffine.repeatedRootTests {c : ℕ → ℝ}
    (hc : NewtonParametersAffine c) : NewtonRepeatedRootTests c :=
  hc.preservesNonposRooted.repeatedRootTests

/-- Repeated-root tests force the Newton parameters to form a nondecreasing
arithmetic progression. -/
theorem NewtonRepeatedRootTests.parametersAffine {c : ℕ → ℝ}
    (hc : NewtonRepeatedRootTests c) : NewtonParametersAffine c := by
  have htestN (N : ℕ) : NewtonRepeatedRootTestsUpTo N c := by
    intro n _ r hr
    exact hc n r hr
  refine ⟨2 * (appellCoefficient (newtonBasisPolynomial c) 2).coeff 1,
    (newton_parameters_affine_data_of_repeatedRootTestsUpTo
      (N := 2) (by norm_num) (htestN 2)).1, ?_⟩
  intro j
  let N := max 2 (j + 1)
  have hN : 2 ≤ N := le_max_left _ _
  have hjN : j < N :=
    (Nat.lt_succ_self j).trans_le (le_max_right 2 (j + 1))
  exact (newton_parameters_affine_data_of_repeatedRootTestsUpTo
    hN (htestN N)).2 j hjN

/-- Repeated-root tests are equivalent to arithmetic-progression Newton
parameters. -/
theorem newtonRepeatedRootTests_iff_parametersAffine (c : ℕ → ℝ) :
    NewtonRepeatedRootTests c ↔ NewtonParametersAffine c :=
  ⟨NewtonRepeatedRootTests.parametersAffine,
    NewtonParametersAffine.repeatedRootTests⟩

/-- Preservation of nonpositive-rooted inputs forces the Newton parameters
to form a nondecreasing arithmetic progression. -/
theorem NewtonPreservesNonposRooted.parametersAffine {c : ℕ → ℝ}
    (hc : NewtonPreservesNonposRooted c) : NewtonParametersAffine c :=
  hc.repeatedRootTests.parametersAffine

/-- Preservation of nonpositive-rooted inputs is equivalent to arithmetic
progression Newton parameters. -/
theorem newtonPreservesNonposRooted_iff_parametersAffine (c : ℕ → ℝ) :
    NewtonPreservesNonposRooted c ↔ NewtonParametersAffine c :=
  ⟨NewtonPreservesNonposRooted.parametersAffine,
    NewtonParametersAffine.preservesNonposRooted⟩

/-- Preservation, repeated-root tests, and arithmetic-progression parameters
are equivalent for a Newton basis. -/
theorem newtonBasis_preserver_equivalences (c : ℕ → ℝ) :
    (NewtonPreservesNonposRooted c ↔ NewtonRepeatedRootTests c) ∧
      (NewtonRepeatedRootTests c ↔ NewtonParametersAffine c) := by
  exact ⟨⟨NewtonPreservesNonposRooted.repeatedRootTests,
    fun htest => htest.parametersAffine.preservesNonposRooted⟩,
    newtonRepeatedRootTests_iff_parametersAffine c⟩

/-- The finite preservation property implies the finite repeated-root tests. -/
theorem NewtonPreservesNonposRootedUpTo.repeatedRootTestsUpTo
    {N : ℕ} {c : ℕ → ℝ} (hc : NewtonPreservesNonposRootedUpTo N c) :
    NewtonRepeatedRootTestsUpTo N c := by
  intro n hn r hr
  apply hc _ _ ((isPFPolynomial_X_add_C hr).pow n).hasOnlyNonposRoots
  rw [natDegree_pow, natDegree_X_add_C, mul_one]
  exact hn

/-- Through degree `N ≥ 2`, repeated-root tests force the first `N` Newton
parameters to form a nondecreasing arithmetic progression. -/
theorem NewtonRepeatedRootTestsUpTo.parametersAffineUpTo
    {N : ℕ} {c : ℕ → ℝ} (htest : NewtonRepeatedRootTestsUpTo N c)
    (hN : 2 ≤ N) : NewtonParametersAffineUpTo N c := by
  refine ⟨2 * (appellCoefficient (newtonBasisPolynomial c) 2).coeff 1, ?_⟩
  exact newton_parameters_affine_data_of_repeatedRootTestsUpTo hN htest

/-- An arithmetic progression through index `N - 1` preserves all admissible
inputs of degree at most `N`. -/
theorem NewtonParametersAffineUpTo.preservesNonposRootedUpTo
    {N : ℕ} {c : ℕ → ℝ} (hc : NewtonParametersAffineUpTo N c) :
    NewtonPreservesNonposRootedUpTo N c := by
  obtain ⟨h, hh, hc⟩ := hc
  intro p hpdeg hproots
  let d : ℕ → ℝ := fun j => c 0 + (j : ℝ) * h
  have hbasis : ∀ n ∈ p.support,
      newtonBasisPolynomial c n = newtonBasisPolynomial d n := by
    intro n hn
    unfold newtonBasisPolynomial
    apply Finset.prod_congr rfl
    intro j hj
    have hnN : n ≤ N := (le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)).trans hpdeg
    have hjN : j < N := (Finset.mem_range.mp hj).trans_le hnN
    rw [hc j hjN]
  have htransform : newtonBasisTransform c p = newtonBasisTransform d p := by
    change basisTransform (newtonBasisPolynomial c) p =
      basisTransform (newtonBasisPolynomial d) p
    exact basisTransform_eq_of_eq_on_support hbasis
  rw [htransform]
  exact (show NewtonParametersAffine d from ⟨h, hh, fun j => by simp [d]⟩).preservesNonposRooted
    p hproots

/-- Through degree `N ≥ 2`, repeated-root tests are equivalent to affine
Newton parameters through index `N - 1`. -/
theorem newtonRepeatedRootTestsUpTo_iff_parametersAffineUpTo
    {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    NewtonRepeatedRootTestsUpTo N c ↔ NewtonParametersAffineUpTo N c := by
  constructor
  · intro htest
    exact htest.parametersAffineUpTo hN
  · intro haffine
    exact haffine.preservesNonposRootedUpTo.repeatedRootTestsUpTo

/-- Through degree `N ≥ 2`, preservation is equivalent to affine Newton
parameters through index `N - 1`. -/
theorem newtonPreservesNonposRootedUpTo_iff_parametersAffineUpTo
    {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    NewtonPreservesNonposRootedUpTo N c ↔ NewtonParametersAffineUpTo N c := by
  constructor
  · intro hpres
    exact hpres.repeatedRootTestsUpTo.parametersAffineUpTo hN
  · exact NewtonParametersAffineUpTo.preservesNonposRootedUpTo

/-- Through degree `N ≥ 2`, preservation, repeated-root tests, and affine
parameters through index `N - 1` are equivalent. -/
theorem newtonBasis_preserver_equivalencesUpTo
    {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    (NewtonPreservesNonposRootedUpTo N c ↔ NewtonRepeatedRootTestsUpTo N c) ∧
      (NewtonRepeatedRootTestsUpTo N c ↔ NewtonParametersAffineUpTo N c) := by
  exact ⟨⟨NewtonPreservesNonposRootedUpTo.repeatedRootTestsUpTo,
    fun htest => (htest.parametersAffineUpTo hN).preservesNonposRootedUpTo⟩,
    newtonRepeatedRootTestsUpTo_iff_parametersAffineUpTo hN c⟩

end RealRooted
