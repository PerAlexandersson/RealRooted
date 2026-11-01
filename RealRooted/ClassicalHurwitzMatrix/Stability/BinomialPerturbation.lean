module

public import RealRooted.Compatibility.Pair
public import RealRooted.SimpleRoots
import RealRooted.ClassicalHurwitzMatrix.Stability.OddEvenConverse
public import RealRooted.ClassicalHurwitzMatrix.Stability
import RealRooted.Compatibility.Basic
import RealRooted.ClassicalHurwitzMatrix.Stability.Routh
import RealRooted.ClassicalHurwitzMatrix.Stability.CoefficientSigns
import RealRooted.Mathlib.Probability.CoeffDistribution
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import RealRooted.CombinatorialExamples.EvenBinom

/-!
# Binomial perturbations and a common interlacer

Weighted coefficient bounds give right-half-plane stability for perturbations
of `(1 + X) ^ n`.  A Joukowski substitution then gives a real-rooted family
with a fixed odd-binomial interlacer.
-/

public section

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted

/-- The perturbation of `(1 + X) ^ n` with prescribed lower coefficients. -/
@[expose] def binomialCoefficientPerturbation (n : ℕ) (c : ℕ → ℂ) : ℂ[X] :=
  (1 + X) ^ n + ∑ k ∈ Finset.range n, monomial k (c k)

private lemma norm_sq_sum_mul_pow_le (n : ℕ) (c : ℕ → ℂ) (z : ℂ)
    (hc : ∑ k ∈ Finset.range n, ‖c k‖ ^ 2 / (n.choose k : ℝ) ≤ 1) :
    ‖∑ k ∈ Finset.range n, c k * z ^ k‖ ^ 2 ≤
      (1 + ‖z‖ ^ 2) ^ n - ‖z‖ ^ (2 * n) := by
  let f : ℕ → ℝ := fun k ↦ ‖c k‖ / √(n.choose k : ℝ)
  let g : ℕ → ℝ := fun k ↦ √(n.choose k : ℝ) * ‖z‖ ^ k
  have hchoose (k : ℕ) (hk : k ∈ Finset.range n) : 0 < (n.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt (Finset.mem_range.mp hk))
  have hsqrt (k : ℕ) (hk : k ∈ Finset.range n) : 0 < √(n.choose k : ℝ) :=
    Real.sqrt_pos.2 (hchoose k hk)
  have hprod (k : ℕ) (hk : k ∈ Finset.range n) :
      f k * g k = ‖c k‖ * ‖z‖ ^ k := by
    dsimp [f, g]
    field_simp [ne_of_gt (hsqrt k hk)]
  have hf_sq (k : ℕ) (hk : k ∈ Finset.range n) :
      f k ^ 2 = ‖c k‖ ^ 2 / (n.choose k : ℝ) := by
    dsimp [f]
    rw [div_pow, Real.sq_sqrt (hchoose k hk).le]
  have hg_sq (k : ℕ) (hk : k ∈ Finset.range n) :
      g k ^ 2 = (n.choose k : ℝ) * ‖z‖ ^ (2 * k) := by
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (hchoose k hk).le]
    ring
  have htriangle :
      ‖∑ k ∈ Finset.range n, c k * z ^ k‖ ≤
        ∑ k ∈ Finset.range n, f k * g k := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, ‖c k * z ^ k‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range n, f k * g k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hprod k hk, norm_mul, norm_pow]
  have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range n, f k * g k := by
    apply Finset.sum_nonneg
    intro k hk
    rw [hprod k hk]
    positivity
  have htriangle_sq :
      ‖∑ k ∈ Finset.range n, c k * z ^ k‖ ^ 2 ≤
        (∑ k ∈ Finset.range n, f k * g k) ^ 2 := by
    nlinarith [norm_nonneg (∑ k ∈ Finset.range n, c k * z ^ k)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) f g
  have hf_sum :
      ∑ k ∈ Finset.range n, f k ^ 2 =
        ∑ k ∈ Finset.range n, ‖c k‖ ^ 2 / (n.choose k : ℝ) := by
    exact Finset.sum_congr rfl hf_sq
  have hg_sum :
      ∑ k ∈ Finset.range n, g k ^ 2 =
        ∑ k ∈ Finset.range n, (n.choose k : ℝ) * ‖z‖ ^ (2 * k) := by
    exact Finset.sum_congr rfl hg_sq
  rw [hf_sum, hg_sum] at hcs
  have hbinom :
      ∑ k ∈ Finset.range n, (n.choose k : ℝ) * ‖z‖ ^ (2 * k) =
        (1 + ‖z‖ ^ 2) ^ n - ‖z‖ ^ (2 * n) := by
    have h := add_pow (‖z‖ ^ 2) 1 n
    rw [Finset.sum_range_succ] at h
    simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one] at h
    rw [show (‖z‖ ^ 2) ^ n = ‖z‖ ^ (2 * n) by rw [pow_mul]] at h
    have hsum :
        ∑ k ∈ Finset.range n, ‖z‖ ^ (2 * k) * (n.choose k : ℝ) =
          ∑ k ∈ Finset.range n, (n.choose k : ℝ) * ‖z‖ ^ (2 * k) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [← hsum]
    simpa [add_comm, pow_mul] using (sub_eq_iff_eq_add.mpr h).symm
  rw [hbinom] at hcs
  have hnonneg : 0 ≤ (1 + ‖z‖ ^ 2) ^ n - ‖z‖ ^ (2 * n) := by
    rw [← hbinom]
    positivity
  calc
    _ ≤ _ := htriangle_sq
    _ ≤ (∑ k ∈ Finset.range n, ‖c k‖ ^ 2 / (n.choose k : ℝ)) *
        ((1 + ‖z‖ ^ 2) ^ n - ‖z‖ ^ (2 * n)) := hcs
    _ ≤ _ := by nlinarith

private lemma norm_one_add_sq (z : ℂ) :
    ‖1 + z‖ ^ 2 = 1 + ‖z‖ ^ 2 + 2 * z.re := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

private lemma eval_binomialCoefficientPerturbation (n : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    (binomialCoefficientPerturbation n c).eval z =
      (1 + z) ^ n + ∑ k ∈ Finset.range n, c k * z ^ k := by
  rw [binomialCoefficientPerturbation, eval_add, eval_pow, eval_add, eval_one, eval_X,
    eval_finsetSum]
  simp

private lemma binomialCoefficientPerturbation_eval_ne_zero_of_re_nonneg
    (n : ℕ) (c : ℕ → ℂ)
    (hc : ∑ k ∈ Finset.range n, ‖c k‖ ^ 2 / (n.choose k : ℝ) ≤ 1)
    {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    (binomialCoefficientPerturbation n c).eval z ≠ 0 := by
  intro hzero
  have hbound := norm_sq_sum_mul_pow_le n c z hc
  have hstrict :
      ‖∑ k ∈ Finset.range n, c k * z ^ k‖ ^ 2 < (1 + ‖z‖ ^ 2) ^ n := by
    have hnormpos : 0 < ‖z‖ ^ (2 * n) := by
      by_cases hn : n = 0
      · simp [hn]
      · positivity
    linarith
  have hbase : (1 + ‖z‖ ^ 2) ^ n ≤ ‖(1 + z) ^ n‖ ^ 2 := by
    rw [norm_pow]
    calc
      _ ≤ (‖1 + z‖ ^ 2) ^ n := by
        gcongr
        rw [norm_one_add_sq]
        linarith
      _ = ‖1 + z‖ ^ (2 * n) := (pow_mul ‖1 + z‖ 2 n).symm
      _ = ‖1 + z‖ ^ (n * 2) := by rw [mul_comm]
      _ = (‖1 + z‖ ^ n) ^ 2 := pow_mul ‖1 + z‖ n 2
  rw [eval_binomialCoefficientPerturbation] at hzero
  have heq : (1 + z) ^ n = -∑ k ∈ Finset.range n, c k * z ^ k := by
    linear_combination hzero
  have hnormeq :
      ‖(1 + z) ^ n‖ ^ 2 = ‖∑ k ∈ Finset.range n, c k * z ^ k‖ ^ 2 := by
    rw [heq, norm_neg]
  linarith

/-- A lower-coefficient perturbation in the weighted unit ball has no zero in
the open right half-plane. -/
theorem binomialCoefficientPerturbation_isRightHalfPlaneStable
    (n : ℕ) (c : ℕ → ℂ)
    (hc : ∑ k ∈ Finset.range n, ‖c k‖ ^ 2 / (n.choose k : ℝ) ≤ 1) :
    IsRightHalfPlaneStable (binomialCoefficientPerturbation n c) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  exact binomialCoefficientPerturbation_eval_ne_zero_of_re_nonneg
    n c hc hz.le hz0

/-- A zero in the closed right half-plane can occur only at the origin, and
then the perturbation is the unique boundary vector `c₀ = -1`, `cₖ = 0`
for `0 < k < n`. -/
theorem binomialCoefficientPerturbation_boundary
    {n : ℕ} (hn : n ≠ 0) (c : ℕ → ℂ)
    (hc : ∑ k ∈ Finset.range n, ‖c k‖ ^ 2 / (n.choose k : ℝ) ≤ 1)
    {z : ℂ} (hz : 0 ≤ z.re)
    (hzero : (binomialCoefficientPerturbation n c).eval z = 0) :
    z = 0 ∧ ∀ k < n, c k = if k = 0 then -1 else 0 := by
  have hz0 : z = 0 := by
    by_contra hne
    exact binomialCoefficientPerturbation_eval_ne_zero_of_re_nonneg
      n c hc hz hne hzero
  subst z
  have hc0 : c 0 = -1 := by
    rw [eval_binomialCoefficientPerturbation] at hzero
    have hsum : ∑ k ∈ Finset.range n, c k * (0 : ℂ) ^ k = c 0 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k hk hk0
        simp [hk0]
      · simp [hn]
    rw [hsum] at hzero
    linear_combination hzero
  let term : ℕ → ℝ := fun k ↦ ‖c k‖ ^ 2 / (n.choose k : ℝ)
  have hterm_nonneg (k : ℕ) : 0 ≤ term k := by
    dsimp [term]
    positivity
  have hzero_mem : 0 ∈ Finset.range n := Finset.mem_range.mpr (Nat.pos_of_ne_zero hn)
  have hterm_zero : term 0 = 1 := by
    simp [term, hc0]
  have herase_nonneg : 0 ≤ ∑ k ∈ (Finset.range n).erase 0, term k := by
    exact Finset.sum_nonneg fun k _ ↦ hterm_nonneg k
  have hdecomp :
      (∑ k ∈ (Finset.range n).erase 0, term k) + term 0 =
        ∑ k ∈ Finset.range n, term k :=
    Finset.sum_erase_add _ _ hzero_mem
  have herase_zero : ∑ k ∈ (Finset.range n).erase 0, term k = 0 := by
    change ∑ k ∈ Finset.range n, term k ≤ 1 at hc
    linarith
  refine ⟨rfl, fun k hk ↦ ?_⟩
  split_ifs with hk0
  · simpa [hk0] using hc0
  · have hkmem : k ∈ (Finset.range n).erase 0 := by
      simp [hk, hk0]
    have htk : term k = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hterm_nonneg i).mp
        herase_zero k hkmem
    have hchoose : (n.choose k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_of_lt hk)).ne'
    dsimp [term] at htk
    field_simp [hchoose] at htk
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (by simpa using htk))

/-! ## The common-interlacer family -/

/-- The even binomial section `∑ k, choose (2n) (2k) X^k`. -/
@[expose] def evenBinomialSection (n : ℕ) : ℝ[X] :=
  BigDescents.evenBinomPolyReal (2 * n)

/-- The odd binomial section `∑ k, choose (2n) (2k + 1) X^k`. -/
@[expose] def oddBinomialSection (n : ℕ) : ℝ[X] :=
  BigDescents.oddBinomPolyReal (2 * n)

/-- The even-binomial section with simultaneous gamma-basis perturbations. -/
@[expose] def binomialPerturbationFamily (n : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  evenBinomialSection n +
    ∑ j ∈ Finset.Icc 1 (n / 2),
      C (a j) * X ^ j * (1 + X) ^ (n - 2 * j)

/-- The ellipsoidal coefficient condition for the binomial perturbation
family. -/
def BinomialPerturbationBound (n : ℕ) (a : ℕ → ℝ) : Prop :=
  ∑ j ∈ Finset.Icc 1 (n / 2),
      a j ^ 2 / (16 ^ j * (n.choose (2 * j) : ℝ)) ≤ 1

private lemma oddEvenPolynomial_binomialSections (n : ℕ) :
    oddEvenPolynomial (oddBinomialSection n) (evenBinomialSection n) =
      (1 + X) ^ (2 * n) := by
  ext k
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [coeff_oddEvenPolynomial_even]
    simp [evenBinomialSection, BigDescents.coeff_evenBinomPolyReal,
      Polynomial.coeff_one_add_X_pow]
  · rw [coeff_oddEvenPolynomial_odd]
    simp [oddBinomialSection, BigDescents.coeff_oddBinomPolyReal,
      Polynomial.coeff_one_add_X_pow]

private lemma oddEvenPolynomial_binomialPerturbationFamily (n : ℕ) (a : ℕ → ℝ) :
    oddEvenPolynomial (oddBinomialSection n) (binomialPerturbationFamily n a) =
      (1 + X) ^ (2 * n) +
        ∑ j ∈ Finset.Icc 1 (n / 2),
          C (a j) * X ^ (2 * j) * (1 + X ^ 2) ^ (n - 2 * j) := by
  let p : ℝ[X] :=
    ∑ j ∈ Finset.Icc 1 (n / 2),
      C (a j) * X ^ j * (1 + X) ^ (n - 2 * j)
  change oddEvenPolynomial (oddBinomialSection n) (evenBinomialSection n + p) = _
  rw [oddEvenPolynomial, add_comp]
  calc
    (evenBinomialSection n).comp (X ^ 2) + p.comp (X ^ 2) +
          X * (oddBinomialSection n).comp (X ^ 2) =
        oddEvenPolynomial (oddBinomialSection n) (evenBinomialSection n) +
          p.comp (X ^ 2) := by
      rw [oddEvenPolynomial]
      ring
    _ = (1 + X) ^ (2 * n) + p.comp (X ^ 2) := by
      rw [oddEvenPolynomial_binomialSections]
    _ = _ := by
      dsimp [p]
      rw [Polynomial.sum_comp]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp [pow_mul]

private def normalizedPerturbationCoefficient (n : ℕ) (a : ℕ → ℝ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 (n / 2),
    if n - 2 * j = k then (a j : ℂ) / 4 ^ j else 0

private lemma normalizedPerturbationCoefficient_apply
    {n j : ℕ} (a : ℕ → ℝ) (hj : j ∈ Finset.Icc 1 (n / 2)) :
    normalizedPerturbationCoefficient n a (n - 2 * j) = (a j : ℂ) / 4 ^ j := by
  rw [normalizedPerturbationCoefficient, Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp only [ite_eq_right_iff]
    intro heq
    have hi' := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Icc.mp hj
    exfalso
    apply hij
    lia
  · exact fun h ↦ (h hj).elim

private lemma normalizedPerturbationCoefficient_eq_zero
    {n k : ℕ} (a : ℕ → ℝ)
    (hk : k ∉ (Finset.Icc 1 (n / 2)).image fun j ↦ n - 2 * j) :
    normalizedPerturbationCoefficient n a k = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  simp only [ite_eq_right_iff]
  intro heq
  exact (hk (Finset.mem_image.mpr ⟨j, hj, heq⟩)).elim

private lemma normalized_exponent_injective (n : ℕ) :
    Set.InjOn (fun j ↦ n - 2 * j) (Finset.Icc 1 (n / 2)) := by
  intro i hi j hj hij
  change i ∈ Finset.Icc 1 (n / 2) at hi
  change j ∈ Finset.Icc 1 (n / 2) at hj
  simp only [Finset.mem_Icc] at hi hj
  lia

private lemma normalized_exponent_lt
    {n j : ℕ} (hj : j ∈ Finset.Icc 1 (n / 2)) : n - 2 * j < n := by
  simp only [Finset.mem_Icc] at hj
  lia

private lemma binomialCoefficientPerturbation_normalized_eq
    (n : ℕ) (a : ℕ → ℝ) :
    binomialCoefficientPerturbation n (normalizedPerturbationCoefficient n a) =
      (1 + X) ^ n +
        ∑ j ∈ Finset.Icc 1 (n / 2),
          monomial (n - 2 * j) ((a j : ℂ) / 4 ^ j) := by
  rw [binomialCoefficientPerturbation]
  congr 1
  let s := Finset.Icc 1 (n / 2)
  let e : ℕ → ℕ := fun j ↦ n - 2 * j
  have himage : s.image e ⊆ Finset.range n := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    exact Finset.mem_range.mpr (normalized_exponent_lt hj)
  calc
    ∑ k ∈ Finset.range n, monomial k (normalizedPerturbationCoefficient n a k) =
        ∑ k ∈ s.image e, monomial k (normalizedPerturbationCoefficient n a k) := by
      symm
      apply Finset.sum_subset himage
      intro k hkRange hkImage
      rw [normalizedPerturbationCoefficient_eq_zero a hkImage]
      simp
    _ = ∑ j ∈ s, monomial (e j) (normalizedPerturbationCoefficient n a (e j)) := by
      rw [Finset.sum_image (normalized_exponent_injective n)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [normalizedPerturbationCoefficient_apply a hj]

private lemma normalizedPerturbationCoefficient_bound
    {n : ℕ} {a : ℕ → ℝ} (ha : BinomialPerturbationBound n a) :
    ∑ k ∈ Finset.range n,
        ‖normalizedPerturbationCoefficient n a k‖ ^ 2 / (n.choose k : ℝ) ≤ 1 := by
  let s := Finset.Icc 1 (n / 2)
  let e : ℕ → ℕ := fun j ↦ n - 2 * j
  let t : ℕ → ℝ := fun k ↦
    ‖normalizedPerturbationCoefficient n a k‖ ^ 2 / (n.choose k : ℝ)
  have himage : s.image e ⊆ Finset.range n := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    exact Finset.mem_range.mpr (normalized_exponent_lt hj)
  have hsupport : ∑ k ∈ Finset.range n, t k = ∑ k ∈ s.image e, t k := by
    symm
    apply Finset.sum_subset himage
    intro k hkRange hkImage
    dsimp [t]
    rw [normalizedPerturbationCoefficient_eq_zero a hkImage]
    simp
  rw [hsupport, Finset.sum_image (normalized_exponent_injective n)]
  change ∑ j ∈ s,
      ‖normalizedPerturbationCoefficient n a (e j)‖ ^ 2 /
        (n.choose (e j) : ℝ) ≤ 1
  have hterm (j : ℕ) (hj : j ∈ s) :
      ‖normalizedPerturbationCoefficient n a (e j)‖ ^ 2 /
          (n.choose (e j) : ℝ) =
        a j ^ 2 / (16 ^ j * (n.choose (2 * j) : ℝ)) := by
    have hj' := Finset.mem_Icc.mp hj
    have htwo : 2 * j ≤ n := by lia
    rw [normalizedPerturbationCoefficient_apply a hj]
    rw [Nat.choose_symm htwo]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow,
      Complex.norm_ofNat]
    rw [div_pow, sq_abs]
    have hpow : ((4 : ℝ) ^ j) ^ 2 = 16 ^ j := by
      calc
        _ = (4 : ℝ) ^ (j * 2) := (pow_mul (4 : ℝ) j 2).symm
        _ = (4 : ℝ) ^ (2 * j) := by rw [mul_comm]
        _ = ((4 : ℝ) ^ 2) ^ j := pow_mul (4 : ℝ) 2 j
        _ = _ := by norm_num
    rw [hpow]
    ring
  rw [Finset.sum_congr rfl hterm]
  exact ha

private lemma joukowski_re_pos {z : ℂ} (hz : 0 < z.re) :
    0 < ((z + z⁻¹) / 2).re := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  rw [Complex.div_re, Complex.add_re, Complex.inv_re]
  norm_num
  have hnorm : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  positivity

private lemma joukowski_base_identity (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    (2 : ℂ) ^ n * z ^ n * (1 + (z + z⁻¹) / 2) ^ n = (1 + z) ^ (2 * n) := by
  have hone : (2 : ℂ) * z * (1 + (z + z⁻¹) / 2) = (1 + z) ^ 2 := by
    field_simp
    ring
  calc
    _ = ((2 : ℂ) * z * (1 + (z + z⁻¹) / 2)) ^ n := by
      rw [mul_pow, mul_pow]
    _ = ((1 + z) ^ 2) ^ n := by rw [hone]
    _ = _ := (pow_mul (1 + z) 2 n).symm

private lemma joukowski_term_identity
    {n j : ℕ} (hj : j ∈ Finset.Icc 1 (n / 2)) (a : ℝ) {z : ℂ} (hz : z ≠ 0) :
    (2 : ℂ) ^ n * z ^ n *
        ((a : ℂ) / 4 ^ j * ((z + z⁻¹) / 2) ^ (n - 2 * j)) =
      (a : ℂ) * z ^ (2 * j) * (1 + z ^ 2) ^ (n - 2 * j) := by
  have hj' := Finset.mem_Icc.mp hj
  have hn : n = 2 * j + (n - 2 * j) := by lia
  have hfour : (4 : ℂ) ^ j = (2 : ℂ) ^ (2 * j) := by
    calc
      _ = ((2 : ℂ) ^ 2) ^ j := by norm_num
      _ = _ := (pow_mul (2 : ℂ) 2 j).symm
  have hzw : (2 : ℂ) * z * ((z + z⁻¹) / 2) = 1 + z ^ 2 := by
    field_simp
    ring
  rw [hn, pow_add, pow_add, hfour, ← hzw]
  field_simp
  simp only [Nat.add_sub_cancel_left]
  have hcancel : (2 : ℂ) * z * ((z ^ 2 + 1) / (z * 2)) = z ^ 2 + 1 := by
    field_simp
  calc
    _ = (a : ℂ) * ((2 : ℂ) * z * ((z ^ 2 + 1) / (z * 2))) ^ (n - 2 * j) := by
      rw [mul_pow, mul_pow]
      ring
    _ = _ := by rw [hcancel]

private lemma eval_joukowski_binomialPerturbationFamily
    (n : ℕ) (a : ℕ → ℝ) {z : ℂ} (hz : z ≠ 0) :
    (complexify (oddEvenPolynomial
        (oddBinomialSection n) (binomialPerturbationFamily n a))).eval z =
      (2 : ℂ) ^ n * z ^ n *
        (binomialCoefficientPerturbation n
          (normalizedPerturbationCoefficient n a)).eval ((z + z⁻¹) / 2) := by
  have hpoly := congrArg (Polynomial.map Complex.ofRealHom)
    (oddEvenPolynomial_binomialPerturbationFamily n a)
  have heval := congrArg (fun p : ℂ[X] ↦ p.eval z) hpoly
  simp only [Polynomial.eval_map, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_one, Polynomial.map_X, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C] at heval
  rw [show complexify (oddEvenPolynomial
      (oddBinomialSection n) (binomialPerturbationFamily n a)) =
    Polynomial.map Complex.ofRealHom (oddEvenPolynomial
      (oddBinomialSection n) (binomialPerturbationFamily n a)) from rfl,
    Polynomial.eval_map]
  rw [heval, binomialCoefficientPerturbation_normalized_eq]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one]
  simp only [eval_monomial]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · exact (joukowski_base_identity n hz).symm
  · apply Finset.sum_congr rfl
    intro j hj
    exact (joukowski_term_identity hj (a j) hz).symm

private lemma oddEvenPolynomial_binomialPerturbationFamily_rhp
    {n : ℕ} {a : ℕ → ℝ} (ha : BinomialPerturbationBound n a) :
    IsRightHalfPlaneStable
      (complexify (oddEvenPolynomial
        (oddBinomialSection n) (binomialPerturbationFamily n a))) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  rw [eval_joukowski_binomialPerturbationFamily n a hz0]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hz0))
    (binomialCoefficientPerturbation_isRightHalfPlaneStable n
      (normalizedPerturbationCoefficient n a)
      (normalizedPerturbationCoefficient_bound ha) _ (joukowski_re_pos hz))

private lemma binomialPerturbationFamily_coeff_zero (n : ℕ) (a : ℕ → ℝ) :
    (binomialPerturbationFamily n a).coeff 0 = 1 := by
  simp [binomialPerturbationFamily, evenBinomialSection,
    BigDescents.coeff_evenBinomPolyReal, coeff_mul]

private lemma binomialPerturbationTerm_natDegree_lt
    {n j : ℕ} (a : ℕ → ℝ) (hj : j ∈ Finset.Icc 1 (n / 2)) :
    (C (a j) * X ^ j * (1 + X) ^ (n - 2 * j)).natDegree < n := by
  have hj' := Finset.mem_Icc.mp hj
  calc
    _ ≤ (C (a j) * X ^ j).natDegree + ((1 + X) ^ (n - 2 * j)).natDegree :=
      natDegree_mul_le
    _ ≤ j + (n - 2 * j) := by
      gcongr
      · exact natDegree_C_mul_X_pow_le (a j) j
      · simp
    _ < n := by lia

private lemma binomialPerturbationFamily_coeff_top (n : ℕ) (a : ℕ → ℝ) :
    (binomialPerturbationFamily n a).coeff n = 1 := by
  rw [binomialPerturbationFamily, coeff_add, evenBinomialSection,
    BigDescents.coeff_evenBinomPolyReal]
  norm_num
  apply Finset.sum_eq_zero
  intro j hj
  exact coeff_eq_zero_of_natDegree_lt (binomialPerturbationTerm_natDegree_lt a hj)

private lemma isHurwitzStable_of_rhp_of_coeff_zero_pos {p : ℝ[X]}
    (hzero : 0 < p.coeff 0) (hrhp : IsRightHalfPlaneStable (complexify p)) :
    IsHurwitzStable p := by
  have hp : p ≠ 0 := by
    intro hp
    subst p
    norm_num at hzero
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  rcases lt_or_gt_of_ne hlc with hlc_neg | hlc_pos
  · have hneg_pos : HasPosLeadingCoeff (-p) := by
      simp only [HasPosLeadingCoeff, leadingCoeff_neg]
      linarith
    have hrhp_neg : IsRightHalfPlaneStable (complexify (-p)) := by
      intro z hz
      rw [show complexify (-p) = -complexify p by simp [complexify]]
      simpa using hrhp z hz
    have hcoeff := hasNonnegCoeffs_of_isRightHalfPlaneStable hneg_pos hrhp_neg 0
    simp only [coeff_neg] at hcoeff
    linarith
  · exact (isHurwitzStable_iff_isRightHalfPlaneStable hlc_pos).mpr hrhp

/-- Under the weighted ellipsoid bound, `binomialPerturbationFamily n a` has
only negative real roots and is weakly interlaced by `oddBinomialSection n`. -/
theorem binomialPerturbationFamily_negativeRoots_interlaced
    {n : ℕ} (hn : n ≠ 0) {a : ℕ → ℝ} (ha : BinomialPerturbationBound n a) :
    (binomialPerturbationFamily n a).Splits ∧
      (∀ r ∈ (binomialPerturbationFamily n a).roots, r < 0) ∧
      StrictInterl (oddBinomialSection n) (binomialPerturbationFamily n a) := by
  have hodd : oddBinomialSection n ≠ 0 := by
    exact BigDescents.oddBinomPolyReal_ne_zero (2 * n) (by positivity)
  have heven : binomialPerturbationFamily n a ≠ 0 := by
    intro h
    have := congrArg (fun p : ℝ[X] ↦ p.coeff 0) h
    rw [binomialPerturbationFamily_coeff_zero] at this
    norm_num at this
  have hstable : IsHurwitzStable (oddEvenPolynomial
      (oddBinomialSection n) (binomialPerturbationFamily n a)) := by
    apply isHurwitzStable_of_rhp_of_coeff_zero_pos
    · rw [show 0 = 2 * 0 by norm_num, coeff_oddEvenPolynomial_even,
        binomialPerturbationFamily_coeff_zero]
      norm_num
    · exact oddEvenPolynomial_binomialPerturbationFamily_rhp ha
  obtain ⟨hodd_nonneg, heven_nonneg, hinterl⟩ :=
    (isHurwitzStable_oddEvenPolynomial_iff hodd heven).mp hstable
  refine ⟨hinterl.2.1.2, ?_, hinterl⟩
  intro r hr
  have hr_nonpos := roots_nonpos_of_hasNonnegCoeffs heven_nonneg r hr
  refine lt_of_le_of_ne hr_nonpos ?_
  intro hr_zero
  subst r
  have hroot := (mem_roots heven).mp hr
  rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero,
    binomialPerturbationFamily_coeff_zero] at hroot
  norm_num at hroot

/-- The unique parameter vector on the ellipsoid boundary that can produce
imaginary-axis zeros after the Joukowski substitution. -/
def IsExceptionalBinomialPerturbation (n : ℕ) (a : ℕ → ℝ) : Prop :=
  ∃ m, n = 2 * m ∧ a m = -(2 : ℝ) ^ n ∧
    ∀ j ∈ Finset.Icc 1 (n / 2), j ≠ m → a j = 0

private lemma isExceptionalBinomialPerturbation_of_boundary
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ)
    (hboundary : ∀ k < n, normalizedPerturbationCoefficient n a k =
      if k = 0 then -1 else 0) :
    IsExceptionalBinomialPerturbation n a := by
  have hc0 := hboundary 0 hn
  rw [ite_eq_left (Eq.refl 0)] at hc0
  have himage : 0 ∈ (Finset.Icc 1 (n / 2)).image (fun j ↦ n - 2 * j) := by
    by_contra hnot
    have hzero := normalizedPerturbationCoefficient_eq_zero a hnot
    rw [hzero] at hc0
    norm_num at hc0
  rcases Finset.mem_image.mp himage with ⟨m, hm, hmzero⟩
  have hn_eq : n = 2 * m := by
    have hm' := Finset.mem_Icc.mp hm
    lia
  refine ⟨m, hn_eq, ?_, ?_⟩
  · have hcm := hboundary (n - 2 * m) (normalized_exponent_lt hm)
    rw [normalizedPerturbationCoefficient_apply a hm] at hcm
    rw [ite_eq_left hmzero] at hcm
    have hden : (4 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [div_eq_iff hden] at hcm
    rw [neg_one_mul] at hcm
    have hfour : (4 : ℂ) ^ m = ((4 : ℝ) ^ m : ℂ) := by norm_num
    rw [hfour] at hcm
    have hreal : a m = -(4 : ℝ) ^ m := by exact_mod_cast hcm
    rw [hn_eq]
    have hpow : (4 : ℝ) ^ m = (2 : ℝ) ^ (2 * m) := by
      calc
        _ = ((2 : ℝ) ^ 2) ^ m := by norm_num
        _ = _ := (pow_mul (2 : ℝ) 2 m).symm
    calc
      a m = -(4 : ℝ) ^ m := hreal
      _ = -(2 : ℝ) ^ (2 * m) := by rw [hpow]
  · intro j hj hjm
    have hcj := hboundary (n - 2 * j) (normalized_exponent_lt hj)
    rw [normalizedPerturbationCoefficient_apply a hj] at hcj
    have hne : n - 2 * j ≠ 0 := by
      intro heq
      have hj' := Finset.mem_Icc.mp hj
      apply hjm
      lia
    rw [ite_eq_right hne] at hcj
    have hden : (4 : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    have haj : (a j : ℂ) = 0 := (div_eq_zero_iff.mp hcj).resolve_right hden
    exact_mod_cast haj

/-- Away from the displayed exceptional vector, the auxiliary odd/even
polynomial is strictly Hurwitz stable. -/
theorem oddEvenPolynomial_binomialPerturbationFamily_strictlyStable
    {n : ℕ} (hn : 0 < n) {a : ℕ → ℝ} (ha : BinomialPerturbationBound n a)
    (hexception : ¬ IsExceptionalBinomialPerturbation n a) :
    IsStrictlyHurwitzStable (oddEvenPolynomial
      (oddBinomialSection n) (binomialPerturbationFamily n a)) := by
  intro z hroot
  have hrhp := oddEvenPolynomial_binomialPerturbationFamily_rhp ha
  have hz_nonpos : z.re ≤ 0 := by
    by_contra hz
    exact hrhp z (lt_of_not_ge hz) hroot
  by_contra hz_neg
  have hzre : z.re = 0 := le_antisymm hz_nonpos (le_of_not_gt hz_neg)
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    have hcoeff : (oddEvenPolynomial
        (oddBinomialSection n) (binomialPerturbationFamily n a)).coeff 0 = 1 := by
      rw [show 0 = 2 * 0 by norm_num, coeff_oddEvenPolynomial_even,
        binomialPerturbationFamily_coeff_zero]
    have hroot' : (complexify (oddEvenPolynomial
        (oddBinomialSection n) (binomialPerturbationFamily n a))).coeff 0 = 0 := by
      simpa only [coeff_zero_eq_eval_zero] using hroot
    change (Polynomial.map Complex.ofRealHom (oddEvenPolynomial
      (oddBinomialSection n) (binomialPerturbationFamily n a))).coeff 0 = 0 at hroot'
    rw [coeff_map, hcoeff] at hroot'
    norm_num at hroot'
  let w := (z + z⁻¹) / 2
  have hwre : w.re = 0 := by
    dsimp only [w]
    rw [Complex.div_re, Complex.add_re, Complex.inv_re, hzre]
    norm_num
  have hqzero :
      (binomialCoefficientPerturbation n
        (normalizedPerturbationCoefficient n a)).eval w = 0 := by
    have hid := eval_joukowski_binomialPerturbationFamily n a hz0
    have hmul : (2 : ℂ) ^ n * z ^ n *
        (binomialCoefficientPerturbation n
          (normalizedPerturbationCoefficient n a)).eval w = 0 := by
      rw [← hid]
      exact hroot
    exact (mul_eq_zero.mp hmul).resolve_left
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hz0))
  have hboundary := binomialCoefficientPerturbation_boundary
    (n := n) (c := normalizedPerturbationCoefficient n a) hn.ne'
    (normalizedPerturbationCoefficient_bound ha) (z := w) hwre.ge hqzero
  exact hexception
    (isExceptionalBinomialPerturbation_of_boundary hn a hboundary.2)

/-- At the exceptional vector, the auxiliary odd/even polynomial has the
imaginary-axis zero `I` (and hence is not strictly Hurwitz stable). -/
theorem oddEvenPolynomial_binomialPerturbationFamily_eval_I_eq_zero
    {n : ℕ} (hn : 0 < n) {a : ℕ → ℝ}
    (hexception : IsExceptionalBinomialPerturbation n a) :
    (complexify (oddEvenPolynomial
      (oddBinomialSection n) (binomialPerturbationFamily n a))).eval Complex.I = 0 := by
  rcases hexception with ⟨m, hnm, ham, _⟩
  have hm : m ∈ Finset.Icc 1 (n / 2) := by
    rw [Finset.mem_Icc, hnm]
    constructor
    · lia
    · simp
  have hc0 : normalizedPerturbationCoefficient n a 0 = -1 := by
    have hc := normalizedPerturbationCoefficient_apply a hm
    rw [show n - 2 * m = 0 by lia] at hc
    rw [hc, ham, hnm]
    have hpow : ((2 : ℂ) ^ (2 * m)) = 4 ^ m := by
      calc
        _ = ((2 : ℂ) ^ 2) ^ m := pow_mul (2 : ℂ) 2 m
        _ = _ := by norm_num
    push_cast
    rw [hpow]
    field_simp
  have hqzero : (binomialCoefficientPerturbation n
      (normalizedPerturbationCoefficient n a)).eval 0 = 0 := by
    rw [eval_binomialCoefficientPerturbation]
    have hsum : ∑ k ∈ Finset.range n,
        normalizedPerturbationCoefficient n a k * (0 : ℂ) ^ k =
          normalizedPerturbationCoefficient n a 0 := by
      rw [Finset.sum_eq_single 0]
      · norm_num
      · intro k _ hk
        simp [hk]
      · simp [hn]
    rw [hsum, hc0]
    norm_num
  have hid := eval_joukowski_binomialPerturbationFamily n a
    (z := Complex.I) (by norm_num)
  rw [show (Complex.I + Complex.I⁻¹) / 2 = 0 by norm_num, hqzero] at hid
  simpa using hid

/-- Off the exceptional vector, both parity sections have simple roots and no
common root; this is the strict form of their interlacing. -/
theorem binomialPerturbationFamily_simpleRoots_noCommonRoot
    {n : ℕ} (hn : 0 < n) {a : ℕ → ℝ} (ha : BinomialPerturbationBound n a)
    (hexception : ¬ IsExceptionalBinomialPerturbation n a) :
    HasSimpleRoots (oddBinomialSection n) ∧
      HasSimpleRoots (binomialPerturbationFamily n a) ∧
      ∀ r, ¬ ((oddBinomialSection n).IsRoot r ∧
        (binomialPerturbationFamily n a).IsRoot r) := by
  have hinterl :=
    (binomialPerturbationFamily_negativeRoots_interlaced hn.ne' ha).2.2
  have hodd_degree : (oddBinomialSection n).natDegree = n - 1 := by
    rw [oddBinomialSection,
      BigDescents.oddBinomPolyReal_natDegree (2 * n) (by positivity)]
    have heq : 2 * n - 1 = 1 + (n - 1) * 2 := by lia
    rw [heq, Nat.add_mul_div_right 1 (n - 1) (by norm_num : 0 < 2)]
    norm_num
  have heven_degree : (binomialPerturbationFamily n a).natDegree = n := by
    have htop : n ≤ (binomialPerturbationFamily n a).natDegree :=
      le_natDegree_of_ne_zero (by
        rw [binomialPerturbationFamily_coeff_top]
        norm_num)
    rcases hinterl.natDegree_eq_or_eq_succ with hsame | hsucc
    · rw [hsame, hodd_degree] at htop
      lia
    · rw [hsucc, hodd_degree]
      lia
  have hstable : IsHurwitzStable (oddEvenPolynomial
      (oddBinomialSection n) (binomialPerturbationFamily n a)) := by
    apply isHurwitzStable_of_rhp_of_coeff_zero_pos
    · rw [show 0 = 2 * 0 by norm_num, coeff_oddEvenPolynomial_even,
        binomialPerturbationFamily_coeff_zero]
      norm_num
    · exact oddEvenPolynomial_binomialPerturbationFamily_rhp ha
  have hodd_nonneg := hasNonnegCoeffs_left_of_oddEvenPolynomial hstable.hasNonnegCoeffs
  have heven_nonneg := hasNonnegCoeffs_right_of_oddEvenPolynomial hstable.hasNonnegCoeffs
  have hodd_pos := hodd_nonneg.pos_leadingCoeff hinterl.1.1
  have heven_pos := heven_nonneg.pos_leadingCoeff hinterl.2.1.1
  have hshape : (binomialPerturbationFamily n a).natDegree =
      (oddBinomialSection n).natDegree + 1 := by
    rw [heven_degree, hodd_degree]
    lia
  have hstrict :=
    oddEvenPolynomial_binomialPerturbationFamily_strictlyStable hn ha hexception
  obtain ⟨hodd_simple, heven_simple⟩ :=
    hstrict.hasSimpleRoots_parts_of_evenShape hodd_pos heven_pos hshape
  exact ⟨hodd_simple, heven_simple,
    fun r ↦ hstrict.noCommonRoot_parts_of_hasNonnegCoeffs
      hinterl.1.1 hodd_nonneg r⟩

/-- Any two members of the fixed-`n` ellipsoid family are compatible: every
nonnegative linear combination is zero or real-rooted. -/
theorem binomialPerturbationFamily_compatible
    {n : ℕ} (hn : n ≠ 0) {a b : ℕ → ℝ}
    (ha : BinomialPerturbationBound n a) (hb : BinomialPerturbationBound n b) :
    Compatible (binomialPerturbationFamily n a) (binomialPerturbationFamily n b) := by
  have hia := (binomialPerturbationFamily_negativeRoots_interlaced hn ha).2.2
  have hib := (binomialPerturbationFamily_negativeRoots_interlaced hn hb).2.2
  have hna : HasNonnegCoeffs (binomialPerturbationFamily n a) := by
    have hstable := isHurwitzStable_of_rhp_of_coeff_zero_pos
      (p := oddEvenPolynomial (oddBinomialSection n) (binomialPerturbationFamily n a))
      (by
        rw [show 0 = 2 * 0 by norm_num, coeff_oddEvenPolynomial_even,
          binomialPerturbationFamily_coeff_zero]
        norm_num)
      (oddEvenPolynomial_binomialPerturbationFamily_rhp ha)
    exact hasNonnegCoeffs_right_of_oddEvenPolynomial hstable.hasNonnegCoeffs
  have hnb : HasNonnegCoeffs (binomialPerturbationFamily n b) := by
    have hstable := isHurwitzStable_of_rhp_of_coeff_zero_pos
      (p := oddEvenPolynomial (oddBinomialSection n) (binomialPerturbationFamily n b))
      (by
        rw [show 0 = 2 * 0 by norm_num, coeff_oddEvenPolynomial_even,
          binomialPerturbationFamily_coeff_zero]
        norm_num)
      (oddEvenPolynomial_binomialPerturbationFamily_rhp hb)
    exact hasNonnegCoeffs_right_of_oddEvenPolynomial hstable.hasNonnegCoeffs
  exact Compatible.of_commonLeftInterleaver hia hib
    (hna.pos_leadingCoeff hia.2.1.1) (hnb.pos_leadingCoeff hib.2.1.1)

end RealRooted
