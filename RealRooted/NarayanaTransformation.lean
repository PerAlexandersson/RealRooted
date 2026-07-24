import Mathlib.Tactic
import RealRooted.LiuWangRecursion
import RealRooted.PFPolynomial
import RealRooted.QuadraticRoot

/-!
# The Narayana Transformation

This module starts a formalization of Mao--Wang, *The Narayana transformation*,
arXiv:2607.01572v1.

The main paper theorem says that the basis transformation
`X ^ k ↦ N_{k,m}` preserves real-rooted polynomials with nonnegative
coefficients.  The proof uses Gribinski--Marcus rectangular additive
convolution.  We first expose the reusable basis-transformation interfaces from
the paper and the checked coefficient infrastructure for the generalized
Narayana polynomials.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- Zero-aware predicate for real-rooted polynomials whose real roots are all
nonpositive. -/
def HasOnlyNonposRoots (p : ℝ[X]) : Prop :=
  p = 0 ∨ p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0

/-- Zero-aware predicate for real-rooted polynomials whose real roots are all
nonnegative. -/
def HasOnlyNonnegRoots (p : ℝ[X]) : Prop :=
  p = 0 ∨ p.Splits ∧ ∀ r ∈ p.roots, 0 ≤ r

theorem IsPFPolynomial.hasOnlyNonposRoots {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    HasOnlyNonposRoots p :=
  hp.eq_zero_or_splits.elim Or.inl fun hsplits =>
    Or.inr ⟨hsplits, hp.roots_nonpos⟩

theorem HasOnlyNonposRoots.of_nonnegCoeffs_splits {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hsplits : p.Splits) :
    HasOnlyNonposRoots p :=
  Or.inr ⟨hsplits, roots_nonpos_of_nonneg_coeffs hsplits hpnn⟩

theorem HasOnlyNonposRoots.neg {p : ℝ[X]} (hp : HasOnlyNonposRoots p) :
    HasOnlyNonposRoots (-p) := by
  simpa only [HasOnlyNonposRoots, neg_eq_zero, Polynomial.splits_neg_iff,
    Polynomial.roots_neg] using hp

theorem HasOnlyNonposRoots.of_neg {p : ℝ[X]} (hp : HasOnlyNonposRoots (-p)) :
    HasOnlyNonposRoots p := by
  simpa using hp.neg

private theorem hasOnlyNonnegRoots_C_mul_X_add_C_of_pos_nonpos {A B : ℝ}
    (hA : 0 < A) (hB : B ≤ 0) :
    HasOnlyNonnegRoots (C A * X + C B : ℝ[X]) := by
  right
  refine ⟨Polynomial.Splits.of_natDegree_eq_one (Polynomial.natDegree_linear hA.ne'), ?_⟩
  intro r hr
  have hroot_eq : r = -(A⁻¹ * B) := by
    rw [Polynomial.roots_C_mul_X_add_C B hA.ne'] at hr
    simpa using hr
  rw [hroot_eq]
  have hAinv : 0 < A⁻¹ := inv_pos.mpr hA
  nlinarith

theorem HasOnlyNonnegRoots.coeff_zero_nonpos_of_natDegree_eq_one {p : ℝ[X]}
    (hp : HasOnlyNonnegRoots p) (hpdeg : p.natDegree = 1)
    (hplead : 0 < p.leadingCoeff) :
    p.coeff 0 ≤ 0 := by
  rcases hp with hpzero | ⟨_hsplits, hroot_nonneg⟩
  · simp [hpzero] at hpdeg
  have hcoeff1pos : 0 < p.coeff 1 := by
    simpa [Polynomial.leadingCoeff, hpdeg] using hplead
  have hcoeff1ne : p.coeff 1 ≠ 0 := hcoeff1pos.ne'
  have hroot_mem : -(p.coeff 1)⁻¹ * p.coeff 0 ∈ p.roots := by
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hpdeg.le,
      Polynomial.roots_C_mul_X_add_C _ hcoeff1ne]
    simp
  have hnonneg : 0 ≤ -(p.coeff 1)⁻¹ * p.coeff 0 := hroot_nonneg _ hroot_mem
  nlinarith [inv_pos.mpr hcoeff1pos]

/-! ### Degree-padded sign flip -/

/-- Degree-`n` sign flip: the coefficient of `X^j` is multiplied by
`(-1)^(n-j)`, with coefficients above degree `n` discarded. For
`p.natDegree ≤ n` this is the coefficient form of `(-1)^n p(-X)`. -/
def degreeSignFlip (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  ∑ j ∈ Finset.range (n + 1), C ((-1 : ℝ) ^ (n - j) * p.coeff j) * X ^ j

theorem coeff_degreeSignFlip_of_le {n j : ℕ} (p : ℝ[X]) (hj : j ≤ n) :
    (degreeSignFlip n p).coeff j = (-1 : ℝ) ^ (n - j) * p.coeff j := by
  unfold degreeSignFlip
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro k hk hkj
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => hkj h.symm), mul_zero]

theorem coeff_degreeSignFlip_of_lt {n j : ℕ} (p : ℝ[X]) (hj : n < j) :
    (degreeSignFlip n p).coeff j = 0 := by
  unfold degreeSignFlip
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => by
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    lia), mul_zero]

theorem natDegree_degreeSignFlip_le (n : ℕ) (p : ℝ[X]) :
    (degreeSignFlip n p).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  exact coeff_degreeSignFlip_of_lt p hj

private theorem neg_one_pow_mul_pow_eq_sub {n j : ℕ} (hj : j ≤ n) :
    (-1 : ℝ) ^ n * (-1 : ℝ) ^ j = (-1 : ℝ) ^ (n - j) := by
  have hpow : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n - j) * (-1 : ℝ) ^ j := by
    nth_rw 1 [show n = n - j + j by lia]
    rw [pow_add]
  have hsq : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
    rw [← pow_add]
    have hEven : Even (j + j) := ⟨j, rfl⟩
    rw [Even.neg_one_pow hEven]
  calc
    (-1 : ℝ) ^ n * (-1 : ℝ) ^ j =
        ((-1 : ℝ) ^ (n - j) * (-1 : ℝ) ^ j) * (-1 : ℝ) ^ j := by rw [hpow]
    _ = (-1 : ℝ) ^ (n - j) * ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) := by ring
    _ = (-1 : ℝ) ^ (n - j) := by rw [hsq, mul_one]

theorem coeff_comp_neg_X (p : ℝ[X]) (j : ℕ) :
    (p.comp (-X)).coeff j = p.coeff j * (-1 : ℝ) ^ j := by
  simpa using Polynomial.comp_C_mul_X_coeff (p := p) (r := (-1 : ℝ)) (n := j)

theorem degreeSignFlip_eq_C_mul_comp_neg_X
    (n : ℕ) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) :
    degreeSignFlip n p = C ((-1 : ℝ) ^ n) * p.comp (-X) := by
  ext j
  by_cases hj : j ≤ n
  · rw [coeff_degreeSignFlip_of_le p hj, coeff_C_mul, coeff_comp_neg_X]
    calc
      (-1 : ℝ) ^ (n - j) * p.coeff j =
          ((-1 : ℝ) ^ n * (-1 : ℝ) ^ j) * p.coeff j := by
        rw [neg_one_pow_mul_pow_eq_sub hj]
      _ = (-1 : ℝ) ^ n * (p.coeff j * (-1 : ℝ) ^ j) := by ring
  · have hjlt : n < j := Nat.lt_of_not_ge hj
    rw [coeff_degreeSignFlip_of_lt p hjlt, coeff_C_mul, coeff_comp_neg_X]
    have hpzero : p.coeff j = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg hjlt)
    simp [hpzero]

theorem natDegree_degreeSignFlip_eq_of_coeff_ne_zero
    {n : ℕ} {p : ℝ[X]} (hcoeff : p.coeff n ≠ 0) :
    (degreeSignFlip n p).natDegree = n := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_degreeSignFlip_le n p) ?_
  rw [coeff_degreeSignFlip_of_le p le_rfl]
  simpa using hcoeff

theorem leadingCoeff_degreeSignFlip_of_coeff_ne_zero
    {n : ℕ} {p : ℝ[X]} (hcoeff : p.coeff n ≠ 0) :
    (degreeSignFlip n p).leadingCoeff = p.coeff n := by
  rw [Polynomial.leadingCoeff, natDegree_degreeSignFlip_eq_of_coeff_ne_zero hcoeff,
    coeff_degreeSignFlip_of_le p le_rfl]
  simp

theorem degreeSignFlip_splits_of_splits
    {n : ℕ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) (hp : p.Splits) :
    (degreeSignFlip n p).Splits := by
  rw [degreeSignFlip_eq_C_mul_comp_neg_X n hpdeg]
  exact hp.comp_neg_X.C_mul _

theorem splits_of_degreeSignFlip_splits
    {n : ℕ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ n)
    (hp : (degreeSignFlip n p).Splits) :
    p.Splits := by
  have hcomp : (p.comp (-X)).Splits := by
    have hscalar : (C ((-1 : ℝ) ^ n) * p.comp (-X)).Splits := by
      rwa [← degreeSignFlip_eq_C_mul_comp_neg_X n hpdeg]
    have hunscaled := hscalar.C_mul (((-1 : ℝ) ^ n)⁻¹)
    have hne : (-1 : ℝ) ^ n ≠ 0 := by simp
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul] using
      hunscaled
  have htwice : ((p.comp (-X)).comp (-X)).Splits := hcomp.comp_neg_X
  simpa [Polynomial.comp_neg_X_comp_neg_X] using htwice

theorem roots_degreeSignFlip {n : ℕ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) :
    (degreeSignFlip n p).roots = p.roots.map fun x => -x := by
  rw [degreeSignFlip_eq_C_mul_comp_neg_X n hpdeg,
    Polynomial.roots_C_mul _ (by simp : (-1 : ℝ) ^ n ≠ 0)]
  exact Polynomial.roots_comp_neg_X p

theorem HasOnlyNonposRoots.degreeSignFlip_hasOnlyNonnegRoots
    {n : ℕ} {p : ℝ[X]} (hp : HasOnlyNonposRoots p) (hpdeg : p.natDegree ≤ n) :
    HasOnlyNonnegRoots (degreeSignFlip n p) := by
  rcases hp with rfl | ⟨hsplits, hroots⟩
  · left
    rw [degreeSignFlip_eq_C_mul_comp_neg_X n (by simp)]
    simp
  · right
    refine ⟨degreeSignFlip_splits_of_splits hpdeg hsplits, ?_⟩
    intro r hr
    rw [roots_degreeSignFlip hpdeg] at hr
    rcases Multiset.mem_map.mp hr with ⟨x, hx, rfl⟩
    exact neg_nonneg.mpr (hroots x hx)

theorem HasOnlyNonnegRoots.degreeSignFlip_hasOnlyNonposRoots
    {n : ℕ} {p : ℝ[X]} (hp : HasOnlyNonnegRoots p) (hpdeg : p.natDegree ≤ n) :
    HasOnlyNonposRoots (degreeSignFlip n p) := by
  rcases hp with rfl | ⟨hsplits, hroots⟩
  · left
    rw [degreeSignFlip_eq_C_mul_comp_neg_X n (by simp)]
    simp
  · right
    refine ⟨degreeSignFlip_splits_of_splits hpdeg hsplits, ?_⟩
    intro r hr
    rw [roots_degreeSignFlip hpdeg] at hr
    rcases Multiset.mem_map.mp hr with ⟨x, hx, rfl⟩
    exact neg_nonpos.mpr (hroots x hx)

private theorem degreeSignFlip_two_quadratic (a b c : ℝ) :
    degreeSignFlip 2 (C a * X ^ 2 + C b * X + C c : ℝ[X]) =
      C a * X ^ 2 + C (-b) * X + C c := by
  ext j
  rcases j with _ | j
  · rw [coeff_degreeSignFlip_of_le _ (by norm_num : 0 ≤ 2)]
    simp
  rcases j with _ | j
  · rw [coeff_degreeSignFlip_of_le _ (by norm_num : 1 ≤ 2)]
    simp
  rcases j with _ | j
  · rw [coeff_degreeSignFlip_of_le _ le_rfl]
    simp
  · have hj : 2 < j + 1 + 1 + 1 := by lia
    rw [coeff_degreeSignFlip_of_lt _ hj]
    simp

/-- The linear basis transform sending `X ^ k` to `P k`. -/
def basisTransform (P : ℕ → ℝ[X]) (p : ℝ[X]) : ℝ[X] :=
  p.sum fun k a => C a * P k

theorem coeff_basisTransform (P : ℕ → ℝ[X]) (p : ℝ[X]) (j : ℕ) :
    (basisTransform P p).coeff j = p.sum fun k a => a * (P k).coeff j := by
  simp [basisTransform, Polynomial.coeff_sum, Polynomial.coeff_C_mul]

@[simp] theorem basisTransform_zero (P : ℕ → ℝ[X]) :
    basisTransform P 0 = 0 := by
  simp [basisTransform]

@[simp] theorem basisTransform_monomial (P : ℕ → ℝ[X]) (n : ℕ) (a : ℝ) :
    basisTransform P (Polynomial.monomial n a) = C a * P n := by
  rw [basisTransform, Polynomial.sum_monomial_index]
  simp

@[simp] theorem basisTransform_C (P : ℕ → ℝ[X]) (a : ℝ) :
    basisTransform P (C a) = C a * P 0 := by
  simpa using basisTransform_monomial P 0 a

@[simp] theorem basisTransform_X_pow (P : ℕ → ℝ[X]) (n : ℕ) :
    basisTransform P (X ^ n) = P n := by
  rw [show (X ^ n : ℝ[X]) = Polynomial.monomial n 1 by
    simp [Polynomial.X_pow_eq_monomial]]
  simp

theorem basisTransform_add (P : ℕ → ℝ[X]) (p q : ℝ[X]) :
    basisTransform P (p + q) = basisTransform P p + basisTransform P q := by
  rw [basisTransform, basisTransform, basisTransform]
  exact Polynomial.sum_add_index p q (fun k a => C a * P k) (by simp) (by simp [add_mul])

theorem basisTransform_smul (P : ℕ → ℝ[X]) (a : ℝ) (p : ℝ[X]) :
    basisTransform P (a • p) = C a * basisTransform P p := by
  rw [basisTransform, basisTransform]
  rw [Polynomial.sum_smul_index]
  · simp [Polynomial.sum_def, Finset.mul_sum, mul_assoc]
  · simp

theorem HasNonnegCoeffs.basisTransform {P : ℕ → ℝ[X]} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hP : ∀ k, HasNonnegCoeffs (P k)) :
    HasNonnegCoeffs (basisTransform P p) := by
  intro j
  rw [coeff_basisTransform]
  simpa only [Polynomial.sum] using
    Finset.sum_nonneg fun k _ => mul_nonneg (hp k) (hP k j)

/-- Falling factorial `⟨x⟩_k = x (x - 1) ... (x - k + 1)`. -/
def fallingFactorialPolynomial (k : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.range k, (X - C (i : ℝ))

/-- The falling-factorial basis transform is the identity on degree-one
polynomials. -/
theorem basisTransform_fallingFactorial_eq_self_of_natDegree_eq_one {p : ℝ[X]}
    (hpdeg : p.natDegree = 1) :
    basisTransform fallingFactorialPolynomial p = p := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hpdeg.le]
  rw [basisTransform_add]
  rw [Polynomial.C_mul', basisTransform_smul]
  rw [show (X : ℝ[X]) = X ^ 1 by simp, basisTransform_X_pow]
  simp [fallingFactorialPolynomial, Polynomial.C_mul']

/-- Degree-two expansion of the falling-factorial basis transform. -/
theorem basisTransform_fallingFactorial_eq_quadratic_of_natDegree_eq_two {p : ℝ[X]}
    (hpdeg : p.natDegree = 2) :
    basisTransform fallingFactorialPolynomial p =
      C (p.coeff 2) * X ^ 2 + C (p.coeff 1 - p.coeff 2) * X + C (p.coeff 0) := by
  have hpform : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
    Polynomial.eq_quadratic_of_degree_le_two (p := p)
      (Polynomial.degree_le_of_natDegree_le (by rw [hpdeg]))
  have hBX : basisTransform fallingFactorialPolynomial (X : ℝ[X]) = X := by
    rw [show (X : ℝ[X]) = X ^ 1 by simp, basisTransform_X_pow]
    simp [fallingFactorialPolynomial]
  conv_lhs => rw [hpform]
  simp only [basisTransform_add, Polynomial.C_mul', basisTransform_smul, hBX, basisTransform_C]
  simp only [basisTransform_X_pow, fallingFactorialPolynomial, map_natCast, range_zero,
    prod_empty]
  norm_num [Finset.prod_range_succ]
  repeat rw [Polynomial.smul_eq_C_mul]
  rw [map_sub]
  ring_nf

/-- Generalized rising factorial `(x|μ)_k = x (x + μ) ... (x + (k-1) μ)`. -/
def risingFactorialPolynomial (μ : ℝ) (k : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.range k, (X + C ((i : ℝ) * μ))

/-- Append the final factor to a generalized rising factorial. -/
theorem risingFactorialPolynomial_succ_mul (μ : ℝ) (n : ℕ) :
    risingFactorialPolynomial μ (n + 1) =
      risingFactorialPolynomial μ n * (X + C ((n : ℝ) * μ)) := by
  simp [risingFactorialPolynomial, Finset.prod_range_succ]

/-- A generalized rising factorial is `X` times the preceding factorial
translated by `μ`. -/
theorem risingFactorialPolynomial_succ_shift (μ : ℝ) (n : ℕ) :
    risingFactorialPolynomial μ (n + 1) =
      X * (risingFactorialPolynomial μ n).comp (X + C μ) := by
  induction n with
  | zero =>
      simp [risingFactorialPolynomial]
  | succ n ih =>
      rw [risingFactorialPolynomial_succ_mul]
      nth_rewrite 1 [ih]
      rw [risingFactorialPolynomial_succ_mul]
      simp only [mul_comp, X_comp, add_comp, C_comp]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

/-- Multiplication by `X` before the rising-factorial basis transform becomes
multiplication by `X` followed by translation after the transform. -/
theorem basisTransform_risingFactorial_X_mul (μ : ℝ) (p : ℝ[X]) :
    basisTransform (risingFactorialPolynomial μ) (X * p) =
      X * (basisTransform (risingFactorialPolynomial μ) p).comp (X + C μ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [mul_add, basisTransform_add, hp, hq, add_comp]
  | monomial n a =>
      rw [Polynomial.X_mul_monomial]
      simp only [basisTransform_monomial]
      rw [risingFactorialPolynomial_succ_shift]
      simp only [mul_comp, C_comp]
      ring

/-- Su--Yang--Zhang's induction recurrence for the generalized
rising-factorial basis transform. -/
theorem basisTransform_risingFactorial_mul_X_add_C (μ r : ℝ) (p : ℝ[X]) :
    basisTransform (risingFactorialPolynomial μ) ((X + C r) * p) =
      X * (basisTransform (risingFactorialPolynomial μ) p).comp (X + C μ) +
        C r * basisTransform (risingFactorialPolynomial μ) p := by
  rw [add_mul, basisTransform_add, basisTransform_risingFactorial_X_mul]
  rw [Polynomial.C_mul', basisTransform_smul]

private theorem listInterlaces_map_sub_tail_of_pairwise_add_le
    (μ : ℝ) (hμ : 0 ≤ μ) :
    ∀ {r : ℝ} {rs : List ℝ},
      (r :: rs).Pairwise (fun x y => x + μ ≤ y) →
        ListInterlaces (rs.map fun x => x - μ) (r :: rs)
  | _, [], _ => by simp [ListInterlaces]
  | r, s :: ss, hpair => by
      rw [List.pairwise_cons] at hpair
      simp only [List.map_cons, ListInterlaces]
      refine ⟨by linarith [hpair.1 s (by simp)], by linarith, ?_⟩
      exact listInterlaces_map_sub_tail_of_pairwise_add_le μ hμ hpair.2

private theorem listAlternates_map_sub_of_pairwise_add_le
    (μ : ℝ) (hμ : 0 ≤ μ) :
    ∀ {rs : List ℝ}, rs.Pairwise (fun x y => x + μ ≤ y) →
      ListAlternates (rs.map fun x => x - μ) rs
  | [], _ => by simp [ListAlternates]
  | r :: rs, hpair => by
      simp only [List.map_cons, ListAlternates]
      exact ⟨by linarith, listInterlaces_map_sub_tail_of_pairwise_add_le μ hμ hpair⟩

private theorem listInterlaces_roots_sort_of_interlaces {g f : ℝ[X]}
    (h : Interlaces g f) :
    ListInterlaces (g.roots.sort (· ≤ ·)) (f.roots.sort (· ≤ ·)) := by
  rcases h with ⟨_, _, _, rs, ss, hrs, hss, hrs_eq, hss_eq, hint⟩
  have hss_unique : ss = g.roots.sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise' hss (Multiset.pairwise_sort ..)
    exact Multiset.coe_eq_coe.mp (hss_eq.trans (Multiset.sort_eq ..).symm)
  have hrs_unique : rs = f.roots.sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise' hrs (Multiset.pairwise_sort ..)
    exact Multiset.coe_eq_coe.mp (hrs_eq.trans (Multiset.sort_eq ..).symm)
  simpa [hss_unique, hrs_unique] using hint

private theorem pairwise_add_le_of_two_listInterlaces (μ : ℝ) :
    ∀ {ps qs : List ℝ},
      qs.Pairwise (· ≤ ·) →
      ListInterlaces ps qs →
      ListInterlaces (ps.map fun x => x - μ) qs →
      qs.Pairwise (fun x y => x + μ ≤ y)
  | [], [], _, _, _ => by simp
  | [], [_], _, _, _ => by simp
  | [], _ :: _ :: _, _, h, _ => by simp [ListInterlaces] at h
  | _ :: _, [], _, h, _ => by simp [ListInterlaces] at h
  | _ :: _, [_], _, h, _ => by simp [ListInterlaces] at h
  | p :: ps, q₁ :: q₂ :: qs, hsorted, hleft, hshift => by
      simp only [ListInterlaces] at hleft
      simp only [List.map_cons, ListInterlaces] at hshift
      rw [List.pairwise_cons]
      refine ⟨?_, pairwise_add_le_of_two_listInterlaces μ
        (List.pairwise_cons.mp hsorted).2 hleft.2.2 hshift.2.2⟩
      intro q hq
      have hq₂q : q₂ ≤ q := by
        rcases List.mem_cons.mp hq with rfl | hq
        · exact le_rfl
        · exact List.rel_of_pairwise_cons (List.pairwise_cons.mp hsorted).2 hq
      linarith [hleft.2.1, hshift.1]

/-- Two interlacings against a polynomial and its translate recover the root
spacing invariant after a degree-increasing step. -/
private theorem prec_comp_X_add_C_of_two_interlacings
    {μ : ℝ} (hμ : 0 ≤ μ) {p q : ℝ[X]}
    (hpq : Prec p q) (hshiftq : Prec (p.comp (X + C μ)) q)
    (hdeg : p.natDegree + 1 = q.natDegree) :
    Prec (q.comp (X + C μ)) q := by
  let ps := p.roots.sort (· ≤ ·)
  let qs := q.roots.sort (· ≤ ·)
  have hpq_int : ListInterlaces ps qs :=
    listInterlaces_roots_sort_of_interlaces (hpq.toInterlaces hdeg)
  have hshiftdeg : (p.comp (X + C μ)).natDegree + 1 = q.natDegree := by
    simpa [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C] using hdeg
  have hshift_int :
      ListInterlaces ((p.comp (X + C μ)).roots.sort (· ≤ ·)) qs :=
    listInterlaces_roots_sort_of_interlaces (hshiftq.toInterlaces hshiftdeg)
  have hshift_roots :
      (p.comp (X + C μ)).roots.sort (· ≤ ·) = ps.map (fun x => x - μ) := by
    apply List.Perm.eq_of_pairwise' (r := fun x y : ℝ => x ≤ y)
    · exact Multiset.pairwise_sort ..
    · exact pairwise_map_sub_const (Multiset.pairwise_sort ..) μ
    · apply Multiset.coe_eq_coe.mp
      calc
        (↑((p.comp (X + C μ)).roots.sort (· ≤ ·)) : Multiset ℝ) =
            (p.comp (X + C μ)).roots := Multiset.sort_eq ..
        _ = p.roots.map (fun x => x - μ) := roots_comp_X_add_C μ
        _ = (↑ps : Multiset ℝ).map (fun x => x - μ) := by
          rw [show (↑ps : Multiset ℝ) = p.roots by exact Multiset.sort_eq ..]
        _ = (↑(ps.map fun x => x - μ) : Multiset ℝ) := rfl
  rw [hshift_roots] at hshift_int
  have hqs_sorted : qs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hqs_gap : qs.Pairwise (fun x y => x + μ ≤ y) :=
    pairwise_add_le_of_two_listInterlaces μ hqs_sorted hpq_int hshift_int
  have hqrr := hpq.2.1
  refine ⟨isRealRooted_comp_X_add_C hqrr.1 hqrr.2 μ, hqrr,
    qs.map (fun x => x - μ), qs, ?_, hqs_sorted, ?_, Multiset.sort_eq ..,
      Or.inr ⟨by simp, listAlternates_map_sub_of_pairwise_add_le μ hμ hqs_gap⟩⟩
  · grind
  · calc
      (↑(qs.map fun x => x - μ) : Multiset ℝ) =
          (↑qs : Multiset ℝ).map (fun x => x - μ) := rfl
      _ = q.roots.map (fun x => x - μ) := by rw [show (↑qs : Multiset ℝ) = q.roots by
        exact Multiset.sort_eq ..]
      _ = (q.comp (X + C μ)).roots := (roots_comp_X_add_C μ).symm

/-- The Su--Yang--Zhang recurrence preserves both the PF property and the
translate-proper-position invariant encoding `μ`-separated roots. -/
private theorem risingFactorialStep_pf_shiftPrec
    {μ r : ℝ} (hμ : 0 ≤ μ) (hr : 0 ≤ r) {f : ℝ[X]}
    (hf : IsPFPolynomial f) (hshift : Prec (f.comp (X + C μ)) f) :
    let g := X * f.comp (X + C μ) + C r * f
    IsPFPolynomial g ∧ Prec (g.comp (X + C μ)) g := by
  dsimp
  let fμ := f.comp (X + C μ)
  have hfrr := hshift.2.1
  have hf_pos : HasPosLeadingCoeff f := hf.hasNonnegCoeffs.pos_leadingCoeff hfrr.1
  have hfμrr : fμ ≠ 0 ∧ fμ.Splits :=
    isRealRooted_comp_X_add_C hfrr.1 hfrr.2 μ
  have hfμnn : HasNonnegCoeffs fμ :=
    hasNonnegCoeffs_comp_X_add_C_of_roots_le hf_pos hfrr.2 fun s hs => by
      linarith [hf.roots_nonpos s hs]
  have hfμ : IsPFPolynomial fμ :=
    IsPFPolynomial.of_realRooted_nonneg hfμnn hfμrr.2
  have hf_Xfμ : Prec f (X * fμ) := by
    simpa [fμ] using
      prec_mul_X_of_prec_of_nonneg hshift hfμ.hasNonnegCoeffs hf.hasNonnegCoeffs
  have hfμ_Xfμ : Prec fμ (X * fμ) :=
    prec_mul_X_of_prec_of_nonneg (prec_refl hfμrr.1 hfμrr.2)
      hfμ.hasNonnegCoeffs hfμ.hasNonnegCoeffs
  have hXfμnn : HasNonnegCoeffs (X * fμ) := hfμ.X_mul.hasNonnegCoeffs
  have hrf_nn : HasNonnegCoeffs (C r * f) :=
    nonnegCoeffs_C_mul hr hf.hasNonnegCoeffs
  have hf_g0 : Prec0 f (X * fμ + C r * f) :=
    prec0_add_right_of_common_left_of_nonneg hf_Xfμ.toPrec0
      (prec0_C_mul_right_of_nonneg hf.prec0_self hr) hXfμnn hrf_nn
  have hfμ_g0 : Prec0 fμ (X * fμ + C r * f) :=
    prec0_add_right_of_common_left_of_nonneg hfμ_Xfμ.toPrec0
      (prec0_C_mul_right_of_nonneg hshift.toPrec0 hr) hXfμnn hrf_nn
  have hg0 : X * fμ + C r * f ≠ 0 := by
    intro hg
    have hcoeff := congrArg
      (fun p : ℝ[X] => p.coeff (X * fμ).natDegree) hg
    have hXpos : HasPosLeadingCoeff (X * fμ) :=
      (hfμ.hasNonnegCoeffs.pos_leadingCoeff hfμrr.1).X_mul
    have hXcoeff : 0 < (X * fμ).coeff (X * fμ).natDegree := by
      change 0 < (X * fμ).coeff (X * fμ).natDegree at hXpos
      exact hXpos
    have hrf_coeff := hrf_nn (X * fμ).natDegree
    simp only [coeff_add, coeff_zero] at hcoeff
    linarith
  have hfg : Prec f (X * fμ + C r * f) :=
    hf_g0.toPrec_of_ne hfrr.1 hg0
  have hfμg : Prec fμ (X * fμ + C r * f) :=
    hfμ_g0.toPrec_of_ne hfμrr.1 hg0
  have hfμdeg : fμ.natDegree = f.natDegree := by
    simp [fμ, Polynomial.natDegree_comp]
  have hXfμdeg : (X * fμ).natDegree = f.natDegree + 1 := by
    rw [Polynomial.natDegree_mul X_ne_zero hfμrr.1, Polynomial.natDegree_X, hfμdeg]
    simp [add_comm]
  have hrfdeg : (C r * f).natDegree ≤ f.natDegree := Polynomial.natDegree_C_mul_le r f
  have hgdeg : (X * fμ + C r * f).natDegree = f.natDegree + 1 := by
    rw [natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff]
    · exact hXfμdeg
    · rw [hXfμdeg]
      lia
    · exact (hfμ.hasNonnegCoeffs.pos_leadingCoeff hfμrr.1).X_mul
  have hgpf : IsPFPolynomial (X * fμ + C r * f) :=
    IsPFPolynomial.of_realRooted_nonneg (hXfμnn.add hrf_nn) hfg.2.1.2
  exact ⟨hgpf, prec_comp_X_add_C_of_two_interlacings hμ hfg hfμg (by lia)⟩

/-- The generalized rising-factorial basis transform is the identity on
degree-one polynomials. -/
theorem basisTransform_risingFactorial_eq_self_of_natDegree_eq_one {μ : ℝ} {p : ℝ[X]}
    (hpdeg : p.natDegree = 1) :
    basisTransform (risingFactorialPolynomial μ) p = p := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hpdeg.le]
  rw [basisTransform_add]
  rw [Polynomial.C_mul', basisTransform_smul]
  rw [show (X : ℝ[X]) = X ^ 1 by simp, basisTransform_X_pow]
  simp [risingFactorialPolynomial, Polynomial.C_mul']

/-- Degree-two expansion of the generalized rising-factorial basis transform. -/
theorem basisTransform_risingFactorial_eq_quadratic_of_natDegree_eq_two
    {μ : ℝ} {p : ℝ[X]} (hpdeg : p.natDegree = 2) :
    basisTransform (risingFactorialPolynomial μ) p =
      C (p.coeff 2) * X ^ 2 + C (p.coeff 1 + μ * p.coeff 2) * X + C (p.coeff 0) := by
  have hpform : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
    Polynomial.eq_quadratic_of_degree_le_two (p := p)
      (Polynomial.degree_le_of_natDegree_le (by rw [hpdeg]))
  have hBX : basisTransform (risingFactorialPolynomial μ) (X : ℝ[X]) = X := by
    rw [show (X : ℝ[X]) = X ^ 1 by simp, basisTransform_X_pow]
    simp [risingFactorialPolynomial]
  conv_lhs => rw [hpform]
  simp only [basisTransform_add, Polynomial.C_mul', basisTransform_smul, hBX, basisTransform_C]
  simp only [basisTransform_X_pow, risingFactorialPolynomial, map_mul, map_natCast, range_zero,
    prod_empty]
  norm_num [Finset.prod_range_succ]
  repeat rw [Polynomial.smul_eq_C_mul]
  rw [map_add, map_mul]
  ring_nf

/-- Brenti's falling-factorial inverse transform, paper Lemma 3.9 / Brenti
Theorem 2.4.2. -/
abbrev brentiFallingFactorialStatement : Prop :=
  ∀ {p : ℝ[X]},
    HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p) →
      HasOnlyNonposRoots p

/-- Degree-zero case of Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial_of_natDegree_eq_zero {p : ℝ[X]}
    (hpdeg : p.natDegree = 0)
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  have hpC : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hpdeg
  rw [hpC] at h ⊢
  simpa [fallingFactorialPolynomial] using h

/-- Degree-one case of Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial_of_natDegree_eq_one {p : ℝ[X]}
    (hpdeg : p.natDegree = 1)
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  simpa [basisTransform_fallingFactorial_eq_self_of_natDegree_eq_one hpdeg] using h

private theorem brentiFallingFactorial_of_natDegree_eq_two_pos_leading {p : ℝ[X]}
    (hpdeg : p.natDegree = 2) (hpos : 0 < p.coeff 2)
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  let q := basisTransform fallingFactorialPolynomial p
  have hqform : q = C (p.coeff 2) * X ^ 2 + C (p.coeff 1 - p.coeff 2) * X +
      C (p.coeff 0) := by
    exact basisTransform_fallingFactorial_eq_quadratic_of_natDegree_eq_two hpdeg
  have hqdeg : q.natDegree = 2 := by
    rw [hqform]
    exact Polynomial.natDegree_quadratic hpos.ne'
  have hqlead_eq : q.leadingCoeff = p.coeff 2 := by
    rw [Polynomial.leadingCoeff, hqdeg, hqform]
    simp
  have hqlead : HasPosLeadingCoeff q := by
    rw [HasPosLeadingCoeff, hqlead_eq]
    exact hpos
  have hq0 : q ≠ 0 := hqlead.ne_zero
  rcases h with hzero | ⟨hqsplits, hqroots⟩
  · exact (hq0 hzero).elim
  have hqnn : HasNonnegCoeffs q :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hqsplits).mpr
      ⟨hqlead, hqroots⟩).1
  have hd : 0 ≤ p.coeff 1 - p.coeff 2 := by
    have hcoeff := hqnn 1
    rw [hqform] at hcoeff
    simpa using hcoeff
  have hc : 0 ≤ p.coeff 0 := by
    have hcoeff := hqnn 0
    rw [hqform] at hcoeff
    simpa using hcoeff
  have hb : 0 ≤ p.coeff 1 := by nlinarith
  have hpform : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
    Polynomial.eq_quadratic_of_degree_le_two (p := p)
      (Polynomial.degree_le_of_natDegree_le (by rw [hpdeg]))
  have hpnn : HasNonnegCoeffs p := by
    rw [hpform]
    exact ((nonnegCoeffs_C_mul hpos.le (hasNonnegCoeffs_X.pow 2)).add
      (nonnegCoeffs_C_mul hb hasNonnegCoeffs_X)).add (hasNonnegCoeffs_C hc)
  have hqquad_splits : (C (p.coeff 2) * X ^ 2 + C (p.coeff 1 - p.coeff 2) * X +
      C (p.coeff 0) : ℝ[X]).Splits := by
    rwa [← hqform]
  have hdisc_q : 4 * p.coeff 2 * p.coeff 0 ≤ (p.coeff 1 - p.coeff 2) ^ 2 :=
    (quadraticPoly_splits_iff_le hpos).mp hqquad_splits
  have hdisc_p : 4 * p.coeff 2 * p.coeff 0 ≤ p.coeff 1 ^ 2 := by
    nlinarith [sq_nonneg (p.coeff 2), mul_nonneg hd hpos.le]
  have hpsplits_quad : (C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X +
      C (p.coeff 0) : ℝ[X]).Splits :=
    quadraticPoly_splits_of_le hpos hdisc_p
  have hpsplits : p.Splits := by
    simpa [← hpform] using hpsplits_quad
  exact HasOnlyNonposRoots.of_nonnegCoeffs_splits hpnn hpsplits

/-- Degree-two case of Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial_of_natDegree_eq_two {p : ℝ[X]}
    (hpdeg : p.natDegree = 2)
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  have hp0 : p ≠ 0 := by
    intro hpzero
    simp [hpzero] at hpdeg
  have hcoeff2_ne : p.coeff 2 ≠ 0 := by
    simpa [Polynomial.leadingCoeff, hpdeg] using (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  rcases lt_or_gt_of_ne hcoeff2_ne with hneg | hpos
  · have hnegdeg : (-p).natDegree = 2 := by
      rw [Polynomial.natDegree_neg, hpdeg]
    have hnegpos : 0 < (-p).coeff 2 := by
      simp
      linarith
    have htransform_neg : basisTransform fallingFactorialPolynomial (-p) =
        -basisTransform fallingFactorialPolynomial p := by
      rw [show (-p : ℝ[X]) = (-1 : ℝ) • p by simp, basisTransform_smul]
      simp
    have hnegroots : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial (-p)) := by
      rw [htransform_neg]
      exact h.neg
    have hpneg :=
      brentiFallingFactorial_of_natDegree_eq_two_pos_leading hnegdeg hnegpos hnegroots
    exact hpneg.of_neg
  · exact brentiFallingFactorial_of_natDegree_eq_two_pos_leading hpdeg hpos h

/-- Positive-degree leaf for Brenti's falling-factorial inverse transform. -/
abbrev brentiFallingFactorialPositiveDegreeStatement : Prop :=
  ∀ {p : ℝ[X]},
    0 < p.natDegree →
    HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p) →
      HasOnlyNonposRoots p

/-- Degree-at-least-three leaf for Brenti's falling-factorial inverse transform. -/
abbrev brentiFallingFactorialDegreeAtLeastThreeStatement : Prop :=
  ∀ {p : ℝ[X]},
    3 ≤ p.natDegree →
    HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p) →
      HasOnlyNonposRoots p

/-- Degree-at-least-three case of Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial_degreeAtLeastThree {p : ℝ[X]} (hpdeg : 3 ≤ p.natDegree)
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  sorry

/-- Degree-at-least-two case of Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial_degreeAtLeastTwo {p : ℝ[X]} (hpdeg : 2 ≤ p.natDegree)
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  by_cases hdeg2 : p.natDegree = 2
  · exact brentiFallingFactorial_of_natDegree_eq_two hdeg2 h
  · exact brentiFallingFactorial_degreeAtLeastThree (by lia) h

/-- Positive-degree case of Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial_positiveDegree {p : ℝ[X]} (hpdeg : 0 < p.natDegree)
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  by_cases hdeg1 : p.natDegree = 1
  · exact brentiFallingFactorial_of_natDegree_eq_one hdeg1 h
  · exact brentiFallingFactorial_degreeAtLeastTwo (by lia) h

/-- Brenti's falling-factorial inverse transform. -/
theorem brentiFallingFactorial {p : ℝ[X]}
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p := by
  rcases Nat.eq_zero_or_pos p.natDegree with hpdeg | hpdeg
  · exact brentiFallingFactorial_of_natDegree_eq_zero hpdeg h
  · exact brentiFallingFactorial_positiveDegree hpdeg h

/-- Su--Yang--Zhang generalized rising-factorial transform, paper Lemma 3.11.
-/
abbrev generalizedRisingFactorialPreservesPFStatement : Prop :=
  ∀ {μ : ℝ}, 0 < μ → ∀ {p : ℝ[X]},
    IsPFPolynomial p → IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p)

/-- Degree-zero case of the Su--Yang--Zhang generalized rising-factorial
transform. -/
theorem generalizedRisingFactorialPreservesPF_of_natDegree_eq_zero {μ : ℝ}
    {p : ℝ[X]} (hpdeg : p.natDegree = 0) (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) := by
  have hpC : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hpdeg
  rw [hpC] at hp ⊢
  simpa [risingFactorialPolynomial] using hp

/-- Degree-one case of the Su--Yang--Zhang generalized rising-factorial
transform. -/
theorem generalizedRisingFactorialPreservesPF_of_natDegree_eq_one {μ : ℝ}
    {p : ℝ[X]} (hpdeg : p.natDegree = 1) (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) := by
  simpa [basisTransform_risingFactorial_eq_self_of_natDegree_eq_one hpdeg] using hp

/-- Degree-two case of the Su--Yang--Zhang generalized rising-factorial
transform. -/
theorem generalizedRisingFactorialPreservesPF_of_natDegree_eq_two {μ : ℝ}
    (hμ : 0 ≤ μ) {p : ℝ[X]} (hpdeg : p.natDegree = 2) (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) := by
  rw [basisTransform_risingFactorial_eq_quadratic_of_natDegree_eq_two hpdeg]
  have hp0 : p ≠ 0 := by
    intro hpzero
    simp [hpzero] at hpdeg
  have hp_pos : HasPosLeadingCoeff p := hp.hasNonnegCoeffs.pos_leadingCoeff hp0
  have ha : 0 < p.coeff 2 := by
    simpa [HasPosLeadingCoeff, Polynomial.leadingCoeff, hpdeg] using hp_pos
  have hb : 0 ≤ p.coeff 1 := hp.hasNonnegCoeffs 1
  have hc : 0 ≤ p.coeff 0 := hp.hasNonnegCoeffs 0
  have hpsplits : p.Splits := (hp.ne_zero_and_splits hp0).2
  have hpform : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
    Polynomial.eq_quadratic_of_degree_le_two (p := p)
      (Polynomial.degree_le_of_natDegree_le (by rw [hpdeg]))
  have hquad_splits : (C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X +
      C (p.coeff 0) : ℝ[X]).Splits := by
    simpa [← hpform] using hpsplits
  have hdisc : 4 * p.coeff 2 * p.coeff 0 ≤ p.coeff 1 ^ 2 :=
    (quadraticPoly_splits_iff_le ha).mp hquad_splits
  have hmu_a : 0 ≤ μ * p.coeff 2 := mul_nonneg hμ ha.le
  have hsquare : p.coeff 1 ^ 2 ≤ (p.coeff 1 + μ * p.coeff 2) ^ 2 := by
    nlinarith [sq_nonneg (μ * p.coeff 2), mul_nonneg hb hmu_a]
  have hdisc' : 4 * p.coeff 2 * p.coeff 0 ≤ (p.coeff 1 + μ * p.coeff 2) ^ 2 :=
    hdisc.trans hsquare
  exact IsPFPolynomial.of_realRooted_nonneg
    (((nonnegCoeffs_C_mul ha.le (hasNonnegCoeffs_X.pow 2)).add
      (nonnegCoeffs_C_mul (add_nonneg hb hmu_a) hasNonnegCoeffs_X)).add
        (hasNonnegCoeffs_C hc))
    (quadraticPoly_splits_of_le ha hdisc')

private theorem generalizedRisingFactorialPreservesPF_shiftPrec {μ : ℝ}
    (hμ : 0 < μ) :
    ∀ n (p : ℝ[X]), p.natDegree = n → p ≠ 0 → IsPFPolynomial p →
      let q := basisTransform (risingFactorialPolynomial μ) p
      IsPFPolynomial q ∧ Prec (q.comp (X + C μ)) q := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p hpdeg hp0 hp
      by_cases hn0 : n = 0
      · have hpdeg0 : p.natDegree = 0 := by lia
        have hpC : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hpdeg0
        have htransform : basisTransform (risingFactorialPolynomial μ) p = p := by
          rw [hpC]
          simp [risingFactorialPolynomial]
        rw [htransform]
        dsimp
        have hpcomp : p.comp (X + C μ) = p := by
          rw [hpC]
          simp
        rw [hpcomp]
        exact ⟨hp, prec_refl hp0 (hp.ne_zero_and_splits hp0).2⟩
      · have hnpos : 0 < p.natDegree := by lia
        rcases hp.exists_X_sub_C_factor_of_pos_natDegree hnpos with
          ⟨u, q, hu, hfactor, hq, hqdeg⟩
        have hq0 : q ≠ 0 := by
          intro hqzero
          apply hp0
          simp [hfactor, hqzero]
        have ihq := ih q.natDegree (by lia) q rfl hq0 hq
        have hstep := risingFactorialStep_pf_shiftPrec hμ.le (neg_nonneg.mpr hu)
          ihq.1 ihq.2
        have hfactor' : p = (X + C (-u)) * q := by
          simpa [sub_eq_add_neg] using hfactor
        rw [hfactor', basisTransform_risingFactorial_mul_X_add_C]
        exact hstep

/-- Positive-degree leaf for the Su--Yang--Zhang generalized rising-factorial
transform. -/
abbrev generalizedRisingFactorialPreservesPFPositiveDegreeStatement : Prop :=
  ∀ {μ : ℝ}, 0 < μ → ∀ {p : ℝ[X]},
    0 < p.natDegree →
    IsPFPolynomial p → IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p)

/-- Degree-at-least-three leaf for the Su--Yang--Zhang generalized
rising-factorial transform. -/
abbrev generalizedRisingFactorialPreservesPFDegreeAtLeastThreeStatement : Prop :=
  ∀ {μ : ℝ}, 0 < μ → ∀ {p : ℝ[X]},
    3 ≤ p.natDegree →
    IsPFPolynomial p → IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p)

/-- Degree-at-least-three case of the Su--Yang--Zhang generalized rising-factorial
transform. -/
theorem generalizedRisingFactorialPreservesPF_degreeAtLeastThree {μ : ℝ} (hμ : 0 < μ)
    {p : ℝ[X]} (hpdeg : 3 ≤ p.natDegree) (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) := by
  exact (generalizedRisingFactorialPreservesPF_shiftPrec hμ p.natDegree p rfl
    (by intro hpzero; simp [hpzero] at hpdeg) hp).1

/-- Degree-at-least-two case of the Su--Yang--Zhang generalized rising-factorial
transform. -/
theorem generalizedRisingFactorialPreservesPF_degreeAtLeastTwo {μ : ℝ} (hμ : 0 < μ)
    {p : ℝ[X]} (hpdeg : 2 ≤ p.natDegree) (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) := by
  by_cases hdeg2 : p.natDegree = 2
  · exact generalizedRisingFactorialPreservesPF_of_natDegree_eq_two hμ.le hdeg2 hp
  · exact generalizedRisingFactorialPreservesPF_degreeAtLeastThree hμ (by lia) hp

/-- Positive-degree case of the Su--Yang--Zhang generalized rising-factorial
transform. -/
theorem generalizedRisingFactorialPreservesPF_positiveDegree {μ : ℝ} (hμ : 0 < μ)
    {p : ℝ[X]} (hpdeg : 0 < p.natDegree) (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) := by
  by_cases hdeg1 : p.natDegree = 1
  · exact generalizedRisingFactorialPreservesPF_of_natDegree_eq_one hdeg1 hp
  · exact generalizedRisingFactorialPreservesPF_degreeAtLeastTwo hμ (by lia) hp

/-- Su--Yang--Zhang generalized rising-factorial transform preserves PF polynomials. -/
theorem generalizedRisingFactorialPreservesPF {μ : ℝ} (hμ : 0 < μ) {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) := by
  rcases Nat.eq_zero_or_pos p.natDegree with hpdeg | hpdeg
  · exact generalizedRisingFactorialPreservesPF_of_natDegree_eq_zero hpdeg hp
  · exact generalizedRisingFactorialPreservesPF_positiveDegree hμ hpdeg hp

/-- Coefficient `N_m(n,k)` of the generalized Narayana polynomial. -/
def narayanaTransformCoeff (m n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * (Nat.choose (n + m) k : ℝ) /
    (Nat.choose (m + k) k : ℝ)

theorem narayanaTransformCoeff_nonneg (m n k : ℕ) :
    0 ≤ narayanaTransformCoeff m n k := by
  unfold narayanaTransformCoeff
  positivity

@[simp] theorem narayanaTransformCoeff_zero_right (m n : ℕ) :
    narayanaTransformCoeff m n 0 = 1 := by
  simp [narayanaTransformCoeff]

@[simp] theorem narayanaTransformCoeff_zero_left (m k : ℕ) :
    narayanaTransformCoeff m 0 k = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk, narayanaTransformCoeff]
  · have hchoose : Nat.choose 0 k = 0 := by
      cases k with
      | zero => contradiction
      | succ k => simp
    simp [hk, narayanaTransformCoeff, hchoose]

/-- Generalized Narayana polynomial `N_{n,m}` from Mao--Wang, Eq. (1.2). -/
def narayanaPolynomial (m n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (narayanaTransformCoeff m n k) * X ^ k

@[simp] theorem coeff_narayanaPolynomial_of_le {m n k : ℕ} (hk : k ≤ n) :
    (narayanaPolynomial m n).coeff k = narayanaTransformCoeff m n k := by
  simp [narayanaPolynomial, hk]

@[simp] theorem coeff_narayanaPolynomial_of_lt {m n k : ℕ} (hk : n < k) :
    (narayanaPolynomial m n).coeff k = 0 := by
  simp [narayanaPolynomial, hk.not_ge]

theorem hasNonnegCoeffs_narayanaPolynomial (m n : ℕ) :
    HasNonnegCoeffs (narayanaPolynomial m n) := by
  intro k
  by_cases hk : k ≤ n
  · simp [coeff_narayanaPolynomial_of_le hk, narayanaTransformCoeff_nonneg]
  · have hk' : n < k := Nat.lt_of_not_ge hk
    simp [coeff_narayanaPolynomial_of_lt hk']

theorem natDegree_narayanaPolynomial_le (m n : ℕ) :
    (narayanaPolynomial m n).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  exact coeff_narayanaPolynomial_of_lt hk

/-- The Narayana basis transform `X ^ k ↦ N_{k,m}`. -/
def narayanaTransform (m : ℕ) : ℝ[X] → ℝ[X] :=
  basisTransform (narayanaPolynomial m)

@[simp] theorem narayanaTransform_X_pow (m n : ℕ) :
    narayanaTransform m (X ^ n) = narayanaPolynomial m n :=
  basisTransform_X_pow (narayanaPolynomial m) n

@[simp] theorem narayanaTransform_monomial (m n : ℕ) (a : ℝ) :
    narayanaTransform m (Polynomial.monomial n a) = C a * narayanaPolynomial m n := by
  rw [narayanaTransform, basisTransform_monomial]

theorem coeff_narayanaTransform (m : ℕ) (p : ℝ[X]) (j : ℕ) :
    (narayanaTransform m p).coeff j =
      p.sum fun k a => a * (narayanaPolynomial m k).coeff j :=
  coeff_basisTransform (narayanaPolynomial m) p j

@[simp] theorem coeff_narayanaTransform_monomial (m n j : ℕ) (a : ℝ) :
    (narayanaTransform m (Polynomial.monomial n a)).coeff j =
      a * (narayanaPolynomial m n).coeff j := by
  simp [narayanaTransform_monomial]

@[simp] theorem coeff_narayanaTransform_monomial_of_le
    {m n j : ℕ} (hj : j ≤ n) (a : ℝ) :
    (narayanaTransform m (Polynomial.monomial n a)).coeff j =
      a * narayanaTransformCoeff m n j := by
  simp [hj]

@[simp] theorem coeff_narayanaTransform_monomial_of_lt
    {m n j : ℕ} (hj : n < j) (a : ℝ) :
    (narayanaTransform m (Polynomial.monomial n a)).coeff j = 0 := by
  simp [hj]

theorem HasNonnegCoeffs.narayanaTransform {m : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (narayanaTransform m p) :=
  hp.basisTransform (hasNonnegCoeffs_narayanaPolynomial m)

theorem coeff_degreeSignFlip_narayanaTransform_of_le
    (m n : ℕ) (p : ℝ[X]) {j : ℕ} (hj : j ≤ n) :
    (degreeSignFlip n (narayanaTransform m p)).coeff j =
      (-1 : ℝ) ^ (n - j) *
        p.sum fun k a => a * (narayanaPolynomial m k).coeff j := by
  rw [coeff_degreeSignFlip_of_le (narayanaTransform m p) hj, coeff_narayanaTransform]

theorem natDegree_narayanaTransform_le (m : ℕ) (p : ℝ[X]) :
    (narayanaTransform m p).natDegree ≤ p.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_narayanaTransform, Polynomial.sum_def]
  apply Finset.sum_eq_zero
  intro k hk
  have hkdeg : k ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp k hk
  rw [coeff_narayanaPolynomial_of_lt (lt_of_le_of_lt hkdeg hj), mul_zero]

theorem narayanaTransform_coeff_sum_reflect
    (m n j : ℕ) (p : ℝ[X]) (hpdeg : p.natDegree ≤ n) (hj : j ≤ n) :
    p.sum (fun k a => a * (narayanaPolynomial m k).coeff j) =
      ∑ i ∈ Finset.range (n - j + 1),
        p.coeff (n - i) * narayanaTransformCoeff m (n - i) j := by
  let f : ℕ → ℝ := fun k => p.coeff k * (narayanaPolynomial m k).coeff j
  have hsum_range :
      p.sum (fun k a => a * (narayanaPolynomial m k).coeff j) =
        ∑ k ∈ Finset.range (n + 1), f k := by
    rw [Polynomial.sum_over_range]
    · exact Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hpdeg)) (by
        intro k hk_big hk_small
        have hkgt : p.natDegree < k := by
          have hnot : ¬ k < p.natDegree + 1 := by
            simpa [Finset.mem_range] using hk_small
          exact Nat.lt_of_not_ge (by
            intro hk_le
            exact hnot (Nat.lt_succ_iff.mpr hk_le))
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt hkgt])
    · intro k
      simp
  have hlow : ∑ k ∈ Finset.range j, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k < j := Finset.mem_range.mp hk
    simp [f, coeff_narayanaPolynomial_of_lt hkj]
  have htail :
      ∑ k ∈ Finset.range (n + 1), f k =
        ∑ k ∈ Finset.Ico j (n + 1), f k := by
    have hsplit := Finset.sum_range_add_sum_Ico f (Nat.le_succ_of_le hj)
    rw [hlow, zero_add] at hsplit
    exact hsplit.symm
  rw [hsum_range, htail, Finset.sum_Ico_eq_sum_range]
  have hlen : n + 1 - j = n - j + 1 := by lia
  rw [hlen]
  rw [← Finset.sum_range_reflect
    (fun i => p.coeff (j + i) * (narayanaPolynomial m (j + i)).coeff j)
    (n - j + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hindex : j + (n - j + 1 - 1 - i) = n - i := by lia
  rw [hindex]
  have hj_le : j ≤ n - i := by lia
  rw [coeff_narayanaPolynomial_of_le hj_le]

/-- Dominici--Johnston--Jordaan root-location input for the generalized
Narayana polynomials, paper Lemma 2.5. -/
abbrev narayanaPolynomialRootLocationStatement : Prop :=
  ∀ m n : ℕ, IsPFPolynomial (narayanaPolynomial m n)


/-- Mao--Wang Theorem 1.1 in zero-aware PF-polynomial form. -/
abbrev narayanaTransformPreservesPFStatement : Prop :=
  ∀ (m : ℕ) {p : ℝ[X]},
    IsPFPolynomial p → IsPFPolynomial (narayanaTransform m p)

/-- Gribinski--Marcus rectangular additive convolution coefficient. -/
def rectangularConvolutionGamma (m n i j : ℕ) : ℝ :=
  ((Nat.factorial (n - i) : ℝ) * (Nat.factorial (n - j) : ℝ) /
      ((Nat.factorial n : ℝ) * (Nat.factorial (n - i - j) : ℝ))) *
    ((Nat.factorial (n + m - i) : ℝ) * (Nat.factorial (n + m - j) : ℝ) /
      ((Nat.factorial (n + m) : ℝ) * (Nat.factorial (n + m - i - j) : ℝ)))

/-- The rectangular convolution coefficient is symmetric in its two indices. -/
theorem rectangularConvolutionGamma_symm (m n i j : ℕ) :
    rectangularConvolutionGamma m n i j = rectangularConvolutionGamma m n j i := by
  unfold rectangularConvolutionGamma
  rw [Nat.sub_right_comm n i j, Nat.sub_right_comm (n + m) i j]
  ring

def rectangularConvolutionCoeff (m n : ℕ) (f g : ℝ[X]) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    rectangularConvolutionGamma m n i (k - i) *
      f.coeff (n - i) * g.coeff (n - (k - i))

/-- Rectangular additive convolution in the coefficient convention of
Mao--Wang, Eq. (2.3). -/
def rectangularAdditiveConvolution (m n : ℕ) (f g : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (rectangularConvolutionCoeff m n f g k) * X ^ (n - k)

/-- Coefficient extraction for the rectangular additive convolution. -/
theorem coeff_rectangularAdditiveConvolution_of_le (m n : ℕ) (f g : ℝ[X])
    {j : ℕ} (hj : j ≤ n) :
    (rectangularAdditiveConvolution m n f g).coeff j =
      rectangularConvolutionCoeff m n f g (n - j) := by
  unfold rectangularAdditiveConvolution
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single_of_mem (n - j)
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le n j)))]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Nat.sub_sub_self hj,
      if_pos rfl, mul_one]
  · intro k hk hkne
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun hjk => hkne (by lia)), mul_zero]

/-- The rectangular additive convolution has no coefficients above degree `n`. -/
theorem coeff_rectangularAdditiveConvolution_of_gt (m n : ℕ) (f g : ℝ[X])
    {j : ℕ} (hj : n < j) :
    (rectangularAdditiveConvolution m n f g).coeff j = 0 := by
  unfold rectangularAdditiveConvolution
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun hjk => by lia),
    mul_zero]

/-- The rectangular additive convolution has degree at most `n`. -/
theorem natDegree_rectangularAdditiveConvolution_le (m n : ℕ) (f g : ℝ[X]) :
    (rectangularAdditiveConvolution m n f g).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  exact coeff_rectangularAdditiveConvolution_of_gt m n f g hk

@[simp] theorem rectangularConvolutionCoeff_zero (m : ℕ) (f g : ℝ[X]) :
    rectangularConvolutionCoeff m 0 f g 0 = f.coeff 0 * g.coeff 0 := by
  simp [rectangularConvolutionCoeff, rectangularConvolutionGamma]
  have hm : ((Nat.factorial m : ℝ) : ℝ) ≠ 0 := by positivity
  field_simp [hm]
  simp

@[simp] theorem rectangularConvolutionCoeff_one_zero (m : ℕ) (f g : ℝ[X]) :
    rectangularConvolutionCoeff m 1 f g 0 = f.coeff 1 * g.coeff 1 := by
  simp [rectangularConvolutionCoeff, rectangularConvolutionGamma]
  have hm : ((Nat.factorial (1 + m) : ℝ) : ℝ) ≠ 0 := by positivity
  field_simp [hm]
  simp

@[simp] theorem rectangularConvolutionCoeff_one_one (m : ℕ) (f g : ℝ[X]) :
    rectangularConvolutionCoeff m 1 f g 1 =
      f.coeff 1 * g.coeff 0 + f.coeff 0 * g.coeff 1 := by
  unfold rectangularConvolutionCoeff rectangularConvolutionGamma
  simp [Finset.sum_range_succ]
  have hm : ((Nat.factorial m : ℝ) : ℝ) ≠ 0 := by positivity
  have hm1 : ((Nat.factorial (1 + m) : ℝ) : ℝ) ≠ 0 := by positivity
  field_simp [hm, hm1]

private theorem rectangularConvolutionGamma_two_zero_zero (m : ℕ) :
    rectangularConvolutionGamma m 2 0 0 = 1 := by
  unfold rectangularConvolutionGamma
  norm_num
  exact (Nat.factorial_pos (2 + m)).ne'

private theorem rectangularConvolutionGamma_two_zero_one (m : ℕ) :
    rectangularConvolutionGamma m 2 0 1 = 1 := by
  unfold rectangularConvolutionGamma
  norm_num
  exact ⟨(Nat.factorial_pos (2 + m)).ne', (Nat.factorial_pos (1 + m)).ne'⟩

private theorem rectangularConvolutionGamma_two_one_zero (m : ℕ) :
    rectangularConvolutionGamma m 2 1 0 = 1 := by
  rw [rectangularConvolutionGamma_symm]
  exact rectangularConvolutionGamma_two_zero_one m

private theorem rectangularConvolutionGamma_two_zero_two (m : ℕ) :
    rectangularConvolutionGamma m 2 0 2 = 1 := by
  unfold rectangularConvolutionGamma
  norm_num
  exact ⟨(Nat.factorial_pos (2 + m)).ne', (Nat.factorial_pos m).ne'⟩

private theorem rectangularConvolutionGamma_two_two_zero (m : ℕ) :
    rectangularConvolutionGamma m 2 2 0 = 1 := by
  rw [rectangularConvolutionGamma_symm]
  exact rectangularConvolutionGamma_two_zero_two m

private theorem rectangularConvolutionGamma_two_one_one (m : ℕ) :
    rectangularConvolutionGamma m 2 1 1 = ((m : ℝ) + 1) / (2 * ((m : ℝ) + 2)) := by
  unfold rectangularConvolutionGamma
  norm_num
  rw [show 2 + m = m + 2 by lia, show 1 + m = m + 1 by lia]
  rw [Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  norm_num
  have hm : ((Nat.factorial m : ℝ) : ℝ) ≠ 0 := by positivity
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  field_simp [hm, hm2]
  ring

private theorem rectangularConvolutionCoeff_two_zero (m : ℕ) (f g : ℝ[X]) :
    rectangularConvolutionCoeff m 2 f g 0 = f.coeff 2 * g.coeff 2 := by
  simp [rectangularConvolutionCoeff, rectangularConvolutionGamma_two_zero_zero]

private theorem rectangularConvolutionCoeff_two_one (m : ℕ) (f g : ℝ[X]) :
    rectangularConvolutionCoeff m 2 f g 1 =
      f.coeff 2 * g.coeff 1 + f.coeff 1 * g.coeff 2 := by
  unfold rectangularConvolutionCoeff
  simp [Finset.sum_range_succ, rectangularConvolutionGamma_two_zero_one,
    rectangularConvolutionGamma_two_one_zero]

private theorem rectangularConvolutionCoeff_two_two (m : ℕ) (f g : ℝ[X]) :
    rectangularConvolutionCoeff m 2 f g 2 =
      f.coeff 2 * g.coeff 0 +
        (((m : ℝ) + 1) / (2 * ((m : ℝ) + 2))) * (f.coeff 1 * g.coeff 1) +
          f.coeff 0 * g.coeff 2 := by
  unfold rectangularConvolutionCoeff
  simp [Finset.sum_range_succ, rectangularConvolutionGamma_two_zero_two,
    rectangularConvolutionGamma_two_one_one, rectangularConvolutionGamma_two_two_zero]
  ring

theorem rectangularAdditiveConvolution_zero_right (m : ℕ) (f g : ℝ[X]) :
    rectangularAdditiveConvolution m 0 f g = C (f.coeff 0 * g.coeff 0) := by
  ext j
  rcases j with _ | j
  · simp [rectangularAdditiveConvolution, rectangularConvolutionCoeff,
      rectangularConvolutionGamma]
    have hm : ((Nat.factorial m : ℝ) : ℝ) ≠ 0 := by positivity
    field_simp [hm]
    simp
  · rw [coeff_rectangularAdditiveConvolution_of_gt m 0 f g (by simp), Polynomial.coeff_C]
    simp

theorem rectangularAdditiveConvolution_one (m : ℕ) (f g : ℝ[X]) :
    rectangularAdditiveConvolution m 1 f g =
      C (f.coeff 1 * g.coeff 1) * X +
        C (f.coeff 1 * g.coeff 0 + f.coeff 0 * g.coeff 1) := by
  ext j
  rcases j with _ | j
  · rw [coeff_rectangularAdditiveConvolution_of_le m 1 f g (by norm_num : 0 ≤ 1)]
    simp
  · rcases j with _ | j
    · rw [coeff_rectangularAdditiveConvolution_of_le m 1 f g le_rfl]
      simp
    · rw [coeff_rectangularAdditiveConvolution_of_gt m 1 f g (by lia)]
      simp

theorem rectangularAdditiveConvolution_two (m : ℕ) (f g : ℝ[X]) :
    rectangularAdditiveConvolution m 2 f g =
      C (f.coeff 2 * g.coeff 2) * X ^ 2 +
        C (f.coeff 2 * g.coeff 1 + f.coeff 1 * g.coeff 2) * X +
          C (f.coeff 2 * g.coeff 0 +
            (((m : ℝ) + 1) / (2 * ((m : ℝ) + 2))) * (f.coeff 1 * g.coeff 1) +
              f.coeff 0 * g.coeff 2) := by
  ext j
  rcases j with _ | j
  · rw [coeff_rectangularAdditiveConvolution_of_le m 2 f g (by norm_num : 0 ≤ 2),
      rectangularConvolutionCoeff_two_two]
    simp
  rcases j with _ | j
  · rw [coeff_rectangularAdditiveConvolution_of_le m 2 f g (by norm_num : 1 ≤ 2),
      rectangularConvolutionCoeff_two_one]
    simp only [map_mul, map_add, zero_add, coeff_add, coeff_mul_X, mul_coeff_zero,
      coeff_C_zero, coeff_mul_C, coeff_C_succ, zero_mul, coeff_C_mul, mul_zero,
      add_zero, right_eq_add]
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  rcases j with _ | j
  · rw [coeff_rectangularAdditiveConvolution_of_le m 2 f g le_rfl,
      rectangularConvolutionCoeff_two_zero]
    simp only [map_mul, map_add, zero_add, Nat.reduceAdd, coeff_add, coeff_mul_X,
      coeff_mul_C, coeff_C_succ, zero_mul, add_zero, coeff_C_mul, mul_zero]
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  · rw [coeff_rectangularAdditiveConvolution_of_gt m 2 f g (by lia)]
    simp

/-- Degree-zero base case of the Gribinski--Marcus rectangular convolution
preservation theorem. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots_zero {m : ℕ} {f g : ℝ[X]}
    (_hfdeg : f.natDegree = 0) (_hgdeg : g.natDegree = 0)
    (_hflead : 0 < f.leadingCoeff) (_hglead : 0 < g.leadingCoeff)
    (_hfroots : HasOnlyNonnegRoots f) (_hgroots : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m 0 f g) := by
  rw [rectangularAdditiveConvolution_zero_right]
  right
  refine ⟨by simp, ?_⟩
  intro r hr
  have hroots : (C (f.coeff 0 * g.coeff 0) : ℝ[X]).roots = 0 := Polynomial.roots_C _
  have hroot0 : r ∈ (0 : Multiset ℝ) := hroots ▸ hr
  cases hroot0

/-- Degree-one base case of the Gribinski--Marcus rectangular convolution
preservation theorem. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots_one {m : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = 1) (hgdeg : g.natDegree = 1)
    (hflead : 0 < f.leadingCoeff) (hglead : 0 < g.leadingCoeff)
    (hfroots : HasOnlyNonnegRoots f) (hgroots : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m 1 f g) := by
  rw [rectangularAdditiveConvolution_one]
  have hf1pos : 0 < f.coeff 1 := by
    simpa [Polynomial.leadingCoeff, hfdeg] using hflead
  have hg1pos : 0 < g.coeff 1 := by
    simpa [Polynomial.leadingCoeff, hgdeg] using hglead
  have hf0nonpos : f.coeff 0 ≤ 0 :=
    hfroots.coeff_zero_nonpos_of_natDegree_eq_one hfdeg hflead
  have hg0nonpos : g.coeff 0 ≤ 0 :=
    hgroots.coeff_zero_nonpos_of_natDegree_eq_one hgdeg hglead
  apply hasOnlyNonnegRoots_C_mul_X_add_C_of_pos_nonpos
  · exact mul_pos hf1pos hg1pos
  · exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hf1pos.le hg0nonpos)
      (mul_nonpos_of_nonpos_of_nonneg hf0nonpos hg1pos.le)

private theorem quadratic_data_of_hasOnlyNonnegRoots {p : ℝ[X]}
    (hpdeg : p.natDegree = 2) (hplead : 0 < p.leadingCoeff)
    (hproots : HasOnlyNonnegRoots p) :
    0 < p.coeff 2 ∧ p.coeff 1 ≤ 0 ∧ 0 ≤ p.coeff 0 ∧ p.Splits ∧
      4 * p.coeff 2 * p.coeff 0 ≤ p.coeff 1 ^ 2 := by
  have h2pos : 0 < p.coeff 2 := by
    simpa [Polynomial.leadingCoeff, hpdeg] using hplead
  have hfliproots : HasOnlyNonposRoots (degreeSignFlip 2 p) :=
    hproots.degreeSignFlip_hasOnlyNonposRoots (by rw [hpdeg])
  have hp0 : p ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hplead.ne'
  rcases hproots with hpzero | ⟨hpsplits, _hroots⟩
  · exact (hp0 hpzero).elim
  have hflip0 : degreeSignFlip 2 p ≠ 0 := by
    intro hzero
    have hcoeff : (degreeSignFlip 2 p).coeff 2 = 0 := by simp [hzero]
    rw [coeff_degreeSignFlip_of_le p le_rfl] at hcoeff
    norm_num at hcoeff
    exact h2pos.ne' hcoeff
  rcases hfliproots with hflipzero | ⟨hflipsplits, hflip_roots⟩
  · exact (hflip0 hflipzero).elim
  have hfliplead : HasPosLeadingCoeff (degreeSignFlip 2 p) := by
    rw [HasPosLeadingCoeff, leadingCoeff_degreeSignFlip_of_coeff_ne_zero h2pos.ne']
    exact h2pos
  have hflipnn : HasNonnegCoeffs (degreeSignFlip 2 p) :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hflipsplits).mpr
      ⟨hfliplead, hflip_roots⟩).1
  have h0 : 0 ≤ p.coeff 0 := by
    have hcoeff := hflipnn 0
    rw [coeff_degreeSignFlip_of_le p (by norm_num : 0 ≤ 2)] at hcoeff
    simpa using hcoeff
  have h1 : p.coeff 1 ≤ 0 := by
    have hcoeff := hflipnn 1
    rw [coeff_degreeSignFlip_of_le p (by norm_num : 1 ≤ 2)] at hcoeff
    norm_num at hcoeff
    linarith
  have hpform : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
    Polynomial.eq_quadratic_of_degree_le_two (p := p)
      (Polynomial.degree_le_of_natDegree_le (by rw [hpdeg]))
  have hquad_splits : (C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X +
      C (p.coeff 0) : ℝ[X]).Splits := by
    simpa [← hpform] using hpsplits
  have hdisc : 4 * p.coeff 2 * p.coeff 0 ≤ p.coeff 1 ^ 2 :=
    (quadraticPoly_splits_iff_le h2pos).mp hquad_splits
  exact ⟨h2pos, h1, h0, hpsplits, hdisc⟩

/-- Degree-two base case of the Gribinski--Marcus rectangular convolution
preservation theorem. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots_two
    {m : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 2)
    (hflead : 0 < f.leadingCoeff) (hglead : 0 < g.leadingCoeff)
    (hfroots : HasOnlyNonnegRoots f) (hgroots : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m 2 f g) := by
  rcases quadratic_data_of_hasOnlyNonnegRoots hfdeg hflead hfroots with
    ⟨hf2pos, hf1nonpos, hf0nonneg, _hfsplits, hfdisc⟩
  rcases quadratic_data_of_hasOnlyNonnegRoots hgdeg hglead hgroots with
    ⟨hg2pos, hg1nonpos, hg0nonneg, _hgsplits, hgdisc⟩
  let γ : ℝ := ((m : ℝ) + 1) / (2 * ((m : ℝ) + 2))
  let A : ℝ := f.coeff 2 * g.coeff 2
  let B : ℝ := f.coeff 2 * g.coeff 1 + f.coeff 1 * g.coeff 2
  let D : ℝ := f.coeff 2 * g.coeff 0 + γ * (f.coeff 1 * g.coeff 1) +
    f.coeff 0 * g.coeff 2
  let q := rectangularAdditiveConvolution m 2 f g
  have hqform : q = C A * X ^ 2 + C B * X + C D := by
    dsimp [q, A, B, D, γ]
    exact rectangularAdditiveConvolution_two m f g
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos hf2pos hg2pos
  have hBnonpos : B ≤ 0 := by
    dsimp [B]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hf2pos.le hg1nonpos)
      (mul_nonpos_of_nonpos_of_nonneg hf1nonpos hg2pos.le)
  have hγnonneg : 0 ≤ γ := by
    dsimp [γ]
    positivity
  have hγle : γ ≤ (1 : ℝ) / 2 := by
    dsimp [γ]
    have hden : 0 < 2 * ((m : ℝ) + 2) := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg
      (add_nonneg (mul_nonneg hf2pos.le hg0nonneg)
        (mul_nonneg hγnonneg (mul_nonneg_of_nonpos_of_nonpos hf1nonpos hg1nonpos)))
      (mul_nonneg hf0nonneg hg2pos.le)
  have hfg11_nonneg : 0 ≤ f.coeff 1 * g.coeff 1 :=
    mul_nonneg_of_nonpos_of_nonpos hf1nonpos hg1nonpos
  have hcross_nonneg : 0 ≤ f.coeff 2 * g.coeff 2 * (f.coeff 1 * g.coeff 1) :=
    mul_nonneg (mul_nonneg hf2pos.le hg2pos.le) hfg11_nonneg
  have hfdisc_scaled : 4 * f.coeff 2 * f.coeff 0 * g.coeff 2 ^ 2 ≤
      f.coeff 1 ^ 2 * g.coeff 2 ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hfdisc (sq_nonneg (g.coeff 2))
    nlinarith
  have hgdisc_scaled : 4 * g.coeff 2 * g.coeff 0 * f.coeff 2 ^ 2 ≤
      g.coeff 1 ^ 2 * f.coeff 2 ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hgdisc (sq_nonneg (f.coeff 2))
    nlinarith
  have hcross_scaled : 4 * γ * (f.coeff 2 * g.coeff 2 * (f.coeff 1 * g.coeff 1)) ≤
      2 * (f.coeff 2 * g.coeff 2 * (f.coeff 1 * g.coeff 1)) := by
    have hfactor : 4 * γ ≤ (2 : ℝ) := by nlinarith
    exact mul_le_mul_of_nonneg_right hfactor hcross_nonneg
  have hdisc : 4 * A * D ≤ B ^ 2 := by
    dsimp [A, B, D]
    nlinarith [hfdisc_scaled, hgdisc_scaled, hcross_scaled]
  have hqquad_splits : (C A * X ^ 2 + C B * X + C D : ℝ[X]).Splits :=
    quadraticPoly_splits_of_le hApos hdisc
  have hqsplits : q.Splits := by
    simpa [← hqform] using hqquad_splits
  have hqdeg_le : q.natDegree ≤ 2 := by
    dsimp [q]
    exact natDegree_rectangularAdditiveConvolution_le m 2 f g
  have hqflipform : degreeSignFlip 2 q = C A * X ^ 2 + C (-B) * X + C D := by
    rw [hqform]
    exact degreeSignFlip_two_quadratic A B D
  have hqflipnn : HasNonnegCoeffs (degreeSignFlip 2 q) := by
    rw [hqflipform]
    exact ((nonnegCoeffs_C_mul hApos.le (hasNonnegCoeffs_X.pow 2)).add
      (nonnegCoeffs_C_mul (neg_nonneg.mpr hBnonpos) hasNonnegCoeffs_X)).add
        (hasNonnegCoeffs_C hDnonneg)
  have hqflipsplits : (degreeSignFlip 2 q).Splits :=
    degreeSignFlip_splits_of_splits hqdeg_le hqsplits
  have hflip_roots_nonpos : ∀ r ∈ (degreeSignFlip 2 q).roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hqflipsplits hqflipnn
  right
  refine ⟨hqsplits, ?_⟩
  intro r hr
  have hneg_mem : -r ∈ (degreeSignFlip 2 q).roots := by
    rw [roots_degreeSignFlip hqdeg_le]
    exact Multiset.mem_map.mpr ⟨r, hr, rfl⟩
  have hneg_nonpos : -r ≤ 0 := hflip_roots_nonpos (-r) hneg_mem
  linarith

/-- Factorial form of the generalized Narayana coefficient `N_m(n,k)`.

From `N_m(n,k) = C(n,k) * C(n+m,k) / C(m+k,k)` one gets, for `k ≤ n`,
the paper's Eq. (1.2) form. -/
theorem narayanaTransformCoeff_eq_factorial (m n k : ℕ) (hk : k ≤ n) :
    narayanaTransformCoeff m n k =
      ((Nat.factorial n : ℝ) * (Nat.factorial (n + m) : ℝ) *
          (Nat.factorial m : ℝ)) /
        ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ) *
          (Nat.factorial (m + k) : ℝ) *
          (Nat.factorial (n + m - k) : ℝ)) := by
  have hk2 : k ≤ n + m := hk.trans (Nat.le_add_right n m)
  have h3 : k ≤ m + k := Nat.le_add_left k m
  have e1 : (m + k) - k = m := by lia
  unfold narayanaTransformCoeff
  rw [Nat.cast_choose ℝ hk, Nat.cast_choose ℝ hk2, Nat.cast_choose ℝ h3, e1]
  have f0 : ∀ p : ℕ, (Nat.factorial p : ℝ) ≠ 0 := fun p =>
    Nat.cast_ne_zero.mpr (Nat.factorial_pos p).ne'
  field_simp

/-- Complementary-index symmetry of the generalized Narayana coefficients. -/
theorem narayanaTransformCoeff_symm (m n k : ℕ) (hk : k ≤ n) :
    narayanaTransformCoeff m n k = narayanaTransformCoeff m n (n - k) := by
  rw [narayanaTransformCoeff_eq_factorial m n k hk,
      narayanaTransformCoeff_eq_factorial m n (n - k) (Nat.sub_le n k)]
  have h1 : n - (n - k) = k := by lia
  have h2 : m + (n - k) = n + m - k := by lia
  have h3 : n + m - (n - k) = m + k := by lia
  rw [h1, h2, h3]
  ring

/-- Reversed-index coefficient of the generalized Narayana polynomial. -/
theorem coeff_narayanaPolynomial_sub (m n i : ℕ) (hi : i ≤ n) :
    (narayanaPolynomial m n).coeff (n - i) = narayanaTransformCoeff m n i := by
  rw [coeff_narayanaPolynomial_of_le (Nat.sub_le n i)]
  exact (narayanaTransformCoeff_symm m n i hi).symm

/-- The key coefficient identity from Section 2 of Mao--Wang.  For `i+j ≤ n`,
the rectangular convolution coefficient `γ_{i,j}^{(n,m)}` transports the
generalized Narayana coefficient `N_m(n,j)` to `N_m(n-i,j)`. -/
theorem rectangularConvolutionGamma_mul_narayanaTransformCoeff
    (m n i j : ℕ) (h : i + j ≤ n) :
    rectangularConvolutionGamma m n i j * narayanaTransformCoeff m n j =
      narayanaTransformCoeff m (n - i) j := by
  have hj : j ≤ n := by lia
  have hji : j ≤ n - i := by lia
  have ea : (n - i) + m = n + m - i := by lia
  rw [narayanaTransformCoeff_eq_factorial m n j hj,
      narayanaTransformCoeff_eq_factorial m (n - i) j hji, ea]
  unfold rectangularConvolutionGamma
  have f0 : ∀ p : ℕ, (Nat.factorial p : ℝ) ≠ 0 := fun p =>
    Nat.cast_ne_zero.mpr (Nat.factorial_pos p).ne'
  field_simp

/-- Symmetric companion of
`rectangularConvolutionGamma_mul_narayanaTransformCoeff`. -/
theorem rectangularConvolutionGamma_mul_narayanaTransformCoeff_left
    (m n i j : ℕ) (h : i + j ≤ n) :
    rectangularConvolutionGamma m n i j * narayanaTransformCoeff m n i =
      narayanaTransformCoeff m (n - j) i := by
  rw [rectangularConvolutionGamma_symm]
  exact rectangularConvolutionGamma_mul_narayanaTransformCoeff m n j i (by lia)

/-- Rectangular convolution of two generalized Narayana polynomials, expanded
as the finite coefficient sum before the final Vandermonde evaluation. -/
theorem rectangularConvolutionCoeff_narayanaPolynomial_of_le
    (m n k : ℕ) (hk : k ≤ n) :
    rectangularConvolutionCoeff m n (narayanaPolynomial m n)
        (narayanaPolynomial m n) k =
      ∑ i ∈ Finset.range (k + 1),
        rectangularConvolutionGamma m n i (k - i) *
          narayanaTransformCoeff m n i *
          narayanaTransformCoeff m n (k - i) := by
  unfold rectangularConvolutionCoeff
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hi_n : i ≤ n := hik.trans hk
  have hki_n : k - i ≤ n := (Nat.sub_le k i).trans hk
  rw [coeff_narayanaPolynomial_sub m n i hi_n,
    coeff_narayanaPolynomial_sub m n (k - i) hki_n]

/-- The same convolution sum after transporting one Narayana factor with the
rectangular convolution coefficient.  The remaining closed-form step is a
Vandermonde/Chu summation. -/
theorem rectangularConvolutionCoeff_narayanaPolynomial_eq_sum_transport
    (m n k : ℕ) (hk : k ≤ n) :
    rectangularConvolutionCoeff m n (narayanaPolynomial m n)
        (narayanaPolynomial m n) k =
      ∑ i ∈ Finset.range (k + 1),
        narayanaTransformCoeff m n i *
          narayanaTransformCoeff m (n - i) (k - i) := by
  rw [rectangularConvolutionCoeff_narayanaPolynomial_of_le m n k hk]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsum : i + (k - i) ≤ n := by
    rw [Nat.add_sub_of_le hik]
    exact hk
  rw [← rectangularConvolutionGamma_mul_narayanaTransformCoeff m n i (k - i) hsum]
  ring

/-- Vandermonde variant used in the Mao--Wang Section 2 coefficient bridge.
Summing the shifted product of binomials over `Finset.range (k + 1)` collapses
to a single binomial coefficient. -/
theorem sum_choose_mul_choose_shift (m k : ℕ) :
    ∑ i ∈ Finset.range (k + 1),
        Nat.choose k i * Nat.choose (2 * m + k) (m + i) =
      Nat.choose (2 * m + 2 * k) (m + k) := by
  have h1 : Nat.choose (2 * m + 2 * k) (m + k) =
      ∑ i ∈ Finset.range (m + k + 1),
        Nat.choose k i * Nat.choose (2 * m + k) (m + k - i) := by
    rw [show 2 * m + 2 * k = k + (2 * m + k) by ring, Nat.add_choose_eq]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      fun i j => Nat.choose k i * Nat.choose (2 * m + k) j]
  rw [h1, ← Finset.sum_subset (Finset.range_mono (by lia : k + 1 ≤ m + k + 1))]
  · rw [← Finset.sum_flip]
    exact Finset.sum_congr rfl fun x hx => by
      rw [Nat.choose_symm (Finset.mem_range_succ_iff.mp hx),
        Nat.add_sub_assoc (Finset.mem_range_succ_iff.mp hx)]
  · intro x _ hx
    have hx' : k < x :=
      Nat.lt_of_succ_le (Nat.le_of_not_gt (by simpa [Finset.mem_range] using hx))
    rw [Nat.choose_eq_zero_of_lt hx']
    ring

/-- Reciprocal-factorial form of the Chu--Vandermonde summation appearing in
the Mao--Wang Section 2 coefficient bridge. -/
theorem sum_factorial_recip_eq (m k : ℕ) :
    ∑ i ∈ Finset.range (k + 1),
        (1 : ℝ) /
          ((Nat.factorial i : ℝ) * (Nat.factorial (m + i) : ℝ) *
            (Nat.factorial (k - i) : ℝ) *
            (Nat.factorial (m + k - i) : ℝ)) =
      (Nat.factorial (2 * m + 2 * k) : ℝ) /
        ((Nat.factorial k : ℝ) * (Nat.factorial (m + k) : ℝ) ^ 2 *
          (Nat.factorial (2 * m + k) : ℝ)) := by
  have h_binom : (∑ i ∈ Finset.range (k + 1),
        (1 : ℝ) /
          ((Nat.factorial i : ℝ) * (Nat.factorial (m + i) : ℝ) *
            (Nat.factorial (k - i) : ℝ) *
            (Nat.factorial (m + k - i) : ℝ))) =
      ∑ i ∈ Finset.range (k + 1),
        ((Nat.choose k i : ℝ) * (Nat.choose (2 * m + k) (m + i) : ℝ)) /
          ((Nat.factorial k : ℝ) * (Nat.factorial (2 * m + k) : ℝ)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hmi : m + i ≤ 2 * m + k := by lia
    rw [Nat.cast_choose ℝ hik, Nat.cast_choose ℝ hmi]
    field_simp
    rw [show 2 * m + k - (m + i) = m + k - i by lia]
  convert h_binom using 1
  convert congr_arg
      (fun x : ℕ =>
        (x : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (2 * m + k) : ℝ)))
      (sum_choose_mul_choose_shift m k) using 1
  · rw [sum_choose_mul_choose_shift, Nat.cast_choose]
    · rw [show 2 * m + 2 * k - (m + k) = m + k by
        rw [Nat.sub_eq_of_eq_add]
        ring]
      ring
    · lia
  · convert congr_arg
        (fun x : ℕ =>
          (x : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (2 * m + k) : ℝ)))
        (sum_choose_mul_choose_shift m k) using 1
    norm_num [Finset.sum_div]

/-- Short name for the transported Narayana rectangular-convolution coefficient
sum used in the Mao--Wang Section 2 bridge. -/
theorem rectangularConvolutionCoeff_narayana_eq_sum
    (m n k : ℕ) (hk : k ≤ n) :
    rectangularConvolutionCoeff m n (narayanaPolynomial m n)
        (narayanaPolynomial m n) k =
      ∑ i ∈ Finset.range (k + 1),
        narayanaTransformCoeff m n i *
          narayanaTransformCoeff m (n - i) (k - i) :=
  rectangularConvolutionCoeff_narayanaPolynomial_eq_sum_transport m n k hk

/-- Each summand of the Chu--Vandermonde sum factors as a constant independent
of `i` times a reciprocal-factorial term. -/
theorem narayana_product_term_eq (m n k i : ℕ) (hk : k ≤ n) (hi : i ≤ k) :
    narayanaTransformCoeff m n i * narayanaTransformCoeff m (n - i) (k - i) =
      ((Nat.factorial n : ℝ) * (Nat.factorial (n + m) : ℝ) *
          (Nat.factorial m : ℝ) ^ 2 /
            ((Nat.factorial (n - k) : ℝ) *
              (Nat.factorial (n + m - k) : ℝ))) *
        ((1 : ℝ) /
          ((Nat.factorial i : ℝ) * (Nat.factorial (m + i) : ℝ) *
            (Nat.factorial (k - i) : ℝ) *
            (Nat.factorial (m + k - i) : ℝ))) := by
  have h_geometric :
      narayanaTransformCoeff m n i * narayanaTransformCoeff m (n - i) (k - i) =
        ((Nat.factorial n : ℝ) * (Nat.factorial (n + m) : ℝ) *
            (Nat.factorial m : ℝ) /
          ((Nat.factorial i : ℝ) * (Nat.factorial (n - i) : ℝ) *
            (Nat.factorial (m + i) : ℝ) *
            (Nat.factorial (n + m - i) : ℝ))) *
        ((Nat.factorial (n - i) : ℝ) * (Nat.factorial (n + m - i) : ℝ) *
            (Nat.factorial m : ℝ) /
          ((Nat.factorial (k - i) : ℝ) * (Nat.factorial (n - k) : ℝ) *
            (Nat.factorial (m + k - i) : ℝ) *
            (Nat.factorial (n + m - k) : ℝ))) := by
    convert congr_arg₂ (· * ·)
      (narayanaTransformCoeff_eq_factorial m n i (hi.trans hk))
      (narayanaTransformCoeff_eq_factorial m (n - i) (k - i) (by lia)) using 2
    rw [show n + m - i = n - i + m by lia,
      show n - i - (k - i) = n - k by lia,
      show m + (k - i) = m + k - i by lia,
      show n - i + m - (k - i) = n + m - k by lia]
  rw [h_geometric]
  have f0 : ∀ p : ℕ, (Nat.factorial p : ℝ) ≠ 0 := fun p =>
    Nat.cast_ne_zero.mpr (Nat.factorial_pos p).ne'
  field_simp [f0]

/-- Mao--Wang Section 2 coefficient bridge: closed form for the rectangular
convolution coefficient of a generalized Narayana polynomial with itself. -/
theorem coeff_rectangularConvolution_narayana (m n k : ℕ) (hk : k ≤ n) :
    rectangularConvolutionCoeff m n (narayanaPolynomial m n)
        (narayanaPolynomial m n) k =
      narayanaTransformCoeff m n k *
        ((Nat.factorial m : ℝ) * (Nat.factorial (2 * m + 2 * k) : ℝ) /
          ((Nat.factorial (2 * m + k) : ℝ) *
            (Nat.factorial (m + k) : ℝ))) := by
  convert rectangularConvolutionCoeff_narayana_eq_sum m n k hk using 1
  rw [Finset.sum_congr rfl
    fun i hi => narayana_product_term_eq m n k i hk
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  rw [← Finset.mul_sum _ _ _, sum_factorial_recip_eq]
  rw [narayanaTransformCoeff_eq_factorial m n k hk]
  ring

/-- Coefficients of the rectangular additive convolution of two generalized
Narayana polynomials, reduced to the transported convolution sum. -/
theorem coeff_rectangularAdditiveConvolution_narayanaPolynomial_of_le
    (m n j : ℕ) (hj : j ≤ n) :
    (rectangularAdditiveConvolution m n (narayanaPolynomial m n)
        (narayanaPolynomial m n)).coeff j =
      ∑ i ∈ Finset.range (n - j + 1),
        narayanaTransformCoeff m n i *
          narayanaTransformCoeff m (n - i) (n - j - i) := by
  rw [coeff_rectangularAdditiveConvolution_of_le m n (narayanaPolynomial m n)
      (narayanaPolynomial m n) hj,
    rectangularConvolutionCoeff_narayanaPolynomial_eq_sum_transport m n (n - j)
      (Nat.sub_le n j)]

/-- Rectangular-convolution coefficient after applying the degree-`n` sign flip
to an arbitrary input and to `N_{n,m}`. -/
theorem coeff_rectangularAdditiveConvolution_degreeSignFlip_narayanaPolynomial_of_le
    (m n j : ℕ) (p : ℝ[X]) (hj : j ≤ n) :
    (rectangularAdditiveConvolution m n (degreeSignFlip n p)
        (degreeSignFlip n (narayanaPolynomial m n))).coeff j =
      (-1 : ℝ) ^ (n - j) *
        ∑ i ∈ Finset.range (n - j + 1),
          p.coeff (n - i) * narayanaTransformCoeff m (n - i) j := by
  rw [coeff_rectangularAdditiveConvolution_of_le m n (degreeSignFlip n p)
    (degreeSignFlip n (narayanaPolynomial m n)) hj]
  unfold rectangularConvolutionCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hki_n : n - j - i ≤ n := by lia
  have hsum : i + (n - j - i) ≤ n := by
    rw [Nat.add_sub_of_le hik]
    exact Nat.sub_le n j
  have hsign :
      (-1 : ℝ) ^ i * (-1 : ℝ) ^ (n - j - i) = (-1 : ℝ) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hik]
  have hgamma :
      rectangularConvolutionGamma m n i (n - j - i) *
          narayanaTransformCoeff m n (n - j - i) =
        narayanaTransformCoeff m (n - i) j := by
    rw [rectangularConvolutionGamma_mul_narayanaTransformCoeff m n i
      (n - j - i) hsum]
    have hsym := narayanaTransformCoeff_symm m (n - i) (n - j - i) (by lia)
    rwa [show n - i - (n - j - i) = j by lia] at hsym
  rw [coeff_degreeSignFlip_of_le p (by lia : n - i ≤ n),
    coeff_degreeSignFlip_of_le (narayanaPolynomial m n)
      (by lia : n - (n - j - i) ≤ n)]
  rw [show n - (n - i) = i by lia,
    show n - (n - (n - j - i)) = n - j - i by lia]
  rw [coeff_narayanaPolynomial_sub m n (n - j - i) hki_n]
  calc
    rectangularConvolutionGamma m n i (n - j - i) *
          ((-1 : ℝ) ^ i * p.coeff (n - i)) *
        ((-1 : ℝ) ^ (n - j - i) * narayanaTransformCoeff m n (n - j - i)) =
        ((-1 : ℝ) ^ i * (-1 : ℝ) ^ (n - j - i)) *
          p.coeff (n - i) *
            (rectangularConvolutionGamma m n i (n - j - i) *
              narayanaTransformCoeff m n (n - j - i)) := by
      ring
    _ = (-1 : ℝ) ^ (n - j) *
        (p.coeff (n - i) * narayanaTransformCoeff m (n - i) j) := by
      rw [hsign, hgamma]
      ring

/-- Mao--Wang's coefficient comparison: rectangular convolution of the
degree-`n` sign flips of `p` and `N_{n,m}` is the degree-`n` sign flip of the
Narayana transform of `p`. -/
theorem rectangularAdditiveConvolution_degreeSignFlip_narayanaPolynomial_eq
    (m n : ℕ) (p : ℝ[X]) (hpdeg : p.natDegree ≤ n) :
    rectangularAdditiveConvolution m n (degreeSignFlip n p)
        (degreeSignFlip n (narayanaPolynomial m n)) =
      degreeSignFlip n (narayanaTransform m p) := by
  ext j
  by_cases hj : j ≤ n
  · rw [coeff_rectangularAdditiveConvolution_degreeSignFlip_narayanaPolynomial_of_le
      m n j p hj]
    rw [coeff_degreeSignFlip_narayanaTransform_of_le m n p hj,
      narayanaTransform_coeff_sum_reflect m n j p hpdeg hj]
  · have hjlt : n < j := Nat.lt_of_not_ge hj
    rw [coeff_rectangularAdditiveConvolution_of_gt m n (degreeSignFlip n p)
        (degreeSignFlip n (narayanaPolynomial m n)) hjlt,
      coeff_degreeSignFlip_of_lt (narayanaTransform m p) hjlt]

/-- Gribinski--Marcus preservation theorem in the form used by Mao--Wang,
paper Lemma 2.6. -/
abbrev rectangularAdditiveConvolutionPreservesNonnegRootsStatement : Prop :=
  ∀ {m n : ℕ} {f g : ℝ[X]},
    f.natDegree = n →
    g.natDegree = n →
    0 < f.leadingCoeff →
    0 < g.leadingCoeff →
    HasOnlyNonnegRoots f →
    HasOnlyNonnegRoots g →
      HasOnlyNonnegRoots (rectangularAdditiveConvolution m n f g)

/-- Positive-degree leaf of the Gribinski--Marcus preservation theorem. The
degree-zero base case is checked separately. -/
abbrev rectangularAdditiveConvolutionPreservesNonnegRootsPositiveDegreeStatement : Prop :=
  ∀ {m n : ℕ} {f g : ℝ[X]},
    f.natDegree = n + 1 →
    g.natDegree = n + 1 →
    0 < f.leadingCoeff →
    0 < g.leadingCoeff →
    HasOnlyNonnegRoots f →
    HasOnlyNonnegRoots g →
      HasOnlyNonnegRoots (rectangularAdditiveConvolution m (n + 1) f g)

/-- Degree-at-least-three leaf of the Gribinski--Marcus preservation theorem.
The degree-zero, degree-one, and degree-two base cases are checked separately. -/
abbrev rectangularAdditiveConvolutionPreservesNonnegRootsDegreeAtLeastThreeStatement : Prop :=
  ∀ {m n : ℕ} {f g : ℝ[X]},
    f.natDegree = n + 1 + 1 + 1 →
    g.natDegree = n + 1 + 1 + 1 →
    0 < f.leadingCoeff →
    0 < g.leadingCoeff →
    HasOnlyNonnegRoots f →
    HasOnlyNonnegRoots g →
      HasOnlyNonnegRoots (rectangularAdditiveConvolution m (n + 1 + 1 + 1) f g)

/-- Degree-at-least-three case of the Gribinski--Marcus preservation theorem for
rectangular additive convolution. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots_degreeAtLeastThree
    {m n : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = n + 1 + 1 + 1) (hgdeg : g.natDegree = n + 1 + 1 + 1)
    (hflead : 0 < f.leadingCoeff) (hglead : 0 < g.leadingCoeff)
    (hfroots : HasOnlyNonnegRoots f) (hgroots : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m (n + 1 + 1 + 1) f g) := by
  sorry

/-- Degree-at-least-two case of the Gribinski--Marcus preservation theorem for
rectangular additive convolution. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots_degreeAtLeastTwo
    {m n : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = n + 1 + 1) (hgdeg : g.natDegree = n + 1 + 1)
    (hflead : 0 < f.leadingCoeff) (hglead : 0 < g.leadingCoeff)
    (hfroots : HasOnlyNonnegRoots f) (hgroots : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m (n + 1 + 1) f g) := by
  rcases n with _ | n
  · exact rectangularAdditiveConvolutionPreservesNonnegRoots_two
      hfdeg hgdeg hflead hglead hfroots hgroots
  · exact rectangularAdditiveConvolutionPreservesNonnegRoots_degreeAtLeastThree
      hfdeg hgdeg hflead hglead hfroots hgroots

/-- Positive-degree case of the Gribinski--Marcus preservation theorem for
rectangular additive convolution. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots_positiveDegree
    {m n : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = n + 1) (hgdeg : g.natDegree = n + 1)
    (hflead : 0 < f.leadingCoeff) (hglead : 0 < g.leadingCoeff)
    (hfroots : HasOnlyNonnegRoots f) (hgroots : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m (n + 1) f g) := by
  rcases n with _ | n
  · exact rectangularAdditiveConvolutionPreservesNonnegRoots_one
      hfdeg hgdeg hflead hglead hfroots hgroots
  · exact rectangularAdditiveConvolutionPreservesNonnegRoots_degreeAtLeastTwo
      hfdeg hgdeg hflead hglead hfroots hgroots

/-- Gribinski--Marcus preservation theorem for rectangular additive convolution. -/
theorem rectangularAdditiveConvolutionPreservesNonnegRoots {m n : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hflead : 0 < f.leadingCoeff) (hglead : 0 < g.leadingCoeff)
    (hfroots : HasOnlyNonnegRoots f) (hgroots : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m n f g) := by
  rcases n with _ | n
  · exact rectangularAdditiveConvolutionPreservesNonnegRoots_zero
      hfdeg hgdeg hflead hglead hfroots hgroots
  · exact rectangularAdditiveConvolutionPreservesNonnegRoots_positiveDegree
      hfdeg hgdeg hflead hglead hfroots hgroots

@[simp] theorem narayanaPolynomial_zero_right (m : ℕ) :
    narayanaPolynomial m 0 = 1 := by
  simp [narayanaPolynomial]

@[simp] theorem narayanaTransformCoeff_self (m n : ℕ) :
    narayanaTransformCoeff m n n = 1 := by
  dsimp [narayanaTransformCoeff]
  have : ((m + n).choose n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_left n m)).ne'
  simp [this, add_comm n m]

theorem narayanaPolynomial_one (m : ℕ) :
    narayanaPolynomial m 1 = X + C 1 := by
  ext k
  simp only [coeff_add, coeff_X, coeff_C]
  rcases k with _ | _ | _ <;> simp

theorem narayanaPolynomial_two (m : ℕ) :
    narayanaPolynomial m 2 = X ^ 2 + C (2 * ((m : ℝ) + 2) / ((m : ℝ) + 1)) * X + C 1 := by
  ext k
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  rcases k with _ | _ | _ | _
  · simp
  · simp [narayanaTransformCoeff]
    ring
  · simp
  · simp

theorem natDegree_narayanaPolynomial (m n : ℕ) :
    (narayanaPolynomial m n).natDegree = n := by
  have : (narayanaPolynomial m n).coeff n ≠ 0 := by simp
  exact le_antisymm (natDegree_narayanaPolynomial_le m n) (le_natDegree_of_ne_zero this)

theorem leadingCoeff_narayanaPolynomial (m n : ℕ) :
    (narayanaPolynomial m n).leadingCoeff = 1 := by
  simp [leadingCoeff, natDegree_narayanaPolynomial]

theorem narayanaPolynomial_ne_zero (m n : ℕ) :
    narayanaPolynomial m n ≠ 0 := by
  simp [← leadingCoeff_ne_zero, leadingCoeff_narayanaPolynomial]

theorem hasPosLeadingCoeff_narayanaPolynomial (m n : ℕ) :
    HasPosLeadingCoeff (narayanaPolynomial m n) := by
  simp [HasPosLeadingCoeff, leadingCoeff_narayanaPolynomial]

theorem narayanaPolynomial_eval_pos_of_nonneg {x : ℝ} (hx : 0 ≤ x) (m n : ℕ) :
    0 < (narayanaPolynomial m n).eval x := by
  dsimp [narayanaPolynomial]
  rw [eval_finsetSum, ← sum_erase_add _ _ (mem_range.mpr (Nat.succ_pos n))]
  refine add_pos_of_nonneg_of_pos (sum_nonneg fun k _ => ?_) ?_
  · simp only [eval_mul, eval_C, eval_pow, eval_X]
    exact mul_nonneg (narayanaTransformCoeff_nonneg m n k) (pow_nonneg hx k)
  · simp

theorem narayanaPolynomial_eval_one_pos (m n : ℕ) :
    0 < (narayanaPolynomial m n).eval 1 :=
  narayanaPolynomial_eval_pos_of_nonneg zero_le_one m n

theorem narayanaPolynomial_root_nonpos {m n : ℕ} {r : ℝ}
    (hr : (narayanaPolynomial m n).IsRoot r) : r ≤ 0 := by
  by_contra h
  exact (narayanaPolynomial_eval_pos_of_nonneg (not_le.mp h).le m n).ne' hr

private theorem factorial_cast_ne_zero (n : ℕ) :
    (n.factorial : ℝ) ≠ 0 := by
  positivity

lemma factorial_succ_cast (n : ℕ) :
    ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
  rw [Nat.factorial_succ n]
  push_cast
  rfl

lemma factorial_succ_succ_cast (n : ℕ) :
    ((n + 2).factorial : ℝ) = (n + 2) * (n + 1) * n.factorial := by
  rw [Nat.factorial_succ (n + 1), Nat.factorial_succ n]
  push_cast
  ring

lemma factorial_cast_pred {n : ℕ} (hn : n ≠ 0) :
    (n.factorial : ℝ) = n * (n - 1).factorial := by
  have h : n = n - 1 + 1 := by lia
  nth_rw 1 [h]
  rw [Nat.factorial_succ]
  push_cast
  rw [h]
  push_cast
  rfl

private lemma deriv_lag_poly_identity (n m k : ℝ) :
    (n + 2 * m + 2) * (n + 2) * (n + 2 + m) =
      (n + 2 * m + 2 + 2 * k) * (n + 2 - k) * (n + 2 + m - k) +
        (3 * n + 2 * m + 6 - 2 * k) * k * (m + k) := by
  ring

private lemma pure_poly_identity (n m k : ℝ) :
    (n + 2 * m + 2) * (n + 2) * (n + 1) * (n + 2 + m) * (n + 1 + m) =
      (2 * n + 2 * m + 3) * ((n + 1) * (n + 1 + m) * (n + 2 - k) * (n + 2 + m - k) +
        (n + 1) * (n + 1 + m) * k * (m + k)) -
        (n + 1) * ((n + 2 - k) * (n + 1 - k) * (n + 2 + m - k) * (n + 1 + m - k) -
          2 * (n + 2 - k) * (n + 2 + m - k) * k * (m + k) +
          k * (k - 1) * (m + k) * (m + k - 1)) := by
  ring

lemma narayanaTransformCoeff_deriv_lag_rec (m n k : ℕ) (hkpos : k ≠ 0) (hk : k ≤ n + 1) :
    ((n : ℝ) + 2 * m + 2) * narayanaTransformCoeff m (n + 2) k =
      ((n : ℝ) + 2 * m + 2 + 2 * k) * narayanaTransformCoeff m (n + 1) k +
        ((3 * n : ℝ) + 2 * m + 6 - 2 * k) *
          narayanaTransformCoeff m (n + 1) (k - 1) := by
  let F : ℝ := (Nat.factorial (n + 1) : ℝ) * Nat.factorial (n + 1 + m) * Nat.factorial m /
    ((Nat.factorial (n + 2 - k) : ℝ) * Nat.factorial (n + 2 + m - k) * Nat.factorial k *
      Nat.factorial (m + k))
  have hF_eq₁ : (narayanaTransformCoeff m (n + 2) k : ℝ) = ((n : ℝ) + 2) * (n + 2 + m) * F := by
    rw [narayanaTransformCoeff_eq_factorial m (n + 2) k (by lia)]
    dsimp only [F]
    rw [show n + 1 + m = n + m + 1 by ring]
    field_simp [factorial_cast_ne_zero]
    rw [factorial_succ_cast (n + 1), show n + 2 + m = n + m + 1 + 1 by ring,
      factorial_succ_cast (n + m + 1)]
    push_cast
    ring
  have hF_eq₂ : (narayanaTransformCoeff m (n + 1) k : ℝ) =
    ((n : ℝ) + 2 - k) * (n + 2 + m - k) * F := by
    rw [narayanaTransformCoeff_eq_factorial m (n + 1) k hk]
    dsimp only [F]
    field_simp [factorial_cast_ne_zero]
    rw [show n + 2 - k = (n + 1 - k) + 1 by lia, factorial_succ_cast (n + 1 - k)]
    rw [show n + 2 + m - k = (n + 1 + m - k) + 1 by lia, factorial_succ_cast (n + 1 + m - k)]
    rw [Nat.cast_sub hk, Nat.cast_sub (by lia : k ≤ n + 1 + m)]
    push_cast
    ring
  have hF_eq₃ : (narayanaTransformCoeff m (n + 1) (k - 1) : ℝ) = (k : ℝ) * (m + k) * F := by
    have h₆ : m + (k - 1) = m + k - 1 := by lia
    rw [narayanaTransformCoeff_eq_factorial m (n + 1) (k - 1) (by lia)]
    dsimp only [F]
    have h₄ : n + 1 - (k - 1) = n + 2 - k := by lia
    have h₅ : n + 1 + m - (k - 1) = n + 2 + m - k := by lia
    rw [h₄, h₅, h₆]
    field_simp [factorial_cast_ne_zero]
    rw [factorial_cast_pred hkpos, factorial_cast_pred (by lia : m + k ≠ 0)]
    push_cast
    ring
  rw [hF_eq₁, hF_eq₂, hF_eq₃]
  have h_poly := deriv_lag_poly_identity (n : ℝ) (m : ℝ) (k : ℝ)
  rw [show ((n : ℝ) + 2 * m + 2) * (((n : ℝ) + 2) * (n + 2 + m) * F) =
    ((n : ℝ) + 2 * m + 2) * (n + 2) * (n + 2 + m) * F by ring]
  rw [show ((n : ℝ) + 2 * m + 2 + 2 * k) * (((n : ℝ) + 2 - k) * (n + 2 + m - k) * F) +
    ((3 * n : ℝ) + 2 * m + 6 - 2 * k) * ((k : ℝ) * (m + k) * F) =
    (((n : ℝ) + 2 * m + 2 + 2 * k) * (n + 2 - k) * (n + 2 + m - k) +
      ((3 * n : ℝ) + 2 * m + 6 - 2 * k) * k * (m + k)) * F by ring]
  rw [h_poly]

theorem coeff_narayanaPolynomial_deriv_lag_rec (m n k : ℕ) (hkpos : k ≠ 0) :
    ((n : ℝ) + 2 * m + 2) * (narayanaPolynomial m (n + 2)).coeff k =
      ((n : ℝ) + 2 * m + 2 + 2 * k) * (narayanaPolynomial m (n + 1)).coeff k +
        ((3 * n : ℝ) + 2 * m + 6 - 2 * k) *
          (narayanaPolynomial m (n + 1)).coeff (k - 1) := by
  rcases le_or_gt k (n + 2) with hk | hk
  · rw [coeff_narayanaPolynomial_of_le hk]
    have : k - 1 ≤ n + 1 := by lia
    rcases le_or_gt k (n + 1) with hk | hk
    · rw [coeff_narayanaPolynomial_of_le hk, coeff_narayanaPolynomial_of_le this]
      exact narayanaTransformCoeff_deriv_lag_rec m n k hkpos hk
    · obtain rfl : k = n + 2 := by lia
      change _ = _ + _ * (narayanaPolynomial m (n + 1)).coeff (n + 1)
      rw [narayanaTransformCoeff_self,
        coeff_narayanaPolynomial_of_lt (Nat.lt_succ_self (n + 1)),
        coeff_narayanaPolynomial_of_le le_rfl, narayanaTransformCoeff_self]
      push_cast
      ring
  · rw [coeff_narayanaPolynomial_of_lt hk,
      coeff_narayanaPolynomial_of_lt (by lia : n + 1 < k),
      coeff_narayanaPolynomial_of_lt (by lia : n + 1 < k - 1)]
    ring

theorem narayanaPolynomial_deriv_lag_rec (m n : ℕ) :
    C ((n : ℝ) + 2 * m + 2) * narayanaPolynomial m (n + 2) =
      (C ((n : ℝ) + 2 * m + 2) + C ((3 * n : ℝ) + 2 * m + 4) * X) *
          narayanaPolynomial m (n + 1) +
        (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2) *
          (narayanaPolynomial m (n + 1)).derivative := by
  ext k
  rw [add_mul, sub_mul, mul_assoc, mul_assoc]
  rcases k with _ | _ | k
  · simp
  · rw [coeff_C_mul, coeff_narayanaPolynomial_deriv_lag_rec m n 1 one_ne_zero]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative, sq,
      mul_assoc, coeff_X_mul_zero]
    ring
  · rw [coeff_C_mul, coeff_narayanaPolynomial_deriv_lag_rec m n (k + 2) (by lia)]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative, sq,
      mul_assoc]
    push_cast
    ring

lemma narayanaTransformCoeff_pure_rec (m n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    ((n : ℝ) + 2 * m + 2) * narayanaTransformCoeff m (n + 2) k =
      ((2 * n : ℝ) + 2 * m + 3) *
          (narayanaTransformCoeff m (n + 1) k +
            narayanaTransformCoeff m (n + 1) (k - 1)) -
        ((n : ℝ) + 1) *
          (narayanaTransformCoeff m n k -
            2 * narayanaTransformCoeff m n (k - 1) +
            narayanaTransformCoeff m n (k - 2)) := by
  let G : ℝ := (Nat.factorial n : ℝ) * Nat.factorial (n + m) * Nat.factorial m /
    ((Nat.factorial (n + 2 - k) : ℝ) * Nat.factorial (n + 2 + m - k) * Nat.factorial k *
      Nat.factorial (m + k))
  have hG₁ : (narayanaTransformCoeff m (n + 2) k : ℝ) =
      ((n : ℝ) + 2) * (n + 1) * (n + 2 + m) * (n + 1 + m) * G := by
    rw [narayanaTransformCoeff_eq_factorial m (n + 2) k (by lia)]
    have h₁ := factorial_succ_succ_cast n
    have h₂ : ((n + 2 + m).factorial : ℝ) = (n + 2 + m) * (n + 1 + m) * (n + m).factorial := by
      rw [show n + 2 + m = n + m + 2 by ring, factorial_succ_succ_cast]
      push_cast
      ring
    dsimp only [G]
    field_simp [factorial_cast_ne_zero]
    rw [h₁, h₂]
    ring
  have hG₂ : (narayanaTransformCoeff m (n + 1) k : ℝ) =
      ((n : ℝ) + 1) * (n + 1 + m) * (n + 2 - k) * (n + 2 + m - k) * G := by
    rw [narayanaTransformCoeff_eq_factorial m (n + 1) k (by lia)]
    have h₁ := factorial_succ_cast n
    have h₂ : ((n + 1 + m).factorial : ℝ) = (n + 1 + m) * (n + m).factorial := by
      rw [show n + 1 + m = n + m + 1 by ring, factorial_succ_cast (n + m)]
      push_cast
      ring
    have h₃ : ((n + 2 - k).factorial : ℝ) = ((n : ℝ) + 2 - k) * (n + 1 - k).factorial := by
      rw [show n + 2 - k = (n + 1 - k) + 1 by lia, factorial_succ_cast (n + 1 - k),
        Nat.cast_sub (by lia : k ≤ n + 1)]
      push_cast
      ring
    have h₄ : ((n + 2 + m - k).factorial : ℝ) =
      ((n : ℝ) + 2 + m - k) * (n + 1 + m - k).factorial := by
      rw [show n + 2 + m - k = (n + 1 + m - k) + 1 by lia, factorial_succ_cast (n + 1 + m - k),
        Nat.cast_sub (by lia : k ≤ n + 1 + m)]
      push_cast
      ring
    dsimp only [G]
    field_simp [factorial_cast_ne_zero]
    rw [h₁, h₂, h₃, h₄]
    ring
  have hG₃ : (narayanaTransformCoeff m (n + 1) (k - 1) : ℝ) =
      ((n : ℝ) + 1) * (n + 1 + m) * (k : ℝ) * (m + k) * G := by
    rw [narayanaTransformCoeff_eq_factorial m (n + 1) (k - 1) (by lia)]
    have h₁ := factorial_succ_cast n
    have h₂ : ((n + 1 + m).factorial : ℝ) = (n + 1 + m) * (n + m).factorial := by
      rw [show n + 1 + m = n + m + 1 by ring, factorial_succ_cast (n + m)]
      push_cast
      ring
    have h₃ := factorial_cast_pred (by lia : k ≠ 0)
    have h₄ := factorial_cast_pred (by lia : m + k ≠ 0)
    dsimp only [G]
    have h₅ : n + 1 - (k - 1) = n + 2 - k := by lia
    have h₆ : n + 1 + m - (k - 1) = n + 2 + m - k := by lia
    have h₇ : m + k - 1 = m + (k - 1) := by lia
    field_simp [factorial_cast_ne_zero]
    rw [h₅, h₆, h₁, h₂, h₃, h₄, h₇]
    push_cast
    ring
  have hG₄ : (narayanaTransformCoeff m n k : ℝ) =
      ((n : ℝ) + 2 - k) * (n + 1 - k) * (n + 2 + m - k) * (n + 1 + m - k) * G := by
    rw [narayanaTransformCoeff_eq_factorial m n k hkn]
    have h₁ : ((n + 2 - k).factorial : ℝ) =
      ((n : ℝ) + 2 - k) * ((n : ℝ) + 1 - k) * (n - k).factorial := by
      rw [show n + 2 - k = (n - k) + 2 by lia, factorial_succ_succ_cast (n - k), Nat.cast_sub hkn]
      ring
    have h₂ : ((n + 2 + m - k).factorial : ℝ) =
      ((n : ℝ) + 2 + m - k) * ((n : ℝ) + 1 + m - k) * (n + m - k).factorial := by
      rw [show n + 2 + m - k = (n + m - k) + 2 by lia, factorial_succ_succ_cast (n + m - k),
        Nat.cast_sub (by lia : k ≤ n + m), Nat.cast_add]
      ring
    dsimp only [G]
    field_simp [factorial_cast_ne_zero]
    rw [h₁, h₂]
    ring
  have hG₅ : (narayanaTransformCoeff m n (k - 1) : ℝ) =
      ((n : ℝ) + 2 - k) * (n + 2 + m - k) * (k : ℝ) * (m + k) * G := by
    rw [narayanaTransformCoeff_eq_factorial m n (k - 1) (by lia)]
    have h₁ : ((n + 2 - k).factorial : ℝ) =
      ((n : ℝ) + 2 - k) * (n + 1 - k).factorial := by
      rw [show n + 2 - k = (n + 1 - k) + 1 by lia, factorial_succ_cast (n + 1 - k),
        Nat.cast_sub (by lia : k ≤ n + 1)]
      push_cast
      ring
    have h₂ : ((n + 2 + m - k).factorial : ℝ) =
      ((n : ℝ) + 2 + m - k) * (n + 1 + m - k).factorial := by
      rw [show n + 2 + m - k = (n + 1 + m - k) + 1 by lia, factorial_succ_cast (n + 1 + m - k),
        Nat.cast_sub (by lia : k ≤ n + 1 + m)]
      push_cast
      ring
    have h₃ := factorial_cast_pred (by lia : k ≠ 0)
    have h₄ := factorial_cast_pred (by lia : m + k ≠ 0)
    dsimp only [G]
    have h₅ : n - (k - 1) = n + 1 - k := by lia
    have h₆ : n + m - (k - 1) = n + 1 + m - k := by lia
    have h₇ : m + k - 1 = m + (k - 1) := by lia
    field_simp [factorial_cast_ne_zero]
    rw [h₅, h₆, h₁, h₂, h₃, h₄, h₇]
    push_cast
    ring
  have hG₆ : (narayanaTransformCoeff m n (k - 2) : ℝ) =
      (k : ℝ) * (k - 1) * (m + k) * (m + k - 1) * G := by
    rw [narayanaTransformCoeff_eq_factorial m n (k - 2) (by lia)]
    have h₁ : (k.factorial : ℝ) = k * (k - 1) * (k - 2).factorial := by
      conv_lhs => rw [show k = (k - 2) + 2 by lia]
      rw [factorial_succ_succ_cast]
      rw [Nat.cast_sub hk]
      ring
    have h₂ : ((m + k).factorial : ℝ) =
      (m + k) * (m + k - 1) * (m + (k - 2)).factorial := by
      conv_lhs => rw [show m + k = m + (k - 2) + 2 by lia]
      rw [factorial_succ_succ_cast]
      push_cast
      rw [Nat.cast_sub hk]
      ring
    dsimp only [G]
    have h₃ : n - (k - 2) = n + 2 - k := by lia
    have h₄ : n + m - (k - 2) = n + 2 + m - k := by lia
    field_simp [factorial_cast_ne_zero]
    rw [h₃, h₄, h₁, h₂]
    ring
  rw [hG₁, hG₂, hG₃, hG₄, hG₅, hG₆]
  have h_poly := pure_poly_identity (n : ℝ) (m : ℝ) (k : ℝ)
  rw [show ((n : ℝ) + 2 * m + 2) * (((n : ℝ) + 2) * (n + 1) * (n + 2 + m) * (n + 1 + m) * G) =
    ((n : ℝ) + 2 * m + 2) * (n + 2) * (n + 1) * (n + 2 + m) * (n + 1 + m) * G by ring]
  rw [show ((2 * n : ℝ) + 2 * m + 3) * (((n : ℝ) + 1) * (n + 1 + m) * (n + 2 - k) *
    (n + 2 + m - k) * G + ((n : ℝ) + 1) * (n + 1 + m) * (k : ℝ) * (m + k) * G) -
    ((n : ℝ) + 1) * (((n : ℝ) + 2 - k) * (n + 1 - k) * (n + 2 + m - k) * (n + 1 + m - k) * G -
      2 * (((n : ℝ) + 2 - k) * (n + 2 + m - k) * (k : ℝ) * (m + k) * G) +
      (k : ℝ) * (k - 1) * (m + k) * (m + k - 1) * G) =
    (((2 * n : ℝ) + 2 * m + 3) * ((n + 1) * (n + 1 + m) * (n + 2 - k) * (n + 2 + m - k) +
      (n + 1) * (n + 1 + m) * k * (m + k)) -
      ((n : ℝ) + 1) * ((n + 2 - k) * (n + 1 - k) * (n + 2 + m - k) * (n + 1 + m - k) -
        2 * (n + 2 - k) * (n + 2 + m - k) * k * (m + k) +
        k * (k - 1) * (m + k) * (m + k - 1))) * G by ring]
  rw [h_poly]

lemma coeff_narayanaPolynomial_pure_rec_boundary (m n : ℕ) (hn : n ≠ 0) :
    ((n : ℝ) + 2 * m + 2) * (narayanaPolynomial m (n + 2)).coeff (n + 1) =
    ((2 * n : ℝ) + 2 * m + 3) *
      ((narayanaPolynomial m (n + 1)).coeff (n + 1) +
        (narayanaPolynomial m (n + 1)).coeff n) -
    ((n : ℝ) + 1) *
      ((narayanaPolynomial m n).coeff (n + 1) -
        2 * (narayanaPolynomial m n).coeff n +
        (narayanaPolynomial m n).coeff (n - 1)) := by
  rw [coeff_narayanaPolynomial_of_le (Nat.le_succ (n + 1)),
    coeff_narayanaPolynomial_of_le le_rfl,
    coeff_narayanaPolynomial_of_le (Nat.le_succ n),
    coeff_narayanaPolynomial_of_lt (Nat.lt_succ_self n),
    coeff_narayanaPolynomial_of_le le_rfl,
    coeff_narayanaPolynomial_of_le (Nat.sub_le n 1)]
  rw [narayanaTransformCoeff_self (m := m) (n := n + 1),
        narayanaTransformCoeff_self (m := m) (n := n),
    narayanaTransformCoeff_eq_factorial m (n + 2) (n + 1) (Nat.le_succ (n + 1)),
    narayanaTransformCoeff_eq_factorial m (n + 1) n (Nat.le_succ n),
    narayanaTransformCoeff_eq_factorial m n (n - 1) (Nat.sub_le n 1)]
  have heq₃ : n + 2 - (n + 1) = 1 := by lia
  have heq₄ : n + 2 + m - (n + 1) = m + 1 := by lia
  have heq₅ : n + 1 - n = 1 := by lia
  have heq₆ : n + 1 + m - n = m + 1 := by lia
  have heq₇ : n - (n - 1) = 1 := by lia
  have heq₈ : n + m - (n - 1) = m + 1 := by lia
  rw [heq₃, heq₄, heq₅, heq₆, heq₇, heq₈, Nat.factorial_one]
  have hn₂_fac := factorial_succ_succ_cast n
  have hn₁_fac := factorial_succ_cast n
  have hn₂m_fac : ((n + 2 + m).factorial : ℝ) = (n + 2 + m) * (n + 1 + m) * (n + m).factorial := by
    rw [show n + 2 + m = n + m + 2 by ring, factorial_succ_succ_cast]
    push_cast
    ring
  have hn₁m_fac : ((n + 1 + m).factorial : ℝ) = (n + 1 + m) * (n + m).factorial := by
    rw [show n + 1 + m = n + m + 1 by ring, factorial_succ_cast (n + m)]
    push_cast
    ring
  have hn_fac := factorial_cast_pred hn
  have hnm_fac : ((n + m).factorial : ℝ) = (n + m) * (m + (n - 1)).factorial := by
    rw [show n + m = m + (n - 1) + 1 by lia, factorial_succ_cast (m + (n - 1))]
    push_cast
    rw [Nat.cast_sub (by lia : 1 ≤ n)]
    ring
  have hmn_fac : ((m + n).factorial : ℝ) =
      (m + n) * (m + (n - 1)).factorial := by
    rw [show m + n = m + (n - 1) + 1 by lia, factorial_succ_cast (m + (n - 1))]
    push_cast
    rw [Nat.cast_sub (by lia : 1 ≤ n)]
    ring
  have hm_fac := factorial_succ_cast m
  have hmn₁_fac : ((m + (n + 1)).factorial : ℝ) =
      (m + n + 1) * (n + m).factorial := by
    rw [show m + (n + 1) = m + n + 1 by ring, show n + m = m + n by ring,
      factorial_succ_cast (m + n)]
    push_cast
    ring
  simp only [hn₂_fac, hn₁_fac, hn₂m_fac, hn₁m_fac, hmn₁_fac, hn_fac, hnm_fac, hmn_fac, hm_fac]
  have : (Nat.factorial m : ℝ) ≠ 0 := factorial_cast_ne_zero m
  have : (Nat.factorial (n - 1) : ℝ) ≠ 0 := factorial_cast_ne_zero (n - 1)
  have : (Nat.factorial (m + (n - 1)) : ℝ) ≠ 0 := factorial_cast_ne_zero (m + (n - 1))
  have : (n : ℝ) ≠ 0 := by positivity
  have : (m : ℝ) + 1 ≠ 0 := by positivity
  have : (m : ℝ) + n ≠ 0 := by positivity
  have : (n : ℝ) + m ≠ 0 := by positivity
  generalize (Nat.factorial m : ℝ) = Fm at *
  generalize (Nat.factorial (n - 1) : ℝ) = Fn₁ at *
  generalize (Nat.factorial (m + (n - 1)) : ℝ) = Fmn₁ at *
  field_simp
  push_cast
  ring

theorem coeff_narayanaPolynomial_pure_rec (m n k : ℕ) (hk : 2 ≤ k) :
    ((n : ℝ) + 2 * m + 2) * (narayanaPolynomial m (n + 2)).coeff k =
      ((2 * n : ℝ) + 2 * m + 3) *
          ((narayanaPolynomial m (n + 1)).coeff k +
            (narayanaPolynomial m (n + 1)).coeff (k - 1)) -
        ((n : ℝ) + 1) *
          ((narayanaPolynomial m n).coeff k -
            2 * (narayanaPolynomial m n).coeff (k - 1) +
            (narayanaPolynomial m n).coeff (k - 2)) := by
  rcases le_or_gt k n with hkn | hnk
  · have hkn₁ : k ≤ n + 1 := by lia
    have hkn₂ : k ≤ n + 2 := by lia
    have hk₁n : k - 1 ≤ n := by lia
    have hk₂n : k - 2 ≤ n := by lia
    have hk₁n₁ : k - 1 ≤ n + 1 := by lia
    rw [coeff_narayanaPolynomial_of_le hkn₂, coeff_narayanaPolynomial_of_le hkn₁,
      coeff_narayanaPolynomial_of_le hk₁n₁, coeff_narayanaPolynomial_of_le hkn,
      coeff_narayanaPolynomial_of_le hk₁n, coeff_narayanaPolynomial_of_le hk₂n]
    exact narayanaTransformCoeff_pure_rec m n k hk hkn
  · rcases eq_or_lt_of_le (by lia : n + 1 ≤ k) with rfl | hk
    · exact coeff_narayanaPolynomial_pure_rec_boundary m n (by lia)
    · rcases eq_or_lt_of_le (by lia : n + 2 ≤ k) with rfl | hk
      · change _ = _ * (_ + (narayanaPolynomial m (n + 1)).coeff (n + 1)) -
          _ * (_ - 2 * (narayanaPolynomial m n).coeff (n + 1) + (narayanaPolynomial m n).coeff n)
        rw [coeff_narayanaPolynomial_of_le le_rfl,
          narayanaTransformCoeff_self,
          coeff_narayanaPolynomial_of_lt (Nat.lt_succ_self (n + 1)),
          coeff_narayanaPolynomial_of_le le_rfl,
          coeff_narayanaPolynomial_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self n)),
          coeff_narayanaPolynomial_of_lt (Nat.lt_succ_self n),
          coeff_narayanaPolynomial_of_le le_rfl]
        rw [narayanaTransformCoeff_self, narayanaTransformCoeff_self]
        ring
      · rw [coeff_narayanaPolynomial_of_lt hk,
          coeff_narayanaPolynomial_of_lt (by lia : n + 1 < k),
          coeff_narayanaPolynomial_of_lt (by lia : n + 1 < k - 1),
          coeff_narayanaPolynomial_of_lt (by lia : n < k),
          coeff_narayanaPolynomial_of_lt (by lia : n < k - 1),
          coeff_narayanaPolynomial_of_lt (by lia : n < k - 2)]
        simp

theorem narayanaPolynomial_pure_rec (m n : ℕ) :
    C ((n : ℝ) + 2 * m + 2) * narayanaPolynomial m (n + 2) =
      C ((2 * n : ℝ) + 2 * m + 3) * ((1 + X) * narayanaPolynomial m (n + 1)) -
        C ((n : ℝ) + 1) * ((1 - X) ^ 2 * narayanaPolynomial m n) := by
  ext k
  have h₁ : (1 + X : ℝ[X]) * narayanaPolynomial m (n + 1) =
      narayanaPolynomial m (n + 1) + X * narayanaPolynomial m (n + 1) := by ring
  have h₂ : (1 - X : ℝ[X]) ^ 2 * narayanaPolynomial m n =
      narayanaPolynomial m n - C 2 * (X * narayanaPolynomial m n) +
        X ^ 2 * narayanaPolynomial m n := by
    rw [C_ofNat 2]
    ring
  rw [h₁, h₂, mul_add, mul_add, mul_sub]
  rcases k with _ | _ | k
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_zero, sq, mul_assoc,
      coeff_narayanaPolynomial_of_le, narayanaTransformCoeff_zero_right, Nat.zero_le]
    ring
  · rcases n with rfl | n
    · simp only [CharP.cast_eq_zero, zero_add, mul_zero, map_one,
        narayanaPolynomial_zero_right, mul_one, one_mul, coeff_sub, coeff_add, coeff_mul_X,
        coeff_C_zero, coeff_X_pow, OfNat.one_ne_ofNat, ↓reduceIte, add_zero,
        coeff_C_mul, coeff_X_mul, coeff_one]
      rw [coeff_narayanaPolynomial_of_le (Nat.le_succ 1), coeff_narayanaPolynomial_of_le le_rfl]
      rw [narayanaTransformCoeff_self]
      dsimp [narayanaTransformCoeff]
      simp
      field_simp
      ring
    · have hcoeff₁ (N : ℕ) (hN : N ≠ 0) :
            narayanaTransformCoeff m N 1 = (N : ℝ) * (N + m) / (m + 1) := by
        dsimp [narayanaTransformCoeff]
        simp
      simp [hcoeff₁, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, sq, mul_assoc,
        coeff_narayanaPolynomial_of_le, narayanaTransformCoeff_zero_right, add_mul, mul_add]
      field_simp
      ring
  · have hk_ge : 2 ≤ k + 2 := by lia
    rw [coeff_C_mul, coeff_narayanaPolynomial_pure_rec m n (k + 2) hk_ge]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, sq, mul_assoc]
    push_cast
    ring

theorem narayanaPolynomial_no_common_root (m : ℕ) :
    ∀ (n : ℕ) (r : ℝ), (narayanaPolynomial m (n + 1)).IsRoot r →
      ¬ (narayanaPolynomial m n).IsRoot r := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      intro r hr₂ hr₁
      have hr_ne : r ≠ 1 := fun h => (narayanaPolynomial_eval_one_pos m (n + 1)).ne' (h ▸ hr₁)
      have : (C ((n : ℝ) + 2 * m + 2) * narayanaPolynomial m (n + 2)).eval r =
          (C ((2 * n : ℝ) + 2 * m + 3) * ((1 + X) * narayanaPolynomial m (n + 1)) -
            C ((n : ℝ) + 1) * ((1 - X) ^ 2 * narayanaPolynomial m n)).eval r :=
        congrArg (eval r) (narayanaPolynomial_pure_rec m n)
      simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_one, eval_X] at this
      rw [hr₂, hr₁] at this
      have : (1 - r) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hr_ne))
      have : ((n : ℝ) + 1) ≠ 0 := by positivity
      simp_all

theorem prec_narayanaPolynomial_one_two (m : ℕ) :
    Prec (narayanaPolynomial m 1) (narayanaPolynomial m 2) := by
  have hm₁ : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set c : ℝ := 2 * ((m : ℝ) + 2) / ((m : ℝ) + 1) with hcdef
  have hcgt : 2 < c := by
    rw [hcdef, lt_div_iff₀ hm₁]
    linarith
  have hN₁ : narayanaPolynomial m 1 = X + C 1 := narayanaPolynomial_one m
  have hN₂ : narayanaPolynomial m 2 = X ^ 2 + C c * X + C 1 := narayanaPolynomial_two m
  have hdisc : (0 : ℝ) ≤ discrim 1 c 1 := by
    rw [discrim]
    nlinarith [hcgt]
  have hN₂_form : narayanaPolynomial m 2 = C (1 : ℝ) * X ^ 2 + C c * X + C 1 := by simp [hN₂]
  have hsplit₂ : (narayanaPolynomial m 2).Splits := by
    rw [hN₂_form]
    exact quadraticPoly_splits_of_discrim_nonneg one_ne_zero hdisc
  have hsplit₁ : (narayanaPolynomial m 1).Splits := by
    rw [hN₁]
    have : (X + C 1 : ℝ[X]) = X - C (-1) := by simp
    rw [this]
    exact Splits.X_sub_C (-1)
  set d : ℝ := Real.sqrt (discrim 1 c 1) with hddef
  set r₁ : ℝ := (-c - d) / 2 with hr₁_def
  set r₂ : ℝ := (-c + d) / 2 with hr₂_def
  have hr₁₂ : r₁ ≤ r₂ := by
    rw [hr₁_def, hr₂_def]
    have : 0 ≤ d := Real.sqrt_nonneg _
    linarith
  have hd_sq : d ^ 2 = c ^ 2 - 4 := by
    rw [hddef, discrim]
    have := Real.sq_sqrt hdisc
    rw [discrim] at this
    linarith
  have hsum : r₁ + r₂ = -c := by
    rw [hr₁_def, hr₂_def]
    ring
  have hprod : r₁ * r₂ = 1 := by
    rw [hr₁_def, hr₂_def]
    nlinarith [hd_sq]
  have hfactor : narayanaPolynomial m 2 = (X - C r₁) * (X - C r₂) := by
    rw [hN₂]
    symm
    calc (X - C r₁) * (X - C r₂)
      _ = X ^ 2 - C (r₁ + r₂) * X + C (r₁ * r₂) := by
          simp only [map_add, map_mul]
          ring
      _ = X ^ 2 + C c * X + C 1 := by
          rw [hsum, hprod]
          simp
  have hprod_neg : ((-1 : ℝ) - r₁) * ((-1 : ℝ) - r₂) < 0 := by
    calc ((-1 : ℝ) - r₁) * ((-1 : ℝ) - r₂)
      _ = 2 - c := by
          have : ((-1 : ℝ) - r₁) * ((-1 : ℝ) - r₂) = 1 + (r₁ + r₂) + r₁ * r₂ := by ring
          rw [this, hsum, hprod]
          ring
      _ < 0 := by linarith [hcgt]
  have hbetween : r₁ ≤ -1 ∧ -1 ≤ r₂ := by
    constructor
    · rw [hr₁_def]
      linarith [hcgt]
    · by_contra h
      have : r₂ < -1 := not_le.mp h
      nlinarith [hprod_neg, hr₁₂, this]
  refine ⟨⟨narayanaPolynomial_ne_zero m 1, hsplit₁⟩, ⟨narayanaPolynomial_ne_zero m 2, hsplit₂⟩,
    [(-1 : ℝ)], [r₁, r₂], ?_, ?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · exact List.pairwise_singleton _ _
  · simp [hr₁₂]
  · have : (X + C (1 : ℝ)) = X - C (-1) := by simp
    rw [hN₁, this, Polynomial.roots_X_sub_C]
    rfl
  · rw [hfactor, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
      roots_X_sub_C, roots_X_sub_C]
    rfl
  · simp
  · exact ⟨hbetween.1, hbetween.2, trivial⟩

lemma two_mul_sub_two_mul_sq_nonpos_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2).eval r ≤ 0 := by
  simp only [eval_mul, eval_C, eval_sub, eval_pow, eval_X]
  nlinarith

theorem splits_narayanaPolynomial (m n : ℕ) :
    (narayanaPolynomial m n).Splits := by
  set P : ℕ → ℝ[X] := fun k => narayanaPolynomial m (k + 1) with hP
  have hpos (k : ℕ) : HasPosLeadingCoeff (P k) :=
    hasPosLeadingCoeff_narayanaPolynomial m (k + 1)
  have hdeg_succ (k : ℕ) : (P k).natDegree + 1 = (P (k + 1)).natDegree := by
    simp only [hP, natDegree_narayanaPolynomial]
  have hdeg_two (k : ℕ) : 2 ≤ (P (k + 1)).natDegree := by
    rw [hP, natDegree_narayanaPolynomial]
    lia
  have hno (k : ℕ) (r : ℝ) (hr : (P (k + 1)).IsRoot r) : ¬ (P k).IsRoot r :=
    narayanaPolynomial_no_common_root m (k + 1) r hr
  have hrec (k : ℕ) :
      P (k + 2) =
        (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ *
          (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)
            + C ((3 * (k + 1 : ℕ) : ℝ) + 2 * m + 4) * X)) * P (k + 1)
        + (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ * (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2)) *
            (P (k + 1)).derivative
        + 0 * P k := by
    grind [narayanaPolynomial_deriv_lag_rec m (k + 1)]
  have hbase : Prec (P 0) (P 1) := prec_narayanaPolynomial_one_two m
  have hV_nonpos (k : ℕ) (r : ℝ) (hr : (P (k + 1)).IsRoot r) :
      (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ * (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2)).eval r ≤ 0 := by
    rw [eval_mul, eval_C]
    have : 0 ≤ (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos this
      (two_mul_sub_two_mul_sq_nonpos_of_nonpos (narayanaPolynomial_root_nonpos hr))
  have hW_nonpos (k : ℕ) (r : ℝ) (_ : (P (k + 1)).IsRoot r) : (0 : ℝ[X]).eval r ≤ 0 := by simp
  have hbuild := isRealRooted_of_lw_derivative_lag_sequence
    (P := P)
    (U := fun k ↦ C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ *
      (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2) + C ((3 * (k + 1 : ℕ) : ℝ) + 2 * m + 4) * X))
    (V := fun k => C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ * (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2))
    (W := fun _ => 0)
    hbase hpos hdeg_two hrec hV_nonpos hW_nonpos hdeg_succ hno
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [*]
  · rw [← Nat.sub_add_cancel hn]
    exact (hbuild (n - 1)).2

/-- The generalized Narayana polynomials are PF polynomials. -/
theorem narayanaPolynomialRootLocation (m n : ℕ) :
    IsPFPolynomial (narayanaPolynomial m n) :=
  IsPFPolynomial.of_realRooted_nonneg
    (hasNonnegCoeffs_narayanaPolynomial m n)
    (splits_narayanaPolynomial m n)

/-- The Narayana transform preserves PF polynomials, reduced to the
Gribinski--Marcus rectangular additive convolution theorem. -/
theorem narayanaTransformPreservesPF (m : ℕ) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (narayanaTransform m p) := by
  refine IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    hp.hasNonnegCoeffs.narayanaTransform ?_
  by_cases hp0 : p = 0
  · left
    simp [hp0, narayanaTransform]
  · right
    set n := p.natDegree with hn
    have hpdeg : p.natDegree ≤ n := by rw [hn]
    have hqdeg : (narayanaTransform m p).natDegree ≤ n := by
      simpa [hn] using natDegree_narayanaTransform_le m p
    have hpcoeff : p.coeff n ≠ 0 := by
      rw [hn, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp0
    have hfdeg : (degreeSignFlip n p).natDegree = n :=
      natDegree_degreeSignFlip_eq_of_coeff_ne_zero hpcoeff
    have hflead : 0 < (degreeSignFlip n p).leadingCoeff := by
      rw [leadingCoeff_degreeSignFlip_of_coeff_ne_zero hpcoeff, hn,
        Polynomial.coeff_natDegree]
      exact hp.hasNonnegCoeffs.pos_leadingCoeff hp0
    have hNdeg : (narayanaPolynomial m n).natDegree ≤ n := by
      rw [natDegree_narayanaPolynomial]
    have hNcoeff : (narayanaPolynomial m n).coeff n ≠ 0 := by simp
    have hgdeg : (degreeSignFlip n (narayanaPolynomial m n)).natDegree = n :=
      natDegree_degreeSignFlip_eq_of_coeff_ne_zero hNcoeff
    have hglead : 0 < (degreeSignFlip n (narayanaPolynomial m n)).leadingCoeff := by
      rw [leadingCoeff_degreeSignFlip_of_coeff_ne_zero hNcoeff,
        coeff_narayanaPolynomial_of_le le_rfl]
      simp
    have hfroots : HasOnlyNonnegRoots (degreeSignFlip n p) :=
      hp.hasOnlyNonposRoots.degreeSignFlip_hasOnlyNonnegRoots hpdeg
    have hgroots : HasOnlyNonnegRoots (degreeSignFlip n (narayanaPolynomial m n)) :=
      (narayanaPolynomialRootLocation m n).hasOnlyNonposRoots
        |>.degreeSignFlip_hasOnlyNonnegRoots hNdeg
    have hconv :
        HasOnlyNonnegRoots
          (rectangularAdditiveConvolution m n (degreeSignFlip n p)
            (degreeSignFlip n (narayanaPolynomial m n))) :=
      rectangularAdditiveConvolutionPreservesNonnegRoots
        (m := m) (n := n)
        (f := degreeSignFlip n p)
        (g := degreeSignFlip n (narayanaPolynomial m n))
        hfdeg hgdeg hflead hglead hfroots hgroots
    have hconv_eq :
        rectangularAdditiveConvolution m n (degreeSignFlip n p)
            (degreeSignFlip n (narayanaPolynomial m n)) =
          degreeSignFlip n (narayanaTransform m p) :=
      rectangularAdditiveConvolution_degreeSignFlip_narayanaPolynomial_eq m n p hpdeg
    have hsign : HasOnlyNonnegRoots (degreeSignFlip n (narayanaTransform m p)) := by
      simpa [hconv_eq] using hconv
    have hsign_splits : (degreeSignFlip n (narayanaTransform m p)).Splits := by
      rcases hsign with hzero | ⟨hsplits, _⟩
      · simp [hzero]
      · exact hsplits
    exact splits_of_degreeSignFlip_splits hqdeg hsign_splits

end RealRooted
