import Mathlib.Tactic
import RealRooted.GammaRealRoots
import RealRooted.LiebSokal
import RealRooted.LiuWangRecursion
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import RealRooted.Mathlib.Data.Nat.Choose.Cast
import RealRooted.PFPolynomial
import RealRooted.QuadraticRoot
import RealRooted.RectangularConvolution
import RealRooted.RectangularConvolutionIdentity
import RealRooted.Touchard

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

/-- The easy direction of Gribinski--Marcus, Lemma 2.5: a nonzero polynomial
with only nonnegative roots has a real-stable bivariate lift `p(x * y)`. -/
theorem HasOnlyNonnegRoots.mvRealStable_xyLift {p : ℝ[X]}
    (hp : HasOnlyNonnegRoots p) (hpne : p ≠ 0) :
    MvRealStable (xyLift p) := by
  rcases hp with hpzero | ⟨hsplits, hroots⟩
  · exact (hpne hpzero).elim
  intro z hz
  rw [eval_complexifyMv_xyLift, eval_map_ofReal_eq_prod hsplits]
  refine mul_ne_zero (by simp [hpne]) ?_
  apply Multiset.prod_ne_zero
  simp only [Multiset.mem_map, not_exists, not_and]
  rintro r hrmem
  exact sub_ne_zero.mpr
    (mul_ne_ofReal_of_im_pos (hz 0) (hz 1) (hroots r hrmem))

/-- Gribinski--Marcus, Lemma 2.5, in the project's zero-aware root language.
The nonzero hypothesis excludes the identically zero lift. -/
theorem hasOnlyNonnegRoots_iff_mvRealStable_xyLift {p : ℝ[X]} (hpne : p ≠ 0) :
    HasOnlyNonnegRoots p ↔ MvRealStable (xyLift p) := by
  refine ⟨fun hp => hp.mvRealStable_xyLift hpne, ?_⟩
  intro hstable
  have hroot_nonneg_real {z : ℂ}
      (hzroot : (p.map Complex.ofRealHom).IsRoot z) :
      ∃ r : ℝ, 0 ≤ r ∧ z = r := by
    by_contra houtside
    have hzoutside : ∀ r : ℝ, 0 ≤ r → z ≠ r := by
      intro r hr hzr
      exact houtside ⟨r, hr, hzr⟩
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_upperHalfPlane_mul_eq hzoutside
    have hnonzero := hstable ![x, y] (by
      intro i
      fin_cases i
      · simpa using hx
      · simpa using hy)
    rw [eval_complexifyMv_xyLift] at hnonzero
    have harg : ![x, y] 0 * ![x, y] 1 = z := by simpa using hxy
    rw [harg] at hnonzero
    exact hnonzero hzroot
  have hsplitsComplex : (p.map Complex.ofRealHom).Splits := IsAlgClosed.splits _
  have hsplits : p.Splits :=
    Polynomial.Splits.of_splits_map Complex.ofRealHom hsplitsComplex (by
      intro z hzmem
      have hzroot : (p.map Complex.ofRealHom).IsRoot z :=
        (Polynomial.mem_roots (Polynomial.map_ne_zero hpne)).mp hzmem
      obtain ⟨r, -, hzr⟩ := hroot_nonneg_real hzroot
      exact ⟨r, hzr.symm⟩)
  refine Or.inr ⟨hsplits, ?_⟩
  intro r hrmem
  have hrroot : p.IsRoot r := (Polynomial.mem_roots hpne).mp hrmem
  have hmappedRoot : (p.map Complex.ofRealHom).IsRoot (r : ℂ) := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    change p.eval₂ Complex.ofRealHom (Complex.ofRealHom r) = 0
    rw [Polynomial.eval₂_hom, hrroot]
    simp
  obtain ⟨s, hs, hrs⟩ := hroot_nonneg_real hmappedRoot
  have : r = s := by
    have := congrArg Complex.re hrs
    simpa using this
  simpa [this] using hs

/-- The exact-degree, positive-leading-coefficient form of
Gribinski--Marcus, Lemma 2.5. -/
theorem hasOnlyNonnegRoots_iff_realStable_XY {d : ℕ} {p : ℝ[X]}
    (_hpdeg : p.natDegree = d) (hlead : 0 < p.leadingCoeff) :
    HasOnlyNonnegRoots p ↔ MvRealStable (xyLift p) :=
  hasOnlyNonnegRoots_iff_mvRealStable_xyLift
    (Polynomial.leadingCoeff_ne_zero.mp hlead.ne')

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

theorem hasOnlyNonnegRoots_C_mul_X_add_C_of_pos_nonpos {A B : ℝ}
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
  have hcoeff1pos : 0 < p.coeff 1 := by simpa [Polynomial.leadingCoeff, hpdeg] using hplead
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

theorem degreeSignFlip_two_quadratic (a b c : ℝ) :
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


end RealRooted
