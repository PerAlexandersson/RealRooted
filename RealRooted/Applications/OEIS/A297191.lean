module

public import Mathlib
public import RealRooted.OperatorPreservesInterlacing
public import RealRooted.SimpleRoots
public import RealRooted.Basic.Coefficients
public import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic.Chebyshev.Trigonometric
public import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic.Rescale
import RealRooted.GammaTransform.TwoStep
import RealRooted.ThreeTermRecurrence.Interlacing
public import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic.Chebyshev
public import RealRooted.GammaTransform.Basic
import RealRooted.ObreschkoffConverse.Converse
public import RealRooted.AllCombo

/-!
# OEIS A297191

The row polynomials of [OEIS A297191](https://oeis.org/A297191) satisfy a
quadratic recurrence.  We prove that row `n` has `2n` distinct negative roots
and is palindromic.  Inserting the half-step `(1 + X) Pₙ` gives the strict
interlacing chain `P₀ ≪ (1 + X)P₀ ≪ P₁ ≪ (1 + X)P₁ ≪ ⋯`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A297191

/-- The row polynomial of [OEIS A297191](https://oeis.org/A297191), equivalently
every other row of the Delannoy array:
`P_0 = 1`, `P_1 = 1 + 3X + X²`, `P_{n+2} = (1 + 4X + X²) P_{n+1} - X² P_n`.
Equivalently `P_n = gammaTransform_{2n}(Q_n)` with `Q_n` the A054142 rows. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X + X ^ 2
  | n + 2 => (1 + 4 * X + X ^ 2) * polynomial (n + 1) - X ^ 2 * polynomial n

/-! ## Sanity checks (exact) -/

example : polynomial 2 = 1 + 7 * X + 13 * X ^ 2 + 7 * X ^ 3 + X ^ 4 := by
  simp [polynomial]
  ring

private lemma polynomial_add_two (n : ℕ) :
    polynomial (n + 2) =
      (1 + 4 * X + X ^ 2) * polynomial (n + 1) - X ^ 2 * polynomial n :=
  rfl

private lemma recurrenceFactor_monic_natDegree :
    (1 + 4 * X + X ^ 2 : ℝ[X]).Monic ∧
      (1 + 4 * X + X ^ 2 : ℝ[X]).natDegree = 2 := by
  exact ⟨by monicity!, by compute_degree!⟩

private lemma monic_natDegree_polynomial (n : ℕ) :
    (polynomial n).Monic ∧ (polynomial n).natDegree = 2 * n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [polynomial]
  | 1 => refine ⟨?_, ?_⟩ <;> simp only [polynomial]
         · monicity!
         · compute_degree!
  | n + 2 =>
    obtain ⟨h1m, h1d⟩ := ih (n+1) (by lia)
    obtain ⟨h0m, h0d⟩ := ih n (by lia)
    have hA : ((1 + 4 * X + X ^ 2) * polynomial (n + 1)).Monic :=
      recurrenceFactor_monic_natDegree.1.mul h1m
    have hAd : ((1 + 4 * X + X ^ 2) * polynomial (n + 1)).natDegree = 2 * (n+2) := by
      rw [recurrenceFactor_monic_natDegree.1.natDegree_mul h1m,
        recurrenceFactor_monic_natDegree.2, h1d]
      ring
    have hBd : (X ^ 2 * polynomial n : ℝ[X]).natDegree = 2 * n + 2 := by
      rw [(monic_X_pow 2).natDegree_mul h0m, h0d, natDegree_X_pow]; ring
    have hlt : (X ^ 2 * polynomial n : ℝ[X]).degree <
        ((1 + 4 * X + X ^ 2) * polynomial (n + 1)).degree := by
      rw [degree_eq_natDegree hA.ne_zero, degree_eq_natDegree ((monic_X_pow 2).mul h0m).ne_zero,
        hAd, hBd]; norm_cast; lia
    rw [polynomial_add_two]
    refine ⟨hA.sub_of_left hlt, ?_⟩
    rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [hAd, hBd]; lia), hAd]

/-- Degree `2n`, monic, nonnegative coefficients, constant coefficient `1`. -/
theorem natDegree_polynomial (n : ℕ) : (polynomial n).natDegree = 2 * n :=
  (monic_natDegree_polynomial n).2

/-- Every A297191 row polynomial is monic. -/
theorem monic_polynomial (n : ℕ) : (polynomial n).Monic :=
  (monic_natDegree_polynomial n).1

private lemma hasNonnegCoeffs_three : HasNonnegCoeffs (3 : ℝ[X]) := by
  simpa only [C_ofNat] using hasNonnegCoeffs_C (by norm_num : (0 : ℝ) ≤ 3)

private lemma hasNonnegCoeffs_polynomial_succ_aux (n : ℕ) :
    HasNonnegCoeffs (polynomial (n + 1)) ∧
      HasNonnegCoeffs (polynomial (n + 1) - X * polynomial n) := by
  induction n with
  | zero =>
    have : polynomial 1 - X * polynomial 0 = (1 + X) * (1 + X) := by simp [polynomial]; ring
    rw [this]
    refine ⟨?_, (hasNonnegCoeffs_one.add hasNonnegCoeffs_X).mul
      (hasNonnegCoeffs_one.add hasNonnegCoeffs_X)⟩
    simp only [polynomial]
    exact (hasNonnegCoeffs_one.add
      (hasNonnegCoeffs_three.mul hasNonnegCoeffs_X)).add (by
        simpa only [pow_two] using hasNonnegCoeffs_X.mul hasNonnegCoeffs_X)
  | succ n ih =>
    have hD' : HasNonnegCoeffs (polynomial (n + 2) - X * polynomial (n + 1)) := by
      rw [show polynomial (n + 2) - X * polynomial (n + 1) =
          (1 + X) * (1 + X) * polynomial (n + 1) +
            X * (polynomial (n + 1) - X * polynomial n) by
        rw [polynomial_add_two]; ring]
      exact (((hasNonnegCoeffs_one.add hasNonnegCoeffs_X).mul
        (hasNonnegCoeffs_one.add hasNonnegCoeffs_X)).mul ih.1).add
        (hasNonnegCoeffs_X.mul ih.2)
    refine ⟨?_, hD'⟩
    rw [show polynomial (n + 2) = X * polynomial (n + 1) +
        (polynomial (n + 2) - X * polynomial (n + 1)) by ring]
    exact (hasNonnegCoeffs_X.mul ih.1).add hD'

/-- Every A297191 row has nonnegative coefficients. -/
theorem hasNonnegCoeffs_polynomial (n : ℕ) : HasNonnegCoeffs (polynomial n) := by
  cases n with
  | zero => simpa only [polynomial] using hasNonnegCoeffs_one
  | succ n => exact (hasNonnegCoeffs_polynomial_succ_aux n).1

private lemma eval_zero_polynomial (n : ℕ) : (polynomial n).eval 0 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [polynomial]
  | 1 => simp [polynomial]
  | n + 2 => rw [polynomial_add_two]; simp [ih (n+1) (by lia)]

/-- Every A297191 row has constant coefficient one. -/
theorem coeff_zero_polynomial (n : ℕ) : (polynomial n).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_zero_polynomial]

/-- All roots of an A297191 row are strictly negative. -/
theorem roots_mem_Iio_zero (n : ℕ) :
    ∀ r ∈ (polynomial n).roots, r ∈ Set.Iio (0 : ℝ) := by
  intro r hr
  have hnonpos := roots_nonpos_of_hasNonnegCoeffs
    (hasNonnegCoeffs_polynomial n) r hr
  have hne : r ≠ 0 := by
    rintro rfl
    have hroot := (mem_roots (monic_polynomial n).ne_zero).mp hr
    rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero,
      coeff_zero_polynomial] at hroot
    norm_num at hroot
  exact lt_of_le_of_ne hnonpos hne

/-- `P_n(-1) = (-1)^n`; in particular `-1` is not a root of any polynomial. -/
theorem eval_neg_one_polynomial (n : ℕ) : (polynomial n).eval (-1) = (-1) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [polynomial]
  | 1 => simp [polynomial]; norm_num
  | n + 2 =>
    rw [polynomial_add_two]; simp [ih (n+1) (by lia), ih n (by lia)]; ring

private lemma reflect_recurrenceFactor :
    reflect 2 (1 + 4 * X + X ^ 2 : ℝ[X]) = 1 + 4 * X + X ^ 2 := by
  have h : (1 + 4 * X + X ^ 2 : ℝ[X]) =
      C 1 * X ^ 0 + C 4 * X ^ 1 + C 1 * X ^ 2 := by
    simp only [map_one, pow_zero, mul_one, pow_one, one_mul]
    rw [← C_ofNat]
  rw [h, reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow, reflect_C_mul_X_pow]
  norm_num [revAt_le]
  ring

private lemma reflect_polynomial (n : ℕ) : reflect (2 * n) (polynomial n) = polynomial n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [polynomial]
  | 1 =>
    have h : polynomial 1 = C 1 * X ^ 0 + C 3 * X ^ 1 + C 1 * X ^ 2 := by
      simp only [polynomial]
      simp only [map_one, pow_zero, mul_one, pow_one, one_mul]
      rw [← C_ofNat]
    rw [h, reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow, reflect_C_mul_X_pow]
    norm_num [revAt_le]
    ring
  | n + 2 =>
    rw [polynomial_add_two, reflect_sub]
    have e1 : 2 * (n+2) = 2 + 2 * (n+1) := by ring
    have e2 : 2 * (n+2) = 4 + 2 * n := by ring
    rw [e1, reflect_mul _ _ (by rw [recurrenceFactor_monic_natDegree.2])
      (by rw [natDegree_polynomial]), reflect_recurrenceFactor, ih (n + 1) (by lia),
      ← e1, e2, reflect_mul _ _ (by rw [natDegree_X_pow]; norm_num)
      (by rw [natDegree_polynomial]),
      ih n (by lia), reflect_monomial]
    simp [revAt_le]

/-- The rows are palindromic: `X^{2n} P_n(1/X) = P_n`. -/
theorem reverse_polynomial (n : ℕ) : (polynomial n).reverse = polynomial n := by
  rw [reverse, natDegree_polynomial, reflect_polynomial]

private lemma evalSequence_isSolution (x : ℝ) :
    (LinearRecurrence.quadratic (1 + 4 * x + x ^ 2) (-x ^ 2)).IsSolution
      (fun n ↦ (polynomial n).eval x) := by
  rw [LinearRecurrence.quadratic_isSolution_iff]
  intro n
  rw [polynomial_add_two]
  simp only [eval_sub, eval_mul, eval_add, eval_one, eval_ofNat, eval_X, eval_pow]
  ring

/-- Chebyshev closed form for evaluations of the A297191 rows away from zero.
The right side is defined using Mathlib's `Polynomial.Chebyshev.U`. -/
theorem eval_div_pow_polynomial (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (polynomial n).eval x / x ^ n =
      LinearRecurrence.quadraticChebyshevSolution
        ((1 + 4 * x + x ^ 2) / (2 * x)) 1
        ((1 + 3 * x + x ^ 2) / x) n := by
  have hnormalized := LinearRecurrence.quadraticRescale_isSolution hx
    (evalSequence_isSolution x)
  have hnormalized' :
      (LinearRecurrence.quadratic
        (2 * ((1 + 4 * x + x ^ 2) / (2 * x))) (-1)).IsSolution
        (LinearRecurrence.quadraticRescale x
          (fun k ↦ (polynomial k).eval x)) := by
    convert hnormalized using 1
    · field_simp [hx]
  have hclosed := congrFun
    (LinearRecurrence.isSolution_eq_quadraticChebyshevSolution hnormalized') n
  simpa only [LinearRecurrence.quadraticRescale, polynomial, eval_one, one_div,
    pow_zero, pow_one, div_one, eval_add, eval_mul, eval_ofNat, eval_X,
    eval_pow] using hclosed

private lemma isCoprime_X_add_C_of_eval {p : ℝ[X]} (a : ℝ)
    (h : p.eval (-a) ≠ 0) : IsCoprime (X + C a) p := by
  have : X + C a = X - C (-a) := by simp
  rw [this, (irreducible_X_sub_C (-a)).coprime_iff_not_dvd, dvd_iff_isRoot]
  exact h

private lemma isCoprime_polynomial_succ (n : ℕ) :
    IsCoprime (polynomial n) (polynomial (n + 1)) := by
  induction n with
  | zero => simp only [polynomial]; exact isCoprime_one_left
  | succ n ih =>
    have hX : IsCoprime (polynomial (n+1)) (X ^ 2) := by
      apply IsCoprime.pow_right
      have := isCoprime_X_add_C_of_eval (p := polynomial (n+1)) 0 (by simp [eval_zero_polynomial])
      simpa using this.symm
    have h2 : IsCoprime (polynomial (n + 1)) (-(X ^ 2 * polynomial n)) :=
      (hX.mul_right ih.symm).neg_right
    have := h2.add_mul_left_right (1 + 4 * X + X ^ 2)
    rw [polynomial_add_two]
    convert this using 1; ring

/-- `H_n` and `P_{n+1}` have no common root (so the interlacing is root-disjoint). -/
theorem isCoprime_halfStep_polynomial_succ (n : ℕ) :
    IsCoprime ((1 + X) * polynomial n) (polynomial (n + 1)) := by
  refine IsCoprime.mul_left ?_ (isCoprime_polynomial_succ n)
  have := isCoprime_X_add_C_of_eval (p := polynomial (n + 1)) 1
    (by rw [eval_neg_one_polynomial]; simp)
  simpa [add_comm] using this


section
open Real

private lemma cos_eq_half (φ : ℝ) : cos φ = 1 - 2 * sin (φ / 2) ^ 2 := by
  have h := Real.cos_two_mul (φ / 2)
  have htwo : 2 * (φ / 2) = φ := by ring
  rw [htwo] at h
  nlinarith [Real.sin_sq_add_cos_sq (φ/2)]

private def tpar (φ : ℝ) : ℝ := sin (φ / 2) + √(sin (φ / 2) ^ 2 + 1)
private def xpar (φ : ℝ) : ℝ := -(tpar φ) ^ 2

private lemma tpar_pos (φ : ℝ) : 0 < tpar φ := by
  unfold tpar
  have h1 : |sin (φ/2)| < √(sin (φ / 2) ^ 2 + 1) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have := neg_abs_le (sin (φ/2)); linarith

private lemma tpar_eq (φ : ℝ) : tpar φ ^ 2 = 2 * sin (φ / 2) * tpar φ + 1 := by
  unfold tpar
  have hnonneg : (0 : ℝ) ≤ sin (φ / 2) ^ 2 + 1 := by positivity
  have := Real.sq_sqrt hnonneg
  nlinarith

private lemma xpar_key (φ : ℝ) : xpar φ ^ 2 + 4 * xpar φ + 1 = 2 * cos φ * xpar φ := by
  have h := tpar_eq φ
  unfold xpar
  rw [cos_eq_half]
  set t := tpar φ; set s := sin (φ / 2)
  linear_combination (t ^ 2 + 2 * s * t - 1) * h

private lemma xpar_zero : xpar 0 = -1 := by simp [xpar, tpar]

private lemma tpar_strictMonoOn : StrictMonoOn tpar (Set.Icc (-π) π) := by
  intro a ha b hb hab
  have hs : sin (a/2) < sin (b/2) := by
    apply Real.strictMonoOn_sin
    · constructor <;> linarith [ha.1, ha.2]
    · constructor <;> linarith [hb.1, hb.2]
    · linarith
  have ea := tpar_eq a; have eb := tpar_eq b
  have pa := tpar_pos a; have pb := tpar_pos b
  by_contra hc; push Not at hc
  -- s = (t^2-1)/(2t) monotone in t
  have : sin (b/2) * (2 * tpar a * tpar b) ≤ sin (a/2) * (2 * tpar a * tpar b) := by
    nlinarith [mul_pos pa pb]
  have := le_of_mul_le_mul_right this (by positivity)
  linarith

private lemma xpar_strictAntiOn : StrictAntiOn xpar (Set.Icc (-π) π) := by
  intro a ha b hb hab
  have := tpar_strictMonoOn ha hb hab
  have := tpar_pos a
  unfold xpar; nlinarith

private lemma eval_polynomial_mul_cos (x φ : ℝ)
    (h : x ^ 2 + 4 * x + 1 = 2 * cos φ * x) (n : ℕ) :
    (polynomial n).eval x * cos (φ / 2) = x ^ n * cos ((2 * n + 1) * φ / 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [polynomial]
  | 1 =>
    have e : (2 * ((1:ℕ):ℝ) + 1) * φ / 2 = φ / 2 + φ := by push_cast; ring
    have hs : sin φ = 2 * sin (φ/2) * cos (φ/2) := by
      rw [← Real.sin_two_mul]; ring_nf
    rw [e, cos_add, hs]
    simp only [polynomial, eval_add, eval_mul, eval_pow, eval_X, eval_one, eval_ofNat]
    have : 1 + 3 * x + x ^ 2 = x * (2 * cos φ - 1) := by linarith
    rw [this, cos_eq_half]
    ring
  | n + 2 =>
    have h1 := ih (n+1) (by lia)
    have h0 := ih n (by lia)
    set A := (2 * ((n+1 : ℕ):ℝ) + 1) * φ / 2
    have e2 : (2 * ((n+2 : ℕ):ℝ) + 1) * φ / 2 = A + φ := by simp only [A]; push_cast; ring
    have e0 : (2 * ((n : ℕ):ℝ) + 1) * φ / 2 = A - φ := by simp only [A]; push_cast; ring
    rw [e0] at h0
    rw [e2, polynomial_add_two]
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_one, eval_ofNat]
    have : (1 + 4 * x + x ^ 2) = 2 * cos φ * x := by linarith
    rw [this, cos_add]
    have h0' := h0; rw [cos_sub] at h0'
    linear_combination (2 * cos φ * x) * h1 - x ^ 2 * h0'

end

section
open Real

private lemma Polynomial.splits_iff_card_roots.mpr_finset
    (p : ℝ[X]) (hp : p ≠ 0) (S : Finset ℝ)
    (hS : ∀ r ∈ S, p.IsRoot r) (hcard : p.natDegree ≤ S.card) : p.Splits := by
  rw [splits_iff_card_roots]
  have h1 : S.card ≤ p.roots.card := by
    have : S.val ≤ p.roots :=
      (Multiset.le_iff_subset S.nodup).2 fun r hr => (mem_roots hp).2 (hS r hr)
    simpa using Multiset.card_le_card this
  have h2 := card_roots' p
  lia

private lemma exists_root_between (p : ℝ[X]) {x y : ℝ} (hxy : x < y)
    (h : p.eval x * p.eval y < 0) :
    ∃ r ∈ Set.Ioo x y, p.IsRoot r := by
  have hxzero : p.eval x ≠ 0 := by
    rintro h'
    simp [h'] at h
  rcases lt_or_gt_of_ne hxzero with hx | hx
  · have hy : 0 < p.eval y := by nlinarith
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo hxy.le p.continuous.continuousOn ⟨hx, hy⟩
    exact ⟨r, hr, hr0⟩
  · have hy : p.eval y < 0 := by nlinarith
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' hxy.le p.continuous.continuousOn ⟨hy, hx⟩
    exact ⟨r, hr, hr0⟩

private lemma alt_mul_neg {s u v : ℝ} (j : ℕ)
    (hu : 0 < (-1) ^ j * s * u) (hv : 0 < (-1) ^ (j + 1) * s * v) :
    u * v < 0 := by
  have h := mul_pos hu hv
  have e : (-1 : ℝ) ^ j * s * u * ((-1) ^ (j + 1) * s * v) =
      -(((-1 : ℝ) ^ j) ^ 2 * s ^ 2 * (u * v)) := by
    ring
  rw [e, ← pow_mul, mul_comm j 2, pow_mul] at h
  norm_num at h
  by_contra hc; push Not at hc
  nlinarith [sq_nonneg s]

private lemma roots_of_alt_inc (p : ℝ[X]) (s : ℝ) (a : ℕ → ℝ) (N : ℕ)
    (ha : ∀ j < N, a j < a (j + 1))
    (hs : ∀ j ≤ N, 0 < (-1) ^ j * s * p.eval (a j)) :
    ∃ S : Finset ℝ, S.card = N ∧ a 0 ≤ a N ∧
      ∀ r ∈ S, p.IsRoot r ∧ a 0 < r ∧ r < a N := by
  induction N with
  | zero => exact ⟨∅, rfl, le_rfl, by simp⟩
  | succ N ih =>
    obtain ⟨S, hc, h0, hS⟩ := ih (fun j hj => ha j (by lia)) (fun j hj => hs j (by lia))
    have hlt := ha N (by lia)
    obtain ⟨r, hr, hroot⟩ := exists_root_between p hlt
      (alt_mul_neg N (hs N (by lia)) (hs (N+1) le_rfl))
    have hnot : r ∉ S := fun h => by linarith [(hS r h).2.2, hr.1]
    refine ⟨insert r S, by rw [Finset.card_insert_of_notMem hnot, hc], by linarith, ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨hroot, by linarith [hr.1], hr.2⟩
    · obtain ⟨h1, h2, h3⟩ := hS x hx
      exact ⟨h1, h2, by linarith⟩

private lemma roots_of_alt_dec (p : ℝ[X]) (s : ℝ) (a : ℕ → ℝ) (N : ℕ)
    (ha : ∀ j < N, a (j + 1) < a j)
    (hs : ∀ j ≤ N, 0 < (-1) ^ j * s * p.eval (a j)) :
    ∃ S : Finset ℝ, S.card = N ∧ a N ≤ a 0 ∧
      ∀ r ∈ S, p.IsRoot r ∧ a N < r ∧ r < a 0 := by
  induction N with
  | zero => exact ⟨∅, rfl, le_rfl, by simp⟩
  | succ N ih =>
    obtain ⟨S, hc, h0, hS⟩ := ih (fun j hj => ha j (by lia)) (fun j hj => hs j (by lia))
    have hlt := ha N (by lia)
    obtain ⟨r, hr, hroot⟩ := exists_root_between p hlt
      (by rw [mul_comm]; exact alt_mul_neg N (hs N (by lia)) (hs (N+1) le_rfl))
    have hnot : r ∉ S := fun h => by linarith [(hS r h).2.1, hr.2]
    refine ⟨insert r S, by rw [Finset.card_insert_of_notMem hnot, hc], by linarith, ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨hroot, hr.1, by linarith [hr.2]⟩
    · obtain ⟨h1, h2, h3⟩ := hS x hx
      exact ⟨h1, by linarith, h3⟩

private lemma cos_half_pos {φ : ℝ} (h1 : -π < φ) (h2 : φ < π) : 0 < cos (φ / 2) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

/-- Angles at which `polynomial n` vanishes. -/
private def ang (n k : ℕ) : ℝ := ((2 * k + 1 : ℝ) - 2 * n) * π / (2 * n + 1)

private lemma ang_mem (n k : ℕ) (hk : k < 2 * n) : -π < ang n k ∧ ang n k < π := by
  unfold ang
  have hk' : (k : ℝ) + 1 ≤ 2 * n := by exact_mod_cast hk
  have hpos : (0:ℝ) < 2 * n + 1 := by positivity
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith [Real.pi_pos, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  · rw [div_lt_iff₀ hpos]; nlinarith [Real.pi_pos, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]

private lemma isRoot_polynomial_ang (n k : ℕ) (hk : k < 2 * n) :
    (polynomial n).IsRoot (xpar (ang n k)) := by
  obtain ⟨h1, h2⟩ := ang_mem n k hk
  have h := eval_polynomial_mul_cos _ _ (xpar_key (ang n k)) n
  have hc : cos ((2 * n + 1) * ang n k / 2) = 0 := by
    have e : (2 * n + 1) * ang n k / 2 = π / 2 + ((k : ℤ) - n : ℤ) * π := by
      unfold ang; field_simp; push_cast; ring
    rw [e, cos_add_int_mul_pi, cos_pi_div_two, mul_zero]
  rw [hc, mul_zero] at h
  exact (mul_eq_zero.1 h).resolve_right (cos_half_pos h1 h2).ne'

/-- **A297191 is real-rooted.**  (Hint: with `u = X + 1/X`, `P_n = X^n R_n(u)` and
`R_{n+2} = (u+4) R_{n+1} - R_n`, a Chebyshev-type recurrence in `w = (u+4)/2`: `R_n = U_n(w) -
U_{n-1}(w)`.  Roots: `X + 1/X = 2 cos θ - 4` with `θ = (2k+1)π/(2n+1)`.) -/
theorem splits_polynomial (n : ℕ) : (polynomial n).Splits := by
  refine Polynomial.splits_iff_card_roots.mpr_finset _ (monic_natDegree_polynomial n).1.ne_zero
    ((Finset.range (2 * n)).image (fun k => xpar (ang n k))) ?_ ?_
  · intro r hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hr
    exact isRoot_polynomial_ang n k (Finset.mem_range.1 hk)
  · rw [Finset.card_image_of_injOn, Finset.card_range, natDegree_polynomial]
    intro k1 hk1 k2 hk2 heq
    have m1 := ang_mem n k1 (Finset.mem_range.1 hk1)
    have m2 := ang_mem n k2 (Finset.mem_range.1 hk2)
    have := xpar_strictAntiOn.injOn ⟨m1.1.le, m1.2.le⟩ ⟨m2.1.le, m2.2.le⟩ heq
    unfold ang at this
    have hpos : (0:ℝ) < 2 * n + 1 := by positivity
    field_simp at this
    have : (k1 : ℝ) = k2 := by nlinarith [Real.pi_pos]
    exact_mod_cast this

end

section
open Real

/-- Sample angles for the half-step pencil: `0` and the positive zero-angles of `polynomial n`. -/
private def cang (n j : ℕ) : ℝ := if j = 0 then 0 else (2 * j - 1) * π / (2 * n + 1)

private lemma cang_mem (n j : ℕ) (hj : j ≤ n) : 0 ≤ cang n j ∧ cang n j < π := by
  unfold cang
  split_ifs with h
  · exact ⟨le_rfl, Real.pi_pos⟩
  · have hj1 : (1:ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h
    have hj' : (j:ℝ) ≤ n := by exact_mod_cast hj
    have hpos : (0:ℝ) < 2 * n + 1 := by positivity
    constructor
    · apply div_nonneg _ hpos.le; nlinarith [Real.pi_pos]
    · rw [div_lt_iff₀ hpos]; nlinarith [Real.pi_pos]

private lemma cang_lt (n j : ℕ) : cang n j < cang n (j + 1) := by
  have hpos : (0:ℝ) < 2 * n + 1 := by positivity
  have e : cang n (j + 1) = (2 * ((j + 1 : ℕ) : ℝ) - 1) * π / (2 * n + 1) := by
    simp only [cang, Nat.add_one_ne_zero, ite_false]
  rw [e]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [cang, ite_true]; push_cast; apply div_pos _ hpos; nlinarith [Real.pi_pos]
  · simp only [cang, hj.ne', ite_false]
    rw [div_lt_div_iff_of_pos_right hpos]; push_cast; nlinarith [Real.pi_pos]

private lemma cos_eq_of_pm {c φ : ℝ} (hφ : φ = c ∨ φ = -c) (m : ℝ) :
    cos (m * φ / 2) = cos (m * c / 2) := by
  rcases hφ with rfl | rfl
  · rfl
  · have harg : m * -c / 2 = -(m * c / 2) := by ring
    rw [harg, cos_neg]

private lemma pencil_H_zero (n j : ℕ) (hj : j ≤ n) (φ : ℝ)
    (hφ : φ = cang n j ∨ φ = -cang n j) :
    ((1 + X) * polynomial n).eval (xpar φ) = 0 := by
  obtain ⟨c0, c1⟩ := cang_mem n j hj
  have hm : -π < φ ∧ φ < π := by rcases hφ with rfl | rfl <;> constructor <;> linarith
  rw [eval_mul]
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · have : φ = 0 := by simpa [cang] using hφ
    subst this; simp [xpar_zero]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by lia⟩
    have h := eval_polynomial_mul_cos _ _ (xpar_key φ) n
    rw [cos_eq_of_pm hφ] at h
    have hc : cos ((2 * n + 1) * cang n (i+1) / 2) = 0 := by
      have e : (2 * n + 1) * cang n (i+1) / 2 = π / 2 + (i : ℕ) * π := by
        unfold cang; simp only [Nat.add_one_ne_zero, ite_false]; field_simp; push_cast; ring
      rw [e, cos_add_nat_mul_pi, cos_pi_div_two, mul_zero]
    have := cos_half_pos hm.1 hm.2
    rw [hc, mul_zero] at h
    rw [(mul_eq_zero.1 h).resolve_right this.ne', mul_zero]

private lemma pencil_P_sign (n j : ℕ) (hj : j ≤ n) (φ : ℝ)
    (hφ : φ = cang n j ∨ φ = -cang n j) :
    0 < (-1) ^ j * (-1) ^ (n + 1) * (polynomial (n + 1)).eval (xpar φ) := by
  obtain ⟨c0, c1⟩ := cang_mem n j hj
  have hm : -π < φ ∧ φ < π := by rcases hφ with rfl | rfl <;> constructor <;> linarith
  have h := eval_polynomial_mul_cos _ _ (xpar_key φ) (n + 1)
  rw [cos_eq_of_pm hφ] at h
  have hcp := cos_half_pos hm.1 hm.2
  have hsgn : 0 < (-1) ^ j * cos ((2 * ((n + 1 : ℕ) : ℝ) + 1) * cang n j / 2) := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp [cang]
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by lia⟩
      have c0' : 0 < cang n (i+1) := lt_of_le_of_lt (cang_mem n i (by lia)).1 (cang_lt n i)
      have e : (2 * ((n + 1 : ℕ) : ℝ) + 1) * cang n (i+1) / 2
          = (cang n (i+1) + π / 2) + (i : ℕ) * π := by
        have : (2 * (n : ℝ) + 1) * cang n (i+1) / 2 = π / 2 + i * π := by
          unfold cang; simp only [Nat.add_one_ne_zero, ite_false]; field_simp; push_cast; ring
        push_cast; linear_combination this
      rw [e, cos_add_nat_mul_pi, cos_add_pi_div_two]
      have hs := Real.sin_pos_of_pos_of_lt_pi c0' c1
      have : (-1:ℝ) ^ (i + 1) * ((-1) ^ i * -sin (cang n (i + 1))) =
          ((-1:ℝ) ^ i) ^ 2 * sin (cang n (i+1)) := by ring
      rw [this, ← pow_mul, mul_comm i 2, pow_mul]; norm_num; exact hs
  have hx : xpar φ ^ (n + 1) = (-1) ^ (n + 1) * (tpar φ ^ 2) ^ (n + 1) := by
    unfold xpar; rw [neg_eq_neg_one_mul, mul_pow]
  rw [hx] at h
  have ht : 0 < (tpar φ ^ 2) ^ (n + 1) := by have := tpar_pos φ; positivity
  have key : (-1) ^ j * (-1) ^ (n + 1) * (polynomial (n + 1)).eval (xpar φ) * cos (φ / 2) =
      (tpar φ ^ 2) ^ (n + 1) *
        ((-1) ^ j * cos ((2 * ((n + 1 : ℕ) : ℝ) + 1) * cang n j / 2)) := by
    rw [mul_assoc _ ((polynomial (n + 1)).eval (xpar φ)), h]
    have : ((-1 : ℝ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    linear_combination
      ((tpar φ ^ 2) ^ (n + 1) *
        ((-1) ^ j * cos ((2 * ((n + 1 : ℕ) : ℝ) + 1) * cang n j / 2))) * this
  have : 0 < (-1) ^ j * (-1) ^ (n + 1) * (polynomial (n + 1)).eval (xpar φ) * cos (φ / 2) := by
    rw [key]; positivity
  exact pos_of_mul_pos_left this hcp.le

end

section
open Real Filter

private lemma neg_cang_mem (n j : ℕ) (hj : j ≤ n) : -cang n j ∈ Set.Icc (-π) π := by
  obtain ⟨h1, h2⟩ := cang_mem n j hj; constructor <;> linarith

private lemma cang_mem' (n j : ℕ) (hj : j ≤ n) : cang n j ∈ Set.Icc (-π) π := by
  obtain ⟨h1, h2⟩ := cang_mem n j hj; constructor <;> linarith

private lemma pencil_normalized_splits (n : ℕ) (a : ℝ) :
    (C a * ((1 + X) * polynomial n) + polynomial (n + 1)).Splits := by
  set G := C a * ((1 + X) * polynomial n) + polynomial (n + 1) with hGdef
  have hH : (C a * ((1 + X) * polynomial n)).natDegree ≤ 2 * n + 1 := by
    refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
    have : (1 + X : ℝ[X]).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (by simp)
    rw [natDegree_polynomial]; lia
  have hdeglt : (C a * ((1 + X) * polynomial n)).degree < (polynomial (n + 1)).degree :=
    degree_lt_degree (by rw [natDegree_polynomial]; lia)
  have hlead : G.leadingCoeff = 1 := by
    rw [hGdef, leadingCoeff_add_of_degree_lt hdeglt]; exact (monic_natDegree_polynomial _).1
  have hdeg : G.natDegree = 2 * n + 2 := by
    rw [hGdef, natDegree_add_eq_right_of_degree_lt hdeglt, natDegree_polynomial]; ring
  have hval : ∀ j ≤ n, ∀ φ, (φ = cang n j ∨ φ = -cang n j) →
      G.eval (xpar φ) = (polynomial (n + 1)).eval (xpar φ) := by
    intro j hj φ hφ
    rw [hGdef, eval_add, eval_mul, pencil_H_zero n j hj φ hφ]; simp
  -- behaviour at `+∞`
  have htop := tendsto_atTop_of_leadingCoeff_nonneg G
    (natDegree_pos_iff_degree_pos.1 (by lia)) (by rw [hlead]; norm_num)
  obtain ⟨M, hM1, hM2⟩ := ((htop.eventually_gt_atTop 0).and
    (eventually_gt_atTop (xpar (-cang n n)))).exists
  -- behaviour at `-∞`
  have hlead' : (G.comp (-X)).leadingCoeff = 1 := by
    rw [leadingCoeff_comp (by simp), hlead, leadingCoeff_neg, leadingCoeff_X, hdeg]
    rw [pow_add, pow_mul]; norm_num
  have hdeg' : (G.comp (-X)).natDegree = 2 * n + 2 := by
    rw [natDegree_comp, hdeg]; simp
  have hbot := tendsto_atTop_of_leadingCoeff_nonneg (G.comp (-X))
    (natDegree_pos_iff_degree_pos.1 (by lia)) (by rw [hlead']; norm_num)
  obtain ⟨y, hy1, hy2⟩ := ((hbot.eventually_gt_atTop 0).and
    (eventually_gt_atTop (-xpar (cang n n)))).exists
  simp only [eval_comp, eval_neg, eval_X] at hy1
  have hG0 : G ≠ 0 := by rintro h; rw [h] at hM1; simp at hM1
  -- right branch
  obtain ⟨SR, hSRc, -, hSR⟩ := roots_of_alt_inc G ((-1) ^ (n + 1))
    (fun j => if j ≤ n then xpar (-cang n j) else M) (n + 1)
    (by
      intro j hj
      by_cases hjn : j < n
      · simp only [show j ≤ n by lia, show j + 1 ≤ n by lia, ite_true]
        exact xpar_strictAntiOn (neg_cang_mem n (j+1) (by lia)) (neg_cang_mem n j (by lia))
          (neg_lt_neg (cang_lt n j))
      · have hjeq : j = n := by lia
        subst j
        have hnot : ¬ (n + 1 ≤ n) := by lia
        simp only [le_refl, ite_true, hnot, ite_false]
        exact hM2)
    (by
      intro j hj
      by_cases hjn : j ≤ n
      · simp only [hjn, ite_true]
        rw [hval j hjn _ (Or.inr rfl)]; exact pencil_P_sign n j hjn _ (Or.inr rfl)
      · obtain rfl : j = n + 1 := by lia
        simp only [hjn, ite_false]
        rw [← mul_pow]; norm_num; exact hM1)
  -- left branch
  obtain ⟨SL, hSLc, -, hSL⟩ := roots_of_alt_dec G ((-1) ^ (n + 1))
    (fun j => if j ≤ n then xpar (cang n j) else -y) (n + 1)
    (by
      intro j hj
      by_cases hjn : j < n
      · simp only [show j ≤ n by lia, show j + 1 ≤ n by lia, ite_true]
        exact xpar_strictAntiOn (cang_mem' n j (by lia)) (cang_mem' n (j+1) (by lia))
          (cang_lt n j)
      · have hjeq : j = n := by lia
        subst j
        have hnot : ¬ (n + 1 ≤ n) := by lia
        simp only [le_refl, ite_true, hnot, ite_false]
        linarith)
    (by
      intro j hj
      by_cases hjn : j ≤ n
      · simp only [hjn, ite_true]
        rw [hval j hjn _ (Or.inl rfl)]; exact pencil_P_sign n j hjn _ (Or.inl rfl)
      · obtain rfl : j = n + 1 := by lia
        simp only [hjn, ite_false]
        rw [← mul_pow]; norm_num; exact hy1)
  simp only [Nat.zero_le, ite_true, cang, neg_zero, xpar_zero] at hSR hSL
  have hdisj : Disjoint SL SR := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    linarith [(hSL r h1).2.2, (hSR r h2).2.1]
  refine Polynomial.splits_iff_card_roots.mpr_finset G hG0 (SL ∪ SR) ?_ ?_
  · intro r hr
    rcases Finset.mem_union.1 hr with h | h
    · exact (hSL r h).1
    · exact (hSR r h).1
  · rw [Finset.card_union_of_disjoint hdisj, hSLc, hSRc, hdeg]; lia

private lemma one_add_X_splits : (1 + X : ℝ[X]).Splits := by
  rw [show (1 + X : ℝ[X]) = X - C (-1) by simp [add_comm]]
  exact Splits.X_sub_C _

/-- **Half-step chain.**  With `H_n = (1+X) P_n`, every real combination of `H_n` and `P_{n+1}`
is real-rooted (or zero): `H_n ≺ P_{n+1}` in the Obreschkoff sense (degrees `2n+1`, `2n+2`).
The other half step `P_n ≺ H_n` is trivial since `α P_n + β (1+X) P_n = P_n (α + β(1+X))`. -/
theorem allComboRealRooted_halfStep_polynomial_succ (n : ℕ) :
    AllComboRealRooted ((1 + X) * polynomial n) (polynomial (n + 1)) := by
  intro α β
  by_cases hβ : β = 0
  · subst hβ
    simp only [C_0, zero_mul, add_zero]
    exact (one_add_X_splits.mul (splits_polynomial n)).C_mul α
  · have e : C α * ((1 + X) * polynomial n) + C β * polynomial (n + 1) =
        C β * (C (α / β) * ((1 + X) * polynomial n) + polynomial (n + 1)) := by
      rw [mul_add, ← mul_assoc (C β), ← C_mul, mul_div_cancel₀ _ hβ]
    rw [e]
    exact (pencil_normalized_splits n (α / β)).C_mul β

end

/-- Every real combination of `Pₙ` and `(1 + X)Pₙ` splits. -/
theorem allComboRealRooted_polynomial_halfStep (n : ℕ) :
    AllComboRealRooted (polynomial n) ((1 + X) * polynomial n) := by
  intro α β
  have hfactor : C α * polynomial n + C β * ((1 + X) * polynomial n) =
      polynomial n * (C α + C β * (1 + X)) := by
    ring
  rw [hfactor]
  exact (splits_polynomial n).mul
    (Splits.of_natDegree_le_one (by compute_degree!))

/-- Each A297191 row strictly interlaces its `(1 + X)` half-step. -/
theorem strictInterl_polynomial_halfStep (n : ℕ) :
    StrictInterl (polynomial n) ((1 + X) * polynomial n) := by
  have hlinearMonic : (1 + X : ℝ[X]).Monic := by monicity!
  have hhalfMonic := hlinearMonic.mul (monic_polynomial n)
  have hdegree : ((1 + X) * polynomial n).natDegree =
      (polynomial n).natDegree + 1 := by
    have hlinearDegree : (1 + X : ℝ[X]).natDegree = 1 := by compute_degree!
    rw [hlinearMonic.natDegree_mul (monic_polynomial n), natDegree_polynomial,
      hlinearDegree]
    ring
  have horientation := strictInterl_of_allComboRealRooted
    (monic_polynomial n).ne_zero (splits_polynomial n) hhalfMonic.ne_zero
    (one_add_X_splits.mul (splits_polynomial n))
    (allComboRealRooted_polynomial_halfStep n) (Or.inl hdegree.symm)
  exact StrictInterl.forward_of_orientation_of_succDegree hdegree horientation

/-- The half-step `(1 + X)Pₙ` strictly interlaces `Pₙ₊₁`. -/
theorem strictInterl_halfStep_polynomial_succ (n : ℕ) :
    StrictInterl ((1 + X) * polynomial n) (polynomial (n + 1)) := by
  have hlinearMonic : (1 + X : ℝ[X]).Monic := by monicity!
  have hhalfMonic := hlinearMonic.mul (monic_polynomial n)
  have hdegree : (polynomial (n + 1)).natDegree =
      ((1 + X) * polynomial n).natDegree + 1 := by
    have hlinearDegree : (1 + X : ℝ[X]).natDegree = 1 := by compute_degree!
    rw [natDegree_polynomial,
      hlinearMonic.natDegree_mul (monic_polynomial n), natDegree_polynomial,
      hlinearDegree]
    ring
  have horientation := strictInterl_of_allComboRealRooted
    hhalfMonic.ne_zero (one_add_X_splits.mul (splits_polynomial n))
    (monic_polynomial (n + 1)).ne_zero (splits_polynomial (n + 1))
    (allComboRealRooted_halfStep_polynomial_succ n) (Or.inl hdegree.symm)
  exact StrictInterl.forward_of_orientation_of_succDegree hdegree horientation

/-- Every A297191 row has simple roots. -/
theorem hasSimpleRoots_polynomial (n : ℕ) : HasSimpleRoots (polynomial n) := by
  cases n with
  | zero =>
      intro r hr
      simp [polynomial, Polynomial.IsRoot.def] at hr
  | succ n =>
      exact ((strictInterl_halfStep_polynomial_succ n).hasSimpleRoots_of_isCoprime
        (isCoprime_halfStep_polynomial_succ n)).2

/-- Row `n` has exactly `2n` roots, counted with multiplicity. -/
theorem roots_card_polynomial (n : ℕ) : (polynomial n).roots.card = 2 * n := by
  rw [Polynomial.splits_iff_card_roots.mp (splits_polynomial n), natDegree_polynomial]


/-- The A054142 gamma polynomial whose transform is the A297191 row. -/
def gammaPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      (1 + 2 * X) * gammaPolynomial (n + 1) +
        (-1 * X ^ 2) * gammaPolynomial n

private lemma gammaPolynomial_add_two (n : ℕ) :
    gammaPolynomial (n + 2) =
      (1 + 2 * X) * gammaPolynomial (n + 1) +
        (-1 * X ^ 2) * gammaPolynomial n :=
  rfl

private lemma coeff_gammaPolynomial_add_two (n m : ℕ) :
    (gammaPolynomial (n + 2)).coeff (m + 2) =
      (gammaPolynomial (n + 1)).coeff (m + 2) +
        2 * (gammaPolynomial (n + 1)).coeff (m + 1) -
          (gammaPolynomial n).coeff m := by
  rw [gammaPolynomial_add_two]
  simp only [coeff_add, add_mul, one_mul]
  rw [show (2 * X : ℝ[X]) = C 2 * X by rw [map_ofNat],
    show (-1 * X ^ 2 : ℝ[X]) = C (-1) * X ^ 2 by simp,
    mul_assoc, coeff_C_mul, coeff_X_mul, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul]
  ring

private lemma choose_gammaPolynomial_sub (n k : ℕ) :
    Nat.choose (2 * n + 2 - k) (k + 2) + Nat.choose (2 * n - k) k =
      Nat.choose (2 * n - k) (k + 2) +
        2 * Nat.choose (2 * n + 1 - k) (k + 1) := by
  by_cases hk : k ≤ 2 * n
  · have h1 : 2 * n + 1 - k = (2 * n - k) + 1 := by lia
    have h2 : 2 * n + 2 - k = (2 * n - k) + 2 := by lia
    grind
  · grind

private lemma choose_gammaPolynomial_sub_real (n k : ℕ) :
    (Nat.choose (2 * n + 2 - k) (k + 2) : ℝ) =
      (Nat.choose (2 * n - k) (k + 2) : ℝ) +
        2 * (Nat.choose (2 * n + 1 - k) (k + 1) : ℝ) -
          (Nat.choose (2 * n - k) k : ℝ) := by
  have hnat := choose_gammaPolynomial_sub n k
  have hreal : (Nat.choose (2 * n + 2 - k) (k + 2) : ℝ) +
      (Nat.choose (2 * n - k) k : ℝ) =
      (Nat.choose (2 * n - k) (k + 2) : ℝ) +
        2 * (Nat.choose (2 * n + 1 - k) (k + 1) : ℝ) := by
    exact_mod_cast hnat
  linarith

private lemma coeff_zero_gammaPolynomial (n : ℕ) :
    (gammaPolynomial n).coeff 0 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => simp [gammaPolynomial]
      | 1 => simp [gammaPolynomial]
      | n + 2 =>
          simpa [gammaPolynomial_add_two, coeff_mul] using ih (n + 1) (by lia)

private lemma coeff_one_gammaPolynomial_step (n : ℕ) :
    (gammaPolynomial (n + 2)).coeff 1 =
      (gammaPolynomial (n + 1)).coeff 1 +
        2 * (gammaPolynomial (n + 1)).coeff 0 := by
  rw [gammaPolynomial_add_two]
  rw [show (1 + 2 * X : ℝ[X]) * gammaPolynomial (n + 1) +
      (-1 * X ^ 2) * gammaPolynomial n =
      gammaPolynomial (n + 1) + 2 * (X * gammaPolynomial (n + 1)) -
        X ^ 2 * gammaPolynomial n by ring]
  simp [coeff_X_pow_mul']

private lemma coeff_one_gammaPolynomial (n : ℕ) :
    (gammaPolynomial n).coeff 1 = (2 * n - 1 : ℕ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 =>
          rw [gammaPolynomial]
          rw [coeff_one]
          norm_num
      | 1 => norm_num [gammaPolynomial, coeff_add, coeff_one, coeff_X]
      | n + 2 =>
          rw [coeff_one_gammaPolynomial_step, ih (n + 1) (by lia),
            coeff_zero_gammaPolynomial]
          norm_num
          ring

private lemma coeff_gammaPolynomial_eq_choose (n k : ℕ) :
    (gammaPolynomial n).coeff k = (Nat.choose (2 * n - k) k : ℝ) := by
  revert k
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro k
      match n with
      | 0 =>
          rcases k with _ | k <;> simp [gammaPolynomial, coeff_one]
      | 1 =>
          rcases k with _ | _ | k <;>
            simp [gammaPolynomial, coeff_add, coeff_one, coeff_X]
      | n + 2 =>
          cases k with
          | zero => simp [coeff_zero_gammaPolynomial]
          | succ k =>
              cases k with
              | zero =>
                  rw [coeff_one_gammaPolynomial]
                  norm_num
              | succ k =>
                  rw [coeff_gammaPolynomial_add_two,
                    ih (n + 1) (by lia) (k + 2),
                    ih (n + 1) (by lia) (k + 1), ih n (by lia) k]
                  have hfirst : 2 * (n + 1) - (k + 2) = 2 * n - k := by lia
                  have hsecond : 2 * (n + 1) - (k + 1) = 2 * n + 1 - k := by lia
                  have hthird :
                      2 * (n + 2) - (k + 1 + 1) = 2 * n + 2 - k := by
                    lia
                  rw [hfirst, hsecond, hthird]
                  exact (choose_gammaPolynomial_sub_real n k).symm

/-- The A297191 gamma polynomial has degree `n`. -/
theorem natDegree_gammaPolynomial (n : ℕ) : (gammaPolynomial n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_gammaPolynomial_eq_choose]
    exact_mod_cast Nat.choose_eq_zero_of_lt (by lia : 2 * n - k < k)
  · rw [coeff_gammaPolynomial_eq_choose]
    have hsub : 2 * n - n = n := by lia
    rw [hsub, Nat.choose_self]
    norm_num

private lemma hasPosLeadingCoeff_gammaPolynomial (n : ℕ) :
    HasPosLeadingCoeff (gammaPolynomial n) := by
  rw [HasPosLeadingCoeff, leadingCoeff, natDegree_gammaPolynomial,
    coeff_gammaPolynomial_eq_choose]
  have hsub : 2 * n - n = n := by lia
  rw [hsub, Nat.choose_self]
  norm_num

/-- The A297191 gamma polynomial has nonnegative coefficients. -/
theorem hasNonnegCoeffs_gammaPolynomial (n : ℕ) :
    HasNonnegCoeffs (gammaPolynomial n) := by
  intro k
  rw [coeff_gammaPolynomial_eq_choose]
  positivity

/-- The constant coefficient of every A297191 gamma polynomial is one. -/
theorem gammaPolynomial_coeff_zero (n : ℕ) :
    (gammaPolynomial n).coeff 0 = 1 :=
  coeff_zero_gammaPolynomial n

private lemma eval_lag_nonpos (r : ℝ) : (-1 * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  norm_num only [eval_mul, eval_neg, eval_one, eval_pow, eval_X, one_mul]
  nlinarith [sq_nonneg r]

private theorem interlaces_gammaPolynomial_succ (n : ℕ) :
    Interlaces (gammaPolynomial n) (gammaPolynomial (n + 1)) := by
  apply threeTerm_interlaces_of_eval_nonpos
      (P := gammaPolynomial) (a := fun _ ↦ 1 + 2 * X)
      (b := fun _ ↦ -1 * X ^ 2) (D₀ := 0)
  · exact gammaPolynomial_add_two
  · intro k
    rw [natDegree_gammaPolynomial]
    lia
  · exact fun k ↦ hasPosLeadingCoeff_gammaPolynomial k
  · exact fun _ r ↦ eval_lag_nonpos r
  · exact interlaces_of_natDegree_eq_zero_of_natDegree_eq_one
      (by simp [gammaPolynomial]) (by simp [gammaPolynomial])
      (by rw [natDegree_gammaPolynomial])

/-- Consecutive A297191 gamma polynomials are in proper position. -/
theorem strictInterl_gammaPolynomial_succ (n : ℕ) :
    StrictInterl (gammaPolynomial n) (gammaPolynomial (n + 1)) :=
  (interlaces_gammaPolynomial_succ n).toStrictInterl

/-- Each A297191 row is the even gamma transform of its A054142 gamma row. -/
theorem polynomial_eq_gammaTransform (n : ℕ) :
    polynomial n = gammaTransform (2 * n) (gammaPolynomial n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => simp [polynomial, gammaPolynomial, gammaTransform]
      | 1 =>
          have hgamma : gammaTransform 2 (1 + X : ℝ[X]) = (X + 1) ^ 2 + X := by
            simp [gammaTransform, gammaBasisTerm, Finset.sum_range_succ,
              coeff_add, coeff_one, coeff_X]
          change 1 + 3 * X + X ^ 2 = gammaTransform 2 (1 + X)
          rw [hgamma]
          ring
      | n + 2 =>
          rw [polynomial, ih (n + 1) (by lia), ih n (by lia),
            gammaPolynomial_add_two]
          have hdeg :
              (gammaPolynomial (n + 1)).natDegree ≤ (2 * (n + 1)) / 2 := by
            rw [natDegree_gammaPolynomial]
            lia
          calc
            (1 + 4 * X + X ^ 2) *
                  gammaTransform (2 * (n + 1)) (gammaPolynomial (n + 1)) -
                X ^ 2 * gammaTransform (2 * n) (gammaPolynomial n) =
                gammaTransform (2 * (n + 2))
                  (gammaPolynomial (n + 1) +
                    C 2 * (X * gammaPolynomial (n + 1)) +
                      C (-1) * (X * (X * gammaPolynomial n))) := by
                have hambientSucc : 2 * (n + 2) = 2 * (n + 1) + 2 := by lia
                have hambientPrev : 2 * (n + 1) = 2 * n + 2 := by lia
                rw [gammaTransform_add, gammaTransform_add,
                  gammaTransform_C_mul, gammaTransform_C_mul]
                rw [hambientSucc, gammaTransform_pad_two hdeg,
                  gammaTransform_X_mul_two (2 * (n + 1))]
                rw [hambientPrev, gammaTransform_X_mul_two (2 * n + 2),
                  gammaTransform_X_mul_two (2 * n)]
                norm_num [map_ofNat, map_neg, map_one]
                ring
            _ = gammaTransform (2 * (n + 2))
                  ((1 + 2 * X) * gammaPolynomial (n + 1) +
                    (-1 * X ^ 2) * gammaPolynomial n) := by
                congr 1
                norm_num [map_ofNat, map_neg, map_one]
                ring

/-- Consecutive A297191 rows are joined by their missing-degree half step. -/
theorem strictInterl_polynomial_two_step (n : ℕ) :
    StrictInterl (polynomial n) ((1 + X) * polynomial n) ∧
      StrictInterl ((1 + X) * polynomial n) (polynomial (n + 1)) := by
  have h := strictInterl_gammaTransform_two_step
    (n := n) (natDegree_gammaPolynomial n).le
    (by rw [natDegree_gammaPolynomial])
    (hasNonnegCoeffs_gammaPolynomial n)
    (hasNonnegCoeffs_gammaPolynomial (n + 1))
    (by rw [gammaPolynomial_coeff_zero]; norm_num)
    (by rw [gammaPolynomial_coeff_zero]; norm_num)
    (strictInterl_gammaPolynomial_succ n)
  rw [← polynomial_eq_gammaTransform n] at h
  have hambient : 2 * n + 2 = 2 * (n + 1) := by lia
  rw [hambient, ← polynomial_eq_gammaTransform (n + 1)] at h
  simpa only [add_comm] using h

end RealRooted.Applications.OEIS.A297191
