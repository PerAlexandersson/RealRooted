import RealRooted.AissenSchoenbergWhitney
import RealRooted.Basic
import RealRooted.Bezoutian
import RealRooted.CommonInterleaverTwo
import RealRooted.Interlacing.Multiplicity
import RealRooted.Mathlib.Algebra.Polynomial.Degree.SmallDegree
import RealRooted.MaWang
import RealRooted.MultivariateStability
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

open Polynomial

noncomputable section

namespace RealRooted

theorem splits_of_discrim_nonneg {a b c : ℝ} (ha : a ≠ 0)
    (h : 0 ≤ discrim a b c) :
    (C a * X ^ 2 + C b * X + C c).Splits := by
  set s := Real.sqrt (discrim a b c) with hs
  have hs₂ : s ^ 2 = b ^ 2 - 4 * a * c := by rw [hs, Real.sq_sqrt h, discrim]
  set r₁ := (-b + s) / (2 * a) with hr₁
  set r₂ := (-b - s) / (2 * a) with hr₂
  have hprod : a * (r₁ * r₂) = c := by
    rw [hr₁, hr₂]
    field_simp
    nlinarith [hs₂]
  have hsum : a * (r₁ + r₂) = -b := by
    rw [hr₁, hr₂]
    field_simp
    ring
  have hfact : C a * X ^ 2 + C b * X + C c = C a * ((X - C r₁) * (X - C r₂)) := by
    have : C a * ((X - C r₁) * (X - C r₂))
        = C a * X ^ 2 + C (-(a * (r₁ + r₂))) * X + C (a * (r₁ * r₂)) := by
      simp only [C_mul, C_add, C_neg]
      ring
    simp_all
  simp [*]

/-- Complexification of a real polynomial. -/
def complexify (p : ℝ[X]) : ℂ[X] :=
  p.map Complex.ofRealHom

@[simp] theorem complexify_zero :
    complexify 0 = 0 := by
  simp only [complexify, Polynomial.map_zero]

@[simp] theorem complexify_one :
    complexify 1 = 1 := by
  simp [complexify]

@[simp] theorem complexify_C (a : ℝ) :
    complexify (C a) = C (a : ℂ) := by
  simp [complexify]

@[simp] theorem complexify_X :
    complexify X = X := by
  simp [complexify]

/-- A univariate complex polynomial is upper-half-plane stable if it has no root
with strictly positive imaginary part. -/
def IsUpperHalfPlaneStable (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0

/-- Evaluation commutes with Mathlib's canonical identification of a
univariate polynomial with a multivariate polynomial in one variable. -/
@[simp] theorem eval_uniqueAlgEquiv_symm_finOne (p : ℂ[X]) (z : Fin 1 → ℂ) :
    MvPolynomial.eval z ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p) =
      p.eval (z 0) := by
  change
    ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p).eval₂
        (RingHom.id ℂ) z = p.eval (z 0)
  rw [MvPolynomial.eval₂_uniqueAlgEquiv_symm]
  rfl

/-- Univariate upper-half-plane stability agrees with multivariate stability
after Mathlib's canonical `Fin 1` identification. Both predicates exclude the
zero polynomial. -/
theorem isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable (p : ℂ[X]) :
    IsUpperHalfPlaneStable p ↔
      MvUpperHalfPlaneStable
        ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p) := by
  change (∀ z : ℂ, 0 < z.im → p.eval z ≠ 0) ↔
    ∀ z : Fin 1 → ℂ, (∀ i, 0 < (z i).im) →
      MvPolynomial.eval z ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p) ≠ 0
  constructor
  · intro hp z hz
    rw [eval_uniqueAlgEquiv_symm_finOne]
    exact hp (z 0) (hz 0)
  · intro hp z hz
    simpa only [eval_uniqueAlgEquiv_symm_finOne] using
      hp (fun _ => z) (fun _ => hz)

namespace IsUpperHalfPlaneStable

/-- Multiplication transported from the general multivariate stability API. -/
theorem mul {p q : ℂ[X]} (hp : IsUpperHalfPlaneStable p)
    (hq : IsUpperHalfPlaneStable q) :
    IsUpperHalfPlaneStable (p * q) := by
  rw [isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable]
  simpa using
    ((isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable p).mp hp).mul
      ((isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable q).mp hq)

end IsUpperHalfPlaneStable

/-- A univariate complex polynomial is right-half-plane stable if it has no
root with strictly positive real part. -/
def IsRightHalfPlaneStable (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, 0 < z.re → p.eval z ≠ 0

/-- Hurwitz stability for a real polynomial in the coefficient-positive
combinatorial convention used here. -/
def IsHurwitzStable (p : ℝ[X]) : Prop :=
  HasNonnegCoeffs p ∧ IsRightHalfPlaneStable (complexify p)

namespace IsHurwitzStable

theorem hasNonnegCoeffs {p : ℝ[X]} (hp : IsHurwitzStable p) :
    HasNonnegCoeffs p :=
  hp.1

theorem rightHalfPlaneStable {p : ℝ[X]} (hp : IsHurwitzStable p) :
    IsRightHalfPlaneStable (complexify p) :=
  hp.2

end IsHurwitzStable

/-- The classical Hermite--Biehler combination `f + i g`. -/
def hermiteBiehlerPolynomial (f g : ℝ[X]) : ℂ[X] :=
  complexify f + C Complex.I * complexify g

@[simp] theorem eval_hermiteBiehlerPolynomial (f g : ℝ[X]) (z : ℂ) :
    (hermiteBiehlerPolynomial f g).eval z =
      (complexify f).eval z + Complex.I * (complexify g).eval z := by
  simp [hermiteBiehlerPolynomial]

/-! ## Odd/even polynomial used by the Hurwitz form -/

/-- The real polynomial `q(x^2) + x p(x^2)`.

This is the polynomial whose Hurwitz matrix is the two-row Lace matrix for the
odd and even parts in the Athanasiadis--Wagner setup. -/
def oddEvenPolynomial (p q : ℝ[X]) : ℝ[X] :=
  q.comp (X ^ 2) + X * p.comp (X ^ 2)

@[simp] theorem complexify_oddEvenPolynomial (p q : ℝ[X]) :
    complexify (oddEvenPolynomial p q) =
      (complexify q).comp (X ^ 2 : ℂ[X]) +
        X * (complexify p).comp (X ^ 2 : ℂ[X]) := by
  simp [complexify, oddEvenPolynomial, Polynomial.map_comp]

@[simp] theorem eval_complexify_oddEvenPolynomial (p q : ℝ[X]) (z : ℂ) :
    (complexify (oddEvenPolynomial p q)).eval z =
      (complexify q).eval (z ^ 2) + z * (complexify p).eval (z ^ 2) := by
  simp

lemma monomial_comp_X_sq (n : ℕ) (a : ℝ) :
    (Polynomial.monomial n a).comp (X ^ 2 : ℝ[X]) =
      Polynomial.monomial (2 * n) a := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [mul_comp, C_comp, pow_comp, X_comp]
  rw [show (X ^ 2 : ℝ[X]) ^ n = X ^ (2 * n) by rw [pow_mul]]
  rw [Polynomial.C_mul_X_pow_eq_monomial]

@[simp] lemma coeff_comp_X_sq_even (p : ℝ[X]) (n : ℕ) :
    (p.comp (X ^ 2 : ℝ[X])).coeff (2 * n) = p.coeff n := by
  refine Polynomial.induction_on' p ?_ ?_
  · simp_all
  · intro m a
    simp only [monomial_comp_X_sq, Polynomial.coeff_monomial,
      (by lia : 2 * m = 2 * n ↔ m = n)]

@[simp] lemma coeff_comp_X_sq_odd (p : ℝ[X]) (n : ℕ) :
    (p.comp (X ^ 2 : ℝ[X])).coeff (2 * n + 1) = 0 := by
  refine Polynomial.induction_on' p ?_ ?_
  · simp_all
  · intro m a
    simp only [monomial_comp_X_sq, Polynomial.coeff_monomial,
      (by lia : 2 * m = 2 * n + 1 ↔ False), if_false]

@[simp] lemma coeff_X_mul_comp_X_sq_even (p : ℝ[X]) (n : ℕ) :
    (X * p.comp (X ^ 2 : ℝ[X])).coeff (2 * n) = 0 := by
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by lia]
      simp

@[simp] lemma coeff_X_mul_comp_X_sq_odd (p : ℝ[X]) (n : ℕ) :
    (X * p.comp (X ^ 2 : ℝ[X])).coeff (2 * n + 1) = p.coeff n := by
  simp

@[simp] theorem coeff_oddEvenPolynomial_even (p q : ℝ[X]) (n : ℕ) :
    (oddEvenPolynomial p q).coeff (2 * n) = q.coeff n := by
  simp [oddEvenPolynomial]

@[simp] theorem coeff_oddEvenPolynomial_odd (p q : ℝ[X]) (n : ℕ) :
    (oddEvenPolynomial p q).coeff (2 * n + 1) = p.coeff n := by
  simp [oddEvenPolynomial]

/-- The odd/even construction is injective in its two polynomial inputs. -/
theorem oddEvenPolynomial_inj {p q r s : ℝ[X]}
    (h : oddEvenPolynomial p q = oddEvenPolynomial r s) :
    p = r ∧ q = s := by
  constructor
  · ext n
    have hcoeff := congrArg (fun u : ℝ[X] => u.coeff (2 * n + 1)) h
    simpa using hcoeff
  · ext n
    have hcoeff := congrArg (fun u : ℝ[X] => u.coeff (2 * n)) h
    simpa using hcoeff

theorem oddEvenPolynomial_eq_iff {p q r s : ℝ[X]} :
    oddEvenPolynomial p q = oddEvenPolynomial r s ↔ p = r ∧ q = s :=
  ⟨oddEvenPolynomial_inj, fun h => h.1 ▸ h.2 ▸ rfl⟩

@[simp] theorem oddEvenPolynomial_zero_zero :
    oddEvenPolynomial (0 : ℝ[X]) 0 = 0 := by
  simp [oddEvenPolynomial]

@[simp] theorem oddEvenPolynomial_eq_zero_iff {p q : ℝ[X]} :
    oddEvenPolynomial p q = 0 ↔ p = 0 ∧ q = 0 := by
  simpa using
    (oddEvenPolynomial_eq_iff (p := p) (q := q) (r := 0) (s := 0))

theorem oddEvenPolynomial_ne_zero_iff {p q : ℝ[X]} :
    oddEvenPolynomial p q ≠ 0 ↔ p ≠ 0 ∨ q ≠ 0 :=
  (not_congr oddEvenPolynomial_eq_zero_iff).trans not_and_or

theorem hasNonnegCoeffs_oddEvenPolynomial {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (oddEvenPolynomial p q) := fun n => by
  by_cases hmod : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by lia
    rw [hn, coeff_oddEvenPolynomial_even]
    exact hq (n / 2)
  · have hn : n = 2 * (n / 2) + 1 := by lia
    rw [hn, coeff_oddEvenPolynomial_odd]
    exact hp (n / 2)

theorem hasNonnegCoeffs_left_of_oddEvenPolynomial {p q : ℝ[X]}
    (h : HasNonnegCoeffs (oddEvenPolynomial p q)) :
    HasNonnegCoeffs p := fun n => by
  simpa using h (2 * n + 1)

theorem hasNonnegCoeffs_right_of_oddEvenPolynomial {p q : ℝ[X]}
    (h : HasNonnegCoeffs (oddEvenPolynomial p q)) :
    HasNonnegCoeffs q := fun n => by
  simpa using h (2 * n)

theorem inv_sub_real_im_neg (r : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (1 / (z - (r : ℂ))).im < 0 := by
  have h_ne : z - (r : ℂ) ≠ 0 := fun h ↦ hz.ne' (by simpa using congrArg Complex.im h)
  rw [one_div, Complex.inv_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hz) (Complex.normSq_pos.mpr h_ne)

theorem eval_complexify_eq_prod {p : ℝ[X]} (hp : p.Splits) {z : ℂ} :
    (complexify p).eval z
      = (p.leadingCoeff : ℂ) * (p.roots.map (fun r : ℝ => z - (r : ℂ))).prod := by
  unfold complexify
  conv_lhs => rw [hp.eq_prod_roots]
  simp only [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C,
    Polynomial.map_multiset_prod, Multiset.map_map, eval_multiset_prod, Multiset.map_map,
    Function.comp, Polynomial.map_sub, Polynomial.map_X, eval_sub, eval_X, map_C,
    Complex.ofRealHom_eq_coe]

theorem eval_complexify_ne_zero_of_splits_of_im_pos {p : ℝ[X]} (hp : p.Splits) (hp₀ : p ≠ 0)
    {z : ℂ} (hz : 0 < z.im) : (complexify p).eval z ≠ 0 := by
  rw [eval_complexify_eq_prod hp]
  refine mul_ne_zero (by simp [hp₀]) ?_
  apply Multiset.prod_ne_zero
  simp only [Multiset.mem_map, not_exists, not_and]
  rintro r - heq
  exact hz.ne' (by simpa using congrArg Complex.im heq)

private theorem multiset_sum_div (s : Multiset ℂ) (c : ℂ) :
    s.sum / c = (s.map (fun x => x / c)).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih => simp [add_div, ih]

theorem eval_derivative_complexify_eq_sum {p : ℝ[X]} (hp : p.Splits) {z : ℂ} :
    (complexify p).derivative.eval z
      = (p.leadingCoeff : ℂ) *
          (p.roots.map (fun r : ℝ =>
            ((p.roots.erase r).map (fun s : ℝ => z - (s : ℂ))).prod)).sum := by
  unfold complexify
  conv_lhs => rw [hp.eq_prod_roots]
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod, Multiset.map_map,
      derivative_mul]
  simp only [derivative_C, zero_mul, zero_add, eval_mul, eval_C]
  congr 1
  rw [derivative_prod]
  simp only [eval_multisetSum, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro r hr
  simp only [Function.comp, eval_mul, eval_multiset_prod, Multiset.map_map]
  simp

theorem logDeriv_complexify_eq_sum {p : ℝ[X]} (hp : p.Splits) (hp₀ : p ≠ 0)
    {z : ℂ} (hz : 0 < z.im) :
    (complexify p).derivative.eval z / (complexify p).eval z
      = (p.roots.map (fun r : ℝ ↦ 1 / (z - (r : ℂ)))).sum := by
  rw [eval_derivative_complexify_eq_sum hp, eval_complexify_eq_prod hp]
  have hlc : (p.leadingCoeff : ℂ) ≠ 0 := by simp [*]
  rw [mul_div_mul_left _ _ hlc, multiset_sum_div, Multiset.map_map]
  apply congrArg
  apply Multiset.map_congr rfl
  intro r hr
  simp only [Function.comp_apply]
  rw [← Multiset.prod_map_erase (f := fun s : ℝ ↦ z - (s : ℂ)) hr]
  have hzr : z - (r : ℂ) ≠ 0 := fun h ↦ hz.ne' (by simpa using congrArg Complex.im h)
  have hperase : ((p.roots.erase r).map (fun s : ℝ ↦ z - (s : ℂ))).prod ≠ 0 := by
    refine Multiset.prod_ne_zero (fun h ↦ ?_)
    obtain ⟨s, -, hs⟩ := Multiset.mem_map.mp h
    exact hz.ne' (by simpa using congrArg Complex.im hs)
  field_simp

private theorem multiset_sum_im (s : Multiset ℂ) : s.sum.im = (s.map Complex.im).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih => simp [ih]

private theorem multiset_sum_nonpos (s : Multiset ℝ) (h : ∀ x ∈ s, x ≤ 0) :
    s.sum ≤ 0 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.sum_cons]
    have h_ih := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    have ha := h a (Multiset.mem_cons_self a t)
    linarith

private theorem multiset_sum_neg (s : Multiset ℝ) (h_ne : s ≠ 0) (h : ∀ x ∈ s, x < 0) :
    s.sum < 0 := by
  induction s using Multiset.induction with
  | empty => simp at h_ne
  | cons a t _ =>
    rw [Multiset.sum_cons]
    have ha := h a (Multiset.mem_cons_self a t)
    have ht := multiset_sum_nonpos t (fun x hx => le_of_lt (h x (Multiset.mem_cons_of_mem hx)))
    linarith

private theorem multiset_sum_nonpos_eq_zero {s : Multiset ℝ} (h : ∀ x ∈ s, x ≤ 0)
    (hs : s.sum = 0) : ∀ x ∈ s, x = 0 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.sum_cons] at hs
    have ha : a ≤ 0 := h a (Multiset.mem_cons_self a t)
    have ht : t.sum ≤ 0 :=
      multiset_sum_nonpos t (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    have ha₀ : a = 0 := by linarith
    have h_ts : t.sum = 0 := by linarith
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · simp [*]
    · exact ih (fun y hy ↦ h y (Multiset.mem_cons_of_mem hy)) h_ts x hx

theorem logDeriv_complexify_im_neg {p : ℝ[X]} (hp : p.Splits) (hp₀ : p ≠ 0)
    (hdeg : 1 ≤ p.natDegree) {z : ℂ} (hz : 0 < z.im) :
    ((complexify p).derivative.eval z / (complexify p).eval z).im < 0 := by
  rw [logDeriv_complexify_eq_sum hp hp₀ hz, multiset_sum_im, Multiset.map_map]
  apply multiset_sum_neg
  · rw [Ne, Multiset.map_eq_zero, ← Multiset.card_eq_zero, card_roots_of_splits hp]
    lia
  · intro x hx
    simp only [Multiset.mem_map] at hx
    obtain ⟨r, -, rfl⟩ := hx
    simp only [Function.comp_apply]
    exact inv_sub_real_im_neg r hz

theorem eval_derivative_eq_sum_real {p : ℝ[X]} (hp : p.Splits) (x : ℝ) :
    p.derivative.eval x
      = p.leadingCoeff *
          (p.roots.map (fun r : ℝ =>
            ((p.roots.erase r).map (fun s : ℝ => x - s)).prod)).sum := by
  conv_lhs => rw [hp.eq_prod_roots]
  rw [derivative_mul]
  simp only [derivative_C, zero_mul, zero_add, eval_mul, eval_C]
  congr 1
  rw [derivative_prod]
  simp only [eval_multisetSum, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro r hr
  simp only [Function.comp, derivative_sub, derivative_X, derivative_C, sub_zero,
    mul_one, eval_multiset_prod, Multiset.map_map, eval_sub, eval_X, eval_C]

theorem deriv_sum_collapse (M : Multiset ℝ) (s : ℝ) (hs : s ∈ M) (hcount : M.count s = 1) :
    (M.map (fun r : ℝ => ((M.erase r).map (fun t : ℝ => s - t)).prod)).sum
      = ((M.erase s).map (fun t : ℝ => s - t)).prod := by
  rw [← Multiset.cons_erase hs, Multiset.map_cons, Multiset.sum_cons,
      Multiset.erase_cons_head]
  have h_s_notin : s ∉ M.erase s := by
    intro h
    rw [← Multiset.count_pos, Multiset.count_erase_self] at h
    lia
  have h_rest : ((M.erase s).map (fun r : ℝ =>
      (((s ::ₘ M.erase s).erase r).map (fun t : ℝ => s - t)).prod)).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro y hy
    simp only [Multiset.mem_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    have h_r_s : r ≠ s := fun h ↦ h_s_notin (h ▸ hr)
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    refine ⟨s, ?_, ?_⟩
    · rw [Multiset.erase_cons_tail (M.erase s) (Ne.symm h_r_s)]
      simp
    · exact sub_self s
  simp_all

theorem eval_derivative_at_root {p : ℝ[X]} (hp : p.Splits) (s : ℝ)
    (hs : s ∈ p.roots) (hcount : p.roots.count s = 1) :
    p.derivative.eval s
      = p.leadingCoeff * ((p.roots.erase s).map (fun r : ℝ => s - r)).prod := by
  rw [eval_derivative_eq_sum_real hp, deriv_sum_collapse p.roots s hs hcount]

theorem prod_sub_sign_pos (M : Multiset ℝ) (s : ℝ) (hs : s ∉ M) :
    0 < (M.map (fun r => s - r)).prod * (-1 : ℝ) ^ (M.countP (fun r => s < r)) := by
  induction M using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.countP_cons]
    have h_s_notin_t : s ∉ t := fun h_mem ↦ hs (Multiset.mem_cons_of_mem h_mem)
    have h_as_ne : a ≠ s := fun h_eq ↦ hs (h_eq ▸ Multiset.mem_cons_self a t)
    have h_ih := ih h_s_notin_t
    set P := (t.map (fun r => s - r)).prod * (-1 : ℝ) ^ (t.countP (fun r => s < r))
    by_cases h_lt : s < a
    · simp only [h_lt, if_true, pow_add, pow_one]
      have : (s - a) * (t.map (fun r ↦ s - r)).prod *
          ((-1 : ℝ) ^ t.countP (fun r ↦ s < r) * -1) = (a - s) * P := by ring
      simp_all
    · simp only [h_lt, if_false, Nat.add_zero]
      have h_as_lt : a < s := lt_of_le_of_ne (not_lt.mp h_lt) h_as_ne
      have : (s - a) * (t.map (fun r ↦ s - r)).prod *
          (-1 : ℝ) ^ t.countP (fun r ↦ s < r) = (s - a) * P := by ring
      simp_all

theorem deriv_at_root_sign {p : ℝ[X]} (hp : p.Splits) (hlc : 0 < p.leadingCoeff) (s : ℝ)
    (hs : s ∈ p.roots) (hcount : p.roots.count s = 1) :
    0 < p.derivative.eval s * (-1 : ℝ) ^ (p.roots.countP (fun r => s < r)) := by
  have h_s_M : s ∉ p.roots.erase s := by
    intro h
    rw [← Multiset.count_pos, Multiset.count_erase_self] at h
    lia
  have h_cnt : (p.roots.erase s).countP (fun r ↦ s < r)
      = p.roots.countP (fun r ↦ s < r) := by
    rw [← Multiset.cons_erase hs, Multiset.countP_cons]
    simp
  rw [eval_derivative_at_root hp s hs hcount, mul_assoc]
  have h_pos := prod_sub_sign_pos (p.roots.erase s) s h_s_M
  rw [h_cnt] at h_pos
  exact mul_pos hlc h_pos

theorem eval_sign {p : ℝ[X]} (hp : p.Splits) (hlc : 0 < p.leadingCoeff) (s : ℝ)
    (hs : s ∉ p.roots) :
    0 < p.eval s * (-1 : ℝ) ^ (p.roots.countP (fun r => s < r)) := by
  have hev : p.eval s = p.leadingCoeff * (p.roots.map (fun r => s - r)).prod := by
    conv_lhs => rw [hp.eq_prod_roots]
    simp [eval_multiset_prod, Multiset.map_map, Function.comp]
  rw [hev, mul_assoc]
  exact mul_pos hlc (prod_sub_sign_pos p.roots s hs)

private theorem countP_min_strict (a : ℝ) (l : List ℝ) (h : (a :: l).Pairwise (· < ·)) :
    (a :: l).countP (fun r ↦ decide (a < r)) = l.length := by simp_all

theorem countP_eq_interlaces_strict :
    ∀ (ss rs : List ℝ), ss.Pairwise (· < ·) → rs.Pairwise (· < ·) →
    ListInterlaces ss rs → ∀ x ∈ rs, x ∉ ss →
    (rs.countP (fun r => decide (x < r))) =
      (ss.countP (fun s => decide (x < s))) := by
  intro ss rs
  induction ss generalizing rs with
  | nil =>
    intro _ _ hint
    match rs with
    | [] => simp
    | [r] => simp
    | r₁ :: r₂ :: rest => simp [ListInterlaces] at hint
  | cons s ss ih =>
    intro hss_sorted hrs_sorted hint
    match rs with
    | [] => simp
    | [r] => simp [ListInterlaces] at hint
    | r₁ :: r₂ :: rest =>
      obtain ⟨h₁, h₂, htail⟩ := hint
      have hrs_sorted' := hrs_sorted
      rw [List.pairwise_cons] at hrs_sorted
      obtain ⟨hr₁_lt, hrs_tail_sorted⟩ := hrs_sorted
      rw [List.pairwise_cons] at hss_sorted
      obtain ⟨hs_lt, hss_tail_sorted⟩ := hss_sorted
      intro x hx hxnss
      simp only [List.mem_cons] at hx
      simp only [List.mem_cons, not_or] at hxnss
      obtain ⟨hxs, hxss⟩ := hxnss
      rcases hx with hxr₁ | hx₂
      · subst hxr₁
        have hr₁s : x < s := lt_of_le_of_ne h₁ hxs
        rw [countP_min_strict x (r₂ :: rest) hrs_sorted']
        have hcg : (s :: ss).countP (fun r => decide (x < r)) = (s :: ss).length := by
          apply List.countP_eq_length.mpr
          intro a ha; simp only [decide_eq_true_eq]
          rcases List.mem_cons.mp ha with rfl | hass
          · exact hr₁s
          · exact hr₁s.trans (hs_lt a hass)
        rw [hcg, List.length_cons]
        have hlen : (r₂ :: rest).length = ss.length + 1 := by
          have := listInterlaces_cons_length_eq htail
          simp [*]
        simp_all
      · have hxmem : x ∈ r₂ :: rest := List.mem_cons.mpr hx₂
        have hr₂x : r₂ ≤ x := by
          rcases hx₂ with rfl | hxrest
          · simp
          · exact le_of_lt (List.rel_of_pairwise_cons hrs_tail_sorted hxrest)
        have hxr₁' : ¬ x < r₁ := by linarith [hr₁_lt r₂ (by simp : r₂ ∈ r₂ :: rest)]
        have hxs' : ¬ x < s := by linarith
        simp [*]

theorem countP_eq_alternates_strict :
    ∀ (ss rs : List ℝ), ss.Pairwise (· < ·) → rs.Pairwise (· < ·) →
    ListAlternates ss rs → ∀ x ∈ rs, x ∉ ss →
    (rs.countP (fun r ↦ decide (x < r))) =
      (ss.countP (fun s ↦ decide (x < s))) := by
  intro ss rs hss hrs halt x hx hxnss
  match ss, rs with
  | [], [] => simp
  | [], r :: rs' => simp [ListAlternates] at halt
  | s :: ss', [] => simp [ListAlternates] at halt
  | s :: ss', r :: rs' =>
    obtain ⟨hsr, htail⟩ := halt
    rw [List.pairwise_cons] at hss hrs
    obtain ⟨hs_lt, hss'⟩ := hss
    obtain ⟨hr_lt, hrs'⟩ := hrs
    simp only [List.mem_cons, not_or] at hxnss
    obtain ⟨hxs, hxss'⟩ := hxnss
    have hrx : r ≤ x := by
      rcases List.mem_cons.mp hx with rfl | hxrs'
      · simp
      · exact le_of_lt (hr_lt x hxrs')
    have hxs' : ¬ x < s := by linarith [hsr]
    have h_eq := countP_eq_interlaces_strict ss' (r :: rs') hss'
      (by simp_all) htail x hx hxss'
    simp [*]

private theorem pairwise_lt_of_le_of_nodup (l : List ℝ)
    (hsort : l.Pairwise (· ≤ ·)) (hnd : l.Nodup) : l.Pairwise (· < ·) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hsort ⊢
    rw [List.nodup_cons] at hnd
    refine ⟨fun b hb ↦ lt_of_le_of_ne (hsort.1 b hb) ?_, ih hsort.2 hnd.2⟩
    intro h_eq
    simp_all

theorem prec_countP_eq {f g : ℝ[X]} (hpq : Prec g f)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (x : ℝ) (hxf : x ∈ f.roots) (hxg : x ∉ g.roots) :
    f.roots.countP (fun r => x < r) = g.roots.countP (fun r => x < r) := by
  obtain ⟨⟨hg₀, hgs⟩, ⟨hf₀, hfs⟩, ss, rs, hss, hrs, hsseq, hrseq, hshape⟩ := hpq
  have hrs_strict : rs.Pairwise (· < ·) :=
    pairwise_lt_of_le_of_nodup rs hrs (by rw [← Multiset.coe_nodup, hrseq]; exact hfnd)
  have hss_strict : ss.Pairwise (· < ·) :=
    pairwise_lt_of_le_of_nodup ss hss (by rw [← Multiset.coe_nodup, hsseq]; exact hgnd)
  have hxrs : x ∈ rs := by rw [← Multiset.mem_coe, hrseq]; simp_all
  have hxss : x ∉ ss := by rw [← Multiset.mem_coe, hsseq]; simp [*]
  have hlist : rs.countP (fun r ↦ decide (x < r)) = ss.countP (fun s ↦ decide (x < s)) := by
    rcases hshape with ⟨_, hint⟩ | ⟨_, halt⟩
    · exact countP_eq_interlaces_strict ss rs hss_strict hrs_strict hint x hxrs hxss
    · exact countP_eq_alternates_strict ss rs hss_strict hrs_strict halt x hxrs hxss
  rw [← hrseq, ← hsseq, Multiset.coe_countP, Multiset.coe_countP]
  simp [*]

theorem residue_sign_pos {f g : ℝ[X]} (hpq : Prec g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (s : ℝ) (hsf : s ∈ f.roots) (hsg : s ∉ g.roots) :
    0 < g.eval s * f.derivative.eval s := by
  obtain ⟨⟨hg₀, hgs⟩, ⟨hf₀, hfs⟩, _⟩ := id hpq
  have hcount : f.roots.count s = 1 := Multiset.count_eq_one_of_mem hfnd hsf
  have hf' := deriv_at_root_sign hfs hflc s hsf hcount
  have hg := eval_sign hgs hglc s hsg
  have hcnt := prec_countP_eq hpq hfnd hgnd s hsf hsg
  rw [hcnt] at hf'
  set n := g.roots.countP (fun r ↦ s < r)
  set e := (-1 : ℝ) ^ n
  have he₂ : e * e = 1 := by
    simp only [e]
    rw [← pow_add]
    simp
  have h_pos : 0 < (g.eval s * e) * (f.derivative.eval s * e) := mul_pos hg hf'
  have h_eq : (g.eval s * e) * (f.derivative.eval s * e)
      = g.eval s * f.derivative.eval s * (e * e) := by ring
  rwa [h_eq, he₂, mul_one] at h_pos

theorem residue_nonneg {f g : ℝ[X]} (hpq : Prec g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (s : ℝ) (hsf : s ∈ f.roots) (hsg : s ∉ g.roots) :
    0 ≤ g.eval s / f.derivative.eval s := by
  have h_pos := residue_sign_pos hpq hflc hglc hfnd hgnd s hsf hsg
  have h_df_ne : f.derivative.eval s ≠ 0 := fun h_eq ↦ by simp_all
  have h_eq : g.eval s / f.derivative.eval s
      = (g.eval s * f.derivative.eval s) / (f.derivative.eval s * f.derivative.eval s) := by
    field_simp
  rw [h_eq]
  exact le_of_lt (div_pos h_pos (mul_self_pos.mpr h_df_ne))

theorem im_ratio_sub_real_nonpos (z : ℂ) (r s : ℝ) (hz : 0 < z.im) (hrs : r ≤ s) :
    ((z - (r : ℂ)) / (z - (s : ℂ))).im ≤ 0 := by
  by_cases hne : z - (s : ℂ) = 0
  · simp [*]
  rw [Complex.div_im]
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.sub_re, Complex.ofReal_re]
  rw [div_sub_div_same]
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [hz, hrs]
  · exact Complex.normSq_nonneg _

theorem ratio_eq_I_of_hermiteBiehler_root {f g : ℝ[X]} {z : ℂ}
    (h : (hermiteBiehlerPolynomial f g).eval z = 0)
    (hf : (complexify f).eval z ≠ 0) :
    (complexify g).eval z / (complexify f).eval z = Complex.I := by
  rw [eval_hermiteBiehlerPolynomial] at h
  set F := (complexify f).eval z
  set G := (complexify g).eval z
  have h_I_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h_G : G = Complex.I * F := by
    have h_eq : G - Complex.I * F = 0 := by
      have h_step : G - Complex.I * F = -(Complex.I * (F + Complex.I * G)) := by
        rw [mul_add, ← mul_assoc, h_I_sq]; ring
      simp [*]
    exact sub_eq_zero.mp h_eq
  simp [*]

theorem im_real_mul_nonpos (c : ℝ) (w : ℂ) (hc : 0 ≤ c) (hw : w.im ≤ 0) :
    ((c : ℂ) * w).im ≤ 0 := by
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_nonpos_of_nonneg_of_nonpos hc hw

theorem stable_of_im_ratio_nonpos {f g : ℝ[X]}
    (hf₀ : f ≠ 0) (hfs : f.Splits)
    (hratio : ∀ z : ℂ, 0 < z.im →
      ((complexify g).eval z / (complexify f).eval z).im ≤ 0) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) := by
  intro z hz hroot
  have hfz : (complexify f).eval z ≠ 0 :=
    eval_complexify_ne_zero_of_splits_of_im_pos hfs hf₀ hz
  have hI := ratio_eq_I_of_hermiteBiehler_root hroot hfz
  have hle := hratio z hz
  rw [hI, Complex.I_im] at hle
  norm_num at hle

private theorem im_ratio_deg1_deg1 (f g : ℝ[X]) (z : ℂ) (hz : 0 < z.im)
    (hfs : f.Splits) (hgs : g.Splits) (hlf : 0 < f.leadingCoeff) (hlg : 0 < g.leadingCoeff)
    (s r : ℝ) (hfr : f.roots = {s}) (hgr : g.roots = {r}) (hrs : r ≤ s) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  rw [eval_complexify_eq_prod hgs, eval_complexify_eq_prod hfs, hfr, hgr]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  rw [mul_div_mul_comm, ← Complex.ofReal_div]
  refine im_real_mul_nonpos _ _ ?_ (im_ratio_sub_real_nonpos z r s hz hrs)
  exact le_of_lt (div_pos hlg hlf)

private theorem im_ratio_deg1_deg0 (f g : ℝ[X]) (z : ℂ) (hz : 0 < z.im)
    (hfs : f.Splits) (hgs : g.Splits) (hlf : 0 < f.leadingCoeff) (hlg : 0 < g.leadingCoeff)
    (s : ℝ) (hfr : f.roots = {s}) (hgr : g.roots = 0) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  rw [eval_complexify_eq_prod hgs, eval_complexify_eq_prod hfs, hfr, hgr]
  simp only [Multiset.map_singleton, Multiset.prod_singleton, Multiset.map_zero,
    Multiset.prod_zero, mul_one]
  have h_div : (g.leadingCoeff : ℂ) / ((f.leadingCoeff : ℂ) * (z - (s : ℂ)))
      = ((g.leadingCoeff / f.leadingCoeff : ℝ) : ℂ) * (1 / (z - (s : ℂ))) := by
    have : (f.leadingCoeff : ℂ) ≠ 0 := by simp [hlf.ne']
    push_cast; field_simp
  rw [h_div]
  refine im_real_mul_nonpos _ _ ?_ (le_of_lt (inv_sub_real_im_neg s hz))
  exact le_of_lt (div_pos hlg hlf)

private theorem prec_roots_deg1 (f g : ℝ[X]) (hpq : Prec g f) (hd : f.natDegree = 1) :
    g.roots = 0 ∨ ∃ r s, f.roots = {s} ∧ g.roots = {r} ∧ r ≤ s := by
  obtain ⟨⟨hg₀, hgs⟩, ⟨hf₀, hfs⟩, ss, rs, hss, hrs, hsseq, hrseq, hshape⟩ := hpq
  have hfcard : f.roots.card = 1 := by rw [card_roots_of_splits hfs, hd]
  have hrslen : rs.length = 1 := by
    have : (rs : Multiset ℝ).card = 1 := by simp [*]
    simpa using this
  obtain ⟨s, hfr⟩ := Multiset.card_eq_one.mp hfcard
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · simp_all
  · right
    obtain ⟨r, h_ss_r⟩ := List.length_eq_one_iff.mp (by simp [*] : ss.length = 1)
    obtain ⟨s', h_rs_r⟩ := List.length_eq_one_iff.mp hrslen
    have h_s's : s' = s := by simp_all
    refine ⟨r, s, hfr, by simp_all, ?_⟩
    rw [h_ss_r, h_rs_r, h_s's] at halt
    simp only [ListAlternates] at halt
    simp [*]

theorem hermiteBiehlerForwardPos_of_natDegree_le_one {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (hpq : Prec g f)
    (hd : f.natDegree ≤ 1) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) := by
  obtain ⟨⟨hg₀, hgs⟩, ⟨hf₀, hfs⟩, _⟩ := id hpq
  unfold HasPosLeadingCoeff at hf hg
  rcases Nat.lt_or_ge f.natDegree 1 with hlt | hge
  · have hd₀ : f.natDegree = 0 := by lia
    have hgr : g.roots = 0 := by
      obtain ⟨_, _, ss, rs, _, _, hsseq, hrseq, hshape⟩ := hpq
      have hfcard : f.roots.card = 0 := by rw [card_roots_of_splits hfs, hd₀]
      simp_all
    intro z hz hroot
    rw [eval_hermiteBiehlerPolynomial, eval_complexify_eq_prod hfs, eval_complexify_eq_prod hgs,
      hgr] at hroot
    have hfr : f.roots = 0 := by rw [← Multiset.card_eq_zero, card_roots_of_splits hfs, hd₀]
    rw [hfr] at hroot
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one] at hroot
    have h_im :
        (((f.leadingCoeff : ℂ)) + Complex.I * (g.leadingCoeff : ℂ)).im = 0 := by
      simp [*]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_add] at h_im
    simp_all
  · have hd₁ : f.natDegree = 1 := by lia
    apply stable_of_im_ratio_nonpos hf₀ hfs
    intro z hz
    rcases prec_roots_deg1 f g hpq hd₁ with hgr | ⟨r, s, hfr, hgr, hrs⟩
    · obtain ⟨s, hfr⟩ := Multiset.card_eq_one.mp (by rw [card_roots_of_splits hfs, hd₁])
      exact im_ratio_deg1_deg0 f g z hz hfs hgs hf hg s hfr hgr
    · exact im_ratio_deg1_deg1 f g z hz hfs hgs hf hg s r hfr hgr hrs

theorem im_partialfraction_nonpos {f g : ℝ[X]} (z : ℂ) (hz : 0 < z.im) (c₀ : ℝ)
    (residue : ℝ → ℝ) (hres : ∀ s ∈ f.roots, 0 ≤ residue s)
    (h_id : (complexify g).eval z / (complexify f).eval z
        = (c₀ : ℂ) + (f.roots.map (fun s => (residue s : ℂ) / (z - (s : ℂ)))).sum) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  rw [h_id, Complex.add_im, Complex.ofReal_im, zero_add, multiset_sum_im, Multiset.map_map]
  apply multiset_sum_nonpos
  intro y hy
  simp only [Multiset.mem_map] at hy
  obtain ⟨s, hsf, rfl⟩ := hy
  simp only [Function.comp_apply]
  have h_div :
      (residue s : ℂ) / (z - (s : ℂ)) =
        (residue s : ℂ) * (1 / (z - (s : ℂ))) := by
    ring
  rw [h_div]
  exact im_real_mul_nonpos (residue s) _ (hres s hsf) (le_of_lt (inv_sub_real_im_neg s hz))

theorem eval_divByMonic_at_root {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) :
    (f /ₘ (X - C r)).eval r = f.derivative.eval r := by
  nth_rw 2 [← mul_divByMonic_eq_iff_isRoot.mpr hr]
  simp

theorem eval_divByMonic_at_other_root {f : ℝ[X]} {t s : ℝ}
    (ht : f.IsRoot t) (hs : f.IsRoot s) (hst : s ≠ t) : (f /ₘ (X - C t)).eval s = 0 := by
  have h_eval := congrArg (eval s) (mul_divByMonic_eq_iff_isRoot.mpr ht)
  rw [eval_mul, hs] at h_eval
  exact (mul_eq_zero.mp h_eval).resolve_left <| by
    simp only [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.mpr hst

theorem derivative_eval_ne_zero_of_simple_root {f : ℝ[X]} {r : ℝ}
    (hr : f.IsRoot r) (hsimple : f.rootMultiplicity r = 1) : f.derivative.eval r ≠ 0 := by
  have h_f'_ne : f.derivative ≠ 0 := by
    intro h
    have h_f_ne : f ≠ 0 := fun h₀ ↦ by simp [h₀] at hsimple
    have h_f_C : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero (derivative_eq_zero.mp h)
    rw [h_f_C, IsRoot, eval_C] at hr
    rw [h_f_C, hr] at h_f_ne
    simp at h_f_ne
  have h_mult_deriv : f.derivative.rootMultiplicity r = f.rootMultiplicity r - 1 :=
    derivative_rootMultiplicity_of_root hr
  simp_all

noncomputable def lagInterp (f g : ℝ[X]) : ℝ[X] :=
  ∑ s ∈ f.roots.toFinset, C (g.eval s / f.derivative.eval s) * (f /ₘ (X - C s))

theorem eval_lagInterp_at_root {f g : ℝ[X]} (hnd : f.roots.Nodup)
    {sk : ℝ} (hsk : sk ∈ f.roots) :
    (lagInterp f g).eval sk = g.eval sk := by
  have hsk_root : f.IsRoot sk := isRoot_of_mem_roots hsk
  have h_mult : f.rootMultiplicity sk = 1 := by
    simpa [count_roots] using Multiset.count_eq_one_of_mem hnd hsk
  have : f.derivative.eval sk ≠ 0 := derivative_eval_ne_zero_of_simple_root hsk_root h_mult
  have : sk ∈ f.roots.toFinset := Multiset.mem_toFinset.mpr hsk
  rw [lagInterp, eval_finsetSum, Finset.sum_eq_single sk]
  · rw [eval_mul, eval_C, eval_divByMonic_at_root hsk_root]
    simp [*]
  · intro s hs hssk
    have hsroot : f.IsRoot s := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hs)
    rw [eval_mul, eval_divByMonic_at_other_root hsroot hsk_root (fun h ↦ hssk h.symm), mul_zero]
  · simp [*]

theorem lagInterp_degree_lt {f g : ℝ[X]} (hfs : f.Splits) (hnd : f.roots.Nodup)
    (h_deg₁ : 1 ≤ f.natDegree) :
    (lagInterp f g).degree < f.roots.toFinset.card := by
  rw [Multiset.toFinset_card_of_nodup hnd, card_roots_of_splits hfs, lagInterp]
  apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
  have : (⊥ : WithBot ℕ) < (f.natDegree : WithBot ℕ) := by simp
  rw [Finset.sup_lt_iff this]
  intro s hs
  have : (C (g.eval s / f.derivative.eval s) * (f /ₘ (X - C s))).degree
      ≤ (f /ₘ (X - C s)).degree := by
    apply le_trans (degree_mul_le _ _)
    calc (C (g.eval s / f.derivative.eval s)).degree + (f /ₘ (X - C s)).degree
        ≤ 0 + (f /ₘ (X - C s)).degree := by gcongr; exact degree_C_le
      _ = (f /ₘ (X - C s)).degree := by simp
  apply lt_of_le_of_lt this
  have : (f /ₘ (X - C s)).natDegree = f.natDegree - 1 := by
    rw [natDegree_divByMonic f (monic_X_sub_C s)]
    simp
  calc (f /ₘ (X - C s)).degree ≤ ((f /ₘ (X - C s)).natDegree : WithBot ℕ) :=
      degree_le_natDegree
    _ = ((f.natDegree - 1 : ℕ) : WithBot ℕ) := by simp [*]
    _ < (f.natDegree : WithBot ℕ) := by exact_mod_cast by lia

theorem lagInterp_eq_g {f g : ℝ[X]} (hfs : f.Splits) (hnd : f.roots.Nodup)
    (h_deg₁ : 1 ≤ f.natDegree) (hgdeg : g.degree < f.natDegree) :
    lagInterp f g = g := by
  have : f.roots.toFinset.card = f.natDegree := by
    rw [Multiset.toFinset_card_of_nodup hnd, card_roots_of_splits hfs]
  have h_deg_lt : (lagInterp f g).degree < f.roots.toFinset.card :=
    lagInterp_degree_lt hfs hnd h_deg₁
  apply eq_of_degrees_lt_of_eval_finset_eq f.roots.toFinset h_deg_lt
  · simp [*]
  · intro x hx
    exact eval_lagInterp_at_root hnd (Multiset.mem_toFinset.mp hx)

private theorem finset_sum_eq_multiset_map_sum (M : Multiset ℝ) (hnd : M.Nodup)
    (h : ℝ → ℂ) :
    ∑ s ∈ M.toFinset, h s = (M.map h).sum := by
  rw [Finset.sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]

private theorem finset_sum_div (s : Finset ℝ) (h : ℝ → ℂ) (c : ℂ) :
    (∑ x ∈ s, h x) / c = ∑ x ∈ s, h x / c := by
  rw [Finset.sum_div]

theorem eval_complexify_divByMonic {f : ℝ[X]} {s : ℝ} (hs : f.IsRoot s) {z : ℂ}
    (hzs : z - (s : ℂ) ≠ 0) :
    (complexify (f /ₘ (X - C s))).eval z = (complexify f).eval z / (z - (s : ℂ)) := by
  have : complexify f = (X - C (s : ℂ)) * complexify (f /ₘ (X - C s)) := by
    nth_rw 1 [← mul_divByMonic_eq_iff_isRoot.mpr hs]
    simp [complexify]
  simp [this, hzs]

theorem complexify_ratio_eq_partialfraction {f g : ℝ[X]} (hfs : f.Splits) (hnd : f.roots.Nodup)
    (h_deg₁ : 1 ≤ f.natDegree) (hgdeg : g.degree < f.natDegree)
    {z : ℂ} (hz : 0 < z.im) :
    (complexify g).eval z / (complexify f).eval z
      = (f.roots.map
          (fun s ↦ ((g.eval s / f.derivative.eval s : ℝ) : ℂ) / (z - (s : ℂ)))).sum := by
  have hf₀ : f ≠ 0 := by
    rintro rfl
    simp at h_deg₁
  have hfz : (complexify f).eval z ≠ 0 := eval_complexify_ne_zero_of_splits_of_im_pos hfs hf₀ hz
  have h_gi : complexify g = complexify (lagInterp f g) := by
    rw [lagInterp_eq_g hfs hnd h_deg₁ hgdeg]
  have h_ev : (complexify (lagInterp f g)).eval z
      = ∑ s ∈ f.roots.toFinset, ((g.eval s / f.derivative.eval s : ℝ) : ℂ) *
          (complexify (f /ₘ (X - C s))).eval z := by
    unfold lagInterp complexify
    rw [Polynomial.map_sum, eval_finsetSum]
    simp
  rw [h_gi, h_ev, finset_sum_div, ← finset_sum_eq_multiset_map_sum f.roots hnd]
  apply Finset.sum_congr rfl
  intro s hs
  have h_s_root : f.IsRoot s := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hs)
  have h_zs : z - (s : ℂ) ≠ 0 := by
    intro heq
    rw [sub_eq_zero] at heq
    simp_all
  rw [eval_complexify_divByMonic h_s_root h_zs]
  field_simp [hfz, h_zs]

theorem im_ratio_nonpos_of_distinct {f g : ℝ[X]} (hpq : Prec g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (hno_common : ∀ s ∈ f.roots, s ∉ g.roots)
    (h_deg₁ : 1 ≤ f.natDegree) (hgdeg : g.degree < f.natDegree)
    {z : ℂ} (hz : 0 < z.im) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  obtain ⟨-, ⟨-, hfs⟩, -⟩ := id hpq
  apply im_partialfraction_nonpos z hz 0 (fun s => g.eval s / f.derivative.eval s)
  · intro s hsf
    exact residue_nonneg hpq hflc hglc hfnd hgnd s hsf (hno_common s hsf)
  · rw [complexify_ratio_eq_partialfraction hfs hfnd h_deg₁ hgdeg hz]
    simp

theorem degree_sub_c₀_mul_lt {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree) (hflc : 0 < f.leadingCoeff) :
    (g - C (g.leadingCoeff / f.leadingCoeff) * f).degree < f.natDegree := by
  set c₀ := g.leadingCoeff / f.leadingCoeff with hc₀
  have h_flc_ne : f.leadingCoeff ≠ 0 := ne_of_gt hflc
  have hc₀_ne : c₀ ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hg₀) h_flc_ne
  have : (C c₀ * f).degree = f.degree := degree_C_mul hc₀_ne
  have : (C c₀ * f).leadingCoeff = g.leadingCoeff := by simp [*]
  have : g.degree = f.degree := by rw [degree_eq_natDegree hg₀, degree_eq_natDegree hf₀, hdeg]
  have hsub : (g - C c₀ * f).degree < g.degree :=
    degree_sub_lt (by simp [*]) hg₀ (by simp [*])
  rw [degree_eq_natDegree hg₀, hdeg] at hsub
  simp_all

theorem im_ratio_nonpos_of_distinct_eqdeg {f g : ℝ[X]} (hpq : Prec g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (hno_common : ∀ s ∈ f.roots, s ∉ g.roots)
    (h_deg₁ : 1 ≤ f.natDegree) (hgdeg : g.natDegree = f.natDegree)
    {z : ℂ} (hz : 0 < z.im) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  obtain ⟨⟨hg₀, -⟩, ⟨hf₀, hfs⟩, -⟩ := id hpq
  set c₀ := g.leadingCoeff / f.leadingCoeff with hc₀
  set g' := g - C c₀ * f with hg'
  have hg'deg : g'.degree < f.natDegree := degree_sub_c₀_mul_lt hf₀ hg₀ hgdeg hflc
  have hg'eval : ∀ s ∈ f.roots, g'.eval s = g.eval s := by simp [*]
  have hfz : (complexify f).eval z ≠ 0 := eval_complexify_ne_zero_of_splits_of_im_pos hfs hf₀ hz
  have hpf : (complexify g').eval z / (complexify f).eval z
      = (f.roots.map (fun s ↦
          ((g.eval s / f.derivative.eval s : ℝ) : ℂ) / (z - (s : ℂ)))).sum := by
    rw [complexify_ratio_eq_partialfraction hfs hfnd h_deg₁ hg'deg hz]
    congr 1
    apply Multiset.map_congr rfl
    simp_all
  have hgsplit : (complexify g).eval z
      = (complexify g').eval z + (c₀ : ℂ) * (complexify f).eval z := by
    rw [hg']
    unfold complexify
    simp
  have hid : (complexify g).eval z / (complexify f).eval z
      = (c₀ : ℂ) + (f.roots.map (fun s ↦
          ((g.eval s / f.derivative.eval s : ℝ) : ℂ) / (z - (s : ℂ)))).sum := by
    rw [hgsplit, add_div, mul_div_assoc, div_self hfz, mul_one, add_comm, hpf]
  exact im_partialfraction_nonpos z hz c₀ (fun s => g.eval s / f.derivative.eval s)
    (fun s hsf => residue_nonneg hpq hflc hglc hfnd hgnd s hsf (hno_common s hsf)) hid

theorem im_ratio_nonpos {f g : ℝ[X]} (hpq : Prec g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (hno_common : ∀ s ∈ f.roots, s ∉ g.roots)
    (h_deg₁ : 1 ≤ f.natDegree)
    {z : ℂ} (hz : 0 < z.im) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  obtain ⟨⟨hg₀, hgs⟩, ⟨-, hfs⟩, ss, rs, -, -, hsseq, hrseq, hshape⟩ := id hpq
  have hgc : g.roots.card = g.natDegree := card_roots_of_splits hgs
  have hfc : f.roots.card = f.natDegree := card_roots_of_splits hfs
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩
  · have hdd : g.natDegree + 1 = f.natDegree := by
      rw [← hgc, ← hfc, ← hsseq, ← hrseq]
      simpa using hlen
    have hgdeg : g.degree < f.natDegree := by
      rw [degree_eq_natDegree hg₀]
      exact_mod_cast by lia
    exact im_ratio_nonpos_of_distinct hpq hflc hglc hfnd hgnd hno_common h_deg₁ hgdeg hz
  · have heq : g.natDegree = f.natDegree := by
      rw [← hgc, ← hfc, ← hsseq, ← hrseq]
      simpa using hlen
    exact im_ratio_nonpos_of_distinct_eqdeg hpq hflc hglc hfnd hgnd hno_common h_deg₁ heq hz

theorem hermiteBiehlerForwardPos_of_distinct {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (hpq : Prec g f)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (hno_common : ∀ s ∈ f.roots, s ∉ g.roots) (h_deg₁ : 1 ≤ f.natDegree) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) := by
  obtain ⟨-, ⟨hf₀, hfs⟩, -⟩ := id hpq
  unfold HasPosLeadingCoeff at hf hg
  apply stable_of_im_ratio_nonpos hf₀ hfs
  intro z hz
  exact im_ratio_nonpos hpq hf hg hfnd hgnd hno_common h_deg₁ hz

theorem hermiteBiehlerPolynomial_factor_common_root {f g : ℝ[X]} {r : ℝ}
    (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    hermiteBiehlerPolynomial f g
      = (X - C (r : ℂ)) * hermiteBiehlerPolynomial (f /ₘ (X - C r)) (g /ₘ (X - C r)) := by
  have hff : f = (X - C r) * (f /ₘ (X - C r)) := (mul_divByMonic_eq_iff_isRoot.mpr hrf).symm
  have hgg : g = (X - C r) * (g /ₘ (X - C r)) := (mul_divByMonic_eq_iff_isRoot.mpr hrg).symm
  unfold hermiteBiehlerPolynomial complexify
  have hcf : (f.map Complex.ofRealHom)
      = (X - C (r : ℂ)) * ((f /ₘ (X - C r)).map Complex.ofRealHom) := by
    conv_lhs => rw [hff]
    simp
  have hcg : (g.map Complex.ofRealHom)
      = (X - C (r : ℂ)) * ((g /ₘ (X - C r)).map Complex.ofRealHom) := by
    conv_lhs => rw [hgg]
    simp
  rw [hcf, hcg]
  ring

theorem isUpperHalfPlaneStable_of_cofactor {f g : ℝ[X]} {r : ℝ}
    (hrf : f.IsRoot r) (hrg : g.IsRoot r)
    (hcof : IsUpperHalfPlaneStable
      (hermiteBiehlerPolynomial (f /ₘ (X - C r)) (g /ₘ (X - C r)))) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) := by
  rw [hermiteBiehlerPolynomial_factor_common_root hrf hrg]
  apply IsUpperHalfPlaneStable.mul ?_ hcof
  intro z hz
  simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
  intro h
  exact hz.ne' (by simpa using congrArg Complex.im h)

theorem prec_cofactor_of_common_root {f g : ℝ[X]} {r : ℝ}
    (hpq : Prec g f) (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    Prec (g /ₘ (X - C r)) (f /ₘ (X - C r)) := by
  have : (X - C r) * (f /ₘ (X - C r)) = f := mul_divByMonic_eq_iff_isRoot.mpr hrf
  have : (X - C r) * (g /ₘ (X - C r)) = g := mul_divByMonic_eq_iff_isRoot.mpr hrg
  apply prec_of_prec_mul_X_sub_C_both r
  simp [*]

theorem prec_of_prec_cofactor {f g : ℝ[X]} {r : ℝ}
    (hrf : f.IsRoot r) (hrg : g.IsRoot r)
    (h : Prec (g /ₘ (X - C r)) (f /ₘ (X - C r))) : Prec g f := by
  have hff : (X - C r) * (f /ₘ (X - C r)) = f := mul_divByMonic_eq_iff_isRoot.mpr hrf
  have hgg : (X - C r) * (g /ₘ (X - C r)) = g := mul_divByMonic_eq_iff_isRoot.mpr hrg
  have := prec_mul_X_sub_C_both r h
  simp_all

theorem leadingCoeff_divByMonic_X_sub_C {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) :
    (f /ₘ (X - C r)).leadingCoeff = f.leadingCoeff := by
  have hff : (X - C r) * (f /ₘ (X - C r)) = f := mul_divByMonic_eq_iff_isRoot.mpr hr
  nth_rw 2 [← hff]
  rw [leadingCoeff_mul, (monic_X_sub_C r).leadingCoeff, one_mul]

/-- Sign-normalized forward Hermite--Biehler bridge.

This is the minimal sign-stable form used in downstream plumbing:
positive leading coefficients on both inputs prevent the false counterexample.
-/
abbrev hermiteBiehlerForwardPosStatement : Prop :=
  ∀ {f g : ℝ[X]},
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    Prec g f →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)

theorem hermiteBiehlerForwardPos_general {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (hpq : Prec g f) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) := by
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f g with
  | _ n ih =>
    subst hn
    by_cases h_deg_le : f.natDegree ≤ 1
    · exact hermiteBiehlerForwardPos_of_natDegree_le_one hf hg hpq h_deg_le
    · push Not at h_deg_le
      have h_deg₁ : 1 ≤ f.natDegree := by lia
      by_cases hcom : ∃ r, r ∈ f.roots ∧ r ∈ g.roots
      · obtain ⟨r, hrf, hrg⟩ := hcom
        have hrfroot : f.IsRoot r := isRoot_of_mem_roots hrf
        have hrgroot : g.IsRoot r := isRoot_of_mem_roots hrg
        apply isUpperHalfPlaneStable_of_cofactor hrfroot hrgroot
        have hf₁deg : (f /ₘ (X - C r)).natDegree < f.natDegree := by
          rw [natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C]
          lia
        have hpq₁ : Prec (g /ₘ (X - C r)) (f /ₘ (X - C r)) :=
          prec_cofactor_of_common_root hpq hrfroot hrgroot
        have hf₁ : HasPosLeadingCoeff (f /ₘ (X - C r)) := by
          unfold HasPosLeadingCoeff at hf ⊢
          rw [leadingCoeff_divByMonic_X_sub_C hrfroot]
          exact hf
        have hg₁ : HasPosLeadingCoeff (g /ₘ (X - C r)) := by
          unfold HasPosLeadingCoeff at hg ⊢
          rw [leadingCoeff_divByMonic_X_sub_C hrgroot]
          exact hg
        exact ih (f /ₘ (X - C r)).natDegree hf₁deg hf₁ hg₁ hpq₁ rfl
      · push Not at hcom
        have hfnd : f.roots.Nodup := by
          by_contra hnd
          obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup hpq hnd
          simp_all
        have hgnd : g.roots.Nodup := by
          by_contra hnd
          obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup_g hpq hnd
          simp_all
        exact hermiteBiehlerForwardPos_of_distinct hf hg hpq hfnd hgnd
          (fun s hsf hsg ↦ hcom s hsf hsg) h_deg₁

theorem hermiteBiehlerForwardPos {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (h : Prec g f) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) :=
  hermiteBiehlerForwardPos_general hf hg h

lemma hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hp₀ : p ≠ 0) :
    HasPosLeadingCoeff p :=
  lt_of_le_of_ne (hpnn p.natDegree) (Ne.symm (leadingCoeff_ne_zero.mpr hp₀))

/-- Concrete obstruction to a sign-free forward Hermite--Biehler route:
`X - i` has the upper-half-plane root `i`. -/
theorem not_isUpperHalfPlaneStable_hermiteBiehlerPolynomial_X_neg_one :
    ¬ IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (X : ℝ[X]) (-(1 : ℝ[X]))) :=
  fun h => h Complex.I (by simp) (by simp [hermiteBiehlerPolynomial, complexify])

theorem eval_complexify_conj (f : ℝ[X]) (z : ℂ) :
    (complexify f).eval (starRingEnd ℂ z) = starRingEnd ℂ ((complexify f).eval z) := by
  have : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
    ext x
    simp
  simp [complexify, eval_map, hom_eval₂, this]

theorem complexify_conj_root {f : ℝ[X]} {z : ℂ} (hz : (complexify f).eval z = 0) :
    (complexify f).eval (starRingEnd ℂ z) = 0 := by
  rw [eval_complexify_conj, hz, map_zero]

/-- A nonzero split real polynomial has stable complexification. -/
theorem Polynomial.Splits.isUpperHalfPlaneStable_complexify
    {p : ℝ[X]} (hp : p.Splits) (hp0 : p ≠ 0) :
    IsUpperHalfPlaneStable (complexify p) :=
  fun _ hz => eval_complexify_ne_zero_of_splits_of_im_pos hp hp0 hz

/-- Upper-half-plane stability of a real polynomial's complexification forces
all its roots to be real. -/
theorem IsUpperHalfPlaneStable.splits_complexify {p : ℝ[X]}
    (hp : IsUpperHalfPlaneStable (complexify p)) :
    p.Splits := by
  apply Polynomial.splits_of_all_roots_real
  intro z hz
  by_contra him
  rcases lt_or_gt_of_ne him with hneg | hpos
  · exact hp (starRingEnd ℂ z) (by simpa using neg_pos.mpr hneg)
      (complexify_conj_root hz)
  · exact hp z hpos hz

theorem eval_hermiteBiehler_neg_conj (f g : ℝ[X]) (z : ℂ) :
    (hermiteBiehlerPolynomial f (-g)).eval (starRingEnd ℂ z)
      = starRingEnd ℂ ((hermiteBiehlerPolynomial f g).eval z) := by
  simp [hermiteBiehlerPolynomial, eval_complexify_conj]
  simp [complexify]

theorem no_lower_root_hermiteBiehler_neg_of_stable {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    ∀ z : ℂ, z.im < 0 → (hermiteBiehlerPolynomial f (-g)).eval z ≠ 0 := by
  intro z hz hzero
  have hconj_im : 0 < (starRingEnd ℂ z).im := by simp [*]
  apply hstab (starRingEnd ℂ z) hconj_im
  have hthis := eval_hermiteBiehler_neg_conj f g (starRingEnd ℂ z)
  rw [Complex.conj_conj] at hthis
  rw [hthis] at hzero
  have := congrArg (starRingEnd ℂ) hzero
  rwa [Complex.conj_conj, map_zero] at this

theorem no_common_nonreal_root_of_stable {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    {z : ℂ} (hzim : z.im ≠ 0)
    (hf : (complexify f).eval z = 0) (hg : (complexify g).eval z = 0) : False := by
  rcases lt_or_gt_of_ne hzim with hneg | hpos
  · have hcf : (complexify f).eval (starRingEnd ℂ z) = 0 := complexify_conj_root hf
    have hcg : (complexify g).eval (starRingEnd ℂ z) = 0 := complexify_conj_root hg
    have : 0 < (starRingEnd ℂ z).im := by simp [*]
    apply hstab (starRingEnd ℂ z) this
    simp [*]
  · apply hstab z hpos
    simp [*]

lemma discrim_nonneg_of_im_nonpos
    {u₁ u₂ v₁ v₂ : ℝ} (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0) :
    0 ≤ (-(u₁ + u₂) + (v₁ + v₂)) ^ 2
      - 4 * (u₁ * u₂ - v₁ * v₂ - u₁ * v₂ - u₂ * v₁) := by
  have h_sos : (-(u₁ + u₂) + (v₁ + v₂)) ^ 2
        - 4 * (u₁ * u₂ - v₁ * v₂ - u₁ * v₂ - u₂ * v₁)
      = (u₁ - u₂ - v₁ + v₂) ^ 2 + 8 * (v₁ * v₂) := by ring
  rw [h_sos]
  have h_vv : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  positivity

lemma discrim_nonneg_of_im_nonpos'
    {u₁ u₂ v₁ v₂ : ℝ} (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0) :
    0 ≤ (-(u₁ + u₂) - (v₁ + v₂)) ^ 2
      - 4 * (u₁ * u₂ - v₁ * v₂ + u₁ * v₂ + u₂ * v₁) := by
  have h_sos : (-(u₁ + u₂) - (v₁ + v₂)) ^ 2
        - 4 * (u₁ * u₂ - v₁ * v₂ + u₁ * v₂ + u₂ * v₁)
      = (u₁ - u₂ + v₁ - v₂) ^ 2 + 8 * (v₁ * v₂) := by ring
  rw [h_sos]
  have h_vv : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  positivity

lemma hermiteBiehler_coeff (f g : ℝ[X]) (n : ℕ) :
    (hermiteBiehlerPolynomial f g).coeff n
      = (f.coeff n : ℂ) + Complex.I * (g.coeff n : ℂ) := by
  simp [hermiteBiehlerPolynomial, complexify, coeff_map, mul_comm]

lemma im_nonpos_of_stable_root {p : ℂ[X]} (hstab : IsUpperHalfPlaneStable p)
    {w : ℂ} (hw : p.eval w = 0) : w.im ≤ 0 := by
  by_contra h
  exact hstab w (not_le.mp h) hw

lemma hermiteBiehler_natDegree_of_monic {f g : ℝ[X]} {d : ℕ}
    (hf : f.Monic) (hg : g.Monic) (hfd : f.natDegree = d) (hgd : g.natDegree = d) :
    (hermiteBiehlerPolynomial f g).natDegree = d ∧
      (hermiteBiehlerPolynomial f g).coeff d = 1 + Complex.I := by
  have h_coeff : (hermiteBiehlerPolynomial f g).coeff d = 1 + Complex.I := by
    simp [hermiteBiehler_coeff, (by rw [← hfd]; exact hf : f.coeff d = 1),
      (by rw [← hgd]; exact hg : g.coeff d = 1)]
  have : (1 + Complex.I : ℂ) ≠ 0 := by
    intro h
    simpa using congrArg Complex.im h
  constructor
  · apply le_antisymm
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt (hfd.symm ▸ hn),
        coeff_eq_zero_of_natDegree_lt (hgd.symm ▸ hn)]
      simp
    · exact le_natDegree_of_ne_zero (h_coeff.symm ▸ this)
  · simp [*]

lemma hermiteBiehler_factor_two {f g : ℝ[X]}
    (hf : f.Monic) (hg : g.Monic) (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2) :
    ∃ w₁ w₂ : ℂ,
      hermiteBiehlerPolynomial f g
        = C (1 + Complex.I) * ((X - C w₁) * (X - C w₂)) ∧
      (hermiteBiehlerPolynomial f g).roots = {w₁, w₂} := by
  obtain ⟨hdeg, hlead⟩ := hermiteBiehler_natDegree_of_monic hf hg hf₂ hg₂
  have h_splits : (hermiteBiehlerPolynomial f g).Splits := IsAlgClosed.splits _
  have : (hermiteBiehlerPolynomial f g).roots.card = 2 := by
    rw [splits_iff_card_roots.mp h_splits, hdeg]
  obtain ⟨w₁, w₂, hroots⟩ := Multiset.card_eq_two.mp this
  refine ⟨w₁, w₂, ?_, hroots⟩
  have : (hermiteBiehlerPolynomial f g).leadingCoeff = 1 + Complex.I := by
    rw [leadingCoeff, hdeg, hlead]
  rw [h_splits.eq_prod_roots, this, hroots]
  simp

theorem splits_of_stable_monic_two {f g : ℝ[X]}
    (hf : f.Monic) (hg : g.Monic) (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    f.Splits ∧ g.Splits := by
  obtain ⟨w₁, w₂, hfact, hroots⟩ := hermiteBiehler_factor_two hf hg hf₂ hg₂
  have hne : hermiteBiehlerPolynomial f g ≠ 0 := by
    intro h_zero
    simp_all
  have hv₁ : w₁.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  have hv₂ : w₂.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  have hpoly : hermiteBiehlerPolynomial f g
      = C (1 + Complex.I) * X ^ 2 + C ((1 + Complex.I) * (-(w₁ + w₂))) * X
        + C ((1 + Complex.I) * (w₁ * w₂)) := by
    rw [hfact]
    simp only [C_mul, C_add, C_neg]
    ring
  have hc₁ : (f.coeff 1 : ℂ) + Complex.I * (g.coeff 1 : ℂ)
      = (1 + Complex.I) * (-(w₁ + w₂)) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X_one]
    simp [*]
  have hc₀ : (f.coeff 0 : ℂ) + Complex.I * (g.coeff 0 : ℂ)
      = (1 + Complex.I) * (w₁ * w₂) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp
  have hb₁ : f.coeff 1 = -(w₁.re + w₂.re) + (w₁.im + w₂.im) := by
    have := congrArg Complex.re hc₁
    simp [Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    linarith
  have hb₂ : g.coeff 1 = -(w₁.re + w₂.re) - (w₁.im + w₂.im) := by
    have := congrArg Complex.im hc₁
    simp [Complex.add_re, Complex.mul_im, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    linarith
  have hcf : f.coeff 0 = w₁.re * w₂.re - w₁.im * w₂.im
      - (w₁.re * w₂.im + w₂.re * w₁.im) := by
    have := congrArg Complex.re hc₀
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    linarith
  have hcg : g.coeff 0 = w₁.re * w₂.re - w₁.im * w₂.im
      + (w₁.re * w₂.im + w₂.re * w₁.im) := by
    have := congrArg Complex.im hc₀
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    linarith
  have hdiscf : 0 ≤ discrim 1 (f.coeff 1) (f.coeff 0) := by
    rw [discrim, hb₁, hcf]
    have := discrim_nonneg_of_im_nonpos (u₁ := w₁.re) (u₂ := w₂.re) hv₁ hv₂
    nlinarith [this]
  have hdiscg : 0 ≤ discrim 1 (g.coeff 1) (g.coeff 0) := by
    rw [discrim, hb₂, hcg]
    have := discrim_nonneg_of_im_nonpos' (u₁ := w₁.re) (u₂ := w₂.re) hv₁ hv₂
    nlinarith [this]
  have hfexp : f = C 1 * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) := by
    have h₂ : f.coeff 2 = 1 := by
      rw [← hf₂]
      exact hf
    simpa [h₂] using eq_X_sq_add_X_add_C_of_natDegree_le_two (p := f) (by lia)
  have hgexp : g = C 1 * X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := by
    have h₂ : g.coeff 2 = 1 := by
      rw [← hg₂]
      exact hg
    simpa [h₂] using eq_X_sq_add_X_add_C_of_natDegree_le_two (p := g) (by lia)
  constructor
  · rw [hfexp]
    exact splits_of_discrim_nonneg one_ne_zero hdiscf
  · rw [hgexp]
    exact splits_of_discrim_nonneg one_ne_zero hdiscg

lemma triangle_of_sq {A B t S : ℝ} (hA₀ : 0 ≤ A) (hB₀ : 0 ≤ B) (ht₀ : 0 ≤ t)
    (ht₂ : t ^ 2 = A ^ 2 + B ^ 2 - 2 * S) (hS₁ : S ≤ A * B) (hS₂ : -S ≤ A * B) :
    A - B ≤ t ∧ B - A ≤ t ∧ t ≤ A + B := by
  have hd₁ : (A - B) ^ 2 ≤ t ^ 2 := by nlinarith
  have hd₃ : t ^ 2 ≤ (A + B) ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hd₁, hd₃, ht₀, hA₀, hB₀]

lemma interlace_core {u₁ u₂ v₁ v₂ b₁ b₂ c₁ c₂ : ℝ}
    (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0)
    (hb₁ : b₁ = -(u₁ + u₂) + (v₁ + v₂))
    (hb₂ : b₂ = -(u₁ + u₂) - (v₁ + v₂))
    (hc₁ : c₁ = u₁ * u₂ - v₁ * v₂ - (u₁ * v₂ + u₂ * v₁))
    (hc₂ : c₂ = u₁ * u₂ - v₁ * v₂ + (u₁ * v₂ + u₂ * v₁)) :
    (-b₂ - Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2 ≤
        (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2 ∧
      (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2 ≤
        (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2 ∧
      (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2 ≤
        (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2 := by
  have hvv : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  have hDf : b₁ ^ 2 - 4 * c₁ = (u₁ - u₂ - v₁ + v₂) ^ 2 + 8 * (v₁ * v₂) := by
    rw [hb₁, hc₁]
    ring
  have hDg : b₂ ^ 2 - 4 * c₂ = (u₁ - u₂ + v₁ - v₂) ^ 2 + 8 * (v₁ * v₂) := by
    rw [hb₂, hc₂]
    ring
  have hDf₀ : 0 ≤ b₁ ^ 2 - 4 * c₁ := by
    rw [hDf]
    positivity
  have hDg₀ : 0 ≤ b₂ ^ 2 - 4 * c₂ := by
    rw [hDg]
    positivity
  set A := Real.sqrt (b₁ ^ 2 - 4 * c₁) with hA
  set B := Real.sqrt (b₂ ^ 2 - 4 * c₂) with hB
  have hA₀ : 0 ≤ A := Real.sqrt_nonneg _
  have hB₀ : 0 ≤ B := Real.sqrt_nonneg _
  have hA₂ : A ^ 2 = b₁ ^ 2 - 4 * c₁ := Real.sq_sqrt hDf₀
  have hB₂ : B ^ 2 = b₂ ^ 2 - 4 * c₂ := Real.sq_sqrt hDg₀
  have hAB₀ : 0 ≤ A * B := mul_nonneg hA₀ hB₀
  have hprodsq : ((u₁ - u₂) ^ 2 - (v₁ - v₂) ^ 2) ^ 2 ≤ (A * B) ^ 2 := by
    have hABsq : (A * B) ^ 2 =
        (b₁ ^ 2 - 4 * c₁) * (b₂ ^ 2 - 4 * c₂) := by
      rw [mul_pow, hA₂, hB₂]
    rw [hABsq, hDf, hDg]
    nlinarith [mul_nonneg hvv (by positivity : (0 : ℝ) ≤ (u₁ - u₂) ^ 2 + (v₁ - v₂) ^ 2),
      sq_nonneg (v₁ * v₂)]
  have hle₁ : (u₁ - u₂) ^ 2 - (v₁ - v₂) ^ 2 ≤ A * B := by nlinarith [hprodsq, hAB₀]
  have hle₂ : -((u₁ - u₂) ^ 2 - (v₁ - v₂) ^ 2) ≤ A * B := by nlinarith [hprodsq, hAB₀]
  have hbb : 0 ≤ b₂ - b₁ := by
    rw [hb₁, hb₂]
    linarith
  have ht₂ : (b₂ - b₁) ^ 2
      = A ^ 2 + B ^ 2 - 2 * ((u₁ - u₂) ^ 2 - (v₁ - v₂) ^ 2) := by
    rw [hA₂, hB₂, hb₁, hb₂, hc₁, hc₂]
    ring
  obtain ⟨h₁, h₂, h₃⟩ := triangle_of_sq hA₀ hB₀ hbb ht₂ hle₁ hle₂
  refine ⟨by linarith, by linarith, by linarith⟩

lemma roots_monic_quadratic {b c : ℝ} (hd : 0 ≤ b ^ 2 - 4 * c) :
    (C 1 * X ^ 2 + C b * X + C c).roots
      = {(-b - Real.sqrt (b ^ 2 - 4 * c)) / 2, (-b + Real.sqrt (b ^ 2 - 4 * c)) / 2} := by
  have hs₂ : Real.sqrt (b ^ 2 - 4 * c) ^ 2 = b ^ 2 - 4 * c := Real.sq_sqrt hd
  apply (Polynomial.roots_quadratic_eq_pair_iff_of_ne_zero'
    (a := (1 : ℝ)) (b := b) (c := c) (ha := one_ne_zero)).2
  constructor
  · field_simp
    ring
  · field_simp
    nlinarith [hs₂]

lemma hermiteBiehler_vieta_two {f g : ℝ[X]}
    (hf : f.Monic) (hg : g.Monic) (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    ∃ u₁ u₂ v₁ v₂ : ℝ, v₁ ≤ 0 ∧ v₂ ≤ 0 ∧
      f.coeff 1 = -(u₁ + u₂) + (v₁ + v₂) ∧
      g.coeff 1 = -(u₁ + u₂) - (v₁ + v₂) ∧
      f.coeff 0 = u₁ * u₂ - v₁ * v₂ - (u₁ * v₂ + u₂ * v₁) ∧
      g.coeff 0 = u₁ * u₂ - v₁ * v₂ + (u₁ * v₂ + u₂ * v₁) := by
  obtain ⟨w₁, w₂, hfact, hroots⟩ := hermiteBiehler_factor_two hf hg hf₂ hg₂
  have hne : hermiteBiehlerPolynomial f g ≠ 0 := by
    intro h_zero
    simp_all
  have hv₁ : w₁.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  have hv₂ : w₂.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  have hpoly : hermiteBiehlerPolynomial f g
      = C (1 + Complex.I) * X ^ 2 + C ((1 + Complex.I) * (-(w₁ + w₂))) * X
        + C ((1 + Complex.I) * (w₁ * w₂)) := by
    rw [hfact]
    simp only [C_mul, C_add, C_neg]
    ring
  have hc₁ : (f.coeff 1 : ℂ) + Complex.I * (g.coeff 1 : ℂ)
      = (1 + Complex.I) * (-(w₁ + w₂)) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X_one]
    simp [*]
  have hc₀ : (f.coeff 0 : ℂ) + Complex.I * (g.coeff 0 : ℂ)
      = (1 + Complex.I) * (w₁ * w₂) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp
  refine ⟨w₁.re, w₂.re, w₁.im, w₂.im, hv₁, hv₂, ?_, ?_, ?_, ?_⟩
  · have := congrArg Complex.re hc₁
    simp [Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    linarith
  · have := congrArg Complex.im hc₁
    simp [Complex.add_re, Complex.mul_im, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    linarith
  · have := congrArg Complex.re hc₀
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    linarith
  · have := congrArg Complex.im hc₀
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    linarith

theorem prec_of_stable_monic_two {f g : ℝ[X]}
    (hf : f.Monic) (hg : g.Monic) (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    Prec g f := by
  obtain ⟨hfs, hgs⟩ := splits_of_stable_monic_two hf hg hf₂ hg₂ hstab
  obtain ⟨u₁, u₂, v₁, v₂, hv₁, hv₂, hb₁, hb₂, hcf, hcg⟩ :=
    hermiteBiehler_vieta_two hf hg hf₂ hg₂ hstab
  have hfexp : f = C 1 * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) := by
    have h₂ : f.coeff 2 = 1 := by
      rw [← hf₂]
      exact hf
    simpa [h₂] using eq_X_sq_add_X_add_C_of_natDegree_le_two (p := f) (by lia)
  have hgexp : g = C 1 * X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := by
    have h₂ : g.coeff 2 = 1 := by
      rw [← hg₂]
      exact hg
    simpa [h₂] using eq_X_sq_add_X_add_C_of_natDegree_le_two (p := g) (by lia)
  set b₁ := f.coeff 1 with hb₁def
  set c₁ := f.coeff 0 with hc₁def
  set b₂ := g.coeff 1 with hb₂def
  set c₂ := g.coeff 0 with hc₂def
  have : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  have hDf₀ : 0 ≤ b₁ ^ 2 - 4 * c₁ := by
    have : b₁ ^ 2 - 4 * c₁ = (u₁ - u₂ - v₁ + v₂) ^ 2 + 8 * (v₁ * v₂) := by
      rw [hb₁, hcf]
      ring
    rw [this]
    positivity
  have hDg₀ : 0 ≤ b₂ ^ 2 - 4 * c₂ := by
    have : b₂ ^ 2 - 4 * c₂ = (u₁ - u₂ + v₁ - v₂) ^ 2 + 8 * (v₁ * v₂) := by
      rw [hb₂, hcg]
      ring
    rw [this]
    positivity
  have hfroots : f.roots = {(-b₁ - Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2,
      (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2} := by
    conv_lhs => rw [hfexp]
    exact roots_monic_quadratic hDf₀
  have hgroots : g.roots = {(-b₂ - Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2,
      (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2} := by
    conv_lhs => rw [hgexp]
    exact roots_monic_quadratic hDg₀
  obtain ⟨h₁, h₂, h₃⟩ := interlace_core hv₁ hv₂ hb₁ hb₂ hcf hcg
  have hA₀ : 0 ≤ Real.sqrt (b₁ ^ 2 - 4 * c₁) := Real.sqrt_nonneg _
  have hB₀ : 0 ≤ Real.sqrt (b₂ ^ 2 - 4 * c₂) := Real.sqrt_nonneg _
  refine ⟨⟨hg.ne_zero, hgs⟩, ⟨hf.ne_zero, hfs⟩,
    [(-b₂ - Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2, (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2],
    [(-b₁ - Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2, (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2],
    ?_, ?_, ?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
    linarith
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
    linarith
  · rw [hgroots]
    rfl
  · rw [hfroots]
    rfl
  · simp only [ListAlternates, ListInterlaces, and_true]
    exact ⟨h₁, h₂, h₃⟩

lemma discrim_nonneg_of_im_nonpos_f {a b u₁ u₂ v₁ v₂ : ℝ}
    (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0) :
    0 ≤ (-(a * (u₁ + u₂)) + b * (v₁ + v₂)) ^ 2
      - 4 * a * (a * (u₁ * u₂ - v₁ * v₂) - b * (u₁ * v₂ + u₂ * v₁)) := by
  have h_sos : (-(a * (u₁ + u₂)) + b * (v₁ + v₂)) ^ 2
        - 4 * a * (a * (u₁ * u₂ - v₁ * v₂) - b * (u₁ * v₂ + u₂ * v₁))
      = (a * (u₁ - u₂) - b * (v₁ - v₂)) ^ 2 + 4 * (a ^ 2 + b ^ 2) * (v₁ * v₂) := by
    ring
  rw [h_sos]
  have h_vv : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  positivity

lemma discrim_nonneg_of_im_nonpos_g {a b u₁ u₂ v₁ v₂ : ℝ}
    (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0) :
    0 ≤ (-(a * (v₁ + v₂)) - b * (u₁ + u₂)) ^ 2
      - 4 * b * (a * (u₁ * v₂ + u₂ * v₁) + b * (u₁ * u₂ - v₁ * v₂)) := by
  have h_sos : (-(a * (v₁ + v₂)) - b * (u₁ + u₂)) ^ 2
        - 4 * b * (a * (u₁ * v₂ + u₂ * v₁) + b * (u₁ * u₂ - v₁ * v₂))
      = (b * (u₁ - u₂) + a * (v₁ - v₂)) ^ 2 + 4 * (a ^ 2 + b ^ 2) * (v₁ * v₂) := by
    ring
  rw [h_sos]
  have h_vv : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  positivity

lemma hermiteBiehler_natDegree_of_posLead {f g : ℝ[X]} {d : ℕ}
    (hf : 0 < f.coeff d) (hfd : f.natDegree = d) (hgd : g.natDegree = d) :
    (hermiteBiehlerPolynomial f g).natDegree = d ∧
      (hermiteBiehlerPolynomial f g).coeff d
        = (f.coeff d : ℂ) + Complex.I * (g.coeff d : ℂ) := by
  have h_coeff : (hermiteBiehlerPolynomial f g).coeff d
      = (f.coeff d : ℂ) + Complex.I * (g.coeff d : ℂ) := hermiteBiehler_coeff f g d
  have : ((f.coeff d : ℂ) + Complex.I * (g.coeff d : ℂ)) ≠ 0 := by
    intro h
    have hre : f.coeff d = 0 := by simpa using congrArg Complex.re h
    exact hf.ne' hre
  constructor
  · apply le_antisymm
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt (hfd.symm ▸ hn),
        coeff_eq_zero_of_natDegree_lt (hgd.symm ▸ hn)]
      simp
    · exact le_natDegree_of_ne_zero (h_coeff.symm ▸ this)
  · simp [*]

lemma hermiteBiehler_factor_two_posLead {f g : ℝ[X]}
    (hf : 0 < f.coeff 2) (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2) :
    ∃ w₁ w₂ : ℂ,
      hermiteBiehlerPolynomial f g
        = C ((f.coeff 2 : ℂ) + Complex.I * (g.coeff 2 : ℂ))
          * ((X - C w₁) * (X - C w₂)) ∧
      (hermiteBiehlerPolynomial f g).roots = {w₁, w₂} := by
  obtain ⟨hdeg, hlead⟩ := hermiteBiehler_natDegree_of_posLead hf hf₂ hg₂
  have h_splits : (hermiteBiehlerPolynomial f g).Splits := IsAlgClosed.splits _
  have : (hermiteBiehlerPolynomial f g).roots.card = 2 := by
    rw [splits_iff_card_roots.mp h_splits, hdeg]
  obtain ⟨w₁, w₂, hroots⟩ := Multiset.card_eq_two.mp this
  refine ⟨w₁, w₂, ?_, hroots⟩
  have : (hermiteBiehlerPolynomial f g).leadingCoeff
      = (f.coeff 2 : ℂ) + Complex.I * (g.coeff 2 : ℂ) := by
    rw [leadingCoeff, hdeg, hlead]
  rw [h_splits.eq_prod_roots, this, hroots]
  simp

lemma hermiteBiehler_vieta_two_posLead {f g : ℝ[X]}
    (hf : 0 < f.coeff 2) (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    ∃ u₁ u₂ v₁ v₂ : ℝ, v₁ ≤ 0 ∧ v₂ ≤ 0 ∧
      f.coeff 1 = -(f.coeff 2 * (u₁ + u₂)) + g.coeff 2 * (v₁ + v₂) ∧
      g.coeff 1 = -(f.coeff 2 * (v₁ + v₂)) - g.coeff 2 * (u₁ + u₂) ∧
      f.coeff 0 =
        f.coeff 2 * (u₁ * u₂ - v₁ * v₂) -
          g.coeff 2 * (u₁ * v₂ + u₂ * v₁) ∧
      g.coeff 0 =
        f.coeff 2 * (u₁ * v₂ + u₂ * v₁) +
          g.coeff 2 * (u₁ * u₂ - v₁ * v₂) := by
  obtain ⟨w₁, w₂, hfact, hroots⟩ := hermiteBiehler_factor_two_posLead hf hf₂ hg₂
  have hne : hermiteBiehlerPolynomial f g ≠ 0 := by
    intro h_zero
    simp_all
  have hv₁ : w₁.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  have hv₂ : w₂.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  set L : ℂ := (f.coeff 2 : ℂ) + Complex.I * (g.coeff 2 : ℂ) with hL
  have hpoly : hermiteBiehlerPolynomial f g
      = C L * X ^ 2 + C (L * (-(w₁ + w₂))) * X + C (L * (w₁ * w₂)) := by
    rw [hfact]
    simp only [C_mul, C_add, C_neg]
    ring
  have hc₁ : (f.coeff 1 : ℂ) + Complex.I * (g.coeff 1 : ℂ) = L * (-(w₁ + w₂)) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp
  have hc₀ : (f.coeff 0 : ℂ) + Complex.I * (g.coeff 0 : ℂ) = L * (w₁ * w₂) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp
  refine ⟨w₁.re, w₂.re, w₁.im, w₂.im, hv₁, hv₂, ?_, ?_, ?_, ?_⟩
  · have := congrArg Complex.re hc₁
    simp [hL, Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    ring_nf at this ⊢
    assumption
  · have := congrArg Complex.im hc₁
    simp [hL, Complex.add_re, Complex.mul_im, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    ring_nf at this ⊢
    assumption
  · have := congrArg Complex.re hc₀
    simp [hL, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    ring_nf at this ⊢
    assumption
  · have := congrArg Complex.im hc₀
    simp [hL, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    ring_nf at this ⊢
    assumption

theorem splits_of_stable_two {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    f.Splits ∧ g.Splits := by
  have ha : 0 < f.coeff 2 := by rw [← hf₂]; exact hf
  have hb : 0 < g.coeff 2 := by rw [← hg₂]; exact hg
  obtain ⟨u₁, u₂, v₁, v₂, hv₁, hv₂, hb₁, hb₂, hcf, hcg⟩ :=
    hermiteBiehler_vieta_two_posLead ha hf₂ hg₂ hstab
  have hdiscf : 0 ≤ discrim (f.coeff 2) (f.coeff 1) (f.coeff 0) := by
    rw [discrim, hb₁, hcf]
    have := discrim_nonneg_of_im_nonpos_f (a := f.coeff 2) (b := g.coeff 2)
      (u₁ := u₁) (u₂ := u₂) hv₁ hv₂
    assumption
  have hdiscg : 0 ≤ discrim (g.coeff 2) (g.coeff 1) (g.coeff 0) := by
    rw [discrim, hb₂, hcg]
    have := discrim_nonneg_of_im_nonpos_g (a := f.coeff 2) (b := g.coeff 2)
      (u₁ := u₁) (u₂ := u₂) hv₁ hv₂
    assumption
  have hfexp : f = C (f.coeff 2) * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) :=
    eq_X_sq_add_X_add_C_of_natDegree_le_two (by lia)
  have hgexp : g = C (g.coeff 2) * X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) :=
    eq_X_sq_add_X_add_C_of_natDegree_le_two (by lia)
  constructor
  · rw [hfexp]
    exact splits_of_discrim_nonneg (ne_of_gt ha) hdiscf
  · rw [hgexp]
    exact splits_of_discrim_nonneg (ne_of_gt hb) hdiscg

lemma interlace_core_abstract {a b b₁ b₂ c₁ c₂ p q K : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hK0 : 0 ≤ K)
    (hDf : b₁ ^ 2 - 4 * a * c₁ = p ^ 2 + K)
    (hDg : b₂ ^ 2 - 4 * b * c₂ = q ^ 2 + K)
    (ht0 : 0 ≤ a * b₂ - b * b₁)
    (ht2 : (a * b₂ - b * b₁) ^ 2
      = b ^ 2 * (p ^ 2 + K) + a ^ 2 * (q ^ 2 + K) - 2 * (a * b * (p * q))) :
    (-b₂ - Real.sqrt (b₂ ^ 2 - 4 * b * c₂)) / (2 * b)
        ≤ (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a) ∧
      (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a)
        ≤ (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * b * c₂)) / (2 * b) ∧
      (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * b * c₂)) / (2 * b)
        ≤ (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a) := by
  have hDf0 : 0 ≤ b₁ ^ 2 - 4 * a * c₁ := by rw [hDf]; positivity
  have hDg0 : 0 ≤ b₂ ^ 2 - 4 * b * c₂ := by rw [hDg]; positivity
  set A := Real.sqrt (b₁ ^ 2 - 4 * a * c₁) with hA
  set B := Real.sqrt (b₂ ^ 2 - 4 * b * c₂) with hB
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hA2 : A ^ 2 = p ^ 2 + K := by simp_all
  have hB2 : B ^ 2 = q ^ 2 + K := by simp_all
  have hA'0 : 0 ≤ b * A := mul_nonneg hb.le hA0
  have hB'0 : 0 ≤ a * B := mul_nonneg ha.le hB0
  have ht2' : (a * b₂ - b * b₁) ^ 2
      = (b * A) ^ 2 + (a * B) ^ 2 - 2 * (a * b * (p * q)) := by
    rw [mul_pow, mul_pow, hA2, hB2, ht2]
  have hprodsq : (a * b * (p * q)) ^ 2 ≤ (b * A * (a * B)) ^ 2 := by
    have hABsq : (b * A * (a * B)) ^ 2 = a ^ 2 * b ^ 2 * ((p ^ 2 + K) * (q ^ 2 + K)) := by
      have : (b * A * (a * B)) ^ 2 = b ^ 2 * a ^ 2 * (A ^ 2 * B ^ 2) := by ring
      rw [this, hA2, hB2]; ring
    have key : a ^ 2 * b ^ 2 * ((p ^ 2 + K) * (q ^ 2 + K)) - (a * b * (p * q)) ^ 2
        = (a ^ 2 * b ^ 2 * K) * (p ^ 2 + q ^ 2 + K) := by ring
    have hpos : 0 ≤ (a ^ 2 * b ^ 2 * K) * (p ^ 2 + q ^ 2 + K) := by positivity
    rw [hABsq]
    linarith [key, hpos]
  have hAB0 : 0 ≤ b * A * (a * B) := mul_nonneg hA'0 hB'0
  have hle1 : a * b * (p * q) ≤ b * A * (a * B) := by nlinarith [hprodsq, hAB0]
  have hle2 : -(a * b * (p * q)) ≤ b * A * (a * B) := by nlinarith [hprodsq, hAB0]
  obtain ⟨h₁, h₂, h₃⟩ := triangle_of_sq hA'0 hB'0 ht0 ht2' hle1 hle2
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by simp [*]) (by simp [*])]
    nlinarith [h₁]
  · rw [div_le_div_iff₀ (by simp [*]) (by simp [*])]
    nlinarith [h₃]
  · rw [div_le_div_iff₀ (by simp [*]) (by simp [*])]
    nlinarith [h₂]

lemma interlace_core_posLead {a b u₁ u₂ v₁ v₂ b₁ b₂ c₁ c₂ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0)
    (hb₁ : b₁ = -(a * (u₁ + u₂)) + b * (v₁ + v₂))
    (hb₂ : b₂ = -(a * (v₁ + v₂)) - b * (u₁ + u₂))
    (hc₁ : c₁ = a * (u₁ * u₂ - v₁ * v₂) - b * (u₁ * v₂ + u₂ * v₁))
    (hc₂ : c₂ = a * (u₁ * v₂ + u₂ * v₁) + b * (u₁ * u₂ - v₁ * v₂)) :
    (-b₂ - Real.sqrt (b₂ ^ 2 - 4 * b * c₂)) / (2 * b)
        ≤ (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a) ∧
      (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a)
        ≤ (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * b * c₂)) / (2 * b) ∧
      (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * b * c₂)) / (2 * b)
        ≤ (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a) := by
  have : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  refine interlace_core_abstract (p := a * (u₁ - u₂) - b * (v₁ - v₂))
    (q := b * (u₁ - u₂) + a * (v₁ - v₂)) (K := 4 * (a ^ 2 + b ^ 2) * (v₁ * v₂))
    ha hb (by positivity) ?_ ?_ ?_ ?_
  · rw [hb₁, hc₁]; ring
  · rw [hb₂, hc₂]; ring
  · have htid : a * b₂ - b * b₁ = -((a ^ 2 + b ^ 2) * (v₁ + v₂)) := by
      rw [hb₁, hb₂]
      ring
    rw [htid]
    have hsum : v₁ + v₂ ≤ 0 := add_nonpos hv₁ hv₂
    nlinarith [sq_nonneg a, sq_nonneg b]
  · rw [hb₁, hb₂]; ring

theorem prec_of_stable_two {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    Prec g f := by
  obtain ⟨hfs, hgs⟩ := splits_of_stable_two hf hg hf₂ hg₂ hstab
  have ha : 0 < f.coeff 2 := by
    rw [← hf₂]
    exact hf
  have h_b_pos : 0 < g.coeff 2 := by
    rw [← hg₂]
    exact hg
  have h_f_ne : f ≠ 0 := fun h_zero => by simp [h_zero] at ha
  have h_g_ne : g ≠ 0 := fun h_zero => by simp [h_zero] at h_b_pos
  obtain ⟨u₁, u₂, v₁, v₂, hv₁, hv₂, hb₁, hb₂, h_cf, h_cg⟩ :=
    hermiteBiehler_vieta_two_posLead ha hf₂ hg₂ hstab
  have hfexp : f = C (f.coeff 2) * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) :=
    eq_X_sq_add_X_add_C_of_natDegree_le_two (by lia)
  have hgexp : g = C (g.coeff 2) * X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) :=
    eq_X_sq_add_X_add_C_of_natDegree_le_two (by lia)
  set a := f.coeff 2
  set bb := g.coeff 2
  set b₁ := f.coeff 1
  set c₁ := f.coeff 0
  set b₂ := g.coeff 1
  set c₂ := g.coeff 0
  have hvv : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  have hDf₀ : 0 ≤ b₁ ^ 2 - 4 * a * c₁ := by
    have : b₁ ^ 2 - 4 * a * c₁
        = (a * (u₁ - u₂) - bb * (v₁ - v₂)) ^ 2 + 4 * (a ^ 2 + bb ^ 2) * (v₁ * v₂) := by
      rw [hb₁, h_cf]
      ring
    rw [this]
    positivity
  have hDg₀ : 0 ≤ b₂ ^ 2 - 4 * bb * c₂ := by
    have : b₂ ^ 2 - 4 * bb * c₂
        = (bb * (u₁ - u₂) + a * (v₁ - v₂)) ^ 2 + 4 * (a ^ 2 + bb ^ 2) * (v₁ * v₂) := by
      rw [hb₂, h_cg]
      ring
    rw [this]
    positivity
  have hfroots : f.roots = {(-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a),
      (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a)} := by
    conv_lhs => rw [hfexp]
    exact roots_quadratic_posLead ha hDf₀
  have hgroots : g.roots = {(-b₂ - Real.sqrt (b₂ ^ 2 - 4 * bb * c₂)) / (2 * bb),
      (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * bb * c₂)) / (2 * bb)} := by
    conv_lhs => rw [hgexp]
    exact roots_quadratic_posLead h_b_pos hDg₀
  obtain ⟨h₁, h₂, h₃⟩ :=
    interlace_core_posLead ha h_b_pos hv₁ hv₂ hb₁ hb₂ h_cf h_cg
  refine ⟨⟨h_g_ne, hgs⟩, ⟨h_f_ne, hfs⟩,
    [(-b₂ - Real.sqrt (b₂ ^ 2 - 4 * bb * c₂)) / (2 * bb),
      (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * bb * c₂)) / (2 * bb)],
    [(-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a),
      (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a)],
    ?_, ?_, ?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
    linarith
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
    linarith
  · rw [hgroots]
    rfl
  · rw [hfroots]
    rfl
  · simp only [ListAlternates, ListInterlaces, and_true]
    exact ⟨h₁, h₂, h₃⟩

theorem hermiteBiehler_map_conj (f g : ℝ[X]) :
    (hermiteBiehlerPolynomial f g).map (starRingEnd ℂ)
      = complexify f - C Complex.I * complexify g := by
  have hcf : ∀ p : ℝ[X], (complexify p).map (starRingEnd ℂ) = complexify p := by
    intro p
    simp only [complexify, Polynomial.map_map]
    congr 1
    ext x
    simp
  simp only [hermiteBiehlerPolynomial, Polynomial.map_add, Polynomial.map_mul, map_C,
    Complex.conj_I, hcf, C_neg]
  ring

theorem map_conj_of_roots_real {p : ℂ[X]} (hroots : ∀ z ∈ p.roots, z.im = 0) :
    p.map (starRingEnd ℂ)
      = C ((starRingEnd ℂ) p.leadingCoeff) * (p.roots.map fun r => X - C r).prod := by
  have hsplits : p.Splits := IsAlgClosed.splits _
  conv_lhs => rw [hsplits.eq_prod_roots]
  rw [Polynomial.map_mul, map_C, Polynomial.map_multiset_prod, Multiset.map_map]
  congr 1
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun r hr => ?_)
  simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
  rw [Complex.conj_eq_iff_im.mpr (hroots r hr)]

theorem map_conj_self_of_roots_real {p : ℂ[X]}
    (hlc : (starRingEnd ℂ) p.leadingCoeff = p.leadingCoeff)
    (hroots : ∀ z ∈ p.roots, z.im = 0) :
    p.map (starRingEnd ℂ) = p := by
  have hsplits : p.Splits := IsAlgClosed.splits _
  rw [map_conj_of_roots_real hroots, hlc, ← hsplits.eq_prod_roots]

theorem map_conj_neg_of_roots_real {p : ℂ[X]}
    (hlc : (starRingEnd ℂ) p.leadingCoeff = -p.leadingCoeff)
    (hroots : ∀ z ∈ p.roots, z.im = 0) :
    p.map (starRingEnd ℂ) = -p := by
  have hsplits : p.Splits := IsAlgClosed.splits _
  rw [map_conj_of_roots_real hroots, hlc, map_neg, neg_mul, ← hsplits.eq_prod_roots]

theorem g_eq_zero_of_hermiteBiehler_map_conj_self {f g : ℝ[X]}
    (h : (hermiteBiehlerPolynomial f g).map (starRingEnd ℂ) = hermiteBiehlerPolynomial f g) :
    g = 0 := by
  rw [hermiteBiehler_map_conj, hermiteBiehlerPolynomial, sub_eq_add_neg] at h
  have h_cg : complexify g = 0 := by
    have h_neg : -(C Complex.I * complexify g) = C Complex.I * complexify g := add_left_cancel h
    rw [CharZero.neg_eq_self_iff, mul_eq_zero, C_eq_zero] at h_neg
    simpa using h_neg
  simpa [complexify] using h_cg

theorem f_eq_zero_of_hermiteBiehler_map_conj_neg {f g : ℝ[X]}
    (h : (hermiteBiehlerPolynomial f g).map (starRingEnd ℂ) = -hermiteBiehlerPolynomial f g) :
    f = 0 := by
  rw [hermiteBiehler_map_conj, hermiteBiehlerPolynomial, neg_add] at h
  have h_cf : complexify f = 0 := by
    have h_eq : complexify f = - complexify f := add_right_cancel h
    rwa [CharZero.eq_neg_self_iff] at h_eq
  simpa [complexify] using h_cf

lemma hermiteBiehler_natDegree_of_left_dominant {f g : ℝ[X]} (hf : f ≠ 0)
    (h : g.natDegree < f.natDegree) :
    (hermiteBiehlerPolynomial f g).natDegree = f.natDegree ∧
      (hermiteBiehlerPolynomial f g).leadingCoeff = (f.leadingCoeff : ℂ) := by
  have hcd : (hermiteBiehlerPolynomial f g).coeff f.natDegree = (f.leadingCoeff : ℂ) := by
    rw [hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt h]
    simp [coeff_natDegree]
  have hdeg : (hermiteBiehlerPolynomial f g).natDegree = f.natDegree := by
    apply le_antisymm
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt hn,
        coeff_eq_zero_of_natDegree_lt (h.trans hn)]
      simp
    · exact le_natDegree_of_ne_zero (hcd.symm ▸ by simp [hf])
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hcd]⟩

lemma hermiteBiehler_natDegree_of_right_dominant {f g : ℝ[X]} (hg : g ≠ 0)
    (h : f.natDegree < g.natDegree) :
    (hermiteBiehlerPolynomial f g).natDegree = g.natDegree ∧
      (hermiteBiehlerPolynomial f g).leadingCoeff = Complex.I * (g.leadingCoeff : ℂ) := by
  have hcd : (hermiteBiehlerPolynomial f g).coeff g.natDegree
      = Complex.I * (g.leadingCoeff : ℂ) := by
    rw [hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt h]
    simp [coeff_natDegree]
  have hdeg : (hermiteBiehlerPolynomial f g).natDegree = g.natDegree := by
    apply le_antisymm
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt (h.trans hn),
        coeff_eq_zero_of_natDegree_lt hn]
      simp
    · exact le_natDegree_of_ne_zero (hcd.symm ▸ by simp [hg])
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hcd]⟩

theorem roots_real_of_stable_sum_im_zero {p : ℂ[X]} (hstab : IsUpperHalfPlaneStable p)
    (hsum : p.roots.sum.im = 0) : ∀ z ∈ p.roots, z.im = 0 := by
  have hmap : ((p.roots.map Complex.im).sum : ℝ) = 0 := by
    rw [← multiset_sum_im]
    simp [*]
  have hnp : ∀ x ∈ p.roots.map Complex.im, x ≤ 0 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
    exact im_nonpos_of_stable_root hstab ((mem_roots'.mp hz).2)
  intro z hz
  exact multiset_sum_nonpos_eq_zero hnp hmap z.im (Multiset.mem_map_of_mem _ hz)

theorem natDegree_left_le_succ_of_stable {f g : ℝ[X]} (hf : HasPosLeadingCoeff f)
    (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    f.natDegree ≤ g.natDegree + 1 := by
  by_contra hcon
  obtain ⟨hdeg, hlead⟩ :=
    hermiteBiehler_natDegree_of_left_dominant (f := f) (g := g) hf.ne_zero (by lia)
  have hsplits : (hermiteBiehlerPolynomial f g).Splits := IsAlgClosed.splits _
  have hvieta := hsplits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hglt : g.natDegree < f.natDegree - 1 := by lia
  have hnc : (hermiteBiehlerPolynomial f g).nextCoeff
      = ((f.coeff (f.natDegree - 1) : ℝ) : ℂ) := by
    rw [nextCoeff_of_natDegree_pos (by lia : 0 < (hermiteBiehlerPolynomial f g).natDegree),
      hdeg, hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt hglt]
    simp
  rw [hnc, hlead] at hvieta
  have him : (hermiteBiehlerPolynomial f g).roots.sum.im = 0 := by
    have h1 := congrArg Complex.im hvieta
    simp only [Complex.ofReal_im, Complex.mul_im, Complex.neg_im,
      Complex.ofReal_re, zero_mul, add_zero, neg_mul, zero_eq_neg] at h1
    have : (0 : ℝ) < f.leadingCoeff := hf
    rcases mul_eq_zero.mp h1 with h' | h'
    · simp_all
    · simp [*]
  have hreal := roots_real_of_stable_sum_im_zero hstab him
  have hconj : (hermiteBiehlerPolynomial f g).map (starRingEnd ℂ)
      = hermiteBiehlerPolynomial f g :=
    map_conj_self_of_roots_real (by simp [*]) hreal
  exact hg.ne_zero (g_eq_zero_of_hermiteBiehler_map_conj_self hconj)

theorem natDegree_right_le_of_stable {f g : ℝ[X]} (hf : HasPosLeadingCoeff f)
    (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    g.natDegree ≤ f.natDegree := by
  by_contra hcon
  have hlt : f.natDegree < g.natDegree := by lia
  obtain ⟨hdeg, hlead⟩ := hermiteBiehler_natDegree_of_right_dominant hg.ne_zero hlt
  have hsplits : (hermiteBiehlerPolynomial f g).Splits := IsAlgClosed.splits _
  have hvieta := hsplits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hnc : (hermiteBiehlerPolynomial f g).nextCoeff
      = ((f.coeff (g.natDegree - 1) : ℝ) : ℂ)
        + Complex.I * ((g.coeff (g.natDegree - 1) : ℝ) : ℂ) := by
    rw [nextCoeff_of_natDegree_pos (by lia : 0 < (hermiteBiehlerPolynomial f g).natDegree),
      hdeg, hermiteBiehler_coeff]
  rw [hnc, hlead] at hvieta
  have hre : f.coeff (g.natDegree - 1)
      = g.leadingCoeff * (hermiteBiehlerPolynomial f g).roots.sum.im := by
    have h1 := congrArg Complex.re hvieta
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, one_mul, mul_zero, zero_add, add_zero, sub_zero, zero_sub,
      neg_mul, neg_neg] at h1
    assumption
  have hsim : (hermiteBiehlerPolynomial f g).roots.sum.im ≤ 0 := by
    rw [multiset_sum_im]
    apply multiset_sum_nonpos
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
    exact im_nonpos_of_stable_root hstab ((mem_roots'.mp hz).2)
  rcases Nat.lt_or_ge (f.natDegree + 1) g.natDegree with hcase | hcase
  · have hfc : f.coeff (g.natDegree - 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by lia)
    have him : (hermiteBiehlerPolynomial f g).roots.sum.im = 0 := by
      rw [hfc] at hre
      have hg' : (0 : ℝ) < g.leadingCoeff := hg
      rcases mul_eq_zero.mp hre.symm with h' | h'
      · exact absurd h' (ne_of_gt hg')
      · exact h'
    have hreal := roots_real_of_stable_sum_im_zero hstab him
    have hconj : (hermiteBiehlerPolynomial f g).map (starRingEnd ℂ)
        = -hermiteBiehlerPolynomial f g := by
      apply map_conj_neg_of_roots_real _ hreal
      simp [*]
    exact hf.ne_zero (f_eq_zero_of_hermiteBiehler_map_conj_neg hconj)
  · have hdeq : g.natDegree - 1 = f.natDegree := by lia
    have hfc : f.coeff (g.natDegree - 1) = f.leadingCoeff := by simp [*]
    rw [hfc] at hre
    have : (0 : ℝ) < f.leadingCoeff := hf
    have : (0 : ℝ) < g.leadingCoeff := hg
    nlinarith [this, hre, hsim]

theorem natDegree_shape_of_stable {f g : ℝ[X]} (hf : HasPosLeadingCoeff f)
    (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    g.natDegree ≤ f.natDegree ∧ f.natDegree ≤ g.natDegree + 1 :=
  ⟨natDegree_right_le_of_stable hf hg hstab,
    natDegree_left_le_succ_of_stable hf hg hstab⟩

private lemma nonpos_le_of_sq_le_sq {W X : ℝ} (hW : W ≤ 0) (h : X ^ 2 ≤ W ^ 2) :
    W ≤ X ∧ W ≤ -X := by
  constructor <;> nlinarith [sq_nonneg (W - X), sq_nonneg (W + X)]

lemma interlace_core_two_one {a u₁ u₂ v₁ v₂ b₁ b₂ c₁ c₂ : ℝ} (ha : 0 < a)
    (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0) (hb₂_pos : 0 < b₂)
    (hb₁ : b₁ = -(a * (u₁ + u₂))) (hb₂ : b₂ = -(a * (v₁ + v₂)))
    (hc₁ : c₁ = a * (u₁ * u₂ - v₁ * v₂))
    (hc₂ : c₂ = a * (u₁ * v₂ + u₂ * v₁)) :
    (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a) ≤ -c₂ / b₂ ∧
      -c₂ / b₂ ≤ (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a) := by
  have hvv : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  have hinner : 0 ≤ (u₁ - u₂) ^ 2 + 4 * (v₁ * v₂) := by
    nlinarith [sq_nonneg (u₁ - u₂)]
  have hd : b₁ ^ 2 - 4 * a * c₁ =
      a ^ 2 * ((u₁ - u₂) ^ 2 + 4 * (v₁ * v₂)) := by
    rw [hb₁, hc₁]
    ring
  have hD₀ : 0 ≤ b₁ ^ 2 - 4 * a * c₁ := by simp_all
  set t := Real.sqrt (b₁ ^ 2 - 4 * a * c₁) with ht
  have ht₀ : 0 ≤ t := Real.sqrt_nonneg _
  have ht₂ : t ^ 2 = a ^ 2 * ((u₁ - u₂) ^ 2 + 4 * (v₁ * v₂)) := by
    rw [ht, Real.sq_sqrt hD₀, hd]
  have hS : v₁ + v₂ < 0 := by
    by_contra hcon
    have hge : 0 ≤ a * (v₁ + v₂) := mul_nonneg ha.le (not_lt.mp hcon)
    rw [hb₂] at hb₂_pos; linarith
  have hW0 : t * (a * (v₁ + v₂)) ≤ 0 := by nlinarith [mul_nonneg ht₀ ha.le]
  have hWsq : (t * (a * (v₁ + v₂))) ^ 2 =
      a ^ 2 * ((u₁ - u₂) ^ 2 + 4 * (v₁ * v₂)) * (a ^ 2 * (v₁ + v₂) ^ 2) := by
    rw [mul_pow, ht₂]; ring
  have hdiff : (t * (a * (v₁ + v₂))) ^ 2 - (a ^ 2 * ((u₁ - u₂) * (v₁ - v₂))) ^ 2 =
      4 * (a ^ 2 * a ^ 2) * (v₁ * v₂) * ((u₁ - u₂) ^ 2 + (v₁ + v₂) ^ 2) := by
    rw [hWsq]; ring
  have hrhs :
      0 ≤
        4 * (a ^ 2 * a ^ 2) * (v₁ * v₂) *
          ((u₁ - u₂) ^ 2 + (v₁ + v₂) ^ 2) := by
    have h₁ : (0 : ℝ) ≤ 4 * (a ^ 2 * a ^ 2) := by positivity
    have h₂ : (0 : ℝ) ≤ (u₁ - u₂) ^ 2 + (v₁ + v₂) ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg h₁ hvv) h₂
  have hsq :
      (a ^ 2 * ((u₁ - u₂) * (v₁ - v₂))) ^ 2 ≤ (t * (a * (v₁ + v₂))) ^ 2 := by
    linarith
  obtain ⟨hle₁, hle₂⟩ := nonpos_le_of_sq_le_sq hW0 hsq
  constructor
  · rw [div_le_div_iff₀ (by simp [*]) hb₂_pos]
    rw [hb₁, hb₂, hc₂]
    nlinarith [hle₁]
  · rw [div_le_div_iff₀ hb₂_pos (by simp [*])]
    rw [hb₁, hb₂, hc₂]
    nlinarith [hle₂]

lemma hermiteBiehler_factor_two_left {f g : ℝ[X]} (h_f_ne : f ≠ 0)
    (hf₂ : f.natDegree = 2) (hgd : g.natDegree < 2) :
    ∃ w₁ w₂ : ℂ, hermiteBiehlerPolynomial f g =
        C ((f.coeff 2 : ℝ) : ℂ) * ((X - C w₁) * (X - C w₂)) ∧
      (hermiteBiehlerPolynomial f g).roots = {w₁, w₂} := by
  obtain ⟨hdeg, hlead⟩ :=
    hermiteBiehler_natDegree_of_left_dominant h_f_ne (show g.natDegree < f.natDegree by simp [*])
  rw [hf₂] at hdeg
  have hsplits : (hermiteBiehlerPolynomial f g).Splits := IsAlgClosed.splits _
  have hcard : (hermiteBiehlerPolynomial f g).roots.card = 2 := by
    rw [splits_iff_card_roots.mp hsplits, hdeg]
  obtain ⟨w₁, w₂, hroots⟩ := Multiset.card_eq_two.mp hcard
  refine ⟨w₁, w₂, ?_, hroots⟩
  have hlc : (hermiteBiehlerPolynomial f g).leadingCoeff = ((f.coeff 2 : ℝ) : ℂ) := by
    rw [hlead, Polynomial.leadingCoeff, hf₂]
  have := hsplits.eq_prod_roots
  rw [hlc, hroots] at this
  simp [*]

lemma hermiteBiehler_vieta_two_one {f g : ℝ[X]}
    (hf : 0 < f.coeff 2) (hf₂ : f.natDegree = 2) (hgd : g.natDegree < 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    ∃ u₁ u₂ v₁ v₂ : ℝ, v₁ ≤ 0 ∧ v₂ ≤ 0 ∧
      f.coeff 1 = -(f.coeff 2 * (u₁ + u₂)) ∧
      g.coeff 1 = -(f.coeff 2 * (v₁ + v₂)) ∧
      f.coeff 0 = f.coeff 2 * (u₁ * u₂ - v₁ * v₂) ∧
      g.coeff 0 = f.coeff 2 * (u₁ * v₂ + u₂ * v₁) := by
  have h_f_ne : f ≠ 0 := fun h_zero => by simp [h_zero] at hf
  obtain ⟨w₁, w₂, hfact, hroots⟩ := hermiteBiehler_factor_two_left h_f_ne hf₂ hgd
  have hne : hermiteBiehlerPolynomial f g ≠ 0 := by
    intro h_zero
    simp_all
  have hv₁ : w₁.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  have hv₂ : w₂.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  set L : ℂ := ((f.coeff 2 : ℝ) : ℂ) with hL
  have hpoly : hermiteBiehlerPolynomial f g
      = C L * X ^ 2 + C (L * (-(w₁ + w₂))) * X + C (L * (w₁ * w₂)) := by
    rw [hfact]
    simp only [C_mul, C_add, C_neg]
    ring
  have hc₁ : (f.coeff 1 : ℂ) + Complex.I * (g.coeff 1 : ℂ) = L * (-(w₁ + w₂)) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp
  have hc₀ : (f.coeff 0 : ℂ) + Complex.I * (g.coeff 0 : ℂ) = L * (w₁ * w₂) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp
  refine ⟨w₁.re, w₂.re, w₁.im, w₂.im, hv₁, hv₂, ?_, ?_, ?_, ?_⟩
  · have := congrArg Complex.re hc₁
    simp [hL, Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    ring_nf at this ⊢
    assumption
  · have := congrArg Complex.im hc₁
    simp [hL, Complex.add_re, Complex.mul_im, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    ring_nf at this ⊢
    assumption
  · have := congrArg Complex.re hc₀
    simp [hL, Complex.add_re, Complex.mul_re, Complex.mul_im] at this
    assumption
  · have := congrArg Complex.im hc₀
    simp [hL, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    ring_nf at this ⊢
    assumption

theorem prec_of_stable_two_one {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hf₂ : f.natDegree = 2) (hg₁ : g.natDegree = 1)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) : Prec g f := by
  have ha : 0 < f.coeff 2 := by
    rw [← hf₂]
    exact hf
  have hb₂_pos : 0 < g.coeff 1 := by
    rw [← hg₁]
    exact hg
  have h_f_ne : f ≠ 0 := fun h_zero ↦ by simp [h_zero] at ha
  have h_g_ne : g ≠ 0 := fun h_zero ↦ by simp [h_zero] at hb₂_pos
  obtain ⟨u₁, u₂, v₁, v₂, hv₁, hv₂, hb₁, hb₂, hc₁, hc₂⟩ :=
    hermiteBiehler_vieta_two_one ha hf₂ (by simp [*]) hstab
  have hfexp : f = C (f.coeff 2) * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) :=
    eq_X_sq_add_X_add_C_of_natDegree_le_two (by lia)
  have hgexp : g = C (g.coeff 1) * X + C (g.coeff 0) := by
    ext n
    rcases n with _ | _ | n
    · simp
    · simp
    · have h_lt : g.natDegree < n + 2 := by
        rw [hg₁]
        lia
      have hz : g.coeff (n + 2) = 0 := coeff_eq_zero_of_natDegree_lt h_lt
      simp [coeff_add, hz]
  set a := f.coeff 2
  set b₁ := f.coeff 1
  set c₁ := f.coeff 0
  set b₂ := g.coeff 1
  set c₂ := g.coeff 0
  have hvv : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  have hDf₀ : 0 ≤ b₁ ^ 2 - 4 * a * c₁ := by
    have hdd : b₁ ^ 2 - 4 * a * c₁ = a ^ 2 * ((u₁ - u₂) ^ 2 + 4 * (v₁ * v₂)) := by
      rw [hb₁, hc₁]
      ring
    rw [hdd]
    exact mul_nonneg (sq_nonneg a) (by nlinarith [sq_nonneg (u₁ - u₂)])
  have hfroots : f.roots = {(-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a),
      (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a)} := by
    conv_lhs => rw [hfexp]
    exact roots_quadratic_posLead ha hDf₀
  have hb₂_ne : b₂ ≠ 0 := ne_of_gt hb₂_pos
  have hgfact : g = C b₂ * (X - C (-c₂ / b₂)) := by
    rw [hgexp, mul_sub, ← C_mul]
    have : b₂ * (-c₂ / b₂) = -c₂ := by field_simp
    rw [this, C_neg, sub_neg_eq_add]
  have hgroots : g.roots = {-c₂ / b₂} := by rw [hgfact, roots_C_mul _ hb₂_ne, roots_X_sub_C]
  have hfs : f.Splits := splits_of_card_roots (by rw [hfroots, hf₂]; simp)
  have hgs : g.Splits := splits_of_card_roots (by rw [hgroots, hg₁]; simp)
  obtain ⟨h₁, h₂⟩ := interlace_core_two_one ha hv₁ hv₂ hb₂_pos hb₁ hb₂ hc₁ hc₂
  refine ⟨⟨h_g_ne, hgs⟩, ⟨h_f_ne, hfs⟩,
    [-c₂ / b₂],
    [(-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a),
      (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a)],
    ?_, ?_, ?_, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · simp
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
    linarith
  · rw [hgroots]
    simp
  · rw [hfroots]
    rfl
  · simp only [ListInterlaces, and_true]
    exact ⟨h₁, h₂⟩

theorem hermiteBiehlerConverse_of_natDegree_le_two {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : f.natDegree ≤ 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    Prec g f ∨ Prec f g := by
  obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable hf hg hstab
  rcases Nat.lt_or_ge f.natDegree 2 with hflt | hfge
  · exact prec_or_revPrec_of_natDegree_le_one hg hf (by lia) (by lia)
  · have hf₂ : f.natDegree = 2 := by lia
    rcases Nat.lt_or_ge g.natDegree 2 with hglt | hgge
    · have hg₁ : g.natDegree = 1 := by lia
      exact Or.inl (prec_of_stable_two_one hf hg hf₂ hg₁ hstab)
    · have hg₂ : g.natDegree = 2 := by lia
      exact Or.inl (prec_of_stable_two hf hg hf₂ hg₂ hstab)

lemma norm_conj_sub_le {z w : ℂ} (hz : 0 < z.im) (hw : w.im ≤ 0) :
    ‖(starRingEnd ℂ) z - w‖ ≤ ‖z - w‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im]
  nlinarith [mul_nonneg hz.le (neg_nonneg.mpr hw)]

lemma norm_conj_sub_lt {z w : ℂ} (hz : 0 < z.im) (hw : w.im < 0) :
    ‖(starRingEnd ℂ) z - w‖ < ‖z - w‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_lt_sqrt (Complex.normSq_nonneg _)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im]
  nlinarith [mul_pos hz (neg_pos.mpr hw)]

lemma multiset_prod_norm_conj_le {z : ℂ} (hz : 0 < z.im) (S : Multiset ℂ)
    (hS : ∀ w ∈ S, w.im ≤ 0) :
    ‖(S.map fun w => (starRingEnd ℂ) z - w).prod‖ ≤ ‖(S.map fun w => z - w).prod‖ := by
  induction S using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    have ha := hS a (Multiset.mem_cons_self a s)
    have hs : ∀ w ∈ s, w.im ≤ 0 := fun w hw => hS w (Multiset.mem_cons_of_mem hw)
    exact mul_le_mul (norm_conj_sub_le hz ha) (ih hs) (norm_nonneg _) (norm_nonneg _)

lemma multiset_prod_norm_conj_lt {z : ℂ} (hz : 0 < z.im) (S : Multiset ℂ)
    (hS : ∀ w ∈ S, w.im ≤ 0) {w₀ : ℂ} (hw₀ : w₀ ∈ S) (hneg : w₀.im < 0) :
    ‖(S.map fun w => (starRingEnd ℂ) z - w).prod‖ < ‖(S.map fun w => z - w).prod‖ := by
  obtain ⟨S', rfl⟩ : ∃ S', S = w₀ ::ₘ S' :=
    ⟨S.erase w₀, (Multiset.cons_erase hw₀).symm⟩
  simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
  have hS' : ∀ w ∈ S', w.im ≤ 0 := fun w hw => hS w (Multiset.mem_cons_of_mem hw)
  have h_norm_pos : 0 < ‖(S'.map fun w => z - w).prod‖ := by
    rw [norm_pos_iff]
    apply Multiset.prod_ne_zero
    intro h_zero
    obtain ⟨w, hw, hzw⟩ := Multiset.mem_map.mp h_zero
    have him : (z - w).im = 0 := by simp [*]
    have := hS' w hw
    simp only [Complex.sub_im] at him
    linarith
  calc ‖(starRingEnd ℂ) z - w₀‖ * ‖(S'.map fun w => (starRingEnd ℂ) z - w).prod‖
      ≤ ‖(starRingEnd ℂ) z - w₀‖ * ‖(S'.map fun w => z - w).prod‖ :=
        mul_le_mul_of_nonneg_left (multiset_prod_norm_conj_le hz S' hS') (norm_nonneg _)
    _ < ‖z - w₀‖ * ‖(S'.map fun w => z - w).prod‖ :=
        mul_lt_mul_of_pos_right (norm_conj_sub_lt hz hneg) h_norm_pos

lemma eval_eq_prod_roots_complex (p : ℂ[X]) (x : ℂ) :
    p.eval x = p.leadingCoeff * (p.roots.map fun a => x - a).prod := by
  conv_lhs => rw [(IsAlgClosed.splits p).eq_prod_roots]
  simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Function.comp_apply,
    eval_sub, eval_X]

lemma roots_real_of_stable_norm_eq {p : ℂ[X]} (hp : p ≠ 0)
    (hstab : IsUpperHalfPlaneStable p) {z : ℂ} (hz : 0 < z.im)
    (heq : ‖p.eval ((starRingEnd ℂ) z)‖ = ‖p.eval z‖) :
    ∀ w ∈ p.roots, w.im = 0 := by
  intro w₀ hw₀
  by_contra hne
  have hle : ∀ w ∈ p.roots, w.im ≤ 0 := fun w hw =>
    im_nonpos_of_stable_root hstab (isRoot_of_mem_roots hw)
  have hneg : w₀.im < 0 := lt_of_le_of_ne (hle w₀ hw₀) hne
  have :
      ‖(p.roots.map fun w ↦ starRingEnd ℂ z - w).prod‖ <
        ‖(p.roots.map fun w ↦ z - w).prod‖ :=
    multiset_prod_norm_conj_lt hz p.roots hle hw₀ hneg
  rw [eval_eq_prod_roots_complex p, eval_eq_prod_roots_complex p, norm_mul, norm_mul] at heq
  simp_all

lemma no_upper_root_left_of_stable {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hf : HasPosLeadingCoeff f)
    {z : ℂ} (hz : 0 < z.im) (hroot : (complexify f).eval z = 0) : False := by
  set h := hermiteBiehlerPolynomial f g with hh
  have hzim : z.im ≠ 0 := hz.ne'
  have : (complexify g).eval z ≠ 0 := fun hg₀ ↦
    no_common_nonreal_root_of_stable hstab hzim hroot hg₀
  have : h.eval z = Complex.I * (complexify g).eval z := by simp [*]
  have hhz : h.eval z ≠ 0 := by simp [*]
  have hne : h ≠ 0 := fun h_zero ↦ hhz (by rw [h_zero, eval_zero])
  have : h.eval ((starRingEnd ℂ) z) =
      Complex.I * (starRingEnd ℂ) ((complexify g).eval z) := by
    rw [hh, eval_hermiteBiehlerPolynomial, eval_complexify_conj, eval_complexify_conj,
      hroot, map_zero, zero_add]
  have heq : ‖h.eval ((starRingEnd ℂ) z)‖ = ‖h.eval z‖ := by simp_all
  have hroots : ∀ w ∈ h.roots, w.im = 0 :=
    roots_real_of_stable_norm_eq hne hstab hz heq
  set P : ℂ[X] := (h.roots.map fun r ↦ X - C r).prod with hP
  have hfac : h = C h.leadingCoeff * P := (IsAlgClosed.splits (k := ℂ) h).eq_prod_roots
  have hevalh : h.eval z = h.leadingCoeff * P.eval z := by
    conv_lhs => rw [hfac]
    simp
  have hevalhc : (h.map (starRingEnd ℂ)).eval z =
      (starRingEnd ℂ) h.leadingCoeff * P.eval z := by
    rw [map_conj_of_roots_real hroots, eval_mul, eval_C]
  have hsum : h + h.map (starRingEnd ℂ) = 2 * complexify f := by
    rw [hh, hermiteBiehler_map_conj, hermiteBiehlerPolynomial]
    ring
  have hzero : (h.leadingCoeff + (starRingEnd ℂ) h.leadingCoeff) * P.eval z = 0 := by
    have hev := congrArg (fun q : ℂ[X] ↦ q.eval z) hsum
    simp only [eval_add, eval_mul, eval_ofNat] at hev
    rw [hroot, mul_zero, hevalh, hevalhc] at hev
    rw [add_mul]
    exact hev
  have hPz : P.eval z ≠ 0 := by
    intro hP₀
    apply hhz
    rw [hevalh, hP₀, mul_zero]
  have hlceq : (starRingEnd ℂ) h.leadingCoeff = -h.leadingCoeff := by
    rcases mul_eq_zero.mp hzero with hc | hc
    · exact eq_neg_of_add_eq_zero_right hc
    · exact absurd hc hPz
  have hmapneg := map_conj_neg_of_roots_real hlceq hroots
  rw [hh] at hmapneg
  have hf₀ : f = 0 := f_eq_zero_of_hermiteBiehler_map_conj_neg hmapneg
  simp_all

lemma no_upper_root_right_of_stable {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hg : HasPosLeadingCoeff g)
    {z : ℂ} (hz : 0 < z.im) (hroot : (complexify g).eval z = 0) : False := by
  set h := hermiteBiehlerPolynomial f g with hh
  have hzim : z.im ≠ 0 := hz.ne'
  have : (complexify f).eval z ≠ 0 := fun hf₀ ↦
    no_common_nonreal_root_of_stable hstab hzim hf₀ hroot
  have : h.eval z = (complexify f).eval z := by simp [*]
  have hhz : h.eval z ≠ 0 := by simp [*]
  have hne : h ≠ 0 := fun h_zero ↦ hhz (by rw [h_zero, eval_zero])
  have : h.eval ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((complexify f).eval z) := by
    rw [hh, eval_hermiteBiehlerPolynomial, eval_complexify_conj, eval_complexify_conj,
      hroot, map_zero, mul_zero, add_zero]
  have heq : ‖h.eval ((starRingEnd ℂ) z)‖ = ‖h.eval z‖ := by simp_all
  have hroots : ∀ w ∈ h.roots, w.im = 0 :=
    roots_real_of_stable_norm_eq hne hstab hz heq
  set P : ℂ[X] := (h.roots.map fun r ↦ X - C r).prod with hP
  have hfac : h = C h.leadingCoeff * P := (IsAlgClosed.splits (k := ℂ) h).eq_prod_roots
  have hevalh : h.eval z = h.leadingCoeff * P.eval z := by
    conv_lhs => rw [hfac]
    simp
  have hevalhc : (h.map (starRingEnd ℂ)).eval z =
      (starRingEnd ℂ) h.leadingCoeff * P.eval z := by
    rw [map_conj_of_roots_real hroots, eval_mul, eval_C]
  have hdiff : h - h.map (starRingEnd ℂ) = 2 * C Complex.I * complexify g := by
    rw [hh, hermiteBiehler_map_conj, hermiteBiehlerPolynomial]
    ring
  have hzero : (h.leadingCoeff - (starRingEnd ℂ) h.leadingCoeff) * P.eval z = 0 := by
    have hev := congrArg (fun q : ℂ[X] ↦ q.eval z) hdiff
    simp only [eval_sub, eval_mul, eval_ofNat, eval_C] at hev
    rw [hroot, mul_zero, hevalh, hevalhc] at hev
    rw [sub_mul]
    exact hev
  have hPz : P.eval z ≠ 0 := by
    intro hP₀
    apply hhz
    rw [hevalh, hP₀, mul_zero]
  have hlceq : (starRingEnd ℂ) h.leadingCoeff = h.leadingCoeff := by
    rcases mul_eq_zero.mp hzero with hc | hc
    · exact (sub_eq_zero.mp hc).symm
    · exact absurd hc hPz
  have hmapself := map_conj_self_of_roots_real hlceq hroots
  rw [hh] at hmapself
  have hg₀ : g = 0 := g_eq_zero_of_hermiteBiehler_map_conj_self hmapself
  simp_all

theorem splits_of_stable {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    f.Splits ∧ g.Splits := by
  constructor
  · apply Polynomial.splits_of_all_roots_real
    intro z hz
    by_contra him
    rcases lt_or_gt_of_ne him with hlt | hgt
    · exact no_upper_root_left_of_stable hstab hf (by simp [*]) (complexify_conj_root hz)
    · exact no_upper_root_left_of_stable hstab hf hgt hz
  · apply Polynomial.splits_of_all_roots_real
    intro z hz
    by_contra him
    rcases lt_or_gt_of_ne him with hlt | hgt
    · exact no_upper_root_right_of_stable hstab hg (by simp [*]) (complexify_conj_root hz)
    · exact no_upper_root_right_of_stable hstab hg hgt hz

/-- Planning stub for the converse Hermite--Biehler theorem.

The exact orientation hypotheses may still be adjusted, but the target is that
upper-half-plane stability of `f + i g` forces an interlacing relation between
-/
abbrev hermiteBiehlerConverseStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) →
    Prec g f ∨ Prec f g

/-- Analytic bridge from the Hermite--Biehler stable polynomial `q + i p` to
right-half-plane stability of `q(x^2) + x p(x^2)`.

This isolates the classical conformal-substitution part of the
-/
abbrev HermiteBiehlerStableToHurwitzOddEvenStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) →
    IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q))

/-! ## Reduction of the forward Hermite--Biehler/Hurwitz bridge to a
first-quadrant conformal-substitution interface -/

/-- Value of a complexified real polynomial at a real point. -/
theorem eval_complexify_ofReal (p : ℝ[X]) (t : ℝ) :
    (complexify p).eval (t : ℂ) = ((p.eval t : ℝ) : ℂ) := by
  simpa [complexify] using Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := p) t

/-- First-quadrant form of the forward Hermite--Biehler/Hurwitz conformal
substitution: it suffices to exclude roots of `q(x²) + x p(x²)` in the open
first quadrant `{Re > 0, Im > 0}`. -/
abbrev HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) →
    ∀ z : ℂ, 0 < z.re → 0 < z.im →
      (complexify (oddEvenPolynomial p q)).eval z ≠ 0

/-- Upper-half-plane substitution form of the forward Hermite--Biehler/Hurwitz
bridge: for any upper-half-plane point `w` with a right-half-plane square root
`z`, the Hurwitz combination `q(w) + z·p(w)` is nonzero.

This is the genuinely analytic conformal-substitution core: the quadratic map
`z ↦ z²` sends the open first quadrant onto the open upper half-plane, so this
interface and the first-quadrant interface above carry exactly the same
content. -/
abbrev HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) →
    ∀ ⦃w z : ℂ⦄, 0 < w.im → z ^ 2 = w → 0 < z.re →
      (complexify q).eval w + z * (complexify p).eval w ≠ 0

/-- The first-quadrant interface follows from the upper-half-plane substitution
interface: for `z` in the open first quadrant, `w = z²` lies in the open upper
half-plane and `z` is a right-half-plane square root of `w`. -/
theorem hermiteBiehlerStableToHurwitzOddEvenFirstQuadrant_of_upperHalfSubstitution
    (h : HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement) :
    HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement :=
  fun p q h_p h_q h_stable z hzre hzim => by
  rw [eval_complexify_oddEvenPolynomial]
  have h_w : 0 < (z ^ 2).im := by
    rw [pow_two, Complex.mul_im]
    positivity
  simp [*]

/-- Checked reduction of the forward Hermite--Biehler/Hurwitz odd/even bridge to
its first-quadrant conformal-substitution core.

`HermiteBiehlerStableToHurwitzOddEvenStatement` follows from
`HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement`: the real-axis case
`Im z = 0` is handled by positivity of the nonnegative-coefficient polynomial
`q(x²) + x p(x²)`, and the lower half-plane case `Im z < 0` is reduced to the
first quadrant by complex conjugation. -/
theorem hermiteBiehlerStableToHurwitzOddEven_of_firstQuadrant
    (h : HermiteBiehlerStableToHurwitzOddEvenFirstQuadrantStatement) :
    HermiteBiehlerStableToHurwitzOddEvenStatement := by
  intro p q h_p h_q h_stable z hzre
  -- The odd/even polynomial is nonzero, otherwise the stability hypothesis fails.
  have h_f_ne : oddEvenPolynomial p q ≠ 0 := by
    intro h₀
    rw [oddEvenPolynomial_eq_zero_iff] at h₀
    obtain ⟨hp₀, hq₀⟩ := h₀
    have h_I := h_stable Complex.I (by simp)
    simp_all
  rcases lt_trichotomy z.im 0 with h_im | h_im | h_im
  · -- Lower half-plane: reduce to the first quadrant by conjugation.
    have h_conj := eval_complexify_conj (oddEvenPolynomial p q) z
    have h_re : 0 < (starRingEnd ℂ z).re := by simp [*]
    have h_ci : 0 < (starRingEnd ℂ z).im := by simp [*]
    have h_ne : (complexify (oddEvenPolynomial p q)).eval (starRingEnd ℂ z) ≠ 0 :=
      h h_p h_q h_stable (starRingEnd ℂ z) h_re h_ci
    intro h₀
    apply h_ne
    rw [h_conj, h₀, map_zero]
  · -- Real axis: positivity of the nonnegative-coefficient polynomial.
    have h_z : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [h_im]
    rw [h_z, eval_complexify_ofReal]
    have h_pos : 0 < (oddEvenPolynomial p q).eval z.re :=
      eval_pos_of_hasNonnegCoeffs (hasNonnegCoeffs_oddEvenPolynomial h_p h_q) h_f_ne hzre
    simpa using h_pos.ne'
  · -- First quadrant: the interface applies directly.
    exact h h_p h_q h_stable z hzre h_im

/-- Composite reduction: the forward Hermite--Biehler/Hurwitz odd/even bridge
follows from the upper-half-plane substitution interface. -/
theorem hermiteBiehlerStableToHurwitzOddEven_of_upperHalfSubstitution
    (h : HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement) :
    HermiteBiehlerStableToHurwitzOddEvenStatement :=
  hermiteBiehlerStableToHurwitzOddEven_of_firstQuadrant
    (hermiteBiehlerStableToHurwitzOddEvenFirstQuadrant_of_upperHalfSubstitution h)

/-- Packaging form of the analytic Hermite--Biehler-to-Hurwitz odd/even
bridge, including the coefficient half of `IsHurwitzStable`. -/
theorem isHurwitzStable_oddEvenPolynomial_of_hermiteBiehlerStableToHurwitz
    (h : HermiteBiehlerStableToHurwitzOddEvenStatement) {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsHurwitzStable (oddEvenPolynomial p q) :=
  ⟨hasNonnegCoeffs_oddEvenPolynomial hp hq, h hp hq hstable⟩

theorem eval_derivative_eq_sum_complex (p : ℂ[X]) (x : ℂ) :
    p.derivative.eval x
      = p.leadingCoeff * (p.roots.map (fun w =>
          ((p.roots.erase w).map (fun u => x - u)).prod)).sum := by
  have hsplits : p.Splits := IsAlgClosed.splits _
  conv_lhs => rw [hsplits.eq_prod_roots]
  rw [derivative_mul]
  simp only [derivative_C, zero_mul, zero_add, eval_mul, eval_C]
  congr 1
  rw [derivative_prod]
  simp only [eval_multisetSum, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro w hw
  simp only [Function.comp_apply, eval_multiset_prod, Multiset.map_map,
    eval_sub, eval_X, eval_C, derivative_X_sub_C, mul_one]

theorem im_deriv_mul_conj_eq (p : ℂ[X]) (x : ℝ) :
    (p.derivative.eval (x : ℂ) * (starRingEnd ℂ) (p.eval (x : ℂ))).im
      = Complex.normSq p.leadingCoeff *
          (p.roots.map (fun w =>
            Complex.normSq ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod * w.im)).sum := by
  rw [eval_derivative_eq_sum_complex, eval_eq_prod_roots_complex, map_mul]
  set S := (p.roots.map (fun w =>
    ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod)).sum with hS
  set T := (p.roots.map (fun u => (x : ℂ) - u)).prod with hT
  have hre : p.leadingCoeff * S * ((starRingEnd ℂ) p.leadingCoeff * (starRingEnd ℂ) T)
      = ((Complex.normSq p.leadingCoeff : ℝ) : ℂ) * (S * (starRingEnd ℂ) T) := by
    rw [← Complex.mul_conj]
    ring
  rw [hre, Complex.im_ofReal_mul]
  congr 1
  rw [hS, ← Multiset.sum_map_mul_right, multiset_sum_im, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro w hw
  simp only [Function.comp_apply]
  rw [hT, ← Multiset.prod_map_erase (f := fun u => (x : ℂ) - u) hw, map_mul]
  set P := ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod with hP
  have hps : P * ((starRingEnd ℂ) ((x : ℂ) - w) * (starRingEnd ℂ) P)
      = ((Complex.normSq P : ℝ) : ℂ) * (starRingEnd ℂ) ((x : ℂ) - w) := by
    rw [← Complex.mul_conj]
    ring
  simp_all

theorem im_deriv_mul_conj_neg {p : ℂ[X]}
    (hroots : ∀ w ∈ p.roots, w.im ≤ 0)
    {x : ℝ} (hne : p.eval (x : ℂ) ≠ 0)
    {w₀ : ℂ} (hw₀ : w₀ ∈ p.roots) (hneg : w₀.im < 0) :
    (p.derivative.eval (x : ℂ) * (starRingEnd ℂ) (p.eval (x : ℂ))).im < 0 := by
  have hp₀ : p ≠ 0 := fun h_zero => hne (by simp [h_zero])
  rw [im_deriv_mul_conj_eq]
  have hlc : 0 < Complex.normSq p.leadingCoeff :=
    Complex.normSq_pos.mpr (leadingCoeff_ne_zero.mpr hp₀)
  apply mul_neg_of_pos_of_neg hlc
  have hfac : ∀ w ∈ p.roots,
      ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod ≠ 0 := by
    intro w hw hzero
    apply hne
    rw [eval_eq_prod_roots_complex, ← Multiset.prod_map_erase (f := fun u => (x : ℂ) - u) hw,
      hzero, mul_zero, mul_zero]
  rw [← Multiset.sum_map_erase (f := fun w =>
    Complex.normSq ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod * w.im) hw₀]
  have hterm :
      Complex.normSq ((p.roots.erase w₀).map (fun u => (x : ℂ) - u)).prod *
        w₀.im < 0 := by
    have hP : ((p.roots.erase w₀).map (fun u => (x : ℂ) - u)).prod ≠ 0 := hfac w₀ hw₀
    exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hP) hneg
  have hrest : ((p.roots.erase w₀).map (fun w =>
      Complex.normSq ((p.roots.erase w).map (fun u => (x : ℂ) - u)).prod * w.im)).sum ≤ 0 := by
    apply multiset_sum_nonpos
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
    have hwmem : w ∈ p.roots := Multiset.mem_of_mem_erase hw
    exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (hroots w hwmem)
  linarith

theorem derivative_hermiteBiehler (f g : ℝ[X]) :
    (hermiteBiehlerPolynomial f g).derivative
      = hermiteBiehlerPolynomial f.derivative g.derivative := by
  simp only [hermiteBiehlerPolynomial, complexify, derivative_add, derivative_C_mul,
    derivative_map]

theorem im_hb_deriv_mul_conj (f g : ℝ[X]) (x : ℝ) :
    ((hermiteBiehlerPolynomial f g).derivative.eval (x : ℂ) *
        (starRingEnd ℂ) ((hermiteBiehlerPolynomial f g).eval (x : ℂ))).im
      = f.eval x * g.derivative.eval x - f.derivative.eval x * g.eval x := by
  rw [derivative_hermiteBiehler, eval_hermiteBiehlerPolynomial, eval_hermiteBiehlerPolynomial,
    eval_complexify_ofReal, eval_complexify_ofReal, eval_complexify_ofReal,
    eval_complexify_ofReal]
  simp [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.conj_I,
    Complex.conj_ofReal]
  ring

theorem wronskian_pos_of_stable {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnoreal : ∀ t : ℝ, (hermiteBiehlerPolynomial f g).eval (t : ℂ) ≠ 0)
    {w₀ : ℂ} (hw₀ : w₀ ∈ (hermiteBiehlerPolynomial f g).roots) (hneg : w₀.im < 0)
    (t : ℝ) :
    0 < f.derivative.eval t * g.eval t - f.eval t * g.derivative.eval t := by
  have him := im_deriv_mul_conj_neg
    (fun w hw => im_nonpos_of_stable_root hstab (isRoot_of_mem_roots hw)) (hnoreal t) hw₀ hneg
  rw [im_hb_deriv_mul_conj] at him
  linarith

theorem prec_of_stable_same_degree {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnoreal : ∀ t : ℝ, (hermiteBiehlerPolynomial f g).eval (t : ℂ) ≠ 0)
    {w₀ : ℂ} (hw₀ : w₀ ∈ (hermiteBiehlerPolynomial f g).roots) (hneg : w₀.im < 0)
    (hdeg : f.natDegree = g.natDegree) : Prec g f := by
  obtain ⟨hfs, hgs⟩ := splits_of_stable hf hg hstab
  exact (StrictPrecSameDegree.of_wronskian_pos (n := f.natDegree) hg hf hdeg.symm rfl hgs hfs
    (fun t => wronskian_pos_of_stable hstab hnoreal hw₀ hneg t)).to_prec

theorem hnoreal_of_no_common_real_root {f g : ℝ[X]}
    (hnc : ¬ ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r) :
    ∀ t : ℝ, (hermiteBiehlerPolynomial f g).eval (t : ℂ) ≠ 0 := by
  intro t ht
  rw [eval_hermiteBiehlerPolynomial, eval_complexify_ofReal, eval_complexify_ofReal] at ht
  have hf : f.eval t = 0 := by simpa using congrArg Complex.re ht
  have hg : g.eval t = 0 := by simpa using congrArg Complex.im ht
  exact hnc ⟨t, hf, hg⟩

theorem exists_neg_root_of_stable_no_real {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnoreal : ∀ t : ℝ, (hermiteBiehlerPolynomial f g).eval (t : ℂ) ≠ 0)
    (hpos : 0 < (hermiteBiehlerPolynomial f g).natDegree) :
    ∃ w₀ ∈ (hermiteBiehlerPolynomial f g).roots, w₀.im < 0 := by
  have hsplits : (hermiteBiehlerPolynomial f g).Splits := IsAlgClosed.splits _
  have hne_roots : (hermiteBiehlerPolynomial f g).roots ≠ 0 := by
    intro h₀
    have h_card : (hermiteBiehlerPolynomial f g).roots.card = 0 := by simp [h₀]
    rw [splits_iff_card_roots.mp hsplits] at h_card
    rw [h_card] at hpos
    lia
  obtain ⟨w₀, hw₀⟩ := Multiset.exists_mem_of_ne_zero hne_roots
  refine ⟨w₀, hw₀, ?_⟩
  have h_le : w₀.im ≤ 0 := im_nonpos_of_stable_root hstab (isRoot_of_mem_roots hw₀)
  rcases lt_or_eq_of_le h_le with h_lt | h_eq
  · exact h_lt
  · exfalso
    have hreal : w₀ = ((w₀.re : ℝ) : ℂ) := Complex.ext rfl h_eq
    have hroot : (hermiteBiehlerPolynomial f g).eval w₀ = 0 := isRoot_of_mem_roots hw₀
    rw [hreal] at hroot
    exact hnoreal w₀.re hroot

theorem prec_of_stable_same_degree_no_common {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnc : ¬ ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r)
    (hdeg : f.natDegree = g.natDegree) (hfpos : 0 < f.natDegree) : Prec g f := by
  have hnoreal := hnoreal_of_no_common_real_root hnc
  have hlead : 0 < f.coeff f.natDegree := hf
  have : (hermiteBiehlerPolynomial f g).natDegree = f.natDegree :=
    (hermiteBiehler_natDegree_of_posLead hlead rfl hdeg.symm).1
  have hpos : 0 < (hermiteBiehlerPolynomial f g).natDegree := by simp_all
  obtain ⟨w₀, hw₀mem, hw₀neg⟩ := exists_neg_root_of_stable_no_real hstab hnoreal hpos
  exact prec_of_stable_same_degree hf hg hstab hnoreal hw₀mem hw₀neg hdeg

theorem prec_of_stable_succ_degree {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hnc : ¬ ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r)
    (hdeg : f.natDegree = g.natDegree + 1) : Prec g f := by
  have hnoreal := hnoreal_of_no_common_real_root hnc
  have : (hermiteBiehlerPolynomial f g).natDegree = f.natDegree :=
    (hermiteBiehler_natDegree_of_left_dominant hf.ne_zero (by simp [*])).1
  have hpos : 0 < (hermiteBiehlerPolynomial f g).natDegree := by simp [*]
  obtain ⟨w₀, hw₀mem, hw₀neg⟩ := exists_neg_root_of_stable_no_real hstab hnoreal hpos
  obtain ⟨hfs, hgs⟩ := splits_of_stable hf hg hstab
  exact prec_of_wronskian_pos_succ hf hg hdeg rfl hfs hgs
    (fun t => wronskian_pos_of_stable hstab hnoreal hw₀mem hw₀neg t)

theorem isUpperHalfPlaneStable_cofactor_of_stable {f g : ℝ[X]} {r : ℝ}
    (hrf : f.IsRoot r) (hrg : g.IsRoot r)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    IsUpperHalfPlaneStable
      (hermiteBiehlerPolynomial (f /ₘ (X - C r)) (g /ₘ (X - C r))) := by
  intro z hz hroot
  refine hstab z hz ?_
  rw [hermiteBiehlerPolynomial_factor_common_root hrf hrg, eval_mul, hroot, mul_zero]

theorem hermiteBiehlerConverse_general :
    ∀ (n : ℕ) (f g : ℝ[X]), f.natDegree = n → HasPosLeadingCoeff f →
      HasPosLeadingCoeff g → IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) →
      Prec g f ∨ Prec f g := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f g h_fn hf hg hstab
    rcases Nat.lt_or_ge n 3 with h_lt | h_ge
    · exact hermiteBiehlerConverse_of_natDegree_le_two hf hg (by lia) hstab
    · by_cases hc : ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r
      · obtain ⟨r, hrf, hrg⟩ := hc
        set f₁ := f /ₘ (X - C r) with hf₁
        set g₁ := g /ₘ (X - C r) with hg₁
        have h_f_drop : f₁.natDegree = f.natDegree - 1 := by
          rw [hf₁, natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C]
        have h_f₁_pos : HasPosLeadingCoeff f₁ := by
          rw [HasPosLeadingCoeff, hf₁, leadingCoeff_divByMonic_X_sub_C hrf]; exact hf
        have h_g₁_pos : HasPosLeadingCoeff g₁ := by
          rw [HasPosLeadingCoeff, hg₁, leadingCoeff_divByMonic_X_sub_C hrg]; exact hg
        have h_stab₁ : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f₁ g₁) :=
          isUpperHalfPlaneStable_cofactor_of_stable hrf hrg hstab
        have h_lt₁ : f₁.natDegree < n := by rw [h_f_drop, h_fn]; lia
        rcases ih f₁.natDegree h_lt₁ f₁ g₁ rfl h_f₁_pos h_g₁_pos h_stab₁ with h | h
        · exact Or.inl (prec_of_prec_cofactor hrf hrg h)
        · exact Or.inr (prec_of_prec_cofactor hrg hrf h)
      · push Not at hc
        obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable hf hg hstab
        rcases Nat.lt_or_ge g.natDegree f.natDegree with h_g_lt | h_g_ge
        · exact Or.inl (prec_of_stable_succ_degree hf hg hstab (by
            simp_all) (by lia))
        · have h_deg : f.natDegree = g.natDegree := by lia
          exact Or.inl (prec_of_stable_same_degree_no_common hf hg hstab
            (by simp_all) h_deg (by lia))

theorem hermiteBiehlerConverse {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    Prec g f ∨ Prec f g :=
  hermiteBiehlerConverse_general f.natDegree f g rfl hf hg h

theorem ratio_cofactor_eq {f g : ℝ[X]} {r : ℝ} (hrf : f.IsRoot r) (hrg : g.IsRoot r) {z : ℂ}
    (hz : z ≠ (r : ℂ)) :
    (complexify (g /ₘ (X - C r))).eval z / (complexify (f /ₘ (X - C r))).eval z
      = (complexify g).eval z / (complexify f).eval z := by
  have hff : f = (X - C r) * (f /ₘ (X - C r)) := (mul_divByMonic_eq_iff_isRoot.mpr hrf).symm
  have hgg : g = (X - C r) * (g /ₘ (X - C r)) := (mul_divByMonic_eq_iff_isRoot.mpr hrg).symm
  have hfac : ∀ (h : ℝ[X]), (complexify ((X - C r) * h)).eval z
      = (z - (r : ℂ)) * (complexify h).eval z := by
    intro h
    simp [complexify, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  conv_rhs => rw [hff, hgg, hfac, hfac]
  rw [mul_div_mul_left]
  exact sub_ne_zero.mpr hz

theorem im_ratio_nonpos_general {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (hpq : Prec g f)
    (h_deg₁ : 1 ≤ f.natDegree)
    {z : ℂ} (hz : 0 < z.im) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f g with
  | _ n ih =>
    subst hn
    by_cases hcom : ∃ r, r ∈ f.roots ∧ r ∈ g.roots
    · obtain ⟨r, hrf, hrg⟩ := hcom
      have hrfroot : f.IsRoot r := isRoot_of_mem_roots hrf
      have hrgroot : g.IsRoot r := isRoot_of_mem_roots hrg
      have hzr : z ≠ (r : ℂ) := by intro h; simp_all
      rw [← ratio_cofactor_eq hrfroot hrgroot hzr]
      have hpq₁ : Prec (g /ₘ (X - C r)) (f /ₘ (X - C r)) :=
        prec_cofactor_of_common_root hpq hrfroot hrgroot
      have hf₁ : HasPosLeadingCoeff (f /ₘ (X - C r)) := by
        unfold HasPosLeadingCoeff at hf ⊢
        rw [leadingCoeff_divByMonic_X_sub_C hrfroot]; exact hf
      have hg₁ : HasPosLeadingCoeff (g /ₘ (X - C r)) := by
        unfold HasPosLeadingCoeff at hg ⊢
        rw [leadingCoeff_divByMonic_X_sub_C hrgroot]; exact hg
      have hf₁deg : (f /ₘ (X - C r)).natDegree < f.natDegree := by
        rw [natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C]; lia
      by_cases hd₁ : 1 ≤ (f /ₘ (X - C r)).natDegree
      · exact ih _ hf₁deg hf₁ hg₁ hpq₁ hd₁ rfl
      · push Not at hd₁
        have hf₁deg₀ : (f /ₘ (X - C r)).natDegree = 0 := by lia
        have hg₁deg₀ : (g /ₘ (X - C r)).natDegree = 0 := by
          have hg₁_le := hpq₁.natDegree_le
          lia
        have hf₁c : complexify (f /ₘ (X - C r)) = C ((f /ₘ (X - C r)).coeff 0 : ℂ) := by
          rw [complexify, eq_C_of_natDegree_eq_zero hf₁deg₀]; simp
        have hg₁c : complexify (g /ₘ (X - C r)) = C ((g /ₘ (X - C r)).coeff 0 : ℂ) := by
          rw [complexify, eq_C_of_natDegree_eq_zero hg₁deg₀]; simp
        simp [*]
    · push Not at hcom
      have hfnd : f.roots.Nodup := by
        by_contra hnd
        obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup hpq hnd
        simp_all
      have hgnd : g.roots.Nodup := by
        by_contra hnd
        obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup_g hpq hnd
        simp_all
      exact im_ratio_nonpos hpq hf hg hfnd hgnd (fun s hsf hsg ↦ hcom s hsf hsg) h_deg₁ hz

theorem prec_of_stable_general {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (h_deg₁ : 1 ≤ f.natDegree) : Prec g f := by
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f g with
  | _ n ih =>
    subst hn
    by_cases hcom : ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r
    · obtain ⟨r, hrf, hrg⟩ := hcom
      have hstab₁ := isUpperHalfPlaneStable_cofactor_of_stable hrf hrg hstab
      have hf₁ : HasPosLeadingCoeff (f /ₘ (X - C r)) := by
        unfold HasPosLeadingCoeff at hf ⊢
        rw [leadingCoeff_divByMonic_X_sub_C hrf]; exact hf
      have hg₁ : HasPosLeadingCoeff (g /ₘ (X - C r)) := by
        unfold HasPosLeadingCoeff at hg ⊢
        rw [leadingCoeff_divByMonic_X_sub_C hrg]; exact hg
      have hf₁deg : (f /ₘ (X - C r)).natDegree < f.natDegree := by
        rw [natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C]; lia
      by_cases hd₁ : 1 ≤ (f /ₘ (X - C r)).natDegree
      · exact prec_of_prec_cofactor hrf hrg (ih _ hf₁deg hf₁ hg₁ hstab₁ hd₁ rfl)
      · push Not at hd₁
        have hf₁d₀ : (f /ₘ (X - C r)).natDegree = 0 := by lia
        have hfd₁ : f.natDegree = 1 := by
          rw [natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C] at hf₁d₀; lia
        obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable hf hg hstab
        have hg₁d₀ : (g /ₘ (X - C r)).natDegree = 0 := by
          rw [natDegree_divByMonic g (monic_X_sub_C r), natDegree_X_sub_C]; lia
        refine prec_of_prec_cofactor hrf hrg ?_
        obtain ⟨⟨hg₁₀, hg₁s⟩, ⟨hf₁₀, hf₁s⟩⟩ :
            ((g /ₘ (X - C r)) ≠ 0 ∧ (g /ₘ (X - C r)).Splits) ∧
              ((f /ₘ (X - C r)) ≠ 0 ∧ (f /ₘ (X - C r)).Splits) :=
          ⟨isRealRooted_of_deg_zero hg₁.ne_zero hg₁d₀,
            isRealRooted_of_deg_zero hf₁.ne_zero hf₁d₀⟩
        exact prec_degree_zero_degree_zero hg₁₀ hg₁s hf₁₀ hf₁s hg₁d₀ hf₁d₀
    · push Not at hcom
      obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable hf hg hstab
      rcases Nat.lt_or_ge g.natDegree f.natDegree with hglt | hgge
      · exact prec_of_stable_succ_degree hf hg hstab
          (fun ⟨r, hrf, hrg⟩ => hcom r hrf hrg) (by lia)
      · exact prec_of_stable_same_degree_no_common hf hg hstab
          (fun ⟨r, hrf, hrg⟩ => hcom r hrf hrg) (by lia) h_deg₁

theorem hermiteBiehlerStableToHurwitzOddEven_upperHalfSubstitution :
    HermiteBiehlerStableToHurwitzOddEvenUpperHalfSubstitutionStatement := by
  intro p q h_p h_q h_stable w z hwim hzw hzre
  have h_zim : 0 < z.im := by
    have h_we : w.im = 2 * z.re * z.im := by rw [← hzw, pow_two, Complex.mul_im]; ring
    simp_all
  intro heq
  have hpw : (complexify p).eval w ≠ 0 := by
    intro hp₀
    rw [hp₀, mul_zero, add_zero] at heq
    exact h_stable w hwim (by simp [*])
  have h_z_eq : z = -((complexify q).eval w / (complexify p).eval w) := by
    field_simp; linear_combination heq
  have h_q_ne : q ≠ 0 := by
    rintro rfl
    simp only [complexify, Polynomial.map_zero, eval_zero, zero_add] at heq
    have h_z₀ : z ≠ 0 := fun h => by rw [h] at hzre; simp at hzre
    refine hpw ?_
    rcases mul_eq_zero.mp heq with h | h
    · exact absurd h h_z₀
    · exact h
  have h_q_pos : HasPosLeadingCoeff q := hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero h_q h_q_ne
  by_cases h_q_deg : 1 ≤ q.natDegree
  · have h_p_ne : p ≠ 0 := by rintro rfl; simp [complexify] at hpw
    have h_p_pos : HasPosLeadingCoeff p := hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero h_p h_p_ne
    have h_prec : Prec p q := prec_of_stable_general h_q_pos h_p_pos h_stable h_q_deg
    have h_ratio : ((complexify p).eval w / (complexify q).eval w).im ≤ 0 :=
      im_ratio_nonpos_general h_q_pos h_p_pos h_prec h_q_deg hwim
    have h_qw : (complexify q).eval w ≠ 0 := by
      obtain ⟨-, ⟨-, hqs⟩, -⟩ := id h_prec
      exact eval_complexify_ne_zero_of_splits_of_im_pos hqs h_q_ne hwim
    have h_qp_im : 0 ≤ ((complexify q).eval w / (complexify p).eval w).im := by
      have h_recip : ((complexify q).eval w / (complexify p).eval w)
          = ((complexify p).eval w / (complexify q).eval w)⁻¹ := by simp
      rw [h_recip, Complex.inv_im]
      have h_normsq : 0 < Complex.normSq ((complexify p).eval w / (complexify q).eval w) :=
        Complex.normSq_pos.mpr (div_ne_zero hpw h_qw)
      have h_num : 0 ≤ -((complexify p).eval w / (complexify q).eval w).im := by simp [*]
      exact div_nonneg h_num h_normsq.le
    have h_zim_le : z.im ≤ 0 := by simp [*]
    linarith [h_zim, h_zim_le]
  · push Not at h_q_deg
    have h_q_deg₀ : q.natDegree = 0 := by lia
    have h_p_ne : p ≠ 0 := by rintro rfl; simp [complexify] at hpw
    have h_p_pos : HasPosLeadingCoeff p := hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero h_p h_p_ne
    obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable h_q_pos h_p_pos h_stable
    have h_p_deg₀ : p.natDegree = 0 := by lia
    have h_qc : (complexify q).eval w = ((q.coeff 0 : ℝ) : ℂ) := by
      rw [complexify, eq_C_of_natDegree_eq_zero h_q_deg₀]; simp
    have h_pc : (complexify p).eval w = ((p.coeff 0 : ℝ) : ℂ) := by
      rw [complexify, eq_C_of_natDegree_eq_zero h_p_deg₀]; simp
    simp_all

theorem hermiteBiehlerStableToHurwitzOddEven {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (h : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q)) :=
  hermiteBiehlerStableToHurwitzOddEven_of_upperHalfSubstitution
    hermiteBiehlerStableToHurwitzOddEven_upperHalfSubstitution hp hq h

end RealRooted
