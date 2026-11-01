module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Ring.Defs
import RealRooted.Mathlib.Algebra.Polynomial.Homogenize
import RealRooted.QuadraticRoot
import RealRooted.Linear
import RealRooted.RootContinuity
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Denominator-cleared rational substitution

This file defines the homogeneous substitution obtained by evaluating the
bivariate homogenization of a univariate polynomial at two polynomials.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The denominator-cleared substitution of `p`, homogenized in ambient degree
`N` and evaluated at the pair `(A, B)`. -/
def homogenizedSubstitution {R : Type*} [CommSemiring R]
    (N : ℕ) (A B p : R[X]) : R[X] :=
  MvPolynomial.aeval ![A, B] (p.homogenize N)

/-- The denominator-cleared substitution of `p` in its natural degree. -/
def rationalSubstitution {R : Type*} [CommSemiring R]
    (A B p : R[X]) : R[X] :=
  homogenizedSubstitution p.natDegree A B p

/-- The ambient-degree substitution is the expected finite homogeneous sum. -/
theorem homogenizedSubstitution_eq_sum {R : Type*} [CommSemiring R]
    {N : ℕ} {A B p : R[X]} (hdeg : p.natDegree ≤ N) :
    homogenizedSubstitution N A B p =
      ∑ k ∈ Finset.range (N + 1), C (p.coeff k) * A ^ k * B ^ (N - k) := by
  rw [homogenizedSubstitution,
    Polynomial.homogenize_eq_sum_range_C_mul_X_pow hdeg]
  simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [C_eq_algebraMap, mul_assoc]

/-- The exact-degree substitution is the expected finite homogeneous sum. -/
theorem rationalSubstitution_eq_sum {R : Type*} [CommSemiring R]
    (A B p : R[X]) :
    rationalSubstitution A B p =
      ∑ k ∈ Finset.range (p.natDegree + 1),
        C (p.coeff k) * A ^ k * B ^ (p.natDegree - k) := by
  exact homogenizedSubstitution_eq_sum le_rfl

/-- Raising the ambient degree by one multiplies the substitution by the
denominator polynomial. -/
theorem homogenizedSubstitution_succ {R : Type*} [CommSemiring R]
    {N : ℕ} {A B p : R[X]} (hdeg : p.natDegree ≤ N) :
    homogenizedSubstitution (N + 1) A B p =
      B * homogenizedSubstitution N A B p := by
  rw [homogenizedSubstitution, homogenizedSubstitution,
    show p = p * 1 by simp, Polynomial.homogenize_mul p 1 hdeg (by simp)]
  simp [mul_comm]

/-- Multiplying the source by its variable replaces the new homogeneous
degree by a factor of the numerator polynomial. -/
theorem homogenizedSubstitution_X_mul {R : Type*} [CommSemiring R]
    {N : ℕ} {A B p : R[X]} (hdeg : p.natDegree ≤ N) :
    homogenizedSubstitution (N + 1) A B (X * p) =
      A * homogenizedSubstitution N A B p := by
  rw [homogenizedSubstitution, homogenizedSubstitution, Nat.add_comm,
    Polynomial.homogenize_mul X p (m := 1) (n := N)
      Polynomial.natDegree_X_le hdeg]
  simp

/-- Ambient-degree homogeneous substitution is multiplicative when the
ambient degrees are added. -/
theorem homogenizedSubstitution_mul {R : Type*} [CommSemiring R]
    {M N : ℕ} {A B p q : R[X]}
    (hp : p.natDegree ≤ M) (hq : q.natDegree ≤ N) :
    homogenizedSubstitution (M + N) A B (p * q) =
      homogenizedSubstitution M A B p * homogenizedSubstitution N A B q := by
  rw [homogenizedSubstitution, homogenizedSubstitution, homogenizedSubstitution,
    Polynomial.homogenize_mul p q hp hq, map_mul]

/-- Substitution commutes with an injective change of coefficient ring. -/
theorem map_rationalSubstitution {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (hf : Function.Injective f) (A B p : R[X]) :
    (rationalSubstitution A B p).map f =
      rationalSubstitution (A.map f) (B.map f) (p.map f) := by
  simp only [rationalSubstitution_eq_sum, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.coeff_map, Polynomial.natDegree_map_eq_of_injective hf]

/-- Homogeneous substitution respects a displayed product of linear root
factors. -/
theorem homogenizedSubstitution_C_mul_rootFactorProduct
    {R : Type*} [CommRing R] [IsDomain R]
    (A B : R[X]) (c : R) (roots : Multiset R) :
    homogenizedSubstitution roots.card A B
        (C c * (roots.map fun r => X - C r).prod) =
      C c * (roots.map fun r => A - C r * B).prod := by
  rw [homogenizedSubstitution, Polynomial.homogenize_C_mul,
    Polynomial.homogenize_rootFactorProduct]
  simp [map_multiset_prod, C_eq_algebraMap]

/-- Over the complex numbers, exact-degree substitution factors over all roots
of the source polynomial. -/
theorem rationalSubstitution_complex_eq_prod (A B p : ℂ[X]) :
    rationalSubstitution A B p =
      C p.leadingCoeff * (p.roots.map fun r => A - C r * B).prod := by
  have hcard : p.roots.card = p.natDegree :=
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hp : p = C p.leadingCoeff * (p.roots.map fun r => X - C r).prod :=
    (C_leadingCoeff_mul_prod_multiset_X_sub_C hcard).symm
  rw [rationalSubstitution]
  calc
    homogenizedSubstitution p.natDegree A B p =
        homogenizedSubstitution p.roots.card A B p := by rw [hcard]
    _ = homogenizedSubstitution p.roots.card A B
          (C p.leadingCoeff * (p.roots.map fun r => X - C r).prod) :=
      congrArg (homogenizedSubstitution p.roots.card A B) hp
    _ = C p.leadingCoeff * (p.roots.map fun r => A - C r * B).prod :=
      homogenizedSubstitution_C_mul_rootFactorProduct A B p.leadingCoeff p.roots

/-- For a split real source polynomial, substitution factors over its real
roots. -/
theorem rationalSubstitution_eq_prod_of_splits {A B p : ℝ[X]}
    (hp : p.Splits) :
    rationalSubstitution A B p =
      C p.leadingCoeff * (p.roots.map fun r => A - C r * B).prod := by
  have hcard : p.roots.card = p.natDegree :=
    Polynomial.splits_iff_card_roots.mp hp
  have hfactor : p = C p.leadingCoeff * (p.roots.map fun r => X - C r).prod :=
    (C_leadingCoeff_mul_prod_multiset_X_sub_C hcard).symm
  rw [rationalSubstitution]
  calc
    homogenizedSubstitution p.natDegree A B p =
        homogenizedSubstitution p.roots.card A B p := by rw [hcard]
    _ = homogenizedSubstitution p.roots.card A B
          (C p.leadingCoeff * (p.roots.map fun r => X - C r).prod) :=
      congrArg (homogenizedSubstitution p.roots.card A B) hfactor
    _ = C p.leadingCoeff * (p.roots.map fun r => A - C r * B).prod :=
      homogenizedSubstitution_C_mul_rootFactorProduct A B p.leadingCoeff p.roots

/-- The pair `(A, B)` has nonconstant quotient when no complex scalar makes
their complexifications proportional. -/
def HasNonconstantRatio (A B : ℝ[X]) : Prop :=
  ∀ z : ℂ,
    A.map Complex.ofRealHom - C z * B.map Complex.ofRealHom ≠ 0

/-- A denominator-cleared substitution with nonzero source and nonconstant
quotient is nonzero. -/
theorem rationalSubstitution_ne_zero {A B p : ℝ[X]} (hp : p ≠ 0)
    (hratio : HasNonconstantRatio A B) :
    rationalSubstitution A B p ≠ 0 := by
  intro hzero
  have hmap : (rationalSubstitution A B p).map Complex.ofRealHom = 0 := by
    simp [hzero]
  rw [map_rationalSubstitution Complex.ofRealHom Complex.ofRealHom.injective,
    rationalSubstitution_complex_eq_prod] at hmap
  have hpmap : p.map Complex.ofRealHom ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hp
  have hprod :
      ((p.map Complex.ofRealHom).roots.map fun z =>
        A.map Complex.ofRealHom - C z * B.map Complex.ofRealHom).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    simp only [Multiset.mem_map, not_exists, not_and]
    intro z _
    exact hratio z
  apply mul_ne_zero
      (C_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hpmap))
      hprod
  exact hmap

/-- Every real fiber of a nonconstant quotient is nonzero. -/
theorem sub_C_mul_ne_zero_of_hasNonconstantRatio {A B : ℝ[X]}
    (hratio : HasNonconstantRatio A B) (r : ℝ) :
    A - C r * B ≠ 0 := by
  intro hzero
  have hmap := congrArg (Polynomial.map Complex.ofRealHom) hzero
  apply hratio (r : ℂ)
  simpa using hmap

private theorem complex_fiber_natDegree_ne_zero_of_im_ne_zero
    {A B : ℝ[X]} (hB : B ≠ 0) (hratio : HasNonconstantRatio A B)
    {z : ℂ} (hz : z.im ≠ 0) :
    (A.map Complex.ofRealHom - C z * B.map Complex.ofRealHom).natDegree ≠ 0 := by
  let F := A.map Complex.ofRealHom - C z * B.map Complex.ofRealHom
  intro hdegree
  change F.natDegree = 0 at hdegree
  have hcoeff (n : ℕ) (hn : 0 < n) : F.coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [hdegree]
    exact hn
  have hBcoeff (n : ℕ) (hn : 0 < n) : B.coeff n = 0 := by
    have h := congrArg Complex.im (hcoeff n hn)
    simp [F] at h
    exact h.resolve_left hz
  have hAcoeff (n : ℕ) (hn : 0 < n) : A.coeff n = 0 := by
    have h := hcoeff n hn
    have h' : (A.coeff n : ℂ) = 0 := by
      simpa [F, hBcoeff n hn] using h
    exact Complex.ofReal_injective h'
  have hAdegree : A.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hAcoeff
  have hBdegree : B.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hBcoeff
  let a := A.coeff 0
  let b := B.coeff 0
  have hAeq : A = C a := Polynomial.eq_C_of_natDegree_eq_zero hAdegree
  have hBeq : B = C b := Polynomial.eq_C_of_natDegree_eq_zero hBdegree
  have hb : b ≠ 0 := by
    intro h
    apply hB
    rw [hBeq, h, C_0]
  apply hratio ((a : ℂ) / (b : ℂ))
  rw [hAeq, hBeq]
  simp only [Polynomial.map_C, ← Polynomial.C_mul]
  change C (a : ℂ) - C ((a : ℂ) / (b : ℂ) * (b : ℂ)) = 0
  rw [div_mul_cancel₀, sub_self]
  exact_mod_cast hb

private theorem splits_of_rationalSubstitution_splits
    {A B p : ℝ[X]} (hp : p ≠ 0) (hB : B ≠ 0)
    (hcop : IsCoprime A B) (hratio : HasNonconstantRatio A B)
    (hH : (rationalSubstitution A B p).Splits) :
    p.Splits := by
  have hH0 := rationalSubstitution_ne_zero hp hratio
  apply splits_of_forall_aeval_im_eq_zero
  intro z hzroot
  by_contra hzim
  let F : ℂ[X] :=
    A.map Complex.ofRealHom - C z * B.map Complex.ofRealHom
  have hFdegree : F.natDegree ≠ 0 :=
    complex_fiber_natDegree_ne_zero_of_im_ne_zero hB hratio hzim
  obtain ⟨w, hw⟩ := Complex.exists_root
    (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hFdegree))
  have hpmap : p.map Complex.ofRealHom ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hp
  have hzrootmap : (p.map Complex.ofRealHom).IsRoot z := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map]
    exact hzroot
  have hzmem : z ∈ (p.map Complex.ofRealHom).roots :=
    (Polynomial.mem_roots hpmap).mpr hzrootmap
  have hFmem : F ∈
      ((p.map Complex.ofRealHom).roots.map fun r =>
        A.map Complex.ofRealHom - C r * B.map Complex.ofRealHom) := by
    exact Multiset.mem_map.mpr ⟨z, hzmem, rfl⟩
  have hFdvd : F ∣ rationalSubstitution
      (A.map Complex.ofRealHom) (B.map Complex.ofRealHom)
        (p.map Complex.ofRealHom) := by
    rw [rationalSubstitution_complex_eq_prod]
    exact dvd_mul_of_dvd_right (Multiset.dvd_prod hFmem) _
  have hwHmap : (rationalSubstitution
      (A.map Complex.ofRealHom) (B.map Complex.ofRealHom)
        (p.map Complex.ofRealHom)).IsRoot w := hw.dvd hFdvd
  have hwH : (rationalSubstitution A B p).aeval w = 0 := by
    have hmap := map_rationalSubstitution Complex.ofRealHom
      Complex.ofRealHom.injective A B p
    rw [← hmap] at hwHmap
    rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hwHmap
    exact hwHmap
  have hwim : w.im = 0 :=
    im_eq_zero_of_aeval_eq_zero hH0 hH hwH
  have hcopmap : IsCoprime (A.map Complex.ofRealHom)
      (B.map Complex.ofRealHom) :=
    (Polynomial.isCoprime_map Complex.ofRealHom).mpr hcop
  have hFeval :
      (A.map Complex.ofRealHom).eval w -
        z * (B.map Complex.ofRealHom).eval w = 0 := by
    simpa [F, Polynomial.IsRoot.def] using hw
  have hBeval : (B.map Complex.ofRealHom).eval w ≠ 0 := by
    intro hBzero
    have hAzero : (A.map Complex.ofRealHom).eval w = 0 := by
      simpa [hBzero] using hFeval
    rcases Polynomial.aeval_ne_zero_of_isCoprime hcopmap w with hA | hB'
    · exact hA (by simpa [Polynomial.aeval_def] using hAzero)
    · exact hB' (by simpa [Polynomial.aeval_def] using hBzero)
  have hzquot : z = (A.map Complex.ofRealHom).eval w /
      (B.map Complex.ofRealHom).eval w := by
    apply (eq_div_iff hBeval).mpr
    exact (sub_eq_zero.mp hFeval).symm
  have hwreal : w = (w.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hwim]
  have hAeval :
      (A.map Complex.ofRealHom).eval (w.re : ℂ) =
        ((A.eval w.re : ℝ) : ℂ) := by
    exact Polynomial.eval_map_apply Complex.ofRealHom w.re
  have hBeval' :
      (B.map Complex.ofRealHom).eval (w.re : ℂ) =
        ((B.eval w.re : ℝ) : ℂ) := by
    exact Polynomial.eval_map_apply Complex.ofRealHom w.re
  rw [hwreal, hAeval, hBeval'] at hzquot
  have : z.im = 0 := by
    rw [hzquot]
    simp
  exact hzim this

/-- **Rational-substitution root descent.** For coprime real `A` and `B`, a
nonzero denominator, and nonconstant quotient, the cleared substitution
splits exactly when the source and all its real root fibers split. -/
theorem rationalSubstitution_splits_iff {A B p : ℝ[X]}
    (hp : p ≠ 0) (hB : B ≠ 0) (hcop : IsCoprime A B)
    (hratio : HasNonconstantRatio A B) :
    (rationalSubstitution A B p).Splits ↔
      p.Splits ∧ ∀ r ∈ p.roots, (A - C r * B).Splits := by
  constructor
  · intro hH
    have hps := splits_of_rationalSubstitution_splits hp hB hcop hratio hH
    refine ⟨hps, ?_⟩
    intro r hr
    have hfactor : A - C r * B ∣ rationalSubstitution A B p := by
      rw [rationalSubstitution_eq_prod_of_splits hps]
      exact dvd_mul_of_dvd_right
        (Multiset.dvd_prod (Multiset.mem_map.mpr ⟨r, hr, rfl⟩)) _
    exact hH.of_dvd (rationalSubstitution_ne_zero hp hratio) hfactor
  · rintro ⟨hps, hfactors⟩
    rw [rationalSubstitution_eq_prod_of_splits hps]
    apply Polynomial.Splits.mul (Polynomial.Splits.C _)
    refine Multiset.prod_induction (fun q : ℝ[X] => q.Splits) _
      (fun _ _ ha hb => Polynomial.Splits.mul ha hb) Polynomial.Splits.one ?_
    intro q hq
    simp only [Multiset.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    exact hfactors r hr

/-- A root of the source with nonconstant fiber is a rational image of a root
of the cleared substitution. -/
theorem exists_mem_eq_eval_div_of_isRoot
    {A B p : ℝ[X]} {I : Set ℝ} {r : ℝ}
    (hp : p ≠ 0) (hB : B ≠ 0) (hcop : IsCoprime A B)
    (hratio : HasNonconstantRatio A B)
    (hH : (rationalSubstitution A B p).Splits)
    (hI : ∀ x ∈ (rationalSubstitution A B p).roots, x ∈ I)
    (hr : p.IsRoot r) (hfiber : (A - C r * B).natDegree ≠ 0) :
    ∃ x ∈ I, B.eval x ≠ 0 ∧ r = A.eval x / B.eval x := by
  have hH0 := rationalSubstitution_ne_zero hp hratio
  have hmain := (rationalSubstitution_splits_iff hp hB hcop hratio).mp hH
  have hrmem : r ∈ p.roots := (Polynomial.mem_roots hp).mpr hr
  have hfsplit := hmain.2 r hrmem
  have hcard : (A - C r * B).roots.card = (A - C r * B).natDegree :=
    Polynomial.splits_iff_card_roots.mp hfsplit
  obtain ⟨x, hxmem⟩ : ∃ x, x ∈ (A - C r * B).roots := by
    rw [← Multiset.card_pos_iff_exists_mem, hcard]
    exact Nat.pos_of_ne_zero hfiber
  have hfactor : A - C r * B ∣ rationalSubstitution A B p := by
    rw [rationalSubstitution_eq_prod_of_splits hmain.1]
    exact dvd_mul_of_dvd_right
      (Multiset.dvd_prod (Multiset.mem_map.mpr ⟨r, hrmem, rfl⟩)) _
  have hxroot : (A - C r * B).IsRoot x :=
    Polynomial.isRoot_of_mem_roots hxmem
  have hxHroot : (rationalSubstitution A B p).IsRoot x := hxroot.dvd hfactor
  have hxHmem : x ∈ (rationalSubstitution A B p).roots :=
    (Polynomial.mem_roots hH0).mpr hxHroot
  have hBeval : B.eval x ≠ 0 := by
    intro hzero
    have hBroot : B.IsRoot x := hzero
    have hAroot : A.IsRoot x := by
      rw [Polynomial.IsRoot.def] at hxroot ⊢
      simpa [hzero] using hxroot
    exact hcop.not_isRoot_right hAroot hBroot
  refine ⟨x, hI x hxHmem, hBeval, ?_⟩
  apply (eq_div_iff hBeval).mpr
  rw [Polynomial.IsRoot.def] at hxroot
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at hxroot
  exact (sub_eq_zero.mp hxroot).symm

/-- Distinct numerator and denominator degrees, with positive numerator
degree, make every real fiber nonconstant. -/
theorem natDegree_sub_C_mul_ne_zero_of_ne
    {A B : ℝ[X]} (hA : A.natDegree ≠ 0)
    (hdegree : A.natDegree ≠ B.natDegree) (r : ℝ) :
    (A - C r * B).natDegree ≠ 0 := by
  by_cases hr : r = 0
  · simpa [hr] using hA
  have hCBdegree : (C r * B).natDegree = B.natDegree :=
    Polynomial.natDegree_C_mul hr
  rcases lt_or_gt_of_ne hdegree with hlt | hgt
  · rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
    · intro hBzero
      rw [hCBdegree] at hBzero
      rw [hBzero] at hlt
      exact (Nat.not_lt_zero _ hlt)
    · rw [hCBdegree]
      exact hlt
  · rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact hA
    · rw [hCBdegree]
      exact hgt

/-! ## Quadratic rational substitution -/

/-- The quadratic specialization with numerator `X` and denominator
`(1 + sX)²`. -/
def quadraticSubstitution (s : ℝ) (p : ℝ[X]) : ℝ[X] :=
  rationalSubstitution X ((1 + C s * X) ^ 2) p

/-- The quadratic specialization is the coefficient sum
`∑ pₖ Xᵏ (1 + sX)²⁽ⁿ⁻ᵏ⁾`. -/
theorem quadraticSubstitution_eq_sum (s : ℝ) (p : ℝ[X]) :
    quadraticSubstitution s p =
      ∑ k ∈ Finset.range (p.natDegree + 1),
        C (p.coeff k) * X ^ k *
          (1 + C s * X) ^ (2 * (p.natDegree - k)) := by
  rw [quadraticSubstitution, rationalSubstitution_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_mul]

private theorem quadratic_denominator_ne_zero (s : ℝ) :
    (1 + C s * X : ℝ[X]) ^ 2 ≠ 0 := by
  intro hzero
  have h := congrArg (Polynomial.eval 0) hzero
  simp at h

private theorem isCoprime_X_quadratic_denominator (s : ℝ) :
    IsCoprime (X : ℝ[X]) ((1 + C s * X) ^ 2) := by
  rw [show (X : ℝ[X]) = X - C 0 by simp,
    (irreducible_X_sub_C 0).coprime_iff_not_dvd, Polynomial.dvd_iff_isRoot]
  simp

private theorem hasNonconstantRatio_X_quadratic_denominator (s : ℝ) :
    HasNonconstantRatio X ((1 + C s * X) ^ 2) := by
  intro z hzero
  have h := congrArg (Polynomial.eval 0) hzero
  simp at h
  subst z
  simp at hzero

/-- Expanded form of a quadratic-substitution fiber. -/
theorem quadratic_fiber_eq (s r : ℝ) :
    (X - C r * (1 + C s * X) ^ 2 : ℝ[X]) =
      C (-r * s ^ 2) * X ^ 2 + C (1 - 2 * s * r) * X + C (-r) := by
  simp only [map_neg, map_mul, map_pow, map_sub, map_one, map_ofNat]
  ring

/-- A quadratic fiber splits exactly when its discriminant `1 - 4sr` is
nonnegative, including the linear cases `s = 0` and `r = 0`. -/
theorem quadratic_fiber_splits_iff (s r : ℝ) :
    (X - C r * (1 + C s * X) ^ 2 : ℝ[X]).Splits ↔
      0 ≤ 1 - 4 * s * r := by
  by_cases hs : s = 0
  · subst s
    simp
  by_cases hr : r = 0
  · subst r
    simp [Polynomial.Splits.X]
  rw [quadratic_fiber_eq]
  constructor
  · intro hsplit
    by_contra hdisc
    apply quadraticPoly_not_splits_of_discrim_neg
      (mul_ne_zero (neg_ne_zero.mpr hr) (pow_ne_zero 2 hs))
      (show discrim (-r * s ^ 2) (1 - 2 * s * r) (-r) < 0 by
        simp only [discrim]
        nlinarith)
      hsplit
  · intro hdisc
    apply quadraticPoly_splits_of_discrim_nonneg
      (mul_ne_zero (neg_ne_zero.mpr hr) (pow_ne_zero 2 hs))
    simp only [discrim]
    nlinarith

/-- **Quadratic substitution criterion.** The transform splits exactly when
the source splits and every source root satisfies `1 - 4sr ≥ 0`. -/
theorem quadraticSubstitution_splits_iff {s : ℝ} {p : ℝ[X]} (hp : p ≠ 0) :
    (quadraticSubstitution s p).Splits ↔
      p.Splits ∧ ∀ r ∈ p.roots, 0 ≤ 1 - 4 * s * r := by
  unfold quadraticSubstitution
  rw [rationalSubstitution_splits_iff hp (quadratic_denominator_ne_zero s)
    (isCoprime_X_quadratic_denominator s)
    (hasNonconstantRatio_X_quadratic_denominator s)]
  constructor
  · rintro ⟨hps, hfibers⟩
    exact ⟨hps, fun r hr => (quadratic_fiber_splits_iff s r).mp (hfibers r hr)⟩
  · rintro ⟨hps, hdisc⟩
    exact ⟨hps, fun r hr => (quadratic_fiber_splits_iff s r).mpr (hdisc r hr)⟩

private theorem quadratic_fiber_natDegree_ne_zero (s r : ℝ) :
    (X - C r * (1 + C s * X) ^ 2 : ℝ[X]).natDegree ≠ 0 := by
  by_cases hr : r = 0
  · simp [hr]
  by_cases hs : s = 0
  · simp [hs]
  rw [quadratic_fiber_eq]
  have hdegree :
      (C (-r * s ^ 2) * X ^ 2 + C (1 - 2 * s * r) * X +
        C (-r) : ℝ[X]).natDegree = 2 := by
    compute_degree!
  rw [hdegree]
  norm_num

/-- The quadratic substitution has only real nonpositive roots exactly when
the source roots lie in the discriminant window and are nonpositive. -/
theorem quadraticSubstitution_splits_and_roots_nonpos_iff
    {s : ℝ} {p : ℝ[X]} (hp : p ≠ 0) :
    ((quadraticSubstitution s p).Splits ∧
        ∀ x ∈ (quadraticSubstitution s p).roots, x ≤ 0) ↔
      (p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0 ∧ 0 ≤ 1 - 4 * s * r) := by
  constructor
  · rintro ⟨hQsplit, hQroots⟩
    have hcriterion := (quadraticSubstitution_splits_iff hp).mp hQsplit
    refine ⟨hcriterion.1, ?_⟩
    intro r hr
    have hpull := exists_mem_eq_eval_div_of_isRoot
      (A := (X : ℝ[X])) (B := (1 + C s * X) ^ 2)
      (I := {x : ℝ | x ≤ 0}) hp (quadratic_denominator_ne_zero s)
      (isCoprime_X_quadratic_denominator s)
      (hasNonconstantRatio_X_quadratic_denominator s) hQsplit hQroots
      ((Polynomial.mem_roots hp).mp hr) (quadratic_fiber_natDegree_ne_zero s r)
    obtain ⟨x, hx, hden, hratio⟩ := hpull
    simp only [Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C] at hden hratio
    refine ⟨?_, hcriterion.2 r hr⟩
    rw [hratio]
    exact div_nonpos_of_nonpos_of_nonneg hx (sq_nonneg _)
  · rintro ⟨hps, hroots⟩
    have hQsplit : (quadraticSubstitution s p).Splits :=
      (quadraticSubstitution_splits_iff hp).mpr
        ⟨hps, fun r hr => (hroots r hr).2⟩
    refine ⟨hQsplit, ?_⟩
    intro x hx
    have hxroot : (quadraticSubstitution s p).IsRoot x :=
      Polynomial.isRoot_of_mem_roots hx
    have hfactor := rationalSubstitution_eq_prod_of_splits
      (A := (X : ℝ[X])) (B := (1 + C s * X) ^ 2) hps
    have hxzero :
        (C p.leadingCoeff *
          (p.roots.map fun r => X - C r * (1 + C s * X) ^ 2).prod).eval x = 0 := by
      rw [← hfactor]
      exact hxroot
    simp only [Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_multiset_prod] at hxzero
    have hprodzero := (mul_eq_zero.mp hxzero).resolve_left
      (Polynomial.leadingCoeff_ne_zero.mpr hp)
    rw [Multiset.prod_eq_zero_iff] at hprodzero
    obtain ⟨q, hqmem, hqzero⟩ := Multiset.mem_map.mp hprodzero
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hqmem
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_one] at hqzero
    nlinarith [sq_nonneg (1 + s * x), (hroots r hr).1]

private theorem one_div_four_mul_le_iff {s r : ℝ} (hs : s < 0) :
    1 / (4 * s) ≤ r ↔ 0 ≤ 1 - 4 * s * r := by
  rw [div_le_iff_of_neg (by nlinarith : 4 * s < 0)]
  constructor <;> intro h <;> nlinarith

/-- For nonnegative `s`, nonpositive source roots automatically satisfy the
quadratic discriminant condition. -/
theorem quadraticSubstitution_splits_and_roots_nonpos_iff_of_nonneg
    {s : ℝ} (hs : 0 ≤ s) {p : ℝ[X]} (hp : p ≠ 0) :
    ((quadraticSubstitution s p).Splits ∧
        ∀ x ∈ (quadraticSubstitution s p).roots, x ≤ 0) ↔
      (p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0) := by
  rw [quadraticSubstitution_splits_and_roots_nonpos_iff hp]
  constructor
  · rintro ⟨hps, hroots⟩
    exact ⟨hps, fun r hr => (hroots r hr).1⟩
  · rintro ⟨hps, hroots⟩
    refine ⟨hps, fun r hr => ⟨hroots r hr, ?_⟩⟩
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hs (hroots r hr)]

/-- For negative `s`, the nonpositive-root condition is the closed source
window `[1/(4s), 0]`, including both endpoints. -/
theorem quadraticSubstitution_splits_and_roots_nonpos_iff_of_neg
    {s : ℝ} (hs : s < 0) {p : ℝ[X]} (hp : p ≠ 0) :
    ((quadraticSubstitution s p).Splits ∧
        ∀ x ∈ (quadraticSubstitution s p).roots, x ≤ 0) ↔
      (p.Splits ∧ ∀ r ∈ p.roots, r ∈ Set.Icc (1 / (4 * s)) 0) := by
  rw [quadraticSubstitution_splits_and_roots_nonpos_iff hp]
  constructor
  · rintro ⟨hps, hroots⟩
    refine ⟨hps, fun r hr => ?_⟩
    exact ⟨(one_div_four_mul_le_iff hs).mpr (hroots r hr).2, (hroots r hr).1⟩
  · rintro ⟨hps, hroots⟩
    refine ⟨hps, fun r hr => ?_⟩
    exact ⟨(hroots r hr).2, (one_div_four_mul_le_iff hs).mp (hroots r hr).1⟩

/-- Without a root-sign condition and for negative `s`, splitting is
equivalent to the lower bound `r ≥ 1/(4s)` on every source root. -/
theorem quadraticSubstitution_splits_iff_of_neg
    {s : ℝ} (hs : s < 0) {p : ℝ[X]} (hp : p ≠ 0) :
    (quadraticSubstitution s p).Splits ↔
      p.Splits ∧ ∀ r ∈ p.roots, 1 / (4 * s) ≤ r := by
  rw [quadraticSubstitution_splits_iff hp]
  constructor
  · rintro ⟨hps, hroots⟩
    exact ⟨hps, fun r hr => (one_div_four_mul_le_iff hs).mpr (hroots r hr)⟩
  · rintro ⟨hps, hroots⟩
    exact ⟨hps, fun r hr => (one_div_four_mul_le_iff hs).mp (hroots r hr)⟩

end RealRooted
