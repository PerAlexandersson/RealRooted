/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# Veronese sections and multiplication matrices

The `i`th `r`-Veronese section selects coefficients in the progression `i + r * n`.
For positive `r`, these sections give coordinates over the image of `Polynomial.expand`.
We reconstruct polynomials from these coordinates and represent multiplication by a
polynomial as an explicit matrix. The adjugate then gives an expanded multiple of the
original polynomial, over any commutative ring and in every characteristic.

For bivariate polynomials, `veroneseSectionCoeffs` and `veroneseMatrix` act on the
inner variable. The explicit determinant `veroneseNorm` leaves the outer variable
fixed, has the expected degree bound, preserves monicity, and is normalized at
outer degree zero whenever the input is. This is the algebraic layer for transporting
constant-coefficient recurrences to their Veronese sections.
-/

@[expose] public section

namespace Polynomial

open Matrix

noncomputable section

variable {A : Type*}

section Semiring

variable [Semiring A]

/-- The `i`th `r`-Veronese section of a polynomial. For `r = 0` it is zero. -/
def veroneseSection (r i : ℕ) (p : A[X]) : A[X] :=
  if hr : r = 0 then 0 else
    Polynomial.ofFinsupp <|
      ⟨Finsupp.onFinset (Finset.range (p.natDegree + 1))
        (fun n => p.coeff (i + r * n)) (by
          intro n hn
          by_contra hmem
          have hpn : p.natDegree < n := by simpa using hmem
          have hn_le : n ≤ r * n := by
            simpa using Nat.mul_le_mul_right n (Nat.one_le_iff_ne_zero.mpr hr)
          exact hn (coeff_eq_zero_of_natDegree_lt (by lia)))⟩

/-- Coefficients of a Veronese section for a positive modulus. -/
@[simp] theorem coeff_veroneseSection {r i n : ℕ} (hr : 0 < r) (p : A[X]) :
    (p.veroneseSection r i).coeff n = p.coeff (i + r * n) := by
  simp [veroneseSection, Nat.ne_of_gt hr]

/-- The modulus-zero convention gives the zero polynomial. -/
@[simp] theorem veroneseSection_zero_modulus (i : ℕ) (p : A[X]) :
    p.veroneseSection 0 i = 0 := by
  simp [veroneseSection]

/-- Every section of zero is zero. -/
@[simp] theorem veroneseSection_zero (r i : ℕ) :
    (0 : A[X]).veroneseSection r i = 0 := by
  by_cases hr : r = 0
  · simp [hr]
  · ext n
    simp [coeff_veroneseSection (Nat.pos_of_ne_zero hr)]

/-- Veronese sections commute with addition, including modulus zero. -/
@[simp] theorem veroneseSection_add (r i : ℕ) (p q : A[X]) :
    (p + q).veroneseSection r i = p.veroneseSection r i + q.veroneseSection r i := by
  by_cases hr : r = 0
  · simp [hr]
  · ext n
    simp [coeff_veroneseSection (Nat.pos_of_ne_zero hr)]

/-- A Veronese section as an additive homomorphism. -/
def veroneseSectionAddHom (r i : ℕ) : A[X] →+ A[X] where
  toFun := veroneseSection r i
  map_zero' := veroneseSection_zero r i
  map_add' := veroneseSection_add r i

/-- Veronese sections commute with finite sums. -/
theorem veroneseSection_sum {ι : Type*} (r i : ℕ) (s : Finset ι) (f : ι → A[X]) :
    (∑ j ∈ s, f j).veroneseSection r i = ∑ j ∈ s, (f j).veroneseSection r i :=
  map_sum (veroneseSectionAddHom r i) f s

/-- A constant factor can be pulled out of a Veronese section. -/
theorem veroneseSection_C_mul (r i : ℕ) (a : A) (p : A[X]) :
    (C a * p).veroneseSection r i = C a * p.veroneseSection r i := by
  by_cases hr : r = 0
  · simp [hr]
  · ext n
    simp [coeff_veroneseSection (Nat.pos_of_ne_zero hr)]

/-- Multiplication by `X ^ r` shifts each valid section by one power of `X`. -/
theorem veroneseSection_X_pow_mul {r i : ℕ} (hr : 0 < r) (hi : i < r) (p : A[X]) :
    (X ^ r * p).veroneseSection r i = X * p.veroneseSection r i := by
  ext n
  cases n with
  | zero =>
      rw [coeff_veroneseSection hr]
      simp [coeff_X_pow_mul', Nat.not_le_of_lt hi]
  | succ n =>
      rw [coeff_veroneseSection hr, coeff_X_mul, coeff_X_pow_mul']
      have heq : i + r * (n + 1) = i + r * n + r := by ring
      rw [ite_eq_left (by rw [heq]; lia), heq, Nat.add_sub_cancel,
        coeff_veroneseSection hr]

/-- All valid sections together determine a polynomial. -/
theorem eq_of_veroneseSection_eq {r : ℕ} (hr : 0 < r) {p q : A[X]}
    (h : ∀ i : Fin r, p.veroneseSection r i = q.veroneseSection r i) : p = q := by
  ext n
  have hc := congrArg (fun u : A[X] => u.coeff (n / r))
    (h ⟨n % r, Nat.mod_lt n hr⟩)
  simpa [coeff_veroneseSection hr, Nat.mod_add_div] using hc

end Semiring

section CommSemiring

variable [CommSemiring A]

/-- An expanded polynomial acts on each section by ordinary multiplication. -/
theorem veroneseSection_expand_mul {r i : ℕ} (hr : 0 < r) (hi : i < r)
    (a p : A[X]) :
    (expand A r a * p).veroneseSection r i = a * p.veroneseSection r i := by
  induction a using Polynomial.induction_on generalizing p with
  | C a => simp [veroneseSection_C_mul]
  | add a b ha hb => simp [add_mul, ha, hb]
  | monomial n a ha =>
      rw [pow_succ, ← mul_assoc, map_mul, expand_X,
        mul_comm (expand A r (C a * X ^ n)), mul_assoc,
        veroneseSection_X_pow_mul hr hi, ha]
      ring

private theorem not_dvd_sub_add_mul {r i j n : ℕ} (hi : i < r) (hj : j < r)
    (hij : i ≠ j) (hle : i ≤ j + r * n) : ¬r ∣ j + r * n - i := by
  rintro ⟨m, hm⟩
  have heq : j + r * n = i + r * m := by lia
  have hmod := congrArg (fun x : ℕ => x % r) heq
  simp [Nat.add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod
  exact hij hmod.symm

/-- A single expanded residue contribution has just one nonzero section. -/
theorem veroneseSection_X_pow_mul_expand {r : ℕ} (hr : 0 < r)
    (i j : Fin r) (p : A[X]) :
    (X ^ (j : ℕ) * expand A r p).veroneseSection r i = if i = j then p else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    ext n
    rw [coeff_veroneseSection hr, coeff_X_pow_mul', ite_eq_left (by lia)]
    simp [coeff_expand_mul' hr]
  · rw [ite_eq_right hij]
    ext n
    rw [coeff_veroneseSection hr, coeff_X_pow_mul']
    split_ifs with hle
    · rw [coeff_expand hr, ite_eq_right (not_dvd_sub_add_mul j.isLt i.isLt
        (fun h => hij (Fin.ext h.symm)) hle)]
      simp
    · simp

/-- Recompose a vector of residue polynomials by expansion and residue shifts. -/
def veroneseRecompose (r : ℕ) (v : Fin r → A[X]) : A[X] :=
  ∑ j : Fin r, X ^ (j : ℕ) * expand A r (v j)

/-- Taking a section of a recomposed vector recovers the selected entry. -/
@[simp] theorem veroneseSection_veroneseRecompose {r : ℕ} (hr : 0 < r)
    (v : Fin r → A[X]) (i : Fin r) :
    (veroneseRecompose r v).veroneseSection r i = v i := by
  simp [veroneseRecompose, veroneseSection_sum, veroneseSection_X_pow_mul_expand hr]

/-- Every polynomial is recovered from its vector of Veronese sections. -/
@[simp] theorem veroneseRecompose_veroneseSection {r : ℕ} (hr : 0 < r) (p : A[X]) :
    veroneseRecompose r (fun i => p.veroneseSection r i) = p := by
  apply eq_of_veroneseSection_eq hr
  intro i
  exact veroneseSection_veroneseRecompose hr _ i

/-- The section-coordinate matrix of multiplication by `p`.
Columns are the sections of `p * X ^ j`, so no algebra instance or quotient is needed. -/
def veroneseMulMatrix (r : ℕ) (p : A[X]) : Matrix (Fin r) (Fin r) A[X] :=
  fun i j => (p * X ^ (j : ℕ)).veroneseSection r i

/-- Multiplication of a recomposed vector is multiplication by its section matrix. -/
theorem veroneseSection_mul_veroneseRecompose {r : ℕ} (hr : 0 < r)
    (p : A[X]) (v : Fin r → A[X]) (i : Fin r) :
    (p * veroneseRecompose r v).veroneseSection r i =
      (veroneseMulMatrix r p *ᵥ v) i := by
  simp only [veroneseRecompose, Finset.mul_sum, veroneseSection_sum,
    Matrix.mulVec, dotProduct, veroneseMulMatrix]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, mul_comm (p * X ^ (j : ℕ)), veroneseSection_expand_mul hr i.isLt]
  exact mul_comm _ _

/-- The section vector of a product is its multiplication matrix applied to the second vector. -/
theorem veroneseSection_mul {r : ℕ} (hr : 0 < r) (p q : A[X]) (i : Fin r) :
    (p * q).veroneseSection r i =
      (veroneseMulMatrix r p *ᵥ fun j => q.veroneseSection r j) i := by
  rw [← veroneseSection_mul_veroneseRecompose hr, veroneseRecompose_veroneseSection hr]

/-- The multiplication matrix of one is the identity. -/
@[simp] theorem veroneseMulMatrix_one {r : ℕ} (hr : 0 < r) :
    veroneseMulMatrix r (1 : A[X]) = 1 := by
  apply Matrix.ext
  intro i j
  simpa [veroneseMulMatrix, Matrix.one_apply] using
    veroneseSection_X_pow_mul_expand hr i j (1 : A[X])

/-- Section multiplication matrices preserve products. -/
theorem veroneseMulMatrix_mul {r : ℕ} (hr : 0 < r) (p q : A[X]) :
    veroneseMulMatrix r (p * q) = veroneseMulMatrix r p * veroneseMulMatrix r q := by
  apply Matrix.ext
  intro i j
  simpa only [veroneseMulMatrix, mul_assoc, Matrix.mul_apply, Matrix.mulVec, dotProduct] using
    veroneseSection_mul hr p (q * X ^ (j : ℕ)) i

end CommSemiring

section CommRing

variable [CommRing A]

/-- The polynomial reconstructed from the first adjugate column of the section matrix. -/
def veroneseAdjugate {r : ℕ} (hr : 0 < r) (p : A[X]) : A[X] :=
  veroneseRecompose r (fun j => (veroneseMulMatrix r p).adjugate j ⟨0, hr⟩)

/-- The adjugate produces an expanded determinant multiple of the original polynomial. -/
theorem mul_veroneseAdjugate {r : ℕ} (hr : 0 < r) (p : A[X]) :
    p * veroneseAdjugate hr p = expand A r (veroneseMulMatrix r p).det := by
  apply eq_of_veroneseSection_eq hr
  intro i
  rw [veroneseAdjugate, veroneseSection_mul_veroneseRecompose hr]
  have h := congrArg (fun M : Matrix (Fin r) (Fin r) A[X] => M i ⟨0, hr⟩)
    (Matrix.mul_adjugate (veroneseMulMatrix r p))
  change (∑ j, veroneseMulMatrix r p i j *
    (veroneseMulMatrix r p).adjugate j ⟨0, hr⟩) = _
  rw [show expand A r (veroneseMulMatrix r p).det =
      X ^ (0 : ℕ) * expand A r (veroneseMulMatrix r p).det by simp,
    veroneseSection_X_pow_mul_expand hr i ⟨0, hr⟩]
  simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] using h

end CommRing

section Bivariate

variable [CommRing A]

/-- Take a Veronese section in the coefficient variable, leaving the outer variable fixed. -/
def veroneseSectionCoeffs (r i : ℕ) (p : A[X][X]) : A[X][X] :=
  ofFinsupp ⟨Finsupp.mapRange (veroneseSection r i) (veroneseSection_zero r i)
    p.toFinsupp.coeff⟩

/-- Coefficients of the section in the inner variable are the sections of the coefficients. -/
@[simp] theorem coeff_veroneseSectionCoeffs (r i n : ℕ) (p : A[X][X]) :
    (p.veroneseSectionCoeffs r i).coeff n = (p.coeff n).veroneseSection r i := rfl

/-- Every inner section of zero is zero. -/
@[simp] theorem veroneseSectionCoeffs_zero (r i : ℕ) :
    (0 : A[X][X]).veroneseSectionCoeffs r i = 0 := by
  ext n
  simp

/-- Inner sections commute with addition. -/
@[simp] theorem veroneseSectionCoeffs_add (r i : ℕ) (p q : A[X][X]) :
    (p + q).veroneseSectionCoeffs r i =
      p.veroneseSectionCoeffs r i + q.veroneseSectionCoeffs r i := by
  ext n
  simp

/-- Inner sections as additive homomorphisms on bivariate polynomials. -/
def veroneseSectionCoeffsAddHom (r i : ℕ) : A[X][X] →+ A[X][X] where
  toFun := veroneseSectionCoeffs r i
  map_zero' := veroneseSectionCoeffs_zero r i
  map_add' := veroneseSectionCoeffs_add r i

/-- Inner sections commute with finite sums. -/
theorem veroneseSectionCoeffs_sum {ι : Type*} (r i : ℕ) (s : Finset ι)
    (f : ι → A[X][X]) :
    (∑ j ∈ s, f j).veroneseSectionCoeffs r i =
      ∑ j ∈ s, (f j).veroneseSectionCoeffs r i :=
  map_sum (veroneseSectionCoeffsAddHom r i) f s

/-- Sections in the coefficient variable do not increase the outer degree. -/
theorem natDegree_veroneseSectionCoeffs_le (r i : ℕ) (p : A[X][X]) :
    (p.veroneseSectionCoeffs r i).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp [coeff_eq_zero_of_natDegree_lt hn]

/-- Inner sections commute with multiplication by a polynomial with expanded coefficients. -/
theorem veroneseSectionCoeffs_map_expand_mul {r i : ℕ} (hr : 0 < r) (hi : i < r)
    (a p : A[X][X]) :
    (a.map (expand A r).toRingHom * p).veroneseSectionCoeffs r i =
      a * p.veroneseSectionCoeffs r i := by
  apply Polynomial.ext
  intro n
  simp only [coeff_veroneseSectionCoeffs, coeff_mul, coeff_map]
  rw [veroneseSection_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact veroneseSection_expand_mul hr hi _ _

/-- Recompose a vector of bivariate polynomials in the inner variable. -/
def veroneseRecomposeCoeffs (r : ℕ) (v : Fin r → A[X][X]) : A[X][X] :=
  ∑ j : Fin r, C (X ^ (j : ℕ)) * (v j).map (expand A r).toRingHom

/-- Outer coefficients commute with reconstruction in the inner variable. -/
@[simp] theorem coeff_veroneseRecomposeCoeffs (r n : ℕ) (v : Fin r → A[X][X]) :
    (veroneseRecomposeCoeffs r v).coeff n =
      veroneseRecompose r (fun j => (v j).coeff n) := by
  simp only [veroneseRecomposeCoeffs, veroneseRecompose, finsetSum_coeff,
    coeff_C_mul, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

/-- A section of inner reconstruction recovers its selected entry. -/
@[simp] theorem veroneseSectionCoeffs_veroneseRecomposeCoeffs {r : ℕ} (hr : 0 < r)
    (v : Fin r → A[X][X]) (i : Fin r) :
    (veroneseRecomposeCoeffs r v).veroneseSectionCoeffs r i = v i := by
  ext n
  simp [veroneseSection_veroneseRecompose hr]

/-- Inner reconstruction recovers every bivariate polynomial from its sections. -/
@[simp] theorem veroneseRecomposeCoeffs_veroneseSectionCoeffs {r : ℕ} (hr : 0 < r)
    (p : A[X][X]) :
    veroneseRecomposeCoeffs r (fun i => p.veroneseSectionCoeffs r i) = p := by
  ext n
  simp [veroneseRecompose_veroneseSection hr]

/-- Bivariate polynomials are determined by their inner sections. -/
theorem eq_of_veroneseSectionCoeffs_eq {r : ℕ} (hr : 0 < r) {p q : A[X][X]}
    (h : ∀ i : Fin r, p.veroneseSectionCoeffs r i = q.veroneseSectionCoeffs r i) :
    p = q := by
  calc
    p = veroneseRecomposeCoeffs r (fun i => p.veroneseSectionCoeffs r i) :=
      (veroneseRecomposeCoeffs_veroneseSectionCoeffs hr p).symm
    _ = veroneseRecomposeCoeffs r (fun i => q.veroneseSectionCoeffs r i) := by
      exact congrArg (veroneseRecomposeCoeffs r) (_root_.funext h)
    _ = q := veroneseRecomposeCoeffs_veroneseSectionCoeffs hr q

/-- The multiplication matrix in the inner variable; the outer variable is unchanged. -/
def veroneseMatrix (r : ℕ) (p : A[X][X]) : Matrix (Fin r) (Fin r) A[X][X] :=
  fun i j => (p * C (X ^ (j : ℕ))).veroneseSectionCoeffs r i

/-- The outer coefficients of the bivariate section matrix are univariate section matrices. -/
@[simp] theorem coeff_veroneseMatrix (r n : ℕ) (p : A[X][X]) (i j : Fin r) :
    (veroneseMatrix r p i j).coeff n = veroneseMulMatrix r (p.coeff n) i j := by
  simp only [veroneseMatrix, veroneseMulMatrix, coeff_veroneseSectionCoeffs, coeff_mul_C]

/-- Entries of the section matrix have outer degree at most the original outer degree. -/
theorem natDegree_veroneseMatrix_le (r : ℕ) (p : A[X][X]) (i j : Fin r) :
    (veroneseMatrix r p i j).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp [coeff_eq_zero_of_natDegree_lt hn, veroneseMulMatrix]

/-- The inner section matrix describes multiplication of a recomposed vector. -/
theorem veroneseSectionCoeffs_mul_veroneseRecomposeCoeffs {r : ℕ} (hr : 0 < r)
    (p : A[X][X]) (v : Fin r → A[X][X]) (i : Fin r) :
    (p * veroneseRecomposeCoeffs r v).veroneseSectionCoeffs r i =
      (veroneseMatrix r p *ᵥ v) i := by
  simp only [veroneseRecomposeCoeffs, Finset.mul_sum, veroneseSectionCoeffs_sum,
    Matrix.mulVec, dotProduct, veroneseMatrix]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, mul_comm (p * C (X ^ (j : ℕ))),
    veroneseSectionCoeffs_map_expand_mul hr i.isLt]
  exact mul_comm _ _

/-- The explicit section-matrix determinant in the inner variable.
For recurrence applications the outer variable is the forward-shift variable. -/
def veroneseNorm (r : ℕ) (p : A[X][X]) : A[X][X] :=
  (veroneseMatrix r p).det

/-- The outer degree of the norm is bounded by the modulus times the original degree. -/
theorem natDegree_veroneseNorm_le (r : ℕ) (p : A[X][X]) :
    (veroneseNorm r p).natDegree ≤ r * p.natDegree := by
  rw [veroneseNorm, Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  refine (natDegree_smul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  calc
    (∑ i : Fin r, (veroneseMatrix r p (σ i) i).natDegree) ≤
        ∑ _i : Fin r, p.natDegree :=
      Finset.sum_le_sum (fun i _ => natDegree_veroneseMatrix_le r p (σ i) i)
    _ = r * p.natDegree := by simp

/-- At a uniform outer degree bound, the top norm coefficient is a section determinant. -/
theorem coeff_veroneseNorm_mul {r d : ℕ} (p : A[X][X]) (hd : p.natDegree ≤ d) :
    (veroneseNorm r p).coeff (r * d) = (veroneseMulMatrix r (p.coeff d)).det := by
  simp only [veroneseNorm, Matrix.det_apply', finsetSum_coeff, coeff_intCast_mul]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  have hdeg (j : Fin r) (_ : j ∈ Finset.univ) :
      (veroneseMatrix r p (σ j) j).natDegree ≤ d :=
    (natDegree_veroneseMatrix_le r p (σ j) j).trans hd
  simpa only [Finset.card_univ, Fintype.card_fin, coeff_veroneseMatrix] using
    coeff_prod_of_natDegree_le Finset.univ (fun j => veroneseMatrix r p (σ j) j) d hdeg

/-- A normalized denominator has normalized Veronese norm. -/
theorem coeff_veroneseNorm_zero {r : ℕ} (hr : 0 < r) {p : A[X][X]}
    (hp : p.coeff 0 = 1) : (veroneseNorm r p).coeff 0 = 1 := by
  have hmap : (constantCoeff : A[X][X] →+* A[X]).mapMatrix (veroneseMatrix r p) = 1 := by
    apply Matrix.ext
    intro i j
    change (veroneseMatrix r p i j).coeff 0 = (1 : Matrix (Fin r) (Fin r) A[X]) i j
    rw [coeff_veroneseMatrix, hp, veroneseMulMatrix_one hr]
  change constantCoeff (veroneseMatrix r p).det = 1
  rw [RingHom.map_det, hmap, Matrix.det_one]

/-- In the forward convention, a monic polynomial has monic Veronese norm. -/
theorem Monic.veroneseNorm {r : ℕ} (hr : 0 < r) {p : A[X][X]} (hp : p.Monic) :
    (veroneseNorm r p).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (r * p.natDegree)
    (natDegree_veroneseNorm_le r p)
  rw [coeff_veroneseNorm_mul p le_rfl, hp.coeff_natDegree, veroneseMulMatrix_one hr,
    Matrix.det_one]

/-- Over a nontrivial ring the forward norm has exactly the expected outer degree. -/
theorem Monic.natDegree_veroneseNorm [Nontrivial A] {r : ℕ} (hr : 0 < r)
    {p : A[X][X]} (hp : p.Monic) :
    (Polynomial.veroneseNorm r p).natDegree = r * p.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_veroneseNorm_le r p)
  rw [coeff_veroneseNorm_mul p le_rfl, hp.coeff_natDegree, veroneseMulMatrix_one hr,
    Matrix.det_one]
  exact one_ne_zero

/-- The first adjugate column, reconstructed in the inner variable. -/
def veroneseAdjugateCoeffs {r : ℕ} (hr : 0 < r) (p : A[X][X]) : A[X][X] :=
  veroneseRecomposeCoeffs r (fun j => (veroneseMatrix r p).adjugate j ⟨0, hr⟩)

/-- The adjugate factorization of the inner-variable Veronese norm. -/
theorem mul_veroneseAdjugateCoeffs {r : ℕ} (hr : 0 < r) (p : A[X][X]) :
    p * veroneseAdjugateCoeffs hr p = (veroneseNorm r p).map (expand A r).toRingHom := by
  apply eq_of_veroneseSectionCoeffs_eq hr
  intro i
  rw [veroneseAdjugateCoeffs, veroneseSectionCoeffs_mul_veroneseRecomposeCoeffs hr]
  have h := congrArg (fun M : Matrix (Fin r) (Fin r) A[X][X] => M i ⟨0, hr⟩)
    (Matrix.mul_adjugate (veroneseMatrix r p))
  have hsection :
      ((veroneseNorm r p).map (expand A r).toRingHom).veroneseSectionCoeffs r i =
        if i = ⟨0, hr⟩ then veroneseNorm r p else 0 := by
    apply Polynomial.ext
    intro n
    by_cases hi : i = ⟨0, hr⟩
    · simpa [coeff_veroneseSectionCoeffs, hi] using
        veroneseSection_X_pow_mul_expand hr i ⟨0, hr⟩ ((veroneseNorm r p).coeff n)
    · simpa [coeff_veroneseSectionCoeffs, hi] using
        veroneseSection_X_pow_mul_expand hr i ⟨0, hr⟩ ((veroneseNorm r p).coeff n)
  rw [hsection]
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, veroneseNorm] using h

end Bivariate

end

end Polynomial
