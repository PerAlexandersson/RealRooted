import RealRooted.Basic
import RealRooted.AffineFamily
import RealRooted.FolkloreLemma
import RealRooted.PosCombo
import RealRooted.ProductFamily
import RealRooted.WagnerX
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Symmetric decompositions and real-rootedness

This file sets up the `I_d` / `R_d` symmetric-decomposition infrastructure
from Brändén--Solus and records the main interlacing target needed later.

Reference:

@article{BrandenSolus2018,
  author = {Petter Brändén and Liam Solus},
  title = {Symmetric decompositions and real-rootedness},
  year = {2018},
  journal = {None},
  doi = {10.1093/imrn/rnz059},
  url = {https://doi.org/10.1093/imrn/rnz059}
}

The intended first milestones are:
1. formalize the `I_d`- and `R_d`-decomposition existence/uniqueness lemmas
   from Section 2,
2. connect the `I_d`- and `R_d`-decompositions through the `f`-polynomial
   transform,
3. prove Theorem 2.6 in the current `Prec` language.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

section

/-- Brändén--Solus `I_d(p) = x^d p(1/x)`, implemented using Mathlib's bounded
coefficient reflection operator. -/
def IdTransform (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  p.reflect d

@[simp] lemma IdTransform_zero (d : ℕ) :
    IdTransform d (0 : ℝ[X]) = 0 := by
  simp [IdTransform]

@[simp] lemma IdTransform_add (d : ℕ) (p q : ℝ[X]) :
    IdTransform d (p + q) = IdTransform d p + IdTransform d q := by
  simp [IdTransform]

/-- Brändén--Solus `R_d(p)(x) = (-1)^d p(-1 - x)`. -/
def RdTransform (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C (((-1 : ℝ) ^ d)) * p.comp (-X - 1)

/-- The `f`-polynomial transform from equation (2.2), written in coefficient
form to avoid rational-function substitution. -/
def fPolynomial (d : ℕ) (h : ℝ[X]) : ℝ[X] :=
  Finset.sum (Finset.range (d + 1))
    (fun k => C (h.coeff k) * X ^ k * (X + 1) ^ (d - k))

/-- Formula from Lemma 2.1 for the symmetric `I_d`-decomposition component
`a = (p - x I_d(p)) / (1 - x)`, rewritten with monic denominator `X - 1`. -/
def idDecompositionAFormula (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (X * IdTransform d p - p) /ₘ (X - 1)

/-- Formula from Lemma 2.1 for the symmetric `I_d`-decomposition component
`b = (I_d(p) - p) / (1 - x)`, rewritten with monic denominator `X - 1`. -/
def idDecompositionBFormula (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (p - IdTransform d p) /ₘ (X - 1)

/-- Formula from Lemma 2.2 for the symmetric `R_d`-decomposition component
`\tilde a = (1 + x) p - x R_d(p)`. -/
def rdDecompositionAFormula (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (X + 1) * p - X * RdTransform d p

/-- Formula from Lemma 2.2 for the symmetric `R_d`-decomposition component
`\tilde b = R_d(p) - p`. -/
def rdDecompositionBFormula (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  RdTransform d p - p

/-- Predicate saying that `(a,b)` is the `I_d`-decomposition of `p` in the
sense of Brändén--Solus Lemma 2.1. -/
def IsIdDecomposition (d : ℕ) (p a b : ℝ[X]) : Prop :=
  p = a + X * b ∧
  a.natDegree ≤ d ∧
  b.natDegree ≤ d - 1 ∧
  IdTransform d a = a ∧
  IdTransform (d - 1) b = b

/-- Predicate saying that `(a,b)` is the `R_d`-decomposition of `p` in the
sense of Brändén--Solus Lemma 2.2. -/
def IsRdDecomposition (d : ℕ) (p a b : ℝ[X]) : Prop :=
  p = a + X * b ∧
  a.natDegree ≤ d ∧
  b.natDegree ≤ d - 1 ∧
  RdTransform d a = a ∧
  RdTransform (d - 1) b = b

@[simp] lemma fPolynomial_zero (d : ℕ) :
    fPolynomial d 0 = 0 := by
  simp [fPolynomial]

@[simp] lemma fPolynomial_add (d : ℕ) (p q : ℝ[X]) :
    fPolynomial d (p + q) = fPolynomial d p + fPolynomial d q := by
  unfold fPolynomial
  have hterm :
      (fun x => C ((p + q).coeff x) * X ^ x * (X + 1) ^ (d - x)) =
        (fun x => C (p.coeff x) * X ^ x * (X + 1) ^ (d - x) +
          C (q.coeff x) * X ^ x * (X + 1) ^ (d - x)) := by
    funext x
    simp [coeff_add, add_mul]
  rw [hterm, Finset.sum_add_distrib]

@[simp] lemma fPolynomial_C_mul (d : ℕ) (a : ℝ) (p : ℝ[X]) :
    fPolynomial d (C a * p) = C a * fPolynomial d p := by
  unfold fPolynomial
  calc
    ∑ k ∈ Finset.range (d + 1),
        C ((C a * p).coeff k) * X ^ k * (X + 1) ^ (d - k)
      = ∑ k ∈ Finset.range (d + 1),
          C a * (C (p.coeff k) * X ^ k * (X + 1) ^ (d - k)) := by
            grind
    _ = C a * ∑ k ∈ Finset.range (d + 1),
          C (p.coeff k) * X ^ k * (X + 1) ^ (d - k) := by
            rw [Finset.mul_sum]

lemma fPolynomial_succ_of_natDegree_le {d : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    fPolynomial (d + 1) p = (X + 1) * fPolynomial d p := by
  unfold fPolynomial
  rw [Finset.sum_range_succ]
  have htop : p.coeff (d + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (Nat.lt_succ_self d))
  rw [htop]
  simp only [map_zero, zero_mul, tsub_self, pow_zero, mul_one, add_zero]
  calc
    ∑ k ∈ Finset.range (d + 1),
        C (p.coeff k) * X ^ k * (X + 1) ^ (d + 1 - k)
      = ∑ k ∈ Finset.range (d + 1),
          (X + 1) * (C (p.coeff k) * X ^ k * (X + 1) ^ (d - k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            have hsub : d + 1 - k = (d - k) + 1 := by lia
            grind
    _ = (X + 1) * ∑ k ∈ Finset.range (d + 1),
          C (p.coeff k) * X ^ k * (X + 1) ^ (d - k) := by
            rw [Finset.mul_sum]

lemma HasNonnegCoeffs.pow {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    ∀ n : ℕ, HasNonnegCoeffs (p ^ n)
  | 0 => by simpa using hasNonnegCoeffs_one
  | n + 1 => by
      simpa [pow_succ] using (HasNonnegCoeffs.pow hp n).mul hp

lemma hasNonnegCoeffs_X_add_one : HasNonnegCoeffs (X + 1 : ℝ[X]) := by
  simpa using hasNonnegCoeffs_X.add hasNonnegCoeffs_one

lemma hasNonnegCoeffs_IdTransform_iff {d : ℕ} {p : ℝ[X]} :
    HasNonnegCoeffs (IdTransform d p) ↔ HasNonnegCoeffs p := by
  constructor
  · intro hp n
    have h := hp (Polynomial.revAt d n)
    simpa [IdTransform, Polynomial.coeff_reflect, Polynomial.revAt_invol] using h
  · intro hp n
    simpa [IdTransform, Polynomial.coeff_reflect] using hp (Polynomial.revAt d n)

lemma hasNonnegCoeffs_fPolynomial {d : ℕ} {h : ℝ[X]} (hh : HasNonnegCoeffs h) :
    HasNonnegCoeffs (fPolynomial d h) := by
  classical
  unfold fPolynomial
  refine Finset.induction_on (Finset.range (d + 1)) ?base ?step
  · simpa using hasNonnegCoeffs_zero
  · intro k s hk hs
    have hterm : HasNonnegCoeffs (C (h.coeff k) * X ^ k * (X + 1) ^ (d - k)) := by
      have hXk : HasNonnegCoeffs (X ^ k) := HasNonnegCoeffs.pow hasNonnegCoeffs_X k
      have hXp : HasNonnegCoeffs ((X + 1) ^ (d - k)) :=
        HasNonnegCoeffs.pow hasNonnegCoeffs_X_add_one (d - k)
      have hprod : HasNonnegCoeffs (X ^ k * (X + 1) ^ (d - k)) := hXk.mul hXp
      simpa [mul_assoc] using nonnegCoeffs_C_mul (hh k) hprod
    simpa [Finset.sum_insert, hk] using hterm.add hs

lemma fPolynomial_monomial (d n : ℕ) (a : ℝ) :
    fPolynomial d (monomial n a) =
      if n ≤ d then C a * X ^ n * (X + 1) ^ (d - n) else 0 := by
  by_cases h : n ≤ d
  · have hn : n ∈ Finset.range (d + 1) := by
      simp_all
    unfold fPolynomial
    rw [Finset.sum_eq_single n]
    · simp_all
    · intro k hk hkn
      have hcoeff : (monomial n a).coeff k = 0 := by
        simp [coeff_monomial, mt Eq.symm hkn]
      simp_all
    · lia
  · unfold fPolynomial
    have hsum :
        ∑ k ∈ Finset.range (d + 1),
          C (((monomial n a).coeff k)) * X ^ k * (X + 1) ^ (d - k) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hklt : k < d + 1 := Finset.mem_range.mp hk
      have hkn : k ≠ n := by
        lia
      have hcoeff : (monomial n a).coeff k = 0 := by
        simp [coeff_monomial, mt Eq.symm hkn]
      simp_all
    lia

lemma fPolynomial_natDegree_le (d : ℕ) (h : ℝ[X]) :
    (fPolynomial d h).natDegree ≤ d := by
  unfold fPolynomial
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.range (d + 1))
    (f := fun k => C (h.coeff k) * X ^ k * (X + 1) ^ (d - k)) ?_
  intro k hk
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hleft : (C (h.coeff k) * X ^ k).natDegree ≤ k :=
    (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le k)
  have hright : ((X + 1) ^ (d - k) : ℝ[X]).natDegree ≤ d - k := by
    rw [show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp]
    exact le_of_eq (Polynomial.natDegree_pow_X_add_C (n := d - k) (r := (1 : ℝ)))
  calc
    (C (h.coeff k) * X ^ k * (X + 1) ^ (d - k)).natDegree
        ≤ k + (d - k) := by
            simpa [mul_assoc] using (Polynomial.natDegree_mul_le_of_le hleft hright)
    _ = d := by lia

lemma coeff_fPolynomial_top (d : ℕ) (h : ℝ[X]) :
    (fPolynomial d h).coeff d = ∑ k ∈ Finset.range (d + 1), h.coeff k := by
  unfold fPolynomial
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show C (h.coeff k) * X ^ k = Polynomial.monomial k (h.coeff k) by
    rw [Polynomial.C_mul_X_pow_eq_monomial]]
  have hdk : d = (d - k) + k := by lia
  rw [hdk, Polynomial.coeff_monomial_mul, Polynomial.coeff_X_add_one_pow]
  simp

lemma eval_one_eq_sum_coeffs_of_natDegree_le {d : ℕ} {h : ℝ[X]}
    (hd : h.natDegree ≤ d) :
    h.eval 1 = ∑ k ∈ Finset.range (d + 1), h.coeff k := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hd)]
  simp

lemma coeff_fPolynomial_top_eq_eval_one {d : ℕ} {h : ℝ[X]}
    (hd : h.natDegree ≤ d) :
    (fPolynomial d h).coeff d = h.eval 1 := by
  rw [coeff_fPolynomial_top]
  exact (eval_one_eq_sum_coeffs_of_natDegree_le hd).symm

lemma eval_neg_one_fPolynomial (d : ℕ) (h : ℝ[X]) :
    (fPolynomial d h).eval (-1) = h.coeff d * (-1) ^ d := by
  unfold fPolynomial
  rw [Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single d]
  · simp
  · intro k hk hkd
    have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hk_lt : k < d := lt_of_le_of_ne hk_le hkd
    have hsub_pos : 0 < d - k := Nat.sub_pos_of_lt hk_lt
    simp [Polynomial.eval_mul, hsub_pos.ne']
  · simp

lemma eval_one_pos_of_hasNonnegCoeffs {h : ℝ[X]}
    (hh : HasNonnegCoeffs h) (h0 : h ≠ 0) :
    0 < h.eval 1 := by
  have heval :
      h.eval 1 = ∑ i ∈ Finset.range (h.natDegree + 1), h.coeff i := by
    simpa [one_pow, mul_one] using (Polynomial.eval_eq_sum_range (p := h) (x := (1 : ℝ)))
  rw [heval]
  have htop_coeff : 0 < h.coeff h.natDegree := by
    rw [coeff_natDegree]
    exact hh.pos_leadingCoeff h0
  have hle :
      h.coeff h.natDegree ≤
        ∑ i ∈ Finset.range (h.natDegree + 1), h.coeff i :=
    Finset.single_le_sum
      (fun i hi => hh i)
      (Finset.mem_range.mpr (Nat.lt_succ_self _))
  grind

lemma eval_pos_of_hasNonnegCoeffs_of_pos {h : ℝ[X]}
    (hh : HasNonnegCoeffs h) (h0 : h ≠ 0) {x : ℝ} (hx : 0 < x) :
    0 < h.eval x := by
  have heval :
      h.eval x = ∑ i ∈ Finset.range (h.natDegree + 1), h.coeff i * x ^ i := by
    simpa using Polynomial.eval_eq_sum_range (p := h) (x := x)
  rw [heval]
  have hpow_pos : 0 < x ^ h.natDegree := pow_pos hx _
  have htop_coeff : 0 < h.leadingCoeff := hh.pos_leadingCoeff h0
  have htop_term : 0 < h.leadingCoeff * x ^ h.natDegree :=
    mul_pos htop_coeff hpow_pos
  have hle :
      h.leadingCoeff * x ^ h.natDegree ≤
        ∑ i ∈ Finset.range (h.natDegree + 1), h.coeff i * x ^ i :=
    Finset.single_le_sum
      (s := Finset.range (h.natDegree + 1))
      (f := fun i => h.coeff i * x ^ i)
      (fun i hi => mul_nonneg (hh i) (pow_nonneg hx.le _))
      (Finset.mem_range.mpr (Nat.lt_succ_self _))
  grind

lemma fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero {d : ℕ} {h : ℝ[X]}
    (hd : h.natDegree ≤ d) (hh : HasNonnegCoeffs h) (h0 : h ≠ 0) :
    (fPolynomial d h).natDegree = d := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (fPolynomial_natDegree_le d h)
  rw [coeff_fPolynomial_top_eq_eval_one hd]
  exact ne_of_gt (eval_one_pos_of_hasNonnegCoeffs hh h0)

lemma leadingCoeff_fPolynomial_eq_eval_one {d : ℕ} {h : ℝ[X]}
    (hd : h.natDegree ≤ d) (hh : HasNonnegCoeffs h) (h0 : h ≠ 0) :
    (fPolynomial d h).leadingCoeff = h.eval 1 := by
  rw [Polynomial.leadingCoeff, fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hd hh h0]
  exact coeff_fPolynomial_top_eq_eval_one hd

lemma fPolynomial_X_mul_succ (d : ℕ) (p : ℝ[X]) :
    fPolynomial (d + 1) (X * p) = X * fPolynomial d p := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    rw [show X * (p + q) = X * p + X * q by grind]
    rw [fPolynomial_add, fPolynomial_add, hp, hq]
    ring
  · intro n a
    by_cases h : n ≤ d
    · have hs : n + 1 ≤ d + 1 := Nat.succ_le_succ h
      have hf : fPolynomial d (monomial n a) = C a * X ^ n * (X + 1) ^ (d - n) := by
        simpa [h] using (fPolynomial_monomial d n a)
      rw [Polynomial.X_mul_monomial, fPolynomial_monomial, hf]
      grind
    · have hs : ¬ n + 1 ≤ d + 1 := by
        lia
      rw [Polynomial.X_mul_monomial, fPolynomial_monomial]
      rw [show fPolynomial d (monomial n a) = 0 by simpa [h] using (fPolynomial_monomial d n a)]
      lia

lemma fPolynomial_pad_by_X_add_one_pow {m d : ℕ} {p : ℝ[X]}
    (hm : p.natDegree ≤ m) (hmd : m ≤ d) :
    fPolynomial d p = (X + 1) ^ (d - m) * fPolynomial m p := by
  have hpad : ∀ n : ℕ, fPolynomial (m + n) p = (X + 1) ^ n * fPolynomial m p := by
    intro n
    induction n with
    | zero =>
        lia
    | succ n ih =>
        have hm' : p.natDegree ≤ m + n := le_trans hm (Nat.le_add_right _ _)
        rw [show m + n.succ = (m + n) + 1 by lia]
        rw [fPolynomial_succ_of_natDegree_le hm', ih]
        grind
  grind

lemma fPolynomial_X_sub_C_mul_succ (d : ℕ) (r : ℝ) {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    fPolynomial (d + 1) ((X - C r) * p) =
      (C (1 - r) * X - C r) * fPolynomial d p := by
  have hmul : (X - C r) * p = X * p + C (-r) * p := by
    grind
  calc
    fPolynomial (d + 1) ((X - C r) * p)
      = fPolynomial (d + 1) (X * p + C (-r) * p) := by
          lia
    _ = X * fPolynomial d p + C (-r) * fPolynomial (d + 1) p := by
          rw [fPolynomial_add, fPolynomial_X_mul_succ, fPolynomial_C_mul]
    _ = X * fPolynomial d p + C (-r) * ((X + 1) * fPolynomial d p) := by
          rw [fPolynomial_succ_of_natDegree_le hp]
    _ = (C (1 - r) * X - C r) * fPolynomial d p := by
          grind

lemma transformedRoot_nonpos {r : ℝ} (hr : r ≤ 0) :
    r / (1 - r) ≤ 0 := by
  have h1r_pos : 0 < 1 - r := by grind
  have h1r_inv_nonneg : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr h1r_pos.le
  have hmul_nonpos : r * (1 - r)⁻¹ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hr h1r_inv_nonneg
  lia

/-- Inverse Möbius map to `r ↦ r / (1-r)` on `(-1, ∞)`. -/
def untransformRoot (x : ℝ) : ℝ := x / (1 + x)

lemma untransformRoot_nonpos {x : ℝ} (hx1 : -1 < x) (hx0 : x ≤ 0) :
    untransformRoot x ≤ 0 := by
  have h1x_pos : 0 < 1 + x := by grind
  have h1x_inv_nonneg : 0 ≤ (1 + x)⁻¹ := inv_nonneg.mpr h1x_pos.le
  simpa [untransformRoot, div_eq_mul_inv] using
    mul_nonpos_of_nonpos_of_nonneg hx0 h1x_inv_nonneg

lemma transformedRoot_untransformRoot {x : ℝ} (hx1 : -1 < x) :
    untransformRoot x / (1 - untransformRoot x) = x := by
  have h1x_ne : 1 + x ≠ 0 := by grind
  have hden : 1 - x / (1 + x) = (1 : ℝ) / (1 + x) := by
    grind
  rw [untransformRoot, hden]
  simp_all

lemma untransformRoot_transformedRoot {r : ℝ} (hr : r ≤ 0) :
    untransformRoot (r / (1 - r)) = r := by
  have h1r_ne : 1 - r ≠ 0 := by grind
  have hden : 1 + r / (1 - r) = (1 : ℝ) / (1 - r) := by
    grind
  rw [untransformRoot, hden]
  simp_all

lemma eval_fPolynomial_eq_mul_eval_untransform {d : ℕ} {p : ℝ[X]}
    (hd : p.natDegree ≤ d) {x : ℝ} (hx : x ≠ -1) :
    (fPolynomial d p).eval x = (1 + x) ^ d * p.eval (untransformRoot x) := by
  have h1x_ne : 1 + x ≠ 0 := by
    grind
  unfold fPolynomial
  rw [Polynomial.eval_finsetSum, Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hd)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc
    (C (p.coeff k) * X ^ k * (X + 1) ^ (d - k)).eval x
        = p.coeff k * x ^ k * (x + 1) ^ (d - k) := by
            simp
    _ = p.coeff k * x ^ k * (1 + x) ^ (d - k) := by
          grind
    _ = p.coeff k * (x ^ k * (1 + x) ^ (d - k)) := by
          grind
    _ = p.coeff k * ((1 + x) ^ d * (untransformRoot x) ^ k) := by
          have hterm :
              (1 + x) ^ d * (untransformRoot x) ^ k = x ^ k * (1 + x) ^ (d - k) := by
            calc
              (1 + x) ^ d * (untransformRoot x) ^ k
                  = (1 + x) ^ d * (x / (1 + x)) ^ k := by
                      simp [untransformRoot]
              _ = (1 + x) ^ d * (x ^ k * ((1 + x) ^ k)⁻¹) := by
                    rw [div_eq_mul_inv, mul_pow, inv_pow]
              _ = x ^ k * ((1 + x) ^ d * ((1 + x) ^ k)⁻¹) := by grind
              _ = x ^ k * (1 + x) ^ (d - k) := by
                    rw [← pow_sub₀ (1 + x) h1x_ne hk_le]
          lia
    _ = (1 + x) ^ d * (p.coeff k * (untransformRoot x) ^ k) := by
          ring

lemma neg_one_lt_transformedRoot {r : ℝ} (hr : r ≤ 0) :
    -1 < r / (1 - r) := by
  have h1r_pos : 0 < 1 - r := by grind
  have hmul : (-1 : ℝ) * (1 - r) < r := by simp
  exact (lt_div_iff₀ h1r_pos).2 hmul

lemma untransformRoot_mono_of_neg_one_lt {x y : ℝ}
    (hxy : x ≤ y) (hx1 : -1 < x) :
    untransformRoot x ≤ untransformRoot y := by
  have hy1 : -1 < y := lt_of_lt_of_le hx1 hxy
  have h1x_pos : 0 < 1 + x := by grind
  have h1y_pos : 0 < 1 + y := by grind
  rw [untransformRoot, untransformRoot, div_le_div_iff₀ h1x_pos h1y_pos]
  nlinarith

lemma transformedRoot_mono_of_nonpos {r s : ℝ}
    (hrs : r ≤ s) (hs : s ≤ 0) :
    r / (1 - r) ≤ s / (1 - s) := by
  have h1r_pos : 0 < 1 - r := by grind
  have h1s_pos : 0 < 1 - s := by grind
  rw [div_le_div_iff₀ h1r_pos h1s_pos]
  nlinarith

lemma pairwise_map_transformedRoot_of_nonpos :
    ∀ {rs : List ℝ}, rs.Pairwise (· ≤ ·) →
      (∀ r ∈ rs, r ≤ 0) →
      (rs.map (fun r : ℝ => r / (1 - r))).Pairwise (· ≤ ·)
  | [], _, _ => by simp
  | r :: rs, hrs, hnonpos => by
      rw [List.pairwise_cons] at hrs
      rw [List.map, List.pairwise_cons]
      constructor
      · intro y hy
        rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
        exact transformedRoot_mono_of_nonpos (hrs.1 z hz) (hnonpos z (by simp_all))
      · exact pairwise_map_transformedRoot_of_nonpos hrs.2 (fun z hz => hnonpos z (by simp_all))

lemma listInterlaces_map_transformedRoot_of_nonpos :
    ∀ {ss rs : List ℝ}, ListInterlaces ss rs →
      (∀ r ∈ rs, r ≤ 0) →
      ListInterlaces (ss.map (fun r : ℝ => r / (1 - r)))
        (rs.map (fun r : ℝ => r / (1 - r)))
  | [], [], _, _ => by simp_all
  | [], [_], _, _ => by simp [ListInterlaces]
  | s :: ss, r₁ :: r₂ :: rs, h, hnonpos => by
      rcases h with ⟨hr₁s, hsr₂, htail⟩
      have hs_nonpos : s ≤ 0 := le_trans hsr₂ (hnonpos r₂ (by simp))
      refine ⟨?_, ?_, ?_⟩
      · exact transformedRoot_mono_of_nonpos hr₁s hs_nonpos
      · exact transformedRoot_mono_of_nonpos hsr₂ (hnonpos r₂ (by simp))
      · exact listInterlaces_map_transformedRoot_of_nonpos htail
          (fun r hr => hnonpos r (by simp_all))
  | [], _ :: _ :: _, h, _ => by simp [ListInterlaces] at h
  | _ :: _, [], h, _ => by simp [ListInterlaces] at h
  | _ :: _ :: _, [_], h, _ => by simp [ListInterlaces] at h

lemma listAlternates_map_transformedRoot_of_nonpos :
    ∀ {ss rs : List ℝ}, ListAlternates ss rs →
      (∀ r ∈ rs, r ≤ 0) →
      ListAlternates (ss.map (fun r : ℝ => r / (1 - r)))
        (rs.map (fun r : ℝ => r / (1 - r)))
  | [], [], _, _ => by simp_all
  | s :: ss, r :: rs, h, hnonpos => by
      rcases h with ⟨hsr, htail⟩
      exact ⟨transformedRoot_mono_of_nonpos hsr (hnonpos r (by simp)),
        listInterlaces_map_transformedRoot_of_nonpos htail (fun t ht => hnonpos t (by lia))⟩
  | [], _ :: _, h, _ => by simp [ListAlternates] at h
  | _ :: _, [], h, _ => by simp [ListAlternates] at h

lemma listAlternates_neg_one_cons_map_of_listInterlaces_of_nonpos
    {ss : List ℝ} {r₁ : ℝ} {rs : List ℝ}
    (hint : ListInterlaces ss (r₁ :: rs))
    (hnonpos : ∀ r ∈ (r₁ :: rs), r ≤ 0) :
    ListAlternates ((-1) :: ss.map (fun r : ℝ => r / (1 - r)))
      ((r₁ :: rs).map (fun r : ℝ => r / (1 - r))) := by
  refine ⟨le_of_lt (neg_one_lt_transformedRoot (hnonpos r₁ (by simp))), ?_⟩
  exact listInterlaces_map_transformedRoot_of_nonpos hint hnonpos

lemma pairwise_map_untransformRoot_of_neg_one_lt :
    ∀ {rs : List ℝ}, rs.Pairwise (· ≤ ·) →
      (∀ r ∈ rs, -1 < r) →
      (rs.map untransformRoot).Pairwise (· ≤ ·)
  | [], _, _ => by simp
  | r :: rs, hrs, hgt => by
      rw [List.pairwise_cons] at hrs
      rw [List.map, List.pairwise_cons]
      constructor
      · intro y hy
        rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
        exact untransformRoot_mono_of_neg_one_lt (hrs.1 z hz) (hgt r (by simp))
      · exact pairwise_map_untransformRoot_of_neg_one_lt hrs.2 (fun z hz => hgt z (by simp_all))

lemma listInterlaces_map_untransformRoot_of_neg_one_lt :
    ∀ {ss rs : List ℝ}, ListInterlaces ss rs →
      (∀ s ∈ ss, -1 < s) →
      (∀ r ∈ rs, -1 < r) →
      ListInterlaces (ss.map untransformRoot) (rs.map untransformRoot)
  | [], [], _, _, _ => by simp_all
  | [], [_], _, _, _ => by simp [ListInterlaces]
  | s :: ss, r₁ :: r₂ :: rs, h, hss, hrs => by
      rcases h with ⟨hr₁s, hsr₂, htail⟩
      refine ⟨?_, ?_, ?_⟩
      · exact untransformRoot_mono_of_neg_one_lt hr₁s (hrs r₁ (by simp))
      · exact untransformRoot_mono_of_neg_one_lt hsr₂ (hss s (by simp))
      · exact listInterlaces_map_untransformRoot_of_neg_one_lt htail
          (fun s hs => hss s (by simp_all))
          (fun r hr => hrs r (by simp_all))
  | [], _ :: _ :: _, h, _, _ => by simp [ListInterlaces] at h
  | _ :: _, [], h, _, _ => by simp [ListInterlaces] at h
  | _ :: _ :: _, [_], h, _, _ => by simp [ListInterlaces] at h

lemma listAlternates_map_untransformRoot_of_neg_one_lt :
    ∀ {ss rs : List ℝ}, ListAlternates ss rs →
      (∀ s ∈ ss, -1 < s) →
      (∀ r ∈ rs, -1 < r) →
      ListAlternates (ss.map untransformRoot) (rs.map untransformRoot)
  | [], [], _, _, _ => by simp_all
  | s :: ss, r :: rs, h, hss, hrs => by
      rcases h with ⟨hsr, htail⟩
      exact ⟨untransformRoot_mono_of_neg_one_lt hsr (hss s (by simp)),
        listInterlaces_map_untransformRoot_of_neg_one_lt htail
          (fun t ht => hss t (by simp_all))
          (fun t ht => hrs t (by lia))⟩
  | [], _ :: _, h, _, _ => by simp [ListAlternates] at h
  | _ :: _, [], h, _, _ => by simp [ListAlternates] at h

lemma transformedLinearFactor_eq_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    C (1 - r) * X - C r = C (1 - r) * (X - C (r / (1 - r))) := by
  grind

lemma transformedLinearFactor_eq {r : ℝ} (h1r_ne : 1 - r ≠ 0) :
    C (1 - r) * X - C r = C (1 - r) * (X - C (r / (1 - r))) := by
  grind

lemma fPolynomial_X_sub_C_mul_succ' (d : ℕ) {r : ℝ} (hr : r ≤ 0) {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    fPolynomial (d + 1) ((X - C r) * p) =
      C (1 - r) * (X - C (r / (1 - r))) * fPolynomial d p := by
  rw [fPolynomial_X_sub_C_mul_succ d r hp, transformedLinearFactor_eq_of_nonpos hr]

lemma fPolynomial_X_sub_C_mul_succ_of_ne_one (d : ℕ) {r : ℝ} (hr1 : r ≠ 1) {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    fPolynomial (d + 1) ((X - C r) * p) =
      C (1 - r) * (X - C (r / (1 - r))) * fPolynomial d p := by
  have h1r_ne : 1 - r ≠ 0 := by
    grind
  rw [fPolynomial_X_sub_C_mul_succ d r hp, transformedLinearFactor_eq h1r_ne]

lemma fPolynomial_natDegree_factor_of_isRoot
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) {r : ℝ}
    (hr : p.IsRoot r) :
    ∃ q, p = (X - C r) * q ∧
      fPolynomial p.natDegree p =
        C (1 - r) * (X - C (r / (1 - r))) * fPolynomial q.natDegree q := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr
  have hq' : p = (X - C r) * q := by
    lia
  have hq_ne : q ≠ 0 := by
    simp_all
  have hr_mem : r ∈ p.roots := (mem_roots hp_ne).mpr hr
  have hr_nonpos : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hp_splits hpnn r hr_mem
  have hdeg_eq : p.natDegree = q.natDegree + 1 := by
    simpa [Nat.add_comm] using
      (show p.natDegree = 1 + q.natDegree by
        rw [hq', natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C])
  refine ⟨q, hq', ?_⟩
  rw [hdeg_eq, hq']
  simpa using fPolynomial_X_sub_C_mul_succ' q.natDegree hr_nonpos (p := q) le_rfl

lemma isRoot_transformedRoot_fPolynomial_natDegree_of_isRoot
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) {r : ℝ}
    (hr : p.IsRoot r) :
    (fPolynomial p.natDegree p).IsRoot (r / (1 - r)) := by
  rcases fPolynomial_natDegree_factor_of_isRoot hp_ne hp_splits hpnn hr with ⟨q, _, hfac⟩
  simp_all

lemma isRoot_transformedRoot_fPolynomial_of_isRoot
    {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d)
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) {r : ℝ}
    (hr : p.IsRoot r) :
    (fPolynomial d p).IsRoot (r / (1 - r)) := by
  have hroot_min :
      (fPolynomial p.natDegree p).IsRoot (r / (1 - r)) :=
    isRoot_transformedRoot_fPolynomial_natDegree_of_isRoot hp_ne hp_splits hpnn hr
  rw [Polynomial.IsRoot.def, fPolynomial_pad_by_X_add_one_pow (m := p.natDegree) le_rfl hd]
  simp_all

lemma isRoot_neg_one_fPolynomial_of_natDegree_lt
    {d : ℕ} {p : ℝ[X]} (hpd : p.natDegree < d) :
    (fPolynomial d p).IsRoot (-1) := by
  rw [Polynomial.IsRoot.def, eval_neg_one_fPolynomial]
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hpd]

lemma not_isRoot_neg_one_fPolynomial_of_natDegree_eq_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]} (hdeg : p.natDegree = d)
    (hp0 : p ≠ 0) :
    ¬ (fPolynomial d p).IsRoot (-1) := by
  rw [Polynomial.IsRoot.def, eval_neg_one_fPolynomial]
  have hcoeff_ne : p.coeff d ≠ 0 := by
    have hcoeff_eq : p.coeff d = p.leadingCoeff := by
      simpa [hdeg] using (coeff_natDegree (p := p))
    simp_all
  simp_all

private lemma isRealRooted_transformed_linear {r : ℝ} (hr : r ≤ 0) :
    ((C (1 - r) * X - C r) ≠ 0 ∧ (C (1 - r) * X - C r).Splits) := by
  have h1r_pos : 0 < 1 - r := by grind
  have h1r_ne : 1 - r ≠ 0 := ne_of_gt h1r_pos
  have hmul : (1 - r) * (r / (1 - r)) = r := by
    grind
  have hfac :
      C (1 - r) * X - C r =
        C (1 - r) * (X - C (r / (1 - r))) := by
    grind
  rw [hfac]
  exact isRealRooted_C_mul (isRealRooted_X_sub_C (r / (1 - r))).1
    (isRealRooted_X_sub_C (r / (1 - r))).2 h1r_ne

/-- The Brändén--Solus `f`-polynomial transform preserves real-rootedness on
nonnegative-coefficient inputs of degree at most `d`. -/
theorem isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ d)
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) :
    ((fPolynomial d p) ≠ 0 ∧ (fPolynomial d p).Splits) := by
  induction d generalizing p with
  | zero =>
      have hpC : p = C (p.coeff 0) := by
        simpa using (Polynomial.eq_C_of_natDegree_le_zero hpdeg)
      rw [hpC]
      have hfp : fPolynomial 0 (C (p.coeff 0)) = C (p.coeff 0) := by
        simp [fPolynomial]
      lia
  | succ d ih =>
      by_cases hpd : p.natDegree ≤ d
      · rw [fPolynomial_succ_of_natDegree_le hpd]
        have hX1 : ((X + 1 : ℝ[X]) ≠ 0 ∧ (X + 1 : ℝ[X]).Splits) := by
          simpa using (isRealRooted_X_sub_C (-1 : ℝ))
        simp_all
      · have hpdeg_eq : p.natDegree = d + 1 := by
          lia
        have hroots_pos : 0 < p.roots.card := by
          rw [card_roots_of_splits hp_splits, hpdeg_eq]
          lia
        obtain ⟨r, hr_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
        have hr_root : p.IsRoot r := (mem_roots hp_ne).mp hr_mem
        have hr_nonpos : r ≤ 0 :=
          roots_nonpos_of_nonneg_coeffs hp_splits hpnn r hr_mem
        obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr_root
        have hq' : p = (X - C r) * q := by
          lia
        have hq_dvd : q ∣ p := ⟨X - C r, by grind⟩
        have hq_ne : q ≠ 0 := by
          simp_all
        have hq_rr : (q ≠ 0 ∧ q.Splits) := isRealRooted_of_dvd hp_ne hp_splits hq_ne hq_dvd
        have hp_pos : HasPosLeadingCoeff p := hpnn.pos_leadingCoeff hp_ne
        have hq_pos : HasPosLeadingCoeff q := by
          apply hasPosLeadingCoeff_of_X_sub_C_mul (r := r)
          lia
        have hq_nonneg : HasNonnegCoeffs q :=
          hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
            hp_ne hp_splits hpnn hq_rr.1 hq_rr.2 hq_pos hq_dvd
        have hqdeg : q.natDegree ≤ d := by
          have hmuldeg : p.natDegree = 1 + q.natDegree := by
            rw [hq', natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
          lia
        rw [hq', fPolynomial_X_sub_C_mul_succ d r hqdeg]
        have hlin := isRealRooted_transformed_linear hr_nonpos
        have hih := ih hqdeg hq_rr.1 hq_rr.2 hq_nonneg
        exact isRealRooted_mul hlin.1 hlin.2 hih.1 hih.2

theorem roots_fPolynomial_natDegree_eq_map_of_isRealRooted_of_hasNonnegCoeffs
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) :
    (fPolynomial p.natDegree p).roots =
      p.roots.map (fun r : ℝ => r / (1 - r)) := by
  have hP :
      ∀ n (p : ℝ[X]), p.natDegree = n → (p ≠ 0 ∧ p.Splits) → HasNonnegCoeffs p →
        (fPolynomial p.natDegree p).roots =
          p.roots.map (fun r : ℝ => r / (1 - r)) := by
    intro n
    exact Nat.strong_induction_on n (fun n ih =>
      show ∀ (p : ℝ[X]), p.natDegree = n → (p ≠ 0 ∧
        p.Splits) → HasNonnegCoeffs p →
        (fPolynomial p.natDegree p).roots =
          p.roots.map (fun r : ℝ => r / (1 - r)) from by
        intro p hpdeg hp hpnn
        by_cases hn : n = 0
        · have hp0 : p.natDegree = 0 := by lia
          have hpC : p = C (p.coeff 0) := by
            simpa [hp0] using
              (Polynomial.eq_C_of_natDegree_le_zero (show p.natDegree ≤ 0 by lia))
          have hcoeff0_ne : p.coeff 0 ≠ 0 := by
            grind
          rw [hpC]
          simp [fPolynomial]
        · have hroots_pos : 0 < p.roots.card := by
            rw [card_roots_of_splits hp.2, hpdeg]
            lia
          obtain ⟨r, hr_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
          have hr_root : p.IsRoot r := (mem_roots hp.1).mp hr_mem
          obtain ⟨q, hq', hfac⟩ :=
            fPolynomial_natDegree_factor_of_isRoot hp.1 hp.2 hpnn hr_root
          have hq_dvd : q ∣ p := ⟨X - C r, by grind⟩
          have hq_ne : q ≠ 0 := by
            simp_all
          have hr_nonpos : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hp.2 hpnn r hr_mem
          have hq_rr : (q ≠ 0 ∧ q.Splits) := isRealRooted_of_dvd hp.1 hp.2 hq_ne hq_dvd
          have hp_pos : HasPosLeadingCoeff p := hpnn.pos_leadingCoeff hp.1
          have hq_pos : HasPosLeadingCoeff q := by
            apply hasPosLeadingCoeff_of_X_sub_C_mul (r := r)
            lia
          have hq_nonneg : HasNonnegCoeffs q :=
            hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
              hp.1 hp.2 hpnn hq_rr.1 hq_rr.2 hq_pos hq_dvd
          have hmuldeg : n = q.natDegree + 1 := by
            rw [← hpdeg, hq', natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
            lia
          have hqdeg_lt : q.natDegree < n := by
            lia
          have hqdeg_eq : q.natDegree = n - 1 := by lia
          have ihq :
              (fPolynomial q.natDegree q).roots =
                q.roots.map (fun s : ℝ => s / (1 - s)) :=
            ih q.natDegree hqdeg_lt q rfl hq_rr hq_nonneg
          have h1r_ne : 1 - r ≠ 0 := by grind
          have hqf_rr :
              ((fPolynomial q.natDegree q) ≠ 0 ∧ (fPolynomial q.natDegree q).Splits) :=
            isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs le_rfl hq_rr.1 hq_rr.2
              hq_nonneg
          have hroots_f :
              (fPolynomial p.natDegree p).roots =
                ({r / (1 - r)} : Multiset ℝ) + (fPolynomial q.natDegree q).roots := by
            rw [hfac, mul_assoc, roots_C_mul _ h1r_ne,
              roots_mul (mul_ne_zero (X_sub_C_ne_zero (r / (1 - r))) hqf_rr.1), roots_X_sub_C]
          have hp_roots : p.roots = ({r} : Multiset ℝ) + q.roots := by
            rw [hq', roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hq_ne), roots_X_sub_C]
          calc
            (fPolynomial p.natDegree p).roots
                = ({r / (1 - r)} : Multiset ℝ) + (fPolynomial q.natDegree q).roots := hroots_f
            _ = ({r / (1 - r)} : Multiset ℝ) + q.roots.map (fun s : ℝ => s / (1 - s)) := by
                  lia
            _ = ({r} : Multiset ℝ).map (fun s : ℝ => s / (1 - s)) +
                  q.roots.map (fun s : ℝ => s / (1 - s)) := by
                  simp
            _ = (({r} : Multiset ℝ) + q.roots).map (fun s : ℝ => s / (1 - s)) := by
                  simp
            _ = p.roots.map (fun s : ℝ => s / (1 - s)) := by
                  lia)
  simp_all

theorem roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d)
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) :
    (fPolynomial d p).roots =
      Multiset.replicate (d - p.natDegree) (-1) +
        p.roots.map (fun r : ℝ => r / (1 - r)) := by
  let n := p.natDegree
  have hpad : fPolynomial d p = (X + 1) ^ (d - n) * fPolynomial n p := by
    simpa [n] using fPolynomial_pad_by_X_add_one_pow (m := n) (p := p) le_rfl hd
  have hfp_rr : ((fPolynomial n p) ≠ 0 ∧ (fPolynomial n p).Splits) :=
    isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs le_rfl hp_ne hp_splits hpnn
  have hpow_ne : (X + 1 : ℝ[X]) ^ (d - n) ≠ 0 :=
    pow_ne_zero _ (by simpa [sub_eq_add_neg, add_comm] using (X_sub_C_ne_zero (-1 : ℝ)))
  have hroots_pow : ((X + 1 : ℝ[X]) ^ (d - n)).roots = Multiset.replicate (d - n) (-1) := by
    calc
      ((X + 1 : ℝ[X]) ^ (d - n)).roots = ((X - C (-1) : ℝ[X]) ^ (d - n)).roots := by
        simp
      _ = (d - n) • ({-1} : Multiset ℝ) := by
        rw [roots_pow, roots_X_sub_C]
      _ = Multiset.replicate (d - n) (-1) := by
        rw [Multiset.nsmul_singleton]
  rw [hpad, roots_mul (mul_ne_zero hpow_ne hfp_rr.1), hroots_pow,
    roots_fPolynomial_natDegree_eq_map_of_isRealRooted_of_hasNonnegCoeffs hp_ne hp_splits hpnn]

private theorem isRealRooted_of_fPolynomial_natDegree_roots_gt_neg_one
    {p : ℝ[X]}
    (hfpdeg : (fPolynomial p.natDegree p).natDegree = p.natDegree)
    (hfp_ne : (fPolynomial p.natDegree p) ≠ 0)
    (hfp_splits : (fPolynomial p.natDegree p).Splits)
    (hgt : ∀ x ∈ (fPolynomial p.natDegree p).roots, -1 < x) : (p ≠ 0 ∧ p.Splits) := by
  have hP :
      ∀ n : ℕ, ∀ p : ℝ[X],
        p.natDegree = n →
        (fPolynomial n p).natDegree = n →
        ((fPolynomial n p) ≠ 0 ∧ (fPolynomial n p).Splits) →
        (∀ x ∈ (fPolynomial n p).roots, -1 < x) →
        (p ≠ 0 ∧ p.Splits) := by
    intro n
    exact Nat.strong_induction_on n (fun n ih p hpdeg hqdeg hq_rr hq_gt => by
      have hp0 : p ≠ 0 := by
        intro hpz
        simp_all
      by_cases hn : n = 0
      · exact isRealRooted_of_deg_zero hp0 (by lia)
      · have hroots_pos : 0 < (fPolynomial n p).roots.card := by
          rw [card_roots_of_splits hq_rr.2, hqdeg]
          lia
        obtain ⟨x, hx_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
        have hx_root : (fPolynomial n p).IsRoot x := (mem_roots hq_rr.1).mp hx_mem
        have hx_gt : -1 < x := hq_gt x hx_mem
        have hx_ne : x ≠ -1 := by grind
        let r : ℝ := untransformRoot x
        have hr_root : p.IsRoot r := by
          rw [Polynomial.IsRoot.def] at hx_root ⊢
          rw [eval_fPolynomial_eq_mul_eval_untransform (d := n) (p := p)
            (by lia) hx_ne] at hx_root
          have hpow_ne : (1 + x) ^ n ≠ 0 :=
            pow_ne_zero _ (by grind)
          grind
        obtain ⟨u, hu_dvd⟩ := dvd_iff_isRoot.mpr hr_root
        have hpu : p = (X - C r) * u := by
          lia
        have hu0 : u ≠ 0 := by
          simp_all
        have hudeg_succ : p.natDegree = u.natDegree + 1 := by
          simpa [Nat.add_comm] using
            (show p.natDegree = 1 + u.natDegree by
              rw [hpu, natDegree_mul (X_sub_C_ne_zero r) hu0, natDegree_X_sub_C])
        have hu_lt : u.natDegree < n := by
          lia
        have h1r_ne : 1 - r ≠ 0 := by
          intro hzero
          have h1x_ne : 1 + x ≠ 0 := by grind
          dsimp [r, untransformRoot] at hzero
          grind
        have hq_fac0 :
            fPolynomial n p =
              (C (1 - r) * X - C r) * fPolynomial u.natDegree u := by
          have hdeg_eq : n = u.natDegree + 1 := by lia
          rw [hdeg_eq, hpu]
          simpa using fPolynomial_X_sub_C_mul_succ u.natDegree r (p := u) le_rfl
        have hq_fac :
            fPolynomial n p =
              (X - C x) * (C (1 - r) * fPolynomial u.natDegree u) := by
          calc
            fPolynomial n p
                = (C (1 - r) * X - C r) * fPolynomial u.natDegree u := hq_fac0
            _ = (C (1 - r) * (X - C (r / (1 - r)))) * fPolynomial u.natDegree u := by
                  grind
            _ = (C (1 - r) * (X - C x)) * fPolynomial u.natDegree u := by
                  rw [transformedRoot_untransformRoot (x := x) hx_gt]
            _ = (X - C x) * (C (1 - r) * fPolynomial u.natDegree u) := by
                  grind
        have hscaled_ne : C (1 - r) * fPolynomial u.natDegree u ≠ 0 := by
          simp_all
        have hscaled_rr : ((C (1 - r) * fPolynomial u.natDegree u) ≠ 0 ∧
          (C (1 - r) * fPolynomial u.natDegree u).Splits) := by
          apply isRealRooted_of_dvd hq_rr.1 hq_rr.2 hscaled_ne
          simp_all
        have hfu0 : fPolynomial u.natDegree u ≠ 0 := by
          simp_all
        have hfu_rr : ((fPolynomial u.natDegree u) ≠ 0 ∧ (fPolynomial u.natDegree u).Splits) := by
          apply isRealRooted_of_dvd hscaled_rr.1 hscaled_rr.2 hfu0
          simp
        have hfu_deg : (fPolynomial u.natDegree u).natDegree = u.natDegree := by
          have htmp : n = 1 + (C (1 - r) * fPolynomial u.natDegree u).natDegree := by
            rw [← hqdeg, hq_fac, natDegree_mul (X_sub_C_ne_zero x) hscaled_ne, natDegree_X_sub_C]
          rw [natDegree_C_mul h1r_ne] at htmp
          lia
        have hgt_u : ∀ y ∈ (fPolynomial u.natDegree u).roots, -1 < y := by
          simp_all
        have hu_rr : (u ≠ 0 ∧ u.Splits) :=
          ih u.natDegree hu_lt u rfl hfu_deg hfu_rr hgt_u
        simp_all)
  simp_all

lemma root_gt_neg_one_of_mem_roots_fPolynomial_natDegree_of_isRealRooted_of_hasNonnegCoeffs
    {p : ℝ[X]} (hfp_ne : (fPolynomial p.natDegree p) ≠ 0)
    (hpnn : HasNonnegCoeffs p)
    {x : ℝ} (hx : x ∈ (fPolynomial p.natDegree p).roots) :
    -1 < x := by
  have hp0 : p ≠ 0 := by
    intro hpz
    simp_all
  by_cases hxm1 : x = -1
  · subst hxm1
    exfalso
    exact not_isRoot_neg_one_fPolynomial_of_natDegree_eq_of_hasNonnegCoeffs rfl hp0
      ((mem_roots hfp_ne).mp hx)
  · by_cases hxlt : x < -1
    · exfalso
      have hx_root : (fPolynomial p.natDegree p).IsRoot x := (mem_roots hfp_ne).mp hx
      rw [Polynomial.IsRoot.def] at hx_root
      have hux_pos : 0 < untransformRoot x := by
        have h1x_neg : 1 + x < 0 := by grind
        have hx_neg : x < 0 := by grind
        have hdiv_pos : 0 < x / (1 + x) := div_pos_of_neg_of_neg hx_neg h1x_neg
        simpa [untransformRoot] using hdiv_pos
      have hpx_pos : 0 < p.eval (untransformRoot x) :=
        eval_pos_of_hasNonnegCoeffs_of_pos hpnn hp0 hux_pos
      rw [eval_fPolynomial_eq_mul_eval_untransform (d := p.natDegree) (p := p)
        le_rfl hxm1] at hx_root
      have hpow_ne : (1 + x) ^ p.natDegree ≠ 0 :=
        pow_ne_zero _ (by grind)
      simp_all
    · grind

theorem isRealRooted_of_isRealRooted_fPolynomial_natDegree_of_hasNonnegCoeffs
    {p : ℝ[X]} (hfp_ne : (fPolynomial p.natDegree p) ≠ 0)
    (hfp_splits : (fPolynomial p.natDegree p).Splits)
    (hpnn : HasNonnegCoeffs p) : (p ≠ 0 ∧ p.Splits) := by
  have hp0 : p ≠ 0 := by
    intro hpz
    simp_all
  have hfpdeg : (fPolynomial p.natDegree p).natDegree = p.natDegree :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero le_rfl hpnn hp0
  have hgt : ∀ x ∈ (fPolynomial p.natDegree p).roots, -1 < x := by
    intro x hx
    exact root_gt_neg_one_of_mem_roots_fPolynomial_natDegree_of_isRealRooted_of_hasNonnegCoeffs
      hfp_ne hpnn hx
  exact
    isRealRooted_of_fPolynomial_natDegree_roots_gt_neg_one hfpdeg hfp_ne hfp_splits hgt

theorem isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]} (hpd : p.natDegree ≤ d)
    (hfp_ne : (fPolynomial d p) ≠ 0) (hfp_splits : (fPolynomial d p).Splits)
    (hpnn : HasNonnegCoeffs p) : (p ≠ 0 ∧ p.Splits) := by
  have hmin0 : fPolynomial p.natDegree p ≠ 0 := by
    intro hzero
    apply hfp_ne
    rw [fPolynomial_pad_by_X_add_one_pow (m := p.natDegree) (p := p) le_rfl hpd, hzero, mul_zero]
  have hdiv : fPolynomial p.natDegree p ∣ fPolynomial d p := by
    refine ⟨(X + 1) ^ (d - p.natDegree), ?_⟩
    rw [fPolynomial_pad_by_X_add_one_pow (m := p.natDegree) (p := p) le_rfl hpd]
    grind
  have hmin_rr : ((fPolynomial p.natDegree p) ≠ 0 ∧ (fPolynomial p.natDegree p).Splits) :=
    isRealRooted_of_dvd hfp_ne hfp_splits hmin0 hdiv
  exact isRealRooted_of_isRealRooted_fPolynomial_natDegree_of_hasNonnegCoeffs
    hmin_rr.1 hmin_rr.2 hpnn

theorem prec_fPolynomial_of_prec_of_hasNonnegCoeffs_of_minimal
    {d : ℕ} {u v : ℝ[X]}
    (hd : d = max u.natDegree v.natDegree)
    (h : Prec u v)
    (hu_nonneg : HasNonnegCoeffs u)
    (hv_nonneg : HasNonnegCoeffs v) :
    Prec (fPolynomial d u) (fPolynomial d v) := by
  let φ := fun r : ℝ => r / (1 - r)
  rcases h with ⟨hu_rr, hv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud : u.natDegree ≤ d := by simp_all
  have hvd : v.natDegree ≤ d := by simp_all
  have hfu_rr : ((fPolynomial d u) ≠ 0 ∧ (fPolynomial d u).Splits) :=
    isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hud hu_rr.1 hu_rr.2 hu_nonneg
  have hfv_rr : ((fPolynomial d v) ≠ 0 ∧ (fPolynomial d v).Splits) :=
    isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hvd hv_rr.1 hv_rr.2 hv_nonneg
  have hss_nonpos : ∀ s ∈ ss, s ≤ 0 := by
    intro s hs
    have hs_mem : s ∈ u.roots := by
      simpa [hss_eq] using Multiset.mem_coe.mpr hs
    exact roots_nonpos_of_nonneg_coeffs hu_rr.2 hu_nonneg s hs_mem
  have hrs_nonpos : ∀ r ∈ rs, r ≤ 0 := by
    intro r hr
    have hr_mem : r ∈ v.roots := by
      simpa [hrs_eq] using Multiset.mem_coe.mpr hr
    exact roots_nonpos_of_nonneg_coeffs hv_rr.2 hv_nonneg r hr_mem
  have hss_map_sorted : (ss.map φ).Pairwise (· ≤ ·) :=
    pairwise_map_transformedRoot_of_nonpos hss_sorted hss_nonpos
  have hrs_map_sorted : (rs.map φ).Pairwise (· ≤ ·) :=
    pairwise_map_transformedRoot_of_nonpos hrs_sorted hrs_nonpos
  have hss_map_eq : (↑(ss.map φ) : Multiset ℝ) = u.roots.map φ := by
    simpa [φ] using congrArg (fun t : Multiset ℝ => t.map φ) hss_eq
  have hrs_map_eq : (↑(rs.map φ) : Multiset ℝ) = v.roots.map φ := by
    simpa [φ] using congrArg (fun t : Multiset ℝ => t.map φ) hrs_eq
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · cases rs with
    | nil =>
        simp at hlen
    | cons r₁ rest =>
        have hlen_deg_u : ss.length = u.natDegree := by
          rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hu_rr.2]
        have hlen_deg_v : (r₁ :: rest).length = v.natDegree := by
          rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hv_rr.2]
        have hud_pad : d - u.natDegree = 1 := by grind
        have hvd_pad : d - v.natDegree = 0 := by lia
        have hleft_all : ∀ t ∈ ss.map φ, -1 ≤ t := by
          intro t ht
          rcases List.mem_map.mp ht with ⟨s, hs, rfl⟩
          exact le_of_lt (neg_one_lt_transformedRoot (hss_nonpos s hs))
        have hleft_sorted : ((-1) :: ss.map φ).Pairwise (· ≤ ·) :=
          List.pairwise_cons.mpr ⟨hleft_all, hss_map_sorted⟩
        have hleft_eq : (↑((-1) :: ss.map φ) : Multiset ℝ) = (fPolynomial d u).roots := by
          have hleft_multiset :
              (↑((-1) :: ss.map φ) : Multiset ℝ) =
                Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := by
            calc
              (↑((-1) :: ss.map φ) : Multiset ℝ)
                  = ({-1} : Multiset ℝ) + (↑(ss.map φ) : Multiset ℝ) := by
                      simp
              _ = ({-1} : Multiset ℝ) + u.roots.map φ := by
                      lia
              _ = Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := by
                      simp_all
          calc
            (↑((-1) :: ss.map φ) : Multiset ℝ)
                = Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := hleft_multiset
            _ = (fPolynomial d u).roots := by
                    symm
                    simpa [φ] using
                      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
                        hud hu_rr.1 hu_rr.2 hu_nonneg
        have hright_eq : (↑((r₁ :: rest).map φ) : Multiset ℝ) = (fPolynomial d v).roots := by
          calc
            (↑((r₁ :: rest).map φ) : Multiset ℝ) = v.roots.map φ := by
                lia
            _ = (fPolynomial d v).roots := by
                symm
                simpa [φ, hvd_pad] using
                  roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
                    hvd hv_rr.1 hv_rr.2 hv_nonneg
        refine ⟨hfu_rr, hfv_rr, (-1) :: ss.map φ, (r₁ :: rest).map φ,
          hleft_sorted, hrs_map_sorted, hleft_eq, hright_eq, Or.inr ?_⟩
        refine ⟨by simp_all, ?_⟩
        simpa [φ] using
          listAlternates_neg_one_cons_map_of_listInterlaces_of_nonpos
            (ss := ss) (r₁ := r₁) (rs := rest) hint hrs_nonpos
  · have hlen_deg_u : ss.length = u.natDegree := by
      rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hu_rr.2]
    have hlen_deg_v : rs.length = v.natDegree := by
      rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hv_rr.2]
    have hud_pad : d - u.natDegree = 0 := by simp_all
    have hvd_pad : d - v.natDegree = 0 := by lia
    have hleft_eq : (↑(ss.map φ) : Multiset ℝ) = (fPolynomial d u).roots := by
      calc
        (↑(ss.map φ) : Multiset ℝ) = u.roots.map φ := by lia
        _ = (fPolynomial d u).roots := by
            symm
            simpa [φ, hud_pad] using
              roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
                hud hu_rr.1 hu_rr.2 hu_nonneg
    have hright_eq : (↑(rs.map φ) : Multiset ℝ) = (fPolynomial d v).roots := by
      calc
        (↑(rs.map φ) : Multiset ℝ) = v.roots.map φ := by lia
        _ = (fPolynomial d v).roots := by
            symm
            simpa [φ, hvd_pad] using
              roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
                hvd hv_rr.1 hv_rr.2 hv_nonneg
    refine ⟨hfu_rr, hfv_rr, ss.map φ, rs.map φ,
      hss_map_sorted, hrs_map_sorted, hleft_eq, hright_eq, Or.inr ?_⟩
    refine ⟨by simp_all, ?_⟩
    simpa [φ] using listAlternates_map_transformedRoot_of_nonpos halt hrs_nonpos

theorem prec_of_prec_fPolynomial_of_sameDegree_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {u v : ℝ[X]}
    (hud : u.natDegree = d) (hvd : v.natDegree = d)
    (hu_rr_ne : u ≠ 0) (hu_rr_splits : u.Splits)
    (hv_rr_ne : v ≠ 0) (hv_rr_splits : v.Splits)
    (h : Prec (fPolynomial d u) (fPolynomial d v))
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    Prec u v := by
  let φ := fun r : ℝ => r / (1 - r)
  rcases h with ⟨hfu_rr, hfv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud_le : u.natDegree ≤ d := by lia
  have hvd_le : v.natDegree ≤ d := by lia
  have hfu_deg : (fPolynomial d u).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hud_le hu_nonneg hu_rr_ne
  have hfv_deg : (fPolynomial d v).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hvd_le hv_nonneg hv_rr_ne
  have hss_len : ss.length = d := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hfu_rr.2, hfu_deg]
  have hrs_len : rs.length = d := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hfv_rr.2, hfv_deg]
  have hfu_roots :
      (fPolynomial d u).roots = u.roots.map φ := by
    simpa [φ, hud] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hud_le hu_rr_ne hu_rr_splits hu_nonneg
  have hfv_roots :
      (fPolynomial d v).roots = v.roots.map φ := by
    simpa [φ, hvd] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hvd_le hv_rr_ne hv_rr_splits hv_nonneg
  have hss_eq_map : (↑ss : Multiset ℝ) = u.roots.map φ := by
    lia
  have hrs_eq_map : (↑rs : Multiset ℝ) = v.roots.map φ := by
    lia
  have hss_gt_neg_one : ∀ s ∈ ss, -1 < s := by
    intro s hs
    have hs_mem : s ∈ (fPolynomial d u).roots := by
      simpa [hss_eq] using Multiset.mem_coe.mpr hs
    rw [hfu_roots] at hs_mem
    rcases Multiset.mem_map.mp hs_mem with ⟨r, hr, rfl⟩
    exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)
  have hrs_gt_neg_one : ∀ r ∈ rs, -1 < r := by
    intro r hr
    have hr_mem : r ∈ (fPolynomial d v).roots := by
      simpa [hrs_eq] using Multiset.mem_coe.mpr hr
    rw [hfv_roots] at hr_mem
    rcases Multiset.mem_map.mp hr_mem with ⟨s, hs, rfl⟩
    exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hv_rr_splits hv_nonneg s hs)
  have hss'_sorted : (ss.map untransformRoot).Pairwise (· ≤ ·) :=
    pairwise_map_untransformRoot_of_neg_one_lt hss_sorted hss_gt_neg_one
  have hrs'_sorted : (rs.map untransformRoot).Pairwise (· ≤ ·) :=
    pairwise_map_untransformRoot_of_neg_one_lt hrs_sorted hrs_gt_neg_one
  have hss'_eq : (↑(ss.map untransformRoot) : Multiset ℝ) = u.roots := by
    have hmap :
        (↑(ss.map untransformRoot) : Multiset ℝ) = (u.roots.map φ).map untransformRoot := by
      simpa [φ] using congrArg (fun t : Multiset ℝ => t.map untransformRoot) hss_eq_map
    calc
      (↑(ss.map untransformRoot) : Multiset ℝ)
          = (u.roots.map φ).map untransformRoot := hmap
      _ = u.roots.map (fun r : ℝ => untransformRoot (φ r)) := by
            simp
      _ = u.roots.map (fun r : ℝ => r) := by
            refine Multiset.map_congr rfl ?_
            intro r hr
            simp [φ, untransformRoot_transformedRoot
              (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)]
      _ = u.roots := by simp
  have hrs'_eq : (↑(rs.map untransformRoot) : Multiset ℝ) = v.roots := by
    have hmap :
        (↑(rs.map untransformRoot) : Multiset ℝ) = (v.roots.map φ).map untransformRoot := by
      simpa [φ] using congrArg (fun t : Multiset ℝ => t.map untransformRoot) hrs_eq_map
    calc
      (↑(rs.map untransformRoot) : Multiset ℝ)
          = (v.roots.map φ).map untransformRoot := hmap
      _ = v.roots.map (fun r : ℝ => untransformRoot (φ r)) := by
            simp
      _ = v.roots.map (fun r : ℝ => r) := by
            refine Multiset.map_congr rfl ?_
            intro r hr
            simp [φ, untransformRoot_transformedRoot
              (roots_nonpos_of_nonneg_coeffs hv_rr_splits hv_nonneg r hr)]
      _ = v.roots := by simp
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · lia
  · refine ⟨⟨hu_rr_ne, hu_rr_splits⟩, ⟨hv_rr_ne, hv_rr_splits⟩,
      ss.map untransformRoot, rs.map untransformRoot,
      hss'_sorted, hrs'_sorted, hss'_eq, hrs'_eq, Or.inr ?_⟩
    refine ⟨by simp_all, ?_⟩
    exact listAlternates_map_untransformRoot_of_neg_one_lt halt hss_gt_neg_one hrs_gt_neg_one

theorem prec_of_prec_fPolynomial_of_succDegree_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {u v : ℝ[X]}
    (hud : u.natDegree + 1 = d) (hvd : v.natDegree = d)
    (hu_rr_ne : u ≠ 0) (hu_rr_splits : u.Splits)
    (hv_rr_ne : v ≠ 0) (hv_rr_splits : v.Splits)
    (h : Prec (fPolynomial d u) (fPolynomial d v))
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    Prec u v := by
  let φ := fun r : ℝ => r / (1 - r)
  rcases h with ⟨hfu_rr, hfv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud_le : u.natDegree ≤ d := by lia
  have hvd_le : v.natDegree ≤ d := by lia
  have hud_pad : d - u.natDegree = 1 := by lia
  have hvd_pad : d - v.natDegree = 0 := by lia
  have hd_pos : 0 < d := by
    lia
  have hfu_deg : (fPolynomial d u).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hud_le hu_nonneg hu_rr_ne
  have hfv_deg : (fPolynomial d v).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hvd_le hv_nonneg hv_rr_ne
  have hss_len : ss.length = d := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hfu_rr.2, hfu_deg]
  have hrs_len : rs.length = d := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hfv_rr.2, hfv_deg]
  have hfu_roots :
      (fPolynomial d u).roots = ({-1} : Multiset ℝ) + u.roots.map φ := by
    simpa [φ, hud_pad] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hud_le hu_rr_ne hu_rr_splits hu_nonneg
  have hfv_roots :
      (fPolynomial d v).roots = v.roots.map φ := by
    simpa [φ, hvd_pad] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hvd_le hv_rr_ne hv_rr_splits hv_nonneg
  have hss_eq_full : (↑ss : Multiset ℝ) = ({-1} : Multiset ℝ) + u.roots.map φ := by
    lia
  have hrs_eq_map : (↑rs : Multiset ℝ) = v.roots.map φ := by
    lia
  cases ss with
  | nil =>
      simp_all
  | cons s ss' =>
      have hs_ge_neg_one : -1 ≤ s := by
        have hs_mem : s ∈ (↑(s :: ss') : Multiset ℝ) := by simp
        rw [hss_eq_full] at hs_mem
        rcases Multiset.mem_add.mp hs_mem with hs | hs
        · simp_all
        · rcases Multiset.mem_map.mp hs with ⟨r, hr, rfl⟩
          exact le_of_lt <|
            neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)
      have hs_eq : s = -1 := by
        have hminus_mem : (-1 : ℝ) ∈ s :: ss' := by
          have hminus_mem' : (-1 : ℝ) ∈ (↑(s :: ss') : Multiset ℝ) := by
            simp_all
          simpa using hminus_mem'
        rcases List.mem_cons.mp hminus_mem with hs | hs_tail
        · lia
        · have hs_le_neg_one : s ≤ -1 := List.rel_of_pairwise_cons hss_sorted hs_tail
          linarith
      have hss_tail_eq : (↑ss' : Multiset ℝ) = u.roots.map φ := by
        have hcons :
            ({-1} : Multiset ℝ) + (↑ss' : Multiset ℝ) =
              ({-1} : Multiset ℝ) + u.roots.map φ := by
          simp_all
        exact add_left_cancel hcons
      have hss_tail_sorted : ss'.Pairwise (· ≤ ·) := hss_sorted.tail
      have hss_tail_gt_neg_one : ∀ x ∈ ss', -1 < x := by
        intro x hx
        have hx_mem : x ∈ (↑ss' : Multiset ℝ) := by simpa using hx
        rw [hss_tail_eq] at hx_mem
        rcases Multiset.mem_map.mp hx_mem with ⟨r, hr, rfl⟩
        exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)
      have hrs_gt_neg_one : ∀ x ∈ rs, -1 < x := by
        intro x hx
        have hx_mem : x ∈ (↑rs : Multiset ℝ) := by simpa using hx
        rw [hrs_eq_map] at hx_mem
        rcases Multiset.mem_map.mp hx_mem with ⟨r, hr, rfl⟩
        exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hv_rr_splits hv_nonneg r hr)
      have hss'_sorted : (ss'.map untransformRoot).Pairwise (· ≤ ·) :=
        pairwise_map_untransformRoot_of_neg_one_lt hss_tail_sorted hss_tail_gt_neg_one
      have hrs'_sorted : (rs.map untransformRoot).Pairwise (· ≤ ·) :=
        pairwise_map_untransformRoot_of_neg_one_lt hrs_sorted hrs_gt_neg_one
      have hss'_eq : (↑(ss'.map untransformRoot) : Multiset ℝ) = u.roots := by
        have hmap :
            (↑(ss'.map untransformRoot) : Multiset ℝ) =
              (u.roots.map φ).map untransformRoot := by
          simpa [φ] using congrArg (fun t : Multiset ℝ => t.map untransformRoot) hss_tail_eq
        calc
          (↑(ss'.map untransformRoot) : Multiset ℝ)
              = (u.roots.map φ).map untransformRoot := hmap
          _ = u.roots.map (fun r : ℝ => untransformRoot (φ r)) := by
                simp
          _ = u.roots.map (fun r : ℝ => r) := by
                refine Multiset.map_congr rfl ?_
                intro r hr
                simp [φ, untransformRoot_transformedRoot
                  (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)]
          _ = u.roots := by simp
      have hrs'_eq : (↑(rs.map untransformRoot) : Multiset ℝ) = v.roots := by
        have hmap :
            (↑(rs.map untransformRoot) : Multiset ℝ) =
              (v.roots.map φ).map untransformRoot := by
          simpa [φ] using congrArg (fun t : Multiset ℝ => t.map untransformRoot) hrs_eq_map
        calc
          (↑(rs.map untransformRoot) : Multiset ℝ)
              = (v.roots.map φ).map untransformRoot := hmap
          _ = v.roots.map (fun r : ℝ => untransformRoot (φ r)) := by
                simp
          _ = v.roots.map (fun r : ℝ => r) := by
                refine Multiset.map_congr rfl ?_
                intro r hr
                simp [φ, untransformRoot_transformedRoot
                  (roots_nonpos_of_nonneg_coeffs hv_rr_splits hv_nonneg r hr)]
          _ = v.roots := by simp
      rcases hshape with ⟨hlen, _⟩ | ⟨hlen, halt⟩
      · lia
      · cases rs with
        | nil =>
            simp_all
        | cons r rs' =>
            have hint : ListInterlaces ss' (r :: rs') := by
              have hhalt : -1 ≤ r ∧ ListInterlaces ss' (r :: rs') := by
                simpa [hs_eq, ListAlternates] using halt
              lia
            refine ⟨⟨hu_rr_ne, hu_rr_splits⟩, ⟨hv_rr_ne, hv_rr_splits⟩,
              ss'.map untransformRoot, (r :: rs').map untransformRoot,
              hss'_sorted, hrs'_sorted, hss'_eq, hrs'_eq, Or.inl ?_⟩
            refine ⟨?_, ?_⟩
            · simp_all
            · exact listInterlaces_map_untransformRoot_of_neg_one_lt
                hint hss_tail_gt_neg_one hrs_gt_neg_one

private theorem not_prec_fPolynomial_of_right_degree_lt_of_sameDegree_left
    {d : ℕ} {u v : ℝ[X]}
    (hud : u.natDegree = d) (hvd : v.natDegree < d)
    (hu_rr_ne : u ≠ 0) (hu_rr_splits : u.Splits)
    (hv_rr_ne : v ≠ 0) (hv_rr_splits : v.Splits)
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    ¬ Prec (fPolynomial d u) (fPolynomial d v) := by
  let φ := fun r : ℝ => r / (1 - r)
  intro h
  rcases h with ⟨hfu_rr, hfv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud_le : u.natDegree ≤ d := by lia
  have hvd_le : v.natDegree ≤ d := le_of_lt hvd
  have hd_pos : 0 < d := by lia
  have hfu_deg : (fPolynomial d u).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hud_le hu_nonneg hu_rr_ne
  have hfv_deg : (fPolynomial d v).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hvd_le hv_nonneg hv_rr_ne
  have hss_len : ss.length = d := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hfu_rr.2, hfu_deg]
  have hrs_len : rs.length = d := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hfv_rr.2, hfv_deg]
  have hud_pad : d - u.natDegree = 0 := by lia
  have hfu_roots :
      (fPolynomial d u).roots = u.roots.map φ := by
    simpa [φ, hud_pad] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hud_le hu_rr_ne hu_rr_splits hu_nonneg
  have hss_gt_neg_one : ∀ x ∈ ss, -1 < x := by
    intro x hx
    have hx_mem : x ∈ (fPolynomial d u).roots := by
      simpa [hss_eq] using Multiset.mem_coe.mpr hx
    rw [hfu_roots] at hx_mem
    rcases Multiset.mem_map.mp hx_mem with ⟨r, hr, rfl⟩
    exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)
  have hminus_mem : (-1 : ℝ) ∈ rs := by
    have hminus_mem' : (-1 : ℝ) ∈ (fPolynomial d v).roots :=
      (mem_roots hfv_rr.1).2 (isRoot_neg_one_fPolynomial_of_natDegree_lt hvd)
    rw [← hrs_eq] at hminus_mem'
    simpa using hminus_mem'
  cases rs with
  | nil =>
      simp_all
  | cons r rs' =>
      have hfv_roots :
          (fPolynomial d v).roots =
            Multiset.replicate (d - v.natDegree) (-1) + v.roots.map φ := by
        simpa [φ] using
          roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
            hvd_le hv_rr_ne hv_rr_splits hv_nonneg
      have hr_ge_neg_one : -1 ≤ r := by
        have hr_mem : r ∈ (fPolynomial d v).roots := by
          simpa [hrs_eq] using Multiset.mem_coe.mpr (by simp : r ∈ r :: rs')
        rw [hfv_roots] at hr_mem
        rcases Multiset.mem_add.mp hr_mem with hr | hr
        · have hr' : r = -1 := (Multiset.mem_replicate.mp hr).2
          simp_all
        · rcases Multiset.mem_map.mp hr with ⟨s, hs, rfl⟩
          exact le_of_lt <|
            neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hv_rr_splits hv_nonneg s hs)
      have hr_eq : r = -1 := by
        rcases List.mem_cons.mp hminus_mem with hr | hr_tail
        · lia
        · have hr_le_neg_one : r ≤ -1 := List.rel_of_pairwise_cons hrs_sorted hr_tail
          linarith
      cases ss with
      | nil =>
          simp_all
      | cons s ss' =>
          rcases hshape with ⟨hlen, _⟩ | ⟨hlen, halt⟩
          · lia
          · have hs_le_r : s ≤ r := by
              have hhalt : s ≤ r ∧ ListInterlaces ss' (r :: rs') := by
                simpa [ListAlternates] using halt
              lia
            have hs_gt_neg_one : -1 < s := hss_gt_neg_one s (by simp)
            linarith

private theorem not_prec_fPolynomial_of_left_degree_le_sub_two_of_right_full
    {d : ℕ} {u v : ℝ[X]}
    (hud : u.natDegree + 2 ≤ d) (hvd : v.natDegree = d)
    (hu_rr_ne : u ≠ 0) (hu_rr_splits : u.Splits)
    (hv_rr_ne : v ≠ 0) (hv_rr_splits : v.Splits)
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    ¬ Prec (fPolynomial d u) (fPolynomial d v) := by
  let φ := fun r : ℝ => r / (1 - r)
  intro h
  rcases h with ⟨hfu_rr, hfv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud_le : u.natDegree ≤ d := by lia
  have hvd_le : v.natDegree ≤ d := by lia
  have hd_pos : 0 < d := by lia
  have hfu_deg : (fPolynomial d u).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hud_le hu_nonneg hu_rr_ne
  have hfv_deg : (fPolynomial d v).natDegree = d :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hvd_le hv_nonneg hv_rr_ne
  have hss_len : ss.length = d := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hfu_rr.2, hfu_deg]
  have hrs_len : rs.length = d := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hfv_rr.2, hfv_deg]
  have hud_pad_two : 2 ≤ d - u.natDegree := by lia
  have hfu_roots :
      (fPolynomial d u).roots =
        Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := by
    simpa [φ] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hud_le hu_rr_ne hu_rr_splits hu_nonneg
  have hss_ge_neg_one : ∀ x ∈ ss, -1 ≤ x := by
    intro x hx
    have hx_mem : x ∈ (fPolynomial d u).roots := by
      simpa [hss_eq] using Multiset.mem_coe.mpr hx
    rw [hfu_roots] at hx_mem
    rcases Multiset.mem_add.mp hx_mem with hx | hx
    · have hx' : x = -1 := (Multiset.mem_replicate.mp hx).2
      simp_all
    · rcases Multiset.mem_map.mp hx with ⟨r, hr, rfl⟩
      exact le_of_lt <|
        neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr_splits hu_nonneg r hr)
  have hminus_mem : (-1 : ℝ) ∈ ss := by
    have hminus_mem' : (-1 : ℝ) ∈ (fPolynomial d u).roots := by
      rw [hfu_roots]
      exact Multiset.mem_add.mpr <| Or.inl <|
        Multiset.mem_replicate.mpr ⟨by lia, rfl⟩
    rw [← hss_eq] at hminus_mem'
    simpa using hminus_mem'
  cases ss with
  | nil =>
      simp_all
  | cons s ss' =>
      have hss_eq_full :
          (↑(s :: ss') : Multiset ℝ) =
            Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := by
        lia
      have hs_eq : s = -1 := by
        have hs_ge_neg_one : -1 ≤ s := hss_ge_neg_one s (by simp)
        rcases List.mem_cons.mp hminus_mem with hs | hs_tail
        · lia
        · have hs_le_neg_one : s ≤ -1 := List.rel_of_pairwise_cons hss_sorted hs_tail
          linarith
      have hkpos : 0 < d - u.natDegree := by lia
      have hrep :
          Multiset.replicate (d - u.natDegree) (-1) =
            ({-1} : Multiset ℝ) + Multiset.replicate (d - u.natDegree - 1) (-1) := by
        rw [show d - u.natDegree = 1 + (d - u.natDegree - 1) by lia, Multiset.replicate_add]
        simp
      have hss_tail_eq :
          (↑ss' : Multiset ℝ) =
            Multiset.replicate (d - u.natDegree - 1) (-1) + u.roots.map φ := by
        have hcons :
            ({-1} : Multiset ℝ) + (↑ss' : Multiset ℝ) =
              ({-1} : Multiset ℝ) +
                (Multiset.replicate (d - u.natDegree - 1) (-1) + u.roots.map φ) := by
          simp_all
        exact add_left_cancel hcons
      have hminus_mem_tail : (-1 : ℝ) ∈ ss' := by
        have hminus_mem_tail' : (-1 : ℝ) ∈ (↑ss' : Multiset ℝ) := by
          rw [hss_tail_eq]
          exact Multiset.mem_add.mpr <| Or.inl <|
            Multiset.mem_replicate.mpr ⟨by lia, rfl⟩
        simpa using hminus_mem_tail'
      have hfv_roots :
          (fPolynomial d v).roots = v.roots.map φ := by
        have hvd_pad : d - v.natDegree = 0 := by lia
        simpa [φ, hvd_pad] using
          roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
            hvd_le hv_rr_ne hv_rr_splits hv_nonneg
      have hrs_gt_neg_one : ∀ x ∈ rs, -1 < x := by
        intro x hx
        have hx_mem : x ∈ (fPolynomial d v).roots := by
          simpa [hrs_eq] using Multiset.mem_coe.mpr hx
        rw [hfv_roots] at hx_mem
        rcases Multiset.mem_map.mp hx_mem with ⟨r, hr, rfl⟩
        exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hv_rr_splits hv_nonneg r hr)
      cases rs with
      | nil =>
          simp_all
      | cons r rs' =>
          rcases hshape with ⟨hlen, _⟩ | ⟨hlen, halt⟩
          · lia
          · have hhalt : -1 ≤ r ∧ ListInterlaces ss' (r :: rs') := by
              simpa [hs_eq, ListAlternates] using halt
            have hr_gt_neg_one : -1 < r := hrs_gt_neg_one r (by simp)
            have hr_le_neg_one : r ≤ -1 :=
              listInterlaces_all_ge ss' rs' r hhalt.2 (-1) hminus_mem_tail
            linarith

theorem prec_of_prec_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {u v : ℝ[X]}
    (hd : d = max u.natDegree v.natDegree)
    (hu_rr_ne : u ≠ 0) (hu_rr_splits : u.Splits)
    (hv_rr_ne : v ≠ 0) (hv_rr_splits : v.Splits)
    (h : Prec (fPolynomial d u) (fPolynomial d v))
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    Prec u v := by
  have hud : u.natDegree ≤ d := by simp_all
  have hvd : v.natDegree ≤ d := by simp_all
  by_cases hv_eq : v.natDegree = d
  · by_cases hu_eq : u.natDegree = d
    · exact prec_of_prec_fPolynomial_of_sameDegree_of_isRealRooted_of_hasNonnegCoeffs
        hu_eq hv_eq hu_rr_ne hu_rr_splits hv_rr_ne hv_rr_splits h hu_nonneg hv_nonneg
    · have hu_lt : u.natDegree < d := lt_of_le_of_ne hud hu_eq
      by_cases hu_succ : u.natDegree + 1 = d
      · exact prec_of_prec_fPolynomial_of_succDegree_of_isRealRooted_of_hasNonnegCoeffs
          hu_succ hv_eq hu_rr_ne hu_rr_splits hv_rr_ne hv_rr_splits h hu_nonneg hv_nonneg
      · have hu_two : u.natDegree + 2 ≤ d := by lia
        exact False.elim <|
          not_prec_fPolynomial_of_left_degree_le_sub_two_of_right_full
            hu_two hv_eq hu_rr_ne hu_rr_splits hv_rr_ne hv_rr_splits hu_nonneg hv_nonneg h
  · have hv_lt : v.natDegree < d := lt_of_le_of_ne hvd hv_eq
    have hu_eq : u.natDegree = d := by grind
    exact False.elim <|
      not_prec_fPolynomial_of_right_degree_lt_of_sameDegree_left
        hu_eq hv_lt hu_rr_ne hu_rr_splits hv_rr_ne hv_rr_splits hu_nonneg hv_nonneg h

theorem prec_iff_prec_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {u v : ℝ[X]}
    (hd : d = max u.natDegree v.natDegree)
    (hu_rr_ne : u ≠ 0) (hu_rr_splits : u.Splits)
    (hv_rr_ne : v ≠ 0) (hv_rr_splits : v.Splits)
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    (Prec (fPolynomial d u) (fPolynomial d v) ↔ Prec u v) := by
  constructor
  · intro h
    exact prec_of_prec_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs
      hd hu_rr_ne hu_rr_splits hv_rr_ne hv_rr_splits h hu_nonneg hv_nonneg
  · intro h
    exact prec_fPolynomial_of_prec_of_hasNonnegCoeffs_of_minimal
      hd h hu_nonneg hv_nonneg

/-- If `u ≺ v` and both have nonnegative coefficients, then their
Brändén--Solus `f`-polynomials form a positive-combination real-rooted pair. -/
theorem posComboRealRooted_fPolynomial_of_prec
    {d : ℕ} {u v : ℝ[X]} (h : Prec u v)
    (hud : u.natDegree ≤ d) (hvd : v.natDegree ≤ d)
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    PosComboRealRooted (fPolynomial d u) (fPolynomial d v) := by
  have hu_pos : HasPosLeadingCoeff u := hu_nonneg.pos_leadingCoeff h.1.1
  have hv_pos : HasPosLeadingCoeff v := hv_nonneg.pos_leadingCoeff h.2.1.1
  intro lam μ hlam hμ
  have hcombo_rr : ((C lam * u + C μ * v) ≠ 0 ∧ (C lam * u + C μ * v).Splits) :=
    PosComboRealRooted.of_prec h hu_pos hv_pos hlam hμ
  have hcombo_nonneg : HasNonnegCoeffs (C lam * u + C μ * v) :=
    (nonnegCoeffs_C_mul hlam.le hu_nonneg).add (nonnegCoeffs_C_mul hμ.le hv_nonneg)
  have hcombo_deg : (C lam * u + C μ * v).natDegree ≤ d := by
    have hud' : (C lam * u).natDegree ≤ d := by
      rw [Polynomial.natDegree_C_mul hlam.ne']
      lia
    have hvd' : (C μ * v).natDegree ≤ d := by
      rw [Polynomial.natDegree_C_mul hμ.ne']
      lia
    simpa using Polynomial.natDegree_add_le_of_le hud' hvd'
  simpa [fPolynomial_add, fPolynomial_C_mul] using
    isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs
      hcombo_deg hcombo_rr.1 hcombo_rr.2 hcombo_nonneg

lemma eval_one_IdTransform {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (IdTransform d p).eval 1 = p.eval 1 := by
  letI : Invertible (1 : ℝ) := invertibleOne
  simpa [IdTransform, one_pow] using
    (Polynomial.eval₂_reflect_mul_pow (i := RingHom.id ℝ) (x := (1 : ℝ)) d p hd)

lemma X_sub_one_dvd_sub_IdTransform {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    X - 1 ∣ p - IdTransform d p := by
  rw [show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp]
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
  simp [eval_one_IdTransform hd]

lemma X_sub_one_dvd_X_mul_IdTransform_sub {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    X - 1 ∣ X * IdTransform d p - p := by
  rw [show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp]
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
  simp [eval_one_IdTransform hd]

lemma idDecompositionBFormula_mul_X_sub_one {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (X - 1) * idDecompositionBFormula d p = p - IdTransform d p := by
  have hdvd : (p - IdTransform d p) %ₘ (X - 1) = 0 := by
    rw [show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp]
    rw [Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_sub_C (1 : ℝ))]
    exact X_sub_one_dvd_sub_IdTransform hd
  have h := Polynomial.modByMonic_add_div (p - IdTransform d p) (X - 1)
  rw [hdvd, zero_add] at h
  simpa [idDecompositionBFormula] using h

lemma idDecompositionAFormula_mul_X_sub_one {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (X - 1) * idDecompositionAFormula d p = X * IdTransform d p - p := by
  have hdvd : (X * IdTransform d p - p) %ₘ (X - 1) = 0 := by
    rw [show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp]
    rw [Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_sub_C (1 : ℝ))]
    exact X_sub_one_dvd_X_mul_IdTransform_sub hd
  have h := Polynomial.modByMonic_add_div (X * IdTransform d p - p) (X - 1)
  rw [hdvd, zero_add] at h
  simpa [idDecompositionAFormula] using h

lemma IdTransform_natDegree_le {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (IdTransform d p).natDegree ≤ d :=
  (Polynomial.natDegree_reflect_le (N := d) (p := p)).trans <| max_le le_rfl hd

lemma IdTransform_succ {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    IdTransform (d + 1) p = X * IdTransform d p := by
  simpa [IdTransform, mul_comm, mul_left_comm, mul_assoc] using
    (Polynomial.reflect_mul (f := p) (g := (1 : ℝ[X])) (F := d) (G := 1) hd
      (show (1 : ℝ[X]).natDegree ≤ 1 by simp))

lemma IdTransform_X_mul_succ {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    IdTransform (d + 1) (X * p) = IdTransform d p := by
  simpa [IdTransform, add_comm] using
    (Polynomial.reflect_mul (f := (X : ℝ[X])) (g := p) (F := 1) (G := d)
      Polynomial.natDegree_X_le hd)

lemma IdTransform_of_natDegree_le_pred {d : ℕ} (hd : 0 < d) {p : ℝ[X]}
    (hp : p.natDegree ≤ d - 1) :
    IdTransform d p = X * IdTransform (d - 1) p := by
  cases d with
  | zero =>
      lia
  | succ n =>
      simpa using (IdTransform_succ (d := n) (p := p) hp)

lemma IdTransform_X_mul_of_natDegree_le_pred {d : ℕ} (hd : 0 < d) {p : ℝ[X]}
    (hp : p.natDegree ≤ d - 1) :
    IdTransform d (X * p) = IdTransform (d - 1) p := by
  cases d with
  | zero =>
      lia
  | succ n =>
      simpa using (IdTransform_X_mul_succ (d := n) (p := p) hp)

lemma IdTransform_X_sub_one :
    IdTransform 1 (X - 1 : ℝ[X]) = -(X - 1) := by
  simp [IdTransform, sub_eq_add_neg, add_comm]

lemma coeff_zero_eq_zero_of_IdTransform_fixed_of_natDegree_lt {d : ℕ} {p : ℝ[X]}
    (hfix : IdTransform d p = p) (hdeg : p.natDegree < d) :
    p.coeff 0 = 0 := by
  have hcoeff : p.coeff 0 = p.coeff d := by
    simpa [IdTransform, Polynomial.coeff_reflect, Polynomial.revAt_zero] using
      (congrArg (fun q => q.coeff 0) hfix).symm
  exact hcoeff.trans (Polynomial.coeff_eq_zero_of_natDegree_lt hdeg)

lemma isRoot_zero_of_IdTransform_fixed_of_natDegree_lt {d : ℕ} {p : ℝ[X]}
    (hfix : IdTransform d p = p) (hdeg : p.natDegree < d) :
    p.IsRoot 0 := by
  rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero]
  exact coeff_zero_eq_zero_of_IdTransform_fixed_of_natDegree_lt hfix hdeg

lemma exists_eq_X_mul_of_IdTransform_fixed_of_natDegree_lt {d : ℕ} {p : ℝ[X]}
    (hfix : IdTransform d p = p) (hdeg : p.natDegree < d) :
    ∃ q, p = X * q ∧ IdTransform (d - 2) q = q := by
  cases d with
  | zero =>
      lia
  | succ d =>
      cases d with
      | zero =>
          have hpdeg : p.natDegree ≤ 0 := by lia
          have hp0 : p = 0 := by
            calc
              p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hpdeg
              _ = 0 := by
                    simp [coeff_zero_eq_zero_of_IdTransform_fixed_of_natDegree_lt hfix hdeg]
          simp_all
      | succ n =>
          have hroot0 : p.IsRoot 0 :=
            isRoot_zero_of_IdTransform_fixed_of_natDegree_lt hfix hdeg
          obtain ⟨q, hq0⟩ := dvd_iff_isRoot.mpr hroot0
          have hq : p = X * q := by
            simp_all
          have hqdeg : q.natDegree ≤ n := by
            by_cases hqz : q = 0
            · simp [hqz]
            · simp_all
          have hqdeg' : q.natDegree ≤ n + 1 := le_trans hqdeg (Nat.le_succ _)
          have hstep1 : IdTransform (n + 2) (X * q) = IdTransform (n + 1) q := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (IdTransform_X_mul_succ (d := n + 1) (p := q) hqdeg')
          have hstep2 : IdTransform (n + 1) q = X * IdTransform n q := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (IdTransform_of_natDegree_le_pred (d := n + 1) (Nat.succ_pos _) hqdeg)
          simp_all

theorem isIdDecomposition_descend_of_lt_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : 2 ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_lt : a.natDegree < d)
    (hb_lt : b.natDegree < d - 1) :
    ∃ a' b', a = X * a' ∧ b = X * b' ∧
      p = X * (a' + X * b') ∧
      IsIdDecomposition (d - 2) (a' + X * b') a' b' := by
  rcases hid with ⟨hp_eq, ha_deg, hb_deg, hfixA, hfixB⟩
  obtain ⟨a', haX, hfixA'⟩ :=
    exists_eq_X_mul_of_IdTransform_fixed_of_natDegree_lt hfixA ha_lt
  obtain ⟨b', hbX, hfixB'⟩ :=
    exists_eq_X_mul_of_IdTransform_fixed_of_natDegree_lt hfixB hb_lt
  have ha'deg : a'.natDegree ≤ d - 2 := by
    by_cases ha'0 : a' = 0
    · simp [ha'0]
    · rw [haX, natDegree_X_mul ha'0] at ha_lt
      lia
  have hb'deg : b'.natDegree ≤ d - 3 := by
    by_cases hb'0 : b' = 0
    · simp [hb'0]
    · rw [hbX, natDegree_X_mul hb'0] at hb_lt
      lia
  have hpX : p = X * (a' + X * b') := by
    grind
  have hsub : (d - 2) - 1 = d - 3 := by
    lia
  refine ⟨a', b', haX, hbX, hpX, ?_⟩
  refine ⟨rfl, ha'deg, ?_, hfixA', ?_⟩
  · lia
  · lia

lemma IdTransform_X_mul_of_natDegree_le_two_pred {d : ℕ} {p : ℝ[X]}
    (hd : 2 ≤ d) (hp : p.natDegree ≤ d - 2) :
    IdTransform d (X * p) = X * IdTransform (d - 2) p := by
  calc
    IdTransform d (X * p) = IdTransform (d - 1) p :=
      IdTransform_X_mul_of_natDegree_le_pred (by lia) (by lia)
    _ = X * IdTransform (d - 2) p :=
      IdTransform_of_natDegree_le_pred (d := d - 1) (by lia) (by lia)

theorem prec_iff_prec_mul_X_both_of_hasNonnegCoeffs {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec f g ↔ Prec (X * f) (X * g) := by
  constructor
  · intro h
    have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs h.1.2 hfnn
    have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs h.2.1.2 hgnn
    exact (prec_iff_prec_mul_X_both_of_roots_nonpos hf_nonpos hg_nonpos).1 h
  · intro h
    have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_X_mul h.1.1 h.1.2
    have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_X_mul h.2.1.1 h.2.1.2
    have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf_rr.2 hfnn
    have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hg_rr.2 hgnn
    exact (prec_iff_prec_mul_X_both_of_roots_nonpos hf_nonpos hg_nonpos).2 h

lemma hasNonnegCoeffs_of_eq_X_mul {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (h : p = X * q) :
    HasNonnegCoeffs q := by
  intro n
  simpa [h, Polynomial.coeff_X_mul] using hp (n + 1)

lemma natDegree_idDecompositionBFormula_le {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (idDecompositionBFormula d p).natDegree ≤ d - 1 := by
  have hnum : (p - IdTransform d p).natDegree ≤ d := by
    simpa using Polynomial.natDegree_sub_le_of_le hd (IdTransform_natDegree_le hd)
  rw [idDecompositionBFormula, show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp]
  rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C (1 : ℝ))]
  rw [Polynomial.natDegree_X_sub_C]
  lia

lemma natDegree_idDecompositionAFormula_le {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (idDecompositionAFormula d p).natDegree ≤ d := by
  have hI : (IdTransform d p).natDegree ≤ d := IdTransform_natDegree_le hd
  have hXI : (X * IdTransform d p).natDegree ≤ d + 1 := by
    simpa [add_comm] using
      (Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_X_le hI)
  have hp' : p.natDegree ≤ d + 1 := le_trans hd (Nat.le_succ d)
  have hnum : (X * IdTransform d p - p).natDegree ≤ d + 1 := by
    simpa using Polynomial.natDegree_sub_le_of_le hXI hp'
  rw [idDecompositionAFormula, show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp]
  rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C (1 : ℝ))]
  rw [Polynomial.natDegree_X_sub_C]
  lia

theorem idDecompositionFormula_eq_add_X_mul {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    p = idDecompositionAFormula d p + X * idDecompositionBFormula d p := by
  have hA := idDecompositionAFormula_mul_X_sub_one hd
  have hB := idDecompositionBFormula_mul_X_sub_one hd
  have hstep :
    (X - 1) * (idDecompositionAFormula d p + X * idDecompositionBFormula d p)
        = (X - 1) * idDecompositionAFormula d p + X * ((X - 1) * idDecompositionBFormula d p) := by
            ring
  have hmul :
      (X - 1) * (idDecompositionAFormula d p + X * idDecompositionBFormula d p) = (X - 1) * p := by
    grind
  have hdiv := congrArg (fun q => q /ₘ (X - 1)) hmul
  rw [show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp] at hdiv
  have hleft_cancel :
      ((X - C (1 : ℝ)) * (idDecompositionAFormula d p + X * idDecompositionBFormula d p)) /ₘ
          (X - C (1 : ℝ)) =
        idDecompositionAFormula d p + X * idDecompositionBFormula d p := by
    simpa using
      (Polynomial.mul_divByMonic_cancel_left
        (idDecompositionAFormula d p + X * idDecompositionBFormula d p)
        (Polynomial.monic_X_sub_C (1 : ℝ)))
  have hright_cancel :
      ((X - C (1 : ℝ)) * p) /ₘ (X - C (1 : ℝ)) = p := by
    simpa using
      (Polynomial.mul_divByMonic_cancel_left p (Polynomial.monic_X_sub_C (1 : ℝ)))
  lia

theorem idDecompositionFormula_IdTransform_eq_add {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    IdTransform d p = idDecompositionAFormula d p + idDecompositionBFormula d p := by
  have hB := idDecompositionBFormula_mul_X_sub_one hd
  calc
    IdTransform d p = p - (p - IdTransform d p) := by simp
    _ = p - (X - 1) * idDecompositionBFormula d p := by lia
    _ =
        (idDecompositionAFormula d p + X * idDecompositionBFormula d p) -
          (X - 1) * idDecompositionBFormula d p := by
            nth_rw 1 [idDecompositionFormula_eq_add_X_mul hd]
    _ = idDecompositionAFormula d p + idDecompositionBFormula d p := by grind

theorem idDecompositionFormula_eq_of_system {d : ℕ} {p a b : ℝ[X]} (hd : p.natDegree ≤ d)
    (hp : p = a + X * b) (hI : IdTransform d p = a + b) :
    a = idDecompositionAFormula d p ∧ b = idDecompositionBFormula d p := by
  have hsub : p - IdTransform d p = (X - 1) * b := by
    grind
  have hdiv := congrArg (fun q => q /ₘ (X - 1)) hsub
  rw [show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp] at hdiv
  have hb' : idDecompositionBFormula d p = b := by
    have hcancel : ((X - C (1 : ℝ)) * b) /ₘ (X - C (1 : ℝ)) = b := by
      simpa using
        (Polynomial.mul_divByMonic_cancel_left b (Polynomial.monic_X_sub_C (1 : ℝ)))
    calc
      idDecompositionBFormula d p = (p - IdTransform d p) /ₘ (X - C (1 : ℝ)) := by
        simp [idDecompositionBFormula]
      _ = ((X - C (1 : ℝ)) * b) /ₘ (X - C (1 : ℝ)) := hdiv
      _ = b := hcancel
  have hb : b = idDecompositionBFormula d p := hb'.symm
  refine ⟨?_, hb⟩
  calc
    a = p - X * b := by grind
    _ = p - X * idDecompositionBFormula d p := by lia
    _ = idDecompositionAFormula d p := by
      nth_rw 1 [idDecompositionFormula_eq_add_X_mul hd]
      ring

lemma idDecompositionBFormula_fixed {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    IdTransform (d - 1) (idDecompositionBFormula d p) = idDecompositionBFormula d p := by
  cases d with
  | zero =>
      have hp0 : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hd
      have hI0 : IdTransform 0 p = p := by
        rw [hp0, IdTransform, Polynomial.reflect_C]
        lia
      rw [idDecompositionBFormula, hI0, sub_self, zero_divByMonic]
      simp
  | succ n =>
      let a := idDecompositionAFormula (n + 1) p
      let b := idDecompositionBFormula (n + 1) p
      have ha : p = a + X * b := by
        simpa [a, b] using idDecompositionFormula_eq_add_X_mul (d := n + 1) hd
      have hI : IdTransform (n + 1) p = a + b := by
        simpa [a, b] using idDecompositionFormula_IdTransform_eq_add (d := n + 1) hd
      have hbdeg : b.natDegree ≤ n := by
        simpa [b] using natDegree_idDecompositionBFormula_le (d := n + 1) hd
      have ha' : p = IdTransform (n + 1) a + X * IdTransform n b := by
        have h0 : p = IdTransform (n + 1) a + IdTransform (n + 1) b := by
          simpa [IdTransform, Polynomial.reflect_add, a, b] using
            (congrArg (IdTransform (n + 1)) hI)
        rw [IdTransform_of_natDegree_le_pred (d := n + 1) (Nat.succ_pos _) hbdeg] at h0
        lia
      have hI' : IdTransform (n + 1) p = IdTransform (n + 1) a + IdTransform n b := by
        have h0 : IdTransform (n + 1) p = IdTransform (n + 1) a + IdTransform (n + 1) (X * b) := by
          simp_all
        rw [IdTransform_X_mul_of_natDegree_le_pred (d := n + 1) (Nat.succ_pos _) hbdeg] at h0
        lia
      have hsys := idDecompositionFormula_eq_of_system (d := n + 1) (p := p) hd ha' hI'
      lia

lemma idDecompositionAFormula_fixed {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    IdTransform d (idDecompositionAFormula d p) = idDecompositionAFormula d p := by
  cases d with
  | zero =>
      have hp0 : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hd
      have hI0 : IdTransform 0 p = p := by
        rw [hp0, IdTransform, Polynomial.reflect_C]
        lia
      have hB0 : idDecompositionBFormula 0 p = 0 := by
        rw [idDecompositionBFormula, hI0, sub_self, zero_divByMonic]
      have hA0 : idDecompositionAFormula 0 p = p := by
        simpa [hB0] using (idDecompositionFormula_eq_add_X_mul (d := 0) hd).symm
      lia
  | succ n =>
      let a := idDecompositionAFormula (n + 1) p
      let b := idDecompositionBFormula (n + 1) p
      have ha : p = a + X * b := by
        simpa [a, b] using idDecompositionFormula_eq_add_X_mul (d := n + 1) hd
      have hI : IdTransform (n + 1) p = a + b := by
        simpa [a, b] using idDecompositionFormula_IdTransform_eq_add (d := n + 1) hd
      have hbdeg : b.natDegree ≤ n := by
        simpa [b] using natDegree_idDecompositionBFormula_le (d := n + 1) hd
      have ha' : p = IdTransform (n + 1) a + X * IdTransform n b := by
        have h0 : p = IdTransform (n + 1) a + IdTransform (n + 1) b := by
          simpa [IdTransform, Polynomial.reflect_add, a, b] using
            (congrArg (IdTransform (n + 1)) hI)
        rw [IdTransform_of_natDegree_le_pred (d := n + 1) (Nat.succ_pos _) hbdeg] at h0
        lia
      have hI' : IdTransform (n + 1) p = IdTransform (n + 1) a + IdTransform n b := by
        have h0 : IdTransform (n + 1) p = IdTransform (n + 1) a + IdTransform (n + 1) (X * b) := by
          simp_all
        rw [IdTransform_X_mul_of_natDegree_le_pred (d := n + 1) (Nat.succ_pos _) hbdeg] at h0
        lia
      have hsys := idDecompositionFormula_eq_of_system (d := n + 1) (p := p) hd ha' hI'
      lia

theorem isIdDecomposition_formula {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    IsIdDecomposition d p (idDecompositionAFormula d p) (idDecompositionBFormula d p) := by
  refine ⟨idDecompositionFormula_eq_add_X_mul hd, natDegree_idDecompositionAFormula_le hd,
    natDegree_idDecompositionBFormula_le hd, idDecompositionAFormula_fixed hd,
    idDecompositionBFormula_fixed hd⟩

/-- Planning target for Brändén--Solus Lemma 2.1: every polynomial of degree at
most `d` has a unique symmetric `I_d`-decomposition, and the explicit formulas
agree with the abstract pair. -/
def idDecompositionExistsUniqueStatement : Prop :=
  ∀ {d : ℕ} {p : ℝ[X]},
    p.natDegree ≤ d →
    ∃! ab : ℝ[X] × ℝ[X],
      IsIdDecomposition d p ab.1 ab.2 ∧
      ab.1 = idDecompositionAFormula d p ∧
      ab.2 = idDecompositionBFormula d p

theorem idDecompositionExistsUnique : idDecompositionExistsUniqueStatement := by
  intro d p hd
  refine ⟨⟨idDecompositionAFormula d p, idDecompositionBFormula d p⟩, ?_, ?_⟩
  · exact ⟨isIdDecomposition_formula hd, rfl, rfl⟩
  · lia

@[simp] lemma RdTransform_zero (d : ℕ) :
    RdTransform d (0 : ℝ[X]) = 0 := by
  simp [RdTransform]

@[simp] lemma RdTransform_add (d : ℕ) (p q : ℝ[X]) :
    RdTransform d (p + q) = RdTransform d p + RdTransform d q := by
  simp [RdTransform, mul_add]

@[simp] lemma RdTransform_neg (d : ℕ) (p : ℝ[X]) :
    RdTransform d (-p) = -RdTransform d p := by
  simp [RdTransform]

@[simp] lemma RdTransform_sub (d : ℕ) (p q : ℝ[X]) :
    RdTransform d (p - q) = RdTransform d p - RdTransform d q := by
  simp [sub_eq_add_neg]

lemma RdTransform_succ (d : ℕ) (p : ℝ[X]) :
    RdTransform (d + 1) p = -RdTransform d p := by
  unfold RdTransform
  grind

lemma RdTransform_involutive (d : ℕ) (p : ℝ[X]) :
    RdTransform d (RdTransform d p) = p := by
  unfold RdTransform
  rw [mul_comp, C_comp, comp_assoc]
  have hcomp : (-X - 1 : ℝ[X]).comp (-X - 1) = X := by
    simp
  rw [hcomp, ← mul_assoc, ← map_mul]
  have hpow : ((-1 : ℝ) ^ d) * ((-1 : ℝ) ^ d) = 1 := by
    rw [← pow_add, ← two_mul]
    norm_num
  simp_all

lemma RdTransform_X_mul_succ (d : ℕ) (p : ℝ[X]) :
    RdTransform (d + 1) (X * p) = (X + 1) * RdTransform d p := by
  rw [RdTransform_succ, RdTransform, mul_comp, X_comp]
  calc
    -(C (((-1 : ℝ) ^ d)) * ((-X - 1) * p.comp (-X - 1)))
        = (X + 1) * (C (((-1 : ℝ) ^ d)) * p.comp (-X - 1)) := by
            ring
    _ = (X + 1) * RdTransform d p := by rw [RdTransform]

lemma RdTransform_X_add_one_mul_succ (d : ℕ) (p : ℝ[X]) :
    RdTransform (d + 1) ((X + 1) * p) = X * RdTransform d p := by
  rw [show ((X + 1) * p : ℝ[X]) = X * p + p by grind]
  rw [RdTransform_add, RdTransform_X_mul_succ, RdTransform_succ]
  ring

lemma RdTransform_basis_term (d n : ℕ) (a : ℝ) (hn : n ≤ d) :
    RdTransform d (C a * X ^ n * (X + 1) ^ (d - n)) = C a * X ^ (d - n) * (X + 1) ^ n := by
  induction d generalizing n with
  | zero =>
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
      subst hn0
      simp [RdTransform]
  | succ d ih =>
      cases n with
      | zero =>
          have hzero :
              C a * X ^ 0 * (X + 1) ^ (d + 1 - 0) = (X + 1) * (C a * X ^ 0 * (X + 1) ^ d) := by
            grind
          calc
            RdTransform (d + 1) (C a * X ^ 0 * (X + 1) ^ (d + 1 - 0))
                = RdTransform (d + 1) ((X + 1) * (C a * X ^ 0 * (X + 1) ^ d)) := by
                    lia
            _ = X * RdTransform d (C a * X ^ 0 * (X + 1) ^ d) := by
                  rw [RdTransform_X_add_one_mul_succ]
            _ = X * (C a * X ^ (d - 0) * (X + 1) ^ 0) := by
                  simpa using congrArg (fun q => X * q) (ih 0 (Nat.zero_le d))
            _ = C a * X ^ (d + 1 - 0) * (X + 1) ^ 0 := by
                  grind
      | succ n =>
          have hn' : n ≤ d := Nat.succ_le_succ_iff.mp hn
          have hsucc :
              C a * X ^ (n + 1) * (X + 1) ^ (d + 1 - (n + 1)) =
                X * (C a * X ^ n * (X + 1) ^ (d - n)) := by
            grind
          calc
            RdTransform (d + 1) (C a * X ^ (n + 1) * (X + 1) ^ (d + 1 - (n + 1)))
                = RdTransform (d + 1) (X * (C a * X ^ n * (X + 1) ^ (d - n))) := by
                    lia
            _ = (X + 1) * RdTransform d (C a * X ^ n * (X + 1) ^ (d - n)) := by
                  rw [RdTransform_X_mul_succ]
            _ = (X + 1) * (C a * X ^ (d - n) * (X + 1) ^ n) := by
                  simp_all
            _ = C a * X ^ (d + 1 - (n + 1)) * (X + 1) ^ (n + 1) := by
                  grind

lemma RdTransform_fPolynomial (d : ℕ) (h : ℝ[X]) :
    RdTransform d (fPolynomial d h) = fPolynomial d (IdTransform d h) := by
  refine Polynomial.induction_on' h ?_ ?_
  · simp_all
  · intro n a
    by_cases hn : n ≤ d
    · have hf : fPolynomial d (monomial n a) = C a * X ^ n * (X + 1) ^ (d - n) := by
          simp [fPolynomial_monomial, hn]
      rw [hf, RdTransform_basis_term d n a hn]
      have hid : IdTransform d (monomial n a) = monomial (d - n) a := by
        rw [IdTransform, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.reflect_C_mul_X_pow]
        rw [Polynomial.revAt_le hn, Polynomial.C_mul_X_pow_eq_monomial]
      rw [hid]
      have hsub : d - (d - n) = n := by lia
      have hfd : fPolynomial d (monomial (d - n) a) = C a * X ^ (d - n) * (X + 1) ^ n := by
        have hle : d - n ≤ d := Nat.sub_le _ _
        simpa [hle, hsub] using (fPolynomial_monomial d (d - n) a)
      lia
    · have hgt : d < n := lt_of_not_ge hn
      have hf : fPolynomial d (monomial n a) = 0 := by
        simp [fPolynomial_monomial, hn]
      rw [hf, RdTransform_zero]
      have hid : IdTransform d (monomial n a) = monomial n a := by
        rw [IdTransform, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.reflect_C_mul_X_pow]
        rw [Polynomial.revAt_eq_self_of_lt hgt, Polynomial.C_mul_X_pow_eq_monomial]
      lia

lemma natDegree_RdTransform_eq (d : ℕ) (p : ℝ[X]) :
    (RdTransform d p).natDegree = p.natDegree := by
  have hX1 : (-X - 1 : ℝ[X]) = -(X + 1) := by
    ring
  have ht : (-X - 1 : ℝ[X]).natDegree = 1 := by
    rw [hX1, Polynomial.natDegree_neg, show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp,
      Polynomial.natDegree_X_add_C]
  unfold RdTransform
  rw [Polynomial.natDegree_C_mul (pow_ne_zero _ (by simp)), Polynomial.natDegree_comp, ht]
  lia

lemma leadingCoeff_RdTransform (d : ℕ) (p : ℝ[X]) :
    (RdTransform d p).leadingCoeff = (-1 : ℝ) ^ (d + p.natDegree) * p.leadingCoeff := by
  have hX1 : (-X - 1 : ℝ[X]) = -(X + 1) := by
    ring
  have hdeg : (-X - 1 : ℝ[X]).natDegree = 1 := by
    rw [hX1, Polynomial.natDegree_neg, show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp,
      Polynomial.natDegree_X_add_C]
  have ht : (-X - 1 : ℝ[X]).natDegree ≠ 0 := by
    lia
  have hl : (-X - 1 : ℝ[X]).leadingCoeff = (-1 : ℝ) := by
    rw [hX1, Polynomial.leadingCoeff_neg, show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp,
      Polynomial.leadingCoeff_X_add_C]
  unfold RdTransform
  rw [Polynomial.leadingCoeff_C_mul_of_isUnit (show IsUnit (((-1 : ℝ) ^ d)) by
        simp),
    Polynomial.leadingCoeff_comp ht, hl]
  grind

lemma leadingCoeff_RdTransform_eq_of_natDegree_eq {d : ℕ} {p : ℝ[X]} (hd : p.natDegree = d) :
    (RdTransform d p).leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff_RdTransform, hd, ← two_mul d, pow_mul]
  simp

theorem rdDecompositionFormula_eq_add_X_mul (d : ℕ) (p : ℝ[X]) :
    p = rdDecompositionAFormula d p + X * rdDecompositionBFormula d p := by
  unfold rdDecompositionAFormula rdDecompositionBFormula
  ring

theorem rdDecompositionFormula_RdTransform_eq_add_X_add_one_mul (d : ℕ) (p : ℝ[X]) :
    RdTransform d p = rdDecompositionAFormula d p + (X + 1) * rdDecompositionBFormula d p := by
  unfold rdDecompositionAFormula rdDecompositionBFormula
  ring

theorem rdDecompositionFormula_eq_of_system {d : ℕ} {p a b : ℝ[X]}
    (hp : p = a + X * b) (hR : RdTransform d p = a + (X + 1) * b) :
    a = rdDecompositionAFormula d p ∧ b = rdDecompositionBFormula d p := by
  have hbR : b = RdTransform d p - p := by
    grind
  have hb : b = rdDecompositionBFormula d p := by
    simpa [rdDecompositionBFormula] using hbR
  refine ⟨?_, hb⟩
  calc
    a = p - X * b := by grind
    _ = p - X * (RdTransform d p - p) := by lia
    _ = rdDecompositionAFormula d p := by
      unfold rdDecompositionAFormula
      ring

lemma natDegree_rdDecompositionBFormula_le {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (rdDecompositionBFormula d p).natDegree ≤ d - 1 := by
  have hR : (RdTransform d p).natDegree ≤ d := by
    rw [natDegree_RdTransform_eq]
    lia
  have hdeg : (rdDecompositionBFormula d p).natDegree ≤ d := by
    unfold rdDecompositionBFormula
    simpa using Polynomial.natDegree_sub_le_of_le hR hd
  rcases lt_or_eq_of_le hd with hlt | hEq
  · have hR' : (RdTransform d p).natDegree ≤ d - 1 := by
      rw [natDegree_RdTransform_eq]
      lia
    have hp' : p.natDegree ≤ d - 1 := by lia
    unfold rdDecompositionBFormula
    simpa using Polynomial.natDegree_sub_le_of_le hR' hp'
  · have hcoeff : (rdDecompositionBFormula d p).coeff d = 0 := by
      have hRdeg : (RdTransform d p).natDegree = d := by rw [natDegree_RdTransform_eq, hEq]
      have hRcoeff : (RdTransform d p).coeff d = p.leadingCoeff := by
        calc
          (RdTransform d p).coeff d = (RdTransform d p).leadingCoeff := by
            simpa [hRdeg] using (Polynomial.coeff_natDegree (p := RdTransform d p))
          _ = p.leadingCoeff := by
            rw [leadingCoeff_RdTransform_eq_of_natDegree_eq hEq]
      have hpcoeff : p.coeff d = p.leadingCoeff := by
        simpa [hEq] using (Polynomial.coeff_natDegree (p := p))
      unfold rdDecompositionBFormula
      simp_all
    exact Polynomial.natDegree_le_pred hdeg hcoeff

lemma natDegree_rdDecompositionAFormula_le {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (rdDecompositionAFormula d p).natDegree ≤ d := by
  cases d with
  | zero =>
      have hp0 : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hd
      have hA0 : rdDecompositionAFormula 0 p = p := by
        rw [hp0, rdDecompositionAFormula]
        simp [RdTransform]
        ring
      lia
  | succ n =>
      have hbdeg : (rdDecompositionBFormula (n + 1) p).natDegree ≤ n :=
        by simpa using natDegree_rdDecompositionBFormula_le hd
      have hXb : (X * rdDecompositionBFormula (n + 1) p).natDegree ≤ n + 1 := by
        have hXb' :=
          Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_X_le hbdeg
        lia
      have hA : rdDecompositionAFormula (n + 1) p =
          p - X * rdDecompositionBFormula (n + 1) p := by
        unfold rdDecompositionAFormula rdDecompositionBFormula
        ring
      rw [hA]
      simpa using Polynomial.natDegree_sub_le_of_le hd hXb

lemma rdDecompositionBFormula_fixed {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    RdTransform (d - 1) (rdDecompositionBFormula d p) = rdDecompositionBFormula d p := by
  cases d with
  | zero =>
      have hp0 : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hd
      rw [rdDecompositionBFormula, hp0]
      simp [RdTransform]
  | succ n =>
      have hpred : RdTransform n (RdTransform (n + 1) p) = -p := by
        rw [RdTransform_succ, RdTransform_neg, RdTransform_involutive]
      have hs : RdTransform n p = -RdTransform (n + 1) p := by
        rw [RdTransform_succ]
        simp
      change RdTransform n (RdTransform (n + 1) p - p) = RdTransform (n + 1) p - p
      rw [RdTransform_sub, hpred, hs]
      ring

lemma rdDecompositionAFormula_fixed {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    RdTransform d (rdDecompositionAFormula d p) = rdDecompositionAFormula d p := by
  cases d with
  | zero =>
      have hp0 : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hd
      have hB0 : rdDecompositionBFormula 0 p = 0 := by
        rw [rdDecompositionBFormula, hp0]
        simp [RdTransform]
      have hA0 : rdDecompositionAFormula 0 p = p := by
        simpa [hB0] using (rdDecompositionFormula_eq_add_X_mul 0 p).symm
      rw [hA0, hp0]
      simp [RdTransform]
  | succ n =>
      have hpred : RdTransform n (RdTransform (n + 1) p) = -p := by
        rw [RdTransform_succ, RdTransform_neg, RdTransform_involutive]
      have hs : RdTransform n p = -RdTransform (n + 1) p := by
        rw [RdTransform_succ]
        simp
      rw [rdDecompositionAFormula, RdTransform_sub, RdTransform_X_add_one_mul_succ,
        RdTransform_X_mul_succ, hpred, hs]
      ring

theorem isRdDecomposition_formula {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    IsRdDecomposition d p (rdDecompositionAFormula d p) (rdDecompositionBFormula d p) := by
  refine ⟨rdDecompositionFormula_eq_add_X_mul d p, natDegree_rdDecompositionAFormula_le hd,
    natDegree_rdDecompositionBFormula_le hd, rdDecompositionAFormula_fixed hd,
    rdDecompositionBFormula_fixed hd⟩

/-- Planning target for Brändén--Solus Lemma 2.2: every polynomial of degree at
most `d` has a unique symmetric `R_d`-decomposition, again matching the
explicit formulas. -/
def rdDecompositionExistsUniqueStatement : Prop :=
  ∀ {d : ℕ} {p : ℝ[X]},
    p.natDegree ≤ d →
    ∃! ab : ℝ[X] × ℝ[X],
      IsRdDecomposition d p ab.1 ab.2 ∧
      ab.1 = rdDecompositionAFormula d p ∧
      ab.2 = rdDecompositionBFormula d p

theorem rdDecompositionExistsUnique : rdDecompositionExistsUniqueStatement := by
  intro d p hd
  refine ⟨⟨rdDecompositionAFormula d p, rdDecompositionBFormula d p⟩, ?_, ?_⟩
  · exact ⟨isRdDecomposition_formula hd, rfl, rfl⟩
  · lia

lemma eq_zero_of_natDegree_le_zero_of_eq_add_X_mul {p a b : ℝ[X]}
    (hp : p.natDegree ≤ 0) (ha : a.natDegree ≤ 0) (hb : b.natDegree ≤ 0) (h : p = a + X * b) :
    b = 0 := by
  have hp1 : p.coeff 1 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by lia))
  have ha1 : a.coeff 1 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ha (by lia))
  rw [h, Polynomial.coeff_add, Polynomial.coeff_X_mul, ha1, zero_add] at hp1
  have hbC : b = C (b.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hb
  grind

theorem idTransform_eq_add_of_isIdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d) (h : IsIdDecomposition d p a b) :
    IdTransform d p = a + b := by
  rcases h with ⟨hab, had, hbd, hfixA, hfixB⟩
  cases d with
  | zero =>
      have hb0 : b = 0 := eq_zero_of_natDegree_le_zero_of_eq_add_X_mul hd had hbd hab
      simp_all
  | succ n =>
      have hfixB' : IdTransform n b = b := by
        lia
      have hXb : IdTransform (n + 1) (X * b) = b := by
        simpa [Nat.succ_sub_one] using (IdTransform_X_mul_succ (d := n) (p := b) hbd).trans hfixB'
      simp_all

theorem idDecomposition_eq_formula_of_isIdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d) (h : IsIdDecomposition d p a b) :
    a = idDecompositionAFormula d p ∧ b = idDecompositionBFormula d p :=
  idDecompositionFormula_eq_of_system hd h.1 <|
    idTransform_eq_add_of_isIdDecomposition hd h

theorem rdTransform_eq_add_X_add_one_mul_of_isRdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hp : p.natDegree ≤ d) (h : IsRdDecomposition d p a b) :
    RdTransform d p = a + (X + 1) * b := by
  rcases h with ⟨hab, had, hbd, hfixA, hfixB⟩
  cases d with
  | zero =>
      have hb0 : b = 0 := eq_zero_of_natDegree_le_zero_of_eq_add_X_mul hp had hbd hab
      simp_all
  | succ n =>
      have hfixB' : RdTransform n b = b := by
        lia
      rw [hab, RdTransform_add, hfixA, RdTransform_X_mul_succ, hfixB']

theorem rdDecomposition_eq_formula_of_isRdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hp : p.natDegree ≤ d) (h : IsRdDecomposition d p a b) :
    a = rdDecompositionAFormula d p ∧ b = rdDecompositionBFormula d p :=
  rdDecompositionFormula_eq_of_system h.1 <|
    rdTransform_eq_add_X_add_one_mul_of_isRdDecomposition hp h

theorem isRdDecomposition_fPolynomial_of_isIdDecomposition {d : ℕ} {h a b : ℝ[X]}
    (hd : h.natDegree ≤ d) (hid : IsIdDecomposition d h a b) :
    IsRdDecomposition d (fPolynomial d h) (fPolynomial d a) (fPolynomial (d - 1) b) := by
  rcases hid with ⟨hab, had, hbd, hfixA, hfixB⟩
  refine ⟨?_, fPolynomial_natDegree_le d a, fPolynomial_natDegree_le (d - 1) b, ?_, ?_⟩
  · cases d with
    | zero =>
        have hb0 : b = 0 := eq_zero_of_natDegree_le_zero_of_eq_add_X_mul hd had hbd hab
        simp_all
    | succ n =>
        rw [hab, fPolynomial_add]
        rw [show fPolynomial (n + 1) (X * b) = X * fPolynomial (n + 1 - 1) b by
          simpa [Nat.succ_sub_one] using (fPolynomial_X_mul_succ n b)]
  · rw [RdTransform_fPolynomial, hfixA]
  · rw [RdTransform_fPolynomial, hfixB]

/-- Planning target for Brändén--Solus Lemma 2.3, relating the `I_d`- and
`R_d`-decompositions through the `f`-polynomial transform. -/
def fPolynomialDecompositionCompatibilityStatement : Prop :=
  ∀ {d : ℕ} {h a b aTilde bTilde : ℝ[X]},
    h.natDegree ≤ d →
    IsIdDecomposition d h a b →
    IsRdDecomposition d (fPolynomial d h) aTilde bTilde →
    aTilde = fPolynomial d a ∧
    bTilde = fPolynomial (d - 1) b

theorem fPolynomialDecompositionCompatibility : fPolynomialDecompositionCompatibilityStatement := by
  intro d h a b aTilde bTilde hd hid hrd
  have hleft := rdDecomposition_eq_formula_of_isRdDecomposition
    (p := fPolynomial d h) (a := aTilde) (b := bTilde) (fPolynomial_natDegree_le d h) hrd
  have hright := rdDecomposition_eq_formula_of_isRdDecomposition
    (p := fPolynomial d h) (a := fPolynomial d a) (b := fPolynomial (d - 1) b)
    (fPolynomial_natDegree_le d h) (isRdDecomposition_fPolynomial_of_isIdDecomposition hd hid)
  lia

lemma prec_of_prec0_of_ne_zero {f g : ℝ[X]}
    (hf : f ≠ 0) (hg : g ≠ 0) (h : Prec0 f g) :
    Prec f g := by
  rcases h with rfl | rfl | hprec
  · lia
  · lia
  · lia

private lemma natDegree_add_X_mul_ge_of_hasNonnegCoeffs
    {a b : ℝ[X]}
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (hb0 : b ≠ 0) :
    b.natDegree + 1 ≤ (a + X * b).natDegree := by
  apply Polynomial.le_natDegree_of_ne_zero
  have hcoeff_pos : 0 < (a + X * b).coeff (b.natDegree + 1) := by
    rw [Polynomial.coeff_add, Polynomial.coeff_X_mul]
    have ha_coeff_nonneg : 0 ≤ a.coeff (b.natDegree + 1) := ha_nonneg _
    have hb_top_pos : 0 < b.coeff b.natDegree := by
      simpa [HasPosLeadingCoeff] using hb_nonneg.pos_leadingCoeff hb0
    linarith
  grind

private lemma leadingCoeff_add_X_mul_eq_of_natDegree_le
    {a b : ℝ[X]}
    (ha_le : a.natDegree ≤ b.natDegree)
    (hb_nonneg : HasNonnegCoeffs b)
    (hb0 : b ≠ 0) :
    (a + X * b).leadingCoeff = b.leadingCoeff := by
  have hXb_pos : HasPosLeadingCoeff (X * b) :=
    (hasNonnegCoeffs_X.mul hb_nonneg).pos_leadingCoeff (mul_ne_zero X_ne_zero hb0)
  have hdeg_lt : a.natDegree < (X * b).natDegree := by
    simp_all
  have hsum_deg : (a + X * b).natDegree = (X * b).natDegree :=
    natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hXb_pos
  have hXb_deg : (X * b).natDegree = b.natDegree + 1 := by
    simp_all
  have ha_top : a.coeff (b.natDegree + 1) = 0 := by
    have hdeg_top : a.natDegree < b.natDegree + 1 := by
      lia
    exact Polynomial.coeff_eq_zero_of_natDegree_lt hdeg_top
  calc
    (a + X * b).leadingCoeff = (a + X * b).coeff (b.natDegree + 1) := by
      rw [Polynomial.leadingCoeff, hsum_deg, hXb_deg]
    _ = a.coeff (b.natDegree + 1) + (X * b).coeff (b.natDegree + 1) := by
      simp
    _ = b.coeff b.natDegree := by
      simp_all
    _ = b.leadingCoeff := by
      simp

private lemma natDegree_right_of_prec_to_sum
    {a b p : ℝ[X]}
    (hp_eq : p = a + X * b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (hb0 : b ≠ 0)
    (hbp : Prec b p) :
    b.natDegree + 1 = p.natDegree := by
  have hdeg_lo : b.natDegree + 1 ≤ p.natDegree := by
    simpa [hp_eq] using
      natDegree_add_X_mul_ge_of_hasNonnegCoeffs ha_nonneg hb_nonneg hb0
  have hdeg_hi : p.natDegree ≤ b.natDegree + 1 := by
    rcases hbp with ⟨hb_rr, hp_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
    have hss_len : ss.length = b.natDegree := by
      rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hb_rr.2]
    have hrs_len : rs.length = p.natDegree := by
      rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hp_rr.2]
    lia
  lia

/-- Converse branch for the Brändén--Solus decomposition theorem: if the right
component `b` already interlaces `p = a + X*b`, and the top degree of `p`
comes entirely from `X*b`, then subtracting that `X*b` term preserves the
left interlacing relation. -/
private theorem prec_b_component_of_prec_sum_of_leadingCoeff_eq
    {p a b : ℝ[X]}
    (hp_eq : p = a + X * b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (hbp : Prec b p)
    (hlc : p.leadingCoeff = b.leadingCoeff) :
    Prec b a := by
  have hp0 : p ≠ 0 := hbp.2.1.1
  have hp_nonneg : HasNonnegCoeffs p := by
    simpa [hp_eq] using ha_nonneg.add (hasNonnegCoeffs_X.mul hb_nonneg)
  have hdeg : b.natDegree + 1 = p.natDegree :=
    natDegree_right_of_prec_to_sum hp_eq ha_nonneg hb_nonneg hb0 hbp
  let c : ℝ := p.leadingCoeff⁻¹
  have hc_ne : c ≠ 0 := by
    exact inv_ne_zero (ne_of_gt (hp_nonneg.pos_leadingCoeff hp0))
  have hp_monic : (C c * p).Monic := by
    unfold c
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hb_monic : (C c * b).Monic := by
    unfold c
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hscaled : Prec (C c * b) (C c * p) :=
    prec_C_mul_right (prec_C_mul_left hbp hc_ne) hc_ne
  have hp_nonpos : ∀ r ∈ p.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hbp.2.1.2 hp_nonneg
  have hb_nonpos : ∀ r ∈ b.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hbp.1.2 hb_nonneg
  have hdeg_scaled : (C c * b).natDegree + 1 = (C c * p).natDegree := by
    rw [Polynomial.natDegree_C_mul hc_ne, Polynomial.natDegree_C_mul hc_ne, hdeg]
  have hprec0 : Prec0 (C c * b) (C c * p - X * (C c * b)) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using
      prec_sub_X_mul_right
        (f := C c * p) (g := C c * b)
        hscaled hp_monic hb_monic hdeg_scaled
        (by
          simp_all)
        (by
          simp_all)
  have hXC : C c * (X * b) = X * (C c * b) := by
    grind
  have hsub_eq : C c * p - X * (C c * b) = C c * a := by
    grind
  rw [hsub_eq] at hprec0
  have hCb0 : C c * b ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hc_ne) hb0
  have hCa0 : C c * a ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hc_ne) ha0
  have hscaled_prec : Prec (C c * b) (C c * a) :=
    prec_of_prec0_of_ne_zero hCb0 hCa0 hprec0
  have hback :
      Prec (C c⁻¹ * (C c * b)) (C c⁻¹ * (C c * a)) :=
    prec_C_mul_right
      (prec_C_mul_left hscaled_prec (inv_ne_zero hc_ne))
      (inv_ne_zero hc_ne)
  have hcancel_b : C c⁻¹ * (C c * b) = b := by
    calc
      C c⁻¹ * (C c * b) = C (c⁻¹ * c) * b := by grind
      _ = b := by simp_all
  have hcancel_a : C c⁻¹ * (C c * a) = a := by
    calc
      C c⁻¹ * (C c * a) = C (c⁻¹ * c) * a := by grind
      _ = a := by simp_all
  lia

theorem brandenSolusTheorem26_forward_of_prec_b_a {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (hba : Prec b a) :
    Prec a p ∧ Prec b p ∧ Prec (IdTransform d p) p := by
  have hp_eq : p = a + X * b := hid.1
  have hId_eq : IdTransform d p = a + b :=
    idTransform_eq_add_of_isIdDecomposition hd hid
  have hb_rr : (b ≠ 0 ∧ b.Splits) := hba.1
  have ha_rr : (a ≠ 0 ∧ a.Splits) := hba.2.1
  have hb_pos : HasPosLeadingCoeff b := hb_nonneg.pos_leadingCoeff hb_rr.1
  have ha_pos : HasPosLeadingCoeff a := ha_nonneg.pos_leadingCoeff ha_rr.1
  have hXb_nonneg : HasNonnegCoeffs (X * b) := hasNonnegCoeffs_X.mul hb_nonneg
  have hXb_pos : HasPosLeadingCoeff (X * b) :=
    hXb_nonneg.pos_leadingCoeff (mul_ne_zero X_ne_zero hb_rr.1)
  have haxb : Prec a (X * b) := prec_mul_X_of_prec_of_nonneg hba hb_nonneg ha_nonneg
  have hp_right : Prec (a + X * b) (X * b) := by
    simpa using
      (prec_nonneg_combo_right haxb ha_pos hXb_pos
        (a := (1 : ℝ)) (b := (1 : ℝ)) (by simp) (by simp)
        (Or.inl (by simp)))
  have hp0 : p ≠ 0 := by
    simpa [hp_eq] using hp_right.1.1
  have hap : Prec a p := by
    have hprec0 : Prec0 a ([a, X * b].sum) := by
      refine prec0_sum_left_of_common_left_of_nonneg [a, X * b] a ?_ ?_
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact (prec_refl ha_rr.1 ha_rr.2).toPrec0
        · exact haxb.toPrec0
      · simp_all
    exact prec_of_prec0_of_ne_zero ha_rr.1 hp0 (by simp_all)
  have hbXb : Prec b (X * b) :=
    prec_mul_X_of_prec_of_nonneg (prec_refl hb_rr.1 hb_rr.2) hb_nonneg hb_nonneg
  have hbp : Prec b p := by
    have hprec0 : Prec0 b ([a, X * b].sum) := by
      refine prec0_sum_left_of_common_left_of_nonneg [a, X * b] b ?_ ?_
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hba.toPrec0
        · exact hbXb.toPrec0
      · simp_all
    exact prec_of_prec0_of_ne_zero hb_rr.1 hp0 (by simp_all)
  have hIda : Prec (a + b) a := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (prec_nonneg_combo_right hba hb_pos ha_pos
        (a := (1 : ℝ)) (b := (1 : ℝ)) (by simp) (by simp)
        (Or.inl (by simp)))
  have hIdp : Prec (IdTransform d p) p := by
    have hprec0 : Prec0 (∑ t ∈ (Finset.univ : Finset Bool), cond t b a) p := by
      refine prec0_finsetSum_right_of_nonneg (s := (Finset.univ : Finset Bool))
        (f := fun t => cond t b a) (h := p) ?_ ?_
      · intro t ht
        cases t <;> simp [hap.toPrec0, hbp.toPrec0]
      · lia
    have hId0 : IdTransform d p ≠ 0 := by
      simpa [hId_eq] using hIda.1.1
    exact prec_of_prec0_of_ne_zero hId0 hp0 (by
      simpa [hId_eq, add_comm, add_left_comm, add_assoc] using hprec0)
  lia

theorem brandenSolusTheorem26_third_equiv_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) :
    (Prec b a ↔ Prec b p) := by
  constructor
  · intro hba
    exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).2.1
  · intro hbp
    have hlc : p.leadingCoeff = b.leadingCoeff := by
      rw [hid.1]
      exact leadingCoeff_add_X_mul_eq_of_natDegree_le ha_le hb_nonneg hb0
    exact
      prec_b_component_of_prec_sum_of_leadingCoeff_eq
        hid.1 ha_nonneg hb_nonneg ha0 hb0 hbp hlc

private theorem allComboRealRooted_left_X_mul_component_of_prec_left
    {a b p : ℝ[X]}
    (hp_eq : p = a + X * b)
    (hap : Prec a p) :
    AllComboRealRooted a (X * b) := by
  have hall_ap : AllComboRealRooted a p := allComboRealRooted_of_prec hap
  intro α β
  have hrew :
      C α * a + C β * (X * b) =
        C (α - β) * a + C β * p := by
    grind
  simpa [hrew] using hall_ap (α - β) β

private theorem allComboRealRooted_left_X_mul_component_of_prec_right
    {a b p : ℝ[X]}
    (hp_eq : p = a + X * b)
    (hpxb : Prec p (X * b)) :
    AllComboRealRooted a (X * b) := by
  have hall_pXb : AllComboRealRooted p (X * b) := allComboRealRooted_of_prec hpxb
  intro α β
  have hrew :
      C α * a + C β * (X * b) =
        C α * p + C (β - α) * (X * b) := by
    grind
  simpa [hrew] using hall_pXb α (β - α)

private theorem prec_b_component_of_prec_left_of_natDegree_le
    {a b p : ℝ[X]}
    (hp_eq : p = a + X * b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (hb0 : b ≠ 0)
    (hap : Prec a p) :
    Prec b a := by
  have hdeg_lo : b.natDegree + 1 ≤ p.natDegree := by
    simpa [hp_eq] using
      natDegree_add_X_mul_ge_of_hasNonnegCoeffs ha_nonneg hb_nonneg hb0
  have hdeg_hi : p.natDegree ≤ a.natDegree + 1 :=
    (natDegree_bounds_of_prec hap).2
  have hp_deg : p.natDegree = b.natDegree + 1 := by
    lia
  have hab_eq : a.natDegree = b.natDegree := by
    lia
  have hall_aXb : AllComboRealRooted a (X * b) :=
    allComboRealRooted_left_X_mul_component_of_prec_left hp_eq hap
  have hXb_rr : ((X * b) ≠ 0 ∧ (X * b).Splits) :=
    ⟨mul_ne_zero X_ne_zero hb0, by simpa using hall_aXb 0 1⟩
  have hdeg_aXb : a.natDegree + 1 = (X * b).natDegree := by
    simp_all
  have hprec_or : Prec a (X * b) ∨ Prec (X * b) a :=
    prec_of_allComboRealRooted hap.1.1 hap.1.2 hXb_rr.1 hXb_rr.2 hall_aXb
      (Or.inl hdeg_aXb)
  have hnot_rev : ¬ Prec (X * b) a := by
    intro hbad
    have hbound := (natDegree_bounds_of_prec hbad).1
    lia
  have hprec_aXb : Prec a (X * b) := by
    lia
  exact prec_of_prec_mul_X_of_nonneg hprec_aXb hb_nonneg ha_nonneg

private theorem natDegree_X_mul_component_eq_or_succ_of_prec_left_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hp_eq : p = a + X * b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_top : a.natDegree = d)
    (hb0 : b ≠ 0)
    (hap : Prec a p) :
    (X * b).natDegree = d ∨ (X * b).natDegree + 1 = d := by
  have hall_aXb : AllComboRealRooted a (X * b) :=
    allComboRealRooted_left_X_mul_component_of_prec_left hp_eq hap
  have hXb0 : X * b ≠ 0 := mul_ne_zero X_ne_zero hb0
  have hXb_nonneg : HasNonnegCoeffs (X * b) := hasNonnegCoeffs_X.mul hb_nonneg
  have hXb_le_p : (X * b).natDegree ≤ p.natDegree := by
    apply Polynomial.le_natDegree_of_ne_zero
    have hcoeff_pos : 0 < p.coeff (X * b).natDegree := by
      rw [hp_eq, Polynomial.coeff_add]
      have ha_coeff_nonneg : 0 ≤ a.coeff (X * b).natDegree := ha_nonneg _
      have hXb_top_pos : 0 < (X * b).coeff (X * b).natDegree := by
        have hlead : 0 < (X * b).leadingCoeff := hXb_nonneg.pos_leadingCoeff hXb0
        simp_all
      linarith
    grind
  have hXb_le_d : (X * b).natDegree ≤ d := le_trans hXb_le_p hd
  rcases natDegree_eq_or_succ_or_revSucc_of_allComboRealRooted hall_aXb hap.1.1 hXb0 with
    hdeg | hdeg | hdeg
  · lia
  · lia
  · lia

private lemma not_isRoot_zero_of_IdTransform_fixed_top_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]}
    (hfix : IdTransform d p = p)
    (hdeg : p.natDegree = d)
    (hp_nonneg : HasNonnegCoeffs p)
    (hp0 : p ≠ 0) :
    ¬ p.IsRoot 0 := by
  intro hp_root0
  have hcoeff : p.coeff 0 = p.coeff d := by
    simpa [IdTransform, Polynomial.coeff_reflect, Polynomial.revAt_zero] using
      (congrArg (fun q => q.coeff 0) hfix).symm
  have htop : 0 < p.coeff d := by
    rw [← hdeg, Polynomial.coeff_natDegree]
    exact hp_nonneg.pos_leadingCoeff hp0
  rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero] at hp_root0
  simp_all

private lemma exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
    {p : ℝ[X]}
    (hp_rr_ne : p ≠ 0) (hp_rr_splits : p.Splits)
    (hp_nonneg : HasNonnegCoeffs p)
    (hp0_root : ¬ p.IsRoot 0) :
    ∃ c : ℝ, (∀ s ∈ p.roots, s ≤ c) ∧ c < 0 := by
  let rs := p.roots.sort (· ≤ ·)
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_eq : (↑rs : Multiset ℝ) = p.roots := Multiset.sort_eq ..
  by_cases hrs_nil : rs = []
  · refine ⟨-1, ?_, by simp⟩
    intro s hs
    have hs' : s ∈ rs := by
      have : s ∈ (↑rs : Multiset ℝ) := by lia
      exact Multiset.mem_coe.mp this
    simp_all
  · refine ⟨rs.getLast hrs_nil, ?_, ?_⟩
    · intro s hs
      have hs' : s ∈ rs := by
        have : s ∈ (↑rs : Multiset ℝ) := by lia
        exact Multiset.mem_coe.mp this
      exact List.Pairwise.rel_getLast hrs_sorted hs'
    · have hc_root : p.IsRoot (rs.getLast hrs_nil) := by
        have hc_mem : rs.getLast hrs_nil ∈ rs := List.getLast_mem hrs_nil
        have : rs.getLast hrs_nil ∈ (↑rs : Multiset ℝ) := Multiset.mem_coe.mpr hc_mem
        simp_all
      have hc_nonpos : rs.getLast hrs_nil ≤ 0 :=
        roots_nonpos_of_nonneg_coeffs hp_rr_splits hp_nonneg (rs.getLast hrs_nil) <|
          (mem_roots hp_rr_ne).mpr hc_root
      grind

private lemma interlaces_of_prec_sameDegree_rightmost_factor
    {f g q : ℝ[X]} {uR : ℝ}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hright : ∀ r ∈ g.roots, r ≤ uR)
    (hgq : g = (X - C uR) * q) :
    Interlaces q f := by
  obtain ⟨hf, hg, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩ := hfg
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  have hq_ne : q ≠ 0 := by
    simp_all
  have hq : (q ≠ 0 ∧ q.Splits) := by
    apply isRealRooted_of_dvd hg.1 hg.2 hq_ne
    simp_all
  have hq_deg_g : q.natDegree + 1 = g.natDegree := by
    rw [hgq, natDegree_mul (X_sub_C_ne_zero uR) hq_ne, natDegree_X_sub_C]
    lia
  have hq_deg : q.natDegree + 1 = f.natDegree := by
    lia
  rcases hshape with ⟨hlen, _⟩ | ⟨_, halt⟩
  · lia
  · let qs := q.roots.sort (· ≤ ·)
    have hqs_eq : (↑qs : Multiset ℝ) = q.roots := Multiset.sort_eq ..
    have hqs_sorted : qs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
    have hqs_len : qs.length = q.natDegree := by
      rw [show qs = q.roots.sort (· ≤ ·) by lia, Multiset.length_sort,
        card_roots_of_splits hq.2]
    have hqs_le_uR : ∀ r ∈ qs, r ≤ uR := by
      intro r hr
      exact hright r (by
        rw [hgq, roots_mul (mul_ne_zero (X_sub_C_ne_zero uR) hq_ne), roots_X_sub_C]
        apply Multiset.mem_add.mpr
        right
        simpa [hqs_eq] using Multiset.mem_coe.mpr hr)
    have hqs_sorted_right : (qs ++ [uR]).Pairwise (· ≤ ·) := by
      grind
    have hrs_eq_right : rs = qs ++ [uR] := by
      apply List.Perm.eq_of_pairwise' hrs_sorted hqs_sorted_right
      apply Multiset.coe_eq_coe.mp
      calc
        (↑rs : Multiset ℝ) = g.roots := hrs_eq
        _ = ({uR} : Multiset ℝ) + q.roots := by
              rw [hgq, roots_mul (mul_ne_zero (X_sub_C_ne_zero uR) hq_ne), roots_X_sub_C]
        _ = q.roots + ({uR} : Multiset ℝ) := by grind
        _ = q.roots + ↑[uR] := by simp
        _ = (↑qs : Multiset ℝ) + ↑[uR] := by lia
        _ = (↑(qs ++ [uR]) : Multiset ℝ) := by rw [Multiset.coe_add]
    have hlen_qs : qs.length + 1 = ss.length := by
      lia
    have halt_right : ListAlternates ss (qs ++ [uR]) := by
      lia
    have hshape_qs_rs : ListInterlaces qs ss :=
      listInterlaces_of_listAlternates_append_right hlen_qs halt_right
    exact ⟨hf, hq, hq_deg, ss, qs, hss_sorted, hqs_sorted, hss_eq, hqs_eq, hshape_qs_rs⟩

private theorem prec_b_component_of_prec_left_top_of_sameDegree
    {d : ℕ} {p a b : ℝ[X]}
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hXb_top : (X * b).natDegree = d)
    (hap : Prec a p) :
    Prec b a := by
  have hp_eq : p = a + X * b := hid.1
  have hall_aXb : AllComboRealRooted a (X * b) :=
    allComboRealRooted_left_X_mul_component_of_prec_left hp_eq hap
  have hXb_rr : ((X * b) ≠ 0 ∧ (X * b).Splits) :=
    ⟨mul_ne_zero X_ne_zero hb0, by simpa using hall_aXb 0 1⟩
  have hsame : a.natDegree = (X * b).natDegree := by
    lia
  have hprec_or : Prec a (X * b) ∨ Prec (X * b) a :=
    prec_of_allComboRealRooted hap.1.1 hap.1.2 hXb_rr.1 hXb_rr.2 hall_aXb
      (Or.inr hsame)
  have ha_not_root0 : ¬ a.IsRoot 0 :=
    not_isRoot_zero_of_IdTransform_fixed_top_of_hasNonnegCoeffs
      hid.2.2.2.1 ha_top ha_nonneg ha0
  obtain ⟨c, hac_le, hc_lt0⟩ :=
    exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
      hap.1.1 hap.1.2 ha_nonneg ha_not_root0
  have hXb_root0 : (X * b).IsRoot 0 := by
    simp
  have hprec_aXb : Prec a (X * b) :=
    PosComboRealRooted.prec_of_prec_or_revPrec_of_root_asymmetry
      (f := X * b) (g := a) (c := c) (r := 0)
      (by lia)
      hac_le hXb_root0 hc_lt0
  exact prec_of_prec_mul_X_of_nonneg hprec_aXb hb_nonneg ha_nonneg

private theorem prec_b_component_of_prec_left_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hap : Prec a p) :
    Prec b a := by
  have hp_eq : p = a + X * b := hid.1
  have hXb_case :
      (X * b).natDegree = d ∨ (X * b).natDegree + 1 = d :=
    natDegree_X_mul_component_eq_or_succ_of_prec_left_top
      hd hp_eq ha_nonneg hb_nonneg ha_top hb0 hap
  rcases hXb_case with hXb_top | hXb_gap
  · exact
      prec_b_component_of_prec_left_top_of_sameDegree
        hid ha_nonneg hb_nonneg ha0 hb0 ha_top hXb_top hap
  · exfalso
    have hall_aXb : AllComboRealRooted a (X * b) :=
      allComboRealRooted_left_X_mul_component_of_prec_left hp_eq hap
    have hXb_rr : ((X * b) ≠ 0 ∧ (X * b).Splits) :=
      ⟨mul_ne_zero X_ne_zero hb0, by simpa using hall_aXb 0 1⟩
    have hall_Xba : AllComboRealRooted (X * b) a := by
      intro α β
      simpa [add_comm, add_left_comm, add_assoc] using hall_aXb β α
    have hprec_or : Prec (X * b) a ∨ Prec a (X * b) := by
      have hdeg : (X * b).natDegree + 1 = a.natDegree := by
        lia
      exact prec_of_allComboRealRooted hXb_rr.1 hXb_rr.2 hap.1.1 hap.1.2 hall_Xba (Or.inl hdeg)
    have ha_not_root0 : ¬ a.IsRoot 0 :=
      not_isRoot_zero_of_IdTransform_fixed_top_of_hasNonnegCoeffs
        hid.2.2.2.1 ha_top ha_nonneg ha0
    obtain ⟨c, hac_le, hc_lt0⟩ :=
      exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
        hap.1.1 hap.1.2 ha_nonneg ha_not_root0
    have hXb_root0 : (X * b).IsRoot 0 := by
      simp
    have hbad : Prec a (X * b) :=
      PosComboRealRooted.prec_of_prec_or_revPrec_of_root_asymmetry
        (f := X * b) (g := a) (c := c) (r := 0)
        hprec_or hac_le hXb_root0 hc_lt0
    have hbound : a.natDegree ≤ (X * b).natDegree :=
      (natDegree_bounds_of_prec hbad).1
    lia

private theorem prec_b_component_of_prec_right_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hbp : Prec b p) :
    Prec b a := by
  have hp_eq : p = a + X * b := hid.1
  have hp_nonneg : HasNonnegCoeffs p := by
    simpa [hp_eq] using ha_nonneg.add (hasNonnegCoeffs_X.mul hb_nonneg)
  have hpxb : Prec p (X * b) := prec_mul_X_of_prec_of_nonneg hbp hb_nonneg hp_nonneg
  have hall_aXb : AllComboRealRooted a (X * b) :=
    allComboRealRooted_left_X_mul_component_of_prec_right hp_eq hpxb
  have ha_rr : (a ≠ 0 ∧ a.Splits) := by
    exact ⟨ha0, by simpa using hall_aXb 1 0⟩
  have hp_deg : p.natDegree = d := by
    apply le_antisymm hd
    apply Polynomial.le_natDegree_of_ne_zero
    have hcoeff_pos : 0 < p.coeff d := by
      rw [hp_eq, Polynomial.coeff_add]
      have ha_top_pos : 0 < a.coeff d := by
        rw [← ha_top, Polynomial.coeff_natDegree]
        exact ha_nonneg.pos_leadingCoeff ha0
      have hXb_coeff_nonneg : 0 ≤ (X * b).coeff d :=
        (hasNonnegCoeffs_X.mul hb_nonneg) d
      linarith
    grind
  have hbp_deg : b.natDegree + 1 = p.natDegree :=
    natDegree_right_of_prec_to_sum hp_eq ha_nonneg hb_nonneg hb0 hbp
  have hsame : a.natDegree = (X * b).natDegree := by
    simp_all
  have ha_not_root0 : ¬ a.IsRoot 0 :=
    not_isRoot_zero_of_IdTransform_fixed_top_of_hasNonnegCoeffs
      hid.2.2.2.1 ha_top ha_nonneg ha0
  obtain ⟨c, hac_le, hc_lt0⟩ :=
    exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
      ha_rr.1 ha_rr.2 ha_nonneg ha_not_root0
  have hXb_root0 : (X * b).IsRoot 0 := by
    simp
  have hprec_or : Prec a (X * b) ∨ Prec (X * b) a :=
    prec_of_allComboRealRooted ha_rr.1 ha_rr.2 hpxb.2.1.1 hpxb.2.1.2 hall_aXb
      (Or.inr hsame)
  have hprec_aXb : Prec a (X * b) :=
    PosComboRealRooted.prec_of_prec_or_revPrec_of_root_asymmetry
      (f := X * b) (g := a) (c := c) (r := 0)
      (by lia)
      hac_le hXb_root0 hc_lt0
  exact prec_of_prec_mul_X_of_nonneg hprec_aXb hb_nonneg ha_nonneg

theorem brandenSolusTheorem26_first_equiv_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    (Prec b a ↔ Prec a p) := by
  constructor
  · intro hba
    exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).1
  · intro hap
    exact
      prec_b_component_of_prec_left_top
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hap

theorem brandenSolusTheorem26_forward_of_prec_a_p_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    Prec a p → Prec b p ∧ Prec (IdTransform d p) p := by
  intro hap
  have hba : Prec b a := by
    exact
      (brandenSolusTheorem26_first_equiv_of_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top).2 hap
  exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).2

theorem brandenSolusTheorem26_second_equiv_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    (Prec a p ↔ Prec b p) := by
  constructor
  · intro hap
    exact
      (brandenSolusTheorem26_forward_of_prec_a_p_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hap).1
  · intro hbp
    have hba : Prec b a := by
      exact
        prec_b_component_of_prec_right_top
          hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hbp
    exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).1

theorem brandenSolusTheorem26_third_forward_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    Prec b p → Prec (IdTransform d p) p := by
  intro hbp
  have hba : Prec b a := by
    exact
      prec_b_component_of_prec_right_top
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hbp
  exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).2.2

private theorem prec_b_component_of_prec_Id_top_of_right_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hb_top : b.natDegree = d - 1)
    (hIdp : Prec (IdTransform d p) p) :
    Prec b p := by
  let h : ℝ[X] := IdTransform d p
  let t : ℝ[X] := (X - C (1 : ℝ)) * b
  have hp_eq : p = a + X * b := hid.1
  have hId_eq : h = a + b := by
    simpa [h] using idTransform_eq_add_of_isIdDecomposition hd hid
  have hp_nonneg : HasNonnegCoeffs p := by
    simpa [hp_eq] using ha_nonneg.add (hasNonnegCoeffs_X.mul hb_nonneg)
  have hh_nonneg : HasNonnegCoeffs h := by
    rw [hId_eq]
    exact ha_nonneg.add hb_nonneg
  have ha_pos : HasPosLeadingCoeff a := ha_nonneg.pos_leadingCoeff ha0
  have hb_pos : HasPosLeadingCoeff b := hb_nonneg.pos_leadingCoeff hb0
  have hdeg_lo : b.natDegree + 1 ≤ p.natDegree := by
    simpa [hp_eq] using
      natDegree_add_X_mul_ge_of_hasNonnegCoeffs ha_nonneg hb_nonneg hb0
  have hb_succ : b.natDegree + 1 = d := by
    lia
  have hh_deg : h.natDegree = d := by
    rw [hId_eq]
    have hdeg_lt : b.natDegree < a.natDegree := by
      lia
    calc
      (a + b).natDegree = a.natDegree :=
        natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_lt ha_pos
      _ = d := ha_top
  have hdeg_lt : b.natDegree < a.natDegree := by
    lia
  have hh_pos : HasPosLeadingCoeff h := by
    rw [hId_eq]
    exact hasPosLeadingCoeff_add_of_natDegree_lt_left hdeg_lt ha_pos
  have hp_split : p = h + t := by
    grind
  have hall_hp : AllComboRealRooted h p := allComboRealRooted_of_prec hIdp
  have hall_ht : AllComboRealRooted h t := by
    intro α β
    have hrew :
        C α * h + C β * t =
          C (α - β) * h + C β * p := by
      grind
    simpa [hrew] using hall_hp (α - β) β
  have ht_ne : t ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0
  have ht_rr : (t ≠ 0 ∧ t.Splits) :=
    ⟨ht_ne, by simpa using hall_ht 0 1⟩
  have ht_pos : HasPosLeadingCoeff t := by
    dsimp [t]
    unfold HasPosLeadingCoeff at hb_pos ⊢
    rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul]
    lia
  have hb_rr : (b ≠ 0 ∧ b.Splits) := by
    apply isRealRooted_of_dvd ht_rr.1 ht_rr.2 hb0
    refine ⟨X - C (1 : ℝ), ?_⟩
    grind
  have hh_nonpos : ∀ r ∈ h.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hIdp.1.2 hh_nonneg
  have hsame : h.natDegree = t.natDegree := by
    dsimp [t]
    rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C]
    lia
  have hprec_or : Prec h t ∨ Prec t h :=
    prec_of_allComboRealRooted hIdp.1.1 hIdp.1.2 ht_rr.1 ht_rr.2 hall_ht
      (Or.inr hsame)
  have ht_root1 : t.IsRoot 1 := by
    dsimp [t]
    simp
  have hht : Prec h t :=
    PosComboRealRooted.prec_of_prec_or_revPrec_of_root_asymmetry
      (f := t) (g := h) (c := 0) (r := 1)
      (by lia)
      hh_nonpos ht_root1 (by simp)
  have ht_le_one : ∀ r ∈ t.roots, r ≤ 1 := by
    intro r hr
    dsimp [t] at hr
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0), roots_X_sub_C] at hr
    rcases Multiset.mem_add.mp hr with hr | hr
    · simp_all
    · have hr0 : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hb_rr.2 hb_nonneg r hr
      linarith
  have hbh : Prec b h :=
    (interlaces_of_prec_sameDegree_rightmost_factor
      (f := h) (g := t) (q := b) (uR := 1)
      hht hsame ht_le_one (by lia)).toPrec
  have hb_le_one : ∀ r ∈ b.roots, r ≤ (1 : ℝ) := by
    intro r hr
    have hr0 : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hb_rr.2 hb_nonneg r hr
    linarith
  have hbt : Prec b t := by
    dsimp [t]
    exact prec_sameDegree_to_prec_mul_X_sub_C_of_roots_le (1 : ℝ)
      (prec_refl hb_rr.1 hb_rr.2) rfl hb_pos hb_pos hb_le_one hb_le_one
  have hbp_sum : Prec b [h, t].sum := by
    refine prec_sum_left_of_common_left [h, t] b ?_ hb_pos ?_ ?_
    · simp_all
    · simp_all
    · lia
  simp_all

theorem brandenSolusTheorem26_third_converse_of_top_degree_of_right_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hb_top : b.natDegree = d - 1) :
    Prec (IdTransform d p) p → Prec b p := by
  intro hIdp
  exact
    prec_b_component_of_prec_Id_top_of_right_top
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hb_top hIdp

theorem brandenSolusTheorem26_third_equiv_of_top_degree_of_right_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hb_top : b.natDegree = d - 1) :
    (Prec b p ↔ Prec (IdTransform d p) p) := by
  constructor
  · exact
      brandenSolusTheorem26_third_forward_of_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  · exact
      brandenSolusTheorem26_third_converse_of_top_degree_of_right_top
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hb_top

theorem brandenSolusTheorem26_third_converse_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    Prec (IdTransform d p) p → Prec b p := by
  intro hIdp
  let h : ℝ[X] := IdTransform d p
  let t : ℝ[X] := (X - C (1 : ℝ)) * b
  have hp_eq : p = a + X * b := hid.1
  have hId_eq : h = a + b := by
    simpa [h] using idTransform_eq_add_of_isIdDecomposition hd hid
  have hh_nonneg : HasNonnegCoeffs h := by
    rw [hId_eq]
    exact ha_nonneg.add hb_nonneg
  have ha_pos : HasPosLeadingCoeff a := ha_nonneg.pos_leadingCoeff ha0
  have hdeg_lo : b.natDegree + 1 ≤ p.natDegree := by
    simpa [hp_eq] using
      natDegree_add_X_mul_ge_of_hasNonnegCoeffs ha_nonneg hb_nonneg hb0
  have hdeg_lt : b.natDegree < a.natDegree := by
    lia
  have hh_deg : h.natDegree = d := by
    rw [hId_eq]
    calc
      (a + b).natDegree = a.natDegree :=
        natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_lt ha_pos
      _ = d := ha_top
  have hh_nonpos : ∀ r ∈ h.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hIdp.1.2 hh_nonneg
  have hp_split : p = h + t := by
    grind
  have hall_hp : AllComboRealRooted h p := allComboRealRooted_of_prec hIdp
  have hall_ht : AllComboRealRooted h t := by
    intro α β
    have hrew :
        C α * h + C β * t =
          C (α - β) * h + C β * p := by
      grind
    simpa [hrew] using hall_hp (α - β) β
  have ht_ne : t ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0
  have ht_rr : (t ≠ 0 ∧ t.Splits) :=
    ⟨ht_ne, by simpa using hall_ht 0 1⟩
  have ht_root1 : t.IsRoot 1 := by
    dsimp [t]
    simp
  rcases natDegree_eq_or_succ_or_revSucc_of_allComboRealRooted hall_ht hIdp.1.1 ht_ne with
    hsame | htoo_big | hgap
  · have hb_top : b.natDegree = d - 1 := by
      dsimp [t] at hsame
      rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C] at hsame
      lia
    exact
      brandenSolusTheorem26_third_converse_of_top_degree_of_right_top
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hb_top hIdp
  · dsimp [t] at htoo_big
    rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C] at htoo_big
    lia
  · have hall_th : AllComboRealRooted t h := by
      intro α β
      simpa [add_comm, add_left_comm, add_assoc] using hall_ht β α
    have hprec_or : Prec t h ∨ Prec h t :=
      prec_of_allComboRealRooted ht_rr.1 ht_rr.2 hIdp.1.1 hIdp.1.2 hall_th
        (Or.inl hgap)
    have hnot_th : ¬ Prec t h := by
      intro hth
      have h1_le : (1 : ℝ) ≤ 0 :=
        roots_le_of_prec_right hth hh_nonpos 1 ((mem_roots hth.1.1).mpr ht_root1)
      linarith
    rcases hprec_or with hth | hht
    · lia
    · have hbound : h.natDegree ≤ t.natDegree := (natDegree_bounds_of_prec hht).1
      lia

theorem brandenSolusTheorem26_third_equiv_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    (Prec b p ↔ Prec (IdTransform d p) p) := by
  constructor
  · exact
      brandenSolusTheorem26_third_forward_of_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  · exact
      brandenSolusTheorem26_third_converse_of_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top

theorem brandenSolusTheorem26_first_equiv_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (hb0 : b ≠ 0) :
    (Prec b a ↔ Prec a p) := by
  constructor
  · intro hba
    exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).1
  · intro hap
    exact prec_b_component_of_prec_left_of_natDegree_le
      hid.1 ha_nonneg hb_nonneg ha_le hb0 hap

theorem brandenSolusTheorem26_second_equiv_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) :
    (Prec a p ↔ Prec b p) := by
  constructor
  · intro hap
    have hba :
        Prec b a := by
      exact
        (brandenSolusTheorem26_first_equiv_of_natDegree_le
          hd hid ha_nonneg hb_nonneg ha_le hb0).2 hap
    exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).2.1
  · intro hbp
    have hba :
        Prec b a := by
      exact
        (brandenSolusTheorem26_third_equiv_of_natDegree_le
          hd hid ha_nonneg hb_nonneg ha_le ha0 hb0).2 hbp
    exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).1

theorem hasNonnegCoeffs_pair_of_isIdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    HasNonnegCoeffs p ∧ HasNonnegCoeffs (IdTransform d p) := by
  have hp_nonneg : HasNonnegCoeffs p := by
    simpa [hid.1] using ha_nonneg.add (hasNonnegCoeffs_X.mul hb_nonneg)
  have hId_nonneg : HasNonnegCoeffs (IdTransform d p) := by
    rw [idTransform_eq_add_of_isIdDecomposition hd hid]
    exact ha_nonneg.add hb_nonneg
  lia

theorem hasNonnegCoeffs_fPolynomial_pair_of_isIdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    HasNonnegCoeffs (fPolynomial d p) ∧
      HasNonnegCoeffs (RdTransform d (fPolynomial d p)) := by
  rcases hasNonnegCoeffs_pair_of_isIdDecomposition hd hid ha_nonneg hb_nonneg with
    ⟨hp_nonneg, hId_nonneg⟩
  refine ⟨hasNonnegCoeffs_fPolynomial hp_nonneg, ?_⟩
  rw [RdTransform_fPolynomial]
  exact hasNonnegCoeffs_fPolynomial hId_nonneg

theorem hasNonnegCoeffs_pair_of_isRdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hrd : IsRdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    HasNonnegCoeffs p ∧ HasNonnegCoeffs (RdTransform d p) := by
  have hp_nonneg : HasNonnegCoeffs p := by
    simpa [hrd.1] using ha_nonneg.add (hasNonnegCoeffs_X.mul hb_nonneg)
  have hR_nonneg : HasNonnegCoeffs (RdTransform d p) := by
    rw [rdTransform_eq_add_X_add_one_mul_of_isRdDecomposition hd hrd]
    exact ha_nonneg.add (hasNonnegCoeffs_X_add_one.mul hb_nonneg)
  lia

theorem hasNonnegCoeffs_transformed_components_of_isIdDecomposition {d : ℕ} {a b : ℝ[X]}
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    HasNonnegCoeffs (fPolynomial d a) ∧ HasNonnegCoeffs (fPolynomial (d - 1) b) :=
  ⟨hasNonnegCoeffs_fPolynomial ha_nonneg, hasNonnegCoeffs_fPolynomial hb_nonneg⟩

lemma prec_iff_prec_mul_X_add_one_both {f g : ℝ[X]} :
    Prec ((X + 1) * f) ((X + 1) * g) ↔ Prec f g := by
  constructor
  · intro h
    have h' : Prec ((X - C (-1)) * f) ((X - C (-1)) * g) := by
      simp_all
    exact prec_of_prec_mul_X_sub_C_both (-1) h'
  · intro h
    have h' : Prec ((X - C (-1)) * f) ((X - C (-1)) * g) :=
      prec_mul_X_sub_C_both (-1) h
    simp_all

lemma prec_iff_prec_mul_X_add_one_pow_both {n : ℕ} {f g : ℝ[X]} :
    Prec ((X + 1) ^ n * f) ((X + 1) ^ n * g) ↔ Prec f g := by
  induction n with
  | zero =>
      lia
  | succ n ih =>
      have hstep :
          Prec ((X + 1) * ((X + 1) ^ n * f)) ((X + 1) * ((X + 1) ^ n * g)) ↔
            Prec ((X + 1) ^ n * f) ((X + 1) ^ n * g) :=
        prec_iff_prec_mul_X_add_one_both
      grind

/-- Reduced transport target: it is enough to treat the minimal ambient degree
`max u.natDegree v.natDegree`, since larger ambient degrees only add a common
power of `X + 1` to both transformed polynomials. -/
def precFPolynomialTransportMinimalStatement : Prop :=
  ∀ {d : ℕ} {u v : ℝ[X]},
    d = max u.natDegree v.natDegree →
    HasNonnegCoeffs u →
    HasNonnegCoeffs v →
    (Prec (fPolynomial d u) (fPolynomial d v) ↔ Prec u v)

/-- Honest missing transport problem behind Brändén--Solus Theorem 2.6:
the `f`-polynomial transform should preserve the oriented interlacing relation
on nonnegative-coefficient pairs of degree at most `d`. -/
def precFPolynomialTransportStatement : Prop :=
  ∀ {d : ℕ} {u v : ℝ[X]},
    u.natDegree ≤ d →
    v.natDegree ≤ d →
    HasNonnegCoeffs u →
    HasNonnegCoeffs v →
    (Prec (fPolynomial d u) (fPolynomial d v) ↔ Prec u v)

theorem precFPolynomialTransportMinimal : precFPolynomialTransportMinimalStatement := by
  intro d u v hd hu_nonneg hv_nonneg
  constructor
  · intro h
    have hud : u.natDegree ≤ d := by
      simp_all
    have hvd : v.natDegree ≤ d := by
      simp_all
    have hu_rr : (u ≠ 0 ∧ u.Splits) :=
      isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs hud h.1.1 h.1.2 hu_nonneg
    have hv_rr : (v ≠ 0 ∧ v.Splits) :=
      isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs hvd h.2.1.1 h.2.1.2 hv_nonneg
    exact prec_of_prec_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs
      hd hu_rr.1 hu_rr.2 hv_rr.1 hv_rr.2 h hu_nonneg hv_nonneg
  · intro h
    exact prec_fPolynomial_of_prec_of_hasNonnegCoeffs_of_minimal hd h hu_nonneg hv_nonneg

theorem precFPolynomialTransport_of_minimal
    (hminimal : precFPolynomialTransportMinimalStatement) :
    precFPolynomialTransportStatement := by
  intro d u v hud hvd hu_nonneg hv_nonneg
  let m := max u.natDegree v.natDegree
  have hum : u.natDegree ≤ m := le_max_left _ _
  have hvm : v.natDegree ≤ m := le_max_right _ _
  have hmd : m ≤ d := max_le hud hvd
  have hu_pad : fPolynomial d u = (X + 1) ^ (d - m) * fPolynomial m u := by
    simpa [m] using fPolynomial_pad_by_X_add_one_pow hum hmd
  have hv_pad : fPolynomial d v = (X + 1) ^ (d - m) * fPolynomial m v := by
    simpa [m] using fPolynomial_pad_by_X_add_one_pow hvm hmd
  calc
    Prec (fPolynomial d u) (fPolynomial d v)
        ↔ Prec ((X + 1) ^ (d - m) * fPolynomial m u) ((X + 1) ^ (d - m) * fPolynomial m v) := by
              lia
    _ ↔ Prec (fPolynomial m u) (fPolynomial m v) :=
          prec_iff_prec_mul_X_add_one_pow_both
    _ ↔ Prec u v := hminimal (d := m) rfl hu_nonneg hv_nonneg

theorem precFPolynomialTransport : precFPolynomialTransportStatement :=
  precFPolynomialTransport_of_minimal precFPolynomialTransportMinimal

theorem brandenSolusTheorem26_last_equiv_of_precFPolynomialTransport
    (htransport : precFPolynomialTransportStatement)
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    (Prec (IdTransform d p) p ↔
      Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p)) := by
  rcases hasNonnegCoeffs_pair_of_isIdDecomposition hd hid ha_nonneg hb_nonneg with
    ⟨hp_nonneg, hId_nonneg⟩
  rw [RdTransform_fPolynomial]
  exact (htransport
    (u := IdTransform d p) (v := p)
    (IdTransform_natDegree_le hd) hd hId_nonneg hp_nonneg).symm

theorem brandenSolusTheorem26_last_equiv
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    (Prec (IdTransform d p) p ↔
      Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p)) :=
  brandenSolusTheorem26_last_equiv_of_precFPolynomialTransport
    precFPolynomialTransport hd hid ha_nonneg hb_nonneg

private theorem brandenSolusTheorem26_descend_of_lt_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hd2 : 2 ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_lt : a.natDegree < d)
    (hb_lt : b.natDegree < d - 1)
    (hprev :
      ∀ {q a' b' : ℝ[X]},
        q.natDegree ≤ d - 2 →
        IsIdDecomposition (d - 2) q a' b' →
        HasNonnegCoeffs a' →
        HasNonnegCoeffs b' →
        a' ≠ 0 →
        b' ≠ 0 →
        (Prec b' a' ↔ Prec a' q) ∧
        (Prec a' q ↔ Prec b' q) ∧
        (Prec b' q ↔ Prec (IdTransform (d - 2) q) q) ∧
        (Prec (IdTransform (d - 2) q) q ↔
          Prec (RdTransform (d - 2) (fPolynomial (d - 2) q)) (fPolynomial (d - 2) q))) :
    (Prec b a ↔ Prec a p) ∧
    (Prec a p ↔ Prec b p) ∧
    (Prec b p ↔ Prec (IdTransform d p) p) ∧
    (Prec (IdTransform d p) p ↔
      Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p)) := by
  rcases isIdDecomposition_descend_of_lt_top hd2 hid ha_lt hb_lt with
    ⟨a', b', haX, hbX, hpX, hid'⟩
  let q : ℝ[X] := a' + X * b'
  have hidq : IsIdDecomposition (d - 2) q a' b' := by
    lia
  have ha'0 : a' ≠ 0 := by
    simp_all
  have hb'0 : b' ≠ 0 := by
    simp_all
  have ha'_nonneg : HasNonnegCoeffs a' :=
    hasNonnegCoeffs_of_eq_X_mul ha_nonneg haX
  have hb'_nonneg : HasNonnegCoeffs b' :=
    hasNonnegCoeffs_of_eq_X_mul hb_nonneg hbX
  have hXb'deg : (X * b').natDegree ≤ d - 2 := by
    lia
  have hqdeg : q.natDegree ≤ d - 2 := by
    simpa [q] using Polynomial.natDegree_add_le_of_le hidq.2.1 hXb'deg
  have hpair_nonneg :=
    hasNonnegCoeffs_pair_of_isIdDecomposition hqdeg hidq ha'_nonneg hb'_nonneg
  have hq_nonneg : HasNonnegCoeffs q := hpair_nonneg.1
  have hIdq_nonneg : HasNonnegCoeffs (IdTransform (d - 2) q) := hpair_nonneg.2
  have hpX' : p = X * q := by
    lia
  have hIdX : IdTransform d p = X * IdTransform (d - 2) q := by
    calc
      IdTransform d p = IdTransform d (X * q) := by lia
      _ = X * IdTransform (d - 2) q :=
        IdTransform_X_mul_of_natDegree_le_two_pred hd2 hqdeg
  have hsmall := hprev hqdeg hidq ha'_nonneg hb'_nonneg ha'0 hb'0
  rcases hsmall with ⟨hfirst_small, hsecond_small, hthird_small, -⟩
  have hba_transport : Prec b a ↔ Prec b' a' := by
    calc
      Prec b a ↔ Prec (X * b') (X * a') := by lia
      _ ↔ Prec b' a' :=
        (prec_iff_prec_mul_X_both_of_hasNonnegCoeffs hb'_nonneg ha'_nonneg).symm
  have hap_transport : Prec a p ↔ Prec a' q := by
    calc
      Prec a p ↔ Prec (X * a') (X * q) := by lia
      _ ↔ Prec a' q :=
        (prec_iff_prec_mul_X_both_of_hasNonnegCoeffs ha'_nonneg hq_nonneg).symm
  have hbp_transport : Prec b p ↔ Prec b' q := by
    calc
      Prec b p ↔ Prec (X * b') (X * q) := by lia
      _ ↔ Prec b' q :=
        (prec_iff_prec_mul_X_both_of_hasNonnegCoeffs hb'_nonneg hq_nonneg).symm
  have hIdp_transport : Prec (IdTransform d p) p ↔ Prec (IdTransform (d - 2) q) q := by
    calc
      Prec (IdTransform d p) p ↔ Prec (X * IdTransform (d - 2) q) (X * q) := by
        lia
      _ ↔ Prec (IdTransform (d - 2) q) q :=
        (prec_iff_prec_mul_X_both_of_hasNonnegCoeffs hIdq_nonneg hq_nonneg).symm
  refine ⟨?_, ?_, ?_, brandenSolusTheorem26_last_equiv hd hid ha_nonneg hb_nonneg⟩
  · lia
  · lia
  · lia

/-- Naive fully strict translation of Brändén--Solus Theorem 2.6 into the
current `Prec` API.

This exact formulation is false: our `Prec` predicate is reflexive on
real-rooted polynomials and excludes the zero polynomial, so degenerate
decompositions such as `p = 1`, `a = 1`, `b = 0` break the first equivalence.
We keep this definition only so that the counterexample is recorded explicitly
in the library. -/
def brandenSolusTheorem26NaiveStatement : Prop :=
  ∀ {d : ℕ} {p a b : ℝ[X]},
    p.natDegree ≤ d →
    IsIdDecomposition d p a b →
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    (Prec b a ↔ Prec a p) ∧
    (Prec a p ↔ Prec b p) ∧
    (Prec b p ↔ Prec (IdTransform d p) p) ∧
    (Prec (IdTransform d p) p ↔
      Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p))

/-- The naive fully strict `Prec` formulation of Brändén--Solus Theorem 2.6 is
false. The counterexample is the degree-zero decomposition `1 = 1 + X * 0`. -/
theorem not_brandenSolusTheorem26NaiveStatement :
    ¬ brandenSolusTheorem26NaiveStatement := by
  intro h
  have hcase := h (d := 0) (p := (1 : ℝ[X])) (a := (1 : ℝ[X])) (b := 0)
    (by simp)
    (by
      refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> simp [IdTransform])
    (by simpa using hasNonnegCoeffs_one)
    (by simpa using hasNonnegCoeffs_zero)
  rcases hcase with ⟨hba_iff_hap, -, -, -⟩
  have happ : Prec (1 : ℝ[X]) (1 : ℝ[X]) :=
    prec_refl (by simp) (by simp)
  have hnot : ¬ Prec (0 : ℝ[X]) (1 : ℝ[X]) := by
    intro h0
    exact h0.1.1 rfl
  lia

/-- Honest nondegenerate `Prec` target for Brändén--Solus Theorem 2.6.

The extra assumptions `a ≠ 0` and `b ≠ 0` remove the zero-polynomial edge
cases where the paper's strict interlacing language and the current Lean
predicate `Prec` diverge. -/
def brandenSolusTheorem26Statement : Prop :=
  ∀ {d : ℕ} {p a b : ℝ[X]},
    p.natDegree ≤ d →
    IsIdDecomposition d p a b →
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    a ≠ 0 →
    b ≠ 0 →
    (Prec b a ↔ Prec a p) ∧
    (Prec a p ↔ Prec b p) ∧
    (Prec b p ↔ Prec (IdTransform d p) p) ∧
    (Prec (IdTransform d p) p ↔
      Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p))

/-- Reduced frontier for Brändén--Solus Theorem 2.6: after the degree-ordered
and below-top recursive branches, the only genuinely new case is when the
left `I_d`-component occupies the full ambient degree. -/
def brandenSolusTheorem26TopDegreeBoundaryStatement : Prop :=
  ∀ {d : ℕ} {p a b : ℝ[X]},
    p.natDegree ≤ d →
    IsIdDecomposition d p a b →
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    a ≠ 0 →
    b ≠ 0 →
    a.natDegree = d →
    (Prec b a ↔ Prec a p) ∧
    (Prec a p ↔ Prec b p) ∧
    (Prec b p ↔ Prec (IdTransform d p) p) ∧
    (Prec (IdTransform d p) p ↔
      Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p))

/-- Remaining ordered-degree bridge in the already-controlled branch
`a.natDegree ≤ b.natDegree`: upgrading the proved equivalence
`Prec b a ↔ Prec b p` to the desired `Prec b p ↔ Prec (IdTransform d p) p`. -/
def brandenSolusTheorem26OrderedBridgeStatement : Prop :=
  ∀ {d : ℕ} {p a b : ℝ[X]},
    p.natDegree ≤ d →
    IsIdDecomposition d p a b →
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    a ≠ 0 →
    b ≠ 0 →
    a.natDegree ≤ b.natDegree →
    (Prec b p ↔ Prec (IdTransform d p) p)

/-- In the ordered-degree branch `a.natDegree ≤ b.natDegree`, the forward half
of the remaining bridge is already available: once `b` interlaces `p`, the
existing component theorem recovers `b ≺ a`, and the forward Brändén--Solus
implication then yields `IdTransform d p ≺ p`. -/
theorem brandenSolusTheorem26_ordered_bridge_forward_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) :
    Prec b p → Prec (IdTransform d p) p := by
  intro hbp
  have hba : Prec b a := by
    exact
      (brandenSolusTheorem26_third_equiv_of_natDegree_le
        hd hid ha_nonneg hb_nonneg ha_le ha0 hb0).2 hbp
  exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).2.2

/-- Ordered-degree converse bridge: if `a.natDegree ≤ b.natDegree` and
`IdTransform d p ≺ p`, then already `b ≺ p`.

The proof rewrites `p` as `IdTransform d p + (X - 1) * b`, extracts
`b ≺ IdTransform d p` from the shifted pair via the same-degree Obreschkoff
converse, and then sums back to `b ≺ p`. -/
theorem brandenSolusTheorem26_ordered_bridge_converse_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_le : a.natDegree ≤ b.natDegree) :
    Prec (IdTransform d p) p → Prec b p := by
  intro hIdp
  let h : ℝ[X] := IdTransform d p
  let t : ℝ[X] := (X - C (1 : ℝ)) * b
  have hp_eq : p = a + X * b := hid.1
  have hId_eq : h = a + b := by
    simpa [h] using idTransform_eq_add_of_isIdDecomposition hd hid
  have hpair_nonneg := hasNonnegCoeffs_pair_of_isIdDecomposition hd hid ha_nonneg hb_nonneg
  have hp_nonneg : HasNonnegCoeffs p := hpair_nonneg.1
  have hh_nonneg : HasNonnegCoeffs h := by
    lia
  have hh_rr : (h ≠ 0 ∧ h.Splits) := by
    simpa [h] using hIdp.1
  have hp_rr : (p ≠ 0 ∧ p.Splits) := hIdp.2.1
  have ha_pos : HasPosLeadingCoeff a := ha_nonneg.pos_leadingCoeff ha0
  have hb_pos : HasPosLeadingCoeff b := hb_nonneg.pos_leadingCoeff hb0
  have hh_deg : h.natDegree = b.natDegree := by
    rw [hId_eq]
    by_cases hdeg_eq : a.natDegree = b.natDegree
    · calc
        (a + b).natDegree = a.natDegree :=
          natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff hdeg_eq ha_pos hb_pos
        _ = b.natDegree := hdeg_eq
    · have hdeg_lt : a.natDegree < b.natDegree := lt_of_le_of_ne ha_le hdeg_eq
      exact natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hb_pos
  have hh_pos : HasPosLeadingCoeff h := by
    rw [hId_eq]
    by_cases hdeg_eq : a.natDegree = b.natDegree
    · exact hasPosLeadingCoeff_add_of_same_natDegree hdeg_eq ha_pos hb_pos
    · exact hasPosLeadingCoeff_add_of_natDegree_lt_right (lt_of_le_of_ne ha_le hdeg_eq) hb_pos
  have ht_ne : t ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0
  have ht_pos : HasPosLeadingCoeff t := by
    dsimp [t]
    unfold HasPosLeadingCoeff at hb_pos ⊢
    rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul]
    lia
  have hp_split : p = h + t := by
    grind
  have hall_hp : AllComboRealRooted h p := allComboRealRooted_of_prec hIdp
  have hall_ht : AllComboRealRooted h t := by
    intro α β
    have hrew :
        C α * h + C β * t =
          C (α - β) * h + C β * p := by
      grind
    simpa [hrew] using hall_hp (α - β) β
  have ht_rr : (t ≠ 0 ∧ t.Splits) :=
    ⟨ht_ne, by simpa using hall_ht 0 1⟩
  have hb_rr : (b ≠ 0 ∧ b.Splits) := by
    apply isRealRooted_of_dvd ht_rr.1 ht_rr.2 hb0
    refine ⟨X - C (1 : ℝ), ?_⟩
    grind
  have hb_le : ∀ s ∈ b.roots, s ≤ (1 : ℝ) := by
    intro s hs
    have hs0 := roots_nonpos_of_nonneg_coeffs hb_rr.2 hb_nonneg s hs
    linarith
  have hh_le : ∀ s ∈ h.roots, s ≤ (1 : ℝ) := by
    intro s hs
    have hs0 := roots_nonpos_of_nonneg_coeffs hh_rr.2 hh_nonneg s hs
    linarith
  have ht_deg : h.natDegree + 1 = t.natDegree := by
    dsimp [t]
    rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C]
    lia
  have hht_or : Prec h t ∨ Prec t h :=
    prec_of_allComboRealRooted hh_rr.1 hh_rr.2 ht_rr.1 ht_rr.2 hall_ht
      (Or.inl ht_deg)
  have hnot_rev : ¬ Prec t h := by
    intro hth
    have hbounds := natDegree_bounds_of_prec hth
    lia
  have hht : Prec h t := by
    lia
  have hbh : Prec b h :=
    prec_of_prec_mul_X_sub_C_of_sameDegree_of_roots_le (1 : ℝ)
      hht hh_deg.symm hb_pos hh_pos hb_le hh_le
  have hbt : Prec b t :=
    prec_sameDegree_to_prec_mul_X_sub_C_of_roots_le (1 : ℝ)
      (prec_refl hb_rr.1 hb_rr.2) rfl hb_pos hb_pos hb_le hb_le
  have hbp_sum : Prec b [h, t].sum := by
    refine prec_sum_left_of_common_left [h, t] b ?_ hb_pos ?_ ?_
    · simp_all
    · simp_all
    · lia
  simp_all

/-- The ordered-degree converse bridge, packaged as a standalone statement so it
can still be referenced in reduction theorems. This is now proved below. -/
def brandenSolusTheorem26OrderedBridgeConverseStatement : Prop :=
  ∀ {d : ℕ} {p a b : ℝ[X]},
    p.natDegree ≤ d →
    IsIdDecomposition d p a b →
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    a ≠ 0 →
    b ≠ 0 →
    a.natDegree ≤ b.natDegree →
    (Prec (IdTransform d p) p → Prec b p)

/-- The bidirectional ordered-degree bridge reduces to its converse, since the
forward implication is already available from the current library. -/
theorem brandenSolusTheorem26OrderedBridge_of_converse
    (hconverse : brandenSolusTheorem26OrderedBridgeConverseStatement) :
    brandenSolusTheorem26OrderedBridgeStatement := by
  intro d p a b hd hid ha_nonneg hb_nonneg ha0 hb0 ha_le
  constructor
  · exact brandenSolusTheorem26_ordered_bridge_forward_of_natDegree_le
      hd hid ha_nonneg hb_nonneg ha_le ha0 hb0
  · exact hconverse hd hid ha_nonneg hb_nonneg ha0 hb0 ha_le

theorem brandenSolusTheorem26OrderedBridgeConverse :
    brandenSolusTheorem26OrderedBridgeConverseStatement := by
  intro d p a b hd hid ha_nonneg hb_nonneg ha0 hb0 ha_le
  exact brandenSolusTheorem26_ordered_bridge_converse_of_natDegree_le
    hd hid ha_nonneg hb_nonneg ha0 hb0 ha_le

/-- The full nondegenerate Brändén--Solus theorem reduces to the single
top-degree boundary case `a.natDegree = d`, together with the still-missing
ordered-degree bridge `Prec b p ↔ Prec (IdTransform d p) p`. The other
branches are already handled by the degree-ordered lemmas and the recursive
common-`X` descent. -/
theorem brandenSolusTheorem26_of_top_degree_boundary
    (hordered : brandenSolusTheorem26OrderedBridgeStatement)
    (hboundary : brandenSolusTheorem26TopDegreeBoundaryStatement) :
    brandenSolusTheorem26Statement := by
  let P : ℕ → Prop := fun d =>
    ∀ (p a b : ℝ[X]),
      p.natDegree ≤ d →
      IsIdDecomposition d p a b →
      HasNonnegCoeffs a →
      HasNonnegCoeffs b →
      a ≠ 0 →
      b ≠ 0 →
      (Prec b a ↔ Prec a p) ∧
      (Prec a p ↔ Prec b p) ∧
      (Prec b p ↔ Prec (IdTransform d p) p) ∧
      (Prec (IdTransform d p) p ↔
        Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p))
  have hmain : ∀ d, P d := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih p a b hd hid ha_nonneg hb_nonneg ha0 hb0
    have ha_deg : a.natDegree ≤ d := hid.2.1
    have hb_deg : b.natDegree ≤ d - 1 := hid.2.2.1
    by_cases ha_le : a.natDegree ≤ b.natDegree
    · refine ⟨?_, ?_, ?_, brandenSolusTheorem26_last_equiv hd hid ha_nonneg hb_nonneg⟩
      · exact brandenSolusTheorem26_first_equiv_of_natDegree_le
          hd hid ha_nonneg hb_nonneg ha_le hb0
      · exact brandenSolusTheorem26_second_equiv_of_natDegree_le
          hd hid ha_nonneg hb_nonneg ha_le ha0 hb0
      · exact hordered hd hid ha_nonneg hb_nonneg ha0 hb0 ha_le
    · by_cases ha_top : a.natDegree = d
      · exact hboundary hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
      · have ha_lt : a.natDegree < d := lt_of_le_of_ne ha_deg ha_top
        have hb_lt : b.natDegree < d - 1 := by
          lia
        have hd2 : 2 ≤ d := by
          lia
        have hprev :
            ∀ {q a' b' : ℝ[X]},
              q.natDegree ≤ d - 2 →
              IsIdDecomposition (d - 2) q a' b' →
              HasNonnegCoeffs a' →
              HasNonnegCoeffs b' →
              a' ≠ 0 →
              b' ≠ 0 →
              (Prec b' a' ↔ Prec a' q) ∧
              (Prec a' q ↔ Prec b' q) ∧
              (Prec b' q ↔ Prec (IdTransform (d - 2) q) q) ∧
              (Prec (IdTransform (d - 2) q) q ↔
                Prec (RdTransform (d - 2) (fPolynomial (d - 2) q)) (fPolynomial (d - 2) q)) := by
          grind
        exact brandenSolusTheorem26_descend_of_lt_top
          hd hd2 hid ha_nonneg hb_nonneg ha0 hb0 ha_lt hb_lt hprev
  simpa [brandenSolusTheorem26Statement, P] using hmain

/-- Final wrapper in its sharper form: after packaging the already-proved
forward ordered-degree implication, the only remaining abstract inputs are the
top-degree boundary case and the converse half of the ordered bridge. -/
theorem brandenSolusTheorem26_of_ordered_bridge_converse_and_top_degree_boundary
    (hconverse : brandenSolusTheorem26OrderedBridgeConverseStatement)
    (hboundary : brandenSolusTheorem26TopDegreeBoundaryStatement) :
    brandenSolusTheorem26Statement :=
  brandenSolusTheorem26_of_top_degree_boundary
    (brandenSolusTheorem26OrderedBridge_of_converse hconverse)
    hboundary

/-- With the ordered-degree bridge now fully formalized, the only remaining
abstract input for Brändén--Solus Theorem 2.6 is the top-degree boundary case
`a.natDegree = d`. -/
theorem brandenSolusTheorem26_of_top_degree_boundary_only
    (hboundary : brandenSolusTheorem26TopDegreeBoundaryStatement) :
    brandenSolusTheorem26Statement :=
  brandenSolusTheorem26_of_ordered_bridge_converse_and_top_degree_boundary
    brandenSolusTheorem26OrderedBridgeConverse
    hboundary

theorem brandenSolusTheorem26TopDegreeBoundary :
    brandenSolusTheorem26TopDegreeBoundaryStatement := by
  intro d p a b hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      brandenSolusTheorem26_first_equiv_of_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  · exact
      brandenSolusTheorem26_second_equiv_of_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  · exact
      brandenSolusTheorem26_third_equiv_of_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  · exact brandenSolusTheorem26_last_equiv hd hid ha_nonneg hb_nonneg

theorem brandenSolusTheorem26 :
    brandenSolusTheorem26Statement :=
  brandenSolusTheorem26_of_top_degree_boundary_only
    brandenSolusTheorem26TopDegreeBoundary

end
end RealRooted
