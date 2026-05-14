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

set_option linter.style.cdot false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Polynomial Finset

noncomputable section

namespace RealRooted

set_option linter.flexible false in
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
            apply Finset.sum_congr rfl
            intro k hk
            rw [coeff_C_mul, C_mul]
            ring
    _ = C a * ∑ k ∈ Finset.range (d + 1),
          C (p.coeff k) * X ^ k * (X + 1) ^ (d - k) := by
            rw [Finset.mul_sum]

lemma fPolynomial_succ_of_natDegree_le {d : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    fPolynomial (d + 1) p = (X + 1) * fPolynomial d p := by
  unfold fPolynomial
  rw [Finset.sum_range_succ]
  have htop : p.coeff (d + 1) = 0 := by
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (Nat.lt_succ_self d))
  rw [htop]
  simp
  calc
    ∑ k ∈ Finset.range (d + 1),
        C (p.coeff k) * X ^ k * (X + 1) ^ (d + 1 - k)
      = ∑ k ∈ Finset.range (d + 1),
          (X + 1) * (C (p.coeff k) * X ^ k * (X + 1) ^ (d - k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            have hsub : d + 1 - k = (d - k) + 1 := by omega
            rw [hsub, pow_succ]
            ac_rfl
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
      if _h : n ≤ d then C a * X ^ n * (X + 1) ^ (d - n) else 0 := by
  by_cases h : n ≤ d
  · have hn : n ∈ Finset.range (d + 1) := by
      simpa using h
    unfold fPolynomial
    rw [Finset.sum_eq_single n]
    · have hcoeff : (monomial n a).coeff n = a := by
        simp
      rw [hcoeff]
      simp [h]
    · intro k hk hkn
      have hcoeff : (monomial n a).coeff k = 0 := by
        simp [coeff_monomial, mt Eq.symm hkn]
      rw [hcoeff]
      simp
    · intro hnot
      exact (hnot hn).elim
  · unfold fPolynomial
    have hsum :
        ∑ k ∈ Finset.range (d + 1),
          C (((monomial n a).coeff k)) * X ^ k * (X + 1) ^ (d - k) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hklt : k < d + 1 := Finset.mem_range.mp hk
      have hkn : k ≠ n := by
        intro hEq
        exact h (Nat.lt_succ_iff.mp (hEq ▸ hklt))
      have hcoeff : (monomial n a).coeff k = 0 := by
        simp [coeff_monomial, mt Eq.symm hkn]
      rw [hcoeff]
      simp
    simpa [h] using hsum

lemma fPolynomial_natDegree_le (d : ℕ) (h : ℝ[X]) :
    (fPolynomial d h).natDegree ≤ d := by
  unfold fPolynomial
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.range (d + 1))
    (f := fun k => C (h.coeff k) * X ^ k * (X + 1) ^ (d - k)) ?_
  intro k hk
  change (C (h.coeff k) * X ^ k * (X + 1) ^ (d - k)).natDegree ≤ d
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hleft : (C (h.coeff k) * X ^ k).natDegree ≤ k := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le k)
  have hright : ((X + 1) ^ (d - k) : ℝ[X]).natDegree ≤ d - k := by
    rw [show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp]
    exact le_of_eq (Polynomial.natDegree_pow_X_add_C (n := d - k) (r := (1 : ℝ)))
  calc
    (C (h.coeff k) * X ^ k * (X + 1) ^ (d - k)).natDegree
        ≤ k + (d - k) := by
            simpa [mul_assoc] using (Polynomial.natDegree_mul_le_of_le hleft hright)
    _ = d := by omega

lemma coeff_fPolynomial_top (d : ℕ) (h : ℝ[X]) :
    (fPolynomial d h).coeff d = ∑ k ∈ Finset.range (d + 1), h.coeff k := by
  unfold fPolynomial
  rw [Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show C (h.coeff k) * X ^ k = Polynomial.monomial k (h.coeff k) by
    rw [Polynomial.C_mul_X_pow_eq_monomial]]
  have hdk : d = (d - k) + k := by omega
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
  rw [Polynomial.eval_finset_sum]
  rw [Finset.sum_eq_single d]
  · simp
  · intro k hk hkd
    have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hk_lt : k < d := lt_of_le_of_ne hk_le hkd
    have hsub_pos : 0 < d - k := Nat.sub_pos_of_lt hk_lt
    simp [Polynomial.eval_mul, hsub_pos.ne']
  · intro hd_not_mem
    exact (hd_not_mem (Finset.mem_range.mpr (Nat.lt_succ_self d))).elim

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
        ∑ i ∈ Finset.range (h.natDegree + 1), h.coeff i := by
    exact Finset.single_le_sum
      (fun i hi => hh i)
      (Finset.mem_range.mpr (Nat.lt_succ_self _))
  exact lt_of_lt_of_le htop_coeff hle

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
        ∑ i ∈ Finset.range (h.natDegree + 1), h.coeff i * x ^ i := by
    exact Finset.single_le_sum
      (s := Finset.range (h.natDegree + 1))
      (f := fun i => h.coeff i * x ^ i)
      (fun i hi => mul_nonneg (hh i) (pow_nonneg hx.le _))
      (Finset.mem_range.mpr (Nat.lt_succ_self _))
  exact lt_of_lt_of_le htop_term hle

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
    rw [show X * (p + q) = X * p + X * q by ring]
    rw [fPolynomial_add, fPolynomial_add, hp, hq]
    ring
  · intro n a
    by_cases h : n ≤ d
    · have hs : n + 1 ≤ d + 1 := Nat.succ_le_succ h
      have hf : fPolynomial d (monomial n a) = C a * X ^ n * (X + 1) ^ (d - n) := by
        simpa [h] using (fPolynomial_monomial d n a)
      rw [Polynomial.X_mul_monomial, fPolynomial_monomial, hf]
      have hif :
          (if h' : n + 1 ≤ d + 1 then C a * X ^ (n + 1) * (X + 1) ^ (d + 1 - (n + 1)) else 0) =
            C a * X ^ (n + 1) * (X + 1) ^ (d - n) := by
        simp [hs]
      rw [hif]
      ring
    · have hs : ¬ n + 1 ≤ d + 1 := by
        simpa using h
      rw [Polynomial.X_mul_monomial, fPolynomial_monomial]
      rw [show fPolynomial d (monomial n a) = 0 by simpa [h] using (fPolynomial_monomial d n a)]
      simp [hs]

lemma fPolynomial_pad_by_X_add_one_pow {m d : ℕ} {p : ℝ[X]}
    (hm : p.natDegree ≤ m) (hmd : m ≤ d) :
    fPolynomial d p = (X + 1) ^ (d - m) * fPolynomial m p := by
  have hpad : ∀ n : ℕ, fPolynomial (m + n) p = (X + 1) ^ n * fPolynomial m p := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hm' : p.natDegree ≤ m + n := le_trans hm (Nat.le_add_right _ _)
        rw [show m + n.succ = (m + n) + 1 by omega]
        rw [fPolynomial_succ_of_natDegree_le hm', ih]
        simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
  rcases Nat.exists_eq_add_of_le hmd with ⟨n, rfl⟩
  simpa [Nat.add_comm] using hpad n

lemma fPolynomial_X_sub_C_mul_succ (d : ℕ) (r : ℝ) {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    fPolynomial (d + 1) ((X - C r) * p) =
      (C (1 - r) * X - C r) * fPolynomial d p := by
  have hmul : (X - C r) * p = X * p + C (-r) * p := by
    simp [sub_eq_add_neg, add_mul]
  calc
    fPolynomial (d + 1) ((X - C r) * p)
      = fPolynomial (d + 1) (X * p + C (-r) * p) := by
          rw [hmul]
    _ = X * fPolynomial d p + C (-r) * fPolynomial (d + 1) p := by
          rw [fPolynomial_add, fPolynomial_X_mul_succ, fPolynomial_C_mul]
    _ = X * fPolynomial d p + C (-r) * ((X + 1) * fPolynomial d p) := by
          rw [fPolynomial_succ_of_natDegree_le hp]
    _ = (C (1 - r) * X - C r) * fPolynomial d p := by
          have hlin : X - C r * (X + 1) = C (1 - r) * X - C r := by
            calc
              X - C r * (X + 1) = X - (C r * X + C r) := by
                rw [mul_add, mul_one]
              _ = X - C r * X - C r := by
                rw [sub_add_eq_sub_sub]
              _ = (1 - C r) * X - C r := by
                rw [← one_sub_mul]
              _ = C (1 - r) * X - C r := by
                simp
          calc
            X * fPolynomial d p + C (-r) * ((X + 1) * fPolynomial d p)
              = X * fPolynomial d p - C r * ((X + 1) * fPolynomial d p) := by
                  simp [sub_eq_add_neg]
            _ = X * fPolynomial d p - (C r * (X + 1)) * fPolynomial d p := by
                  rw [mul_assoc]
            _ = (X - C r * (X + 1)) * fPolynomial d p := by
                  rw [sub_mul]
            _ = (C (1 - r) * X - C r) * fPolynomial d p := by
                  rw [hlin]

lemma transformedRoot_nonpos {r : ℝ} (hr : r ≤ 0) :
    r / (1 - r) ≤ 0 := by
  have h1r_pos : 0 < 1 - r := by linarith
  have h1r_inv_nonneg : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr h1r_pos.le
  have hmul_nonpos : r * (1 - r)⁻¹ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hr h1r_inv_nonneg
  simpa [div_eq_mul_inv] using hmul_nonpos

/-- Inverse Möbius map to `r ↦ r / (1-r)` on `(-1, ∞)`. -/
def untransformRoot (x : ℝ) : ℝ := x / (1 + x)

lemma untransformRoot_nonpos {x : ℝ} (hx1 : -1 < x) (hx0 : x ≤ 0) :
    untransformRoot x ≤ 0 := by
  have h1x_pos : 0 < 1 + x := by linarith
  have h1x_inv_nonneg : 0 ≤ (1 + x)⁻¹ := inv_nonneg.mpr h1x_pos.le
  simpa [untransformRoot, div_eq_mul_inv] using
    mul_nonpos_of_nonpos_of_nonneg hx0 h1x_inv_nonneg

lemma transformedRoot_untransformRoot {x : ℝ} (hx1 : -1 < x) :
    untransformRoot x / (1 - untransformRoot x) = x := by
  have h1x_ne : 1 + x ≠ 0 := by linarith
  have hden : 1 - x / (1 + x) = (1 : ℝ) / (1 + x) := by
    field_simp [h1x_ne]
    ring
  rw [untransformRoot, hden]
  field_simp [h1x_ne]

lemma untransformRoot_transformedRoot {r : ℝ} (hr : r ≤ 0) :
    untransformRoot (r / (1 - r)) = r := by
  have h1r_ne : 1 - r ≠ 0 := by linarith
  have hden : 1 + r / (1 - r) = (1 : ℝ) / (1 - r) := by
    field_simp [h1r_ne]
    ring
  rw [untransformRoot, hden]
  field_simp [h1r_ne]

lemma eval_fPolynomial_eq_mul_eval_untransform {d : ℕ} {p : ℝ[X]}
    (hd : p.natDegree ≤ d) {x : ℝ} (hx : x ≠ -1) :
    (fPolynomial d p).eval x = (1 + x) ^ d * p.eval (untransformRoot x) := by
  have h1x_ne : 1 + x ≠ 0 := by
    intro h0
    apply hx
    linarith
  unfold fPolynomial
  rw [Polynomial.eval_finset_sum, Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hd)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc
    (C (p.coeff k) * X ^ k * (X + 1) ^ (d - k)).eval x
        = p.coeff k * x ^ k * (x + 1) ^ (d - k) := by
            simp [Polynomial.eval_mul, mul_assoc]
    _ = p.coeff k * x ^ k * (1 + x) ^ (d - k) := by
          rw [add_comm]
    _ = p.coeff k * (x ^ k * (1 + x) ^ (d - k)) := by
          rw [mul_assoc]
    _ = p.coeff k * ((1 + x) ^ d * (untransformRoot x) ^ k) := by
          have hterm :
              (1 + x) ^ d * (untransformRoot x) ^ k = x ^ k * (1 + x) ^ (d - k) := by
            calc
              (1 + x) ^ d * (untransformRoot x) ^ k
                  = (1 + x) ^ d * (x / (1 + x)) ^ k := by
                      simp [untransformRoot]
              _ = (1 + x) ^ d * (x ^ k * ((1 + x) ^ k)⁻¹) := by
                    rw [div_eq_mul_inv, mul_pow, inv_pow]
              _ = x ^ k * ((1 + x) ^ d * ((1 + x) ^ k)⁻¹) := by ring
              _ = x ^ k * (1 + x) ^ (d - k) := by
                    rw [← pow_sub₀ (1 + x) h1x_ne hk_le]
          rw [← hterm]
    _ = (1 + x) ^ d * (p.coeff k * (untransformRoot x) ^ k) := by
          ring

lemma neg_one_lt_transformedRoot {r : ℝ} (hr : r ≤ 0) :
    -1 < r / (1 - r) := by
  have h1r_pos : 0 < 1 - r := by linarith
  have hmul : (-1 : ℝ) * (1 - r) < r := by linarith
  exact (lt_div_iff₀ h1r_pos).2 hmul

lemma untransformRoot_mono_of_neg_one_lt {x y : ℝ}
    (hxy : x ≤ y) (hx1 : -1 < x) :
    untransformRoot x ≤ untransformRoot y := by
  have hy1 : -1 < y := lt_of_lt_of_le hx1 hxy
  have h1x_pos : 0 < 1 + x := by linarith
  have h1y_pos : 0 < 1 + y := by linarith
  rw [untransformRoot, untransformRoot, div_le_div_iff₀ h1x_pos h1y_pos]
  nlinarith

lemma transformedRoot_mono_of_nonpos {r s : ℝ}
    (hrs : r ≤ s) (hs : s ≤ 0) :
    r / (1 - r) ≤ s / (1 - s) := by
  have h1r_pos : 0 < 1 - r := by linarith
  have h1s_pos : 0 < 1 - s := by linarith
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
        exact transformedRoot_mono_of_nonpos (hrs.1 z hz) (hnonpos z (by simp [hz]))
      · exact pairwise_map_transformedRoot_of_nonpos hrs.2 (fun z hz => hnonpos z (by simp [hz]))

lemma listInterlaces_map_transformedRoot_of_nonpos :
    ∀ {ss rs : List ℝ}, ListInterlaces ss rs →
      (∀ r ∈ rs, r ≤ 0) →
      ListInterlaces (ss.map (fun r : ℝ => r / (1 - r)))
        (rs.map (fun r : ℝ => r / (1 - r)))
  | [], [], _, _ => by simp [ListInterlaces]
  | [], [_], _, _ => by simp [ListInterlaces]
  | s :: ss, r₁ :: r₂ :: rs, h, hnonpos => by
      rcases h with ⟨hr₁s, hsr₂, htail⟩
      have hs_nonpos : s ≤ 0 := le_trans hsr₂ (hnonpos r₂ (by simp))
      refine ⟨?_, ?_, ?_⟩
      · exact transformedRoot_mono_of_nonpos hr₁s hs_nonpos
      · exact transformedRoot_mono_of_nonpos hsr₂ (hnonpos r₂ (by simp))
      · exact listInterlaces_map_transformedRoot_of_nonpos htail
          (fun r hr => hnonpos r (by simp [hr]))
  | [], _ :: _ :: _, h, _ => by simp [ListInterlaces] at h
  | _ :: _, [], h, _ => by simp [ListInterlaces] at h
  | _ :: _ :: _, [_], h, _ => by simp [ListInterlaces] at h

lemma listAlternates_map_transformedRoot_of_nonpos :
    ∀ {ss rs : List ℝ}, ListAlternates ss rs →
      (∀ r ∈ rs, r ≤ 0) →
      ListAlternates (ss.map (fun r : ℝ => r / (1 - r)))
        (rs.map (fun r : ℝ => r / (1 - r)))
  | [], [], _, _ => by simp [ListAlternates]
  | s :: ss, r :: rs, h, hnonpos => by
      rcases h with ⟨hsr, htail⟩
      exact ⟨transformedRoot_mono_of_nonpos hsr (hnonpos r (by simp)),
        listInterlaces_map_transformedRoot_of_nonpos htail (fun t ht => hnonpos t (by simp [ht]))⟩
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
      · exact pairwise_map_untransformRoot_of_neg_one_lt hrs.2 (fun z hz => hgt z (by simp [hz]))

lemma listInterlaces_map_untransformRoot_of_neg_one_lt :
    ∀ {ss rs : List ℝ}, ListInterlaces ss rs →
      (∀ s ∈ ss, -1 < s) →
      (∀ r ∈ rs, -1 < r) →
      ListInterlaces (ss.map untransformRoot) (rs.map untransformRoot)
  | [], [], _, _, _ => by simp [ListInterlaces]
  | [], [_], _, _, _ => by simp [ListInterlaces]
  | s :: ss, r₁ :: r₂ :: rs, h, hss, hrs => by
      rcases h with ⟨hr₁s, hsr₂, htail⟩
      refine ⟨?_, ?_, ?_⟩
      · exact untransformRoot_mono_of_neg_one_lt hr₁s (hrs r₁ (by simp))
      · exact untransformRoot_mono_of_neg_one_lt hsr₂ (hss s (by simp))
      · exact listInterlaces_map_untransformRoot_of_neg_one_lt htail
          (fun s hs => hss s (by simp [hs]))
          (fun r hr => hrs r (by simp [hr]))
  | [], _ :: _ :: _, h, _, _ => by simp [ListInterlaces] at h
  | _ :: _, [], h, _, _ => by simp [ListInterlaces] at h
  | _ :: _ :: _, [_], h, _, _ => by simp [ListInterlaces] at h

lemma listAlternates_map_untransformRoot_of_neg_one_lt :
    ∀ {ss rs : List ℝ}, ListAlternates ss rs →
      (∀ s ∈ ss, -1 < s) →
      (∀ r ∈ rs, -1 < r) →
      ListAlternates (ss.map untransformRoot) (rs.map untransformRoot)
  | [], [], _, _, _ => by simp [ListAlternates]
  | s :: ss, r :: rs, h, hss, hrs => by
      rcases h with ⟨hsr, htail⟩
      exact ⟨untransformRoot_mono_of_neg_one_lt hsr (hss s (by simp)),
        listInterlaces_map_untransformRoot_of_neg_one_lt htail
          (fun t ht => hss t (by simp [ht]))
          (fun t ht => hrs t (by simp [ht]))⟩
  | [], _ :: _, h, _, _ => by simp [ListAlternates] at h
  | _ :: _, [], h, _, _ => by simp [ListAlternates] at h

lemma transformedLinearFactor_eq_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    C (1 - r) * X - C r = C (1 - r) * (X - C (r / (1 - r))) := by
  have h1r_pos : 0 < 1 - r := by linarith
  have h1r_ne : 1 - r ≠ 0 := ne_of_gt h1r_pos
  have hmul : (1 - r) * (r / (1 - r)) = r := by
    field_simp [h1r_ne]
  calc
    C (1 - r) * X - C r
        = C (1 - r) * X - C ((1 - r) * (r / (1 - r))) := by rw [hmul]
    _ = C (1 - r) * X - C (1 - r) * C (r / (1 - r)) := by simp [C_mul]
    _ = C (1 - r) * (X - C (r / (1 - r))) := by rw [mul_sub]

lemma transformedLinearFactor_eq {r : ℝ} (h1r_ne : 1 - r ≠ 0) :
    C (1 - r) * X - C r = C (1 - r) * (X - C (r / (1 - r))) := by
  have hmul : (1 - r) * (r / (1 - r)) = r := by
    field_simp [h1r_ne]
  calc
    C (1 - r) * X - C r
        = C (1 - r) * X - C ((1 - r) * (r / (1 - r))) := by rw [hmul]
    _ = C (1 - r) * X - C (1 - r) * C (r / (1 - r)) := by simp [C_mul]
    _ = C (1 - r) * (X - C (r / (1 - r))) := by rw [mul_sub]

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
    exact sub_ne_zero.mpr (by simpa [eq_comm] using hr1)
  rw [fPolynomial_X_sub_C_mul_succ d r hp, transformedLinearFactor_eq h1r_ne]

lemma fPolynomial_natDegree_factor_of_isRoot
    {p : ℝ[X]} (hp : IsRealRooted p) (hpnn : HasNonnegCoeffs p) {r : ℝ}
    (hr : p.IsRoot r) :
    ∃ q, p = (X - C r) * q ∧
      fPolynomial p.natDegree p =
        C (1 - r) * (X - C (r / (1 - r))) * fPolynomial q.natDegree q := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr
  have hp_ne : p ≠ 0 := hp.1
  have hq' : p = (X - C r) * q := by
    simpa [mul_comm] using hq
  have hq_ne : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hq
    exact hp_ne hq
  have hr_mem : r ∈ p.roots := (mem_roots hp.1).mpr hr
  have hr_nonpos : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hp hpnn r hr_mem
  have hdeg_eq : p.natDegree = q.natDegree + 1 := by
    simpa [Nat.add_comm] using
      (show p.natDegree = 1 + q.natDegree by
        rw [hq', natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C])
  refine ⟨q, hq', ?_⟩
  rw [hdeg_eq, hq']
  simpa using fPolynomial_X_sub_C_mul_succ' q.natDegree hr_nonpos (p := q) le_rfl

lemma isRoot_transformedRoot_fPolynomial_natDegree_of_isRoot
    {p : ℝ[X]} (hp : IsRealRooted p) (hpnn : HasNonnegCoeffs p) {r : ℝ}
    (hr : p.IsRoot r) :
    (fPolynomial p.natDegree p).IsRoot (r / (1 - r)) := by
  rcases fPolynomial_natDegree_factor_of_isRoot hp hpnn hr with ⟨q, _hq, hfac⟩
  rw [Polynomial.IsRoot.def, hfac]
  simp [Polynomial.eval_mul]

lemma isRoot_transformedRoot_fPolynomial_of_isRoot
    {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d)
    (hp : IsRealRooted p) (hpnn : HasNonnegCoeffs p) {r : ℝ}
    (hr : p.IsRoot r) :
    (fPolynomial d p).IsRoot (r / (1 - r)) := by
  have hroot_min :
      (fPolynomial p.natDegree p).IsRoot (r / (1 - r)) :=
    isRoot_transformedRoot_fPolynomial_natDegree_of_isRoot hp hpnn hr
  rw [Polynomial.IsRoot.def, fPolynomial_pad_by_X_add_one_pow (m := p.natDegree) le_rfl hd]
  rw [Polynomial.eval_mul]
  have hroot_eval :
      (fPolynomial p.natDegree p).eval (r / (1 - r)) = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot_min
  simp [hroot_eval]

lemma isRoot_neg_one_fPolynomial_of_natDegree_lt
    {d : ℕ} {p : ℝ[X]} (hpd : p.natDegree < d) :
    (fPolynomial d p).IsRoot (-1) := by
  rw [Polynomial.IsRoot.def, eval_neg_one_fPolynomial]
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hpd]

lemma not_isRoot_neg_one_fPolynomial_of_natDegree_eq_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]} (hdeg : p.natDegree = d)
    (hpnn : HasNonnegCoeffs p) (hp0 : p ≠ 0) :
    ¬ (fPolynomial d p).IsRoot (-1) := by
  rw [Polynomial.IsRoot.def, eval_neg_one_fPolynomial]
  have hcoeff_ne : p.coeff d ≠ 0 := by
    have hcoeff_eq : p.coeff d = p.leadingCoeff := by
      simpa [hdeg] using (coeff_natDegree (p := p))
    rw [hcoeff_eq]
    exact ne_of_gt (hpnn.pos_leadingCoeff hp0)
  have hpow_ne : ((-1 : ℝ) ^ d) ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  intro hroot
  have hzero : p.coeff d * (-1 : ℝ) ^ d = 0 := by
    simpa using hroot
  rcases mul_eq_zero.mp hzero with hcoeff0 | hpow0
  · exact hcoeff_ne hcoeff0
  · exact hpow_ne hpow0

private lemma hasPosLeadingCoeff_of_X_sub_C_mul {q : ℝ[X]} {r : ℝ}
    (h : HasPosLeadingCoeff ((X - C r) * q)) :
    HasPosLeadingCoeff q := by
  unfold HasPosLeadingCoeff at h ⊢
  simpa [Polynomial.leadingCoeff_mul, leadingCoeff_X_sub_C] using h

private lemma hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
    {p q : ℝ[X]}
    (hp : IsRealRooted p) (hpnn : HasNonnegCoeffs p)
    (hq : IsRealRooted q) (hq_pos : HasPosLeadingCoeff q)
    (hqp : q ∣ p) :
    HasNonnegCoeffs q := by
  refine (hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hq).mpr ?_
  refine ⟨hq_pos, ?_⟩
  intro r hr
  have hrq : q.IsRoot r := (mem_roots hq.1).mp hr
  have hrp : p.IsRoot r := IsRoot.of_dvd hqp hrq
  exact roots_nonpos_of_nonneg_coeffs hp hpnn r ((mem_roots hp.1).mpr hrp)

private lemma isRealRooted_transformed_linear {r : ℝ} (hr : r ≤ 0) :
    IsRealRooted (C (1 - r) * X - C r) := by
  have h1r_pos : 0 < 1 - r := by linarith
  have h1r_ne : 1 - r ≠ 0 := ne_of_gt h1r_pos
  have hmul : (1 - r) * (r / (1 - r)) = r := by
    field_simp [h1r_ne]
  have hfac :
      C (1 - r) * X - C r =
        C (1 - r) * (X - C (r / (1 - r))) := by
    calc
      C (1 - r) * X - C r
          = C (1 - r) * X - C ((1 - r) * (r / (1 - r))) := by rw [hmul]
      _ = C (1 - r) * X - C (1 - r) * C (r / (1 - r)) := by
            simp [C_mul]
      _ = C (1 - r) * (X - C (r / (1 - r))) := by
            rw [mul_sub]
  rw [hfac]
  exact isRealRooted_C_mul (isRealRooted_X_sub_C (r / (1 - r))) h1r_ne

/-- The Brändén--Solus `f`-polynomial transform preserves real-rootedness on
nonnegative-coefficient inputs of degree at most `d`. -/
theorem isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ d)
    (hp : IsRealRooted p) (hpnn : HasNonnegCoeffs p) :
    IsRealRooted (fPolynomial d p) := by
  induction d generalizing p with
  | zero =>
      have hpC : p = C (p.coeff 0) := by
        simpa using (Polynomial.eq_C_of_natDegree_le_zero hpdeg)
      rw [hpC]
      have hfp : fPolynomial 0 (C (p.coeff 0)) = C (p.coeff 0) := by
        simp [fPolynomial]
      rw [hfp]
      rw [hpC] at hp
      exact hp
  | succ d ih =>
      by_cases hpd : p.natDegree ≤ d
      · rw [fPolynomial_succ_of_natDegree_le hpd]
        have hX1 : IsRealRooted (X + 1 : ℝ[X]) := by
          simpa using (isRealRooted_X_sub_C (-1 : ℝ))
        exact isRealRooted_mul hX1 (ih hpd hp hpnn)
      · have hpdeg_eq : p.natDegree = d + 1 := by
          omega
        have hroots_pos : 0 < p.roots.card := by
          rw [hp.2, hpdeg_eq]
          exact Nat.succ_pos d
        obtain ⟨r, hr_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
        have hr_root : p.IsRoot r := (mem_roots hp.1).mp hr_mem
        have hr_nonpos : r ≤ 0 :=
          roots_nonpos_of_nonneg_coeffs hp hpnn r hr_mem
        obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr_root
        have hq' : p = (X - C r) * q := by
          simpa [mul_comm] using hq
        have hq_dvd : q ∣ p := ⟨X - C r, by simpa [mul_comm] using hq⟩
        have hq_ne : q ≠ 0 := by
          intro hq0
          rw [hq0, mul_zero] at hq
          exact hp.1 hq
        have hq_rr : IsRealRooted q := isRealRooted_of_dvd hp hq_ne hq_dvd
        have hp_pos : HasPosLeadingCoeff p := hpnn.pos_leadingCoeff hp.1
        have hq_pos : HasPosLeadingCoeff q := by
          apply hasPosLeadingCoeff_of_X_sub_C_mul (r := r)
          simpa [hq'] using hp_pos
        have hq_nonneg : HasNonnegCoeffs q :=
          hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
            hp hpnn hq_rr hq_pos hq_dvd
        have hqdeg : q.natDegree ≤ d := by
          have hmuldeg : p.natDegree = 1 + q.natDegree := by
            rw [hq', natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
          omega
        rw [hq', fPolynomial_X_sub_C_mul_succ d r hqdeg]
        exact isRealRooted_mul (isRealRooted_transformed_linear hr_nonpos)
          (ih hqdeg hq_rr hq_nonneg)

theorem roots_fPolynomial_natDegree_eq_map_of_isRealRooted_of_hasNonnegCoeffs
    {p : ℝ[X]} (hp : IsRealRooted p) (hpnn : HasNonnegCoeffs p) :
    (fPolynomial p.natDegree p).roots =
      p.roots.map (fun r : ℝ => r / (1 - r)) := by
  have hP :
      ∀ n (p : ℝ[X]), p.natDegree = n → IsRealRooted p → HasNonnegCoeffs p →
        (fPolynomial p.natDegree p).roots =
          p.roots.map (fun r : ℝ => r / (1 - r)) := by
    intro n
    exact Nat.strong_induction_on n (fun n ih =>
      show ∀ (p : ℝ[X]), p.natDegree = n → IsRealRooted p → HasNonnegCoeffs p →
        (fPolynomial p.natDegree p).roots =
          p.roots.map (fun r : ℝ => r / (1 - r)) from by
        intro p hpdeg hp hpnn
        by_cases hn : n = 0
        · have hp0 : p.natDegree = 0 := by simpa [hn] using hpdeg
          have hpC : p = C (p.coeff 0) := by
            simpa [hp0] using
              (Polynomial.eq_C_of_natDegree_le_zero (show p.natDegree ≤ 0 by omega))
          have hcoeff0_ne : p.coeff 0 ≠ 0 := by
            intro h0
            rw [hpC, h0] at hp
            exact hp.1 (by simp)
          rw [hpC]
          simp [fPolynomial, hcoeff0_ne]
        · have hroots_pos : 0 < p.roots.card := by
            rw [hp.2, hpdeg]
            omega
          obtain ⟨r, hr_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
          have hr_root : p.IsRoot r := (mem_roots hp.1).mp hr_mem
          obtain ⟨q, hq', hfac⟩ := fPolynomial_natDegree_factor_of_isRoot hp hpnn hr_root
          have hq_dvd : q ∣ p := ⟨X - C r, by simpa [mul_comm] using hq'⟩
          have hq_ne : q ≠ 0 := by
            intro hq0
            rw [hq0, mul_zero] at hq'
            exact hp.1 hq'
          have hr_nonpos : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hp hpnn r hr_mem
          have hq_rr : IsRealRooted q := isRealRooted_of_dvd hp hq_ne hq_dvd
          have hp_pos : HasPosLeadingCoeff p := hpnn.pos_leadingCoeff hp.1
          have hq_pos : HasPosLeadingCoeff q := by
            apply hasPosLeadingCoeff_of_X_sub_C_mul (r := r)
            simpa [hq'] using hp_pos
          have hq_nonneg : HasNonnegCoeffs q :=
            hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
              hp hpnn hq_rr hq_pos hq_dvd
          have hmuldeg : n = q.natDegree + 1 := by
            rw [← hpdeg, hq', natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
            omega
          have hqdeg_lt : q.natDegree < n := by
            omega
          have hqdeg_eq : q.natDegree = n - 1 := by omega
          have ihq :
              (fPolynomial q.natDegree q).roots =
                q.roots.map (fun s : ℝ => s / (1 - s)) :=
            ih q.natDegree hqdeg_lt q rfl hq_rr hq_nonneg
          have h1r_ne : 1 - r ≠ 0 := by linarith
          have hqf_rr :
              IsRealRooted (fPolynomial q.natDegree q) :=
            isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs le_rfl hq_rr hq_nonneg
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
                  rw [ihq]
            _ = ({r} : Multiset ℝ).map (fun s : ℝ => s / (1 - s)) +
                  q.roots.map (fun s : ℝ => s / (1 - s)) := by
                  simp
            _ = (({r} : Multiset ℝ) + q.roots).map (fun s : ℝ => s / (1 - s)) := by
                  simp
            _ = p.roots.map (fun s : ℝ => s / (1 - s)) := by
                  rw [hp_roots])
  exact hP p.natDegree p rfl hp hpnn

theorem roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d)
    (hp : IsRealRooted p) (hpnn : HasNonnegCoeffs p) :
    (fPolynomial d p).roots =
      Multiset.replicate (d - p.natDegree) (-1) +
        p.roots.map (fun r : ℝ => r / (1 - r)) := by
  let n := p.natDegree
  have hpad : fPolynomial d p = (X + 1) ^ (d - n) * fPolynomial n p := by
    simpa [n] using fPolynomial_pad_by_X_add_one_pow (m := n) (p := p) le_rfl hd
  have hfp_rr :
      IsRealRooted (fPolynomial n p) :=
    isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs le_rfl hp hpnn
  have hpow_ne : (X + 1 : ℝ[X]) ^ (d - n) ≠ 0 := by
    exact pow_ne_zero _ (by simpa [sub_eq_add_neg, add_comm] using (X_sub_C_ne_zero (-1 : ℝ)))
  have hroots_pow : ((X + 1 : ℝ[X]) ^ (d - n)).roots = Multiset.replicate (d - n) (-1) := by
    calc
      ((X + 1 : ℝ[X]) ^ (d - n)).roots = ((X - C (-1) : ℝ[X]) ^ (d - n)).roots := by
        simp [sub_eq_add_neg, add_comm]
      _ = (d - n) • ({-1} : Multiset ℝ) := by
        rw [roots_pow, roots_X_sub_C]
      _ = Multiset.replicate (d - n) (-1) := by
        rw [Multiset.nsmul_singleton]
  rw [hpad, roots_mul (mul_ne_zero hpow_ne hfp_rr.1), hroots_pow,
    roots_fPolynomial_natDegree_eq_map_of_isRealRooted_of_hasNonnegCoeffs hp hpnn]

private theorem isRealRooted_of_fPolynomial_natDegree_roots_gt_neg_one
    {p : ℝ[X]}
    (hfpdeg : (fPolynomial p.natDegree p).natDegree = p.natDegree)
    (hfp : IsRealRooted (fPolynomial p.natDegree p))
    (hgt : ∀ x ∈ (fPolynomial p.natDegree p).roots, -1 < x) :
    IsRealRooted p := by
  have hP :
      ∀ n : ℕ, ∀ p : ℝ[X],
        p.natDegree = n →
        (fPolynomial n p).natDegree = n →
        IsRealRooted (fPolynomial n p) →
        (∀ x ∈ (fPolynomial n p).roots, -1 < x) →
        IsRealRooted p := by
    intro n
    exact Nat.strong_induction_on n (fun n ih p hpdeg hqdeg hq_rr hq_gt => by
      have hp0 : p ≠ 0 := by
        intro hpz
        rw [hpz, fPolynomial_zero] at hq_rr
        exact hq_rr.1 rfl
      by_cases hn : n = 0
      · exact isRealRooted_of_deg_zero hp0 (by simpa [hpdeg] using hn)
      · have hroots_pos : 0 < (fPolynomial n p).roots.card := by
          rw [hq_rr.2, hqdeg]
          omega
        obtain ⟨x, hx_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
        have hx_root : (fPolynomial n p).IsRoot x := (mem_roots hq_rr.1).mp hx_mem
        have hx_gt : -1 < x := hq_gt x hx_mem
        have hx_ne : x ≠ -1 := by linarith
        let r : ℝ := untransformRoot x
        have hr_root : p.IsRoot r := by
          rw [Polynomial.IsRoot.def] at hx_root ⊢
          rw [eval_fPolynomial_eq_mul_eval_untransform (d := n) (p := p)
            (by simp [hpdeg]) hx_ne] at hx_root
          have hpow_ne : (1 + x) ^ n ≠ 0 := by
            exact pow_ne_zero _ (by linarith)
          exact (mul_eq_zero.mp hx_root).resolve_left hpow_ne
        obtain ⟨u, hu_dvd⟩ := dvd_iff_isRoot.mpr hr_root
        have hpu : p = (X - C r) * u := by
          simpa [mul_comm] using hu_dvd
        have hu0 : u ≠ 0 := by
          intro huz
          apply hp0
          rw [hpu, huz, mul_zero]
        have hudeg_succ : p.natDegree = u.natDegree + 1 := by
          simpa [Nat.add_comm] using
            (show p.natDegree = 1 + u.natDegree by
              rw [hpu, natDegree_mul (X_sub_C_ne_zero r) hu0, natDegree_X_sub_C])
        have hu_lt : u.natDegree < n := by
          omega
        have h1r_ne : 1 - r ≠ 0 := by
          intro hzero
          have h1x_ne : 1 + x ≠ 0 := by linarith
          dsimp [r, untransformRoot] at hzero
          field_simp [h1x_ne] at hzero
          linarith
        have hq_fac0 :
            fPolynomial n p =
              (C (1 - r) * X - C r) * fPolynomial u.natDegree u := by
          have hdeg_eq : n = u.natDegree + 1 := by omega
          rw [hdeg_eq, hpu]
          simpa using fPolynomial_X_sub_C_mul_succ u.natDegree r (p := u) le_rfl
        have hq_fac :
            fPolynomial n p =
              (X - C x) * (C (1 - r) * fPolynomial u.natDegree u) := by
          calc
            fPolynomial n p
                = (C (1 - r) * X - C r) * fPolynomial u.natDegree u := hq_fac0
            _ = (C (1 - r) * (X - C (r / (1 - r)))) * fPolynomial u.natDegree u := by
                  rw [transformedLinearFactor_eq h1r_ne]
            _ = (C (1 - r) * (X - C x)) * fPolynomial u.natDegree u := by
                  rw [transformedRoot_untransformRoot (x := x) hx_gt]
            _ = (X - C x) * (C (1 - r) * fPolynomial u.natDegree u) := by
                  ac_rfl
        have hscaled_ne : C (1 - r) * fPolynomial u.natDegree u ≠ 0 := by
          intro hzero
          apply hq_rr.1
          rw [hq_fac, hzero, mul_zero]
        have hscaled_rr : IsRealRooted (C (1 - r) * fPolynomial u.natDegree u) := by
          apply isRealRooted_of_dvd hq_rr hscaled_ne
          refine ⟨X - C x, ?_⟩
          simpa [mul_assoc, mul_left_comm, mul_comm] using hq_fac
        have hfu0 : fPolynomial u.natDegree u ≠ 0 := by
          intro hzero
          apply hscaled_ne
          simp [hzero, h1r_ne]
        have hfu_rr : IsRealRooted (fPolynomial u.natDegree u) := by
          apply isRealRooted_of_dvd hscaled_rr hfu0
          refine ⟨C (1 - r), ?_⟩
          simp [mul_assoc, mul_left_comm, mul_comm]
        have hfu_deg : (fPolynomial u.natDegree u).natDegree = u.natDegree := by
          have htmp : n = 1 + (C (1 - r) * fPolynomial u.natDegree u).natDegree := by
            rw [← hqdeg, hq_fac, natDegree_mul (X_sub_C_ne_zero x) hscaled_ne, natDegree_X_sub_C]
          rw [natDegree_C_mul h1r_ne] at htmp
          omega
        have hgt_u : ∀ y ∈ (fPolynomial u.natDegree u).roots, -1 < y := by
          intro y hy
          have hy_scaled : y ∈ (C (1 - r) * fPolynomial u.natDegree u).roots := by
            rw [roots_C_mul _ h1r_ne]
            simpa using hy
          have hy_root :
              (C (1 - r) * fPolynomial u.natDegree u).IsRoot y :=
            (mem_roots hscaled_ne).mp hy_scaled
          have hy_mem_q : y ∈ (fPolynomial n p).roots := by
            have hdiv :
                C (1 - r) * fPolynomial u.natDegree u ∣ fPolynomial n p := by
              refine ⟨X - C x, ?_⟩
              simpa [mul_assoc, mul_left_comm, mul_comm] using hq_fac
            exact (mem_roots hq_rr.1).mpr (IsRoot.of_dvd hdiv hy_root)
          exact hq_gt y hy_mem_q
        have hu_rr : IsRealRooted u :=
          ih u.natDegree hu_lt u rfl hfu_deg hfu_rr hgt_u
        rw [hpu]
        exact isRealRooted_mul (isRealRooted_X_sub_C r) hu_rr)
  exact hP p.natDegree p rfl hfpdeg hfp hgt

lemma root_gt_neg_one_of_mem_roots_fPolynomial_natDegree_of_isRealRooted_of_hasNonnegCoeffs
    {p : ℝ[X]} (hfp : IsRealRooted (fPolynomial p.natDegree p))
    (hpnn : HasNonnegCoeffs p)
    {x : ℝ} (hx : x ∈ (fPolynomial p.natDegree p).roots) :
    -1 < x := by
  have hp0 : p ≠ 0 := by
    intro hpz
    rw [hpz, fPolynomial_zero] at hfp
    exact hfp.1 rfl
  by_cases hxm1 : x = -1
  · subst hxm1
    exfalso
    exact not_isRoot_neg_one_fPolynomial_of_natDegree_eq_of_hasNonnegCoeffs rfl hpnn hp0
      ((mem_roots hfp.1).mp hx)
  · by_cases hxlt : x < -1
    · exfalso
      have hx_root : (fPolynomial p.natDegree p).IsRoot x := (mem_roots hfp.1).mp hx
      rw [Polynomial.IsRoot.def] at hx_root
      have hux_pos : 0 < untransformRoot x := by
        have h1x_neg : 1 + x < 0 := by linarith
        have hx_neg : x < 0 := by linarith
        have hdiv_pos : 0 < x / (1 + x) := div_pos_of_neg_of_neg hx_neg h1x_neg
        simpa [untransformRoot] using hdiv_pos
      have hpx_pos : 0 < p.eval (untransformRoot x) :=
        eval_pos_of_hasNonnegCoeffs_of_pos hpnn hp0 hux_pos
      rw [eval_fPolynomial_eq_mul_eval_untransform (d := p.natDegree) (p := p)
        le_rfl hxm1] at hx_root
      have hpow_ne : (1 + x) ^ p.natDegree ≠ 0 := by
        exact pow_ne_zero _ (by linarith)
      exact hpx_pos.ne' ((mul_eq_zero.mp hx_root).resolve_left hpow_ne)
    · have hx_ge : -1 ≤ x := by linarith
      exact lt_of_le_of_ne hx_ge (by simpa [eq_comm] using hxm1)

theorem isRealRooted_of_isRealRooted_fPolynomial_natDegree_of_hasNonnegCoeffs
    {p : ℝ[X]} (hfp : IsRealRooted (fPolynomial p.natDegree p))
    (hpnn : HasNonnegCoeffs p) :
    IsRealRooted p := by
  have hp0 : p ≠ 0 := by
    intro hpz
    rw [hpz, fPolynomial_zero] at hfp
    exact hfp.1 rfl
  have hfpdeg : (fPolynomial p.natDegree p).natDegree = p.natDegree :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero le_rfl hpnn hp0
  have hgt : ∀ x ∈ (fPolynomial p.natDegree p).roots, -1 < x := by
    intro x hx
    exact root_gt_neg_one_of_mem_roots_fPolynomial_natDegree_of_isRealRooted_of_hasNonnegCoeffs
      hfp hpnn hx
  exact
    isRealRooted_of_fPolynomial_natDegree_roots_gt_neg_one hfpdeg hfp hgt

theorem isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]} (hpd : p.natDegree ≤ d)
    (hfp : IsRealRooted (fPolynomial d p))
    (hpnn : HasNonnegCoeffs p) :
    IsRealRooted p := by
  have hmin0 : fPolynomial p.natDegree p ≠ 0 := by
    intro hzero
    apply hfp.1
    rw [fPolynomial_pad_by_X_add_one_pow (m := p.natDegree) (p := p) le_rfl hpd, hzero, mul_zero]
  have hdiv : fPolynomial p.natDegree p ∣ fPolynomial d p := by
    refine ⟨(X + 1) ^ (d - p.natDegree), ?_⟩
    rw [fPolynomial_pad_by_X_add_one_pow (m := p.natDegree) (p := p) le_rfl hpd]
    ac_rfl
  have hmin_rr : IsRealRooted (fPolynomial p.natDegree p) :=
    isRealRooted_of_dvd hfp hmin0 hdiv
  exact isRealRooted_of_isRealRooted_fPolynomial_natDegree_of_hasNonnegCoeffs hmin_rr hpnn

theorem prec_fPolynomial_of_prec_of_hasNonnegCoeffs_of_minimal
    {d : ℕ} {u v : ℝ[X]}
    (hd : d = max u.natDegree v.natDegree)
    (h : Prec u v)
    (hu_nonneg : HasNonnegCoeffs u)
    (hv_nonneg : HasNonnegCoeffs v) :
    Prec (fPolynomial d u) (fPolynomial d v) := by
  let φ := fun r : ℝ => r / (1 - r)
  rcases h with ⟨hu_rr, hv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud : u.natDegree ≤ d := by simp [hd]
  have hvd : v.natDegree ≤ d := by simp [hd]
  have hfu_rr : IsRealRooted (fPolynomial d u) :=
    isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hud hu_rr hu_nonneg
  have hfv_rr : IsRealRooted (fPolynomial d v) :=
    isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hvd hv_rr hv_nonneg
  have hss_nonpos : ∀ s ∈ ss, s ≤ 0 := by
    intro s hs
    have hs_mem : s ∈ u.roots := by
      rw [← hss_eq]
      exact hs
    exact roots_nonpos_of_nonneg_coeffs hu_rr hu_nonneg s hs_mem
  have hrs_nonpos : ∀ r ∈ rs, r ≤ 0 := by
    intro r hr
    have hr_mem : r ∈ v.roots := by
      rw [← hrs_eq]
      exact hr
    exact roots_nonpos_of_nonneg_coeffs hv_rr hv_nonneg r hr_mem
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
          rw [← Multiset.coe_card, hss_eq, hu_rr.2]
        have hlen_deg_v : (r₁ :: rest).length = v.natDegree := by
          rw [← Multiset.coe_card, hrs_eq, hv_rr.2]
        have hud_pad : d - u.natDegree = 1 := by omega
        have hvd_pad : d - v.natDegree = 0 := by omega
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
                      rw [hss_map_eq]
              _ = Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := by
                      rw [hud_pad]
                      simp
          calc
            (↑((-1) :: ss.map φ) : Multiset ℝ)
                = Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := hleft_multiset
            _ = (fPolynomial d u).roots := by
                    symm
                    simpa [φ] using
                      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
                        hud hu_rr hu_nonneg
        have hright_eq : (↑((r₁ :: rest).map φ) : Multiset ℝ) = (fPolynomial d v).roots := by
          calc
            (↑((r₁ :: rest).map φ) : Multiset ℝ) = v.roots.map φ := by
                simpa [φ] using hrs_map_eq
            _ = (fPolynomial d v).roots := by
                symm
                simpa [φ, hvd_pad] using
                  roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
                    hvd hv_rr hv_nonneg
        refine ⟨hfu_rr, hfv_rr, (-1) :: ss.map φ, (r₁ :: rest).map φ,
          hleft_sorted, hrs_map_sorted, hleft_eq, hright_eq, Or.inr ?_⟩
        refine ⟨by simp [hlen], ?_⟩
        simpa [φ] using
          listAlternates_neg_one_cons_map_of_listInterlaces_of_nonpos
            (ss := ss) (r₁ := r₁) (rs := rest) hint hrs_nonpos
  · have hlen_deg_u : ss.length = u.natDegree := by
      rw [← Multiset.coe_card, hss_eq, hu_rr.2]
    have hlen_deg_v : rs.length = v.natDegree := by
      rw [← Multiset.coe_card, hrs_eq, hv_rr.2]
    have hud_pad : d - u.natDegree = 0 := by omega
    have hvd_pad : d - v.natDegree = 0 := by omega
    have hleft_eq : (↑(ss.map φ) : Multiset ℝ) = (fPolynomial d u).roots := by
      calc
        (↑(ss.map φ) : Multiset ℝ) = u.roots.map φ := by simpa [φ] using hss_map_eq
        _ = (fPolynomial d u).roots := by
            symm
            simpa [φ, hud_pad] using
              roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
                hud hu_rr hu_nonneg
    have hright_eq : (↑(rs.map φ) : Multiset ℝ) = (fPolynomial d v).roots := by
      calc
        (↑(rs.map φ) : Multiset ℝ) = v.roots.map φ := by simpa [φ] using hrs_map_eq
        _ = (fPolynomial d v).roots := by
            symm
            simpa [φ, hvd_pad] using
              roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
                hvd hv_rr hv_nonneg
    refine ⟨hfu_rr, hfv_rr, ss.map φ, rs.map φ,
      hss_map_sorted, hrs_map_sorted, hleft_eq, hright_eq, Or.inr ?_⟩
    refine ⟨by simp [hlen], ?_⟩
    simpa [φ] using listAlternates_map_transformedRoot_of_nonpos halt hrs_nonpos

theorem prec_of_prec_fPolynomial_of_sameDegree_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {u v : ℝ[X]}
    (hud : u.natDegree = d) (hvd : v.natDegree = d)
    (hu_rr : IsRealRooted u) (hv_rr : IsRealRooted v)
    (h : Prec (fPolynomial d u) (fPolynomial d v))
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    Prec u v := by
  let φ := fun r : ℝ => r / (1 - r)
  rcases h with ⟨hfu_rr, hfv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud_le : u.natDegree ≤ d := by simp [hud]
  have hvd_le : v.natDegree ≤ d := by simp [hvd]
  have hfu_deg : (fPolynomial d u).natDegree = d := by
    exact fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hud_le hu_nonneg hu_rr.1
  have hfv_deg : (fPolynomial d v).natDegree = d := by
    exact fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hvd_le hv_nonneg hv_rr.1
  have hss_len : ss.length = d := by
    rw [← Multiset.coe_card, hss_eq, hfu_rr.2, hfu_deg]
  have hrs_len : rs.length = d := by
    rw [← Multiset.coe_card, hrs_eq, hfv_rr.2, hfv_deg]
  have hfu_roots :
      (fPolynomial d u).roots = u.roots.map φ := by
    simpa [φ, hud] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hud_le hu_rr hu_nonneg
  have hfv_roots :
      (fPolynomial d v).roots = v.roots.map φ := by
    simpa [φ, hvd] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hvd_le hv_rr hv_nonneg
  have hss_eq_map : (↑ss : Multiset ℝ) = u.roots.map φ := by
    rw [hss_eq, hfu_roots]
  have hrs_eq_map : (↑rs : Multiset ℝ) = v.roots.map φ := by
    rw [hrs_eq, hfv_roots]
  have hss_gt_neg_one : ∀ s ∈ ss, -1 < s := by
    intro s hs
    have hs_mem : s ∈ (fPolynomial d u).roots := by
      rw [← hss_eq]
      exact hs
    rw [hfu_roots] at hs_mem
    rcases Multiset.mem_map.mp hs_mem with ⟨r, hr, rfl⟩
    exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr hu_nonneg r hr)
  have hrs_gt_neg_one : ∀ r ∈ rs, -1 < r := by
    intro r hr
    have hr_mem : r ∈ (fPolynomial d v).roots := by
      rw [← hrs_eq]
      exact hr
    rw [hfv_roots] at hr_mem
    rcases Multiset.mem_map.mp hr_mem with ⟨s, hs, rfl⟩
    exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hv_rr hv_nonneg s hs)
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
            simp [Multiset.map_map, Function.comp, φ]
      _ = u.roots.map (fun r : ℝ => r) := by
            refine Multiset.map_congr rfl ?_
            intro r hr
            simp [φ, untransformRoot_transformedRoot
              (roots_nonpos_of_nonneg_coeffs hu_rr hu_nonneg r hr)]
      _ = u.roots := by simp
  have hrs'_eq : (↑(rs.map untransformRoot) : Multiset ℝ) = v.roots := by
    have hmap :
        (↑(rs.map untransformRoot) : Multiset ℝ) = (v.roots.map φ).map untransformRoot := by
      simpa [φ] using congrArg (fun t : Multiset ℝ => t.map untransformRoot) hrs_eq_map
    calc
      (↑(rs.map untransformRoot) : Multiset ℝ)
          = (v.roots.map φ).map untransformRoot := hmap
      _ = v.roots.map (fun r : ℝ => untransformRoot (φ r)) := by
            simp [Multiset.map_map, Function.comp, φ]
      _ = v.roots.map (fun r : ℝ => r) := by
            refine Multiset.map_congr rfl ?_
            intro r hr
            simp [φ, untransformRoot_transformedRoot
              (roots_nonpos_of_nonneg_coeffs hv_rr hv_nonneg r hr)]
      _ = v.roots := by simp
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · exfalso
    omega
  · refine ⟨hu_rr, hv_rr, ss.map untransformRoot, rs.map untransformRoot,
      hss'_sorted, hrs'_sorted, hss'_eq, hrs'_eq, Or.inr ?_⟩
    refine ⟨by simpa using hlen, ?_⟩
    exact listAlternates_map_untransformRoot_of_neg_one_lt halt hss_gt_neg_one hrs_gt_neg_one

theorem prec_of_prec_fPolynomial_of_succDegree_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {u v : ℝ[X]}
    (hud : u.natDegree + 1 = d) (hvd : v.natDegree = d)
    (hu_rr : IsRealRooted u) (hv_rr : IsRealRooted v)
    (h : Prec (fPolynomial d u) (fPolynomial d v))
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    Prec u v := by
  let φ := fun r : ℝ => r / (1 - r)
  rcases h with ⟨hfu_rr, hfv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud_le : u.natDegree ≤ d := by omega
  have hvd_le : v.natDegree ≤ d := by simp [hvd]
  have hud_pad : d - u.natDegree = 1 := by omega
  have hvd_pad : d - v.natDegree = 0 := by omega
  have hd_pos : 0 < d := by
    have : 0 < u.natDegree + 1 := Nat.succ_pos _
    omega
  have hfu_deg : (fPolynomial d u).natDegree = d := by
    exact fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hud_le hu_nonneg hu_rr.1
  have hfv_deg : (fPolynomial d v).natDegree = d := by
    exact fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hvd_le hv_nonneg hv_rr.1
  have hss_len : ss.length = d := by
    rw [← Multiset.coe_card, hss_eq, hfu_rr.2, hfu_deg]
  have hrs_len : rs.length = d := by
    rw [← Multiset.coe_card, hrs_eq, hfv_rr.2, hfv_deg]
  have hfu_roots :
      (fPolynomial d u).roots = ({-1} : Multiset ℝ) + u.roots.map φ := by
    simpa [φ, hud_pad] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hud_le hu_rr hu_nonneg
  have hfv_roots :
      (fPolynomial d v).roots = v.roots.map φ := by
    simpa [φ, hvd_pad] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hvd_le hv_rr hv_nonneg
  have hss_eq_full : (↑ss : Multiset ℝ) = ({-1} : Multiset ℝ) + u.roots.map φ := by
    rw [hss_eq, hfu_roots]
  have hrs_eq_map : (↑rs : Multiset ℝ) = v.roots.map φ := by
    rw [hrs_eq, hfv_roots]
  cases ss with
  | nil =>
      simp at hss_len
      omega
  | cons s ss' =>
      have hs_ge_neg_one : -1 ≤ s := by
        have hs_mem : s ∈ (↑(s :: ss') : Multiset ℝ) := by simp
        rw [hss_eq_full] at hs_mem
        rcases Multiset.mem_add.mp hs_mem with hs | hs
        · have hs' : s = -1 := by simpa using hs
          exact le_of_eq hs'.symm
        · rcases Multiset.mem_map.mp hs with ⟨r, hr, rfl⟩
          exact le_of_lt <|
            neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr hu_nonneg r hr)
      have hs_eq : s = -1 := by
        have hminus_mem : (-1 : ℝ) ∈ s :: ss' := by
          have hminus_mem' : (-1 : ℝ) ∈ (↑(s :: ss') : Multiset ℝ) := by
            rw [hss_eq_full]
            simp
          simpa using hminus_mem'
        rcases List.mem_cons.mp hminus_mem with hs | hs_tail
        · exact hs.symm
        · have hs_le_neg_one : s ≤ -1 := List.rel_of_pairwise_cons hss_sorted hs_tail
          linarith
      have hss_tail_eq : (↑ss' : Multiset ℝ) = u.roots.map φ := by
        have hcons :
            ({-1} : Multiset ℝ) + (↑ss' : Multiset ℝ) =
              ({-1} : Multiset ℝ) + u.roots.map φ := by
          simpa [hs_eq] using hss_eq_full
        exact add_left_cancel hcons
      have hss_tail_sorted : ss'.Pairwise (· ≤ ·) := hss_sorted.tail
      have hss_tail_gt_neg_one : ∀ x ∈ ss', -1 < x := by
        intro x hx
        have hx_mem : x ∈ (↑ss' : Multiset ℝ) := by simpa using hx
        rw [hss_tail_eq] at hx_mem
        rcases Multiset.mem_map.mp hx_mem with ⟨r, hr, rfl⟩
        exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr hu_nonneg r hr)
      have hrs_gt_neg_one : ∀ x ∈ rs, -1 < x := by
        intro x hx
        have hx_mem : x ∈ (↑rs : Multiset ℝ) := by simpa using hx
        rw [hrs_eq_map] at hx_mem
        rcases Multiset.mem_map.mp hx_mem with ⟨r, hr, rfl⟩
        exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hv_rr hv_nonneg r hr)
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
                simp [Multiset.map_map, Function.comp, φ]
          _ = u.roots.map (fun r : ℝ => r) := by
                refine Multiset.map_congr rfl ?_
                intro r hr
                simp [φ, untransformRoot_transformedRoot
                  (roots_nonpos_of_nonneg_coeffs hu_rr hu_nonneg r hr)]
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
                simp [Multiset.map_map, Function.comp, φ]
          _ = v.roots.map (fun r : ℝ => r) := by
                refine Multiset.map_congr rfl ?_
                intro r hr
                simp [φ, untransformRoot_transformedRoot
                  (roots_nonpos_of_nonneg_coeffs hv_rr hv_nonneg r hr)]
          _ = v.roots := by simp
      rcases hshape with ⟨hlen, _⟩ | ⟨hlen, halt⟩
      · exfalso
        omega
      · cases rs with
        | nil =>
            simp at hrs_len
            omega
        | cons r rs' =>
            have hint : ListInterlaces ss' (r :: rs') := by
              have hhalt : -1 ≤ r ∧ ListInterlaces ss' (r :: rs') := by
                simpa [hs_eq, ListAlternates] using halt
              exact hhalt.2
            refine ⟨hu_rr, hv_rr, ss'.map untransformRoot, (r :: rs').map untransformRoot,
              hss'_sorted, hrs'_sorted, hss'_eq, hrs'_eq, Or.inl ?_⟩
            refine ⟨?_, ?_⟩
            · have hlen' : ss'.length + 1 = (r :: rs').length := by
                simpa [hs_eq] using hlen
              simpa using hlen'
            · exact listInterlaces_map_untransformRoot_of_neg_one_lt
                hint hss_tail_gt_neg_one hrs_gt_neg_one

private theorem not_prec_fPolynomial_of_right_degree_lt_of_sameDegree_left
    {d : ℕ} {u v : ℝ[X]}
    (hud : u.natDegree = d) (hvd : v.natDegree < d)
    (hu_rr : IsRealRooted u) (hv_rr : IsRealRooted v)
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    ¬ Prec (fPolynomial d u) (fPolynomial d v) := by
  let φ := fun r : ℝ => r / (1 - r)
  intro h
  rcases h with ⟨hfu_rr, hfv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud_le : u.natDegree ≤ d := by simp [hud]
  have hvd_le : v.natDegree ≤ d := le_of_lt hvd
  have hd_pos : 0 < d := by omega
  have hfu_deg : (fPolynomial d u).natDegree = d := by
    exact fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hud_le hu_nonneg hu_rr.1
  have hfv_deg : (fPolynomial d v).natDegree = d := by
    exact fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hvd_le hv_nonneg hv_rr.1
  have hss_len : ss.length = d := by
    rw [← Multiset.coe_card, hss_eq, hfu_rr.2, hfu_deg]
  have hrs_len : rs.length = d := by
    rw [← Multiset.coe_card, hrs_eq, hfv_rr.2, hfv_deg]
  have hud_pad : d - u.natDegree = 0 := by omega
  have hfu_roots :
      (fPolynomial d u).roots = u.roots.map φ := by
    simpa [φ, hud_pad] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hud_le hu_rr hu_nonneg
  have hss_gt_neg_one : ∀ x ∈ ss, -1 < x := by
    intro x hx
    have hx_mem : x ∈ (fPolynomial d u).roots := by
      rw [← hss_eq]
      exact hx
    rw [hfu_roots] at hx_mem
    rcases Multiset.mem_map.mp hx_mem with ⟨r, hr, rfl⟩
    exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr hu_nonneg r hr)
  have hminus_mem : (-1 : ℝ) ∈ rs := by
    have hminus_mem' : (-1 : ℝ) ∈ (fPolynomial d v).roots := by
      exact (mem_roots hfv_rr.1).2 (isRoot_neg_one_fPolynomial_of_natDegree_lt hvd)
    rw [← hrs_eq] at hminus_mem'
    simpa using hminus_mem'
  cases rs with
  | nil =>
      simp at hrs_len
      omega
  | cons r rs' =>
      have hfv_roots :
          (fPolynomial d v).roots =
            Multiset.replicate (d - v.natDegree) (-1) + v.roots.map φ := by
        simpa [φ] using
          roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
            hvd_le hv_rr hv_nonneg
      have hr_ge_neg_one : -1 ≤ r := by
        have hr_mem : r ∈ (fPolynomial d v).roots := by
          rw [← hrs_eq]
          simp
        rw [hfv_roots] at hr_mem
        rcases Multiset.mem_add.mp hr_mem with hr | hr
        · have hr' : r = -1 := (Multiset.mem_replicate.mp hr).2
          exact le_of_eq hr'.symm
        · rcases Multiset.mem_map.mp hr with ⟨s, hs, rfl⟩
          exact le_of_lt <|
            neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hv_rr hv_nonneg s hs)
      have hr_eq : r = -1 := by
        rcases List.mem_cons.mp hminus_mem with hr | hr_tail
        · exact hr.symm
        · have hr_le_neg_one : r ≤ -1 := List.rel_of_pairwise_cons hrs_sorted hr_tail
          linarith
      cases ss with
      | nil =>
          simp at hss_len
          omega
      | cons s ss' =>
          rcases hshape with ⟨hlen, _⟩ | ⟨hlen, halt⟩
          · exfalso
            omega
          · have hs_le_r : s ≤ r := by
              have hhalt : s ≤ r ∧ ListInterlaces ss' (r :: rs') := by
                simpa [ListAlternates] using halt
              exact hhalt.1
            have hs_gt_neg_one : -1 < s := hss_gt_neg_one s (by simp)
            linarith

private theorem not_prec_fPolynomial_of_left_degree_le_sub_two_of_right_full
    {d : ℕ} {u v : ℝ[X]}
    (hud : u.natDegree + 2 ≤ d) (hvd : v.natDegree = d)
    (hu_rr : IsRealRooted u) (hv_rr : IsRealRooted v)
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    ¬ Prec (fPolynomial d u) (fPolynomial d v) := by
  let φ := fun r : ℝ => r / (1 - r)
  intro h
  rcases h with ⟨hfu_rr, hfv_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hud_le : u.natDegree ≤ d := by omega
  have hvd_le : v.natDegree ≤ d := by simp [hvd]
  have hd_pos : 0 < d := by omega
  have hfu_deg : (fPolynomial d u).natDegree = d := by
    exact fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hud_le hu_nonneg hu_rr.1
  have hfv_deg : (fPolynomial d v).natDegree = d := by
    exact fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hvd_le hv_nonneg hv_rr.1
  have hss_len : ss.length = d := by
    rw [← Multiset.coe_card, hss_eq, hfu_rr.2, hfu_deg]
  have hrs_len : rs.length = d := by
    rw [← Multiset.coe_card, hrs_eq, hfv_rr.2, hfv_deg]
  have hud_pad_two : 2 ≤ d - u.natDegree := by omega
  have hfu_roots :
      (fPolynomial d u).roots =
        Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := by
    simpa [φ] using
      roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
        hud_le hu_rr hu_nonneg
  have hss_ge_neg_one : ∀ x ∈ ss, -1 ≤ x := by
    intro x hx
    have hx_mem : x ∈ (fPolynomial d u).roots := by
      rw [← hss_eq]
      exact hx
    rw [hfu_roots] at hx_mem
    rcases Multiset.mem_add.mp hx_mem with hx | hx
    · have hx' : x = -1 := (Multiset.mem_replicate.mp hx).2
      exact le_of_eq hx'.symm
    · rcases Multiset.mem_map.mp hx with ⟨r, hr, rfl⟩
      exact le_of_lt <|
        neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hu_rr hu_nonneg r hr)
  have hminus_mem : (-1 : ℝ) ∈ ss := by
    have hminus_mem' : (-1 : ℝ) ∈ (fPolynomial d u).roots := by
      rw [hfu_roots]
      exact Multiset.mem_add.mpr <| Or.inl <|
        Multiset.mem_replicate.mpr ⟨by omega, rfl⟩
    rw [← hss_eq] at hminus_mem'
    simpa using hminus_mem'
  cases ss with
  | nil =>
      simp at hss_len
      omega
  | cons s ss' =>
      have hss_eq_full :
          (↑(s :: ss') : Multiset ℝ) =
            Multiset.replicate (d - u.natDegree) (-1) + u.roots.map φ := by
        rw [hss_eq, hfu_roots]
      have hs_eq : s = -1 := by
        have hs_ge_neg_one : -1 ≤ s := hss_ge_neg_one s (by simp)
        rcases List.mem_cons.mp hminus_mem with hs | hs_tail
        · exact hs.symm
        · have hs_le_neg_one : s ≤ -1 := List.rel_of_pairwise_cons hss_sorted hs_tail
          linarith
      have hkpos : 0 < d - u.natDegree := by omega
      have hrep :
          Multiset.replicate (d - u.natDegree) (-1) =
            ({-1} : Multiset ℝ) + Multiset.replicate (d - u.natDegree - 1) (-1) := by
        rw [show d - u.natDegree = 1 + (d - u.natDegree - 1) by omega, Multiset.replicate_add]
        simp
      have hss_tail_eq :
          (↑ss' : Multiset ℝ) =
            Multiset.replicate (d - u.natDegree - 1) (-1) + u.roots.map φ := by
        have hcons :
            ({-1} : Multiset ℝ) + (↑ss' : Multiset ℝ) =
              ({-1} : Multiset ℝ) +
                (Multiset.replicate (d - u.natDegree - 1) (-1) + u.roots.map φ) := by
          simpa [hs_eq, hrep, add_assoc] using hss_eq_full
        exact add_left_cancel hcons
      have hminus_mem_tail : (-1 : ℝ) ∈ ss' := by
        have hminus_mem_tail' : (-1 : ℝ) ∈ (↑ss' : Multiset ℝ) := by
          rw [hss_tail_eq]
          exact Multiset.mem_add.mpr <| Or.inl <|
            Multiset.mem_replicate.mpr ⟨by omega, rfl⟩
        simpa using hminus_mem_tail'
      have hfv_roots :
          (fPolynomial d v).roots = v.roots.map φ := by
        have hvd_pad : d - v.natDegree = 0 := by omega
        simpa [φ, hvd_pad] using
          roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
            hvd_le hv_rr hv_nonneg
      have hrs_gt_neg_one : ∀ x ∈ rs, -1 < x := by
        intro x hx
        have hx_mem : x ∈ (fPolynomial d v).roots := by
          rw [← hrs_eq]
          exact hx
        rw [hfv_roots] at hx_mem
        rcases Multiset.mem_map.mp hx_mem with ⟨r, hr, rfl⟩
        exact neg_one_lt_transformedRoot (roots_nonpos_of_nonneg_coeffs hv_rr hv_nonneg r hr)
      cases rs with
      | nil =>
          simp at hrs_len
          omega
      | cons r rs' =>
          rcases hshape with ⟨hlen, _⟩ | ⟨hlen, halt⟩
          · exfalso
            omega
          · have hhalt : -1 ≤ r ∧ ListInterlaces ss' (r :: rs') := by
              simpa [hs_eq, ListAlternates] using halt
            have hr_gt_neg_one : -1 < r := hrs_gt_neg_one r (by simp)
            have hr_le_neg_one : r ≤ -1 :=
              listInterlaces_all_ge ss' rs' r hhalt.2 (-1) hminus_mem_tail
            linarith

theorem prec_of_prec_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {u v : ℝ[X]}
    (hd : d = max u.natDegree v.natDegree)
    (hu_rr : IsRealRooted u) (hv_rr : IsRealRooted v)
    (h : Prec (fPolynomial d u) (fPolynomial d v))
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    Prec u v := by
  have hud : u.natDegree ≤ d := by simp [hd]
  have hvd : v.natDegree ≤ d := by simp [hd]
  by_cases hv_eq : v.natDegree = d
  · by_cases hu_eq : u.natDegree = d
    · exact prec_of_prec_fPolynomial_of_sameDegree_of_isRealRooted_of_hasNonnegCoeffs
        hu_eq hv_eq hu_rr hv_rr h hu_nonneg hv_nonneg
    · have hu_lt : u.natDegree < d := lt_of_le_of_ne hud hu_eq
      by_cases hu_succ : u.natDegree + 1 = d
      · exact prec_of_prec_fPolynomial_of_succDegree_of_isRealRooted_of_hasNonnegCoeffs
          hu_succ hv_eq hu_rr hv_rr h hu_nonneg hv_nonneg
      · have hu_two : u.natDegree + 2 ≤ d := by omega
        exact False.elim <|
          not_prec_fPolynomial_of_left_degree_le_sub_two_of_right_full
            hu_two hv_eq hu_rr hv_rr hu_nonneg hv_nonneg h
  · have hv_lt : v.natDegree < d := lt_of_le_of_ne hvd hv_eq
    have hu_eq : u.natDegree = d := by omega
    exact False.elim <|
      not_prec_fPolynomial_of_right_degree_lt_of_sameDegree_left
        hu_eq hv_lt hu_rr hv_rr hu_nonneg hv_nonneg h

theorem prec_iff_prec_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {u v : ℝ[X]}
    (hd : d = max u.natDegree v.natDegree)
    (hu_rr : IsRealRooted u) (hv_rr : IsRealRooted v)
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    (Prec (fPolynomial d u) (fPolynomial d v) ↔ Prec u v) := by
  constructor
  · intro h
    exact prec_of_prec_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs
      hd hu_rr hv_rr h hu_nonneg hv_nonneg
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
  have hcombo_rr : IsRealRooted (C lam * u + C μ * v) :=
    PosComboRealRooted.of_prec h hu_pos hv_pos hlam hμ
  have hcombo_nonneg : HasNonnegCoeffs (C lam * u + C μ * v) := by
    exact (nonnegCoeffs_C_mul hlam.le hu_nonneg).add (nonnegCoeffs_C_mul hμ.le hv_nonneg)
  have hcombo_deg : (C lam * u + C μ * v).natDegree ≤ d := by
    have hud' : (C lam * u).natDegree ≤ d := by
      rw [Polynomial.natDegree_C_mul hlam.ne']
      exact hud
    have hvd' : (C μ * v).natDegree ≤ d := by
      rw [Polynomial.natDegree_C_mul hμ.ne']
      exact hvd
    simpa using Polynomial.natDegree_add_le_of_le hud' hvd'
  simpa [fPolynomial_add, fPolynomial_C_mul] using
    isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs
      hcombo_deg hcombo_rr hcombo_nonneg

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
    (IdTransform d p).natDegree ≤ d := by
  exact (Polynomial.natDegree_reflect_le (N := d) (p := p)).trans <| max_le le_rfl hd

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
      cases Nat.not_lt_zero _ hd
  | succ n =>
      simpa using (IdTransform_succ (d := n) (p := p) hp)

lemma IdTransform_X_mul_of_natDegree_le_pred {d : ℕ} (hd : 0 < d) {p : ℝ[X]}
    (hp : p.natDegree ≤ d - 1) :
    IdTransform d (X * p) = IdTransform (d - 1) p := by
  cases d with
  | zero =>
      cases Nat.not_lt_zero _ hd
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
      omega
  | succ d =>
      cases d with
      | zero =>
          have hpdeg : p.natDegree ≤ 0 := by omega
          have hp0 : p = 0 := by
            calc
              p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hpdeg
              _ = 0 := by
                    simp [coeff_zero_eq_zero_of_IdTransform_fixed_of_natDegree_lt hfix hdeg]
          refine ⟨0, ?_, by simp [IdTransform]⟩
          simp [hp0]
      | succ n =>
          have hroot0 : p.IsRoot 0 :=
            isRoot_zero_of_IdTransform_fixed_of_natDegree_lt hfix hdeg
          obtain ⟨q, hq0⟩ := dvd_iff_isRoot.mpr hroot0
          have hq : p = X * q := by
            simpa using hq0
          have hqdeg : q.natDegree ≤ n := by
            by_cases hqz : q = 0
            · simp [hqz]
            · rw [hq, natDegree_X_mul hqz] at hdeg
              omega
          have hqdeg' : q.natDegree ≤ n + 1 := le_trans hqdeg (Nat.le_succ _)
          have hstep1 : IdTransform (n + 2) (X * q) = IdTransform (n + 1) q := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (IdTransform_X_mul_succ (d := n + 1) (p := q) hqdeg')
          have hstep2 : IdTransform (n + 1) q = X * IdTransform n q := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (IdTransform_of_natDegree_le_pred (d := n + 1) (Nat.succ_pos _) hqdeg)
          have hXeq : X * IdTransform n q = X * q := by
            calc
              X * IdTransform n q = IdTransform (n + 1) q := by rw [hstep2]
              _ = IdTransform (n + 2) (X * q) := by rw [hstep1]
              _ = X * q := by simpa [hq] using hfix
          refine ⟨q, hq, ?_⟩
          simpa using mul_left_cancel₀ X_ne_zero hXeq

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
      omega
  have hb'deg : b'.natDegree ≤ d - 3 := by
    by_cases hb'0 : b' = 0
    · simp [hb'0]
    · rw [hbX, natDegree_X_mul hb'0] at hb_lt
      omega
  have hpX : p = X * (a' + X * b') := by
    rw [hp_eq, haX, hbX]
    ring
  have hsub : (d - 2) - 1 = d - 3 := by
    omega
  refine ⟨a', b', haX, hbX, hpX, ?_⟩
  refine ⟨rfl, ha'deg, ?_, hfixA', ?_⟩
  · simpa [hsub] using hb'deg
  · simpa [hsub] using hfixB'

lemma IdTransform_X_mul_of_natDegree_le_two_pred {d : ℕ} {p : ℝ[X]}
    (hd : 2 ≤ d) (hp : p.natDegree ≤ d - 2) :
    IdTransform d (X * p) = X * IdTransform (d - 2) p := by
  calc
    IdTransform d (X * p) = IdTransform (d - 1) p := by
      exact IdTransform_X_mul_of_natDegree_le_pred (by omega) (by omega)
    _ = X * IdTransform (d - 2) p := by
      exact IdTransform_of_natDegree_le_pred (d := d - 1) (by omega) (by omega)

theorem prec_iff_prec_mul_X_both_of_hasNonnegCoeffs {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec f g ↔ Prec (X * f) (X * g) := by
  constructor
  · intro h
    have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs h.1 hfnn
    have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs h.2.1 hgnn
    exact (prec_iff_prec_mul_X_both_of_roots_nonpos hf_nonpos hg_nonpos).1 h
  · intro h
    have hf_rr : IsRealRooted f := isRealRooted_of_X_mul h.1
    have hg_rr : IsRealRooted g := isRealRooted_of_X_mul h.2.1
    have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf_rr hfnn
    have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hg_rr hgnn
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
  omega

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
  omega

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
    calc
      (X - 1) * (idDecompositionAFormula d p + X * idDecompositionBFormula d p)
          = (X - 1) * idDecompositionAFormula d p +
              X * ((X - 1) * idDecompositionBFormula d p) := hstep
      _ = (X * IdTransform d p - p) + X * (p - IdTransform d p) := by rw [hA, hB]
      _ = (X - 1) * p := by ring
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
  calc
    p = ((X - C (1 : ℝ)) * p) /ₘ (X - C (1 : ℝ)) := hright_cancel.symm
    _ = ((X - C (1 : ℝ)) * (idDecompositionAFormula d p + X * idDecompositionBFormula d p)) /ₘ
          (X - C (1 : ℝ)) := hdiv.symm
    _ = idDecompositionAFormula d p + X * idDecompositionBFormula d p := hleft_cancel

theorem idDecompositionFormula_IdTransform_eq_add {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    IdTransform d p = idDecompositionAFormula d p + idDecompositionBFormula d p := by
  have hB := idDecompositionBFormula_mul_X_sub_one hd
  calc
    IdTransform d p = p - (p - IdTransform d p) := by ring
    _ = p - (X - 1) * idDecompositionBFormula d p := by rw [← hB]
    _ =
        (idDecompositionAFormula d p + X * idDecompositionBFormula d p) -
          (X - 1) * idDecompositionBFormula d p := by
            nth_rw 1 [idDecompositionFormula_eq_add_X_mul hd]
    _ = idDecompositionAFormula d p + idDecompositionBFormula d p := by ring

theorem idDecompositionFormula_eq_of_system {d : ℕ} {p a b : ℝ[X]} (hd : p.natDegree ≤ d)
    (hp : p = a + X * b) (hI : IdTransform d p = a + b) :
    a = idDecompositionAFormula d p ∧ b = idDecompositionBFormula d p := by
  have hsub : p - IdTransform d p = (X - 1) * b := by
    rw [hI, hp]
    ring
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
    a = p - X * b := by rw [hp]; ring
    _ = p - X * idDecompositionBFormula d p := by rw [hb]
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
        simp
      rw [idDecompositionBFormula, hI0, sub_self, zero_divByMonic]
      rw [IdTransform, Polynomial.reflect_zero]
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
        simpa [a, b] using h0
      have hI' : IdTransform (n + 1) p = IdTransform (n + 1) a + IdTransform n b := by
        have h0 : IdTransform (n + 1) p = IdTransform (n + 1) a + IdTransform (n + 1) (X * b) := by
          simpa [IdTransform, Polynomial.reflect_add, a, b] using
            (congrArg (IdTransform (n + 1)) ha)
        rw [IdTransform_X_mul_of_natDegree_le_pred (d := n + 1) (Nat.succ_pos _) hbdeg] at h0
        simpa [a, b] using h0
      have hsys := idDecompositionFormula_eq_of_system (d := n + 1) (p := p) hd ha' hI'
      simpa [a, b] using hsys.2

lemma idDecompositionAFormula_fixed {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    IdTransform d (idDecompositionAFormula d p) = idDecompositionAFormula d p := by
  cases d with
  | zero =>
      have hp0 : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hd
      have hI0 : IdTransform 0 p = p := by
        rw [hp0, IdTransform, Polynomial.reflect_C]
        simp
      have hB0 : idDecompositionBFormula 0 p = 0 := by
        rw [idDecompositionBFormula, hI0, sub_self, zero_divByMonic]
      have hA0 : idDecompositionAFormula 0 p = p := by
        simpa [hB0] using (idDecompositionFormula_eq_add_X_mul (d := 0) hd).symm
      rw [hA0, hI0]
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
        simpa [a, b] using h0
      have hI' : IdTransform (n + 1) p = IdTransform (n + 1) a + IdTransform n b := by
        have h0 : IdTransform (n + 1) p = IdTransform (n + 1) a + IdTransform (n + 1) (X * b) := by
          simpa [IdTransform, Polynomial.reflect_add, a, b] using
            (congrArg (IdTransform (n + 1)) ha)
        rw [IdTransform_X_mul_of_natDegree_le_pred (d := n + 1) (Nat.succ_pos _) hbdeg] at h0
        simpa [a, b] using h0
      have hsys := idDecompositionFormula_eq_of_system (d := n + 1) (p := p) hd ha' hI'
      simpa [a, b] using hsys.1

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
  · intro ab hab
    rcases ab with ⟨a, b⟩
    rcases hab with ⟨_, ha, hb⟩
    refine Prod.ext ?_ ?_
    · simpa using ha
    · simpa using hb

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
  calc
    C (((-1 : ℝ) ^ (d + 1))) * p.comp (-X - 1)
        = C (((-1 : ℝ) ^ d)) * (C (-1) * p.comp (-X - 1)) := by
            rw [pow_succ, map_mul, mul_assoc]
    _ = -(C (((-1 : ℝ) ^ d)) * p.comp (-X - 1)) := by
          simp

lemma RdTransform_involutive (d : ℕ) (p : ℝ[X]) :
    RdTransform d (RdTransform d p) = p := by
  unfold RdTransform
  rw [mul_comp, C_comp, comp_assoc]
  have hcomp : (-X - 1 : ℝ[X]).comp (-X - 1) = X := by
    calc
      (-X - 1 : ℝ[X]).comp (-X - 1) = -(-X - 1 : ℝ[X]) - 1 := by
        simp [sub_eq_add_neg, add_comp]
      _ = X := by
        ring
  rw [hcomp, ← mul_assoc, ← map_mul]
  have hpow : ((-1 : ℝ) ^ d) * ((-1 : ℝ) ^ d) = 1 := by
    rw [← pow_add, ← two_mul]
    norm_num
  rw [hpow]
  simp

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
  rw [show ((X + 1) * p : ℝ[X]) = X * p + p by ring]
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
            simp [pow_succ, mul_assoc, mul_comm]
          calc
            RdTransform (d + 1) (C a * X ^ 0 * (X + 1) ^ (d + 1 - 0))
                = RdTransform (d + 1) ((X + 1) * (C a * X ^ 0 * (X + 1) ^ d)) := by
                    rw [hzero]
            _ = X * RdTransform d (C a * X ^ 0 * (X + 1) ^ d) := by
                  rw [RdTransform_X_add_one_mul_succ]
            _ = X * (C a * X ^ (d - 0) * (X + 1) ^ 0) := by
                  simpa using congrArg (fun q => X * q) (ih 0 (Nat.zero_le d))
            _ = C a * X ^ (d + 1 - 0) * (X + 1) ^ 0 := by
                  rw [pow_zero, mul_one, Nat.sub_zero, show d + 1 - 0 = d + 1 by simp, pow_succ]
                  ring
      | succ n =>
          have hn' : n ≤ d := Nat.succ_le_succ_iff.mp hn
          have hsucc :
              C a * X ^ (n + 1) * (X + 1) ^ (d + 1 - (n + 1)) =
                X * (C a * X ^ n * (X + 1) ^ (d - n)) := by
            rw [Nat.succ_sub_succ_eq_sub, pow_succ]
            ring
          calc
            RdTransform (d + 1) (C a * X ^ (n + 1) * (X + 1) ^ (d + 1 - (n + 1)))
                = RdTransform (d + 1) (X * (C a * X ^ n * (X + 1) ^ (d - n))) := by
                    rw [hsucc]
            _ = (X + 1) * RdTransform d (C a * X ^ n * (X + 1) ^ (d - n)) := by
                  rw [RdTransform_X_mul_succ]
            _ = (X + 1) * (C a * X ^ (d - n) * (X + 1) ^ n) := by
                  simpa using congrArg (fun q => (X + 1) * q) (ih n hn')
            _ = C a * X ^ (d + 1 - (n + 1)) * (X + 1) ^ (n + 1) := by
                  rw [Nat.succ_sub_succ_eq_sub, pow_succ]
                  ring

lemma RdTransform_fPolynomial (d : ℕ) (h : ℝ[X]) :
    RdTransform d (fPolynomial d h) = fPolynomial d (IdTransform d h) := by
  refine Polynomial.induction_on' h ?_ ?_
  · intro p q hp hq
    rw [fPolynomial_add, RdTransform_add, hp, hq]
    simp [IdTransform, Polynomial.reflect_add, fPolynomial_add]
  · intro n a
    by_cases hn : n ≤ d
    · have hf : fPolynomial d (monomial n a) = C a * X ^ n * (X + 1) ^ (d - n) := by
          simp [fPolynomial_monomial, hn]
      rw [hf, RdTransform_basis_term d n a hn]
      have hid : IdTransform d (monomial n a) = monomial (d - n) a := by
        rw [IdTransform, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.reflect_C_mul_X_pow]
        rw [Polynomial.revAt_le hn, Polynomial.C_mul_X_pow_eq_monomial]
      rw [hid]
      have hsub : d - (d - n) = n := by omega
      have hfd : fPolynomial d (monomial (d - n) a) = C a * X ^ (d - n) * (X + 1) ^ n := by
        have hle : d - n ≤ d := Nat.sub_le _ _
        simpa [hle, hsub] using (fPolynomial_monomial d (d - n) a)
      rw [hfd]
    · have hgt : d < n := lt_of_not_ge hn
      have hf : fPolynomial d (monomial n a) = 0 := by
        simp [fPolynomial_monomial, hn]
      rw [hf, RdTransform_zero]
      have hid : IdTransform d (monomial n a) = monomial n a := by
        rw [IdTransform, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.reflect_C_mul_X_pow]
        rw [Polynomial.revAt_eq_self_of_lt hgt, Polynomial.C_mul_X_pow_eq_monomial]
      rw [hid]
      simp [fPolynomial_monomial, hn]

lemma natDegree_RdTransform_eq (d : ℕ) (p : ℝ[X]) :
    (RdTransform d p).natDegree = p.natDegree := by
  have hX1 : (-X - 1 : ℝ[X]) = -(X + 1) := by
    ring
  have ht : (-X - 1 : ℝ[X]).natDegree = 1 := by
    rw [hX1, Polynomial.natDegree_neg, show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp,
      Polynomial.natDegree_X_add_C]
  unfold RdTransform
  rw [Polynomial.natDegree_C_mul (pow_ne_zero _ (by norm_num)), Polynomial.natDegree_comp, ht]
  simp

lemma leadingCoeff_RdTransform (d : ℕ) (p : ℝ[X]) :
    (RdTransform d p).leadingCoeff = (-1 : ℝ) ^ (d + p.natDegree) * p.leadingCoeff := by
  have hX1 : (-X - 1 : ℝ[X]) = -(X + 1) := by
    ring
  have hdeg : (-X - 1 : ℝ[X]).natDegree = 1 := by
    rw [hX1, Polynomial.natDegree_neg, show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp,
      Polynomial.natDegree_X_add_C]
  have ht : (-X - 1 : ℝ[X]).natDegree ≠ 0 := by
    rw [hdeg]
    norm_num
  have hl : (-X - 1 : ℝ[X]).leadingCoeff = (-1 : ℝ) := by
    rw [hX1, Polynomial.leadingCoeff_neg, show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp,
      Polynomial.leadingCoeff_X_add_C]
  unfold RdTransform
  rw [Polynomial.leadingCoeff_C_mul_of_isUnit (show IsUnit (((-1 : ℝ) ^ d)) by
        exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))),
    Polynomial.leadingCoeff_comp ht, hl]
  calc
    (-1) ^ d * (p.leadingCoeff * (-1) ^ p.natDegree) =
        ((-1) ^ d * (-1) ^ p.natDegree) * p.leadingCoeff := by ring
    _ = (-1) ^ (d + p.natDegree) * p.leadingCoeff := by rw [← pow_add]

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
    rw [hR, hp]
    ring
  have hb : b = rdDecompositionBFormula d p := by
    simpa [rdDecompositionBFormula] using hbR
  refine ⟨?_, hb⟩
  calc
    a = p - X * b := by rw [hp]; ring
    _ = p - X * (RdTransform d p - p) := by rw [hbR]
    _ = rdDecompositionAFormula d p := by
      unfold rdDecompositionAFormula
      ring

lemma natDegree_rdDecompositionBFormula_le {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (rdDecompositionBFormula d p).natDegree ≤ d - 1 := by
  have hR : (RdTransform d p).natDegree ≤ d := by
    rw [natDegree_RdTransform_eq]
    exact hd
  have hdeg : (rdDecompositionBFormula d p).natDegree ≤ d := by
    unfold rdDecompositionBFormula
    simpa using Polynomial.natDegree_sub_le_of_le hR hd
  rcases lt_or_eq_of_le hd with hlt | hEq
  · have hR' : (RdTransform d p).natDegree ≤ d - 1 := by
      rw [natDegree_RdTransform_eq]
      omega
    have hp' : p.natDegree ≤ d - 1 := by omega
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
      rw [Polynomial.coeff_sub, hRcoeff, hpcoeff, sub_self]
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
      rw [hA0]
      exact hd
  | succ n =>
      have hbdeg : (rdDecompositionBFormula (n + 1) p).natDegree ≤ n :=
        by simpa using natDegree_rdDecompositionBFormula_le hd
      have hXb : (X * rdDecompositionBFormula (n + 1) p).natDegree ≤ n + 1 := by
        have hXb' :=
          Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_X_le hbdeg
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hXb'
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
  · intro ab hab
    rcases ab with ⟨a, b⟩
    rcases hab with ⟨_, ha, hb⟩
    refine Prod.ext ?_ ?_
    · simpa using ha
    · simpa using hb

lemma eq_zero_of_natDegree_le_zero_of_eq_add_X_mul {p a b : ℝ[X]}
    (hp : p.natDegree ≤ 0) (ha : a.natDegree ≤ 0) (hb : b.natDegree ≤ 0) (h : p = a + X * b) :
    b = 0 := by
  have hp1 : p.coeff 1 = 0 := by
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by simp))
  have ha1 : a.coeff 1 = 0 := by
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ha (by simp))
  rw [h, Polynomial.coeff_add, Polynomial.coeff_X_mul, ha1, zero_add] at hp1
  have hbC : b = C (b.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hb
  rw [hbC, hp1]
  simp

theorem idTransform_eq_add_of_isIdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d) (h : IsIdDecomposition d p a b) :
    IdTransform d p = a + b := by
  rcases h with ⟨hab, had, hbd, hfixA, hfixB⟩
  cases d with
  | zero =>
      have hb0 : b = 0 := eq_zero_of_natDegree_le_zero_of_eq_add_X_mul hd had hbd hab
      rw [hab, hb0]
      simpa using hfixA
  | succ n =>
      have hfixB' : IdTransform n b = b := by
        simpa [Nat.succ_sub_one] using hfixB
      have hXb : IdTransform (n + 1) (X * b) = b := by
        simpa [Nat.succ_sub_one] using (IdTransform_X_mul_succ (d := n) (p := b) hbd).trans hfixB'
      rw [hab, IdTransform_add, hfixA, hXb]

theorem idDecomposition_eq_formula_of_isIdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d) (h : IsIdDecomposition d p a b) :
    a = idDecompositionAFormula d p ∧ b = idDecompositionBFormula d p := by
  exact idDecompositionFormula_eq_of_system hd h.1 <|
    idTransform_eq_add_of_isIdDecomposition hd h

theorem rdTransform_eq_add_X_add_one_mul_of_isRdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hp : p.natDegree ≤ d) (h : IsRdDecomposition d p a b) :
    RdTransform d p = a + (X + 1) * b := by
  rcases h with ⟨hab, had, hbd, hfixA, hfixB⟩
  cases d with
  | zero =>
      have hb0 : b = 0 := eq_zero_of_natDegree_le_zero_of_eq_add_X_mul hp had hbd hab
      have hfixA' : a.comp (-X - 1) = a := by
        simpa [RdTransform] using hfixA
      rw [hb0] at hab ⊢
      simp [hab, hfixA', RdTransform]
  | succ n =>
      have hfixB' : RdTransform n b = b := by
        simpa [Nat.succ_sub_one] using hfixB
      rw [hab, RdTransform_add, hfixA, RdTransform_X_mul_succ, hfixB']

theorem rdDecomposition_eq_formula_of_isRdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hp : p.natDegree ≤ d) (h : IsRdDecomposition d p a b) :
    a = rdDecompositionAFormula d p ∧ b = rdDecompositionBFormula d p := by
  exact rdDecompositionFormula_eq_of_system h.1 <|
    rdTransform_eq_add_X_add_one_mul_of_isRdDecomposition hp h

theorem isRdDecomposition_fPolynomial_of_isIdDecomposition {d : ℕ} {h a b : ℝ[X]}
    (hd : h.natDegree ≤ d) (hid : IsIdDecomposition d h a b) :
    IsRdDecomposition d (fPolynomial d h) (fPolynomial d a) (fPolynomial (d - 1) b) := by
  rcases hid with ⟨hab, had, hbd, hfixA, hfixB⟩
  refine ⟨?_, fPolynomial_natDegree_le d a, fPolynomial_natDegree_le (d - 1) b, ?_, ?_⟩
  · cases d with
    | zero =>
        have hb0 : b = 0 := eq_zero_of_natDegree_le_zero_of_eq_add_X_mul hd had hbd hab
        rw [hab, hb0]
        simp
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
  exact ⟨hleft.1.trans hright.1.symm, hleft.2.trans hright.2.symm⟩

lemma prec_of_prec0_of_ne_zero {f g : ℝ[X]}
    (hf : f ≠ 0) (hg : g ≠ 0) (h : Prec0 f g) :
    Prec f g := by
  rcases h with rfl | rfl | hprec
  · contradiction
  · contradiction
  · exact hprec

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
      simpa using hb_nonneg.pos_leadingCoeff hb0
    linarith
  exact ne_of_gt hcoeff_pos

private lemma leadingCoeff_add_X_mul_eq_of_natDegree_le
    {a b : ℝ[X]}
    (ha_le : a.natDegree ≤ b.natDegree)
    (hb_nonneg : HasNonnegCoeffs b)
    (hb0 : b ≠ 0) :
    (a + X * b).leadingCoeff = b.leadingCoeff := by
  have hXb_pos : HasPosLeadingCoeff (X * b) :=
    (hasNonnegCoeffs_X.mul hb_nonneg).pos_leadingCoeff (mul_ne_zero X_ne_zero hb0)
  have hdeg_lt : a.natDegree < (X * b).natDegree := by
    rw [natDegree_X_mul hb0]
    omega
  have hsum_deg : (a + X * b).natDegree = (X * b).natDegree :=
    natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hXb_pos
  have hXb_deg : (X * b).natDegree = b.natDegree + 1 := by
    simpa [Nat.add_comm] using natDegree_X_mul hb0
  have ha_top : a.coeff (b.natDegree + 1) = 0 := by
    have hdeg_top : a.natDegree < b.natDegree + 1 := by
      simpa [hXb_deg] using hdeg_lt
    exact Polynomial.coeff_eq_zero_of_natDegree_lt hdeg_top
  calc
    (a + X * b).leadingCoeff = (a + X * b).coeff (b.natDegree + 1) := by
      rw [Polynomial.leadingCoeff, hsum_deg, hXb_deg]
    _ = a.coeff (b.natDegree + 1) + (X * b).coeff (b.natDegree + 1) := by
      rw [Polynomial.coeff_add]
    _ = b.coeff b.natDegree := by
      rw [ha_top, zero_add, Polynomial.coeff_X_mul]
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
      rw [← Multiset.coe_card, hss_eq, hb_rr.2]
    have hrs_len : rs.length = p.natDegree := by
      rw [← Multiset.coe_card, hrs_eq, hp_rr.2]
    rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩ <;> omega
  omega

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
    field_simp [ne_of_gt (hp_nonneg.pos_leadingCoeff hp0)]
  have hb_monic : (C c * b).Monic := by
    unfold c
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [hlc]
    field_simp [ne_of_gt (hb_nonneg.pos_leadingCoeff hb0)]
  have hscaled : Prec (C c * b) (C c * p) :=
    prec_C_mul_right (prec_C_mul_left hbp hc_ne) hc_ne
  have hp_nonpos : ∀ r ∈ p.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hbp.2.1 hp_nonneg
  have hb_nonpos : ∀ r ∈ b.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hbp.1 hb_nonneg
  have hdeg_scaled : (C c * b).natDegree + 1 = (C c * p).natDegree := by
    rw [Polynomial.natDegree_C_mul hc_ne, Polynomial.natDegree_C_mul hc_ne, hdeg]
  have hprec0 : Prec0 (C c * b) (C c * p - X * (C c * b)) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using
      prec_sub_X_mul_right
        (f := C c * p) (g := C c * b)
        hscaled hp_monic hb_monic hdeg_scaled
        (by
          intro r hr
          exact hp_nonpos r (by simpa [roots_C_mul _ hc_ne] using hr))
        (by
          intro r hr
          exact hb_nonpos r (by simpa [roots_C_mul _ hc_ne] using hr))
  have hXC : C c * (X * b) = X * (C c * b) := by
    ext n
    cases n <;> simp [Polynomial.coeff_X_mul, Polynomial.C_mul, mul_assoc]
  have hsub_eq : C c * p - X * (C c * b) = C c * a := by
    calc
      C c * p - X * (C c * b)
          = C c * (a + X * b) - X * (C c * b) := by rw [hp_eq]
      _ = C c * a + C c * (X * b) - X * (C c * b) := by rw [mul_add]
      _ = C c * a := by rw [hXC]; ring
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
      C c⁻¹ * (C c * b) = C (c⁻¹ * c) * b := by rw [Polynomial.C_mul, mul_assoc]
      _ = b := by simp [hc_ne]
  have hcancel_a : C c⁻¹ * (C c * a) = a := by
    calc
      C c⁻¹ * (C c * a) = C (c⁻¹ * c) * a := by rw [Polynomial.C_mul, mul_assoc]
      _ = a := by simp [hc_ne]
  simpa [hcancel_b, hcancel_a] using hback

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
  have hb_rr : IsRealRooted b := hba.1
  have ha_rr : IsRealRooted a := hba.2.1
  have hb_pos : HasPosLeadingCoeff b := hb_nonneg.pos_leadingCoeff hb_rr.1
  have ha_pos : HasPosLeadingCoeff a := ha_nonneg.pos_leadingCoeff ha_rr.1
  have hXb_nonneg : HasNonnegCoeffs (X * b) := hasNonnegCoeffs_X.mul hb_nonneg
  have hXb_pos : HasPosLeadingCoeff (X * b) :=
    hXb_nonneg.pos_leadingCoeff (mul_ne_zero X_ne_zero hb_rr.1)
  have haxb : Prec a (X * b) := prec_mul_X_of_prec_of_nonneg hba hb_nonneg ha_nonneg
  have hp_right : Prec (a + X * b) (X * b) := by
    simpa using
      (prec_nonneg_combo_right haxb ha_pos hXb_pos
        (a := (1 : ℝ)) (b := (1 : ℝ)) (by positivity) (by positivity)
        (Or.inl (by positivity)))
  have hp0 : p ≠ 0 := by
    simpa [hp_eq] using hp_right.1.1
  have hap : Prec a p := by
    have hprec0 : Prec0 a ([a, X * b].sum) := by
      refine prec0_sum_left_of_common_left_of_nonneg [a, X * b] a ?_ ?_
      · intro q hq
        simp at hq
        rcases hq with rfl | rfl
        · exact (prec_refl ha_rr).toPrec0
        · exact haxb.toPrec0
      · intro q hq
        simp at hq
        rcases hq with rfl | rfl
        · exact ha_nonneg
        · exact hXb_nonneg
    exact prec_of_prec0_of_ne_zero ha_rr.1 hp0 (by simpa [hp_eq] using hprec0)
  have hbXb : Prec b (X * b) := by
    exact prec_mul_X_of_prec_of_nonneg (prec_refl hb_rr) hb_nonneg hb_nonneg
  have hbp : Prec b p := by
    have hprec0 : Prec0 b ([a, X * b].sum) := by
      refine prec0_sum_left_of_common_left_of_nonneg [a, X * b] b ?_ ?_
      · intro q hq
        simp at hq
        rcases hq with rfl | rfl
        · exact hba.toPrec0
        · exact hbXb.toPrec0
      · intro q hq
        simp at hq
        rcases hq with rfl | rfl
        · exact ha_nonneg
        · exact hXb_nonneg
    exact prec_of_prec0_of_ne_zero hb_rr.1 hp0 (by simpa [hp_eq] using hprec0)
  have hIda : Prec (a + b) a := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (prec_nonneg_combo_right hba hb_pos ha_pos
        (a := (1 : ℝ)) (b := (1 : ℝ)) (by positivity) (by positivity)
        (Or.inl (by positivity)))
  have hIdp : Prec (IdTransform d p) p := by
    have hprec0 : Prec0 (∑ t ∈ (Finset.univ : Finset Bool), cond t b a) p := by
      refine prec0_finset_sum_right_of_nonneg (s := (Finset.univ : Finset Bool))
        (f := fun t => cond t b a) (h := p) ?_ ?_
      · intro t ht
        cases t <;> simp [hap.toPrec0, hbp.toPrec0]
      · intro t ht
        cases t <;> simp [ha_nonneg, hb_nonneg]
    have hId0 : IdTransform d p ≠ 0 := by
      simpa [hId_eq] using hIda.1.1
    exact prec_of_prec0_of_ne_zero hId0 hp0 (by
      simpa [hId_eq, add_comm, add_left_comm, add_assoc] using hprec0)
  exact ⟨hap, hbp, hIdp⟩

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
    rw [hp_eq]
    have hC : C α = C β + C (α - β) := by
      ext n
      cases n <;> simp
    calc
      C α * a + C β * (X * b)
          = (C β + C (α - β)) * a + C β * (X * b) := by rw [hC]
      _ = C β * a + C (α - β) * a + C β * (X * b) := by rw [add_mul]
      _ = C (α - β) * a + C β * (a + X * b) := by
            rw [mul_add]
            ac_rfl
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
    have hC : C β = C α + C (β - α) := by
      ext n
      cases n <;> simp
    calc
      C α * a + C β * (X * b)
          = C α * a + (C α + C (β - α)) * (X * b) := by rw [hC]
      _ = C α * a + (C α * (X * b) + C (β - α) * (X * b)) := by rw [add_mul]
      _ = C α * (a + X * b) + C (β - α) * (X * b) := by
            rw [mul_add]
            ac_rfl
      _ = C α * p + C (β - α) * (X * b) := by rw [hp_eq]
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
    apply le_antisymm
    · exact le_trans hdeg_hi (Nat.succ_le_succ ha_le)
    · exact hdeg_lo
  have hab_eq : a.natDegree = b.natDegree := by
    omega
  have hall_aXb : AllComboRealRooted a (X * b) :=
    allComboRealRooted_left_X_mul_component_of_prec_left hp_eq hap
  have hXb_rr : IsRealRooted (X * b) := by
    rcases hall_aXb 0 1 with hzero | hrr
    · have hXb0 : X * b = 0 := by
        simpa using hzero
      exact False.elim (hb0 ((mul_eq_zero.mp hXb0).resolve_left X_ne_zero))
    · simpa using hrr
  have hdeg_aXb : a.natDegree + 1 = (X * b).natDegree := by
    rw [natDegree_X_mul hb0]
    omega
  have hprec_or : Prec a (X * b) ∨ Prec (X * b) a := by
    exact prec_of_allComboRealRooted hap.1 hXb_rr hall_aXb (Or.inl hdeg_aXb)
  have hnot_rev : ¬ Prec (X * b) a := by
    intro hbad
    have hbound := (natDegree_bounds_of_prec hbad).1
    rw [← hdeg_aXb] at hbound
    omega
  have hprec_aXb : Prec a (X * b) := by
    rcases hprec_or with h | h
    · exact h
    · exact False.elim (hnot_rev h)
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
        rw [Polynomial.leadingCoeff] at hlead
        exact hlead
      linarith
    exact ne_of_gt hcoeff_pos
  have hXb_le_d : (X * b).natDegree ≤ d := le_trans hXb_le_p hd
  rcases natDegree_eq_or_succ_or_revSucc_of_allComboRealRooted hall_aXb hap.1.1 hXb0 with
    hdeg | hdeg | hdeg
  · left
    omega
  · exfalso
    omega
  · right
    omega

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
  rw [hp_root0] at hcoeff
  linarith

private lemma exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
    {p : ℝ[X]}
    (hp_rr : IsRealRooted p)
    (hp_nonneg : HasNonnegCoeffs p)
    (hp0_root : ¬ p.IsRoot 0) :
    ∃ c : ℝ, (∀ s ∈ p.roots, s ≤ c) ∧ c < 0 := by
  let rs := p.roots.sort (· ≤ ·)
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_eq : (↑rs : Multiset ℝ) = p.roots := Multiset.sort_eq ..
  by_cases hrs_nil : rs = []
  · refine ⟨-1, ?_, by norm_num⟩
    intro s hs
    have hs' : s ∈ rs := by
      have : s ∈ (↑rs : Multiset ℝ) := by simpa [hrs_eq] using hs
      exact Multiset.mem_coe.mp this
    simp [hrs_nil] at hs'
  · refine ⟨rs.getLast hrs_nil, ?_, ?_⟩
    · intro s hs
      have hs' : s ∈ rs := by
        have : s ∈ (↑rs : Multiset ℝ) := by simpa [hrs_eq] using hs
        exact Multiset.mem_coe.mp this
      exact List.Pairwise.rel_getLast hrs_sorted hs'
    · have hc_root : p.IsRoot (rs.getLast hrs_nil) := by
        have hc_mem : rs.getLast hrs_nil ∈ rs := List.getLast_mem hrs_nil
        have : rs.getLast hrs_nil ∈ (↑rs : Multiset ℝ) := Multiset.mem_coe.mpr hc_mem
        exact (mem_roots hp_rr.1).mp (by simpa [hrs_eq] using this)
      have hc_nonpos : rs.getLast hrs_nil ≤ 0 :=
        roots_nonpos_of_nonneg_coeffs hp_rr hp_nonneg (rs.getLast hrs_nil) <|
          (mem_roots hp_rr.1).mpr hc_root
      have hc_ne : rs.getLast hrs_nil ≠ 0 := by
        intro hc0
        exact hp0_root (hc0 ▸ hc_root)
      exact lt_of_le_of_ne hc_nonpos hc_ne

private lemma listInterlaces_of_listAlternates_append_right
    {ss qs : List ℝ} {uR : ℝ}
    (hlen : qs.length + 1 = ss.length)
    (halt : ListAlternates ss (qs ++ [uR])) :
    ListInterlaces qs ss := by
  have halt0 :
      ListAlternates (ss.map (· - uR)) ((qs.map (· - uR)) ++ [0]) := by
    simpa [List.map_append] using listAlternates_map_sub_const halt uR
  have hlen0 : (qs.map (· - uR)).length + 1 = (ss.map (· - uR)).length := by
    simpa using hlen
  have hint0 :
      ListInterlaces (qs.map (· - uR)) (ss.map (· - uR)) :=
    listInterlaces_of_listAlternates_append_zero
      (qs.map (· - uR)) (ss.map (· - uR)) hlen0 halt0
  have hfun :
      ((fun x : ℝ => x + uR) ∘ fun x => x - uR) = fun x => x := by
    funext x
    change (x - uR) + uR = x
    ring_nf
  simpa [List.map_map, Function.comp, hfun] using
    listInterlaces_map_sub_const hint0 (-uR)

private lemma interlaces_of_prec_sameDegree_rightmost_factor
    {f g q : ℝ[X]} {uR : ℝ}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hright : ∀ r ∈ g.roots, r ≤ uR)
    (hgq : g = (X - C uR) * q) :
    Interlaces q f := by
  obtain ⟨hf, hg, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩ := hfg
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hg.2]
  have hq_ne : q ≠ 0 := by
    exact right_ne_zero_of_mul (by simpa [hgq] using hg.1)
  have hq : IsRealRooted q := by
    apply isRealRooted_of_dvd hg hq_ne
    exact ⟨X - C uR, by simp [hgq, mul_comm]⟩
  have hq_deg_g : q.natDegree + 1 = g.natDegree := by
    rw [hgq, natDegree_mul (X_sub_C_ne_zero uR) hq_ne, natDegree_X_sub_C]
    omega
  have hq_deg : q.natDegree + 1 = f.natDegree := by
    omega
  rcases hshape with ⟨hlen, _⟩ | ⟨_hlen, halt⟩
  · exfalso
    omega
  ·
    let qs := q.roots.sort (· ≤ ·)
    have hqs_eq : (↑qs : Multiset ℝ) = q.roots := Multiset.sort_eq ..
    have hqs_sorted : qs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
    have hqs_len : qs.length = q.natDegree := by
      rw [show qs = q.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hq.2]
    have hqs_le_uR : ∀ r ∈ qs, r ≤ uR := by
      intro r hr
      exact hright r (by
        rw [hgq, roots_mul (mul_ne_zero (X_sub_C_ne_zero uR) hq_ne), roots_X_sub_C]
        apply Multiset.mem_add.mpr
        right
        rw [← hqs_eq]
        exact Multiset.mem_coe.mpr hr)
    have hqs_sorted_right : (qs ++ [uR]).Pairwise (· ≤ ·) := by
      rw [List.pairwise_append]
      refine ⟨hqs_sorted, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact hqs_le_uR a ha
    have hrs_eq_right : rs = qs ++ [uR] := by
      apply List.Perm.eq_of_pairwise' hrs_sorted hqs_sorted_right
      apply Multiset.coe_eq_coe.mp
      calc
        (↑rs : Multiset ℝ) = g.roots := hrs_eq
        _ = ({uR} : Multiset ℝ) + q.roots := by
              rw [hgq, roots_mul (mul_ne_zero (X_sub_C_ne_zero uR) hq_ne), roots_X_sub_C]
        _ = q.roots + ({uR} : Multiset ℝ) := by rw [add_comm]
        _ = q.roots + ↑[uR] := by simp
        _ = (↑qs : Multiset ℝ) + ↑[uR] := by rw [hqs_eq]
        _ = (↑(qs ++ [uR]) : Multiset ℝ) := by rw [Multiset.coe_add]
    have hlen_qs : qs.length + 1 = ss.length := by
      rw [hqs_len, hss_len, hq_deg]
    have halt_right : ListAlternates ss (qs ++ [uR]) := by
      simpa [hrs_eq_right] using halt
    have hshape_qs_rs : ListInterlaces qs ss :=
      listInterlaces_of_listAlternates_append_right hlen_qs halt_right
    exact ⟨hf, hq, hq_deg, ss, qs, hss_sorted, hqs_sorted, hss_eq, hqs_eq, hshape_qs_rs⟩

private theorem prec_b_component_of_prec_left_top_of_sameDegree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
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
  have hXb_rr : IsRealRooted (X * b) := by
    rcases hall_aXb 0 1 with hzero | hrr
    · have hXb0 : X * b = 0 := by simpa using hzero
      exact False.elim (hb0 ((mul_eq_zero.mp hXb0).resolve_left X_ne_zero))
    · simpa using hrr
  have hsame : a.natDegree = (X * b).natDegree := by
    rw [ha_top, hXb_top]
  have hprec_or : Prec a (X * b) ∨ Prec (X * b) a := by
    exact prec_of_allComboRealRooted hap.1 hXb_rr hall_aXb (Or.inr hsame)
  have ha_not_root0 : ¬ a.IsRoot 0 := by
    exact
      not_isRoot_zero_of_IdTransform_fixed_top_of_hasNonnegCoeffs
        hid.2.2.2.1 ha_top ha_nonneg ha0
  obtain ⟨c, hac_le, hc_lt0⟩ :=
    exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
      hap.1 ha_nonneg ha_not_root0
  have hXb_root0 : (X * b).IsRoot 0 := by
    simp [Polynomial.IsRoot]
  have hprec_aXb : Prec a (X * b) := by
    exact
      PosComboRealRooted.prec_of_prec_or_revPrec_of_root_asymmetry
        (f := X * b) (g := a) (c := c) (r := 0)
        (by simpa [or_comm] using hprec_or)
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
      (X * b).natDegree = d ∨ (X * b).natDegree + 1 = d := by
    exact
      natDegree_X_mul_component_eq_or_succ_of_prec_left_top
        hd hp_eq ha_nonneg hb_nonneg ha_top hb0 hap
  rcases hXb_case with hXb_top | hXb_gap
  · exact
      prec_b_component_of_prec_left_top_of_sameDegree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hXb_top hap
  · exfalso
    have hall_aXb : AllComboRealRooted a (X * b) :=
      allComboRealRooted_left_X_mul_component_of_prec_left hp_eq hap
    have hXb_rr : IsRealRooted (X * b) := by
      rcases hall_aXb 0 1 with hzero | hrr
      · have hXb0 : X * b = 0 := by
          simpa using hzero
        exact False.elim (hb0 ((mul_eq_zero.mp hXb0).resolve_left X_ne_zero))
      · simpa using hrr
    have hall_Xba : AllComboRealRooted (X * b) a := by
      intro α β
      simpa [add_comm, add_left_comm, add_assoc] using hall_aXb β α
    have hprec_or : Prec (X * b) a ∨ Prec a (X * b) := by
      have hdeg : (X * b).natDegree + 1 = a.natDegree := by
        rw [ha_top]
        exact hXb_gap
      exact prec_of_allComboRealRooted hXb_rr hap.1 hall_Xba (Or.inl hdeg)
    have ha_not_root0 : ¬ a.IsRoot 0 := by
      exact
        not_isRoot_zero_of_IdTransform_fixed_top_of_hasNonnegCoeffs
          hid.2.2.2.1 ha_top ha_nonneg ha0
    obtain ⟨c, hac_le, hc_lt0⟩ :=
      exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
        hap.1 ha_nonneg ha_not_root0
    have hXb_root0 : (X * b).IsRoot 0 := by
      simp [Polynomial.IsRoot]
    have hbad : Prec a (X * b) := by
      exact
        PosComboRealRooted.prec_of_prec_or_revPrec_of_root_asymmetry
          (f := X * b) (g := a) (c := c) (r := 0)
          hprec_or hac_le hXb_root0 hc_lt0
    have hbound : a.natDegree ≤ (X * b).natDegree :=
      (natDegree_bounds_of_prec hbad).1
    rw [ha_top] at hbound
    omega

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
  have ha_rr : IsRealRooted a := by
    rcases hall_aXb 1 0 with hzero | hrr
    · exact False.elim (ha0 (by simpa using hzero))
    · simpa using hrr
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
    exact ne_of_gt hcoeff_pos
  have hbp_deg : b.natDegree + 1 = p.natDegree :=
    natDegree_right_of_prec_to_sum hp_eq ha_nonneg hb_nonneg hb0 hbp
  have hsame : a.natDegree = (X * b).natDegree := by
    rw [ha_top, natDegree_X_mul hb0, hbp_deg, hp_deg]
  have ha_not_root0 : ¬ a.IsRoot 0 := by
    exact
      not_isRoot_zero_of_IdTransform_fixed_top_of_hasNonnegCoeffs
        hid.2.2.2.1 ha_top ha_nonneg ha0
  obtain ⟨c, hac_le, hc_lt0⟩ :=
    exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
      ha_rr ha_nonneg ha_not_root0
  have hXb_root0 : (X * b).IsRoot 0 := by
    simp [Polynomial.IsRoot]
  have hprec_or : Prec a (X * b) ∨ Prec (X * b) a := by
    exact prec_of_allComboRealRooted ha_rr hpxb.2.1 hall_aXb (Or.inr hsame)
  have hprec_aXb : Prec a (X * b) := by
    exact
      PosComboRealRooted.prec_of_prec_or_revPrec_of_root_asymmetry
        (f := X * b) (g := a) (c := c) (r := 0)
        (by simpa [or_comm] using hprec_or)
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
    omega
  have hh_deg : h.natDegree = d := by
    rw [hId_eq]
    have hdeg_lt : b.natDegree < a.natDegree := by
      rw [ha_top]
      omega
    calc
      (a + b).natDegree = a.natDegree :=
        natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_lt ha_pos
      _ = d := ha_top
  have hdeg_lt : b.natDegree < a.natDegree := by
    rw [ha_top]
    omega
  have hh_pos : HasPosLeadingCoeff h := by
    rw [hId_eq]
    exact hasPosLeadingCoeff_add_of_natDegree_lt_left hdeg_lt ha_pos
  have hp_split : p = h + t := by
    calc
      p = a + X * b := hp_eq
      _ = (a + b) + (X - C (1 : ℝ)) * b := by
            rw [sub_mul]
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = h + (X - C (1 : ℝ)) * b := by rw [hId_eq]
  have hall_hp : AllComboRealRooted h p := allComboRealRooted_of_prec hIdp
  have hall_ht : AllComboRealRooted h t := by
    intro α β
    have hrew :
        C α * h + C β * t =
          C (α - β) * h + C β * p := by
      rw [hp_split]
      rw [mul_add]
      have hC : C (α - β) + C β = C α := by
        rw [← C_add]
        congr 1
        ring
      calc
        C α * h + C β * t = (C (α - β) + C β) * h + C β * t := by rw [hC]
        _ = C (α - β) * h + (C β * h + C β * t) := by
              rw [add_mul]
              ac_rfl
    simpa [hrew] using hall_hp (α - β) β
  have ht_ne : t ≠ 0 := by
    exact mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0
  have ht_rr : IsRealRooted t := by
    rcases hall_ht 0 1 with hzero | hrr
    · exact False.elim (ht_ne (by simpa [t] using hzero))
    · simpa [t] using hrr
  have ht_pos : HasPosLeadingCoeff t := by
    dsimp [t]
    unfold HasPosLeadingCoeff at hb_pos ⊢
    rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul]
    exact hb_pos
  have hb_rr : IsRealRooted b := by
    apply isRealRooted_of_dvd ht_rr hb0
    refine ⟨X - C (1 : ℝ), ?_⟩
    dsimp [t]
    rw [mul_comm]
  have hh_nonpos : ∀ r ∈ h.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hIdp.1 hh_nonneg
  have hsame : h.natDegree = t.natDegree := by
    dsimp [t]
    rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C]
    omega
  have hprec_or : Prec h t ∨ Prec t h := by
    exact prec_of_allComboRealRooted hIdp.1 ht_rr hall_ht (Or.inr hsame)
  have ht_root1 : t.IsRoot 1 := by
    dsimp [t]
    simp [Polynomial.IsRoot]
  have hht : Prec h t := by
    exact
      PosComboRealRooted.prec_of_prec_or_revPrec_of_root_asymmetry
        (f := t) (g := h) (c := 0) (r := 1)
        (by simpa [or_comm] using hprec_or)
        hh_nonpos ht_root1 (by norm_num)
  have ht_le_one : ∀ r ∈ t.roots, r ≤ 1 := by
    intro r hr
    dsimp [t] at hr
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0), roots_X_sub_C] at hr
    rcases Multiset.mem_add.mp hr with hr | hr
    · rcases Multiset.mem_singleton.mp hr with rfl
      norm_num
    ·
      have hr0 : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hb_rr hb_nonneg r hr
      linarith
  have hbh : Prec b h := by
    exact
      (interlaces_of_prec_sameDegree_rightmost_factor
        (f := h) (g := t) (q := b) (uR := 1)
        hht hsame ht_le_one (by rfl)).toPrec
  have hb_le_one : ∀ r ∈ b.roots, r ≤ (1 : ℝ) := by
    intro r hr
    have hr0 : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hb_rr hb_nonneg r hr
    linarith
  have hbt : Prec b t := by
    dsimp [t]
    exact prec_sameDegree_to_prec_mul_X_sub_C_of_roots_le (1 : ℝ)
      (prec_refl hb_rr) rfl hb_pos hb_pos hb_le_one hb_le_one
  have hbp_sum : Prec b [h, t].sum := by
    refine prec_sum_left_of_common_left [h, t] b ?_ hb_pos ?_ ?_
    · intro q hq
      simp at hq
      rcases hq with rfl | rfl
      · exact hbh
      · exact hbt
    · intro q hq
      simp at hq
      rcases hq with rfl | rfl
      · exact hh_pos
      · exact ht_pos
    · simp
  simpa [List.sum_cons, hp_split] using hbp_sum

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
    rw [ha_top]
    exact lt_of_lt_of_le (Nat.lt_succ_self b.natDegree) (le_trans hdeg_lo hd)
  have hh_deg : h.natDegree = d := by
    rw [hId_eq]
    calc
      (a + b).natDegree = a.natDegree :=
        natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_lt ha_pos
      _ = d := ha_top
  have hh_nonpos : ∀ r ∈ h.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hIdp.1 hh_nonneg
  have hp_split : p = h + t := by
    calc
      p = a + X * b := hp_eq
      _ = (a + b) + (X - C (1 : ℝ)) * b := by
        rw [sub_mul]
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = h + (X - C (1 : ℝ)) * b := by rw [hId_eq]
  have hall_hp : AllComboRealRooted h p := allComboRealRooted_of_prec hIdp
  have hall_ht : AllComboRealRooted h t := by
    intro α β
    have hrew :
        C α * h + C β * t =
          C (α - β) * h + C β * p := by
      rw [hp_split]
      rw [mul_add]
      have hC : C (α - β) + C β = C α := by
        rw [← C_add]
        congr 1
        ring
      calc
        C α * h + C β * t = (C (α - β) + C β) * h + C β * t := by rw [hC]
        _ = C (α - β) * h + (C β * h + C β * t) := by
          rw [add_mul]
          ac_rfl
    simpa [hrew] using hall_hp (α - β) β
  have ht_ne : t ≠ 0 := by
    exact mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0
  have ht_rr : IsRealRooted t := by
    rcases hall_ht 0 1 with hzero | hrr
    · exact False.elim (ht_ne (by simpa [t] using hzero))
    · simpa [t] using hrr
  have ht_root1 : t.IsRoot 1 := by
    dsimp [t]
    simp [Polynomial.IsRoot]
  rcases natDegree_eq_or_succ_or_revSucc_of_allComboRealRooted hall_ht hIdp.1.1 ht_ne with
    hsame | htoo_big | hgap
  · have hb_top : b.natDegree = d - 1 := by
      dsimp [t] at hsame
      rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C] at hsame
      omega
    exact
      brandenSolusTheorem26_third_converse_of_top_degree_of_right_top
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hb_top hIdp
  · dsimp [t] at htoo_big
    rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C] at htoo_big
    omega
  · have hall_th : AllComboRealRooted t h := by
      intro α β
      simpa [add_comm, add_left_comm, add_assoc] using hall_ht β α
    have hprec_or : Prec t h ∨ Prec h t := by
      exact prec_of_allComboRealRooted ht_rr hIdp.1 hall_th (Or.inl hgap)
    have hnot_th : ¬ Prec t h := by
      intro hth
      have h1_le : (1 : ℝ) ≤ 0 := by
        exact roots_le_of_prec_right hth hh_nonpos 1 ((mem_roots hth.1.1).mpr ht_root1)
      linarith
    rcases hprec_or with hth | hht
    · exact False.elim (hnot_th hth)
    ·
      have hbound : h.natDegree ≤ t.natDegree := (natDegree_bounds_of_prec hht).1
      have hbound' : d ≤ b.natDegree + 1 := by
        dsimp [t] at hbound
        rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C] at hbound
        simpa [Nat.add_comm] using hbound
      dsimp [t] at hgap
      rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C] at hgap
      omega

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
  exact ⟨hp_nonneg, hId_nonneg⟩

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
  exact ⟨hp_nonneg, hR_nonneg⟩

theorem hasNonnegCoeffs_transformed_components_of_isIdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    HasNonnegCoeffs (fPolynomial d a) ∧ HasNonnegCoeffs (fPolynomial (d - 1) b) := by
  exact ⟨hasNonnegCoeffs_fPolynomial ha_nonneg, hasNonnegCoeffs_fPolynomial hb_nonneg⟩

lemma prec_iff_prec_mul_X_add_one_both {f g : ℝ[X]} :
    Prec ((X + 1) * f) ((X + 1) * g) ↔ Prec f g := by
  constructor
  · intro h
    have h' : Prec ((X - C (-1)) * f) ((X - C (-1)) * g) := by
      simpa using h
    exact prec_of_prec_mul_X_sub_C_both (-1) h'
  · intro h
    have h' : Prec ((X - C (-1)) * f) ((X - C (-1)) * g) :=
      prec_mul_X_sub_C_both (-1) h
    simpa using h'

lemma prec_iff_prec_mul_X_add_one_pow_both {n : ℕ} {f g : ℝ[X]} :
    Prec ((X + 1) ^ n * f) ((X + 1) ^ n * g) ↔ Prec f g := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hstep :
          Prec ((X + 1) * ((X + 1) ^ n * f)) ((X + 1) * ((X + 1) ^ n * g)) ↔
            Prec ((X + 1) ^ n * f) ((X + 1) ^ n * g) :=
        prec_iff_prec_mul_X_add_one_both
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hstep.trans ih

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
      simp [hd]
    have hvd : v.natDegree ≤ d := by
      simp [hd]
    have hu_rr : IsRealRooted u :=
      isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs hud h.1 hu_nonneg
    have hv_rr : IsRealRooted v :=
      isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs hvd h.2.1 hv_nonneg
    exact prec_of_prec_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs
      hd hu_rr hv_rr h hu_nonneg hv_nonneg
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
              rw [hu_pad, hv_pad]
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
    simpa [q] using hid'
  have ha'0 : a' ≠ 0 := by
    intro ha'z
    apply ha0
    rw [haX, ha'z]
    simp
  have hb'0 : b' ≠ 0 := by
    intro hb'z
    apply hb0
    rw [hbX, hb'z]
    simp
  have ha'_nonneg : HasNonnegCoeffs a' :=
    hasNonnegCoeffs_of_eq_X_mul ha_nonneg haX
  have hb'_nonneg : HasNonnegCoeffs b' :=
    hasNonnegCoeffs_of_eq_X_mul hb_nonneg hbX
  have hXb'deg : (X * b').natDegree ≤ d - 2 := by
    have hbdegX : b.natDegree = b'.natDegree + 1 := by
      rw [hbX, natDegree_X_mul hb'0]
    have hd3 : 3 ≤ d := by
      rw [hbdegX] at hb_lt
      omega
    have hb'deg : b'.natDegree ≤ (d - 2) - 1 := hidq.2.2.1
    have hb'succ : b'.natDegree + 1 ≤ d - 2 := by
      have htmp : b'.natDegree + 1 ≤ ((d - 2) - 1) + 1 := Nat.succ_le_succ hb'deg
      have hsub : ((d - 2) - 1) + 1 = d - 2 := by
        omega
      simpa [hsub] using htmp
    rw [natDegree_X_mul hb'0]
    exact hb'succ
  have hqdeg : q.natDegree ≤ d - 2 := by
    simpa [q] using Polynomial.natDegree_add_le_of_le hidq.2.1 hXb'deg
  have hpair_nonneg :=
    hasNonnegCoeffs_pair_of_isIdDecomposition hqdeg hidq ha'_nonneg hb'_nonneg
  have hq_nonneg : HasNonnegCoeffs q := hpair_nonneg.1
  have hIdq_nonneg : HasNonnegCoeffs (IdTransform (d - 2) q) := hpair_nonneg.2
  have hpX' : p = X * q := by
    simpa [q] using hpX
  have hIdX : IdTransform d p = X * IdTransform (d - 2) q := by
    calc
      IdTransform d p = IdTransform d (X * q) := by rw [hpX']
      _ = X * IdTransform (d - 2) q :=
        IdTransform_X_mul_of_natDegree_le_two_pred hd2 hqdeg
  have hsmall := hprev hqdeg hidq ha'_nonneg hb'_nonneg ha'0 hb'0
  rcases hsmall with ⟨hfirst_small, hsecond_small, hthird_small, -⟩
  have hba_transport : Prec b a ↔ Prec b' a' := by
    calc
      Prec b a ↔ Prec (X * b') (X * a') := by rw [hbX, haX]
      _ ↔ Prec b' a' :=
        (prec_iff_prec_mul_X_both_of_hasNonnegCoeffs hb'_nonneg ha'_nonneg).symm
  have hap_transport : Prec a p ↔ Prec a' q := by
    calc
      Prec a p ↔ Prec (X * a') (X * q) := by rw [haX, hpX']
      _ ↔ Prec a' q :=
        (prec_iff_prec_mul_X_both_of_hasNonnegCoeffs ha'_nonneg hq_nonneg).symm
  have hbp_transport : Prec b p ↔ Prec b' q := by
    calc
      Prec b p ↔ Prec (X * b') (X * q) := by rw [hbX, hpX']
      _ ↔ Prec b' q :=
        (prec_iff_prec_mul_X_both_of_hasNonnegCoeffs hb'_nonneg hq_nonneg).symm
  have hIdp_transport : Prec (IdTransform d p) p ↔ Prec (IdTransform (d - 2) q) q := by
    calc
      Prec (IdTransform d p) p ↔ Prec (X * IdTransform (d - 2) q) (X * q) := by
        rw [hIdX, hpX']
      _ ↔ Prec (IdTransform (d - 2) q) q :=
        (prec_iff_prec_mul_X_both_of_hasNonnegCoeffs hIdq_nonneg hq_nonneg).symm
  refine ⟨?_, ?_, ?_, brandenSolusTheorem26_last_equiv hd hid ha_nonneg hb_nonneg⟩
  · calc
      Prec b a ↔ Prec b' a' := hba_transport
      _ ↔ Prec a' q := hfirst_small
      _ ↔ Prec a p := hap_transport.symm
  · calc
      Prec a p ↔ Prec a' q := hap_transport
      _ ↔ Prec b' q := hsecond_small
      _ ↔ Prec b p := hbp_transport.symm
  · calc
      Prec b p ↔ Prec b' q := hbp_transport
      _ ↔ Prec (IdTransform (d - 2) q) q := hthird_small
      _ ↔ Prec (IdTransform d p) p := hIdp_transport.symm

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
  have happ : Prec (1 : ℝ[X]) (1 : ℝ[X]) := by
    apply prec_refl
    exact ⟨by simp, by simp⟩
  have hnot : ¬ Prec (0 : ℝ[X]) (1 : ℝ[X]) := by
    intro h0
    exact h0.1.1 rfl
  exact hnot (hba_iff_hap.mpr happ)

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
    simpa [h] using hpair_nonneg.2
  have hh_rr : IsRealRooted h := by
    simpa [h] using hIdp.1
  have hp_rr : IsRealRooted p := hIdp.2.1
  have ha_pos : HasPosLeadingCoeff a := ha_nonneg.pos_leadingCoeff ha0
  have hb_pos : HasPosLeadingCoeff b := hb_nonneg.pos_leadingCoeff hb0
  have hh_deg : h.natDegree = b.natDegree := by
    rw [hId_eq]
    by_cases hdeg_eq : a.natDegree = b.natDegree
    · calc
        (a + b).natDegree = a.natDegree := by
          exact natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff hdeg_eq ha_pos hb_pos
        _ = b.natDegree := hdeg_eq
    · have hdeg_lt : a.natDegree < b.natDegree := lt_of_le_of_ne ha_le hdeg_eq
      exact natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hb_pos
  have hh_pos : HasPosLeadingCoeff h := by
    rw [hId_eq]
    by_cases hdeg_eq : a.natDegree = b.natDegree
    · exact hasPosLeadingCoeff_add_of_same_natDegree hdeg_eq ha_pos hb_pos
    · exact hasPosLeadingCoeff_add_of_natDegree_lt_right (lt_of_le_of_ne ha_le hdeg_eq) hb_pos
  have ht_ne : t ≠ 0 := by
    exact mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0
  have ht_pos : HasPosLeadingCoeff t := by
    dsimp [t]
    unfold HasPosLeadingCoeff at hb_pos ⊢
    rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul]
    exact hb_pos
  have hp_split : p = h + t := by
    calc
      p = a + X * b := hp_eq
      _ = (a + b) + (X - C (1 : ℝ)) * b := by
        rw [sub_mul]
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = h + (X - C (1 : ℝ)) * b := by rw [hId_eq]
  have hall_hp : AllComboRealRooted h p := allComboRealRooted_of_prec hIdp
  have hall_ht : AllComboRealRooted h t := by
    intro α β
    have hrew :
        C α * h + C β * t =
          C (α - β) * h + C β * p := by
      rw [hp_split]
      rw [mul_add]
      have hC : C (α - β) + C β = C α := by
        rw [← C_add]
        congr 1
        ring
      calc
        C α * h + C β * t = (C (α - β) + C β) * h + C β * t := by rw [hC]
        _ = C (α - β) * h + (C β * h + C β * t) := by
          rw [add_mul]
          ac_rfl
    simpa [hrew] using hall_hp (α - β) β
  have ht_rr : IsRealRooted t := by
    rcases hall_ht 0 1 with hzero | hrr
    · exact False.elim (ht_ne (by simpa [t] using hzero))
    · simpa [t] using hrr
  have hb_rr : IsRealRooted b := by
    apply isRealRooted_of_dvd ht_rr hb0
    refine ⟨X - C (1 : ℝ), ?_⟩
    dsimp [t]
    rw [mul_comm]
  have hb_le : ∀ s ∈ b.roots, s ≤ (1 : ℝ) := by
    intro s hs
    have hs0 := roots_nonpos_of_nonneg_coeffs hb_rr hb_nonneg s hs
    linarith
  have hh_le : ∀ s ∈ h.roots, s ≤ (1 : ℝ) := by
    intro s hs
    have hs0 := roots_nonpos_of_nonneg_coeffs hh_rr hh_nonneg s hs
    linarith
  have ht_deg : h.natDegree + 1 = t.natDegree := by
    dsimp [t]
    rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C]
    omega
  have hht_or : Prec h t ∨ Prec t h := by
    exact prec_of_allComboRealRooted hh_rr ht_rr hall_ht (Or.inl ht_deg)
  have hnot_rev : ¬ Prec t h := by
    intro hth
    have hbounds := natDegree_bounds_of_prec hth
    have hbad : h.natDegree + 1 ≤ h.natDegree := by
      simpa [ht_deg] using hbounds.1
    omega
  have hht : Prec h t := by
    rcases hht_or with hht | hth
    · exact hht
    · exact False.elim (hnot_rev hth)
  have hbh : Prec b h := by
    exact prec_of_prec_mul_X_sub_C_of_sameDegree_of_roots_le (1 : ℝ)
      hht hh_deg.symm hb_pos hh_pos hb_le hh_le
  have hbt : Prec b t := by
    exact prec_sameDegree_to_prec_mul_X_sub_C_of_roots_le (1 : ℝ)
      (prec_refl hb_rr) rfl hb_pos hb_pos hb_le hb_le
  have hbp_sum : Prec b [h, t].sum := by
    refine prec_sum_left_of_common_left [h, t] b ?_ hb_pos ?_ ?_
    · intro q hq
      simp at hq
      rcases hq with rfl | rfl
      · exact hbh
      · exact hbt
    · intro q hq
      simp at hq
      rcases hq with rfl | rfl
      · exact hh_pos
      · exact ht_pos
    · simp
  simpa [List.sum_cons, hp_split] using hbp_sum

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
          omega
        have hd2 : 2 ≤ d := by
          have : 0 < d - 1 := lt_of_le_of_lt (Nat.zero_le _) hb_lt
          omega
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
          intro q a' b' hqdeg hidq ha'_nonneg hb'_nonneg ha'0 hb'0
          exact ih (d - 2) (by omega) q a' b' hqdeg hidq ha'_nonneg hb'_nonneg ha'0 hb'0
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
