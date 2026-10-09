import RealRooted.Hadamard.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Vieta

open Polynomial

namespace RealRooted
namespace Kostov

noncomputable section

/-!
# Kostov's coefficient map for the Schur–Szegő composition

Fix `n ≥ 2` and write a monic `P` of degree `n` with `P(-1) = 0` as
`(X + 1)(X^(n-1) + c₁ X^(n-2) + ⋯ + c_(n-1))`.  If `P = K_(a₁) * ⋯ * K_(a_(n-1))` is a
Schur–Szegő factorization with `K_a = (X+1)^(n-1)(X+a)`, then the interior coefficients of `P`
are an affine function of the elementary symmetric functions `σ_j(a)`
(`interiorCoeff_composition`).  The linear part is a scaled Vandermonde matrix in the ratios
`(n-k)/k`, hence invertible (`det_coeffMatrix_ne_zero`), so `coeffMap` recovers `σ(a)` from
`c` (`coeffMap_eq_sigma`).

Reference: V. P. Kostov, *Eigenvectors in the context of the Schur–Szegő composition of
polynomials*, Math. Balkanica 22 (2008), 155–173, §5.1.
-/

/-- The composition factor `K_a = (X + 1)^(n - 1) (X + a)`. -/
def factor (n : ℕ) (a : ℝ) : ℝ[X] := (X + 1) ^ (n - 1) * (X + C a)

/-- The monic polynomial `P` obtained from the coefficient vector `c`. -/
def monicPolynomial (n : ℕ) (c : Fin (n - 1) → ℝ) : ℝ[X] :=
  (X + 1) *
    (X ^ (n - 1) + ∑ i : Fin (n - 1), C (c i) * X ^ (n - 2 - i.1))

/-- The coefficient of `X^(i+1)` used in the interior coefficient system. -/
def interiorCoeff (n : ℕ) (p : ℝ[X]) (i : Fin (n - 1)) : ℝ :=
  p.coeff (i.1 + 1)

/--
The coefficient matrix taking the elementary symmetric functions of the
composition parameters to the interior coefficients of their CSS product.

The row `i` corresponds to `k=i+1`, and the column `j` to `σ_(j+1)`.
-/
def coeffMatrix (n : ℕ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  fun i j =>
    ((Nat.choose (n - 1) (i.1 + 1) : ℝ) ^ (j.1 + 1) *
        (Nat.choose (n - 1) i.1 : ℝ) ^ (n - 2 - j.1)) /
      (Nat.choose n (i.1 + 1) : ℝ) ^ (n - 2)

/-- The affine constant coming from the leading symmetric function `σ₀=1`. -/
def coeffConstant (n : ℕ) (i : Fin (n - 1)) : ℝ :=
  (Nat.choose (n - 1) i.1 : ℝ) ^ (n - 1) /
    (Nat.choose n (i.1 + 1) : ℝ) ^ (n - 2)

/-- The ratio `b_k / d_k`, written as `(n-k)/k` for `k=i+1`. -/
private def ratio (n : ℕ) (i : Fin (n - 1)) : ℝ :=
  ((n - (i.1 + 1) : ℕ) : ℝ) / ((i.1 + 1 : ℕ) : ℝ)

/-- The row scale in the Vandermonde factorization of the coefficient matrix. -/
private def rowScale (n : ℕ) (i : Fin (n - 1)) : ℝ :=
  ((Nat.choose (n - 1) i.1 : ℝ) ^ (n - 1) /
      (Nat.choose n (i.1 + 1) : ℝ) ^ (n - 2)) * ratio n i

/-- The explicit coefficient realization of Kostov's affine map. -/
def coeffMap (n : ℕ) (c : Fin (n - 1) → ℝ) : Fin (n - 1) → ℝ :=
  (coeffMatrix n)⁻¹.mulVec
    (interiorCoeff n (monicPolynomial n c) - coeffConstant n)

/-- The CSS product of a list of Kostov composition factors. -/
def composition (n : ℕ) : List ℝ → ℝ[X]
  | [] => (X + 1) ^ n
  | a :: as => schurSzegoComp n (factor n a) (composition n as)

/-- The elementary-symmetric coordinates of a list of composition parameters. -/
def sigma (n : ℕ) (a : List ℝ) (j : Fin (n - 1)) : ℝ :=
  (a : Multiset ℝ).esymm (j.1 + 1)

private theorem kostov_choose_prev_pos {n : ℕ}
    (i : Fin (n - 1)) : 0 < Nat.choose (n - 1) i.1 := by
  exact Nat.choose_pos (Nat.le_of_lt i.isLt)

private theorem kostov_choose_pos {n : ℕ} (hn : 2 ≤ n)
    (i : Fin (n - 1)) : 0 < Nat.choose n (i.1 + 1) := by
  apply Nat.choose_pos
  exact (Nat.succ_le_of_lt i.isLt).trans (by lia)

private theorem kostov_ratio_eq_choose_ratio {n : ℕ} (hn : 2 ≤ n)
    (i : Fin (n - 1)) :
    ratio n i =
      (Nat.choose (n - 1) (i.1 + 1) : ℝ) /
        (Nat.choose (n - 1) i.1 : ℝ) := by
  have hki : i.1 + 1 ≤ n - 1 := Nat.succ_le_of_lt i.isLt
  have hkn : i.1 + 1 ≤ n := hki.trans (by lia)
  have hdi : (Nat.choose (n - 1) i.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (kostov_choose_prev_pos i))
  have hki0 : (i.1 + 1 : ℝ) ≠ 0 := by positivity
  have hrec := Nat.choose_succ_right_eq (n - 1) i.1
  have hsub : n - 1 - i.1 = n - (i.1 + 1) := by lia
  have hrec' :
      (Nat.choose (n - 1) (i.1 + 1) : ℝ) * (i.1 + 1 : ℝ) =
        (Nat.choose (n - 1) i.1 : ℝ) * (n - 1 - i.1 : ℕ) := by
    exact_mod_cast hrec
  rw [hsub] at hrec'
  rw [Nat.cast_sub hkn] at hrec'
  rw [ratio]
  rw [Nat.cast_sub hkn]
  field_simp [hdi, hki0]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hrec'.symm

private theorem kostov_ratio_strict {n : ℕ}
    {i j : Fin (n - 1)} (hlt : i < j) : ratio n j < ratio n i := by
  have hlt' : i.1 + 1 < j.1 + 1 := by lia
  have hik : (i.1 + 1 : ℝ) < (j.1 + 1 : ℝ) := by exact_mod_cast hlt'
  have hkn : i.1 + 1 ≤ n := by lia
  have hkn' : j.1 + 1 ≤ n := by lia
  have hi0 : (i.1 + 1 : ℝ) > 0 := by positivity
  have hj0 : (j.1 + 1 : ℝ) > 0 := by positivity
  simp only [ratio]
  rw [Nat.cast_sub hkn, Nat.cast_sub hkn']
  norm_num only [Nat.cast_add, Nat.cast_one]
  refine (div_lt_div_iff₀ (a := (n : ℝ) - ((j.1 : ℝ) + 1))
    (c := (n : ℝ) - ((i.1 : ℝ) + 1)) hj0 hi0).2 ?_
  have hn0 : 0 < n := by lia
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  nlinarith

private theorem ratio_injective {n : ℕ} :
    Function.Injective (ratio n) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (ne_of_lt (kostov_ratio_strict hlt)) hij.symm
  · exact (ne_of_lt (kostov_ratio_strict hgt)) hij

private theorem coeffMatrix_eq_scaledVandermonde {n : ℕ}
    (hn : 2 ≤ n) :
    coeffMatrix n = Matrix.of (fun i j =>
      rowScale n i * (ratio n i) ^ j.1) := by
  ext i j
  have hdi : (Nat.choose (n - 1) i.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (kostov_choose_prev_pos i))
  have hci : (Nat.choose n (i.1 + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (kostov_choose_pos hn i))
  change ((Nat.choose (n - 1) (i.1 + 1) : ℝ) ^ (j.1 + 1) *
      (Nat.choose (n - 1) i.1 : ℝ) ^ (n - 2 - j.1)) /
      (Nat.choose n (i.1 + 1) : ℝ) ^ (n - 2) =
    rowScale n i * (ratio n i) ^ j.1
  rw [rowScale, kostov_ratio_eq_choose_ratio hn]
  rw [div_pow]
  field_simp [hdi, hci]
  have hde : n - 2 - j.1 + 1 + j.1 = n - 1 := by lia
  have hdexp :
      (Nat.choose (n - 1) i.1 : ℝ) ^ (n - 2 - j.1) *
          (Nat.choose (n - 1) i.1 : ℝ) *
          (Nat.choose (n - 1) i.1 : ℝ) ^ j.1 =
        (Nat.choose (n - 1) i.1 : ℝ) ^ (n - 1) := by
    rw [← pow_succ, ← pow_add, hde]
  have hbexp :
      (Nat.choose (n - 1) (i.1 + 1) : ℝ) ^ (j.1 + 1) =
        (Nat.choose (n - 1) (i.1 + 1) : ℝ) ^ j.1 *
          Nat.choose (n - 1) (i.1 + 1) := by
    rw [pow_succ]
  rw [hbexp]
  calc
    _ = (Nat.choose (n - 1) (i.1 + 1) : ℝ) ^ j.1 *
          Nat.choose (n - 1) (i.1 + 1) *
          ((Nat.choose (n - 1) i.1 : ℝ) ^ (n - 2 - j.1) *
            (Nat.choose (n - 1) i.1 : ℝ) *
            (Nat.choose (n - 1) i.1 : ℝ) ^ j.1) := by ring
    _ = (Nat.choose (n - 1) (i.1 + 1) : ℝ) ^ j.1 *
          Nat.choose (n - 1) (i.1 + 1) *
          (Nat.choose (n - 1) i.1 : ℝ) ^ (n - 1) := by rw [hdexp]
    _ = _ := by ring

/-- The coefficient matrix is invertible for every ambient degree. -/
theorem det_coeffMatrix_ne_zero (n : ℕ) :
    (coeffMatrix n).det ≠ 0 := by
  classical
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n =>
      have hn : 2 ≤ n.succ.succ := by lia
      rw [coeffMatrix_eq_scaledVandermonde hn]
      change (Matrix.of (fun i j =>
        rowScale n.succ.succ i *
          Matrix.vandermonde (ratio n.succ.succ) i j)).det ≠ 0
      rw [Matrix.det_mul_column]
      apply mul_ne_zero
      · apply (Finset.prod_ne_zero_iff).2
        intro i hi
        dsimp [rowScale]
        apply mul_ne_zero
        · apply div_ne_zero
          · exact pow_ne_zero _ (by
              exact_mod_cast (Nat.ne_of_gt (kostov_choose_prev_pos i)))
          · exact pow_ne_zero _ (by
              exact_mod_cast (Nat.ne_of_gt (kostov_choose_pos hn i)))
        · have hnum : 0 < n.succ.succ - (i.1 + 1) := by lia
          dsimp [ratio]
          apply div_ne_zero
          · exact_mod_cast (Nat.ne_of_gt hnum)
          · exact_mod_cast (Nat.succ_ne_zero i.1)
      · exact (Matrix.det_vandermonde_ne_zero_iff).2 ratio_injective

/-- The interior coefficient of one composition factor. -/
theorem coeff_factor_succ (n k : ℕ) (a : ℝ) :
    (factor n a).coeff (k + 1) =
      (Nat.choose (n - 1) k : ℝ) +
        (Nat.choose (n - 1) (k + 1) : ℝ) * a := by
  rw [factor, mul_add, coeff_add, coeff_mul_X, coeff_mul_C]
  simp only [coeff_X_add_one_pow]

/-- The CSS coefficient formula for a Kostov composition factor. -/
theorem coeff_schurSzegoComp_factor_succ {n k : ℕ} (hk : k + 1 ≤ n)
    (f : ℝ[X]) (a : ℝ) :
    (schurSzegoComp n f (factor n a)).coeff (k + 1) =
      f.coeff (k + 1) *
          ((Nat.choose (n - 1) k : ℝ) +
            (Nat.choose (n - 1) (k + 1) : ℝ) * a) /
        (Nat.choose n (k + 1) : ℝ) := by
  rw [coeff_schurSzegoComp_of_le hk, coeff_factor_succ]

private theorem kostov_esymm_map (a : Multiset ℝ) (b : ℝ) (j : ℕ) :
    (a.map (fun x => b * x)).esymm j =
      b ^ j * a.esymm j := by
  change (a.map (b • ·)).esymm j = _
  rw [← Multiset.pow_smul_esymm]
  simp only [smul_eq_mul]

private theorem kostov_prod_affine (a : Multiset ℝ) (d b : ℝ) :
    (a.map (fun x => d + b * x)).prod =
      ∑ j ∈ Finset.range (a.card + 1),
        (a.esymm j * b ^ j * d ^ (a.card - j)) := by
  have h := Multiset.prod_X_add_C_eq_sum_esymm
    (a.map (fun x => b • x))
  have heval := congrArg (fun p : ℝ[X] => p.eval d) h
  rw [Polynomial.eval_multiset_prod] at heval
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_C_mul, Polynomial.eval_X_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Multiset.card_map,
    Multiset.map_map, Function.comp_apply, smul_eq_mul] at heval
  simpa only [kostov_esymm_map, mul_assoc, mul_comm, mul_left_comm] using heval

private theorem kostov_sum_split (n : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n + 1), f j) =
      f 0 + ∑ j : Fin n, f (j.1 + 1) := by
  rw [Finset.sum_range_succ']
  rw [← Fin.sum_univ_eq_sum_range]
  rw [add_comm]

private theorem coeff_composition_succ (n k : ℕ) (a : List ℝ)
    (hk : k + 1 ≤ n) :
    (composition n a).coeff (k + 1) =
      (Nat.choose n (k + 1) : ℝ) *
          ((a : Multiset ℝ).map (fun x =>
            (Nat.choose (n - 1) k : ℝ) +
              (Nat.choose (n - 1) (k + 1) : ℝ) * x)).prod /
        (Nat.choose n (k + 1) : ℝ) ^ a.length := by
  induction a with
  | nil =>
      simp [composition, coeff_X_add_one_pow]
  | cons x xs ih =>
      rw [composition, schurSzegoComp_comm,
        coeff_schurSzegoComp_factor_succ hk, ih]
      rw [← Multiset.cons_coe]
      simp only [List.length_cons, Multiset.map_cons, Multiset.prod_cons]
      have hc : (Nat.choose n (k + 1) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hk)
      field_simp [hc]
      ring

/-- The composition coefficients are the stated affine function of the
elementary-symmetric coordinates of its factors. -/
theorem interiorCoeff_composition (n : ℕ) (a : List ℝ)
    (ha : a.length = n - 1) :
    interiorCoeff n (composition n a) =
      (coeffMatrix n).mulVec (sigma n a) + coeffConstant n := by
  funext i
  have hki : i.1 + 1 ≤ n := by lia
  change (composition n a).coeff (i.1 + 1) =
    ((coeffMatrix n).mulVec (sigma n a) + coeffConstant n) i
  rw [coeff_composition_succ n i.1 a hki, kostov_prod_affine,
    Multiset.coe_card, ha, kostov_sum_split]
  dsimp [coeffMatrix, sigma, coeffConstant, Matrix.mulVec,
    dotProduct]
  have hc : (Nat.choose n (i.1 + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hki)
  have hc' : (Nat.choose n (1 + i.1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by lia))
  have hd : (Nat.choose (n - 1) i.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (kostov_choose_prev_pos i))
  have he0 : (a : Multiset ℝ).esymm 0 = 1 := by
    simp [Multiset.esymm]
  have hpow : ∀ j : Fin (n - 1), n - 1 - (j.1 + 1) = n - 2 - j.1 := by
    intro j
    lia
  rw [he0]
  simp_rw [hpow]
  have hc2 : (Nat.choose n (1 + i.1) : ℝ) ^ (n - 2) ≠ 0 :=
    pow_ne_zero _ hc'
  field_simp [hc, hc', hc2, hd]
  rw [← Finset.sum_div]
  field_simp [hc2]
  have hCpow :
      (Nat.choose n (i.1 + 1) : ℝ) ^ (n - 1) =
        (Nat.choose n (i.1 + 1) : ℝ) ^ (n - 2) *
          Nat.choose n (i.1 + 1) := by
    calc
      (Nat.choose n (i.1 + 1) : ℝ) ^ (n - 1) =
          (Nat.choose n (i.1 + 1) : ℝ) ^ (n - 2 + 1) := by
            congr 1
            lia
      _ = _ := by rw [pow_succ]
  rw [hCpow]
  simp only [mul_comm, mul_left_comm, mul_assoc]
  congr 2
  rw [add_comm]

/-- The inverse matrix recovers the interior coefficient vector. -/
theorem coeffMatrix_mulVec_coeffMap (n : ℕ)
    (c : Fin (n - 1) → ℝ) :
    (coeffMatrix n).mulVec (coeffMap n c) =
      interiorCoeff n (monicPolynomial n c) - coeffConstant n := by
  have hdet : IsUnit (coeffMatrix n).det :=
    isUnit_iff_ne_zero.mpr (det_coeffMatrix_ne_zero n)
  rw [coeffMap, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv (coeffMatrix n) hdet,
    Matrix.one_mulVec]

/-- The coefficient map recovers the elementary-symmetric coordinates of a
factorization with the prescribed composition polynomial. -/
theorem coeffMap_eq_sigma (n : ℕ) (c : Fin (n - 1) → ℝ) (a : List ℝ)
    (ha : a.length = n - 1)
    (hfactor : composition n a = monicPolynomial n c) :
    coeffMap n c = sigma n a := by
  have hcomposition :
      (coeffMatrix n).mulVec (sigma n a) =
        interiorCoeff n (composition n a) - coeffConstant n := by
    rw [interiorCoeff_composition n a ha]
    abel
  have hpolynomial :
      (coeffMatrix n).mulVec (sigma n a) =
        interiorCoeff n (monicPolynomial n c) - coeffConstant n := by
    rw [← hfactor]
    exact hcomposition
  apply Matrix.mulVec_injective_of_det_ne_zero (det_coeffMatrix_ne_zero n)
  rw [coeffMatrix_mulVec_coeffMap, hpolynomial]

end
end Kostov
end RealRooted
