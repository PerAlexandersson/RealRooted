module

public import RealRooted.SimpleRoots
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import RealRooted.MaWang.Strong
import Mathlib.Tactic

/-!
# Signed-arrow Chebyshev polynomials

For a real symmetric matrix `D` with spectrum in `[-2, 2]`, we prove simplicity
and consecutive interlacing for the corner entries of `U_n(A(x)/2)`, where
`A(x) = [[x, vᵀ], [-v, D]]`. There is no restriction on `v`.
Source: unpublished manuscript, `toeplitz-chebyshev-sturm-20261029.md`, Theorem 1.

The proof uses the matrix Turán identity at a zero of a single corner entry.
Its neighboring entries have opposite signs, so the root-sign induction applies
directly, without a deformation argument.
-/

@[expose] public section

open Polynomial Matrix
open scoped BigOperators

noncomputable section

namespace RealRooted.Toeplitz.SignedArrow

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The signed-arrow matrix, with distinguished coordinate `none`. -/
def arrow {R : Type*} [Ring R] (D : Matrix ι ι R) (v : ι → R) (x : R) :
    Matrix (Option ι) (Option ι) R
  | none, none => x
  | none, some j => v j
  | some i, none => -v i
  | some i, some j => D i j

/-- The matrix-valued monic Chebyshev sequence `S_n(A) = U_n(A/2)`. -/
def chebMatrix {R : Type*} [CommRing R] [Algebra ℝ R]
    (D : Matrix ι ι R) (v : ι → R) (x : R) (n : ℕ) :
    Matrix (Option ι) (Option ι) R :=
  aeval (arrow D v x) (Chebyshev.S ℝ n)

/-- The polynomial whose value is the distinguished corner of `U_n(A(x)/2)`. -/
def row (D : Matrix ι ι ℝ) (v : ι → ℝ) (n : ℕ) : ℝ[X] :=
  chebMatrix (D.map C) (fun i => C (v i)) X n none none

@[simp] private lemma chebMatrix_zero {R : Type*} [CommRing R] [Algebra ℝ R]
    (D : Matrix ι ι R) (v : ι → R) (x : R) : chebMatrix D v x 0 = 1 := by
  simp [chebMatrix]

@[simp] private lemma chebMatrix_one {R : Type*} [CommRing R] [Algebra ℝ R]
    (D : Matrix ι ι R) (v : ι → R) (x : R) : chebMatrix D v x 1 = arrow D v x := by
  simp [chebMatrix]

private lemma chebMatrix_add_two {R : Type*} [CommRing R] [Algebra ℝ R]
    (D : Matrix ι ι R) (v : ι → R) (x : R) (n : ℕ) :
    chebMatrix D v x (n + 2) = arrow D v x * chebMatrix D v x (n + 1) -
      chebMatrix D v x n := by
  simp [chebMatrix, Nat.cast_add, Chebyshev.S_add_two]

private lemma commute_chebMatrix {R : Type*} [CommRing R] [Algebra ℝ R]
    (D : Matrix ι ι R) (v : ι → R) (x : R) (n : ℕ) :
    Commute (arrow D v x) (chebMatrix D v x n) := by
  have h := (Commute.all (X : ℝ[X]) (Chebyshev.S ℝ n)).map (aeval (arrow D v x))
  simpa [chebMatrix] using h

private def signature : Matrix (Option ι) (Option ι) ℝ :=
  diagonal fun i => Option.casesOn i 1 (fun _ => -1)

private lemma arrow_signature (D : Matrix ι ι ℝ) (hD : D.IsHermitian)
    (v : ι → ℝ) (x : ℝ) :
    (arrow D v x)ᵀ * signature = signature * arrow D v x := by
  ext i j
  cases i with
  | none => cases j <;> simp [signature, arrow]
  | some i =>
    cases j with
    | none => simp [signature, arrow]
    | some j =>
      simp only [signature, mul_diagonal, diagonal_mul, transpose_apply, arrow]
      have hs := congrArg (fun M => M i j) hD.eq
      simpa using hs

private lemma chebMatrix_signature (D : Matrix ι ι ℝ) (hD : D.IsHermitian)
    (v : ι → ℝ) (x : ℝ) (n : ℕ) :
    (chebMatrix D v x n)ᵀ * signature = signature * chebMatrix D v x n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using arrow_signature D hD v x
  | more n ih ih' =>
    rw [chebMatrix_add_two, transpose_sub, transpose_mul, sub_mul, mul_assoc,
      arrow_signature D hD v x, ← mul_assoc, ih', mul_assoc,
      ← (commute_chebMatrix D v x (n + 1)).eq, ih, mul_sub]

private lemma chebMatrix_first_row (D : Matrix ι ι ℝ) (hD : D.IsHermitian)
    (v : ι → ℝ) (x : ℝ) (n : ℕ) (i : ι) :
    chebMatrix D v x n none (some i) = -chebMatrix D v x n (some i) none := by
  have h := congrArg (fun M => M none (some i)) (chebMatrix_signature D hD v x n)
  simpa [signature] using h.symm

omit [DecidableEq ι] in
private lemma corner_mul {R : Type*} [CommRing R]
    (B C : Matrix (Option ι) (Option ι) R) :
    (B * C) none none = B none none * C none none +
      ∑ i, B none (some i) * C (some i) none := by
  simp [Matrix.mul_apply, Fintype.sum_option]

/-- The initial signed-arrow row is one. -/
@[simp] theorem row_zero (D : Matrix ι ι ℝ) (v : ι → ℝ) : row D v 0 = 1 := by
  simp [row]

/-- The first signed-arrow row is the variable. -/
@[simp] theorem row_one (D : Matrix ι ι ℝ) (v : ι → ℝ) : row D v 1 = X := by
  simp [row, arrow]

private lemma matrix_column_step {R : Type*} [CommRing R] [Algebra ℝ R]
    (D : Matrix ι ι R) (v : ι → R) (x : R) (n : ℕ) :
    chebMatrix D v x (n + 2) none none =
      x * chebMatrix D v x (n + 1) none none +
        ∑ i, v i * chebMatrix D v x (n + 1) (some i) none -
          chebMatrix D v x n none none := by
  simp [chebMatrix_add_two, Matrix.sub_apply, corner_mul, arrow]

private lemma matrix_lower_column_step {R : Type*} [CommRing R] [Algebra ℝ R]
    (D : Matrix ι ι R) (v : ι → R) (x : R) (n : ℕ) (i : ι) :
    chebMatrix D v x (n + 2) (some i) none =
      -v i * chebMatrix D v x (n + 1) none none +
        ∑ j, D i j * chebMatrix D v x (n + 1) (some j) none -
          chebMatrix D v x n (some i) none := by
  simp [chebMatrix_add_two, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_option, arrow]

private lemma row_monic_lower_degree (D : Matrix ι ι ℝ) (v : ι → ℝ) (n : ℕ) :
    (row D v n).IsMonicOfDegree n ∧
      ∀ i, (chebMatrix (D.map C) (fun j => C (v j)) X n (some i) none).natDegree ≤ n - 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [row]
  | one =>
    exact ⟨by simpa using Polynomial.isMonicOfDegree_X ℝ, by simp [arrow]⟩
  | more n ih ih' =>
    have htail : (∑ i, C (v i) *
        chebMatrix (D.map C) (fun j => C (v j)) X (n + 1) (some i) none).natDegree ≤ n := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i _
      exact (Polynomial.natDegree_C_mul_le _ _).trans (by simpa using ih'.2 i)
    constructor
    · change (chebMatrix (D.map C) (fun j => C (v j)) X (n + 2) none none).IsMonicOfDegree _
      rw [matrix_column_step]
      have hm := (Polynomial.isMonicOfDegree_X ℝ).mul ih'.1
      have hm' : (X * row D v (n + 1)).IsMonicOfDegree (n + 2) := by
        convert hm using 1; lia
      exact (hm'.add_right (by lia)).sub (by
        change (row D v n).natDegree < n + 2
        rw [ih.1.natDegree_eq]
        lia)
    · intro i
      rw [matrix_lower_column_step]
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · apply (Polynomial.natDegree_add_le _ _).trans
        apply max_le
        · simpa [row] using (Polynomial.natDegree_C_mul_le (-(v i))
            (row D v (n + 1))).trans (by rw [ih'.1.natDegree_eq])
        · apply Polynomial.natDegree_sum_le_of_forall_le
          intro j _
          exact (Polynomial.natDegree_C_mul_le _ _).trans
            ((ih'.2 j).trans (by lia))
      · exact (ih.2 i).trans (by lia)

/-- Every corner row is monic of degree equal to its index. -/
theorem row_isMonicOfDegree (D : Matrix ι ι ℝ) (v : ι → ℝ) (n : ℕ) :
    (row D v n).IsMonicOfDegree n :=
  (row_monic_lower_degree D v n).1

/-- Spectral containment gives the bilinear bound needed in the corner energy identity. -/
private theorem dotProduct_mulVec_le (D : Matrix ι ι ℝ) (hD : D.IsHermitian)
    (hsp : spectrum ℝ D ⊆ Set.Icc (-2 : ℝ) 2) (b c : ι → ℝ) :
    b ⬝ᵥ D *ᵥ c ≤ b ⬝ᵥ b + c ⬝ᵥ c := by
  have hpos : (4 - D ^ 2).PosSemidef := by
    let e := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hD.eigenvectorUnitary
    have he : (4 - D ^ 2 : Matrix ι ι ℝ) =
        e (4 - diagonal (RCLike.ofReal ∘ hD.eigenvalues) ^ 2) := by
      simp only [map_sub, map_ofNat, map_pow]
      rw [← hD.spectral_theorem]
    rw [he]
    change (hD.eigenvectorUnitary.val *
      (4 - diagonal (RCLike.ofReal ∘ hD.eigenvalues) ^ 2) *
        star hD.eigenvectorUnitary.val).PosSemidef
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    have heq : (4 - diagonal (RCLike.ofReal ∘ hD.eigenvalues) ^ 2 : Matrix ι ι ℝ) =
        diagonal (fun i => 4 - hD.eigenvalues i ^ 2) := by
      ext i j
      by_cases hij : i = j
      · subst j; simp [pow_two, Matrix.ofNat_apply]
      · simp [pow_two, Matrix.ofNat_apply, hij]
    rw [heq, posSemidef_diagonal_iff]
    intro i
    have hi := hsp (hD.eigenvalues_mem_spectrum_real i)
    nlinarith [hi.1, hi.2]
  have hc := hpos.dotProduct_mulVec_nonneg c
  have hs : 0 ≤ (2 • b - D *ᵥ c) ⬝ᵥ (2 • b - D *ᵥ c) := by
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have ht : (D *ᵥ c) ⬝ᵥ (D *ᵥ c) = c ⬝ᵥ (D ^ 2) *ᵥ c := by
    calc
      _ = c ⬝ᵥ Dᵀ *ᵥ (D *ᵥ c) := by rw [Matrix.dotProduct_transpose_mulVec]
      _ = _ := by rw [show Dᵀ = D from hD.eq, mulVec_mulVec, pow_two]
  simp only [sub_mulVec, Matrix.ofNat_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, star_trivial] at hc
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    dotProduct_comm (D *ᵥ c) b, ht] at hs
  norm_num only [nsmul_eq_mul, Nat.cast_ofNat] at hs
  nlinarith

private lemma map_chebMatrix (D : Matrix ι ι ℝ) (v : ι → ℝ) (x : ℝ) (n : ℕ) :
    (chebMatrix (D.map C) (fun i => C (v i)) X n).map (evalRingHom x) =
      chebMatrix D v x n := by
  let f := (Polynomial.aeval (R := ℝ) x).mapMatrix (m := Option ι)
  have hA : f (arrow (D.map C) (fun i => C (v i)) X) = arrow D v x := by
    ext i j
    cases i <;> cases j <;> simp [f, arrow]
  have h := congrArg (fun g => g (Chebyshev.S ℝ n))
    (Polynomial.aeval_algHom f (arrow (D.map C) (fun i => C (v i)) X))
  simpa [chebMatrix, hA, f] using h.symm

/-- Evaluation of the polynomial row is the corner of the matrix Chebyshev polynomial. -/
theorem eval_row (D : Matrix ι ι ℝ) (v : ι → ℝ) (x : ℝ) (n : ℕ) :
    (row D v n).eval x = chebMatrix D v x n none none := by
  exact congrArg (fun M => M none none) (map_chebMatrix D v x n)

/-- The monic normalization used here is exactly the second-kind Chebyshev
polynomial at half the signed-arrow matrix. -/
theorem chebMatrix_eq_U (D : Matrix ι ι ℝ) (v : ι → ℝ) (x : ℝ) (n : ℕ) :
    chebMatrix D v x n = aeval ((2 : ℝ)⁻¹ • arrow D v x) (Chebyshev.U ℝ n) := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  rw [chebMatrix, Chebyshev.S_eq_U_comp_half_mul_X, Polynomial.aeval_comp]
  simp [Algebra.smul_def]

private lemma chebMatrix_turan_reordered (D : Matrix ι ι ℝ) (v : ι → ℝ)
    (x : ℝ) (n : ℕ) :
    chebMatrix D v x (n + 1) ^ 2 + chebMatrix D v x n ^ 2 -
      chebMatrix D v x (n + 1) * arrow D v x * chebMatrix D v x n = 1 := by
  have ht : Chebyshev.S ℝ ((n : ℤ) + 1) ^ 2 + Chebyshev.S ℝ (n : ℤ) ^ 2 -
      Chebyshev.S ℝ ((n : ℤ) + 1) * X * Chebyshev.S ℝ (n : ℤ) = 1 := by
    linear_combination Chebyshev.S_sq_add_S_sq ℝ (n : ℤ)
  have h := congrArg (aeval (arrow D v x)) ht
  simpa [chebMatrix] using h

private lemma corner_energy (D : Matrix ι ι ℝ) (hD : D.IsHermitian)
    (v : ι → ℝ) (x : ℝ) (n : ℕ) (hx : chebMatrix D v x (n + 1) none none = 0) :
    let b := fun i => chebMatrix D v x (n + 1) (some i) none
    let c := fun i => chebMatrix D v x n (some i) none
    1 = -b ⬝ᵥ b - c ⬝ᵥ c + b ⬝ᵥ D *ᵥ c -
      chebMatrix D v x (n + 2) none none * chebMatrix D v x n none none := by
  let b := fun i => chebMatrix D v x (n + 1) (some i) none
  let c := fun i => chebMatrix D v x n (some i) none
  let q := chebMatrix D v x n none none
  let p := chebMatrix D v x (n + 2) none none
  have ht := congrArg (fun M => M none none) (chebMatrix_turan_reordered D v x n)
  have hs := matrix_column_step D v x n
  rw [hx, mul_zero, zero_add] at hs
  simp only [Matrix.sub_apply, Matrix.add_apply, pow_two,
    chebMatrix_first_row D hD v x, hx, mul_zero, zero_mul, zero_add,
    Matrix.mul_apply, Fintype.sum_option, arrow, Finset.sum_neg_distrib,
    neg_mul, mul_neg, Matrix.one_apply_eq] at ht
  have hcross : (∑ j, (∑ i, b i * D i j) * c j) = b ⬝ᵥ D *ᵥ c := by
    simp only [dotProduct, Matrix.mulVec]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hprod : (∑ i, b i * v i) * q = (p + q) * q := by
    have hsum : (∑ i, b i * v i) = p + q := by
      change p = (∑ i, v i * b i) - q at hs
      have heq : (∑ i, b i * v i) = ∑ i, v i * b i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      linarith
    rw [hsum]
  change -(b ⬝ᵥ b) + (q * q + -(c ⬝ᵥ c)) -
    -(-((∑ i, b i * v i) * q) + ∑ j, (∑ i, b i * D i j) * c j) = 1 at ht
  rw [hprod, hcross] at ht
  change 1 = (-b) ⬝ᵥ b - c ⬝ᵥ c + b ⬝ᵥ D *ᵥ c - p * q
  rw [neg_dotProduct]
  nlinarith

/-- The neighboring product at a row zero is at most minus one, uniformly in the coupling. -/
theorem eval_mul_le_neg_one (D : Matrix ι ι ℝ) (hD : D.IsHermitian)
    (hsp : spectrum ℝ D ⊆ Set.Icc (-2 : ℝ) 2) (v : ι → ℝ)
    (n : ℕ) (x : ℝ) (hx : (row D v (n + 1)).IsRoot x) :
    (row D v (n + 2)).eval x * (row D v n).eval x ≤ -1 := by
  rw [Polynomial.IsRoot.def, eval_row] at hx
  have he := corner_energy D hD v x n hx
  have hb := dotProduct_mulVec_le D hD hsp
    (fun i => chebMatrix D v x (n + 1) (some i) none)
    (fun i => chebMatrix D v x n (some i) none)
  dsimp only at he
  rw [eval_row, eval_row]
  simp only [neg_dotProduct] at he
  linarith

/-- At each zero of a positive-index row, its neighboring rows have opposite signs. -/
theorem eval_mul_neg (D : Matrix ι ι ℝ) (hD : D.IsHermitian)
    (hsp : spectrum ℝ D ⊆ Set.Icc (-2 : ℝ) 2) (v : ι → ℝ)
    (n : ℕ) (x : ℝ) (hx : (row D v (n + 1)).IsRoot x) :
    (row D v (n + 2)).eval x * (row D v n).eval x < 0 := by
  exact lt_of_le_of_lt (eval_mul_le_neg_one D hD hsp v n x hx) (by norm_num)

/-- Consecutive signed-arrow corner rows have no common real root. -/
theorem not_isRoot_succ (D : Matrix ι ι ℝ) (hD : D.IsHermitian)
    (hsp : spectrum ℝ D ⊆ Set.Icc (-2 : ℝ) 2) (v : ι → ℝ)
    (n : ℕ) (x : ℝ) (hx : (row D v n).IsRoot x) :
    ¬ (row D v (n + 1)).IsRoot x := by
  cases n with
  | zero => simp at hx
  | succ n =>
    intro hn
    have hs := eval_mul_neg D hD hsp v n x hx
    simp [hn.eq_zero] at hs

/-- The degree of a signed-arrow corner row is its index. -/
@[simp] theorem row_natDegree (D : Matrix ι ι ℝ) (v : ι → ℝ) (n : ℕ) :
    (row D v n).natDegree = n := (row_isMonicOfDegree D v n).natDegree_eq

/-- The signed-arrow Chebyshev theorem: consecutive rows interlace and both
have simple real roots. The spectral interval is closed and the coupling is arbitrary. -/
theorem strictInterl (D : Matrix ι ι ℝ) (hD : D.IsHermitian)
    (hsp : spectrum ℝ D ⊆ Set.Icc (-2 : ℝ) 2) (v : ι → ℝ) (n : ℕ) :
    StrictInterl (row D v n) (row D v (n + 1)) ∧
      HasSimpleRoots (row D v n) ∧ HasSimpleRoots (row D v (n + 1)) := by
  have hpos (k : ℕ) : HasPosLeadingCoeff (row D v k) := by
    change 0 < (row D v k).leadingCoeff
    rw [(row_isMonicOfDegree D v k).monic.leadingCoeff]
    exact zero_lt_one
  have hinter : ∀ k : ℕ, Interlaces (row D v k) (row D v (k + 1)) := by
    intro k
    induction k with
    | zero => simp [Interlaces, ListInterlaces]
    | succ k ih =>
      exact (MaWang.strictInterl_of_interlaces_eval_mul_neg_succ ih (hpos k)
        (hpos (k + 2)) (by simp) (eval_mul_neg D hD hsp v k)).toInterlaces (by simp)
  have hno : ∀ x : ℝ, ¬ ((row D v n).IsRoot x ∧ (row D v (n + 1)).IsRoot x) :=
    fun x hx => not_isRoot_succ D hD hsp v n x hx.1 hx.2
  exact ⟨(hinter n).toStrictInterl,
    (hinter n).toStrictInterl.hasSimpleRoots_of_no_common_root hno⟩

/-- Every signed-arrow corner row has exactly its index many distinct real zeros. -/
theorem roots_card (D : Matrix ι ι ℝ) (hD : D.IsHermitian)
    (hsp : spectrum ℝ D ⊆ Set.Icc (-2 : ℝ) 2) (v : ι → ℝ) (n : ℕ) :
    (row D v n).Splits ∧ (row D v n).roots.Nodup ∧ (row D v n).roots.card = n := by
  obtain ⟨hi, hs, _⟩ := strictInterl D hD hsp v n
  exact ⟨hi.1.2, hs.roots_nodup, by
    rw [Polynomial.splits_iff_card_roots.mp hi.1.2, row_natDegree]⟩

end RealRooted.Toeplitz.SignedArrow
