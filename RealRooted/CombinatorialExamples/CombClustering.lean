module

public import RealRooted.PFPolynomial
public import RealRooted.SimpleRoots
public import Mathlib.Analysis.Real.Sqrt
import RealRooted.PolyaFrequencyConvolution
import RealRooted.OscillatoryInterlacing
import RealRooted.Schur.MinorPositivity
import RealRooted.CubicDiscriminant
import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Hessenberg
import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.DeterminantPencil
import RealRooted.Mathlib.LinearAlgebra.Matrix.LeadingSections
import RealRooted.MatrixInterlacing.ThreeBidiagonalProduction
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Charpoly
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Spectrum
public import RealRooted.Toeplitz.SignedPerturbation.Chebyshev
public import Mathlib.RingTheory.PowerSeries.Inverse
import RealRooted.Toeplitz.SignedPerturbation.Factorization
import RealRooted.Toeplitz.RowDifferenceDeterminant
import RealRooted.Basic.AffineInterlacing
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/-!
# Comb clustering polynomials at edge caps two to five

Let `B_n^{(s)}(t)` count vertex-disjoint packings of connected edge sets with one
through `s` edges on the comb with `n` spine vertices, each carrying one pendant leaf,
with weight `t` per piece. RealRooted issue #2648 (parent #2646) asks for simple
negative zeros and strict interlacing of consecutive rows for `s = 2, 3, 4, 5`, and
for the root bound `(-16, 0)` at `s = 4`.

## Definition by the interval recurrence

We *define* the rows by the first-interval recurrence of the issue. Each piece
occupies an interval of `j + 1` spine vertices, and `kernel s` records the number of
admissible pieces on such an interval as its coefficient at `z ^ j`:

* `s = 2`: `K = 1 + 3z + z²`;
* `s = 3`: `K = 1 + 4z + 4z² + z³`;
* `s = 4`: `K = 1 + 4z + 7z² + 5z³ + z⁴`;
* `s = 5`: `K = 1 + 4z + 8z² + 11z³ + 6z⁴ + z⁵`.

Then `row K 0 = 1` and `row K (n + 1) = row K n + t ∑_{j ≤ n} [z^(n-j)]K · row K j`, so
the ordinary generating function is `1 / (1 - z - t z K(z))`
(`rowSeries_mul_denominator`). The counting bridge, i.e. the identification of
these rows with the graph-packing enumerators, is out of scope here: it is a
separate combinatorial bijection and is not assumed anywhere.

## Main results

* `row_eq_det`: the rows are the leading determinants of a lower-Hessenberg pencil,
  for kernels of any length.
* `row_roots_of_isPFPolynomial`: for a Pólya-frequency kernel with `K(0) = 1` and
  `K'(0) > 0`, every row has simple negative zeros, and consecutive rows interlace
  with disjoint zero sets (hence strictly).
* `polynomial_roots_of_two_or_three`: the full statement at caps two and three.
* `polynomial_four_roots`: the full statement at cap four, including the bound
  `(-16, 0)`, via the shifted kernel `zK(z) + (1 - z)/16 = (1 + 2z)²(1 + 11z + 16z² + 4z³)/16`.
* Cap five: only ingredients of the pole-separation proof are formalized
  (`polynomial_five_monic_natDegree_roots`, `rowSeries_mul_denominator`,
  `row_eval_eq_chebyshev_sum`, `five_denominator_division`, `quarticMajorant_tail`).

## Proof route

Write `S` for the upper shift. Then `B_n(t) = det(I - S + t K(D)) = det(I + t A_n)` with
`A_n = K(D) (I - S)⁻¹`. The lower Toeplitz factor is totally nonnegative when `K` is PF,
and `(I - S)⁻¹` is the upper all-ones matrix. The oscillation theorem
`Matrix.IsTotallyNonneg.leading_charpoly_strictInterlaces` gives simple positive
eigenvalues interlacing strictly with those of the leading section `A_{n-1}`; their
negative reciprocals are the zeros of `B_n`. At cap four we apply the same theorem to
`A_n - I/16`, a product of a totally nonnegative Toeplitz section and the all-ones matrix.

The strict-interlacing argument follows issue #2648; the oscillatory criterion is
from Gantmacher–Krein (see `RealRooted.OscillatoryInterlacing`).
-/

@[expose] public section

open Polynomial Matrix BigOperators

noncomputable section

namespace RealRooted.CombClustering

/-- The interval kernel: its coefficient at `j` counts pieces occupying `j + 1`
spine vertices. The four supported edge caps are 2, 3, 4, and 5. -/
def kernel : ℕ → ℝ[X]
  | 2 => 1 + 3 * X + X ^ 2
  | 3 => 1 + 4 * X + 4 * X ^ 2 + X ^ 3
  | 4 => 1 + 4 * X + 7 * X ^ 2 + 5 * X ^ 3 + X ^ 4
  | 5 => 1 + 4 * X + 8 * X ^ 2 + 11 * X ^ 3 + 6 * X ^ 4 + X ^ 5
  | _ => 1

/-- Rows of `1 / (1 - z - t z K(z))`, defined by the first-interval recurrence.
The finite sum includes exactly the admissible nonnegative preceding indices. -/
def row (K : ℝ[X]) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => row K n + X * ∑ j : Fin (n + 1), C (K.coeff (n - j.val)) * row K j.val
termination_by n => n

/-- The recurrence polynomial at edge cap `s` and spine length `n`. -/
def polynomial (s n : ℕ) : ℝ[X] := row (kernel s) n

/-- The empty comb has just the empty packing. -/
@[simp] theorem row_zero (K : ℝ[X]) : row K 0 = 1 := by
  rw [row]

/-- Decomposition at the first occupied spine interval. -/
theorem row_succ (K : ℝ[X]) (n : ℕ) :
    row K (n + 1) = row K n +
      X * ∑ j : Fin (n + 1), C (K.coeff (n - j.val)) * row K j.val := by
  rw [row]

/-- Every recurrence row has constant coefficient one. -/
@[simp] theorem coeff_row_zero (K : ℝ[X]) (n : ℕ) : (row K n).coeff 0 = 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [row_succ, ih]

/-- No recurrence row vanishes. -/
theorem row_ne_zero (K : ℝ[X]) (n : ℕ) : row K n ≠ 0 := by
  intro h
  have := coeff_row_zero K n
  simp [h] at this

/-- The recurrence has degree at most the spine length. -/
theorem natDegree_row_le (K : ℝ[X]) (n : ℕ) : (row K n).natDegree ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [row_succ]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · exact (ih n (by lia)).trans (by lia)
      · apply (Polynomial.natDegree_mul_le).trans
        rw [Polynomial.natDegree_X]
        have hsum : (∑ j : Fin (n + 1),
            C (K.coeff (n - j.val)) * row K j.val).natDegree ≤ n := by
          apply Polynomial.natDegree_sum_le_of_forall_le
          intro j _
          exact (Polynomial.natDegree_C_mul_le _ _).trans
            ((ih j.val j.isLt).trans (by have := j.isLt; lia))
        lia

/-- If the single-tooth weight is one, the top coefficient is one at every length. -/
theorem coeff_row_self {K : ℝ[X]} (hK : K.coeff 0 = 1) (n : ℕ) :
    (row K n).coeff n = 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [row_succ, Polynomial.coeff_add,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by have := natDegree_row_le K n; lia),
        zero_add, Polynomial.coeff_X_mul, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul]
      rw [Finset.sum_eq_single (Fin.last n)]
      · simp [hK, ih n (by lia)]
      · intro j _ hj
        have hjn : j.val < n := by
          have := j.isLt
          have : j.val ≠ n := fun h => hj (Fin.ext (by simpa using h))
          lia
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          ((natDegree_row_le K j.val).trans_lt hjn), mul_zero]
      · simp

/-- The recurrence rows are monic of exactly the spine length. -/
theorem row_monic_natDegree {K : ℝ[X]} (hK : K.coeff 0 = 1) (n : ℕ) :
    (row K n).Monic ∧ (row K n).natDegree = n := by
  have hc := coeff_row_self hK n
  have hd : (row K n).natDegree = n :=
    le_antisymm (natDegree_row_le K n)
      (Polynomial.le_natDegree_of_ne_zero (by rw [hc]; norm_num))
  exact ⟨by simpa [Polynomial.Monic, Polynomial.leadingCoeff, hd] using hc, hd⟩

private def lowerSection (K : ℝ[X]) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (toeplitz K.coeff).submatrix Fin.val Fin.val

private def upperSection (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i ≤ j then 1 else 0

private theorem lowerSection_apply (K : ℝ[X]) (n : ℕ) (i j : Fin n) :
    lowerSection K n i j = if j.val ≤ i.val then K.coeff (i.val - j.val) else 0 :=
  rfl

private theorem upperSection_apply (n : ℕ) (i j : Fin n) :
    upperSection n i j = if i ≤ j then 1 else 0 :=
  rfl

private theorem upperSection_det (n : ℕ) : (upperSection n).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [upperSection]
  · intro i j hij
    have h : ¬i ≤ j := not_le.mpr hij
    simp [upperSection, h]

private def spectralMatrix (K : ℝ[X]) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  lowerSection K n * upperSection n

private theorem lowerSection_triangular (K : ℝ[X]) (n : ℕ) :
    (lowerSection K n).IsLowerTriangular := by
  intro i j hij
  have hval : i.val < j.val := hij
  simp [lowerSection, toeplitz_apply, Nat.not_le_of_lt hval]

private theorem lowerSection_totallyNonneg {K : ℝ[X]} (hK : IsPFPolynomial K) (n : ℕ) :
    (lowerSection K n).IsTotallyNonneg :=
  hK.to_sequence.submatrix (fun _ _ h => h) (fun _ _ h => h)

private theorem upperSection_totallyNonneg (n : ℕ) :
    (upperSection n).IsTotallyNonneg := by
  have h := (constantOne_isPolyaFreqSeq.submatrix
    (f := (Fin.val : Fin n → ℕ)) (g := Fin.val)
    (fun _ _ h => h) (fun _ _ h => h)).transpose
  convert h using 1
  ext i j
  simp [upperSection, toeplitz_apply]

private theorem spectralMatrix_totallyNonneg {K : ℝ[X]} (hK : IsPFPolynomial K) (n : ℕ) :
    (spectralMatrix K n).IsTotallyNonneg :=
  (lowerSection_totallyNonneg hK n).mul (upperSection_totallyNonneg n)

private theorem spectralMatrix_leading (K : ℝ[X]) (n : ℕ) :
    (spectralMatrix K (n + 1)).submatrix Fin.castSucc Fin.castSucc =
      spectralMatrix K n := by
  rw [spectralMatrix, (lowerSection_triangular K (n + 1)).leading_submatrix_mul]
  rfl

private theorem spectralMatrix_det {K : ℝ[X]} (hK : K.coeff 0 = 1) (n : ℕ) :
    (spectralMatrix K n).det = 1 := by
  rw [spectralMatrix, Matrix.det_mul,
    Matrix.det_of_isLowerTriangular _ (lowerSection_triangular K n), upperSection_det]
  simp [lowerSection_apply, hK]

/-- The infinite lower-Hessenberg pencil whose leading determinants are the interval rows. -/
def intervalPencil (K : ℝ[X]) : Matrix ℕ ℕ ℝ[X] := fun i j =>
  (if i = j then 1 else 0) - (if j = i + 1 then 1 else 0) +
    X * (if j ≤ i then C (K.coeff (i - j)) else 0)

private theorem intervalPencil_hessenberg (K : ℝ[X]) (i j : ℕ) (hij : i + 1 < j) :
    intervalPencil K i j = 0 := by
  simp [intervalPencil, show i ≠ j by lia, show j ≠ i + 1 by lia,
    show ¬j ≤ i by lia]

private theorem intervalPencil_super (K : ℝ[X]) (i : ℕ) :
    intervalPencil K i (i + 1) = -1 := by
  simp [intervalPencil]

private theorem intervalPencil_annihilates (K : ℝ[X]) (i : ℕ) :
    ∑ j ∈ Finset.range (i + 2), intervalPencil K i j * row K j = 0 := by
  simp only [intervalPencil, add_mul, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range,
    show i < i + 2 by lia, show i + 1 < i + 2 by lia, ite_true]
  rw [← Finset.mul_sum, show i + 2 = (i + 1) + 1 by lia, Finset.sum_range_succ]
  simp only [show ¬i + 1 ≤ i by lia, ite_false, add_zero]
  have hs : (∑ j ∈ Finset.range (i + 1),
      if j ≤ i then C (K.coeff (i - j)) * row K j else 0) =
        ∑ j : Fin (i + 1), C (K.coeff (i - j.val)) * row K j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j => C (K.coeff (i - j)) * row K j)]
    apply Finset.sum_congr rfl
    intro j hj
    exact ite_eq_left (by have := Finset.mem_range.mp hj; lia)
  rw [hs, row_succ]
  ring

/-- The recurrence is the determinant of its lower-Hessenberg pencil, at every length. -/
theorem row_eq_det (K : ℝ[X]) (n : ℕ) :
    row K n = ((intervalPencil K).submatrix (Fin.val : Fin n → ℕ) Fin.val).det := by
  cases n with
  | zero => simp
  | succ n =>
    symm
    rw [Matrix.det_eq_superdiagonal_prod_mul_of_mulVec_eq_single
      ((intervalPencil K).submatrix (Fin.val : Fin (n + 1) → ℕ) Fin.val)
      (fun i j hij => intervalPencil_hessenberg K i.val j.val hij)
      (fun j => row K j.val) (row_zero K) _
      (Matrix.leading_mulVec_eq_single_of_sum_eq_zero (intervalPencil K) (row K)
        (intervalPencil_hessenberg K) (intervalPencil_annihilates K) n)]
    simp only [Matrix.submatrix_apply, Fin.val_castSucc, Fin.val_succ,
      intervalPencil_super, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_add, ← two_mul, pow_mul]
    simp

private theorem difference_mul_upperSection (n : ℕ) :
    rowDifference ℝ n * upperSection (n + 1) = 1 := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    rw [rowDifference_mul_last]
    simp [upperSection, Matrix.one_apply, Fin.last_le_iff, eq_comm]
  | cast i =>
    rw [rowDifference_mul_castSucc]
    simp only [upperSection, Matrix.one_apply]
    by_cases hij : i.castSucc = j
    · subst j
      simp [Fin.castSucc_lt_succ.not_ge]
    · have heq : (i.castSucc ≤ j) = (i.succ ≤ j) := by
        apply propext
        constructor
        · intro h
          exact Fin.castSucc_lt_iff_succ_le.mp (lt_of_le_of_ne h hij)
        · intro h
          exact Fin.castSucc_lt_succ.le.trans h
      simp [hij, heq]

/-- Entries of `rowDifference`, read off from its action on the identity matrix. -/
private theorem rowDifference_apply (n : ℕ) (i j : Fin (n + 1)) :
    rowDifference ℝ n i j =
      (if i.val = j.val then 1 else 0) - (if i.val + 1 = j.val then 1 else 0) := by
  induction i using Fin.lastCases with
  | last =>
    have h := rowDifference_mul_last (R := ℝ) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) j
    rw [Matrix.mul_one] at h
    have hj : n + 1 ≠ j.val := by have := j.isLt; lia
    rw [h, Matrix.one_apply]
    simp [Fin.ext_iff, hj]
  | cast i =>
    have h := rowDifference_mul_castSucc (R := ℝ)
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j
    rw [Matrix.mul_one] at h
    rw [h, Matrix.one_apply, Matrix.one_apply]
    simp [Fin.ext_iff]

private theorem finitePencil_eq (K : ℝ[X]) (n : ℕ) :
    (intervalPencil K).submatrix (Fin.val : Fin (n + 1) → ℕ) Fin.val =
      (rowDifference ℝ n).map (C (R := ℝ)) +
        (X : ℝ[X]) • (lowerSection K (n + 1)).map (C (R := ℝ)) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply,
    rowDifference_apply, lowerSection_apply, Matrix.submatrix_apply, smul_eq_mul]
  simp only [intervalPencil]
  split_ifs <;> first | lia | simp

private theorem row_eq_det_one_add (K : ℝ[X]) (n : ℕ) :
    row K n = (1 + (X : ℝ[X]) • (spectralMatrix K n).map (C (R := ℝ))).det := by
  cases n with
  | zero => simp
  | succ n =>
    rw [row_eq_det, finitePencil_eq]
    have hmul :
        ((rowDifference ℝ n).map (C (R := ℝ)) +
            (X : ℝ[X]) • (lowerSection K (n + 1)).map (C (R := ℝ))) *
          (upperSection (n + 1)).map (C (R := ℝ)) =
            1 + (X : ℝ[X]) • (spectralMatrix K (n + 1)).map (C (R := ℝ)) := by
      rw [Matrix.add_mul, ← Matrix.map_mul, difference_mul_upperSection,
        Matrix.map_one (C (R := ℝ)) (map_zero _) (map_one _), Matrix.smul_mul, ← Matrix.map_mul]
      rfl
    have hU : ((upperSection (n + 1)).map (C (R := ℝ))).det = 1 := by
      have h := RingHom.map_det (C (R := ℝ)) (upperSection (n + 1))
      rw [upperSection_det, map_one] at h
      exact h.symm
    rw [← hmul, Matrix.det_mul, hU, mul_one]

private theorem spectralMatrix_adjacent {K : ℝ[X]} (hK : IsPFPolynomial K)
    (hzero : 0 < K.coeff 0) (hone : 0 < K.coeff 1) (n : ℕ) :
    (∀ i : Fin n, 0 < spectralMatrix K (n + 1) i.castSucc i.succ) ∧
      ∀ i : Fin n, 0 < spectralMatrix K (n + 1) i.succ i.castSucc := by
  have hL := lowerSection_totallyNonneg hK (n + 1)
  have hU := upperSection_totallyNonneg (n + 1)
  have hbound (i j k : Fin (n + 1)) :
      lowerSection K (n + 1) i k * upperSection (n + 1) k j ≤
        spectralMatrix K (n + 1) i j := by
    rw [spectralMatrix, Matrix.mul_apply]
    exact Finset.single_le_sum
      (f := fun l => lowerSection K (n + 1) i l * upperSection (n + 1) l j)
      (fun l _ => mul_nonneg (hL.nonneg i l) (hU.nonneg l j)) (Finset.mem_univ k)
  constructor
  · intro i
    have h := hbound i.castSucc i.succ i.castSucc
    have h1 : lowerSection K (n + 1) i.castSucc i.castSucc = K.coeff 0 := by
      simp [lowerSection_apply]
    have h2 : upperSection (n + 1) i.castSucc i.succ = 1 := by
      simp [upperSection_apply, Fin.castSucc_lt_succ.le]
    rw [h1, h2, mul_one] at h
    exact hzero.trans_le h
  · intro i
    have h := hbound i.succ i.castSucc i.castSucc
    have h1 : lowerSection K (n + 1) i.succ i.castSucc = K.coeff 1 := by
      simp [lowerSection_apply]
    have h2 : upperSection (n + 1) i.castSucc i.castSucc = 1 := by
      simp [upperSection_apply]
    rw [h1, h2, mul_one] at h
    exact hone.trans_le h

private theorem spectralMatrix_strict {K : ℝ[X]} (hK : IsPFPolynomial K)
    (hzero : K.coeff 0 = 1) (hone : 0 < K.coeff 1) (n : ℕ) :
    Interlaces (spectralMatrix K n).charpoly (spectralMatrix K (n + 1)).charpoly ∧
      (∀ x : ℝ, ¬((spectralMatrix K n).charpoly.IsRoot x ∧
        (spectralMatrix K (n + 1)).charpoly.IsRoot x)) ∧
      ∀ x ∈ (spectralMatrix K (n + 1)).charpoly.roots, 0 < x := by
  obtain ⟨hsuper, hsub⟩ := spectralMatrix_adjacent hK (by rw [hzero]; norm_num) hone n
  obtain ⟨hi, -, -, hno, hpos⟩ :=
    (spectralMatrix_totallyNonneg hK (n + 1)).leading_charpoly_strictInterlaces
      (by rw [spectralMatrix_det hzero]; norm_num) hsuper hsub
  rw [spectralMatrix_leading] at hi hno
  exact ⟨hi, fun x hx => hno x hx.symm, hpos⟩

private theorem reverse_comp_neg (p : ℝ[X]) :
    (p.comp (-X)).reverse = C ((-1 : ℝ) ^ p.natDegree) * p.reverse.comp (-X) := by
  have hd : (p.comp (-X)).natDegree = p.natDegree := Polynomial.natDegree_comp_neg_X p
  ext k
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_comp_neg_X, Polynomial.coeff_reverse, hd]
  rcases le_or_gt k p.natDegree with hk | hk
  · rw [Polynomial.revAt_le hk]
    have hpow : (-1 : ℝ) ^ p.natDegree = (-1) ^ (p.natDegree - k) * (-1) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    have hsq : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hpow]
    linear_combination (-(p.coeff (p.natDegree - k) * (-1) ^ (p.natDegree - k))) * hsq
  · rw [Polynomial.revAt_eq_self_of_lt hk, Polynomial.coeff_eq_zero_of_natDegree_lt hk]
    ring

private theorem row_eq_signed_reverse (K : ℝ[X]) (n : ℕ) :
    row K n = C ((-1 : ℝ) ^ n) *
      ((spectralMatrix K n).charpoly.comp (-X)).reverse := by
  rw [reverse_comp_neg, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    ← mul_assoc, ← map_mul, ← pow_add, ← two_mul, pow_mul]
  simp only [neg_one_sq, one_pow, map_one, one_mul]
  rw [row_eq_det_one_add, Matrix.det_one_add_X_smul_eq_reverse_charpoly_comp_neg_X]

private theorem row_eq_reflectedReciprocal (K : ℝ[X]) (n : ℕ) :
    row K n = reflectedReciprocal (spectralMatrix K n).charpoly := by
  rw [reflectedReciprocal, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  exact row_eq_signed_reverse K n

private theorem row_roots_of_spectrum {K : ℝ[X]} {n : ℕ}
    (hi : Interlaces (spectralMatrix K n).charpoly (spectralMatrix K (n + 1)).charpoly)
    (hpos : ∀ m x, (spectralMatrix K m).charpoly.IsRoot x → 0 < x)
    (hno : ∀ x, ¬((spectralMatrix K n).charpoly.IsRoot x ∧
      (spectralMatrix K (n + 1)).charpoly.IsRoot x)) :
    Interlaces (row K n) (row K (n + 1)) ∧ HasSimpleRoots (row K n) ∧
      (∀ x ∈ (row K n).roots, x < 0) ∧
      ∀ x : ℝ, ¬((row K n).IsRoot x ∧ (row K (n + 1)).IsRoot x) := by
  have hp m : ∀ x ∈ (spectralMatrix K m).charpoly.roots, 0 < x :=
    fun x hx => hpos m x (Polynomial.isRoot_of_mem_roots hx)
  have hr := hi.reflectedReciprocal_strict (hp _) (hp _) hno
  simp only [row_eq_reflectedReciprocal]
  exact ⟨(hi.reflectedReciprocal (hp _) (hp _)).1, hr.2.1, hr.2.2.2.2.1, hr.2.2.2.1⟩

/-- A PF interval kernel with single-tooth weight one and positive two-spine weight
gives simple negative roots and strict interlacing at every length. -/
theorem row_roots_of_isPFPolynomial {K : ℝ[X]} (hK : IsPFPolynomial K)
    (hzero : K.coeff 0 = 1) (hone : 0 < K.coeff 1) (n : ℕ) :
    Interlaces (row K n) (row K (n + 1)) ∧ HasSimpleRoots (row K n) ∧
      (∀ x ∈ (row K n).roots, x < 0) ∧
      ∀ x : ℝ, ¬((row K n).IsRoot x ∧ (row K (n + 1)).IsRoot x) := by
  have h := spectralMatrix_strict hK hzero hone n
  exact row_roots_of_spectrum h.1 (fun m _ hx =>
    (spectralMatrix_totallyNonneg hK m).pos_of_isRoot_charpoly_of_det_ne_zero
      (by rw [spectralMatrix_det hzero]; norm_num) hx) h.2.1

private theorem sqrt_five_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private theorem sqrt_five_lt_three : Real.sqrt 5 < 3 := by
  nlinarith [Real.sqrt_nonneg 5, sqrt_five_sq]

/-- The cap-two kernel factors into positive linear factors. -/
theorem kernel_two_factorization :
    kernel 2 = (X + C ((3 + Real.sqrt 5) / 2)) *
      (X + C ((3 - Real.sqrt 5) / 2)) := by
  have h : ((3 + Real.sqrt 5) / 2) * ((3 - Real.sqrt 5) / 2) = (1 : ℝ) := by
    nlinarith [sqrt_five_sq]
  have hs : ((3 + Real.sqrt 5) / 2) + ((3 - Real.sqrt 5) / 2) = (3 : ℝ) := by ring
  have hexp : (X + C ((3 + Real.sqrt 5) / 2)) * (X + C ((3 - Real.sqrt 5) / 2)) =
      X ^ 2 + C (((3 + Real.sqrt 5) / 2) + ((3 - Real.sqrt 5) / 2)) * X +
        C (((3 + Real.sqrt 5) / 2) * ((3 - Real.sqrt 5) / 2)) := by
    rw [map_add, map_mul]
    ring
  rw [hexp, hs, h, map_one, Polynomial.C_ofNat]
  simp only [kernel]
  ring

/-- The cap-three kernel is the cap-two kernel times `1 + z`. -/
theorem kernel_three_factorization : kernel 3 = (X + 1) * kernel 2 := by
  simp only [kernel]
  ring

private theorem sixteen_mul_C_inv : (16 : ℝ[X]) * C (1 / 16 : ℝ) = 1 := by
  rw [← Polynomial.C_ofNat, ← map_mul]
  norm_num

/-- The exact shifted-kernel factorization used for cap four in issue #2648. -/
theorem kernel_four_shift_factorization :
    16 * (X * kernel 4 + C (1 / 16 : ℝ) * (1 - X)) =
      (1 + 2 * X) ^ 2 * (1 + 11 * X + 16 * X ^ 2 + 4 * X ^ 3) := by
  have h := sixteen_mul_C_inv
  simp only [kernel]
  linear_combination (1 - X) * h

private theorem kernel_four_cubic_isPFPolynomial :
    IsPFPolynomial (1 + 11 * X + 16 * X ^ 2 + 4 * X ^ 3 : ℝ[X]) := by
  have hnn : HasNonnegCoeffs (1 + 11 * X + 16 * X ^ 2 + 4 * X ^ 3 : ℝ[X]) := by
    intro i
    simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_ofNat_mul,
      Polynomial.coeff_X, Polynomial.coeff_X_pow]
    positivity
  apply IsPFPolynomial.of_realRooted_nonneg hnn
  apply splits_of_natDegree_le_three_cubicDiscr_nonneg
  · compute_degree!
  · simp only [cubicDiscr, Polynomial.coeff_add, Polynomial.coeff_one,
      Polynomial.coeff_ofNat_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow]
    norm_num

private theorem linear_two_isPFPolynomial : IsPFPolynomial (1 + 2 * X : ℝ[X]) := by
  have h2 : (C 2 : ℝ[X]) * C (1 / 2) = 1 := by
    rw [← map_mul]
    norm_num
  have h : (1 + 2 * X : ℝ[X]) = C 2 * (X + C (1 / 2)) := by
    rw [mul_add, h2, Polynomial.C_ofNat]
    ring
  rw [h]
  exact IsPFPolynomial.const_mul (by norm_num) (isPFPolynomial_X_add_C (by norm_num))

/-- The shifted cap-four kernel is PF. This is the polynomial input to the
shifted-matrix proof of the root bound `(-16, 0)`, not that bound itself. -/
theorem kernel_four_shift_isPFPolynomial :
    IsPFPolynomial (X * kernel 4 + C (1 / 16 : ℝ) * (1 - X)) := by
  have hscaled : IsPFPolynomial
      (16 * (X * kernel 4 + C (1 / 16 : ℝ) * (1 - X))) := by
    rw [kernel_four_shift_factorization]
    exact (linear_two_isPFPolynomial.pow 2).mul kernel_four_cubic_isPFPolynomial
  have h := IsPFPolynomial.const_mul (a := 1 / 16) (by norm_num) hscaled
  rwa [← mul_assoc, mul_comm (C (1 / 16 : ℝ)) (16 : ℝ[X]), sixteen_mul_C_inv, one_mul] at h

/-- The cap-two interval kernel is a PF polynomial. -/
theorem kernel_two_isPFPolynomial : IsPFPolynomial (kernel 2) := by
  rw [kernel_two_factorization]
  exact (isPFPolynomial_X_add_C (by positivity)).mul
    (isPFPolynomial_X_add_C (by linarith [sqrt_five_lt_three]))

/-- The cap-three interval kernel is a PF polynomial. -/
theorem kernel_three_isPFPolynomial : IsPFPolynomial (kernel 3) := by
  rw [kernel_three_factorization]
  exact isPFPolynomial_X_add_one.mul kernel_two_isPFPolynomial

private theorem kernel_two_coeff :
    (kernel 2).coeff 0 = 1 ∧ (kernel 2).coeff 1 = 3 ∧ (kernel 2).coeff 2 = 1 := by
  simp only [kernel, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_ofNat_mul,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num

private theorem kernel_three_coeff :
    (kernel 3).coeff 0 = 1 ∧ (kernel 3).coeff 1 = 4 ∧ (kernel 3).coeff 2 = 4 ∧
      (kernel 3).coeff 3 = 1 := by
  simp only [kernel, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_ofNat_mul,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num

private theorem kernel_four_coeff : (kernel 4).coeff 0 = 1 ∧ (kernel 4).coeff 1 = 4 := by
  simp only [kernel, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_ofNat_mul,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num

private theorem kernel_five_coeff_zero : (kernel 5).coeff 0 = 1 := by
  simp only [kernel, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_ofNat_mul,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num

private theorem kernel_two_natDegree : (kernel 2).natDegree ≤ 2 := by
  simp only [kernel]
  compute_degree!

private theorem kernel_three_natDegree : (kernel 3).natDegree ≤ 3 := by
  simp only [kernel]
  compute_degree!

/-- The kernels at caps two and three are PF and have a positive two-spine weight. -/
theorem kernel_isPFPolynomial_of_two_or_three {s : ℕ} (hs : s = 2 ∨ s = 3) :
    IsPFPolynomial (kernel s) ∧ (kernel s).coeff 0 = 1 ∧ 0 < (kernel s).coeff 1 := by
  rcases hs with rfl | rfl
  · refine ⟨kernel_two_isPFPolynomial, kernel_two_coeff.1, ?_⟩
    rw [kernel_two_coeff.2.1]
    norm_num
  · refine ⟨kernel_three_isPFPolynomial, kernel_three_coeff.1, ?_⟩
    rw [kernel_three_coeff.2.1]
    norm_num

/-- For caps two and three, at every spine length the recurrence polynomial is
monic of degree `n` with simple negative roots. Consecutive rows interlace and
have disjoint root sets, so all interlacing inequalities are strict.

This is the cap-two and cap-three statement of RealRooted issue #2648 for the
recurrence rows; the graph-packing counting bridge is out of scope. -/
theorem polynomial_roots_of_two_or_three {s : ℕ} (hs : s = 2 ∨ s = 3) (n : ℕ) :
    (polynomial s n).Monic ∧ (polynomial s n).natDegree = n ∧
      (polynomial s n).Splits ∧ HasSimpleRoots (polynomial s n) ∧
      (∀ x ∈ (polynomial s n).roots, x < 0) ∧
      Interlaces (polynomial s n) (polynomial s (n + 1)) ∧
      ∀ x : ℝ, ¬((polynomial s n).IsRoot x ∧ (polynomial s (n + 1)).IsRoot x) := by
  obtain ⟨hK, hzero, hone⟩ := kernel_isPFPolynomial_of_two_or_three hs
  obtain ⟨hm, hd⟩ := row_monic_natDegree hzero n
  obtain ⟨hi, hs, hr, hn⟩ := row_roots_of_isPFPolynomial hK hzero hone n
  exact ⟨hm, hd, hi.2.1.2, hs, hr, hi, hn⟩

/-- The cap-two recurrence in the three-lag form stated in issue #2648. -/
theorem polynomial_two_add_three (n : ℕ) :
    polynomial 2 (n + 3) = (1 + X) * polynomial 2 (n + 2) +
      3 * X * polynomial 2 (n + 1) + X * polynomial 2 n := by
  change row (kernel 2) ((n + 2) + 1) = _
  rw [row_succ, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hz : (∑ j : Fin n,
      C ((kernel 2).coeff (n + 2 - j.val)) * row (kernel 2) j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj := j.isLt
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (kernel_two_natDegree.trans_lt (by lia)),
      map_zero, zero_mul]
  obtain ⟨h0, h1, h2⟩ := kernel_two_coeff
  simp only [Fin.val_castSucc, Fin.val_last] at *
  rw [hz]
  simp only [show n + 2 - n = 2 by lia, show n + 2 - (n + 1) = 1 by lia,
    Nat.sub_self, h0, h1, h2, map_one, Polynomial.C_ofNat, polynomial]
  ring

/-- The cap-three recurrence in the four-lag form stated in issue #2648. -/
theorem polynomial_three_add_four (n : ℕ) :
    polynomial 3 (n + 4) = (1 + X) * polynomial 3 (n + 3) +
      4 * X * polynomial 3 (n + 2) + 4 * X * polynomial 3 (n + 1) +
      X * polynomial 3 n := by
  change row (kernel 3) ((n + 3) + 1) = _
  rw [row_succ, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc,
    Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hz : (∑ j : Fin n,
      C ((kernel 3).coeff (n + 3 - j.val)) * row (kernel 3) j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj := j.isLt
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (kernel_three_natDegree.trans_lt (by lia)),
      map_zero, zero_mul]
  obtain ⟨h0, h1, h2, h3⟩ := kernel_three_coeff
  simp only [Fin.val_castSucc, Fin.val_last] at *
  rw [hz]
  simp only [show n + 3 - n = 3 by lia, show n + 3 - (n + 1) = 2 by lia,
    show n + 3 - (n + 2) = 1 by lia, Nat.sub_self, h0, h1, h2, h3, map_one,
    Polynomial.C_ofNat, polynomial]
  ring

/-- The shifted cap-four kernel `zK(z) + (1 - z) / 16`. -/
private def shiftedKernel : ℝ[X] := X * kernel 4 + C (1 / 16 : ℝ) * (1 - X)

private theorem shiftedKernel_coeff_zero : shiftedKernel.coeff 0 = 1 / 16 := by
  simp only [shiftedKernel, Polynomial.coeff_add, Polynomial.coeff_X_mul_zero,
    Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

private theorem shiftedKernel_coeff_succ (m : ℕ) :
    shiftedKernel.coeff (m + 1) = (kernel 4).coeff m - if m = 0 then 1 / 16 else 0 := by
  simp only [shiftedKernel, Polynomial.coeff_add, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X]
  rcases m with _ | m
  · simp
    ring
  · simp

private theorem linearTwo_coeff_one : (1 + 2 * X : ℝ[X]).coeff 1 = 2 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_ofNat_mul,
    Polynomial.coeff_X]
  norm_num

private theorem linearTwo_natDegree : (1 + 2 * X : ℝ[X]).natDegree ≤ 1 := by
  compute_degree!

/-- The shifted kernel is `(1 + 2z) · q(z)` with `q` again PF. -/
private theorem shiftedKernel_eq : shiftedKernel = (1 + 2 * X) *
    (C (1 / 16 : ℝ) * ((1 + 2 * X) * (1 + 11 * X + 16 * X ^ 2 + 4 * X ^ 3))) := by
  have h16 : 16 * shiftedKernel =
      (1 + 2 * X) ^ 2 * (1 + 11 * X + 16 * X ^ 2 + 4 * X ^ 3) :=
    kernel_four_shift_factorization
  calc shiftedKernel = C (1 / 16 : ℝ) * (16 * shiftedKernel) := by
        rw [← mul_assoc, mul_comm (C (1 / 16 : ℝ)) (16 : ℝ[X]), sixteen_mul_C_inv, one_mul]
    _ = _ := by
        rw [h16]
        ring

/-- Rows `2, …, n + 1` and columns `1, …, n` of the shifted Toeplitz section. -/
private def shiftedSection (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (lowerSection shiftedKernel (n + 1)).submatrix Fin.succ Fin.castSucc

private theorem shiftedSection_tnn (n : ℕ) : (shiftedSection n).IsTotallyNonneg :=
  (lowerSection_totallyNonneg kernel_four_shift_isPFPolynomial (n + 1)).submatrix
    Fin.strictMono_succ Fin.strictMono_castSucc

private theorem shiftedSection_det_pos (n : ℕ) : 0 < (shiftedSection n).det := by
  have hq : IsPFPolynomial
      (C (1 / 16 : ℝ) * ((1 + 2 * X) * (1 + 11 * X + 16 * X ^ 2 + 4 * X ^ 3))) :=
    IsPFPolynomial.const_mul (by norm_num)
      (linear_two_isPFPolynomial.mul kernel_four_cubic_isPFPolynomial)
  change 0 < ((toeplitzFin shiftedKernel.coeff n).submatrix Fin.succ Fin.castSucc).det
  rw [shiftedKernel_eq, Schur.toeplitzFin_coeff_mul]
  let mid : Fin n ↪o Fin (n + 1) := OrderEmbedding.ofStrictMono _ Fin.strictMono_castSucc
  apply (lowerSection_totallyNonneg linear_two_isPFPolynomial (n + 1)).toRect.det_submatrix_mul_pos
    (lowerSection_totallyNonneg hq (n + 1)).toRect Fin.strictMono_succ
    Fin.strictMono_castSucc mid
  · rw [Matrix.det_of_isUpperTriangular]
    · apply Finset.prod_pos
      intro i _
      change 0 < (toeplitz (1 + 2 * X : ℝ[X]).coeff) (i.val + 1) i.val
      rw [toeplitz_apply, ite_eq_left (show i.val ≤ i.val + 1 by lia),
        show i.val + 1 - i.val = 1 by lia,
        linearTwo_coeff_one]
      norm_num
    · intro i j hij
      change toeplitz (1 + 2 * X : ℝ[X]).coeff (i.val + 1) j.val = 0
      have hlt : j.val < i.val := hij
      rw [toeplitz_apply, ite_eq_left (show j.val ≤ i.val + 1 by lia)]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (linearTwo_natDegree.trans_lt (by lia))
  · change 0 < (lowerSection
      (C (1 / 16 : ℝ) * ((1 + 2 * X) * (1 + 11 * X + 16 * X ^ 2 + 4 * X ^ 3))) n).det
    rw [Matrix.det_of_isLowerTriangular _ (lowerSection_triangular _ n)]
    apply Finset.prod_pos
    intro i _
    rw [lowerSection_apply, ite_eq_left le_rfl, Nat.sub_self, Polynomial.coeff_C_mul,
      Polynomial.coeff_zero_eq_eval_zero]
    norm_num

private theorem shiftedSection_eq (n : ℕ) :
    shiftedSection (n + 1) =
      lowerSection (kernel 4) (n + 1) - (1 / 16 : ℝ) • rowDifference ℝ n := by
  ext i j
  rw [Matrix.sub_apply, Matrix.smul_apply, rowDifference_apply, smul_eq_mul]
  change (if j.val ≤ i.val + 1 then shiftedKernel.coeff (i.val + 1 - j.val) else 0) =
    (if j.val ≤ i.val then (kernel 4).coeff (i.val - j.val) else 0) -
      1 / 16 * ((if i.val = j.val then 1 else 0) - (if i.val + 1 = j.val then 1 else 0))
  rcases lt_trichotomy j.val (i.val + 1) with h | h | h
  · have hji : j.val ≤ i.val := by lia
    rw [ite_eq_left h.le, ite_eq_left hji, show i.val + 1 - j.val = (i.val - j.val) + 1 by lia,
      shiftedKernel_coeff_succ, ite_eq_right (show i.val + 1 ≠ j.val by lia)]
    by_cases hij : i.val = j.val
    · rw [ite_eq_left hij, ite_eq_left (show i.val - j.val = 0 by lia)]
      ring
    · rw [ite_eq_right hij, ite_eq_right (show i.val - j.val ≠ 0 by lia)]
      ring
  · rw [ite_eq_left h.le, ite_eq_right (show ¬j.val ≤ i.val by lia), h, Nat.sub_self,
      shiftedKernel_coeff_zero, ite_eq_right (show i.val ≠ i.val + 1 by lia),
      ite_eq_left rfl]
    ring
  · rw [ite_eq_right (show ¬j.val ≤ i.val + 1 by lia),
      ite_eq_right (show ¬j.val ≤ i.val by lia),
      ite_eq_right (show i.val ≠ j.val by lia), ite_eq_right (show i.val + 1 ≠ j.val by lia)]
    ring

/-- The cap-four spectral matrix shifted by `1 / 16`. -/
private def shiftedMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  spectralMatrix (kernel 4) n - Matrix.scalar (Fin n) (1 / 16 : ℝ)

private theorem shiftedMatrix_eq (n : ℕ) :
    shiftedMatrix n = shiftedSection n * upperSection n := by
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    rw [shiftedSection_eq, Matrix.sub_mul, Matrix.smul_mul, difference_mul_upperSection]
    simp [shiftedMatrix, spectralMatrix, Matrix.smul_one_eq_diagonal]

private theorem shiftedMatrix_tnn (n : ℕ) : (shiftedMatrix n).IsTotallyNonneg := by
  rw [shiftedMatrix_eq]
  exact (shiftedSection_tnn n).mul (upperSection_totallyNonneg n)

private theorem shiftedMatrix_det (n : ℕ) : (shiftedMatrix n).det ≠ 0 := by
  rw [shiftedMatrix_eq, Matrix.det_mul, upperSection_det, mul_one]
  exact (shiftedSection_det_pos n).ne'

private theorem shiftedMatrix_adjacent (n : ℕ) :
    (∀ i : Fin n, 0 < shiftedMatrix (n + 1) i.castSucc i.succ) ∧
      ∀ i : Fin n, 0 < shiftedMatrix (n + 1) i.succ i.castSucc := by
  have hpositive (i j k : Fin (n + 1)) (h1 : 0 < shiftedSection (n + 1) i k)
      (h2 : k ≤ j) : 0 < shiftedMatrix (n + 1) i j := by
    rw [shiftedMatrix_eq, Matrix.mul_apply]
    apply Finset.sum_pos'
    · intro l _
      exact mul_nonneg ((shiftedSection_tnn _).nonneg i l)
        ((upperSection_totallyNonneg _).nonneg l j)
    · exact ⟨k, Finset.mem_univ k, by simpa [upperSection, h2] using h1⟩
  constructor
  · intro i
    apply hpositive _ _ i.castSucc _ Fin.castSucc_lt_succ.le
    change 0 < toeplitz shiftedKernel.coeff (i.val + 1) i.val
    rw [toeplitz_apply, ite_eq_left (show i.val ≤ i.val + 1 by lia),
      show i.val + 1 - i.val = 0 + 1 by lia,
      shiftedKernel_coeff_succ, kernel_four_coeff.1]
    norm_num
  · intro i
    apply hpositive _ _ i.castSucc _ le_rfl
    change 0 < toeplitz shiftedKernel.coeff (i.val + 1 + 1) i.val
    rw [toeplitz_apply, ite_eq_left (show i.val ≤ i.val + 1 + 1 by lia),
      show i.val + 1 + 1 - i.val = 1 + 1 by lia,
      shiftedKernel_coeff_succ, kernel_four_coeff.2]
    norm_num

private theorem shiftedMatrix_leading (n : ℕ) :
    (shiftedMatrix (n + 1)).submatrix Fin.castSucc Fin.castSucc = shiftedMatrix n := by
  ext i j
  rw [shiftedMatrix, shiftedMatrix, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.sub_apply,
    ← spectralMatrix_leading (kernel 4) n, Matrix.submatrix_apply]
  simp [Matrix.scalar_apply, Matrix.diagonal_apply]

private theorem shiftedMatrix_translate (n : ℕ) :
    (shiftedMatrix n).charpoly.comp (X + C (-(1 / 16 : ℝ))) =
      (spectralMatrix (kernel 4) n).charpoly := by
  rw [shiftedMatrix, Matrix.charpoly_sub_scalar, Polynomial.comp_assoc]
  simp

private theorem spectralMatrix_four_strict (n : ℕ) :
    Interlaces (spectralMatrix (kernel 4) n).charpoly
        (spectralMatrix (kernel 4) (n + 1)).charpoly ∧
      ∀ x : ℝ, ¬((spectralMatrix (kernel 4) n).charpoly.IsRoot x ∧
        (spectralMatrix (kernel 4) (n + 1)).charpoly.IsRoot x) := by
  obtain ⟨ha, hb⟩ := shiftedMatrix_adjacent n
  obtain ⟨hi, -, -, hno, -⟩ := (shiftedMatrix_tnn (n + 1)).leading_charpoly_strictInterlaces
    (shiftedMatrix_det _) ha hb
  rw [shiftedMatrix_leading] at hi hno
  constructor
  · rw [← shiftedMatrix_translate, ← shiftedMatrix_translate]
    exact interlaces_comp_X_add_C hi _
  · rintro x ⟨hx, hy⟩
    rw [← shiftedMatrix_translate, Polynomial.IsRoot.def, Polynomial.eval_comp] at hx hy
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at hx hy
    exact hno _ ⟨hy, hx⟩

private theorem spectralMatrix_four_root_gt (n : ℕ) {x : ℝ}
    (hx : (spectralMatrix (kernel 4) n).charpoly.IsRoot x) : 1 / 16 < x := by
  rw [← shiftedMatrix_translate, Polynomial.IsRoot.def, Polynomial.eval_comp] at hx
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at hx
  have h := (shiftedMatrix_tnn n).pos_of_isRoot_charpoly_of_det_ne_zero
    (shiftedMatrix_det n) hx
  linarith

/-- At cap four the degree-`n` monic row splits into `n` simple roots in
`(-16, 0)`, and consecutive rows strictly interlace. -/
theorem polynomial_four_roots (n : ℕ) :
    (polynomial 4 n).Monic ∧ (polynomial 4 n).natDegree = n ∧
      (polynomial 4 n).Splits ∧ HasSimpleRoots (polynomial 4 n) ∧
      (∀ x ∈ (polynomial 4 n).roots, -16 < x ∧ x < 0) ∧
      Interlaces (polynomial 4 n) (polynomial 4 (n + 1)) ∧
      ∀ x : ℝ, ¬((polynomial 4 n).IsRoot x ∧ (polynomial 4 (n + 1)).IsRoot x) := by
  obtain ⟨hi, hd⟩ := spectralMatrix_four_strict n
  have hs (m : ℕ) := (spectralMatrix_four_strict m).1.2.1.2
  have hpos (m : ℕ) (x : ℝ) (hx : (spectralMatrix (kernel 4) m).charpoly.IsRoot x) :
      0 < x :=
    lt_trans (by norm_num) (spectralMatrix_four_root_gt m hx)
  obtain ⟨hr, hsimple, -, hno⟩ := row_roots_of_spectrum hi hpos hd
  obtain ⟨hm, hdeg⟩ := row_monic_natDegree kernel_four_coeff.1 n
  refine ⟨hm, hdeg, hr.2.1.2, hsimple, ?_, hr, hno⟩
  intro x hx
  change x ∈ (row (kernel 4) n).roots at hx
  rw [row_eq_reflectedReciprocal, reflectedReciprocal_roots hi.2.1.1 (hs n)
    (fun z hz => hpos n z (Polynomial.isRoot_of_mem_roots hz)), Multiset.mem_map] at hx
  obtain ⟨z, hzmem, rfl⟩ := hx
  have hz := Polynomial.isRoot_of_mem_roots hzmem
  have hb := spectralMatrix_four_root_gt n hz
  have hzinv : 1 / z < 16 := (div_lt_iff₀ (hpos n z hz)).mpr (by linarith)
  exact ⟨by simpa [one_div] using neg_lt_neg hzinv, neg_neg_of_pos (inv_pos.mpr (hpos n z hz))⟩

/-- At caps two, three and four the recurrence polynomial has exactly `n` real
zeros, counted with multiplicity; `polynomial_roots_of_two_or_three` and
`polynomial_four_roots` show that all these zeros are distinct and negative. -/
theorem card_roots_polynomial {s : ℕ} (hs : s = 2 ∨ s = 3 ∨ s = 4) (n : ℕ) :
    (polynomial s n).roots.card = n := by
  have h : (polynomial s n).natDegree = n ∧ (polynomial s n).Splits := by
    rcases hs with hs | hs
    · obtain ⟨-, hd, hsplit, -⟩ := polynomial_roots_of_two_or_three (Or.inl hs) n
      exact ⟨hd, hsplit⟩
    rcases hs with hs | rfl
    · obtain ⟨-, hd, hsplit, -⟩ := polynomial_roots_of_two_or_three (Or.inr hs) n
      exact ⟨hd, hsplit⟩
    · obtain ⟨-, hd, hsplit, -⟩ := polynomial_four_roots n
      exact ⟨hd, hsplit⟩
  rw [Polynomial.splits_iff_card_roots.mp h.2, h.1]

/-- Nonnegative interval weights give nonnegative row coefficients at every length. -/
theorem hasNonnegCoeffs_row {K : ℝ[X]} (hK : HasNonnegCoeffs K) (n : ℕ) :
    HasNonnegCoeffs (row K n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simpa using hasNonnegCoeffs_one
    | succ n =>
      rw [row_succ]
      exact (ih n (by lia)).add (hasNonnegCoeffs_X.mul (hasNonnegCoeffs_finsetSum _ _
        fun j _ => hasNonnegCoeffs_C_mul (hK _) (ih j.val j.isLt)))

/-- At cap five the row is monic of degree `n`, and each real root is strictly negative. -/
theorem polynomial_five_monic_natDegree_roots (n : ℕ) :
    (polynomial 5 n).Monic ∧ (polynomial 5 n).natDegree = n ∧
      ∀ x ∈ (polynomial 5 n).roots, x < 0 := by
  obtain ⟨hm, hd⟩ := row_monic_natDegree kernel_five_coeff_zero n
  refine ⟨hm, hd, ?_⟩
  have hK : HasNonnegCoeffs (kernel 5) := by
    intro i
    simp only [kernel, AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, coeff_one,
      coeff_ofNat_mul, coeff_X, mul_ite, mul_one, mul_zero, coeff_X_pow]
    positivity
  intro x hx
  by_contra! h
  exact ((hasNonnegCoeffs_row hK n).eval_pos_of_coeff_zero_pos (by simp) h).ne'
    (Polynomial.isRoot_of_mem_roots hx)

/-- The evaluated first-interval recurrence. -/
theorem eval_row_succ (K : ℝ[X]) (t : ℝ) (n : ℕ) :
    (row K (n + 1)).eval t = (row K n).eval t +
      t * ∑ j ∈ Finset.range (n + 1), (row K j).eval t * K.coeff (n - j) := by
  rw [row_succ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_finsetSum,
    Fin.sum_univ_eq_sum_range (fun j => (C (K.coeff (n - j)) * row K j).eval t)]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_mul, Polynomial.eval_C, mul_comm]

private theorem coeff_rowSeries_mul (K : ℝ[X]) (t : ℝ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk (fun m => (row K m).eval t) * (K : PowerSeries ℝ)) =
      ∑ j ∈ Finset.range (n + 1), (row K j).eval t * K.coeff (n - j) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro j _
  simp

/-- Multiplying the series of evaluated rows by `1 - z - tzK(z)` gives one. -/
theorem rowSeries_mul_denominator (K : ℝ[X]) (t : ℝ) :
    PowerSeries.mk (fun n => (row K n).eval t) *
      (1 - PowerSeries.X - PowerSeries.C t * (K : PowerSeries ℝ) * PowerSeries.X) = 1 := by
  have he : ∀ F : PowerSeries ℝ,
      F * (1 - PowerSeries.X - PowerSeries.C t * (K : PowerSeries ℝ) * PowerSeries.X) =
        F - F * PowerSeries.X - F * (K : PowerSeries ℝ) * PowerSeries.C t * PowerSeries.X :=
    fun F => by ring
  rw [he]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [map_sub, map_sub, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_succ_mul_X,
      PowerSeries.coeff_mul_C, coeff_rowSeries_mul, PowerSeries.coeff_one,
      ite_eq_right (Nat.add_one_ne_zero n), PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      eval_row_succ]
    ring

/-- Given the quadratic factor and a normalized cofactor of the rescaled denominator,
the evaluated row is a convolution with Chebyshev polynomials of the second kind. -/
theorem row_eval_eq_chebyshev_sum (K : ℝ[X]) (t r c : ℝ) (Q : PowerSeries ℝ)
    (hQ : PowerSeries.constantCoeff Q = 1)
    (hf : PowerSeries.rescale r
        (1 - PowerSeries.X - PowerSeries.C t * (K : PowerSeries ℝ) * PowerSeries.X) =
      (1 - PowerSeries.C (2 * c) * PowerSeries.X + PowerSeries.X ^ 2) * Q) (n : ℕ) :
    r ^ n * (row K n).eval t = ∑ j ∈ Finset.range (n + 1),
      PowerSeries.coeff j Q⁻¹ * ToeplitzPerturbation.chebU c (n - j) := by
  let F := PowerSeries.rescale r (PowerSeries.mk fun m => (row K m).eval t)
  have hprod := congrArg (PowerSeries.rescale r) (rowSeries_mul_denominator K t)
  rw [map_mul, hf, map_one] at hprod
  have hinv := PowerSeries.mul_inv_cancel Q (by rw [hQ]; norm_num)
  have hcheb := ToeplitzPerturbation.chebQuad_mul_chebSeries c
  have heq : F = Q⁻¹ * ToeplitzPerturbation.chebSeries c := by
    change F * _ = 1 at hprod
    calc
      F = F * ((1 - PowerSeries.C (2 * c) * PowerSeries.X + PowerSeries.X ^ 2) *
          ToeplitzPerturbation.chebSeries c) * (Q * Q⁻¹) := by rw [hcheb, hinv]; ring
      _ = _ := by linear_combination (Q⁻¹ * ToeplitzPerturbation.chebSeries c) * hprod
  have h := congrArg (PowerSeries.coeff n) heq
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa [F, ToeplitzPerturbation.chebSeries] using h

/-- Polynomial division of the cap-five denominator by `1 - 2cu + u²`.
The quartic coefficients are computed from the leading term downward. The
remaining scalar identity is exactly the branch equation in issue #2648. -/
theorem five_denominator_division (r c u : ℝ) :
    let a₄ := r ^ 6
    let a₃ := 6 * r ^ 5 + 2 * c * a₄
    let a₂ := 11 * r ^ 4 + 2 * c * a₃ - a₄
    let a₁ := 8 * r ^ 3 + 2 * c * a₂ - a₃
    let a₀ := 4 * r ^ 2 + 2 * c * a₁ - a₂
    a₀ * (1 - r * u) + r * u * (kernel 5).eval (r * u) =
      (1 - 2 * c * u + u ^ 2) * (a₀ + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3 + a₄ * u ^ 4) +
        u * (r + (2 * c - r) * a₀ - a₁) := by
  simp [kernel]
  ring

/-- Coefficient majorant for the product of four geometric series whose
ratios have norm at most `2 / 3`. -/
def quarticMajorant (n : ℕ) : ℝ := ((n + 3).choose 3 : ℝ) * (2 / 3 : ℝ) ^ n

private theorem quarticMajorant_nonneg (n : ℕ) : 0 ≤ quarticMajorant n := by
  unfold quarticMajorant
  positivity

/-- The sum of the quartic majorant is exactly 81. -/
theorem hasSum_quarticMajorant : HasSum quarticMajorant 81 := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one 3 (r := (2 / 3 : ℝ)) (by norm_num)
  have h81 : (1 : ℝ) / (1 - 2 / 3) ^ (3 + 1) = 81 := by norm_num
  rw [h81] at h
  exact h

private theorem quarticMajorant_succ_le {n : ℕ} (hn : 100 ≤ n) :
    quarticMajorant (n + 1) ≤ 3 / 4 * quarticMajorant n := by
  have hnat := Nat.choose_mul_succ_eq (n + 3) 3
  rw [show n + 3 + 1 - 3 = n + 1 by lia] at hnat
  have hc : ((n + 3).choose 3 : ℝ) * (n + 4) = ((n + 4).choose 3 : ℝ) * (n + 1) := by
    exact_mod_cast hnat
  have ha : (0 : ℝ) ≤ ((n + 3).choose 3 : ℝ) := Nat.cast_nonneg _
  have hm : (8 : ℝ) * (n + 4) ≤ 9 * (n + 1) := by
    have : (100 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have hkey : (8 * ((n + 4).choose 3 : ℝ)) * (n + 1) ≤
      (9 * ((n + 3).choose 3 : ℝ)) * (n + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hm ha]
  have hb : (8 : ℝ) * ((n + 4).choose 3 : ℝ) ≤ 9 * ((n + 3).choose 3 : ℝ) :=
    le_of_mul_le_mul_right hkey hpos
  unfold quarticMajorant
  rw [pow_succ, show n + 1 + 3 = n + 4 by lia]
  linarith [mul_le_mul_of_nonneg_right hb (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) n)]

/-- Both error terms needed in the cap-five angular argument are smaller than
one hundredth for every `n ≥ 100`. -/
theorem quarticMajorant_tail {n : ℕ} (hn : 100 ≤ n) :
    (∑' j, quarticMajorant (n + 1 + j)) < 1 / 100 ∧
      81 * (n : ℝ) * quarticMajorant (n + 1) < 1 / 100 := by
  have hdec (m : ℕ) (hm : 100 ≤ m) :
      81 * (m + 1 : ℝ) * quarticMajorant (m + 2) ≤
        81 * (m : ℝ) * quarticMajorant (m + 1) := by
    have h1 := mul_le_mul_of_nonneg_left (quarticMajorant_succ_le (n := m + 1) (by lia))
      (show 0 ≤ 81 * (m + 1 : ℝ) by positivity)
    have h2 : (81 : ℝ) * (m + 1) * (3 / 4) ≤ 81 * m := by
      have : (100 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    linarith [mul_le_mul_of_nonneg_right h2 (quarticMajorant_nonneg (m + 1))]
  have hsmall : 81 * (n : ℝ) * quarticMajorant (n + 1) < 1 / 100 := by
    induction n, hn using Nat.le_induction with
    | base => norm_num [quarticMajorant, Nat.choose]
    | succ m hm ih => exact lt_of_le_of_lt (by simpa using hdec m hm) ih
  refine ⟨?_, hsmall⟩
  have hbound (j : ℕ) : quarticMajorant (n + 1 + j) ≤
      (3 / 4 : ℝ) ^ j * quarticMajorant (n + 1) := by
    induction j with
    | zero => simp
    | succ j ih =>
      exact (quarticMajorant_succ_le (n := n + 1 + j) (by lia)).trans
        (by
          rw [pow_succ]
          nlinarith [mul_le_mul_of_nonneg_left ih (by norm_num : 0 ≤ (3 / 4 : ℝ))])
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num)).mul_right (quarticMajorant (n + 1))
  have hsummable : Summable fun j => quarticMajorant (n + 1 + j) :=
    Summable.of_nonneg_of_le (fun _ => quarticMajorant_nonneg _) hbound hg.summable
  have hsum : (∑' j, quarticMajorant (n + 1 + j)) ≤
      (1 - 3 / 4)⁻¹ * quarticMajorant (n + 1) := by
    rw [← hg.tsum_eq]
    exact Summable.tsum_le_tsum hbound hsummable hg.summable
  have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num at hsum
  nlinarith [mul_le_mul_of_nonneg_right hn' (quarticMajorant_nonneg (n + 1))]

end RealRooted.CombClustering
