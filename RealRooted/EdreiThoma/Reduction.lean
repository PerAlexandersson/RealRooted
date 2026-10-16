module

public import RealRooted.EdreiThoma.Identities
public import RealRooted.EdreiThoma.Easy
public import RealRooted.Mathlib.LinearAlgebra.Matrix.CauchyBinet

@[expose] public section

open Polynomial Filter Topology

noncomputable section

namespace RealRooted.EdreiThoma

/-- The coefficients of `exp (ε z)`. -/
def expSeq (ε : ℝ) (n : ℕ) : ℝ := ε ^ n / (n.factorial : ℝ)

/-! ### Auxiliary lemmas -/

private lemma toeplitz_conv_eq_sum (a b : ℕ → ℝ) {N i : ℕ} (hi : i < N) (j : ℕ) :
    toeplitz (natCauchyConvolution a b) i j = ∑ l : Fin N, toeplitz a i l * toeplitz b l j := by
  rw [Fin.sum_univ_eq_sum_range (fun l => toeplitz a i l * toeplitz b l j)]
  rw [← Finset.sum_range_add_sum_Ico _ (show i + 1 ≤ N by lia)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (i+1) N) (fun l hl => by
      simp only [Finset.mem_Ico] at hl; simp [toeplitz_apply, show ¬ l ≤ i by lia])]
  rw [add_zero, ← Finset.sum_range_reflect]
  rw [Finset.sum_congr rfl (g := fun k => a k * (if j ≤ i - k then b (i - k - j) else 0))
    (by
      intro k hk
      simp only [Finset.mem_range] at hk
      have hik : i - (i - k) = k := by lia
      simp [toeplitz_apply, hik])]
  unfold natCauchyConvolution
  rw [toeplitz_apply]
  split_ifs with hji
  · symm
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by lia : i - j + 1 ≤ i + 1))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_range] at hk
      rw [ite_eq_left (by lia), show i - k - j = i - j - k by lia]
    · intro k hk hk'
      simp only [Finset.mem_range] at hk hk'
      rw [ite_eq_right (by lia), mul_zero]
  · symm
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [ite_eq_right (by lia), mul_zero]

/-- The increasing enumeration (as natural numbers) of an `n`-subset of `Fin N`. -/
private def sEnum {N n : ℕ}
    (S : {S : Finset (Fin N) // S.card = Fintype.card (Fin n)}) (j : Fin n) :
    ℕ :=
  ((S.1.orderEmbOfFin (S.2.trans (Fintype.card_fin n)) j : Fin N) : ℕ)

private lemma sEnum_strictMono {N n : ℕ}
    (S : {S : Finset (Fin N) // S.card = Fintype.card (Fin n)}) :
    StrictMono (sEnum S) := fun _ _ h => (S.1.orderEmbOfFin _).strictMono h

/-- Cauchy–Binet for minors of the Toeplitz matrix of a product. -/
private lemma minor_conv (a b : ℕ → ℝ) (n : ℕ) (r c : Fin n → ℕ) (N : ℕ)
    (hr : ∀ i, r i < N) :
    Matrix.det (Matrix.of fun i j => toeplitz (natCauchyConvolution a b) (r i) (c j)) =
      ∑ S : {S : Finset (Fin N) // S.card = Fintype.card (Fin n)},
        Matrix.det (Matrix.of fun i j => toeplitz a (r i) (sEnum S j)) *
          Matrix.det (Matrix.of fun i j => toeplitz b (sEnum S i) (c j)) := by
  let P : Matrix (Fin n) (Fin N) ℝ := Matrix.of fun i l => toeplitz a (r i) l
  let Q : Matrix (Fin N) (Fin n) ℝ := Matrix.of fun l j => toeplitz b l (c j)
  have hPQ : (Matrix.of fun i j => toeplitz (natCauchyConvolution a b) (r i) (c j)) = P * Q := by
    ext i j
    change toeplitz (natCauchyConvolution a b) (r i) (c j) =
      ∑ l : Fin N, toeplitz a (r i) l * toeplitz b l (c j)
    exact toeplitz_conv_eq_sum a b (hr i) (c j)
  rw [hPQ, Matrix.det_mul_eq_sum_minors P Q
    (fun S => (S.1.orderIsoOfFin (S.2.trans (Fintype.card_fin n))).toEquiv)]
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 2

private lemma tc_eq (a : ℕ → ℝ) (m i j : ℕ) :
    tc a ((m : ℤ) + i - j) = toeplitz a (m + i) j := by
  unfold tc
  rw [toeplitz_apply]
  split_ifs with h1 h2 h2
  · congr 1; lia
  · lia
  · lia
  · rfl

private lemma A_eq (a : ℕ → ℝ) (n m : ℕ) :
    A a n m = Matrix.det (Matrix.of fun i j : Fin n => toeplitz a (m + i) j) := by
  unfold A
  simp_rw [tc_eq]

private lemma expSeq_entry {ε : ℝ} (hε : 0 < ε) (m i j : ℕ) :
    toeplitz (expSeq ε) (m + i) j =
      ε ^ (m + i) / ((m + i).factorial : ℝ) *
        ((ε ^ j)⁻¹ * ((m + i).descFactorial j : ℝ)) := by
  rw [toeplitz_apply]
  unfold expSeq
  split_ifs with h
  · have h1 := Nat.factorial_mul_descFactorial h
    have h2 : ε ^ (m + i) = ε ^ (m + i - j) * ε ^ j := by rw [← pow_add]; congr 1; lia
    rw [← h1, h2]
    push_cast
    have : (0:ℝ) < ((m+i-j).factorial : ℝ) := by positivity
    have : (0:ℝ) < ((m+i).descFactorial j : ℝ) := by
      exact Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr h)
    field_simp
  · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr (by lia)]; simp

/-- The coefficient sequence of `exp (ε z)` is Pólya-frequency when `ε ≥ 0`. -/
theorem isPolyaFreqSeq_expSeq {ε : ℝ} (hε : 0 ≤ ε) : IsPolyaFreqSeq (expSeq ε) := by
  have h := isPolyaFreqSeries_rescale_exp hε
  unfold IsPolyaFreqSeries at h
  convert h using 1
  funext n
  norm_num [expSeq, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, div_eq_mul_inv]

/-- The consecutive Toeplitz minors of `exp (ε z)` are strictly positive for `ε > 0`:
`A^{(n)}_m = ε^{mn} ∏_{i<n} i! / (m+i)!`.  (Suggested proof: multiply row `i` by `(m+i)!`;
the entry becomes the falling factorial `(m+i)(m+i-1)⋯(m+i-j+1)` of degree `j` in `x_i = m+i`,
which is also valid when `m+i-j<0` (it vanishes); the falling-factorial basis is unitriangular
to the monomial basis, so the determinant is the Vandermonde `∏_{i<i'} (x_{i'}-x_i) = ∏ i!`.
For `ε`, scale rows and columns.) -/
theorem A_expSeq_pos {ε : ℝ} (hε : 0 < ε) (n m : ℕ) : 0 < A (expSeq ε) n m := by
  rw [A_eq]
  simp_rw [expSeq_entry hε]
  have hc := Matrix.det_mul_column
    (fun i : Fin n => ε ^ (m + (i:ℕ)) / ((m + (i:ℕ)).factorial : ℝ))
    (Matrix.of fun i j : Fin n => (ε ^ (j:ℕ))⁻¹ * ((m + (i:ℕ)).descFactorial j : ℝ))
  have hr := Matrix.det_mul_row (fun j : Fin n => (ε ^ (j:ℕ))⁻¹)
    (Matrix.of fun i j : Fin n => ((m + (i:ℕ)).descFactorial j : ℝ))
  simp only [Matrix.of_apply] at hc hr
  rw [hc, hr]
  have hv := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun i : Fin n => ((m + (i:ℕ) : ℕ) : ℝ)) (fun j => descPochhammer ℝ j)
    (fun j => descPochhammer_natDegree ℝ j) (fun j => monic_descPochhammer ℝ j)
  simp only [descPochhammer_eval_eq_descFactorial] at hv
  rw [← hv, Matrix.det_vandermonde]
  refine mul_pos (Finset.prod_pos fun i _ => by positivity) (mul_pos
    (Finset.prod_pos fun i _ => by positivity) (Finset.prod_pos fun i _ =>
      Finset.prod_pos fun j hj => ?_))
  simp only [Finset.mem_Ioi] at hj
  have : (i:ℕ) < j := hj
  push_cast
  linarith [show ((i:ℕ):ℝ) < (j:ℕ) by exact_mod_cast this]

/-- Edrei's Observation II: if `a` is a Pólya frequency sequence with `a 0 = 1` and `ε > 0`,
then `a ⋆ exp (ε ·)` has property (P): all consecutive Toeplitz minors are strictly positive.
(Suggested proof: Cauchy–Binet for the minor with rows `I = {m,…,m+n-1}` and columns
`J = {0,…,n-1}` of `T(a) T(g)` expresses `A^{(n)}_m` as `∑_K det T(a)[I,K] det T(g)[K,J]`; all
summands are `≥ 0` since `a` and `g = exp (ε ·)` are PF, and the summand `K = I` equals
`(a 0)^n * A^{(n)}_m(g) > 0`, since `T(a)[I,I]` is lower triangular with diagonal `a 0`.) -/
theorem A_natCauchyConvolution_expSeq_pos {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a)
    (h0 : a 0 = 1) {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    0 < A (natCauchyConvolution a (expSeq ε)) n m := by
  rw [A_eq, minor_conv a (expSeq ε) n (fun i => m + i) (fun j => j) (m + n)
    (fun i => by lia)]
  let S0 : {S : Finset (Fin (m+n)) // S.card = Fintype.card (Fin n)} :=
    ⟨Finset.univ.map (Fin.natAddEmb m), by simp⟩
  have hS0 : ∀ j, sEnum S0 j = m + j := by
    intro j
    have := Finset.orderEmbOfFin_unique (S0.2.trans (Fintype.card_fin n)) (f := Fin.natAdd m)
      (fun x => by simp [S0]) (Fin.strictMono_natAdd m)
    simp only [sEnum]
    rw [← this]
    simp
  have hT : Matrix.det (Matrix.of fun i j : Fin n => toeplitz a (m + i) (sEnum S0 j)) = 1 := by
    simp_rw [hS0]
    rw [Matrix.det_of_isLowerTriangular]
    · simp [toeplitz_apply, h0]
    · intro i j hij
      have : (i:ℕ) < j := hij
      simp [toeplitz_apply]
      lia
  have hpos : 0 < Matrix.det (Matrix.of fun i j : Fin n =>
      toeplitz (expSeq ε) (sEnum S0 i) j) := by
    simp_rw [hS0]
    rw [← A_eq]
    exact A_expSeq_pos hε n m
  calc (0:ℝ) < _ := by show 0 < _ * _; rw [hT, one_mul]; exact hpos
    _ ≤ _ := Finset.single_le_sum
      (f := fun S : {S : Finset (Fin (m+n)) // S.card = Fintype.card (Fin n)} =>
        Matrix.det (Matrix.of fun i j : Fin n => toeplitz a (m + i) (sEnum S j)) *
          Matrix.det (Matrix.of fun i j : Fin n => toeplitz (expSeq ε) (sEnum S i) j))
        (fun S _ => mul_nonneg
          (ha (rows := fun i => m + i) (cols := sEnum S)
            (fun x y h => by simpa using h) (sEnum_strictMono S))
          (isPolyaFreqSeq_expSeq hε.le (rows := sEnum S) (cols := fun j => j)
            (sEnum_strictMono S) (fun x y h => h)))
        (Finset.mem_univ S0)

/-- **Reduction of Edrei–Thoma to the case with property (P).** For a Pólya frequency
sequence `a` with `a 0 = 1` and `ε > 0`, the perturbed sequence `a ⋆ exp (ε ·)` is again a
Pólya frequency
sequence, with constant term `1` and property (P); hence the A17 results (`coeff_S_nonneg`,
`monotone_limits`, ...) apply to it. (If
`a ⋆ exp (ε ·) = e^{φ} ∏(1+α_i z)/∏(1-β_i z)`, then
`a = e^{φ - ε z} ∏(1+α_i z)/∏(1-β_i z)`.) -/
theorem reduction_to_P {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) (h0 : a 0 = 1)
    {ε : ℝ} (hε : 0 < ε) :
    IsPolyaFreqSeq (natCauchyConvolution a (expSeq ε)) ∧
      natCauchyConvolution a (expSeq ε) 0 = 1 ∧
      ∀ n m, 0 < A (natCauchyConvolution a (expSeq ε)) n m :=
  ⟨ha.natCauchyConvolution (isPolyaFreqSeq_expSeq hε.le),
    by simp [natCauchyConvolution, expSeq, h0],
    A_natCauchyConvolution_expSeq_pos ha h0 hε⟩


end RealRooted.EdreiThoma
