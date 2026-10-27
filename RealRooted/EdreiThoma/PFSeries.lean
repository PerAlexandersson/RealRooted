module

public import RealRooted.AissenSchoenbergWhitneyBase
import RealRooted.Mathlib.LinearAlgebra.Matrix.JacobiComplementaryMinor

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace RealRooted

/-- A general `2 × 2` minor: rows `(p, q)`, columns `(0, s)`. -/
theorem IsPolyaFreqSeq.minor2 {a : ℕ → ℝ} (h : IsPolyaFreqSeq a) {p q s : ℕ}
    (hpq : p < q) (hs : s ≤ p) (hs' : 0 < s) :
    a (p - s) * a q ≤ a p * a (q - s) := by
  have := h (rows := ![p, q]) (cols := ![0, s]) (by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all) (by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
  rw [Matrix.det_fin_two] at this
  have hsq : s ≤ q := by lia
  simp [toeplitz, hs, hsq] at this
  linarith

/-- (ii) Log-concavity (2 × 2 minors). -/
theorem IsPolyaFreqSeq.log_concave {a : ℕ → ℝ} (h : IsPolyaFreqSeq a) (n : ℕ) :
    a n * a (n + 2) ≤ a (n + 1) ^ 2 := by
  simpa [pow_two] using h.minor2 (p := n + 1) (q := n + 2) (s := 1)
    (by lia) (by lia) (by lia)

/-- One-step bound `a n ≤ (a 1)^n` (from the minors with rows `(1, n+1)`, columns `(0, 1)`). -/
private theorem IsPolyaFreqSeq.le_pow_one {a : ℕ → ℝ} (h : IsPolyaFreqSeq a)
    (h0 : a 0 = 1) (n : ℕ) : a n ≤ a 1 ^ n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have := h.minor2 (p := 1) (q := n+1) (s := 1) (by lia) le_rfl one_pos
    simp [h0] at this
    rw [pow_succ]
    nlinarith [h.nonneg 1, h.nonneg n]

/-- (iii) Geometric growth: `a_n ≤ M^n`; so the generating function has positive radius. -/
theorem IsPolyaFreqSeq.exists_geometric_bound {a : ℕ → ℝ} (h : IsPolyaFreqSeq a)
    (h0 : a 0 = 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n, a n ≤ M ^ n :=
  ⟨a 1, h.nonneg 1, h.le_pow_one h0⟩
/-- The leading `N × N` block of the Toeplitz matrix. -/
private def toepMat (a : ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => toeplitz a i j

private lemma toepMat_mul {a c : ℕ → ℝ}
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), c k * a (n - k) = if n = 0 then 1 else 0)
    (N : ℕ) : toepMat a N * toepMat c N = 1 := by
  ext i j
  simp only [Matrix.mul_apply, toepMat, Matrix.of_apply, Matrix.one_apply]
  rcases lt_or_ge (i : ℕ) j with hij | hij
  · rw [ite_eq_right (by intro e; subst e; exact lt_irrefl _ hij)]
    apply Finset.sum_eq_zero
    intro l _
    simp only [toeplitz_apply]
    split_ifs <;> first | (exfalso; lia) | simp
  · have := Fin.sum_univ_eq_sum_range
      (fun l => toeplitz a i l * toeplitz c l j) N
    rw [this]
    have hsub : Finset.Ico (j : ℕ) (i + 1) ⊆ Finset.range N := by
      intro l hl; simp at hl ⊢; lia
    rw [← Finset.sum_subset hsub (fun l _ hl => by
      simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hl
      simp only [toeplitz_apply]; split_ifs <;> first | (exfalso; lia) | simp)]
    rw [Finset.sum_Ico_eq_sum_range]
    have h2 : (i : ℕ) + 1 - j = (i - j : ℕ) + 1 := by lia
    rw [h2]
    have h3 : ∀ q ∈ Finset.range ((i - j : ℕ) + 1),
        toeplitz a i (j + q) * toeplitz c (j + q) j = c q * a ((i - j : ℕ) - q) := by
      intro q hq
      simp at hq
      simp only [toeplitz_apply]
      rw [ite_eq_left (by lia), ite_eq_left (by lia)]
      rw [mul_comm]; congr 2 <;> lia
    rw [Finset.sum_congr rfl h3, hconv]
    congr 1
    simp only [Fin.ext_iff, eq_iff_iff]
    lia

private lemma toepMat_det {a : ℕ → ℝ} (h0 : a 0 = 1) (N : ℕ) : (toepMat a N).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [toepMat, toeplitz_apply, h0]
  · intro i j hij
    simp only [toepMat, Matrix.of_apply, toeplitz_apply]
    rw [ite_eq_right]
    have : i < j := hij
    rw [Fin.lt_def] at this; lia
/-- (iv) The reciprocal series with alternating signs, `1 / F(-z) = ∑ b_n z^n`, is again a PF
sequence (Jacobi complementary minors).  Here `∑_{k ≤ n} a_k (-1)^{n-k} b_{n-k} = δ_{n0}`. -/
theorem IsPolyaFreqSeq.exists_inverse {a : ℕ → ℝ} (h : IsPolyaFreqSeq a) (h0 : a 0 = 1) :
    ∃ b : ℕ → ℝ, IsPolyaFreqSeq b ∧ b 0 = 1 ∧ ∀ n, ∑ k ∈ Finset.range (n + 1),
      a k * ((-1) ^ (n - k) * b (n - k)) = if n = 0 then 1 else 0 := by
  set c : ℕ → ℝ := fun n => PowerSeries.coeff n (PowerSeries.mk a)⁻¹ with hc
  have hcc : PowerSeries.constantCoeff (PowerSeries.mk a) ≠ 0 := by simp [h0]
  have hconv1 : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * c (n - k) =
      if n = 0 then 1 else 0 := by
    intro n
    have := congrArg (PowerSeries.coeff n) (PowerSeries.mul_inv_cancel _ hcc)
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun p q => PowerSeries.coeff p (PowerSeries.mk a) *
        PowerSeries.coeff q (PowerSeries.mk a)⁻¹),
      PowerSeries.coeff_one] at this
    simpa [hc] using this
  have hconv2 : ∀ n, ∑ k ∈ Finset.range (n + 1), c k * a (n - k) =
      if n = 0 then 1 else 0 := by
    intro n
    have := congrArg (PowerSeries.coeff n) (PowerSeries.inv_mul_cancel _ hcc)
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun p q => PowerSeries.coeff p (PowerSeries.mk a)⁻¹ *
        PowerSeries.coeff q (PowerSeries.mk a)),
      PowerSeries.coeff_one] at this
    simpa [hc] using this
  refine ⟨fun n => (-1) ^ n * c n, ?_, ?_, ?_⟩
  · intro k r cc hr hcc'
    set N := (∑ i, (r i + cc i)) + 1 with hN
    have hrN : ∀ i, r i < N := fun i => by
      have := Finset.single_le_sum (f := fun i => r i + cc i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
      lia
    have hcN : ∀ i, cc i < N := fun i => by
      have := Finset.single_le_sum (f := fun i => r i + cc i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
      lia
    have htrunc : (toepMat a N).IsTotallyNonneg := by
      intro m f g hf hg
      convert h (rows := fun i => (f i : ℕ)) (cols := fun i => (g i : ℕ))
        (fun _ _ hij => hf hij) (fun _ _ hij => hg hij) using 1
      congr 1
    have hinv := Matrix.tn_inverse (toepMat a N) (toepMat c N) (toepMat_mul hconv2 N)
      (toepMat_det h0 N) htrunc
    have hminor := hinv (rows := fun i => (⟨r i, hrN i⟩ : Fin N))
      (cols := fun i => (⟨cc i, hcN i⟩ : Fin N))
      (fun _ _ hij => hr hij) (fun _ _ hij => hcc' hij)
    convert hminor using 2
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, toepMat, toeplitz_apply]
    split_ifs with hle
    · have : (-1 : ℝ) ^ r i = (-1) ^ (r i - cc j) * (-1) ^ cc j := by
        rw [← pow_add]; congr 1; lia
      rw [this]
      have h2 : ((-1 : ℝ) ^ cc j) * (-1) ^ cc j = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
      linear_combination (-(-1) ^ (r i - cc j) * c (r i - cc j)) * h2
    · simp
  · simp [hc, h0]
  · intro n
    rw [← hconv1 n]
    apply Finset.sum_congr rfl
    intro k _
    change a k * ((-1) ^ (n - k) * ((-1) ^ (n - k) * c (n - k))) = _
    rw [← mul_assoc ((-1 : ℝ) ^ (n - k)), ← pow_add, ← two_mul, pow_mul]; simp

/-! ## Auxiliary results toward (v)/(vi) -/

/-- No internal zeros: once a PF sequence with `a 0 = 1` vanishes, it vanishes from then on. -/
theorem IsPolyaFreqSeq.eq_zero_of_ge {a : ℕ → ℝ} (h : IsPolyaFreqSeq a)
    (h0 : a 0 = 1) {m n : ℕ}
    (hm : a m = 0) (hmn : m ≤ n) : a n = 0 := by
  classical
  have hex : ∃ m, a m = 0 := ⟨m, hm⟩
  set m0 := Nat.find hex with hm0
  have hm0z : a m0 = 0 := Nat.find_spec hex
  have hm0le : m0 ≤ m := Nat.find_min' hex hm
  have hm0pos : 0 < m0 := by
    rcases Nat.eq_zero_or_pos m0 with h' | h'
    · rw [h'] at hm0z; rw [h0] at hm0z; exact absurd hm0z one_ne_zero
    · exact h'
  have hprev : 0 < a (m0 - 1) := by
    have hne : a (m0 - 1) ≠ 0 := Nat.find_min hex (by lia)
    exact lt_of_le_of_ne (h.nonneg _) (Ne.symm hne)
  have hm0n : m0 ≤ n := by lia
  rcases hm0n.lt_or_eq with hlt | heq
  · have := h.minor2 (p := m0) (q := n) (s := 1) hlt (by lia) one_pos
    rw [hm0z, zero_mul] at this
    have h2 := h.nonneg n
    have : a n ≤ 0 := by
      by_contra hc; push Not at hc
      linarith [mul_pos hprev hc]
    linarith
  · rw [← heq]; exact hm0z

/-- The generating function converges absolutely on the disc `a 1 * ‖z‖ < 1`. -/
theorem IsPolyaFreqSeq.summable_genFun {a : ℕ → ℝ} (h : IsPolyaFreqSeq a)
    (h0 : a 0 = 1) {z : ℂ}
    (hz : a 1 * ‖z‖ < 1) : Summable (fun n => (a n : ℂ) * z ^ n) := by
  apply Summable.of_norm_bounded (g := fun n => (a 1 * ‖z‖) ^ n)
  · exact summable_geometric_of_lt_one (mul_nonneg (h.nonneg 1) (norm_nonneg _)) hz
  · intro n
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (h.nonneg n), mul_pow]
    gcongr
    exact h.le_pow_one h0 n

/-- The generating function series is absolutely summable on the disc `a 1 * ‖z‖ < 1`. -/
theorem IsPolyaFreqSeq.summable_norm_genFun {a : ℕ → ℝ} (h : IsPolyaFreqSeq a)
    (h0 : a 0 = 1) {z : ℂ} (hz : a 1 * ‖z‖ < 1) :
    Summable fun n => ‖(a n : ℂ) * z ^ n‖ :=
  (h.summable_genFun h0 hz).norm

end RealRooted
