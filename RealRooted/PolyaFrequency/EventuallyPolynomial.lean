import RealRooted.AissenSchoenbergWhitneyBase
import RealRooted.Mathlib.Analysis.Polynomial.Asymptotics
import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.ColumnDifference
import RealRooted.Mathlib.Topology.Instances.Matrix.Determinant

/-!
# Eventually polynomial Pólya-frequency sequences

This file records eventual positivity and ordered initial-column-minor
nonnegativity for causal forward differences of Pólya-frequency sequences
whose tails are given by evaluations of a nonzero polynomial.  It does not
yet prove total nonnegativity of the causal forward difference.
-/

open Filter Polynomial Topology

namespace RealRooted

/-- The Toeplitz matrix of the causal forward difference is obtained by
subtracting the next column entrywise. This is an entrywise identity, not a
total-nonnegativity preservation result. -/
theorem toeplitz_causalFwdDiff (a : ℕ → ℝ) (i j : ℕ) :
    toeplitz (Function.causalFwdDiff a) i j =
      toeplitz a i j - toeplitz a i (j + 1) := by
  by_cases hji : j ≤ i
  · rw [toeplitz_apply, if_pos hji, toeplitz_apply, if_pos hji]
    by_cases hzero : i - j = 0
    · have hij : i = j := Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) hji
      subst i
      simp [toeplitz_apply, Function.causalFwdDiff]
    · have hpos : 0 < i - j := Nat.pos_of_ne_zero hzero
      have hsucc : j + 1 ≤ i := by
        exact Nat.succ_le_iff.mpr (Nat.lt_of_sub_pos hpos)
      rw [toeplitz_apply, if_pos hsucc]
      have hindex : i - j = i - (j + 1) + 1 := by
        lia
      rw [hindex]
      simp [Function.causalFwdDiff]
  · have hsucc : ¬ j + 1 ≤ i := fun h => hji (le_trans (Nat.le_succ _) h)
    simp [toeplitz_apply, hji, hsucc]

/-- The finite Toeplitz minor with a final row normalized by `d`. -/
noncomputable def normalizedToeplitzMinor (a : ℕ → ℝ) {n : ℕ} (rows : Fin n → ℕ)
    (N : ℕ) (d : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => Fin.lastCases (toeplitz a N j / d)
    (fun i => toeplitz a (rows i) j) i

/-- The entrywise limit of a normalized appended Toeplitz minor. -/
def normalizedToeplitzMinorLimit (a : ℕ → ℝ) {n : ℕ} (rows : Fin n → ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => Fin.lastCases 1 (fun i => toeplitz a (rows i) j) i

private theorem strictMono_lastCases {n : ℕ} {rows : Fin n → ℕ}
    (hrows : StrictMono rows) {N : ℕ} (hN : ∀ i, rows i < N) :
    StrictMono (Fin.lastCases N rows) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last => exact (not_lt_of_ge (Fin.le_last _) hij).elim
  | cast i =>
      cases j using Fin.lastCases with
      | last => simpa using hN i
      | cast j => simpa using hrows (Fin.castSucc_lt_castSucc_iff.mp hij)

/-- An ordered PF Toeplitz minor remains nonnegative when only its appended
final row is divided by a positive scalar. -/
theorem IsPolyaFreqSeq.det_normalizedToeplitzMinor_nonneg {a : ℕ → ℝ}
    (ha : IsPolyaFreqSeq a) {n : ℕ} {rows : Fin n → ℕ} (hrows : StrictMono rows)
    {N : ℕ} (hN : ∀ i, rows i < N) {d : ℝ} (hd : 0 < d) :
    0 ≤ (normalizedToeplitzMinor a rows N d).det := by
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    (toeplitz a).submatrix (Fin.lastCases N rows) Fin.val
  have hcols : StrictMono (fun j : Fin (n + 1) => (j : ℕ)) := fun _ _ hij => hij
  have hM : 0 ≤ M.det := ha (strictMono_lastCases hrows hN) hcols
  have hnormalized : normalizedToeplitzMinor a rows N d =
      Matrix.updateRow M (Fin.last n) (d⁻¹ • M (Fin.last n)) := by
    ext i j
    cases i using Fin.lastCases <;> simp [normalizedToeplitzMinor, M, div_eq_inv_mul]
  rw [hnormalized, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  exact mul_nonneg (inv_nonneg.mpr hd.le) hM

/-- The normalized appended Toeplitz minors are eventually nonnegative when
their final-row normalizers are eventually positive. -/
theorem IsPolyaFreqSeq.eventually_det_normalizedToeplitzMinor_nonneg
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) {n : ℕ} {rows : Fin n → ℕ}
    (hrows : StrictMono rows) {d : ℕ → ℝ}
    (hrows_lt : ∀ᶠ N in atTop, ∀ i, rows i < N)
    (hd : ∀ᶠ N in atTop, 0 < d N) :
    ∀ᶠ N in atTop, 0 ≤ (normalizedToeplitzMinor a rows N (d N)).det := by
  filter_upwards [hrows_lt, hd] with N hN hdN
  exact ha.det_normalizedToeplitzMinor_nonneg hrows hN hdN

/-- For a PF sequence with a nonzero eventual polynomial tail, the normalized
appended Toeplitz minors using the tail entry in column `n` are eventually
nonnegative. -/
theorem IsPolyaFreqSeq.eventually_det_normalizedToeplitzMinor_tail_nonneg
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) {p : ℝ[X]} (hp : p ≠ 0)
    (hap : ∀ᶠ k in atTop, a k = p.eval (k : ℝ)) {n : ℕ}
    {rows : Fin n → ℕ} (hrows : StrictMono rows)
    (hrows_lt : ∀ᶠ N in atTop, ∀ i, rows i < N) :
    ∀ᶠ N in atTop,
      0 ≤ (normalizedToeplitzMinor a rows N (a (N - n))).det := by
  apply ha.eventually_det_normalizedToeplitzMinor_nonneg hrows hrows_lt
  exact (tendsto_sub_atTop_nat n).eventually
    (Polynomial.eventually_pos_of_eventually_nonneg_of_eventually_eq_eval_nat hp
      (Eventually.of_forall ha.nonneg) hap)

/-- Normalizing the appended row by its entry in column `n` converges
entrywise to a row of ones. -/
theorem tendsto_normalizedToeplitzMinor_tail {a : ℕ → ℝ} {p : ℝ[X]}
    (hp : p ≠ 0) (hap : ∀ᶠ k in atTop, a k = p.eval (k : ℝ))
    {n : ℕ} (rows : Fin n → ℕ) (i j : Fin (n + 1)) :
    Tendsto (fun N => normalizedToeplitzMinor a rows N (a (N - n)) i j)
      atTop (𝓝 (normalizedToeplitzMinorLimit a rows i j)) := by
  cases i using Fin.lastCases with
  | cast i =>
      simp [normalizedToeplitzMinor, normalizedToeplitzMinorLimit]
  | last =>
      have hratio := Polynomial.tendsto_nat_sub_div_of_eventually_eq_eval hp hap j n
      have htoeplitz : Tendsto (fun N => toeplitz a N j / a (N - n)) atTop (𝓝 1) := by
        apply hratio.congr'
        filter_upwards [eventually_ge_atTop (j : ℕ)] with N hN
        simp [toeplitz_apply, hN]
      simpa [normalizedToeplitzMinor, normalizedToeplitzMinorLimit] using htoeplitz

/-- The limiting appended minor has nonnegative determinant. -/
theorem IsPolyaFreqSeq.det_normalizedToeplitzMinorLimit_nonneg
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) {p : ℝ[X]} (hp : p ≠ 0)
    (hap : ∀ᶠ k in atTop, a k = p.eval (k : ℝ)) {n : ℕ}
    {rows : Fin n → ℕ} (hrows : StrictMono rows)
    (hrows_lt : ∀ᶠ N in atTop, ∀ i, rows i < N) :
    0 ≤ (normalizedToeplitzMinorLimit a rows).det := by
  apply Matrix.det_nonneg_of_tendsto
  · exact ha.eventually_det_normalizedToeplitzMinor_tail_nonneg hp hap hrows hrows_lt
  · intro i j
    exact tendsto_normalizedToeplitzMinor_tail hp hap rows i j

/-- Ordered initial-column minors of the causal forward-difference Toeplitz
matrix are nonnegative under a nonzero eventual polynomial tail. -/
theorem IsPolyaFreqSeq.causalFwdDiff_initialMinor_nonneg
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) {p : ℝ[X]} (hp : p ≠ 0)
    (hap : ∀ᶠ k in atTop, a k = p.eval (k : ℝ)) {n : ℕ}
    {rows : Fin n → ℕ} (hrows : StrictMono rows) :
    0 ≤ ((toeplitz (Function.causalFwdDiff a)).submatrix rows Fin.val).det := by
  have hrows_lt : ∀ᶠ N in atTop, ∀ i, rows i < N :=
    Filter.eventually_all.mpr fun i => eventually_gt_atTop (rows i)
  have hlimit := ha.det_normalizedToeplitzMinorLimit_nonneg hp hap hrows hrows_lt
  have hrow : ∀ j, normalizedToeplitzMinorLimit a rows (Fin.last n) j = 1 := by
    intro j
    simp [normalizedToeplitzMinorLimit]
  rw [Matrix.det_eq_last_apply_mul_det_adjacentColumnDifference_of_lastRow_eq
    (normalizedToeplitzMinorLimit a rows) 1 hrow] at hlimit
  have hblock : Matrix.of (fun (i j : Fin n) =>
      normalizedToeplitzMinorLimit a rows i.castSucc j.castSucc -
        normalizedToeplitzMinorLimit a rows i.castSucc j.succ) =
      (toeplitz (Function.causalFwdDiff a)).submatrix rows Fin.val := by
    ext i j
    simpa [normalizedToeplitzMinorLimit] using
      (toeplitz_causalFwdDiff a (rows i) (j : ℕ)).symm
  simpa [hblock] using hlimit

/-- A Pólya-frequency sequence which eventually agrees with evaluations of a
nonzero real polynomial is eventually strictly positive. -/
theorem IsPolyaFreqSeq.eventually_pos_of_eventually_polynomial
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) {p : ℝ[X]} (hp : p ≠ 0)
    (hap : ∀ᶠ n in atTop, a n = p.eval (n : ℝ)) :
    ∀ᶠ n in atTop, 0 < a n :=
  Polynomial.eventually_pos_of_eventually_nonneg_of_eventually_eq_eval_nat hp
    (Eventually.of_forall ha.nonneg) hap

end RealRooted
