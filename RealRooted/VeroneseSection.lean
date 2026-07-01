import RealRooted.AissenSchoenbergWhitney
import RealRooted.HermiteBiehler
import RealRooted.WagnerX
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Veronese sections

This file starts the formalization of Athanasiadis--Wagner's Veronese-section
results.  It contains the coefficient-level core: Veronese subsequences
preserve Toeplitz total nonnegativity, by identifying each Toeplitz minor with
a subminor of the original Toeplitz matrix.  It also records the two-row Lace
submatrix statements and conditional polynomial wrappers around
Aissen--Schoenberg--Whitney, Hermite--Biehler, and Hurwitz-matrix interfaces.

The unconditional real-rootedness theorem for Veronese sections of
real-rooted polynomials with nonnegative coefficients is proved separately in
`RealRooted.VeroneseMatrix`, using a cyclic matrix and interlacing-preserver
argument.  This file should therefore be read as the Athanasiadis--Wagner
background and conditional fully-interlacing route, not as the final matrix
proof of that real-rootedness consequence.
-/

open Polynomial Matrix

noncomputable section

namespace RealRooted

/-- Coefficient-level Veronese section of a sequence. -/
def veroneseSectionSeq (r k : ℕ) (a : ℕ → ℝ) : ℕ → ℝ :=
  fun n => a (k + r * n)

/-- The `k`th `r`-Veronese section of a formal power series. -/
def veroneseSectionPowerSeries (r k : ℕ) (A : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => PowerSeries.coeff (k + r * n) A

@[simp] theorem coeff_veroneseSectionPowerSeries (r k n : ℕ) (A : PowerSeries ℝ) :
    PowerSeries.coeff n (veroneseSectionPowerSeries r k A) =
      PowerSeries.coeff (k + r * n) A := by
  simp [veroneseSectionPowerSeries]

/-- The `k`th `r`-Veronese section of a polynomial, with the degenerate case
`r = 0` set to zero.  The coefficient theorem below is intended for `0 < r`. -/
def veroneseSectionPolynomial (r k : ℕ) (p : ℝ[X]) : ℝ[X] :=
  if hr0 : r = 0 then 0 else
    Polynomial.ofFinsupp <|
      Finsupp.onFinset (Finset.range (p.natDegree + 1))
        (fun n => p.coeff (k + r * n))
        (by
          intro n hn
          have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
          by_contra hmem
          have hnotlt : ¬ n < p.natDegree + 1 := by
            simp_all
          have hle : p.natDegree + 1 ≤ n := Nat.le_of_not_gt hnotlt
          have hpn : p.natDegree < n := Nat.lt_of_succ_le hle
          have hn_le_mul : n ≤ r * n := by
            simpa [one_mul] using
              Nat.mul_le_mul_right n (Nat.succ_le_of_lt hrpos)
          have hn_le : n ≤ k + r * n :=
            Nat.le_trans hn_le_mul (Nat.le_add_left (r * n) k)
          exact hn <|
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hpn hn_le))

@[simp] theorem coeff_veroneseSectionPolynomial {r k n : ℕ} {p : ℝ[X]}
    (hr : 0 < r) :
    (veroneseSectionPolynomial r k p).coeff n = p.coeff (k + r * n) := by
  simp [veroneseSectionPolynomial, Nat.ne_of_gt hr]

theorem hasNonnegCoeffs_veroneseSectionPolynomial {r k : ℕ} {p : ℝ[X]}
    (hr : 0 < r) (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (veroneseSectionPolynomial r k p) := by
  intro n
  rw [coeff_veroneseSectionPolynomial (r := r) (k := k) (p := p) hr]
  exact hp (k + r * n)

theorem veroneseSectionPolynomial_ne_zero_of_coeff_ne_zero
    {r k n : ℕ} {p : ℝ[X]} (hr : 0 < r)
    (hcoeff : p.coeff (k + r * n) ≠ 0) :
    veroneseSectionPolynomial r k p ≠ 0 := by
  intro hzero
  have hcoeff_zero : (veroneseSectionPolynomial r k p).coeff n = 0 := by
    simp_all
  rw [coeff_veroneseSectionPolynomial (r := r) (k := k) (p := p) hr] at hcoeff_zero
  lia

/-! ## Veronese section recurrences -/

/-- Veronese sections commute with addition. -/
theorem veroneseSectionPolynomial_add {r k : ℕ} (hr : 0 < r) (p q : ℝ[X]) :
    veroneseSectionPolynomial r k (p + q) =
      veroneseSectionPolynomial r k p + veroneseSectionPolynomial r k q := by
  ext n
  simp_all

/-- Veronese sections commute with scalar multiplication. -/
theorem veroneseSectionPolynomial_C_mul {r k : ℕ} (hr : 0 < r)
    (a : ℝ) (p : ℝ[X]) :
    veroneseSectionPolynomial r k (C a * p) =
      C a * veroneseSectionPolynomial r k p := by
  ext n
  simp_all

/-- Multiplication by `X` shifts positive Veronese sections down by one
residue. -/
theorem veroneseSectionPolynomial_X_mul_succ {r k : ℕ} (hk : k + 1 < r)
    (p : ℝ[X]) :
    veroneseSectionPolynomial r (k + 1) (X * p) =
      veroneseSectionPolynomial r k p := by
  have hr : 0 < r := by lia
  ext n
  rw [coeff_veroneseSectionPolynomial (r := r) (k := k + 1) (p := X * p) hr]
  rw [show k + 1 + r * n = (k + r * n) + 1 by lia]
  simp_all

/-- Multiplication by `X` wraps the zeroth Veronese section to the last
residue, with one extra factor of `X`. -/
theorem veroneseSectionPolynomial_X_mul_zero {r : ℕ} (hr : 0 < r)
    (p : ℝ[X]) :
    veroneseSectionPolynomial r 0 (X * p) =
      X * veroneseSectionPolynomial r (r - 1) p := by
  ext n
  cases n with
  | zero =>
      simp_all
  | succ n =>
      have hidx : 0 + r * (n + 1) = (r - 1 + r * n) + 1 := by
        lia
      simp_all

/-- The zeroth Veronese section after multiplying by a linear factor
`X + a`.  This is the wrap-around update used in Wagner-style proofs of
Veronese real-rootedness. -/
theorem veroneseSectionPolynomial_X_add_C_mul_zero {r : ℕ} (hr : 0 < r)
    (a : ℝ) (p : ℝ[X]) :
    veroneseSectionPolynomial r 0 ((X + C a) * p) =
      X * veroneseSectionPolynomial r (r - 1) p +
        C a * veroneseSectionPolynomial r 0 p := by
  have hmul : (X + C a) * p = X * p + C a * p := by grind
  rw [hmul]
  rw [veroneseSectionPolynomial_add hr]
  rw [veroneseSectionPolynomial_X_mul_zero hr]
  rw [veroneseSectionPolynomial_C_mul hr]

/-- Positive-residue Veronese sections after multiplying by a linear factor
`X + a`. -/
theorem veroneseSectionPolynomial_X_add_C_mul_succ {r k : ℕ}
    (hk : k + 1 < r) (a : ℝ) (p : ℝ[X]) :
    veroneseSectionPolynomial r (k + 1) ((X + C a) * p) =
      veroneseSectionPolynomial r k p +
        C a * veroneseSectionPolynomial r (k + 1) p := by
  have hr : 0 < r := by lia
  have hmul : (X + C a) * p = X * p + C a * p := by grind
  rw [hmul]
  rw [veroneseSectionPolynomial_add hr]
  rw [veroneseSectionPolynomial_X_mul_succ hk]
  rw [veroneseSectionPolynomial_C_mul hr]

/-! ## Two-row Lace matrices -/

/-- The Lace matrix of a two-term sequence of coefficient sequences.

Even rows contain the Toeplitz matrix for `a`; odd rows contain the Toeplitz
matrix for `b`. This is the two-row special case needed for Corollary 5.6. -/
def lacePair (a b : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  .of fun i j ↦
    if i % 2 = 0 then
      toeplitz a (i / 2) j
    else
      toeplitz b (i / 2) j

/-- TNN formulation of a fully interlacing two-term sequence. -/
def FullyInterlacingPair (a b : ℕ → ℝ) : Prop := (lacePair a b).IsTotallyNonneg

/-! ## Hurwitz matrix comparison for odd/even parts -/

/-- Row-oriented Hurwitz matrix entry attached to a coefficient sequence.

Even rows use odd coefficients and odd rows use even coefficients.  With this
convention, the Hurwitz matrix of `q(x^2) + x p(x^2)` is literally the two-row
Lace matrix of `p` and `q`. -/
def hurwitz (c : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  .of fun i j ↦
    if i % 2 = 0 then
      toeplitz (fun n => c (2 * n + 1)) (i / 2) j
    else
      toeplitz (fun n => c (2 * n)) (i / 2) j

@[simp] theorem hurwitz_oddEvenPolynomial (p q : ℝ[X]) (row col : ℕ) :
    hurwitz (fun n => (oddEvenPolynomial p q).coeff n) row col =
      lacePair p.coeff (fun n => q.coeff n) row col := by
  unfold hurwitz lacePair toeplitz
  simp

/-- For odd/even polynomials, Hurwitz total nonnegativity is exactly the
two-row Lace total nonnegativity condition. -/
theorem hurwitzMatrixTotallyNonnegative_oddEvenPolynomial_iff_fullyInterlacingPair
    (p q : ℝ[X]) :
    (hurwitz (oddEvenPolynomial p q).coeff).IsTotallyNonneg ↔
      FullyInterlacingPair p.coeff q.coeff := by
  simp [FullyInterlacingPair, hurwitz, lacePair]

/-- The Lace matrix of the interleaved Veronese sections
`S_0 a, S_0 b, S_1 a, S_1 b, ...`, encoded as the column submatrix of the
original Lace matrix with column indices divisible by `r`. -/
def veronesePairLace (r : ℕ) (a b : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  .of fun i j ↦ lacePair a b i (r * j)

/-- TNN formulation of full interlacing for the interleaved Veronese sections
of a two-term sequence. -/
def VeronesePairFullyInterlacing (r : ℕ) (a b : ℕ → ℝ) : Prop :=
  (veronesePairLace r a b).IsTotallyNonneg

/-- Two-row TNN version of the Veronese preservation theorem: the Lace matrix
of the interleaved Veronese sections is a column submatrix of the original Lace
matrix. -/
theorem fullyInterlacingPair_veronesePair {a b : ℕ → ℝ}
    (h : FullyInterlacingPair a b) {r : ℕ} (hr : 0 < r) :
    VeronesePairFullyInterlacing r a b := by
  have hcol : StrictMono (fun col => r * col) :=
    fun _ _ hij => by simp_all
  exact h.submatrix strictMono_id hcol

/-- Even rows of `veronesePairLace` are Toeplitz rows for the sections of
the first sequence. -/
theorem veronesePairLace_even {a b : ℕ → ℝ} {r k n c : ℕ} (hk : k < r) :
    veronesePairLace r a b (2 * (k + r * n)) c =
      toeplitz (veroneseSectionSeq r k a) n c := by
  have hmod : 2 * (k + r * n) % 2 = 0 := Nat.mul_mod_right 2 (k + r * n)
  have hdiv : 2 * (k + r * n) / 2 = k + r * n :=
    Nat.mul_div_right (k + r * n) (by lia)
  dsimp [veronesePairLace, lacePair]
  rw [if_pos hmod, hdiv]
  dsimp [toeplitz, veroneseSectionSeq]
  by_cases hc : c ≤ n
  · have hc' : r * c ≤ k + r * n :=
      Nat.le_trans (Nat.mul_le_mul_left r hc) (Nat.le_add_left (r * n) k)
    rw [if_pos hc, if_pos hc']
    congr 1
    calc
      k + r * n - r * c = k + (r * n - r * c) :=
        Nat.add_sub_assoc (Nat.mul_le_mul_left r hc) k
      _ = k + r * (n - c) := by
        rw [← Nat.mul_sub_left_distrib]
  · have hlt : n < c := Nat.lt_of_not_ge hc
    have hc' : ¬ r * c ≤ k + r * n := by
      have hsucc : n + 1 ≤ c := Nat.succ_le_of_lt hlt
      have hmul : r * (n + 1) ≤ r * c := Nat.mul_le_mul_left r hsucc
      lia
    lia

/-- Odd rows of `veronesePairLace` are Toeplitz rows for the sections of
the second sequence. -/
theorem veronesePairLace_odd {a b : ℕ → ℝ} {r k n c : ℕ} (hk : k < r) :
    veronesePairLace r a b (2 * (k + r * n) + 1) c =
      toeplitz (veroneseSectionSeq r k b) n c := by
  have hmod_ne : ¬ (2 * (k + r * n) + 1) % 2 = 0 := by
    lia
  have hdiv : (2 * (k + r * n) + 1) / 2 = k + r * n := by
    lia
  dsimp [veronesePairLace, lacePair]
  rw [if_neg hmod_ne, hdiv]
  dsimp [toeplitz, veroneseSectionSeq]
  by_cases hc : c ≤ n
  · have hc' : r * c ≤ k + r * n :=
      Nat.le_trans (Nat.mul_le_mul_left r hc) (Nat.le_add_left (r * n) k)
    rw [if_pos hc, if_pos hc']
    congr 1
    calc
      k + r * n - r * c = k + (r * n - r * c) :=
        Nat.add_sub_assoc (Nat.mul_le_mul_left r hc) k
      _ = k + r * (n - c) := by
        rw [← Nat.mul_sub_left_distrib]
  · have hlt : n < c := Nat.lt_of_not_ge hc
    have hc' : ¬ r * c ≤ k + r * n := by
      have hsucc : n + 1 ≤ c := Nat.succ_le_of_lt hlt
      have hmul : r * (n + 1) ≤ r * c := Nat.mul_le_mul_left r hsucc
      lia
    lia

/-- The first row family of a fully interlacing pair is a Pólya-frequency
sequence. -/
theorem FullyInterlacingPair.left_pf {a b : ℕ → ℝ}
    (h : FullyInterlacingPair a b) :
    IsPolyaFreqSeq a := by
  intro n rows cols hrows hcols
  let rows' : Fin n → ℕ := fun i => 2 * rows i
  have hrows' : StrictMono rows' :=
    fun _ _ hij => Nat.mul_lt_mul_of_pos_left (hrows hij) (by lia)
  have hminor : (toeplitz a).submatrix rows cols = submatrix (lacePair a b) rows' cols := by
    ext i j
    simp [submatrix, rows', lacePair]
  rw [hminor]
  exact h hrows' hcols

/-- The second row family of a fully interlacing pair is a Pólya-frequency
sequence. -/
theorem FullyInterlacingPair.right_pf {a b : ℕ → ℝ} (h : FullyInterlacingPair a b) :
    IsPolyaFreqSeq b := by
  intro n rows cols hrows hcols
  let rows' : Fin n → ℕ := fun i => 2 * rows i + 1
  have hrows' : StrictMono rows' :=
    fun _ _ hij => Nat.add_lt_add_right
      (Nat.mul_lt_mul_of_pos_left (hrows hij) (by lia)) 1
  have hminor : (toeplitz b).submatrix rows cols = submatrix (lacePair a b) rows' cols := by
    ext i j
    have hdiv : (2 * rows i + 1) / 2 = rows i := by
      lia
    simp [submatrix, rows', lacePair, hdiv]
  rw [hminor]
  exact h hrows' hcols

/-- Row map selecting, from the interleaved Veronese pair, the two rows
belonging to a fixed residue class `k`. -/
def veronesePairSectionRowMap (r k : ℕ) (row : ℕ) : ℕ :=
  2 * (k + r * (row / 2)) + row % 2

theorem strictMono_veronesePairSectionRowMap {r k : ℕ} (hr : 0 < r) :
    StrictMono (veronesePairSectionRowMap r k) := by
  intro m n hmn
  unfold veronesePairSectionRowMap
  by_cases hq : m / 2 = n / 2
  · rw [hq]
    gcongr
    lia
  · have hqle : m / 2 ≤ n / 2 := Nat.div_le_div_right (le_of_lt hmn)
    have hqlt : m / 2 < n / 2 := lt_of_le_of_ne hqle hq
    have hqsucc : m / 2 + 1 ≤ n / 2 := Nat.succ_le_of_lt hqlt
    have hmul : r * (m / 2 + 1) ≤ r * (n / 2) :=
      Nat.mul_le_mul_left r hqsucc
    lia

theorem lacePair_veroneseSectionSeq {a b : ℕ → ℝ} {r k row col : ℕ}
    (hk : k < r) :
    lacePair (veroneseSectionSeq r k a) (veroneseSectionSeq r k b) row col =
      veronesePairLace r a b (veronesePairSectionRowMap r k row) col := by
  unfold lacePair veronesePairSectionRowMap
  dsimp
  by_cases heven : row % 2 = 0
  · rw [if_pos heven]
    have hrowmap :
        2 * (k + r * (row / 2)) + row % 2 =
          2 * (k + r * (row / 2)) := by
      lia
    rw [hrowmap]
    exact (veronesePairLace_even (a := a) (b := b) (r := r) (k := k)
      (n := row / 2) (c := col) hk).symm
  · rw [if_neg heven]
    have hmod : row % 2 = 1 := by lia
    rw [hmod]
    exact (veronesePairLace_odd (a := a) (b := b) (r := r) (k := k)
      (n := row / 2) (c := col) hk).symm

/-- Fixed-residue heredity for the interleaved Veronese pair.  This is the
two-row TNN form of the "in particular" statement in Athanasiadis--Wagner
Corollary 5.6. -/
theorem VeronesePairFullyInterlacing.section {a b : ℕ → ℝ} {r k : ℕ}
    (h : VeronesePairFullyInterlacing r a b) (hr : 0 < r) (hk : k < r) :
    FullyInterlacingPair (veroneseSectionSeq r k a) (veroneseSectionSeq r k b) := by
  intro n rows cols hrows hcols
  let rows' : Fin n → ℕ := fun i => veronesePairSectionRowMap r k (rows i)
  have hrows' : StrictMono rows' := (strictMono_veronesePairSectionRowMap hr).comp hrows
  have hminor :
      submatrix (lacePair (veroneseSectionSeq r k a) (veroneseSectionSeq r k b)) rows cols =
        submatrix (veronesePairLace r a b) rows' cols := by
    ext i j
    simp [submatrix, rows', lacePair_veroneseSectionSeq hk]
  rw [hminor]
  exact h hrows' hcols

/-- Fixed-residue Veronese sections of a fully interlacing pair are again a
fully interlacing pair. -/
theorem fullyInterlacingPair_veroneseSectionPair {a b : ℕ → ℝ} {r k : ℕ}
    (h : FullyInterlacingPair a b) (hr : 0 < r) (hk : k < r) :
    FullyInterlacingPair (veroneseSectionSeq r k a) (veroneseSectionSeq r k b) :=
  VeronesePairFullyInterlacing.section (fullyInterlacingPair_veronesePair h hr) hr hk

/-- The `i`th entry in the interleaved Veronese sequence
`S_0 a, S_0 b, S_1 a, S_1 b, ...`. -/
def veronesePairSectionSeq (r : ℕ) (a b : ℕ → ℝ) (i : ℕ) : ℕ → ℝ :=
  if i % 2 = 0 then
    veroneseSectionSeq r (i / 2) a
  else
    veroneseSectionSeq r (i / 2) b

/-- Row selector which extracts two entries from the interleaved Veronese
sequence, preserving their internal Toeplitz row order. -/
def veronesePairSelectRowMap (r i j : ℕ) (row : ℕ) : ℕ :=
  if row % 2 = 0 then
    i + (2 * r) * (row / 2)
  else
    j + (2 * r) * (row / 2)

theorem div_two_lt_of_lt_two_mul {i r : ℕ} (hi : i < 2 * r) : i / 2 < r := by
  lia

theorem strictMono_veronesePairSelectRowMap {r i j : ℕ}
    (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    StrictMono (veronesePairSelectRowMap r i j) := by
  intro m n hmn
  unfold veronesePairSelectRowMap
  by_cases hq : m / 2 = n / 2
  · grind
  · have hqle : m / 2 ≤ n / 2 := Nat.div_le_div_right (le_of_lt hmn)
    have hqlt : m / 2 < n / 2 := lt_of_le_of_ne hqle hq
    have hqsucc : m / 2 + 1 ≤ n / 2 := Nat.succ_le_of_lt hqlt
    by_cases hm0 : m % 2 = 0
    · rw [if_pos hm0]
      by_cases hn0 : n % 2 = 0
      · simp_all
      · rw [if_neg hn0]
        have hblock : (2 * r) * (m / 2 + 1) ≤ (2 * r) * (n / 2) :=
          Nat.mul_le_mul_left (2 * r) hqsucc
        lia
    · rw [if_neg hm0]
      by_cases hn0 : n % 2 = 0
      · rw [if_pos hn0]
        have hblock : (2 * r) * (m / 2 + 1) ≤ (2 * r) * (n / 2) :=
          Nat.mul_le_mul_left (2 * r) hqsucc
        lia
      · simp_all

theorem lacePair_veronesePairSectionSeq {a b : ℕ → ℝ} {r i j row col : ℕ}
    (hi : i < 2 * r) (hj : j < 2 * r) :
    lacePair (veronesePairSectionSeq r a b i)
        (veronesePairSectionSeq r a b j) row col =
      veronesePairLace r a b (veronesePairSelectRowMap r i j row) col := by
  unfold lacePair veronesePairSectionSeq veronesePairSelectRowMap
  dsimp
  by_cases hrow : row % 2 = 0
  · rw [if_pos hrow]
    by_cases hi_even : i % 2 = 0
    · rw [if_pos hi_even]
      have hik : i / 2 < r := div_two_lt_of_lt_two_mul hi
      have hmap :
          i + (2 * r) * (row / 2) =
            2 * (i / 2 + r * (row / 2)) := by
        lia
      rw [if_pos hrow, hmap]
      exact (veronesePairLace_even (a := a) (b := b) (r := r)
        (k := i / 2) (n := row / 2) (c := col) hik).symm
    · rw [if_neg hi_even]
      have hik : i / 2 < r := div_two_lt_of_lt_two_mul hi
      have hmap :
          i + (2 * r) * (row / 2) =
            2 * (i / 2 + r * (row / 2)) + 1 := by
        lia
      rw [if_pos hrow, hmap]
      exact (veronesePairLace_odd (a := a) (b := b) (r := r)
        (k := i / 2) (n := row / 2) (c := col) hik).symm
  · rw [if_neg hrow]
    by_cases hj_even : j % 2 = 0
    · rw [if_pos hj_even]
      have hjk : j / 2 < r := div_two_lt_of_lt_two_mul hj
      have hmap :
          j + (2 * r) * (row / 2) =
            2 * (j / 2 + r * (row / 2)) := by
        lia
      rw [if_neg hrow, hmap]
      exact (veronesePairLace_even (a := a) (b := b) (r := r)
        (k := j / 2) (n := row / 2) (c := col) hjk).symm
    · rw [if_neg hj_even]
      have hjk : j / 2 < r := div_two_lt_of_lt_two_mul hj
      have hmap :
          j + (2 * r) * (row / 2) =
            2 * (j / 2 + r * (row / 2)) + 1 := by
        lia
      rw [if_neg hrow, hmap]
      exact (veronesePairLace_odd (a := a) (b := b) (r := r)
        (k := j / 2) (n := row / 2) (c := col) hjk).symm

/-- Any ordered pair of entries in the interleaved Veronese sequence is a
fully interlacing pair.  This is the coefficient-level pairwise form of
Athanasiadis--Wagner Corollary 5.6. -/
theorem VeronesePairFullyInterlacing.sectionPair {a b : ℕ → ℝ} {r i j : ℕ}
    (h : VeronesePairFullyInterlacing r a b) (hr : 0 < r)
    (hij : i < j) (hj : j < 2 * r) :
    FullyInterlacingPair (veronesePairSectionSeq r a b i)
      (veronesePairSectionSeq r a b j) := by
  intro n rows cols hrows hcols
  let rows' : Fin n → ℕ := fun row => veronesePairSelectRowMap r i j (rows row)
  have hi : i < 2 * r := lt_trans hij hj
  have hrows' : StrictMono rows' := (strictMono_veronesePairSelectRowMap hr hij hj).comp hrows
  have hminor :
      submatrix
          (lacePair (veronesePairSectionSeq r a b i)
            (veronesePairSectionSeq r a b j)) rows cols =
        submatrix (veronesePairLace r a b) rows' cols := by
    ext row col
    simp [submatrix, rows', lacePair_veronesePairSectionSeq hi hj]
  rw [hminor]
  exact h hrows' hcols

/-- Pairwise version of `fullyInterlacingPair_veronesePair`: starting from a
fully interlacing pair, any ordered pair in the interleaved Veronese sequence
is fully interlacing. -/
theorem fullyInterlacingPair_veroneseSectionPairwise {a b : ℕ → ℝ} {r i j : ℕ}
    (h : FullyInterlacingPair a b) (hr : 0 < r)
    (hij : i < j) (hj : j < 2 * r) :
    FullyInterlacingPair (veronesePairSectionSeq r a b i)
      (veronesePairSectionSeq r a b j) :=
  VeronesePairFullyInterlacing.sectionPair
    (fullyInterlacingPair_veronesePair h hr) hr hij hj

/-- Fin-indexed form of `VeronesePairFullyInterlacing.sectionPair`, avoiding
an explicit upper-bound hypothesis on the second index. -/
theorem VeronesePairFullyInterlacing.sectionPair_fin {a b : ℕ → ℝ} {r : ℕ}
    (h : VeronesePairFullyInterlacing r a b) (hr : 0 < r)
    (i j : Fin (2 * r)) (hij : i < j) :
    FullyInterlacingPair (veronesePairSectionSeq r a b i)
      (veronesePairSectionSeq r a b j) :=
  h.sectionPair hr hij j.isLt

/-- Fin-indexed pairwise Veronese theorem for a fully interlacing pair. -/
theorem fullyInterlacingPair_veroneseSectionPairwise_fin {a b : ℕ → ℝ}
    {r : ℕ} (h : FullyInterlacingPair a b) (hr : 0 < r)
    (i j : Fin (2 * r)) (hij : i < j) :
    FullyInterlacingPair (veronesePairSectionSeq r a b i)
      (veronesePairSectionSeq r a b j) :=
  fullyInterlacingPair_veroneseSectionPairwise h hr hij j.isLt

/-- The `i`th polynomial in the interleaved Veronese sequence
`S_0 p, S_0 q, S_1 p, S_1 q, ...`. -/
def veronesePairSectionPolynomial (r : ℕ) (p q : ℝ[X]) (i : ℕ) : ℝ[X] :=
  if i % 2 = 0 then
    veroneseSectionPolynomial r (i / 2) p
  else
    veroneseSectionPolynomial r (i / 2) q

@[simp] theorem coeff_veronesePairSectionPolynomial {r i n : ℕ} {p q : ℝ[X]}
    (hr : 0 < r) :
    (veronesePairSectionPolynomial r p q i).coeff n =
      veronesePairSectionSeq r (fun m => p.coeff m) (fun m => q.coeff m) i n := by
  unfold veronesePairSectionPolynomial veronesePairSectionSeq
  by_cases hi : i % 2 = 0
  · simp [hi, veroneseSectionSeq,
      coeff_veroneseSectionPolynomial (r := r) (k := i / 2) (p := p) hr]
  · simp [hi, veroneseSectionSeq,
      coeff_veroneseSectionPolynomial (r := r) (k := i / 2) (p := q) hr]

theorem coeff_function_veroneseSectionPolynomial {r k : ℕ} {p : ℝ[X]}
    (hr : 0 < r) : (veroneseSectionPolynomial r k p).coeff =
      veroneseSectionSeq r k p.coeff := by
  funext n
  simp [veroneseSectionSeq,
    coeff_veroneseSectionPolynomial (r := r) (k := k) (p := p) hr]

theorem coeff_function_veronesePairSectionPolynomial {r i : ℕ} {p q : ℝ[X]}
    (hr : 0 < r) :
    (fun n => (veronesePairSectionPolynomial r p q i).coeff n) =
      veronesePairSectionSeq r p.coeff (fun n => q.coeff n) i := by
  simp_all

theorem fullyInterlacingPair_veroneseSectionPolynomial_coeff
    {p q : ℝ[X]} {r k : ℕ}
    (hfull : FullyInterlacingPair p.coeff (fun n => q.coeff n))
    (hr : 0 < r) (hk : k < r) :
    FullyInterlacingPair (veroneseSectionPolynomial r k p).coeff
      (fun n => (veroneseSectionPolynomial r k q).coeff n) := by
  rw [coeff_function_veroneseSectionPolynomial (p := p) hr,
    coeff_function_veroneseSectionPolynomial (p := q) hr]
  exact fullyInterlacingPair_veroneseSectionPair hfull hr hk

theorem fullyInterlacingPair_veronesePairSectionPolynomial_coeff
    {p q : ℝ[X]} {r i j : ℕ}
    (hfull : FullyInterlacingPair p.coeff (fun n => q.coeff n))
    (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    FullyInterlacingPair
      (fun n => (veronesePairSectionPolynomial r p q i).coeff n)
      (fun n => (veronesePairSectionPolynomial r p q j).coeff n) := by
  rw [coeff_function_veronesePairSectionPolynomial (p := p) (q := q) (i := i) hr,
    coeff_function_veronesePairSectionPolynomial (p := p) (q := q) (i := j) hr]
  exact fullyInterlacingPair_veroneseSectionPairwise hfull hr hij hj

/-! ## Conditional bridge to polynomial interlacing -/

/-- Strong interface for the polynomial-to-lace direction.

This is stronger than the Athanasiadis--Wagner polynomial setting: plain
`Prec p q` does not include nonnegative coefficients or the AESW/PF condition.
For Veronese applications, prefer `PfPrecToFullyInterlacingPairStatement` or
`NonnegPrecToFullyInterlacingPairStatement` below. -/
def PrecToFullyInterlacingPairStatement : Prop :=
  ∀ {p q : ℝ[X]}, Prec p q →
    FullyInterlacingPair p.coeff (fun n => q.coeff n)

/-- Polynomial-to-lace interface in the AESW/Pólya-frequency regime used by
Athanasiadis--Wagner. -/
def PfPrecToFullyInterlacingPairStatement : Prop :=
  ∀ {p q : ℝ[X]},
    IsPolyaFreqSeq p.coeff →
    IsPolyaFreqSeq (fun n => q.coeff n) →
    Prec p q →
    FullyInterlacingPair p.coeff (fun n => q.coeff n)

/-- Polynomial-to-lace interface in the real-rooted, nonnegative-coefficient
regime.  The reverse ASW theorem reduces this to
`PfPrecToFullyInterlacingPairStatement`. -/
def NonnegPrecToFullyInterlacingPairStatement : Prop :=
  ∀ {p q : ℝ[X]},
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    Prec p q →
    FullyInterlacingPair p.coeff (fun n => q.coeff n)

/-- Hermite--Biehler/Hurwitz bridge target for producing the polynomial
`q(x^2) + x p(x^2)` from an AESW interlacing pair. -/
def PfPrecToHurwitzOddEvenStatement : Prop :=
  ∀ {p q : ℝ[X]},
    IsPolyaFreqSeq p.coeff →
    IsPolyaFreqSeq (fun n => q.coeff n) →
    Prec p q →
    IsHurwitzStable (oddEvenPolynomial p q)

/-- Nonnegative-coefficient version of the Hurwitz odd/even bridge.

This is the useful polynomial setting for the sign-normalized
Hermite--Biehler route: `Prec p q` already supplies nonzeroness, while
nonnegative coefficients supply positive leading coefficients. -/
def NonnegPrecToHurwitzOddEvenStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    Prec p q →
    IsHurwitzStable (oddEvenPolynomial p q)

/-- Hurwitz-to-Lace bridge target: total nonnegativity of the Hurwitz matrix of
`q(x^2) + x p(x^2)` should be exactly full interlacing of the two coefficient
rows. -/
def HurwitzOddEvenToFullyInterlacingPairStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    IsHurwitzStable (oddEvenPolynomial p q) →
    FullyInterlacingPair p.coeff (fun n => q.coeff n)

/-- Classical Hurwitz criterion interface in matrix form: Hurwitz stability
should imply total nonnegativity of the Hurwitz matrix. -/
def HurwitzStableToMatrixTotallyNonnegativeStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄, IsHurwitzStable p → (hurwitz p.coeff).IsTotallyNonneg

/-- The legacy strong interface implies the PF interface. -/
theorem pfPrecToFullyInterlacingPair_of_precToFully
    (h : PrecToFullyInterlacingPairStatement) :
    PfPrecToFullyInterlacingPairStatement :=
  fun {p q} _ _ hpq => h (p := p) (q := q) hpq

/-- The legacy strong interface implies the nonnegative-coefficient interface. -/
theorem nonnegPrecToFullyInterlacingPair_of_precToFully
    (h : PrecToFullyInterlacingPairStatement) :
    NonnegPrecToFullyInterlacingPairStatement :=
  fun {p q} _ _ hpq => h (p := p) (q := q) hpq

/-- Reverse ASW turns the PF bridge into the nonnegative-coefficient bridge,
because real-rooted polynomials with nonnegative coefficients have all roots
nonpositive. -/
theorem nonnegPrecToFullyInterlacingPair_of_pfPrec
    (hPfToFull : PfPrecToFullyInterlacingPairStatement) :
    NonnegPrecToFullyInterlacingPairStatement :=
  fun {_ _} hpnn hqnn hpq =>
    hPfToFull
    (aissenSchoenbergWhitney_reverse hpnn hpq.1.2 (roots_nonpos_of_nonneg_coeffs hpq.1.2 hpnn))
    (aissenSchoenbergWhitney_reverse hqnn hpq.2.1.2 (roots_nonpos_of_nonneg_coeffs hpq.2.1.2 hqnn))
    hpq

/-- Positive-leading-coefficient form used when zero coefficients are ruled out
explicitly. -/
theorem pfPrecToHurwitzOddEven_of_hermiteBiehlerPosCoeffs
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement) :
    ∀ {p q : ℝ[X]},
      HasNonnegCoeffs p →
      HasNonnegCoeffs q →
      p ≠ 0 →
      q ≠ 0 →
      Prec p q →
      IsHurwitzStable (oddEvenPolynomial p q) := by
  intro p q hpnn hqnn hp0 hq0 hpq
  have hp : HasPosLeadingCoeff p :=
    hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hpnn hp0
  have hq : HasPosLeadingCoeff q :=
    hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hqnn hq0
  refine ⟨hasNonnegCoeffs_oddEvenPolynomial hpnn hqnn, ?_⟩
  exact hHBToHurwitz hpnn hqnn (hHB (f := q) (g := p) hq hp hpq)

/-- Sign-normalized Hermite--Biehler gives the nonnegative-coefficient
Hurwitz odd/even bridge. -/
theorem nonnegPrecToHurwitzOddEven_of_hermiteBiehlerPos
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement) :
    NonnegPrecToHurwitzOddEvenStatement :=
  fun {_ _} hpnn hqnn hpq =>
    pfPrecToHurwitzOddEven_of_hermiteBiehlerPosCoeffs hHB hHBToHurwitz
      hpnn hqnn hpq.1.1 hpq.2.1.1 hpq

/-- Sign-normalized Hermite--Biehler also gives the PF/AESW Hurwitz odd/even
bridge, since PF coefficients are nonnegative. -/
theorem pfPrecToHurwitzOddEven_of_hermiteBiehlerPos
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement) :
    PfPrecToHurwitzOddEvenStatement :=
  fun {_ _} hppf hqpf =>
    nonnegPrecToHurwitzOddEven_of_hermiteBiehlerPos hHB hHBToHurwitz hppf.nonneg hqpf.nonneg

/-- The planned Hermite--Biehler/Hurwitz route implies the PF polynomial-to-Lace
bridge. -/
theorem pfPrecToFullyInterlacingPair_of_hurwitzOddEven
    (hPrecToHurwitz : PfPrecToHurwitzOddEvenStatement)
    (hHurwitzToFull : HurwitzOddEvenToFullyInterlacingPairStatement) :
    PfPrecToFullyInterlacingPairStatement :=
  fun {_ _} hppf hqpf hpq => hHurwitzToFull (hPrecToHurwitz hppf hqpf hpq)

/-- The nonnegative-coefficient Hurwitz odd/even bridge implies the
nonnegative-coefficient polynomial-to-Lace bridge. -/
theorem nonnegPrecToFullyInterlacingPair_of_hurwitzOddEvenDirect
    (hPrecToHurwitz : NonnegPrecToHurwitzOddEvenStatement)
    (hHurwitzToFull : HurwitzOddEvenToFullyInterlacingPairStatement) :
    NonnegPrecToFullyInterlacingPairStatement :=
  fun {_ _} hpnn hqnn hpq => hHurwitzToFull (hPrecToHurwitz hpnn hqnn hpq)

/-- The matrix form of the Hurwitz criterion gives the Hurwitz-to-Lace bridge
for odd/even polynomials by the explicit matrix identity above. -/
theorem hurwitzOddEvenToFullyInterlacingPair_of_matrixTNN
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    HurwitzOddEvenToFullyInterlacingPairStatement :=
  fun {p q} hhur =>
    (hurwitzMatrixTotallyNonnegative_oddEvenPolynomial_iff_fullyInterlacingPair p q).1
    (hHurwitzToMatrix hhur)

/-- Hermite--Biehler/Hurwitz plus the matrix Hurwitz criterion imply the PF
polynomial-to-Lace bridge. -/
theorem pfPrecToFullyInterlacingPair_of_hurwitzMatrix
    (hPrecToHurwitz : PfPrecToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    PfPrecToFullyInterlacingPairStatement :=
  pfPrecToFullyInterlacingPair_of_hurwitzOddEven hPrecToHurwitz
    (hurwitzOddEvenToFullyInterlacingPair_of_matrixTNN hHurwitzToMatrix)

/-- Matrix Hurwitz criterion version of the nonnegative-coefficient
polynomial-to-Lace bridge. -/
theorem nonnegPrecToFullyInterlacingPair_of_hurwitzMatrixDirect
    (hPrecToHurwitz : NonnegPrecToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    NonnegPrecToFullyInterlacingPairStatement :=
  nonnegPrecToFullyInterlacingPair_of_hurwitzOddEvenDirect hPrecToHurwitz
    (hurwitzOddEvenToFullyInterlacingPair_of_matrixTNN hHurwitzToMatrix)

/-- Sign-normalized Hermite--Biehler route to the PF polynomial-to-Lace
bridge. -/
theorem pfPrecToFullyInterlacingPair_of_hermiteBiehlerPosHurwitzMatrix
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    PfPrecToFullyInterlacingPairStatement :=
  pfPrecToFullyInterlacingPair_of_hurwitzMatrix
    (pfPrecToHurwitzOddEven_of_hermiteBiehlerPos hHB hHBToHurwitz)
    hHurwitzToMatrix

/-- Combining reverse ASW with the Hermite--Biehler/Hurwitz route gives the
nonnegative-coefficient polynomial-to-Lace bridge. -/
theorem nonnegPrecToFullyInterlacingPair_of_hurwitzOddEven
    (hPrecToHurwitz : PfPrecToHurwitzOddEvenStatement)
    (hHurwitzToFull : HurwitzOddEvenToFullyInterlacingPairStatement) :
    NonnegPrecToFullyInterlacingPairStatement :=
  nonnegPrecToFullyInterlacingPair_of_pfPrec
    (pfPrecToFullyInterlacingPair_of_hurwitzOddEven hPrecToHurwitz hHurwitzToFull)

/-- Nonnegative-coefficient version using the matrix Hurwitz criterion. -/
theorem nonnegPrecToFullyInterlacingPair_of_hurwitzMatrix
    (hPrecToHurwitz : PfPrecToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    NonnegPrecToFullyInterlacingPairStatement :=
  nonnegPrecToFullyInterlacingPair_of_pfPrec
    (pfPrecToFullyInterlacingPair_of_hurwitzMatrix hPrecToHurwitz hHurwitzToMatrix)

/-- Sign-normalized Hermite--Biehler route to the nonnegative-coefficient
polynomial-to-Lace bridge.  No reverse ASW hypothesis is needed here because
the theorem assumes nonnegative coefficients directly. -/
theorem nonnegPrecToFullyInterlacingPair_of_hermiteBiehlerPosHurwitzMatrix
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    NonnegPrecToFullyInterlacingPairStatement :=
  nonnegPrecToFullyInterlacingPair_of_hurwitzMatrixDirect
    (nonnegPrecToHurwitzOddEven_of_hermiteBiehlerPos hHB hHBToHurwitz)
    hHurwitzToMatrix

/-- Zero-aware interface from the two-row Lace condition back to polynomial
interlacing.  This is the conservative target, since a Veronese section may be
the zero polynomial. -/
def FullyInterlacingPairToPrec0Statement : Prop :=
  ∀ {p q : ℝ[X]},
    FullyInterlacingPair p.coeff (fun n => q.coeff n) → Prec0 p q

/-- Strict interface from the two-row Lace condition back to polynomial
interlacing.  This is useful in nondegenerate applications where the relevant
sections are known to be nonzero. -/
def FullyInterlacingPairToPrecStatement : Prop :=
  ∀ {p q : ℝ[X]},
    FullyInterlacingPair p.coeff (fun n => q.coeff n) → Prec p q

/-- Interlacing-extraction interface for the converse lace-to-polynomial
bridge.  Given two nonzero polynomials whose coefficient sequences form a
fully interlacing pair, the two-row Lace total-nonnegativity certificate should
produce sorted root lists witnessing the proper-position root configuration of
`Prec`.

This isolates the genuinely combinatorial heart of the converse direction:
total nonnegativity of the cross `2 × 2` Lace minors forces the roots of the
two polynomials to interlace.  Real-rootedness itself, the `Splits` part of
`Prec`, is supplied separately by the forward Aissen--Schoenberg--Whitney
theorem, so this statement only asks for the interlacing data. -/
def FullyInterlacingPairInterlaceStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄, p ≠ 0 → q ≠ 0 →
    FullyInterlacingPair p.coeff (fun n => q.coeff n) →
    ∃ ss rs : List ℝ,
      ss.Pairwise (· ≤ ·) ∧ rs.Pairwise (· ≤ ·) ∧
      (↑ss : Multiset ℝ) = p.roots ∧ (↑rs : Multiset ℝ) = q.roots ∧
        ((ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
          (ss.length = rs.length ∧ ListAlternates ss rs))

/-- Checked reduction for the converse lace-to-interlacing bridge.

The zero-aware target `FullyInterlacingPairToPrec0Statement` follows from two
classical inputs:

* the forward Aissen--Schoenberg--Whitney theorem
  `aissenSchoenbergWhitneyForwardStatement`, which turns the two
  Pólya-frequency coefficient rows (`FullyInterlacingPair.left_pf` and
  `FullyInterlacingPair.right_pf`) into real-rootedness of each polynomial; and
* the interlacing-extraction interface `FullyInterlacingPairInterlaceStatement`,
  which supplies the proper-position root data from the cross Lace minors.

The zero polynomial cases are discharged directly by `prec0_zero_left` and
`prec0_zero_right`. -/
theorem fullyInterlacingPairToPrec0_of_forwardASW_interlace
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    FullyInterlacingPairToPrec0Statement := by
  intro p q hfull
  rcases eq_or_ne p 0 with rfl | hp0
  · exact prec0_zero_left q
  rcases eq_or_ne q 0 with rfl | hq0
  · exact prec0_zero_right p
  refine Or.inr (Or.inr ?_)
  have hp_pf : IsPolyaFreqSeq p.coeff := hfull.left_pf
  have hq_pf : IsPolyaFreqSeq (fun n => q.coeff n) := hfull.right_pf
  obtain ⟨hp_split, _⟩ := hASW hp_pf
  obtain ⟨hq_split, _⟩ := hASW hq_pf
  obtain ⟨ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩ := hInt hp0 hq0 hfull
  exact ⟨⟨hp0, hp_split⟩, ⟨hq0, hq_split⟩, ss, rs, hss, hrs,
    hss_eq, hrs_eq, hshape⟩

/-- Converse Hurwitz-matrix interface specialized to the odd/even polynomial.

This is the orientation of the classical total-nonnegativity criterion needed
for the converse Lace bridge: total nonnegativity of the two-row Lace matrix of
`p` and `q`, equivalently of the Hurwitz matrix of `q(x^2) + x p(x^2)`, forces
Hurwitz stability of `q(x^2) + x p(x^2)`. It is the exact converse of the
forward interface `HurwitzOddEvenToFullyInterlacingPairStatement` and follows
from the matrix Hurwitz criterion
`HurwitzMatrixTotallyNonnegativeToStableStatement` via
`hurwitzMatrixTotallyNonnegative_oddEvenPolynomial_iff_fullyInterlacingPair`. -/
def FullyInterlacingPairToHurwitzOddEvenStableStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    FullyInterlacingPair p.coeff (fun n => q.coeff n) →
    IsHurwitzStable (oddEvenPolynomial p q)

/-- Analytic converse interface (converse Hermite--Biehler / Hurwitz step).

Hurwitz stability of the odd/even polynomial `q(x^2) + x p(x^2)` of two nonzero
polynomials forces proper position `Prec p q`. This isolates the genuinely
analytic heart of the converse direction: once the two-row Lace certificate has
been turned into Hurwitz stability of `q(x^2) + x p(x^2)`, the roots of `p` and
`q` interlace in the `p ≪ q` orientation. Real-rootedness (`Splits`) is part of
`Prec`, so it is supplied here as well. -/
def HurwitzStableOddEvenToPrecStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄, p ≠ 0 → q ≠ 0 →
    IsHurwitzStable (oddEvenPolynomial p q) → Prec p q

/-- Converse analytic substitution interface (converse of
`HermiteBiehlerStableToHurwitzOddEvenStatement`).

Right-half-plane stability of the odd/even polynomial `q(x^2) + x p(x^2)`
forces upper-half-plane stability of the Hermite--Biehler combination
`q + i p`.  This is the exact reverse of the classical conformal-substitution
bridge `HermiteBiehlerStableToHurwitzOddEvenStatement`, recovering the
Hermite--Biehler factor from the Hurwitz factor by inverting the quadratic
substitution `z ↦ z^2`. -/
def HurwitzOddEvenToHermiteBiehlerStableStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q)) →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)

/-- The conformal rotation `z ↦ i * z` maps the open right half-plane onto the
open upper half-plane.

Consequently, a complex polynomial `P` is upper-half-plane stable exactly when
its rotation `P(i * z)`, implemented by substituting `X ↦ C Complex.I * X`, is
right-half-plane stable.  This elementary equivalence isolates the remaining
analytic content of the converse Hurwitz/Hermite--Biehler bridge below. -/
theorem isUpperHalfPlaneStable_iff_isRightHalfPlaneStable_comp (P : ℂ[X]) :
    IsUpperHalfPlaneStable P ↔
      IsRightHalfPlaneStable (P.comp (C Complex.I * X)) := by
  constructor
  · intro h z hz
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    exact h (Complex.I * z) (by simpa [Complex.mul_im] using hz)
  · intro h w hw
    have key : P.eval w = (P.comp (C Complex.I * X)).eval (-Complex.I * w) := by
      rw [Polynomial.eval_comp]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring_nf
      simp [Complex.I_sq]
    rw [key]
    exact h (-Complex.I * w) (by simpa [Complex.mul_re] using hw)

/-- Minimal conformal-substitution interface for the converse Hurwitz/
Hermite--Biehler bridge.

This is the remaining analytic input after the elementary half-plane rotation:
right-half-plane stability of the odd/even Hurwitz polynomial `q(x^2)+x p(x^2)`
forces right-half-plane stability of the rotated Hermite--Biehler combination
`(q + i p)(i * z)`. -/
def HurwitzOddEvenToHermiteBiehlerRotatedStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    IsRightHalfPlaneStable (complexify (oddEvenPolynomial p q)) →
    IsRightHalfPlaneStable
      ((hermiteBiehlerPolynomial q p).comp (C Complex.I * X))

/-- Checked reduction of the converse analytic-substitution interface to the
rotated right-half-plane version. -/
theorem hurwitzOddEvenToHermiteBiehlerStable_of_rotated
    (hRot : HurwitzOddEvenToHermiteBiehlerRotatedStatement) :
    HurwitzOddEvenToHermiteBiehlerStableStatement := by
  intro p q hp hq hrhp
  rw [isUpperHalfPlaneStable_iff_isRightHalfPlaneStable_comp]
  exact hRot hp hq hrhp

/-- Oriented converse Hermite--Biehler interface (oriented converse of
`hermiteBiehlerForwardPosStatement`).

For polynomials `f`, `g` with positive leading coefficients, upper-half-plane
stability of the combination `f + i g` forces the oriented proper position
`Prec g f`.  This is strictly stronger than the disjunctive
`hermiteBiehlerConverseStatement` already recorded in
`RealRooted.HermiteBiehler`: it commits to the orientation matching the forward
bridge `hermiteBiehlerForwardPosStatement`, where `Prec g f` produces
upper-half-plane stability of `f + i g`. -/
def HermiteBiehlerConverseOrientedStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) →
    Prec g f

/-- Orientation-selection interface for the converse Hermite--Biehler theorem.

The disjunctive converse `hermiteBiehlerConverseStatement` in
`RealRooted.HermiteBiehler` only concludes `Prec g f ∨ Prec f g`, leaving the
orientation open.  This interface records the single remaining analytic fact
needed to commit to the orientation matching the forward bridge
`hermiteBiehlerForwardPosStatement`: for `f`, `g` with positive leading
coefficients, upper-half-plane stability of `f + i g` excludes the reversed
proper position, so the reversed branch `Prec f g` can only occur together with
the oriented one `Prec g f`. -/
def HermiteBiehlerOrientationStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) →
    Prec f g → Prec g f

/-- Checked reduction of the oriented converse Hermite--Biehler interface.

`HermiteBiehlerConverseOrientedStatement` follows from the disjunctive converse
Hermite--Biehler theorem `hermiteBiehlerConverseStatement` together with the
orientation-selection input `HermiteBiehlerOrientationStatement`.  The
disjunctive converse supplies `Prec g f ∨ Prec f g` from positive leading
coefficients and upper-half-plane stability; the orientation input selects the
oriented branch. -/
theorem hermiteBiehlerConverseOriented_of_orientation
    (hConv : hermiteBiehlerConverseStatement)
    (hOrient : HermiteBiehlerOrientationStatement) :
    HermiteBiehlerConverseOrientedStatement :=
  fun _ _ hf hg hstable => (hConv hf hg hstable).elim id (hOrient hf hg hstable)

/-- Checked reduction of the analytic converse step
`HurwitzStableOddEvenToPrecStatement`.

The analytic converse Hermite--Biehler/Hurwitz step factors through the
Hermite--Biehler combination `q + i p`, via two named, strictly smaller
classical inputs, each a converse of a forward interface already present in the
project:

* `HurwitzOddEvenToHermiteBiehlerStableStatement`, the converse analytic
  substitution, which turns right-half-plane stability of `q(x^2) + x p(x^2)`
  into upper-half-plane stability of `q + i p`; and
* `HermiteBiehlerConverseOrientedStatement`, the oriented converse
  Hermite--Biehler theorem, which turns that upper-half-plane stability into the
  proper-position relation `Prec p q`.

The nonnegativity halves of `IsHurwitzStable` supply the positive leading
coefficients needed by the oriented Hermite--Biehler input through
`hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero`. -/
theorem hurwitzStableOddEvenToPrec_of_converse
    (hSub : HurwitzOddEvenToHermiteBiehlerStableStatement)
    (hHB : HermiteBiehlerConverseOrientedStatement) :
    HurwitzStableOddEvenToPrecStatement := by
  intro p q hp hq hstable
  obtain ⟨hnn, hrhp⟩ := hstable
  have hpnn : HasNonnegCoeffs p := hasNonnegCoeffs_left_of_oddEvenPolynomial hnn
  have hqnn : HasNonnegCoeffs q := hasNonnegCoeffs_right_of_oddEvenPolynomial hnn
  have hupper : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) :=
    hSub hpnn hqnn hrhp
  have hqpos : HasPosLeadingCoeff q :=
    hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hqnn hq
  have hppos : HasPosLeadingCoeff p :=
    hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hpnn hp
  exact hHB hqpos hppos hupper

/-! ## Degree-based orientation of the converse Hermite--Biehler step

The oriented converse Hermite--Biehler interface
`HermiteBiehlerConverseOrientedStatement` (and hence the analytic step
`HurwitzStableOddEvenToPrecStatement`) is only genuinely analytic in the
*equal-degree* regime.  Once the two factors have strictly ordered degrees, the
orientation is forced by the elementary degree constraint carried by `Prec`, so
the orientation-selection input is unnecessary and the *disjunctive* converse
`hermiteBiehlerConverseStatement` already suffices.

This isolates exactly where the orientation analytic content is needed: it is
used only when the two polynomials have equal degree (equivalently, for the
odd/even polynomial, only when its degree is odd). -/

/-- The proper-position relation respects degree: `Prec f g` forces
`f.natDegree ≤ g.natDegree`.  Both interlacing shapes (`differ-by-1` and
`same-degree`) only increase the length of the right-hand root list. -/
theorem Prec.natDegree_le {f g : ℝ[X]} (h : Prec f g) :
    f.natDegree ≤ g.natDegree := by
  obtain ⟨⟨_, hfs⟩, ⟨_, hgs⟩, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩ := h
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hfs]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hgs]
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩ <;> lia

/-- Elementary orientation resolution by degree.  A disjunctive proper-position
conclusion `Prec g f ∨ Prec f g` collapses to the oriented branch `Prec g f`
as soon as the degrees are strictly ordered `g.natDegree < f.natDegree`, since
the reversed branch `Prec f g` would force `f.natDegree ≤ g.natDegree`. -/
theorem prec_of_or_of_natDegree_lt {f g : ℝ[X]}
    (h : Prec g f ∨ Prec f g) (hgf : g.natDegree < f.natDegree) : Prec g f :=
  h.elim id fun h => absurd h.natDegree_le (by lia)

/-- Degree-restricted oriented converse Hermite--Biehler step, *without* any
orientation-selection input.

For `f, g` with positive leading coefficients and strictly ordered degrees
`g.natDegree < f.natDegree`, upper-half-plane stability of `f + i g` forces the
oriented proper position `Prec g f`, using only the disjunctive converse
`hermiteBiehlerConverseStatement`.  This is the part of
`HermiteBiehlerConverseOrientedStatement` that needs no extra analytic
orientation fact: the orientation is pinned by the degree gap.  The remaining,
genuinely analytic, orientation content of the oriented converse is therefore
confined to the equal-degree case. -/
theorem hermiteBiehlerConverseOriented_of_natDegree_lt
    (hConv : hermiteBiehlerConverseStatement) {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : g.natDegree < f.natDegree)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    Prec g f :=
  prec_of_or_of_natDegree_lt (hConv hf hg hstable) hdeg

/-- Strict-degree case of the analytic converse step
`HurwitzStableOddEvenToPrecStatement`, *without* the oriented converse interface.

When `p.natDegree < q.natDegree` (equivalently, when `oddEvenPolynomial p q` has
even degree, see
`natDegree_lt_iff_even_natDegree_oddEvenPolynomial`), Hurwitz stability of
`q(x²) + x p(x²)` forces `Prec p q` using only the converse substitution
interface `HurwitzOddEvenToHermiteBiehlerStableStatement` and the *disjunctive*
converse Hermite--Biehler theorem `hermiteBiehlerConverseStatement`.  No
orientation-selection input (`HermiteBiehlerOrientationStatement` /
`HermiteBiehlerConverseOrientedStatement`) is needed: the orientation is forced
by the degree gap.

This sharpens `hurwitzStableOddEvenToPrec_of_converse`, which in general also
needs the oriented converse, by showing the orientation input is dispensable in
the strict-degree (even-degree) regime; only the equal-degree (odd-degree)
regime retains genuinely analytic orientation content. -/
theorem hurwitzStableOddEvenToPrec_of_converse_natDegree_lt
    (hSub : HurwitzOddEvenToHermiteBiehlerStableStatement)
    (hConv : hermiteBiehlerConverseStatement)
    {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hdeg : p.natDegree < q.natDegree)
    (hstable : IsHurwitzStable (oddEvenPolynomial p q)) : Prec p q := by
  obtain ⟨hnn, hrhp⟩ := hstable
  have hpnn := hasNonnegCoeffs_left_of_oddEvenPolynomial hnn
  have hqnn := hasNonnegCoeffs_right_of_oddEvenPolynomial hnn
  have hupper := hSub hpnn hqnn hrhp
  have hqpos := hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hqnn hq
  have hppos := hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hpnn hp
  exact hermiteBiehlerConverseOriented_of_natDegree_lt hConv hqpos hppos hdeg hupper

/-! ### Degree of the odd/even polynomial -/

/-- Composition with `X²` is nonzero-preserving. -/
theorem comp_X_sq_ne_zero {p : ℝ[X]} (hp : p ≠ 0) :
    p.comp (X ^ 2 : ℝ[X]) ≠ 0 := by
  rw [Ne, Polynomial.comp_eq_zero_iff]
  rintro (h | ⟨_, hc⟩)
  · exact hp h
  · have hd :
      (X ^ 2 : ℝ[X]).natDegree = (C ((X ^ 2 : ℝ[X]).coeff 0)).natDegree := by
      rw [← hc]
    simp at hd

/-- The Veronese substitution `X ↦ X²` doubles the degree. -/
theorem natDegree_comp_X_sq (q : ℝ[X]) :
    (q.comp (X ^ 2 : ℝ[X])).natDegree = 2 * q.natDegree := by
  rw [Polynomial.natDegree_comp]; simp; ring

/-- Degree of the odd part `x · p(x²)`. -/
theorem natDegree_X_mul_comp_X_sq {p : ℝ[X]} (hp : p ≠ 0) :
    (X * p.comp (X ^ 2 : ℝ[X])).natDegree = 2 * p.natDegree + 1 := by
  rw [Polynomial.natDegree_mul (by simp) (comp_X_sq_ne_zero hp), Polynomial.natDegree_X,
    natDegree_comp_X_sq]
  ring

/-- Degree of the odd/even polynomial `q(x²) + x p(x²)`.

The even part `q(x²)` has degree `2·deg q` and the odd part `x p(x²)` has degree
`2·deg p + 1`; these have opposite parity, so there is never any leading
cancellation and the degree is their maximum. -/
theorem natDegree_oddEvenPolynomial {p q : ℝ[X]} (hp : p ≠ 0) :
    (oddEvenPolynomial p q).natDegree =
      max (2 * q.natDegree) (2 * p.natDegree + 1) := by
  have ha : (q.comp (X ^ 2 : ℝ[X])).natDegree = 2 * q.natDegree :=
    natDegree_comp_X_sq q
  have hb : (X * p.comp (X ^ 2 : ℝ[X])).natDegree = 2 * p.natDegree + 1 :=
    natDegree_X_mul_comp_X_sq hp
  unfold oddEvenPolynomial
  rcases lt_trichotomy (2 * q.natDegree) (2 * p.natDegree + 1) with h | h | h
  · rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt (by rw [ha, hb]; exact h), hb,
      max_eq_right (by lia)]
  · exfalso
    lia
  · rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt (by rw [ha, hb]; exact h), ha,
      max_eq_left (by lia)]

/-- The strict-degree hypothesis used in
`hurwitzStableOddEvenToPrec_of_converse_natDegree_lt` is exactly the statement
that the odd/even polynomial has *even* degree: for `p ≠ 0`,
`p.natDegree < q.natDegree ↔ Even (oddEvenPolynomial p q).natDegree`.

Thus the orientation-free reduction covers precisely the even-degree case, and
the genuinely analytic orientation content of the converse Hermite--Biehler step
is confined to the odd-degree (equal-degree) case. -/
theorem natDegree_lt_iff_even_natDegree_oddEvenPolynomial {p q : ℝ[X]}
    (hp : p ≠ 0) :
    p.natDegree < q.natDegree ↔ Even (oddEvenPolynomial p q).natDegree := by
  rw [natDegree_oddEvenPolynomial hp]
  constructor
  · intro h
    rw [max_eq_left (by lia)]
    exact ⟨q.natDegree, by ring⟩
  · intro h
    by_contra hcon
    have hle := Nat.not_lt.mp hcon
    rw [max_eq_right (by lia)] at h
    rcases h with ⟨k, hk⟩
    lia

/-- Existence of a right-half-plane square root.

Any complex number with strictly positive imaginary part has a square root lying
in the open right half-plane.  This is the elementary fact powering the
degenerate (`p = 0` or `q = 0`) cases of the converse conformal substitution. -/
theorem exists_rightHalfPlane_sqrt_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    ∃ z : ℂ, 0 < z.re ∧ z ^ 2 = w := by
  obtain ⟨z₀, hz₀⟩ : ∃ z : ℂ, z ^ 2 = w := by
    obtain ⟨z, hz⟩ := Complex.exists_root (f := X ^ 2 - C w)
      (by rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num)
    have hz' : z ^ 2 - w = 0 := by
      simpa [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C] using hz
    exact ⟨z, sub_eq_zero.mp hz'⟩
  have hre : z₀.re ≠ 0 := by
    intro h0
    have him : (z₀ ^ 2).im = 0 := by simp [pow_two, Complex.mul_im, h0]
    rw [hz₀] at him
    linarith
  rcases lt_or_gt_of_ne hre with h | h
  · refine ⟨-z₀, ?_, ?_⟩
    · simp only [Complex.neg_re]
      linarith
    · rw [neg_sq]
      exact hz₀
  · exact ⟨z₀, h, hz₀⟩

/-- Degenerate (`p = 0`) case of the converse conformal substitution. -/
theorem isUpperHalfPlaneStable_hermiteBiehler_of_rhp_left_zero
    {q : ℝ[X]}
    (hrhp : IsRightHalfPlaneStable (complexify (oddEvenPolynomial 0 q))) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q 0) := by
  intro z hz
  obtain ⟨w, hwre, hwsq⟩ := exists_rightHalfPlane_sqrt_of_im_pos hz
  have hc0 : complexify (0 : ℝ[X]) = 0 := by simp [complexify]
  have h := hrhp w hwre
  rw [eval_complexify_oddEvenPolynomial, hc0] at h
  simp only [Polynomial.eval_zero, mul_zero, add_zero] at h
  rw [hwsq] at h
  rw [eval_hermiteBiehlerPolynomial, hc0]
  simpa using h

/-- Degenerate (`q = 0`) case of the converse conformal substitution. -/
theorem isUpperHalfPlaneStable_hermiteBiehler_of_rhp_right_zero
    {p : ℝ[X]}
    (hrhp : IsRightHalfPlaneStable (complexify (oddEvenPolynomial p 0))) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial 0 p) := by
  intro z hz
  obtain ⟨w, hwre, hwsq⟩ := exists_rightHalfPlane_sqrt_of_im_pos hz
  have hc0 : complexify (0 : ℝ[X]) = 0 := by simp [complexify]
  have h := hrhp w hwre
  rw [eval_complexify_oddEvenPolynomial, hc0] at h
  simp only [Polynomial.eval_zero, zero_add] at h
  rw [hwsq] at h
  rw [eval_hermiteBiehlerPolynomial, hc0]
  simp only [Polynomial.eval_zero, zero_add]
  have hp : (complexify p).eval z ≠ 0 := by
    intro h0
    apply h
    rw [h0, mul_zero]
  exact mul_ne_zero Complex.I_ne_zero hp

/-- Checked reduction of the rotated converse conformal-substitution interface.

`HurwitzOddEvenToHermiteBiehlerRotatedStatement` follows from the real-variable
converse Hurwitz/Hermite--Biehler interlacing step
`HurwitzStableOddEvenToPrecStatement` together with the established forward
Hermite--Biehler bridge `hermiteBiehlerForwardPosStatement`. -/
theorem hurwitzOddEvenToHermiteBiehlerRotated_of_hurwitzStablePrec
    (hPrec : HurwitzStableOddEvenToPrecStatement)
    (hFwd : hermiteBiehlerForwardPosStatement) :
    HurwitzOddEvenToHermiteBiehlerRotatedStatement := by
  intro p q hp hq hrhp
  rw [← isUpperHalfPlaneStable_iff_isRightHalfPlaneStable_comp]
  by_cases hp0 : p = 0
  · subst hp0
    exact isUpperHalfPlaneStable_hermiteBiehler_of_rhp_left_zero hrhp
  · by_cases hq0 : q = 0
    · subst hq0
      exact isUpperHalfPlaneStable_hermiteBiehler_of_rhp_right_zero hrhp
    · have hO : IsHurwitzStable (oddEvenPolynomial p q) :=
        ⟨hasNonnegCoeffs_oddEvenPolynomial hp hq, hrhp⟩
      have hprec : Prec p q := hPrec hp0 hq0 hO
      have hqpos : HasPosLeadingCoeff q :=
        hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hq hq0
      have hppos : HasPosLeadingCoeff p :=
        hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero hp hp0
      exact hFwd hqpos hppos hprec

/-- Checked reduction of the interlacing-extraction interface.

`FullyInterlacingPairInterlaceStatement` follows from two named, strictly
smaller classical inputs, both natural converses of forward interfaces already
in the project:

* `FullyInterlacingPairToHurwitzOddEvenStableStatement`, the converse Hurwitz
  matrix criterion specialized to the odd/even polynomial, which turns the
  two-row Lace total-nonnegativity certificate into Hurwitz stability of
  `q(x^2) + x p(x^2)`; and
* `HurwitzStableOddEvenToPrecStatement`, the analytic converse
  Hermite--Biehler/Hurwitz step, which turns that Hurwitz stability into the
  proper-position relation `Prec p q`.

The interlacing list data demanded by `FullyInterlacingPairInterlaceStatement`
is then read off directly from the `Prec p q` witness. -/
theorem fullyInterlacingPairInterlace_of_oddEvenStableToPrec
    (hStable : FullyInterlacingPairToHurwitzOddEvenStableStatement)
    (hPrec : HurwitzStableOddEvenToPrecStatement) :
    FullyInterlacingPairInterlaceStatement := by
  intro p q hp hq hfull
  have hstable : IsHurwitzStable (oddEvenPolynomial p q) := hStable hfull
  obtain ⟨_, _, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩ := hPrec hp hq hstable
  exact ⟨ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩

/-- Once a two-row Lace certificate is available, fixed Veronese sections
preserve polynomial interlacing in the zero-aware sense, assuming the
lace-to-polynomial bridge. -/
theorem prec0_veroneseSectionPolynomial_of_fullyInterlacingPair
    {p q : ℝ[X]} {r k : ℕ}
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hfull : FullyInterlacingPair p.coeff (fun n => q.coeff n))
    (hr : 0 < r) (hk : k < r) :
    Prec0 (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) :=
  hFullToPrec0 (fullyInterlacingPair_veroneseSectionPolynomial_coeff hfull hr hk)

/-- Strict version of
`prec0_veroneseSectionPolynomial_of_fullyInterlacingPair`. -/
theorem prec_veroneseSectionPolynomial_of_fullyInterlacingPair
    {p q : ℝ[X]} {r k : ℕ}
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hfull : FullyInterlacingPair p.coeff (fun n => q.coeff n))
    (hr : 0 < r) (hk : k < r) :
    Prec (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) :=
  hFullToPrec (fullyInterlacingPair_veroneseSectionPolynomial_coeff hfull hr hk)

/-- Lace-certificate version of the pairwise Veronese polynomial theorem. -/
theorem prec0_veronesePairSectionPolynomial_of_fullyInterlacingPair
    {p q : ℝ[X]} {r i j : ℕ}
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hfull : FullyInterlacingPair p.coeff (fun n => q.coeff n))
    (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    Prec0 (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  hFullToPrec0
    (fullyInterlacingPair_veronesePairSectionPolynomial_coeff hfull hr hij hj)

/-- Strict lace-certificate version of the pairwise Veronese polynomial
theorem. -/
theorem prec_veronesePairSectionPolynomial_of_fullyInterlacingPair
    {p q : ℝ[X]} {r i j : ℕ}
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hfull : FullyInterlacingPair p.coeff (fun n => q.coeff n))
    (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    Prec (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  hFullToPrec
    (fullyInterlacingPair_veronesePairSectionPolynomial_coeff hfull hr hij hj)

/-- Fin-indexed zero-aware lace-certificate version. -/
theorem prec0_veronesePairSectionPolynomial_fin_of_fullyInterlacingPair
    {p q : ℝ[X]} {r : ℕ}
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hfull : FullyInterlacingPair p.coeff (fun n => q.coeff n))
    (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec0 (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec0_veronesePairSectionPolynomial_of_fullyInterlacingPair
    (p := p) (q := q) (r := r) (i := i) (j := j)
    hFullToPrec0 hfull hr hij j.isLt

/-- Fin-indexed strict lace-certificate version. -/
theorem prec_veronesePairSectionPolynomial_fin_of_fullyInterlacingPair
    {p q : ℝ[X]} {r : ℕ}
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hfull : FullyInterlacingPair p.coeff (fun n => q.coeff n))
    (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec_veronesePairSectionPolynomial_of_fullyInterlacingPair
    (p := p) (q := q) (r := r) (i := i) (j := j)
    hFullToPrec hfull hr hij j.isLt

/-- PF/AESW version of the fixed-section Veronese interlacing theorem. -/
theorem prec0_veroneseSectionPolynomial_of_pf_prec {p q : ℝ[X]} {r k : ℕ}
    (hPfToFull : PfPrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hppf : IsPolyaFreqSeq p.coeff)
    (hqpf : IsPolyaFreqSeq (fun n => q.coeff n))
    (hpq : Prec p q) (hr : 0 < r) (hk : k < r) :
    Prec0 (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) :=
  prec0_veroneseSectionPolynomial_of_fullyInterlacingPair
    hFullToPrec0 (hPfToFull hppf hqpf hpq) hr hk

/-- Strict PF/AESW version of the fixed-section Veronese interlacing theorem. -/
theorem prec_veroneseSectionPolynomial_of_pf_prec {p q : ℝ[X]} {r k : ℕ}
    (hPfToFull : PfPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hppf : IsPolyaFreqSeq p.coeff)
    (hqpf : IsPolyaFreqSeq (fun n => q.coeff n))
    (hpq : Prec p q) (hr : 0 < r) (hk : k < r) :
    Prec (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) :=
  prec_veroneseSectionPolynomial_of_fullyInterlacingPair
    hFullToPrec (hPfToFull hppf hqpf hpq) hr hk

/-- Nonnegative-coefficient version of the fixed-section Veronese interlacing
theorem, using the corrected polynomial-to-lace interface. -/
theorem prec0_veroneseSectionPolynomial_of_nonneg_prec {p q : ℝ[X]} {r k : ℕ}
    (hNonnegToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpq : Prec p q) (hr : 0 < r) (hk : k < r) :
    Prec0 (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) :=
  prec0_veroneseSectionPolynomial_of_fullyInterlacingPair
    hFullToPrec0 (hNonnegToFull hpnn hqnn hpq) hr hk

/-- Strict nonnegative-coefficient version of the fixed-section Veronese
interlacing theorem. -/
theorem prec_veroneseSectionPolynomial_of_nonneg_prec {p q : ℝ[X]} {r k : ℕ}
    (hNonnegToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpq : Prec p q) (hr : 0 < r) (hk : k < r) :
    Prec (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) :=
  prec_veroneseSectionPolynomial_of_fullyInterlacingPair
    hFullToPrec (hNonnegToFull hpnn hqnn hpq) hr hk

/-- PF/AESW pairwise Veronese interlacing theorem. -/
theorem prec0_veronesePairSectionPolynomial_of_pf_prec
    {p q : ℝ[X]} {r i j : ℕ}
    (hPfToFull : PfPrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hppf : IsPolyaFreqSeq p.coeff)
    (hqpf : IsPolyaFreqSeq (fun n => q.coeff n))
    (hpq : Prec p q) (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    Prec0 (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec0_veronesePairSectionPolynomial_of_fullyInterlacingPair
    hFullToPrec0 (hPfToFull hppf hqpf hpq) hr hij hj

/-- Strict PF/AESW pairwise Veronese interlacing theorem. -/
theorem prec_veronesePairSectionPolynomial_of_pf_prec
    {p q : ℝ[X]} {r i j : ℕ}
    (hPfToFull : PfPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hppf : IsPolyaFreqSeq p.coeff)
    (hqpf : IsPolyaFreqSeq (fun n => q.coeff n))
    (hpq : Prec p q) (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    Prec (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec_veronesePairSectionPolynomial_of_fullyInterlacingPair
    hFullToPrec (hPfToFull hppf hqpf hpq) hr hij hj

/-- Nonnegative-coefficient pairwise Veronese interlacing theorem. -/
theorem prec0_veronesePairSectionPolynomial_of_nonneg_prec
    {p q : ℝ[X]} {r i j : ℕ}
    (hNonnegToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpq : Prec p q) (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    Prec0 (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec0_veronesePairSectionPolynomial_of_fullyInterlacingPair
    hFullToPrec0 (hNonnegToFull hpnn hqnn hpq) hr hij hj

/-- Strict nonnegative-coefficient pairwise Veronese interlacing theorem. -/
theorem prec_veronesePairSectionPolynomial_of_nonneg_prec
    {p q : ℝ[X]} {r i j : ℕ}
    (hNonnegToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpq : Prec p q) (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    Prec (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec_veronesePairSectionPolynomial_of_fullyInterlacingPair
    hFullToPrec (hNonnegToFull hpnn hqnn hpq) hr hij hj

/-- Fin-indexed PF/AESW pairwise Veronese interlacing theorem. -/
theorem prec0_veronesePairSectionPolynomial_fin_of_pf_prec
    {p q : ℝ[X]} {r : ℕ}
    (hPfToFull : PfPrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hppf : IsPolyaFreqSeq p.coeff)
    (hqpf : IsPolyaFreqSeq (fun n => q.coeff n))
    (hpq : Prec p q) (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec0 (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec0_veronesePairSectionPolynomial_fin_of_fullyInterlacingPair
    hFullToPrec0 (hPfToFull hppf hqpf hpq) hr i j hij

/-- Strict Fin-indexed PF/AESW pairwise Veronese interlacing theorem. -/
theorem prec_veronesePairSectionPolynomial_fin_of_pf_prec
    {p q : ℝ[X]} {r : ℕ}
    (hPfToFull : PfPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hppf : IsPolyaFreqSeq p.coeff)
    (hqpf : IsPolyaFreqSeq (fun n => q.coeff n))
    (hpq : Prec p q) (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec_veronesePairSectionPolynomial_fin_of_fullyInterlacingPair
    hFullToPrec (hPfToFull hppf hqpf hpq) hr i j hij

/-- Fin-indexed nonnegative-coefficient pairwise Veronese interlacing
theorem. -/
theorem prec0_veronesePairSectionPolynomial_fin_of_nonneg_prec
    {p q : ℝ[X]} {r : ℕ}
    (hNonnegToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpq : Prec p q) (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec0 (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec0_veronesePairSectionPolynomial_fin_of_fullyInterlacingPair
    hFullToPrec0 (hNonnegToFull hpnn hqnn hpq) hr i j hij

/-- Strict Fin-indexed nonnegative-coefficient pairwise Veronese interlacing
theorem. -/
theorem prec_veronesePairSectionPolynomial_fin_of_nonneg_prec
    {p q : ℝ[X]} {r : ℕ}
    (hNonnegToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpq : Prec p q) (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec_veronesePairSectionPolynomial_fin_of_fullyInterlacingPair
    hFullToPrec (hNonnegToFull hpnn hqnn hpq) hr i j hij

/-! ### Veronese wrappers from the sign-normalized Hermite--Biehler/Hurwitz route -/

/-- Sign-normalized PF/AESW fixed-section Veronese interlacing through the
Hermite--Biehler/Hurwitz matrix route. -/
theorem prec0_veroneseSectionPolynomial_of_hermiteBiehlerPosHurwitzMatrix
    {p q : ℝ[X]} {r k : ℕ}
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hppf : IsPolyaFreqSeq p.coeff)
    (hqpf : IsPolyaFreqSeq (fun n => q.coeff n))
    (hpq : Prec p q) (hr : 0 < r) (hk : k < r) :
    Prec0 (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) :=
  prec0_veroneseSectionPolynomial_of_pf_prec
    (pfPrecToFullyInterlacingPair_of_hermiteBiehlerPosHurwitzMatrix
      hHB hHBToHurwitz hHurwitzToMatrix)
    hFullToPrec0 hppf hqpf hpq hr hk

/-- Strict sign-normalized PF/AESW fixed-section Veronese interlacing through
the Hermite--Biehler/Hurwitz matrix route. -/
theorem prec_veroneseSectionPolynomial_of_hermiteBiehlerPosHurwitzMatrix
    {p q : ℝ[X]} {r k : ℕ}
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hppf : IsPolyaFreqSeq p.coeff)
    (hqpf : IsPolyaFreqSeq (fun n => q.coeff n))
    (hpq : Prec p q) (hr : 0 < r) (hk : k < r) :
    Prec (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) :=
  prec_veroneseSectionPolynomial_of_pf_prec
    (pfPrecToFullyInterlacingPair_of_hermiteBiehlerPosHurwitzMatrix
      hHB hHBToHurwitz hHurwitzToMatrix)
    hFullToPrec hppf hqpf hpq hr hk

/-- Sign-normalized Fin-indexed PF/AESW pairwise Veronese interlacing through
the Hermite--Biehler/Hurwitz matrix route. -/
theorem prec0_veronesePairSectionPolynomial_fin_of_hermiteBiehlerPosHurwitzMatrix
    {p q : ℝ[X]} {r : ℕ}
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hppf : IsPolyaFreqSeq p.coeff)
    (hqpf : IsPolyaFreqSeq (fun n => q.coeff n))
    (hpq : Prec p q) (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec0 (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec0_veronesePairSectionPolynomial_fin_of_pf_prec
    (pfPrecToFullyInterlacingPair_of_hermiteBiehlerPosHurwitzMatrix
      hHB hHBToHurwitz hHurwitzToMatrix)
    hFullToPrec0 hppf hqpf hpq hr i j hij

/-- Strict sign-normalized Fin-indexed PF/AESW pairwise Veronese interlacing
through the Hermite--Biehler/Hurwitz matrix route. -/
theorem prec_veronesePairSectionPolynomial_fin_of_hermiteBiehlerPosHurwitzMatrix
    {p q : ℝ[X]} {r : ℕ}
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hppf : IsPolyaFreqSeq p.coeff)
    (hqpf : IsPolyaFreqSeq (fun n => q.coeff n))
    (hpq : Prec p q) (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec_veronesePairSectionPolynomial_fin_of_pf_prec
    (pfPrecToFullyInterlacingPair_of_hermiteBiehlerPosHurwitzMatrix
      hHB hHBToHurwitz hHurwitzToMatrix)
    hFullToPrec hppf hqpf hpq hr i j hij

/-- Sign-normalized nonnegative-coefficient fixed-section Veronese
interlacing through the Hermite--Biehler/Hurwitz matrix route. -/
theorem prec0_veroneseSectionPolynomial_of_nonneg_hermiteBiehlerPosHurwitzMatrix
    {p q : ℝ[X]} {r k : ℕ}
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpq : Prec p q) (hr : 0 < r) (hk : k < r) :
    Prec0 (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) :=
  prec0_veroneseSectionPolynomial_of_nonneg_prec
    (nonnegPrecToFullyInterlacingPair_of_hermiteBiehlerPosHurwitzMatrix
      hHB hHBToHurwitz hHurwitzToMatrix)
    hFullToPrec0 hpnn hqnn hpq hr hk

/-- Strict sign-normalized nonnegative-coefficient fixed-section Veronese
interlacing through the Hermite--Biehler/Hurwitz matrix route. -/
theorem prec_veroneseSectionPolynomial_of_nonneg_hermiteBiehlerPosHurwitzMatrix
    {p q : ℝ[X]} {r k : ℕ}
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpq : Prec p q) (hr : 0 < r) (hk : k < r) :
    Prec (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) :=
  prec_veroneseSectionPolynomial_of_nonneg_prec
    (nonnegPrecToFullyInterlacingPair_of_hermiteBiehlerPosHurwitzMatrix
      hHB hHBToHurwitz hHurwitzToMatrix)
    hFullToPrec hpnn hqnn hpq hr hk

/-- Sign-normalized Fin-indexed nonnegative-coefficient pairwise Veronese
interlacing through the Hermite--Biehler/Hurwitz matrix route. -/
theorem
    prec0_veronesePairSectionPolynomial_fin_of_nonneg_hermiteBiehlerPosHurwitzMatrix
    {p q : ℝ[X]} {r : ℕ}
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpq : Prec p q) (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec0 (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec0_veronesePairSectionPolynomial_fin_of_nonneg_prec
    (nonnegPrecToFullyInterlacingPair_of_hermiteBiehlerPosHurwitzMatrix
      hHB hHBToHurwitz hHurwitzToMatrix)
    hFullToPrec0 hpnn hqnn hpq hr i j hij

/-- Strict sign-normalized Fin-indexed nonnegative-coefficient pairwise
Veronese interlacing through the Hermite--Biehler/Hurwitz matrix route. -/
theorem
    prec_veronesePairSectionPolynomial_fin_of_nonneg_hermiteBiehlerPosHurwitzMatrix
    {p q : ℝ[X]} {r : ℕ}
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpq : Prec p q) (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec_veronesePairSectionPolynomial_fin_of_nonneg_prec
    (nonnegPrecToFullyInterlacingPair_of_hermiteBiehlerPosHurwitzMatrix
      hHB hHBToHurwitz hHurwitzToMatrix)
    hFullToPrec hpnn hqnn hpq hr i j hij

/-- Conditional polynomial version of Athanasiadis--Wagner Corollary 5.6:
assuming the bridge between classical polynomial interlacing and the two-row
Lace condition, fixed Veronese sections preserve interlacing in the zero-aware
`Prec0` sense. -/
theorem prec0_veroneseSectionPolynomial_of_prec {p q : ℝ[X]} {r k : ℕ}
    (hPrecToFull : PrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpq : Prec p q) (hr : 0 < r) (hk : k < r) :
    Prec0 (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) :=
  prec0_veroneseSectionPolynomial_of_fullyInterlacingPair
    hFullToPrec0 (hPrecToFull hpq) hr hk

/-- Strict version of `prec0_veroneseSectionPolynomial_of_prec`, for
applications where the two-row Lace condition is known to imply the strict
local `Prec` relation. -/
theorem prec_veroneseSectionPolynomial_of_prec {p q : ℝ[X]} {r k : ℕ}
    (hPrecToFull : PrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : Prec p q) (hr : 0 < r) (hk : k < r) :
    Prec (veroneseSectionPolynomial r k p) (veroneseSectionPolynomial r k q) :=
  prec_veroneseSectionPolynomial_of_fullyInterlacingPair
    hFullToPrec (hPrecToFull hpq) hr hk

/-- Conditional polynomial version of the pairwise form of
Athanasiadis--Wagner Corollary 5.6.  Among the interleaved sequence
`S_0 p, S_0 q, S_1 p, S_1 q, ...`, every ordered pair is interlacing in the
zero-aware `Prec0` sense, assuming the `Prec`/Lace bridge interfaces. -/
theorem prec0_veronesePairSectionPolynomial_of_prec {p q : ℝ[X]} {r i j : ℕ}
    (hPrecToFull : PrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpq : Prec p q) (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    Prec0 (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec0_veronesePairSectionPolynomial_of_fullyInterlacingPair
    hFullToPrec0 (hPrecToFull hpq) hr hij hj

/-- Strict version of `prec0_veronesePairSectionPolynomial_of_prec`, for
nondegenerate applications where the Lace condition is known to imply the
strict local `Prec` relation. -/
theorem prec_veronesePairSectionPolynomial_of_prec {p q : ℝ[X]} {r i j : ℕ}
    (hPrecToFull : PrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : Prec p q) (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    Prec (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec_veronesePairSectionPolynomial_of_fullyInterlacingPair
    hFullToPrec (hPrecToFull hpq) hr hij hj

/-- Fin-indexed version of
`prec0_veronesePairSectionPolynomial_of_prec`.  This states the pairwise
interlacing property for any two ordered entries of the `2*r`-term interleaved
Veronese sequence. -/
theorem prec0_veronesePairSectionPolynomial_fin_of_prec {p q : ℝ[X]} {r : ℕ}
    (hPrecToFull : PrecToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement)
    (hpq : Prec p q) (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec0 (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec0_veronesePairSectionPolynomial_of_prec
    (p := p) (q := q) (r := r) (i := i) (j := j)
    hPrecToFull hFullToPrec0 hpq hr hij j.isLt

/-- Strict Fin-indexed version of
`prec_veronesePairSectionPolynomial_of_prec`. -/
theorem prec_veronesePairSectionPolynomial_fin_of_prec {p q : ℝ[X]} {r : ℕ}
    (hPrecToFull : PrecToFullyInterlacingPairStatement)
    (hFullToPrec : FullyInterlacingPairToPrecStatement)
    (hpq : Prec p q) (hr : 0 < r) (i j : Fin (2 * r)) (hij : i < j) :
    Prec (veronesePairSectionPolynomial r p q i)
      (veronesePairSectionPolynomial r p q j) :=
  prec_veronesePairSectionPolynomial_of_prec
    (p := p) (q := q) (r := r) (i := i) (j := j)
    hPrecToFull hFullToPrec hpq hr hij j.isLt

/-- Veronese subsequences preserve Toeplitz total nonnegativity.

The hypothesis `k < r` is essential for the Toeplitz submatrix identification:
it makes `cols j ≤ rows i` equivalent to
`r * cols j ≤ k + r * rows i`. -/
protected theorem IsPolyaFreqSeq.veroneseSectionSeq {a : ℕ → ℝ}
    (ha : IsPolyaFreqSeq a) {r k : ℕ} (hr : 0 < r) (hk : k < r) :
    IsPolyaFreqSeq (veroneseSectionSeq r k a) := by
  intro n rows cols hrows hcols
  let rows' : Fin n → ℕ := fun i => k + r * rows i
  let cols' : Fin n → ℕ := fun i => r * cols i
  have hrows' : StrictMono rows' :=
    fun _ _ hij => Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left (hrows hij) hr) k
  have hcols' : StrictMono cols' :=
    fun _ _ hij => Nat.mul_lt_mul_of_pos_left (hcols hij) hr
  have hminor : (toeplitz (veroneseSectionSeq r k a)).submatrix rows cols =
      (toeplitz a).submatrix rows' cols' := by
    ext i j
    dsimp [toeplitz, veroneseSectionSeq, rows', cols']
    by_cases hle : cols j ≤ rows i
    · have hle' : r * cols j ≤ k + r * rows i :=
        Nat.le_trans (Nat.mul_le_mul_left r hle) (Nat.le_add_left (r * rows i) k)
      rw [if_pos hle, if_pos hle']
      congr 1
      calc
        k + r * (rows i - cols j) =
            k + (r * rows i - r * cols j) := by
          rw [Nat.mul_sub_left_distrib]
        _ = k + r * rows i - r * cols j :=
          (Nat.add_sub_assoc (Nat.mul_le_mul_left r hle) k).symm
    · have hlt : rows i < cols j := Nat.lt_of_not_ge hle
      have hnot : ¬ r * cols j ≤ k + r * rows i := by
        have hsucc : rows i + 1 ≤ cols j := Nat.succ_le_of_lt hlt
        have hmul : r * (rows i + 1) ≤ r * cols j :=
          Nat.mul_le_mul_left r hsucc
        lia
      lia
  rw [hminor]
  exact ha hrows' hcols'

theorem IsPolyaFreqSeq_veroneseSectionPolynomial_coeff {p : ℝ[X]}
    (hp : IsPolyaFreqSeq p.coeff) {r k : ℕ}
    (hr : 0 < r) (hk : k < r) :
    IsPolyaFreqSeq (veroneseSectionPolynomial r k p).coeff := by
  have hseq : IsPolyaFreqSeq (veroneseSectionSeq r k p.coeff) := hp.veroneseSectionSeq hr hk
  rw [show (veroneseSectionPolynomial r k p).coeff = veroneseSectionSeq r k p.coeff by
    funext n
    simp [veroneseSectionSeq,
      coeff_veroneseSectionPolynomial (r := r) (k := k) (p := p) hr]]
  exact hseq

/-- Conditional real-rootedness of Veronese sections from the forward ASW
theorem and a PF certificate for the original polynomial. -/
theorem splits_veroneseSectionPolynomial_of_pf {p : ℝ[X]}
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hp : IsPolyaFreqSeq p.coeff) {r k : ℕ}
    (hr : 0 < r) (hk : k < r) :
    veroneseSectionPolynomial r k p = 0 ∨
      (veroneseSectionPolynomial r k p).Splits := by
  have hpf : IsPolyaFreqSeq (veroneseSectionPolynomial r k p).coeff :=
    IsPolyaFreqSeq_veroneseSectionPolynomial_coeff (p := p) hp hr hk
  exact Or.inr (hASW hpf).1

/-- Zero-aware real-rootedness of Veronese sections from the forward ASW
theorem and a PF certificate for the original polynomial. -/
theorem veroneseSectionPolynomial_eq_zero_or_isRealRooted_of_pf {p : ℝ[X]}
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hp : IsPolyaFreqSeq (fun n => p.coeff n)) {r k : ℕ}
    (hr : 0 < r) (hk : k < r) :
    veroneseSectionPolynomial r k p = 0 ∨
      (veroneseSectionPolynomial r k p).Splits :=
  splits_veroneseSectionPolynomial_of_pf hASW hp hr hk

/-- Conditional PF preservation for Veronese sections of real-rooted
nonnegative-coefficient polynomials, using the reverse ASW theorem. -/
theorem IsPolyaFreqSeq_veroneseSectionPolynomial_of_realRooted_nonneg
    {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hprr : p.Splits) {r k : ℕ}
    (hr : 0 < r) (hk : k < r) :
    IsPolyaFreqSeq (veroneseSectionPolynomial r k p).coeff := by
  have hpf : IsPolyaFreqSeq p.coeff :=
    aissenSchoenbergWhitney_reverse hpnn hprr (roots_nonpos_of_nonneg_coeffs hprr hpnn)
  exact IsPolyaFreqSeq_veroneseSectionPolynomial_coeff (p := p) hpf hr hk

/-- Conditional real-rootedness of Veronese sections of real-rooted
nonnegative-coefficient polynomials, assuming both directions of ASW. -/
theorem splits_veroneseSectionPolynomial_of_splits_nonneg {p : ℝ[X]}
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hpnn : HasNonnegCoeffs p) (hprr : p.Splits) {r k : ℕ}
    (hr : 0 < r) (hk : k < r) :
    veroneseSectionPolynomial r k p = 0 ∨
      (veroneseSectionPolynomial r k p).Splits := by
  have hpf : IsPolyaFreqSeq (veroneseSectionPolynomial r k p).coeff :=
    IsPolyaFreqSeq_veroneseSectionPolynomial_of_realRooted_nonneg hpnn hprr hr hk
  exact Or.inr (hASW hpf).1

/-- Zero-aware real-rootedness of Veronese sections of real-rooted
nonnegative-coefficient polynomials, assuming both directions of ASW. -/
theorem veroneseSectionPolynomial_eq_zero_or_isRealRooted_of_realRooted_nonneg
    {p : ℝ[X]}
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hpnn : HasNonnegCoeffs p) (hprr_splits : p.Splits) {r k : ℕ}
    (hr : 0 < r) (hk : k < r) :
    veroneseSectionPolynomial r k p = 0 ∨
      (veroneseSectionPolynomial r k p).Splits :=
  splits_veroneseSectionPolynomial_of_splits_nonneg
    hASW hpnn hprr_splits hr hk

end RealRooted
