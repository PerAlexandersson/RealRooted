import RealRooted.AissenSchoenbergWhitney
import RealRooted.HermiteBiehler
import RealRooted.WagnerX
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Veronese sections

This file formalizes the Veronese-section results of Athanasiadis--Wagner.

* Coefficient level: `IsPolyaFreqSeq.veroneseSectionSeq` shows that Veronese
  subsequences preserve the Pólya-frequency property, by identifying each
  Toeplitz minor of a section with a Toeplitz minor of the original sequence.
* Polynomial level: `isPolyaFreqSeq_veroneseSectionPolynomial_coeff` lifts this
  to coefficient sequences.  With both directions of Aissen--Schoenberg--Whitney,
  `splits_veroneseSectionPolynomial_of_splits_nonneg` proves that every Veronese
  section of a real-rooted polynomial with nonnegative coefficients is zero or
  real-rooted, with no further hypotheses.
* Two-row Lace matrices: `FullyInterlacingPair` is preserved by single and
  paired Veronese sections (`fullyInterlacingPair_veroneseSectionPair`,
  `fullyInterlacingPair_veroneseSectionPairwise`).  For odd/even polynomials,
  Hurwitz total nonnegativity is exactly `FullyInterlacingPair`.
* Refuted orientation: `not_nonnegStrictInterl_fullyInterlacingPair` and
  `not_isHurwitzStable_oddEven_fullyInterlacingPair` show that the current row
  orientation of the polynomial-to-Lace direction fails.
* Odd/even Hermite--Biehler: the forward direction
  `isHurwitzStable_oddEvenPolynomial_of_strictInterl` is proved.  The converse
  `strictInterl_of_isHurwitzStable_oddEvenPolynomial` still takes the unproved
  targets `HurwitzOddEvenToHermiteBiehlerStableStatement` and
  `HermiteBiehlerConverseOrientedStatement` (issue #1112) as hypotheses.  In
  the strict-degree case,
  `strictInterl_of_isHurwitzStable_oddEvenPolynomial_of_natDegree_lt` needs
  only the first of them.

`RealRooted.VeroneseMatrix` gives a second, matrix-based proof of the
real-rootedness consequence.
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
      ⟨Finsupp.onFinset (Finset.range (p.natDegree + 1))
        (fun n => p.coeff (k + r * n))
        (by
          intro n hn
          have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
          by_contra hmem
          have hnotlt : ¬ n < p.natDegree + 1 := by simp_all
          have hle : p.natDegree + 1 ≤ n := Nat.le_of_not_gt hnotlt
          have hpn : p.natDegree < n := Nat.lt_of_succ_le hle
          have hn_le_mul : n ≤ r * n := by
            simpa [one_mul] using
              Nat.mul_le_mul_right n (Nat.succ_le_of_lt hrpos)
          have hn_le : n ≤ k + r * n :=
            Nat.le_trans hn_le_mul (Nat.le_add_left (r * n) k)
          exact hn <|
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hpn hn_le))⟩

@[simp] theorem coeff_veroneseSectionPolynomial {r k n : ℕ} {p : ℝ[X]}
    (hr : 0 < r) :
    (veroneseSectionPolynomial r k p).coeff n = p.coeff (k + r * n) := by
  simp [veroneseSectionPolynomial, Nat.ne_of_gt hr]

theorem hasNonnegCoeffs_veroneseSectionPolynomial {r k : ℕ} {p : ℝ[X]}
    (hr : 0 < r) (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (veroneseSectionPolynomial r k p) :=
  fun n => by
    simpa [coeff_veroneseSectionPolynomial (r := r) (k := k) (p := p) hr] using
      hp (k + r * n)

theorem veroneseSectionPolynomial_ne_zero_of_coeff_ne_zero
    {r k n : ℕ} {p : ℝ[X]} (hr : 0 < r)
    (hcoeff : p.coeff (k + r * n) ≠ 0) :
    veroneseSectionPolynomial r k p ≠ 0 :=
  fun hzero => hcoeff <| by
    simpa [coeff_veroneseSectionPolynomial (r := r) (k := k) (p := p) hr] using
      congrArg (fun q : ℝ[X] => q.coeff n) hzero

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
  rw [coeff_veroneseSectionPolynomial (r := r) (k := k + 1) (p := X * p) hr,
    show k + 1 + r * n = (k + r * n) + 1 by lia]
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
      have hidx : 0 + r * (n + 1) = (r - 1 + r * n) + 1 := by lia
      simp_all

/-- The zeroth Veronese section after multiplying by a linear factor
`X + a`.  This is the wrap-around update used in Wagner-style proofs of
Veronese real-rootedness. -/
theorem veroneseSectionPolynomial_X_add_C_mul_zero {r : ℕ} (hr : 0 < r)
    (a : ℝ) (p : ℝ[X]) :
    veroneseSectionPolynomial r 0 ((X + C a) * p) =
      X * veroneseSectionPolynomial r (r - 1) p +
        C a * veroneseSectionPolynomial r 0 p := by
  have hmul : (X + C a) * p = X * p + C a * p := by ring
  rw [hmul, veroneseSectionPolynomial_add hr, veroneseSectionPolynomial_X_mul_zero hr,
    veroneseSectionPolynomial_C_mul hr]

/-- Positive-residue Veronese sections after multiplying by a linear factor
`X + a`. -/
theorem veroneseSectionPolynomial_X_add_C_mul_succ {r k : ℕ}
    (hk : k + 1 < r) (a : ℝ) (p : ℝ[X]) :
    veroneseSectionPolynomial r (k + 1) ((X + C a) * p) =
      veroneseSectionPolynomial r k p +
        C a * veroneseSectionPolynomial r (k + 1) p := by
  have hr : 0 < r := by lia
  have hmul : (X + C a) * p = X * p + C a * p := by ring
  rw [hmul, veroneseSectionPolynomial_add hr, veroneseSectionPolynomial_X_mul_succ hk,
    veroneseSectionPolynomial_C_mul hr]

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
      lacePair p.coeff q.coeff row col := by
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
  rw [ite_eq_left hmod, hdiv]
  dsimp [toeplitz, veroneseSectionSeq]
  by_cases hc : c ≤ n
  · have hc' : r * c ≤ k + r * n :=
      Nat.le_trans (Nat.mul_le_mul_left r hc) (Nat.le_add_left (r * n) k)
    rw [ite_eq_left hc, ite_eq_left hc']
    congr 1
    calc
      k + r * n - r * c = k + (r * n - r * c) :=
        Nat.add_sub_assoc (Nat.mul_le_mul_left r hc) k
      _ = k + r * (n - c) := by rw [← Nat.mul_sub_left_distrib]
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
  have hmod_ne : ¬ (2 * (k + r * n) + 1) % 2 = 0 := by lia
  have hdiv : (2 * (k + r * n) + 1) / 2 = k + r * n := by lia
  dsimp [veronesePairLace, lacePair]
  rw [ite_eq_right hmod_ne, hdiv]
  dsimp [toeplitz, veroneseSectionSeq]
  by_cases hc : c ≤ n
  · have hc' : r * c ≤ k + r * n :=
      Nat.le_trans (Nat.mul_le_mul_left r hc) (Nat.le_add_left (r * n) k)
    rw [ite_eq_left hc, ite_eq_left hc']
    congr 1
    calc
      k + r * n - r * c = k + (r * n - r * c) :=
        Nat.add_sub_assoc (Nat.mul_le_mul_left r hc) k
      _ = k + r * (n - c) := by rw [← Nat.mul_sub_left_distrib]
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
    IsPolyaFreqSeq a := fun n rows cols hrows hcols => by
  let rows' : Fin n → ℕ := fun i => 2 * rows i
  have hrows' : StrictMono rows' :=
    fun _ _ hij => Nat.mul_lt_mul_of_pos_left (hrows hij) (by lia)
  have hminor : (toeplitz a).submatrix rows cols = submatrix (lacePair a b) rows' cols := by
    ext i j
    simp [submatrix, rows', lacePair]
  simpa [hminor] using h hrows' hcols

/-- The second row family of a fully interlacing pair is a Pólya-frequency
sequence. -/
theorem FullyInterlacingPair.right_pf {a b : ℕ → ℝ} (h : FullyInterlacingPair a b) :
    IsPolyaFreqSeq b := fun n rows cols hrows hcols => by
  let rows' : Fin n → ℕ := fun i => 2 * rows i + 1
  have hrows' : StrictMono rows' :=
    fun _ _ hij => Nat.add_lt_add_right
      (Nat.mul_lt_mul_of_pos_left (hrows hij) (by lia)) 1
  have hminor : (toeplitz b).submatrix rows cols = submatrix (lacePair a b) rows' cols := by
    ext i j
    have hdiv : (2 * rows i + 1) / 2 = rows i := by lia
    simp [submatrix, rows', lacePair, hdiv]
  simpa [hminor] using h hrows' hcols

/-- Row map selecting, from the interleaved Veronese pair, the two rows
belonging to a fixed residue class `k`. -/
def veronesePairSectionRowMap (r k : ℕ) (row : ℕ) : ℕ :=
  2 * (k + r * (row / 2)) + row % 2

theorem strictMono_veronesePairSectionRowMap {r k : ℕ} (hr : 0 < r) :
    StrictMono (veronesePairSectionRowMap r k) := fun m n hmn => by
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
  · rw [ite_eq_left heven]
    have hrowmap :
        2 * (k + r * (row / 2)) + row % 2 =
          2 * (k + r * (row / 2)) := by
      lia
    simpa [hrowmap] using
      (veronesePairLace_even (a := a) (b := b) (r := r) (k := k)
      (n := row / 2) (c := col) hk).symm
  · rw [ite_eq_right heven]
    have hmod : row % 2 = 1 := by lia
    simpa [hmod] using
      (veronesePairLace_odd (a := a) (b := b) (r := r) (k := k)
      (n := row / 2) (c := col) hk).symm

/-- Fixed-residue heredity for the interleaved Veronese pair.  This is the
two-row TNN form of the "in particular" statement in Athanasiadis--Wagner
Corollary 5.6. -/
theorem VeronesePairFullyInterlacing.section {a b : ℕ → ℝ} {r k : ℕ}
    (h : VeronesePairFullyInterlacing r a b) (hr : 0 < r) (hk : k < r) :
    FullyInterlacingPair (veroneseSectionSeq r k a) (veroneseSectionSeq r k b) :=
  fun n rows cols hrows hcols => by
  let rows' : Fin n → ℕ := fun i => veronesePairSectionRowMap r k (rows i)
  have hrows' : StrictMono rows' := (strictMono_veronesePairSectionRowMap hr).comp hrows
  have hminor :
      submatrix (lacePair (veroneseSectionSeq r k a) (veroneseSectionSeq r k b)) rows cols =
        submatrix (veronesePairLace r a b) rows' cols := by
    ext i j
    simp [submatrix, rows', lacePair_veroneseSectionSeq hk]
  simpa [hminor] using h hrows' hcols

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

theorem div_two_lt_of_lt_two_mul {i r : ℕ} (hi : i < 2 * r) : i / 2 < r := by lia

theorem strictMono_veronesePairSelectRowMap {r i j : ℕ}
    (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    StrictMono (veronesePairSelectRowMap r i j) := fun m n hmn => by
  unfold veronesePairSelectRowMap
  by_cases hq : m / 2 = n / 2
  · grind
  · have hqle : m / 2 ≤ n / 2 := Nat.div_le_div_right (le_of_lt hmn)
    have hqlt : m / 2 < n / 2 := lt_of_le_of_ne hqle hq
    have hqsucc : m / 2 + 1 ≤ n / 2 := Nat.succ_le_of_lt hqlt
    have hblock : (2 * r) * (m / 2 + 1) ≤ (2 * r) * (n / 2) :=
      Nat.mul_le_mul_left (2 * r) hqsucc
    by_cases hm0 : m % 2 = 0
    · rw [ite_eq_left hm0]
      by_cases hn0 : n % 2 = 0
      · simp_all
      · rw [ite_eq_right hn0]
        lia
    · rw [ite_eq_right hm0]
      by_cases hn0 : n % 2 = 0
      · rw [ite_eq_left hn0]
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
  · rw [ite_eq_left hrow]
    have hik : i / 2 < r := div_two_lt_of_lt_two_mul hi
    by_cases hi_even : i % 2 = 0
    · rw [ite_eq_left hi_even]
      have hmap :
          i + (2 * r) * (row / 2) =
            2 * (i / 2 + r * (row / 2)) := by
        lia
      simpa [hrow, hmap] using
        (veronesePairLace_even (a := a) (b := b) (r := r)
        (k := i / 2) (n := row / 2) (c := col) hik).symm
    · rw [ite_eq_right hi_even]
      have hmap :
          i + (2 * r) * (row / 2) =
            2 * (i / 2 + r * (row / 2)) + 1 := by
        lia
      simpa [hrow, hmap] using
        (veronesePairLace_odd (a := a) (b := b) (r := r)
        (k := i / 2) (n := row / 2) (c := col) hik).symm
  · rw [ite_eq_right hrow]
    have hjk : j / 2 < r := div_two_lt_of_lt_two_mul hj
    by_cases hj_even : j % 2 = 0
    · rw [ite_eq_left hj_even]
      have hmap :
          j + (2 * r) * (row / 2) =
            2 * (j / 2 + r * (row / 2)) := by
        lia
      simpa [hrow, hmap] using
        (veronesePairLace_even (a := a) (b := b) (r := r)
        (k := j / 2) (n := row / 2) (c := col) hjk).symm
    · rw [ite_eq_right hj_even]
      have hmap :
          j + (2 * r) * (row / 2) =
            2 * (j / 2 + r * (row / 2)) + 1 := by
        lia
      simpa [hrow, hmap] using
        (veronesePairLace_odd (a := a) (b := b) (r := r)
        (k := j / 2) (n := row / 2) (c := col) hjk).symm

/-- Any ordered pair of entries in the interleaved Veronese sequence is a
fully interlacing pair.  This is the coefficient-level pairwise form of
Athanasiadis--Wagner Corollary 5.6. -/
theorem VeronesePairFullyInterlacing.sectionPair {a b : ℕ → ℝ} {r i j : ℕ}
    (h : VeronesePairFullyInterlacing r a b) (hr : 0 < r)
    (hij : i < j) (hj : j < 2 * r) :
    FullyInterlacingPair (veronesePairSectionSeq r a b i)
      (veronesePairSectionSeq r a b j) :=
  fun n rows cols hrows hcols => by
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
  simpa [hminor] using h hrows' hcols

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
      veronesePairSectionSeq r p.coeff q.coeff i n := by
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
    (veronesePairSectionPolynomial r p q i).coeff =
      veronesePairSectionSeq r p.coeff q.coeff i := by
  funext n
  exact coeff_veronesePairSectionPolynomial (r := r) (i := i) (n := n) hr

theorem fullyInterlacingPair_veroneseSectionPolynomial_coeff
    {p q : ℝ[X]} {r k : ℕ}
    (hfull : FullyInterlacingPair p.coeff q.coeff)
    (hr : 0 < r) (hk : k < r) :
    FullyInterlacingPair (veroneseSectionPolynomial r k p).coeff
      (veroneseSectionPolynomial r k q).coeff := by
  simpa [coeff_function_veroneseSectionPolynomial (p := p) hr,
    coeff_function_veroneseSectionPolynomial (p := q) hr] using
    fullyInterlacingPair_veroneseSectionPair hfull hr hk

theorem fullyInterlacingPair_veronesePairSectionPolynomial_coeff
    {p q : ℝ[X]} {r i j : ℕ}
    (hfull : FullyInterlacingPair p.coeff q.coeff)
    (hr : 0 < r) (hij : i < j) (hj : j < 2 * r) :
    FullyInterlacingPair
      (veronesePairSectionPolynomial r p q i).coeff
      (veronesePairSectionPolynomial r p q j).coeff := by
  simpa [coeff_function_veronesePairSectionPolynomial (p := p) (q := q) (i := i) hr,
    coeff_function_veronesePairSectionPolynomial (p := p) (q := q) (i := j) hr] using
    fullyInterlacingPair_veroneseSectionPairwise hfull hr hij hj

/-! ## Polynomial interlacing and the two-row Lace matrix

The row order of `lacePair` is reversed relative to the polynomial-to-Lace
direction: the strictly interlacing nonnegative pair `X + 2`, `X + 1` has a
negative `2 × 2` Lace minor.  The negations below record that refuted
orientation. -/

/-- Unproved target: Hurwitz stability of `q(x^2) + x p(x^2)` makes the
reversed two-row Lace matrix of `q` and `p` totally nonnegative.  Tracked in
GitHub issue #1113. -/
def HurwitzOddEvenToReverseFullyInterlacingPairStatement : Prop :=
  ∀ ⦃p q : ℝ[X]⦄,
    IsHurwitzStable (oddEvenPolynomial p q) →
    FullyInterlacingPair q.coeff p.coeff

/-- The linear pair `X + 2`, `X + 1` violates the current Lace orientation:
the minor on rows `2, 3` and columns `0, 1` has determinant `-1`. -/
private theorem not_fullyInterlacingPair_X_add_C_two_one :
    ¬ FullyInterlacingPair (X + C (2 : ℝ)).coeff (X + C (1 : ℝ)).coeff := by
  intro hfull
  have hminor := hfull (rows := ![2, 3]) (cols := ![0, 1]) (by decide) (by decide)
  erw [Matrix.det_fin_two] at hminor
  norm_num [FullyInterlacingPair, lacePair, toeplitz, Matrix.det_fin_two,
    Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one]
    at hminor

private theorem strictInterl_X_add_C_two_one : StrictInterl (X + C (2 : ℝ)) (X + C (1 : ℝ)) := by
  rw [StrictInterl.X_add_C_iff]
  norm_num

/-- In the historical row orientation, strict interlacing of nonnegative
polynomials does not make their two-row Lace matrix totally nonnegative. -/
theorem not_nonnegStrictInterl_fullyInterlacingPair :
    ¬ ∀ {p q : ℝ[X]},
      HasNonnegCoeffs p →
      HasNonnegCoeffs q →
      StrictInterl p q →
      FullyInterlacingPair p.coeff q.coeff := by
  intro h
  have hpnn : HasNonnegCoeffs (X + C (2 : ℝ)) :=
    hasNonnegCoeffs_X_add_C (by norm_num)
  have hqnn : HasNonnegCoeffs (X + C (1 : ℝ)) :=
    hasNonnegCoeffs_X_add_C (by norm_num)
  exact not_fullyInterlacingPair_X_add_C_two_one
    (h (p := X + C (2 : ℝ)) (q := X + C (1 : ℝ)) hpnn hqnn
      strictInterl_X_add_C_two_one)

/-- The odd/even polynomial `q(x^2) + x p(x^2)` of a strictly interlacing pair
with nonnegative coefficients is Hurwitz stable, by the sign-normalized
Hermite--Biehler theorem. -/
theorem isHurwitzStable_oddEvenPolynomial_of_strictInterl {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q) (hpq : StrictInterl p q) :
    IsHurwitzStable (oddEvenPolynomial p q) :=
  ⟨hasNonnegCoeffs_oddEvenPolynomial hpnn hqnn,
    hermiteBiehlerStableToHurwitzOddEven hpnn hqnn
      (hermiteBiehlerForwardPos (hqnn.pos_leadingCoeff hpq.2.1.1)
        (hpnn.pos_leadingCoeff hpq.1.1) hpq)⟩

/-- Hurwitz stability of `q(x^2) + x p(x^2)` does not make the current
row-oriented Lace matrix of `p` and `q` totally nonnegative. -/
theorem not_isHurwitzStable_oddEven_fullyInterlacingPair :
    ¬ ∀ ⦃p q : ℝ[X]⦄,
      IsHurwitzStable (oddEvenPolynomial p q) →
      FullyInterlacingPair p.coeff q.coeff := fun h =>
  not_nonnegStrictInterl_fullyInterlacingPair fun hpnn hqnn hpq =>
    h (isHurwitzStable_oddEvenPolynomial_of_strictInterl hpnn hqnn hpq)

/-- The forward Hurwitz-matrix criterion is false for the row orientation used
by `hurwitz`: Hurwitz stability does not force the row-oriented Hurwitz matrix
to be totally nonnegative. -/
theorem not_forall_isHurwitzStable_hurwitz_isTotallyNonneg :
    ¬ ∀ ⦃p : ℝ[X]⦄, IsHurwitzStable p → (hurwitz p.coeff).IsTotallyNonneg := fun h =>
  not_nonnegStrictInterl_fullyInterlacingPair fun hpnn hqnn hpq =>
    (hurwitzMatrixTotallyNonnegative_oddEvenPolynomial_iff_fullyInterlacingPair _ _).1
      (h (isHurwitzStable_oddEvenPolynomial_of_strictInterl hpnn hqnn hpq))

/-! ## Converse Hermite--Biehler step for odd/even polynomials -/

/-- Unproved target: converse of the conformal substitution
`hermiteBiehlerStableToHurwitzOddEven`.  Right-half-plane stability of the
odd/even polynomial `q(x^2) + x p(x^2)` forces upper-half-plane stability of
the Hermite--Biehler combination `q + i p`.  Tracked, together with
`HermiteBiehlerConverseOrientedStatement`, in GitHub issue #1112. -/
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
right-half-plane stable. -/
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
    simpa [key] using h (-Complex.I * w) (by simpa [Complex.mul_re] using hw)

/-- Unproved target: oriented converse of `hermiteBiehlerForwardPos`.  For
polynomials `f`, `g` with positive leading coefficients, upper-half-plane
stability of `f + i g` forces `StrictInterl g f`.  The checked converse
`hermiteBiehlerConverse` only gives `StrictInterl g f ∨ StrictInterl f g`, and
`hermiteBiehlerConverseOriented_of_natDegree_lt` settles the strict-degree case.
Tracked, together with `HurwitzOddEvenToHermiteBiehlerStableStatement`, in
GitHub issue #1112. -/
def HermiteBiehlerConverseOrientedStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) →
    StrictInterl g f

/-- Converse Hermite--Biehler step for odd/even polynomials, reduced to the
converse conformal substitution and the oriented converse Hermite--Biehler
theorem.  The nonnegativity half of `IsHurwitzStable` supplies the positive
leading coefficients. -/
theorem strictInterl_of_isHurwitzStable_oddEvenPolynomial
    (hSub : HurwitzOddEvenToHermiteBiehlerStableStatement)
    (hHB : HermiteBiehlerConverseOrientedStatement)
    {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hstable : IsHurwitzStable (oddEvenPolynomial p q)) : StrictInterl p q := by
  obtain ⟨hnn, hrhp⟩ := hstable
  have hpnn : HasNonnegCoeffs p := hasNonnegCoeffs_left_of_oddEvenPolynomial hnn
  have hqnn : HasNonnegCoeffs q := hasNonnegCoeffs_right_of_oddEvenPolynomial hnn
  exact hHB (hqnn.pos_leadingCoeff hq) (hpnn.pos_leadingCoeff hp) (hSub hpnn hqnn hrhp)

/-! ## Degree-based orientation of the converse Hermite--Biehler step

Once the two factors have strictly ordered degrees, the orientation is forced
by the elementary degree constraint carried by `StrictInterl`, so the checked
disjunctive converse `hermiteBiehlerConverse` already suffices.  The orientation
content of `HermiteBiehlerConverseOrientedStatement` is therefore confined to
the equal-degree case. -/

/-- Elementary orientation resolution by degree.  A disjunctive interlacing
conclusion `StrictInterl g f ∨ StrictInterl f g` collapses to the oriented branch
`StrictInterl g f`
as soon as the degrees are strictly ordered `g.natDegree < f.natDegree`, since
the reversed branch `StrictInterl f g` would force `f.natDegree ≤ g.natDegree`. -/
theorem strictInterl_of_or_of_natDegree_lt {f g : ℝ[X]}
    (h : StrictInterl g f ∨ StrictInterl f g)
    (hgf : g.natDegree < f.natDegree) : StrictInterl g f :=
  h.elim id fun h => absurd h.natDegree_le (by lia)

/-- Oriented converse Hermite--Biehler theorem in the strict-degree case.
For `f, g` with positive leading coefficients and `g.natDegree < f.natDegree`,
upper-half-plane stability of `f + i g` forces `StrictInterl g f`. -/
theorem hermiteBiehlerConverseOriented_of_natDegree_lt {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : g.natDegree < f.natDegree)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    StrictInterl g f :=
  strictInterl_of_or_of_natDegree_lt (hermiteBiehlerConverse hf hg hstable) hdeg

/-- Strict-degree case of `strictInterl_of_isHurwitzStable_oddEvenPolynomial`,
needing only the converse conformal substitution.

When `p.natDegree < q.natDegree` (equivalently, when `oddEvenPolynomial p q` has
even degree, see `natDegree_lt_iff_even_natDegree_oddEvenPolynomial`), Hurwitz
stability of `q(x²) + x p(x²)` forces `StrictInterl p q`: the orientation is
forced by the degree gap. -/
theorem strictInterl_of_isHurwitzStable_oddEvenPolynomial_of_natDegree_lt
    (hSub : HurwitzOddEvenToHermiteBiehlerStableStatement)
    {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hdeg : p.natDegree < q.natDegree)
    (hstable : IsHurwitzStable (oddEvenPolynomial p q)) : StrictInterl p q := by
  obtain ⟨hnn, hrhp⟩ := hstable
  have hpnn := hasNonnegCoeffs_left_of_oddEvenPolynomial hnn
  have hqnn := hasNonnegCoeffs_right_of_oddEvenPolynomial hnn
  exact hermiteBiehlerConverseOriented_of_natDegree_lt (hqnn.pos_leadingCoeff hq)
    (hpnn.pos_leadingCoeff hp) hdeg (hSub hpnn hqnn hrhp)

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
    · simpa using hz₀
  · exact ⟨z₀, h, hz₀⟩

/-- Degenerate (`p = 0`) case of the converse conformal substitution. -/
theorem isUpperHalfPlaneStable_hermiteBiehler_of_rhp_left_zero
    {q : ℝ[X]}
    (hrhp : IsRightHalfPlaneStable (complexify (oddEvenPolynomial 0 q))) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q 0) := fun z hz => by
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
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial 0 p) := fun z hz => by
  obtain ⟨w, hwre, hwsq⟩ := exists_rightHalfPlane_sqrt_of_im_pos hz
  have hc0 : complexify (0 : ℝ[X]) = 0 := by simp [complexify]
  have h := hrhp w hwre
  rw [eval_complexify_oddEvenPolynomial, hc0] at h
  simp only [Polynomial.eval_zero, zero_add] at h
  rw [hwsq] at h
  rw [eval_hermiteBiehlerPolynomial, hc0]
  simp only [Polynomial.eval_zero, zero_add]
  exact mul_ne_zero Complex.I_ne_zero fun h0 => h (by rw [h0, mul_zero])

/-- Veronese subsequences preserve Toeplitz total nonnegativity.

The hypothesis `k < r` is essential for the Toeplitz submatrix identification:
it makes `cols j ≤ rows i` equivalent to
`r * cols j ≤ k + r * rows i`. -/
protected theorem IsPolyaFreqSeq.veroneseSectionSeq {a : ℕ → ℝ}
    (ha : IsPolyaFreqSeq a) {r k : ℕ} (hr : 0 < r) (hk : k < r) :
    IsPolyaFreqSeq (veroneseSectionSeq r k a) :=
  fun n rows cols hrows hcols => by
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
      rw [ite_eq_left hle, ite_eq_left hle']
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
  simpa [hminor] using ha hrows' hcols'

theorem isPolyaFreqSeq_veroneseSectionPolynomial_coeff {p : ℝ[X]}
    (hp : IsPolyaFreqSeq p.coeff) {r k : ℕ}
    (hr : 0 < r) (hk : k < r) :
    IsPolyaFreqSeq (veroneseSectionPolynomial r k p).coeff := by
  simpa [coeff_function_veroneseSectionPolynomial hr] using hp.veroneseSectionSeq hr hk

/-- Real-rootedness of Veronese sections from the forward ASW
theorem and a PF certificate for the original polynomial. -/
theorem splits_veroneseSectionPolynomial_of_pf {p : ℝ[X]}
    (hp : IsPolyaFreqSeq p.coeff) {r k : ℕ}
    (hr : 0 < r) (hk : k < r) :
    veroneseSectionPolynomial r k p = 0 ∨
      (veroneseSectionPolynomial r k p).Splits :=
  Or.inr
    (aissenSchoenbergWhitneyForward
      (isPolyaFreqSeq_veroneseSectionPolynomial_coeff (p := p) hp hr hk)).1

/-- PF preservation for Veronese sections of real-rooted
nonnegative-coefficient polynomials, using the reverse ASW theorem. -/
theorem isPolyaFreqSeq_veroneseSectionPolynomial_of_splits_of_hasNonnegCoeffs
    {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hprr : p.Splits) {r k : ℕ}
    (hr : 0 < r) (hk : k < r) :
    IsPolyaFreqSeq (veroneseSectionPolynomial r k p).coeff :=
  isPolyaFreqSeq_veroneseSectionPolynomial_coeff (p := p)
    (aissenSchoenbergWhitney_reverse hpnn hprr (roots_nonpos_of_nonneg_coeffs hprr hpnn))
    hr hk

/-- Real-rootedness of Veronese sections of real-rooted
nonnegative-coefficient polynomials, from both directions of ASW. -/
theorem splits_veroneseSectionPolynomial_of_splits_nonneg {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hprr : p.Splits) {r k : ℕ}
    (hr : 0 < r) (hk : k < r) :
    veroneseSectionPolynomial r k p = 0 ∨
      (veroneseSectionPolynomial r k p).Splits :=
  Or.inr
    (aissenSchoenbergWhitneyForward
      (isPolyaFreqSeq_veroneseSectionPolynomial_of_splits_of_hasNonnegCoeffs hpnn hprr hr hk)).1

end RealRooted
