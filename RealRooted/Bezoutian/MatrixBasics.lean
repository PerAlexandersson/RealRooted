import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import RealRooted.Bezoutian.StrictInterleaving
import RealRooted.Mathlib.Algebra.Polynomial.Bezoutian

/-!
# Elementary real Bezout matrices

Coefficient and matrix definitions, scalar transport, explicit linear and
quadratic formulas, and small positive-definiteness certificates.
-/

open Polynomial Matrix

noncomputable section

namespace RealRooted

/-- Compatibility wrapper for the Mathlib-shaped coefficient Bezoutian. -/
def bezoutSeqEntry {A : Type*} [CommRing A] (a b : ℕ → A) (i j : ℕ) : A :=
  Finset.sum (Finset.range (min i j + 1)) fun k ↦
    a (i + j + 1 - k) * b k - b (i + j + 1 - k) * a k

lemma bezoutSeqEntry.comm {A : Type*} [CommRing A] (a b : ℕ → A) (i j : ℕ) :
    bezoutSeqEntry a b i j = bezoutSeqEntry a b j i :=
  Polynomial.bezoutSeqEntry.comm a b i j

lemma bezoutSeqEntry.eq_zero_of_le_left {A : Type*} [CommRing A] (a b : ℕ → A)
    {n : ℕ} {i j : ℕ}
    (ha : ∀ k, n < k → a k = 0) (hb : ∀ k, n < k → b k = 0) (hi : n ≤ i) :
    bezoutSeqEntry a b i j = 0 :=
  Polynomial.bezoutSeqEntry.eq_zero_of_le_left a b ha hb hi

lemma bezoutSeqEntry.eq_zero_of_le_right {A : Type*} [CommRing A] (a b : ℕ → A)
    {n : ℕ} {i j : ℕ}
    (ha : ∀ k, n < k → a k = 0) (hb : ∀ k, n < k → b k = 0) (hj : n ≤ j) :
    bezoutSeqEntry a b i j = 0 :=
  Polynomial.bezoutSeqEntry.eq_zero_of_le_right a b ha hb hj

lemma bezoutSeqEntry.telescoping {A : Type*} [CommRing A] (a b : ℕ → A) (i j : ℕ) :
    bezoutSeqEntry a b i (j + 1) - bezoutSeqEntry a b (i + 1) j =
    a (i + 1) * b (j + 1) - a (j + 1) * b (i + 1) :=
  Polynomial.bezoutSeqEntry.telescoping a b i j

lemma bezoutSeqEntry.coeff_mul_sub_coeff_mul {A : Type*} [CommRing A] (a b : ℕ → A)
    (i j : ℕ) :
    a i * b j - a j * b i =
      (if i ≠ 0 then bezoutSeqEntry a b (i - 1) j else 0) -
        (if j ≠ 0 then bezoutSeqEntry a b i (j - 1) else 0) :=
  Polynomial.bezoutSeqEntry.coeff_mul_sub_coeff_mul a b i j

lemma bezoutSeqEntry.bilinear_mul_sub {A : Type*} [CommRing A] (a b : ℕ → A)
    (n : ℕ) (t₁ t₂ : A)
    (ha : ∀ k, n < k → a k = 0) (hb : ∀ k, n < k → b k = 0) :
    (t₁ - t₂) * ∑ i : Fin n, ∑ j : Fin n,
    bezoutSeqEntry a b i.val j.val * t₁ ^ i.val * t₂ ^ j.val =
    (∑ i ∈ Finset.range (n + 1), a i * t₁ ^ i) *
      (∑ j ∈ Finset.range (n + 1), b j * t₂ ^ j) -
    (∑ i ∈ Finset.range (n + 1), a i * t₂ ^ i) *
      (∑ j ∈ Finset.range (n + 1), b j * t₁ ^ j) :=
  Polynomial.bezoutSeqEntry.bilinear_mul_sub a b n t₁ t₂ ha hb

/-- The `(i,j)` coefficient of the Bezoutian
`(p(X) q(Y) - p(Y) q(X)) / (X - Y)`.

This definition is independent of a matrix size. Coefficients outside the
degrees of `p` and `q` vanish through `Polynomial.coeff`. -/
def bezoutEntry (p q : ℝ[X]) (i j : ℕ) : ℝ :=
  Finset.sum (Finset.range (min i j + 1)) fun k ↦
    p.coeff (i + j + 1 - k) * q.coeff k -
      q.coeff (i + j + 1 - k) * p.coeff k

/-- The `n × n` Bezout matrix attached to two polynomials. -/
def bezoutMatrix (n : ℕ) (p q : ℝ[X]) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ bezoutEntry p q i.1 j.1

def bezoutRowPoly (n : ℕ) (p q : ℝ[X]) (i : Fin n) : ℝ[X] :=
  ∑ j : Fin n, C (bezoutEntry p q i j) * X ^ (j : ℕ)

lemma bezoutEntry.comm (p q : ℝ[X]) (i j : ℕ) :
    bezoutEntry p q i j = bezoutEntry p q j i :=
  Polynomial.bezoutEntry.comm p q i j

lemma bezoutEntry.cast_complex (p q : ℝ[X]) (i j : ℕ) :
    (bezoutEntry p q i j : ℂ) =
      bezoutSeqEntry (p.map Complex.ofRealHom).coeff
        (q.map Complex.ofRealHom).coeff i j := by
  simp [bezoutEntry, bezoutSeqEntry, coeff_map]
lemma bezoutMatrix.isHermitian (n : ℕ) (p q : ℝ[X]) :
    (bezoutMatrix n p q).IsHermitian := by
  ext i j
  simp [bezoutMatrix, bezoutEntry.comm p q i.1 j.1]

lemma Matrix.PosDef.sum_pos {m : ℕ} {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.PosDef)
    {x : Fin m → ℝ} (hx : x ≠ 0) :
    0 < ∑ i : Fin m, ∑ j : Fin m, B i j * x i * x j := by
  have h_dot := hB.dotProduct_mulVec_pos hx
  simp only [dotProduct, mulVec, star_trivial] at h_dot
  have h_sum : ∑ i : Fin m, x i * ∑ j : Fin m, B i j * x j =
      ∑ i : Fin m, ∑ j : Fin m, B i j * x i * x j := by
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  simp_all

lemma bezoutMatrix.left_ne_zero_of_posDef_two {p q : ℝ[X]}
    (h : (bezoutMatrix 2 p q).PosDef) :
    p ≠ 0 := by
  rintro rfl
  have hdiag : 0 < bezoutMatrix 2 0 q 0 0 := h.diag_pos
  simp [bezoutMatrix, bezoutEntry] at hdiag

lemma bezoutMatrix.right_ne_zero_of_posDef_two {p q : ℝ[X]}
    (h : (bezoutMatrix 2 p q).PosDef) :
    q ≠ 0 := by
  rintro rfl
  have hdiag : 0 < bezoutMatrix 2 p 0 0 0 := h.diag_pos
  simp [bezoutMatrix, bezoutEntry] at hdiag

lemma bezoutEntry.C_mul_C_mul (u v : ℝ) (p q : ℝ[X]) (i j : ℕ) :
    bezoutEntry (C u * p) (C v * q) i j = u * v * bezoutEntry p q i j := by
  simp only [bezoutEntry, coeff_C_mul, Finset.mul_sum]
  grind

lemma bezoutMatrix.C_mul_C_mul (n : ℕ) (u v : ℝ) (p q : ℝ[X]) :
    bezoutMatrix n (C u * p) (C v * q) = (u * v) • bezoutMatrix n p q := by
  ext i j
  simp [bezoutMatrix, bezoutEntry.C_mul_C_mul]

lemma bezoutMatrix.C_mul_C_mul_posDef_iff {n : ℕ} {u v : ℝ} {p q : ℝ[X]}
    (hu : 0 < u) (hv : 0 < v) :
    (bezoutMatrix n (C u * p) (C v * q)).PosDef ↔ (bezoutMatrix n p q).PosDef := by
  rw [bezoutMatrix.C_mul_C_mul]
  refine ⟨fun h ↦ ?_, fun h ↦ h.smul (mul_pos hu hv)⟩
  have hscaled := h.smul (inv_pos.mpr (mul_pos hu hv))
  rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hu.ne' hv.ne'), one_smul] at hscaled

lemma bezoutMatrix.linear_eq_diagonal (a b : ℝ) :
    bezoutMatrix 1 (X + C a) (X + C b) =
    Matrix.diagonal (fun _ : Fin 1 ↦ b - a) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [bezoutMatrix, bezoutEntry, Matrix.diagonal]

lemma bezoutMatrix.linear_posDef_one {a b : ℝ} (hab : a < b) :
    (bezoutMatrix 1 (X + C a) (X + C b)).PosDef := by
  rw [bezoutMatrix.linear_eq_diagonal]
  simp_all

lemma bezoutMatrix.lt_of_linear_posDef_one {a b : ℝ}
    (h : (bezoutMatrix 1 (X + C a) (X + C b)).PosDef) :
    a < b := by
  have hdiag := h.diag_pos (i := 0)
  rw [bezoutMatrix.linear_eq_diagonal] at hdiag
  simp_all

lemma bezoutMatrix.linear_posDef_one_iff {a b : ℝ} :
    (bezoutMatrix 1 (X + C a) (X + C b)).PosDef ↔ a < b :=
  ⟨bezoutMatrix.lt_of_linear_posDef_one, bezoutMatrix.linear_posDef_one⟩

/-- Every polynomial of the form `X + C a` is real-rooted. -/
lemma Polynomial.isRealRooted_X_add_C (a : ℝ) :
    (X + C a : ℝ[X]) ≠ 0 ∧ (X + C a).Splits := by
  simpa [sub_eq_add_neg] using isRealRooted_X_sub_C (-a)

lemma Polynomial.roots_sort_mul_X_add_C_X_add_C {a c : ℝ} (hac : a ≤ c) :
    ((X + C a) * (X + C c)).roots.sort (· ≤ ·) = [(-c : ℝ), -a] := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · simp
  · simp [neg_le_neg hac]
  · apply Multiset.coe_eq_coe.mp
    rw [Multiset.sort_eq]
    rw [roots_mul (mul_ne_zero (X_add_C_ne_zero a) (X_add_C_ne_zero c)),
      roots_X_add_C, roots_X_add_C]
    exact Multiset.pair_comm (-a) (-c)

lemma Polynomial.exists_pos_scalar_mul_X_add_C_of_natDegree_one {p : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hp_deg : p.natDegree = 1) :
    ∃ u a : ℝ, 0 < u ∧ p = C u * (X + C a) := by
  let u := p.coeff 1
  have hu_pos : 0 < u := by simpa [HasPosLeadingCoeff, leadingCoeff, hp_deg, u] using hp_pos
  refine ⟨u, p.coeff 0 / u, hu_pos, ?_⟩
  calc
    p = C u * X + C (p.coeff 0) := by
      simpa [u] using Polynomial.eq_X_add_C_of_natDegree_le_one (p := p) hp_deg.le
    _ = C u * (X + C (p.coeff 0 / u)) := by rw [mul_add, ← C_mul, mul_div_cancel₀ _ hu_pos.ne']

lemma StrictPrecSameDegree.X_add_C_iff {a b : ℝ} :
    StrictPrecSameDegree (X + C b) (X + C a) ↔ a < b := by
  simp [StrictPrecSameDegree, Polynomial.isRealRooted_X_add_C, List.interleaves_singleton_singleton]

lemma StrictPrecSameDegree.X_add_C_bezoutMatrix_posDef_iff_one {a b : ℝ} :
    StrictPrecSameDegree (X + C b) (X + C a) ↔
    (bezoutMatrix 1 (X + C a) (X + C b)).PosDef := by
  rw [StrictPrecSameDegree.X_add_C_iff, bezoutMatrix.linear_posDef_one_iff]

lemma Polynomial.isRealRooted_of_natDegree_two_of_isRoot {p : ℝ[X]} {x : ℝ}
    (hdeg : p.natDegree = 2) (hx : p.IsRoot x) :
    p ≠ 0 ∧ p.Splits := by
  have hp_ne : p ≠ 0 := fun hp ↦ by
    simp_all
  exact ⟨hp_ne, Splits.of_natDegree_eq_two hdeg hx⟩

lemma Polynomial.eq_quadratic_of_natDegree_le_two {p : ℝ[X]} (hp : p.natDegree ≤ 2) :
    p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
  Polynomial.eq_quadratic_of_degree_le_two (p := p) (Polynomial.degree_le_of_natDegree_le hp)

lemma Polynomial.exists_quadratic_eq_zero_of_discrim_nonneg {a b c : ℝ}
    (ha : a ≠ 0) (hdisc : 0 ≤ discrim a b c) :
    ∃ x : ℝ, a * (x * x) + b * x + c = 0 := by
  refine exists_quadratic_eq_zero ha
    ⟨Real.sqrt (discrim a b c), by simp_all⟩

lemma Polynomial.isRealRooted_of_natDegree_two_of_discrim_nonneg {p : ℝ[X]}
    (hdeg : p.natDegree = 2)
    (hdisc : 0 ≤ discrim (p.coeff 2) (p.coeff 1) (p.coeff 0)) :
    p ≠ 0 ∧ p.Splits := by
  have hp_ne : p ≠ 0 := fun hp ↦ by
    simp_all
  have hcoeff2 : p.coeff 2 ≠ 0 := hdeg.symm ▸ leadingCoeff_ne_zero.mpr hp_ne
  rcases exists_quadratic_eq_zero_of_discrim_nonneg hcoeff2 hdisc with ⟨x, hx⟩
  have h_root : p.IsRoot x := by
    rw [IsRoot.def, eq_quadratic_of_natDegree_le_two hdeg.le]
    simpa [pow_two] using hx
  exact isRealRooted_of_natDegree_two_of_isRoot hdeg h_root

/-- A real-rooted quadratic is a positive/negative scalar multiple of two
linear factors, with the constants ordered in the `X + C a` convention used
below. -/
lemma Polynomial.exists_sorted_linear_factors_of_isRealRooted_natDegree_two {p : ℝ[X]}
    (hp_splits : p.Splits) (hdeg : p.natDegree = 2) :
    ∃ a c : ℝ, a ≤ c ∧ p = C p.leadingCoeff * ((X + C a) * (X + C c)) := by
  have hcard : p.roots.card = 2 := by rw [hp_splits.natDegree_eq_card_roots.symm, hdeg]
  rcases Multiset.card_eq_two.mp hcard with ⟨r, s, hroots⟩
  by_cases hrs : r ≤ s
  · refine ⟨-s, -r, neg_le_neg hrs, ?_⟩
    conv_lhs => rw [hp_splits.eq_prod_roots]
    rw [hroots]
    simp [sub_eq_add_neg, mul_comm]
  · refine ⟨-r, -s, neg_le_neg (not_le.mp hrs).le, ?_⟩
    conv_lhs => rw [hp_splits.eq_prod_roots]
    rw [hroots]
    simp [sub_eq_add_neg]

lemma bezoutMatrix.quadratic_eq_fin_two (a b c d : ℝ) :
    bezoutMatrix 2 ((X + C a) * (X + C c)) ((X + C b) * (X + C d)) =
    !![(a + c) * (b * d) - (b + d) * (a * c), b * d - a * c;
    b * d - a * c, b + d - (a + c)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bezoutMatrix, bezoutEntry, coeff_add, coeff_mul, Finset.antidiagonal,
      Finset.range, coeff_X, coeff_C]

lemma bezoutMatrix.fin_two_eq_coeff_of_natDegree_le_two {p q : ℝ[X]}
    (hp_deg : p.natDegree ≤ 2) (hq_deg : q.natDegree ≤ 2) :
    bezoutMatrix 2 q p =
    !![q.coeff 1 * p.coeff 0 - p.coeff 1 * q.coeff 0,
      q.coeff 2 * p.coeff 0 - p.coeff 2 * q.coeff 0;
      q.coeff 2 * p.coeff 0 - p.coeff 2 * q.coeff 0,
      q.coeff 2 * p.coeff 1 - p.coeff 2 * q.coeff 1] := by
  have hp3 : p.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hp_deg)
  have hq3 : q.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hq_deg)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bezoutMatrix, bezoutEntry, hp3, hq3, Finset.sum_range_succ]

lemma bezoutMatrix.dotProduct_fin_two_coeff_discrim_right_top {p q : ℝ[X]}
    (hp_deg : p.natDegree ≤ 2) (hq_deg : q.natDegree ≤ 2) :
    let x : Fin 2 → ℝ := fun i ↦ if i = 0 then 2 * p.coeff 2 else -p.coeff 1
    dotProduct (star x) (Matrix.mulVec (bezoutMatrix 2 q p) x) =
    discrim (p.coeff 2) (p.coeff 1) (p.coeff 0) * (bezoutMatrix 2 q p 1 1) := by
  intro x
  rw [bezoutMatrix.fin_two_eq_coeff_of_natDegree_le_two hp_deg hq_deg]
  norm_num [x, dotProduct, Matrix.mulVec, discrim]
  ring

lemma bezoutMatrix.discrim_pos_of_posDef_of_entry_pos_right_top {p q : ℝ[X]}
    (hp_deg : p.natDegree ≤ 2) (hq_deg : q.natDegree ≤ 2)
    (hp_coeff2 : p.coeff 2 ≠ 0)
    (hentry : 0 < bezoutMatrix 2 q p 1 1)
    (h : (bezoutMatrix 2 q p).PosDef) :
    0 < discrim (p.coeff 2) (p.coeff 1) (p.coeff 0) := by
  let x : Fin 2 → ℝ := fun i ↦ if i = 0 then 2 * p.coeff 2 else -p.coeff 1
  have hx : x ≠ 0 := fun hx0 ↦ hp_coeff2 (by simpa [x] using congr_fun hx0 0)
  have hquad : 0 < dotProduct (star x) (Matrix.mulVec (bezoutMatrix 2 q p) x) :=
    h.dotProduct_mulVec_pos hx
  rw [bezoutMatrix.dotProduct_fin_two_coeff_discrim_right_top hp_deg hq_deg] at hquad
  simp_all

lemma bezoutMatrix.right_isRealRooted_of_posDef_two_of_natDegree_two {p q : ℝ[X]}
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree ≤ 2)
    (h : (bezoutMatrix 2 q p).PosDef) :
    p ≠ 0 ∧ p.Splits := by
  have hp_ne : p ≠ 0 := bezoutMatrix.right_ne_zero_of_posDef_two h
  have hp_coeff2 : p.coeff 2 ≠ 0 := hp_deg.symm ▸ leadingCoeff_ne_zero.mpr hp_ne
  have hentry := h.diag_pos (i := 1)
  have hdisc : 0 ≤ discrim (p.coeff 2) (p.coeff 1) (p.coeff 0) :=
    (bezoutMatrix.discrim_pos_of_posDef_of_entry_pos_right_top hp_deg.le hq_deg
      hp_coeff2 hentry h).le
  exact Polynomial.isRealRooted_of_natDegree_two_of_discrim_nonneg hp_deg hdisc

lemma bezoutMatrix.dotProduct_fin_two_coeff_discrim_left_top {p q : ℝ[X]}
    (hp_deg : p.natDegree ≤ 2) (hq_deg : q.natDegree ≤ 2) :
    let x : Fin 2 → ℝ := fun i ↦ if i = 0 then 2 * q.coeff 2 else -q.coeff 1
    dotProduct (star x) (Matrix.mulVec (bezoutMatrix 2 q p) x) =
    discrim (q.coeff 2) (q.coeff 1) (q.coeff 0) * (bezoutMatrix 2 q p 1 1) := by
  intro x
  rw [bezoutMatrix.fin_two_eq_coeff_of_natDegree_le_two hp_deg hq_deg]
  norm_num [x, dotProduct, Matrix.mulVec, discrim]
  ring

lemma bezoutMatrix.left_isRealRooted_of_posDef_two_of_natDegree_two {p q : ℝ[X]}
    (hp_deg : p.natDegree ≤ 2) (hq_deg : q.natDegree = 2)
    (h : (bezoutMatrix 2 q p).PosDef) :
    q ≠ 0 ∧ q.Splits := by
  have hq_ne : q ≠ 0 := bezoutMatrix.left_ne_zero_of_posDef_two h
  have hq_coeff2 : q.coeff 2 ≠ 0 := hq_deg.symm ▸ leadingCoeff_ne_zero.mpr hq_ne
  let x : Fin 2 → ℝ := fun i ↦ if i = 0 then 2 * q.coeff 2 else -q.coeff 1
  have hx : x ≠ 0 := fun hx0 ↦ hq_coeff2 (by simpa [x] using congr_fun hx0 0)
  have hquad : 0 < dotProduct (star x) (Matrix.mulVec (bezoutMatrix 2 q p) x) :=
    h.dotProduct_mulVec_pos hx
  rw [bezoutMatrix.dotProduct_fin_two_coeff_discrim_left_top hp_deg hq_deg.le] at hquad
  have hentry := h.diag_pos (i := 1)
  have hdisc : 0 ≤ discrim (q.coeff 2) (q.coeff 1) (q.coeff 0) :=
    (pos_of_mul_pos_left hquad hentry.le).le
  exact Polynomial.isRealRooted_of_natDegree_two_of_discrim_nonneg hq_deg hdisc

/-- The lower-right diagonal entry gives a necessary sum inequality for a
positive-semidefinite quadratic Bezoutian. -/
lemma bezoutMatrix.sum_le_of_quadratic_posSemidef {a b c d : ℝ}
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosSemidef) :
    a + c ≤ b + d := by
  have hdiag := h.diag_nonneg (i := 1)
  rw [bezoutMatrix.quadratic_eq_fin_two] at hdiag
  simpa using hdiag

/-- The determinant inequality for a positive-semidefinite `2 × 2` real matrix,
written in entry form. -/
lemma _root_.Matrix.PosSemidef.det_nonneg_fin_two {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosSemidef) :
    0 ≤ A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  have hdet : 0 ≤ A.det := hA.det_nonneg
  simpa [Matrix.det_fin_two] using hdet

/-- The determinant inequality extracted from the closed-form quadratic
Bezoutian. -/
lemma bezoutMatrix.det_nonneg_of_quadratic_posSemidef {a b c d : ℝ}
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosSemidef) :
    0 ≤ ((a + c) * (b * d) - (b + d) * (a * c)) * (b + d - (a + c)) -
    (b * d - a * c) * (b * d - a * c) := by
  have hdet := h.det_nonneg_fin_two
  rw [bezoutMatrix.quadratic_eq_fin_two] at hdet
  simpa using hdet

/-- The determinant obstruction for the quadratic Bezoutian in fact factors
into the four expected endpoint gaps. -/
lemma bezoutMatrix.det_factor_nonneg_of_quadratic_posSemidef {a b c d : ℝ}
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosSemidef) :
    0 ≤ (a - b) * (a - d) * (b - c) * (c - d) := by
  have hdet := bezoutMatrix.det_nonneg_of_quadratic_posSemidef h
  grind

lemma _root_.Matrix.posDef_fin_two_of_entries {a b c : ℝ}
    (ha : 0 < a) (hdet : 0 < a * c - b * b) :
    (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  refine .of_dotProduct_mulVec_pos (.ext (by simp)) fun x hx ↦ ?_
  have h : x 0 = 0 → x 1 ≠ 0 := by simpa [funext_iff, Fin.forall_fin_two] using hx
  simp only [star_trivial, cons_mulVec, cons_dotProduct, dotProduct_of_isEmpty,
    add_zero, empty_mulVec, dotProduct_cons, gt_iff_lt]
  change 0 < x 0 * (a * x 0 + b * x 1) + x 1 * (b * x 0 + c * x 1)
  rcases eq_or_ne (x 1) 0 with h1 | h1
  · rw [h1]
    nlinarith [mul_self_pos.mpr (fun h0 ↦ h h0 h1 : x 0 ≠ 0)]
  · nlinarith [sq_nonneg (a * x 0 + b * x 1), mul_pos hdet (mul_self_pos.mpr h1)]

/-- An explicit `LDLᵀ` certificate for positive definiteness of a symmetric
`3 × 3` real matrix. -/
lemma _root_.Matrix.posDef_fin_three_of_ldl {d₀ d₁ d₂ l₁₀ l₂₀ l₂₁ : ℝ}
    (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    (!![d₀, d₀ * l₁₀, d₀ * l₂₀;
        d₀ * l₁₀, d₀ * l₁₀ ^ 2 + d₁,
          d₀ * l₁₀ * l₂₀ + d₁ * l₂₁;
        d₀ * l₂₀, d₀ * l₁₀ * l₂₀ + d₁ * l₂₁,
          d₀ * l₂₀ ^ 2 + d₁ * l₂₁ ^ 2 + d₂] :
      Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · exact Matrix.IsHermitian.ext (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp)
  · intro x hx
    have hform :
        dotProduct (star x) (Matrix.mulVec
          ((!![d₀, d₀ * l₁₀, d₀ * l₂₀;
            d₀ * l₁₀, d₀ * l₁₀ ^ 2 + d₁,
              d₀ * l₁₀ * l₂₀ + d₁ * l₂₁;
            d₀ * l₂₀, d₀ * l₁₀ * l₂₀ + d₁ * l₂₁,
              d₀ * l₂₀ ^ 2 + d₁ * l₂₁ ^ 2 + d₂] :
            Matrix (Fin 3) (Fin 3) ℝ)) x) =
          d₀ * (x 0 + l₁₀ * x 1 + l₂₀ * x 2) ^ 2 +
          d₁ * (x 1 + l₂₁ * x 2) ^ 2 + d₂ * (x 2) ^ 2 := by
      rw [Matrix.vec3_dotProduct]
      simp only [Matrix.mulVec, Matrix.vec3_dotProduct]
      simp
      ring
    rw [hform]
    by_cases hx₂ : x 2 = 0
    · by_cases hx₁ : x 1 = 0
      · have hx₀ : x 0 ≠ 0 := by
          intro hx₀
          apply hx
          funext i
          fin_cases i <;> assumption
        simp [hx₂, hx₁, mul_pos hd₀ (sq_pos_of_ne_zero hx₀)]
      · have h₁ : 0 < d₁ * (x 1 + l₂₁ * x 2) ^ 2 := by
          simp [hx₂, mul_pos hd₁ (sq_pos_of_ne_zero hx₁)]
        positivity
    · have h₂ : 0 < d₂ * (x 2) ^ 2 :=
        mul_pos hd₂ (sq_pos_of_ne_zero hx₂)
      positivity

lemma bezoutEntry.eq_zero_of_le_left (p q : ℝ[X]) {n : ℕ} {i j : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) (hi : n ≤ i) :
    bezoutEntry p q i j = 0 := by
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  have hk_le : k ≤ min i j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hj_le : k ≤ j := hk_le.trans (min_le_right i j)
  have hp0 : p.coeff (i + j + 1 - k) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
  have hq0 : q.coeff (i + j + 1 - k) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
  simp [hp0, hq0]

lemma bezoutEntry.eq_zero_of_le_right (p q : ℝ[X]) {n : ℕ} {i j : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) (hj : n ≤ j) :
    bezoutEntry p q i j = 0 :=
  bezoutEntry.comm p q j i ▸ bezoutEntry.eq_zero_of_le_left p q hp hq hj

lemma bezoutEntry.telescoping (p q : ℝ[X]) (i j : ℕ) :
    bezoutEntry p q i (j + 1) - bezoutEntry p q (i + 1) j =
    p.coeff (i + 1) * q.coeff (j + 1) - p.coeff (j + 1) * q.coeff (i + 1) :=
  bezoutSeqEntry.telescoping p.coeff q.coeff i j

lemma bezoutEntry.coeff_mul_sub_coeff_mul (p q : ℝ[X]) (i j : ℕ) :
    p.coeff i * q.coeff j - p.coeff j * q.coeff i =
      (if i ≠ 0 then bezoutEntry p q (i - 1) j else 0) -
        (if j ≠ 0 then bezoutEntry p q i (j - 1) else 0) :=
  bezoutSeqEntry.coeff_mul_sub_coeff_mul p.coeff q.coeff i j

lemma bezoutEntry.bilinear_mul_sub (p q : ℝ[X]) {n : ℕ} (t₁ t₂ : ℝ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (t₁ - t₂) * ∑ i : Fin n, ∑ j : Fin n,
    bezoutEntry p q i.val j.val * t₁ ^ i.val * t₂ ^ j.val =
    p.eval t₁ * q.eval t₂ - p.eval t₂ * q.eval t₁ := by
  have hp_zero (k : ℕ) (hk : n < k) : p.coeff k = 0 :=
    coeff_eq_zero_of_natDegree_lt (hp.trans_lt hk)
  have hq_zero (k : ℕ) (hk : n < k) : q.coeff k = 0 :=
    coeff_eq_zero_of_natDegree_lt (hq.trans_lt hk)
  have h_eq :
      (t₁ - t₂) * ∑ i : Fin n, ∑ j : Fin n,
        bezoutSeqEntry p.coeff q.coeff i.val j.val * t₁ ^ i.val * t₂ ^ j.val =
      (∑ i ∈ Finset.range (n + 1), p.coeff i * t₁ ^ i) *
        (∑ j ∈ Finset.range (n + 1), q.coeff j * t₂ ^ j) -
      (∑ i ∈ Finset.range (n + 1), p.coeff i * t₂ ^ i) *
        (∑ j ∈ Finset.range (n + 1), q.coeff j * t₁ ^ j) :=
    bezoutSeqEntry.bilinear_mul_sub p.coeff q.coeff n t₁ t₂ hp_zero hq_zero
  simp_rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp),
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq)]
  exact h_eq

end RealRooted
