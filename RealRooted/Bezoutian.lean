import RealRooted.Basic
import RealRooted.Linear
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Matrix.PosDef

/-!
# Bezout matrices and interlacing

This file records the planned Bezout-matrix characterization of strict
same-degree interlacing.  The main theorem at the bottom uses `proof_wanted`,
not `sorry`: it is a breadcrumb for a future formalization pass, not yet a
completed proof.

For polynomials

`p(X) = \sum_i a_i X^i`, `q(X) = \sum_i b_i X^i`,

the Bezoutian is

`(p(X) q(Y) - p(Y) q(X)) / (X - Y)`.

The coefficient of `X^i Y^j` is

`∑ k ≤ min i j, a_{i+j+1-k} b_k - b_{i+j+1-k} a_k`.

The matrix below uses this coefficient formula directly.  With the current root
orientation convention, strict same-degree alternation of `p` by `q` should be
detected by positive definiteness of `bezoutMatrix n q p`, not
`bezoutMatrix n p q`.

The positive-semidefinite weak theorem is deliberately not the main target here:
common factors and multiple roots introduce rank defects and gcd bookkeeping.
The primary theorem for this file is the strict `PosDef` version.

The reusable theorem `prec_iff_sorted_roots` below normalizes `Prec` to the
canonical sorted root lists, so future Bezoutian work can avoid arbitrary
root-list witnesses.  Its statement is:

```lean
lemma prec_iff_sorted_roots
    {p q : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits) :
    Prec p q ↔
      let sp := p.roots.sort (· ≤ ·)
      let sq := q.roots.sort (· ≤ ·)
      ((sp.length + 1 = sq.length ∧ ListInterlaces sp sq) ∨
        (sp.length = sq.length ∧ ListAlternates sp sq))
```

It should feed separate same-degree and degree-difference-one Bezoutian
statements formulated directly on canonical sorted root lists.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- `Prec` can be checked on the canonical sorted root lists. -/
lemma prec_iff_sorted_roots {p q : ℝ[X]}
    (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits) :
    Prec p q ↔
      let sp := p.roots.sort (· ≤ ·)
      let sq := q.roots.sort (· ≤ ·)
      ((sp.length + 1 = sq.length ∧ ListInterlaces sp sq) ∨
        (sp.length = sq.length ∧ ListAlternates sp sq)) := by
  constructor
  · intro h
    rcases h with ⟨_, _, ss, rs, hss_sorted, hrs_sorted, hss_roots, hrs_roots, hcase⟩
    have hss_eq : ss = p.roots.sort (· ≤ ·) := by
      exact List.Perm.eq_of_pairwise' hss_sorted (Multiset.pairwise_sort ..)
        (Multiset.coe_eq_coe.mp (by simp [hss_roots]))
    have hrs_eq : rs = q.roots.sort (· ≤ ·) := by
      exact List.Perm.eq_of_pairwise' hrs_sorted (Multiset.pairwise_sort ..)
        (Multiset.coe_eq_coe.mp (by simp [hrs_roots]))
    simpa [hss_eq, hrs_eq] using hcase
  · intro h
    let sp := p.roots.sort (· ≤ ·)
    let sq := q.roots.sort (· ≤ ·)
    change ((sp.length + 1 = sq.length ∧ ListInterlaces sp sq) ∨
      (sp.length = sq.length ∧ ListAlternates sp sq)) at h
    refine ⟨hp, hq, sp, sq, ?_, ?_, ?_, ?_, h⟩
    · exact Multiset.pairwise_sort ..
    · exact Multiset.pairwise_sort ..
    · simp [sp]
    · simp [sq]

/-- In the same-degree case, `Prec` is the canonical sorted-root
`ListAlternates` condition. -/
lemma prec_iff_sorted_roots_alternates {p q : ℝ[X]}
    (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits)
    (hdeg : p.natDegree = q.natDegree) :
    Prec p q ↔ ListAlternates (p.roots.sort (· ≤ ·)) (q.roots.sort (· ≤ ·)) := by
  rw [prec_iff_sorted_roots hp hq]
  let sp := p.roots.sort (· ≤ ·)
  let sq := q.roots.sort (· ≤ ·)
  change ((sp.length + 1 = sq.length ∧ ListInterlaces sp sq) ∨
      (sp.length = sq.length ∧ ListAlternates sp sq)) ↔ ListAlternates sp sq
  have hlen : sp.length = sq.length := by
    simp [sp, sq, Multiset.length_sort, card_roots_of_splits hp.2,
      card_roots_of_splits hq.2, hdeg]
  constructor
  · rintro (⟨hbad, _⟩ | ⟨_, halt⟩)
    · exfalso
      rw [← hlen] at hbad
      exact Nat.succ_ne_self sp.length hbad
    · exact halt
  · intro halt
    exact Or.inr ⟨hlen, halt⟩

/-- In the degree-difference-one case, `Prec` is the canonical sorted-root
`ListInterlaces` condition. -/
lemma prec_iff_sorted_roots_interlaces {p q : ℝ[X]}
    (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits)
    (hdeg : p.natDegree + 1 = q.natDegree) :
    Prec p q ↔ ListInterlaces (p.roots.sort (· ≤ ·)) (q.roots.sort (· ≤ ·)) := by
  rw [prec_iff_sorted_roots hp hq]
  let sp := p.roots.sort (· ≤ ·)
  let sq := q.roots.sort (· ≤ ·)
  change ((sp.length + 1 = sq.length ∧ ListInterlaces sp sq) ∨
      (sp.length = sq.length ∧ ListAlternates sp sq)) ↔ ListInterlaces sp sq
  have hlen : sp.length + 1 = sq.length := by
    simp [sp, sq, Multiset.length_sort, card_roots_of_splits hp.2,
      card_roots_of_splits hq.2, hdeg]
  constructor
  · rintro (⟨_, hint⟩ | ⟨hbad, _⟩)
    · exact hint
    · exfalso
      rw [← hbad] at hlen
      exact Nat.succ_ne_self sp.length hlen
  · intro hint
    exact Or.inl ⟨hlen, hint⟩

/-- Strict differ-by-one interlacing on sorted root lists:
`r₁ < s₁ < r₂ < ... < sₙ₋₁ < rₙ`. -/
def ListStrictInterlaces : List ℝ → List ℝ → Prop
  | [], [] => True
  | [], [_] => True
  | s :: ss, r₁ :: r₂ :: rs => r₁ < s ∧ s < r₂ ∧ ListStrictInterlaces ss (r₂ :: rs)
  | _, _ => False

/-- Strict same-degree alternation on sorted root lists:
`s₁ < r₁ < s₂ < r₂ < ... < sₙ < rₙ`. -/
def ListStrictAlternates : List ℝ → List ℝ → Prop
  | [], [] => True
  | s :: ss, r :: rs => s < r ∧ ListStrictInterlaces ss (r :: rs)
  | _, _ => False

/-- Strict same-degree proper position, stated on canonical sorted root lists. -/
def StrictPrecSameDegree (p q : ℝ[X]) : Prop :=
  (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits) ∧ p.natDegree = q.natDegree ∧
    ListStrictAlternates (p.roots.sort (· ≤ ·)) (q.roots.sort (· ≤ ·))

/-- The `(i,j)` coefficient of the Bezoutian
`(p(X) q(Y) - p(Y) q(X)) / (X - Y)`.

This definition is independent of a matrix size.  Coefficients outside the
degrees of `p` and `q` vanish through `Polynomial.coeff`. -/
def bezoutEntry (p q : ℝ[X]) (i j : ℕ) : ℝ :=
  Finset.sum (Finset.range (min i j + 1)) fun k =>
    p.coeff (i + j + 1 - k) * q.coeff k -
      q.coeff (i + j + 1 - k) * p.coeff k

/-- The `n × n` Bezout matrix attached to two polynomials. -/
def bezoutMatrix (n : ℕ) (p q : ℝ[X]) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => bezoutEntry p q i.1 j.1

lemma bezoutEntry_self (p : ℝ[X]) (i j : ℕ) :
    bezoutEntry p p i j = 0 := by
  simp [bezoutEntry]

lemma bezoutEntry_swap (p q : ℝ[X]) (i j : ℕ) :
    bezoutEntry q p i j = -bezoutEntry p q i j := by
  simp [bezoutEntry]

lemma bezoutEntry_zero_left (p : ℝ[X]) (i j : ℕ) :
    bezoutEntry 0 p i j = 0 := by
  simp [bezoutEntry]

lemma bezoutEntry_comm (p q : ℝ[X]) (i j : ℕ) :
    bezoutEntry p q i j = bezoutEntry p q j i := by
  simp [bezoutEntry, Nat.add_comm, Nat.add_assoc, min_comm]

lemma bezoutMatrix_self (n : ℕ) (p : ℝ[X]) :
    bezoutMatrix n p p = 0 := by
  ext i j
  simp [bezoutMatrix, bezoutEntry_self]

lemma bezoutMatrix_isHermitian (n : ℕ) (p q : ℝ[X]) :
    (bezoutMatrix n p q).IsHermitian := by
  exact Matrix.IsHermitian.ext (by
    intro i j
    simp [bezoutMatrix, bezoutEntry_comm p q i.1 j.1])

lemma bezoutMatrix_zero_posSemidef (p q : ℝ[X]) :
    (bezoutMatrix 0 p q).PosSemidef := by
  exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (bezoutMatrix_isHermitian 0 p q) (by
    intro x
    simp [dotProduct])

lemma bezoutMatrix_swap (n : ℕ) (p q : ℝ[X]) :
    bezoutMatrix n q p = -bezoutMatrix n p q := by
  ext i j
  change bezoutEntry q p i.1 j.1 = -bezoutEntry p q i.1 j.1
  exact bezoutEntry_swap p q i.1 j.1

lemma bezoutEntry_C_mul_C_mul (u v : ℝ) (p q : ℝ[X]) (i j : ℕ) :
    bezoutEntry (C u * p) (C v * q) i j = u * v * bezoutEntry p q i j := by
  unfold bezoutEntry
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  simp [coeff_C_mul]
  ring

lemma bezoutMatrix_C_mul_C_mul (n : ℕ) (u v : ℝ) (p q : ℝ[X]) :
    bezoutMatrix n (C u * p) (C v * q) = (u * v) • bezoutMatrix n p q := by
  ext i j
  simp [bezoutMatrix, bezoutEntry_C_mul_C_mul]

lemma bezoutMatrix_linear_eq_diagonal (a b : ℝ) :
    bezoutMatrix 1 (X + C a) (X + C b) =
      Matrix.diagonal (fun _ : Fin 1 => b - a) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [bezoutMatrix, bezoutEntry, Matrix.diagonal]

lemma bezoutMatrix_linear_posSemidef_one {a b : ℝ} (hab : a ≤ b) :
    (bezoutMatrix 1 (X + C a) (X + C b)).PosSemidef := by
  rw [bezoutMatrix_linear_eq_diagonal]
  exact Matrix.PosSemidef.diagonal (fun _ => sub_nonneg.mpr hab)

lemma not_bezoutMatrix_linear_posSemidef_one_swap {a b : ℝ} (hab : a < b) :
    ¬ (bezoutMatrix 1 (X + C b) (X + C a)).PosSemidef := by
  intro h
  have hdiag :
      0 ≤ (bezoutMatrix 1 (X + C b) (X + C a)) (0 : Fin 1) (0 : Fin 1) :=
    Matrix.PosSemidef.diag_nonneg h
  simp [bezoutMatrix, bezoutEntry] at hdiag
  linarith

/-- Every polynomial of the form `X + C a` is real-rooted. -/
lemma isRealRooted_X_add_C (a : ℝ) : (X + C a : ℝ[X]) ≠ 0 ∧ (X + C a).Splits := by
  simpa [sub_eq_add_neg] using isRealRooted_X_sub_C (-a)

/-- The unique root of `X + C a` is `-a`. -/
lemma roots_X_add_C (a : ℝ) :
    (X + C a : ℝ[X]).roots = {(-a : ℝ)} := by
  rw [show X + C a = X - C (-a) by simp [sub_eq_add_neg], roots_X_sub_C]

/-- Ordered linear factors satisfy the `Prec` orientation predicted by the
positive-semidefinite Bezout matrix orientation. -/
lemma prec_X_add_C_of_le {a b : ℝ} (hab : a ≤ b) :
    Prec (X + C b) (X + C a) := by
  refine ⟨?_, ?_, [(-b : ℝ)], [(-a : ℝ)], ?_, ?_, ?_, ?_, ?_⟩
  · exact isRealRooted_X_add_C b
  · exact isRealRooted_X_add_C a
  · simp
  · simp
  · rw [roots_X_add_C]
    simp
  · rw [roots_X_add_C]
    simp
  · exact Or.inr ⟨by simp, by simp [ListAlternates, ListInterlaces, hab]⟩

/-- The `1 × 1` Bezoutian positive-semidefinite sanity check implies the
corresponding linear `Prec` orientation. -/
lemma prec_of_bezoutMatrix_linear_posSemidef_one {a b : ℝ}
    (h : (bezoutMatrix 1 (X + C a) (X + C b)).PosSemidef) :
    Prec (X + C b) (X + C a) := by
  have hdiag :
      0 ≤ (bezoutMatrix 1 (X + C a) (X + C b)) (0 : Fin 1) (0 : Fin 1) := by
    exact Matrix.PosSemidef.diag_nonneg h
  rw [bezoutMatrix_linear_eq_diagonal] at hdiag
  have hab : a ≤ b := by
    simpa [Matrix.diagonal] using hdiag
  exact prec_X_add_C_of_le hab

/-- The degree-zero endpoint of the Bezoutian characterization. -/
lemma prec_iff_bezoutMatrix_posSemidef_of_isRealRooted_natDegree_zero
    {p q : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits)
    (hp_deg : p.natDegree = 0) (hq_deg : q.natDegree = 0) :
    Prec p q ↔ (bezoutMatrix 0 q p).PosSemidef := by
  constructor
  · intro _
    exact bezoutMatrix_zero_posSemidef q p
  · intro _
    rw [prec_iff_sorted_roots_alternates hp hq (by rw [hp_deg, hq_deg])]
    have hp_nil : p.roots.sort (· ≤ ·) = [] := by
      apply List.length_eq_zero_iff.mp
      simp [Multiset.length_sort, card_roots_of_splits hp.2, hp_deg]
    have hq_nil : q.roots.sort (· ≤ ·) = [] := by
      apply List.length_eq_zero_iff.mp
      simp [Multiset.length_sort, card_roots_of_splits hq.2, hq_deg]
    simp [hp_nil, hq_nil, ListAlternates]

/-- A real-rooted quadratic is a positive/negative scalar multiple of two
linear factors, with the constants ordered in the `X + C a` convention used
below. -/
lemma exists_sorted_linearFactors_of_isRealRooted_natDegree_two {p : ℝ[X]}
    (hp : p ≠ 0 ∧ p.Splits) (hdeg : p.natDegree = 2) :
    ∃ a c : ℝ, a ≤ c ∧ p = C p.leadingCoeff * ((X + C a) * (X + C c)) := by
  have hsplits : p.Splits := hp.2
  have hcard : p.roots.card = 2 := by
    rw [card_roots_of_splits hp.2, hdeg]
  rcases Multiset.card_eq_two.mp hcard with ⟨r, s, hroots⟩
  by_cases hrs : r ≤ s
  · refine ⟨-s, -r, by linarith, ?_⟩
    calc
      p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod := hsplits.eq_prod_roots
      _ = C p.leadingCoeff * ((X + C (-s)) * (X + C (-r))) := by
        rw [hroots]
        simp [sub_eq_add_neg, mul_comm]
  · have hsr : s ≤ r := le_of_not_ge hrs
    refine ⟨-r, -s, by linarith, ?_⟩
    calc
      p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod := hsplits.eq_prod_roots
      _ = C p.leadingCoeff * ((X + C (-r)) * (X + C (-s))) := by
        rw [hroots]
        simp [sub_eq_add_neg]

lemma bezoutMatrix_quadratic_eq_fin_two (a b c d : ℝ) :
    bezoutMatrix 2 ((X + C a) * (X + C c)) ((X + C b) * (X + C d)) =
      !![(a + c) * (b * d) - (b + d) * (a * c), b * d - a * c;
        b * d - a * c, b + d - (a + c)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bezoutMatrix, bezoutEntry, coeff_add, coeff_mul, Finset.antidiagonal,
      Finset.range, coeff_X, coeff_C]

/-- The lower-right diagonal entry gives a necessary sum inequality for a
positive-semidefinite quadratic Bezoutian. -/
lemma sum_le_of_bezoutMatrix_quadratic_posSemidef {a b c d : ℝ}
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
      ((X + C b) * (X + C d))).PosSemidef) :
    a + c ≤ b + d := by
  have hdiag :
      0 ≤ (bezoutMatrix 2 ((X + C a) * (X + C c))
        ((X + C b) * (X + C d))) (1 : Fin 2) (1 : Fin 2) := by
    exact Matrix.PosSemidef.diag_nonneg h
  rw [bezoutMatrix_quadratic_eq_fin_two] at hdiag
  simpa using hdiag

/-- The upper-left diagonal entry gives a second necessary inequality for a
positive-semidefinite quadratic Bezoutian. -/
lemma weighted_const_nonneg_of_bezoutMatrix_quadratic_posSemidef {a b c d : ℝ}
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
      ((X + C b) * (X + C d))).PosSemidef) :
    0 ≤ (a + c) * (b * d) - (b + d) * (a * c) := by
  have hdiag :
      0 ≤ (bezoutMatrix 2 ((X + C a) * (X + C c))
        ((X + C b) * (X + C d))) (0 : Fin 2) (0 : Fin 2) := by
    exact Matrix.PosSemidef.diag_nonneg h
  rw [bezoutMatrix_quadratic_eq_fin_two] at hdiag
  simpa using hdiag

/-- The determinant inequality for a positive-semidefinite `2 × 2` real matrix,
written in entry form. -/
lemma det_nonneg_of_posSemidef_fin_two {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosSemidef) :
    0 ≤ A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  have hdet : 0 ≤ A.det := Matrix.PosSemidef.det_nonneg hA
  simpa [Matrix.det_fin_two] using hdet

/-- The determinant inequality extracted from the closed-form quadratic
Bezoutian. -/
lemma det_nonneg_of_bezoutMatrix_quadratic_posSemidef {a b c d : ℝ}
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
      ((X + C b) * (X + C d))).PosSemidef) :
    0 ≤ ((a + c) * (b * d) - (b + d) * (a * c)) * (b + d - (a + c)) -
      (b * d - a * c) * (b * d - a * c) := by
  have hdet := det_nonneg_of_posSemidef_fin_two h
  rw [bezoutMatrix_quadratic_eq_fin_two] at hdet
  simpa using hdet

/-- The determinant obstruction for the quadratic Bezoutian in fact factors
into the four expected endpoint gaps. -/
lemma det_factor_nonneg_of_bezoutMatrix_quadratic_posSemidef {a b c d : ℝ}
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
      ((X + C b) * (X + C d))).PosSemidef) :
    0 ≤ (a - b) * (a - d) * (b - c) * (c - d) := by
  have hdet := det_nonneg_of_bezoutMatrix_quadratic_posSemidef h
  convert hdet using 1
  ring

/-- A `2 × 2` real symmetric matrix is positive semidefinite if its two
diagonal entries and determinant are nonnegative. -/
lemma posSemidef_fin_two_of_entries {A B C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hdet : 0 ≤ A * C - B * B) :
    (!![A, B; B, C] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact Matrix.IsHermitian.ext (by intro i j; fin_cases i <;> fin_cases j <;> simp)
  · intro x
    by_cases hAz : A = 0
    · have hB : B = 0 := by nlinarith [sq_nonneg B]
      norm_num [dotProduct, Matrix.mulVec, hAz, hB]
      nlinarith [mul_nonneg hC (sq_nonneg (x 1))]
    · have hApos : 0 < A := lt_of_le_of_ne' hA hAz
      have hmain :
          0 ≤ A * (x 0 + B / A * x 1) ^ 2 + (A * C - B * B) / A * (x 1) ^ 2 := by
        exact add_nonneg (mul_nonneg hA (sq_nonneg _))
          (mul_nonneg (div_nonneg hdet (le_of_lt hApos)) (sq_nonneg _))
      norm_num [dotProduct, Matrix.mulVec]
      field_simp [ne_of_gt hApos] at hmain
      nlinarith

/-- For ordered quadratic factors, positive semidefiniteness of the Bezoutian
extracts the expected interleaving inequalities on the constants. -/
lemma const_interleaves_of_bezoutMatrix_quadratic_posSemidef {a b c d : ℝ}
    (hac : a ≤ c) (hbd : b ≤ d)
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
      ((X + C b) * (X + C d))).PosSemidef) :
    a ≤ b ∧ b ≤ c ∧ c ≤ d := by
  have hsum := sum_le_of_bezoutMatrix_quadratic_posSemidef h
  have hdet := det_factor_nonneg_of_bezoutMatrix_quadratic_posSemidef h
  have hab : a ≤ b := by
    by_contra hnot
    have hba : b < a := lt_of_not_ge hnot
    have hcd : c < d := by nlinarith
    have had : a < d := lt_of_le_of_lt hac hcd
    have hbc : b < c := lt_of_lt_of_le hba hac
    have h1 : (a - b) * (a - d) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hba) (sub_neg.mpr had)
    have h2 : 0 < (b - c) * (c - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hbc) (sub_neg.mpr hcd)
    have hprod : ((a - b) * (a - d)) * ((b - c) * (c - d)) < 0 :=
      mul_neg_of_neg_of_pos h1 h2
    nlinarith
  have hbc : b ≤ c := by
    by_contra hnot
    have hcb : c < b := lt_of_not_ge hnot
    have hab' : a < b := lt_of_le_of_lt hac hcb
    have hcd : c < d := lt_of_lt_of_le hcb hbd
    have had : a < d := lt_of_le_of_lt hac hcd
    have h1 : 0 < (a - b) * (a - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hab') (sub_neg.mpr had)
    have h2 : (b - c) * (c - d) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hcb) (sub_neg.mpr hcd)
    have hprod : ((a - b) * (a - d)) * ((b - c) * (c - d)) < 0 :=
      mul_neg_of_pos_of_neg h1 h2
    nlinarith
  have hcd : c ≤ d := by
    by_contra hnot
    have hdc : d < c := lt_of_not_ge hnot
    have hab' : a < b := by nlinarith
    have had : a < d := lt_of_lt_of_le hab' hbd
    have hbc' : b < c := lt_of_le_of_lt hbd hdc
    have h1 : 0 < (a - b) * (a - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hab') (sub_neg.mpr had)
    have h2 : (b - c) * (c - d) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hbc') (sub_pos.mpr hdc)
    have hprod : ((a - b) * (a - d)) * ((b - c) * (c - d)) < 0 :=
      mul_neg_of_pos_of_neg h1 h2
    nlinarith
  exact ⟨hab, hbc, hcd⟩

/-- Ordered constants give the positive-semidefinite quadratic Bezoutian. -/
lemma bezoutMatrix_quadratic_posSemidef_two_of_const_interleaves {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (bezoutMatrix 2 ((X + C a) * (X + C c))
      ((X + C b) * (X + C d))).PosSemidef := by
  rw [bezoutMatrix_quadratic_eq_fin_two]
  refine posSemidef_fin_two_of_entries ?_ ?_ ?_
  · have hAeq : (a + c) * (b * d) - (b + d) * (a * c) =
        (b - a) * c ^ 2 + (d - c) * (b ^ 2 + (b - a) * (c - b)) := by
      ring
    rw [hAeq]
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hcb : 0 ≤ c - b := sub_nonneg.mpr hbc
    have hdc : 0 ≤ d - c := sub_nonneg.mpr hcd
    exact add_nonneg (mul_nonneg hba (sq_nonneg c))
      (mul_nonneg hdc (add_nonneg (sq_nonneg b) (mul_nonneg hba hcb)))
  · nlinarith
  · have hdet_eq :
        ((a + c) * (b * d) - (b + d) * (a * c)) * (b + d - (a + c)) -
          (b * d - a * c) * (b * d - a * c) =
        (b - a) * (c - b) * (d - c) * (d - a) := by
      ring
    rw [hdet_eq]
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hcb : 0 ≤ c - b := sub_nonneg.mpr hbc
    have hdc : 0 ≤ d - c := sub_nonneg.mpr hcd
    have hda : 0 ≤ d - a := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg hba hcb) hdc) hda

lemma bezoutMatrix_quadratic_commonFactor_eq_vecMulVec (a b c : ℝ) :
    bezoutMatrix 2 ((X + C a) * (X + C c)) ((X + C b) * (X + C c)) =
      (b - a) • Matrix.vecMulVec (fun i : Fin 2 => if i = 0 then c else 1)
        (star (fun i : Fin 2 => if i = 0 then c else 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bezoutMatrix, bezoutEntry, Matrix.vecMulVec, coeff_add, coeff_mul,
      Finset.antidiagonal, Finset.range, coeff_X, coeff_C]
  all_goals ring

lemma bezoutMatrix_quadratic_commonFactor_posSemidef_two {a b c : ℝ}
    (hab : a ≤ b) :
    (bezoutMatrix 2 ((X + C a) * (X + C c))
      ((X + C b) * (X + C c))).PosSemidef := by
  rw [bezoutMatrix_quadratic_commonFactor_eq_vecMulVec]
  exact (Matrix.posSemidef_vecMulVec_self_star
    (fun i : Fin 2 => if i = 0 then c else 1)).smul (sub_nonneg.mpr hab)

lemma not_bezoutMatrix_quadratic_commonFactor_posSemidef_two_swap {a b c : ℝ}
    (hab : a < b) :
    ¬ (bezoutMatrix 2 ((X + C b) * (X + C c))
      ((X + C a) * (X + C c))).PosSemidef := by
  intro h
  have hdiag :
      0 ≤ (bezoutMatrix 2 ((X + C b) * (X + C c))
        ((X + C a) * (X + C c))) (1 : Fin 2) (1 : Fin 2) :=
    Matrix.PosSemidef.diag_nonneg h
  rw [bezoutMatrix_quadratic_commonFactor_eq_vecMulVec] at hdiag
  simp [Matrix.vecMulVec] at hdiag
  linarith

/-- Multiplying the ordered linear `Prec` example by a common linear factor
preserves the expected Bezoutian orientation in degree two. -/
lemma prec_quadratic_commonFactor_of_le {a b c : ℝ} (hab : a ≤ b) :
    Prec (((X + C b) * (X + C c)) : ℝ[X])
      (((X + C a) * (X + C c)) : ℝ[X]) := by
  have hb : (X + C b : ℝ[X]) ≠ 0 ∧ (X + C b).Splits := isRealRooted_X_add_C b
  have hc : (X + C c : ℝ[X]) ≠ 0 ∧ (X + C c).Splits := isRealRooted_X_add_C c
  have ha : (X + C a : ℝ[X]) ≠ 0 ∧ (X + C a).Splits := isRealRooted_X_add_C a
  by_cases hca : c ≤ a
  · refine ⟨isRealRooted_mul hb hc, isRealRooted_mul ha hc,
      [(-b : ℝ), -c], [(-a : ℝ), -c], ?_, ?_, ?_, ?_, ?_⟩
    · simp
      linarith
    · simp
      linarith
    · rw [roots_mul (mul_ne_zero hb.1 hc.1), roots_X_add_C, roots_X_add_C]
      rfl
    · rw [roots_mul (mul_ne_zero ha.1 hc.1), roots_X_add_C, roots_X_add_C]
      rfl
    · exact Or.inr ⟨by simp, by
        simp [ListAlternates, ListInterlaces]
        constructor <;> linarith⟩
  · by_cases hcb : c ≤ b
    · have hac : a ≤ c := le_of_not_ge hca
      refine ⟨isRealRooted_mul hb hc, isRealRooted_mul ha hc,
        [(-b : ℝ), -c], [(-c : ℝ), -a], ?_, ?_, ?_, ?_, ?_⟩
      · simp
        linarith
      · simp
        linarith
      · rw [roots_mul (mul_ne_zero hb.1 hc.1), roots_X_add_C, roots_X_add_C]
        rfl
      · rw [roots_mul (mul_ne_zero ha.1 hc.1), roots_X_add_C, roots_X_add_C,
          Multiset.add_comm]
        rfl
      · exact Or.inr ⟨by simp, by
          simp [ListAlternates, ListInterlaces]
          constructor <;> linarith⟩
    · have hbc : b ≤ c := le_of_not_ge hcb
      refine ⟨isRealRooted_mul hb hc, isRealRooted_mul ha hc,
        [(-c : ℝ), -b], [(-c : ℝ), -a], ?_, ?_, ?_, ?_, ?_⟩
      · simp
        linarith
      · simp
        linarith
      · rw [roots_mul (mul_ne_zero hb.1 hc.1), roots_X_add_C, roots_X_add_C,
          Multiset.add_comm]
        rfl
      · rw [roots_mul (mul_ne_zero ha.1 hc.1), roots_X_add_C, roots_X_add_C,
          Multiset.add_comm]
        rfl
      · exact Or.inr ⟨by simp, by
          simp [ListAlternates, ListInterlaces]
          constructor <;> linarith⟩

/-- The common-factor `2 × 2` Bezoutian positive-semidefinite sanity check
implies the corresponding quadratic `Prec` orientation. -/
lemma prec_of_bezoutMatrix_quadratic_commonFactor_posSemidef_two {a b c : ℝ}
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
      ((X + C b) * (X + C c))).PosSemidef) :
    Prec (((X + C b) * (X + C c)) : ℝ[X])
      (((X + C a) * (X + C c)) : ℝ[X]) := by
  have hdiag :
      0 ≤ (bezoutMatrix 2 ((X + C a) * (X + C c))
        ((X + C b) * (X + C c))) (1 : Fin 2) (1 : Fin 2) := by
    exact Matrix.PosSemidef.diag_nonneg h
  rw [bezoutMatrix_quadratic_commonFactor_eq_vecMulVec] at hdiag
  have hab : a ≤ b := by
    simp [Matrix.vecMulVec] at hdiag
    linarith
  exact prec_quadratic_commonFactor_of_le hab

lemma bezoutMatrix_quadratic_nonCommon_eq_decomp :
    bezoutMatrix 2 ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))
        ((X + C (2 : ℝ)) * (X + C (4 : ℝ))) =
      ((1 / 2 : ℝ) • Matrix.vecMulVec (fun i : Fin 2 => if i = 0 then (5 : ℝ) else 2)
        (star (fun i : Fin 2 => if i = 0 then (5 : ℝ) else 2))) +
        Matrix.diagonal (fun i : Fin 2 => if i = 0 then (3 / 2 : ℝ) else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bezoutMatrix, bezoutEntry, Matrix.vecMulVec, Matrix.diagonal, coeff_add,
      coeff_mul, Finset.antidiagonal, Finset.range, coeff_X, coeff_C, coeff_one]

lemma bezoutMatrix_quadratic_nonCommon_posSemidef_two :
    (bezoutMatrix 2 ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))
      ((X + C (2 : ℝ)) * (X + C (4 : ℝ)))).PosSemidef := by
  rw [bezoutMatrix_quadratic_nonCommon_eq_decomp]
  apply Matrix.PosSemidef.add
  · exact (Matrix.posSemidef_vecMulVec_self_star
      (fun i : Fin 2 => if i = 0 then (5 : ℝ) else 2)).smul (by norm_num)
  · exact Matrix.PosSemidef.diagonal (by intro i; fin_cases i <;> norm_num)

lemma not_bezoutMatrix_quadratic_nonCommon_posSemidef_two_swap :
    ¬ (bezoutMatrix 2 ((X + C (2 : ℝ)) * (X + C (4 : ℝ)))
      ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))).PosSemidef := by
  intro h
  have hdiag :
      0 ≤ (bezoutMatrix 2 ((X + C (2 : ℝ)) * (X + C (4 : ℝ)))
        ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))) (1 : Fin 2) (1 : Fin 2) :=
    Matrix.PosSemidef.diag_nonneg h
  norm_num [bezoutMatrix, bezoutEntry, coeff_add, coeff_mul, Finset.antidiagonal,
    Finset.range, coeff_X, coeff_C, coeff_one] at hdiag

/-- A nested non-common root pattern fails positive semidefiniteness; this is
the first place where diagonal inequalities alone are not enough. -/
lemma not_bezoutMatrix_quadratic_nested_posSemidef_two :
    ¬ (bezoutMatrix 2 ((X + C (1 : ℝ)) * (X + C (4 : ℝ)))
      ((X + C (2 : ℝ)) * (X + C (3 : ℝ)))).PosSemidef := by
  intro h
  have hquad := Matrix.PosSemidef.dotProduct_mulVec_nonneg h ![(1 : ℝ), -3]
  rw [bezoutMatrix_quadratic_eq_fin_two] at hquad
  norm_num [dotProduct, Matrix.mulVec] at hquad

/-- If four linear-factor constants interleave as `a ≤ b ≤ c ≤ d`, then the
corresponding quadratic factors satisfy the expected `Prec` orientation. -/
lemma prec_quadratic_of_const_interleaves {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    Prec (((X + C b) * (X + C d)) : ℝ[X])
      (((X + C a) * (X + C c)) : ℝ[X]) := by
  have ha : (X + C a : ℝ[X]) ≠ 0 ∧ (X + C a).Splits := isRealRooted_X_add_C a
  have hb : (X + C b : ℝ[X]) ≠ 0 ∧ (X + C b).Splits := isRealRooted_X_add_C b
  have hc : (X + C c : ℝ[X]) ≠ 0 ∧ (X + C c).Splits := isRealRooted_X_add_C c
  have hd : (X + C d : ℝ[X]) ≠ 0 ∧ (X + C d).Splits := isRealRooted_X_add_C d
  refine ⟨isRealRooted_mul hb hd, isRealRooted_mul ha hc,
    [(-d : ℝ), -b], [(-c : ℝ), -a], ?_, ?_, ?_, ?_, ?_⟩
  · simp
    linarith
  · simp
    linarith
  · rw [roots_mul (mul_ne_zero hb.1 hd.1), roots_X_add_C, roots_X_add_C,
      Multiset.add_comm]
    rfl
  · rw [roots_mul (mul_ne_zero ha.1 hc.1), roots_X_add_C, roots_X_add_C,
      Multiset.add_comm]
    rfl
  · exact Or.inr ⟨by simp, by
      simp [ListAlternates, ListInterlaces]
      constructor
      · linarith
      · constructor <;> linarith⟩

/-- A sorted two-element list whose multiset is a sorted pair is the expected
ordered list. -/
lemma sorted_pair_eq_of_pairwise_of_multiset_eq_pair {b d x y : ℝ} (hbd : b ≤ d)
    (hxy : [x, y].Pairwise (· ≤ ·))
    (h : (↑[x, y] : Multiset ℝ) = ({-b, -d} : Multiset ℝ)) :
    x = -d ∧ y = -b := by
  have hperm : [x, y].Perm [-d, -b] := by
    apply Multiset.coe_eq_coe.mp
    rw [h]
    exact Multiset.pair_comm (-b) (-d)
  have hsorted : [-d, -b].Pairwise (· ≤ ·) := by
    simp
    linarith
  have hlist : [x, y] = [-d, -b] := List.Perm.eq_of_pairwise' hxy hsorted hperm
  simpa using hlist

/-- For sorted quadratic linear-factor products, `Prec` is equivalent to the
expected interleaving inequalities on the constants. -/
lemma const_interleaves_of_prec_quadratic {a b c d : ℝ} (hac : a ≤ c) (hbd : b ≤ d)
    (h : Prec (((X + C b) * (X + C d)) : ℝ[X])
      (((X + C a) * (X + C c)) : ℝ[X])) :
    a ≤ b ∧ b ≤ c ∧ c ≤ d := by
  rcases h with ⟨_, _, ss, rs, hss_sorted, hrs_sorted, hss_roots, hrs_roots, hcase⟩
  have hp_roots_card : (((X + C b) * (X + C d)) : ℝ[X]).roots.card = 2 := by
    rw [roots_mul (mul_ne_zero (isRealRooted_X_add_C b).1 (isRealRooted_X_add_C d).1),
      roots_X_add_C, roots_X_add_C]
    simp
  have hq_roots_card : (((X + C a) * (X + C c)) : ℝ[X]).roots.card = 2 := by
    rw [roots_mul (mul_ne_zero (isRealRooted_X_add_C a).1 (isRealRooted_X_add_C c).1),
      roots_X_add_C, roots_X_add_C]
    simp
  have hss_len : ss.length = 2 := by
    have hcard := congrArg Multiset.card hss_roots
    simpa [hp_roots_card] using hcard
  have hrs_len : rs.length = 2 := by
    have hcard := congrArg Multiset.card hrs_roots
    simpa [hq_roots_card] using hcard
  rcases List.length_eq_two.mp hss_len with ⟨x, y, rfl⟩
  rcases List.length_eq_two.mp hrs_len with ⟨z, w, rfl⟩
  have hss_pair : (↑[x, y] : Multiset ℝ) = ({-b, -d} : Multiset ℝ) := by
    simpa [roots_mul (mul_ne_zero (isRealRooted_X_add_C b).1 (isRealRooted_X_add_C d).1),
      roots_X_add_C] using hss_roots
  have hrs_pair : (↑[z, w] : Multiset ℝ) = ({-a, -c} : Multiset ℝ) := by
    simpa [roots_mul (mul_ne_zero (isRealRooted_X_add_C a).1 (isRealRooted_X_add_C c).1),
      roots_X_add_C] using hrs_roots
  rcases sorted_pair_eq_of_pairwise_of_multiset_eq_pair hbd hss_sorted hss_pair with
    ⟨rfl, rfl⟩
  rcases sorted_pair_eq_of_pairwise_of_multiset_eq_pair hac hrs_sorted hrs_pair with
    ⟨rfl, rfl⟩
  rcases hcase with ⟨hlen, _⟩ | ⟨_, halt⟩
  · simp at hlen
  · simp [ListAlternates, ListInterlaces] at halt
    constructor
    · linarith
    · constructor <;> linarith

/-- The positive-semidefinite quadratic Bezoutian gives the expected `Prec`
orientation for ordered non-common quadratic factors. -/
lemma prec_of_bezoutMatrix_quadratic_posSemidef_two {a b c d : ℝ}
    (hac : a ≤ c) (hbd : b ≤ d)
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
      ((X + C b) * (X + C d))).PosSemidef) :
    Prec (((X + C b) * (X + C d)) : ℝ[X])
      (((X + C a) * (X + C c)) : ℝ[X]) := by
  rcases const_interleaves_of_bezoutMatrix_quadratic_posSemidef hac hbd h with
    ⟨hab, hbc, hcd⟩
  exact prec_quadratic_of_const_interleaves hab hbc hcd

/-- The degree-two case of the Bezoutian-to-`Prec` direction for arbitrary
real-rooted quadratics with positive leading coefficients. -/
lemma prec_of_bezoutMatrix_posSemidef_of_isRealRooted_quadratic
    {p q : ℝ[X]}
    (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2)
    (h : (bezoutMatrix 2 q p).PosSemidef) :
    Prec p q := by
  obtain ⟨b, d, hbd, hp_eq⟩ :=
    exists_sorted_linearFactors_of_isRealRooted_natDegree_two hp hp_deg
  obtain ⟨a, c, hac, hq_eq⟩ :=
    exists_sorted_linearFactors_of_isRealRooted_natDegree_two hq hq_deg
  let mp : ℝ[X] := (X + C b) * (X + C d)
  let mq : ℝ[X] := (X + C a) * (X + C c)
  let u : ℝ := q.leadingCoeff
  let v : ℝ := p.leadingCoeff
  have hu : 0 < u := by simpa [u, HasPosLeadingCoeff] using hq_pos
  have hv : 0 < v := by simpa [v, HasPosLeadingCoeff] using hp_pos
  have hq_eq' : q = C u * mq := by simpa [u, mq] using hq_eq
  have hp_eq' : p = C v * mp := by simpa [v, mp] using hp_eq
  have hscaled : ((u * v) • bezoutMatrix 2 mq mp).PosSemidef := by
    have h' : (bezoutMatrix 2 (C u * mq) (C v * mp)).PosSemidef := by
      simpa [hq_eq', hp_eq'] using h
    simpa [bezoutMatrix_C_mul_C_mul] using h'
  have hmonic : (bezoutMatrix 2 mq mp).PosSemidef := by
    have huv : 0 < u * v := mul_pos hu hv
    have hnonneg : 0 ≤ (u * v)⁻¹ := inv_nonneg.mpr (le_of_lt huv)
    have htmp := hscaled.smul hnonneg
    have hscalar : v⁻¹ * u⁻¹ * (u * v) = 1 := by
      field_simp [ne_of_gt hu, ne_of_gt hv]
    simpa [smul_smul, hscalar] using htmp
  have hprec_monic : Prec mp mq := by
    simpa [mp, mq] using prec_of_bezoutMatrix_quadratic_posSemidef_two hac hbd hmonic
  have hprec_scaled : Prec (C v * mp) (C u * mq) :=
    prec_C_mul_right (prec_C_mul_left hprec_monic (ne_of_gt hv)) (ne_of_gt hu)
  simpa [hp_eq', hq_eq'] using hprec_scaled

/-- The degree-two case of the `Prec`-to-Bezoutian direction for arbitrary
real-rooted quadratics with positive leading coefficients. -/
lemma bezoutMatrix_posSemidef_of_prec_quadratic
    {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2)
    (hprec : Prec p q) :
    (bezoutMatrix 2 q p).PosSemidef := by
  obtain ⟨b, d, hbd, hp_eq⟩ :=
    exists_sorted_linearFactors_of_isRealRooted_natDegree_two hprec.1 hp_deg
  obtain ⟨a, c, hac, hq_eq⟩ :=
    exists_sorted_linearFactors_of_isRealRooted_natDegree_two hprec.2.1 hq_deg
  let mp : ℝ[X] := (X + C b) * (X + C d)
  let mq : ℝ[X] := (X + C a) * (X + C c)
  let u : ℝ := q.leadingCoeff
  let v : ℝ := p.leadingCoeff
  have hu : 0 < u := by simpa [u, HasPosLeadingCoeff] using hq_pos
  have hv : 0 < v := by simpa [v, HasPosLeadingCoeff] using hp_pos
  have hq_eq' : q = C u * mq := by simpa [u, mq] using hq_eq
  have hp_eq' : p = C v * mp := by simpa [v, mp] using hp_eq
  have hprec_monic : Prec mp mq := by
    have h1 : Prec (C v⁻¹ * p) q :=
      prec_C_mul_left hprec (inv_ne_zero (ne_of_gt hv))
    have hleft : C v⁻¹ * p = mp := by
      rw [hp_eq']
      rw [← mul_assoc, ← C_mul]
      simp [inv_mul_cancel₀ (ne_of_gt hv)]
    have h2 : Prec mp q := by
      rwa [hleft] at h1
    have h3 : Prec mp (C u⁻¹ * q) :=
      prec_C_mul_right h2 (inv_ne_zero (ne_of_gt hu))
    have hright : C u⁻¹ * q = mq := by
      rw [hq_eq']
      rw [← mul_assoc, ← C_mul]
      simp [inv_mul_cancel₀ (ne_of_gt hu)]
    rwa [hright] at h3
  rcases const_interleaves_of_prec_quadratic hac hbd hprec_monic with ⟨hab, hbc, hcd⟩
  have hmonic : (bezoutMatrix 2 mq mp).PosSemidef := by
    simpa [mq, mp] using bezoutMatrix_quadratic_posSemidef_two_of_const_interleaves
      hab hbc hcd
  have hscaled : ((u * v) • bezoutMatrix 2 mq mp).PosSemidef :=
    hmonic.smul (mul_nonneg (le_of_lt hu) (le_of_lt hv))
  simpa [hq_eq', hp_eq', bezoutMatrix_C_mul_C_mul] using hscaled

/-- Complete degree-two model theorem for real-rooted quadratics with positive
leading coefficients. -/
lemma prec_iff_bezoutMatrix_posSemidef_of_isRealRooted_quadratic
    {p q : ℝ[X]}
    (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2) :
    Prec p q ↔ (bezoutMatrix 2 q p).PosSemidef := by
  constructor
  · exact bezoutMatrix_posSemidef_of_prec_quadratic hp_pos hq_pos hp_deg hq_deg
  · exact prec_of_bezoutMatrix_posSemidef_of_isRealRooted_quadratic
      hp hq hp_pos hq_pos hp_deg hq_deg

/-- The `Prec` side of the concrete non-common-factor quadratic Bezoutian
orientation example. -/
lemma prec_quadratic_nonCommon_example :
    Prec (((X + C (2 : ℝ)) * (X + C (4 : ℝ))) : ℝ[X])
      (((X + C (1 : ℝ)) * (X + C (3 : ℝ))) : ℝ[X]) := by
  exact prec_quadratic_of_const_interleaves (by norm_num) (by norm_num) (by norm_num)

/--
Strict same-degree Bezoutian characterization.

The orientation is chosen so that `StrictPrecSameDegree p q` corresponds to
positive definiteness of `bezoutMatrix n q p`.  This is the intended main
Bezoutian theorem: it avoids the common-factor and multiple-root degeneracies
that belong to a separate positive-semidefinite/gcd-reduced generalization.
It is recorded with `proof_wanted` instead of `sorry`.
-/
proof_wanted strictPrecSameDegree_iff_bezoutMatrix_posDef
    {p q : ℝ[X]} {n : ℕ}
    (_hp_pos : HasPosLeadingCoeff p) (_hq_pos : HasPosLeadingCoeff q)
    (_hp_deg : p.natDegree = n) (_hq_deg : q.natDegree = n) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix n q p).PosDef

end RealRooted
