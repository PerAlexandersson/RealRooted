import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Mathlib.Data.List.Interleave

/-!
# Bezout matrices and interlacing

This file records the Bezout-matrix characterization of strict same-degree interlacing.

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

-/

open Polynomial Matrix

noncomputable section

namespace RealRooted

private lemma interleaves_reverse_of_interlaced_left :
    ∀ {ss rs : List ℝ} (h : ss.length + 1 = rs.length)
      (hint : ∀ (i : Fin ss.length) (j : Fin rs.length), i.1 + 1 = j.1 → ss[i.1] < rs[j.1])
      (hint' : ∀ (i : Fin rs.length) (j : Fin ss.length), i.1 < j.1 + 1 → rs[i.1] < ss[j.1]),
      List.Interleaves (· > ·) ss.reverse rs.reverse := by
  intro ss
  induction ss with
  | nil =>
    intro rs h _ _
    rcases rs with _ | ⟨r, _ | ⟨r₂, rs⟩⟩
    · simp
    · simp
    · simp at h
  | cons s ss ih =>
  intro rs h hint hint'
  rcases rs with _ | ⟨r₁, _ | ⟨r₂, rs⟩⟩
  · simp at h
  · simp at h
  have h_len : ss.length + 1 = (r₂ :: rs).length := by
    simp only [List.length_cons] at h ⊢
    lia
  rw [List.reverse_cons, List.reverse_cons, List.reverse_cons,
    List.interleaves_append_singleton_append_singleton_of_length_eq_length_add_one
      (by simpa using h_len),
    List.interleaves_append_singleton_append_singleton_of_length_eq_length
      (by simpa using h_len), ← List.reverse_cons]
  refine ⟨hint' ⟨0, by simp⟩ ⟨0, by simp⟩ (by simp), hint ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp),
    ih h_len ?_ ?_⟩
  · intro i j hij
    have := hint ⟨i.1 + 1, by simp⟩
      ⟨j.1 + 1, by rw [List.length_cons (a := r₁)]; lia⟩ (by lia)
    rwa [List.getElem_cons_succ, List.getElem_cons_succ] at this
  · intro i j hij
    have := hint' ⟨i.1 + 1, by rw [List.length_cons (a := r₁)]; lia⟩
      ⟨j.1 + 1, by simp⟩ (by lia)
    simp_all

private lemma interleaves_reverse_of_interlaced :
    ∀ {ss rs : List ℝ} (h : ss.length = rs.length)
      (hint : ∀ (k : Fin ss.length), ss[k.1] < rs[k.1])
      (hint' : ∀ (i j : Fin ss.length), i.1 < j.1 → rs[i.1] < ss[j.1]),
      List.Interleaves (· > ·) ss.reverse rs.reverse := by
  intro ss
  induction ss with
  | nil =>
    intro rs h _ _
    rcases rs with _ | ⟨r, rs⟩
    · simp
    · simp at h
  | cons s ss ih =>
  intro rs h hint hint'
  rcases rs with _ | ⟨r, rs⟩
  · simp at h
  have h_len : ss.length = rs.length := by
    simp only [List.length_cons] at h ⊢
    lia
  rw [List.reverse_cons, List.reverse_cons,
    List.interleaves_append_singleton_append_singleton_of_length_eq_length
      (by simpa using h_len), ← List.reverse_cons]
  refine ⟨hint ⟨0, by simp⟩,
          interleaves_reverse_of_interlaced_left (by simp [h_len]) ?_ ?_⟩
  · intro i j hij
    rcases i with ⟨i_val, hi⟩
    rcases j with ⟨_ | j_val, hj⟩
    · lia
    · have h_eq : i_val = j_val := by lia
      subst h_eq
      have := hint ⟨i_val + 1, by lia⟩
      simp_all
  · intro i j hij
    rcases i with ⟨_ | i_val, hi⟩
    · rcases j with ⟨j_val, hj⟩
      exact hint' ⟨0, h.symm ▸ hi⟩
        ⟨j_val + 1, by rw [List.length_cons]; lia⟩ (by lia)
    · rcases j with ⟨j_val, hj⟩
      exact hint' ⟨i_val + 1, h.symm ▸ hi⟩
        ⟨j_val + 1, by rw [List.length_cons]; lia⟩ hij

private lemma List.Interleaves.ofFn {n : ℕ}
    (s r : Fin n → ℝ)
    (hint : ∀ k : Fin n, s k < r k)
    (hint' : ∀ (i j : Fin n), i < j → r i < s j) :
    List.Interleaves (· > ·) (List.ofFn s).reverse (List.ofFn r).reverse := by
  have h_len : (List.ofFn s).length = (List.ofFn r).length := by simp
  refine interleaves_reverse_of_interlaced h_len ?_ ?_ <;> simp_all

private lemma interlaced_of_interleaves_reverse_left :
    ∀ {ss rs : List ℝ} (h : ss.length + 1 = rs.length)
      (_ : List.Interleaves (· > ·) ss.reverse rs.reverse),
      (∀ (i : Fin ss.length) (j : Fin rs.length), i.1 + 1 = j.1 → ss[i.1] < rs[j.1]) ∧
      (∀ (i : Fin rs.length) (j : Fin ss.length), i.1 < j.1 + 1 → rs[i.1] < ss[j.1]) := by
  intro ss
  induction ss with
  | nil =>
    simp
  | cons s ss ih =>
  intro rs h h_inter
  rcases rs with _ | ⟨r₁, _ | ⟨r₂, rs⟩⟩
  · simp
  · simp at h
  have h_len : ss.length + 1 = (r₂ :: rs).length := by simp_all
  rw [List.reverse_cons, List.reverse_cons, List.reverse_cons,
    List.interleaves_append_singleton_append_singleton_of_length_eq_length_add_one
      (by simpa using h_len),
    List.interleaves_append_singleton_append_singleton_of_length_eq_length
      (by simpa using h_len), ← List.reverse_cons] at h_inter
  obtain ⟨hr1s, hsr2, h_inter_tail⟩ := h_inter
  have h_tail := ih h_len h_inter_tail
  constructor
  · intro i j hij
    rcases i with ⟨_ | i_val, hi⟩
    · grind
    · rcases j with ⟨_ | j_val, hj⟩
      · lia
      · have h_hint := h_tail.1 ⟨i_val, by grind⟩
          ⟨j_val, by rw [List.length_cons] at hj; lia⟩ (by lia)
        simp_all
  · intro i j hij
    rcases i with ⟨_ | i_val, hi⟩
    · rcases j with ⟨_ | j_val, hj⟩
      · grind
      · have h_hint := h_tail.2 ⟨0, by lia⟩
          ⟨j_val, by grind⟩ (by lia)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, gt_iff_lt] at h_hint ⊢
        exact lt_trans hr1s (lt_trans hsr2 h_hint)
    · rcases j with ⟨_ | j_val, hj⟩
      · lia
      · have h_hint := h_tail.2 ⟨i_val, by grind⟩
          ⟨j_val, by grind⟩ (by lia)
        simp_all

private lemma interlaced_of_interleaves_reverse :
    ∀ {ss rs : List ℝ} (h : ss.length = rs.length)
      (_ : List.Interleaves (· > ·) ss.reverse rs.reverse),
      (∀ (k : Fin ss.length), ss[k.1] < rs[k.1]) ∧
      (∀ (i j : Fin ss.length), i.1 < j.1 → rs[i.1] < ss[j.1]) := by
  intro ss
  induction ss with
  | nil =>
    simp
  | cons s ss ih =>
  intro rs h h_inter
  rcases rs with _ | ⟨r, rs⟩
  · simp at h
  have h_len : ss.length = rs.length := by simp_all
  rw [List.reverse_cons, List.reverse_cons,
    List.interleaves_append_singleton_append_singleton_of_length_eq_length
      (by simpa using h_len), ← List.reverse_cons] at h_inter
  obtain ⟨hsr, h_inter_tail⟩ := h_inter
  have h_tail := interlaced_of_interleaves_reverse_left
    (by simp_all) h_inter_tail
  constructor
  · intro k
    rcases k with ⟨_ | k_val, hk⟩
    · grind
    · have h_hint := h_tail.1 ⟨k_val, by simp_all⟩
        ⟨k_val + 1, by lia⟩ (by lia)
      simp_all
  · intro i j hij
    rcases i with ⟨_ | i_val, hi⟩
    · rcases j with ⟨_ | j_val, hj⟩
      · lia
      · have h_hint := h_tail.2 ⟨0, by lia⟩
          ⟨j_val, by grind⟩ (by lia)
        simp_all
    · rcases j with ⟨_ | j_val, hj⟩
      · lia
      · have h_hint := h_tail.2 ⟨i_val + 1, by lia⟩
          ⟨j_val, by grind⟩ (by lia)
        simp_all

/-- Strict same-degree proper position, stated on canonical sorted root lists. -/
def StrictPrecSameDegree (p q : ℝ[X]) : Prop :=
  (p ≠ 0 ∧ p.Splits) ∧ (q ≠ 0 ∧ q.Splits) ∧ p.natDegree = q.natDegree ∧
    List.Interleaves (· > ·) (p.roots.sort (· ≤ ·)).reverse (q.roots.sort (· ≤ ·)).reverse

lemma StrictPrecSameDegree.C_mul_C_mul {p q : ℝ[X]} (h : StrictPrecSameDegree p q)
    {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    StrictPrecSameDegree (C u * p) (C v * q) := by
  obtain ⟨hp, hq, hdeg, halt⟩ := h
  refine ⟨isRealRooted_C_mul hp.1 hp.2 hu, isRealRooted_C_mul hq.1 hq.2 hv, ?_, ?_⟩
  · exact (natDegree_C_mul hu).trans (hdeg.trans (natDegree_C_mul hv).symm)
  · simp_all

lemma StrictPrecSameDegree.C_mul_C_mul_iff {p q : ℝ[X]} {u v : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    StrictPrecSameDegree (C u * p) (C v * q) ↔ StrictPrecSameDegree p q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.C_mul_C_mul hu hv⟩
  have h_mul := h.C_mul_C_mul (inv_ne_zero hu) (inv_ne_zero hv)
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hu, C_1, one_mul,
    ← mul_assoc, ← C_mul, inv_mul_cancel₀ hv, C_1, one_mul] at h_mul

/-- The `(i,j)` coefficient of the Bezoutian
`(p(X) q(Y) - p(Y) q(X)) / (X - Y)`.

This definition is independent of a matrix size.  Coefficients outside the
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
    bezoutEntry p q i j = bezoutEntry p q j i := by
  simp [bezoutEntry, Nat.add_comm, Nat.add_assoc, min_comm]

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
    _ = C u * (X + C (p.coeff 0 / u)) := by
      rw [mul_add, ← C_mul, mul_div_cancel₀ _ hu_pos.ne']

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
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · exact Matrix.IsHermitian.ext (by simp)
  · intro x hx
    have hmain :
        0 < a * (x 0 + b / a * x 1) ^ 2 + (a * c - b * b) / a * (x 1) ^ 2 := by
      by_cases hx1 : x 1 = 0
      · have hx0 : x 0 ≠ 0 := fun h0 ↦ hx <| funext fun i ↦ by fin_cases i <;> assumption
        have hfirst : 0 < a * (x 0 + b / a * x 1) ^ 2 := by
          simp [hx1, mul_pos ha (sq_pos_of_ne_zero hx0)]
        simp_all
      · have hfirst : 0 ≤ a * (x 0 + b / a * x 1) ^ 2 :=
          mul_nonneg ha.le (sq_nonneg _)
        have : 0 < (a * c - b * b) / a * (x 1) ^ 2 :=
          mul_pos (div_pos hdet ha) (sq_pos_of_ne_zero hx1)
        linarith
    norm_num [dotProduct, Matrix.mulVec]
    field_simp [ne_of_gt ha] at hmain
    nlinarith

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
    p.coeff (i + 1) * q.coeff (j + 1) - p.coeff (j + 1) * q.coeff (i + 1) := by
  rcases le_or_gt i j with hij | hij
  · rcases eq_or_lt_of_le hij with rfl | h_lt
    · rw [bezoutEntry.comm p q i (i + 1), sub_self]
      ring
    · have hmin1 : min i (j + 1) = i := min_eq_left (by lia)
      have hmin2 : min (i + 1) j = i + 1 := min_eq_left (by lia)
      have h_eq : i + (j + 1) + 1 = i + 1 + j + 1 := by lia
      have h_index : i + 1 + j + 1 - (i + 1) = j + 1 := by lia
      simp only [bezoutEntry, hmin1, hmin2, h_eq, Finset.sum_sub_distrib,
        Finset.sum_range_succ, h_index]
      ring
  · have hmin1 : min i (j + 1) = j + 1 := min_eq_right (by lia)
    have hmin2 : min (i + 1) j = j := min_eq_right (by lia)
    have h_eq : i + (j + 1) + 1 = i + 1 + j + 1 := by lia
    have h_index : i + 1 + j + 1 - (j + 1) = i + 1 := by lia
    simp only [bezoutEntry, hmin1, hmin2, h_eq, Finset.sum_sub_distrib,
      Finset.sum_range_succ, h_index]
    ring

lemma bezoutEntry.bilinear_mul_sub (p q : ℝ[X]) (n : ℕ) (t₁ t₂ : ℝ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (t₁ - t₂) * ∑ i : Fin n, ∑ j : Fin n,
    bezoutEntry p q i.val j.val * t₁ ^ i.val * t₂ ^ j.val =
    p.eval t₁ * q.eval t₂ - p.eval t₂ * q.eval t₁ := by
  have heq_left : ∀ i j : ℕ, n ≤ i → bezoutEntry p q i j = 0 :=
    fun i j hi ↦ bezoutEntry.eq_zero_of_le_left p q hp hq hi
  have heq_right : ∀ i j : ℕ, n ≤ j → bezoutEntry p q i j = 0 :=
    fun i j hj ↦ bezoutEntry.eq_zero_of_le_right p q hp hq hj
  have h_telescope : ∀ i j : ℕ,
      p.coeff i * q.coeff j - p.coeff j * q.coeff i =
        (if i ≠ 0 then bezoutEntry p q (i - 1) j else 0) -
          (if j ≠ 0 then bezoutEntry p q i (j - 1) else 0) := by
    intro i j
    rcases i with (_ | i) <;> rcases j with (_ | j) <;>
      simp only [↓reduceIte, ne_eq, not_true_eq_false, Nat.succ_ne_zero,
        add_tsub_cancel_right, not_false_eq_true]
    · ring
    · simp only [bezoutEntry, min_eq_left (Nat.zero_le j)]
      rw [Finset.range_one, Finset.sum_singleton]
      grind
    · simp only [bezoutEntry, min_eq_right (Nat.zero_le i)]
      rw [Finset.range_one, Finset.sum_singleton]
      grind
    · rw [← bezoutEntry.telescoping]
  have h_rhs : p.eval t₁ * q.eval t₂ - p.eval t₂ * q.eval t₁ =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (p.coeff i * q.coeff j - p.coeff j * q.coeff i) * t₁ ^ i * t₂ ^ j := by
    have h_expand : p.eval t₁ * q.eval t₂ = ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1), p.coeff i * q.coeff j * t₁ ^ i * t₂ ^ j := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp),
         Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq), Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      grind
    have h_expand' : p.eval t₂ * q.eval t₁ = ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1), p.coeff j * q.coeff i * t₁ ^ i * t₂ ^ j := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp),
         Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq), Finset.sum_mul,
         Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      grind
    simp only [h_expand, h_expand', sub_mul, Finset.sum_sub_distrib]
  have h_rhs_sum :
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (p.coeff i * q.coeff j - p.coeff j * q.coeff i) * t₁ ^ i * t₂ ^ j =
      t₁ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n + 1),
        bezoutEntry p q i j * t₁ ^ i * t₂ ^ j -
      t₂ * ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range n,
        bezoutEntry p q i j * t₁ ^ i * t₂ ^ j := by
    have h_telescope_sum :
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (p.coeff i * q.coeff j - p.coeff j * q.coeff i) * t₁ ^ i * t₂ ^ j =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if i ≠ 0 then bezoutEntry p q (i - 1) j else 0) * t₁ ^ i * t₂ ^ j -
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if j ≠ 0 then bezoutEntry p q i (j - 1) else 0) * t₁ ^ i * t₂ ^ j := by
      simp only [h_telescope, sub_mul, Finset.sum_sub_distrib]
    convert h_telescope_sum using 2 <;> norm_num [Finset.sum_range_succ']
    · simp only [pow_succ', mul_assoc, mul_add, mul_comm, mul_left_comm, Finset.mul_sum]
    · simp only [pow_succ', mul_comm, mul_assoc, mul_left_comm, mul_add, Finset.mul_sum]
  rw [h_rhs, h_rhs_sum]
  simp [Finset.sum_range, Fin.sum_univ_castSucc, sub_mul, heq_left, heq_right]

lemma bezoutEntry.wronskian (p q : ℝ[X]) (n : ℕ) (t : ℝ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    ∑ i : Fin n, ∑ j : Fin n,
    bezoutEntry p q i.val j.val * t ^ (i.val + j.val) =
    p.derivative.eval t * q.eval t -
    p.eval t * q.derivative.eval t := by
  have h_apply : deriv (fun t₁ ↦ (t₁ - t) * ∑ i : Fin n, ∑ j : Fin n,
        bezoutEntry p q i.val j.val * t₁ ^ i.val * t ^ j.val) t =
      deriv (fun t₁ ↦ p.eval t₁ * q.eval t - p.eval t * q.eval t₁) t :=
    Filter.EventuallyEq.deriv_eq <| Filter.Eventually.of_forall fun t₁ ↦
      bezoutEntry.bilinear_mul_sub p q n t₁ t hp hq
  have h_left : deriv (fun t₁ ↦ (t₁ - t) * ∑ i : Fin n, ∑ j : Fin n,
        bezoutEntry p q i.val j.val * t₁ ^ i.val * t ^ j.val) t =
      ∑ i : Fin n, ∑ j : Fin n, bezoutEntry p q i.val j.val * t ^ i.val * t ^ j.val := by
    have h_sub : HasDerivAt (fun t₁ : ℝ ↦ t₁ - t) 1 t := by
      simpa using (hasDerivAt_id' t).sub_const t
    have h_sum : HasDerivAt
        (fun t₁ : ℝ ↦ ∑ i : Fin n, ∑ j : Fin n,
          bezoutEntry p q i.val j.val * t₁ ^ i.val * t ^ j.val)
        (∑ i : Fin n, ∑ j : Fin n,
          ((i.val : ℝ) * t ^ (i.val - 1)) * bezoutEntry p q i.val j.val * t ^ j.val) t := by
      refine HasDerivAt.fun_sum fun i _ ↦ HasDerivAt.fun_sum fun j _ ↦ ?_
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        ((hasDerivAt_pow i.val t).const_mul (bezoutEntry p q i.val j.val)).mul_const (t ^ j.val)
    simpa [sub_self, zero_mul, one_mul, mul_assoc, mul_comm, mul_left_comm, Pi.mul_def] using
      (h_sub.mul h_sum).deriv
  have h_deriv : deriv (fun t₁ ↦ p.eval t₁ * q.eval t - p.eval t * q.eval t₁) t =
      p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t :=
    HasDerivAt.deriv <| ((p.hasDerivAt t).mul_const (q.eval t)).sub
      (HasDerivAt.const_mul (p.eval t) (q.hasDerivAt t))
  grind

lemma bezoutMatrix.vandermonde_diagonal (p q : ℝ[X]) (n : ℕ) (t : ℝ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    dotProduct (fun i : Fin n ↦ t ^ (i : ℕ))
    ((bezoutMatrix n p q).mulVec (fun j : Fin n ↦ t ^ (j : ℕ))) =
    p.derivative.eval t * q.eval t -
    p.eval t * q.derivative.eval t := by
  convert bezoutEntry.wronskian p q n t hp hq using 1
  · simp only [bezoutMatrix, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc,
      mul_comm, pow_add]

lemma bezoutMatrix.vandermonde_off_diagonal (p q : ℝ[X]) (n : ℕ)
    (r : Fin n → ℝ) (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (hroots : ∀ k : Fin n, q.eval (r k) = 0)
    (hinj : Function.Injective r)
    (k l : Fin n) (hkl : k ≠ l) :
    dotProduct (fun i : Fin n ↦ r k ^ (i : ℕ))
    ((bezoutMatrix n p q).mulVec (fun j : Fin n ↦ r l ^ (j : ℕ))) = 0 := by
  have h_bezoutian : ∑ i : Fin n, ∑ j : Fin n,
      bezoutEntry p q i.val j.val * r k ^ i.val * r l ^ j.val = 0 := by
    have h_mul := bezoutEntry.bilinear_mul_sub p q n (r k) (r l) hp hq
    grind
  convert h_bezoutian using 1
  · simp only [bezoutMatrix, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

lemma bezoutMatrix.vandermonde_eq_diagonal (p q : ℝ[X]) (n : ℕ)
    (r : Fin n → ℝ) (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (hroots : ∀ k : Fin n, q.eval (r k) = 0)
    (hinj : Function.Injective r) :
    (vandermonde r) * (bezoutMatrix n p q) * (vandermonde r)ᵀ =
    Matrix.diagonal (fun k ↦ p.derivative.eval (r k) * q.eval (r k) -
    p.eval (r k) * q.derivative.eval (r k)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [diagonal_apply_eq, mul_apply, vandermonde_apply, transpose_apply]
    convert bezoutMatrix.vandermonde_diagonal p q n (r i) hp hq using 1
    · simpa only [mul_comm, Finset.mul_sum _ _ _, dotProduct, mulVec] using
        Finset.sum_comm.trans
          (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)
  · simp only [diagonal_apply_ne _ hij, mul_apply, vandermonde_apply, transpose_apply]
    convert bezoutMatrix.vandermonde_off_diagonal p q n r hp hq hroots hinj i j hij using 1
    · simpa only [mul_comm, Finset.mul_sum _ _ _, mul_left_comm, dotProduct, mulVec] using
        Finset.sum_comm.trans
          (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)

lemma Matrix.PosDef.of_congruent_diagonal {n : ℕ} {V : Matrix (Fin n) (Fin n) ℝ}
    {d : Fin n → ℝ} (hd : ∀ k, 0 < d k) (hV : V.det ≠ 0) :
    (Vᵀ * diagonal d * V).PosDef := by
  have h_inj : Function.Injective V.mulVec := by
    rwa [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact PosDef.conjTranspose_mul_mul_same (PosDef.diagonal hd) h_inj

lemma Matrix.PosDef.of_congruent_to_diagonal {n : ℕ}
    {V B : Matrix (Fin n) (Fin n) ℝ}
    {d : Fin n → ℝ} (hd : ∀ k, 0 < d k) (hV : V.det ≠ 0)
    (heq : V * B * Vᵀ = diagonal d) :
    B.PosDef := by
  let W := (V⁻¹)ᵀ
  have hW : W.det ≠ 0 := by
    simp [W, hV]
  have hB_eq : B = Wᵀ * diagonal d * W := by
    rw [show B = V⁻¹ * (V * B * Vᵀ) * (Vᵀ)⁻¹ by simp [Matrix.mul_assoc, hV], heq]
    simp [W, Matrix.transpose_nonsing_inv]
  rw [hB_eq]
  exact Matrix.PosDef.of_congruent_diagonal hd hW

lemma StrictMono.prod_sub_mul_prod_sub_pos_of_interlacing {n : ℕ}
    (s r : Fin n → ℝ) (hr : StrictMono r)
    (hint : ∀ k : Fin n, s k < r k)
    (hint' : ∀ (i j : Fin n), i < j → r i < s j)
    (k : Fin n) :
    0 < (∏ j : Fin n, (r k - s j)) *
    (∏ j ∈ Finset.univ.erase k, (r k - r j)) := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  have h_prod : 0 < (∏ j ∈ Finset.univ.erase k, (r k - r j)) *
      (∏ j ∈ Finset.univ.erase k, (r k - s j)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_pos fun x hx ↦ ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hx) with h | h
    · exact mul_pos (sub_pos.mpr (hr h)) (sub_pos.mpr (lt_trans (hint x) (hr h)))
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hr h)) (sub_neg.mpr (hint' k x h))
  nlinarith [hint k]

lemma Polynomial.eval_derivative_prod_X_sub_C_univ_at_root {n : ℕ} (r : Fin n → ℝ)
    (k : Fin n) :
    eval (r k) (derivative (∏ j : Fin n, (X - C (r j)))) =
    ∏ j ∈ Finset.univ.erase k, (r k - r j) := by
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ k)]
  simp [eval_prod, Finset.sdiff_singleton_eq_erase]

lemma Polynomial.splits_eq_C_mul_prod {n : ℕ} {q : ℝ[X]}
    (hq_ne : q ≠ 0) (hq_deg : q.natDegree = n)
    (r : Fin n → ℝ) (hr_roots : ∀ k, q.IsRoot (r k))
    (hinj : Function.Injective r) :
    q = C q.leadingCoeff * ∏ j : Fin n, (X - C (r j)) := by
  refine eq_of_degree_sub_lt_of_eval_finset_eq (Finset.image r Finset.univ) ?_ ?_
  · refine lt_of_lt_of_eq (degree_sub_lt ?_ hq_ne ?_) ?_
    · rw [degree_eq_natDegree hq_ne, hq_deg, degree_mul, degree_C (leadingCoeff_ne_zero.mpr hq_ne),
        zero_add, degree_prod]
      simp_all [degree_X_sub_C]
    · simp [leadingCoeff_prod]
    · rw [degree_eq_natDegree hq_ne, hq_deg,
        Finset.card_image_of_injective _ hinj, Finset.card_fin]
  · simp_all [eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, hinj.eq_iff]

lemma Polynomial.roots_sort_eq_of_isRoot {n : ℕ} {p : ℝ[X]} (hp_ne : p ≠ 0)
    (hp_deg : p.natDegree = n)
    (s : Fin n → ℝ) (hs_roots : ∀ k, p.IsRoot (s k)) (hs_sorted : StrictMono s) :
    p.roots.sort (· ≤ ·) = List.map s (List.finRange n) := by
  have hp_eq : p = C p.leadingCoeff * ∏ j : Fin n, (X - C (s j)) :=
    splits_eq_C_mul_prod hp_ne hp_deg s hs_roots hs_sorted.injective
  have hp_roots_eq : p.roots = Multiset.ofList (List.map s (List.finRange n)) := by
    rw [hp_eq, roots_C_mul _ (mt leadingCoeff_eq_zero.mp hp_ne), roots_prod]
    · norm_num [List.map]
      rw [List.ofFn_eq_map]
    · grind
  rw [hp_roots_eq, Multiset.coe_sort, List.mergeSort_eq_self]
  simp only [List.pairwise_iff_get, List.get_eq_getElem, List.getElem_map,
    List.getElem_finRange, Fin.cast_mk, hs_sorted.le_iff_le, Fin.mk_le_mk,
    Fin.val_fin_le]
  grind

lemma StrictPrecSameDegree.interlacing_fin {n : ℕ}
    {p q : ℝ[X]} (h : StrictPrecSameDegree p q)
    (hq_deg : q.natDegree = n)
    (s : Fin n → ℝ) (hs_roots : ∀ k, p.IsRoot (s k)) (hs_sorted : StrictMono s)
    (r : Fin n → ℝ) (hr_roots : ∀ k, q.IsRoot (r k)) (hr_sorted : StrictMono r) :
    (∀ k : Fin n, s k < r k) ∧ (∀ (i j : Fin n), i < j → r i < s j) := by
  obtain ⟨hp, hq, hdeg, h_interlaces⟩ := h
  rw [Polynomial.roots_sort_eq_of_isRoot hp.1 (hdeg.trans hq_deg) s hs_roots hs_sorted,
      Polynomial.roots_sort_eq_of_isRoot hq.1 hq_deg r hr_roots hr_sorted] at h_interlaces
  have h_len : (List.map s (List.finRange n)).length =
    (List.map r (List.finRange n)).length := by simp
  obtain ⟨h_inter1, h_inter2⟩ := interlaced_of_interleaves_reverse h_len h_interlaces
  constructor
  · intro k
    simpa only [List.getElem_map, List.getElem_finRange, Fin.cast_mk] using
      h_inter1 ⟨k.1, by simp⟩
  · intro i j hij
    simpa only [List.getElem_map, List.getElem_finRange, Fin.cast_mk] using
      h_inter2 ⟨i.1, by simp⟩ ⟨j.1, by simp⟩ hij

lemma StrictPrecSameDegree.roots_nodup {p q : ℝ[X]}
    (h : StrictPrecSameDegree p q) :
    p.roots.Nodup ∧ q.roots.Nodup := by
  obtain ⟨_, _, _, h_interlacing⟩ := h
  rw [← Multiset.sort_eq p.roots (· ≤ ·), ← Multiset.sort_eq q.roots (· ≤ ·),
    Multiset.coe_nodup, Multiset.coe_nodup]
  exact ⟨(List.pairwise_reverse.mp h_interlacing.pairwise_left).nodup,
         (List.pairwise_reverse.mp h_interlacing.pairwise_right).nodup⟩

lemma Polynomial.exists_strictMono_roots {n : ℕ} {p : ℝ[X]}
    (hp_splits : p.Splits) (hp_deg : p.natDegree = n)
    (hp_nodup : p.roots.Nodup) :
    ∃ s : Fin n → ℝ, StrictMono s ∧ ∀ k, p.IsRoot (s k) := by
  have h_card : p.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hp_nodup, ← hp_deg,
      ← Splits.natDegree_eq_card_roots hp_splits]
  let e := p.roots.toFinset.orderEmbOfFin h_card
  have he : ∀ k : Fin n, e k ∈ p.roots := fun k ↦
    Multiset.mem_toFinset.mp (Finset.orderEmbOfFin_mem p.roots.toFinset h_card k)
  exact ⟨e, e.strictMono, fun k ↦ isRoot_of_mem_roots (he k)⟩

lemma Polynomial.eval_derivative_C_mul_prod_X_sub_C_univ_at_root {n : ℕ} (c : ℝ)
    (r : Fin n → ℝ) (k : Fin n) :
    eval (r k) (derivative (C c * ∏ j : Fin n, (X - C (r j)))) =
    c * ∏ j ∈ Finset.univ.erase k, (r k - r j) := by
  simp [eval_derivative_prod_X_sub_C_univ_at_root r k]

lemma Polynomial.wronskian_at_root_pos_of_interlacing {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (h : StrictPrecSameDegree p q)
    (r : Fin n → ℝ) (hr_roots : ∀ k, q.IsRoot (r k))
    (hr_sorted : StrictMono r)
    (k : Fin n) :
    0 < q.derivative.eval (r k) * p.eval (r k) := by
  obtain ⟨hp_nodup, _⟩ := h.roots_nodup
  have hp_splits := h.1.2
  obtain ⟨s, hs_mono, hs_roots⟩ := exists_strictMono_roots hp_splits hp_deg hp_nodup
  obtain ⟨c₁, hc₁⟩ :
      ∃ c₁ : ℝ, 0 < c₁ ∧ p = C c₁ * ∏ j : Fin n, (X - C (s j)) := by
    have hp_eq : p = C p.leadingCoeff * ∏ j : Fin n, (X - C (s j)) :=
      splits_eq_C_mul_prod (leadingCoeff_ne_zero.mp hp_pos.ne')
        hp_deg s hs_roots hs_mono.injective
    exact ⟨p.leadingCoeff, hp_pos, hp_eq⟩
  obtain ⟨c₂, hc₂⟩ :
      ∃ c₂ : ℝ, 0 < c₂ ∧ q = C c₂ * ∏ j : Fin n, (X - C (r j)) := by
    have hq_eq : q = C q.leadingCoeff * ∏ j : Fin n, (X - C (r j)) :=
      splits_eq_C_mul_prod (leadingCoeff_ne_zero.mp hq_pos.ne')
        hq_deg r hr_roots hr_sorted.injective
    exact ⟨q.leadingCoeff, hq_pos, hq_eq⟩
  have h_eval : q.derivative.eval (r k) * p.eval (r k) = c₂ * c₁ * (∏ j : Fin n,
    (r k - s j)) * (∏ j ∈ Finset.univ.erase k, (r k - r j)) := by
    rw [hc₂.2, hc₁.2]
    simp only [Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ k),
      derivative_mul, derivative_C, zero_mul, derivative_sub, derivative_X, sub_zero,
      mul_one, zero_add, eval_mul, eval_C, eval_add, eval_sub, eval_X, sub_self,
      mul_zero, eval_prod, Finset.sdiff_singleton_eq_erase]
    ring
  have h_prod :
      0 < (∏ j : Fin n, (r k - s j)) * (∏ j ∈ Finset.univ.erase k, (r k - r j)) := by
    have h_interlacing :=
      StrictPrecSameDegree.interlacing_fin h hq_deg s hs_roots hs_mono r
        hr_roots hr_sorted
    exact StrictMono.prod_sub_mul_prod_sub_pos_of_interlacing s r hr_sorted
      h_interlacing.1 h_interlacing.2 k
  rw [h_eval, mul_assoc]
  simp_all

lemma StrictPrecSameDegree.bezoutMatrix_posDef_three_le
    {p q : ℝ[X]} {n : ℕ}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n + 3) (hq_deg : q.natDegree = n + 3)
    (h : StrictPrecSameDegree p q) :
    (bezoutMatrix (n + 3) q p).PosDef := by
  obtain ⟨_, hq_nodup⟩ := h.roots_nodup
  have hq_splits := h.2.1.2
  obtain ⟨s, hs_mono, hs_roots⟩ :
      ∃ s : Fin (n + 3) → ℝ, StrictMono s ∧ ∀ k, q.IsRoot (s k) :=
    Polynomial.exists_strictMono_roots hq_splits hq_deg hq_nodup
  have h_v_eq : vandermonde s * bezoutMatrix (n + 3) q p * (vandermonde s)ᵀ =
      diagonal fun k ↦ q.derivative.eval (s k) * p.eval (s k) := by
    have h_vandermonde : ∀ k : Fin (n + 3),
        p.derivative.eval (s k) * q.eval (s k) -
          p.eval (s k) * q.derivative.eval (s k) =
        q.derivative.eval (s k) * p.eval (s k) * (-1) := by
      intro k
      have hq_zero : q.eval (s k) = 0 := hs_roots k
      grind
    have h_neg : bezoutMatrix (n + 3) q p = -bezoutMatrix (n + 3) p q := by
      ext i j
      simp [bezoutMatrix, bezoutEntry]
    convert congr_arg (fun x ↦ -x)
      (bezoutMatrix.vandermonde_eq_diagonal p q (n + 3) s hp_deg.le hq_deg.le
        (by simp_all) hs_mono.injective) using 1 <;> simp_all
  refine Matrix.PosDef.of_congruent_to_diagonal ?_ ?_ h_v_eq
  · intro k
    convert Polynomial.wronskian_at_root_pos_of_interlacing hp_pos hq_pos
      hp_deg hq_deg h s hs_roots hs_mono k using 1
  · simp_all [Matrix.det_vandermonde, Finset.prod_eq_zero_iff, sub_eq_zero,
      hs_mono.injective.eq_iff]

lemma bezoutMatrix.wronskian_pos_of_posDef
    {p q : ℝ[X]} {n : ℕ}
    (hq_deg : q.natDegree ≤ n + 1) (hp_deg : p.natDegree ≤ n + 1)
    (h : (bezoutMatrix (n + 1) q p).PosDef) (t : ℝ) :
    0 < q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t := by
  have hvec_ne : (fun i : Fin (n + 1) ↦ t ^ (i : ℕ)) ≠ 0 := fun hzero ↦ by
    have h0 := congr_fun hzero 0
    simp_all
  have h_sum_pos := Matrix.PosDef.sum_pos h hvec_ne
  have h_sum_eq :
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        bezoutMatrix (n + 1) q p i j * t ^ (i : ℕ) * t ^ (j : ℕ)) =
      q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t := by
    simp_rw [bezoutMatrix, mul_assoc, ← pow_add]
    exact bezoutEntry.wronskian q p (n + 1) t hq_deg hp_deg
  simp_all

lemma bezoutEntry.bilinear_mul_sub_complex (p q : ℝ[X]) (n : ℕ) (z w : ℂ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (z - w) * ∑ i : Fin n, ∑ j : Fin n,
    (bezoutEntry p q i.val j.val : ℂ) * z ^ i.val * w ^ j.val =
    (p.map Complex.ofRealHom).eval z * (q.map Complex.ofRealHom).eval w -
    (p.map Complex.ofRealHom).eval w * (q.map Complex.ofRealHom).eval z := by
  have heq_left : ∀ i j : ℕ, n ≤ i → (bezoutEntry p q i j : ℂ) = 0 :=
    fun i j hi ↦ by rw [bezoutEntry.eq_zero_of_le_left p q hp hq hi, Complex.ofReal_zero]
  have heq_right : ∀ i j : ℕ, n ≤ j → (bezoutEntry p q i j : ℂ) = 0 :=
    fun i j hj ↦ by rw [bezoutEntry.eq_zero_of_le_right p q hp hq hj, Complex.ofReal_zero]
  have h_telescope : ∀ i j : ℕ,
      (p.coeff i : ℂ) * (q.coeff j : ℂ) - (p.coeff j : ℂ) * (q.coeff i : ℂ) =
        (if i ≠ 0 then (bezoutEntry p q (i - 1) j : ℂ) else 0) -
          (if j ≠ 0 then (bezoutEntry p q i (j - 1) : ℂ) else 0) := by
    intro i j
    have h_real : p.coeff i * q.coeff j - p.coeff j * q.coeff i =
        (if i ≠ 0 then bezoutEntry p q (i - 1) j else 0) -
          (if j ≠ 0 then bezoutEntry p q i (j - 1) else 0) := by
      rcases i with (_ | i) <;> rcases j with (_ | j) <;>
        simp only [↓reduceIte, ne_eq, not_true_eq_false, Nat.succ_ne_zero,
          add_tsub_cancel_right, not_false_eq_true]
      · ring
      · simp only [bezoutEntry, min_eq_left (Nat.zero_le j)]
        rw [Finset.range_one, Finset.sum_singleton]
        grind
      · simp only [bezoutEntry, min_eq_right (Nat.zero_le i)]
        rw [Finset.range_one, Finset.sum_singleton]
        grind
      · rw [← bezoutEntry.telescoping]
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp_all
      · subst hi
        simp only [ne_self_iff_false, ↓reduceIte, if_pos hj] at h_real ⊢
        norm_cast
    · by_cases hj : j = 0
      · subst hj
        simp only [ne_self_iff_false, ↓reduceIte, if_pos hi] at h_real ⊢
        norm_cast
      · simp only [if_pos hi, if_pos hj] at h_real ⊢
        norm_cast
  have h_rhs : (p.map Complex.ofRealHom).eval z * (q.map Complex.ofRealHom).eval w -
      (p.map Complex.ofRealHom).eval w * (q.map Complex.ofRealHom).eval z =
    ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      ((p.coeff i : ℂ) * (q.coeff j : ℂ) -
        (p.coeff j : ℂ) * (q.coeff i : ℂ)) * z ^ i * w ^ j := by
    have h_expand : (p.map Complex.ofRealHom).eval z * (q.map Complex.ofRealHom).eval w =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (p.coeff i : ℂ) * (q.coeff j : ℂ) * z ^ i * w ^ j := by
      rw [Polynomial.eval_eq_sum_range' (by rw [natDegree_map]; exact Nat.lt_succ_of_le hp),
          Polynomial.eval_eq_sum_range' (by rw [natDegree_map]; exact Nat.lt_succ_of_le hq)]
      simp only [coeff_map, Complex.ofRealHom_eq_coe, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      grind
    have h_expand' : (p.map Complex.ofRealHom).eval w * (q.map Complex.ofRealHom).eval z =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (p.coeff j : ℂ) * (q.coeff i : ℂ) * z ^ i * w ^ j := by
      rw [Polynomial.eval_eq_sum_range' (by rw [natDegree_map]; exact Nat.lt_succ_of_le hp),
          Polynomial.eval_eq_sum_range' (by rw [natDegree_map]; exact Nat.lt_succ_of_le hq)]
      rw [Finset.sum_comm]
      simp only [coeff_map, Complex.ofRealHom_eq_coe, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      grind
    simp only [h_expand, h_expand', sub_mul, Finset.sum_sub_distrib]
  have h_rhs_sum :
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        ((p.coeff i : ℂ) * (q.coeff j : ℂ) -
          (p.coeff j : ℂ) * (q.coeff i : ℂ)) * z ^ i * w ^ j =
      z * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n + 1),
        (bezoutEntry p q i j : ℂ) * z ^ i * w ^ j -
      w * ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range n,
        (bezoutEntry p q i j : ℂ) * z ^ i * w ^ j := by
    have h_telescope_sum :
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          ((p.coeff i : ℂ) * (q.coeff j : ℂ) -
            (p.coeff j : ℂ) * (q.coeff i : ℂ)) * z ^ i * w ^ j =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if i ≠ 0 then (bezoutEntry p q (i - 1) j : ℂ) else 0) * z ^ i * w ^ j -
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if j ≠ 0 then (bezoutEntry p q i (j - 1) : ℂ) else 0) * z ^ i * w ^ j := by
      simp only [h_telescope, sub_mul, Finset.sum_sub_distrib]
    convert h_telescope_sum using 2 <;> norm_num [Finset.sum_range_succ']
    · simp only [pow_succ', mul_assoc, mul_add, mul_comm, mul_left_comm, Finset.mul_sum]
    · simp only [pow_succ', mul_comm, mul_assoc, mul_left_comm, mul_add, Finset.mul_sum]
  rw [h_rhs, h_rhs_sum]
  simp [Finset.sum_range, Fin.sum_univ_castSucc, sub_mul, heq_left, heq_right]

lemma _root_.Matrix.PosDef.eq_zero_of_sum_mul_mul_eq_zero {m : ℕ}
    {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.PosDef)
    (x : Fin m → ℝ)
    (hx : ∑ i : Fin m, ∑ j : Fin m, B i j * x i * x j = 0) :
    x = 0 := by
  by_contra hx_ne
  have := Matrix.PosDef.sum_pos hB hx_ne
  linarith

lemma bezoutMatrix.no_complex_root_of_posDef {n : ℕ}
    {p q : ℝ[X]} (hp_deg : p.natDegree ≤ n + 1) (hq_deg : q.natDegree ≤ n + 1)
    (hB : (bezoutMatrix (n + 1) q p).PosDef)
    (z : ℂ) (hz : 0 < z.im) (hroot : (p.map Complex.ofRealHom).eval z = 0) :
    False := by
  obtain ⟨x, hx⟩ : ∃ x : Fin (n + 1) → ℝ,
      x ≠ 0 ∧ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        (bezoutMatrix (n + 1) q p i j : ℝ) * (x i) * (x j) = 0 := by
    obtain ⟨y, hy⟩ : ∃ y : Fin (n + 1) → ℂ,
        y ≠ 0 ∧ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          (bezoutMatrix (n + 1) q p i j : ℂ) * y i *
            starRingEnd ℂ (y j) = 0 := by
      use fun i ↦ z ^ i.val
      have h_bezoutian : (z - starRingEnd ℂ z) * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          (bezoutEntry q p i.val j.val : ℂ) * z ^ i.val * (starRingEnd ℂ z) ^ j.val = 0 := by
        convert bezoutEntry.bilinear_mul_sub_complex q p (n + 1) z
          (starRingEnd ℂ z) hq_deg hp_deg using 1
        simp_all only [eval_map, mul_zero, sub_zero, zero_eq_mul]
        exact Or.inr (by simpa [Polynomial.eval₂_eq_sum_range,
          Complex.ext_iff] using congr_arg Star.star hroot)
      exact ⟨fun hy_eq ↦ by simpa using congr_fun hy_eq ⟨0, by lia⟩, by
        have hdiff_ne : z - starRingEnd ℂ z ≠ 0 := by
          intro hdiff
          have him := congr_arg Complex.im hdiff
          simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add, Complex.zero_im] at him
          linarith
        have hsum := (mul_eq_zero.mp h_bezoutian).resolve_left hdiff_ne
        simpa only [bezoutMatrix, map_pow] using hsum⟩
    refine ⟨fun i ↦ (y i).re, ?_, ?_⟩
    all_goals
      simp_all only [Complex.ext_iff, Complex.zero_re, Complex.zero_im, ne_eq,
        Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.conj_re, Complex.mul_im, add_zero, Complex.conj_im, mul_neg,
        sub_neg_eq_add, Finset.sum_add_distrib, Complex.im_sum, Finset.sum_neg_distrib]
    · intro hre_zero
      have him_ne : (fun i ↦ (y i).im) ≠ 0 := fun h ↦
        hy.1 (funext fun i ↦ Complex.ext (congr_fun hre_zero i) (congr_fun h i))
      have him_pos := Matrix.PosDef.sum_pos hB him_ne
      have hre_sum :
          ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            bezoutMatrix (n + 1) q p i j * (y i).re * (y j).re = 0 := by
        simp [congr_fun hre_zero]
      linarith
    · have h_pos (x : Fin (n + 1) → ℝ) :
          0 ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            bezoutMatrix (n + 1) q p i j * x i * x j := by
        rcases eq_or_ne x 0 with rfl | hx
        · simp
        · exact (Matrix.PosDef.sum_pos hB hx).le
      linarith [h_pos (fun i ↦ (y i).re), h_pos (fun i ↦ (y i).im)]
  exact hx.1 (hB.eq_zero_of_sum_mul_mul_eq_zero x hx.2)

lemma bezoutMatrix.no_complex_root_q_of_posDef {n : ℕ}
    {p q : ℝ[X]} (hp_deg : p.natDegree ≤ n + 1) (hq_deg : q.natDegree ≤ n + 1)
    (hB : (bezoutMatrix (n + 1) q p).PosDef)
    (z : ℂ) (hz : 0 < z.im) (hroot : (q.map Complex.ofRealHom).eval z = 0) :
    False := by
  have h_no_complex := @bezoutMatrix.no_complex_root_of_posDef
  contrapose! h_no_complex
  use n, q, -p
  refine ⟨hq_deg, ?_, ?_, z, hz, hroot, h_no_complex⟩
  · simp_all
  · convert hB using 1
    ext i j
    simp [bezoutMatrix, bezoutEntry, neg_add_eq_sub, Finset.sum_sub_distrib]

lemma Polynomial.splits_of_all_roots_real {p : ℝ[X]}
    (hall : ∀ z : ℂ, (p.map Complex.ofRealHom).eval z = 0 → z.im = 0) :
    p.Splits := by
  apply splits_iff_exists_multiset.mpr
  use (p.map Complex.ofRealHom).roots.map Complex.re
  refine map_injective (algebraMap ℝ ℂ) (Complex.ofReal_injective) ?_
  have h_factor :
      p.map Complex.ofRealHom =
        C (p.leadingCoeff : ℂ) *
          Multiset.prod (Multiset.map (fun z ↦ X - C z)
            (p.map Complex.ofRealHom).roots) := by
    convert Splits.eq_prod_roots _
    · simp
    · exact IsAlgClosed.splits _
  convert h_factor using 1
  · rfl
  · norm_num [Polynomial.map_multiset_prod]
    exact Or.inl (congr_arg _
      (Multiset.map_congr rfl fun x hx ↦ by
        rw [← Complex.re_add_im x]
        simp [hall x (isRoot_of_mem_roots hx)]))

lemma bezoutMatrix.splits_of_posDef {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hB : (bezoutMatrix n q p).PosDef) :
    p.Splits ∧ q.Splits := by
  by_cases hn : n = 0
  · subst hn
    have hp : p.natDegree = 0 := hp_deg
    have hq : q.natDegree = 0 := hq_deg
    obtain ⟨-, hp_splits⟩ := isRealRooted_of_deg_zero (leadingCoeff_ne_zero.mp hp_pos.ne') hp
    obtain ⟨-, hq_splits⟩ := isRealRooted_of_deg_zero (leadingCoeff_ne_zero.mp hq_pos.ne') hq
    simp_all
  · have hn_eq : n = n - 1 + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)).symm
    have hB' : (bezoutMatrix (n - 1 + 1) q p).PosDef := hn_eq ▸ hB
    constructor
    · apply Polynomial.splits_of_all_roots_real
      intro z hz
      by_contra h_im_ne_zero
      rcases lt_or_gt_of_ne h_im_ne_zero with h_neg | h_pos
      · have h_star_im : 0 < (starRingEnd ℂ z).im := by simp [h_neg]
        have h_star_root : (p.map Complex.ofRealHom).eval (starRingEnd ℂ z) = 0 := by
          simpa [eval_eq_sum_range] using congr_arg Star.star hz
        exact bezoutMatrix.no_complex_root_of_posDef (hn_eq ▸ hp_deg.le) (hn_eq ▸ hq_deg.le)
          hB' (starRingEnd ℂ z) h_star_im h_star_root
      · exact bezoutMatrix.no_complex_root_of_posDef (hn_eq ▸ hp_deg.le) (hn_eq ▸ hq_deg.le)
          hB' z h_pos hz
    · apply Polynomial.splits_of_all_roots_real
      intro z hz
      by_contra h_im_ne_zero
      rcases lt_or_gt_of_ne h_im_ne_zero with h_neg | h_pos
      · have h_star_im : 0 < (starRingEnd ℂ z).im := by simp [h_neg]
        have h_star_root : (q.map Complex.ofRealHom).eval (starRingEnd ℂ z) = 0 := by
          simpa [eval_eq_sum_range] using congr_arg Star.star hz
        exact bezoutMatrix.no_complex_root_q_of_posDef (hn_eq ▸ hp_deg.le) (hn_eq ▸ hq_deg.le)
          hB' (starRingEnd ℂ z) h_star_im h_star_root
      · exact bezoutMatrix.no_complex_root_q_of_posDef (hn_eq ▸ hp_deg.le) (hn_eq ▸ hq_deg.le)
          hB' z h_pos hz

lemma Polynomial.no_repeated_root_of_wronskian_pos {p q : ℝ[X]}
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t)
    (r : ℝ) (hp_root : p.IsRoot r) : ¬ p.derivative.IsRoot r := by
  intro hd
  have := hW r
  simp_all

lemma Polynomial.roots_nodup_of_splits_and_simple {p : ℝ[X]}
    (h_simple : ∀ r : ℝ, p.IsRoot r → ¬ p.derivative.IsRoot r) :
    p.roots.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro r
  rw [count_roots]
  by_cases hr : p.IsRoot r
  · exact Nat.le_of_not_lt fun h ↦ h_simple r hr <| by
      simpa [hr] using Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity h
  · rw [rootMultiplicity_eq_zero hr]
    simp

lemma StrictMono.fin_interlacing_of_root_between {n : ℕ}
    (s r : Fin (n + 1) → ℝ) (hs : StrictMono s)
    (h_root_below : s 0 < r 0)
    (h_between : ∀ k : Fin n,
    ∃ j : Fin (n + 1), r k.castSucc < s j ∧ s j < r k.succ) :
    (∀ k : Fin (n + 1), s k < r k) ∧
    (∀ (i j : Fin (n + 1)), i < j → r i < s j) := by
  have h_second_part : ∀ i j : Fin (n + 1), i < j → r i < s j := by
    intro i
    refine Fin.reverseInduction ?_ ?_ i
    · grind
    · intro i IH j hj
      obtain ⟨k, hk₁, hk₂⟩ := h_between i
      by_cases h_cases : j ≤ k
      · grind
      · exact lt_of_lt_of_le hk₁ (hs.monotone (not_le.mp h_cases).le)
  refine ⟨fun k ↦ ?_, h_second_part⟩
  refine Fin.inductionOn k ?_ ?_
  · simp_all
  · intro k ih
    obtain ⟨j, hj₁, hj₂⟩ := h_between k
    refine lt_of_le_of_lt (hs.monotone (Nat.succ_le_of_lt ?_)) hj₂
    by_contra hnot
    have h_le : j ≤ k.castSucc := not_lt.mp hnot
    have : s j ≤ s k.castSucc := hs.monotone h_le
    grind

lemma Polynomial.roots_sort_eq_ofFn {n : ℕ} {p : ℝ[X]}
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hp_deg : p.natDegree = n)
    (hp_nodup : p.roots.Nodup)
    (s : Fin n → ℝ) (hs : StrictMono s)
    (hs_surj : ∀ x ∈ p.roots, ∃ k, s k = x) :
    p.roots.sort (· ≤ ·) = List.ofFn s := by
  have h_eq_multiset : p.roots = Multiset.ofList (List.ofFn s) := by
    refine Multiset.eq_of_le_of_card_le (Multiset.le_iff_count.mpr ?_) ?_
    · intro x
      by_cases hx : x ∈ p.roots <;> simp_all
    · rw [Polynomial.splits_iff_card_roots] at hp_splits
      simp_all
  rw [h_eq_multiset, List.ofFn_eq_map]
  refine List.mergeSort_eq_self (· ≤ ·) ?_
  simp only [List.pairwise_iff_get, List.get_eq_getElem, List.getElem_map,
    List.getElem_finRange, Fin.cast_mk]
  exact fun i j hij ↦ hs.monotone hij.le

lemma StrictPrecSameDegree.of_fin_interlacing {n : ℕ}
    (s r : Fin n → ℝ) (hs : StrictMono s) (hr : StrictMono r)
    (hint : ∀ k : Fin n, s k < r k)
    (hint' : ∀ (i j : Fin n), i < j → r i < s j)
    (p q : ℝ[X])
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0)
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hp_roots_nodup : p.roots.Nodup) (hq_roots_nodup : q.roots.Nodup)
    (hs_surj : ∀ x ∈ p.roots, ∃ k, s k = x)
    (hr_surj : ∀ x ∈ q.roots, ∃ k, r k = x) :
    StrictPrecSameDegree p q :=
  ⟨⟨hp_ne, hp_splits⟩, ⟨hq_ne, hq_splits⟩, hp_deg ▸ hq_deg ▸ rfl,
    Polynomial.roots_sort_eq_ofFn hp_ne hp_splits hp_deg hp_roots_nodup s hs hs_surj ▸
    Polynomial.roots_sort_eq_ofFn hq_ne hq_splits hq_deg hq_roots_nodup r hr hr_surj ▸
    List.Interleaves.ofFn s r hint hint'⟩

lemma Polynomial.has_root_between_roots_of_wronskian_pos {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n + 1) (hq_deg : q.natDegree = n + 1)
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t -
    q.eval t * p.derivative.eval t)
    (r : Fin (n + 1) → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k)) :
    (∃ x, p.IsRoot x ∧ x < r 0) ∧
    (∀ k : Fin n, ∃ x, p.IsRoot x ∧ r k.castSucc < x ∧ x < r k.succ) := by
  have h_sign_change_prod : ∀ k : Fin (n + 1),
      0 < p.eval (r k) * ∏ j ∈ Finset.erase Finset.univ k, (r k - r j) := by
    intro k
    have h_eval_deriv :
        q.derivative.eval (r k) =
          q.leadingCoeff * ∏ j ∈ Finset.erase Finset.univ k, (r k - r j) := by
      have h_eval_deriv : q = Polynomial.C q.leadingCoeff * ∏ j : Fin (n + 1),
        (Polynomial.X - Polynomial.C (r j)) := by
        convert Polynomial.splits_eq_C_mul_prod _ _ _ _ _
        · exact leadingCoeff_ne_zero.mp hq_pos.ne'
        · simp_all
        · simp_all
        · exact hr_mono.injective
      conv_lhs => rw [h_eval_deriv]
      exact Polynomial.eval_derivative_C_mul_prod_X_sub_C_univ_at_root
        q.leadingCoeff r k
    have := hW (r k)
    have hq_eval : q.eval (r k) = 0 := hr_roots k
    rw [hq_eval, zero_mul, sub_zero, h_eval_deriv, mul_assoc] at this
    have h_prod := pos_of_mul_pos_right this hq_pos.le
    grind
  have h_sign_change_pow : ∀ k : Fin (n + 1), 0 < p.eval (r k) * (-1) ^ (n - k.val) := by
    intro k
    have h_prod_sign : ∏ j ∈ Finset.erase (Finset.univ : Finset (Fin (n + 1))) k,
      (r k - r j) = (-1) ^ (n - k.val) *
        (∏ j ∈ Finset.erase (Finset.univ : Finset (Fin (n + 1))) k,
          |r k - r j|) := by
      have h_prod_sign_abs : ∏ j ∈ Finset.erase (Finset.univ : Finset (Fin (n + 1))) k,
        (r k - r j) = ∏ j ∈ Finset.erase (Finset.univ : Finset (Fin (n + 1))) k,
          (-1) ^ (if k < j then 1 else 0) * |r k - r j| := by
        refine Finset.prod_congr rfl fun j hj ↦ ?_
        split_ifs with hjk
        · simp_all only [pow_one, neg_mul, one_mul]
          rw [abs_of_neg] <;> linarith [hr_mono hjk]
        · simp_all only [pow_zero, one_mul]
          rw [abs_of_nonneg (sub_nonneg.mpr (hr_mono.monotone (not_lt.mp hjk)))]
      rw [h_prod_sign_abs, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      simp only [Finset.sum_boole, Nat.cast_id,
        mul_eq_mul_right_iff]
      have : (Finset.univ.erase k).filter (fun x ↦ k < x) = Finset.Ioi k := by grind
      simp_all
    specialize h_sign_change_prod k
    rw [h_prod_sign] at h_sign_change_prod
    nlinarith [show 0 < ∏ j ∈ Finset.univ.erase k, |r k - r j| from
      Finset.prod_pos fun j hj ↦ abs_pos.mpr <| sub_ne_zero.mpr <|
        hr_mono.injective.ne (Finset.ne_of_mem_erase hj).symm]
  have h_sign_change_mul : ∀ k : Fin n,
      p.eval (r (Fin.castSucc k)) * p.eval (r (Fin.succ k)) < 0 := by
    intro k
    have h_sign_change_k : 0 < p.eval (r (Fin.castSucc k)) * (-1) ^ (n - k.val) := by grind
    have h_sign_change_k_succ : 0 < p.eval (r (Fin.succ k)) * (-1) ^ (n - (k.val + 1)) := by grind
    rw [show n - k = n - (k + 1) + 1 by lia] at h_sign_change_k
    let m := n - (k.val + 1)
    change 0 < p.eval (r (Fin.castSucc k)) * (-1) ^ (m + 1) at h_sign_change_k
    change 0 < p.eval (r (Fin.succ k)) * (-1) ^ m at h_sign_change_k_succ
    rcases Nat.even_or_odd m with hm | hm
    · have hm_pow : (-1 : ℝ) ^ m = 1 := hm.neg_one_pow
      have hm_succ_pow : (-1 : ℝ) ^ (m + 1) = -1 := by simp_all
      rw [hm_pow] at h_sign_change_k_succ
      rw [hm_succ_pow] at h_sign_change_k
      nlinarith
    · have hm_pow : (-1 : ℝ) ^ m = -1 := hm.neg_one_pow
      have hm_succ_pow : (-1 : ℝ) ^ (m + 1) = 1 := by simp_all
      rw [hm_pow] at h_sign_change_k_succ
      rw [hm_succ_pow] at h_sign_change_k
      nlinarith
  constructor
  · have h_sign_change_zero : 0 < p.eval (r 0) * (-1) ^ n := by grind
    have h_sign_change_bot : ∃ x : ℝ, x < r 0 ∧ 0 < p.eval x * (-1) ^ (n + 1) := by
      have h_tendsto_bot :
          Filter.Tendsto (fun x ↦ p.eval x * (-1) ^ (n + 1)) Filter.atBot
            Filter.atTop := by
        have h_tendsto_neg :
            Filter.Tendsto (fun x ↦ p.eval (-x) * (-1) ^ (n + 1))
              Filter.atTop Filter.atTop := by
          have h_leading :
              0 < Polynomial.leadingCoeff (p.comp (-Polynomial.X)) *
                (-1) ^ (n + 1) := by
            rw [Polynomial.comp_neg_X_leadingCoeff_eq, hp_deg]
            rcases Nat.even_or_odd (n + 1) with h | h <;>
              rw [h.neg_one_pow] <;> norm_num <;> exact hp_pos
          have h_tendsto_comp :
              Filter.Tendsto
                (fun x ↦ Polynomial.eval x
                  (p.comp (-Polynomial.X) * Polynomial.C ((-1) ^ (n + 1))))
                Filter.atTop Filter.atTop := by
            rw [Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg]
            rw [Polynomial.degree_mul, Polynomial.degree_C] <;> norm_num [h_leading]
            exact ⟨Polynomial.natDegree_pos_iff_degree_pos.mp (by lia), by
              simpa [hp_deg] using h_leading.le⟩
          simp_all
        convert h_tendsto_neg.comp Filter.tendsto_neg_atBot_atTop using 2
        simp
      exact (Filter.Eventually.and (Filter.eventually_lt_atBot (r 0))
        (h_tendsto_bot.eventually_gt_atTop 0)).exists
    obtain ⟨x, hx₁, hx₂⟩ := h_sign_change_bot
    have h_ivt : ∃ c ∈ Set.Ioo x (r 0), p.eval c = 0 := by
      have h_cont : ContinuousOn (fun t ↦ p.eval t) (Set.Icc x (r 0)) :=
        p.continuous.continuousOn
      have h_sign_change_ends : p.eval x * p.eval (r 0) < 0 := by
        by_cases h : Even n <;> simp_all [Nat.even_add_one] <;> nlinarith
      rw [mul_neg_iff] at h_sign_change_ends
      rcases h_sign_change_ends with h_sign_change_ends | h_sign_change_ends
      · exact intermediate_value_Ioo' hx₁.le h_cont (by simp_all)
      · exact intermediate_value_Ioo hx₁.le h_cont (by simp_all)
    rcases h_ivt with ⟨c, hc_in, hc_root⟩
    exact ⟨c, hc_root, hc_in.2⟩
  · intro k
    have h_ivt : ∃ x ∈ Set.Ioo (r (Fin.castSucc k)) (r (Fin.succ k)), p.eval x = 0 := by
      have h_cont :
          ContinuousOn (fun x ↦ p.eval x)
            (Set.Icc (r (Fin.castSucc k)) (r (Fin.succ k))) :=
        p.continuous.continuousOn
      have := h_sign_change_mul k
      rw [mul_neg_iff] at this
      have hle : r (Fin.castSucc k) ≤ r (Fin.succ k) :=
        hr_mono.monotone (Nat.le_succ _)
      rcases this with h | h
      · exact intermediate_value_Ioo'
          (by simp_all) h_cont (by simp_all)
      · exact intermediate_value_Ioo
          (by simp_all) h_cont (by simp_all)
    rcases h_ivt with ⟨c, hc_in, hc_root⟩
    exact ⟨c, hc_root, hc_in⟩

lemma StrictPrecSameDegree.of_wronskian_pos {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t -
    q.eval t * p.derivative.eval t) :
    StrictPrecSameDegree p q := by
  rcases n with (_ | n)
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hp_deg] at hW ⊢
    rw [Polynomial.eq_C_of_natDegree_eq_zero hq_deg] at hW ⊢
    simp_all
  · have h_real_roots : p.roots.Nodup ∧ q.roots.Nodup := by
      apply And.intro
      · apply Polynomial.roots_nodup_of_splits_and_simple
        · exact fun r hr ↦ Polynomial.no_repeated_root_of_wronskian_pos hW r hr
      · apply Polynomial.roots_nodup_of_splits_and_simple
        · intro r hr hd
          specialize hW r
          simp_all
    obtain ⟨s, hs_mono, hs_roots⟩ :
      ∃ s : Fin (n + 1) → ℝ, StrictMono s ∧ ∀ k, p.IsRoot (s k) :=
      Polynomial.exists_strictMono_roots hp_splits hp_deg h_real_roots.1
    obtain ⟨r, hr_mono, hr_roots⟩ :
      ∃ r : Fin (n + 1) → ℝ, StrictMono r ∧ ∀ k, q.IsRoot (r k) :=
      Polynomial.exists_strictMono_roots hq_splits hq_deg h_real_roots.2
    have hs_surj : ∀ x ∈ p.roots, ∃ k, s k = x := by
      intro x hx
      have h_subset : Finset.image s Finset.univ ⊆ p.roots.toFinset := by
        rw [Finset.image_subset_iff]
        simp_all
      have h_card : p.roots.toFinset.card ≤ (Finset.image s Finset.univ).card := by
        rw [Finset.card_image_of_injective _ hs_mono.injective, Finset.card_univ,
          Fintype.card_fin]
        exact le_trans (Multiset.toFinset_card_le _)
          (hp_deg.symm ▸ Polynomial.card_roots' p)
      have h_eq := Finset.eq_of_subset_of_card_le h_subset h_card
      have hx_in : x ∈ Finset.image s Finset.univ :=
        h_eq.symm ▸ Multiset.mem_toFinset.mpr hx
      grind
    have hr_surj : ∀ x ∈ q.roots, ∃ k, r k = x := by
      intro x hx
      have h_subset : Finset.image r Finset.univ ⊆ q.roots.toFinset := by
        rw [Finset.image_subset_iff]
        simp_all
      have h_card : q.roots.toFinset.card ≤ (Finset.image r Finset.univ).card := by
        rw [Finset.card_image_of_injective _ hr_mono.injective, Finset.card_univ,
          Fintype.card_fin]
        exact le_trans (Multiset.toFinset_card_le _)
          (hq_deg.symm ▸ Polynomial.card_roots' q)
      have h_eq := Finset.eq_of_subset_of_card_le h_subset h_card
      have hx_in : x ∈ Finset.image r Finset.univ :=
        h_eq.symm ▸ Multiset.mem_toFinset.mpr hx
      grind
    have h_inter := Polynomial.has_root_between_roots_of_wronskian_pos
      hp_pos hq_pos hp_deg hq_deg hW
      r hr_mono hr_roots
    have h_inter' := StrictMono.fin_interlacing_of_root_between s r hs_mono ?_ ?_
    · exact StrictPrecSameDegree.of_fin_interlacing s r hs_mono hr_mono
        h_inter'.1 h_inter'.2 p q (leadingCoeff_ne_zero.mp hp_pos.ne')
        (leadingCoeff_ne_zero.mp hq_pos.ne') hp_splits hq_splits hp_deg hq_deg
        h_real_roots.1 h_real_roots.2 hs_surj hr_surj
    · obtain ⟨x, hx₁, hx₂⟩ := h_inter.1
      have hx_mem : x ∈ p.roots :=
        mem_roots'.mpr ⟨leadingCoeff_ne_zero.mp hp_pos.ne', hx₁⟩
      obtain ⟨k, rfl⟩ := hs_surj x hx_mem
      exact lt_of_le_of_lt (hs_mono.monotone (Nat.zero_le _)) hx₂
    · intro k
      obtain ⟨x, hx_root, hx_between⟩ := h_inter.2 k
      have hx_mem : x ∈ p.roots :=
        mem_roots'.mpr ⟨leadingCoeff_ne_zero.mp hp_pos.ne', hx_root⟩
      grind

lemma StrictPrecSameDegree.of_splits_and_posDef {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hB : (bezoutMatrix n q p).PosDef) :
    StrictPrecSameDegree p q :=
  match n with
  | 0 =>
    ⟨⟨leadingCoeff_ne_zero.mp hp_pos.ne', hp_splits⟩,
      ⟨leadingCoeff_ne_zero.mp hq_pos.ne', hq_splits⟩,
      hp_deg ▸ hq_deg ▸ rfl, by
        have hp_roots : p.roots = 0 :=
          Multiset.card_eq_zero.mp (hp_splits.natDegree_eq_card_roots.symm ▸ hp_deg)
        have hq_roots : q.roots = 0 :=
          Multiset.card_eq_zero.mp (hq_splits.natDegree_eq_card_roots.symm ▸ hq_deg)
        simp [hp_roots, hq_roots]⟩
  | m + 1 =>
    StrictPrecSameDegree.of_wronskian_pos hp_pos hq_pos hp_deg hq_deg hp_splits hq_splits fun t ↦
      bezoutMatrix.wronskian_pos_of_posDef hq_deg.le hp_deg.le hB t

lemma StrictPrecSameDegree.of_bezoutMatrix_posDef_three_le
    {p q : ℝ[X]} {n : ℕ}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n + 3) (hq_deg : q.natDegree = n + 3)
    (h : (bezoutMatrix (n + 3) q p).PosDef) :
    StrictPrecSameDegree p q :=
  let ⟨hp_s, hq_s⟩ := bezoutMatrix.splits_of_posDef hp_pos hq_pos hp_deg hq_deg h
  StrictPrecSameDegree.of_splits_and_posDef hp_pos hq_pos hp_deg hq_deg hp_s hq_s h

lemma _root_.Matrix.PosDef.det_pos_fin_two_entries {a b c : ℝ}
    (h : (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).PosDef) :
    0 < a * c - b * b := by
  have hdiag : 0 < (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := h.diag_pos
  have : 0 < a := by simpa using hdiag
  have hx : ![-b, a] ≠ (0 : Fin 2 → ℝ) := fun hzero => by simp_all
  have hquad := h.dotProduct_mulVec_pos hx
  norm_num [dotProduct, Matrix.mulVec] at hquad
  nlinarith

lemma bezoutMatrix.det_pos_of_quadratic_posDef {a b c d : ℝ}
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosDef) :
    0 < ((a + c) * (b * d) - (b + d) * (a * c)) * (b + d - (a + c)) -
    (b * d - a * c) * (b * d - a * c) := by
  rw [bezoutMatrix.quadratic_eq_fin_two] at h
  exact h.det_pos_fin_two_entries

lemma bezoutMatrix.det_factor_pos_of_quadratic_posDef {a b c d : ℝ}
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosDef) :
    0 < (a - b) * (a - d) * (b - c) * (c - d) := by
  have hdet := bezoutMatrix.det_pos_of_quadratic_posDef h
  grind

/-- For ordered quadratic factors, positive semidefiniteness of the Bezoutian
extracts the expected interleaving inequalities on the constants. -/
lemma bezoutMatrix.const_interleaves_of_quadratic_posSemidef {a b c d : ℝ}
    (hac : a ≤ c) (hbd : b ≤ d)
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosSemidef) :
    a ≤ b ∧ b ≤ c ∧ c ≤ d := by
  have h_sum := bezoutMatrix.sum_le_of_quadratic_posSemidef h
  have h_det := bezoutMatrix.det_factor_nonneg_of_quadratic_posSemidef h
  have hab : a ≤ b := by
    by_contra hnot
    have hba : b < a := not_le.mp hnot
    have hcd : c < d := by linarith
    have had : a < d := lt_of_le_of_lt hac hcd
    have hbc : b < c := lt_of_lt_of_le hba hac
    have h1 : (a - b) * (a - d) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hba) (sub_neg.mpr had)
    have h2 : 0 < (b - c) * (c - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hbc) (sub_neg.mpr hcd)
    nlinarith
  have hbc : b ≤ c := by
    by_contra hnot
    have hcb : c < b := not_le.mp hnot
    have hab' : a < b := lt_of_le_of_lt hac hcb
    have hcd : c < d := lt_of_lt_of_le hcb hbd
    have had : a < d := lt_of_le_of_lt hac hcd
    have h1 : 0 < (a - b) * (a - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hab') (sub_neg.mpr had)
    have h2 : (b - c) * (c - d) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hcb) (sub_neg.mpr hcd)
    nlinarith
  have hcd : c ≤ d := by
    by_contra hnot
    have hdc : d < c := not_le.mp hnot
    have hab' : a < b := by linarith
    have had : a < d := lt_of_lt_of_le hab' hbd
    have hbc' : b < c := lt_of_le_of_lt hbd hdc
    have h1 : 0 < (a - b) * (a - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hab') (sub_neg.mpr had)
    have h2 : (b - c) * (c - d) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hbc') (sub_pos.mpr hdc)
    nlinarith
  simp_all

/-- Ordered constants give the positive-semidefinite quadratic Bezoutian. -/
lemma bezoutMatrix.const_strictInterleaves_of_quadratic_posDef {a b c d : ℝ}
    (hac : a ≤ c) (hbd : b ≤ d)
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosDef) :
    a < b ∧ b < c ∧ c < d := by
  rcases bezoutMatrix.const_interleaves_of_quadratic_posSemidef hac hbd h.posSemidef with
    ⟨hab_le, hbc_le, hcd_le⟩
  have h_det := bezoutMatrix.det_factor_pos_of_quadratic_posDef h
  have hab_ne : a ≠ b := by
    rintro rfl
    simp_all
  have hbc_ne : b ≠ c := by
    rintro rfl
    simp_all
  have hcd_ne : c ≠ d := by
    rintro rfl
    simp_all
  grind

lemma bezoutMatrix.quadratic_posDef_two_of_const_strictInterleaves {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosDef := by
  rw [bezoutMatrix.quadratic_eq_fin_two]
  refine Matrix.posDef_fin_two_of_entries ?_ ?_
  · have hAeq : (a + c) * (b * d) - (b + d) * (a * c) =
        (b - a) * c ^ 2 + (d - c) * (b ^ 2 + (b - a) * (c - b)) := by ring
    rw [hAeq]
    have hba : 0 < b - a := sub_pos.mpr hab
    have hcb : 0 < c - b := sub_pos.mpr hbc
    have hdc : 0 < d - c := sub_pos.mpr hcd
    by_cases hc0 : c = 0
    · have hb0 : b ≠ 0 := by linarith
      have hb_pos : 0 < b ^ 2 + (b - a) * (c - b) :=
        add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hb0)
          (mul_nonneg hba.le hcb.le)
      nlinarith
    · have hleft : 0 < (b - a) * c ^ 2 :=
        mul_pos hba (sq_pos_of_ne_zero hc0)
      have h_nonneg : 0 ≤ (d - c) * (b ^ 2 + (b - a) * (c - b)) :=
        mul_nonneg hdc.le (add_nonneg (sq_nonneg b) (mul_nonneg hba.le hcb.le))
      nlinarith
  · have hdet_eq :
        ((a + c) * (b * d) - (b + d) * (a * c)) * (b + d - (a + c)) -
          (b * d - a * c) * (b * d - a * c) =
        (b - a) * (c - b) * (d - c) * (d - a) := by ring
    rw [hdet_eq]
    have : 0 < d - a := by linarith
    simp_all

lemma StrictPrecSameDegree.quadratic_of_const_strictInterleaves {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    StrictPrecSameDegree ((X + C b) * (X + C d)) ((X + C a) * (X + C c)) := by
  refine ⟨isRealRooted_mul (Polynomial.isRealRooted_X_add_C b).1
            (Polynomial.isRealRooted_X_add_C b).2
            (Polynomial.isRealRooted_X_add_C d).1
            (Polynomial.isRealRooted_X_add_C d).2,
          isRealRooted_mul (Polynomial.isRealRooted_X_add_C a).1
            (Polynomial.isRealRooted_X_add_C a).2
            (Polynomial.isRealRooted_X_add_C c).1
            (Polynomial.isRealRooted_X_add_C c).2,
          by rw [natDegree_mul (Polynomial.isRealRooted_X_add_C b).1
                   (Polynomial.isRealRooted_X_add_C d).1,
                 natDegree_mul (Polynomial.isRealRooted_X_add_C a).1
                   (Polynomial.isRealRooted_X_add_C c).1]; simp,
          ?_⟩
  rw [Polynomial.roots_sort_mul_X_add_C_X_add_C (by linarith : b ≤ d),
    Polynomial.roots_sort_mul_X_add_C_X_add_C (by linarith : a ≤ c)]
  simp [*]

lemma StrictPrecSameDegree.quadratic_iff_const_strictInterleaves {a b c d : ℝ}
    (hac : a ≤ c) (hbd : b ≤ d) :
    StrictPrecSameDegree ((X + C b) * (X + C d)) ((X + C a) * (X + C c)) ↔
      a < b ∧ b < c ∧ c < d := by
  constructor
  · rintro ⟨_, _, _, halt⟩
    rw [Polynomial.roots_sort_mul_X_add_C_X_add_C hbd,
      Polynomial.roots_sort_mul_X_add_C_X_add_C hac] at halt
    simp_all
  · exact fun ⟨hab, hbc, hcd⟩ ↦
      StrictPrecSameDegree.quadratic_of_const_strictInterleaves hab hbc hcd

lemma StrictPrecSameDegree.of_bezoutMatrix_quadratic_posDef {a b c d : ℝ}
    (hac : a ≤ c) (hbd : b ≤ d)
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosDef) :
    StrictPrecSameDegree ((X + C b) * (X + C d)) ((X + C a) * (X + C c)) :=
  let ⟨hab, hbc, hcd⟩ := bezoutMatrix.const_strictInterleaves_of_quadratic_posDef hac hbd h
  StrictPrecSameDegree.quadratic_of_const_strictInterleaves hab hbc hcd

lemma StrictPrecSameDegree.bezoutMatrix_quadratic_posDef {a b c d : ℝ}
    (hac : a ≤ c) (hbd : b ≤ d)
    (h : StrictPrecSameDegree ((X + C b) * (X + C d)) ((X + C a) * (X + C c))) :
    (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosDef :=
  let ⟨hab, hbc, hcd⟩ :=
    (StrictPrecSameDegree.quadratic_iff_const_strictInterleaves hac hbd).mp h
  bezoutMatrix.quadratic_posDef_two_of_const_strictInterleaves hab hbc hcd

lemma StrictPrecSameDegree.bezoutMatrix_posDef_quadratic
    {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2)
    (hprec : StrictPrecSameDegree p q) :
    (bezoutMatrix 2 q p).PosDef := by
  obtain ⟨hp_ne, hp_splits⟩ := hprec.1
  obtain ⟨hq_ne, hq_splits⟩ := hprec.2.1
  obtain ⟨b, d, hbd, hp_eq⟩ :=
    Polynomial.exists_sorted_linear_factors_of_isRealRooted_natDegree_two hp_splits hp_deg
  obtain ⟨a, c, hac, hq_eq⟩ :=
    Polynomial.exists_sorted_linear_factors_of_isRealRooted_natDegree_two hq_splits hq_deg
  let mp : ℝ[X] := (X + C b) * (X + C d)
  let mq : ℝ[X] := (X + C a) * (X + C c)
  let u : ℝ := q.leadingCoeff
  let v : ℝ := p.leadingCoeff
  have hu : 0 < u := hq_pos
  have hv : 0 < v := hp_pos
  have hq_eq' : q = C u * mq := hq_eq
  have hp_eq' : p = C v * mp := hp_eq
  have hprec_monic : StrictPrecSameDegree mp mq :=
    (StrictPrecSameDegree.C_mul_C_mul_iff hv.ne' hu.ne').mp (by grind)
  have hmonic : (bezoutMatrix 2 mq mp).PosDef :=
    StrictPrecSameDegree.bezoutMatrix_quadratic_posDef hac hbd hprec_monic
  have hscaled : (bezoutMatrix 2 (C u * mq) (C v * mp)).PosDef :=
    (bezoutMatrix.C_mul_C_mul_posDef_iff (n := 2) (u := u) (v := v) hu hv).mpr hmonic
  grind

lemma StrictPrecSameDegree.of_bezoutMatrix_posDef_of_isRealRooted_quadratic
    {p q : ℝ[X]}
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2)
    (h : (bezoutMatrix 2 q p).PosDef) :
    StrictPrecSameDegree p q := by
  obtain ⟨b, d, hbd, hp_eq⟩ :=
    Polynomial.exists_sorted_linear_factors_of_isRealRooted_natDegree_two hp_splits hp_deg
  obtain ⟨a, c, hac, hq_eq⟩ :=
    Polynomial.exists_sorted_linear_factors_of_isRealRooted_natDegree_two hq_splits hq_deg
  let mp : ℝ[X] := (X + C b) * (X + C d)
  let mq : ℝ[X] := (X + C a) * (X + C c)
  let u : ℝ := q.leadingCoeff
  let v : ℝ := p.leadingCoeff
  have hu : 0 < u := hq_pos
  have hv : 0 < v := hp_pos
  have hq_eq' : q = C u * mq := hq_eq
  have hp_eq' : p = C v * mp := hp_eq
  have hscaled : (bezoutMatrix 2 (C u * mq) (C v * mp)).PosDef := hp_eq' ▸ hq_eq' ▸ h
  have hmonic : (bezoutMatrix 2 mq mp).PosDef :=
    (bezoutMatrix.C_mul_C_mul_posDef_iff (n := 2) (u := u) (v := v) hu hv).mp hscaled
  have hprec_monic : StrictPrecSameDegree mp mq :=
    StrictPrecSameDegree.of_bezoutMatrix_quadratic_posDef hac hbd hmonic
  have hprec_scaled : StrictPrecSameDegree (C v * mp) (C u * mq) :=
    hprec_monic.C_mul_C_mul (ne_of_gt hv) (ne_of_gt hu)
  grind

lemma StrictPrecSameDegree.bezoutMatrix_posDef_iff_of_isRealRooted_quadratic
    {p q : ℝ[X]}
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix 2 q p).PosDef := by
  constructor
  · exact StrictPrecSameDegree.bezoutMatrix_posDef_quadratic
      hp_pos hq_pos hp_deg hq_deg
  · exact StrictPrecSameDegree.of_bezoutMatrix_posDef_of_isRealRooted_quadratic
      hp_splits hq_splits hp_pos hq_pos hp_deg hq_deg

lemma StrictPrecSameDegree.bezoutMatrix_posDef_iff_natDegree_zero
    {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 0) (hq_deg : q.natDegree = 0) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix 0 q p).PosDef := by
  obtain ⟨hp_ne, hp_splits⟩ :=
    isRealRooted_of_deg_zero (leadingCoeff_ne_zero.mp hp_pos.ne') hp_deg
  obtain ⟨hq_ne, hq_splits⟩ :=
    isRealRooted_of_deg_zero (leadingCoeff_ne_zero.mp hq_pos.ne') hq_deg
  constructor
  · intro hprec
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (bezoutMatrix.isHermitian _ _ _) ?_
    intro x hx
    exact False.elim (hx (funext fun i ↦ i.elim0))
  · intro _
    refine ⟨⟨hp_ne, hp_splits⟩, ⟨hq_ne, hq_splits⟩, hp_deg.trans hq_deg.symm, ?_⟩
    have hp_roots : p.roots.sort (· ≤ ·) = [] := by
      simp [Multiset.card_eq_zero.mp (hp_splits.natDegree_eq_card_roots.symm ▸ hp_deg)]
    have hq_roots : q.roots.sort (· ≤ ·) = [] := by
      simp [Multiset.card_eq_zero.mp (hq_splits.natDegree_eq_card_roots.symm ▸ hq_deg)]
    simp_all

lemma StrictPrecSameDegree.bezoutMatrix_posDef_iff_natDegree_one
    {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 1) (hq_deg : q.natDegree = 1) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix 1 q p).PosDef := by
  rcases Polynomial.exists_pos_scalar_mul_X_add_C_of_natDegree_one hp_pos hp_deg with
    ⟨u, a, hu, hp_eq⟩
  rcases Polynomial.exists_pos_scalar_mul_X_add_C_of_natDegree_one hq_pos hq_deg with
    ⟨v, b, hv, hq_eq⟩
  rw [hp_eq, hq_eq]
  calc
    StrictPrecSameDegree (C u * (X + C a)) (C v * (X + C b))
        ↔ StrictPrecSameDegree (X + C a) (X + C b) :=
      StrictPrecSameDegree.C_mul_C_mul_iff (ne_of_gt hu) (ne_of_gt hv)
    _ ↔ (bezoutMatrix 1 (X + C b) (X + C a)).PosDef :=
      StrictPrecSameDegree.X_add_C_bezoutMatrix_posDef_iff_one (a := b) (b := a)
    _ ↔ (bezoutMatrix 1 (C v * (X + C b)) (C u * (X + C a))).PosDef :=
      (bezoutMatrix.C_mul_C_mul_posDef_iff (n := 1) (u := v) (v := u) hv hu).symm

lemma StrictPrecSameDegree.bezoutMatrix_posDef_iff_natDegree_two
    {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix 2 q p).PosDef :=
  ⟨StrictPrecSameDegree.bezoutMatrix_posDef_quadratic hp_pos hq_pos hp_deg hq_deg, fun h ↦
    have hp_rr : p ≠ 0 ∧ p.Splits :=
      bezoutMatrix.right_isRealRooted_of_posDef_two_of_natDegree_two hp_deg hq_deg.le h
    have hq_rr : q ≠ 0 ∧ q.Splits :=
      bezoutMatrix.left_isRealRooted_of_posDef_two_of_natDegree_two hp_deg.le hq_deg h
    (StrictPrecSameDegree.bezoutMatrix_posDef_iff_of_isRealRooted_quadratic
      hp_rr.2 hq_rr.2 hp_pos hq_pos hp_deg hq_deg).mpr h⟩

/--
Strict same-degree Bezoutian characterization.

The orientation is chosen so that `StrictPrecSameDegree p q` corresponds to
positive definiteness of `bezoutMatrix n q p`.
-/
theorem strictPrecSameDegree_iff_bezoutMatrix_posDef
    {p q : ℝ[X]} {n : ℕ}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix n q p).PosDef :=
  match n, hp_deg, hq_deg with
  | 0, hp_deg, hq_deg =>
    StrictPrecSameDegree.bezoutMatrix_posDef_iff_natDegree_zero
      hp_pos hq_pos hp_deg hq_deg
  | 1, hp_deg, hq_deg =>
    StrictPrecSameDegree.bezoutMatrix_posDef_iff_natDegree_one
      hp_pos hq_pos hp_deg hq_deg
  | 2, hp_deg, hq_deg =>
    StrictPrecSameDegree.bezoutMatrix_posDef_iff_natDegree_two
      hp_pos hq_pos hp_deg hq_deg
  | _n + 3, hp_deg, hq_deg =>
    ⟨StrictPrecSameDegree.bezoutMatrix_posDef_three_le
       hp_pos hq_pos hp_deg hq_deg,
      StrictPrecSameDegree.of_bezoutMatrix_posDef_three_le
       hp_pos hq_pos hp_deg hq_deg⟩

end RealRooted
