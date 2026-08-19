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

-/

open Polynomial Matrix

noncomputable section

namespace RealRooted

protected lemma interleaves_reverse_of_interlaced_left :
    ∀ {ss rs : List ℝ} (h : ss.length + 1 = rs.length)
      (h_lt₁ : ∀ (i : Fin ss.length) (j : Fin rs.length),
        i.val + 1 = j.val → ss[i.val] < rs[j.val])
      (h_lt₂ : ∀ (i : Fin rs.length) (j : Fin ss.length),
        i.val < j.val + 1 → rs[i.val] < ss[j.val]),
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
    intro rs h h_lt₁ h_lt₂
    rcases rs with _ | ⟨r₁, _ | ⟨r₂, rs⟩⟩
    · simp at h
    · simp at h
    have h_len : ss.length + 1 = (r₂ :: rs).length := by
      simp only [List.length_cons] at h ⊢
      lia
    have h_eq_len₁ : ss.reverse.length + 1 = (rs.reverse ++ [r₂]).length := by simp_all
    have h_eq_len₂ : ss.reverse.length = rs.reverse.length := by simpa using h_len
    rw [List.reverse_cons, List.reverse_cons, List.reverse_cons,
      List.interleaves_append_singleton_append_singleton_of_length_add_one_eq_length h_eq_len₁,
      List.interleaves_append_singleton_append_singleton_of_length_eq_length h_eq_len₂,
      ← List.reverse_cons]
    refine ⟨h_lt₂ ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩ Nat.zero_lt_one,
      h_lt₁ ⟨0, Nat.zero_lt_succ _⟩ ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩ rfl,
      ih h_len ?_ ?_⟩
    · intro i j hij
      exact
        h_lt₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
          ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ (by lia)
    · intro i j hij
      exact
        h_lt₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
          ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ (by lia)

protected lemma interleaves_reverse_of_interlaced :
    ∀ {ss rs : List ℝ} (h : ss.length = rs.length)
      (h_lt₁ : ∀ (k : Fin ss.length), ss[k.val] < rs[k.val])
      (h_lt₂ : ∀ (i j : Fin ss.length), i.val < j.val → rs[i.val] < ss[j.val]),
      List.Interleaves (· > ·) ss.reverse rs.reverse := by
  intro ss
  induction ss with
  | nil =>
    intro rs h _ _
    rcases rs with _ | ⟨r, rs⟩
    · simp
    · simp at h
  | cons s ss ih =>
    intro rs h h_lt₁ h_lt₂
    rcases rs with _ | ⟨r, rs⟩
    · simp at h
    have h_len : ss.length = rs.length := by
      simp only [List.length_cons] at h ⊢
      lia
    have h_eq_len : ss.reverse.length = rs.reverse.length := by simp_all
    rw [List.reverse_cons, List.reverse_cons,
      List.interleaves_append_singleton_append_singleton_of_length_eq_length h_eq_len,
      ← List.reverse_cons]
    have h_len_left : ss.length + 1 = (r :: rs).length := by simp [h_len]
    refine ⟨h_lt₁ ⟨0, Nat.zero_lt_succ _⟩,
            RealRooted.interleaves_reverse_of_interlaced_left h_len_left ?_ ?_⟩
    · intro i j hij
      rcases i with ⟨i_val, hi⟩
      rcases j with ⟨_ | j_val, hj⟩
      · lia
      · have h_eq : i_val = j_val := by lia
        subst h_eq
        exact h_lt₁ ⟨i_val + 1, Nat.succ_lt_succ hi⟩
    · intro i j hij
      rcases i with ⟨_ | i_val, hi⟩
      · exact h_lt₂ ⟨0, Nat.zero_lt_succ _⟩ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
          (Nat.zero_lt_succ _)
      · exact h_lt₂ ⟨i_val + 1, h.symm ▸ hi⟩ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ hij

protected lemma List.Interleaves.ofFn {n : ℕ}
    (s r : Fin n → ℝ)
    (h_lt₁ : ∀ k : Fin n, s k < r k)
    (h_lt₂ : ∀ (i j : Fin n), i < j → r i < s j) :
    List.Interleaves (· > ·) (List.ofFn s).reverse (List.ofFn r).reverse := by
  have h_len : (List.ofFn s).length = (List.ofFn r).length := by simp
  refine RealRooted.interleaves_reverse_of_interlaced h_len ?_ ?_ <;> simp_all

protected lemma List.Interleaves.ofFn_succ {n : ℕ}
    (s : Fin n → ℝ) (t : Fin (n + 1) → ℝ)
    (h_lt₁ : ∀ (i : Fin n) (j : Fin (n + 1)), i.val + 1 = j.val → s i < t j)
    (h_lt₂ : ∀ (i : Fin (n + 1)) (j : Fin n), i.val < j.val + 1 → t i < s j) :
    List.Interleaves (· > ·) (List.ofFn s).reverse (List.ofFn t).reverse := by
  have h_len_st : (List.ofFn s).length + 1 = (List.ofFn t).length := by simp
  apply RealRooted.interleaves_reverse_of_interlaced_left h_len_st
  · intro i j hij
    have hi : i.val < n := by simpa using i.isLt
    have hj : j.val < n + 1 := by simpa using j.isLt
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact h_lt₁ ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
  · intro i j hij
    have hi : i.val < n + 1 := by simpa using i.isLt
    have hj : j.val < n := by simpa using j.isLt
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact h_lt₂ ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij


protected lemma interlaced_of_interleaves_reverse_left :
    ∀ {ss rs : List ℝ} (h : ss.length + 1 = rs.length)
      (_ : List.Interleaves (· > ·) ss.reverse rs.reverse),
      (∀ (i : Fin ss.length) (j : Fin rs.length), i.val + 1 = j.val →
        ss[i.val] < rs[j.val]) ∧
      (∀ (i : Fin rs.length) (j : Fin ss.length), i.val < j.val + 1 →
        rs[i.val] < ss[j.val]) := by
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
    have h_eq_len₁ : ss.reverse.length + 1 = (rs.reverse ++ [r₂]).length := by simp_all
    have h_eq_len₂ : ss.reverse.length = rs.reverse.length := by simp_all
    rw [List.reverse_cons, List.reverse_cons, List.reverse_cons,
      List.interleaves_append_singleton_append_singleton_of_length_add_one_eq_length h_eq_len₁,
      List.interleaves_append_singleton_append_singleton_of_length_eq_length h_eq_len₂,
      ← List.reverse_cons] at h_inter
    obtain ⟨hr₁s, hsr₂, h_inter_tail⟩ := h_inter
    have h_tail :
        (∀ (i : Fin ss.length) (j : Fin (r₂ :: rs).length),
          i.val + 1 = j.val → ss[i.val] < (r₂ :: rs)[j.val]) ∧
        (∀ (i : Fin (r₂ :: rs).length) (j : Fin ss.length),
          i.val < j.val + 1 → (r₂ :: rs)[i.val] < ss[j.val]) :=
      ih h_len h_inter_tail
    constructor
    · intro i j hij
      rcases i with ⟨_ | i_val, hi⟩
      · rcases j with ⟨_ | _ | j_val, hj⟩
        · contradiction
        · exact hsr₂
        · lia
      · rcases j with ⟨_ | j_val, hj⟩
        · contradiction
        · exact h_tail.1 ⟨i_val, Nat.lt_of_succ_lt_succ hi⟩
            ⟨j_val, Nat.lt_of_succ_lt_succ hj⟩ (Nat.succ.inj hij)
    · intro i j hij
      rcases i with ⟨_ | i_val, hi⟩
      · rcases j with ⟨_ | j_val, hj⟩
        · exact hr₁s
        · exact hr₁s.trans (hsr₂.trans (h_tail.2 ⟨0, Nat.zero_lt_succ _⟩
            ⟨j_val, Nat.lt_of_succ_lt_succ hj⟩ (Nat.zero_lt_succ _)))
      · rcases j with ⟨_ | j_val, hj⟩
        · contradiction
        · exact h_tail.2 ⟨i_val, Nat.lt_of_succ_lt_succ hi⟩
            ⟨j_val, Nat.lt_of_succ_lt_succ hj⟩ (Nat.succ_lt_succ_iff.mp hij)

protected lemma interlaced_of_interleaves_reverse :
    ∀ {ss rs : List ℝ} (h : ss.length = rs.length)
      (_ : List.Interleaves (· > ·) ss.reverse rs.reverse),
      (∀ (k : Fin ss.length), ss[k.val] < rs[k.val]) ∧
      (∀ (i j : Fin ss.length), i.val < j.val → rs[i.val] < ss[j.val]) := by
  intro ss
  induction ss with
  | nil =>
    simp
  | cons s ss ih =>
    intro rs h h_inter
    rcases rs with _ | ⟨r, rs⟩
    · simp at h
    have h_len : ss.length = rs.length := by simp_all
    have h_eq_len : ss.reverse.length = rs.reverse.length := by simp_all
    rw [List.reverse_cons, List.reverse_cons,
      List.interleaves_append_singleton_append_singleton_of_length_eq_length h_eq_len,
      ← List.reverse_cons] at h_inter
    obtain ⟨hsr, h_inter_tail⟩ := h_inter
    have h_len_left : ss.length + 1 = (r :: rs).length := by simp [h_len]
    have h_tail :
        (∀ (i : Fin ss.length) (j : Fin (r :: rs).length),
          i.val + 1 = j.val → ss[i.val] < (r :: rs)[j.val]) ∧
        (∀ (i : Fin (r :: rs).length) (j : Fin ss.length),
          i.val < j.val + 1 → (r :: rs)[i.val] < ss[j.val]) :=
      RealRooted.interlaced_of_interleaves_reverse_left h_len_left h_inter_tail
    constructor
    · intro k
      rcases k with ⟨_ | k_val, hk⟩
      · exact hsr
      · have h_lt : k_val + 1 < (r :: rs).length := by lia
        exact h_tail.1 ⟨k_val, Nat.lt_of_succ_lt_succ hk⟩ ⟨k_val + 1, h_lt⟩ rfl
    · intro i j hij
      rcases i with ⟨_ | i_val, hi⟩
      · rcases j with ⟨_ | j_val, hj⟩
        · lia
        · exact h_tail.2 ⟨0, Nat.zero_lt_succ _⟩ ⟨j_val, Nat.lt_of_succ_lt_succ hj⟩ hij
      · rcases j with ⟨_ | j_val, hj⟩
        · contradiction
        · have h_lt : i_val + 1 < (r :: rs).length := by lia
          exact h_tail.2 ⟨i_val + 1, h_lt⟩ ⟨j_val, Nat.lt_of_succ_lt_succ hj⟩ hij


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


def bezoutSeqEntry {A : Type*} [CommRing A] (a b : ℕ → A) (i j : ℕ) : A :=
  Finset.sum (Finset.range (min i j + 1)) fun k ↦
    a (i + j + 1 - k) * b k - b (i + j + 1 - k) * a k

lemma bezoutSeqEntry.comm {A : Type*} [CommRing A] (a b : ℕ → A) (i j : ℕ) :
    bezoutSeqEntry a b i j = bezoutSeqEntry a b j i := by
  simp [bezoutSeqEntry, Nat.add_comm, Nat.add_assoc, min_comm]

lemma bezoutSeqEntry.eq_zero_of_le_left {A : Type*} [CommRing A] (a b : ℕ → A)
    {n : ℕ} {i j : ℕ}
    (ha : ∀ k, n < k → a k = 0) (hb : ∀ k, n < k → b k = 0) (hi : n ≤ i) :
    bezoutSeqEntry a b i j = 0 := by
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  have hk_le : k ≤ min i j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hj_le : k ≤ j := hk_le.trans (min_le_right i j)
  have hp0 : a (i + j + 1 - k) = 0 := ha _ (by lia)
  have hq0 : b (i + j + 1 - k) = 0 := hb _ (by lia)
  simp [hp0, hq0]

lemma bezoutSeqEntry.eq_zero_of_le_right {A : Type*} [CommRing A] (a b : ℕ → A)
    {n : ℕ} {i j : ℕ}
    (ha : ∀ k, n < k → a k = 0) (hb : ∀ k, n < k → b k = 0) (hj : n ≤ j) :
    bezoutSeqEntry a b i j = 0 :=
  bezoutSeqEntry.comm a b j i ▸ bezoutSeqEntry.eq_zero_of_le_left a b ha hb hj

lemma bezoutSeqEntry.telescoping {A : Type*} [CommRing A] (a b : ℕ → A) (i j : ℕ) :
    bezoutSeqEntry a b i (j + 1) - bezoutSeqEntry a b (i + 1) j =
    a (i + 1) * b (j + 1) - a (j + 1) * b (i + 1) := by
  rcases le_or_gt i j with hij | hij
  · rcases eq_or_lt_of_le hij with rfl | h_lt
    · rw [bezoutSeqEntry.comm a b i (i + 1), sub_self]
      simp [*]
    · have hmin₁ : min i (j + 1) = i := min_eq_left (Nat.le_succ_of_le hij)
      have hmin₂ : min (i + 1) j = i + 1 := min_eq_left h_lt
      have h_index : (i + 1) + j + 1 - (i + 1) = j + 1 := by lia
      simp only [bezoutSeqEntry, hmin₁, hmin₂, Finset.sum_sub_distrib,
        Finset.sum_range_succ]
      rw [h_index]
      ring_nf
  · have hmin₁ : min i (j + 1) = j + 1 := min_eq_right hij
    have hmin₂ : min (i + 1) j = j := min_eq_right (Nat.le_succ_of_le hij.le)
    have h_index : i + (j + 1) + 1 - (j + 1) = i + 1 := by lia
    simp only [bezoutSeqEntry, hmin₁, hmin₂, Finset.sum_sub_distrib,
      Finset.sum_range_succ]
    rw [h_index]
    ring_nf

lemma bezoutSeqEntry.coeff_mul_sub_coeff_mul {A : Type*} [CommRing A] (a b : ℕ → A)
    (i j : ℕ) :
    a i * b j - a j * b i =
      (if i ≠ 0 then bezoutSeqEntry a b (i - 1) j else 0) -
        (if j ≠ 0 then bezoutSeqEntry a b i (j - 1) else 0) := by
  rcases i with _ | i
  · rcases j with _ | j
    · simp
    · simp [bezoutSeqEntry]
      ring
  · rcases j with _ | j
    · simp [bezoutSeqEntry]
      ring
    · simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        not_false_eq_true, ↓reduceIte, add_tsub_cancel_right]
      rw [← bezoutSeqEntry.telescoping]

lemma bezoutSeqEntry.bilinear_mul_sub {A : Type*} [CommRing A] (a b : ℕ → A)
    (n : ℕ) (t₁ t₂ : A)
    (ha : ∀ k, n < k → a k = 0) (hb : ∀ k, n < k → b k = 0) :
    (t₁ - t₂) * ∑ i : Fin n, ∑ j : Fin n,
    bezoutSeqEntry a b i.val j.val * t₁ ^ i.val * t₂ ^ j.val =
    (∑ i ∈ Finset.range (n + 1), a i * t₁ ^ i) *
      (∑ j ∈ Finset.range (n + 1), b j * t₂ ^ j) -
    (∑ i ∈ Finset.range (n + 1), a i * t₂ ^ i) *
      (∑ j ∈ Finset.range (n + 1), b j * t₁ ^ j) := by
  have h_eq_left (i j : ℕ) (hi : n ≤ i) : bezoutSeqEntry a b i j = 0 :=
    bezoutSeqEntry.eq_zero_of_le_left a b ha hb hi
  have h_eq_right (i j : ℕ) (hj : n ≤ j) : bezoutSeqEntry a b i j = 0 :=
    bezoutSeqEntry.eq_zero_of_le_right a b ha hb hj
  have h_telescope (i j : ℕ) :
      a i * b j - a j * b i =
        (if i ≠ 0 then bezoutSeqEntry a b (i - 1) j else 0) -
          (if j ≠ 0 then bezoutSeqEntry a b i (j - 1) else 0) :=
    bezoutSeqEntry.coeff_mul_sub_coeff_mul a b i j
  have h_rhs :
      (∑ i ∈ Finset.range (n + 1), a i * t₁ ^ i) *
        (∑ j ∈ Finset.range (n + 1), b j * t₂ ^ j) -
      (∑ i ∈ Finset.range (n + 1), a i * t₂ ^ i) *
        (∑ j ∈ Finset.range (n + 1), b j * t₁ ^ j) =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (a i * b j - a j * b i) * t₁ ^ i * t₂ ^ j := by
    have h_expand₁ :
        (∑ i ∈ Finset.range (n + 1), a i * t₁ ^ i) *
          (∑ j ∈ Finset.range (n + 1), b j * t₂ ^ j) =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          a i * b j * t₁ ^ i * t₂ ^ j := by
      rw [Finset.sum_mul_sum]
      simp only [mul_assoc, mul_left_comm]
    have h_expand₂ :
        (∑ i ∈ Finset.range (n + 1), a i * t₂ ^ i) *
          (∑ j ∈ Finset.range (n + 1), b j * t₁ ^ j) =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          a j * b i * t₁ ^ i * t₂ ^ j := by
      rw [Finset.sum_mul_sum, Finset.sum_comm]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    simp only [h_expand₁, h_expand₂, sub_mul, Finset.sum_sub_distrib]
  have h_rhs_sum :
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (a i * b j - a j * b i) * t₁ ^ i * t₂ ^ j =
      t₁ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n + 1),
        bezoutSeqEntry a b i j * t₁ ^ i * t₂ ^ j -
      t₂ * ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range n,
        bezoutSeqEntry a b i j * t₁ ^ i * t₂ ^ j := by
    have h_telescope_sum :
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (a i * b j - a j * b i) * t₁ ^ i * t₂ ^ j =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if i ≠ 0 then bezoutSeqEntry a b (i - 1) j else 0) * t₁ ^ i * t₂ ^ j -
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if j ≠ 0 then bezoutSeqEntry a b i (j - 1) else 0) * t₁ ^ i * t₂ ^ j := by
      simp only [h_telescope, sub_mul, Finset.sum_sub_distrib]
    convert h_telescope_sum using 2 <;> norm_num [Finset.sum_range_succ']
    · simp only [pow_succ', mul_assoc, mul_add, mul_comm, mul_left_comm, Finset.mul_sum]
    · simp only [pow_succ', mul_comm, mul_assoc, mul_left_comm, mul_add, Finset.mul_sum]
  rw [h_rhs, h_rhs_sum]
  simp [Finset.sum_range, Fin.sum_univ_castSucc, sub_mul, h_eq_left, h_eq_right]

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

lemma bezoutMatrix.mulVec_vandermonde_eq_zero_of_common_root
    {p q : ℝ[X]} {n : ℕ} {r : ℝ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h_pr : p.eval r = 0) (h_qr : q.eval r = 0) :
    (bezoutMatrix n p q).mulVec (fun j => r ^ (j : ℕ)) = 0 := by
  set c : Fin n → ℝ := fun i => ∑ j : Fin n, bezoutMatrix n p q i j * r ^ (j : ℕ) with hc
  set P : ℝ[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ) with hP
  have h_P_eval (t : ℝ) : P.eval t = ∑ i : Fin n, ∑ j : Fin n,
      bezoutEntry p q (i : ℕ) (j : ℕ) * t ^ (i : ℕ) * r ^ (j : ℕ) := by
    rw [hP]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, hc]
    simp_rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [bezoutMatrix]
    ring
  have h_roots_ne (t : ℝ) (htr : t ≠ r) : P.eval t = 0 := by
    have : (t - r) * ∑ i : Fin n, ∑ j : Fin n,
        bezoutEntry p q i.val j.val * t ^ i.val * r ^ j.val =
        p.eval t * q.eval r - p.eval r * q.eval t :=
      bezoutEntry.bilinear_mul_sub p q t r hp hq
    rw [← h_P_eval t, h_pr, h_qr, mul_zero, zero_mul, sub_zero] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr htr)
  have h_P_zero : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := {t : ℝ | t ≠ r}) h_roots_ne
    have : {t : ℝ | t ≠ r} = (Set.univ : Set ℝ) \ {r} := by
      ext t
      simp
    rw [this]
    exact Set.Infinite.sdiff Set.infinite_univ (Set.finite_singleton r)
  have h_c_zero (i : Fin n) : c i = 0 := by
    have : P.coeff (i : ℕ) = c i := by
      rw [hP, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [coeff_C_mul, coeff_X_pow]
        split_ifs with heq
        · exfalso
          exact hj (Fin.ext heq.symm)
        · exact mul_zero _
      · intro hi_univ
        exact (hi_univ (Finset.mem_univ i)).elim
    rw [← this, h_P_zero, coeff_zero]
  funext i
  simp only [mulVec, dotProduct]
  simp_all

lemma bezoutMatrix.det_eq_zero_of_common_root
    {p q : ℝ[X]} {n : ℕ} {r : ℝ} (hn : n ≠ 0)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h_pr : p.eval r = 0) (h_qr : q.eval r = 0) :
    (bezoutMatrix n p q).det = 0 := by
  by_contra h_det
  have h_inj : Function.Injective (bezoutMatrix n p q).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h_det))
  have h_vec_ne : (fun j : Fin n => r ^ (j : ℕ)) ≠ 0 := fun h ↦
    one_ne_zero (congr_fun h ⟨0, Nat.pos_of_ne_zero hn⟩)
  have : (bezoutMatrix n p q).mulVec (fun j => r ^ (j : ℕ)) = 0 :=
    mulVec_vandermonde_eq_zero_of_common_root hp hq h_pr h_qr
  exact h_vec_ne (h_inj (this.trans (mulVec_zero _).symm))

lemma bezoutMatrix.not_posDef_of_common_root
    {p q : ℝ[X]} {n : ℕ} {r : ℝ} (hn : n ≠ 0)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h_pr : p.eval r = 0) (h_qr : q.eval r = 0) :
    ¬ (bezoutMatrix n p q).PosDef :=
  fun h_pos ↦ lt_irrefl 0
    (det_eq_zero_of_common_root hn hp hq h_pr h_qr ▸ h_pos.det_pos)

lemma bezoutMatrix.no_common_real_root_of_posDef
    {p q : ℝ[X]} {n : ℕ} (hn : n ≠ 0)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h_pos : (bezoutMatrix n p q).PosDef) (r : ℝ) :
    ¬ (p.eval r = 0 ∧ q.eval r = 0) :=
  fun ⟨h_pr, h_qr⟩ ↦ not_posDef_of_common_root hn hp hq h_pr h_qr h_pos
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
      bezoutEntry.bilinear_mul_sub p q t₁ t hp hq
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
    (hr_roots : ∀ k : Fin n, q.eval (r k) = 0)
    (hr_inj : Function.Injective r)
    (k l : Fin n) (hkl : k ≠ l) :
    dotProduct (fun i : Fin n ↦ r k ^ (i : ℕ))
    ((bezoutMatrix n p q).mulVec (fun j : Fin n ↦ r l ^ (j : ℕ))) = 0 := by
  have h_bezoutian : ∑ i : Fin n, ∑ j : Fin n,
      bezoutEntry p q i.val j.val * r k ^ i.val * r l ^ j.val = 0 := by
    have h_mul := bezoutEntry.bilinear_mul_sub p q (r k) (r l) hp hq
    grind
  convert h_bezoutian using 1
  · simp only [bezoutMatrix, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

lemma bezoutMatrix.vandermonde_eq_diagonal (p q : ℝ[X]) (n : ℕ)
    (r : Fin n → ℝ) (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (hr_roots : ∀ k : Fin n, q.eval (r k) = 0)
    (hr_inj : Function.Injective r) :
    (vandermonde r) * (bezoutMatrix n p q) * (vandermonde r)ᵀ =
    Matrix.diagonal (fun k ↦ p.derivative.eval (r k) * q.eval (r k) -
    p.eval (r k) * q.derivative.eval (r k)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [diagonal_apply_eq, mul_apply, vandermonde_apply, transpose_apply]
    convert bezoutMatrix.vandermonde_diagonal p q n (r i) hp hq using 1
    · have (x y : Fin n) :
          r i ^ y.val * (r i ^ x.val * bezoutMatrix n p q x y) =
          r i ^ x.val * (r i ^ y.val * bezoutMatrix n p q x y) := by
        ring
      simpa only [mul_comm, Finset.mul_sum, dotProduct, Matrix.mulVec] using
        Finset.sum_comm.trans
          (Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ this x y)
  · simp only [diagonal_apply_ne _ hij, mul_apply, vandermonde_apply, transpose_apply]
    convert bezoutMatrix.vandermonde_off_diagonal p q n r hp hq hr_roots hr_inj i j hij using 1
    · simpa only [mul_comm, Finset.mul_sum, dotProduct, Matrix.mulVec, mul_left_comm] using
        Finset.sum_comm
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
  obtain ⟨h_inter1, h_inter2⟩ := RealRooted.interlaced_of_interleaves_reverse h_len h_interlaces
  constructor
  · intro k
    have hk : k.val < (List.map s (List.finRange n)).length := by simp
    simpa only [List.getElem_map, List.getElem_finRange, Fin.cast_mk] using
      h_inter1 ⟨k.val, hk⟩
  · intro i j hij
    have hi : i.val < (List.map s (List.finRange n)).length := by simp
    have hj : j.val < (List.map s (List.finRange n)).length := by simp
    simpa only [List.getElem_map, List.getElem_finRange, Fin.cast_mk] using
      h_inter2 ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
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

lemma bezoutEntry.bilinear_mul_sub_complex (p q : ℝ[X]) {n : ℕ} (z w : ℂ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (z - w) * ∑ i : Fin n, ∑ j : Fin n,
    (bezoutEntry p q i.val j.val : ℂ) * z ^ i.val * w ^ j.val =
    (p.map Complex.ofRealHom).eval z * (q.map Complex.ofRealHom).eval w -
    (p.map Complex.ofRealHom).eval w * (q.map Complex.ofRealHom).eval z := by
  have hp_zero (k : ℕ) (hk : n < k) : (p.map Complex.ofRealHom).coeff k = 0 := by
    rw [coeff_map]
    simp [coeff_eq_zero_of_natDegree_lt (hp.trans_lt hk)]
  have hq_zero (k : ℕ) (hk : n < k) : (q.map Complex.ofRealHom).coeff k = 0 := by
    rw [coeff_map]
    simp [coeff_eq_zero_of_natDegree_lt (hq.trans_lt hk)]
  have h_eq :
      (z - w) * ∑ i : Fin n, ∑ j : Fin n,
        bezoutSeqEntry (p.map Complex.ofRealHom).coeff (q.map Complex.ofRealHom).coeff
          i.val j.val * z ^ i.val * w ^ j.val =
      (∑ i ∈ Finset.range (n + 1), (p.map Complex.ofRealHom).coeff i * z ^ i) *
        (∑ j ∈ Finset.range (n + 1), (q.map Complex.ofRealHom).coeff j * w ^ j) -
      (∑ i ∈ Finset.range (n + 1), (p.map Complex.ofRealHom).coeff i * w ^ i) *
        (∑ j ∈ Finset.range (n + 1), (q.map Complex.ofRealHom).coeff j * z ^ j) :=
    bezoutSeqEntry.bilinear_mul_sub
      (p.map Complex.ofRealHom).coeff (q.map Complex.ofRealHom).coeff
      n z w hp_zero hq_zero
  simp_rw [← bezoutEntry.cast_complex] at h_eq
  have hp_lim : (p.map Complex.ofRealHom).natDegree < n + 1 := by
    rw [natDegree_map]
    exact Nat.lt_succ_of_le hp
  have hq_lim : (q.map Complex.ofRealHom).natDegree < n + 1 := by
    rw [natDegree_map]
    exact Nat.lt_succ_of_le hq
  simp_rw [Polynomial.eval_eq_sum_range' hp_lim,
    Polynomial.eval_eq_sum_range' hq_lim]
  exact h_eq

lemma PosDef.eq_zero_of_sum_mul_star_eq_zero {m : ℕ} {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.PosDef) (y : Fin m → ℂ)
    (hy_sum : ∑ i : Fin m, ∑ j : Fin m, (B i j : ℂ) * y i * starRingEnd ℂ (y j) = 0) :
    y = 0 := by
  have h_pos (x : Fin m → ℝ) :
      0 ≤ ∑ i : Fin m, ∑ j : Fin m, B i j * x i * x j := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (Matrix.PosDef.sum_pos hB hx).le
  have hre_zero : (fun i ↦ (y i).re) = 0 := by
    by_contra hre_ne
    have hre_pos : 0 < ∑ i : Fin m, ∑ j : Fin m, B i j * (y i).re * (y j).re :=
      Matrix.PosDef.sum_pos hB hre_ne
    have h_re_sum : ∑ i : Fin m, ∑ j : Fin m, B i j * (y i).re * (y j).re +
        ∑ i : Fin m, ∑ j : Fin m, B i j * (y i).im * (y j).im = 0 := by
      have :
          (∑ i : Fin m, ∑ j : Fin m,
            (B i j : ℂ) * y i * starRingEnd ℂ (y j)).re = 0 := by
        rw [hy_sum, Complex.zero_re]
      simp_all only [Complex.ext_iff, Complex.zero_re, Complex.zero_im,
        Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.conj_re, Complex.mul_im, add_zero, Complex.conj_im, mul_neg,
        sub_neg_eq_add, Finset.sum_add_distrib, Complex.im_sum, Finset.sum_neg_distrib]
    linarith [h_pos (fun i ↦ (y i).im), hre_pos, h_re_sum]
  have him_zero : (fun i ↦ (y i).im) = 0 := by
    have h_re_sum : ∑ i : Fin m, ∑ j : Fin m, B i j * (y i).re * (y j).re +
        ∑ i : Fin m, ∑ j : Fin m, B i j * (y i).im * (y j).im = 0 := by
      have :
          (∑ i : Fin m, ∑ j : Fin m,
            (B i j : ℂ) * y i * starRingEnd ℂ (y j)).re = 0 := by
        rw [hy_sum, Complex.zero_re]
      simp_all only [Complex.ext_iff, Complex.zero_re, Complex.zero_im,
        Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.conj_re, Complex.mul_im, add_zero, Complex.conj_im, mul_neg,
        sub_neg_eq_add, Finset.sum_add_distrib, Complex.im_sum, Finset.sum_neg_distrib]
    have hre_zero_pt (i : Fin m) : (y i).re = 0 := by
      have := congr_fun hre_zero i
      simpa using this
    simp only [hre_zero_pt, mul_zero, Finset.sum_const_zero, zero_add] at h_re_sum
    by_contra him_ne
    have him_pos : 0 < ∑ i : Fin m, ∑ j : Fin m, B i j * (y i).im * (y j).im :=
      Matrix.PosDef.sum_pos hB him_ne
    linarith [him_pos, h_re_sum]
  funext i
  exact Complex.ext (congr_fun hre_zero i) (congr_fun him_zero i)

lemma bezoutMatrix.no_complex_root_of_posDef {n : ℕ}
    {p q : ℝ[X]} (hp_deg : p.natDegree ≤ n + 1) (hq_deg : q.natDegree ≤ n + 1)
    (hB : (bezoutMatrix (n + 1) q p).PosDef)
    (z : ℂ) (hz : 0 < z.im) (hroot : (p.map Complex.ofRealHom).eval z = 0) :
    False := by
  have h_star_root : (p.map Complex.ofRealHom).eval (starRingEnd ℂ z) = 0 := by
    simpa [eval_eq_sum_range] using congr_arg Star.star hroot
  have h_bezoutian : (z - starRingEnd ℂ z) * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      (bezoutEntry q p i.val j.val : ℂ) * z ^ i.val * (starRingEnd ℂ z) ^ j.val = 0 := by
    convert bezoutEntry.bilinear_mul_sub_complex q p z
      (starRingEnd ℂ z) hq_deg hp_deg using 1
    simp_all only [eval_map, mul_zero, sub_zero]
  have h_z_ne : z - starRingEnd ℂ z ≠ 0 := by
    intro hdiff
    have him := congr_arg Complex.im hdiff
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
    linarith
  have hsum : ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      (bezoutMatrix (n + 1) q p i j : ℂ) * z ^ i.val * starRingEnd ℂ (z ^ j.val) = 0 := by
    have hsum_aux := (mul_eq_zero.mp h_bezoutian).resolve_left h_z_ne
    simpa only [bezoutMatrix, map_pow] using hsum_aux
  have h_y_ne : (fun (i : Fin (n + 1)) ↦ z ^ i.val) ≠ 0 := fun h ↦
    one_ne_zero (congr_fun h ⟨0, Nat.zero_lt_succ n⟩)
  have h_y_zero :=
    PosDef.eq_zero_of_sum_mul_star_eq_zero hB (fun (i : Fin (n + 1)) ↦ z ^ i.val) hsum
  exact h_y_ne h_y_zero

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

lemma tendsto_eval_mul_neg_one_pow_atBot {n : ℕ} {p : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hp_deg : p.natDegree = n + 1) :
    Filter.Tendsto (fun x ↦ p.eval x * (-1) ^ (n + 1)) Filter.atBot Filter.atTop := by
  have h_leading :
      0 < Polynomial.leadingCoeff (p.comp (-Polynomial.X)) * (-1) ^ (n + 1) := by
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
    refine ⟨Polynomial.natDegree_pos_iff_degree_pos.mp ?_, ?_⟩
    · simp [*]
    · simpa [hp_deg] using h_leading.le
  have h_tendsto_neg :
      Filter.Tendsto (fun x ↦ p.eval (-x) * (-1) ^ (n + 1)) Filter.atTop Filter.atTop := by
    simp_all
  convert h_tendsto_neg.comp Filter.tendsto_neg_atBot_atTop using 2
  simp

lemma mul_neg_of_pos_mul_neg_one_pow_succ {n : ℕ} {a b : ℝ}
    (ha : 0 < a * (-1) ^ n) (hb : 0 < b * (-1) ^ (n + 1)) :
    b * a < 0 := by
  have h_pow : (-1 : ℝ) ^ (n + 1) = -((-1) ^ n) := by
    rw [pow_succ]
    ring
  have h_sq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  rw [h_pow] at hb
  nlinarith [hb, ha, h_sq]

lemma exists_index_eq_of_mem_roots {n : ℕ} {p : ℝ[X]} (s : Fin n → ℝ) (hs : StrictMono s)
    (hs_root : ∀ k, p.IsRoot (s k)) (hp_ne : p ≠ 0) (hp_deg : p.natDegree ≤ n)
    (x : ℝ) (hx : x ∈ p.roots) : ∃ i, s i = x := by
  have h_subset : Finset.image s Finset.univ ⊆ p.roots.toFinset := by
    rw [Finset.image_subset_iff]
    intro k _
    exact Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hp_ne, hs_root k⟩)
  have h_card : p.roots.toFinset.card ≤ (Finset.image s Finset.univ).card := by
    rw [Finset.card_image_of_injective _ hs.injective, Finset.card_univ, Fintype.card_fin]
    exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' p |>.trans hp_deg)
  have h_eq := Finset.eq_of_subset_of_card_le h_subset h_card
  have hx_in : x ∈ Finset.image s Finset.univ := by
    rwa [h_eq, Multiset.mem_toFinset]
  rcases Finset.mem_image.mp hx_in with ⟨i, _, hi⟩
  exact ⟨i, hi⟩

lemma prod_sub_eq_neg_one_pow_mul_prod_abs {m : ℕ}
    (r : Fin m → ℝ) (hr : StrictMono r) (k : Fin m) :
    ∏ j ∈ Finset.univ.erase k, (r k - r j) = (-1) ^ (m - 1 - k.val) *
      ∏ j ∈ Finset.univ.erase k, |r k - r j| := by
  have h_prod_sign_abs : ∏ j ∈ Finset.univ.erase k, (r k - r j) =
      ∏ j ∈ Finset.univ.erase k,
        (-1) ^ (if k < j then 1 else 0) * |r k - r j| := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    split_ifs with hjk
    · simp only [pow_one, neg_mul, one_mul]
      rw [abs_of_neg (sub_neg.mpr (hr hjk))]
      ring
    · simp only [pow_zero, one_mul]
      rw [abs_of_nonneg (sub_nonneg.mpr (hr.monotone (not_lt.mp hjk)))]
  rw [h_prod_sign_abs, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 2
  have : (Finset.univ.erase k).filter (fun x ↦ k < x) = Finset.Ioi k := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, Finset.mem_Ioi, and_true]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨ne_of_gt h, h⟩⟩
  rw [Finset.sum_boole, this, Fin.card_Ioi]
  rfl

lemma sign_p_at_root_of_wronskian_pos {n : ℕ}
    {p q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q) (hq_deg : q.natDegree = n + 1)
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t)
    (r : Fin (n + 1) → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k))
    (k : Fin (n + 1)) : 0 < p.eval (r k) * (-1) ^ (n - k.val) := by
  have hq_eq : q = C q.leadingCoeff * ∏ j : Fin (n + 1),
    (X - C (r j)) := by
    convert Polynomial.splits_eq_C_mul_prod _ _ _ _ _
    · exact leadingCoeff_ne_zero.mp hq_pos.ne'
    · simp_all
    · simp_all
    · exact hr_mono.injective
  have h_eval_deriv :
      q.derivative.eval (r k) =
        q.leadingCoeff * ∏ j ∈ Finset.erase Finset.univ k, (r k - r j) := by
    conv_lhs => rw [hq_eq]
    exact Polynomial.eval_derivative_C_mul_prod_X_sub_C_univ_at_root
      q.leadingCoeff r k
  have h_sign_change_prod :
      0 < p.eval (r k) * ∏ j ∈ Finset.erase Finset.univ k, (r k - r j) := by
    have := hW (r k)
    have hq_eval : q.eval (r k) = 0 := hr_roots k
    rw [hq_eval, zero_mul, sub_zero, h_eval_deriv, mul_assoc] at this
    have h_prod := pos_of_mul_pos_right this hq_pos.le
    rwa [mul_comm] at h_prod
  have h_prod_sign := prod_sub_eq_neg_one_pow_mul_prod_abs r hr_mono k
  have : n + 1 - 1 - k.val = n - k.val := rfl
  rw [this] at h_prod_sign
  rw [h_prod_sign] at h_sign_change_prod
  nlinarith [show 0 < ∏ j ∈ Finset.univ.erase k, |r k - r j| from
    Finset.prod_pos fun j hj ↦ abs_pos.mpr <| sub_ne_zero.mpr <|
      hr_mono.injective.ne (Finset.ne_of_mem_erase hj).symm]

lemma sign_change_p_of_wronskian_pos {n : ℕ}
    {p q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q) (hq_deg : q.natDegree = n + 1)
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t)
    (r : Fin (n + 1) → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k))
    (k : Fin n) : p.eval (r (Fin.castSucc k)) * p.eval (r (Fin.succ k)) < 0 := by
  have h_sign_change_k := sign_p_at_root_of_wronskian_pos hq_pos hq_deg hW
    r hr_mono hr_roots (Fin.castSucc k)
  have h_sign_change_succ := sign_p_at_root_of_wronskian_pos hq_pos hq_deg hW
    r hr_mono hr_roots (Fin.succ k)
  have h_eq : n - (Fin.castSucc k : ℕ) = n - (Fin.succ k : ℕ) + 1 := by
    have : (Fin.castSucc k : ℕ) = k.val := rfl
    have : (Fin.succ k : ℕ) = k.val + 1 := rfl
    lia
  rw [h_eq] at h_sign_change_k
  exact mul_neg_of_pos_mul_neg_one_pow_succ h_sign_change_succ h_sign_change_k

lemma Polynomial.exists_root_between_roots_of_wronskian_pos {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n + 1) (hq_deg : q.natDegree = n + 1)
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t -
    q.eval t * p.derivative.eval t)
    (r : Fin (n + 1) → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k)) :
    (∃ x, p.IsRoot x ∧ x < r 0) ∧
    (∀ k : Fin n, ∃ x, p.IsRoot x ∧ r k.castSucc < x ∧ x < r k.succ) := by
  constructor
  · have h_sign_change_zero : 0 < p.eval (r 0) * (-1) ^ n :=
      sign_p_at_root_of_wronskian_pos hq_pos hq_deg hW r hr_mono hr_roots 0
    have h_tendsto_bot :
        Filter.Tendsto (fun x ↦ p.eval x * (-1) ^ (n + 1)) Filter.atBot Filter.atTop :=
      tendsto_eval_mul_neg_one_pow_atBot hp_pos hp_deg
    have h_sign_change_bot : ∃ x : ℝ, x < r 0 ∧ 0 < p.eval x * (-1) ^ (n + 1) :=
      (Filter.Eventually.and (Filter.eventually_lt_atBot (r 0))
        (h_tendsto_bot.eventually_gt_atTop 0)).exists
    obtain ⟨x, hx₁, hx₂⟩ := h_sign_change_bot
    have h_ivt : ∃ c ∈ Set.Ioo x (r 0), p.eval c = 0 := by
      have h_cont : ContinuousOn (fun t ↦ p.eval t) (Set.Icc x (r 0)) :=
        p.continuous.continuousOn
      have h_sign_change_ends : p.eval x * p.eval (r 0) < 0 :=
        mul_neg_of_pos_mul_neg_one_pow_succ h_sign_change_zero hx₂
      rw [mul_neg_iff] at h_sign_change_ends
      rcases h_sign_change_ends with h | h
      · exact intermediate_value_Ioo' hx₁.le h_cont (Set.mem_Ioo.mpr ⟨h.2, h.1⟩)
      · exact intermediate_value_Ioo hx₁.le h_cont (Set.mem_Ioo.mpr ⟨h.1, h.2⟩)
    rcases h_ivt with ⟨c, hc_in, hc_root⟩
    exact ⟨c, hc_root, hc_in.2⟩
  · intro k
    have h_ivt : ∃ x ∈ Set.Ioo (r (Fin.castSucc k)) (r (Fin.succ k)), p.eval x = 0 := by
      have h_cont :
          ContinuousOn (fun x ↦ p.eval x)
            (Set.Icc (r (Fin.castSucc k)) (r (Fin.succ k))) :=
        p.continuous.continuousOn
      have := sign_change_p_of_wronskian_pos hq_pos hq_deg hW r hr_mono hr_roots k
      rw [mul_neg_iff] at this
      have hle : r (Fin.castSucc k) ≤ r (Fin.succ k) :=
        hr_mono.monotone (Nat.le_succ _)
      rcases this with h | h
      · exact intermediate_value_Ioo' hle h_cont (Set.mem_Ioo.mpr ⟨h.2, h.1⟩)
      · exact intermediate_value_Ioo hle h_cont (Set.mem_Ioo.mpr ⟨h.1, h.2⟩)
    rcases h_ivt with ⟨c, hc_in, hc_root⟩
    exact ⟨c, hc_root, hc_in⟩

lemma sign_p_at_root_of_wronskian_pos' {n : ℕ}
    {p q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q)
    (hq_deg : q.natDegree = n)
    (hW : ∀ t : ℝ, 0 < p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t)
    (r : Fin n → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k))
    (k : Fin n) : 0 < p.eval (r k) * (-1) ^ (n - k.val) := by
  have hq_eq : q = C q.leadingCoeff * ∏ j : Fin n, (X - C (r j)) :=
    Polynomial.splits_eq_C_mul_prod (leadingCoeff_ne_zero.mp hq_pos.ne')
      hq_deg r hr_roots hr_mono.injective
  have h_eval_deriv :
      q.derivative.eval (r k) =
        q.leadingCoeff * ∏ j ∈ Finset.erase Finset.univ k, (r k - r j) := by
    conv_lhs => rw [hq_eq]
    exact Polynomial.eval_derivative_C_mul_prod_X_sub_C_univ_at_root q.leadingCoeff r k
  have h_W_val :
      0 < p.derivative.eval (r k) * q.eval (r k) - p.eval (r k) * q.derivative.eval (r k) :=
    hW (r k)
  rw [hr_roots k, mul_zero, zero_sub, h_eval_deriv] at h_W_val
  have h_prod_neg : p.eval (r k) *
      (∏ j ∈ Finset.erase Finset.univ k, (r k - r j)) < 0 := by
    have : 0 < q.leadingCoeff := hq_pos
    nlinarith [h_W_val, this]
  have h_prod_sign :
      ∏ j ∈ Finset.univ.erase k, (r k - r j) =
        (-1) ^ (n - 1 - k.val) * ∏ j ∈ Finset.univ.erase k, |r k - r j| :=
    prod_sub_eq_neg_one_pow_mul_prod_abs r hr_mono k
  have h_abs_pos : 0 < ∏ j ∈ Finset.univ.erase k, |r k - r j| :=
    Finset.prod_pos fun j hj ↦ abs_pos.mpr <| sub_ne_zero.mpr <|
      hr_mono.injective.ne (Finset.ne_of_mem_erase hj).symm
  rw [h_prod_sign] at h_prod_neg
  have : n - k.val = (n - 1 - k.val) + 1 := by lia
  rw [this, pow_succ]
  nlinarith [h_abs_pos, h_prod_neg]

lemma sign_change_p_of_wronskian_pos' {n : ℕ}
    {p q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q)
    (hq_deg : q.natDegree = n)
    (hW : ∀ t : ℝ, 0 < p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t)
    (r : Fin n → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k))
    (k : Fin n) (hk : k.val + 1 < n) :
    p.eval (r k) * p.eval (r ⟨k.val + 1, hk⟩) < 0 := by
  have hk₀ : 0 < p.eval (r k) * (-1) ^ (n - k.val) :=
    sign_p_at_root_of_wronskian_pos' hq_pos hq_deg hW r hr_mono hr_roots k
  have hk₁ : 0 < p.eval (r ⟨k.val + 1, hk⟩) * (-1) ^ (n - (k.val + 1)) :=
    sign_p_at_root_of_wronskian_pos' hq_pos hq_deg hW r hr_mono hr_roots ⟨k.val + 1, hk⟩
  have : n - k.val = (n - (k.val + 1)) + 1 := by lia
  rw [this] at hk₀
  exact mul_neg_of_pos_mul_neg_one_pow_succ hk₁ hk₀

lemma exists_root_between_consecutive_of_wronskian_pos {n : ℕ}
    {p q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q)
    (hq_deg : q.natDegree = n)
    (hW : ∀ t : ℝ, 0 < p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t)
    (r : Fin n → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k))
    (k : Fin n) (hk : k.val + 1 < n) :
    ∃ x, p.IsRoot x ∧ r k < x ∧ x < r ⟨k.val + 1, hk⟩ := by
  have : p.eval (r k) * p.eval (r ⟨k.val + 1, hk⟩) < 0 :=
    sign_change_p_of_wronskian_pos' hq_pos hq_deg hW r hr_mono hr_roots k hk
  have h_lt : r k < r ⟨k.val + 1, hk⟩ := hr_mono (Nat.lt_succ_self k.val)
  have h_cont : ContinuousOn (fun t ↦ p.eval t) (Set.Icc (r k) (r ⟨k.val + 1, hk⟩)) :=
    p.continuous.continuousOn
  rw [mul_neg_iff] at this
  rcases this with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · obtain ⟨c, hc_in, hc_root⟩ :=
      intermediate_value_Ioo' h_lt.le h_cont (Set.mem_Ioo.mpr ⟨h₂, h₁⟩)
    exact ⟨c, hc_root, hc_in.1, hc_in.2⟩
  · obtain ⟨c, hc_in, hc_root⟩ :=
      intermediate_value_Ioo h_lt.le h_cont (Set.mem_Ioo.mpr ⟨h₁, h₂⟩)
    exact ⟨c, hc_root, hc_in.1, hc_in.2⟩

lemma exists_root_below_min_of_wronskian_pos {n : ℕ} (hn : n ≠ 0)
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n + 1) (hq_deg : q.natDegree = n)
    (hW : ∀ t : ℝ, 0 < p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t)
    (r : Fin n → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k)) :
    ∃ x, p.IsRoot x ∧ x < r ⟨0, Nat.pos_of_ne_zero hn⟩ := by
  set k : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  have h_sign₀ : 0 < p.eval (r k) * (-1) ^ (n - k.val) :=
    sign_p_at_root_of_wronskian_pos' hq_pos hq_deg hW r hr_mono hr_roots k
  simp only [k, Nat.sub_zero] at h_sign₀
  have h_tendsto_bot :
      Filter.Tendsto (fun x ↦ p.eval x * (-1) ^ (n + 1)) Filter.atBot Filter.atTop :=
    tendsto_eval_mul_neg_one_pow_atBot hp_pos hp_deg
  obtain ⟨x, hx₁, hx₂⟩ := (Filter.Eventually.and (Filter.eventually_lt_atBot (r k))
    (h_tendsto_bot.eventually_gt_atTop 0)).exists
  have h_cont : ContinuousOn (fun t ↦ p.eval t) (Set.Icc x (r k)) :=
    p.continuous.continuousOn
  have : p.eval x * p.eval (r k) < 0 :=
    mul_neg_of_pos_mul_neg_one_pow_succ h_sign₀ hx₂
  rw [mul_neg_iff] at this
  rcases this with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · obtain ⟨c, hc_in, hc_root⟩ :=
      intermediate_value_Ioo' hx₁.le h_cont (Set.mem_Ioo.mpr ⟨h₂, h₁⟩)
    exact ⟨c, hc_root, hc_in.2⟩
  · obtain ⟨c, hc_in, hc_root⟩ :=
      intermediate_value_Ioo hx₁.le h_cont (Set.mem_Ioo.mpr ⟨h₁, h₂⟩)
    exact ⟨c, hc_root, hc_in.2⟩

lemma exists_root_above_max_of_wronskian_pos {n : ℕ} (hn : n ≠ 0)
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n + 1) (hq_deg : q.natDegree = n)
    (hW : ∀ t : ℝ, 0 < p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t)
    (r : Fin n → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k)) :
    ∃ x, p.IsRoot x ∧ r ⟨n - 1, Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.one_pos⟩ < x := by
  set k : Fin n := ⟨n - 1, Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.one_pos⟩
  have hsign : 0 < p.eval (r k) * (-1) ^ (n - (n - 1)) :=
    sign_p_at_root_of_wronskian_pos' hq_pos hq_deg hW r hr_mono hr_roots k
  have : n - (n - 1) = 1 := by lia
  rw [this, pow_one] at hsign
  have : p.eval (r k) < 0 := by simp_all
  have h_tendsto_top : Filter.Tendsto (fun x ↦ p.eval x) Filter.atTop Filter.atTop := by
    apply Polynomial.tendsto_atTop_of_leadingCoeff_nonneg
    · rw [← Polynomial.natDegree_pos_iff_degree_pos, hp_deg]
      exact Nat.succ_pos n
    · exact hp_pos.le
  obtain ⟨x, hx₁, hx₂⟩ := (Filter.Eventually.and
    (Filter.eventually_gt_atTop (r k))
    (h_tendsto_top.eventually_gt_atTop 0)).exists
  have h_cont : ContinuousOn (fun t ↦ p.eval t) (Set.Icc (r k) x) :=
    p.continuous.continuousOn
  obtain ⟨c, hc_in, hc_root⟩ :=
    intermediate_value_Ioo hx₁.le h_cont (Set.mem_Ioo.mpr ⟨this, hx₂⟩)
  exact ⟨c, hc_root, hc_in.1⟩

lemma apply_lt_of_card_lt_le {m : ℕ} {t : Fin m → ℝ} (ht : StrictMono t) {c : ℝ}
    {k : Fin m} (h_card : k.val + 1 ≤ (Finset.univ.filter (fun i ↦ t i < c)).card) :
    t k < c := by
  rwa [← Tuple.lt_card_lt_iff_apply_lt_of_monotone ht.monotone]

lemma lt_apply_of_card_le_le {m : ℕ} {t : Fin m → ℝ} (ht : StrictMono t) {c : ℝ}
    {k : Fin m} (h_card : (Finset.univ.filter (fun i ↦ t i ≤ c)).card ≤ k.val) :
    c < t k := by
  rwa [← not_le, ← Tuple.lt_card_le_iff_apply_le_of_monotone ht.monotone, not_lt]

lemma card_le_filter_of_inj_roots {N l : ℕ} {p : ℝ[X]} {t : Fin N → ℝ}
    (ht_surj : ∀ x ∈ p.roots, ∃ i, t i = x)
    (hp_ne : p ≠ 0) (g : Fin l → ℝ) (hg_inj : Function.Injective g)
    (hg_root : ∀ j, p.IsRoot (g j)) (P : ℝ → Prop) [DecidablePred P]
    (hg_prop : ∀ j, P (g j)) :
    l ≤ (Finset.univ.filter (fun i ↦ P (t i))).card := by
  have h_mem (j : Fin l) : ∃ i : Fin N, t i = g j :=
    ht_surj (g j) (mem_roots'.mpr ⟨hp_ne, hg_root j⟩)
  choose idx h_idx using h_mem
  have h_idx_inj : Function.Injective idx := fun a b hab ↦
    hg_inj ((h_idx a).symm.trans ((congr_arg t hab).trans (h_idx b)))
  have h_sub : Finset.univ.image idx ⊆ Finset.univ.filter (fun i ↦ P (t i)) := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h_idx y).symm ▸ hg_prop y⟩
  rw [← Fintype.card_fin l, ← Finset.card_univ,
    ← Finset.card_image_of_injective _ h_idx_inj]
  exact Finset.card_le_card h_sub

lemma card_lt_le_of_inj_roots {N l : ℕ} {p : ℝ[X]} {t : Fin N → ℝ}
    (ht_surj : ∀ x ∈ p.roots, ∃ i, t i = x)
    (hp_ne : p ≠ 0) {c : ℝ} (g : Fin l → ℝ) (hg_inj : Function.Injective g)
    (hg_root : ∀ j, p.IsRoot (g j)) (hg_lt : ∀ j, g j < c) :
    l ≤ (Finset.univ.filter (fun i ↦ t i < c)).card :=
  card_le_filter_of_inj_roots ht_surj hp_ne g hg_inj hg_root (fun x ↦ x < c) hg_lt

lemma card_gt_le_of_inj_roots {N l : ℕ} {p : ℝ[X]} {t : Fin N → ℝ}
    (ht_surj : ∀ x ∈ p.roots, ∃ i, t i = x)
    (hp_ne : p ≠ 0) {c : ℝ} (g : Fin l → ℝ) (hg_inj : Function.Injective g)
    (hg_root : ∀ j, p.IsRoot (g j)) (hg_gt : ∀ j, c < g j) :
    l ≤ (Finset.univ.filter (fun i ↦ c < t i)).card :=
  card_le_filter_of_inj_roots ht_surj hp_ne g hg_inj hg_root (fun x ↦ c < x) hg_gt

lemma Polynomial.roots_nodup_of_wronskian_pos {p q : ℝ[X]}
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t) :
    p.roots.Nodup ∧ q.roots.Nodup := by
  constructor
  · apply Polynomial.roots_nodup_of_splits_and_simple
    intro r hr hd
    have := hW r
    simp_all
  · apply Polynomial.roots_nodup_of_splits_and_simple
    intro r hr hd
    have := hW r
    simp_all

lemma StrictPrecSameDegree.of_wronskian_pos {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t -
    q.eval t * p.derivative.eval t) :
    StrictPrecSameDegree p q := by
  rcases n with (_ | n)
  · rw [eq_C_of_natDegree_eq_zero hp_deg] at hW ⊢
    rw [eq_C_of_natDegree_eq_zero hq_deg] at hW ⊢
    simp_all
  · have h_real_roots := Polynomial.roots_nodup_of_wronskian_pos hW
    obtain ⟨s, hs_mono, hs_roots⟩ :
      ∃ s : Fin (n + 1) → ℝ, StrictMono s ∧ ∀ k, p.IsRoot (s k) :=
      Polynomial.exists_strictMono_roots hp_splits hp_deg h_real_roots.1
    obtain ⟨r, hr_mono, hr_roots⟩ :
      ∃ r : Fin (n + 1) → ℝ, StrictMono r ∧ ∀ k, q.IsRoot (r k) :=
      Polynomial.exists_strictMono_roots hq_splits hq_deg h_real_roots.2
    have hs_surj : ∀ x ∈ p.roots, ∃ k, s k = x :=
      fun x hx ↦ exists_index_eq_of_mem_roots s hs_mono hs_roots
        (leadingCoeff_ne_zero.mp hp_pos.ne') hp_deg.le x hx
    have hr_surj : ∀ x ∈ q.roots, ∃ k, r k = x :=
      fun x hx ↦ exists_index_eq_of_mem_roots r hr_mono hr_roots
        (leadingCoeff_ne_zero.mp hq_pos.ne') hq_deg.le x hx
    have h_inter := Polynomial.exists_root_between_roots_of_wronskian_pos
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

lemma strictMono_of_lt_and_lt {n : ℕ} {α : Type*} [LinearOrder α]
    (u : Fin (n + 1) → α) (s : Fin n → α)
    (hu_hi : ∀ i : Fin n, u i.castSucc < s i)
    (hu_lo : ∀ i : Fin n, s i < u i.succ) :
    StrictMono u := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  exact lt_trans (hu_hi i) (hu_lo i)

lemma interlace_of_interlaced_roots {n : ℕ} {p : ℝ[X]} (hp_ne : p ≠ 0)
    (t : Fin (n + 1) → ℝ) (ht_mono : StrictMono t) (ht_surj : ∀ x ∈ p.roots, ∃ i, t i = x)
    (u : Fin (n + 1) → ℝ) (hu_mono : StrictMono u) (hu_root : ∀ i, p.IsRoot (u i))
    (s : Fin n → ℝ) (hs_mono : StrictMono s)
    (hu_hi : ∀ i : Fin n, u i.castSucc < s i)
    (hu_lo : ∀ i : Fin n, s i < u i.succ)
    (k : Fin n) : t k.castSucc < s k ∧ s k < t k.succ := by
  have h_le : k.val + 1 ≤ n + 1 := by lia
  let g_low : Fin (k.val + 1) → ℝ := fun j ↦ u (Fin.castLE h_le j)
  have hg_low_lt (j : Fin (k.val + 1)) : g_low j < s k := by
    simp only [g_low]
    have h_lt' : (Fin.castLE h_le j).val < n := by
      simp [Fin.castLE]
      lia
    have h_lt_j := hu_hi ⟨(Fin.castLE h_le j).val, h_lt'⟩
    refine lt_of_lt_of_le h_lt_j (hs_mono.monotone ?_)
    simp only [Fin.le_def, Fin.val_castLE]
    lia
  have hg_low_mono : StrictMono g_low :=
    fun a b hab ↦ hu_mono (Fin.strictMono_castLE h_le hab)
  have h_card_l : k.val + 1 ≤ (Finset.univ.filter (fun i ↦ t i < s k)).card :=
    card_lt_le_of_inj_roots ht_surj hp_ne g_low hg_low_mono.injective
      (fun j ↦ hu_root _) hg_low_lt
  have h_lt_high (j : Fin (n - k.val)) : k.val + j.val + 1 < n + 1 := by lia
  let g_high : Fin (n - k.val) → ℝ := fun j => u ⟨k.val + j.val + 1, h_lt_high j⟩
  have hg_high_gt (j : Fin (n - k.val)) : s k < g_high j := by
    simp only [g_high]
    have h_pos' : k.val + j.val < n := by lia
    have hlo := hu_lo ⟨k.val + j.val, h_pos'⟩
    refine lt_of_le_of_lt (hs_mono.monotone ?_) hlo
    simp only [Fin.le_def]
    lia
  have hg_high_mono : StrictMono g_high := by
    intro a b hab
    simp only [g_high]
    apply hu_mono
    simp only [Fin.lt_def]
    simp [*]
  have h_card_h : n - k.val ≤ (Finset.univ.filter (fun i ↦ s k < t i)).card :=
    card_gt_le_of_inj_roots ht_surj hp_ne g_high hg_high_mono.injective
      (fun j ↦ hu_root _) hg_high_gt
  refine ⟨apply_lt_of_card_lt_le ht_mono h_card_l, lt_apply_of_card_le_le ht_mono ?_⟩
  have h_part : (Finset.univ.filter (fun i ↦ t i ≤ s k)).card +
      (Finset.univ.filter (fun i ↦ s k < t i)).card = n + 1 := by
    have h_eq : (Finset.univ.filter (fun i : Fin (n + 1) ↦ s k < t i)) =
        (Finset.univ.filter (fun i => ¬ t i ≤ s k)) := by
      simp
    rw [h_eq, Finset.card_filter_add_card_filter_not]
    simp
  simp only [Fin.val_succ]
  lia

lemma exists_strictMono_u_of_bounds {α : Type*} [LinearOrder α] {n : ℕ} (hn : n ≠ 0)
    (s : Fin n → α)
    (xl xh : α) (h_xl_lt : xl < s ⟨0, Nat.pos_of_ne_zero hn⟩)
    (h_xh_gt : s ⟨n - 1, Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.one_pos⟩ < xh)
    (xb : Fin (n - 1) → α)
    (h_xb_lo : ∀ j : Fin (n - 1), s ⟨j.val, by lia⟩ < xb j)
    (h_xb_hi : ∀ j : Fin (n - 1), xb j < s ⟨j.val + 1, by lia⟩)
    (P : α → Prop) (h_xl_P : P xl) (h_xh_P : P xh) (h_xb_P : ∀ j : Fin (n - 1), P (xb j)) :
    ∃ u : Fin (n + 1) → α, StrictMono u ∧
      (∀ i : Fin n, u i.castSucc < s i) ∧
      (∀ i : Fin n, s i < u i.succ) ∧
      (∀ i : Fin (n + 1), P (u i)) := by
  let u : Fin (n + 1) → α := fun i ↦
    if h0 : i.val = 0 then xl
    else if hn' : i.val = n then xh
    else xb ⟨i.val - 1, by lia⟩
  have hu_hi (i : Fin (n + 1)) (hi : i.val < n) : u i < s ⟨i.val, hi⟩ := by
    simp only [u]
    split_ifs with h₀ hn'
    · have : i = ⟨0, by lia⟩ := Fin.ext h₀
      subst this
      exact h_xl_lt
    · lia
    · have h_lt_n₁ : i.val - 1 < n - 1 := by lia
      have hb := h_xb_hi ⟨i.val - 1, h_lt_n₁⟩
      have heq : (⟨i.val - 1 + 1, by lia⟩ : Fin n) = ⟨i.val, hi⟩ := Fin.ext (by lia)
      rwa [heq] at hb
  have hu_lo (i : Fin (n + 1)) (hi : 0 < i.val) : s ⟨i.val - 1, by lia⟩ < u i := by
    simp only [u]
    split_ifs with h₀ hn'
    · lia
    · have : i = ⟨n, by lia⟩ := Fin.ext hn'
      subst this
      exact h_xh_gt
    · exact h_xb_lo ⟨i.val - 1, by lia⟩
  have hu_mono : StrictMono u :=
    strictMono_of_lt_and_lt u s (fun i ↦ hu_hi i.castSucc i.isLt)
      (fun i ↦ hu_lo i.succ (by simp))
  refine
    ⟨u, hu_mono, fun i ↦ hu_hi i.castSucc i.isLt,
      fun i ↦ hu_lo i.succ (by simp), fun i ↦ ?_⟩
  simp only [u]
  split_ifs with h₀ hn'
  · exact h_xl_P
  · exact h_xh_P
  · exact h_xb_P ⟨i.val - 1, by lia⟩

lemma prec_of_wronskian_pos_succ {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n + 1) (hq_deg : q.natDegree = n)
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hW : ∀ t : ℝ, 0 < p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t) :
    Prec q p := by
  have hp_ne : p ≠ 0 := leadingCoeff_ne_zero.mp hp_pos.ne'
  have hq_ne : q ≠ 0 := leadingCoeff_ne_zero.mp hq_pos.ne'
  have hpq_nodup := Polynomial.roots_nodup_of_wronskian_pos hW
  have hp_nodup : p.roots.Nodup := hpq_nodup.2
  have hq_nodup : q.roots.Nodup := hpq_nodup.1
  obtain ⟨s, hs_mono, hs_roots⟩ := Polynomial.exists_strictMono_roots hq_splits hq_deg hq_nodup
  obtain ⟨t, ht_mono, ht_roots⟩ := Polynomial.exists_strictMono_roots hp_splits hp_deg hp_nodup
  have hs_surj : ∀ x ∈ q.roots, ∃ i, s i = x :=
    fun x hx ↦ exists_index_eq_of_mem_roots s hs_mono hs_roots hq_ne hq_deg.le x hx
  have ht_surj : ∀ x ∈ p.roots, ∃ i, t i = x :=
    fun x hx ↦ exists_index_eq_of_mem_roots t ht_mono ht_roots hp_ne hp_deg.le x hx
  rcases eq_or_ne n 0 with hn₀ | hn
  · subst hn₀
    have hq_roots : q.roots = 0 := by
      rw [← Multiset.card_eq_zero, ← Splits.natDegree_eq_card_roots hq_splits, hq_deg]
    have hp_roots : p.roots = {t 0} := by
      have : p.roots.card = 1 := by
        rw [← Splits.natDegree_eq_card_roots hp_splits, hp_deg]
      obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp this
      have ht₀_mem : t 0 ∈ p.roots := mem_roots'.mpr ⟨hp_ne, ht_roots 0⟩
      rw [ha] at ht₀_mem ⊢
      rw [Multiset.mem_singleton.mp ht₀_mem]
    refine ⟨⟨hq_ne, hq_splits⟩, ⟨hp_ne, hp_splits⟩, [], [t 0], by simp, by simp,
      by simp [hq_roots], by simp [hp_roots], ?_⟩
    left
    constructor <;> simp [ListInterlaces]
  classical
  obtain ⟨xl, h_xl_root, h_xl_lt⟩ :=
    exists_root_below_min_of_wronskian_pos hn hp_pos hq_pos hp_deg hq_deg hW s hs_mono hs_roots
  obtain ⟨xh, h_xh_root, h_xh_gt⟩ :=
    exists_root_above_max_of_wronskian_pos hn hp_pos hq_pos hp_deg hq_deg hW s hs_mono hs_roots
  have hj_lt (j : Fin (n - 1)) : j.val < n := by lia
  have hj_succ_lt (j : Fin (n - 1)) : j.val + 1 < n := by lia
  have h_between (j : Fin (n - 1)) :
      ∃ x, p.IsRoot x ∧ s ⟨j.val, hj_lt j⟩ < x ∧ x < s ⟨j.val + 1, hj_succ_lt j⟩ := by
    obtain ⟨x, hx_root, hx_lo, hx_hi⟩ :=
      exists_root_between_consecutive_of_wronskian_pos hq_pos hq_deg hW s hs_mono hs_roots
        ⟨j.val, hj_lt j⟩ (hj_succ_lt j)
    exact ⟨x, hx_root, hx_lo, hx_hi⟩
  choose xb h_xb_root h_xb_lo h_xb_hi using h_between
  obtain ⟨u, hu_mono, hu_hi, hu_lo, hu_root⟩ :=
    exists_strictMono_u_of_bounds hn s xl xh h_xl_lt h_xh_gt xb h_xb_lo h_xb_hi
      (fun x ↦ p.IsRoot x) h_xl_root h_xh_root h_xb_root
  have h_interlace (k : Fin n) : t k.castSucc < s k ∧ s k < t k.succ :=
    interlace_of_interlaced_roots hp_ne t ht_mono ht_surj u hu_mono hu_root s hs_mono hu_hi hu_lo k
  have h_len_st : (List.ofFn s).length + 1 = (List.ofFn t).length := by simp
  refine
    ⟨⟨hq_ne, hq_splits⟩, ⟨hp_ne, hp_splits⟩, q.roots.sort (· ≤ ·),
      p.roots.sort (· ≤ ·), Multiset.pairwise_sort _ _, Multiset.pairwise_sort _ _,
      by simp, by simp, Or.inl ⟨?_, ?_⟩⟩
  · rw [Multiset.length_sort, Multiset.length_sort]
    rw [← Splits.natDegree_eq_card_roots hp_splits, ← Splits.natDegree_eq_card_roots hq_splits,
      hp_deg, hq_deg]
  · rw [Polynomial.roots_sort_eq_ofFn hq_ne hq_splits hq_deg hq_nodup s hs_mono hs_surj,
      Polynomial.roots_sort_eq_ofFn hp_ne hp_splits hp_deg hp_nodup t ht_mono ht_surj]
    apply listInterlaces_of_interleaves_of_length h_len_st
    apply List.Interleaves.mono (r := fun a b : ℝ => a < b) (fun a b h => h.le)
    rw [← List.interleaves_reverse_reverse_of_length_add_one_eq_length
      (r := fun a b : ℝ => a > b) h_len_st]
    apply List.Interleaves.ofFn_succ s t
    · intro i j hij
      rcases j with ⟨j_val, hj⟩
      subst hij
      exact (h_interlace ⟨i.val, i.isLt⟩).2
    · intro i j hij
      have hlt : t (⟨j.val, j.isLt⟩ : Fin n).castSucc < s ⟨j.val, j.isLt⟩ :=
        (h_interlace ⟨j.val, j.isLt⟩).1
      have h_le_ij : ⟨i.val, i.isLt⟩ ≤ (⟨j.val, j.isLt⟩ : Fin n).castSucc := by
        simp only [Fin.le_def, Fin.val_castSucc]
        lia
      have hle : t ⟨i.val, i.isLt⟩ ≤ t (⟨j.val, j.isLt⟩ : Fin n).castSucc :=
        ht_mono.monotone h_le_ij
      exact lt_of_le_of_lt hle hlt
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
theorem StrictPrecSameDegree.to_prec {p q : ℝ[X]} (h : StrictPrecSameDegree p q) : Prec p q := by
  obtain ⟨⟨hp_ne, hp_splits⟩, ⟨hq_ne, hq_splits⟩, hdeg, h_inter⟩ := h
  have h_len : (p.roots.sort (· ≤ ·)).length = (q.roots.sort (· ≤ ·)).length := by
    simp [card_roots_of_splits, *]
  rw [List.interleaves_reverse_reverse_of_length_eq_length h_len] at h_inter
  have h_le : List.Interleaves (· ≤ ·) (q.roots.sort (· ≤ ·))
      (p.roots.sort (· ≤ ·)) := h_inter.mono fun _ _ hab ↦ le_of_lt hab
  exact
    ⟨⟨hp_ne, hp_splits⟩, ⟨hq_ne, hq_splits⟩, p.roots.sort (· ≤ ·),
      q.roots.sort (· ≤ ·), Multiset.pairwise_sort .., Multiset.pairwise_sort ..,
      Multiset.sort_eq _ _, Multiset.sort_eq _ _,
      Or.inr ⟨h_len, (listAlternates_iff_interleaves_of_length h_len).2 h_le⟩⟩
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
    have h₁ : (a - b) * (a - d) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hba) (sub_neg.mpr had)
    have h₂ : 0 < (b - c) * (c - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hbc) (sub_neg.mpr hcd)
    nlinarith
  have hbc : b ≤ c := by
    by_contra hnot
    have hcb : c < b := not_le.mp hnot
    have hab' : a < b := lt_of_le_of_lt hac hcb
    have hcd : c < d := lt_of_lt_of_le hcb hbd
    have had : a < d := lt_of_le_of_lt hac hcd
    have h₁ : 0 < (a - b) * (a - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hab') (sub_neg.mpr had)
    have h₂ : (b - c) * (c - d) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hcb) (sub_neg.mpr hcd)
    nlinarith
  have hcd : c ≤ d := by
    by_contra hnot
    have hdc : d < c := not_le.mp hnot
    have hab' : a < b := by linarith
    have had : a < d := lt_of_lt_of_le hab' hbd
    have hbc' : b < c := lt_of_le_of_lt hbd hdc
    have h₁ : 0 < (a - b) * (a - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hab') (sub_neg.mpr had)
    have h₂ : (b - c) * (c - d) < 0 :=
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
