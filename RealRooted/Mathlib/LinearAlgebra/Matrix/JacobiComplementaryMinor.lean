/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Jacobi's complementary minor identity and the inverse of a totally nonnegative matrix

For real square matrices `A` and `B` with `A * B = 1`, Jacobi's identity expresses a minor of `B`
through the complementary minor of `A` and `A.det`, with the sign `(-1) ^ (∑ s + ∑ t)`. The proof
reorders rows and columns by `finSumEquivOfFinset`, tracks the sign of the resulting permutation,
and compares determinants of block matrices. As a consequence, if a totally nonnegative matrix
`A` has determinant one, then its inverse conjugated by alternating signs is totally nonnegative.

## Main statements

* `Matrix.jacobi_minor`: for `A * B = 1`, with `s.card = t.card = k`,
  `(-1) ^ (∑ z ∈ s, z + ∑ z ∈ t, z) * A.det * (B.submatrix s t).det` equals the complementary
  minor `(A.submatrix tᶜ sᶜ).det` (rows and columns taken in increasing order).
* `Matrix.tn_inverse`: if `A * B = 1`, `A.det = 1` and `A.IsTotallyNonneg`, then the matrix
  `((-1) ^ (i + j) * B i j)` is totally nonnegative.
-/

@[expose] public section

open Finset Equiv

namespace Matrix

noncomputable section

/-! ## Jacobi's complementary minor identity and total nonnegativity of the inverse -/

section Jacobi
open Finset Equiv

variable {N : ℕ}

private def sortEquiv (s : Finset (Fin N)) {k : ℕ} (h : s.card = k) : Fin k ⊕ Fin (N - k) ≃ Fin N :=
  finSumEquivOfFinset h (by rw [Finset.card_compl, Fintype.card_fin, h])

private lemma sortEquiv_congr {s t : Finset (Fin N)} {k : ℕ} (hs : s.card = k) (ht : t.card = k)
    (hst : s = t) : sortEquiv s hs = sortEquiv t ht := by subst hst; rfl

private lemma swap_strictMono_comp {u : Finset (Fin N)} {x y : Fin N} (hxy : y.val = x.val + 1)
    (hu : ¬ (x ∈ u ∧ y ∈ u)) {m : ℕ} {f : Fin m → Fin N} (hf : StrictMono f)
    (hfu : ∀ i, f i ∈ u) : StrictMono (fun i => Equiv.swap x y (f i)) := by
  intro i j hij
  have h1 := hf hij
  have hi := hfu i
  have hj := hfu j
  simp only [Equiv.swap_apply_def]
  rw [Fin.lt_def] at h1
  split_ifs with a b c d e f g h <;> simp only [Fin.lt_def] <;>
    simp_all [Fin.ext_iff] <;> lia

private lemma sortEquiv_move {s : Finset (Fin N)} {k : ℕ} (h : s.card = k) {x y : Fin N}
    (hxy : y.val = x.val + 1) (hx : x ∈ s) (hy : y ∉ s) (h' : (insert y (s.erase x)).card = k) :
    sortEquiv (insert y (s.erase x)) h' = (sortEquiv s h).trans (Equiv.swap x y) := by
  have hne : x ≠ y := by intro e; subst e; exact hy hx
  ext (i | i) : 1
  · simp only [sortEquiv, finSumEquivOfFinset_inl, Equiv.trans_apply]
    have := Finset.orderEmbOfFin_unique h'
      (f := fun i => Equiv.swap x y (s.orderEmbOfFin h i)) ?_ ?_
    · exact (congrFun this i).symm
    · intro i
      have hi := s.orderEmbOfFin_mem h i
      simp only [Equiv.swap_apply_def]
      split_ifs with a b
      · simp
      · rw [b] at hi; exact absurd hi hy
      · simp [Finset.mem_erase, a, hi]
    · exact swap_strictMono_comp hxy (fun hh => hy hh.2) (s.orderEmbOfFin h).strictMono
        (s.orderEmbOfFin_mem h)
  · simp only [sortEquiv, finSumEquivOfFinset_inr, Equiv.trans_apply]
    have hc : (insert y (s.erase x))ᶜ.card = N - k := by
      rw [Finset.card_compl, Fintype.card_fin, h']
    have := Finset.orderEmbOfFin_unique hc
      (f := fun i => Equiv.swap x y
        (sᶜ.orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin, h]) i)) ?_ ?_
    · exact (congrFun this i).symm
    · intro i
      have hi := sᶜ.orderEmbOfFin_mem (by rw [Finset.card_compl, Fintype.card_fin, h]) i
      rw [Finset.mem_compl] at hi
      simp only [Equiv.swap_apply_def]
      split_ifs with a b
      · rw [a] at hi; exact absurd hx hi
      · simp [Finset.mem_erase, Finset.mem_compl, hne]
      · simp [Finset.mem_erase, a, b]
    · exact swap_strictMono_comp hxy (fun hh => (Finset.mem_compl.1 hh.1) hx)
        (sᶜ.orderEmbOfFin _).strictMono (sᶜ.orderEmbOfFin_mem _)

private def initSeg (N k : ℕ) : Finset (Fin N) := univ.filter (fun z => z.val < k)

private lemma card_initSeg {k : ℕ} (hk : k ≤ N) : (initSeg N k).card = k := by
  simp [initSeg, Fin.card_filter_val_lt, hk]

private lemma exists_down_move {s : Finset (Fin N)} {k : ℕ} (h : s.card = k) (hk : k ≤ N)
    (hne : s ≠ initSeg N k) :
    ∃ y ∈ s, 0 < y.val ∧ ∀ x : Fin N, x.val + 1 = y.val → x ∉ s := by
  obtain ⟨x, hx0, hxs⟩ : ∃ x ∈ initSeg N k, x ∉ s := by
    by_contra hc
    push Not at hc
    exact hne (Finset.eq_of_subset_of_card_le hc (by rw [h, card_initSeg hk])).symm
  have hxk : x.val < k := by simpa [initSeg] using hx0
  have hT : (s.filter (fun z => x < z)).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hc
    have hsub : s ⊆ Finset.Iio x := by
      intro z hz
      have := hc hz
      rw [Finset.mem_Iio]
      rcases lt_trichotomy z x with h1 | h1 | h1
      · exact h1
      · subst h1; exact absurd hz hxs
      · exact absurd h1 this
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio, h] at this
    lia
  set y := (s.filter (fun z => x < z)).min' hT with hy
  have hymem := (s.filter (fun z => x < z)).min'_mem hT
  rw [← hy, Finset.mem_filter] at hymem
  refine ⟨y, hymem.1, ?_, ?_⟩
  · have := hymem.2; rw [Fin.lt_def] at this; lia
  · intro z hz hzs
    have hxz : x ≤ z := by
      have := hymem.2; rw [Fin.lt_def] at this; rw [Fin.le_def]; lia
    rcases hxz.lt_or_eq with h1 | h1
    · have := (s.filter (fun z => x < z)).min'_le z (Finset.mem_filter.2 ⟨hzs, h1⟩)
      rw [← hy, Fin.le_def] at this; lia
    · subst h1; exact hxs hzs

private lemma sign_sortEquiv_init {k : ℕ} (hk : k ≤ N) :
    ∀ (s : Finset (Fin N)) (h : s.card = k),
    Perm.sign ((sortEquiv (initSeg N k) (card_initSeg hk)).symm.trans (sortEquiv s h)) *
      (-1 : ℤˣ) ^ (∑ z ∈ s, (z : ℕ)) = (-1) ^ (∑ z ∈ initSeg N k, (z : ℕ)) := by
  intro s
  induction hn : ∑ z ∈ s, (z : ℕ) using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  intro h
  by_cases hs : s = initSeg N k
  · subst hs; subst hn; simp
  obtain ⟨y, hys, hy0, hy⟩ := exists_down_move h hk hs
  set x : Fin N := ⟨y.val - 1, by lia⟩ with hxdef
  have hxs : x ∉ s := hy x (by simp [hxdef]; lia)
  have hxy : y.val = x.val + 1 := by simp [hxdef]; lia
  have hne : x ≠ y := by intro e; rw [e] at hxs; exact hxs hys
  set s' := insert x (s.erase y) with hs'
  have hcard : s'.card = k := by
    rw [hs', Finset.card_insert_of_notMem (by simp [hxs]), Finset.card_erase_of_mem hys, h]
    have : 0 < k := by rw [← h]; exact Finset.card_pos.2 ⟨y, hys⟩
    lia
  have hback : insert y (s'.erase x) = s := by
    rw [hs', Finset.erase_insert (by simp [hxs])]
    exact Finset.insert_erase hys
  have hmove := sortEquiv_move hcard hxy (by simp [hs']) (by simp [hs', hne.symm])
    (by rw [hback, h])
  rw [sortEquiv_congr _ h hback] at hmove
  have hsum : ∑ z ∈ s, (z : ℕ) = ∑ z ∈ s', (z : ℕ) + 1 := by
    rw [hs', Finset.sum_insert (by simp [hxs]), ← Finset.add_sum_erase s _ hys]
    lia
  have := ih (∑ z ∈ s', (z : ℕ)) (by lia) s' rfl hcard
  rw [hmove, ← Equiv.trans_assoc, Perm.sign_trans, Perm.sign_swap hne, ← hn, hsum, pow_succ]
  rw [← this]
  simp only [mul_neg, mul_one, neg_mul, neg_neg]
  rw [one_mul]

private lemma sign_sortEquiv {s t : Finset (Fin N)} {k : ℕ} (hs : s.card = k) (ht : t.card = k) :
    (Perm.sign ((sortEquiv s hs).symm.trans (sortEquiv t ht)) : ℤ) =
      (-1) ^ (∑ z ∈ s, (z : ℕ) + ∑ z ∈ t, (z : ℕ)) := by
  have hk : k ≤ N := by rw [← hs]; simpa using Finset.card_le_univ s
  have h1 := sign_sortEquiv_init hk s hs
  have h2 := sign_sortEquiv_init hk t ht
  set E0 := sortEquiv (initSeg N k) (card_initSeg hk)
  have : (sortEquiv s hs).symm.trans (sortEquiv t ht) =
      (E0.symm.trans (sortEquiv s hs)).symm.trans (E0.symm.trans (sortEquiv t ht)) := by
    ext z; simp
  rw [this, Perm.sign_trans, Perm.sign_symm]
  have key : ∀ (u : ℤˣ) (n m : ℕ), u * (-1) ^ n = (-1) ^ m → u = (-1) ^ m * (-1) ^ n := by
    intro u n m hu
    rw [← hu, mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  rw [key _ _ _ h1, key _ _ _ h2]
  push_cast
  rw [pow_add]
  have : ((-1 : ℤ) ^ (∑ z ∈ initSeg N k, (z : ℕ))) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination ((-1 : ℤ) ^ ∑ z ∈ t, (z:ℕ)) * ((-1 : ℤ) ^ ∑ z ∈ s, (z:ℕ)) * this

/-- The complement of a `k`-subset of `Fin N` has `N - k` elements. -/
lemma card_compl_eq {s : Finset (Fin N)} {k : ℕ} (h : s.card = k) : sᶜ.card = N - k := by
  rw [Finset.card_compl, Fintype.card_fin, h]

/-- Jacobi's complementary minor identity (with `A * B = 1`). -/
lemma jacobi_minor (A B : Matrix (Fin N) (Fin N) ℝ) (hAB : A * B = 1) {s t : Finset (Fin N)}
    {k : ℕ} (hs : s.card = k) (ht : t.card = k) :
    (-1 : ℝ) ^ (∑ z ∈ s, (z : ℕ) + ∑ z ∈ t, (z : ℕ)) * A.det *
      (B.submatrix (s.orderEmbOfFin hs) (t.orderEmbOfFin ht)).det =
    (A.submatrix (tᶜ.orderEmbOfFin (card_compl_eq ht))
      (sᶜ.orderEmbOfFin (card_compl_eq hs))).det := by
  set es := sortEquiv s hs
  set et := sortEquiv t ht
  set Ap := A.submatrix et es with hAp
  set Bp := B.submatrix es et with hBp
  have hP : Ap * Bp = 1 := by
    rw [hAp, hBp, Matrix.submatrix_mul_equiv, hAB, Matrix.submatrix_one_equiv]
  have hAb : Ap = Matrix.fromBlocks Ap.toBlocks₁₁ Ap.toBlocks₁₂ Ap.toBlocks₂₁ Ap.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks Ap).symm
  have hBb : Bp = Matrix.fromBlocks Bp.toBlocks₁₁ Bp.toBlocks₁₂ Bp.toBlocks₂₁ Bp.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks Bp).symm
  have hP' := hP
  rw [hAb, hBb, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hP'
  obtain ⟨e11, -, e21, -⟩ := hP'
  have key : Ap * Matrix.fromBlocks Bp.toBlocks₁₁ 0 Bp.toBlocks₂₁ 1 =
      Matrix.fromBlocks 1 Ap.toBlocks₁₂ 0 Ap.toBlocks₂₂ := by
    conv_lhs => rw [hAb]
    rw [Matrix.fromBlocks_multiply]
    simp [e11, e21]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁] at hdet
  simp only [Matrix.det_one, mul_one, one_mul] at hdet
  have hB11 : Bp.toBlocks₁₁ = B.submatrix (s.orderEmbOfFin hs) (t.orderEmbOfFin ht) := by
    ext i j; simp [Bp, es, et, Matrix.toBlocks₁₁, sortEquiv, finSumEquivOfFinset_inl]
  have hA22 : Ap.toBlocks₂₂ =
      A.submatrix (tᶜ.orderEmbOfFin (card_compl_eq ht)) (sᶜ.orderEmbOfFin (card_compl_eq hs)) := by
    ext i j; simp [Ap, es, et, Matrix.toBlocks₂₂, sortEquiv, finSumEquivOfFinset_inr]
  have hApdet : Ap.det = (-1 : ℝ) ^ (∑ z ∈ s, (z : ℕ) + ∑ z ∈ t, (z : ℕ)) * A.det := by
    have : Ap = (A.submatrix es es).submatrix (et.trans es.symm) id := by
      ext i j; simp [Ap]
    rw [this, Matrix.det_permute, Matrix.det_submatrix_equiv_self]
    have hsg : Perm.sign (et.trans es.symm) = Perm.sign (es.symm.trans et) := by
      rw [← Perm.sign_trans_trans_symm (es.symm.trans et) es]
      congr 1
      ext z; simp
    rw [hsg]
    have := sign_sortEquiv hs ht
    have h2 : ((Perm.sign (es.symm.trans et) : ℤ) : ℝ) =
        (-1 : ℝ) ^ (∑ z ∈ s, (z : ℕ) + ∑ z ∈ t, (z : ℕ)) := by
      rw [this]; push_cast; rfl
    rw [h2]
  rw [← hB11, ← hA22, ← hdet, hApdet]

private lemma orderEmbOfFin_image {k : ℕ} {r : Fin k → Fin N} (hr : StrictMono r) :
    ∃ h : (Finset.univ.image r).card = k, ⇑((Finset.univ.image r).orderEmbOfFin h) = r := by
  have h : (Finset.univ.image r).card = k := by
    rw [Finset.card_image_of_injective _ hr.injective]; simp
  exact ⟨h, (Finset.orderEmbOfFin_unique h (fun i => by simp) hr).symm⟩

/-- If `A` is totally nonnegative with `det A = 1` and `A * B = 1`, then the sign-conjugated
inverse `((-1)^(i+j) B i j)` is totally nonnegative. -/
private lemma tn_inverse_aux (A B : Matrix (Fin N) (Fin N) ℝ) (hAB : A * B = 1)
    (hdet : A.det = 1)
    (hA : ∀ (m : ℕ) (f g : Fin m → Fin N), StrictMono f → StrictMono g →
      0 ≤ (A.submatrix f g).det)
    {k : ℕ} (r c : Fin k → Fin N) (hr : StrictMono r) (hc : StrictMono c) :
    0 ≤ (Matrix.of fun i j => (-1 : ℝ) ^ (r i : ℕ) *
      ((-1 : ℝ) ^ (c j : ℕ) * B (r i) (c j))).det := by
  obtain ⟨hs, hrs⟩ := orderEmbOfFin_image hr
  obtain ⟨ht, hct⟩ := orderEmbOfFin_image hc
  have hJ := jacobi_minor A B hAB hs ht
  rw [hdet, mul_one, hrs, hct] at hJ
  have e1 : (Matrix.of fun i j => (-1 : ℝ) ^ (r i : ℕ) * ((-1 : ℝ) ^ (c j : ℕ) * B (r i) (c j))).det
      = (∏ i, (-1 : ℝ) ^ (r i : ℕ)) * ((∏ j, (-1 : ℝ) ^ (c j : ℕ)) * (B.submatrix r c).det) := by
    have hmatrix :
        Matrix.of (fun i j => (-1 : ℝ) ^ (r i : ℕ) *
          ((-1 : ℝ) ^ (c j : ℕ) * B (r i) (c j))) =
          Matrix.of (fun i j => (fun i => (-1 : ℝ) ^ (r i : ℕ)) i *
            (Matrix.of fun i j => (fun j => (-1 : ℝ) ^ (c j : ℕ)) j *
              (B.submatrix r c) i j) i j) := rfl
    rw [hmatrix, Matrix.det_mul_column, Matrix.det_mul_row]
  have p1 : (∏ i, (-1 : ℝ) ^ (r i : ℕ)) = (-1) ^ (∑ z ∈ Finset.univ.image r, (z : ℕ)) := by
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_image (fun x _ y _ h => hr.injective h)]
  have p2 : (∏ j, (-1 : ℝ) ^ (c j : ℕ)) = (-1) ^ (∑ z ∈ Finset.univ.image c, (z : ℕ)) := by
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_image (fun x _ y _ h => hc.injective h)]
  rw [e1, p1, p2, ← mul_assoc, ← pow_add, hJ]
  exact hA _ _ _ (Finset.orderEmbOfFin _ _).strictMono (Finset.orderEmbOfFin _ _).strictMono

/-- If a totally nonnegative real matrix has determinant one, then its inverse, conjugated
by alternating signs, is totally nonnegative. -/
theorem tn_inverse (A B : Matrix (Fin N) (Fin N) ℝ) (hAB : A * B = 1) (hdet : A.det = 1)
    (hA : A.IsTotallyNonneg) :
    (Matrix.of fun (i j : Fin N) =>
      (-1 : ℝ) ^ (i : ℕ) * ((-1 : ℝ) ^ (j : ℕ) * B i j)).IsTotallyNonneg := by
  intro k r c hr hc
  exact tn_inverse_aux A B hAB hdet hA r c hr hc

end Jacobi

end

end Matrix
