module

import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
import RealRooted.DegreeDropReversal
import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!+# Sign comparison for a polynomial pencil and its reflection

We formalize the sign-counting argument in Y. Cao and H. Fu,
*Real-rooted Ehrhart h*-polynomials of crown posets and wheel and whirl matroids*,
arXiv:2610.40496v1, Lemma 4.1. Two sign grids on `[-1, 0]`, one for a polynomial
and one for its reflection, exhibit disjoint families of roots on either side of `-1`.
The degree bound then proves splitting and simplicity.
-/

public section

open Polynomial Finset

namespace RealRooted.RootCounting

private theorem root_data_of_grid {p : ℝ[X]} {n : ℕ}
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hleft : x 0 = -1) (hright : x (Fin.last n) = 0)
    (hsign : ∀ i : Fin n, p.eval (x i.castSucc) * p.eval (x i.succ) < 0) :
    ∃ r : Fin n → ℝ, Function.Injective r ∧
      ∀ i, -1 < r i ∧ r i < 0 ∧ p.IsRoot (r i) := by
  obtain ⟨r, hr, hroot⟩ := Polynomial.exists_ordered_roots_of_strict_sign_changes x hx hsign
  refine ⟨r, hr.injective, fun i => ⟨?_, ?_, (hroot i).2.2⟩⟩
  · rw [← hleft]
    exact (hx.monotone (Fin.zero_le i.castSucc)).trans_lt (hroot i).1
  · rw [← hright]
    exact (hroot i).2.1.trans_le (hx.monotone (Fin.le_last i.succ))

/-- Strict sign changes for a polynomial and its degree-`2n` reflection on
`[-1, 0]` force exactly `2n` distinct negative roots. -/
theorem splits_nodup_neg_of_reflect_sign_changes {p : ℝ[X]} {n : ℕ}
    (hp : p ≠ 0) (hdegree : p.natDegree ≤ 2 * n)
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hleft : x 0 = -1) (hright : x (Fin.last n) = 0)
    (hsign : ∀ i : Fin n, p.eval (x i.castSucc) * p.eval (x i.succ) < 0)
    (hreflect : ∀ i : Fin n,
      (p.reflect (2 * n)).eval (x i.castSucc) *
        (p.reflect (2 * n)).eval (x i.succ) < 0) :
    p.natDegree = 2 * n ∧ p.Splits ∧ p.roots.Nodup ∧ ∀ z ∈ p.roots, z < 0 := by
  classical
  obtain ⟨r, hr, hroots⟩ := root_data_of_grid x hx hleft hright hsign
  obtain ⟨s, hs, hsroots⟩ := root_data_of_grid x hx hleft hright hreflect
  let f : Fin n ⊕ Fin n → ℝ := Sum.elim r (fun i => (s i)⁻¹)
  have hinv (i : Fin n) : (s i)⁻¹ < -1 := by
    have hneg := (hsroots i).2.1
    have hlow := (hsroots i).1
    simpa using (inv_lt_inv_of_neg hneg (by norm_num : (-1 : ℝ) < 0)).mpr hlow
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (hr hab)
      | inr j =>
        have := (hroots i).1
        have := hinv j
        change r i = (s j)⁻¹ at hab
        exact False.elim (by linarith)
    | inr i =>
      cases b with
      | inl j =>
        have := (hroots j).1
        have := hinv i
        change (s i)⁻¹ = r j at hab
        exact False.elim (by linarith)
      | inr j => exact congrArg Sum.inr (hs (inv_injective hab))
  have hfroot (i : Fin n ⊕ Fin n) : p.IsRoot (f i) ∧ f i < 0 := by
    cases i with
    | inl i => exact ⟨(hroots i).2.2, (hroots i).2.1⟩
    | inr i =>
      refine ⟨?_, (hinv i).trans (by norm_num)⟩
      apply (DegreeDropReversal.isRoot_reflect_inv_iff
        (inv_ne_zero (ne_of_lt (hsroots i).2.1)) hdegree).mp
      simpa using (hsroots i).2.2
  let S := Finset.univ.image f
  have hcard : S.card = 2 * n := by
    simpa [S, two_mul] using Finset.card_image_of_injective Finset.univ hf
  have hsub : S ⊆ p.roots.toFinset := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hfroot i).1)
  have hcount := Finset.card_le_card hsub
  have hset := Multiset.toFinset_card_le p.roots
  have hdeg := Polynomial.card_roots' p
  have heq : S = p.roots.toFinset := Finset.eq_of_subset_of_card_le hsub (by lia)
  refine ⟨by lia, Polynomial.splits_iff_card_roots.mpr (by lia),
    Multiset.toFinset_card_eq_card_iff_nodup.mp (by lia), ?_⟩
  intro z hz
  have hzS : z ∈ S := by rw [heq]; exact Multiset.mem_toFinset.mpr hz
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzS
  exact (hfroot i).2

private theorem signed_sub_pos {a b lam : ℝ} {k : ℕ}
    (hlam : 0 ≤ lam) (hlam₁ : lam ≤ 1) (h : |b| < (-1 : ℝ) ^ k * a) :
    0 < (-1 : ℝ) ^ k * (a - lam * b) := by
  have hb : |(-1 : ℝ) ^ k * (lam * b)| ≤ |b| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul,
      abs_of_nonneg hlam]
    exact mul_le_of_le_one_left (abs_nonneg b) hlam₁
  have := le_abs_self ((-1 : ℝ) ^ k * (lam * b))
  nlinarith

private theorem sign_changes_of_signed_pos {p : ℝ[X]} {n : ℕ}
    {x : Fin (n + 1) → ℝ}
    (hs : ∀ i, 0 < (-1 : ℝ) ^ (n - i.val) * p.eval (x i))
    (i : Fin n) : p.eval (x i.castSucc) * p.eval (x i.succ) < 0 := by
  have ha := hs i.castSucc
  have hb := hs i.succ
  have hidx : n - i.val = (n - (i.val + 1)) + 1 := by have := i.isLt; lia
  simp only [Fin.val_castSucc, Fin.val_succ, hidx, pow_succ, mul_neg_one] at ha hb
  have hsq : ((-1 : ℝ) ^ (n - (i.val + 1))) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hprod := mul_pos ha hb
  have heq :
      (-((-1 : ℝ) ^ (n - (i.val + 1))) * p.eval (x i.castSucc)) *
          ((-1 : ℝ) ^ (n - (i.val + 1)) * p.eval (x i.succ)) =
        -(p.eval (x i.castSucc) * p.eval (x i.succ)) := by
    calc
      _ = -(((-1 : ℝ) ^ (n - (i.val + 1))) ^ 2 *
        (p.eval (x i.castSucc) * p.eval (x i.succ))) := by ring
      _ = _ := by rw [hsq]; ring
  rw [heq] at hprod
  linarith

/-- A reciprocal polynomial that strictly dominates a correction on a half grid
gives simple negative roots throughout the pencil, provided its reflected
correction has no larger modulus. This is Cao–Fu, Lemma 4.1, with arbitrary
correction polynomials and an upper bound on the degree. -/
theorem splits_nodup_neg_of_pencil_sign_domination {H Q : ℝ[X]} {n : ℕ}
    (hH : H.natDegree ≤ 2 * n) (hQ : Q.natDegree ≤ 2 * n)
    (hzero : 0 < H.eval 0) (hQzero : Q.eval 0 = 0)
    (hrec : H.reflect (2 * n) = H)
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hleft : x 0 = -1) (hright : x (Fin.last n) = 0)
    (hdom : ∀ i, |Q.eval (x i)| < (-1 : ℝ) ^ (n - i.val) * H.eval (x i))
    (hbound : ∀ i, |(Q.reflect (2 * n)).eval (x i)| ≤ |Q.eval (x i)|)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam₁ : lam ≤ 1) :
    (H - C lam * Q).natDegree = 2 * n ∧ (H - C lam * Q).Splits ∧
      (H - C lam * Q).roots.Nodup ∧ ∀ z ∈ (H - C lam * Q).roots, z < 0 := by
  have hp : H - C lam * Q ≠ 0 := by
    intro h
    have := congrArg (fun p : ℝ[X] => p.eval 0) h
    simp [hQzero] at this
    linarith
  have hdeg : (H - C lam * Q).natDegree ≤ 2 * n :=
    (natDegree_sub_le _ _).trans (max_le hH ((natDegree_C_mul_le _ _).trans hQ))
  apply splits_nodup_neg_of_reflect_sign_changes hp hdeg x hx hleft hright
  · apply sign_changes_of_signed_pos
    intro i
    simpa using signed_sub_pos hlam hlam₁ (hdom i)
  · apply sign_changes_of_signed_pos
    intro i
    have h := signed_sub_pos hlam hlam₁ ((hbound i).trans_lt (hdom i))
    simpa [reflect_sub, reflect_C_mul, hrec] using h

end RealRooted.RootCounting
