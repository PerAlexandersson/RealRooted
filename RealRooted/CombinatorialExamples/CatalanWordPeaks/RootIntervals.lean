/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.Basic.ProperPosition
public import RealRooted.SimpleRoots
import RealRooted.MaWang.StrictSigns.RootSigns
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Strict root separation from isolating intervals

We use the standard root multiset and `StrictInterl` predicates. The latter
permits shared roots, so strict inequalities and absence of common roots are
retained separately. The interval argument uses the library IVT lemma and
Mathlib's degree bound, without a second root-list infrastructure.
-/

public noncomputable section

namespace RealRooted.CatalanWordPeaks

open Polynomial

/-- Disjoint sign-changing intervals exhaust the roots of a polynomial whose
 degree is bounded by their number. The returned root list is increasing. -/
theorem roots_of_intervals {p : ℝ[X]} {m : ℕ} (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ m) (l u : Fin m → ℝ)
    (hwidth : ∀ i, l i < u i)
    (hsep : ∀ i j, i < j → u i ≤ l j)
    (hsign : ∀ i, p.eval (l i) * p.eval (u i) < 0) :
    ∃ r : Fin m → ℝ, StrictMono r ∧
      (∀ i, l i < r i ∧ r i < u i) ∧
      (↑(List.ofFn r) : Multiset ℝ) = p.roots ∧ p.Splits ∧ p.natDegree = m := by
  classical
  choose r hr using fun i ↦ MaWang.exists_isRoot_between_of_eval_mul_neg (hwidth i) (hsign i)
  have hmono : StrictMono r := fun i j hij ↦
    (hr i).2.1.trans_le (hsep i j hij) |>.trans (hr j).1
  have hn : (List.ofFn r).Nodup :=
    List.pairwise_ofFn.mpr (fun _ _ h ↦ (hmono h).ne)
  have hsub : (↑(List.ofFn r) : Multiset ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hn)]
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hx)
    exact (mem_roots hp).mpr (hr i).2.2
  have heq : (↑(List.ofFn r) : Multiset ℝ) = p.roots := by
    apply Multiset.eq_of_le_of_card_le hsub
    exact (card_roots' p).trans (by simpa only [Multiset.coe_card, List.length_ofFn] using hdeg)
  have hd : p.natDegree = m := by
    have hc := Multiset.card_le_card hsub
    simp only [Multiset.coe_card, List.length_ofFn] at hc
    exact le_antisymm hdeg (hc.trans (card_roots' p))
  refine ⟨r, hmono, fun i ↦ ⟨(hr i).1, (hr i).2.1⟩, heq, ?_, hd⟩
  exact splits_iff_card_roots.mpr (by rw [← heq, Multiset.coe_card, List.length_ofFn, hd])

/-- A complete injective root enumeration gives simple real roots. -/
theorem hasSimpleRoots_of_root_list {p : ℝ[X]} {m : ℕ} (hp : p ≠ 0)
    {r : Fin m → ℝ} (hr : StrictMono r)
    (heq : (↑(List.ofFn r) : Multiset ℝ) = p.roots) : HasSimpleRoots p := by
  classical
  have hn : p.roots.Nodup := by
    rw [← heq, Multiset.coe_nodup]
    exact List.pairwise_ofFn.mpr (fun _ _ h ↦ (hr h).ne)
  exact HasSimpleRoots.of_roots_nodup hp hn

/-- Strictly separated complete root lists imply the standard oriented interlacing
relation for either of the two permitted degree patterns. -/
theorem strictInterl_of_root_lists {p q : ℝ[X]} {m d : ℕ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hps : p.Splits) (hqs : q.Splits)
    (r : Fin m → ℝ) (s : Fin d → ℝ) (hr : StrictMono r) (hs : StrictMono s)
    (heqp : (↑(List.ofFn r) : Multiset ℝ) = p.roots)
    (heqq : (↑(List.ofFn s) : Multiset ℝ) = q.roots)
    (hd : d = m ∨ d = m + 1)
    (hright : ∀ i j, j.val = i.val + (d - m) → r i < s j)
    (hleft : ∀ i j, j.val + 1 = i.val + (d - m) → s j < r i) :
    StrictInterl p q := by
  refine ⟨⟨hp, hps⟩, ⟨hq, hqs⟩, List.ofFn r, List.ofFn s,
    List.pairwise_ofFn.mpr (fun _ _ h ↦ (hr h).le),
    List.pairwise_ofFn.mpr (fun _ _ h ↦ (hs h).le), heqp, heqq, ?_⟩
  rcases hd with rfl | rfl
  · right
    refine ⟨by simp only [List.length_ofFn], listAlternates_of_interleaves_of_length
      (by simp only [List.length_ofFn]) (List.interleaves_ofFn_even.mpr ⟨?_, ?_⟩)⟩
    · intro i
      exact (hright i i (by simp only [Nat.sub_self, Nat.add_zero])).le
    · intro i hi
      exact (hleft ⟨i + 1, hi⟩ ⟨i, by lia⟩ (by simp only [Nat.sub_self, Nat.add_zero])).le
  · left
    refine ⟨by simp only [List.length_ofFn], listInterlaces_of_interleaves_of_length
      (by simp only [List.length_ofFn]) (List.interleaves_ofFn_odd.mpr ⟨?_, ?_⟩)⟩
    · intro i
      exact (hright i i.succ (by simp only [Nat.add_sub_cancel_left, Fin.val_succ])).le
    · intro i
      exact (hleft i i.castSucc (by simp only [Nat.add_sub_cancel_left, Fin.val_castSucc])).le

/-- Strict cross-list inequalities exclude every common root. -/
theorem no_common_root_of_root_lists {p q : ℝ[X]} {m d : ℕ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hd : d = m ∨ d = m + 1)
    (r : Fin m → ℝ) (s : Fin d → ℝ) (hs : StrictMono s)
    (heqp : (↑(List.ofFn r) : Multiset ℝ) = p.roots)
    (heqq : (↑(List.ofFn s) : Multiset ℝ) = q.roots)
    (hright : ∀ i j, j.val = i.val + (d - m) → r i < s j)
    (hleft : ∀ i j, j.val + 1 = i.val + (d - m) → s j < r i) :
    ∀ x, ¬ (p.IsRoot x ∧ q.IsRoot x) := by
  intro x ⟨hx, hy⟩
  have hx' := (mem_roots hp).mpr hx
  have hy' := (mem_roots hq).mpr hy
  rw [← heqp] at hx'
  rw [← heqq] at hy'
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hx')
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hy')
  by_cases hij : i.val + (d - m) ≤ j.val
  · let k : Fin d := ⟨i.val + (d - m), lt_of_le_of_lt hij j.isLt⟩
    have hlt := (hright i k rfl).trans_le (hs.monotone hij)
    exact hlt.ne hj.symm
  · have hi := i.isLt
    have hk : i.val + (d - m) - 1 < d := by rcases hd with rfl | rfl <;> lia
    let k : Fin d := ⟨i.val + (d - m) - 1, hk⟩
    have hlt := (hs.monotone (show j ≤ k by change j.val ≤ k.val; dsimp [k]; lia)).trans_lt
      (hleft i k (by dsimp [k]; lia))
    exact hlt.ne hj

/-- In the strict orientation, every old root lies below a new root; in particular
 the new rightmost root is strictly farther right whenever the old row is nonconstant. -/
theorem exists_root_above_of_root_lists {p q : ℝ[X]} {m d : ℕ}
    (hm : m ≠ 0) (hd : d = m ∨ d = m + 1)
    (r : Fin m → ℝ) (s : Fin d → ℝ) (hs : StrictMono s)
    (heqp : (↑(List.ofFn r) : Multiset ℝ) = p.roots)
    (heqq : (↑(List.ofFn s) : Multiset ℝ) = q.roots)
    (hright : ∀ i j, j.val = i.val + (d - m) → r i < s j) :
    ∃ y ∈ q.roots, (∀ x ∈ p.roots, x < y) ∧ ∀ z ∈ q.roots, z ≤ y := by
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> lia
  let last : Fin d := ⟨d - 1, by lia⟩
  refine ⟨s last, ?_, ?_, ?_⟩
  · rw [← heqq]
    exact Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨last, rfl⟩)
  · intro x hx
    rw [← heqp] at hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hx)
    have hi := i.isLt
    have hk : i.val + (d - m) < d := by rcases hd with rfl | rfl <;> lia
    exact (hright i ⟨_, hk⟩ rfl).trans_le (hs.monotone (by change _ ≤ d - 1; lia))
  · intro z hz
    rw [← heqq] at hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hz)
    exact hs.monotone (by change i.val ≤ d - 1; have hi := i.isLt; lia)

end RealRooted.CatalanWordPeaks
