import RealRooted.Mathlib.Algebra.Polynomial.Roots
import RealRooted.Mathlib.Data.Multiset.Card
import Mathlib.Data.Real.Basic

/-!
# Finite root counting

Finite-set counting criteria for simple roots, together with elementary index
arguments used after disjoint root-localization estimates.
-/

namespace RealRooted.RootCounting

open Polynomial

theorem roots_nodup_of_card_roots
    {p : ℝ[X]} (hcard : Multiset.card p.roots = p.natDegree)
    {s : Finset ℝ} (hsub : ∀ x ∈ s, p.IsRoot x) (hp : p ≠ 0)
    (hle : p.natDegree ≤ s.card) : p.roots.Nodup := by
  refine Multiset.nodup_of_finset_card_le (fun x hx => ?_) (by rw [hcard]; exact hle)
  exact (mem_roots hp).mpr (hsub x hx)

/-! ### Counting exhibited roots

The anchor for the Newton-polygon index count is a cardinality inequality: the
outer roots below the last dominance interval, the outer roots above its mirror,
and the roots the Eisenstein localization exhibits in the middle are pairwise
disjoint, so their counts sum to at most the degree. -/

theorem card_le_natDegree {p : ℝ[X]} (hp : p ≠ 0)
    (hcard : Multiset.card p.roots = p.natDegree)
    {S : Finset ℝ} (hS : ∀ x ∈ S, p.IsRoot x) : S.card ≤ p.natDegree := by
  classical
  have hsub : S ⊆ p.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (hS x hx))
  calc S.card ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ = p.natDegree := hcard

/-- Three pairwise disjoint families of roots have total size at most the
degree. -/
theorem card_three_le {p : ℝ[X]} (hp : p ≠ 0)
    (hcard : Multiset.card p.roots = p.natDegree) {S T U : Finset ℝ}
    (hS : ∀ x ∈ S, p.IsRoot x) (hT : ∀ x ∈ T, p.IsRoot x)
    (hU : ∀ x ∈ U, p.IsRoot x)
    (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U) :
    S.card + T.card + U.card ≤ p.natDegree := by
  classical
  have hSTU : ∀ x ∈ S ∪ T ∪ U, p.IsRoot x := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact hS x h'
      · exact hT x h'
    · exact hU x h
  have hd1 : Disjoint (S ∪ T) U := by
    rw [Finset.disjoint_union_left]
    exact ⟨hSU, hTU⟩
  have hcards : (S ∪ T ∪ U).card = S.card + T.card + U.card := by
    rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hST]
  rw [← hcards]
  exact card_le_natDegree hp hcard hSTU

/-! ### From the anchor to the exact index

A strictly increasing count that is bounded below by the index everywhere and
reaches the index at one point equals the index throughout. -/

theorem strict_chain_le {N : ℕ → ℕ} (hmono : ∀ j, N j < N (j + 1)) (j e : ℕ) :
    N j + e ≤ N (j + e) := by
  induction e with
  | zero => simp
  | succ e ih =>
      have := hmono (j + e)
      calc N j + (e + 1) = (N j + e) + 1 := by ring
        _ ≤ N (j + e) + 1 := by lia
        _ ≤ N (j + e + 1) := by lia
        _ = N (j + (e + 1)) := by ring_nf

/-- **The anchor argument.**  `N j >= j` everywhere below `J`, `N` strictly
increasing, and `N J <= J` force `N j = j` for every `j <= J`. -/
theorem index_eq {N : ℕ → ℕ} (hmono : ∀ j, N j < N (j + 1)) {J : ℕ}
    (hge : ∀ j, j ≤ J → j ≤ N j) (hJ : N J ≤ J) (j : ℕ) (hj : j ≤ J) :
    N j = j := by
  have hchain := strict_chain_le hmono j (J - j)
  have hje : j + (J - j) = J := by lia
  rw [hje] at hchain
  have := hge j hj
  lia

/-- The count inequality that supplies the anchor: if the two outer families of
size `B` and a middle family of size `M` are disjoint inside a degree-`n`
polynomial, and the middle family already accounts for all but `2 j` of the
degree, then `B <= j`. -/
theorem outer_le_of_count {B M n j : ℕ} (h : B + M + B ≤ n) (hM : n ≤ M + 2 * j) :
    B ≤ j := by lia

/-! ### Extracting a root family from a disjoint existence statement

The Eisenstein localization gives, for each index in a range, *some* root in an
interval, with the intervals pairwise disjoint.  This turns that into a single
`Finset` of roots of the right size, which is what `card_three_le` consumes. -/

theorem exists_root_family {p : ℝ[X]} {ι : Type*} (s : Finset ι)
    (P : ι → ℝ → Prop) (hex : ∀ i ∈ s, ∃ y, P i y ∧ p.IsRoot y)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ y z, P i y → P j z → y ≠ z) :
    ∃ S : Finset ℝ, S.card = s.card ∧ (∀ x ∈ S, p.IsRoot x) ∧
      ∀ x ∈ S, ∃ i ∈ s, P i x := by
  classical
  choose! f hf hroot using hex
  refine ⟨s.image f, ?_, ?_, ?_⟩
  · refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    by_contra hne
    exact hdisj a (by simpa using ha) b (by simpa using hb) hne (f a) (f b)
      (hf a (by simpa using ha)) (hf b (by simpa using hb)) hab
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hroot i hi
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i, hi, hf i hi⟩

/-- **The anchor, packaged.**  The cardinality count, the index arithmetic and
the overlap combine into the exact index identification. -/
theorem index_eq_of_count {B M n J jmin : ℕ}
    (hcount : B + M + B ≤ n) (hMn : n ≤ M + 2 * jmin) (hJ : jmin ≤ J)
    {Nfun : ℕ → ℕ} (hmono : ∀ j, Nfun j < Nfun (j + 1))
    (hge : ∀ j, j ≤ J → j ≤ Nfun j) (hNJ : Nfun J = B) :
    ∀ j, j ≤ J → Nfun j = j := by
  have hB : B ≤ jmin := outer_le_of_count hcount hMn
  exact index_eq hmono hge (by lia)


end RealRooted.RootCounting
