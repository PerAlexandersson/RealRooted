import RealRooted.GeneralizedSnakePosets.FiniteBoard

/-!
# Chain polynomials of finite relations

For a relation `r` and a finite set `D`, the chain polynomial counts the
subsets of `D` whose distinct elements are pairwise `r`-related, by size.
Non-nesting rook polynomials are the chain polynomials of the relation
"row increases and column decreases".

This file proves the general tools used for the Braun–Jal Theorem 3.5
decomposition:

* transport along a relation-preserving injection;
* a product formula when every element of one part lies below every element
  of the other;
* expansion along one element, and along an antichain.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

variable {α β : Type*}

/-- `P` is an `r`-chain: any two distinct elements are related one way or the
other. -/
def IsRelChain (r : α → α → Prop) (P : Finset α) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, a ≠ b → r a b ∨ r b a

theorem IsRelChain.mono {r : α → α → Prop} {P Q : Finset α} (h : IsRelChain r Q)
    (hPQ : P ⊆ Q) : IsRelChain r P :=
  fun a ha b hb hab => h a (hPQ ha) b (hPQ hb) hab

/-- The chain polynomial `∑_{P ⊆ D, P an r-chain} X ^ |P|`. -/
def chainPolynomial (r : α → α → Prop) (D : Finset α) : ℝ[X] := by
  classical
  exact ∑ P ∈ D.powerset.filter (IsRelChain r), X ^ P.card

theorem mem_chains {r : α → α → Prop} {D P : Finset α} [DecidablePred (IsRelChain r)] :
    P ∈ D.powerset.filter (IsRelChain r) ↔ P ⊆ D ∧ IsRelChain r P := by
  rw [Finset.mem_filter, Finset.mem_powerset]

/-- Chain polynomials are invariant under a relation-preserving injection. -/
theorem chainPolynomial_image [DecidableEq β] {r : α → α → Prop} {r' : β → β → Prop} {D : Finset α}
    {f : α → β} (hf : Set.InjOn f D) (hr : ∀ a ∈ D, ∀ b ∈ D, r' (f a) (f b) ↔ r a b) :
    chainPolynomial r' (D.image f) = chainPolynomial r D := by
  classical
  unfold chainPolynomial
  symm
  refine Finset.sum_nbij' (fun P => P.image f) (fun Q => D.filter fun a => f a ∈ Q)
    ?_ ?_ ?_ ?_ ?_
  · intro P hP
    obtain ⟨hPD, hP⟩ := mem_chains.mp hP
    refine mem_chains.mpr ⟨Finset.image_subset_image hPD, ?_⟩
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := fun h => hxy (by rw [h])
    rcases hP a ha b hb hab with h | h
    · exact Or.inl ((hr a (hPD ha) b (hPD hb)).mpr h)
    · exact Or.inr ((hr b (hPD hb) a (hPD ha)).mpr h)
  · intro Q hQ
    obtain ⟨-, hQ⟩ := mem_chains.mp hQ
    refine mem_chains.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro a ha b hb hab
    obtain ⟨haD, haQ⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbD, hbQ⟩ := Finset.mem_filter.mp hb
    rcases hQ _ haQ _ hbQ (fun h => hab (hf haD hbD h)) with h | h
    · exact Or.inl ((hr a haD b hbD).mp h)
    · exact Or.inr ((hr b hbD a haD).mp h)
  · intro P hP
    have hPD := (mem_chains.mp hP).1
    ext a
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨haD, b, hb, hba⟩
      rwa [← hf (hPD hb) haD hba]
    · intro ha
      exact ⟨hPD ha, a, ha, rfl⟩
  · intro Q hQ
    have hQD := (mem_chains.mp hQ).1
    ext y
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨-, ha⟩, rfl⟩
      exact ha
    · intro hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hQD hy)
      exact ⟨a, ⟨ha, hy⟩, rfl⟩
  · intro P hP
    rw [Finset.card_image_of_injOn (hf.mono (mem_chains.mp hP).1)]

/-- **Product formula.** If every element of `A` lies below every element of
`B`, then chains of `A ∪ B` are pairs of chains. -/
theorem chainPolynomial_union_of_forall_rel [DecidableEq α] {r : α → α → Prop} {A B : Finset α}
    (hAB : Disjoint A B) (hrel : ∀ a ∈ A, ∀ b ∈ B, r a b) :
    chainPolynomial r (A ∪ B) = chainPolynomial r A * chainPolynomial r B := by
  classical
  unfold chainPolynomial
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun S => (S ∩ A, S ∩ B)) (fun PQ => PQ.1 ∪ PQ.2)
    ?_ ?_ ?_ ?_ ?_
  · intro S hS
    obtain ⟨-, hS⟩ := mem_chains.mp hS
    exact Finset.mem_product.mpr
      ⟨mem_chains.mpr ⟨Finset.inter_subset_right, hS.mono Finset.inter_subset_left⟩,
        mem_chains.mpr ⟨Finset.inter_subset_right, hS.mono Finset.inter_subset_left⟩⟩
  · rintro ⟨P, Q⟩ hPQ
    obtain ⟨hP, hQ⟩ := Finset.mem_product.mp hPQ
    obtain ⟨hPA, hP⟩ := mem_chains.mp hP
    obtain ⟨hQB, hQ⟩ := mem_chains.mp hQ
    refine mem_chains.mpr ⟨Finset.union_subset_union hPA hQB, ?_⟩
    intro a ha b hb hab
    rcases Finset.mem_union.mp ha with ha | ha <;> rcases Finset.mem_union.mp hb with hb | hb
    · exact hP a ha b hb hab
    · exact Or.inl (hrel a (hPA ha) b (hQB hb))
    · exact Or.inr (hrel b (hPA hb) a (hQB ha))
    · exact hQ a ha b hb hab
  · intro S hS
    have hSAB := (mem_chains.mp hS).1
    change S ∩ A ∪ S ∩ B = S
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hSAB]
  · rintro ⟨P, Q⟩ hPQ
    obtain ⟨hP, hQ⟩ := Finset.mem_product.mp hPQ
    have hPA := (mem_chains.mp hP).1
    have hQB := (mem_chains.mp hQ).1
    have hPB : P ∩ B = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
      (Finset.disjoint_of_subset_left hPA hAB)
    have hQA : Q ∩ A = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
      (Finset.disjoint_of_subset_left hQB hAB.symm)
    simp only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hPA,
      Finset.inter_eq_left.mpr hQB, hPB, hQA, Finset.union_empty, Finset.empty_union]
  · intro S hS
    have hSAB := (mem_chains.mp hS).1
    rw [← pow_add, ← Finset.card_union_of_disjoint
      (Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hAB)),
      ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hSAB]

/-- The elements of `D` comparable with `c`. -/
def comparableWith (r : α → α → Prop) (D : Finset α) (c : α) : Finset α := by
  classical
  exact D.filter fun d => r d c ∨ r c d

theorem mem_comparableWith {r : α → α → Prop} {D : Finset α} {c d : α} :
    d ∈ comparableWith r D c ↔ d ∈ D ∧ (r d c ∨ r c d) := by
  classical
  unfold comparableWith
  exact Finset.mem_filter

/-- **Expansion along one element.** Chains avoiding `c`, plus `X` times the
chains of elements comparable with `c`. -/
theorem chainPolynomial_eq_erase_add [DecidableEq α] {r : α → α → Prop} (hirr : ∀ a, ¬ r a a)
    {D : Finset α} {c : α} (hc : c ∈ D) :
    chainPolynomial r D =
      chainPolynomial r (D.erase c) + X * chainPolynomial r (comparableWith r D c) := by
  classical
  unfold chainPolynomial
  rw [← Finset.sum_filter_not_add_sum_filter _ (fun P => c ∈ P), Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext P
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase]
    tauto
  · refine Finset.sum_nbij' (fun S => S.erase c) (fun T => insert c T) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      obtain ⟨hS, hcS⟩ := Finset.mem_filter.mp hS
      obtain ⟨hSD, hS⟩ := mem_chains.mp hS
      refine mem_chains.mpr ⟨?_, hS.mono (Finset.erase_subset _ _)⟩
      intro d hd
      obtain ⟨hdc, hdS⟩ := Finset.mem_erase.mp hd
      exact mem_comparableWith.mpr ⟨hSD hdS, hS d hdS c hcS hdc⟩
    · intro T hT
      obtain ⟨hTD, hT⟩ := mem_chains.mp hT
      refine Finset.mem_filter.mpr ⟨mem_chains.mpr ⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
      · exact Finset.insert_subset hc fun d hd => (mem_comparableWith.mp (hTD hd)).1
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with ha' | ha' <;>
          rcases Finset.mem_insert.mp hb with hb' | hb'
        · exact absurd (ha'.trans hb'.symm) hab
        · rw [ha']
          exact (mem_comparableWith.mp (hTD hb')).2.symm
        · rw [hb']
          exact (mem_comparableWith.mp (hTD ha')).2
        · exact hT a ha' b hb' hab
    · intro S hS
      exact Finset.insert_erase (Finset.mem_filter.mp hS).2
    · intro T hT
      have hcT : c ∉ T := fun h =>
        (mem_comparableWith.mp ((mem_chains.mp hT).1 h)).2.elim (hirr c) (hirr c)
      exact Finset.erase_insert hcT
    · intro S hS
      rw [← pow_succ', Finset.card_erase_add_one (Finset.mem_filter.mp hS).2]

/-- **Expansion along an antichain.** If no two elements of `Q ⊆ D` are
related, every chain meets `Q` at most once. -/
theorem chainPolynomial_eq_sdiff_add_sum [DecidableEq α] {r : α → α → Prop} (hirr : ∀ a, ¬ r a a)
    {D Q : Finset α} (hQ : Q ⊆ D) (hanti : ∀ q ∈ Q, ∀ q' ∈ Q, ¬ r q q') :
    chainPolynomial r D =
      chainPolynomial r (D \ Q) + ∑ q ∈ Q, X * chainPolynomial r (comparableWith r D q) := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | insert q Q hqQ ih =>
      have hQ' : Q ⊆ D := (Finset.subset_insert _ _).trans hQ
      have hq : q ∈ D \ Q := Finset.mem_sdiff.mpr ⟨hQ (Finset.mem_insert_self _ _), hqQ⟩
      have hcomp : comparableWith r (D \ Q) q = comparableWith r D q := by
        ext d
        simp only [mem_comparableWith, Finset.mem_sdiff]
        constructor
        · rintro ⟨⟨hd, -⟩, h⟩
          exact ⟨hd, h⟩
        · rintro ⟨hd, h⟩
          refine ⟨⟨hd, fun hdQ => ?_⟩, h⟩
          rcases h with h | h
          · exact hanti d (Finset.mem_insert_of_mem hdQ) q (Finset.mem_insert_self _ _) h
          · exact hanti q (Finset.mem_insert_self _ _) d (Finset.mem_insert_of_mem hdQ) h
      rw [ih hQ' fun a ha b hb => hanti a (Finset.mem_insert_of_mem ha) b
          (Finset.mem_insert_of_mem hb),
        chainPolynomial_eq_erase_add hirr hq, hcomp, Finset.sdiff_insert,
        Finset.sum_insert hqQ]
      ring

/-! ## Rook polynomials as chain polynomials -/

/-- Strictly increasing in both coordinates. -/
def incRel (a b : ℕ × ℕ) : Prop :=
  a.1 < b.1 ∧ a.2 < b.2

/-- Row strictly increases and column strictly decreases: the non-nesting
order. -/
def nestRel (a b : ℕ × ℕ) : Prop :=
  a.1 < b.1 ∧ b.2 < a.2

theorem incRel_irrefl (a : ℕ × ℕ) : ¬ incRel a a := fun h => lt_irrefl _ h.1

namespace FiniteSkewBoard

/-- A non-nesting rook polynomial is the chain polynomial of `nestRel`. -/
theorem rookPolynomial_eq_chainPolynomial (B : FiniteSkewBoard) :
    B.rookPolynomial = chainPolynomial nestRel B.cells := by
  classical
  unfold rookPolynomial chainPolynomial
  refine Finset.sum_congr (Finset.filter_congr fun P hP => ?_) fun _ _ => rfl
  have hPB := Finset.mem_powerset.mp hP
  constructor
  · rintro ⟨-, hrow, hord⟩ a ha b hb hab
    rcases lt_or_gt_of_ne (hrow a ha b hb hab) with h | h
    · exact Or.inl ⟨h, hord a ha b hb h⟩
    · exact Or.inr ⟨h, hord b hb a ha h⟩
  · intro h
    refine ⟨hPB, fun a ha b hb hab => ?_, fun a ha b hb hlt => ?_⟩
    · rcases h a ha b hb hab with h | h
      · exact h.1.ne
      · exact h.1.ne'
    · rcases h a ha b hb (fun hab => by rw [hab] at hlt; exact lt_irrefl _ hlt) with h | h
      · exact h.2
      · exact absurd h.1 (lt_asymm hlt)

/-- Reflecting the column order turns the non-nesting order into the
increasing order. -/
theorem rookPolynomial_eq_chainPolynomial_reflect {B : FiniteSkewBoard} {N : ℕ}
    (hB : ∀ p ∈ B.cells, p.2 ≤ N) :
    B.rookPolynomial = chainPolynomial incRel (B.cells.image fun p => (p.1, N - p.2)) := by
  rw [rookPolynomial_eq_chainPolynomial, chainPolynomial_image]
  · rintro ⟨a, b⟩ ha ⟨c, d⟩ hc h
    simp only [Prod.mk.injEq] at h
    have := hB _ ha
    have := hB _ hc
    simp only [Prod.mk.injEq]
    lia
  · rintro ⟨a, b⟩ ha ⟨c, d⟩ hc
    have := hB _ ha
    have := hB _ hc
    simp only [incRel, nestRel]
    lia

end FiniteSkewBoard

end GeneralizedSnakePosets
end RealRooted
