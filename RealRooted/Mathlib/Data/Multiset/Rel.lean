import Mathlib.Data.List.Forall2
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Multiset.ZeroCons

/-!
# Additional lemmas for multiset relations

This file provides reusable constructors for diagonal multiset relations and
heterogeneous composition.  It is intended for upstreaming to
`Mathlib.Data.Multiset.ZeroCons`.
-/

namespace Multiset

/-- Compose multiset relations whose element relations may differ. -/
theorem Rel.comp {α β γ : Type*}
    {R : α → β → Prop} {S : β → γ → Prop} {T : α → γ → Prop}
    {xs : Multiset α} {ys : Multiset β} {zs : Multiset γ}
    (hcomp : ∀ a b c, R a b → S b c → T a c)
    (h₁ : Multiset.Rel R xs ys) (h₂ : Multiset.Rel S ys zs) :
    Multiset.Rel T xs zs := by
  induction ys using Multiset.induction_on generalizing xs zs with
  | empty =>
      have hxs : xs = 0 := Multiset.rel_zero_right.mp h₁
      have hzs : zs = 0 := Multiset.rel_zero_left.mp h₂
      subst xs
      subst zs
      exact Rel.zero
  | cons b ys ih =>
      obtain ⟨a, xs', hab, htail₁, hxs⟩ := Multiset.rel_cons_right.mp h₁
      obtain ⟨c, zs', hbc, htail₂, hzs⟩ := Multiset.rel_cons_left.mp h₂
      subst xs
      subst zs
      exact Rel.cons (hcomp a b c hab hbc) (ih htail₁ htail₂)

/-- Related multisets have equally many elements satisfying corresponding predicates. -/
theorem Rel.card_filter_eq {α β : Type*} {R : α → β → Prop}
    {s : Multiset α} {t : Multiset β} (hrel : Multiset.Rel R s t)
    (P : α → Prop) (Q : β → Prop) [DecidablePred P] [DecidablePred Q]
    (hpred : ∀ a ∈ s, ∀ b ∈ t, R a b → (P a ↔ Q b)) :
    (s.filter P).card = (t.filter Q).card := by
  induction hrel with
  | zero => simp
  | @cons a b s t hab hrel ih =>
      have hpq : P a ↔ Q b := hpred a (by simp) b (by simp) hab
      have htail : ∀ c ∈ s, ∀ d ∈ t, R c d → (P c ↔ Q d) := by
        intro c hc d hd hcd
        exact hpred c (by simp [hc]) d (by simp [hd]) hcd
      by_cases ha : P a
      · have hb : Q b := hpq.mp ha
        simp [ha, hb, ih htail]
      · have hb : ¬Q b := fun hb => ha (hpq.mpr hb)
        simp [ha, hb, ih htail]

private theorem rel_uncross_min_cons {α : Type*} [LinearOrder α]
    {R : α → α → Prop} {a b : α} {as bs : Multiset α}
    (huncross : ∀ {a c b d}, a ≤ c → b ≤ d → R a d → R c b →
      R a b ∧ R c d)
    (ha : ∀ c ∈ as, a ≤ c) (hb : ∀ d ∈ bs, b ≤ d)
    (hrel : Multiset.Rel R (a ::ₘ as) (b ::ₘ bs)) :
    R a b ∧ Multiset.Rel R as bs := by
  obtain ⟨d, ds, hdb, hds, heq⟩ := Multiset.rel_cons_right.mp hrel
  rcases Multiset.cons_eq_cons.mp heq with hsame | hswap
  · rcases hsame with ⟨rfl, rfl⟩
    exact ⟨hdb, hds⟩
  · rcases hswap with ⟨_, cs, has, hds'⟩
    subst as
    subst ds
    obtain ⟨c, ts, hac, hct, rfl⟩ := Multiset.rel_cons_left.mp hds
    have had : a ≤ d := ha d (by simp)
    have hbc : b ≤ c := hb c (by simp)
    obtain ⟨hab, hdc⟩ := huncross had hbc hac hdb
    exact ⟨hab, Multiset.Rel.cons hdc hct⟩

/-- An uncrossable multiset relation pairs the corresponding sorted elements. -/
theorem Rel.forall₂_sort {α : Type*} [LinearOrder α] {R : α → α → Prop}
    (huncross : ∀ {a c b d}, a ≤ c → b ≤ d → R a d → R c b →
      R a b ∧ R c d)
    {s t : Multiset α} (hrel : Multiset.Rel R s t) :
    List.Forall₂ R (s.sort (· ≤ ·)) (t.sort (· ≤ ·)) := by
  revert t
  apply Multiset.strongInductionOn s
  intro s ih t hrel
  cases hs : s.sort (· ≤ ·) with
  | nil =>
      have hs0 : s = 0 := by
        calc
          s = ↑(s.sort (· ≤ ·)) :=
            (Multiset.sort_eq (s := s) (r := (· ≤ ·))).symm
          _ = 0 := by simp [hs]
      subst s
      have ht0 : t = 0 := Multiset.rel_zero_left.mp hrel
      subst t
      simp
  | cons a as =>
      have hsrepr : s = a ::ₘ (as : Multiset α) := by
        calc
          s = ↑(s.sort (· ≤ ·)) :=
            (Multiset.sort_eq (s := s) (r := (· ≤ ·))).symm
          _ = a ::ₘ (as : Multiset α) := by rw [hs]
      have hsord : (a :: as).Pairwise (· ≤ ·) := by
        simpa [hs] using
          (Multiset.pairwise_sort (s := s) (r := (· ≤ ·)))
      have ha : ∀ c ∈ (as : Multiset α), a ≤ c := by
        intro c hc
        exact (List.pairwise_cons.mp hsord).1 c (by simpa using hc)
      cases ht : t.sort (· ≤ ·) with
      | nil =>
          have ht0 : t = 0 := by
            calc
              t = ↑(t.sort (· ≤ ·)) :=
                (Multiset.sort_eq (s := t) (r := (· ≤ ·))).symm
              _ = 0 := by simp [ht]
          subst t
          have hs0 : s = 0 := Multiset.rel_zero_right.mp hrel
          have : False := by simpa [hsrepr] using hs0
          exact this.elim
      | cons b bs =>
          have htrepr : t = b ::ₘ (bs : Multiset α) := by
            calc
              t = ↑(t.sort (· ≤ ·)) :=
                (Multiset.sort_eq (s := t) (r := (· ≤ ·))).symm
              _ = b ::ₘ (bs : Multiset α) := by rw [ht]
          have htord : (b :: bs).Pairwise (· ≤ ·) := by
            simpa [ht] using
              (Multiset.pairwise_sort (s := t) (r := (· ≤ ·)))
          have hb : ∀ d ∈ (bs : Multiset α), b ≤ d := by
            intro d hd
            exact (List.pairwise_cons.mp htord).1 d (by simpa using hd)
          rw [hsrepr, htrepr] at hrel
          obtain ⟨hab, htail⟩ := rel_uncross_min_cons huncross ha hb hrel
          have hsmall : (as : Multiset α) < s := by
            rw [hsrepr]
            exact Multiset.lt_cons_self _ _
          have ih_tail := ih (as : Multiset α) hsmall (bs : Multiset α) htail
          rw [hsrepr, htrepr, Multiset.sort_cons ha, Multiset.sort_cons hb]
          exact List.Forall₂.cons hab ih_tail

end Multiset
