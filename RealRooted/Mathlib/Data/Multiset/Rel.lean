import Mathlib.Data.Multiset.ZeroCons

/-!
# Additional lemmas for multiset relations

This file provides reusable constructors for diagonal multiset relations and
heterogeneous composition.  It is intended for upstreaming to
`Mathlib.Data.Multiset.ZeroCons`.
-/

namespace Multiset

/-- Lift a pointwise reflexivity proof to a multiset relation. -/
theorem Rel.diag {α : Type*} {R : α → α → Prop} {s : Multiset α}
    (h : ∀ a ∈ s, R a a) : Multiset.Rel R s s := by
  induction s using Multiset.induction_on with
  | empty => exact Rel.zero
  | cons a s ih =>
      exact Rel.cons (h a (by simp))
        (ih fun b hb => h b (by simp [hb]))

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
      obtain ⟨a, xs, hab, h₁, rfl⟩ := Multiset.rel_cons_right.mp h₁
      obtain ⟨c, zs, hbc, h₂, rfl⟩ := Multiset.rel_cons_left.mp h₂
      exact Rel.cons (hcomp a b c hab hbc) (ih h₁ h₂)

/-- Every element on the left of a multiset relation has a related element on the right. -/
theorem Rel.exists_right_of_mem_left {α β : Type*} {R : α → β → Prop}
    {s : Multiset α} {t : Multiset β} (hrel : Multiset.Rel R s t)
    {a : α} (ha : a ∈ s) : ∃ b ∈ t, R a b := by
  induction s using Multiset.induction_on generalizing t with
  | empty => simp at ha
  | cons a' s ih =>
      obtain ⟨b, t, hab, hrel, rfl⟩ := Multiset.rel_cons_left.mp hrel
      rw [Multiset.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨b, by simp, hab⟩
      · obtain ⟨c, hc, hac⟩ := ih hrel ha
        exact ⟨c, by simp [hc], hac⟩

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

end Multiset
