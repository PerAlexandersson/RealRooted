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
      apply Rel.cons
      · exact h a (by simp)
      · apply ih
        intro b hb
        exact h b (by simp [hb])

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

end Multiset
