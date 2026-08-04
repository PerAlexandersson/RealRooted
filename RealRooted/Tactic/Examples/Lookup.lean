import RealRooted.Tactic.Lookup

/-!
# Certificate lookup examples

Smoke tests for exact local and tagged certificate lookup.
-/

namespace RealRooted
namespace Tactic

example {P : Prop} (h : P) : P := by
  rr_lookup

@[rr_nonzero] theorem rr_lookup_true_smoke : True := by
  trivial

example : True := by
  rr_lookup

@[rr_pos_lc] theorem rr_lookup_attr_true_smoke : True := by
  trivial

example : True := by
  rr_lookup [rr_pos_lc]

def RRLookupSmokeRel {α : Type} (x : α) : Prop := x = x

@[rr_matrix_rect] theorem rr_lookup_forall_smoke (m : ℕ) :
    ∀ n : ℕ, RRLookupSmokeRel (n + m) := by
  intro n
  rfl

example : ∀ n : ℕ, RRLookupSmokeRel (n + 3) := by
  rr_lookup [rr_matrix_rect]

@[rr_base_prec] theorem rr_lookup_full_forall_smoke :
    ∀ n : ℕ, RRLookupSmokeRel n := by
  intro n
  rfl

example : ∀ n : ℕ, RRLookupSmokeRel n := by
  rr_lookup [rr_base_prec]

@[rr_degree] theorem rr_lookup_determined_smoke : 37 = 37 := by
  rfl

@[rr_degree] theorem rr_lookup_partial_decoy_smoke (h : False) : 37 = 37 := by
  contradiction

example : 37 = 37 := by
  rr_lookup [rr_degree]

class RRLookupSmokeClass (α : Type) : Prop where
  witness : True

class RRLookupMissingClass (α : Type) : Prop where
  witness : True

instance : RRLookupSmokeClass ℕ := ⟨trivial⟩

@[rr_nonneg] theorem rr_lookup_missing_typeclass_decoy {α : Type}
    [RRLookupMissingClass α] (x : α) : RRLookupSmokeRel x := rfl

@[rr_nonneg] theorem rr_lookup_typeclass_smoke {α : Type} [RRLookupSmokeClass α]
    (x : α) : RRLookupSmokeRel x := rfl

example : RRLookupSmokeRel (37 : ℕ) := by
  rr_lookup [rr_nonneg]

local syntax (name := rr_lookup_attr_macro_smoke) "rr_lookup_attr_macro_smoke" : tactic

local macro_rules
  | `(tactic| rr_lookup_attr_macro_smoke) =>
      `(tactic| rr_lookup [rr_pos_lc])

example : True := by
  rr_lookup_attr_macro_smoke

example (h : True) : True := by
  fail_if_success rr_lookup [rr_missing_attr]
  exact h

end Tactic
end RealRooted
