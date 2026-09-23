import RealRooted.Tactic.Lookup

/-!
# Certificate lookup examples

Smoke tests for exact local and tagged certificate lookup.
-/

namespace RealRooted
namespace Tactic

example {P : Prop} (h : P) : P := by rr_lookup

@[rr_nonzero] theorem rr_lookup_true_smoke : True := by trivial

example : True := by rr_lookup

@[rr_pos_lc] theorem rr_lookup_attr_true_smoke : True := by trivial

example : True := by rr_lookup [rr_pos_lc]

def RRLookupSmokeRel {α : Type} (x : α) : Prop := x = x

/-- This relation remains untagged so these examples can only use locals. -/
def RRLookupFreshRel (n : Nat) : Prop := n = n

def RRLookupFreshPolyRel {α : Type} (x : α) : Prop := x = x

example (_h : ∀ n : Nat, RRLookupFreshRel n) : RRLookupFreshRel 5 := by rr_lookup

example (_h : ∀ n : Nat, RRLookupFreshRel n) : RRLookupFreshRel 5 := by rr_lookup [rr_nonneg]

example (_hbad : False → RRLookupFreshRel 5) : RRLookupFreshRel 5 := by
  fail_if_success rr_lookup
  rfl

example (_hloose : ∀ _n : Nat, RRLookupFreshRel 5) : RRLookupFreshRel 5 := by
  fail_if_success rr_lookup
  rfl

theorem rr_lookup_mvar_goal_smoke {n : Nat} (_h : RRLookupFreshRel n) : True :=
  trivial

example (_h : ∀ n : Nat, RRLookupFreshRel n) : True := by
  fail_if_success (apply rr_lookup_mvar_goal_smoke; rr_lookup)
  trivial

inductive RRLookupTaggedRel : Prop where
  | intro

@[rr_degree, rr_nonzero] theorem rr_lookup_dual_tag_smoke : RRLookupTaggedRel := .intro

@[rr_degree] theorem rr_lookup_degree_tag_smoke : RRLookupTaggedRel := .intro

-- Ambiguity lists each candidate once and reports all of its provenance tags.
/-- error: rr_lookup failed: ambiguous tagged certificates: RealRooted.Tactic.rr_lookup_degree_tag_smoke [rr_degree], RealRooted.Tactic.rr_lookup_dual_tag_smoke [rr_degree, rr_nonzero] -/
#guard_msgs in
example : RRLookupTaggedRel := by rr_lookup

-- A scoped ambiguity keeps the requested tag in the diagnostic.
/-- error: rr_lookup failed: ambiguous tagged certificates for [rr_degree]: RealRooted.Tactic.rr_lookup_degree_tag_smoke [rr_degree], RealRooted.Tactic.rr_lookup_dual_tag_smoke [rr_degree, rr_nonzero] -/
#guard_msgs in
example : RRLookupTaggedRel := by rr_lookup [rr_degree]

/-- An ambiguous tagged search does not consume or corrupt the goal state. -/
example : RRLookupTaggedRel := by
  fail_if_success rr_lookup [rr_degree]
  exact rr_lookup_dual_tag_smoke

inductive RRLookupLocalPrecedenceRel : Prop where
  | intro

@[rr_nonneg] theorem rr_lookup_local_precedence_tag_one : RRLookupLocalPrecedenceRel := .intro

@[rr_nonneg] theorem rr_lookup_local_precedence_tag_two : RRLookupLocalPrecedenceRel := .intro

/-- A local exact certificate wins before the ambiguous scoped tagged search. -/
example (h : RRLookupLocalPrecedenceRel) : RRLookupLocalPrecedenceRel := by
  rr_lookup [rr_nonneg]

inductive RRLookupNoCertificateRel : Prop where
  | intro

/-- error: rr_lookup failed: no local or tagged certificate matches the goal for [rr_root_bound] -/
#guard_msgs in
example : RRLookupNoCertificateRel := by rr_lookup [rr_root_bound]

@[rr_matrix_rect] theorem rr_lookup_forall_smoke (m : ℕ) :
    ∀ n : ℕ, RRLookupSmokeRel (n + m) := by
  intro n
  rfl

example : ∀ n : ℕ, RRLookupSmokeRel (n + 3) := by rr_lookup [rr_matrix_rect]

@[rr_base_prec] theorem rr_lookup_full_forall_smoke :
    ∀ n : ℕ, RRLookupSmokeRel n := by
  intro n
  rfl

example : ∀ n : ℕ, RRLookupSmokeRel n := by rr_lookup [rr_base_prec]

@[rr_degree] theorem rr_lookup_determined_smoke : 37 = 37 := by rfl

@[rr_degree] theorem rr_lookup_partial_decoy_smoke (h : False) : 37 = 37 := by contradiction

example : 37 = 37 := by rr_lookup [rr_degree]

class RRLookupSmokeClass (α : Type) : Prop where
  witness : True

class RRLookupMissingClass (α : Type) : Prop where
  witness : True

instance : RRLookupSmokeClass ℕ := ⟨trivial⟩

example
    (_h : ∀ {α : Type} [RRLookupSmokeClass α] (x : α),
      RRLookupFreshPolyRel x) :
    RRLookupFreshPolyRel (37 : Nat) := by
  rr_lookup

@[rr_nonneg] theorem rr_lookup_missing_typeclass_decoy {α : Type}
    [RRLookupMissingClass α] (x : α) : RRLookupSmokeRel x := rfl

@[rr_nonneg] theorem rr_lookup_typeclass_smoke {α : Type} [RRLookupSmokeClass α]
    (x : α) : RRLookupSmokeRel x := rfl

example : RRLookupSmokeRel (37 : ℕ) := by rr_lookup [rr_nonneg]

local syntax (name := rr_lookup_attr_macro_smoke) "rr_lookup_attr_macro_smoke" : tactic

local macro_rules
  | `(tactic| rr_lookup_attr_macro_smoke) =>
      `(tactic| rr_lookup [rr_pos_lc])

example : True := by rr_lookup_attr_macro_smoke

/-- error: rr_lookup failed: unknown certificate attribute [rr_missing_attr] -/
#guard_msgs in
example : True := by rr_lookup [rr_missing_attr]

/-- Failed lookup leaves the surrounding proof state usable. -/
example (h : True) : True := by
  fail_if_success rr_lookup [rr_missing_attr]
  exact h

end Tactic
end RealRooted
