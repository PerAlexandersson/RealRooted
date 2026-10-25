module

public meta import Lean.Meta.Tactic.Simp
public import Lean.Meta.Tactic.Simp
public import Mathlib.Init

/-!
# Simp set for threshold-matrix orbits

Declared in its own `meta` file: a module registers simp attributes at compile time, and an
attribute cannot be used in the file that declares it.
-/

public meta section

/-- Unfolding lemmas for explicit threshold-matrix orbits, used by the `rr_row_splits`
threshold-orbit route. -/
register_simp_attr rr_threshold_unfold
