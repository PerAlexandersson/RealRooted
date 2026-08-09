import RealRooted.Tactic.FiniteSymbolPF

/-!
# Compatibility frontend for PF-bidiagonal tactic shells

The active PF-bidiagonal frontend used by older proof-testbed shells is now
folded into `RealRooted.Tactic.PFBidiagonal`. The imported
`RealRooted.Tactic.FiniteSymbolPF` module retains only checked algebraic helpers
and explicitly named legacy routes through a false homogeneous premise. This
module remains as a stable import surface for callers that still import the
frontend name.
-/
