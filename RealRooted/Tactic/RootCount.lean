import RealRooted.Tactic.RootCount.LowDegreeRules

/-!
# Root-count tactic compatibility facade

Re-exports the theorem, syntax, and macro-rule layers of the root-count tactic.

For a constant-degree split pencil on `[0, μ]` that avoids a fixed threshold,
use `rr_rightFamily_card_roots_gt_eq_zero_param`. The sequence sibling applies
the same proved endpoint pointwise. Their bare forms infer the four complete
certificate families from the local context; neither tactic proves an
interlacing or proper-position conclusion. The target orientation is the
upper-endpoint count equal to the normalized zero-endpoint count:
`card (roots (f + C μ * g) above x) = card (roots f above x)`.
-/
