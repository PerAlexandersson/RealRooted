module

public import Lean
public import Batteries.Lean.TagAttribute
public meta import Lean
public meta import Batteries.Lean.TagAttribute

/-!
# Certificate attributes for RealRooted tactics

These attributes mark lemmas that recurrence-based tactics may use as
certificates.  They are intentionally lightweight `TagAttribute`s: the first
tactic implementations should prefer explicit arguments, then use these tags
as a convenient fallback once the proof shape is stable.

- `[rr_recurrence]` for recurrence lemmas;
- `[rr_degree]` for `natDegree` lemmas;
- `[rr_nonzero]` for nonzero lemmas;
- `[rr_pos_lc]` for positive-leading-coefficient lemmas;
- `[rr_nonneg]` for nonnegative-coefficient lemmas;
- `[rr_base_strict_interl]` for base `StrictInterl` cases;
- `[rr_matrix_rect]` for matrix rectangularity lemmas.
-/

public meta section

/-- Tag attribute `rr_recurrence`, marking recurrence lemmas used by the RealRooted recurrence
tactics. -/
initialize rrRecurrenceAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_recurrence
    "recurrence lemmas used by RealRooted recurrence tactics"

/-- Tag attribute `rr_degree`, marking `natDegree` lemmas used by the RealRooted recurrence
tactics. -/
initialize rrDegreeAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_degree
    "natDegree lemmas used by RealRooted recurrence tactics"

/-- Tag attribute `rr_nonzero`, marking nonzero lemmas used by the RealRooted recurrence
tactics. -/
initialize rrNonzeroAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_nonzero
    "nonzero lemmas used by RealRooted recurrence tactics"

/-- Tag attribute `rr_pos_lc`, marking positive-leading-coefficient lemmas used by the
RealRooted recurrence tactics. -/
initialize rrPosLCAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_pos_lc
    "positive-leading-coefficient lemmas used by RealRooted recurrence tactics"

/-- Tag attribute `rr_nonneg`, marking nonnegative-coefficient lemmas used by the RealRooted
recurrence tactics. -/
initialize rrNonnegAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_nonneg
    "nonnegative-coefficient lemmas used by RealRooted recurrence tactics"

/-- Tag attribute `rr_base_strict_interl`, marking base `StrictInterl` cases used by the
RealRooted recurrence tactics. -/
initialize rrBaseStrictInterlAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_base_strict_interl
    "base StrictInterl cases used by RealRooted recurrence tactics"

/-- Tag attribute `rr_matrix_rect`, marking matrix rectangularity lemmas used by the RealRooted
matrix tactics. -/
initialize rrMatrixRectAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_matrix_rect
    "matrix rectangularity lemmas used by RealRooted matrix tactics"

namespace RealRooted
namespace Tactic

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Elab.Tactic

/-- The certificate attributes, each paired with its name, in the order used for lookup and
diagnostics. -/
def rrCertificateAttributes : Array (Name × Lean.TagAttribute) :=
  #[
    (`rr_recurrence, rrRecurrenceAttr),
    (`rr_degree, rrDegreeAttr),
    (`rr_nonzero, rrNonzeroAttr),
    (`rr_pos_lc, rrPosLCAttr),
    (`rr_nonneg, rrNonnegAttr),
    (`rr_base_strict_interl, rrBaseStrictInterlAttr),
    (`rr_matrix_rect, rrMatrixRectAttr)
  ]

/-- Format a list of declaration names for tactic diagnostics. -/
def formatNameList (names : Array Name) : String :=
  if names.isEmpty then
    "(none)"
  else
    String.intercalate ", " (names.toList.map toString)

end Tactic
end RealRooted


