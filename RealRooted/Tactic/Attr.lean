import Lean

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
- `[rr_root_bound]` for root-interval lemmas;
- `[rr_base_prec]` for base `Prec` cases;
- `[rr_base_interlaces]` for base `Interlaces` cases.

Planned matrix attributes:

- `[rr_matrix_rect]`;
- `[rr_matrix_nonneg]`;
- `[rr_matrix_2x2]`;
- `[rr_matrix_threshold]`.
-/

initialize rrRecurrenceAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_recurrence
    "recurrence lemmas used by RealRooted recurrence tactics"

initialize rrDegreeAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_degree
    "natDegree lemmas used by RealRooted recurrence tactics"

initialize rrNonzeroAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_nonzero
    "nonzero lemmas used by RealRooted recurrence tactics"

initialize rrPosLCAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_pos_lc
    "positive-leading-coefficient lemmas used by RealRooted recurrence tactics"

initialize rrNonnegAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_nonneg
    "nonnegative-coefficient lemmas used by RealRooted recurrence tactics"

initialize rrRootBoundAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_root_bound
    "root-location lemmas used by RealRooted recurrence tactics"

initialize rrBasePrecAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_base_prec
    "base Prec cases used by RealRooted recurrence tactics"

initialize rrBaseInterlacesAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_base_interlaces
    "base Interlaces cases used by RealRooted recurrence tactics"

initialize rrMatrixRectAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_matrix_rect
    "matrix rectangularity lemmas used by RealRooted matrix tactics"

initialize rrMatrixNonnegAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_matrix_nonneg
    "matrix nonnegative-coefficient lemmas used by RealRooted matrix tactics"

initialize rrMatrix2x2Attr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_matrix_2x2
    "matrix 2x2 interlacing lemmas used by RealRooted matrix tactics"

initialize rrMatrixThresholdAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_matrix_threshold
    "row-threshold lemmas used by RealRooted matrix tactics"

namespace RealRooted
namespace Tactic

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Elab.Tactic

def rrCertificateAttributes : Array (Name × Lean.TagAttribute) :=
  #[
    (`rr_recurrence, rrRecurrenceAttr),
    (`rr_degree, rrDegreeAttr),
    (`rr_nonzero, rrNonzeroAttr),
    (`rr_pos_lc, rrPosLCAttr),
    (`rr_nonneg, rrNonnegAttr),
    (`rr_root_bound, rrRootBoundAttr),
    (`rr_base_prec, rrBasePrecAttr),
    (`rr_base_interlaces, rrBaseInterlacesAttr),
    (`rr_matrix_rect, rrMatrixRectAttr),
    (`rr_matrix_nonneg, rrMatrixNonnegAttr),
    (`rr_matrix_2x2, rrMatrix2x2Attr),
    (`rr_matrix_threshold, rrMatrixThresholdAttr)
  ]

private def taggedDecls (env : Environment) (attr : Lean.TagAttribute) : Array Name :=
  Id.run do
    let mut names := #[]
    for (declName, _) in env.constants do
      if attr.hasTag env declName then
        names := names.push declName
    return names.qsort Name.quickLt

private def namesString (names : Array Name) : String :=
  if names.isEmpty then
    "(none)"
  else
    String.intercalate ", " (names.toList.map toString)

private def logTaggedCertificates [Monad m] [MonadEnv m] [MonadLog m]
    [MonadOptions m] [AddMessageContext m] : m Unit := do
  let env ← getEnv
  for (attrName, attr) in rrCertificateAttributes do
    let names := taggedDecls env attr
    logInfo m!"[{attrName}] {names.size}: {namesString names}"

end Tactic
end RealRooted

open RealRooted.Tactic

syntax (name := rr_certificates_cmd) "#rr_certificates" : command

elab_rules : command
  | `(command| #rr_certificates) => logTaggedCertificates

syntax (name := rr_certificates_tac) "rr_certificates" : tactic

elab_rules : tactic
  | `(tactic| rr_certificates) => logTaggedCertificates
