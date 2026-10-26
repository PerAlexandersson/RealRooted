module

public import Batteries.Lean.TagAttribute
public meta import Batteries.Lean.TagAttribute

set_option rr.row.explain true
set_option linter.style.longLine false

/-!
# Row-model registry

The `rr_row_model` attribute marks transfer theorems that identify a recurrence sequence
with a model whose splitting or adjacent interlacing is already known. The row tactics
inspect these declarations without importing their application modules.
-/

public meta section

/-- Model-transfer theorems available to the row tactics. -/
initialize rrRowModelAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_row_model
    "model-transfer theorems used by RealRooted row tactics"
