module

public import Batteries.Lean.TagAttribute

/-!
# Row-model registry

The `rr_row_model` attribute marks transfer theorems that identify a recurrence sequence
with a model whose splitting or adjacent interlacing is already known. The row tactics
inspect these declarations without importing their application modules.
-/

@[expose] public section

/-- Model-transfer theorems available to the row tactics. -/
initialize rrRowModelAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `rr_row_model
    "model-transfer theorems used by RealRooted row tactics"
