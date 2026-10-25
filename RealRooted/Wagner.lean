/-
# Wagner's lemma — re-export shim

This file re-exports the split Wagner modules:
- `WagnerX`: Wagner (3) — `StrictInterl f g ↔ StrictInterl g (X·f)` and shifted variants
- `WagnerRightSum`: Wagner (1) — common-right addition theorems
- `WagnerLeftSum`: Wagner (2) — common-left addition theorems, `SumCompatibleLeft`
-/
module

public import RealRooted.WagnerX
public import RealRooted.WagnerRightSum
public import RealRooted.Wagner.LeftSum

@[expose] public section
