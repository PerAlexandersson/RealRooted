/-
# Wagner's lemma — re-export shim

This file re-exports the split Wagner modules:
- `WagnerX`: Wagner (3) — `Prec f g ↔ Prec g (X·f)` and shifted variants
- `WagnerRightSum`: Wagner (1) — common-right addition theorems
- `WagnerLeftSum`: Wagner (2) — common-left addition theorems, `SumCompatibleLeft`
-/
import RealRooted.WagnerX
import RealRooted.WagnerRightSum
import RealRooted.WagnerLeftSum
