/-
# Wagner's lemma — re-export shim

This file re-exports the split Wagner modules:
- `WagnerX`: Wagner (3) — `Prec f g ↔ Prec g (X·f)` and shifted variants
- `WagnerRightSum`: Wagner (1) — common-right addition theorems
- `WagnerLeftSum`: Wagner (2) — common-left addition theorems, `SumCompatibleLeft`

Primary source for Wagner (1)/(2)/(3):

D. G. Wagner, *Total positivity of Hadamard products*,
J. Math. Anal. Appl. 163 (1992), no. 2, 459-483.
DOI: 10.1016/0022-247X(92)90261-B
-/
import RealRooted.WagnerX
import RealRooted.WagnerRightSum
import RealRooted.WagnerLeftSum
