/-
# Convex combinations preserve interlacing — re-export shim

This file re-exports the split ConvexCombination modules:
- `WeightedSum`: weightedSum, WeightedCompatibleLeft, prec_sum_*
- `PosCombo`: PosComboRealRooted, family/coprimeness lemmas, convex wrappers
- `AllCombo`: AllComboRealRooted, iterateTDeriv infrastructure
- `ObreschkoffConverse`: Wronskian, prec_of_allComboRealRooted
-/
import RealRooted.WeightedSum
import RealRooted.PosCombo
import RealRooted.AllCombo
import RealRooted.ObreschkoffConverse
