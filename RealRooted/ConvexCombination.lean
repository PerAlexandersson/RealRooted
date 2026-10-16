/-
# Convex combinations preserve interlacing — re-export shim

This file re-exports the split ConvexCombination modules:
- `WeightedSum`: weightedSum, WeightedCompatibleLeft, prec_sum_*
- `PosCombo`: PosComboRealRooted, family/coprimeness lemmas, convex wrappers
- `AllCombo`: AllComboRealRooted, iterateTDeriv infrastructure
- `ObreschkoffConverse`: Wronskian, strictInterl_of_allComboRealRooted
-/

module

public import RealRooted.WeightedSum
public import RealRooted.PosCombo
public import RealRooted.AllCombo
public import RealRooted.ObreschkoffConverse

public section

