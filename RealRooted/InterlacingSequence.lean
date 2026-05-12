/-
# Interlacing sequences and matrices — re-export shim

This file re-exports the split InterlacingSequence modules:
- `InterlacingSequenceBasic`: sequence predicates, basic list-level properties
- `CommonInterleaverSeq`: root-slot intervals, Chudnovsky-Seymour, common interleaver
- `CommonInterleaverTwo`: compatibility/common-interleaver bridge targets
- `ProductFamily`: zipWith product constructions (Brändén 7.8.3)
- `AffineFamily`: Has2x2InterlacingProperty, affine criterion (Brändén 7.8.4)
- `MatrixInterlacing`: sparse pairs, matrix preservation (Brändén 7.8.5)
-/
import RealRooted.InterlacingSequenceBasic
import RealRooted.CommonInterleaverSeq
import RealRooted.CommonInterleaverTwo
import RealRooted.ProductFamily
import RealRooted.AffineFamily
import RealRooted.MatrixInterlacing
