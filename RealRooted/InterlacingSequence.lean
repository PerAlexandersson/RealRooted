import RealRooted.InterlacingSequenceBasic
import RealRooted.CommonInterleaverSeq
import RealRooted.CommonInterleaverTwo
import RealRooted.ProductFamily
import RealRooted.AffineFamily
import RealRooted.MatrixInterlacing

/-!
# Interlacing sequences and matrices

This is the re-export shim for the split interlacing-sequence modules:

- `InterlacingSequenceBasic`: sequence predicates and basic list-level facts;
- `CommonInterleaverSeq`: root-slot intervals, Chudnovsky-Seymour, and common
  interleavers;
- `CommonInterleaverTwo`: compatibility/common-interleaver bridge targets;
- `ProductFamily`: `zipWith` product constructions (Brändén 7.8.3);
- `AffineFamily`: `Has2x2InterlacingProperty`, affine criterion
  (Brändén 7.8.4);
- `MatrixInterlacing`: sparse pairs and matrix preservation (Brändén 7.8.5).
-/
