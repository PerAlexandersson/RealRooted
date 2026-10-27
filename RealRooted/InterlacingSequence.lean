module

public import RealRooted.InterlacingSequenceBasic
public import RealRooted.InterlacingSequence.NonnegativeShift
public import RealRooted.CommonInterleaverSeq
public import RealRooted.CommonInterleaverTwo
public import RealRooted.ProductFamily
public import RealRooted.AffineFamily
public import RealRooted.MatrixInterlacing

/-!
# Interlacing sequences and matrices

This is the re-export shim for the split interlacing-sequence modules:

- `InterlacingSequenceBasic`: sequence predicates and basic list-level facts;
- `InterlacingSequence.NonnegativeShift`: simultaneous finite-family
  translation to nonnegative coefficients;
- `CommonInterleaverSeq`: root-slot intervals, Chudnovsky-Seymour, and common
  interleavers;
- `CommonInterleaverTwo`: compatibility/common-interleaver bridge targets;
- `ProductFamily`: `zipWith` product constructions (Brändén 7.8.3);
- `AffineFamily`: `Has2x2InterlacingProperty`, affine criterion
  (Brändén 7.8.4);
- `MatrixInterlacing`: sparse pairs and matrix preservation (Brändén 7.8.5).
-/

public section
