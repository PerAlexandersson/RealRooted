import RealRooted.MatrixInterlacing.Action
import RealRooted.MatrixInterlacing.SparseTests
import RealRooted.MatrixInterlacing.Converse
import RealRooted.MatrixInterlacing.AffinePair
import RealRooted.MatrixInterlacing.Preservation
import RealRooted.MatrixInterlacing.TotallyNonnegative

/-!
# Matrix preservation of interlacing sequences

Sparse pair machinery, `matPolyAction` definition, forward and backward
matrix-preservation theorems (Brändén, Theorem 7.8.5).
The totally-nonnegative leaf specializes the generic polynomial-matrix theorem
to constant rectangular matrices and proves Fisk's positive-leading wrapper.
-/
