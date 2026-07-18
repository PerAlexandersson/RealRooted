import RealRooted.Tactic.Attr
import RealRooted.Tactic.AllCombo
import RealRooted.Tactic.SideGoals
import RealRooted.Tactic.ScalarDen
import RealRooted.Tactic.Sign
import RealRooted.Tactic.RootBounds
import RealRooted.Tactic.Lookup
import RealRooted.Tactic.Finish
import RealRooted.Tactic.CoefficientShape
import RealRooted.Tactic.CubicDiscriminant
import RealRooted.Tactic.Derivative
import RealRooted.Tactic.EulerOperator
import RealRooted.Tactic.WagnerX
import RealRooted.Tactic.MaWang
import RealRooted.Tactic.LiuWangRecursion
import RealRooted.Tactic.SecondDerivative
import RealRooted.Tactic.Favard
import RealRooted.Tactic.LiuWang
import RealRooted.Tactic.GammaRealRoots
import RealRooted.Tactic.MagnitudeDominated
import RealRooted.Tactic.Product
import RealRooted.Tactic.OperatorPreservesInterlacing
import RealRooted.Tactic.PFPolynomial
import RealRooted.Tactic.PFBidiagonal
import RealRooted.Tactic.FiniteSymbolPF
import RealRooted.Tactic.FiniteSymbolPFFrontend
import RealRooted.Tactic.PFBidiagonalFrontend
import RealRooted.Tactic.I2DerivativeLag
import RealRooted.Tactic.IteratedDerivativeShift
import RealRooted.Tactic.J1Chebyshev
import RealRooted.Tactic.J1Gap3Reciprocal
import RealRooted.Tactic.Linear
import RealRooted.Tactic.LinearPowerFamily
import RealRooted.Tactic.Matrix
import RealRooted.Tactic.MultiplierSequence
import RealRooted.Tactic.SymmetricDecomposition
import RealRooted.Tactic.VeroneseSection
import RealRooted.Tactic.WeightedSum
import RealRooted.Tactic.OEIS
import RealRooted.Tactic.Targets

/-!
# RealRooted tactic entry point

This module collects the planned tactic support for recurrence-based
real-rootedness proofs.

The initial implementation goal is intentionally modest: automate the
repeated proof shell in the combinatorial examples, while keeping recurrence,
degree, root-bound, and sign certificates explicit.

See `RealRooted/Tactic/PLAN.md` for the implementation plan.  The repository
normally ignores new Markdown files, so `.gitignore` has a narrow exception
for this tactic plan.
-/
