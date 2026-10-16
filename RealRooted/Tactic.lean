module

public import RealRooted.Tactic.Attr
public import RealRooted.Tactic.AllCombo
public import RealRooted.Tactic.AffineDerivative
public import RealRooted.Tactic.AissenSchoenbergWhitney
public import RealRooted.Tactic.Bezoutian
public import RealRooted.Tactic.SideGoals
public import RealRooted.Tactic.ScalarDen
public import RealRooted.Tactic.Sign
public import RealRooted.Tactic.RootBounds
public import RealRooted.Tactic.RootCount
public import RealRooted.Tactic.SignAssembly
public import RealRooted.Tactic.Lookup
public import RealRooted.Tactic.Finish
public import RealRooted.Tactic.StaircaseSum
public import RealRooted.Tactic.CommonInterleaver
public import RealRooted.Tactic.CoefficientShape
public import RealRooted.Tactic.CubicDiscriminant
public import RealRooted.Tactic.Derivative
public import RealRooted.Tactic.EulerOperator
public import RealRooted.Tactic.InterlacingSequence
public import RealRooted.Tactic.Wagner
public import RealRooted.Tactic.WagnerX
public import RealRooted.Tactic.MaWang
public import RealRooted.Tactic.EndpointDerivative
public import RealRooted.Tactic.LiuWangRecursion
public import RealRooted.Tactic.SecondDerivative
public import RealRooted.Tactic.Favard
public import RealRooted.Tactic.LiuWang
public import RealRooted.Tactic.GammaRealRoots
public import RealRooted.Tactic.GeneralizedLaguerre
public import RealRooted.Tactic.MagnitudeDominated
public import RealRooted.Tactic.PreservingOperatorSequence
public import RealRooted.Tactic.Product
public import RealRooted.Tactic.Product.Interlacing
public import RealRooted.Tactic.RecurrenceIdentification
public import RealRooted.Tactic.Recurrence
public import RealRooted.Tactic.RowClosedForm
public import RealRooted.Tactic.RowInterlacing
public import RealRooted.Tactic.ReciprocalShift
public import RealRooted.Tactic.OperatorPreservesInterlacing
public import RealRooted.Tactic.PFPolynomial
public import RealRooted.Tactic.PFBidiagonal
public import RealRooted.Tactic.PosCombo
public import RealRooted.Tactic.FiniteSymbol
public import RealRooted.Tactic.FiniteSymbolPF
public import RealRooted.Tactic.Hadamard
public import RealRooted.Tactic.HermiteBiehler
public import RealRooted.Tactic.HermitePoulain
public import RealRooted.Tactic.HomogenizeStable
public import RealRooted.Tactic.IteratedDerivativeShift
public import RealRooted.Tactic.IteratedDerivativeShiftProduct
public import RealRooted.Tactic.J1Chebyshev
public import RealRooted.Tactic.J1Gap3Reciprocal
public import RealRooted.Tactic.Kurtz
public import RealRooted.Tactic.Linear
public import RealRooted.Tactic.LinearPowerFamily
public import RealRooted.Tactic.Matrix
public import RealRooted.Tactic.MultiplierSequence
public import RealRooted.Tactic.Narayana
public import RealRooted.Tactic.SymmetricDecomposition
public import RealRooted.Tactic.VeroneseSection
public import RealRooted.Tactic.WeightedSum
public import RealRooted.Tactic.OEIS
public import RealRooted.Tactic.Targets

/-!
# RealRooted tactic entry point

This module collects the planned tactic support for recurrence-based
real-rootedness proofs.

The initial implementation goal is intentionally modest: automate the
repeated proof shell in the combinatorial examples, while keeping recurrence,
degree, root-bound, and sign certificates explicit.

The tactic roadmap is tracked in GitHub issue #1061.
-/

public section
