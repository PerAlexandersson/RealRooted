import RealRooted.NarayanaTransformation.Basis
import RealRooted.NarayanaTransformation.Coefficients
import RealRooted.NarayanaTransformation.Endpoints
import RealRooted.NarayanaTransformation.Falling
import RealRooted.NarayanaTransformation.Gamma
import RealRooted.NarayanaTransformation.Rectangular
import RealRooted.NarayanaTransformation.Recurrences
import RealRooted.NarayanaTransformation.Rising
import RealRooted.NarayanaTransformation.RootGeometry

/-!
# The Narayana Transformation

This module starts a formalization of Mao--Wang, *The Narayana transformation*,
arXiv:2607.01572v1.

The main paper theorem says that the basis transformation
`X ^ k ↦ N_{k,m}` preserves real-rooted polynomials with nonnegative
coefficients.  The proof uses Gribinski--Marcus rectangular additive
convolution.  We first expose the reusable basis-transformation interfaces from
the paper and the checked coefficient infrastructure for the generalized
Narayana polynomials.  This module is the compatibility facade for the focused
proof layers in `NarayanaTransformation/`.
-/
