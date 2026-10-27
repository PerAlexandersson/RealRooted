module

public import RealRooted.NarayanaTransformation.Basis
public import RealRooted.NarayanaTransformation.Basis.Stirling
public import RealRooted.NarayanaTransformation.Coefficients
public import RealRooted.NarayanaTransformation.Endpoints
public import RealRooted.NarayanaTransformation.Falling
public import RealRooted.NarayanaTransformation.Gamma
public import RealRooted.NarayanaTransformation.Rectangular
public import RealRooted.NarayanaTransformation.Recurrences
public import RealRooted.NarayanaTransformation.Rising
public import RealRooted.NarayanaTransformation.RootGeometry

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

public section
