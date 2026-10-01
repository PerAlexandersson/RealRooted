import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Dominance
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Nonneg

/-!
# Perron–Frobenius theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "perron-frobenius"
authors = ["Perron", "Frobenius"]
years = [1907, 1912]

[[definitions]]
name = "Matrix.CollatzWielandt.perronRoot"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt"
label = "Perron root"

[[theorems]]
name = "Matrix.exists_nonneg_mulVec_eq_perronRoot_smul"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Nonneg"
label = "The Perron root has a nonnegative eigenvector"

[[theorems]]
name = "Matrix.exists_positive_eigenvector_of_irreducible"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Irreducible"
label = "Irreducible matrices have a positive eigenvector"

[[theorems]]
name = "Matrix.pft_primitive"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Irreducible"
label = "Primitive matrices: uniqueness of the eigenvector"

[[theorems]]
name = "Matrix.perron_root_is_spectral_radius"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Dominance"
label = "The Perron root is the spectral radius"

[[theorems]]
name = "Matrix.CollatzWielandt.eq_perron_root_of_positive_eigenvector"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt"
label = "A positive eigenvector belongs to the Perron root"
-->

<!-- realrooted-catalog-content -->
# Perron–Frobenius theorem

For a square matrix `A` with nonnegative real entries, the **Perron root** is
the Collatz–Wielandt value

```text
r(A) = sup over nonnegative v ≠ 0 of  min over i with v_i > 0 of (A v)_i / v_i.
```

**Theorem (Perron–Frobenius).**

- Every nonnegative matrix has `r(A)` as an eigenvalue, with a nonnegative
  eigenvector.
- If `A` is irreducible, the eigenvalue `r(A)` is positive and has a strictly
  positive eigenvector. Moreover `r(A)` is the spectral radius: every real
  eigenvalue `μ` satisfies `|μ| ≤ r(A)`.
- If `A` is primitive (some power is entrywise positive), a nonnegative
  eigenvector with positive eigenvalue is unique up to scaling.
- A strictly positive eigenvector can only belong to the eigenvalue `r(A)`.

The proofs go through the Collatz–Wielandt function on the standard simplex,
upper semicontinuity and compactness for existence, and a triangle-equality
phase argument for dominance. The irreducible case is reduced to the primitive
one through `1 + A`.

## References

O. Perron, “Zur Theorie der Matrices,” Mathematische Annalen 64 (1907),
248–263.

G. Frobenius, “Über Matrizen aus nicht negativen Elementen,” Sitzungsberichte
der Königlich Preussischen Akademie der Wissenschaften (1912), 456–477.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius`.
-/
