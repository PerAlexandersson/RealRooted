module

import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Dominance
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Nonneg

/-!
# Perron–Frobenius theorem

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "perron-frobenius"
formalized = "2026-08-21"
references = [
  "Perron1907",
]
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
label = "Perron–Frobenius: an irreducible nonnegative matrix has a positive eigenvector"
headline = true

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

A nonnegative square matrix has its Collatz–Wielandt value as an eigenvalue with a nonnegative
eigenvector, and for irreducible matrices this eigenvector is positive and the eigenvalue is the
spectral radius.

## Results

Let $A$ be a nonnegative real $n\times n$ matrix, $n\ge1$. The *Perron root* is
$$
r(A) = \sup_{v \geq 0,\ v \neq 0}\ \min_{i\,:\,v_i > 0} \frac{(Av)_i}{v_i}.
$$

**Theorem (Perron–Frobenius).** [@Perron1907]

- $r(A)$ is an eigenvalue of $A$ with a nonnegative eigenvector.
- If $A$ is irreducible, then $A$ has an eigenvector with positive entries and a positive
  eigenvalue. Moreover $r(A)\in\operatorname{spec}(A)$ and $|\mu|\le r(A)$ for every real
  eigenvalue $\mu$.
- If $A$ is primitive (some power is entrywise positive), then there is exactly one
  nonnegative eigenvector of sum $1$ with positive eigenvalue.
- If $Av=rv$ with $v$ entrywise positive and $r>0$, then $r=r(A)$.

## Use

The Perron root controls the growth of $A^n$. Applied to a companion or transfer matrix, it is
a root of maximal modulus of a linear recurrence with nonnegative coefficients, which locates
the dominant root in [limits of zeros](rr:limits-of-zeros) arguments.

## Proof

Existence comes from upper semicontinuity of the Collatz–Wielandt function on the standard
simplex. The irreducible case reduces to the primitive case through $1+A$.

## References

[@Perron1907]; G. Frobenius, “Über Matrizen aus nicht negativen Elementen,”
*Sitzungsberichte der Königlich Preussischen Akademie der Wissenschaften* (1912), 456–477.
<!-- /realrooted-catalog-content -->
-/
