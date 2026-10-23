# Centered Eulerian polynomials

The modules in `RealRooted/CenteredEulerian/` develop the coefficients of
`sqrt(1-s²) (sec + tan)(c arcsin s)` as polynomials in `c`. They are independent
of a permutation model. The Eulerian compendium identifies these coefficients
with its finite zig-zag permutation quotient in the downstream paper library.

The proof follows Appendix B of `alternating_eulerian_shorter_proof.md`, added
to the Eulerian compendium as part of `thm:zigzagEulerian`. Formal series and
coefficient identities lead to a banded multiplication matrix. Parity gives a
finite eigenvector at each root; a strict weighted column bound places that
root in `Complex.normSq c < 13/3`. The matrix norm argument imports
`Matrix.norm_lt_of_weighted_column_sum_lt`, rather than duplicating it.

`Riccati.lean` supplies the formal-series uniqueness and parameter-shift
identities from Appendix A. The downstream weak-word enumeration establishes
which finite permutation polynomial these coefficients represent.

The analytic estimates use the cotangent expansion formalized in Mathlib;
see NIST DLMF 4.22.3 (cotangent) and 4.22.5 (cosecant). The combinatorial
interpretation and its literature references belong to the downstream paper.

Aristotle supplied the initial Lean 4.28 candidate in task
`61da6424-89ea-4fbf-852c-6e47d3e3aef9`. Integration ports it to Lean 4.35,
uses explicit imports and project proof conventions, and checks the actual
statements and axiom closure locally. The full default build passes (11144 jobs); all five endpoint axiom
audits use only `propext`, `Classical.choice` and `Quot.sound`. The universal
disk-to-interval transfer lives in `IntervalDifferential/`.
