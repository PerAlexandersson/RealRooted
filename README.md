# RealRooted

`RealRooted` is an experimental Lean 4 library for real-rooted univariate
polynomials, interlacing, compatibility, Polya-frequency sequences, and related
combinatorial applications.

The repository is a research formalization workspace rather than a polished
mathlib contribution.  The useful part is that the named theorem declarations
below are checked by Lean, and the surrounding files give searchable proof
infrastructure for real-rootedness and interlacing arguments.  The long-term
goal is to extract stable, reusable components for eventual upstreaming.

## Table of Contents

- [Build](#build)
- [Repository Layout](#repository-layout)
- [Main Concepts](#main-concepts)
- [Checked Highlights](#checked-highlights)
- [Current Roadmap](#current-roadmap)
- [Development Notes](#development-notes)
- [Bibliography and Links](#bibliography-and-links)

## Build

The project uses Lean 4 and Mathlib through Lake.

```bash
lake exe cache get
lake build
```

Useful focused checks for recent theorem areas are:

```bash
lake build RealRooted.CommonInterleaverTwo
lake build RealRooted.ChudnovskySeymour
lake build RealRooted.Hadamard
lake build RealRooted.VeroneseMatrix
lake build RealRooted.VeroneseSection
lake build RealRooted.Bezoutian
```

## Repository Layout

- `RealRooted.lean` is the umbrella import for the public development.
- `RealRooted/Basic.lean`, `Derivative.lean`, `Wagner*.lean`, and
  `InterlacingSequence*.lean` contain the core interlacing API.
- `RealRooted/CommonInterleaver*.lean` and `ChudnovskySeymour.lean` contain the
  compatibility and common-interleaver work.
- `RealRooted/AissenSchoenbergWhitney.lean`, `PFPolynomial.lean`,
  `VeroneseSection.lean`, and `VeroneseMatrix.lean` contain the PF, Toeplitz,
  and Veronese-section material.
- `RealRooted/SymmetricDecomposition.lean`, `Bezoutian.lean`, and
  `Hadamard.lean` contain larger theorem packages and classical interfaces.
- `RealRooted/Challenges/` contains compact entry points for famous theorem
  statements, each linking the Lean-facing declaration to human catalog
  statements and references.
- `RealRooted/CombinatorialExamples/` contains examples such as Eulerian,
  type B Eulerian, simsun, Touchard, Narayana, Motzkin, and related families.
- `RealRooted/Mathlib/` contains local compatibility lemmas intended to look
  like future Mathlib additions.

## Main Concepts

- `Interlaces f g`, `Prec f g`, and `Prec0 f g`: the main interlacing and
  proper-position relations.  `Prec0` is the zero-aware version.
- `p = 0 ∨ p.Splits`: the zero-aware real-rootedness convention used in closure
  statements where the zero polynomial is a natural exceptional case.
- `IsGeneralizedSturmSeq ps`, `IsInterlacingSeq fs`, and `IsInterlacingSeq0 fs`:
  list-level Sturm and interlacing predicates.
- `Compatible f g`, `PairwiseCompatible fs`, and `FamilyCompatible fs`:
  Chudnovsky-Seymour style compatibility predicates.
- `HasCommonInterleaver fs` and `HasCommonLeftInterleaver fs`: common
  interleaver data for finite families.
- `AllComboRealRooted f g`: every real linear combination of `f` and `g` is
  zero or real-rooted.
- `IsPolyaFreqSeq a`: total nonnegativity of the Toeplitz matrix of a sequence.
- `veroneseSectionPolynomial r k p`: the fixed-residue Veronese section of a
  polynomial.
- `FullyInterlacingPair a b`: the two-row Lace total-nonnegativity interface
  used by the Veronese and Hurwitz-matrix route.

## Checked Highlights

Every declaration named in this section is a checked Lean declaration, unless
it is explicitly described as an unproved conjecture (bearing a `sorry` stub).

### Theorem-Level Highlights

The formalization now contains theorem interfaces for several standard
real-rootedness and interlacing results.  In ordinary mathematical language,
the checked or challenge-facing highlights are:

- Cauchy interlacing: the eigenvalues of a principal codimension-one submatrix
  of a real symmetric or Hermitian matrix interlace the eigenvalues of the
  original matrix.  See `cauchy_interlacing` and
  `RealRooted.Challenges.CauchyInterlacing`; references include Fisk (2005)
  and Godsil (2017).
- Wagner's lemma: for real-rooted polynomials with nonpositive roots and
  positive leading coefficients, common interlacers are closed under addition,
  and multiplication by `X` shifts the interlacing relation in the expected
  way.  See `RealRooted.Challenges.Wagner`; reference: Wagner (1992).
- Obreschkoff's theorem: two polynomials have a real-rooted real pencil
  `alpha * f + beta * g` if and only if they interlace, up to orientation and
  degree conventions.  See `allComboRealRooted_of_prec`,
  `prec_of_allComboRealRooted`, and `RealRooted.Challenges.Obreschkoff`;
  references include Obreschkoff (1963), Dedieu (1992), and Branden (2004).
- Interlacing preservers: a linear operator that preserves real-rootedness
  sends interlacing pairs to interlacing pairs, up to the zero and orientation
  conventions used by `Prec0`.  See
  `operatorPreservesInterlacingPairsUpToOrder` and
  `RealRooted.Challenges.OperatorPreservers`; reference: Branden (2004).
- Matrix preservers: a polynomial matrix with nonnegative coefficients
  preserves interlacing sequences when its two-by-two affine tests interlace.
  See `matrix_preserves_interlacing_seq` and
  `RealRooted.Challenges.MatrixInterlacing`; reference: Branden (2015).
- Favard interlacing: a three-term Favard recurrence with positive recurrence
  coefficients gives a Sturm sequence, hence every polynomial in the sequence
  is real-rooted.  See `favardInterlacing` and
  `RealRooted.Challenges.Favard`; reference: Favard (1935).
- Polya-frequency and Veronese results: the ASW reverse direction and the
  Toeplitz/PF infrastructure imply that Veronese sections of a real-rooted
  polynomial with nonnegative coefficients are real-rooted or zero.  See
  `aissenSchoenbergWhitney_reverse`,
  `isRealRootedOrZero_veroneseSectionPolynomial_of_realRooted_nonneg_matrix`,
  and `RealRooted.Challenges.VeroneseSections`; references include
  Aissen--Schoenberg--Whitney (1952) and Athanasiadis--Wagner (2024).
- Eulerian examples: ordinary Eulerian and type `B` Eulerian polynomials are
  real-rooted, and the formalization proves stronger consecutive interlacing
  or Sturm-sequence statements.  See `RealRooted.Challenges.Eulerian`;
  references include Frobenius (1910).
- Graph polynomials: finite claw-free graphs have real-rooted independence
  polynomials, and matching-polynomial corollaries are packaged through the
  line-graph reduction.  See `Graph.clawFree_indepPoly_splits` and
  `RealRooted.Challenges.ChudnovskySeymour`; references include
  Chudnovsky--Seymour (2007) and Heilmann--Lieb (1972).

The challenge surface also records theorem-shaped targets as they mature.
Kurtz's coefficient inequality criterion and the finite Hermite--Poulain
differential-operator preserver are checked, while Borcea--Branden's
finite-symbol classification is currently a scaffold because a faithful
statement needs a multivariate real-stability API.

### Interlacing And Preservers

- `derivative_interlaces`: Rolle-style derivative interlacing for real-rooted
  polynomials.
- `prec_add_of_prec_right_of_posLeadingCoeff`, `prec_add_of_prec_left`, and
  `prec0_mul_X_of_prec0`: checked Wagner-lemma forms for common interlacers
  and multiplication by `X`.
- `prec_ma_wang` and `generalizedLiuWangCriterion`: Ma-Wang and Liu-Wang style
  criteria for interlacing recurrences and weighted sums.
- `favardInterlacing` and `isRealRooted_of_favard`: a Favard recurrence
  interface for orthogonal-polynomial style Sturm sequences.
- `matrix_preserves_interlacing_seq` and
  `matrix_preserves_interlacing_seq0_of_2x2`: matrix preservers from finite
  two-by-two interlacing checks.
- `operatorPreservesInterlacingPairsUpToOrder`: a general operator-preserver
  interface for interlacing pairs.
- `cauchy_interlacing`: Cauchy's eigenvalue interlacing theorem for Hermitian
  matrices and one-index principal submatrices.

### Compatibility And Common Interleavers

- `hasCommonInterleaver_of_pairwiseHasCommonInterleaver`: pairwise common
  interleavers imply a global common interleaver.
- `isRealRooted_sum_of_commonInterleaver` and
  `isRealRooted_sum_of_commonLeftInterleaver`: nonnegative sums are real-rooted
  when a family has common interleaver data.
- `familyCompatible_of_commonInterleaver` and
  `pairwiseCompatible_of_familyCompatible`: the easy directions relating
  common interleavers and compatibility.
- Declarations with prefix `chudnovskySeymour_fourWay_of_`: several checked
  Chudnovsky-Seymour four-way packages under formalized bridge hypotheses.
- `pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one`: the complete
  low-degree compatibility equivalence.

### Symmetric Decomposition And Bezoutians

- `idDecompositionExistsUnique` and `rdDecompositionExistsUnique`: existence
  and uniqueness of the Branden-Solus symmetric decompositions.
- `brandenSolusTheorem26`: the formalized Branden-Solus Theorem 2.6 package in
  the local `Prec` language.
- `isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs`: real-rootedness
  preservation for the `h -> f` transform in the nonnegative setting.
- `strictPrecSameDegree_iff_bezoutMatrix_posDef`: strict same-degree
  Bezoutian characterization.

### Polya Frequency, ASW, And Veronese Sections

- `aissenSchoenbergWhitney_reverse`: the reverse Aissen-Schoenberg-Whitney
  direction, from real-rooted nonpositive roots and nonnegative coefficients to
  a Polya-frequency coefficient sequence.
- `aissenSchoenbergWhitneyForward`: the target theorem for the opposite ASW
  direction.
- `IsPolyaFreqSeq.veroneseSectionSeq` and
  `IsPolyaFreqSeq_veroneseSectionPolynomial_coeff`: Veronese subsequences and
  Veronese section coefficients preserve Toeplitz total nonnegativity.
- `isRealRootedOrZero_veroneseSectionPolynomial_of_realRooted_nonneg_matrix`:
  the completed cyclic-matrix proof that Veronese sections of a real-rooted
  nonnegative-coefficient polynomial are zero or real-rooted.
- `not_isUpperHalfPlaneStable_hermiteBiehlerPolynomial_X_neg_one`: a checked
  counterexample documenting why the Hermite-Biehler forward route is exposed
  only in sign-normalized form.

### Combinatorial Examples

The example files prove real-rootedness and, in many cases, Sturm or interlacing
sequence statements for standard combinatorial families.  Representative
declarations include:

- `isRealRooted_eulerianTilde`
- `isRealRooted_typeBEulerian`
- `isRealRooted_simsun`
- `isRealRooted_touchard`
- `isRealRooted_coloredSetPartitions`
- `isRealRooted_narayana_of_nonnegCoeffs`
- `isRealRooted_motzkin`

## Current Roadmap

The Chudnovsky-Seymour and Heilmann-Lieb graph-facing line is now represented
by checked theorem interfaces in `ChudnovskySeymour.lean` and
`HeilmannLieb.lean`.  The graph endpoint is
`Graph.clawFree_indepPoly_splits`: finite claw-free graphs have real-rooted
independence polynomials.  The matching-polynomial corollaries are packaged
through the line-graph reduction in `HeilmannLieb`.

The next standard theorem input is Garloff-Wagner Hadamard proper-position,
recorded as `garloffWagnerHadamardNonnegPrec`.  This is the remaining
RealRooted theorem currently used as an external standard fact by the
`SuperEulerian` project.

New formalization target: Braun-Jal, *Order polytopes of generalized snake
posets are h^*-real-rooted*, arXiv:2607.00922v1.  The immediate Lean todo is
their Theorem 4.1: for a generalized snake word `w` of length `n >= 1`, the
non-nesting rook polynomial `M_{epsilon w}` is real-rooted and the polynomial
for the word with the final letter deleted interlaces it.  Concrete subtasks:
define generalized snake words, deletion of the final letter, and prefix
operations; define the associated squarecase/non-nesting rook polynomials;
formalize the modified Narayana polynomials `P_n`, the auxiliary sums `G_n`,
and the interlacing inputs behind Lemmas 3.3 and 3.4; prove the positive
non-nesting recurrence of Theorem 3.5; expose the Branden matrix interlacing
preserver used in the induction; prove Theorem 4.1 by strong induction; then
package the resulting h^*-real-rootedness statement for order polytopes via the
Stanley / Alexandersson-Jal width-two correspondence.

Short-term documentation/onboarding now uses concise challenge entry-point files
in `RealRooted/Challenges/` for the famous general theorems and theorem-shaped
targets.  These files point to the corresponding human theorem statements on
symmetricfunctions.com and to the original publications or catalog references,
while the detailed proof infrastructure remains in the main theorem modules.
The current challenge surface includes ASW, Chudnovsky-Seymour, Hadamard,
Wagner, Cauchy interlacing, Obreschkoff, operator and matrix interlacing
preservers, Hermite-Biehler/Hurwitz, Veronese sections, Favard, Kurtz,
Hermite-Poulain, Borcea-Branden, and Eulerian polynomials.

Longer term, a Borcea-Branden direction would be a substantial expansion toward
stability theory.  A realistic path would first build the Hermite-Biehler and
Hurwitz-matrix total-nonnegativity interfaces into proved theorems, then add the
multivariate stability infrastructure needed for algebraic-symbol preserver
theorems.

GitHub issues track individual proof tasks rather than being duplicated here.
Current open themes include Liu's compatible-sequences theorem, the
Gustafsson-Solus interlacing recursion, the Haglund-Zhang `s`-inversion
backend, characteristic-polynomial packaging for Cauchy interlacing, a finite
Borcea-Branden symbol interface, and the Braun-Jal generalized snake poset
target.

## Development Notes

For unproved conjectures and target theorem interfaces, the project prefers
declaring standard Lean `theorem` signatures with `sorry` proofs. We avoid
passing conjectures around as hypothetical parameters (axioms in disguise).
Using standard `sorry` stubs simplifies downstream signatures, avoids
parameter propagation clutter, and aligns with Mathlib best practices.

New Lean code should follow the Lean community style guidelines and Mathlib
naming conventions where practical.  In particular, keep declarations explicit,
prefer small reusable lemmas, keep top-level declarations flush-left, and make
sure public modules are imported by `RealRooted.lean`. All committed code must
build without warnings (with the exception of `sorry` warnings).

To maintain clean and reliable build verification, the use of `set_option` is
forbidden in the codebase. All warnings, lint errors, or resource limits should
be addressed by refining the underlying proofs and definitions rather than
suppressing them.

To ensure proofs are deterministic and maintainable, the use of `try`,
`all_goals`, and `any_goals` tactics is forbidden in proofs (they remain
permitted inside custom tactic implementations). Proofs should use structured
casing or sequential composition instead. Similarly, the use of `simp +decide`
and `simp_all +decide` is discouraged; prefer `simp` and `simp_all` without
`+decide` whenever possible.

Please keep repository configuration files (like `lakefile.toml` and
  `lake-manifest.json`) free of hardcoded absolute paths such as
  `/lake-cache/projects/...`. Reusable relative repository paths
  (e.g. `.lake/packages` and `.lake/build`) ensure that the builds work
  out-of-the-box in local developer environments.

### Repository Cleanliness

To maintain a polished repository:
* Do not commit transient development artifacts such as build logs (`*.log`),
  Git patch files (`*.patch`), backup files (e.g., `*~`), or temporary
  scratch files.
* Keep issue-specific design or reference notes local. Note that `.gitignore`
  is configured to ignore all Markdown (`*.md`) files by default, with
  exceptions only for `README.md` and `RealRooted/Tactic/PLAN.md`.
* Ensure any new types of temporary files or scratch directories are kept
  local or explicitly added to `.gitignore`.

## Bibliography and Links

- M. Aissen, I. J. Schoenberg, and A. M. Whitney, *On the generating functions
  of totally positive sequences. I*, J. Analyse Math. 2 (1952), 93--103.
- C. A. Athanasiadis and C. H. Wagner, *Veronese sections and interlacing
  matrices of polynomials and formal power series*, arXiv:2404.12989.
- J. Borcea and P. Branden, *The Lee-Yang and Polya-Schur programs. I. Linear
  operators preserving stability*, Invent. Math. 177 (2009), 541--569.
- P. Branden, *On operators on polynomials preserving real-rootedness and the
  Neggers-Stanley conjecture*, J. Algebraic Combin. 20 (2004), 119--130.
- P. Branden, *Iterated sequences and the geometry of zeros*, J. Reine Angew.
  Math. 658 (2011), 115--131.
- P. Branden, *Unimodality, log-concavity, real-rootedness and beyond*, in
  *Handbook of Enumerative Combinatorics*, CRC Press, 2015, 437--483.
- B. Braun and A. Jal, *Order polytopes of generalized snake posets are
  h^*-real-rooted*, arXiv:2607.00922.
- P. Branden and L. Solus, *Symmetric decompositions and real-rootedness*,
  Int. Math. Res. Not. (2019), doi:10.1093/imrn/rnz059.
- M. Chudnovsky and P. Seymour, *The roots of the independence polynomial of a
  clawfree graph*, J. Combin. Theory Ser. B 97 (2007), 350--357.
- J.-P. Dedieu, *Obreschkoff's theorem revisited: what convex sets are
  contained in the set of hyperbolic polynomials?*, J. Pure Appl. Algebra 81
  (1992), 269--278.
- J. Favard, *Sur les polynomes de Tchebicheff*, C. R. Acad. Sci. Paris 200
  (1935), 2052--2053.
- S. Fisk, *A very short proof of Cauchy's interlace theorem for eigenvalues
  of Hermitian matrices*, Amer. Math. Monthly 112 (2005), 118.
- F. G. Frobenius, *Uber die Bernoullischen Zahlen und die Eulerschen
  Polynome*, Sitzungsberichte der Koniglich Preussischen Akademie der
  Wissenschaften (1910), 809--847.
- J. Garloff and D. G. Wagner, *Hadamard Products of Stable Polynomials Are
  Stable*, J. Math. Anal. Appl. 202 (1996), 797--809.
- C. D. Godsil, *Algebraic Combinatorics*, Routledge, 2017.
- O. J. Heilmann and E. H. Lieb, *Theory of monomer-dimer systems*, Comm. Math.
  Phys. 25 (1972), 190--232.
- J. I. Hutchinson, *On a remarkable class of entire functions*, Trans. Amer.
  Math. Soc. 25 (1923), 325--332.
- O. Holtz, *Hermite-Biehler, Routh-Hurwitz, and total positivity*, Linear
  Algebra Appl. 372 (2003), 105--110.
- D. C. Kurtz, *A sufficient condition for all the roots of a polynomial to be
  real*, Amer. Math. Monthly 99 (1992), 259--263.
- N. Obreschkoff, *Verteilung und Berechnung der Nullstellen reeller
  Polynome*, VEB Deutscher Verlag der Wissenschaften, Berlin, 1963.
- D. G. Wagner, *Total positivity of Hadamard products*, J. Math. Anal. Appl.
  163 (1992), 459--483.
- Symmetric Functions Catalog:
  <https://www.symmetricfunctions.com/realRooted.htm>,
  <https://www.symmetricfunctions.com/realRootedInterlacing.htm>,
  <https://www.symmetricfunctions.com/polyaFrequency.htm>, and
  <https://www.symmetricfunctions.com/realRootedWords.htm>.
