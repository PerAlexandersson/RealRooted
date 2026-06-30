# Hadamard Classical Machinery Plan

This is the implementation plan for the classical theorem package behind
`RealRooted.Hadamard`, especially issue #34:

```lean
RealRooted.garloffWagnerHadamardNonnegPrecStatement
```

The current Lean file already has the public Hadamard product API and theorem
interfaces.  The missing work is the classical proof machinery that turns those
interfaces into theorems rather than assumptions.

## Current State

- `RealRooted/Hadamard.lean` defines `hadamardProduct` and proves the basic
  coefficient API, algebraic identities, and nonnegative-coefficient closure.
- The real-rootedness interface
  `garloffWagnerHadamardNonnegRealRootedStatement` is present but not proved.
- The proper-position interface
  `garloffWagnerHadamardNonnegPrecStatement` is present but not proved.
- The downstream wrappers from these interfaces to PF polynomials, `Prec0`, and
  reciprocal-cone closure are already in place.
- `RealRooted/HermiteBiehler.lean`, `RealRooted/HurwitzMatrix.lean`, and the
  interlacing files contain useful adjacent infrastructure, but the finite
  multiplier-sequence, Schur-Szego, Grace apolarity, and Garloff-Wagner stable
  Hadamard theorems are not yet formalized.

## Guiding Principle

Prove the univariate theorem needed by #34 first.  Do not start with the full
multivariate stable-polynomial theory unless it becomes the cleanest route to
the univariate proper-position theorem.

The target theorem is a zero-aware, nonnegative-coefficient wrapper.  The
classical theorem is usually stated for nonzero standard polynomials with only
nonpositive zeros.  The Lean proof should isolate that strict theorem first,
then derive the current `Prec0` wrapper by splitting off zero Hadamard products.

## Milestones

### 0. Audit Statement Orientation

Before proving anything substantial, verify the orientation of:

- `Prec f g`,
- the website notation `f \interl g`,
- Wagner's `f << g` or equivalent convention,
- Garloff-Wagner Theorem 4(b).

Record the chosen translation in the module docstring of `Hadamard.lean`.
This avoids proving a theorem with the right name and the reversed relation.

### 1. Finish the Coefficientwise Hadamard API

Add only the lemmas needed by later proofs.

Likely useful declarations:

```lean
theorem coeff_hadamardProduct
theorem support_hadamardProduct_subset_left
theorem support_hadamardProduct_subset_right
theorem natDegree_hadamardProduct_le_left
theorem natDegree_hadamardProduct_le_right
theorem hadamardProduct_eq_zero_iff_support_disjoint
```

Also add binomial-normalized Hadamard composition for a fixed degree:

```lean
def schurSzegoComp (n : Nat) (f g : R[X]) : R[X]
```

This should model

```text
sum k, choose n k * a_k * b_k * X^k
```

when

```text
f = sum k, choose n k * a_k * X^k
g = sum k, choose n k * b_k * X^k.
```

Keep the ordinary `hadamardProduct` theorem as the public target.  Use
normalization lemmas to move between ordinary coefficients and Schur-Szego
coefficients.

### 2. Formalize Finite Multiplier Sequences

This is the most direct route to the single-polynomial Hadamard theorem.

Introduce a finite-degree predicate:

```lean
def IsFiniteMultiplierSequence (n : Nat) (gamma : Nat -> R) : Prop :=
  forall p : R[X], p.natDegree <= n -> p.Splits ->
    (diagonalOperator gamma p = 0 \/ (diagonalOperator gamma p).Splits)
```

Then prove the finite Polya-Schur/Jensen-polynomial criterion in the
nonpositive-root convention:

```lean
theorem finiteMultiplierSequence_iff_jensen_nonpositive_roots :
  IsFiniteMultiplierSequence n gamma <->
    IsPFPolynomial (sum k in range (n + 1),
      C (choose n k * gamma k) * X ^ k)
```

The exact statement can be adjusted to match Mathlib APIs.  The important point
is that a nonnegative-coefficient real-rooted polynomial gives a diagonal
operator preserving real-rootedness up to degree `n`.

Expected payoff:

```lean
theorem garloffWagnerHadamardNonnegRealRooted :
  garloffWagnerHadamardNonnegRealRootedStatement
```

### 3. Add Schur-Szego Composition

Formalize the degree-`n` composition theorem:

```lean
theorem schurSzegoComp_preserves_realRooted_nonpositive :
  ...
```

This is both a second proof route for real-rootedness and a useful bridge to
the proper-position theorem.  It also gives a clean theorem statement for
documentation and future Mathlib-shaped extraction.

Useful references:

- Schur, 1914.
- Polya-Schur, 1914.
- Rahman-Schmeisser, *Analytic Theory of Polynomials*, for Schur-Szego
  composition.

### 4. Add Grace Apolarity as a Structural Route

The stable-polynomial route usually passes through Grace apolarity or
Grace-Walsh-Szego plus polarization.  For the univariate project, we only need
the finite apolar theorem and its diagonal consequences.

Likely declarations:

```lean
def AreApolar (n : Nat) (f g : C[X]) : Prop := ...

theorem grace_apolarity :
  AreApolar n f g ->
  all_roots_in_circular_domain C f ->
  exists z, z in C /\ g.eval z = 0
```

Do not attempt the whole multivariate stability library at this stage unless it
is cheaper than a finite univariate proof.

### 5. Prove the Garloff-Wagner Proper-Position Theorem

There are two plausible routes.

Route A: stable-pencils route.

1. Translate `Prec f g` into stability of the bivariate or complex pencil
   `g + z * f`, using the existing Hermite-Biehler/Obreschkoff material where
   possible.
2. Prove the Garloff-Wagner stable Hadamard theorem in the special
   nonnegative-coefficient setting.
3. Translate the resulting stable pencil back to `Prec0`.

Route B: finite Schur-Szego route.

1. Prove Schur-Szego composition preserves the appropriate root order for two
   pairs in the same proper-position relation.
2. Normalize coefficients back to ordinary Hadamard products.
3. Derive the zero-aware `Prec0` wrapper.

Route B is likely smaller if the needed theorem can be found in a finite
univariate form.  Route A is more canonical for the Garloff-Wagner paper and may
pay off for later stable-polynomial work.

Expected payoff:

```lean
theorem garloffWagnerHadamardNonnegPrec :
  garloffWagnerHadamardNonnegPrecStatement
```

After this theorem lands, the existing wrappers should give:

```lean
garloffWagnerHadamardPFPrec_of_nonnegPrec
garloffWagnerHadamardPFPrec0_of_nonnegPrec
garloffWagnerHadamardNonnegRealRooted_of_nonnegPrec
hadamardProduct_preserves_pf_of_garloffWagner
hadamardProduct_preserves_prec0_right
hadamardProduct_preserves_prec0_left
hadamardReciprocalConeClosure_of_garloffWagner
```

### 6. Remove the Downstream Assumption

Once #34 is proved in RealRooted:

1. Replace the SuperEulerian `StandardFacts.garloffWagner` field by the
   RealRooted theorem.
2. Build RealRooted.
3. Build SuperEulerian.

Commands:

```bash
lake build RealRooted.Hadamard
lake build
cd /workspace/lean/SuperEulerian && lake build SuperEulerian
```

## Theorem Ledger

| Classical theorem | Lean target or future target |
| --- | --- |
| Schur-Polya/Wagner Hadamard theorem for nonnegative real-rooted polynomials | `garloffWagnerHadamardNonnegRealRootedStatement` |
| Garloff-Wagner Theorem 4(b), proper-position Hadamard closure | `garloffWagnerHadamardNonnegPrecStatement` |
| PF closure under coefficientwise product | `schurPolyaWagnerHadamardPFStatement` and wrappers |
| Finite Polya-Schur theorem | future `finiteMultiplierSequence_iff_jensen_nonpositive_roots` |
| Schur-Szego composition theorem | future `schurSzegoComp_preserves_realRooted_nonpositive` |
| Grace apolarity theorem | future `grace_apolarity` |
| Hadamard products of stable polynomials are stable | possible future stable-polynomial theorem; use only if it shortens #34 |

## Verification Discipline

- For each new Lean theorem, run a focused build on the owning module first.
- Before pushing, run full `lake build`.
- Keep theorem statements upstream-shaped when possible, especially for
  multiplier sequences, Schur-Szego composition, and apolarity.
- Avoid duplicating local helper lemmas.  If a coefficient or degree lemma is
  reusable, put it in the lowest sensible module under `RealRooted/Mathlib/...`
  or the owning `RealRooted` file.
