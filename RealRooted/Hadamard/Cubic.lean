import RealRooted.Hadamard.Newton

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Cubic Schur--Szego reductions

Degree-three PF-factor reductions, normalized diagonal base cases, and the
finite Polya--Schur equivalence interfaces.
-/

/-- Nonzero-core version of the arbitrary-level Schur--Szego base case with a
degree-`≤ 2` PF factor. -/
theorem finiteSchurSzegoCompositionNonzero_of_pf_factor_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 2)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
    hf hfdeg hpdeg hsplit

/-- If the degree-`n` Jensen polynomial is PF and itself has degree at most
two, then the diagonal sequence is a finite multiplier sequence through degree
`n`.

Unlike `isFiniteMultiplierSequence_of_isPF_jensenPolynomial_natDegree_le_two`,
the degree bound here is on the Jensen polynomial, not on the ambient level
`n`.  The proof is the Schur--Szegő base case with a degree-`≤ 2` PF factor,
applied to the Jensen polynomial and then identified with the diagonal
operator. -/
theorem isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma))
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFiniteMultiplierSequence n gamma := by
  intro p hp hsplit
  have hschur : schurSzegoComp n (jensenPolynomial n gamma) p = 0 ∨
      (schurSzegoComp n (jensenPolynomial n gamma) p).Splits :=
    finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
      hjensen hjdeg hp hsplit
  have heq : schurSzegoComp n (jensenPolynomial n gamma) p =
      diagonalOperator gamma p :=
    schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le hp
  rwa [heq] at hschur

/-- PF-preservation version of
`isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two`. -/
theorem isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma))
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_finiteMultiplierSequence hgamma
    (isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
      hjensen hjdeg)

/-- Finite multiplier sequences are classified by the PF Jensen polynomial in
the special case where that Jensen polynomial has degree at most two. -/
theorem isFiniteMultiplierSequence_iff_jensenPolynomial_of_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFiniteMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  ⟨isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence hgamma,
    fun hjensen =>
      isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
        hjensen hjdeg⟩

/-- PF-preservation classification in the special case where the Jensen
polynomial has degree at most two. -/
theorem isFinitePFMultiplierSequence_iff_jensenPolynomial_of_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  ⟨isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence,
    fun hjensen =>
      isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
        hgamma hjensen hjdeg⟩

/-- Nonzero-core version of the arbitrary-level degree-`≤ 2` Schur--Szego
base case. -/
theorem finiteSchurSzegoCompositionNonzero_of_factors_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 2)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ 2) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_factors_natDegree_le_two
    hf hfdeg hpdeg hsplit

/-- Cubic-discriminant splitting route for the fixed-degree Schur--Szegő
composition with a degree-`≤ 3` factor.

Once the fixed-degree Schur--Szegő composition's cubic coefficient discriminant
`cubicDiscr (schurSzegoComp n f p)` is known to be nonnegative, the composition
is either zero or splits over `ℝ`.  The composition inherits the degree bound of
the degree-`≤ 3` factor `f` via `natDegree_schurSzegoComp_le_left`, so the
result is the degree-`≤ 3` cubic discriminant criterion applied to it. -/
theorem finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg
    {n : ℕ} {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  Or.inr (splits_of_natDegree_le_three_cubicDiscr_nonneg
    (le_trans (natDegree_schurSzegoComp_le_left n f p) hfdeg) hdisc)

/-- Nonzero-core version of the degree-`≤ 3` cubic-discriminant splitting route
for the fixed-degree Schur--Szegő composition. -/
theorem finiteSchurSzegoCompositionNonzero_of_natDegree_le_three_cubicDiscr_nonneg
    {n : ℕ} {f p : ℝ[X]} (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg
    hfdeg hdisc

/-- Degree-`≤ 3` PF-factor Schur--Szegő composition reduced to the cubic
discriminant inequality.

This packages the exact hypotheses of the Schur--Szegő PF-factor route while
leaving only `0 ≤ cubicDiscr (schurSzegoComp n f p)` as the remaining
degree-three obligation. -/
theorem finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (_hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (_hpdeg : p.natDegree ≤ n) (_hsplit : p.Splits)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg
    hfdeg hdisc

/-- The level-three normalized diagonal-operator form is exactly the
Schur--Szego composition cubic discriminant. -/
theorem cubicDiscr_diagonalOperator_normalized_three_eq_cubicDiscr_schurSzegoComp
    (f q : ℝ[X]) :
    cubicDiscr (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ)) q) =
      cubicDiscr (schurSzegoComp 3 f q) := by
  rw [← schurSzegoComp_eq_diagonalOperator 3 q f, schurSzegoComp_comm]

/-- Level-three normalized diagonal-operator cubic-discriminant base case for
a degree-`≤ 3` PF factor and a splitting factor. -/
def pfCubicDiscrDiagonalNonnegStatement : Prop :=
  ∀ {f q : ℝ[X]},
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    q.natDegree ≤ 3 →
    q.Splits →
    0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ)) q)

/-- The normalized diagonal base case is equivalent to the level-three
Schur--Szego cubic-discriminant base case. -/
theorem pfCubicDiscrDiagonalNonnegStatement_iff :
    pfCubicDiscrDiagonalNonnegStatement ↔
      ∀ {f q : ℝ[X]},
        IsPFPolynomial f →
        f.natDegree ≤ 3 →
        q.natDegree ≤ 3 →
        q.Splits →
        0 ≤ cubicDiscr (schurSzegoComp 3 f q) := by
  simp only [pfCubicDiscrDiagonalNonnegStatement,
    cubicDiscr_diagonalOperator_normalized_three_eq_cubicDiscr_schurSzegoComp]

/-- The classical fixed-degree Schur--Szego theorem discharges the isolated
level-three diagonal cubic-discriminant base case. -/
theorem pfCubicDiscrDiagonalNonnegStatement_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    pfCubicDiscrDiagonalNonnegStatement :=
  pfCubicDiscrDiagonalNonnegStatement_iff.mpr fun {f q} hf hfdeg hqdeg hsplit => by
    rcases hSZ hf hfdeg hqdeg hsplit with hzero | hs
    · simp [hzero, cubicDiscr]
    · exact cubicDiscr_nonneg_of_splits_natDegree_le_three
        ((natDegree_schurSzegoComp_le_left 3 f q).trans hfdeg) hs

/-- The isolated normalized diagonal base case discharges the level-three
degree-`≤ 3` PF-factor Schur--Szego composition route. -/
theorem finiteSchurSzegoComposition_of_pf_factor_three_of_base
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {f q : ℝ[X]} (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hqdeg : q.natDegree ≤ 3) (hsplit : q.Splits) :
    schurSzegoComp 3 f q = 0 ∨ (schurSzegoComp 3 f q).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hqdeg hsplit
    (pfCubicDiscrDiagonalNonnegStatement_iff.mp h hf hfdeg hqdeg hsplit)

/-- The isolated level-three diagonal base case proves the reflected
diagonal-operator discriminant input at every level `n ≥ 3`. -/
theorem cubicDiscr_reflect_diagonalOperator_nonneg_of_pfCubicDiscrDiagonalNonneg
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (reflect 3 ((derivative^[n - 3]) (reflect n p)))) :=
  h hf hfdeg
    (natDegree_reflect_iterate_derivative_reflect_le_three hn hpdeg)
    (reflect_iterate_derivative_reflect_splits_of_splits hn hpdeg hsplit)

/-- The isolated level-three diagonal base case proves high-level
cubic-discriminant nonnegativity for degree-`≤ 3` PF factors. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  cubicDiscr_schurSzegoComp_nonneg_of_reflect_diagonalOperator_three
    hn hfdeg hpdeg
    (cubicDiscr_reflect_diagonalOperator_nonneg_of_pfCubicDiscrDiagonalNonneg
      h hn hf hfdeg hpdeg hsplit)

/-- Low-level (`n < 3`) cubic-discriminant nonnegativity for a degree-`≤ 3`
PF factor with `f.natDegree ≤ n`. -/
private theorem cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_natDegree_lt_three
    {n : ℕ} (hn : n < 3) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) := by
  rcases finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
      hf (hfn.trans (Nat.lt_succ_iff.mp hn)) hpdeg hsplit with hzero | hs
  · simp [hzero, cubicDiscr]
  · exact cubicDiscr_nonneg_of_splits_natDegree_le_three
      ((natDegree_schurSzegoComp_le_left n f p).trans hfdeg) hs

/-- The isolated level-three diagonal base case proves the corrected all-level
cubic-discriminant route retaining `f.natDegree ≤ n`. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_leftNatDegree_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  (le_or_gt 3 n).elim
    (fun hn =>
      cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_of_pfDiagonalBase
        h hn hf hfdeg hpdeg hsplit)
    (fun hn =>
      cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_natDegree_lt_three
        hn hf hfdeg hfn hpdeg hsplit)

/-- Degree-`≤ 3` Schur--Szego composition reduced to the reflected-derivative
diagonal-operator discriminant. -/
theorem finiteSchurSzegoComposition_of_pf_factor_le_three_reflect_diagonalOperator
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hdisc : 0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (reflect 3 ((derivative^[n - 3]) (reflect n p))))) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit
    (cubicDiscr_schurSzegoComp_nonneg_of_reflect_diagonalOperator_three
      hn hfdeg hpdeg hdisc)

/-- The isolated level-three diagonal base case discharges the high-level
degree-`≤ 3` PF-factor Schur--Szego route. -/
theorem finiteSchurSzegoComposition_of_pf_factor_le_three_of_pfCubicDiscrDiagonalNonneg
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit
    (cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_of_pfDiagonalBase
      h hn hf hfdeg hpdeg hsplit)

/-- Corrected all-level degree-`≤ 3` PF-factor Schur--Szego route from the
isolated level-three diagonal base case, retaining `f.natDegree ≤ n`. -/
theorem
    finiteSchurSzegoComposition_of_pf_factor_le_three_leftNatDegree_of_pfCubicDiscrDiagonalNonneg
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit
    (cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_leftNatDegree_of_pfDiagonalBase
      h hf hfdeg hfn hpdeg hsplit)

/-- Degree-`≤ 3` PF-factor Schur--Szegő composition reduced to the
denominator-cleared cubic-discriminant numerator at levels `n ≥ 3`. -/
theorem finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hnum : 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit
    ((cubicDiscr_schurSzegoComp_nonneg_iff_of_three_le hn f p).2 hnum)

/-- Corrected all-level denominator-cleared numerator route for cubic
discriminant nonnegativity, retaining the original fixed-degree Schur--Szegő
hypothesis `f.natDegree ≤ n`.

For `3 ≤ n`, this is exactly the denominator-cleared numerator equivalence.
For `n < 3`, the left-degree hypothesis makes `f` a degree-`≤ 2` PF factor,
so the checked quadratic Schur--Szegő base case supplies splitting, hence
cubic-discriminant nonnegativity in degree at most three. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_leftNatDegree_num_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  (le_or_gt 3 n).elim
    (fun hn =>
      (cubicDiscr_schurSzegoComp_nonneg_iff_of_three_le hn f p).2
        (hnum hn))
    (fun hn =>
      cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_natDegree_lt_three
        hn hf hfdeg hfn hpdeg hsplit)

/-- Corrected all-level denominator-cleared numerator route for degree-`≤ 3`
PF factors, retaining the original fixed-degree Schur--Szegő hypothesis
`f.natDegree ≤ n`.

For `3 ≤ n`, this is the denominator-cleared cubic-discriminant route.  For
`n < 3`, the hypothesis `f.natDegree ≤ n` makes `f` a degree-`≤ 2` PF factor,
so the checked quadratic Schur--Szegő base case applies directly. -/
theorem finiteSchurSzegoComposition_of_pf_factor_le_three_leftNatDegree_num_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit
    (cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_leftNatDegree_num_nonneg
      hf hfdeg hfn hpdeg hsplit hnum)

/-- Nonzero-core version of the degree-`≤ 3` PF-factor Schur--Szegő reduction
to the cubic discriminant inequality. -/
theorem finiteSchurSzegoCompositionNonzero_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit hdisc

/-- Nonzero-core version of the high-level diagonal-base route for degree-`≤ 3`
PF factors. -/
theorem finiteSchurSzegoCompositionNonzero_of_pf_factor_le_three_of_pfCubicDiscrDiagonalNonneg
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_le_three_of_pfCubicDiscrDiagonalNonneg
    h hn hf hfdeg hpdeg hsplit

/-- Nonzero-core version of the corrected all-level diagonal-base route for
degree-`≤ 3` PF factors, retaining `f.natDegree ≤ n`. -/
theorem
    finiteSchurSzegoCompositionNonzero_of_pf_factor_le_three_leftNatDegree_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_le_three_leftNatDegree_of_pfCubicDiscrDiagonalNonneg
    h hf hfdeg hfn hpdeg hsplit

/-- Nonzero-core version of the degree-`≤ 3` PF-factor Schur--Szegő reduction
to the denominator-cleared cubic-discriminant numerator at levels `n ≥ 3`. -/
theorem finiteSchurSzegoCompositionNonzero_of_pf_factor_le_three_cubicDiscrNumerator_nonneg
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hnum : 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
    hn hf hfdeg hpdeg hsplit hnum

/-- Nonzero-core version of the corrected all-level denominator-cleared
numerator route for degree-`≤ 3` PF factors, retaining the original
fixed-degree Schur--Szegő hypothesis `f.natDegree ≤ n`. -/
theorem finiteSchurSzegoCompositionNonzero_of_pf_factor_le_three_leftNatDegree_num_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_le_three_leftNatDegree_num_nonneg
    hf hfdeg hfn hpdeg hsplit hnum

/-- The full finite Schur--Szegő theorem implies the finite Pólya--Schur
theorem. -/
theorem finitePolyaSchur_nonneg_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    finitePolyaSchurNonnegStatement :=
  finitePolyaSchur_nonneg_of_backward
    (finitePolyaSchurNonnegBackward_of_schurSzego hSZ)

/-- Fixed-degree Schur--Szegő composition and finite Pólya--Schur are
equivalent classical inputs in the nonnegative-coefficient convention used
here. -/
theorem finiteSchurSzegoCompositionStatement_iff_finitePolyaSchur :
    finiteSchurSzegoCompositionStatement ↔ finitePolyaSchurNonnegStatement :=
  ⟨finitePolyaSchur_nonneg_of_schurSzego,
    finiteSchurSzegoComposition_of_finitePolyaSchur⟩

/-- The finite Pólya--Schur theorem implies the nonzero core of fixed-degree
Schur--Szegő composition. -/
theorem finiteSchurSzegoCompositionNonzero_of_finitePolyaSchur
    (hFPS : finitePolyaSchurNonnegStatement) :
    finiteSchurSzegoCompositionNonzeroStatement :=
  finiteSchurSzegoCompositionNonzero_of_full
    (finiteSchurSzegoComposition_of_finitePolyaSchur hFPS)

/-- The nonzero core of fixed-degree Schur--Szegő composition and finite
Pólya--Schur are equivalent classical inputs in the local convention. -/
theorem finiteSchurSzegoCompositionNonzeroStatement_iff_finitePolyaSchur :
    finiteSchurSzegoCompositionNonzeroStatement ↔ finitePolyaSchurNonnegStatement :=
  ⟨finitePolyaSchur_nonneg_of_schurSzegoNonzero,
    finiteSchurSzegoCompositionNonzero_of_finitePolyaSchur⟩

/-- The nonzero Schur--Szegő core is equivalent to the hard backward direction
of finite Pólya--Schur. -/
theorem finiteSchurSzegoCompositionNonzeroStatement_iff_finitePolyaSchurBackward :
    finiteSchurSzegoCompositionNonzeroStatement ↔
      finitePolyaSchurNonnegBackwardStatement :=
  ⟨finitePolyaSchurNonnegBackward_of_schurSzegoNonzero,
    fun hBack =>
      finiteSchurSzegoCompositionNonzero_of_finitePolyaSchur
        (finitePolyaSchur_nonneg_of_backward hBack)⟩
end RealRooted
