import RealRooted.Hadamard.Newton

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Cubic Schur--Szego reductions

Degree-three PF-factor reductions of the Schur--Szegő composition to cubic
discriminant inequalities.
-/

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

/-- The level-three normalized diagonal-operator form is exactly the
Schur--Szego composition cubic discriminant. -/
theorem cubicDiscr_diagonalOperator_normalized_three_eq_cubicDiscr_schurSzegoComp
    (f q : ℝ[X]) :
    cubicDiscr (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ)) q) =
      cubicDiscr (schurSzegoComp 3 f q) := by
  rw [← schurSzegoComp_eq_diagonalOperator 3 q f, schurSzegoComp_comm]

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

/-- Schur--Szegő composition with a degree-`≤ 3` factor reduced to the
denominator-cleared cubic-discriminant numerator at levels `n ≥ 3`. -/
theorem finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3)
    (hnum : 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg hfdeg
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
  finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg hfdeg
    (cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_leftNatDegree_num_nonneg
      hf hfdeg hfn hpdeg hsplit hnum)

end RealRooted
