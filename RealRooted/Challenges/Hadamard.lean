import RealRooted.CubicDiscriminant
import RealRooted.Hadamard

/-!
# Hadamard and Hurwitz-matrix challenge entry point

This module exposes the Garloff--Wagner, Schur--Szego, finite Polya--Schur,
and Hurwitz-matrix targets as stable names for theorem-proving sessions.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace Challenges
namespace Hadamard

/-! ## Schur--Szego and finite Polya--Schur targets -/

/-- Challenge-facing target for the fixed-degree Schur--Szego theorem. -/
abbrev finiteSchurSzegoTarget : Prop :=
  finiteSchurSzegoCompositionStatement

/-- Challenge-facing nonzero core of the fixed-degree Schur--Szego theorem. -/
abbrev finiteSchurSzegoNonzeroTarget : Prop :=
  finiteSchurSzegoCompositionNonzeroStatement

/-- Challenge-facing target for the backward finite Polya--Schur theorem. -/
abbrev finitePolyaSchurBackwardTarget : Prop :=
  finitePolyaSchurNonnegBackwardStatement

/-- Challenge-facing target for the finite Polya--Schur theorem. -/
abbrev finitePolyaSchurTarget : Prop :=
  finitePolyaSchurNonnegStatement

/-- The full fixed-degree Schur--Szego target is equivalent to its nonzero
core; zero input cases are bookkeeping. -/
theorem finiteSchurSzegoTarget_iff_nonzero :
    finiteSchurSzegoTarget ↔ finiteSchurSzegoNonzeroTarget :=
  finiteSchurSzegoCompositionStatement_iff_nonzero

/-- Challenge-facing reduction from the nonzero Schur--Szego core to the full
fixed-degree Schur--Szego target. -/
theorem finiteSchurSzegoTarget_of_nonzero
    (h : finiteSchurSzegoNonzeroTarget) :
    finiteSchurSzegoTarget :=
  finiteSchurSzegoComposition_of_nonzero h

/-- Challenge-facing reduction from the full fixed-degree Schur--Szego target
to its nonzero core; the zero input cases are pure bookkeeping. -/
theorem finiteSchurSzegoNonzeroTarget_of_finiteSchurSzego
    (h : finiteSchurSzegoTarget) :
    finiteSchurSzegoNonzeroTarget :=
  finiteSchurSzegoCompositionNonzero_of_full h

/-- Challenge-facing reduction from the nonzero Schur--Szego core to the
backward finite Polya--Schur target. -/
theorem finitePolyaSchurBackwardTarget_of_schurSzegoNonzero
    (h : finiteSchurSzegoNonzeroTarget) :
    finitePolyaSchurBackwardTarget :=
  finitePolyaSchurNonnegBackward_of_schurSzegoNonzero h

/-- Challenge-facing reduction from the nonzero Schur--Szego core to the full
finite Polya--Schur target. -/
theorem finitePolyaSchurTarget_of_schurSzegoNonzero
    (h : finiteSchurSzegoNonzeroTarget) :
    finitePolyaSchurTarget :=
  finitePolyaSchur_nonneg_of_schurSzegoNonzero h

/-- Challenge-facing reduction from the finite Pólya--Schur theorem to the
full fixed-degree Schur--Szegő target. -/
theorem finiteSchurSzegoTarget_of_finitePolyaSchur
    (h : finitePolyaSchurTarget) :
    finiteSchurSzegoTarget :=
  finiteSchurSzegoComposition_of_finitePolyaSchur h

/-- Challenge-facing reduction from finite Pólya--Schur to the nonzero
fixed-degree Schur--Szegő core. -/
theorem finiteSchurSzegoNonzeroTarget_of_finitePolyaSchur
    (h : finitePolyaSchurTarget) :
    finiteSchurSzegoNonzeroTarget :=
  finiteSchurSzegoCompositionNonzero_of_finitePolyaSchur h

/-- Challenge-facing reduction from the backward finite Pólya--Schur direction
to the nonzero fixed-degree Schur--Szego core. -/
theorem finiteSchurSzegoNonzeroTarget_of_backward
    (h : finitePolyaSchurBackwardTarget) :
    finiteSchurSzegoNonzeroTarget :=
  finiteSchurSzegoCompositionNonzeroStatement_iff_finitePolyaSchurBackward.2 h

/-- Challenge-facing reduction from the backward finite Pólya--Schur direction
to the full fixed-degree Schur--Szego target. -/
theorem finiteSchurSzegoTarget_of_backward
    (h : finitePolyaSchurBackwardTarget) :
    finiteSchurSzegoTarget :=
  finiteSchurSzegoTarget_of_nonzero
    (finiteSchurSzegoNonzeroTarget_of_backward h)

/-- Challenge-facing equivalence between fixed-degree Schur--Szegő and finite
Pólya--Schur in the local nonnegative-coefficient convention. -/
theorem finiteSchurSzegoTarget_iff_finitePolyaSchurTarget :
    finiteSchurSzegoTarget ↔ finitePolyaSchurTarget :=
  finiteSchurSzegoCompositionStatement_iff_finitePolyaSchur

/-- Challenge-facing equivalence between the nonzero Schur--Szegő core and
finite Pólya--Schur. -/
theorem finiteSchurSzegoNonzeroTarget_iff_finitePolyaSchurTarget :
    finiteSchurSzegoNonzeroTarget ↔ finitePolyaSchurTarget :=
  finiteSchurSzegoCompositionNonzeroStatement_iff_finitePolyaSchur

/-- Challenge-facing equivalence between the nonzero Schur--Szegő core and
the backward finite Pólya--Schur target. -/
theorem finiteSchurSzegoNonzeroTarget_iff_finitePolyaSchurBackwardTarget :
    finiteSchurSzegoNonzeroTarget ↔ finitePolyaSchurBackwardTarget :=
  finiteSchurSzegoCompositionNonzeroStatement_iff_finitePolyaSchurBackward

/-- Challenge-facing equivalence between the full finite Pólya--Schur theorem
and its hard backward direction. -/
theorem finitePolyaSchurTarget_iff_backwardTarget :
    finitePolyaSchurTarget ↔ finitePolyaSchurBackwardTarget :=
  finitePolyaSchurNonnegStatement_iff_backward

/-- Challenge-facing reduction from the backward finite Pólya--Schur direction
to the full finite Pólya--Schur theorem. -/
theorem finitePolyaSchurTarget_of_backward
    (h : finitePolyaSchurBackwardTarget) :
    finitePolyaSchurTarget :=
  finitePolyaSchur_nonneg_of_backward h

/-- Challenge-facing extraction of the backward finite Pólya--Schur direction
from the full finite Pólya--Schur theorem. -/
theorem finitePolyaSchurBackwardTarget_of_target
    (h : finitePolyaSchurTarget) :
    finitePolyaSchurBackwardTarget :=
  finitePolyaSchur_backward_of_nonneg h

/-- Challenge-facing finite multiplier-sequence criterion from the full finite
Pólya--Schur theorem. -/
theorem finiteMultiplierSequencePair_of_jensenPolynomial
    (hFPS : finitePolyaSchurTarget)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma :=
  isFiniteMultiplierSequence_of_jensenPolynomial hFPS hgamma hjensen

/-- Challenge-facing finite multiplier-sequence criterion from the backward
finite Pólya--Schur direction. -/
theorem finiteMultiplierSequencePair_of_jensenPolynomial_of_backward
    (hBack : finitePolyaSchurBackwardTarget)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma :=
  isFiniteMultiplierSequence_of_jensenPolynomial_of_backward hBack hgamma hjensen

/-- Challenge-facing PF multiplier-sequence criterion from the full finite
Pólya--Schur theorem. -/
theorem finitePFMultiplierSequencePair_of_jensenPolynomial
    (hFPS : finitePolyaSchurTarget)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_jensenPolynomial hFPS hgamma hjensen

/-- Challenge-facing PF multiplier-sequence criterion from the backward finite
Pólya--Schur direction. -/
theorem finitePFMultiplierSequencePair_of_jensenPolynomial_of_backward
    (hBack : finitePolyaSchurBackwardTarget)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_jensenPolynomial_of_backward
    hBack hgamma hjensen

/-- Challenge-facing PF-preservation form of finite Pólya--Schur. -/
theorem finitePFMultiplierSequencePair_iff_jensenPolynomial
    (hFPS : finitePolyaSchurTarget)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  isFinitePFMultiplierSequence_iff_jensenPolynomial hFPS hgamma

/-- Challenge-facing PF-preservation form of the backward finite Pólya--Schur
direction. -/
theorem finitePFMultiplierSequencePair_iff_jensenPolynomial_of_backward
    (hBack : finitePolyaSchurBackwardTarget)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  isFinitePFMultiplierSequence_iff_jensenPolynomial_of_backward hBack hgamma

/-- Challenge-facing pointwise form of the fixed-degree Schur--Szegő target. -/
theorem finiteSchurSzegoPair_of_finiteSchurSzegoTarget
    (hSZ : finiteSchurSzegoTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfn : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  hSZ hf hfn hpdeg hsplit

/-- Challenge-facing pointwise form of the nonzero fixed-degree Schur--Szegő
core. -/
theorem finiteSchurSzegoNonzeroPair_of_finiteSchurSzegoNonzeroTarget
    (hSZ : finiteSchurSzegoNonzeroTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfn : f.natDegree ≤ n)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  hSZ hf hf0 hfn hp0 hpdeg hsplit

/-- Challenge-facing pointwise Schur--Szegő pair route from finite
Pólya--Schur. -/
theorem finiteSchurSzegoPair_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfn : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_finiteSchurSzegoTarget
    (finiteSchurSzegoTarget_of_finitePolyaSchur hFPS) hf hfn hpdeg hsplit

/-- Challenge-facing pointwise nonzero Schur--Szegő pair route from finite
Pólya--Schur. -/
theorem finiteSchurSzegoNonzeroPair_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfn : f.natDegree ≤ n)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoNonzeroPair_of_finiteSchurSzegoNonzeroTarget
    (finiteSchurSzegoNonzeroTarget_of_finitePolyaSchur hFPS)
    hf hf0 hfn hp0 hpdeg hsplit

/-- Challenge-facing pointwise Schur--Szegő pair route from the backward finite
Pólya--Schur direction. -/
theorem finiteSchurSzegoPair_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfn : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_finitePolyaSchur
    (finitePolyaSchurTarget_of_backward hBack) hf hfn hpdeg hsplit

/-- Challenge-facing pointwise nonzero Schur--Szegő pair route from the
backward finite Pólya--Schur direction. -/
theorem finiteSchurSzegoNonzeroPair_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfn : f.natDegree ≤ n)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoNonzeroPair_of_finitePolyaSchur
    (finitePolyaSchurTarget_of_backward hBack)
    hf hf0 hfn hp0 hpdeg hsplit

/-- High-level PF-factor pointwise Schur--Szegő route from the fixed-degree
Schur--Szegő target. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_finiteSchurSzegoTarget
    (hSZ : finiteSchurSzegoTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  hSZ hf (hfdeg.trans hn) hpdeg hsplit

/-- High-level PF-factor pointwise Schur--Szegő route from finite
Pólya--Schur. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_finitePolyaSchur
    hFPS hf (hfdeg.trans hn) hpdeg hsplit

/-- High-level PF-factor pointwise Schur--Szegő route from the backward finite
Pólya--Schur direction. -/
theorem
    finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_finitePolyaSchurBackward
    hBack hf (hfdeg.trans hn) hpdeg hsplit

/-- High-level PF-factor pointwise Schur--Szegő route from the nonzero
fixed-degree Schur--Szegő core. -/
theorem
    finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_finiteSchurSzegoNonzeroTarget
    (hSZ : finiteSchurSzegoNonzeroTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoTarget_of_nonzero hSZ hf (hfdeg.trans hn) hpdeg hsplit

/-- Nonzero-core high-level PF-factor pointwise Schur--Szegő route from the
nonzero fixed-degree Schur--Szegő core. -/
theorem
    finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_finiteSchurSzegoNonzeroTarget
    (hSZ : finiteSchurSzegoNonzeroTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  hSZ hf hf0 (hfdeg.trans hn) hp0 hpdeg hsplit

/-- Nonzero-core high-level PF-factor pointwise Schur--Szegő route from the
full fixed-degree Schur--Szegő target. -/
theorem
    finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_finiteSchurSzegoTarget
    (hSZ : finiteSchurSzegoTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_finiteSchurSzegoNonzeroTarget
    (finiteSchurSzegoNonzeroTarget_of_finiteSchurSzego hSZ)
    hn hf hf0 hfdeg hp0 hpdeg hsplit

/-- Nonzero-core high-level PF-factor pointwise Schur--Szegő route from finite
Pólya--Schur. -/
theorem finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoNonzeroPair_of_finitePolyaSchur
    hFPS hf hf0 (hfdeg.trans hn) hp0 hpdeg hsplit

/-- Nonzero-core high-level PF-factor pointwise Schur--Szegő route from the
backward finite Pólya--Schur direction. -/
theorem
    finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoNonzeroPair_of_finitePolyaSchurBackward
    hBack hf hf0 (hfdeg.trans hn) hp0 hpdeg hsplit

/-- Challenge-facing checked low-degree Schur--Szegő base case, through
degree `2`. -/
theorem finiteSchurSzegoPair_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_natDegree_le_two hn hf hfdeg hpdeg hsplit

/-- Challenge-facing checked low-degree nonzero Schur--Szegő base case, through
degree `2`. -/
theorem finiteSchurSzegoNonzeroPair_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ n)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoCompositionNonzero_of_natDegree_le_two
    hn hf hf0 hfdeg hp0 hpdeg hsplit

/-- Challenge-facing checked low-degree Schur--Szegő base case for arbitrary
level when both factors have degree at most `2`. -/
theorem finiteSchurSzegoPair_of_factors_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ 2) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_factors_natDegree_le_two
    hf hfdeg hpdeg hsplit

/-- Challenge-facing checked Schur--Szegő composition with a degree-`≤ 2` PF
factor and an arbitrary-degree splitting factor.  This strictly extends
`finiteSchurSzegoPair_of_factors_natDegree_le_two`: the splitting factor `p`
may have any degree up to the level `n`. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
    hf hfdeg hpdeg hsplit

/-- Challenge-facing checked low-degree nonzero Schur--Szegő base case for
arbitrary level when both factors have degree at most `2`. -/
theorem finiteSchurSzegoNonzeroPair_of_factors_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 2)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ 2) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoCompositionNonzero_of_factors_natDegree_le_two
    hf hf0 hfdeg hp0 hpdeg hsplit

/-- Challenge-facing nonzero Schur--Szegő base case with a degree-`≤ 2` PF
factor and an arbitrary-degree splitting factor. -/
theorem finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 2)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoCompositionNonzero_of_pf_factor_natDegree_le_two
    hf hf0 hfdeg hp0 hpdeg hsplit

/-- Challenge-facing degree-`≤ 3` PF-factor Schur--Szegő route, assuming the
remaining cubic discriminant inequality for the composition. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit hdisc

/-- Challenge-facing nonzero degree-`≤ 3` PF-factor Schur--Szegő route,
assuming the remaining cubic discriminant inequality for the composition. -/
theorem finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p)) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoCompositionNonzero_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hf0 hfdeg hp0 hpdeg hsplit hdisc

/-- Challenge-facing checked low-degree backward finite Pólya--Schur base case,
through degree `2`. -/
theorem finitePolyaSchurBackwardPair_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma :=
  finitePolyaSchurNonnegBackward_of_natDegree_le_two hn hgamma hjensen

/-- Challenge-facing checked low-degree finite Pólya--Schur classification,
through degree `2`. -/
theorem finitePolyaSchurPair_iff_jensenPolynomial_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFiniteMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  finitePolyaSchur_nonneg_of_natDegree_le_two hn hgamma

/-- Challenge-facing checked low-degree PF multiplier-sequence classification,
through degree `2`. -/
theorem finitePFMultiplierSequencePair_iff_jensenPolynomial_of_natDegree_le_two
    {n : ℕ} (hn : n ≤ 2) {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  isFinitePFMultiplierSequence_iff_jensenPolynomial_natDegree_le_two hn hgamma

/-- Challenge-facing finite multiplier-sequence criterion when the Jensen
polynomial itself has degree at most `2`. -/
theorem finiteMultiplierSequencePair_of_jensenPolynomial_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma))
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFiniteMultiplierSequence n gamma :=
  isFiniteMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
    hjensen hjdeg

/-- Challenge-facing PF multiplier-sequence criterion when the Jensen
polynomial itself has degree at most `2`. -/
theorem finitePFMultiplierSequencePair_of_jensenPolynomial_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma))
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_isPF_jensenPolynomial_self_natDegree_le_two
    hgamma hjensen hjdeg

/-- Challenge-facing finite Pólya--Schur classification when the Jensen
polynomial itself has degree at most `2`. -/
theorem finitePolyaSchurPair_iff_jensenPolynomial_of_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFiniteMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  isFiniteMultiplierSequence_iff_jensenPolynomial_of_self_natDegree_le_two
    hgamma hjdeg

/-- Challenge-facing PF-preservation classification when the Jensen polynomial
itself has degree at most `2`. -/
theorem finitePFMultiplierSequencePair_iff_jensenPolynomial_of_self_natDegree_le_two
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjdeg : (jensenPolynomial n gamma).natDegree ≤ 2) :
    IsFinitePFMultiplierSequence n gamma ↔
      IsPFPolynomial (jensenPolynomial n gamma) :=
  isFinitePFMultiplierSequence_iff_jensenPolynomial_of_self_natDegree_le_two
    hgamma hjdeg

/-- Challenge-facing cubic discriminant splitting target. -/
abbrev cubicDiscriminantSplittingTarget : Prop :=
  ∀ {p : ℝ[X]}, p.natDegree = 3 → 0 ≤ cubicDiscr p → p.Splits

/-- The checked cubic discriminant criterion proves the challenge target. -/
theorem cubicDiscriminantSplittingTarget_proved :
    cubicDiscriminantSplittingTarget :=
  fun hdeg hdisc => splits_of_cubicDiscr_nonneg hdeg hdisc

/-- Challenge-facing cubic discriminant splitting target through degree three. -/
abbrev cubicDiscriminantNatDegreeLeThreeTarget : Prop :=
  ∀ {p : ℝ[X]}, p.natDegree ≤ 3 → 0 ≤ cubicDiscr p → p.Splits

/-- The checked cubic discriminant criterion proves the degree-`≤ 3`
challenge target. -/
theorem cubicDiscriminantNatDegreeLeThreeTarget_proved :
    cubicDiscriminantNatDegreeLeThreeTarget :=
  fun hdeg hdisc => splits_of_natDegree_le_three_cubicDiscr_nonneg hdeg hdisc

/-- Challenge-facing equivalence form of the checked cubic discriminant
criterion through degree three. -/
theorem cubicDiscriminantNonneg_iff_splits_of_natDegree_le_three
    {p : ℝ[X]} (hdeg : p.natDegree ≤ 3) :
    0 ≤ cubicDiscr p ↔ p.Splits :=
  RealRooted.cubicDiscr_nonneg_iff_splits_of_natDegree_le_three hdeg

/-- Challenge-facing target for the exact-degree-three diagonal-operator
output, once its cubic discriminant is known to be nonnegative. -/
abbrev diagonalOperatorCubicDiscriminantTarget : Prop :=
  ∀ {gamma : ℕ → ℝ} {p : ℝ[X]},
    (diagonalOperator gamma p).natDegree = 3 →
    0 ≤ cubicDiscr (diagonalOperator gamma p) →
    (diagonalOperator gamma p).Splits

/-- The cubic discriminant criterion proves the exact-degree-three diagonal
operator target. -/
theorem diagonalOperatorCubicDiscriminantTarget_proved :
    diagonalOperatorCubicDiscriminantTarget :=
  fun hdeg hdisc =>
    diagonalOperator_splits_of_natDegree_three_cubicDiscr_nonneg hdeg hdisc

/-- Challenge-facing target for degree-`≤ 3` diagonal-operator outputs, once
their cubic discriminant is known to be nonnegative. -/
abbrev diagonalOperatorCubicDiscriminantLeThreeTarget : Prop :=
  ∀ {gamma : ℕ → ℝ} {p : ℝ[X]},
    (diagonalOperator gamma p).natDegree ≤ 3 →
    0 ≤ cubicDiscr (diagonalOperator gamma p) →
    (diagonalOperator gamma p).Splits

/-- The degree-`≤ 3` cubic discriminant criterion proves the diagonal-operator
target. -/
theorem diagonalOperatorCubicDiscriminantLeThreeTarget_proved :
    diagonalOperatorCubicDiscriminantLeThreeTarget :=
  fun hdeg hdisc =>
    diagonalOperator_splits_of_natDegree_le_three_cubicDiscr_nonneg hdeg hdisc

/-- Challenge-facing cubic-discriminant splitting target for the fixed-degree
Schur--Szegő composition with a degree-`≤ 3` factor: once the composition's
cubic coefficient discriminant is nonnegative, it is either zero or splits. -/
abbrev schurSzegoCompCubicDiscriminantLeThreeTarget : Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]}, f.natDegree ≤ 3 →
    0 ≤ cubicDiscr (schurSzegoComp n f p) →
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits

/-- The checked degree-`≤ 3` cubic-discriminant route for the Schur--Szegő
composition proves the challenge target. -/
theorem schurSzegoCompCubicDiscriminantLeThreeTarget_proved :
    schurSzegoCompCubicDiscriminantLeThreeTarget :=
  fun hfdeg hdisc =>
    finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg
      hfdeg hdisc

/-- Challenge-facing target for the missing degree-`≤ 3` PF-factor cubic
discriminant inequality in the Schur--Szegő route. -/
abbrev schurSzegoCompPFFactorCubicDiscriminantNonnegTarget : Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    p.natDegree ≤ n →
    p.Splits →
    0 ≤ cubicDiscr (schurSzegoComp n f p)

/-- Challenge-facing high-level part (`n ≥ 3`) of the degree-`≤ 3` PF-factor
Schur--Szegő cubic-discriminant target. -/
abbrev schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget : Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    3 ≤ n →
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    p.natDegree ≤ n →
    p.Splits →
    0 ≤ cubicDiscr (schurSzegoComp n f p)

/-- Challenge-facing low-level part (`n < 3`) of the degree-`≤ 3` PF-factor
Schur--Szegő cubic-discriminant target. -/
abbrev schurSzegoCompPFFactorLowLevelCubicDiscriminantNonnegTarget : Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    n < 3 →
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    p.natDegree ≤ n →
    p.Splits →
    0 ≤ cubicDiscr (schurSzegoComp n f p)

/-- Concrete low-level counterexample: at level `2`, the Schur--Szegő
composition of `(X + 1)^3` with `(X + 1)^2` has negative cubic coefficient
discriminant. -/
theorem cubicDiscr_schurSzegoComp_X_add_one_cube_square_level_two :
    cubicDiscr
      (schurSzegoComp 2 ((X + 1 : ℝ[X]) ^ 3) ((X + 1 : ℝ[X]) ^ 2)) = -27 := by
  norm_num [schurSzegoComp, cubicDiscr, Finset.sum_range_succ,
    coeff_X_add_one_pow, Polynomial.coeff_one, Polynomial.coeff_monomial]

/-- The low-level (`n < 3`) cubic-discriminant nonnegativity target is false
as stated. -/
theorem not_schurSzegoCompPFFactorLowLevelCubicDiscriminantNonnegTarget :
    ¬ schurSzegoCompPFFactorLowLevelCubicDiscriminantNonnegTarget := by
  intro h
  have hdisc : 0 ≤ cubicDiscr
      (schurSzegoComp 2 ((X + 1 : ℝ[X]) ^ 3) ((X + 1 : ℝ[X]) ^ 2)) :=
    h (by norm_num) (by simpa using isPFPolynomial_X_add_one.pow 3)
      (natDegree_X_add_one_pow_le 3) (natDegree_X_add_one_pow_le 2)
      (splits_X_add_one_pow 2)
  norm_num [cubicDiscr_schurSzegoComp_X_add_one_cube_square_level_two] at hdisc

/-- Consequently, the unrestricted degree-`≤ 3` PF-factor cubic-discriminant
nonnegativity target is also false as stated. -/
theorem not_schurSzegoCompPFFactorCubicDiscriminantNonnegTarget :
    ¬ schurSzegoCompPFFactorCubicDiscriminantNonnegTarget :=
  fun h =>
    not_schurSzegoCompPFFactorLowLevelCubicDiscriminantNonnegTarget
      (fun _hn => h)

/-- Corrected degree-`≤ 3` PF-factor cubic-discriminant target retaining the
original Schur--Szegő ambient-degree hypothesis on the left factor. -/
abbrev schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :
    Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    f.natDegree ≤ n →
    p.natDegree ≤ n →
    p.Splits →
    0 ≤ cubicDiscr (schurSzegoComp n f p)

/-- Corrected low-level part (`n < 3`) of the degree-`≤ 3` PF-factor
cubic-discriminant target, retaining the left ambient-degree hypothesis. -/
abbrev schurSzegoCompPFFactorLowLevelCubicDiscriminantNonnegOfLeftNatDegreeTarget :
    Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    n < 3 →
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    f.natDegree ≤ n →
    p.natDegree ≤ n →
    p.Splits →
    0 ≤ cubicDiscr (schurSzegoComp n f p)

/-- The corrected low-level (`n < 3`) cubic-discriminant target follows from
the checked degree-`≤ 2` Schur--Szegő base case. -/
theorem schurSzegoCompPFFactorLowLevelCubicDiscriminantNonnegOfLeftNatDegreeTarget_proved :
    schurSzegoCompPFFactorLowLevelCubicDiscriminantNonnegOfLeftNatDegreeTarget := by
  intro n f p hn hf hfdeg hfn hpdeg hsplit
  have hn2 : n ≤ 2 := Nat.lt_succ_iff.mp hn
  rcases finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
      hf (hfn.trans hn2) hpdeg hsplit with hzero | hs
  · simp [hzero, cubicDiscr]
  · exact cubicDiscr_nonneg_of_splits_natDegree_le_three
      ((natDegree_schurSzegoComp_le_left n f p).trans hfdeg) hs

/-- Challenge-facing denominator-cleared numerator target for the
degree-`≤ 3` PF-factor Schur--Szegő cubic-discriminant route at levels
`n ≥ 3`. -/
abbrev schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget : Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    3 ≤ n →
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    p.natDegree ≤ n →
    p.Splits →
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p

/-- Challenge-facing normalized Jensen-product form of the missing
degree-`≤ 3` PF-factor cubic discriminant inequality.

For a degree-`≤ 3` left factor `f`, the fixed-degree Schur--Szegő composition
is the degree-three Jensen polynomial attached to the coefficientwise product
of the binomial-normalized coefficient sequences of `p` and `f`. -/
abbrev schurSzegoCompPFFactorJensenProductCubicDiscriminantTarget : Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    p.natDegree ≤ n →
    p.Splits →
    0 ≤ cubicDiscr
      (jensenPolynomial 3 (fun k =>
        (p.coeff k / (Nat.choose n k : ℝ)) *
          (f.coeff k / (Nat.choose 3 k : ℝ))))

/-- Challenge-facing diagonal-operator form of the missing degree-`≤ 3`
PF-factor cubic discriminant inequality.

This packages the normalized Jensen-product target as preservation of cubic
discriminant nonnegativity by the diagonal sequence supplied by the
degree-`≤ 3` PF factor. -/
abbrev schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantTarget : Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    p.natDegree ≤ n →
    p.Splits →
    0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ))))

/-- Corrected normalized Jensen-product form of the degree-`≤ 3` PF-factor
cubic discriminant target, retaining the left ambient-degree hypothesis. -/
abbrev
    schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget :
    Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    f.natDegree ≤ n →
    p.natDegree ≤ n →
    p.Splits →
    0 ≤ cubicDiscr
      (jensenPolynomial 3 (fun k =>
        (p.coeff k / (Nat.choose n k : ℝ)) *
          (f.coeff k / (Nat.choose 3 k : ℝ))))

/-- Corrected diagonal-operator form of the degree-`≤ 3` PF-factor cubic
discriminant target, retaining the left ambient-degree hypothesis. -/
abbrev
    schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget :
    Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    f.natDegree ≤ n →
    p.natDegree ≤ n →
    p.Splits →
    0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ))))

/-- Challenge-facing high-level normalized diagonal-operator form of the
degree-`≤ 3` PF-factor Schur--Szegő cubic-discriminant route. -/
abbrev
    schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget :
    Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    3 ≤ n →
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    p.natDegree ≤ n →
    p.Splits →
    0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ))))

/-- Challenge-facing reflected-derivative diagonal-operator form of the
high-level (`n ≥ 3`) degree-`≤ 3` PF-factor cubic discriminant inequality. -/
abbrev schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget : Prop :=
  ∀ {n : ℕ} {f p : ℝ[X]},
    3 ≤ n →
    IsPFPolynomial f →
    f.natDegree ≤ 3 →
    p.natDegree ≤ n →
    p.Splits →
    0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (reflect 3 ((derivative^[n - 3]) (reflect n p))))

/-- Challenge-facing normalized Jensen-polynomial form of the cubic
Schur--Szegő composition with a degree-`≤ 3` left factor. -/
theorem schurSzegoComp_eq_jensenPolynomialThree_normalized
    {n : ℕ} {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3) :
    schurSzegoComp n f p =
      jensenPolynomial 3 (fun k =>
        (p.coeff k / (Nat.choose n k : ℝ)) *
          (f.coeff k / (Nat.choose 3 k : ℝ))) :=
  RealRooted.schurSzegoComp_eq_jensenPolynomial_three_normalized hfdeg

/-- Challenge-facing normalized diagonal-operator form of the Schur--Szegő
composition with a degree-`≤ 3` left factor. -/
theorem schurSzegoComp_eq_diagonalOperator_jensenPolynomialThree_normalized
    {n : ℕ} {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3) :
    schurSzegoComp n f p =
      diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ))) :=
  RealRooted.schurSzegoComp_eq_diagonalOperator_jensenPolynomial_three_normalized
    hfdeg

/-- Challenge-facing normalized Jensen-polynomial form of the cubic
discriminant of a fixed-degree Schur--Szegő composition with a degree-`≤ 3`
left factor. -/
theorem cubicDiscr_schurSzegoComp_eq_jensenPolynomialThree_normalized
    {n : ℕ} {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3) :
    cubicDiscr (schurSzegoComp n f p) =
      cubicDiscr
        (jensenPolynomial 3 (fun k =>
          (p.coeff k / (Nat.choose n k : ℝ)) *
            (f.coeff k / (Nat.choose 3 k : ℝ)))) :=
  RealRooted.cubicDiscr_schurSzegoComp_eq_jensenPolynomial_three_normalized hfdeg

/-- Challenge-facing normalized diagonal-operator form of the cubic
discriminant of a fixed-degree Schur--Szegő composition with a degree-`≤ 3`
left factor. -/
theorem cubicDiscr_schurSzegoComp_eq_diagonalOperator_jensenPolynomialThree_normalized
    {n : ℕ} {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3) :
    cubicDiscr (schurSzegoComp n f p) =
      cubicDiscr
        (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
          (jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ)))) :=
  RealRooted.cubicDiscr_schurSzegoComp_eq_diagonalOperator_jensenPolynomial_three_normalized
    hfdeg

/-- Challenge-facing reflected-derivative form of the level-`n` degree-three
normalized Jensen section. -/
theorem jensenPolynomialThree_normalized_eq_reflectIterateDerivative
    {n : ℕ} (hn : 3 ≤ n) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) :
    jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ)) =
      C ((6 : ℝ) / Nat.factorial n) *
        reflect 3 ((derivative^[n - 3]) (reflect n p)) :=
  RealRooted.jensenPolynomial_three_normalized_eq_reflect_iterate_derivative
    hn hpdeg

/-- Challenge-facing scalar-pulled reflected-derivative form of degree-three
fixed-degree Schur--Szego composition. -/
theorem schurSzegoComp_eq_C_mul_reflectDiagonalOperatorThree
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hfdeg : f.natDegree ≤ 3) (hpdeg : p.natDegree ≤ n) :
    schurSzegoComp n f p =
      C ((6 : ℝ) / Nat.factorial n) *
        diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
          (reflect 3 ((derivative^[n - 3]) (reflect n p))) :=
  RealRooted.schurSzegoComp_eq_C_mul_diagonalOperator_reflect_iterate_derivative_three
    hn hfdeg hpdeg

/-- Challenge-facing reflected-derivative discriminant form of degree-three
fixed-degree Schur--Szego composition. -/
theorem cubicDiscr_schurSzegoComp_eq_reflectDiagonalOperatorThree
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hfdeg : f.natDegree ≤ 3) (hpdeg : p.natDegree ≤ n) :
    cubicDiscr (schurSzegoComp n f p) =
      ((6 : ℝ) / Nat.factorial n) ^ 4 *
        cubicDiscr
          (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
            (reflect 3 ((derivative^[n - 3]) (reflect n p)))) :=
  RealRooted.cubicDiscr_schurSzegoComp_eq_reflect_diagonalOperator_three
    hn hfdeg hpdeg

/-- Challenge-facing nonnegativity transfer through the reflected-derivative
diagonal-operator form of degree-three fixed-degree Schur--Szego composition. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_reflectDiagonalOperatorThree
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hfdeg : f.natDegree ≤ 3) (hpdeg : p.natDegree ≤ n)
    (hdisc : 0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (reflect 3 ((derivative^[n - 3]) (reflect n p))))) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  RealRooted.cubicDiscr_schurSzegoComp_nonneg_of_reflect_diagonalOperator_three
    hn hfdeg hpdeg hdisc

/-- The isolated level-three diagonal base case implies the reflected-diagonal
cubic-discriminant target. -/
theorem schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_of_pfCubicDiscrDiagonal
    (h : pfCubicDiscrDiagonalNonnegStatement) :
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget :=
  fun hn hf hfdeg hpdeg hsplit =>
    RealRooted.cubicDiscr_reflect_diagonalOperator_nonneg_of_pfCubicDiscrDiagonalNonneg
      h hn hf hfdeg hpdeg hsplit

/-- The reflected-diagonal target specializes at level `3` to the isolated
level-three diagonal base case. -/
theorem pfCubicDiscrDiagonalNonnegStatement_of_reflectDiagonalTarget
    (h : schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget) :
    pfCubicDiscrDiagonalNonnegStatement :=
  fun hf hfdeg hqdeg hsplit => by
    simpa using h (n := 3) le_rfl hf hfdeg hqdeg hsplit

/-- The reflected-diagonal high-level target is equivalent to the isolated
level-three diagonal base case. -/
theorem schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_iff_pfDiagonalBase :
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget ↔
      pfCubicDiscrDiagonalNonnegStatement :=
  ⟨pfCubicDiscrDiagonalNonnegStatement_of_reflectDiagonalTarget,
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_of_pfCubicDiscrDiagonal⟩

/-- The reflected-diagonal cubic-discriminant target implies the high-level
Schur--Szegő cubic-discriminant target. -/
theorem schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_of_reflectDiagonal
    (hdisc : schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget) :
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget :=
  fun hn hf hfdeg hpdeg hsplit =>
    cubicDiscr_schurSzegoComp_nonneg_of_reflectDiagonalOperatorThree
      hn hfdeg hpdeg (hdisc hn hf hfdeg hpdeg hsplit)

/-- The isolated level-three diagonal base case implies the high-level
Schur--Szego cubic-discriminant target. -/
theorem schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement) :
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget :=
  fun hn hf hfdeg hpdeg hsplit =>
    cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_of_pfDiagonalBase
      h hn hf hfdeg hpdeg hsplit

/-- The isolated level-three diagonal base case is equivalent to the
high-level Schur--Szego cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_pfDiagonalBase :
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget ↔
      pfCubicDiscrDiagonalNonnegStatement :=
  ⟨fun h f q hf hfdeg hqdeg hsplit => by
    simpa [cubicDiscr_diagonalOperator_normalized_three_eq_cubicDiscr_schurSzegoComp]
      using h (by norm_num) hf hfdeg hqdeg hsplit,
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_of_pfDiagonalBase⟩

/-- The high-level Schur--Szego cubic-discriminant target is equivalent to the
reflected-diagonal target. -/
theorem
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_reflectDiagonal :
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget ↔
      schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget :=
  schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_pfDiagonalBase.trans
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_iff_pfDiagonalBase.symm

/-- The reflected-diagonal high-level target, together with the checked
low-level route, proves the corrected all-level cubic-discriminant target that
retains the left ambient-degree hypothesis. -/
theorem schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_reflectDiagonal
    (hdisc : schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_leftNatDegree_of_pfDiagonalBase
    (schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_iff_pfDiagonalBase.1
      hdisc)

/-- The isolated level-three diagonal base case implies the corrected
all-level cubic-discriminant target retaining the left ambient-degree
hypothesis. -/
theorem schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_leftNatDegree_of_pfDiagonalBase
    h

/-- The isolated level-three diagonal base case is equivalent to the corrected
all-level cubic-discriminant target retaining the left ambient-degree
hypothesis. -/
theorem
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_pfDiagonalBase :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget ↔
      pfCubicDiscrDiagonalNonnegStatement :=
  ⟨fun h f q hf hfdeg hqdeg hsplit => by
    simpa [cubicDiscr_diagonalOperator_normalized_three_eq_cubicDiscr_schurSzegoComp]
      using h hf hfdeg hfdeg hqdeg hsplit,
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_pfDiagonalBase⟩

/-- The corrected all-level cubic-discriminant target retaining the left
ambient-degree hypothesis is equivalent to the reflected-diagonal target. -/
theorem
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_reflectDiagonal :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget ↔
      schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_pfDiagonalBase.trans
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_iff_pfDiagonalBase.symm

/-- The corrected all-level cubic-discriminant target retaining the left
ambient-degree hypothesis is equivalent to the high-level target. -/
theorem
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_highLevel :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget ↔
      schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_pfDiagonalBase.trans
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_pfDiagonalBase.symm

/-- Challenge-facing degree-`≤ 3` PF-factor Schur--Szego route through the
reflected-derivative diagonal-operator discriminant. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_reflectDiagonalOperator
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hdisc : 0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (reflect 3 ((derivative^[n - 3]) (reflect n p))))) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  RealRooted.finiteSchurSzegoComposition_of_pf_factor_le_three_reflect_diagonalOperator
    hn hf hfdeg hpdeg hsplit hdisc

/-- High-level cubic-discriminant target version of the degree-`≤ 3`
PF-factor Schur--Szego route. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_highLevelTarget
    (hdisc : schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit (hdisc hn hf hfdeg hpdeg hsplit)

/-- High-level diagonal-operator target version of the degree-`≤ 3` PF-factor
Schur--Szego route. -/
theorem
    finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_highLevelDiagonalOperatorTarget
    (hdisc :
      schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit <| by
      simpa [cubicDiscr_schurSzegoComp_eq_diagonalOperator_jensenPolynomialThree_normalized
        hfdeg] using hdisc hn hf hfdeg hpdeg hsplit

/-- Reflected-diagonal target version of the high-level degree-`≤ 3` PF-factor
Schur--Szego route. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_reflectDiagonalTarget
    (hdisc : schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_reflectDiagonalOperator
    hn hf hfdeg hpdeg hsplit (hdisc hn hf hfdeg hpdeg hsplit)

/-- Isolated diagonal-base version of the high-level degree-`≤ 3` PF-factor
Schur--Szego route. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_le_three_of_pfCubicDiscrDiagonalNonneg
    h hn hf hfdeg hpdeg hsplit

/-- Nonzero-core reflected-diagonal-operator version of the high-level
degree-`≤ 3` PF-factor Schur--Szego route. -/
theorem finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_reflectDiagonalOperator
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hdisc : 0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (reflect 3 ((derivative^[n - 3]) (reflect n p))))) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_reflectDiagonalOperator
    hn hf hfdeg hpdeg hsplit hdisc

/-- Nonzero-core high-level cubic-discriminant target version of the
degree-`≤ 3` PF-factor Schur--Szego route. -/
theorem finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_highLevelTarget
    (hdisc : schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_highLevelTarget
    hdisc hn hf hfdeg hpdeg hsplit

/-- Nonzero-core high-level diagonal-operator target version of the
degree-`≤ 3` PF-factor Schur--Szego route. -/
theorem
    finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_highLevelDiagonalOperatorTarget
    (hdisc :
      schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_highLevelDiagonalOperatorTarget
    hdisc hn hf hfdeg hpdeg hsplit

/-- Nonzero-core reflected-diagonal target version of the high-level
degree-`≤ 3` PF-factor Schur--Szego route. -/
theorem finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_reflectDiagonalTarget
    (hdisc : schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_reflectDiagonalTarget
    hdisc hn hf hfdeg hpdeg hsplit

/-- Nonzero-core isolated diagonal-base version of the high-level degree-`≤ 3`
PF-factor Schur--Szego route. -/
theorem finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_pfDiagonalBase
    h hn hf hfdeg hpdeg hsplit

/-- All-level reflected-diagonal target version of the corrected degree-`≤ 3`
PF-factor Schur--Szego route retaining the left ambient-degree hypothesis. -/
theorem finiteSchurSzegoPair_of_leftNatDegree_of_reflectDiagonalTarget
    (hdisc : schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_le_three_leftNatDegree_of_pfCubicDiscrDiagonalNonneg
    (schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_iff_pfDiagonalBase.1
      hdisc)
    hf hfdeg hfn hpdeg hsplit

/-- All-level corrected cubic-discriminant target version of the degree-`≤ 3`
PF-factor Schur--Szego route retaining the left ambient-degree hypothesis. -/
theorem finiteSchurSzegoPair_of_leftNatDegreeTarget
    (hdisc : schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit (hdisc hf hfdeg hfn hpdeg hsplit)

/-- All-level high-level cubic-discriminant target version of the corrected
degree-`≤ 3` PF-factor Schur--Szego route retaining the left ambient-degree
hypothesis. -/
theorem finiteSchurSzegoPair_of_leftNatDegree_of_highLevelTarget
    (hdisc : schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegreeTarget
    (schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_highLevel.2
      hdisc)
    hf hfdeg hfn hpdeg hsplit

/-- All-level isolated diagonal-base version of the corrected degree-`≤ 3`
PF-factor Schur--Szego route retaining the left ambient-degree hypothesis. -/
theorem finiteSchurSzegoPair_of_leftNatDegree_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegreeTarget
    (schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_pfDiagonalBase.2
      h)
    hf hfdeg hfn hpdeg hsplit

/-- Nonzero-core all-level reflected-diagonal target version of the corrected
degree-`≤ 3` PF-factor Schur--Szego route retaining the left ambient-degree
hypothesis. -/
theorem finiteSchurSzegoNonzeroPair_of_leftNatDegree_of_reflectDiagonalTarget
    (hdisc : schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegree_of_reflectDiagonalTarget
    hdisc hf hfdeg hfn hpdeg hsplit

/-- Nonzero-core all-level corrected cubic-discriminant target version of the
degree-`≤ 3` PF-factor Schur--Szego route retaining the left ambient-degree
hypothesis. -/
theorem finiteSchurSzegoNonzeroPair_of_leftNatDegreeTarget
    (hdisc : schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegreeTarget
    hdisc hf hfdeg hfn hpdeg hsplit

/-- Nonzero-core all-level high-level cubic-discriminant target version of the
corrected degree-`≤ 3` PF-factor Schur--Szego route retaining the left
ambient-degree hypothesis. -/
theorem finiteSchurSzegoNonzeroPair_of_leftNatDegree_of_highLevelTarget
    (hdisc : schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegree_of_highLevelTarget
    hdisc hf hfdeg hfn hpdeg hsplit

/-- Nonzero-core all-level isolated diagonal-base version of the corrected
degree-`≤ 3` PF-factor Schur--Szego route retaining the left ambient-degree
hypothesis. -/
theorem finiteSchurSzegoNonzeroPair_of_leftNatDegree_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegree_of_pfDiagonalBase
    h hf hfdeg hfn hpdeg hsplit

/-- Challenge-facing cubic-discriminant nonnegativity for the degree-three
normalized Jensen section of a splitting polynomial. -/
theorem cubicDiscr_jensenPolynomialThree_normalized_nonneg_of_splits
    {n : ℕ} (hn : 3 ≤ n) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    0 ≤ cubicDiscr
      (jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ))) :=
  RealRooted.cubicDiscr_jensenPolynomial_three_normalized_nonneg_of_splits
    hn hpdeg hsplit

/-- Challenge-facing denominator-cleared form of the Schur--Szegő cubic
discriminant nonnegativity target at binomial level `n ≥ 3`. -/
theorem cubicDiscr_schurSzegoComp_nonneg_iff_of_three_le
    {n : ℕ} (hn : 3 ≤ n) (f p : ℝ[X]) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) ↔
      0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  RealRooted.cubicDiscr_schurSzegoComp_nonneg_iff_of_three_le hn f p

/-- Challenge-facing diagonal-operator Jensen route to the denominator-cleared
cubic-discriminant numerator. -/
theorem schurSzegoCompCubicDiscrNumerator_nonneg_of_diagonalOperatorJensen
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3)
    (hdisc : 0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ))))) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  RealRooted.schurSzegoCompCubicDiscrNumerator_nonneg_of_diagonalOperator_jensen_nonneg
    hn hfdeg hdisc

/-- The denominator-cleared numerator target gives the original cubic
discriminant nonnegativity statement at levels `n ≥ 3`. -/
theorem schurSzegoCompPFFactorCubicDiscriminantNonneg_of_numeratorTarget
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hn : 3 ≤ n) (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  (cubicDiscr_schurSzegoComp_nonneg_iff_of_three_le hn f p).2
    (hnum hn hf hfdeg hpdeg hsplit)

/-- The high-level numerator target proves the corrected degree-`≤ 3`
PF-factor cubic-discriminant target, once the original left ambient-degree
hypothesis `f.natDegree ≤ n` is retained. -/
theorem schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_numerator
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  fun hf hfdeg hfn hpdeg hsplit =>
    cubicDiscr_schurSzegoComp_nonneg_of_pf_factor_le_three_leftNatDegree_num_nonneg
      hf hfdeg hfn hpdeg hsplit
      (fun hn => hnum hn hf hfdeg hpdeg hsplit)

/-- At levels `n ≥ 3`, the cubic-discriminant target is equivalent to the
denominator-cleared numerator target. -/
theorem schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_numerator :
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget ↔
      schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget :=
  ⟨fun hdisc _n f p hn hf hfdeg hpdeg hsplit =>
    (cubicDiscr_schurSzegoComp_nonneg_iff_of_three_le hn f p).1
      (hdisc hn hf hfdeg hpdeg hsplit),
    schurSzegoCompPFFactorCubicDiscriminantNonneg_of_numeratorTarget⟩

/-- At high levels, the original cubic-discriminant target is equivalent to
the normalized diagonal-operator target. -/
theorem
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_highLevelDiagonalOperator :
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget ↔
      schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget :=
  ⟨fun hdisc {n} {f} {p} hn hf hfdeg hpdeg hsplit => by
    simpa [← cubicDiscr_schurSzegoComp_eq_diagonalOperator_jensenPolynomialThree_normalized
      hfdeg] using hdisc hn hf hfdeg hpdeg hsplit,
    fun hdiag {n} {f} {p} hn hf hfdeg hpdeg hsplit => by
      simpa [cubicDiscr_schurSzegoComp_eq_diagonalOperator_jensenPolynomialThree_normalized
        hfdeg] using hdiag hn hf hfdeg hpdeg hsplit⟩

/-- The high-level diagonal-operator target implies the high-level
cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorHighLevelCubicDiscriminantTarget_of_highLevelDiagonalOperator
    (hdisc :
      schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget) :
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget :=
  schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_highLevelDiagonalOperator.2
    hdisc

/-- The high-level cubic-discriminant target implies the high-level
diagonal-operator target. -/
theorem
    schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_highLevelCubicDiscriminant
    (hdisc : schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget) :
    schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget :=
  schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_highLevelDiagonalOperator.1
    hdisc

/-- Pointwise high-level Schur--Szegő cubic-discriminant route from the
high-level diagonal-operator target. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_highLevelDiagonalOperatorTarget
    (hdisc :
      schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hn : 3 ≤ n) (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  schurSzegoCompPFFactorHighLevelCubicDiscriminantTarget_of_highLevelDiagonalOperator
    hdisc hn hf hfdeg hpdeg hsplit

/-- The high-level diagonal-operator target gives the denominator-cleared
numerator target. -/
theorem
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_highLevelDiagonalOperator
    (hdisc :
      schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget) :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget :=
  schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_numerator.1
    (schurSzegoCompPFFactorHighLevelCubicDiscriminantTarget_of_highLevelDiagonalOperator
      hdisc)

/-- The denominator-cleared numerator target gives the high-level
diagonal-operator target. -/
theorem
    schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget_of_numerator
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget) :
    schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget :=
  schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_highLevelCubicDiscriminant
    (schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_numerator.2
      hnum)

/-- The high-level normalized diagonal-operator target is equivalent to the
denominator-cleared numerator target. -/
theorem
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_highLevelDiagonalOperator :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget ↔
      schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget :=
  schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_numerator.symm.trans
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_highLevelDiagonalOperator

/-- The denominator-cleared high-level numerator target is equivalent to the
isolated level-three diagonal base case. -/
theorem schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_pfDiagonalBase :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget ↔
      pfCubicDiscrDiagonalNonnegStatement :=
  schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_numerator.symm.trans
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_pfDiagonalBase

/-- The denominator-cleared high-level numerator target is equivalent to the
reflected-diagonal target. -/
theorem
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_reflectDiagonal :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget ↔
      schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_pfDiagonalBase.trans
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_iff_pfDiagonalBase.symm

/-- The denominator-cleared high-level numerator target is equivalent to the
corrected all-level cubic-discriminant target retaining the left ambient-degree
hypothesis. -/
theorem
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_leftNatDegreeTarget :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget ↔
      schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_pfDiagonalBase.trans
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_pfDiagonalBase.symm

/-- The corrected all-level cubic-discriminant target retaining the left
ambient-degree hypothesis is equivalent to the denominator-cleared high-level
numerator target. -/
theorem
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_numerator :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget ↔
      schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_leftNatDegreeTarget.symm

/-- The denominator-cleared numerator target implies the corrected all-level
cubic-discriminant target retaining the left ambient-degree hypothesis. -/
theorem schurSzegoCompPFFactorLeftNatDegreeTarget_of_numerator
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_numerator hnum

/-- The corrected all-level cubic-discriminant target retaining the left
ambient-degree hypothesis implies the denominator-cleared numerator target. -/
theorem schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_leftNatDegree
    (hdisc : schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget) :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_numerator.1
    hdisc

/-- The corrected all-level cubic-discriminant target retaining the left
ambient-degree hypothesis is equivalent to the high-level diagonal-operator
target. -/
theorem
    schurSzegoCompPFFactorLeftNatDegreeTarget_iff_highLevelDiagonalOperator :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget ↔
      schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_highLevel.trans
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_highLevelDiagonalOperator

/-- The high-level diagonal-operator target is equivalent to the corrected
all-level cubic-discriminant target retaining the left ambient-degree
hypothesis. -/
theorem
    schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_iff_leftNatDegree :
    schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget ↔
      schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorLeftNatDegreeTarget_iff_highLevelDiagonalOperator.symm

/-- The high-level diagonal-operator target is equivalent to the isolated
level-three diagonal base case. -/
theorem
    schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_iff_pfDiagonalBase :
    schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget ↔
      pfCubicDiscrDiagonalNonnegStatement :=
  schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_iff_leftNatDegree.trans
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_pfDiagonalBase

/-- The isolated level-three diagonal base case implies the high-level
diagonal-operator target. -/
theorem schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement) :
    schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget :=
  schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_iff_pfDiagonalBase.2 h

/-- The high-level diagonal-operator target implies the corrected all-level
cubic-discriminant target retaining the left ambient-degree hypothesis. -/
theorem schurSzegoCompPFFactorLeftNatDegreeTarget_of_highLevelDiagonalOperator
    (hdisc :
      schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_iff_leftNatDegree.1
    hdisc

/-- The corrected all-level cubic-discriminant target retaining the left
ambient-degree hypothesis implies the high-level diagonal-operator target. -/
theorem schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_leftNatDegree
    (hdisc :
      schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget) :
    schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget :=
  schurSzegoCompPFFactorLeftNatDegreeTarget_iff_highLevelDiagonalOperator.1
    hdisc

/-- The classical fixed-degree Schur--Szego theorem discharges the
reflected-diagonal cubic-discriminant target. -/
theorem schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget :=
  schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_of_pfCubicDiscrDiagonal
    (pfCubicDiscrDiagonalNonnegStatement_of_schurSzego hSZ)

/-- The classical fixed-degree Schur--Szego theorem discharges the high-level
cubic-discriminant target. -/
theorem schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget :=
  schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_of_pfDiagonalBase
    (pfCubicDiscrDiagonalNonnegStatement_of_schurSzego hSZ)

/-- The classical fixed-degree Schur--Szego theorem discharges the corrected
all-level left-degree cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_pfDiagonalBase
    (pfCubicDiscrDiagonalNonnegStatement_of_schurSzego hSZ)

/-- The classical fixed-degree Schur--Szego theorem discharges the
denominator-cleared numerator target. -/
theorem schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_pfDiagonalBase.2
    (pfCubicDiscrDiagonalNonnegStatement_of_schurSzego hSZ)

/-- The classical fixed-degree Schur--Szego theorem discharges the high-level
diagonal-operator target. -/
theorem schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget :=
  schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_pfDiagonalBase
    (pfCubicDiscrDiagonalNonnegStatement_of_schurSzego hSZ)

/-- Challenge-facing alias: the fixed-degree Schur--Szegő target discharges
the isolated level-three diagonal base case. -/
theorem pfCubicDiscrDiagonalNonnegStatement_of_finiteSchurSzego
    (hSZ : finiteSchurSzegoTarget) :
    pfCubicDiscrDiagonalNonnegStatement :=
  pfCubicDiscrDiagonalNonnegStatement_of_schurSzego hSZ

/-- Challenge-facing alias: the fixed-degree Schur--Szegő target discharges
the reflected-diagonal cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_of_finiteSchurSzego
    (hSZ : finiteSchurSzegoTarget) :
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget :=
  schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_of_schurSzego
    hSZ

/-- Challenge-facing alias: the fixed-degree Schur--Szegő target discharges
the high-level cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_of_finiteSchurSzego
    (hSZ : finiteSchurSzegoTarget) :
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget :=
  schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_of_schurSzego
    hSZ

/-- Challenge-facing alias: the fixed-degree Schur--Szegő target discharges
the corrected all-level left-degree cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_finiteSchurSzego
    (hSZ : finiteSchurSzegoTarget) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_schurSzego
    hSZ

/-- Challenge-facing alias: the fixed-degree Schur--Szegő target discharges
the denominator-cleared numerator target. -/
theorem schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_finiteSchurSzego
    (hSZ : finiteSchurSzegoTarget) :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_schurSzego hSZ

/-- Challenge-facing alias: the fixed-degree Schur--Szegő target discharges
the high-level diagonal-operator target. -/
theorem schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_finiteSchurSzego
    (hSZ : finiteSchurSzegoTarget) :
    schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget :=
  schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_schurSzego hSZ

/-- Challenge-facing alias: the nonzero fixed-degree Schur--Szegő core
discharges the isolated level-three diagonal base case. -/
theorem pfCubicDiscrDiagonalNonnegStatement_of_finiteSchurSzegoNonzero
    (hSZ : finiteSchurSzegoNonzeroTarget) :
    pfCubicDiscrDiagonalNonnegStatement :=
  pfCubicDiscrDiagonalNonnegStatement_of_schurSzego
    (finiteSchurSzegoTarget_of_nonzero hSZ)

/-- Challenge-facing alias: the nonzero fixed-degree Schur--Szegő core
discharges the reflected-diagonal cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_of_finiteSchurSzegoNonzero
    (hSZ : finiteSchurSzegoNonzeroTarget) :
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget :=
  schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_of_schurSzego
    (finiteSchurSzegoTarget_of_nonzero hSZ)

/-- Challenge-facing alias: the nonzero fixed-degree Schur--Szegő core
discharges the high-level cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_of_finiteSchurSzegoNonzero
    (hSZ : finiteSchurSzegoNonzeroTarget) :
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget :=
  schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_of_schurSzego
    (finiteSchurSzegoTarget_of_nonzero hSZ)

/-- Challenge-facing alias: the nonzero fixed-degree Schur--Szegő core
discharges the corrected all-level left-degree cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_finiteSchurSzegoNonzero
    (hSZ : finiteSchurSzegoNonzeroTarget) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_schurSzego
    (finiteSchurSzegoTarget_of_nonzero hSZ)

/-- Challenge-facing alias: the nonzero fixed-degree Schur--Szegő core
discharges the denominator-cleared numerator target. -/
theorem
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_finiteSchurSzegoNonzero
    (hSZ : finiteSchurSzegoNonzeroTarget) :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_schurSzego
    (finiteSchurSzegoTarget_of_nonzero hSZ)

/-- Challenge-facing alias: the nonzero fixed-degree Schur--Szegő core
discharges the high-level diagonal-operator target. -/
theorem
    schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_finiteSchurSzegoNonzero
    (hSZ : finiteSchurSzegoNonzeroTarget) :
    schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget :=
  schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_schurSzego
    (finiteSchurSzegoTarget_of_nonzero hSZ)

/-- Challenge-facing alias: finite Pólya--Schur discharges the isolated
level-three diagonal base case. -/
theorem pfCubicDiscrDiagonalNonnegStatement_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget) :
    pfCubicDiscrDiagonalNonnegStatement :=
  pfCubicDiscrDiagonalNonnegStatement_of_schurSzego
    (finiteSchurSzegoTarget_of_finitePolyaSchur hFPS)

/-- Challenge-facing alias: finite Pólya--Schur discharges the
reflected-diagonal cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget) :
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget :=
  schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_of_schurSzego
    (finiteSchurSzegoTarget_of_finitePolyaSchur hFPS)

/-- Challenge-facing alias: finite Pólya--Schur discharges the high-level
cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget) :
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget :=
  schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_of_schurSzego
    (finiteSchurSzegoTarget_of_finitePolyaSchur hFPS)

/-- Challenge-facing alias: finite Pólya--Schur discharges the corrected
all-level left-degree cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_schurSzego
    (finiteSchurSzegoTarget_of_finitePolyaSchur hFPS)

/-- Challenge-facing alias: finite Pólya--Schur discharges the
denominator-cleared numerator target. -/
theorem schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget) :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_schurSzego
    (finiteSchurSzegoTarget_of_finitePolyaSchur hFPS)

/-- Challenge-facing alias: finite Pólya--Schur discharges the high-level
diagonal-operator target. -/
theorem
    schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget) :
    schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget :=
  schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_schurSzego
    (finiteSchurSzegoTarget_of_finitePolyaSchur hFPS)

/-- Challenge-facing alias: the backward finite Pólya--Schur direction
discharges the isolated level-three diagonal base case. -/
theorem pfCubicDiscrDiagonalNonnegStatement_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget) :
    pfCubicDiscrDiagonalNonnegStatement :=
  pfCubicDiscrDiagonalNonnegStatement_of_finitePolyaSchur
    (finitePolyaSchurTarget_of_backward hBack)

/-- Challenge-facing alias: the backward finite Pólya--Schur direction
discharges the reflected-diagonal cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget) :
    schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget :=
  schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget_of_finitePolyaSchur
    (finitePolyaSchurTarget_of_backward hBack)

/-- Challenge-facing alias: the backward finite Pólya--Schur direction
discharges the high-level cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget) :
    schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget :=
  schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_of_finitePolyaSchur
    (finitePolyaSchurTarget_of_backward hBack)

/-- Challenge-facing alias: the backward finite Pólya--Schur direction
discharges the corrected all-level left-degree cubic-discriminant target. -/
theorem
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_finitePolyaSchur
    (finitePolyaSchurTarget_of_backward hBack)

/-- Challenge-facing alias: the backward finite Pólya--Schur direction
discharges the denominator-cleared numerator target. -/
theorem
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget) :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_finitePolyaSchur
    (finitePolyaSchurTarget_of_backward hBack)

/-- Challenge-facing alias: the backward finite Pólya--Schur direction
discharges the high-level diagonal-operator target. -/
theorem
    schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget) :
    schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget :=
  schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_of_finitePolyaSchur
    (finitePolyaSchurTarget_of_backward hBack)

/-- Pointwise form of the corrected left-degree cubic-discriminant target. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegreeTarget
    (hdisc : schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  hdisc hf hfdeg hfn hpdeg hsplit

/-- Pointwise corrected left-degree cubic-discriminant route from the
high-level cubic-discriminant target. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_highLevelTarget
    (hdisc : schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  (schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_highLevel.2
    hdisc) hf hfdeg hfn hpdeg hsplit

/-- Pointwise corrected left-degree cubic-discriminant route from the
reflected-diagonal target. -/
theorem
    cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_reflectDiagonalTarget
    (hdisc : schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  (schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_reflectDiagonal.2
    hdisc) hf hfdeg hfn hpdeg hsplit

/-- Pointwise corrected left-degree cubic-discriminant route from the isolated
level-three diagonal base case. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_pfDiagonalBase
    h hf hfdeg hfn hpdeg hsplit

/-- Pointwise corrected left-degree cubic-discriminant route from the
denominator-cleared numerator target. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_numeratorTarget
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  schurSzegoCompPFFactorLeftNatDegreeTarget_of_numerator
    hnum hf hfdeg hfn hpdeg hsplit

/-- Pointwise corrected left-degree cubic-discriminant route from the
high-level diagonal-operator target. -/
theorem
    cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_highLevelDiagonalOperatorTarget
    (hdisc :
      schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  (schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_iff_leftNatDegree.1
    hdisc) hf hfdeg hfn hpdeg hsplit

/-- Pointwise corrected left-degree cubic-discriminant route from the
corrected normalized Jensen-product target. -/
theorem
    cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_jensenProductLeftNatDegreeTarget
    (hdisc :
      schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  by
    simpa [cubicDiscr_schurSzegoComp_eq_jensenPolynomialThree_normalized
      hfdeg] using hdisc hf hfdeg hfn hpdeg hsplit

/-- Pointwise corrected left-degree cubic-discriminant route from the
corrected diagonal-operator target. -/
theorem
    cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_diagonalOperatorLeftNatDegreeTarget
    (hdisc :
      schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  by
    simpa [cubicDiscr_schurSzegoComp_eq_diagonalOperator_jensenPolynomialThree_normalized
      hfdeg] using hdisc hf hfdeg hfn hpdeg hsplit

/-- Pointwise denominator-cleared numerator route from the numerator target
itself. -/
theorem schurSzegoCompCubicDiscrNumerator_nonneg_of_numeratorTarget
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  hnum hn hf hfdeg hpdeg hsplit

/-- Pointwise denominator-cleared numerator route from the high-level
cubic-discriminant target. -/
theorem schurSzegoCompCubicDiscrNumerator_nonneg_of_highLevelTarget
    (hdisc : schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  (schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_numerator.1
    hdisc) hn hf hfdeg hpdeg hsplit

/-- Pointwise denominator-cleared numerator route from the corrected
left-degree cubic-discriminant target. -/
theorem schurSzegoCompCubicDiscrNumerator_nonneg_of_leftNatDegreeTarget
    (hdisc : schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  (schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_numerator.1
    hdisc) hn hf hfdeg hpdeg hsplit

/-- Pointwise denominator-cleared numerator route from the isolated
level-three diagonal base case. -/
theorem schurSzegoCompCubicDiscrNumerator_nonneg_of_pfDiagonalBase
    (h : pfCubicDiscrDiagonalNonnegStatement)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  (schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_pfDiagonalBase.2
    h) hn hf hfdeg hpdeg hsplit

/-- Pointwise denominator-cleared numerator route from the reflected-diagonal
target. -/
theorem schurSzegoCompCubicDiscrNumerator_nonneg_of_reflectDiagonalTarget
    (hdisc : schurSzegoCompPFFactorReflectDiagonalCubicDiscriminantTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  (schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_reflectDiagonal.2
    hdisc) hn hf hfdeg hpdeg hsplit

/-- Pointwise denominator-cleared numerator route from the high-level
diagonal-operator target. -/
theorem
    schurSzegoCompCubicDiscrNumerator_nonneg_of_highLevelDiagonalOperatorTarget
    (hdisc :
      schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  (schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_highLevelDiagonalOperator.2
    hdisc) hn hf hfdeg hpdeg hsplit

/-- Pointwise corrected left-degree cubic-discriminant route from the
classical fixed-degree Schur--Szegő theorem. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_schurSzego
    hSZ hf hfdeg hfn hpdeg hsplit

/-- Pointwise denominator-cleared high-level numerator route from the
classical fixed-degree Schur--Szegő theorem. -/
theorem schurSzegoCompCubicDiscrNumerator_nonneg_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_schurSzego
    hSZ hn hf hfdeg hpdeg hsplit

/-- Pointwise corrected left-degree cubic-discriminant route from the
challenge-facing fixed-degree Schur--Szego target. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_finiteSchurSzego
    (hSZ : finiteSchurSzegoTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_schurSzego
    hSZ hf hfdeg hfn hpdeg hsplit

/-- Pointwise denominator-cleared high-level numerator route from the
challenge-facing fixed-degree Schur--Szego target. -/
theorem schurSzegoCompCubicDiscrNumerator_nonneg_of_finiteSchurSzego
    (hSZ : finiteSchurSzegoTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  schurSzegoCompCubicDiscrNumerator_nonneg_of_schurSzego
    hSZ hn hf hfdeg hpdeg hsplit

/-- Pointwise corrected left-degree cubic-discriminant route from the nonzero
core of the classical fixed-degree Schur--Szegő theorem. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_schurSzegoNonzero
    (hSZ : finiteSchurSzegoNonzeroTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_schurSzego
    (finiteSchurSzegoTarget_of_nonzero hSZ) hf hfdeg hfn hpdeg hsplit

/-- Pointwise denominator-cleared high-level numerator route from the nonzero
core of the classical fixed-degree Schur--Szegő theorem. -/
theorem schurSzegoCompCubicDiscrNumerator_nonneg_of_schurSzegoNonzero
    (hSZ : finiteSchurSzegoNonzeroTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  schurSzegoCompCubicDiscrNumerator_nonneg_of_schurSzego
    (finiteSchurSzegoTarget_of_nonzero hSZ) hn hf hfdeg hpdeg hsplit

/-- Pointwise corrected left-degree cubic-discriminant route from finite
Pólya--Schur. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_schurSzego
    (finiteSchurSzegoTarget_of_finitePolyaSchur hFPS)
    hf hfdeg hfn hpdeg hsplit

/-- Pointwise denominator-cleared high-level numerator route from finite
Pólya--Schur. -/
theorem schurSzegoCompCubicDiscrNumerator_nonneg_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  schurSzegoCompCubicDiscrNumerator_nonneg_of_schurSzego
    (finiteSchurSzegoTarget_of_finitePolyaSchur hFPS)
    hn hf hfdeg hpdeg hsplit

/-- Pointwise corrected left-degree cubic-discriminant route from the backward
finite Pólya--Schur direction. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) :=
  cubicDiscr_schurSzegoComp_nonneg_of_leftNatDegree_of_finitePolyaSchur
    (finitePolyaSchurTarget_of_backward hBack) hf hfdeg hfn hpdeg hsplit

/-- Pointwise denominator-cleared high-level numerator route from the backward
finite Pólya--Schur direction. -/
theorem schurSzegoCompCubicDiscrNumerator_nonneg_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  schurSzegoCompCubicDiscrNumerator_nonneg_of_finitePolyaSchur
    (finitePolyaSchurTarget_of_backward hBack) hn hf hfdeg hpdeg hsplit

/-- The full degree-`≤ 3` PF-factor cubic-discriminant target splits into
independent high-level (`n ≥ 3`) and low-level (`n < 3`) targets. -/
theorem schurSzegoCompPFFactorCubicDiscriminantNonnegTarget_iff_high_low :
    schurSzegoCompPFFactorCubicDiscriminantNonnegTarget ↔
      schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget ∧
        schurSzegoCompPFFactorLowLevelCubicDiscriminantNonnegTarget :=
  ⟨fun hdisc => ⟨fun _ => hdisc, fun _ => hdisc⟩,
    fun ⟨hhigh, hlow⟩ {n _f _p} hf hfdeg hpdeg hsplit =>
      (le_or_gt 3 n).elim (hhigh · hf hfdeg hpdeg hsplit)
        (hlow · hf hfdeg hpdeg hsplit)⟩

/-- A low-level proof together with the denominator-cleared high-level
numerator target gives the full degree-`≤ 3` PF-factor cubic-discriminant
target. -/
theorem schurSzegoCompPFFactorCubicDiscriminantNonnegTarget_of_lowLevel_of_numerator
    (hlow : schurSzegoCompPFFactorLowLevelCubicDiscriminantNonnegTarget)
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegTarget_iff_high_low.2
    ⟨schurSzegoCompPFFactorHighLevelCubicDiscriminantNonnegTarget_iff_numerator.2
      hnum, hlow⟩

/-- The diagonal-operator cubic discriminant target is equivalent to the
normalized Jensen-product target. -/
theorem schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantTarget_iff_jensenProduct :
    schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantTarget ↔
      schurSzegoCompPFFactorJensenProductCubicDiscriminantTarget :=
  by
    constructor <;>
      intro h n f p hf hfdeg hpdeg hsplit <;>
      simpa [← cubicDiscr_schurSzegoComp_eq_jensenPolynomial_three_normalized hfdeg,
        ← cubicDiscr_schurSzegoComp_eq_diagonalOperator_jensenPolynomial_three_normalized hfdeg]
        using h hf hfdeg hpdeg hsplit

/-- The corrected diagonal-operator cubic discriminant target is equivalent to
the corrected normalized Jensen-product target. -/
theorem
    schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget_iff_jensenProduct :
    schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget ↔
      schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget :=
  by
    constructor <;>
      intro h n f p hf hfdeg hfn hpdeg hsplit <;>
      simpa [← cubicDiscr_schurSzegoComp_eq_jensenPolynomial_three_normalized hfdeg,
        ← cubicDiscr_schurSzegoComp_eq_diagonalOperator_jensenPolynomial_three_normalized hfdeg]
        using h hf hfdeg hfn hpdeg hsplit

/-- The corrected Schur--Szego cubic discriminant target is equivalent to the
corrected normalized Jensen-product target. -/
theorem
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_jensenProduct :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget ↔
      schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget :=
  ⟨fun hdisc n f p hf hfdeg hfn hpdeg hsplit => by
    simpa [cubicDiscr_schurSzegoComp_eq_jensenPolynomial_three_normalized hfdeg]
      using hdisc hf hfdeg hfn hpdeg hsplit,
    fun hjensen n f p hf hfdeg hfn hpdeg hsplit => by
      simpa [cubicDiscr_schurSzegoComp_eq_jensenPolynomial_three_normalized hfdeg]
        using hjensen hf hfdeg hfn hpdeg hsplit⟩

/-- The corrected Schur--Szego cubic discriminant target is equivalent to the
corrected diagonal-operator target. -/
theorem
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_diagonalOperator :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget ↔
      schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_jensenProduct.trans <|
    Iff.symm <|
      schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget_iff_jensenProduct

/-- The denominator-cleared numerator target is equivalent to the corrected
normalized Jensen-product target. -/
theorem
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_jensenProductLeftNatDegree :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget ↔
      schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_leftNatDegreeTarget.trans
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_jensenProduct

/-- The denominator-cleared numerator target is equivalent to the corrected
diagonal-operator target. -/
theorem
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_diagonalOperatorLeftNatDegree :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget ↔
      schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_leftNatDegreeTarget.trans
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_diagonalOperator

/-- The corrected normalized Jensen-product target is equivalent to the
denominator-cleared numerator target. -/
theorem
    schurSzegoCompPFFactorJensenProductLeftNatDegreeTarget_iff_numerator :
    schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget ↔
      schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_jensenProductLeftNatDegree.symm

/-- The corrected diagonal-operator target is equivalent to the
denominator-cleared numerator target. -/
theorem
    schurSzegoCompPFFactorDiagonalOperatorLeftNatDegreeTarget_iff_numerator :
    schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget ↔
      schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_iff_diagonalOperatorLeftNatDegree.symm

/-- The denominator-cleared numerator target implies the corrected
normalized Jensen-product target. -/
theorem
    schurSzegoCompPFFactorJensenProductLeftNatDegreeTarget_of_numerator
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget) :
    schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorJensenProductLeftNatDegreeTarget_iff_numerator.2 hnum

/-- The corrected normalized Jensen-product target implies the
denominator-cleared numerator target. -/
theorem
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_jensenProductLeftNatDegree
    (hdisc :
      schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget) :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget :=
  schurSzegoCompPFFactorJensenProductLeftNatDegreeTarget_iff_numerator.1 hdisc

/-- The denominator-cleared numerator target implies the corrected
diagonal-operator target. -/
theorem
    schurSzegoCompPFFactorDiagonalOperatorLeftNatDegreeTarget_of_numerator
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget) :
    schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorDiagonalOperatorLeftNatDegreeTarget_iff_numerator.2 hnum

/-- The corrected diagonal-operator target implies the denominator-cleared
numerator target. -/
theorem
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_diagonalOperatorLeftNatDegree
    (hdisc :
      schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget) :
    schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget :=
  schurSzegoCompPFFactorDiagonalOperatorLeftNatDegreeTarget_iff_numerator.1 hdisc

/-- The corrected normalized Jensen-product target implies the corrected
Schur--Szego cubic discriminant target. -/
theorem schurSzegoCompPFFactorLeftNatDegreeTarget_of_jensenProduct
    (hdisc :
      schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_jensenProduct.2
    hdisc

/-- The corrected Schur--Szego cubic discriminant target implies the corrected
normalized Jensen-product target. -/
theorem schurSzegoCompPFFactorJensenProductTarget_of_leftNatDegreeTarget
    (hdisc : schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget) :
    schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_jensenProduct.1
    hdisc

/-- The corrected diagonal-operator target implies the corrected Schur--Szego
cubic discriminant target. -/
theorem schurSzegoCompPFFactorLeftNatDegreeTarget_of_diagonalOperator
    (hdisc :
      schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_diagonalOperator.2
    hdisc

/-- The corrected diagonal-operator target implies the corrected normalized
Jensen-product target. -/
theorem schurSzegoCompPFFactorJensenProductTarget_of_diagonalOperator
    (hdisc :
      schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget) :
    schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget_iff_jensenProduct.1
    hdisc

/-- The corrected Schur--Szego cubic discriminant target implies the corrected
diagonal-operator target. -/
theorem schurSzegoCompPFFactorDiagonalOperatorTarget_of_leftNatDegreeTarget
    (hdisc : schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget) :
    schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_diagonalOperator.1
    hdisc

/-- The corrected normalized Jensen-product target implies the corrected
diagonal-operator target. -/
theorem schurSzegoCompPFFactorDiagonalOperatorTarget_of_jensenProduct
    (hdisc :
      schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget) :
    schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget_iff_jensenProduct.2
    hdisc

/-- Pointwise denominator-cleared numerator route from the corrected
normalized Jensen-product target. -/
theorem
    schurSzegoCompCubicDiscrNumerator_nonneg_of_jensenProductLeftNatDegreeTarget
    (hdisc :
      schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_jensenProductLeftNatDegree
    hdisc hn hf hfdeg hpdeg hsplit

/-- Pointwise denominator-cleared numerator route from the corrected
diagonal-operator target. -/
theorem
    schurSzegoCompCubicDiscrNumerator_nonneg_of_diagonalOperatorLeftNatDegreeTarget
    (hdisc :
      schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget_of_diagonalOperatorLeftNatDegree
    hdisc hn hf hfdeg hpdeg hsplit

/-- The classical fixed-degree Schur--Szego theorem discharges the corrected
normalized Jensen-product target. -/
theorem schurSzegoCompPFFactorJensenProductTarget_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorJensenProductTarget_of_leftNatDegreeTarget
    (schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_schurSzego
      hSZ)

/-- The classical fixed-degree Schur--Szego theorem discharges the corrected
diagonal-operator target. -/
theorem schurSzegoCompPFFactorDiagonalOperatorTarget_of_schurSzego
    (hSZ : finiteSchurSzegoCompositionStatement) :
    schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorDiagonalOperatorTarget_of_leftNatDegreeTarget
    (schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_of_schurSzego
      hSZ)

/-- Challenge-facing alias: the fixed-degree Schur--Szegő target discharges
the corrected normalized Jensen-product target. -/
theorem schurSzegoCompPFFactorJensenProductTarget_of_finiteSchurSzego
    (hSZ : finiteSchurSzegoTarget) :
    schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorJensenProductTarget_of_schurSzego hSZ

/-- Challenge-facing alias: the fixed-degree Schur--Szegő target discharges
the corrected diagonal-operator target. -/
theorem schurSzegoCompPFFactorDiagonalOperatorTarget_of_finiteSchurSzego
    (hSZ : finiteSchurSzegoTarget) :
    schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorDiagonalOperatorTarget_of_schurSzego hSZ

/-- Challenge-facing alias: the nonzero fixed-degree Schur--Szegő core
discharges the corrected normalized Jensen-product target. -/
theorem
    schurSzegoCompPFFactorJensenProductTarget_of_finiteSchurSzegoNonzero
    (hSZ : finiteSchurSzegoNonzeroTarget) :
    schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorJensenProductTarget_of_finiteSchurSzego
    (finiteSchurSzegoTarget_of_nonzero hSZ)

/-- Challenge-facing alias: the nonzero fixed-degree Schur--Szegő core
discharges the corrected diagonal-operator target. -/
theorem
    schurSzegoCompPFFactorDiagonalOperatorTarget_of_finiteSchurSzegoNonzero
    (hSZ : finiteSchurSzegoNonzeroTarget) :
    schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorDiagonalOperatorTarget_of_finiteSchurSzego
    (finiteSchurSzegoTarget_of_nonzero hSZ)

/-- Challenge-facing alias: finite Pólya--Schur discharges the corrected
normalized Jensen-product target. -/
theorem schurSzegoCompPFFactorJensenProductTarget_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget) :
    schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorJensenProductTarget_of_finiteSchurSzego
    (finiteSchurSzegoTarget_of_finitePolyaSchur hFPS)

/-- Challenge-facing alias: finite Pólya--Schur discharges the corrected
diagonal-operator target. -/
theorem schurSzegoCompPFFactorDiagonalOperatorTarget_of_finitePolyaSchur
    (hFPS : finitePolyaSchurTarget) :
    schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorDiagonalOperatorTarget_of_finiteSchurSzego
    (finiteSchurSzegoTarget_of_finitePolyaSchur hFPS)

/-- Challenge-facing alias: the backward finite Pólya--Schur direction
discharges the corrected normalized Jensen-product target. -/
theorem
    schurSzegoCompPFFactorJensenProductTarget_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget) :
    schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorJensenProductTarget_of_finitePolyaSchur
    (finitePolyaSchurTarget_of_backward hBack)

/-- Challenge-facing alias: the backward finite Pólya--Schur direction
discharges the corrected diagonal-operator target. -/
theorem
    schurSzegoCompPFFactorDiagonalOperatorTarget_of_finitePolyaSchurBackward
    (hBack : finitePolyaSchurBackwardTarget) :
    schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget :=
  schurSzegoCompPFFactorDiagonalOperatorTarget_of_finitePolyaSchur
    (finitePolyaSchurTarget_of_backward hBack)

/-- The normalized Jensen-product cubic discriminant target implies the
original Schur--Szegő cubic discriminant target. -/
theorem schurSzegoCompPFFactorCubicDiscriminantNonnegTarget_of_jensenProduct
    (hdisc : schurSzegoCompPFFactorJensenProductCubicDiscriminantTarget) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegTarget :=
  fun hf hfdeg hpdeg hsplit => by
    simpa [cubicDiscr_schurSzegoComp_eq_jensenPolynomial_three_normalized hfdeg]
      using hdisc hf hfdeg hpdeg hsplit

/-- The diagonal-operator cubic discriminant target implies the original
Schur--Szegő cubic discriminant target. -/
theorem schurSzegoCompPFFactorCubicDiscriminantNonnegTarget_of_diagonalOperator
    (hdisc : schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantTarget) :
    schurSzegoCompPFFactorCubicDiscriminantNonnegTarget :=
  fun hf hfdeg hpdeg hsplit => by
    simpa [cubicDiscr_schurSzegoComp_eq_diagonalOperator_jensenPolynomial_three_normalized
      hfdeg] using hdisc hf hfdeg hpdeg hsplit

/-- The degree-`≤ 3` PF-factor cubic discriminant target is exactly the
remaining input needed for the corresponding Schur--Szegő pair route. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_cubicDiscriminantTarget
    (hdisc : schurSzegoCompPFFactorCubicDiscriminantNonnegTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_cubicDiscr_nonneg
    hf hfdeg hpdeg hsplit (hdisc hf hfdeg hpdeg hsplit)

/-- Denominator-cleared numerator version of the degree-`≤ 3` PF-factor
Schur--Szego route at a single level `n ≥ 3`, taking the pointwise numerator
nonnegativity `0 ≤ schurSzegoCompCubicDiscrNumerator n f p` as hypothesis. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hnum : 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
    hn hf hfdeg hpdeg hsplit hnum

/-- Nonzero-core denominator-cleared numerator version of the degree-`≤ 3`
PF-factor Schur--Szego route at a single level `n ≥ 3`. -/
theorem finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hnum : 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoCompositionNonzero_of_pf_factor_le_three_cubicDiscrNumerator_nonneg
    hn hf hf0 hfdeg hp0 hpdeg hsplit hnum

/-- All-level denominator-cleared numerator version of the corrected
degree-`≤ 3` PF-factor Schur--Szego route retaining the left ambient-degree
hypothesis `f.natDegree ≤ n`, taking the pointwise numerator nonnegativity for
levels `n ≥ 3` as hypothesis. -/
theorem finiteSchurSzegoPair_of_leftNatDegree_num_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition_of_pf_factor_le_three_leftNatDegree_num_nonneg
    hf hfdeg hfn hpdeg hsplit hnum

/-- Nonzero-core all-level denominator-cleared numerator version of the
corrected degree-`≤ 3` PF-factor Schur--Szego route retaining the left
ambient-degree hypothesis `f.natDegree ≤ n`. -/
theorem finiteSchurSzegoNonzeroPair_of_leftNatDegree_num_nonneg
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoCompositionNonzero_of_pf_factor_le_three_leftNatDegree_num_nonneg
    hf hf0 hfdeg hfn hp0 hpdeg hsplit hnum

/-- Denominator-cleared numerator version of the degree-`≤ 3` PF-factor
Schur--Szegő route at levels `n ≥ 3`. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_numeratorTarget
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
    hn hf hfdeg hpdeg hsplit (hnum hn hf hfdeg hpdeg hsplit)

/-- Nonzero-core denominator-cleared numerator target version of the
degree-`≤ 3` PF-factor Schur--Szego route at levels `n ≥ 3`. -/
theorem finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_numeratorTarget
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
    hn hf hf0 hfdeg hp0 hpdeg hsplit (hnum hn hf hfdeg hpdeg hsplit)

/-- Corrected denominator-cleared numerator route retaining the original
left ambient-degree hypothesis `f.natDegree ≤ n`.  This uses the checked
degree-`≤ 2` Schur--Szegő base case when `n < 3` and the numerator target when
`3 ≤ n`. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_leftNatDegree_of_numeratorTarget
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegree_num_nonneg
    hf hfdeg hfn hpdeg hsplit
    (fun hn => hnum hn hf hfdeg hpdeg hsplit)

/-- All-level denominator-cleared numerator target version of the corrected
degree-`≤ 3` PF-factor Schur--Szego route retaining the left ambient-degree
hypothesis. -/
theorem finiteSchurSzegoPair_of_leftNatDegree_of_numeratorTarget
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegreeTarget
    (schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget_iff_numerator.2
      hnum)
    hf hfdeg hfn hpdeg hsplit

/-- All-level high-level diagonal-operator target version of the corrected
degree-`≤ 3` PF-factor Schur--Szego route retaining the left ambient-degree
hypothesis. -/
theorem
    finiteSchurSzegoPair_of_leftNatDegree_of_highLevelDiagonalOperatorTarget
    (hdisc :
      schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegreeTarget
    (schurSzegoCompPFFactorHighLevelDiagonalOperatorTarget_iff_leftNatDegree.1
      hdisc)
    hf hfdeg hfn hpdeg hsplit

/-- Nonzero-core all-level denominator-cleared numerator target version of the
corrected degree-`≤ 3` PF-factor Schur--Szego route retaining the left
ambient-degree hypothesis. -/
theorem finiteSchurSzegoNonzeroPair_of_leftNatDegree_of_numeratorTarget
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegree_of_numeratorTarget
    hnum hf hfdeg hfn hpdeg hsplit

/-- Nonzero-core all-level high-level diagonal-operator target version of the
corrected degree-`≤ 3` PF-factor Schur--Szego route retaining the left
ambient-degree hypothesis. -/
theorem
    finiteSchurSzegoNonzeroPair_of_leftNatDegree_of_highLevelDiagonalOperatorTarget
    (hdisc :
      schurSzegoCompPFFactorHighLevelDiagonalOperatorCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegree_of_highLevelDiagonalOperatorTarget
    hdisc hf hfdeg hfn hpdeg hsplit

/-- Low-level plus denominator-cleared numerator version of the degree-`≤ 3`
PF-factor Schur--Szegő route. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_lowLevel_of_numeratorTarget
    (hlow : schurSzegoCompPFFactorLowLevelCubicDiscriminantNonnegTarget)
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_cubicDiscriminantTarget
    (schurSzegoCompPFFactorCubicDiscriminantNonnegTarget_of_lowLevel_of_numerator
      hlow hnum)
    hf hfdeg hpdeg hsplit

/-- Nonzero-core low-level plus denominator-cleared numerator version of the
degree-`≤ 3` PF-factor Schur--Szegő route. -/
theorem finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_lowLevel_of_numeratorTarget
    (hlow : schurSzegoCompPFFactorLowLevelCubicDiscriminantNonnegTarget)
    (hnum : schurSzegoCompPFFactorCubicDiscrNumeratorNonnegTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_lowLevel_of_numeratorTarget
    hlow hnum hf hfdeg hpdeg hsplit

/-- Normalized Jensen-product version of the degree-`≤ 3` PF-factor
Schur--Szegő route. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_jensenProductTarget
    (hdisc : schurSzegoCompPFFactorJensenProductCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_cubicDiscriminantTarget
    (schurSzegoCompPFFactorCubicDiscriminantNonnegTarget_of_jensenProduct
      hdisc)
    hf hfdeg hpdeg hsplit

/-- Nonzero-core normalized Jensen-product version of the degree-`≤ 3`
PF-factor Schur--Szegő route. -/
theorem finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_jensenProductTarget
    (hdisc : schurSzegoCompPFFactorJensenProductCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_jensenProductTarget
    hdisc hf hfdeg hpdeg hsplit

/-- Diagonal-operator version of the degree-`≤ 3` PF-factor Schur--Szegő
route. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_diagonalOperatorTarget
    (hdisc : schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_cubicDiscriminantTarget
    (schurSzegoCompPFFactorCubicDiscriminantNonnegTarget_of_diagonalOperator
      hdisc)
    hf hfdeg hpdeg hsplit

/-- Nonzero-core diagonal-operator version of the degree-`≤ 3` PF-factor
Schur--Szegő route. -/
theorem finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_diagonalOperatorTarget
    (hdisc : schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_diagonalOperatorTarget
    hdisc hf hfdeg hpdeg hsplit

/-- All-level normalized Jensen-product route with the corrected left
ambient-degree interface. -/
theorem finiteSchurSzegoPair_of_leftNatDegree_of_jensenProductTarget
    (hdisc : schurSzegoCompPFFactorJensenProductCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (_hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_jensenProductTarget
    hdisc hf hfdeg hpdeg hsplit

/-- Nonzero-core all-level normalized Jensen-product route with the corrected
left ambient-degree interface. -/
theorem finiteSchurSzegoNonzeroPair_of_leftNatDegree_of_jensenProductTarget
    (hdisc : schurSzegoCompPFFactorJensenProductCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegree_of_jensenProductTarget
    hdisc hf hfdeg hfn hpdeg hsplit

/-- All-level diagonal-operator route with the corrected left ambient-degree
interface. -/
theorem finiteSchurSzegoPair_of_leftNatDegree_of_diagonalOperatorTarget
    (hdisc : schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (_hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_diagonalOperatorTarget
    hdisc hf hfdeg hpdeg hsplit

/-- Nonzero-core all-level diagonal-operator route with the corrected left
ambient-degree interface. -/
theorem finiteSchurSzegoNonzeroPair_of_leftNatDegree_of_diagonalOperatorTarget
    (hdisc : schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegree_of_diagonalOperatorTarget
    hdisc hf hfdeg hfn hpdeg hsplit

/-- All-level corrected normalized Jensen-product route with the corrected
left ambient-degree target as input. -/
theorem
    finiteSchurSzegoPair_of_leftNatDegree_of_jensenProductLeftNatDegreeTarget
    (hdisc :
      schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegreeTarget
    (schurSzegoCompPFFactorLeftNatDegreeTarget_of_jensenProduct hdisc)
    hf hfdeg hfn hpdeg hsplit

/-- Nonzero-core all-level corrected normalized Jensen-product route with the
corrected left ambient-degree target as input. -/
theorem
    finiteSchurSzegoNonzeroPair_of_leftNatDegree_of_jensenProductLeftNatDegreeTarget
    (hdisc :
      schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegree_of_jensenProductLeftNatDegreeTarget
    hdisc hf hfdeg hfn hpdeg hsplit

/-- All-level corrected diagonal-operator route with the corrected left
ambient-degree target as input. -/
theorem
    finiteSchurSzegoPair_of_leftNatDegree_of_diagonalOperatorLeftNatDegreeTarget
    (hdisc :
      schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegreeTarget
    (schurSzegoCompPFFactorLeftNatDegreeTarget_of_diagonalOperator hdisc)
    hf hfdeg hfn hpdeg hsplit

/-- Nonzero-core all-level corrected diagonal-operator route with the corrected
left ambient-degree target as input. -/
theorem
    finiteSchurSzegoNonzeroPair_of_leftNatDegree_of_diagonalOperatorLeftNatDegreeTarget
    (hdisc :
      schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget)
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n) (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegree_of_diagonalOperatorLeftNatDegreeTarget
    hdisc hf hfdeg hfn hpdeg hsplit

/-- High-level corrected cubic-discriminant route for degree-`≤ 3` PF-factors
at levels `n ≥ 3`. -/
theorem finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_leftNatDegreeTarget
    (hdisc : schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegreeTarget
    hdisc hf hfdeg (hfdeg.trans hn) hpdeg hsplit

/-- Nonzero-core high-level corrected cubic-discriminant route for degree-`≤ 3`
PF-factors at levels `n ≥ 3`. -/
theorem
    finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_leftNatDegreeTarget
    (hdisc : schurSzegoCompPFFactorCubicDiscriminantNonnegOfLeftNatDegreeTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_leftNatDegreeTarget
    hdisc hn hf hfdeg hpdeg hsplit

/-- High-level corrected normalized Jensen-product route for degree-`≤ 3`
PF-factors at levels `n ≥ 3`. -/
theorem
    finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_jensenProductLeftNatDegreeTarget
    (hdisc :
      schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegree_of_jensenProductLeftNatDegreeTarget
    hdisc hf hfdeg (hfdeg.trans hn) hpdeg hsplit

/-- Nonzero-core high-level corrected normalized Jensen-product route for
degree-`≤ 3` PF-factors at levels `n ≥ 3`. -/
theorem
    finiteSchurSzegoNonzeroPair_of_pf_factor_natDegree_le_three_of_jensenProductLeftNatDegreeTarget
    (hdisc :
      schurSzegoCompPFFactorJensenProductCubicDiscriminantOfLeftNatDegreeTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_jensenProductLeftNatDegreeTarget
    hdisc hn hf hfdeg hpdeg hsplit

/-- High-level corrected diagonal-operator route for degree-`≤ 3` PF-factors
at levels `n ≥ 3`. -/
theorem
    finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_diagonalOperatorLeftNatDegreeTarget
    (hdisc :
      schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_leftNatDegree_of_diagonalOperatorLeftNatDegreeTarget
    hdisc hf hfdeg (hfdeg.trans hn) hpdeg hsplit

/-- Nonzero-core high-level corrected diagonal-operator route for degree-`≤ 3`
PF-factors at levels `n ≥ 3`. -/
theorem
    finiteSchurSzegoNonzeroPair_of_pf_factor_le_three_of_diagonalOperatorLeftNatDegreeTarget
    (hdisc :
      schurSzegoCompPFFactorDiagonalOperatorCubicDiscriminantOfLeftNatDegreeTarget)
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (_hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ 3)
    (_hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoPair_of_pf_factor_natDegree_le_three_of_diagonalOperatorLeftNatDegreeTarget
    hdisc hn hf hfdeg hpdeg hsplit

/-- Challenge-facing explicit cubic discriminant formula for degree-three
Jensen polynomials. -/
theorem cubicDiscr_jensenPolynomialThree (gamma : ℕ → ℝ) :
    cubicDiscr (jensenPolynomial 3 gamma) =
      27 * (6 * gamma 3 * gamma 2 * gamma 1 * gamma 0
        - 4 * gamma 2 ^ 3 * gamma 0
        + 3 * gamma 2 ^ 2 * gamma 1 ^ 2
        - 4 * gamma 3 * gamma 1 ^ 3
        - gamma 3 ^ 2 * gamma 0 ^ 2) :=
  RealRooted.cubicDiscr_jensenPolynomial_three gamma

/-- Challenge-facing nonnegativity of the cubic discriminant for a degree-three
Jensen polynomial that is zero or splits. -/
theorem cubicDiscr_jensenPolynomialThree_nonneg_of_eq_zero_or_splits
    {gamma : ℕ → ℝ}
    (hs : jensenPolynomial 3 gamma = 0 ∨ (jensenPolynomial 3 gamma).Splits) :
    0 ≤ cubicDiscr (jensenPolynomial 3 gamma) :=
  RealRooted.cubicDiscr_jensenPolynomial_three_nonneg_of_eq_zero_or_splits hs

/-- Challenge-facing nonnegativity of the cubic discriminant for a PF
degree-three Jensen polynomial. -/
theorem cubicDiscr_jensenPolynomialThree_nonneg_of_isPF
    {gamma : ℕ → ℝ}
    (hj : IsPFPolynomial (jensenPolynomial 3 gamma)) :
    0 ≤ cubicDiscr (jensenPolynomial 3 gamma) :=
  hj.cubicDiscr_jensenPolynomial_three_nonneg

/-- Challenge-facing equivalence between nonnegative cubic discriminant and
zero-or-splitting for degree-three Jensen polynomials. -/
theorem cubicDiscr_jensenPolynomialThree_nonneg_iff_eq_zero_or_splits
    {gamma : ℕ → ℝ} :
    0 ≤ cubicDiscr (jensenPolynomial 3 gamma) ↔
      jensenPolynomial 3 gamma = 0 ∨ (jensenPolynomial 3 gamma).Splits :=
  RealRooted.cubicDiscr_jensenPolynomial_three_nonneg_iff_eq_zero_or_splits

/-- Challenge-facing normalized coefficient log-concavity for a splitting
polynomial of degree at most the ambient binomial level. -/
theorem normalizedCoeffLogConcave_of_splits_natDegree_le
    {n : ℕ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) (hs : p.Splits) :
    (p.coeff 0 / (n.choose 0 : ℝ)) * (p.coeff 2 / (n.choose 2 : ℝ)) ≤
        (p.coeff 1 / (n.choose 1 : ℝ)) ^ 2 ∧
      (p.coeff 1 / (n.choose 1 : ℝ)) * (p.coeff 3 / (n.choose 3 : ℝ)) ≤
        (p.coeff 2 / (n.choose 2 : ℝ)) ^ 2 :=
  RealRooted.normalized_coeff_logConcave_of_splits_natDegree_le hpdeg hs

/-- Challenge-facing first adjacent normalized log-concavity inequality for a
splitting polynomial at binomial level `n`. -/
theorem normalizedCoeffLogConcave_left_of_splits_natDegree_le
    {n : ℕ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) (hs : p.Splits) :
    (p.coeff 0 / (n.choose 0 : ℝ)) * (p.coeff 2 / (n.choose 2 : ℝ)) ≤
      (p.coeff 1 / (n.choose 1 : ℝ)) ^ 2 :=
  RealRooted.normalized_coeff_left_logConcave_of_splits_natDegree_le hpdeg hs

/-- Challenge-facing second adjacent normalized log-concavity inequality for a
splitting polynomial at binomial level `n`. -/
theorem normalizedCoeffLogConcave_right_of_splits_natDegree_le
    {n : ℕ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) (hs : p.Splits) :
    (p.coeff 1 / (n.choose 1 : ℝ)) * (p.coeff 3 / (n.choose 3 : ℝ)) ≤
      (p.coeff 2 / (n.choose 2 : ℝ)) ^ 2 :=
  RealRooted.normalized_coeff_right_logConcave_of_splits_natDegree_le hpdeg hs

/-- Challenge-facing nonnegativity of binomially normalized coefficients for a
PF polynomial. -/
theorem normalizedCoeff_nonneg_of_isPF (n : ℕ) {f : ℝ[X]}
    (hf : IsPFPolynomial f) :
    ∀ k, 0 ≤ f.coeff k / (Nat.choose n k : ℝ) :=
  RealRooted.normalized_coeff_nonneg_of_isPF n hf

/-- Challenge-facing constant normalized coefficient nonnegativity for a PF
polynomial at binomial level three. -/
theorem normalizedCoeff_zero_nonneg_of_isPF_three {f : ℝ[X]}
    (hf : IsPFPolynomial f) :
    0 ≤ f.coeff 0 / (Nat.choose 3 0 : ℝ) :=
  RealRooted.normalized_coeff_zero_nonneg_of_isPF_three hf

/-- Challenge-facing linear normalized coefficient nonnegativity for a PF
polynomial at binomial level three. -/
theorem normalizedCoeff_one_nonneg_of_isPF_three {f : ℝ[X]}
    (hf : IsPFPolynomial f) :
    0 ≤ f.coeff 1 / (Nat.choose 3 1 : ℝ) :=
  RealRooted.normalized_coeff_one_nonneg_of_isPF_three hf

/-- Challenge-facing quadratic normalized coefficient nonnegativity for a PF
polynomial at binomial level three. -/
theorem normalizedCoeff_two_nonneg_of_isPF_three {f : ℝ[X]}
    (hf : IsPFPolynomial f) :
    0 ≤ f.coeff 2 / (Nat.choose 3 2 : ℝ) :=
  RealRooted.normalized_coeff_two_nonneg_of_isPF_three hf

/-- Challenge-facing cubic normalized coefficient nonnegativity for a PF
polynomial at binomial level three. -/
theorem normalizedCoeff_three_nonneg_of_isPF_three {f : ℝ[X]}
    (hf : IsPFPolynomial f) :
    0 ≤ f.coeff 3 / (Nat.choose 3 3 : ℝ) :=
  RealRooted.normalized_coeff_three_nonneg_of_isPF_three hf

/-- Challenge-facing normalized coefficient log-concavity for a degree-`≤ 3`
PF polynomial. -/
theorem normalizedCoeffLogConcave_of_isPF_natDegree_le_three
    {f : ℝ[X]} (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3) :
    (f.coeff 0 / (Nat.choose 3 0 : ℝ)) * (f.coeff 2 / (Nat.choose 3 2 : ℝ)) ≤
        (f.coeff 1 / (Nat.choose 3 1 : ℝ)) ^ 2 ∧
      (f.coeff 1 / (Nat.choose 3 1 : ℝ)) * (f.coeff 3 / (Nat.choose 3 3 : ℝ)) ≤
        (f.coeff 2 / (Nat.choose 3 2 : ℝ)) ^ 2 :=
  RealRooted.normalized_coeff_logConcave_of_isPF_natDegree_le_three hf hfdeg

/-- Challenge-facing first adjacent normalized log-concavity inequality for a
degree-`≤ 3` PF polynomial. -/
theorem normalizedCoeffLogConcave_left_of_isPF_natDegree_le_three
    {f : ℝ[X]} (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3) :
    (f.coeff 0 / (Nat.choose 3 0 : ℝ)) * (f.coeff 2 / (Nat.choose 3 2 : ℝ)) ≤
      (f.coeff 1 / (Nat.choose 3 1 : ℝ)) ^ 2 :=
  RealRooted.normalized_coeff_left_logConcave_of_isPF_natDegree_le_three hf hfdeg

/-- Challenge-facing second adjacent normalized log-concavity inequality for a
degree-`≤ 3` PF polynomial. -/
theorem normalizedCoeffLogConcave_right_of_isPF_natDegree_le_three
    {f : ℝ[X]} (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3) :
    (f.coeff 1 / (Nat.choose 3 1 : ℝ)) * (f.coeff 3 / (Nat.choose 3 3 : ℝ)) ≤
      (f.coeff 2 / (Nat.choose 3 2 : ℝ)) ^ 2 :=
  RealRooted.normalized_coeff_right_logConcave_of_isPF_natDegree_le_three hf hfdeg

/-- Challenge-facing PF property of the normalized degree-three Jensen
polynomial associated to a degree-`≤ 3` PF polynomial. -/
theorem jensenPolynomialThree_normalizedCoeff_isPF_of_isPF_natDegree_le_three
    {f : ℝ[X]} (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ 3) :
    IsPFPolynomial
      (jensenPolynomial 3 (fun k => f.coeff k / (Nat.choose 3 k : ℝ))) :=
  hf.jensenPolynomial_normalized_coeff_of_natDegree_le hfdeg

/-- Challenge-facing cubic Newton inequalities for an exact-degree splitting
Jensen polynomial. -/
theorem jensenPolynomialThree_logConcave_of_splits_natDegree_three
    {gamma : ℕ → ℝ}
    (hdeg : (jensenPolynomial 3 gamma).natDegree = 3)
    (hs : (jensenPolynomial 3 gamma).Splits) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  jensenPolynomial_three_logConcave_of_splits_natDegree_three hdeg hs

/-- Challenge-facing cubic log-concavity for a Jensen polynomial that is zero
or splits. -/
theorem jensenPolynomialThree_logConcave_of_eq_zero_or_splits
    {gamma : ℕ → ℝ}
    (hs : jensenPolynomial 3 gamma = 0 ∨ (jensenPolynomial 3 gamma).Splits) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  jensenPolynomial_three_logConcave_of_eq_zero_or_splits hs

/-- Challenge-facing cubic log-concavity inequalities from the PF Jensen
polynomial hypothesis. -/
theorem jensenPolynomialThree_logConcave_of_isPF
    {gamma : ℕ → ℝ}
    (hj : IsPFPolynomial (jensenPolynomial 3 gamma)) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  hj.jensenPolynomial_three_logConcave

/-- Challenge-facing cubic log-concavity necessary condition for finite
multiplier sequences. -/
theorem finiteMultiplierSequenceThree_logConcave
    {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hmult : IsFiniteMultiplierSequence 3 gamma) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  finiteMultiplierSequence_three_logConcave hgamma hmult

/-- Challenge-facing cubic log-concavity necessary condition for finite PF
multiplier sequences. -/
theorem finitePFMultiplierSequenceThree_logConcave
    {gamma : ℕ → ℝ}
    (hmult : IsFinitePFMultiplierSequence 3 gamma) :
    gamma 0 * gamma 2 ≤ gamma 1 ^ 2 ∧
      gamma 1 * gamma 3 ≤ gamma 2 ^ 2 :=
  finitePFMultiplierSequence_three_logConcave hmult

/-! ## Garloff--Wagner and Hurwitz-matrix targets -/

/-- Challenge-facing target for Garloff--Wagner, Theorem 4(b), in the
nonnegative-coefficient proper-position form used by RealRooted. -/
def garloffWagnerNonnegPrecTarget : Prop :=
  ∀ {f g p q : ℝ[X]},
    HasNonnegCoeffs f → HasNonnegCoeffs g → HasNonnegCoeffs p → HasNonnegCoeffs q →
    Prec f g → Prec p q → Prec0 (hadamardProduct f p) (hadamardProduct g q)

/-- Challenge-facing PF-polynomial strict proper-position Garloff--Wagner
target. -/
abbrev garloffWagnerPFPrecTarget : Prop :=
  garloffWagnerHadamardPFPrecStatement

/-- Challenge-facing zero-aware PF-polynomial proper-position
Garloff--Wagner target. -/
abbrev garloffWagnerPFPrec0Target : Prop :=
  garloffWagnerHadamardPFPrec0Statement

/-- Challenge-facing one-polynomial nonnegative real-rooted Hadamard target. -/
abbrev garloffWagnerNonnegRealRootedTarget : Prop :=
  garloffWagnerHadamardNonnegRealRootedStatement

/-- Challenge-facing PF-polynomial Schur--Pólya--Wagner Hadamard target. -/
abbrev schurPolyaWagnerHadamardPFTarget : Prop :=
  schurPolyaWagnerHadamardPFStatement

/-- Challenge-facing Hadamard closure target for the reciprocal-interlacing
cone. -/
abbrev hadamardReciprocalConeClosureTarget : Prop :=
  hadamardReciprocalConeClosureStatement

/-- Challenge-facing Pólya-frequency coefficientwise Hadamard closure target. -/
abbrev polyaFrequencyHadamardCoeffTarget : Prop :=
  polyaFrequencyHadamardCoeffStatement

/-- Challenge-facing target for Garloff--Wagner, Theorem 1, in the
Hurwitz-stability form. -/
abbrev hurwitzStableHadamardTarget : Prop :=
  hadamardPreservesHurwitzStableStatement

/-- Challenge-facing right-half-plane analytic core for Garloff--Wagner,
Theorem 1. -/
abbrev rightHalfPlaneStableHadamardTarget : Prop :=
  hadamardPreservesRightHalfPlaneStableStatement

/-- Challenge-facing matrix Hadamard target for Hurwitz matrices. -/
abbrev hurwitzMatrixHadamardTarget : Prop :=
  hadamardPreservesHurwitzMatrixTNStatement

/-- Challenge-facing pure Hurwitz Schur-product target. -/
abbrev hurwitzSchurTarget : Prop :=
  HurwitzMatrixSchurProductTNStatement

/-- Challenge-facing low-order Hurwitz Schur-product target through size
`3`. -/
abbrev hurwitzSchurLeThreeTarget : Prop :=
  HurwitzMatrixSchurProductDetLeThreeStatement

/-- Challenge-facing isolated in-band `3 x 3` Hurwitz Schur-product target. -/
abbrev hurwitzSchurInBandTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeInBandStatement

/-- Challenge-facing triangular-free `3 x 3` Hurwitz Schur-product target. -/
abbrev hurwitzSchurTriangularFreeTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreStatement

/-- Challenge-facing fully in-band top-right subcase of the triangular-free
`3 x 3` target. -/
abbrev hurwitzSchurFullBandTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement

/-- Challenge-facing Pólya-frequency target for the column-zero sequences.

This is the Hurwitz-specific leaf exposed by the staircase/Toeplitz normal
form: for two totally nonnegative Hurwitz matrices, the pointwise product of
their column-zero sequences should be Pólya-frequency. -/
abbrev hurwitzColumnZeroProductPFTarget : Prop :=
  ∀ {a b : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    (hurwitz b).IsTotallyNonneg →
    IsPolyaFreqSeq (fun k => hurwitz a k 0 * hurwitz b k 0)

/-- Challenge-facing even-column Toeplitz target for the column-zero product
sequence.  This is the sharper leaf that the fully in-band Hurwitz staircase
actually needs; it is weaker than full Pólya-frequency of the column-zero
product sequence. -/
abbrev hurwitzColumnZeroProductEvenColToeplitzTarget : Prop :=
  HurwitzColumnZeroProductEvenColToeplitzStatement

/-- Challenge-facing Hurwitz normal form of the even-column Toeplitz leaf. -/
abbrev hurwitzMulTotallyNonnegTarget : Prop :=
  HurwitzMulTotallyNonnegStatement

/-- The column-zero product Pólya-frequency leaf is false.  It was only a
sufficient route to the full-band Hurwitz Schur-product target, not a valid
consequence of total nonnegativity of the two Hurwitz matrices. -/
theorem not_hurwitzColumnZeroProductPFTarget :
    ¬ hurwitzColumnZeroProductPFTarget :=
  not_hurwitzColumnZeroProductPF

/-- Challenge-facing corner-zeroed determinant subtarget for the fully in-band
top-right subcase of the triangular-free `3 x 3` target. -/
abbrev hurwitzSchurFullBandCornerZeroedTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedStatement

/-- Challenge-facing single-matrix determinant subtarget for the fully in-band
corner-zeroed `3 x 3` target. -/
abbrev hurwitzSchurFullBandCornerZeroedSingleTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement

/-- Challenge-facing column-normalized form of the single-matrix determinant
subtarget for the fully in-band corner-zeroed `3 x 3` target. -/
abbrev hurwitzSchurFullBandCornerZeroedSingleColZeroTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement

/-- Challenge-facing first-column normal form of the single-matrix determinant
subtarget for the fully in-band corner-zeroed `3 x 3` target. -/
abbrev hurwitzSchurFullBandCornerZeroedSingleFirstColTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement

/-- Challenge-facing strict-remainder branch of the first-column normal form. -/
abbrev hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget :
    Prop :=
  HurwitzMatrixSchurProductDetFirstColPositiveRemainderStatement

/-- Challenge-facing corner-zero top-right subcase of the triangular-free
`3 x 3` target. -/
abbrev hurwitzSchurCornerZeroTarget : Prop :=
  HurwitzMatrixSchurProductDetFinThreeCoreCornerZeroStatement

/-- Challenge-facing low-order Hurwitz-matrix Hadamard target through size
`3`. -/
abbrev hurwitzMatrixHadamardLeThreeTarget : Prop :=
  hadamardPreservesHurwitzMatrixTNDetLeThreeStatement

/-- Challenge-facing odd/even PF consequence of the Hurwitz-matrix Hadamard
target. -/
abbrev hurwitzMatrixHadamardOddEvenPFTarget : Prop :=
  hadamardPreservesHurwitzMatrixOddEvenPFStatement

/-- Challenge-facing odd-coefficient PF consequence of the Hurwitz-matrix
Hadamard target. -/
abbrev hurwitzMatrixHadamardOddCoeffPFTarget : Prop :=
  ∀ {a b : ℝ[X]},
    (hurwitz a.coeff).IsTotallyNonneg →
    (hurwitz b.coeff).IsTotallyNonneg →
    IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n + 1))

/-- Challenge-facing even-coefficient PF consequence of the Hurwitz-matrix
Hadamard target. -/
abbrev hurwitzMatrixHadamardEvenCoeffPFTarget : Prop :=
  ∀ {a b : ℝ[X]},
    (hurwitz a.coeff).IsTotallyNonneg →
    (hurwitz b.coeff).IsTotallyNonneg →
    IsPolyaFreqSeq (fun n => (hadamardProduct a b).coeff (2 * n))

/-- The full Hurwitz Schur-product target implies the matrix Hadamard target. -/
theorem hurwitzMatrixHadamardTarget_of_hurwitzSchur
    (_h : hurwitzSchurTarget) :
    hurwitzMatrixHadamardTarget :=
  hadamardPreservesHurwitzMatrixTN_of_schur

/-- Challenge-facing equivalence between Garloff--Wagner Theorem 1 and its
right-half-plane analytic core. -/
theorem hurwitzStableHadamardTarget_iff_rightHalfPlaneStableHadamardTarget :
    hurwitzStableHadamardTarget ↔ rightHalfPlaneStableHadamardTarget :=
  hadamardPreservesHurwitzStable_iff_rightHalfPlane

/-- Challenge-facing route from the right-half-plane analytic core to
Garloff--Wagner Theorem 1. -/
theorem hurwitzStableHadamardTarget_of_rightHalfPlane
    (h : rightHalfPlaneStableHadamardTarget) :
    hurwitzStableHadamardTarget :=
  hurwitzStableHadamardTarget_iff_rightHalfPlaneStableHadamardTarget.2 h

/-- Challenge-facing reduction from Garloff--Wagner Theorem 1 to its
right-half-plane analytic core. -/
theorem rightHalfPlaneStableHadamardTarget_of_hurwitzStable
    (h : hurwitzStableHadamardTarget) :
    rightHalfPlaneStableHadamardTarget :=
  hurwitzStableHadamardTarget_iff_rightHalfPlaneStableHadamardTarget.1 h

/-- Challenge-facing equivalence between Garloff--Wagner Theorem 1 and the
Hurwitz-matrix Hadamard leaf, modulo both directions of the Hurwitz-matrix
criterion. -/
theorem hurwitzStableHadamardTarget_iff_matrixHadamardTarget
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    hurwitzStableHadamardTarget ↔ hurwitzMatrixHadamardTarget :=
  hadamardPreservesHurwitzStable_iff_matrixTN hFwd hBwd

/-- Challenge-facing equivalence between the right-half-plane analytic core and
the Hurwitz-matrix Hadamard leaf, modulo both directions of the Hurwitz-matrix
criterion. -/
theorem rightHalfPlaneStableHadamardTarget_iff_matrixHadamardTarget
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    rightHalfPlaneStableHadamardTarget ↔ hurwitzMatrixHadamardTarget :=
  hadamardPreservesRightHalfPlaneStable_iff_matrixTN hFwd hBwd

/-- Challenge-facing Hurwitz-stability target through the Hurwitz-matrix
Hadamard route and both directions of the Hurwitz-matrix criterion. -/
theorem hurwitzStableHadamardTarget_of_matrixRoute
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    hurwitzStableHadamardTarget :=
  (hurwitzStableHadamardTarget_iff_matrixHadamardTarget hFwd hBwd).2 hMatHad

/-- Challenge-facing right-half-plane analytic target through the
Hurwitz-matrix Hadamard route and both directions of the Hurwitz-matrix
criterion. -/
theorem rightHalfPlaneStableHadamardTarget_of_matrixRoute
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    rightHalfPlaneStableHadamardTarget :=
  (rightHalfPlaneStableHadamardTarget_iff_matrixHadamardTarget hFwd hBwd).2 hMatHad

/-- Challenge-facing Hurwitz-stability target from the pure Hurwitz
Schur-product core and both directions of the Hurwitz-matrix criterion. -/
theorem hurwitzStableHadamardTarget_of_hurwitzSchur
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (_hSchur : hurwitzSchurTarget)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    hurwitzStableHadamardTarget :=
  hadamardPreservesHurwitzStable_of_hurwitzSchur hFwd hBwd

/-- Challenge-facing right-half-plane analytic target from the pure Hurwitz
Schur-product core and both directions of the Hurwitz-matrix criterion. -/
theorem rightHalfPlaneStableHadamardTarget_of_hurwitzSchur
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (_hSchur : hurwitzSchurTarget)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    rightHalfPlaneStableHadamardTarget :=
  hadamardPreservesRightHalfPlaneStable_of_hurwitzSchur hFwd hBwd

/-- Challenge-facing matrix Hadamard target from Garloff--Wagner Theorem 1
plus the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hurwitzMatrixHadamardTarget_of_stableRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hurwitzMatrixHadamardTarget :=
  hadamardPreservesHurwitzMatrixTN_of_stableRoute hBwd hThm1 hFwd

/-- Challenge-facing matrix Hadamard target from the right-half-plane analytic
core plus the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hurwitzMatrixHadamardTarget_of_rightHalfPlaneRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : rightHalfPlaneStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hurwitzMatrixHadamardTarget :=
  hadamardPreservesHurwitzMatrixTN_of_rightHalfPlaneRoute hBwd hRHP hFwd

/-- The matrix Hadamard target implies its odd/even PF consequence. -/
theorem hurwitzMatrixHadamardOddEvenPFTarget_of_matrixHadamard
    (h : hurwitzMatrixHadamardTarget) :
    hurwitzMatrixHadamardOddEvenPFTarget :=
  hadamardPreservesHurwitzMatrixOddEvenPF_of_matrixTN h

/-- The bundled odd/even PF consequence implies the odd-coefficient PF leaf. -/
theorem hurwitzMatrixHadamardOddCoeffPFTarget_of_oddEvenPF
    (h : hurwitzMatrixHadamardOddEvenPFTarget) :
    hurwitzMatrixHadamardOddCoeffPFTarget :=
  fun ha hb => (h ha hb).1

/-- The bundled odd/even PF consequence implies the even-coefficient PF leaf. -/
theorem hurwitzMatrixHadamardEvenCoeffPFTarget_of_oddEvenPF
    (h : hurwitzMatrixHadamardOddEvenPFTarget) :
    hurwitzMatrixHadamardEvenCoeffPFTarget :=
  fun ha hb => (h ha hb).2

/-- The matrix Hadamard target implies the odd-coefficient PF leaf. -/
theorem hurwitzMatrixHadamardOddCoeffPFTarget_of_matrixHadamard
    (h : hurwitzMatrixHadamardTarget) :
    hurwitzMatrixHadamardOddCoeffPFTarget :=
  hadamardProduct_oddCoeff_isPolyaFreqSeq_of_matrixTN h

/-- The matrix Hadamard target implies the even-coefficient PF leaf. -/
theorem hurwitzMatrixHadamardEvenCoeffPFTarget_of_matrixHadamard
    (h : hurwitzMatrixHadamardTarget) :
    hurwitzMatrixHadamardEvenCoeffPFTarget :=
  hadamardProduct_evenCoeff_isPolyaFreqSeq_of_matrixTN h

/-- The full Hurwitz Schur-product target implies the odd/even PF consequence
for Hadamard products. -/
theorem hurwitzMatrixHadamardOddEvenPFTarget_of_hurwitzSchur
    (_h : hurwitzSchurTarget) :
    hurwitzMatrixHadamardOddEvenPFTarget :=
  hadamardPreservesHurwitzMatrixOddEvenPF_of_schur

/-- The full Hurwitz Schur-product target implies the odd-coefficient PF leaf. -/
theorem hurwitzMatrixHadamardOddCoeffPFTarget_of_hurwitzSchur
    (h : hurwitzSchurTarget) :
    hurwitzMatrixHadamardOddCoeffPFTarget :=
  hurwitzMatrixHadamardOddCoeffPFTarget_of_matrixHadamard
    (hurwitzMatrixHadamardTarget_of_hurwitzSchur h)

/-- The full Hurwitz Schur-product target implies the even-coefficient PF leaf. -/
theorem hurwitzMatrixHadamardEvenCoeffPFTarget_of_hurwitzSchur
    (h : hurwitzSchurTarget) :
    hurwitzMatrixHadamardEvenCoeffPFTarget :=
  hurwitzMatrixHadamardEvenCoeffPFTarget_of_matrixHadamard
    (hurwitzMatrixHadamardTarget_of_hurwitzSchur h)

/-- Challenge-facing odd/even PF consequence from Garloff--Wagner Theorem 1
plus the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hurwitzMatrixHadamardOddEvenPFTarget_of_stableRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hurwitzMatrixHadamardOddEvenPFTarget :=
  hadamardPreservesHurwitzMatrixOddEvenPF_of_stableRoute hBwd hThm1 hFwd

/-- Challenge-facing odd-coefficient PF consequence from Garloff--Wagner
Theorem 1 plus the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hurwitzMatrixHadamardOddCoeffPFTarget_of_stableRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hurwitzMatrixHadamardOddCoeffPFTarget :=
  fun ha hb =>
    (hurwitzMatrixHadamardOddEvenPFTarget_of_stableRoute hBwd hThm1 hFwd ha hb).1

/-- Challenge-facing even-coefficient PF consequence from Garloff--Wagner
Theorem 1 plus the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hurwitzMatrixHadamardEvenCoeffPFTarget_of_stableRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hurwitzMatrixHadamardEvenCoeffPFTarget :=
  fun ha hb =>
    (hurwitzMatrixHadamardOddEvenPFTarget_of_stableRoute hBwd hThm1 hFwd ha hb).2

/-- Challenge-facing odd/even PF consequence from the right-half-plane
analytic core plus the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hurwitzMatrixHadamardOddEvenPFTarget_of_rightHalfPlaneRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : rightHalfPlaneStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hurwitzMatrixHadamardOddEvenPFTarget :=
  hadamardPreservesHurwitzMatrixOddEvenPF_of_rightHalfPlaneRoute hBwd hRHP hFwd

/-- Challenge-facing odd-coefficient PF consequence from the right-half-plane
analytic core plus the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hurwitzMatrixHadamardOddCoeffPFTarget_of_rightHalfPlaneRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : rightHalfPlaneStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hurwitzMatrixHadamardOddCoeffPFTarget :=
  fun ha hb =>
    (hurwitzMatrixHadamardOddEvenPFTarget_of_rightHalfPlaneRoute hBwd hRHP hFwd ha hb).1

/-- Challenge-facing even-coefficient PF consequence from the right-half-plane
analytic core plus the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hurwitzMatrixHadamardEvenCoeffPFTarget_of_rightHalfPlaneRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : rightHalfPlaneStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hurwitzMatrixHadamardEvenCoeffPFTarget :=
  fun ha hb =>
    (hurwitzMatrixHadamardOddEvenPFTarget_of_rightHalfPlaneRoute hBwd hRHP hFwd ha hb).2

/-- The triangular-free `3 x 3` target is equivalent to the conjunction of
the full-band and corner-zero top-right subcases. -/
theorem hurwitzSchurTriangularFreeTarget_iff_fullBand_cornerZero :
    hurwitzSchurTriangularFreeTarget ↔
      hurwitzSchurFullBandTarget ∧ hurwitzSchurCornerZeroTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_iff_fullBand_cornerZero

/-- Since the corner-zero subcase is proved, the triangular-free `3 x 3` target
is equivalent to the fully in-band top-right subcase. -/
theorem hurwitzSchurTriangularFreeTarget_iff_fullBand :
    hurwitzSchurTriangularFreeTarget ↔ hurwitzSchurFullBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_iff_fullBand

/-- Challenge-facing equivalence between the isolated in-band `3 x 3` target
and its triangular-free refinement. -/
theorem hurwitzSchurInBandTarget_iff_triangularFree :
    hurwitzSchurInBandTarget ↔ hurwitzSchurTriangularFreeTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_iff_core

/-- Challenge-facing equivalence between the low-order size-`≤ 3` Hurwitz
Schur-product target and the isolated in-band `3 x 3` target. -/
theorem hurwitzSchurLeThreeTarget_iff_inBand :
    hurwitzSchurLeThreeTarget ↔ hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetLeThree_iff_inBand

/-- The isolated in-band `3 x 3` target is equivalent to the full-band
top-right subcase, since the corner-zero subcase is proved. -/
theorem hurwitzSchurInBandTarget_iff_fullBand :
    hurwitzSchurInBandTarget ↔ hurwitzSchurFullBandTarget :=
  hurwitzSchurInBandTarget_iff_triangularFree.trans
    hurwitzSchurTriangularFreeTarget_iff_fullBand

/-- The low-order size-`≤ 3` target is equivalent to the full-band top-right
subcase. -/
theorem hurwitzSchurLeThreeTarget_iff_fullBand :
    hurwitzSchurLeThreeTarget ↔ hurwitzSchurFullBandTarget :=
  hurwitzSchurLeThreeTarget_iff_inBand.trans
    hurwitzSchurInBandTarget_iff_fullBand

/-- Challenge-facing reduction from the triangular-free `3 x 3` target back to
the full-band top-right subcase. -/
theorem hurwitzSchurFullBandTarget_of_triangularFree
    (h : hurwitzSchurTriangularFreeTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzSchurTriangularFreeTarget_iff_fullBand.1 h

/-- Challenge-facing reduction from the isolated in-band `3 x 3` target back to
the full-band top-right subcase. -/
theorem hurwitzSchurFullBandTarget_of_inBand
    (h : hurwitzSchurInBandTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzSchurInBandTarget_iff_fullBand.1 h

/-- Challenge-facing reduction from the low-order size-`≤ 3` target back to the
full-band top-right subcase. -/
theorem hurwitzSchurFullBandTarget_of_leThree
    (h : hurwitzSchurLeThreeTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzSchurLeThreeTarget_iff_fullBand.1 h

/-- Challenge-facing low-order consequence of the full Hurwitz Schur-product
target. -/
theorem hurwitzSchurLeThreeTarget_of_hurwitzSchur
    (_h : hurwitzSchurTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_schurProductTN

/-- Challenge-facing in-band `3 x 3` consequence of the full Hurwitz
Schur-product target. -/
theorem hurwitzSchurInBandTarget_of_hurwitzSchur
    (_h : hurwitzSchurTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_schurProductTN

/-- Challenge-facing reduction from the column-zero Pólya-frequency leaf to the
fully in-band `3 x 3` Hurwitz Schur-product target. -/
theorem hurwitzSchurFullBandTarget_of_columnZeroProductPF
    (hPF : hurwitzColumnZeroProductPFTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_polyaFreq hPF

/-- Challenge-facing reduction from the column-zero Pólya-frequency leaf to the
isolated in-band `3 x 3` Hurwitz Schur-product target. -/
theorem hurwitzSchurInBandTarget_of_columnZeroProductPF
    (hPF : hurwitzColumnZeroProductPFTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_polyaFreq hPF

/-- Challenge-facing reduction from the column-zero Pólya-frequency leaf to the
low-order size-`≤ 3` Hurwitz Schur-product target. -/
theorem hurwitzSchurLeThreeTarget_of_columnZeroProductPF
    (hPF : hurwitzColumnZeroProductPFTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_polyaFreq hPF

/-- Challenge-facing implication from the full column-zero Pólya-frequency leaf
to the sharper even-column Toeplitz leaf. -/
theorem hurwitzColumnZeroProductEvenColToeplitzTarget_of_columnZeroProductPF
    (hPF : hurwitzColumnZeroProductPFTarget) :
    hurwitzColumnZeroProductEvenColToeplitzTarget :=
  hurwitzColumnZeroProductEvenColToeplitz_of_polyaFreq hPF

/-- Challenge-facing reduction from the Hurwitz normal-form leaf to the
even-column Toeplitz leaf. -/
theorem hurwitzColumnZeroProductEvenColToeplitzTarget_of_hurwitzMul
    (h : hurwitzMulTotallyNonnegTarget) :
    hurwitzColumnZeroProductEvenColToeplitzTarget :=
  hurwitzColumnZeroProductEvenColToeplitz_of_hurwitzMul h

/-- Challenge-facing reduction from the even-column Toeplitz leaf to the
Hurwitz normal-form leaf. -/
theorem hurwitzMulTotallyNonnegTarget_of_evenColToeplitz
    (h : hurwitzColumnZeroProductEvenColToeplitzTarget) :
    hurwitzMulTotallyNonnegTarget :=
  hurwitzMul_of_hurwitzColumnZeroProductEvenColToeplitz h

/-- Challenge-facing reduction from the even-column Toeplitz leaf to the fully
in-band `3 x 3` Hurwitz Schur-product target. -/
theorem hurwitzSchurFullBandTarget_of_evenColToeplitz
    (hEven : hurwitzColumnZeroProductEvenColToeplitzTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_evenColToeplitz hEven

/-- Challenge-facing reduction from the Hurwitz normal-form leaf to the fully
in-band `3 x 3` Hurwitz Schur-product target. -/
theorem hurwitzSchurFullBandTarget_of_hurwitzMul
    (h : hurwitzMulTotallyNonnegTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzSchurFullBandTarget_of_evenColToeplitz
    (hurwitzColumnZeroProductEvenColToeplitzTarget_of_hurwitzMul h)

/-- Challenge-facing unconditional size-`≤ 2` part of the even-column Toeplitz
leaf.  The remaining size-`3` slice is the genuine Garloff-Wagner content of
issue #34. -/
theorem hurwitzColumnZeroProductEvenColToeplitzTarget_size_le_two
    {a b : ℕ → ℝ}
    (ha : (hurwitz a).IsTotallyNonneg) (hb : (hurwitz b).IsTotallyNonneg)
    {n : ℕ} (hn : n ≤ 2) {rows cols : Fin n → ℕ}
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 ≤ ((toeplitz (fun k => hurwitz a k 0 * hurwitz b k 0)).submatrix rows
        (fun j => 2 * cols j)).det :=
  hurwitzColumnZeroProductEvenColToeplitz_of_size_le_two ha hb hn hrows hcols

/-- Challenge-facing reduction from the even-column Toeplitz leaf to the
isolated in-band `3 x 3` Hurwitz Schur-product target. -/
theorem hurwitzSchurInBandTarget_of_evenColToeplitz
    (hEven : hurwitzColumnZeroProductEvenColToeplitzTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_evenColToeplitz hEven

/-- Challenge-facing reduction from the Hurwitz normal-form leaf to the
isolated in-band `3 x 3` Hurwitz Schur-product target. -/
theorem hurwitzSchurInBandTarget_of_hurwitzMul
    (h : hurwitzMulTotallyNonnegTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_fullBand
    (hurwitzSchurFullBandTarget_of_hurwitzMul h)

/-- Challenge-facing reduction from the even-column Toeplitz leaf to the
low-order size-`≤ 3` Hurwitz Schur-product target. -/
theorem hurwitzSchurLeThreeTarget_of_evenColToeplitz
    (hEven : hurwitzColumnZeroProductEvenColToeplitzTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_evenColToeplitz hEven

/-- Challenge-facing reduction from the Hurwitz normal-form leaf to the
low-order size-`≤ 3` Hurwitz Schur-product target. -/
theorem hurwitzSchurLeThreeTarget_of_hurwitzMul
    (h : hurwitzMulTotallyNonnegTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_fullBand
    (hurwitzSchurFullBandTarget_of_hurwitzMul h)

/-- Challenge-facing theorem discharging the corner-zero top-right subcase. -/
theorem hurwitzSchurCornerZeroTarget_proved :
    hurwitzSchurCornerZeroTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreCornerZero

/-- Challenge-facing reduction from the corner-zeroed full-band subtarget to
the fully in-band top-right subcase. -/
theorem hurwitzSchurFullBandTarget_of_cornerZeroed
    (h : hurwitzSchurFullBandCornerZeroedTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroed h

/-- Challenge-facing reduction from the single-matrix corner-zeroed determinant
subtarget to the two-matrix corner-zeroed full-band subtarget. -/
theorem hurwitzSchurFullBandCornerZeroedTarget_of_single
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurFullBandCornerZeroedTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroed_of_single h

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the general single-matrix leaf. -/
theorem hurwitzSchurFullBandCornerZeroedSingleTarget_of_colZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurFullBandCornerZeroedSingleTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle_of_colZero h

/-- Challenge-facing specialization from the general single-matrix leaf to the
column-normalized single-matrix leaf. -/
theorem hurwitzSchurFullBandCornerZeroedSingleColZeroTarget_of_single
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurFullBandCornerZeroedSingleColZeroTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_single
    h

/-- Challenge-facing reduction from the first-column normal form to the
column-normalized single-matrix leaf. -/
theorem hurwitzSchurFullBandCornerZeroedSingleColZeroTarget_of_firstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzSchurFullBandCornerZeroedSingleColZeroTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_firstCol
    h

/-- Challenge-facing specialization from the column-normalized single-matrix
leaf to the first-column normal form. -/
theorem hurwitzSchurFullBandCornerZeroedSingleFirstColTarget_of_colZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurFullBandCornerZeroedSingleFirstColTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_colZero
    h

/-- Challenge-facing specialization from the general single-matrix leaf to the
first-column normal form. -/
theorem hurwitzSchurFullBandCornerZeroedSingleFirstColTarget_of_single
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurFullBandCornerZeroedSingleFirstColTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_single
    h

/-- Challenge-facing reduction from the strict-remainder branch to the
first-column normal form. -/
theorem hurwitzSchurFullBandCornerZeroedSingleFirstColTarget_of_positiveRemainder
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget) :
    hurwitzSchurFullBandCornerZeroedSingleFirstColTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_positiveRemainder
    h

/-- Challenge-facing reduction from the strict-remainder branch to the
column-normalized single-matrix leaf. -/
theorem hurwitzSchurFullBandCornerZeroedSingleColZeroTarget_of_positiveRemainder
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget) :
    hurwitzSchurFullBandCornerZeroedSingleColZeroTarget :=
  hurwitzSchurFullBandCornerZeroedSingleColZeroTarget_of_firstCol
    (hurwitzSchurFullBandCornerZeroedSingleFirstColTarget_of_positiveRemainder h)

/-- Challenge-facing disproof of the first-column normal form: this branch is
too strong and should not be used as a route to the two-matrix #34 target. -/
theorem not_hurwitzSchurFullBandCornerZeroedSingleFirstColTarget :
    ¬ hurwitzSchurFullBandCornerZeroedSingleFirstColTarget :=
  not_hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol

/-- The column-normalized single-matrix leaf is false, since it specializes to
the false first-column normal form. -/
theorem not_hurwitzSchurFullBandCornerZeroedSingleColZeroTarget :
    ¬ hurwitzSchurFullBandCornerZeroedSingleColZeroTarget :=
  not_hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero

/-- The general single-matrix corner-zeroed leaf is false, since it specializes
to the false first-column normal form. -/
theorem not_hurwitzSchurFullBandCornerZeroedSingleTarget :
    ¬ hurwitzSchurFullBandCornerZeroedSingleTarget :=
  not_hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle

/-- The strict-remainder branch is also false, since it implies the false
first-column normal form. -/
theorem not_hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget :
    ¬ hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget :=
  fun h => not_hurwitzSchurFullBandCornerZeroedSingleFirstColTarget
    (hurwitzSchurFullBandCornerZeroedSingleFirstColTarget_of_positiveRemainder h)

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the two-matrix corner-zeroed full-band subtarget. -/
theorem hurwitzSchurFullBandCornerZeroedTarget_of_singleColZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurFullBandCornerZeroedTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroed_of_singleColZero h

/-- Challenge-facing reduction from the first-column normal form to the
two-matrix corner-zeroed full-band subtarget. -/
theorem hurwitzSchurFullBandCornerZeroedTarget_of_singleFirstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzSchurFullBandCornerZeroedTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroed_of_singleFirstCol h

/-- Challenge-facing reduction from the strict-remainder branch to the
two-matrix corner-zeroed full-band subtarget. -/
theorem hurwitzSchurFullBandCornerZeroedTarget_of_positiveRemainder
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget) :
    hurwitzSchurFullBandCornerZeroedTarget :=
  hurwitzSchurFullBandCornerZeroedTarget_of_singleFirstCol
    (hurwitzSchurFullBandCornerZeroedSingleFirstColTarget_of_positiveRemainder h)

/-- Challenge-facing reduction from the single-matrix corner-zeroed determinant
subtarget to the fully in-band top-right subcase. -/
theorem hurwitzSchurFullBandTarget_of_cornerZeroedSingle
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroedSingle h

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the fully in-band top-right subcase. -/
theorem hurwitzSchurFullBandTarget_of_cornerZeroedSingleColZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroedSingleColZero h

/-- Challenge-facing reduction from the first-column normal form to the fully
in-band top-right subcase. -/
theorem hurwitzSchurFullBandTarget_of_cornerZeroedSingleFirstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroedSingleFirstCol h

/-- Challenge-facing reduction from the strict-remainder branch to the fully
in-band top-right subcase. -/
theorem hurwitzSchurFullBandTarget_of_positiveRemainder
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget) :
    hurwitzSchurFullBandTarget :=
  hurwitzSchurFullBandTarget_of_cornerZeroedSingleFirstCol
    (hurwitzSchurFullBandCornerZeroedSingleFirstColTarget_of_positiveRemainder h)

/-- Challenge-facing reduction from the two top-right subcases to the
triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_fullBand_cornerZero
    (hF : hurwitzSchurFullBandTarget)
    (hZ : hurwitzSchurCornerZeroTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_fullBand_cornerZero hF hZ

/-- Since the corner-zero subcase is proved, the triangular-free `3 x 3` target
now reduces to the fully in-band top-right subcase alone. -/
theorem hurwitzSchurTriangularFreeTarget_of_fullBand
    (hF : hurwitzSchurFullBandTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_fullBand hF

/-- Challenge-facing reduction from the column-zero Pólya-frequency leaf to
the triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_columnZeroProductPF
    (hPF : hurwitzColumnZeroProductPFTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzSchurTriangularFreeTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_columnZeroProductPF hPF)

/-- Challenge-facing reduction from the even-column Toeplitz leaf to the
triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_evenColToeplitz
    (hEven : hurwitzColumnZeroProductEvenColToeplitzTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzSchurTriangularFreeTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_evenColToeplitz hEven)

/-- Challenge-facing reduction from the Hurwitz normal-form leaf to the
triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_hurwitzMul
    (h : hurwitzMulTotallyNonnegTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzSchurTriangularFreeTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_hurwitzMul h)

/-- Challenge-facing reduction from the corner-zeroed full-band subtarget to
the triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_fullBandCornerZeroed
    (h : hurwitzSchurFullBandCornerZeroedTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzSchurTriangularFreeTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_cornerZeroed h)

/-- Challenge-facing reduction from the single-matrix corner-zeroed determinant
subtarget to the triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_cornerZeroedSingle
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_cornerZeroedSingle h

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_cornerZeroedSingleColZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_cornerZeroedSingleColZero h

/-- Challenge-facing reduction from the first-column normal form to the
triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_cornerZeroedSingleFirstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_cornerZeroedSingleFirstCol h

/-- Challenge-facing reduction from the strict-remainder branch to the
triangular-free `3 x 3` target. -/
theorem hurwitzSchurTriangularFreeTarget_of_positiveRemainder
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget) :
    hurwitzSchurTriangularFreeTarget :=
  hurwitzSchurTriangularFreeTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_positiveRemainder h)

/-- Challenge-facing reduction from the two top-right subcases to the isolated
in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_fullBand_cornerZero
    (hF : hurwitzSchurFullBandTarget)
    (hZ : hurwitzSchurCornerZeroTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_core
    (hurwitzSchurTriangularFreeTarget_of_fullBand_cornerZero hF hZ)

/-- Challenge-facing reduction from the fully in-band top-right subcase alone to
the isolated in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_fullBand
    (hF : hurwitzSchurFullBandTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_fullBand hF

/-- Challenge-facing reduction from the corner-zeroed full-band subtarget to
the isolated in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_fullBandCornerZeroed
    (h : hurwitzSchurFullBandCornerZeroedTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzSchurInBandTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_cornerZeroed h)

/-- Challenge-facing reduction from the single-matrix corner-zeroed determinant
subtarget to the isolated in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_cornerZeroedSingle
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingle h

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the isolated in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_cornerZeroedSingleColZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingleColZero h

/-- Challenge-facing reduction from the first-column normal form to the
isolated in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_cornerZeroedSingleFirstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingleFirstCol h

/-- Challenge-facing reduction from the strict-remainder branch to the isolated
in-band `3 x 3` target. -/
theorem hurwitzSchurInBandTarget_of_positiveRemainder
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget) :
    hurwitzSchurInBandTarget :=
  hurwitzSchurInBandTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_positiveRemainder h)

/-- Challenge-facing reduction from the two top-right subcases to the
low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_fullBand_cornerZero
    (hF : hurwitzSchurFullBandTarget)
    (hZ : hurwitzSchurCornerZeroTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_core
    (hurwitzSchurTriangularFreeTarget_of_fullBand_cornerZero hF hZ)

/-- Challenge-facing reduction from the fully in-band top-right subcase alone to
the low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_fullBand
    (hF : hurwitzSchurFullBandTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_fullBand hF

/-- Challenge-facing reduction from the corner-zeroed full-band subtarget to
the low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_fullBandCornerZeroed
    (h : hurwitzSchurFullBandCornerZeroedTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzSchurLeThreeTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_cornerZeroed h)

/-- Challenge-facing reduction from the single-matrix corner-zeroed determinant
subtarget to the low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_cornerZeroedSingle
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_cornerZeroedSingle h

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_cornerZeroedSingleColZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_cornerZeroedSingleColZero h

/-- Challenge-facing reduction from the first-column normal form to the
low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_cornerZeroedSingleFirstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzMatrixSchurProductDetLeThree_of_cornerZeroedSingleFirstCol h

/-- Challenge-facing reduction from the strict-remainder branch to the
low-order Hurwitz Schur-product target through size `3`. -/
theorem hurwitzSchurLeThreeTarget_of_positiveRemainder
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget) :
    hurwitzSchurLeThreeTarget :=
  hurwitzSchurLeThreeTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_positiveRemainder h)

/-- Challenge-facing reduction from the two top-right subcases to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_fullBand_cornerZero
    (hF : hurwitzSchurFullBandTarget)
    (hZ : hurwitzSchurCornerZeroTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand
    (hurwitzSchurInBandTarget_of_fullBand_cornerZero hF hZ)

/-- Challenge-facing reduction from the isolated in-band `3 x 3` target to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_inBand
    (h : hurwitzSchurInBandTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_inBand h

/-- Challenge-facing reduction from the low-order size-`≤ 3` Hurwitz
Schur-product target to the low-order Hurwitz-matrix Hadamard target. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_hurwitzSchurLeThree
    (h : hurwitzSchurLeThreeTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_hurwitzLeThree h

/-- Challenge-facing low-order Hurwitz-matrix Hadamard consequence of the full
Hurwitz Schur-product target. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_hurwitzSchur
    (_h : hurwitzSchurTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_schur

/-- Challenge-facing reduction from the column-zero Pólya-frequency leaf to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_columnZeroProductPF
    (hPF : hurwitzColumnZeroProductPFTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hurwitzMatrixHadamardLeThreeTarget_of_hurwitzSchurLeThree
    (hurwitzSchurLeThreeTarget_of_columnZeroProductPF hPF)

/-- Challenge-facing reduction from the even-column Toeplitz leaf to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_evenColToeplitz
    (hEven : hurwitzColumnZeroProductEvenColToeplitzTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_fullBand
    (hurwitzSchurFullBandTarget_of_evenColToeplitz hEven)

/-- Challenge-facing reduction from the Hurwitz normal-form leaf to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_hurwitzMul
    (h : hurwitzMulTotallyNonnegTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_fullBand
    (hurwitzSchurFullBandTarget_of_hurwitzMul h)

/-- Challenge-facing low-order consequence of the full Hurwitz-matrix Hadamard
target. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_matrixHadamard
    (h : hurwitzMatrixHadamardTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_matrixTN h

/-- Challenge-facing low-order matrix Hadamard target from Garloff--Wagner
Theorem 1 plus the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_stableRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_stableRoute
    hBwd hThm1 hFwd

/-- Challenge-facing low-order matrix Hadamard target from the right-half-plane
analytic core plus the Hurwitz-matrix total-nonnegativity criterion. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_rightHalfPlaneRoute
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : rightHalfPlaneStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_matrixTN
    (hadamardPreservesHurwitzMatrixTN_of_rightHalfPlaneRoute hBwd hRHP hFwd)

/-- Challenge-facing reduction from the fully in-band top-right subcase alone to
the low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_fullBand
    (hF : hurwitzSchurFullBandTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_fullBand hF

/-- Challenge-facing reduction from the corner-zeroed full-band subtarget to
the low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_fullBandCornerZeroed
    (h : hurwitzSchurFullBandCornerZeroedTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hurwitzMatrixHadamardLeThreeTarget_of_fullBand
    (hurwitzSchurFullBandTarget_of_cornerZeroed h)

/-- Challenge-facing reduction from the single-matrix corner-zeroed determinant
subtarget to the low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_cornerZeroedSingle
    (h : hurwitzSchurFullBandCornerZeroedSingleTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingle h

/-- Challenge-facing reduction from the column-normalized single-matrix leaf
to the low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_cornerZeroedSingleColZero
    (h : hurwitzSchurFullBandCornerZeroedSingleColZeroTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleColZero h

/-- Challenge-facing reduction from the first-column normal form to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_cornerZeroedSingleFirstCol
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleFirstCol h

/-- Challenge-facing reduction from the strict-remainder branch to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_cornerZeroedSingleFirstColPositiveRemainder
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hadamardPreservesHurwitzMatrixTNDetLeThree_of_cornerZeroedSingleFirstColPositiveRemainder h

/-- Short challenge-facing alias from the strict-remainder branch to the
low-order Hurwitz-matrix Hadamard target through size `3`. -/
theorem hurwitzMatrixHadamardLeThreeTarget_of_positiveRemainder
    (h : hurwitzSchurFullBandCornerZeroedSingleFirstColPositiveRemainderTarget) :
    hurwitzMatrixHadamardLeThreeTarget :=
  hurwitzMatrixHadamardLeThreeTarget_of_hurwitzSchurLeThree
    (hurwitzSchurLeThreeTarget_of_positiveRemainder h)

/-- Challenge-facing reduction of Garloff--Wagner's nonnegative
proper-position target through the odd/even Hurwitz-stability route. -/
theorem garloffWagnerNonnegPrecTarget_of_oddEven
    (hThm1 : hurwitzStableHadamardTarget)
    (hPrecToHurwitz : NonnegPrecToHurwitzOddEvenStatement)
    (hHurwitzToFull : HurwitzOddEvenToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerNonnegPrecTarget :=
  garloffWagnerHadamardNonnegPrec_of_oddEven
    hThm1 hPrecToHurwitz hHurwitzToFull hFullToPrec0

/-- Challenge-facing reduction of Garloff--Wagner's nonnegative
proper-position target through the Hurwitz-matrix Hadamard leaf. -/
theorem garloffWagnerNonnegPrecTarget_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerNonnegPrecTarget :=
  garloffWagnerHadamardNonnegPrec_of_matrixHadamardBridges hToFull hMatHad hFullToPrec0

/-- Challenge-facing reduction of Garloff--Wagner's nonnegative
proper-position target through the stable matrix route. -/
theorem garloffWagnerNonnegPrecTarget_of_stableRoute
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerNonnegPrecTarget :=
  garloffWagnerNonnegPrecTarget_of_matrixHadamardBridges hToFull
    (hurwitzMatrixHadamardTarget_of_stableRoute hBwd hThm1 hFwd)
    hFullToPrec0

/-- Challenge-facing reduction of Garloff--Wagner's nonnegative
proper-position target through the right-half-plane matrix route. -/
theorem garloffWagnerNonnegPrecTarget_of_rightHalfPlaneRoute
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : rightHalfPlaneStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerNonnegPrecTarget :=
  garloffWagnerNonnegPrecTarget_of_matrixHadamardBridges hToFull
    (hurwitzMatrixHadamardTarget_of_rightHalfPlaneRoute hBwd hRHP hFwd)
    hFullToPrec0

/-- Challenge-facing reduction of Garloff--Wagner's nonnegative
proper-position target through the pure Hurwitz Schur-product target. -/
theorem garloffWagnerNonnegPrecTarget_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (_hSchur : hurwitzSchurTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerNonnegPrecTarget :=
  garloffWagnerHadamardNonnegPrec_of_hurwitzSchur hToFull hFullToPrec0

/-- Challenge-facing reduction of Garloff--Wagner's nonnegative
proper-position target through the six unbundled classical inputs. -/
theorem garloffWagnerNonnegPrecTarget_of_classicalInputs
    (hRHP : hadamardPreservesRightHalfPlaneStableStatement)
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerNonnegPrecTarget :=
  garloffWagnerHadamardNonnegPrec_of_classicalInputs
    hRHP hHB hHBToHurwitz hHurwitzToMatrix hASW hInt

/-- Challenge-facing reduction of Garloff--Wagner's nonnegative
proper-position target through the bundled classical inputs. -/
theorem garloffWagnerNonnegPrecTarget_of_classicalInputsBundle
    (h : GarloffWagnerClassicalInputs) :
    garloffWagnerNonnegPrecTarget :=
  garloffWagnerHadamardNonnegPrec_of_classicalInputsBundle h

/-- Challenge-facing reduction of Garloff--Wagner's nonnegative
proper-position target through the matrix-core classical inputs. -/
theorem garloffWagnerNonnegPrecTarget_of_matrixClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerNonnegPrecTarget :=
  garloffWagnerHadamardNonnegPrec_of_matrixClassicalInputs hRoute hMatHad hASW hInt

/-- Challenge-facing reduction of Garloff--Wagner's nonnegative
proper-position target through the pure Hurwitz Schur-product classical
inputs. -/
theorem garloffWagnerNonnegPrecTarget_of_hurwitzSchurClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (_hSchur : hurwitzSchurTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerNonnegPrecTarget :=
  garloffWagnerHadamardNonnegPrec_of_hurwitzSchurClassicalInputs hRoute hASW hInt

/-- Challenge-facing reduction from the nonnegative two-pair statement to the
strict PF-polynomial proper-position target. -/
theorem garloffWagnerPFPrecTarget_of_nonnegPrec
    (_h : garloffWagnerNonnegPrecTarget) :
    garloffWagnerPFPrecTarget :=
  garloffWagnerHadamardPFPrec_of_nonnegPrec

/-- Challenge-facing reduction of the strict PF target through the odd/even
Hurwitz-stability route. -/
theorem garloffWagnerPFPrecTarget_of_oddEven
    (hThm1 : hurwitzStableHadamardTarget)
    (hPrecToHurwitz : NonnegPrecToHurwitzOddEvenStatement)
    (hHurwitzToFull : HurwitzOddEvenToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerPFPrecTarget :=
  garloffWagnerPFPrecTarget_of_nonnegPrec
    (garloffWagnerNonnegPrecTarget_of_oddEven
      hThm1 hPrecToHurwitz hHurwitzToFull hFullToPrec0)

/-- Challenge-facing reduction of the strict PF target through the
Hurwitz-matrix Hadamard leaf. -/
theorem garloffWagnerPFPrecTarget_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerPFPrecTarget :=
  garloffWagnerHadamardPFPrec_of_matrixHadamardBridges hToFull hMatHad hFullToPrec0

/-- Challenge-facing reduction of the strict PF target through the stable
matrix route. -/
theorem garloffWagnerPFPrecTarget_of_stableRoute
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerPFPrecTarget :=
  garloffWagnerPFPrecTarget_of_matrixHadamardBridges hToFull
    (hurwitzMatrixHadamardTarget_of_stableRoute hBwd hThm1 hFwd) hFullToPrec0

/-- Challenge-facing reduction of the strict PF target through the
right-half-plane matrix route. -/
theorem garloffWagnerPFPrecTarget_of_rightHalfPlaneRoute
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : rightHalfPlaneStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerPFPrecTarget :=
  garloffWagnerPFPrecTarget_of_matrixHadamardBridges hToFull
    (hurwitzMatrixHadamardTarget_of_rightHalfPlaneRoute hBwd hRHP hFwd) hFullToPrec0

/-- Challenge-facing reduction of the strict PF target through the pure
Hurwitz Schur-product target. -/
theorem garloffWagnerPFPrecTarget_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (_hSchur : hurwitzSchurTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerPFPrecTarget :=
  garloffWagnerHadamardPFPrec_of_hurwitzSchur hToFull hFullToPrec0

/-- Challenge-facing reduction of the strict PF target through the six
unbundled classical inputs. -/
theorem garloffWagnerPFPrecTarget_of_classicalInputs
    (hRHP : hadamardPreservesRightHalfPlaneStableStatement)
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerPFPrecTarget :=
  garloffWagnerHadamardPFPrec_of_classicalInputs hRHP hHB hHBToHurwitz hHurwitzToMatrix hASW hInt

/-- Challenge-facing reduction of the strict PF target through the bundled
classical inputs. -/
theorem garloffWagnerPFPrecTarget_of_classicalInputsBundle
    (h : GarloffWagnerClassicalInputs) :
    garloffWagnerPFPrecTarget :=
  garloffWagnerHadamardPFPrec_of_classicalInputsBundle h

/-- Challenge-facing reduction of the strict PF target through the matrix-core
classical inputs. -/
theorem garloffWagnerPFPrecTarget_of_matrixClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerPFPrecTarget :=
  garloffWagnerHadamardPFPrec_of_matrixClassicalInputs
    hRoute hMatHad hASW hInt

/-- Challenge-facing reduction of the strict PF target through the pure
Hurwitz Schur-product classical inputs. -/
theorem garloffWagnerPFPrecTarget_of_hurwitzSchurClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (_hSchur : hurwitzSchurTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerPFPrecTarget :=
  garloffWagnerHadamardPFPrec_of_hurwitzSchurClassicalInputs
    hRoute hASW hInt

/-- Challenge-facing reduction from strict PF proper position to the zero-aware
PF proper-position target. -/
theorem garloffWagnerPFPrec0Target_of_prec
    (h : garloffWagnerPFPrecTarget) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerHadamardPFPrec0_of_prec h

/-- Challenge-facing reduction from the nonnegative two-pair statement to the
zero-aware PF proper-position target. -/
theorem garloffWagnerPFPrec0Target_of_nonnegPrec
    (_h : garloffWagnerNonnegPrecTarget) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerHadamardPFPrec0_of_nonnegPrec

/-- Challenge-facing reduction of the zero-aware PF target through the odd/even
Hurwitz-stability route. -/
theorem garloffWagnerPFPrec0Target_of_oddEven
    (hThm1 : hurwitzStableHadamardTarget)
    (hPrecToHurwitz : NonnegPrecToHurwitzOddEvenStatement)
    (hHurwitzToFull : HurwitzOddEvenToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerPFPrec0Target_of_nonnegPrec
    (garloffWagnerNonnegPrecTarget_of_oddEven
      hThm1 hPrecToHurwitz hHurwitzToFull hFullToPrec0)

/-- Challenge-facing reduction of the zero-aware PF target through the
Hurwitz-matrix Hadamard leaf. -/
theorem garloffWagnerPFPrec0Target_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerHadamardPFPrec0_of_matrixHadamardBridges hToFull hMatHad hFullToPrec0

/-- Challenge-facing reduction of the zero-aware PF target through the stable
matrix route. -/
theorem garloffWagnerPFPrec0Target_of_stableRoute
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerPFPrec0Target_of_matrixHadamardBridges hToFull
    (hurwitzMatrixHadamardTarget_of_stableRoute hBwd hThm1 hFwd) hFullToPrec0

/-- Challenge-facing reduction of the zero-aware PF target through the
right-half-plane matrix route. -/
theorem garloffWagnerPFPrec0Target_of_rightHalfPlaneRoute
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : rightHalfPlaneStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerPFPrec0Target_of_matrixHadamardBridges hToFull
    (hurwitzMatrixHadamardTarget_of_rightHalfPlaneRoute hBwd hRHP hFwd) hFullToPrec0

/-- Challenge-facing reduction of the zero-aware PF target through the pure
Hurwitz Schur-product target. -/
theorem garloffWagnerPFPrec0Target_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (_hSchur : hurwitzSchurTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerHadamardPFPrec0_of_hurwitzSchur hToFull hFullToPrec0

/-- Challenge-facing reduction of the zero-aware PF target through the six
unbundled classical inputs. -/
theorem garloffWagnerPFPrec0Target_of_classicalInputs
    (hRHP : hadamardPreservesRightHalfPlaneStableStatement)
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerHadamardPFPrec0_of_classicalInputs hRHP hHB hHBToHurwitz hHurwitzToMatrix hASW hInt

/-- Challenge-facing reduction of the zero-aware PF target through the bundled
classical inputs. -/
theorem garloffWagnerPFPrec0Target_of_classicalInputsBundle
    (h : GarloffWagnerClassicalInputs) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerHadamardPFPrec0_of_classicalInputsBundle h

/-- Challenge-facing reduction of the zero-aware PF target through the
matrix-core classical inputs. -/
theorem garloffWagnerPFPrec0Target_of_matrixClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerHadamardPFPrec0_of_matrixClassicalInputs hRoute hMatHad hASW hInt

/-- Challenge-facing reduction of the zero-aware PF target through the pure
Hurwitz Schur-product classical inputs. -/
theorem garloffWagnerPFPrec0Target_of_hurwitzSchurClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (_hSchur : hurwitzSchurTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerPFPrec0Target :=
  garloffWagnerHadamardPFPrec0_of_hurwitzSchurClassicalInputs hRoute hASW hInt

/-- Challenge-facing reduction from the nonnegative two-pair target to the
one-polynomial real-rooted Hadamard target. -/
theorem garloffWagnerNonnegRealRootedTarget_of_nonnegPrec
    (_h : garloffWagnerNonnegPrecTarget) :
    garloffWagnerNonnegRealRootedTarget :=
  garloffWagnerHadamardNonnegRealRooted_of_nonnegPrec

/-- Challenge-facing one-polynomial real-rooted Hadamard target through the
odd/even Hurwitz-stability route. -/
theorem garloffWagnerNonnegRealRootedTarget_of_oddEven
    (hThm1 : hurwitzStableHadamardTarget)
    (hPrecToHurwitz : NonnegPrecToHurwitzOddEvenStatement)
    (hHurwitzToFull : HurwitzOddEvenToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerNonnegRealRootedTarget :=
  garloffWagnerNonnegRealRootedTarget_of_nonnegPrec
    (garloffWagnerNonnegPrecTarget_of_oddEven
      hThm1 hPrecToHurwitz hHurwitzToFull hFullToPrec0)

/-- Challenge-facing one-polynomial real-rooted Hadamard target through the
Hurwitz-matrix Hadamard leaf. -/
theorem garloffWagnerNonnegRealRootedTarget_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerNonnegRealRootedTarget :=
  garloffWagnerHadamardNonnegRealRooted_of_matrixHadamardBridges hToFull hMatHad hFullToPrec0

/-- Challenge-facing one-polynomial real-rooted Hadamard target through the
stable matrix route. -/
theorem garloffWagnerNonnegRealRootedTarget_of_stableRoute
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerNonnegRealRootedTarget :=
  garloffWagnerNonnegRealRootedTarget_of_matrixHadamardBridges hToFull
    (hurwitzMatrixHadamardTarget_of_stableRoute hBwd hThm1 hFwd) hFullToPrec0

/-- Challenge-facing one-polynomial real-rooted Hadamard target through the
right-half-plane matrix route. -/
theorem garloffWagnerNonnegRealRootedTarget_of_rightHalfPlaneRoute
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : rightHalfPlaneStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerNonnegRealRootedTarget :=
  garloffWagnerNonnegRealRootedTarget_of_matrixHadamardBridges hToFull
    (hurwitzMatrixHadamardTarget_of_rightHalfPlaneRoute hBwd hRHP hFwd) hFullToPrec0

/-- Challenge-facing one-polynomial real-rooted Hadamard target through the
pure Hurwitz Schur-product target. -/
theorem garloffWagnerNonnegRealRootedTarget_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hSchur : hurwitzSchurTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    garloffWagnerNonnegRealRootedTarget :=
  garloffWagnerHadamardNonnegRealRooted_of_hurwitzSchur hToFull hSchur hFullToPrec0

/-- Challenge-facing one-polynomial real-rooted Hadamard target through the
six unbundled classical inputs. -/
theorem garloffWagnerNonnegRealRootedTarget_of_classicalInputs
    (hRHP : hadamardPreservesRightHalfPlaneStableStatement)
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerNonnegRealRootedTarget :=
  garloffWagnerHadamardNonnegRealRooted_of_classicalInputs
    hRHP hHB hHBToHurwitz hHurwitzToMatrix hASW hInt

/-- Challenge-facing one-polynomial real-rooted Hadamard target through the
bundled classical inputs. -/
theorem garloffWagnerNonnegRealRootedTarget_of_classicalInputsBundle
    (h : GarloffWagnerClassicalInputs) :
    garloffWagnerNonnegRealRootedTarget :=
  garloffWagnerHadamardNonnegRealRooted_of_classicalInputsBundle h

/-- Challenge-facing one-polynomial real-rooted Hadamard target through the
matrix-core classical inputs. -/
theorem garloffWagnerNonnegRealRootedTarget_of_matrixClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerNonnegRealRootedTarget :=
  garloffWagnerHadamardNonnegRealRooted_of_matrixClassicalInputs
    hRoute hMatHad hASW hInt

/-- Challenge-facing one-polynomial real-rooted Hadamard target through the
pure Hurwitz Schur-product classical inputs. -/
theorem garloffWagnerNonnegRealRootedTarget_of_hurwitzSchurClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hSchur : hurwitzSchurTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    garloffWagnerNonnegRealRootedTarget :=
  garloffWagnerHadamardNonnegRealRooted_of_hurwitzSchurClassicalInputs
    hRoute hSchur hASW hInt

/-- Challenge-facing PF Schur--Pólya--Wagner target from the zero-aware PF
Garloff--Wagner wrapper. -/
theorem schurPolyaWagnerHadamardPFTarget_of_prec0
    (h : garloffWagnerPFPrec0Target) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_garloffWagner_prec0 h

/-- Challenge-facing PF Schur--Pólya--Wagner target from the strict PF
proper-position target. -/
theorem schurPolyaWagnerHadamardPFTarget_of_prec
    (h : garloffWagnerPFPrecTarget) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_garloffWagner_prec h

/-- Challenge-facing PF Schur--Pólya--Wagner target from the nonnegative
two-pair Garloff--Wagner target. -/
theorem schurPolyaWagnerHadamardPFTarget_of_nonnegPrec
    (_h : garloffWagnerNonnegPrecTarget) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_garloffWagner_nonnegPrec

/-- Challenge-facing PF Schur--Pólya--Wagner target through the odd/even
Hurwitz-stability route. -/
theorem schurPolyaWagnerHadamardPFTarget_of_oddEven
    (hThm1 : hurwitzStableHadamardTarget)
    (hPrecToHurwitz : NonnegPrecToHurwitzOddEvenStatement)
    (hHurwitzToFull : HurwitzOddEvenToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPFTarget_of_nonnegPrec
    (garloffWagnerNonnegPrecTarget_of_oddEven
      hThm1 hPrecToHurwitz hHurwitzToFull hFullToPrec0)

/-- Challenge-facing PF Schur--Pólya--Wagner target from the one-polynomial
nonnegative real-rooted Hadamard target. -/
theorem schurPolyaWagnerHadamardPFTarget_of_garloffWagner_nonneg
    (h : garloffWagnerNonnegRealRootedTarget) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_garloffWagner_nonneg h

/-- Challenge-facing PF Schur--Pólya--Wagner target through the Hurwitz-matrix
Hadamard leaf. -/
theorem schurPolyaWagnerHadamardPFTarget_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_matrixHadamardBridges hToFull hMatHad hFullToPrec0

/-- Challenge-facing PF Schur--Pólya--Wagner target through the stable matrix
route. -/
theorem schurPolyaWagnerHadamardPFTarget_of_stableRoute
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPFTarget_of_matrixHadamardBridges hToFull
    (hurwitzMatrixHadamardTarget_of_stableRoute hBwd hThm1 hFwd) hFullToPrec0

/-- Challenge-facing PF Schur--Pólya--Wagner target through the
right-half-plane matrix route. -/
theorem schurPolyaWagnerHadamardPFTarget_of_rightHalfPlaneRoute
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : rightHalfPlaneStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPFTarget_of_matrixHadamardBridges hToFull
    (hurwitzMatrixHadamardTarget_of_rightHalfPlaneRoute hBwd hRHP hFwd) hFullToPrec0

/-- Challenge-facing PF Schur--Pólya--Wagner target through the pure Hurwitz
Schur-product target. -/
theorem schurPolyaWagnerHadamardPFTarget_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (_hSchur : hurwitzSchurTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_hurwitzSchur hToFull hFullToPrec0

/-- Challenge-facing PF Schur--Pólya--Wagner target through the six
unbundled classical inputs. -/
theorem schurPolyaWagnerHadamardPFTarget_of_classicalInputs
    (hRHP : hadamardPreservesRightHalfPlaneStableStatement)
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_classicalInputs hRHP hHB hHBToHurwitz hHurwitzToMatrix hASW hInt

/-- Challenge-facing PF Schur--Pólya--Wagner target through the bundled
classical inputs. -/
theorem schurPolyaWagnerHadamardPFTarget_of_classicalInputsBundle
    (h : GarloffWagnerClassicalInputs) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_classicalInputsBundle h

/-- Challenge-facing PF Schur--Pólya--Wagner target through the matrix-core
classical inputs. -/
theorem schurPolyaWagnerHadamardPFTarget_of_matrixClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_matrixClassicalInputs hRoute hMatHad hASW hInt

/-- Challenge-facing PF Schur--Pólya--Wagner target through the pure Hurwitz
Schur-product classical inputs. -/
theorem schurPolyaWagnerHadamardPFTarget_of_hurwitzSchurClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (_hSchur : hurwitzSchurTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    schurPolyaWagnerHadamardPFTarget :=
  schurPolyaWagnerHadamardPF_of_hurwitzSchurClassicalInputs hRoute hASW hInt

/-- Challenge-facing reciprocal-cone Hadamard closure from the zero-aware PF
Garloff--Wagner wrapper. -/
theorem hadamardReciprocalConeClosureTarget_of_prec0
    (h : garloffWagnerPFPrec0Target) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosure_of_garloffWagner_prec0 h

/-- Challenge-facing reciprocal-cone Hadamard closure from the strict PF
proper-position target. -/
theorem hadamardReciprocalConeClosureTarget_of_prec
    (h : garloffWagnerPFPrecTarget) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosure_of_garloffWagner_prec h

/-- Challenge-facing reciprocal-cone Hadamard closure from the nonnegative
two-pair Garloff--Wagner target. -/
theorem hadamardReciprocalConeClosureTarget_of_nonnegPrec
    (_h : garloffWagnerNonnegPrecTarget) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosure_of_garloffWagner

/-- Challenge-facing reciprocal-cone Hadamard closure through the odd/even
Hurwitz-stability route. -/
theorem hadamardReciprocalConeClosureTarget_of_oddEven
    (hThm1 : hurwitzStableHadamardTarget)
    (hPrecToHurwitz : NonnegPrecToHurwitzOddEvenStatement)
    (hHurwitzToFull : HurwitzOddEvenToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosureTarget_of_nonnegPrec
    (garloffWagnerNonnegPrecTarget_of_oddEven
      hThm1 hPrecToHurwitz hHurwitzToFull hFullToPrec0)

/-- Challenge-facing reciprocal-cone Hadamard closure through the
Hurwitz-matrix Hadamard leaf. -/
theorem hadamardReciprocalConeClosureTarget_of_matrixHadamardBridges
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosure_of_matrixHadamardBridges hToFull hMatHad hFullToPrec0

/-- Challenge-facing reciprocal-cone Hadamard closure through the stable
matrix route. -/
theorem hadamardReciprocalConeClosureTarget_of_stableRoute
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosureTarget_of_matrixHadamardBridges hToFull
    (hurwitzMatrixHadamardTarget_of_stableRoute hBwd hThm1 hFwd) hFullToPrec0

/-- Challenge-facing reciprocal-cone Hadamard closure through the
right-half-plane matrix route. -/
theorem hadamardReciprocalConeClosureTarget_of_rightHalfPlaneRoute
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : rightHalfPlaneStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosureTarget_of_matrixHadamardBridges hToFull
    (hurwitzMatrixHadamardTarget_of_rightHalfPlaneRoute hBwd hRHP hFwd) hFullToPrec0

/-- Challenge-facing reciprocal-cone Hadamard closure through the pure Hurwitz
Schur-product target. -/
theorem hadamardReciprocalConeClosureTarget_of_hurwitzSchur
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (_hSchur : hurwitzSchurTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosure_of_hurwitzSchur hToFull hFullToPrec0

/-- Challenge-facing reciprocal-cone Hadamard closure through the six
unbundled classical inputs. -/
theorem hadamardReciprocalConeClosureTarget_of_classicalInputs
    (hRHP : hadamardPreservesRightHalfPlaneStableStatement)
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosure_of_classicalInputs hRHP hHB hHBToHurwitz hHurwitzToMatrix hASW hInt

/-- Challenge-facing reciprocal-cone Hadamard closure through the bundled
classical inputs. -/
theorem hadamardReciprocalConeClosureTarget_of_classicalInputsBundle
    (h : GarloffWagnerClassicalInputs) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosure_of_classicalInputsBundle h

/-- Challenge-facing reciprocal-cone Hadamard closure through the matrix-core
classical inputs. -/
theorem hadamardReciprocalConeClosureTarget_of_matrixClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosure_of_matrixClassicalInputs hRoute hMatHad hASW hInt

/-- Challenge-facing reciprocal-cone Hadamard closure through the pure
Hurwitz Schur-product classical inputs. -/
theorem hadamardReciprocalConeClosureTarget_of_hurwitzSchurClassicalInputs
    (hRoute : HermiteBiehlerHurwitzRoute)
    (_hSchur : hurwitzSchurTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    hadamardReciprocalConeClosureTarget :=
  hadamardReciprocalConeClosure_of_hurwitzSchurClassicalInputs hRoute hASW hInt

/-- Challenge-facing coefficientwise Pólya-frequency closure from the
Schur--Pólya--Wagner PF target. -/
theorem polyaFrequencyHadamardCoeffTarget_of_schurPolyaWagner
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hSPW : schurPolyaWagnerHadamardPFTarget) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_schurPolyaWagner hASW hSPW

/-- Challenge-facing coefficientwise Pólya-frequency closure from the
zero-aware PF proper-position target. -/
theorem polyaFrequencyHadamardCoeffTarget_of_prec0
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hGW : garloffWagnerPFPrec0Target) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_garloffWagner_prec0 hASW hGW

/-- Challenge-facing coefficientwise Pólya-frequency closure from the strict
PF proper-position target. -/
theorem polyaFrequencyHadamardCoeffTarget_of_prec
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hGW : garloffWagnerPFPrecTarget) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_garloffWagner_prec hASW hGW

/-- Challenge-facing coefficientwise Pólya-frequency closure from the
one-polynomial nonnegative real-rooted Hadamard target. -/
theorem polyaFrequencyHadamardCoeffTarget_of_garloffWagner_nonneg
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hGW : garloffWagnerNonnegRealRootedTarget) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_garloffWagner_nonneg hASW hGW

/-- Challenge-facing coefficientwise Pólya-frequency closure from the
nonnegative two-pair Garloff--Wagner target. -/
theorem polyaFrequencyHadamardCoeffTarget_of_garloffWagner_nonnegPrec
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (_hGW : garloffWagnerNonnegPrecTarget) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_garloffWagner_nonnegPrec hASW

/-- Challenge-facing coefficientwise Pólya-frequency closure through the
odd/even Hurwitz-stability route. -/
theorem polyaFrequencyHadamardCoeffTarget_of_oddEven
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hPrecToHurwitz : NonnegPrecToHurwitzOddEvenStatement)
    (hHurwitzToFull : HurwitzOddEvenToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeffTarget_of_garloffWagner_nonnegPrec hASW
    (garloffWagnerNonnegPrecTarget_of_oddEven
      hThm1 hPrecToHurwitz hHurwitzToFull hFullToPrec0)

/-- Challenge-facing coefficientwise Pólya-frequency closure through the
Hurwitz-matrix Hadamard leaf. -/
theorem polyaFrequencyHadamardCoeffTarget_of_matrixHadamardBridges
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_matrixHadamardBridges hASW hToFull hMatHad hFullToPrec0

/-- Challenge-facing coefficientwise Pólya-frequency closure through the
stable matrix route. -/
theorem polyaFrequencyHadamardCoeffTarget_of_stableRoute
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hThm1 : hurwitzStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeffTarget_of_matrixHadamardBridges hASW hToFull
    (hurwitzMatrixHadamardTarget_of_stableRoute hBwd hThm1 hFwd) hFullToPrec0

/-- Challenge-facing coefficientwise Pólya-frequency closure through the
right-half-plane matrix route. -/
theorem polyaFrequencyHadamardCoeffTarget_of_rightHalfPlaneRoute
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (hBwd : HurwitzMatrixTotallyNonnegativeToStableStatement)
    (hRHP : rightHalfPlaneStableHadamardTarget)
    (hFwd : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeffTarget_of_matrixHadamardBridges hASW hToFull
    (hurwitzMatrixHadamardTarget_of_rightHalfPlaneRoute hBwd hRHP hFwd) hFullToPrec0

/-- Challenge-facing coefficientwise Pólya-frequency closure through the pure
Hurwitz Schur-product target. -/
theorem polyaFrequencyHadamardCoeffTarget_of_hurwitzSchur
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hToFull : NonnegPrecToFullyInterlacingPairStatement)
    (_hSchur : hurwitzSchurTarget)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_hurwitzSchur hASW hToFull hFullToPrec0

/-- Challenge-facing coefficientwise Pólya-frequency closure through the six
unbundled classical inputs. -/
theorem polyaFrequencyHadamardCoeffTarget_of_classicalInputs
    (hASW0 : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hRHP : hadamardPreservesRightHalfPlaneStableStatement)
    (hHB : hermiteBiehlerForwardPosStatement)
    (hHBToHurwitz : HermiteBiehlerStableToHurwitzOddEvenStatement)
    (hHurwitzToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_classicalInputs
    hASW0 hRHP hHB hHBToHurwitz hHurwitzToMatrix hASW hInt

/-- Challenge-facing coefficientwise Pólya-frequency closure through the
bundled classical inputs. -/
theorem polyaFrequencyHadamardCoeffTarget_of_classicalInputsBundle
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (h : GarloffWagnerClassicalInputs) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_classicalInputsBundle hASW h

/-- Challenge-facing coefficientwise Pólya-frequency closure through the
matrix-core classical inputs. -/
theorem polyaFrequencyHadamardCoeffTarget_of_matrixClassicalInputs
    (hASW0 : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hRoute : HermiteBiehlerHurwitzRoute)
    (hMatHad : hurwitzMatrixHadamardTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_matrixClassicalInputs
    hASW0 hRoute hMatHad hASW hInt

/-- Challenge-facing coefficientwise Pólya-frequency closure through the pure
Hurwitz Schur-product classical inputs. -/
theorem polyaFrequencyHadamardCoeffTarget_of_hurwitzSchurClassicalInputs
    (hASW0 : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hRoute : HermiteBiehlerHurwitzRoute)
    (_hSchur : hurwitzSchurTarget)
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hInt : FullyInterlacingPairInterlaceStatement) :
    polyaFrequencyHadamardCoeffTarget :=
  polyaFrequencyHadamardCoeff_of_hurwitzSchurClassicalInputs
    hASW0 hRoute hASW hInt

end Hadamard
end Challenges
end RealRooted
