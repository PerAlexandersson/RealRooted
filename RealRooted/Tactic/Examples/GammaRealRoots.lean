import RealRooted.Tactic.GammaRealRoots

open Polynomial

namespace RealRooted
namespace Tactic

example (d : ℕ) (γ δ : ℝ[X]) :
    gammaTransform d (γ + δ) = gammaTransform d γ + gammaTransform d δ := by
  rr_gamma_transform_add

example (d : ℕ) (a : ℝ) (γ : ℝ[X]) :
    gammaTransform d (C a * γ) = C a * gammaTransform d γ := by
  rr_gamma_transform_C_mul

example (d n : ℕ) (a : ℝ) :
    gammaTransform d (monomial n a) =
      if n ≤ d / 2 then C a * gammaBasisTerm d n else 0 := by
  rr_gamma_transform_monomial

example (d : ℕ) (γ : ℝ[X]) :
    IdTransform d (gammaTransform d γ) = gammaTransform d γ := by
  rr_gamma_transform_fixed

example (d i : ℕ) :
    HasNonnegCoeffs (gammaBasisTerm d i) := by
  rr_gamma_basis_nonneg

example {d : ℕ} {γ : ℝ[X]} (hγ : HasNonnegCoeffs γ) :
    HasNonnegCoeffs (gammaTransform d γ) := by
  rr_gamma_transform_nonneg using nonneg := hγ

example (d : ℕ) (γ : ℝ[X]) :
    (gammaTransform d γ).natDegree ≤ d := by
  rr_gamma_transform_natDegree_le

example {d : ℕ} {γ δ : ℝ[X]}
    (hγ : γ.natDegree ≤ d / 2)
    (hδ : δ.natDegree ≤ d / 2)
    (hEq : gammaTransform d γ = gammaTransform d δ) :
    γ = δ := by
  rr_gamma_transform_injective using
    left_degree := hγ,
    right_degree := hδ,
    transform_eq := hEq

example {d : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) :
    gammaTransform d γ = 0 ↔ γ = 0 := by
  rr_gamma_transform_zero_iff using gamma_degree := hγ

example (d : ℕ) (γ : ℝ[X]) :
    gammaTransform (d + 2) (X * γ) = X * gammaTransform d γ := by
  rr_gamma_transform_X_mul_two

example {d : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) :
    gammaTransform (d + 2) γ = (X + 1) ^ 2 * gammaTransform d γ := by
  rr_gamma_transform_pad_two using gamma_degree := hγ

example (m : ℕ) (γ : ℝ[X]) :
    gammaTransform (2 * m + 1) γ = (X + 1) * gammaTransform (2 * m) γ := by
  rr_gamma_transform_odd

example {d : ℕ} {γ : ℝ[X]}
    (hdeg : γ.natDegree ≤ d / 2)
    (hne : γ ≠ 0)
    (hsplits : γ.Splits)
    (hnn : HasNonnegCoeffs γ) :
    (gammaTransform d γ) ≠ 0 ∧ (gammaTransform d γ).Splits := by
  rr_gamma_transform_realrooted_nonneg using
    gamma_degree := hdeg,
    gamma_nonzero := hne,
    gamma_splits := hsplits,
    gamma_nonneg := hnn

example {d : ℕ} {γ : ℝ[X]}
    (hdeg : γ.natDegree ≤ d / 2)
    (hne : γ ≠ 0)
    (hsplits : γ.Splits)
    (hnn : HasNonnegCoeffs γ) :
    HasRootsNonpos (gammaTransform d γ) := by
  rr_gamma_transform_roots_nonpos_nonneg using
    gamma_degree := hdeg,
    gamma_nonzero := hne,
    gamma_splits := hsplits,
    gamma_nonneg := hnn

example {d : ℕ} {γ : ℝ[X]}
    (hdeg : γ.natDegree ≤ d / 2)
    (hne : γ ≠ 0)
    (hsplits : γ.Splits)
    (hnp : HasRootsNonpos γ) :
    ((gammaTransform d γ) ≠ 0 ∧ (gammaTransform d γ).Splits) ∧
      HasRootsNonpos (gammaTransform d γ) := by
  rr_gamma_transform_realrooted_nonpos using
    gamma_degree := hdeg,
    gamma_nonzero := hne,
    gamma_splits := hsplits,
    gamma_roots_nonpos := hnp

example {γ : ℝ[X]}
    (hne : gammaTransform (2 * γ.natDegree) γ ≠ 0)
    (hsplits : (gammaTransform (2 * γ.natDegree) γ).Splits)
    (hnp : HasRootsNonpos (gammaTransform (2 * γ.natDegree) γ)) :
    (γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ := by
  rr_gamma_transform_backward_minimal using
    transform_nonzero := hne,
    transform_splits := hsplits,
    transform_roots_nonpos := hnp

example {d : ℕ} {γ : ℝ[X]}
    (hdeg : γ.natDegree ≤ d / 2)
    (hne : gammaTransform d γ ≠ 0)
    (hsplits : (gammaTransform d γ).Splits)
    (hnp : HasRootsNonpos (gammaTransform d γ)) :
    (γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ := by
  rr_gamma_transform_backward using
    gamma_degree := hdeg,
    transform_nonzero := hne,
    transform_splits := hsplits,
    transform_roots_nonpos := hnp

example {d : ℕ} {p γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2)
    (hpdeg : p.natDegree ≤ d)
    (hsym : IdTransform d p = p)
    (hexp : IsGammaExpansion d p γ) :
    (((γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ) ↔
      ((p ≠ 0 ∧ p.Splits) ∧ HasRootsNonpos p)) := by
  rr_gamma_realrooted_iff using
    gamma_degree := hγdeg,
    polynomial_degree := hpdeg,
    symmetric := hsym,
    expansion := hexp

example {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, (Γ n).natDegree ≤ d n / 2)
    (hne : ∀ n : Nat, Γ n ≠ 0)
    (hsplits : ∀ n : Nat, (Γ n).Splits)
    (hnn : ∀ n : Nat, HasNonnegCoeffs (Γ n)) :
    ∀ n : Nat, gammaTransform (d n) (Γ n) ≠ 0 ∧
      (gammaTransform (d n) (Γ n)).Splits := by
  rr_gamma_transform_sequence_realrooted_nonneg using
    gamma_degree := hdeg,
    gamma_nonzero := hne,
    gamma_splits := hsplits,
    gamma_nonneg := hnn

example {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, (Γ n).natDegree ≤ d n / 2)
    (hne : ∀ n : Nat, Γ n ≠ 0)
    (hsplits : ∀ n : Nat, (Γ n).Splits)
    (hnn : ∀ n : Nat, HasNonnegCoeffs (Γ n)) :
    ∀ n : Nat, HasRootsNonpos (gammaTransform (d n) (Γ n)) := by
  rr_gamma_transform_sequence_roots_nonpos_nonneg using
    gamma_degree := hdeg,
    gamma_nonzero := hne,
    gamma_splits := hsplits,
    gamma_nonneg := hnn

example {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, (Γ n).natDegree ≤ d n / 2)
    (hne : ∀ n : Nat, Γ n ≠ 0)
    (hsplits : ∀ n : Nat, (Γ n).Splits)
    (hnp : ∀ n : Nat, HasRootsNonpos (Γ n)) :
    ∀ n : Nat,
      (gammaTransform (d n) (Γ n) ≠ 0 ∧
        (gammaTransform (d n) (Γ n)).Splits) ∧
        HasRootsNonpos (gammaTransform (d n) (Γ n)) := by
  rr_gamma_transform_sequence_realrooted_nonpos using
    gamma_degree := hdeg,
    gamma_nonzero := hne,
    gamma_splits := hsplits,
    gamma_roots_nonpos := hnp

example {d : Nat → Nat} {Γ : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, (Γ n).natDegree ≤ d n / 2)
    (hne : ∀ n : Nat, gammaTransform (d n) (Γ n) ≠ 0)
    (hsplits : ∀ n : Nat, (gammaTransform (d n) (Γ n)).Splits)
    (hnp : ∀ n : Nat, HasRootsNonpos (gammaTransform (d n) (Γ n))) :
    ∀ n : Nat, (Γ n ≠ 0 ∧ (Γ n).Splits) ∧ HasRootsNonpos (Γ n) := by
  rr_gamma_transform_sequence_backward using
    gamma_degree := hdeg,
    transform_nonzero := hne,
    transform_splits := hsplits,
    transform_roots_nonpos := hnp

example {Γ : Nat → ℝ[X]}
    (hne : ∀ n : Nat, gammaTransform (2 * (Γ n).natDegree) (Γ n) ≠ 0)
    (hsplits : ∀ n : Nat,
      (gammaTransform (2 * (Γ n).natDegree) (Γ n)).Splits)
    (hnp : ∀ n : Nat,
      HasRootsNonpos (gammaTransform (2 * (Γ n).natDegree) (Γ n))) :
    ∀ n : Nat, (Γ n ≠ 0 ∧ (Γ n).Splits) ∧ HasRootsNonpos (Γ n) := by
  rr_gamma_transform_sequence_backward_minimal using
    transform_nonzero := hne,
    transform_splits := hsplits,
    transform_roots_nonpos := hnp

example {d : Nat → Nat} {P Γ : Nat → ℝ[X]}
    (hγdeg : ∀ n : Nat, (Γ n).natDegree ≤ d n / 2)
    (hpdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hsym : ∀ n : Nat, IdTransform (d n) (P n) = P n)
    (hexp : ∀ n : Nat, IsGammaExpansion (d n) (P n) (Γ n)) :
    ∀ n : Nat,
      (((Γ n ≠ 0 ∧ (Γ n).Splits) ∧ HasRootsNonpos (Γ n)) ↔
        ((P n ≠ 0 ∧ (P n).Splits) ∧ HasRootsNonpos (P n))) := by
  rr_gamma_sequence_realrooted_iff using
    gamma_degree := hγdeg,
    polynomial_degree := hpdeg,
    symmetric := hsym,
    expansion := hexp

end Tactic
end RealRooted
