import RealRooted.JensenPencilContraction
import RealRooted.MultiplierSequence.Bidiagonal.Jensen

/-!
# Jensen-pencil contraction for bidiagonal operators

This module turns the Schur--Szegő compatibility contraction into a
coefficient-bidiagonal PF-preserver theorem, with rowwise variants.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The root-count contraction core needed by the general Jensen-pencil
argument.

This is the zero-aware Schur--Szegő formulation of the finite-free
multiplicative-convolution step: composing both Jensen endpoints with the
same PF polynomial preserves compatibility after restoring the explicit
factor `X` on the second endpoint. -/
def schurSzegoPreservesJensenPencilCompatibilityStatement : Prop :=
  ∀ {d : ℕ} {A B p : ℝ[X]},
    IsPFPolynomial A →
    IsPFPolynomial (X * B) →
    IsPFPolynomial p →
    A.natDegree ≤ d →
    B.natDegree ≤ d →
    p.natDegree ≤ d →
    Compatible A (X * B) →
    Compatible (schurSzegoComp d A p)
      (X * schurSzegoComp d B p)

/-- The two endpoint compositions in the Jensen-pencil contraction core are
individually PF.  Thus the remaining content of the core statement is their
compatibility, not endpoint real-rootedness or root location. -/
theorem schurSzegoJensenEndpoints_pf
    {d : ℕ} {A B p : ℝ[X]}
    (hA : IsPFPolynomial A) (hXB : IsPFPolynomial (X * B))
    (hp : IsPFPolynomial p) (hAdeg : A.natDegree ≤ d)
    (hBdeg : B.natDegree ≤ d) (hpdeg : p.natDegree ≤ d) :
    IsPFPolynomial (schurSzegoComp d A p) ∧
      IsPFPolynomial (X * schurSzegoComp d B p) := by
  exact ⟨hA.schurSzegoComp hp hAdeg hpdeg,
    ((isPFPolynomial_of_X_mul hXB).schurSzegoComp hp hBdeg hpdeg).X_mul⟩

/-- The Schur--Szegő compatibility core implies the complete Jensen-pencil
bidiagonal preserver theorem. -/
theorem jensenPencilBidiagonalPreserver_of_schurSzegoCompatibility
    (hcore : schurSzegoPreservesJensenPencilCompatibilityStatement) :
    ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d := by
  intro alpha beta d hcert p hp hdeg
  have hcompat :
      Compatible
        (schurSzegoComp d (jensenPolynomial d alpha) p)
        (X * schurSzegoComp d (jensenPolynomial d beta) p) :=
    hcore hcert.1 hcert.2.1 hp
      (natDegree_jensenPolynomial_le d alpha)
      (natDegree_jensenPolynomial_le d beta) hdeg hcert.compatible
  have hout_nonneg : HasNonnegCoeffs (bidiagonalOperator alpha beta p) :=
    hp.hasNonnegCoeffs.bidiagonalOperator_of_degree_le hdeg
      (fun k hk => hcert.alpha_nonneg_of_le hk)
      (fun k hk => hcert.beta_nonneg_of_le hk)
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hout_nonneg
  rw [bidiagonalOperator_eq_schurSzegoComp hdeg]
  rcases hcompat 1 1 (by norm_num) (by norm_num) with hzero | hsplits
  · simpa using Or.inl hzero
  · exact Or.inr (by simpa using hsplits.2)

/-- Jensen-pencil implication for coefficient-bidiagonal PF preservers. -/
theorem jensenPencilBidiagonalPreserver :
    ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d := by
  exact jensenPencilBidiagonalPreserver_of_schurSzegoCompatibility
    schurSzegoPreservesJensenPencilCompatibility

/-- Apply the named Jensen-pencil backend theorem. -/
theorem bidiagonalPFPreserver_of_jensenPencil
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  jensenPencilBidiagonalPreserver hcert

/-- A Jensen-pencil certificate gives a coefficient-bidiagonal PF preserver
once the global backend is available. -/
theorem BidiagonalJensenPencilCertificate.toPFPreserver
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  bidiagonalPFPreserver_of_jensenPencil hcert

/-- Rowwise Jensen-pencil certificates give rowwise coefficient-bidiagonal
PF preservers. -/
theorem BidiagonalJensenPencilCertificate.toPFPreserver_sequence
    {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hcert : ∀ n : Nat,
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n)) :
    ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n) :=
  fun n => (hcert n).toPFPreserver

/-- Tail-start rowwise version of
`BidiagonalJensenPencilCertificate.toPFPreserver_sequence`. -/
theorem BidiagonalJensenPencilCertificate.toPFPreserver_sequence_from
    (N : Nat) {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n)) :
    ∀ n : Nat, N ≤ n → BidiagonalPFPreserver (alpha n) (beta n) (d n) :=
  fun n hn => (hcert n hn).toPFPreserver


end RealRooted
