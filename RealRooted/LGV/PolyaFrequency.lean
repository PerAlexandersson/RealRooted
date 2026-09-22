/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import RealRooted.LGV.Toeplitz
import RealRooted.LGV.TotallyNonnegative

/-!
# Ordered LGV certificates and Pólya-frequency sequences

This file is the endpoint adapter from standalone LeanLGV to the
Pólya-frequency interface in `RealRooted`. All path-cancellation arguments
remain in LeanLGV; here we only apply their determinant nonnegativity theorem
to every strict Toeplitz minor.
-/

namespace RealRooted

noncomputable section

/-- Ordered LGV cancellation certificates for every strict Toeplitz minor,
together with nonnegative path weights, make the Toeplitz matrix totally
nonnegative. -/
theorem toeplitz_isTotallyNonneg_of_orderedCertificates
    {a : ℕ → ℝ} (N : LGV.FinitePathNetwork ℝ ℕ)
    (hN : N.matrix = toeplitz a)
    (certificate : ∀ {n : ℕ} (I : StrictToeplitzMinorIndex n),
      LGV.FinitePathNetwork.OrderedCancellationCertificate (I.pathNetwork N))
    (hweight : ∀ {s t : ℕ} (p : N.Path s t), 0 ≤ N.weight p) :
    (toeplitz a).IsTotallyNonneg := by
  rw [← hN]
  apply N.matrix_isTotallyNonneg_of_orderedCertificates
  · intro n rows cols hrows hcols
    exact certificate ⟨rows, cols, hrows, hcols⟩
  · exact hweight

/-- Ordered cancellation certificates on minor-local networks make the
Toeplitz matrix totally nonnegative.  The network for each strict minor may
differ from the networks for all other minors. -/
theorem toeplitz_isTotallyNonneg_of_minorOrderedCertificates
    {a : ℕ → ℝ}
    (network : ∀ {n : ℕ}, StrictToeplitzMinorIndex n →
      LGV.FinitePathNetwork ℝ (Fin n))
    (hmatrix : ∀ {n : ℕ} (I : StrictToeplitzMinorIndex n),
      (network I).matrix = I.toeplitzSubmatrix a)
    (certificate : ∀ {n : ℕ} (I : StrictToeplitzMinorIndex n),
      LGV.FinitePathNetwork.OrderedCancellationCertificate (network I))
    (hweight : ∀ {n : ℕ} (I : StrictToeplitzMinorIndex n)
      {s t : Fin n} (p : (network I).Path s t),
      0 ≤ (network I).weight p) :
    (toeplitz a).IsTotallyNonneg := by
  intro n rows cols hrows hcols
  let I : StrictToeplitzMinorIndex n := ⟨rows, cols, hrows, hcols⟩
  change 0 ≤ Matrix.det (I.toeplitzSubmatrix a)
  rw [← hmatrix I]
  exact (certificate I).det_nonneg (hweight I)

/-- Ordered LGV cancellation certificates for all strict Toeplitz minors give
the associated Pólya-frequency sequence. -/
theorem isPolyaFreqSeq_of_orderedCertificates
    {a : ℕ → ℝ} (N : LGV.FinitePathNetwork ℝ ℕ)
    (hN : N.matrix = toeplitz a)
    (certificate : ∀ {n : ℕ} (I : StrictToeplitzMinorIndex n),
      LGV.FinitePathNetwork.OrderedCancellationCertificate (I.pathNetwork N))
    (hweight : ∀ {s t : ℕ} (p : N.Path s t), 0 ≤ N.weight p) :
    IsPolyaFreqSeq a :=
  toeplitz_isTotallyNonneg_of_orderedCertificates N hN certificate hweight

/-- Minor-local ordered cancellation certificates give the associated
Pólya-frequency sequence. -/
theorem isPolyaFreqSeq_of_minorOrderedCertificates
    {a : ℕ → ℝ}
    (network : ∀ {n : ℕ}, StrictToeplitzMinorIndex n →
      LGV.FinitePathNetwork ℝ (Fin n))
    (hmatrix : ∀ {n : ℕ} (I : StrictToeplitzMinorIndex n),
      (network I).matrix = I.toeplitzSubmatrix a)
    (certificate : ∀ {n : ℕ} (I : StrictToeplitzMinorIndex n),
      LGV.FinitePathNetwork.OrderedCancellationCertificate (network I))
    (hweight : ∀ {n : ℕ} (I : StrictToeplitzMinorIndex n)
      {s t : Fin n} (p : (network I).Path s t),
      0 ≤ (network I).weight p) :
    IsPolyaFreqSeq a :=
  toeplitz_isTotallyNonneg_of_minorOrderedCertificates
    network hmatrix certificate hweight

end

end RealRooted
