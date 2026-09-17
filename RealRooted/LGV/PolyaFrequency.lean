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

end

end RealRooted
