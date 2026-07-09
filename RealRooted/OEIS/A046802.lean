import RealRooted.ThresholdMatrix

/-!
# OEIS A046802

This module is the sequence-facing surface for the A046802 backend.  The
mathematical work lives in `RealRooted.ThresholdMatrix`, where the
Haglund--Zhang binomial Eulerian refined vector is encoded as a threshold
matrix recursion and the reusable interlacing backend is proved.

The declarations here keep the generated OEIS file boundary explicit: the
interlacing certificate, nonzero proof, and splitting proof are bundled for
downstream tactics and generated sequence ledgers.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace OEIS

/-- Generated-file interlacing certificate for the A046802 refinement. -/
theorem A046802_generated_interlaces (n : ℕ) :
    IsInterlacingSeq0Nonneg (A046802Refined n) :=
  A046802_interlaces n

/-- Generated-file real-rootedness certificate for each nonzero refined
polynomial in the A046802 backend vector. -/
theorem A046802_generated_refined_realRooted (n : ℕ) :
    ∀ f ∈ A046802Refined n, f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  A046802_refined_realRooted n

/-- Generated-file alias for the tactic-facing `rr_s_inversion` route. -/
theorem A046802_generated_rr_s_inversion_binomial_eulerian_sequence (n : ℕ) :
    A046802 n ≠ 0 ∧ (A046802 n).Splits :=
  rr_s_inversion_binomial_eulerian_sequence n

/-- Generated-file real-rootedness certificate for A046802. -/
theorem A046802_generated_realRooted (n : ℕ) :
    A046802 n ≠ 0 ∧ (A046802 n).Splits :=
  A046802_generated_rr_s_inversion_binomial_eulerian_sequence n

/-- Generated-file nonzero certificate for A046802. -/
theorem A046802_generated_ne_zero (n : ℕ) :
    A046802 n ≠ 0 :=
  (A046802_generated_realRooted n).1

/-- Generated-file splitting certificate for A046802. -/
theorem A046802_generated_splits (n : ℕ) :
    (A046802 n).Splits :=
  (A046802_generated_realRooted n).2

/-- Bundled certificate for the Haglund--Zhang representation of A046802. -/
theorem A046802_certificate (n : ℕ) :
    IsInterlacingSeq0Nonneg (A046802Refined n) ∧
      A046802 n ≠ 0 ∧ (A046802 n).Splits :=
  ⟨A046802_generated_interlaces n, A046802_generated_ne_zero n,
    A046802_generated_splits n⟩

end OEIS
end RealRooted
