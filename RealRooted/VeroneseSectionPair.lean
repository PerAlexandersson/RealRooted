import RealRooted.VeroneseMatrix

/-!
# Strict proper position between normalized Veronese sections

The production Veronese matrix theorem packages the residue sections of one
nonnegative real-rooted polynomial as a descending weak interlacing list.
This file extracts the strict two-section corollary when both residues are
nonzero.  Unlike the legacy pair-section tactics, it needs no conditional
`*Statement` bridge.

This sequence-independent corollary was first used in
`ProofsOeis.VeronesePairs`.
-/

open Polynomial

noncomputable section

namespace RealRooted

theorem prec_veroneseSectionPolynomial_of_residue_lt
    {r j k : ℕ} (hr : 0 < r) (hjk : j < k) (hk : k < r)
    {p : ℝ[X]} (hpnn : HasNonnegCoeffs p) (hp0 : p ≠ 0)
    (hps : p.Splits)
    (hj0 : veroneseSectionPolynomial r j p ≠ 0)
    (hk0 : veroneseSectionPolynomial r k p ≠ 0) :
    Prec (veroneseSectionPolynomial r k p)
      (veroneseSectionPolynomial r j p) := by
  let fs := veroneseSectionPolynomialListDesc r p
  have hpkg :=
    isInterlacingSeq0Nonneg_and_real_veroneseSectionPolynomialListDesc_of_realRooted_nonneg
      hr hpnn hp0 hps
  let ir : Fin r := ⟨r - 1 - k, by lia⟩
  let qr : Fin r := ⟨r - 1 - j, by lia⟩
  let i : Fin fs.length := ⟨ir.1, by simp [fs]⟩
  let q : Fin fs.length := ⟨qr.1, by simp [fs]⟩
  have hiq : i < q := by
    simp [i, q, ir, qr]
    lia
  have hprec0 : Prec0 (fs.get i) (fs.get q) := by
    exact (isInterlacingSeq0_iff_pairwise.mp hpkg.1.1).rel_get_of_lt hiq
  have hi : fs.get i = veroneseSectionPolynomial r k p := by
    rw [show fs.get i = veroneseSectionPolynomial r (r - 1 - ir.1) p by
      exact get_veroneseSectionPolynomialListDesc (p := p) ir]
    simp [ir]
    congr 1
    lia
  have hq : fs.get q = veroneseSectionPolynomial r j p := by
    rw [show fs.get q = veroneseSectionPolynomial r (r - 1 - qr.1) p by
      exact get_veroneseSectionPolynomialListDesc (p := p) qr]
    simp [qr]
    congr 1
    lia
  rw [hi, hq] at hprec0
  exact hprec0.toPrec_of_ne hk0 hj0

end RealRooted
