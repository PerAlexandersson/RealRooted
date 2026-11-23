module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.Hermite.Companions
import RealRooted.RiemannHypothesis
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Positivity
import RealRooted.MultiplierSequence.InvPochhammer
import RealRooted.MultiplierSequence.PolyaSchur

/-!
# Xi Hermite companions under RH

Finite multiplier weights give further simple real-rooted Hermite families
under Mathlib's RH. The factorial family specializes the companion following
O'Sullivan's Corollary 3.8; positive Pochhammer parameters give a derived family.
-/

@[expose] public section

open Polynomial

namespace RealRooted

/-- A weighted Hermite companion for a shift of the normalized xi coefficients. -/
noncomputable def riemannXiHermiteCompanion (d n : ℕ) (weight : ℕ → ℝ) : ℝ[X] :=
  hermiteCompanion d (fun k => riemannXiCoeff (n + k)) weight

/-- The factorial-weighted xi Hermite companion. -/
noncomputable def riemannXiHermiteFactorial (d n : ℕ) : ℝ[X] :=
  hermiteFactorialPolynomial d (fun k => riemannXiCoeff (n + k))

/-- The rising-factorial-weighted xi Hermite companion. -/
noncomputable def riemannXiHermitePochhammer (d n : ℕ) (a : ℝ) : ℝ[X] :=
  hermitePochhammerPolynomial d (fun k => riemannXiCoeff (n + k)) a

/-- RH gives splitting for every finite multiplier weight, allowing vanishing entries. -/
theorem riemannXiHermiteCompanion_splits (hRH : RiemannHypothesis)
    (d n : ℕ) {weight : ℕ → ℝ} (hweight : IsFiniteMultiplierSequence d weight) :
    (riemannXiHermiteCompanion d n weight).Splits :=
  hermiteCompanion_splits hweight (riemannXiJensenPolynomial_splits hRH d n)

/-- A nonzero final weight makes an RH xi Hermite companion simple-real-rooted. -/
theorem isSimpleRealRooted_riemannXiHermiteCompanion
    (hRH : RiemannHypothesis) (d n : ℕ) {weight : ℕ → ℝ}
    (hweight : IsFiniteMultiplierSequence d weight) (hw : weight d ≠ 0) :
    IsSimpleRealRooted (riemannXiHermiteCompanion d n weight) := by
  apply isSimpleRealRooted_hermiteCompanion_of_coeff_zero hweight
    (riemannXiJensenPolynomial_splits hRH d n) _ hw
  simpa using (riemannXiCoeff_pos n).ne'

/-- Nonzero final weight gives exact degree independently of RH. -/
theorem natDegree_riemannXiHermiteCompanion (d n : ℕ) {weight : ℕ → ℝ}
    (hw : weight d ≠ 0) : (riemannXiHermiteCompanion d n weight).natDegree = d := by
  apply natDegree_hermiteCompanion _ hw
  simpa using (riemannXiCoeff_pos n).ne'

/-- The leading coefficient is controlled by the final weight, independently of RH. -/
theorem leadingCoeff_riemannXiHermiteCompanion (d n : ℕ) {weight : ℕ → ℝ}
    (hw : weight d ≠ 0) :
    (riemannXiHermiteCompanion d n weight).leadingCoeff = riemannXiCoeff n * weight d * 2 ^ d := by
  simpa [riemannXiHermiteCompanion] using leadingCoeff_hermiteCompanion (d := d)
    (gamma := fun k => riemannXiCoeff (n + k)) (by simpa using (riemannXiCoeff_pos n).ne') hw

/-- RH implies simple real roots for every factorial-weighted xi Hermite companion. -/
theorem isSimpleRealRooted_riemannXiHermiteFactorial
    (hRH : RiemannHypothesis) (d n : ℕ) :
    IsSimpleRealRooted (riemannXiHermiteFactorial d n) :=
  isSimpleRealRooted_riemannXiHermiteCompanion hRH d n
    (isMultiplierSequence_inv_factorial.finite d) (by positivity)

/-- Every factorial-weighted xi Hermite companion has exact degree without RH. -/
theorem natDegree_riemannXiHermiteFactorial (d n : ℕ) :
    (riemannXiHermiteFactorial d n).natDegree = d :=
  natDegree_riemannXiHermiteCompanion d n (by positivity)

/-- RH gives simple roots for every positive Pochhammer parameter and every shift. -/
theorem isSimpleRealRooted_riemannXiHermitePochhammer
    (hRH : RiemannHypothesis) (d n : ℕ) {a : ℝ} (ha : 0 < a) :
    IsSimpleRealRooted (riemannXiHermitePochhammer d n a) :=
  isSimpleRealRooted_riemannXiHermiteCompanion hRH d n
    ((isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp
      (isPFMultiplierSequence_inv_ascPochhammer ha)).1.finite d)
    (inv_ne_zero (ascPochhammer_pos d a ha).ne')

/-- Positive Pochhammer parameters give exact degree independently of RH. -/
theorem natDegree_riemannXiHermitePochhammer (d n : ℕ) {a : ℝ} (ha : 0 < a) :
    (riemannXiHermitePochhammer d n a).natDegree = d :=
  natDegree_riemannXiHermiteCompanion d n (inv_ne_zero (ascPochhammer_pos d a ha).ne')

end RealRooted
