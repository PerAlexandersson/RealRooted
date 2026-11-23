module

public import RealRooted.RiemannHypothesis.Hermite
public import RealRooted.SimpleRoots
import RealRooted.RiemannHypothesis
import RealRooted.Hermite.FiniteTransfer
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Positivity

/-!
# Simple roots of the xi Hermite Jensen polynomials

Under Mathlib's Riemann hypothesis, every xi Hermite Jensen polynomial has
simple real roots. This strengthens splitting of the finite polynomial family;
it makes no simplicity assertion about the zeros of the Riemann xi function.
-/

public section

namespace RealRooted

/-- Every xi Hermite Jensen polynomial has its specified degree, independently of RH. -/
theorem natDegree_riemannXiHermitePolynomial (d n : ℕ) :
    (riemannXiHermitePolynomial d n).natDegree = d := by
  apply natDegree_hermiteJensenPolynomial
  simpa using (riemannXiCoeff_pos n).ne'

/-- The xi Hermite Jensen normalization has a strictly positive leading coefficient. -/
theorem leadingCoeff_riemannXiHermitePolynomial (d n : ℕ) :
    (riemannXiHermitePolynomial d n).leadingCoeff = riemannXiCoeff n * 2 ^ d := by
  simpa [riemannXiHermitePolynomial] using leadingCoeff_hermiteJensenPolynomial (d := d)
    (gamma := fun k => riemannXiCoeff (n + k)) (by simpa using (riemannXiCoeff_pos n).ne')

/-- The leading coefficient is positive for all degrees and shifts without RH. -/
theorem leadingCoeff_riemannXiHermitePolynomial_pos (d n : ℕ) :
    0 < (riemannXiHermitePolynomial d n).leadingCoeff := by
  rw [leadingCoeff_riemannXiHermitePolynomial]
  exact mul_pos (riemannXiCoeff_pos n) (by positivity)

/-- No xi Hermite Jensen polynomial is the zero polynomial. -/
theorem riemannXiHermitePolynomial_ne_zero (d n : ℕ) :
    riemannXiHermitePolynomial d n ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mp (leadingCoeff_riemannXiHermitePolynomial_pos d n).ne'

/-- RH implies simple real roots for every degree and shift of the normalized
xi Hermite Jensen polynomials. Constants are included. -/
theorem isSimpleRealRooted_riemannXiHermitePolynomial
    (hRH : RiemannHypothesis) (d n : ℕ) :
    IsSimpleRealRooted (riemannXiHermitePolynomial d n) := by
  apply isSimpleRealRooted_hermiteJensenPolynomial_of_coeff_zero
    (riemannXiJensenPolynomial_splits hRH d n)
  simpa using (riemannXiCoeff_pos n).ne'

/-- RH is equivalent to simple real-rootedness of the unshifted xi Hermite
Jensen family. -/
theorem riemannHypothesis_iff_simple_hermite_zero :
    RiemannHypothesis ↔ ∀ d, IsSimpleRealRooted (riemannXiHermitePolynomial d 0) := by
  constructor
  · intro h d
    exact isSimpleRealRooted_riemannXiHermitePolynomial h d 0
  · intro h
    exact riemannHypothesis_iff_riemannXiHermitePolynomial_zero_splits.mpr
      (fun d => (h d).2.1)

/-- RH is equivalent to simple real-rootedness of the xi Hermite Jensen
polynomials in every degree and shift. -/
theorem riemannHypothesis_iff_simple_hermite :
    RiemannHypothesis ↔ ∀ d n, IsSimpleRealRooted (riemannXiHermitePolynomial d n) := by
  constructor
  · exact isSimpleRealRooted_riemannXiHermitePolynomial
  · intro h
    exact riemannHypothesis_iff_simple_hermite_zero.mpr (fun d => h d 0)

end RealRooted
