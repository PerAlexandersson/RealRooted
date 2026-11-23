module

public import RealRooted.MultiplierSequence
public import RealRooted.SimpleRoots
import RealRooted.MittagLeffler.Growth
import RealRooted.MultiplierSequence.Veronese
import RealRooted.MultiplierSequence.JensenDerivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.JensenSimple

/-!
# Simple negative Jensen roots for Mittag--Leffler sections

For every stride at least two and every residue below the stride, the
Mittag--Leffler Jensen polynomials have their full degree and only simple
negative zeros. Residue zero gives Kim--Kim (2015), Proposition 2.4;
the residue extension is a derived consequence of the same argument.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- Integer-stride factorial Jensen polynomials have only simple real roots
when the stride is at least two. The degree-zero boundary is included. -/
theorem isSimpleRealRooted_jensenPolynomial_factorial_veronese
    {r s : ℕ} (hr : 2 ≤ r) (hs : s < r) (d : ℕ) :
    IsSimpleRealRooted (jensenPolynomial d
      (fun k ↦ (k.factorial : ℝ) / (s + r * k).factorial)) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by decide) hr
  have hrR : 1 < (r : ℝ) := by exact_mod_cast (show 1 < r by lia)
  have horder : (r : ℝ)⁻¹ < 1 := by
    rw [inv_eq_one_div]
    exact (div_lt_one (by positivity)).mpr hrR
  have h := IsLaguerrePolya.simple_jensenPolynomial
    (isLaguerrePolyaTypeI_mittagLefflerNat hs).toLaguerrePolya
      (orderLE_mittagLefflerNat hr0) horder
      (mittagLefflerNat_zero_ne_zero hs) (mittagLefflerNat_ne_polynomial hs) d
  simpa only [iteratedDeriv_mittagLefflerNat_zero hs, ofReal_re] using h

/-- The factorial Jensen polynomial has exact degree and strictly negative
roots for every valid residue, including the exponential stride-one boundary. -/
theorem jensenPolynomial_factorial_veronese_degree_roots
    {r s : ℕ} (hs : s < r) (d : ℕ) :
    (jensenPolynomial d (fun k ↦
      (k.factorial : ℝ) / (s + r * k).factorial)).natDegree = d ∧
      ∀ x ∈ (jensenPolynomial d (fun k ↦
        (k.factorial : ℝ) / (s + r * k).factorial)).roots, x < 0 := by
  let gamma : ℕ → ℝ := fun k ↦ (k.factorial : ℝ) / (s + r * k).factorial
  have hpos (k : ℕ) : 0 < gamma k := by dsimp only [gamma]; positivity
  have hpf := isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence
    (isPFMultiplierSequence_factorial_veronese hs) d
  refine ⟨natDegree_jensenPolynomial (hpos d).ne', fun x hx ↦ ?_⟩
  apply lt_of_le_of_ne (hpf.roots_nonpos x hx)
  intro hx0
  subst x
  have heval := (mem_roots (ne_zero_of_mem_roots hx)).mp hx
  have h0 : (jensenPolynomial d gamma).eval 0 ≠ 0 := by
    simpa only [← Polynomial.coeff_zero_eq_eval_zero, coeff_jensenPolynomial,
      Nat.zero_le, ite_true, Nat.choose_zero_right, Nat.cast_one, one_mul] using
      (hpos 0).ne'
  exact h0 heval

end RealRooted
