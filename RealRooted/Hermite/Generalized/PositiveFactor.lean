module

public import RealRooted.Hermite.Generalized.Basic
public import RealRooted.SimpleRoots
import RealRooted.Hermite.Generalized.JensenIdentity
import RealRooted.MittagLeffler.Jensen
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# The positive compressed factor of a generalized Hermite polynomial

The factorial Jensen polynomial has simple negative roots. Reflection gives
the positive factor in the generalized Hermite power substitution.
-/

public section

open Polynomial

namespace RealRooted

/-- The reflected factorial Jensen polynomial has simple positive roots. -/
private theorem factorialJensen_neg_data {p s : ℕ} (hp : 2 ≤ p) (hs : s < p)
    (q : ℕ) :
    let Q := (jensenPolynomial q
      (fun k ↦ (k.factorial : ℝ) / (s + p * k).factorial)).comp (-X)
    IsSimpleRealRooted Q ∧ Q.natDegree = q ∧ ∀ a ∈ Q.roots, 0 < a := by
  let J := jensenPolynomial q (fun k ↦ (k.factorial : ℝ) / (s + p * k).factorial)
  have hJ := isSimpleRealRooted_jensenPolynomial_factorial_veronese hp hs q
  obtain ⟨hdeg, hneg⟩ := jensenPolynomial_factorial_veronese_degree_roots hs q
  have hsimple : HasSimpleRoots (J.comp (-X)) := by
    simpa using hJ.2.2.comp_C_mul_X_add_C (a := -1) (b := 0) (by norm_num)
  refine ⟨⟨hsimple.ne_zero, hJ.2.1.comp_neg_X, hsimple⟩, ?_, ?_⟩
  · simpa using hdeg
  · intro a ha
    have hroot : J.IsRoot (-a) := by
      simpa only [IsRoot.def, eval_comp, eval_neg, eval_X] using isRoot_of_mem_roots ha
    have hlt := hneg (-a) ((mem_roots hJ.1).mpr hroot)
    linarith

/-- A generalized Hermite polynomial has a simple positive-root factor of
the exact quotient degree. The constant and zero-degree cases are included. -/
theorem generalizedHermite_eq_C_mul_X_pow_comp {p s : ℕ}
    (hp : 2 ≤ p) (hs : s < p) (q : ℕ) :
    ∃ (c : ℝ) (Q : ℝ[X]), c ≠ 0 ∧
      generalizedHermite p (s + p * q) = C c * (X ^ s * Q.comp (X ^ p)) ∧
      IsSimpleRealRooted Q ∧ Q.natDegree = q ∧ ∀ a ∈ Q.roots, 0 < a := by
  let c : ℝ := (-1 : ℝ) ^ q * (s + p * q).factorial / q.factorial
  let Q := (jensenPolynomial q
    (fun k ↦ (k.factorial : ℝ) / (s + p * k).factorial)).comp (-X)
  refine ⟨c, Q, ?_, ?_, factorialJensen_neg_data hp hs q⟩
  · exact div_ne_zero (mul_ne_zero (pow_ne_zero q (by norm_num)) (by positivity))
      (by positivity)
  · rw [generalizedHermite_eq_jensenPolynomial hs q]
    simp only [Q, comp_assoc, neg_comp, X_comp]
    ring

end RealRooted
