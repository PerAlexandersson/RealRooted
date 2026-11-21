module

public import RealRooted.Apolarity
import RealRooted.GraceHalfPlane

/-!
# Scaling covariance and half-plane separation for apolarity

These algebraic consequences of Grace's theorem support the unpublished
quartic exponential-row argument in RealRooted issue #2415:
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

public section

open Polynomial

namespace RealRooted

private lemma coeff_comp_scale {R : Type*} [CommRing R] (p : R[X]) (a : R) (k : ℕ) :
    (p.comp (C a * X)).coeff k = p.coeff k * a ^ k := by
  induction p using Polynomial.induction_on' with
  | add p q ih ih' => simp [add_comp, ih, ih', add_mul]
  | monomial n b =>
    simp only [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_comp, pow_comp, mul_pow,
      ← map_pow, coeff_C_mul]
    by_cases h : n = k
    · subst k; simp
    · simp [coeff_X_pow, Ne.symm h]

/-- Scaling both variables of the degree-`n` apolar pairing multiplies it by `aⁿ`.
The identity holds over every commutative ring, including at `a = 0`. -/
theorem apolarPairing_comp_C_mul_X {R : Type*} [CommRing R]
    (n : ℕ) (f g : R[X]) (a : R) :
    apolarPairing n (f.comp (C a * X)) (g.comp (C a * X)) =
      a ^ n * apolarPairing n f g := by
  simp only [apolarPairing, coeff_comp_scale, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Finset.mem_range_succ_iff.mp hk
  have ha : a ^ k * a ^ (n - k) = a ^ n := by rw [← pow_add, Nat.add_sub_of_le hk']
  calc
    _ = ((-1 : R) ^ k * (n.choose k : R) * f.coeff k * g.coeff (n - k)) *
        (a ^ k * a ^ (n - k)) := by ring
    _ = _ := by rw [ha]; ring

/-- For a nonzero scale, apolarity is invariant under simultaneous dilation. -/
theorem areApolar_comp_C_mul_X_iff {R : Type*} [CommRing R] [IsDomain R]
    (n : ℕ) (f g : R[X]) {a : R} (ha : a ≠ 0) :
    AreApolar n (f.comp (C a * X)) (g.comp (C a * X)) ↔ AreApolar n f g := by
  simp only [AreApolar, apolarPairing_comp_C_mul_X,
    mul_eq_zero, pow_ne_zero n ha, false_or]

/-- The upper-half-plane form of Grace also permits a degree bound for the first lift.
This handles degree drops of auxiliary polynomials without a limiting argument. -/
theorem exists_isRoot_le_im_of_areApolar_of_natDegree_le {n : ℕ} {b : ℝ} {f g : ℂ[X]}
    (hf : (binomialLift n f).natDegree ≤ n) (hg : (binomialLift n g).natDegree = n)
    (hap : AreApolar n f g) (hroots : ∀ z, (binomialLift n f).IsRoot z → b ≤ z.im) :
    ∃ z, b ≤ z.im ∧ (binomialLift n g).IsRoot z := by
  have hfhat : (binomialLift n (negComp f)).natDegree ≤ n := by
    rw [negComp_binomialLift, negComp, natDegree_comp]
    simpa using hf
  have hghat : (binomialLift n (negComp g)).natDegree = n := by
    rw [negComp_binomialLift, negComp, natDegree_comp]
    simpa using hg
  have hroothat : (binomialLift n (negComp f)).RootsIn (lowerHalf (-b)) := by
    rw [negComp_binomialLift]
    intro w hw
    have hw' : (binomialLift n f).IsRoot (-w) := by
      simpa [negComp, IsRoot.def] using hw
    have hh := hroots (-w) hw'
    simp only [Complex.neg_im] at hh
    rw [mem_lowerHalf]
    linarith
  obtain ⟨w, hw, hmem⟩ := grace_apolarity_lowerHalf hfhat hghat
    ((areApolar_negComp_iff n f g).mpr hap) hroothat
  refine ⟨-w, ?_, ?_⟩
  · have hm : w.im ≤ -b := mem_lowerHalf.mp hmem
    simpa using neg_le_neg hm
  · rw [negComp_binomialLift] at hw
    simpa [negComp, IsRoot.def] using hw

end RealRooted
