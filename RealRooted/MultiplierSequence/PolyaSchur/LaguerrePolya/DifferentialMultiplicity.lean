module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.DifferentialApply
public import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.PolynomialAlgebra
public import Mathlib.Analysis.Analytic.Order
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.DerivativeMultiplicity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Entire-target multiplicity for real-rooted differential symbols

A multiple zero of a nonzero finite real-rooted differential image of an LP
function forces the input to vanish to the output order plus the symbol degree.
Translation gives the exponential-polynomial case of Craven–Csordas (1994),
Lemma 4.2. No growth restriction or nonzero constant coefficient is needed.
The nonzero-output premise is essential for annihilated exponential inputs.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- Multiplicity descent through every factor of a real root multiset. -/
private theorem vanishing_differential_root_product {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (s : Multiset ℝ) {x : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hne : ∃ z, (((s.map (fun r => X - C r)).prod).map ofRealHom).differentialApply f z ≠ 0)
    (hzero : ∀ j < k, iteratedDeriv (𝕜 := ℂ) (F := ℂ) j
      ((((s.map (fun r => X - C r)).prod).map ofRealHom).differentialApply f) x = 0) :
    ∀ j < k + s.card, iteratedDeriv j f x = 0 := by
  induction s using Multiset.induction_on generalizing k with
  | empty => simpa using hzero
  | @cons r s ih =>
      let q : ℝ[X] := (s.map (fun r => X - C r)).prod
      let g : ℂ → ℂ := (q.map ofRealHom).differentialApply f
      have hq : q.Splits := Splits.multisetProd (by simp [Splits.X_sub_C])
      have hg : IsLaguerrePolya g := hf.differentialApply hq
      have heq :
          ((((r ::ₘ s).map (fun u => X - C u)).prod).map ofRealHom).differentialApply f =
            fun z => _root_.deriv g z + ((-r : ℝ) : ℂ) * g z := by
        simp only [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul,
          Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ofRealHom_eq_coe]
        rw [sub_eq_add_neg, ← C_neg, differentialApply_mul _ _ hf.differentiable,
          differentialApply_add, differentialApply_X, differentialApply_C]
        simp only [ofReal_neg]
        rfl
      rw [heq] at hne hzero
      have hg0 : ∃ z, g z ≠ 0 := by
        by_contra h
        have hz : g = 0 := by ext z; simpa using not_exists.mp h z
        simp [hz] at hne
      have hback := hg.vanishing_of_linear_differential (-r) hne hk (by
        intro j hj
        simpa only [iteratedDeriv_linear_differential hg.differentiable] using hzero j hj)
      have hprev := ih (by lia : 2 ≤ k + 1) hg0 hback
      intro j hj
      exact hprev j (by simpa only [Multiset.card_cons, Nat.add_assoc, Nat.add_comm 1] using hj)

/-- A zero of order at least `k ≥ 2` of a nonzero real-rooted finite
 differential image forces order at least `k + degree(q)` in the LP input. -/
theorem IsLaguerrePolya.vanishing_of_differentialApply {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {q : ℝ[X]} (hq : q.Splits)
    (hne : ∃ z, (q.map ofRealHom).differentialApply f z ≠ 0) {x : ℝ} {k : ℕ}
    (hk : 2 ≤ k)
    (hzero : ∀ j < k, iteratedDeriv j ((q.map ofRealHom).differentialApply f) x = 0) :
    ∀ j < k + q.natDegree, iteratedDeriv j f x = 0 := by
  have hq0 : q ≠ 0 := by
    intro hz
    simp [hz] at hne
  have hlc : (q.leadingCoeff : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (leadingCoeff_ne_zero.mpr hq0)
  let g := (((q.roots.map (fun r => X - C r)).prod).map ofRealHom).differentialApply f
  have heq : (q.map ofRealHom).differentialApply f =
      fun z => (q.leadingCoeff : ℂ) * g z := by
    conv_lhs => rw [hq.eq_prod_roots]
    rw [Polynomial.map_mul, Polynomial.map_C, differentialApply_mul _ _ hf.differentiable,
      differentialApply_C]
    rfl
  have hg0 : ∃ z, g z ≠ 0 := by
    obtain ⟨z, hz⟩ := hne
    refine ⟨z, ?_⟩
    rw [heq] at hz
    exact (mul_ne_zero_iff.mp hz).2
  have hgvan : ∀ j < k, iteratedDeriv j g x = 0 := by
    intro j hj
    have h := hzero j hj
    rw [heq, iteratedDeriv_const_mul_field] at h
    exact (mul_eq_zero.mp h).resolve_left hlc
  rw [hq.natDegree_eq_card_roots]
  exact vanishing_differential_root_product hf q.roots hk hg0 hgvan

/-- Translating a finite differential image traces a multiple zero back to the
translated input point. This is the exponential-polynomial differential-symbol
case of Craven–Csordas (1994), Lemma 4.2, with arbitrary multiple-zero order. -/
theorem IsLaguerrePolya.vanishing_of_differentialApply_translate {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {q : ℝ[X]} (hq : q.Splits) (a : ℝ)
    (hne : ∃ z, (q.map ofRealHom).differentialApply f z ≠ 0) {x : ℝ} {k : ℕ}
    (hk : 2 ≤ k)
    (hzero : ∀ j < k, iteratedDeriv (𝕜 := ℂ) (F := ℂ) j
      (fun z => (q.map ofRealHom).differentialApply f (z + a)) x = 0) :
    ∀ j < k + q.natDegree, iteratedDeriv j f (x + a : ℝ) = 0 := by
  apply hf.vanishing_of_differentialApply hq hne hk
  intro j hj
  simpa only [iteratedDeriv_comp_add_const, ofReal_add] using hzero j hj

/-- Analytic-order form of multiplicity descent for a nonzero finite
real-rooted differential image of an LP function. -/
theorem IsLaguerrePolya.le_analyticOrderAt_of_differentialApply {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {q : ℝ[X]} (hq : q.Splits)
    (hne : ∃ z, (q.map ofRealHom).differentialApply f z ≠ 0) {x : ℝ} {k : ℕ}
    (hk : 2 ≤ k)
    (horder : (k : ℕ∞) ≤ analyticOrderAt ((q.map ofRealHom).differentialApply f) (x : ℂ)) :
    ((k + q.natDegree : ℕ) : ℕ∞) ≤ analyticOrderAt f (x : ℂ) := by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hf.differentiable.analyticAt _)]
  apply hf.vanishing_of_differentialApply hq hne hk
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    ((hf.differentialApply hq).differentiable.analyticAt _)).mp horder

/-- A finite real-rooted differential image has a simple zero whenever the
input has a nonvanishing derivative below the symbol degree plus two there. -/
theorem IsLaguerrePolya.deriv_differentialApply_ne_zero_of_jet {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {q : ℝ[X]} (hq : q.Splits)
    (hne : ∃ z, (q.map ofRealHom).differentialApply f z ≠ 0) {x : ℝ}
    (hjet : ∃ j < q.natDegree + 2, iteratedDeriv j f x ≠ 0)
    (hzero : (q.map ofRealHom).differentialApply f x = 0) :
    _root_.deriv ((q.map ofRealHom).differentialApply f) x ≠ 0 := by
  intro hd
  have hvan := hf.vanishing_of_differentialApply hq hne (k := 2) (by lia) (by
    intro j hj
    have hjcases : j = 0 ∨ j = 1 := by lia
    rcases hjcases with rfl | rfl
    · simpa only [iteratedDeriv_zero] using hzero
    · simpa only [iteratedDeriv_one] using hd)
  obtain ⟨j, hj, hne⟩ := hjet
  exact hne (hvan j (by lia))

end RealRooted
