module

public import RealRooted.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.Multiset.Sort
public import RealRooted.Derivative.Algebra

public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-! ## Rolle's theorem for polynomials -/

theorem exists_root_derivative_between {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) :
    ∃ c, a < c ∧ c < b ∧ p.derivative.IsRoot c := by
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_zero hab p.continuous.continuousOn
    (by simp_all) fun x _ => p.hasDerivAt x
  exact ⟨c, hc_mem.1, hc_mem.2, hc_eq⟩

/-- Between two distinct real roots of a polynomial lies a root of its
derivative. -/
theorem exists_mem_Ioo_isRoot_derivative {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) :
    ∃ c ∈ Set.Ioo a b, p.derivative.IsRoot c := by
  obtain ⟨c, hac, hcb, hc⟩ := exists_root_derivative_between hab ha hb
  exact ⟨c, ⟨hac, hcb⟩, hc⟩

theorem isRoot_derivative_of_rootMultiplicity_ge_two {p : ℝ[X]} {r : ℝ}
    (hm : 2 ≤ p.rootMultiplicity r) :
    p.derivative.IsRoot r := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hm
  have hdvd : (X - C r) ^ 2 ∣ p := (le_rootMultiplicity_iff hp0).mp hm
  have hdvd' : (X - C r) ^ (2 - 1) ∣ p.derivative :=
    pow_sub_one_dvd_derivative_of_pow_dvd hdvd
  simp only [Nat.reduceSubDiff, pow_one] at hdvd'
  exact dvd_iff_isRoot.mp hdvd'

end RealRooted
