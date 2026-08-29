import RealRooted.ParkingFunctions.ToricContribution.IntervalInsertion

/-!
# The triangular interval-root invariant

This file packages the four facts propagated by horizontal interval insertion:
exact degree, a nonzero value at zero, splitting, and simple roots in `(0,1)`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace ParkingFunctions
namespace ToricContribution

/-- A polynomial has exactly `n` simple roots, all in the open unit interval,
and has a nonzero value at the left endpoint. -/
structure IntervalRootData (p : ℝ[X]) (n : ℕ) : Prop where
  natDegree_eq : p.natDegree = n
  eval_zero_ne : p.eval 0 ≠ 0
  splits : p.Splits
  roots_mem_Ioo : ∀ r ∈ p.roots, r ∈ Set.Ioo (0 : ℝ) 1
  eval_derivative_ne_zero : ∀ r, p.IsRoot r → p.derivative.eval r ≠ 0

theorem IntervalRootData.insertionOperator
    {p : ℝ[X]} {n : ℕ} (hp : IntervalRootData p n)
    (a b : ℝ) (ha : 0 < a) (hba : 0 < b - a) :
    IntervalRootData (insertionOperator a b p) (n + 1) := by
  have hp_ne : p ≠ 0 := by
    intro hzero
    apply hp.eval_zero_ne
    simp [hzero]
  obtain ⟨hdeg, hsplits, hroots, hsimple⟩ :=
    insertionOperator_data_of_simple_roots_Ioo
      a b hp.splits hp.eval_zero_ne
      (fun r hr => hp.roots_mem_Ioo r ((mem_roots hp_ne).mpr hr))
      hp.eval_derivative_ne_zero ha hba
  refine ⟨hp.natDegree_eq ▸ hdeg, ?_, hsplits, hroots, hsimple⟩
  rw [insertionOperator_eval_zero]
  exact mul_ne_zero ha.ne' hp.eval_zero_ne

theorem IntervalRootData.C_mul
    {p : ℝ[X]} {n : ℕ} (hp : IntervalRootData p n) {c : ℝ} (hc : c ≠ 0) :
    IntervalRootData (C c * p) n := by
  have hp_ne : p ≠ 0 := by
    intro hzero
    apply hp.eval_zero_ne
    simp [hzero]
  have hcp_ne : C c * p ≠ 0 := mul_ne_zero (C_ne_zero.mpr hc) hp_ne
  refine ⟨by rw [natDegree_C_mul hc, hp.natDegree_eq], ?_, hp.splits.C_mul c, ?_, ?_⟩
  · simp [hc, hp.eval_zero_ne]
  · intro r hr
    apply hp.roots_mem_Ioo r
    have hr_scaled := (mem_roots hcp_ne).mp hr
    apply (mem_roots hp_ne).mpr
    rw [IsRoot.def] at hr_scaled ⊢
    simpa [hc] using hr_scaled
  · intro r hr
    have hrp : p.IsRoot r := by
      rw [IsRoot.def] at hr ⊢
      simpa [hc] using hr
    have hder := hp.eval_derivative_ne_zero r hrp
    simpa [hc] using mul_ne_zero hc hder

/-- Horizontal propagation through the finite-offset triangle.  The condition
`t ≤ d` is exactly what makes `b-a = d+1-t` strictly positive at every step. -/
theorem triangleFamily_intervalRootData
    {N d : ℕ} {c : ℝ} {J : ℝ[X]}
    (hdN : d ≤ N) (hc : 0 < c)
    (hbase : IntervalRootData ((derivative^[d]) J) (N - d)) :
    ∀ t, t ≤ d → IntervalRootData (triangleFamily c J d t) (N - d + t)
  | 0, _ => by simpa using hbase
  | t + 1, ht => by
      have ht' : t ≤ d := by lia
      have ih := triangleFamily_intervalRootData hdN hc hbase t ht'
      have ha : 0 < c + t := by positivity
      have hba : 0 < (c + d + 1) - (c + t) := by
        have hcast : (t : ℝ) + 1 ≤ d := by exact_mod_cast ht
        linarith
      rw [triangleFamily_succ]
      simpa [Nat.add_assoc] using
        ih.insertionOperator (c + t) (c + d + 1) ha hba

theorem signedTriangleFamily_intervalRootData
    {N d t : ℕ} {c : ℝ} {J : ℝ[X]}
    (hdata : IntervalRootData (triangleFamily c J d t) (N - d + t)) :
    IntervalRootData (signedTriangleFamily c J d t) (N - d + t) := by
  apply hdata.C_mul
  exact pow_ne_zero d (by norm_num)

end ToricContribution
end ParkingFunctions
end RealRooted
