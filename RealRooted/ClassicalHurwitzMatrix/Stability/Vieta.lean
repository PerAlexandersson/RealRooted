import RealRooted.ClassicalHurwitzMatrix.Stability

/-!
# Vieta consequences of strict Hurwitz stability

Strict left-half-plane root location forces the next-to-leading coefficient
to have the same positive sign as a positive leading coefficient.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A positive-leading nonconstant strictly Hurwitz-stable polynomial has
positive next-to-leading coefficient. -/
theorem IsStrictlyHurwitzStable.nextCoeff_pos {p : ℝ[X]}
    (h : IsStrictlyHurwitzStable p) (hlead : HasPosLeadingCoeff p)
    (hdegree : p.natDegree ≠ 0) : 0 < p.nextCoeff := by
  let q := complexify p
  have hqDegree : q.natDegree = p.natDegree := by
    simp [q, complexify]
  have hrootsNe : q.roots ≠ 0 := by
    intro hrootsZero
    have hcard :=
      Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits q)
    rw [hrootsZero] at hcard
    simp only [Multiset.card_zero] at hcard
    lia
  have hsumReNeg : q.roots.sum.re < 0 := by
    change Complex.reAddGroupHom q.roots.sum < 0
    rw [map_multiset_sum Complex.reAddGroupHom]
    simpa using Multiset.sum_lt_sum_of_nonempty
      (f := Complex.re) (g := fun _ => (0 : ℝ)) hrootsNe
      (fun z hz => h z (isRoot_of_mem_roots hz))
  have hvieta :=
    (IsAlgClosed.splits q).nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hvietaRe := congrArg Complex.re hvieta
  have hqNextCoeff : q.nextCoeff = (p.nextCoeff : ℂ) := by
    exact Polynomial.nextCoeff_map Complex.ofReal_injective p
  have hqLeadingCoeff : q.leadingCoeff = (p.leadingCoeff : ℂ) := by
    exact Polynomial.leadingCoeff_map_of_injective Complex.ofReal_injective p
  rw [hqNextCoeff, hqLeadingCoeff] at hvietaRe
  norm_num at hvietaRe
  unfold HasPosLeadingCoeff at hlead
  nlinarith

/-- Coefficient form of `IsStrictlyHurwitzStable.nextCoeff_pos`. -/
theorem IsStrictlyHurwitzStable.coeff_natDegree_sub_one_pos {p : ℝ[X]}
    (h : IsStrictlyHurwitzStable p) (hlead : HasPosLeadingCoeff p)
    (hdegree : p.natDegree ≠ 0) :
    0 < p.coeff (p.natDegree - 1) := by
  rw [← Polynomial.nextCoeff_of_natDegree_pos (Nat.pos_of_ne_zero hdegree)]
  exact h.nextCoeff_pos hlead hdegree

end RealRooted
