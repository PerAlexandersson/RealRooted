import RealRooted.Tactic.SignAssembly

/-!
# Sign assembly tactic examples

The examples keep the sign and endpoint certificates explicit and exercise
all supported conclusions of the degree-gap-two frontend.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace Tactic

private def linearSource : ℝ[X] := X - C (-1)

private def cubicTarget : ℝ[X] :=
  (X - C (-3)) * (X - C (-2)) * (X - C 0)

private lemma linearSource_natDegree : linearSource.natDegree = 1 := by
  rw [linearSource, natDegree_X_sub_C]

private lemma cubicTarget_natDegree : cubicTarget.natDegree = 3 := by
  rw [cubicTarget,
    natDegree_mul
      (mul_ne_zero (X_sub_C_ne_zero (-3 : ℝ))
        (X_sub_C_ne_zero (-2 : ℝ)))
      (X_sub_C_ne_zero (0 : ℝ)),
    natDegree_mul (X_sub_C_ne_zero (-3 : ℝ))
      (X_sub_C_ne_zero (-2 : ℝ)),
    natDegree_X_sub_C, natDegree_X_sub_C, natDegree_X_sub_C]

private def quadraticSource : ℝ[X] :=
  (X - C (-1)) * (X - C 1)

private def quarticTarget : ℝ[X] :=
  ((X - C (-3)) * (X - C (-2))) * ((X - C 0) * (X - C 2))

private lemma quadraticSource_natDegree : quadraticSource.natDegree = 2 := by
  rw [quadraticSource,
    natDegree_mul (X_sub_C_ne_zero (-1 : ℝ)) (X_sub_C_ne_zero (1 : ℝ)),
    natDegree_X_sub_C, natDegree_X_sub_C]

private lemma quarticTarget_natDegree : quarticTarget.natDegree = 4 := by
  rw [quarticTarget,
    natDegree_mul
      (mul_ne_zero (X_sub_C_ne_zero (-3 : ℝ)) (X_sub_C_ne_zero (-2 : ℝ)))
      (mul_ne_zero (X_sub_C_ne_zero (0 : ℝ)) (X_sub_C_ne_zero (2 : ℝ))),
    natDegree_mul (X_sub_C_ne_zero (-3 : ℝ)) (X_sub_C_ne_zero (-2 : ℝ)),
    natDegree_mul (X_sub_C_ne_zero (0 : ℝ)) (X_sub_C_ne_zero (2 : ℝ)),
    natDegree_X_sub_C, natDegree_X_sub_C, natDegree_X_sub_C,
    natDegree_X_sub_C]

private lemma quadraticSource_roots :
    quadraticSource.roots = {(-1 : ℝ), 1} := by
  rw [quadraticSource,
    roots_mul
      (mul_ne_zero (X_sub_C_ne_zero (-1 : ℝ)) (X_sub_C_ne_zero (1 : ℝ))),
    roots_X_sub_C, roots_X_sub_C]
  rfl

example : cubicTarget ≠ 0 ∧ cubicTarget.Splits := by
  rr_sign_assembly_gap_two using
    source_splits := Polynomial.Splits.X_sub_C (-1 : ℝ),
    target_pos := by
      exact
        ((hasPosLeadingCoeff_X_sub_C (-3 : ℝ)).mul
          (hasPosLeadingCoeff_X_sub_C (-2 : ℝ))).mul
            (hasPosLeadingCoeff_X_sub_C (0 : ℝ)),
    target_odd := by
      rw [cubicTarget_natDegree]
      norm_num,
    roots_sorted := (by norm_num : [(-1 : ℝ)].Pairwise (· ≤ ·)),
    roots_eq := by
      simpa [linearSource] using (roots_X_sub_C (-1 : ℝ)).symm,
    degree_gap := by
      change cubicTarget.natDegree = linearSource.natDegree + 2
      rw [cubicTarget_natDegree, linearSource_natDegree],
    roots_nonempty := by norm_num,
    consecutive_signs := by
      intro pre r₁ r₂ rest h
      have := congrArg List.length h
      simp at this
      lia,
    left_sign := by
      show cubicTarget.eval [(-1 : ℝ)].head! < 0
      norm_num [cubicTarget],
    right_sign := by
      change cubicTarget.eval ([(-1 : ℝ)].getLast (by simp)) < 0
      norm_num [cubicTarget],
    witness_lt := (by norm_num : (-5 / 2 : ℝ) < [(-1 : ℝ)].head!),
    witness_sign := by
      show 0 < cubicTarget.eval (-5 / 2 : ℝ)
      norm_num [cubicTarget]

example : quarticTarget ≠ 0 ∧ quarticTarget.Splits := by
  rr_sign_assembly_gap_two_even using
    source_splits :=
      (Polynomial.Splits.X_sub_C (-1 : ℝ)).mul
        (Polynomial.Splits.X_sub_C (1 : ℝ)),
    target_pos := by
      exact
        ((hasPosLeadingCoeff_X_sub_C (-3 : ℝ)).mul
          (hasPosLeadingCoeff_X_sub_C (-2 : ℝ))).mul
            ((hasPosLeadingCoeff_X_sub_C (0 : ℝ)).mul
              (hasPosLeadingCoeff_X_sub_C (2 : ℝ))),
    target_even := by
      show Even quarticTarget.natDegree
      rw [quarticTarget_natDegree]
      norm_num,
    roots_sorted := (by norm_num : [(-1 : ℝ), 1].Pairwise (· ≤ ·)),
    roots_eq := by
      change (↑[(-1 : ℝ), 1] : Multiset ℝ) = quadraticSource.roots
      rw [quadraticSource_roots]
      rfl,
    degree_gap := by
      change quarticTarget.natDegree = quadraticSource.natDegree + 2
      rw [quarticTarget_natDegree, quadraticSource_natDegree],
    roots_nonempty := by norm_num,
    consecutive_signs := by
      intro pre r₁ r₂ rest h
      have hlen := congrArg List.length h
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have hpre : pre = [] := List.length_eq_zero_iff.mp (by lia)
      have hrest : rest = [] := List.length_eq_zero_iff.mp (by lia)
      subst pre
      subst rest
      have hr₁ : r₁ = (-1 : ℝ) := by grind
      have hr₂ : r₂ = (1 : ℝ) := by grind
      subst r₁
      subst r₂
      norm_num [quarticTarget],
    left_sign := by
      show 0 < quarticTarget.eval [(-1 : ℝ), 1].head!
      norm_num [quarticTarget],
    right_sign := by
      change quarticTarget.eval ([(-1 : ℝ), 1].getLast (by simp)) < 0
      norm_num [quarticTarget],
    witness_lt := (by norm_num : (-5 / 2 : ℝ) < [(-1 : ℝ), 1].head!),
    witness_sign := by
      show quarticTarget.eval (-5 / 2 : ℝ) < 0
      norm_num [quarticTarget]

section Abstract

variable {f F : ℝ[X]} {rs : List ℝ} {a : ℝ}
variable (hf_splits : f.Splits)
variable (hF_pos : HasPosLeadingCoeff F)
variable (hF_odd : Odd F.natDegree)
variable (hrs_sorted : rs.Pairwise (· ≤ ·))
variable (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
variable (hdeg : F.natDegree = f.natDegree + 2)
variable (hn : 1 ≤ rs.length)
variable (hsign :
  ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
    rs = pre ++ r₁ :: r₂ :: rest → F.eval r₁ * F.eval r₂ < 0)
variable (hleft : F.eval rs.head! < 0)
variable (hright : F.eval (rs.getLast (by grind)) < 0)
variable (ha_lt : a < rs.head!)
variable (ha_pos : 0 < F.eval a)

example : F.Splits := by
  rr_sign_assembly_gap_two using
    source_splits := hf_splits,
    target_pos := hF_pos,
    target_odd := hF_odd,
    roots_sorted := hrs_sorted,
    roots_eq := hrs_eq,
    degree_gap := hdeg,
    roots_nonempty := hn,
    consecutive_signs := hsign,
    left_sign := hleft,
    right_sign := hright,
    witness_lt := ha_lt,
    witness_sign := ha_pos

example : F ≠ 0 := by
  rr_sign_assembly_gap_two using
    source_splits := hf_splits,
    target_pos := hF_pos,
    target_odd := hF_odd,
    roots_sorted := hrs_sorted,
    roots_eq := hrs_eq,
    degree_gap := hdeg,
    roots_nonempty := hn,
    consecutive_signs := hsign,
    left_sign := hleft,
    right_sign := hright,
    witness_lt := ha_lt,
    witness_sign := ha_pos

end Abstract

section AbstractEven

variable {f F : ℝ[X]} {rs : List ℝ} {a : ℝ}
variable (hf_splits : f.Splits)
variable (hF_pos : HasPosLeadingCoeff F)
variable (hF_even : Even F.natDegree)
variable (hrs_sorted : rs.Pairwise (· ≤ ·))
variable (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
variable (hdeg : F.natDegree = f.natDegree + 2)
variable (hn : 1 ≤ rs.length)
variable (hsign :
  ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
    rs = pre ++ r₁ :: r₂ :: rest → F.eval r₁ * F.eval r₂ < 0)
variable (hleft : 0 < F.eval rs.head!)
variable (hright : F.eval (rs.getLast (by grind)) < 0)
variable (ha_lt : a < rs.head!)
variable (ha_neg : F.eval a < 0)

example : F.Splits := by
  rr_sign_assembly_gap_two_even using
    source_splits := hf_splits,
    target_pos := hF_pos,
    target_even := hF_even,
    roots_sorted := hrs_sorted,
    roots_eq := hrs_eq,
    degree_gap := hdeg,
    roots_nonempty := hn,
    consecutive_signs := hsign,
    left_sign := hleft,
    right_sign := hright,
    witness_lt := ha_lt,
    witness_sign := ha_neg

example : F ≠ 0 := by
  rr_sign_assembly_gap_two_even using
    source_splits := hf_splits,
    target_pos := hF_pos,
    target_even := hF_even,
    roots_sorted := hrs_sorted,
    roots_eq := hrs_eq,
    degree_gap := hdeg,
    roots_nonempty := hn,
    consecutive_signs := hsign,
    left_sign := hleft,
    right_sign := hright,
    witness_lt := ha_lt,
    witness_sign := ha_neg

end AbstractEven

end Tactic
end RealRooted
