import RealRooted.JacobiDeformation.CriticalProduct

/-!
# Nodes at a double root of the image product

A common root of the actual image product and its derivative has multiplicity
at least two.  This file extracts two distinct nodes producing that root and
clears the two corresponding image equations.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- A common root of the image product and its derivative comes from two
distinct interior nodes.  Their common image level supplies the two cleared
coordinate identities used in the double-root calculation. -/
theorem exists_imageProduct_double_nodes {m : ℕ} {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V) (t : Fin m → ℝ)
    (htinj : Function.Injective t) (ht : ∀ i, 0 < t i ∧ t i < 1) {xi : ℝ}
    (hroot : (imageProduct U V t).IsRoot xi)
    (hder : (imageProduct U V t).derivative.IsRoot xi) :
    ∃ a b : Fin m, a ≠ b ∧ xi < 0 ∧
      xi * t a * t b = -U ∧ xi * (1 - t a) * (1 - t b) = -V := by
  have hmult : 1 < (imageProduct U V t).rootMultiplicity xi :=
    (one_lt_rootMultiplicity_iff_isRoot (imageProduct_ne_zero U V t)).mpr
      ⟨hroot, hder⟩
  rw [← count_roots, roots_imageProduct, Multiset.count_map] at hmult
  change 1 < (Finset.univ.filter fun i => xi = -(imageValue U V (t i))).card at hmult
  rw [Finset.one_lt_card] at hmult
  obtain ⟨a, ha, b, hb, hab⟩ := hmult
  have hia : xi = -(imageValue U V (t a)) := (Finset.mem_filter.mp ha).2
  have hib : xi = -(imageValue U V (t b)) := (Finset.mem_filter.mp hb).2
  have hvalue_a : imageValue U V (t a) = -xi := by linarith
  have hvalue_b : imageValue U V (t b) = -xi := by linarith
  have hxi : xi < 0 := by
    have himage : 0 < imageValue U V (t a) := by
      unfold imageValue
      exact add_pos (div_pos hU (ht a).1) (div_pos hV (sub_pos.mpr (ht a).2))
    linarith
  have hquadratic_a : imageQuadratic (-xi) U V (t a) = 0 :=
    (imageQuadratic_eq_zero_iff (ht a).1 (ht a).2).mpr hvalue_a
  have hquadratic_b : imageQuadratic (-xi) U V (t b) = 0 :=
    (imageQuadratic_eq_zero_iff (ht b).1 (ht b).2).mpr hvalue_b
  have hnodes : t a ≠ t b := fun hab' => hab (htinj hab')
  have hfactor_zero : (-xi) * (1 - t a - t b) + U - V = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hnodes)
    rw [← imageQuadratic_sub, hquadratic_a, hquadratic_b]
    ring
  have hfactor : xi * (1 - t a - t b) + V - U = 0 := by
    linarith
  have hcleared : xi * t a * (1 - t a) + U * (1 - t a) + V * t a = 0 := by
    unfold imageQuadratic at hquadratic_a
    linarith
  have hproduct : xi * t a * t b + U = 0 := by
    linear_combination hcleared - t a * hfactor
  have hcomplement : xi * (1 - t a) * (1 - t b) + V = 0 := by
    linear_combination hcleared + (1 - t a) * hfactor
  refine ⟨a, b, hab, hxi, ?_, ?_⟩ <;> linarith

end RealRooted.JacobiDeformation
