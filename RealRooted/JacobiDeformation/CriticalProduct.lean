import RealRooted.JacobiDeformation.CriticalCoordinates
import RealRooted.JacobiDeformation.CriticalThreshold
import RealRooted.JacobiDeformation.DerivativeSimple

/-!
# The critical image product

This module packages the elementary consequences of the product in equation
(18), independently of the finite-kernel identity that later identifies that
product with the deformation at `δ = 0`.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The monic product whose roots are the negatives of the Jacobi image
values at the supplied nodes. -/
def imageProduct {m : ℕ} (U V : ℝ) (x : Fin m → ℝ) : ℝ[X] :=
  ((Finset.univ.1.map fun i => -(imageValue U V (x i))).map
    (fun r => X - C r)).prod

theorem imageProduct_ne_zero {m : ℕ} (U V : ℝ) (x : Fin m → ℝ) :
    imageProduct U V x ≠ 0 := by
  unfold imageProduct
  apply Multiset.prod_ne_zero
  simp only [Multiset.mem_map, not_exists, not_and]
  intro i _
  exact X_sub_C_ne_zero _

theorem roots_imageProduct {m : ℕ} (U V : ℝ) (x : Fin m → ℝ) :
    (imageProduct U V x).roots =
      Finset.univ.1.map (fun i => -(imageValue U V (x i))) := by
  unfold imageProduct
  exact Polynomial.roots_multiset_prod_X_sub_C _

theorem imageProduct_splits {m : ℕ} (U V : ℝ) (x : Fin m → ℝ) :
    (imageProduct U V x).Splits := by
  unfold imageProduct
  refine Multiset.prod_induction (fun p : ℝ[X] => p.Splits) _
    (fun _ _ hp hq => hp.mul hq) Splits.one ?_
  intro p hp
  simp only [Multiset.mem_map] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact Splits.X_sub_C _

theorem imageProduct_natDegree {m : ℕ} (U V : ℝ) (x : Fin m → ℝ) :
    (imageProduct U V x).natDegree = m := by
  calc
    (imageProduct U V x).natDegree = (imageProduct U V x).roots.card :=
      (card_roots_of_splits (imageProduct_splits U V x)).symm
    _ = m := by rw [roots_imageProduct, Multiset.card_map]; simp

/-- Distinct interior nodes give image-product root multiplicity at most two,
because an image level is cut out by a quadratic. -/
theorem imageProduct_rootMultiplicity_le_two {m : ℕ} {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V) (x : Fin m → ℝ)
    (hx : Function.Injective x) (hinterior : ∀ i, 0 < x i ∧ x i < 1) (a : ℝ) :
    (imageProduct U V x).rootMultiplicity a ≤ 2 := by
  rw [← count_roots, roots_imageProduct, Multiset.count_map]
  change (Finset.univ.filter fun i => a = -(imageValue U V (x i))).card ≤ 2
  by_contra hle
  have hthree : 2 < (Finset.univ.filter fun i =>
      a = -(imageValue U V (x i))).card := by lia
  rw [Finset.two_lt_card] at hthree
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := hthree
  have hivalue : imageValue U V (x i) = -a := by
    have := (Finset.mem_filter.mp hi).2
    linarith
  have hjvalue : imageValue U V (x j) = -a := by
    have := (Finset.mem_filter.mp hj).2
    linarith
  have hkvalue : imageValue U V (x k) = -a := by
    have := (Finset.mem_filter.mp hk).2
    linarith
  rcases imageValue_three_solution_collision hU hV
      (hinterior i).1 (hinterior i).2
      (hinterior j).1 (hinterior j).2
      (hinterior k).1 (hinterior k).2
      hivalue hjvalue hkvalue with hxy | hxz | hyz
  · exact hij (hx hxy)
  · exact hik (hx hxz)
  · exact hjk (hx hyz)

/-- The sharp-threshold image value occurs at most once among distinct
interior nodes. -/
theorem imageProduct_threshold_rootMultiplicity_le_one {m : ℕ} {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V) (x : Fin m → ℝ)
    (hx : Function.Injective x) (hinterior : ∀ i, 0 < x i ∧ x i < 1) :
    (imageProduct U V x).rootMultiplicity
        (-(Real.sqrt U + Real.sqrt V) ^ 2) ≤ 1 := by
  rw [← count_roots, roots_imageProduct, Multiset.count_map]
  change (Finset.univ.filter fun i =>
    -(Real.sqrt U + Real.sqrt V) ^ 2 = -(imageValue U V (x i))).card ≤ 1
  by_contra hle
  have htwo : 1 < (Finset.univ.filter fun i =>
      -(Real.sqrt U + Real.sqrt V) ^ 2 = -(imageValue U V (x i))).card := by
    lia
  rw [Finset.one_lt_card] at htwo
  obtain ⟨i, hi, j, hj, hij⟩ := htwo
  have hivalue : imageValue U V (x i) =
      (Real.sqrt U + Real.sqrt V) ^ 2 := by
    have := (Finset.mem_filter.mp hi).2
    linarith
  have hjvalue : imageValue U V (x j) =
      (Real.sqrt U + Real.sqrt V) ^ 2 := by
    have := (Finset.mem_filter.mp hj).2
    linarith
  exact hij (hx (imageValue_sqrt_threshold_unique hU hV
    (hinterior i).1 (hinterior i).2
    (hinterior j).1 (hinterior j).2 hivalue hjvalue))

/-- Every image-product root lies at or below the negative sharp threshold. -/
theorem imageProduct_roots_le_neg_sqrt_threshold {m : ℕ} {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V) (x : Fin m → ℝ)
    (hinterior : ∀ i, 0 < x i ∧ x i < 1) :
    ∀ r ∈ (imageProduct U V x).roots,
      r ≤ -(Real.sqrt U + Real.sqrt V) ^ 2 := by
  intro r hr
  rw [roots_imageProduct] at hr
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hr
  have hbound := sqrt_threshold_le_imageValue hU hV
    (hinterior i).1 (hinterior i).2
  linarith

/-- The critical image product has a nonzero split derivative with simple
roots, all strictly below the negative sharp threshold. -/
theorem imageProduct_derivative_package {m : ℕ} {U V : ℝ} (hm : 1 ≤ m)
    (hU : 0 < U) (hV : 0 < V) (x : Fin m → ℝ)
    (hx : Function.Injective x) (hinterior : ∀ i, 0 < x i ∧ x i < 1) :
    (imageProduct U V x).derivative ≠ 0 ∧
      (imageProduct U V x).derivative.Splits ∧
      HasSimpleRoots (imageProduct U V x).derivative ∧
      ∀ r ∈ (imageProduct U V x).derivative.roots,
        r < -(Real.sqrt U + Real.sqrt V) ^ 2 := by
  have hdegree : (imageProduct U V x).natDegree ≠ 0 := by
    rw [imageProduct_natDegree]
    lia
  obtain ⟨hder0, hdersplits, hdersimple⟩ :=
    derivative_ne_zero_splits_hasSimpleRoots_of_rootMultiplicity_le_two
      (imageProduct_splits U V x) hdegree
      (imageProduct_rootMultiplicity_le_two hU hV x hx hinterior)
  have hthreshold_simple :
      (imageProduct U V x).IsRoot (-(Real.sqrt U + Real.sqrt V) ^ 2) →
        (imageProduct U V x).rootMultiplicity
          (-(Real.sqrt U + Real.sqrt V) ^ 2) = 1 := by
    intro hroot
    apply Nat.le_antisymm
    · exact imageProduct_threshold_rootMultiplicity_le_one hU hV x hx hinterior
    · exact (rootMultiplicity_pos (imageProduct_ne_zero U V x)).mpr hroot
  exact ⟨hder0, hdersplits, hdersimple,
    derivative_roots_lt_of_roots_le_of_root_simple_at_upper
      (imageProduct_splits U V x) hdegree
      (imageProduct_roots_le_neg_sqrt_threshold hU hV x hinterior)
      hthreshold_simple⟩

end RealRooted.JacobiDeformation
