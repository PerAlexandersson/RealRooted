import RealRooted.JacobiDeformation.RootGeometry
import RealRooted.DerivativeSimpleRoots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Jacobi image product

For nodes `t_1, …, t_m`, the image product is the monic polynomial

`imageProduct U V t = ∏_i (X + U / t_i + V / (1 - t_i))`.

At the roots of `p_m` it equals the Jacobi deformation at `δ = 0`
(`RealRooted.JacobiDeformation.BaseProduct`); this file only develops the
product itself.  For distinct interior nodes each root has multiplicity at
most two and the sharp-threshold root is simple, so the derivative is
nonzero, split, simple-rooted, and all its roots lie strictly below
`-(√U + √V) ^ 2`.  We also record the product coordinates of a cleared image
root, the fixed-coordinate logarithmic-derivative identity, the two nodes
behind a double root, and the sign of the second derivative at a double root.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-! ## Roots and derivative of the image product -/

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
    roots_derivative_lt_of_roots_le_of_rootMultiplicity_eq_one
      (imageProduct_splits U V x) hdegree
      (imageProduct_roots_le_neg_sqrt_threshold hU hV x hinterior)
      hthreshold_simple⟩

/-! ## Product coordinates for cleared Jacobi image roots -/

/-- The interior-node product in the image-coordinate identity is positive. -/
theorem prod_node_mul_one_sub_pos {m : ℕ} (t : Fin m → ℝ)
    (ht : ∀ i, 0 < t i ∧ t i < 1) :
    0 < ∏ i, t i * (1 - t i) := by
  refine Finset.prod_pos fun i _ => ?_
  exact mul_pos (ht i).1 (sub_pos.mpr (ht i).2)

private theorem eval_imageProduct_eq_prod {m : ℕ} (U V xi : ℝ) (t : Fin m → ℝ) :
    (imageProduct U V t).eval xi =
      Finset.univ.prod (fun i : Fin m => xi + U / t i + V / (1 - t i)) := by
  unfold imageProduct
  rw [eval_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply, eval_sub, eval_X, eval_C]
  rw [show ((Finset.univ : Finset (Fin m)).1.map (fun i =>
      xi - -(imageValue U V (t i)))).prod =
        Finset.univ.prod (fun i : Fin m => xi - -(imageValue U V (t i))) by rfl]
  apply Finset.prod_congr rfl
  intro i _
  unfold imageValue
  ring

/-- Multiplying the cleared root-image identities at a finite family of
interior nodes yields the exact `imageProduct` coordinate formula. -/
theorem imageProduct_coordinate_identity
    {m : ℕ} (t : Fin m → ℝ) (ht : ∀ i, 0 < t i ∧ t i < 1)
    {xi r z U V : ℝ}
    (hprod : xi * r * z = -U) (hcomp : xi * (1 - r) * (1 - z) = -V) :
    xi ^ m * Finset.univ.prod (fun i : Fin m => r - t i) *
        Finset.univ.prod (fun i : Fin m => z - t i) =
      (-1 : ℝ) ^ m * Finset.univ.prod (fun i : Fin m => t i * (1 - t i)) *
        (imageProduct U V t).eval xi := by
  have hterm : ∀ i : Fin m,
      xi * (r - t i) * (z - t i) =
        -(t i * (1 - t i)) * (xi + U / t i + V / (1 - t i)) := by
    intro i
    have ht0 : t i ≠ 0 := (ht i).1.ne'
    have h1t0 : 1 - t i ≠ 0 := (sub_pos.mpr (ht i).2).ne'
    have hcleared := image_root_product_cleared hprod hcomp (t := t i)
    field_simp [ht0, h1t0]
    linarith [hcleared]
  have hterms :
      Finset.univ.prod (fun i : Fin m => xi * (r - t i) * (z - t i)) =
        Finset.univ.prod (fun i : Fin m =>
          -(t i * (1 - t i)) * (xi + U / t i + V / (1 - t i))) := by
    refine Finset.prod_congr rfl fun i _ => hterm i
  have himage := eval_imageProduct_eq_prod U V xi t
  calc
    xi ^ m * Finset.univ.prod (fun i : Fin m => r - t i) *
        Finset.univ.prod (fun i : Fin m => z - t i) =
        Finset.univ.prod (fun i : Fin m => xi * (r - t i) * (z - t i)) := by
          simp [Finset.prod_mul_distrib, mul_assoc]
    _ = Finset.univ.prod (fun i : Fin m =>
          -(t i * (1 - t i)) * (xi + U / t i + V / (1 - t i))) := hterms
    _ = Finset.univ.prod (fun i : Fin m =>
          ((-1 : ℝ) * (t i * (1 - t i))) *
            (xi + U / t i + V / (1 - t i))) := by
          apply Finset.prod_congr rfl
          intro i _
          ring
    _ = Finset.univ.prod (fun i : Fin m => (-1 : ℝ) * (t i * (1 - t i))) *
          Finset.univ.prod (fun i : Fin m =>
            xi + U / t i + V / (1 - t i)) := by
          rw [Finset.prod_mul_distrib]
    _ = (Finset.univ.prod (fun _i : Fin m => (-1 : ℝ)) *
          Finset.univ.prod (fun i : Fin m => t i * (1 - t i))) *
          Finset.univ.prod (fun i : Fin m =>
            xi + U / t i + V / (1 - t i)) := by
          rw [Finset.prod_mul_distrib]
    _ = (-1 : ℝ) ^ m * Finset.univ.prod (fun i : Fin m => t i * (1 - t i)) *
          (imageProduct U V t).eval xi := by
          rw [himage]
          simp

/-! ## Fixed-coordinate derivative identity for the image product -/

private theorem eval_derivative_prod_div_eval_prod
    {ι : Type*} (s : Finset ι) (g : ι → ℝ[X]) (x : ℝ)
    (h : ∀ i ∈ s, (g i).eval x ≠ 0) :
    (derivative (∏ i ∈ s, g i)).eval x / (∏ i ∈ s, g i).eval x =
      ∑ i ∈ s, (derivative (g i)).eval x / (g i).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hprod : (∏ i ∈ s, g i).eval x ≠ 0 := by
        rw [Polynomial.eval_prod]
        exact Finset.prod_ne_zero_iff.mpr fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hga : (g a).eval x ≠ 0 := h a (Finset.mem_insert_self a s)
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Polynomial.derivative_mul]
      simp only [Polynomial.eval_add, Polynomial.eval_mul]
      rw [← ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
      field_simp

private theorem image_node_log_derivative
    (t xi r z U V : ℝ) (ht0 : t ≠ 0) (ht1 : 1 - t ≠ 0)
    (hr : r - t ≠ 0) (hz : z - t ≠ 0)
    (himage : xi + (U / t + V / (1 - t)) ≠ 0)
    (hprod : xi * r * z = -U) (hcomp : xi * (1 - r) * (1 - z) = -V) :
    xi * (r - z) / (xi + (U / t + V / (1 - t))) =
      (r - z) + r * (1 - r) / (r - t) - z * (1 - z) / (z - t) := by
  have hU : U = -(xi * r * z) := by linarith
  have hV : V = -(xi * (1 - r) * (1 - z)) := by linarith
  subst U
  subst V
  rw [div_eq_iff himage]
  field_simp [ht0, ht1, hr, hz]
  ring

private theorem imageProduct_eq_prod_imageValue {m : ℕ} (U V : ℝ) (t : Fin m → ℝ) :
    imageProduct U V t = Finset.univ.prod
      (fun i : Fin m => (X : ℝ[X]) + C (imageValue U V (t i))) := by
  unfold imageProduct
  simp only [Multiset.map_map, Function.comp_apply]
  rw [show ((Finset.univ : Finset (Fin m)).1.map (fun i =>
      X - C (-(imageValue U V (t i))))).prod =
        Finset.univ.prod (fun i : Fin m => X - C (-(imageValue U V (t i)))) by rfl]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_neg]
  ring

/-- The fixed-coordinate logarithmic derivative identity for the
image product.  The hypotheses allow the empty family `Fin 0`. -/
theorem imageProduct_derivative_identity
    {m : ℕ} (t : Fin m → ℝ) (ht : ∀ i, 0 < t i ∧ t i < 1)
    {U V xi r z : ℝ}
    (hprod : xi * r * z = -U) (hcomp : xi * (1 - r) * (1 - z) = -V)
    (hqr : (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i)).eval r ≠ 0)
    (hqz : (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i)).eval z ≠ 0)
    (himage : (imageProduct U V t).eval xi ≠ 0) :
    xi * (r - z) * (imageProduct U V t).derivative.eval xi /
        (imageProduct U V t).eval xi =
      (m : ℝ) * (r - z) +
        r * (1 - r) *
            (derivative (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i))).eval r /
          (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i)).eval r -
        z * (1 - z) *
            (derivative (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i))).eval z /
          (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i)).eval z := by
  let g : Fin m → ℝ[X] := fun i => X + C (imageValue U V (t i))
  have himageProduct : imageProduct U V t = ∏ i, g i := by
    simpa only [g] using imageProduct_eq_prod_imageValue U V t
  have ht0 : ∀ i : Fin m, t i ≠ 0 := fun i => (ht i).1.ne'
  have ht1 : ∀ i : Fin m, 1 - t i ≠ 0 := fun i =>
    (sub_pos.mpr (ht i).2).ne'
  have hfacr : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      (X - C (t i)).eval r ≠ 0 := by
    intro i hi
    rw [Polynomial.eval_prod] at hqr
    exact Finset.prod_ne_zero_iff.mp hqr i hi
  have hfacz : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      (X - C (t i)).eval z ≠ 0 := by
    intro i hi
    rw [Polynomial.eval_prod] at hqz
    exact Finset.prod_ne_zero_iff.mp hqz i hi
  have hfacxi : ∀ i ∈ (Finset.univ : Finset (Fin m)), (g i).eval xi ≠ 0 := by
    intro i hi
    rw [himageProduct, Polynomial.eval_prod] at himage
    exact Finset.prod_ne_zero_iff.mp himage i hi
  have hqderr :
      (derivative (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i))).eval r /
          (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i)).eval r =
        ∑ i, 1 / (r - t i) := by
    rw [eval_derivative_prod_div_eval_prod _ _ _ hfacr]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hqderz :
      (derivative (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i))).eval z /
          (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i)).eval z =
        ∑ i, 1 / (z - t i) := by
    rw [eval_derivative_prod_div_eval_prod _ _ _ hfacz]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hgder :
      (derivative (Finset.univ.prod g)).eval xi / (Finset.univ.prod g).eval xi =
        ∑ i, 1 / (xi + (U / t i + V / (1 - t i))) := by
    rw [eval_derivative_prod_div_eval_prod _ _ _ hfacxi]
    exact Finset.sum_congr rfl fun i _ => by simp [g, imageValue]
  rw [himageProduct]
  calc
    xi * (r - z) * (derivative (Finset.univ.prod g)).eval xi /
        (Finset.univ.prod g).eval xi =
        ∑ i, xi * (r - z) / (xi + (U / t i + V / (1 - t i))) := by
          rw [mul_div_assoc, hgder, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [mul_one_div]
    _ = ∑ i, ((r - z) + r * (1 - r) / (r - t i) -
          z * (1 - z) / (z - t i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          apply image_node_log_derivative (t i) xi r z U V (ht0 i) (ht1 i)
          · simpa using hfacr i (Finset.mem_univ i)
          · simpa using hfacz i (Finset.mem_univ i)
          · simpa [g, imageValue] using hfacxi i (Finset.mem_univ i)
          · exact hprod
          · exact hcomp
    _ = (m : ℝ) * (r - z) +
          r * (1 - r) *
              (derivative
                (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i))).eval r /
            (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i)).eval r -
          z * (1 - z) *
              (derivative
                (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i))).eval z /
            (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i)).eval z := by
          have e0 : ∑ _i : Fin m, (r - z) = (m : ℝ) * (r - z) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have e1 : ∑ i : Fin m, r * (1 - r) / (r - t i) =
              r * (1 - r) * ∑ i : Fin m, 1 / (r - t i) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => (mul_one_div _ _).symm
          have e2 : ∑ i : Fin m, z * (1 - z) / (z - t i) =
              z * (1 - z) * ∑ i : Fin m, 1 / (z - t i) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => (mul_one_div _ _).symm
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, e0, e1, e2,
            ← hqderr, ← hqderz]
          ring

/-- At a zero of the image-product derivative, the fixed-coordinate right
hand side of `imageProduct_derivative_identity` vanishes. -/
theorem imageProduct_derivative_identity_of_derivative_eval_zero
    {m : ℕ} (t : Fin m → ℝ) (ht : ∀ i, 0 < t i ∧ t i < 1)
    {U V xi r z : ℝ}
    (hprod : xi * r * z = -U) (hcomp : xi * (1 - r) * (1 - z) = -V)
    (hqr : (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i)).eval r ≠ 0)
    (hqz : (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i)).eval z ≠ 0)
    (himage : (imageProduct U V t).eval xi ≠ 0)
    (hderivative : (imageProduct U V t).derivative.eval xi = 0) :
    (m : ℝ) * (r - z) +
        r * (1 - r) *
            (derivative (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i))).eval r /
          (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i)).eval r -
        z * (1 - z) *
            (derivative (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i))).eval z /
          (Finset.univ.prod fun i : Fin m => (X : ℝ[X]) - C (t i)).eval z = 0 := by
  rw [← imageProduct_derivative_identity t ht hprod hcomp hqr hqz himage,
    hderivative, mul_zero, zero_div]

/-! ## Nodes at a double root of the image product

A common root of the image product and its derivative has multiplicity at
least two.  We extract two distinct nodes producing that root and clear the
two corresponding image equations.
-/

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

/-! ## The second derivative at a double image root -/

/-- The second derivative of `(X - C c)^2 * g`, evaluated at the double root `c`,
is `2 * g c`. -/
private theorem eval_derivative_derivative_sq_mul (c : ℝ) (g : ℝ[X]) :
    (derivative (derivative ((X - C c) ^ 2 * g))).eval c = 2 * g.eval c := by
  simp [derivative_mul, pow_two, add_mul]
  ring

/-- The derivative of the node polynomial at `t a` is the product over all
other nodes. -/
private theorem eval_derivative_prod_X_sub_C {m : ℕ} (t : Fin m → ℝ) (a : Fin m) :
    (derivative (∏ i : Fin m, (X - C (t i)))).eval (t a) =
      ∏ i ∈ (univ : Finset (Fin m)).erase a, (t a - t i) := by
  classical
  rw [derivative_prod_finset, eval_finsetSum, Finset.sum_eq_single a]
  · simp [eval_prod]
  · intro i _ hia
    simp only [eval_prod, eval_sub, eval_X, eval_C, derivative_sub, derivative_X,
      derivative_C, sub_zero, mul_one]
    refine Finset.prod_eq_zero (i := a) ?_ ?_
    · exact Finset.mem_erase.mpr ⟨fun h => hia (h ▸ rfl), Finset.mem_univ a⟩
    · ring
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The cleared scalar identity for an image coordinate at an interior node. -/
private theorem image_coordinate_identity {r z s U V xi : ℝ}
    (hs0 : s ≠ 0) (hs1 : (1 : ℝ) - s ≠ 0)
    (hU : xi * r * z = -U) (hV : xi * (1 - r) * (1 - z) = -V) :
    xi + (U / s + V / (1 - s)) =
      (-xi / (s * (1 - s))) * ((r - s) * (z - s)) := by
  have hUe : U = -(xi * r * z) := by linarith
  have hVe : V = -(xi * (1 - r) * (1 - z)) := by linarith
  subst hUe
  subst hVe
  field_simp
  ring

/-- Rewrite the image product as its finite product of image factors. -/
private theorem imageProduct_eq_prod_X_add_C {m : ℕ} (U V : ℝ) (t : Fin m → ℝ) :
    imageProduct U V t = ∏ i : Fin m, (X + C (U / t i + V / (1 - t i))) := by
  unfold imageProduct
  simp only [Multiset.map_map, Function.comp_apply]
  rw [show ((Finset.univ : Finset (Fin m)).1.map (fun i =>
      X - C (-(imageValue U V (t i))))).prod =
        Finset.univ.prod (fun i : Fin m => X - C (-(imageValue U V (t i)))) by rfl]
  apply Finset.prod_congr rfl
  intro i _
  unfold imageValue
  rw [map_neg]
  ring

/-- At a double image root, the second derivative of `imageProduct` has the
strict sign obtained from the two distinguished node derivatives. -/
theorem imageProduct_double_root_sign {m : ℕ} (t : Fin m → ℝ) (U V xi : ℝ)
    (hinj : Function.Injective t)
    (ht0 : ∀ i : Fin m, 0 < t i) (ht1 : ∀ i : Fin m, t i < 1)
    (a b : Fin m) (hab : a ≠ b) (hxi : xi < 0)
    (hU : xi * t a * t b = -U) (hV : xi * (1 - t a) * (1 - t b) = -V) :
    (imageProduct U V t).derivative.derivative.eval xi *
        (derivative (∏ i : Fin m, (X - C (t i)))).eval (t a) *
        (derivative (∏ i : Fin m, (X - C (t i)))).eval (t b) < 0 := by
  classical
  set c : Fin m → ℝ := fun i => U / t i + V / (1 - t i) with hc
  set I : Finset (Fin m) := ((univ : Finset (Fin m)).erase a).erase b with hI
  have hne0 : ∀ i : Fin m, t i ≠ 0 := fun i => ne_of_gt (ht0 i)
  have hne1 : ∀ i : Fin m, (1 : ℝ) - t i ≠ 0 := fun i =>
    (sub_pos.mpr (ht1 i)).ne'
  have hca : c a = -xi := by
    have h := image_coordinate_identity (r := t a) (z := t b) (s := t a)
      (hne0 a) (hne1 a) hU hV
    simp only [sub_self, zero_mul, mul_zero] at h
    simp only [hc]
    linarith
  have hcb : c b = -xi := by
    have h := image_coordinate_identity (r := t a) (z := t b) (s := t b)
      (hne0 b) (hne1 b) hU hV
    simp only [sub_self, mul_zero] at h
    simp only [hc]
    linarith
  have hbmem : b ∈ (univ : Finset (Fin m)).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, mem_univ b⟩
  have hamem : a ∈ (univ : Finset (Fin m)).erase b :=
    Finset.mem_erase.mpr ⟨hab, mem_univ a⟩
  have himage : imageProduct U V t = ∏ i : Fin m, (X + C (c i)) := by
    rw [imageProduct_eq_prod_X_add_C]
  have hf : (∏ i : Fin m, (X + C (c i))) =
      (X - C xi) ^ 2 * ∏ i ∈ I, (X + C (c i)) := by
    rw [← Finset.mul_prod_erase (univ : Finset (Fin m)) (fun i => X + C (c i))
      (mem_univ a), ← Finset.mul_prod_erase ((univ : Finset (Fin m)).erase a)
      (fun i => X + C (c i)) hbmem, hca, hcb, hI]
    rw [map_neg, ← sub_eq_add_neg]
    ring
  have hf2 : (derivative (derivative (∏ i : Fin m, (X + C (c i))))).eval xi =
      2 * ∏ i ∈ I, (xi + c i) := by
    rw [hf, eval_derivative_derivative_sq_mul, eval_prod]
    simp
  have hqa : (derivative (∏ i : Fin m, (X - C (t i)))).eval (t a) =
      (t a - t b) * ∏ i ∈ I, (t a - t i) := by
    rw [eval_derivative_prod_X_sub_C, hI,
      ← Finset.mul_prod_erase ((univ : Finset (Fin m)).erase a) (fun i => t a - t i) hbmem]
  have hqb : (derivative (∏ i : Fin m, (X - C (t i)))).eval (t b) =
      (t b - t a) * ∏ i ∈ I, (t b - t i) := by
    rw [eval_derivative_prod_X_sub_C, hI, Finset.erase_right_comm,
      ← Finset.mul_prod_erase ((univ : Finset (Fin m)).erase b) (fun i => t b - t i) hamem]
  have hprod : (∏ i ∈ I, (xi + c i)) =
      (∏ i ∈ I, (-xi / (t i * (1 - t i)))) *
        ((∏ i ∈ I, (t a - t i)) * ∏ i ∈ I, (t b - t i)) := by
    have hcongr : ∀ i ∈ I, xi + c i =
        (-xi / (t i * (1 - t i))) * ((t a - t i) * (t b - t i)) :=
      fun i _ => image_coordinate_identity (hne0 i) (hne1 i) hU hV
    rw [Finset.prod_congr rfl hcongr, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hW : 0 < ∏ i ∈ I, (-xi / (t i * (1 - t i))) := by
    refine Finset.prod_pos ?_
    intro i _
    have hden : 0 < t i * (1 - t i) :=
      mul_pos (ht0 i) (sub_pos.mpr (ht1 i))
    exact div_pos (by linarith) hden
  have hPa : (∏ i ∈ I, (t a - t i)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    have hia : i ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp (hI ▸ hi)).2).1
    exact sub_ne_zero_of_ne fun h => hia (hinj h.symm)
  have hPb : (∏ i ∈ I, (t b - t i)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    have hib : i ≠ b := (Finset.mem_erase.mp (hI ▸ hi)).1
    exact sub_ne_zero_of_ne fun h => hib (hinj h.symm)
  have htab : t a - t b ≠ 0 := sub_ne_zero_of_ne fun h => hab (hinj h)
  rw [himage, hqa, hqb, hf2, hprod]
  have hsq1 : 0 < (t a - t b) ^ 2 := by positivity
  have hsq2 : 0 < (∏ i ∈ I, (t a - t i)) ^ 2 := by positivity
  have hsq3 : 0 < (∏ i ∈ I, (t b - t i)) ^ 2 := by positivity
  have hkey : 0 < 2 * (∏ i ∈ I, (-xi / (t i * (1 - t i)))) * (t a - t b) ^ 2 *
      (∏ i ∈ I, (t a - t i)) ^ 2 * (∏ i ∈ I, (t b - t i)) ^ 2 := by
    positivity
  linarith [hkey]

/-- The two-node double-root sign, retaining the empty remaining product. -/
theorem imageProduct_double_root_sign_two_nodes (t : Fin 2 → ℝ) (U V xi : ℝ)
    (hinj : Function.Injective t)
    (ht0 : ∀ i : Fin 2, 0 < t i) (ht1 : ∀ i : Fin 2, t i < 1) (hxi : xi < 0)
    (hU : xi * t 0 * t 1 = -U) (hV : xi * (1 - t 0) * (1 - t 1) = -V) :
    (imageProduct U V t).derivative.derivative.eval xi *
        (derivative (∏ i : Fin 2, (X - C (t i)))).eval (t 0) *
        (derivative (∏ i : Fin 2, (X - C (t i)))).eval (t 1) < 0 :=
  imageProduct_double_root_sign t U V xi hinj ht0 ht1 0 1 (by decide) hxi hU hV

end RealRooted.JacobiDeformation
