module

public import RealRooted.SimpleRoots
public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import RealRooted.MaWang.StrictStep
import RealRooted.Mathlib.Algebra.Polynomial.Derivative

/-!
# Simple roots under Hermite basis transforms

A basis whose raising operator is an affine multiplier minus a positive
constant times differentiation sends every nonzero real-rooted polynomial to
a polynomial with simple real roots. Repeated roots of the input are allowed.
-/

public section

open Polynomial

namespace RealRooted

/-- A negative constant derivative coefficient makes each affine factor step strict. -/
private theorem affine_derivative_step {f : ℝ[X]} {a b c : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hf : IsSimpleRealRooted f)
    (hpos : HasPosLeadingCoeff f) :
    IsSimpleRealRooted ((C a * X + C b) * f + C (-c) * f.derivative) ∧
      HasPosLeadingCoeff ((C a * X + C b) * f + C (-c) * f.derivative) := by
  let F := (C a * X + C b) * f + C (-c) * f.derivative
  have htop : a * f.leadingCoeff ≠ 0 := ne_of_gt (mul_pos ha hpos)
  have hdeg := natDegree_and_leadingCoeff_quadratic_derivative_add_linear_mul_add
    f (C (-c) * f.derivative) 0 0 b a
    ((natDegree_C_mul_le _ _).trans ((natDegree_derivative_le f).trans (Nat.sub_le _ _)))
    (by simpa using htop)
  have hdegree : F.natDegree = f.natDegree + 1 := by
    simpa [F, add_comm] using hdeg.1
  have hFpos : HasPosLeadingCoeff F := by
    have hlead : F.leadingCoeff = a * f.leadingCoeff := by
      simpa [F, add_comm] using hdeg.2
    change 0 < F.leadingCoeff
    rw [hlead]
    exact mul_pos ha hpos
  refine ⟨?_, hFpos⟩
  by_cases hzero : f.natDegree = 0
  · have hsmall : F.natDegree ≤ 1 := by lia
    have hFne : F ≠ 0 := leadingCoeff_ne_zero.mp (ne_of_gt hFpos)
    exact ⟨hFne, Splits.of_natDegree_le_one hsmall,
      hasSimpleRoots_of_natDegree_le_one hFne hsmall⟩
  · have hstep := MaWang.strictInterl_and_hasSimpleRoots_of_eval_neg
      hf.2.1 hpos hFpos hzero hdegree hf.2.2 (show F = _ by rfl)
      (fun r _ => by simpa using neg_neg_of_pos hc)
    exact ⟨hstep.2.ne_zero, hstep.1.2.1.2, hstep.2⟩

/-- Induction over the real linear factors preserves positive leading coefficient. -/
private theorem basisTransform_prod_simple {B : ℕ → ℝ[X]} {a b c : ℝ}
    (hzero : B 0 = 1) (ha : 0 < a) (hc : 0 < c)
    (hrec : ∀ n, B (n + 1) = (C a * X + C b) * B n + C (-c) * (B n).derivative)
    (s : Multiset ℝ) :
    IsSimpleRealRooted (basisTransform B (s.map (fun r => X - C r)).prod) ∧
      HasPosLeadingCoeff (basisTransform B (s.map (fun r => X - C r)).prod) := by
  induction s using Multiset.induction_on with
  | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero]
      have heq : basisTransform B 1 = 1 := by
        simpa [hzero] using basisTransform_C B 1
      rw [heq]
      exact ⟨⟨one_ne_zero, Splits.one,
        hasSimpleRoots_of_natDegree_le_one one_ne_zero (by simp)⟩, by simp [HasPosLeadingCoeff]⟩
  | @cons r s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      have heq := basisTransform_mul_X_add_C_of_succ_derivative B
        (C a * X + C b) (C (-c)) hrec (-r) (s.map (fun r => X - C r)).prod
      rw [map_neg, ← sub_eq_add_neg] at heq
      rw [heq]
      have hlinear : C a * X + C b + -C r = C a * X + C (b - r) := by
        simp [sub_eq_add_neg, add_assoc]
      rw [hlinear]
      exact affine_derivative_step ha hc ih.1 ih.2

/-- A positive affine raising operator with a negative derivative term makes
the roots of every nonzero split input simple. -/
theorem isSimpleRealRooted_basisTransform_of_raising
    {B : ℕ → ℝ[X]} {a b c : ℝ} (hzero : B 0 = 1) (ha : 0 < a) (hc : 0 < c)
    (hrec : ∀ n, B (n + 1) = (C a * X + C b) * B n + C (-c) * (B n).derivative)
    {p : ℝ[X]} (hp : p.Splits) (hp0 : p ≠ 0) :
    IsSimpleRealRooted (basisTransform B p) := by
  have hprod := (basisTransform_prod_simple hzero ha hc hrec p.roots).1
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have heq : basisTransform B p =
      C p.leadingCoeff * basisTransform B (p.roots.map (fun r => X - C r)).prod := by
    conv_lhs => rw [hp.eq_prod_roots]
    exact linearMap_C_mul (basisTransformₗ B) _ _
  rw [heq]
  exact ⟨mul_ne_zero (C_ne_zero.mpr hlc) hprod.1, hprod.2.1.C_mul _,
    hprod.2.2.C_mul hlc⟩

/-- The same raising operator preserves splitting, including the zero input. -/
theorem splits_basisTransform_of_raising
    {B : ℕ → ℝ[X]} {a b c : ℝ} (hzero : B 0 = 1) (ha : 0 < a) (hc : 0 < c)
    (hrec : ∀ n, B (n + 1) = (C a * X + C b) * B n + C (-c) * (B n).derivative)
    {p : ℝ[X]} (hp : p.Splits) :
    (basisTransform B p).Splits := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact (isSimpleRealRooted_basisTransform_of_raising hzero ha hc hrec hp hp0).2.1

end RealRooted
