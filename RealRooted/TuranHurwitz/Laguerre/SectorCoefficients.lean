module

public import RealRooted.TuranHurwitz.ConvexRegionCoefficients
public import RealRooted.TuranHurwitz.TwoRaySector
public import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The paired coefficient lemma for the part (ii) sector

Rotating the squared roots into the open right half-plane replaces the
argument calculation by a polynomial identity and Gauss–Lucas.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The monic polynomial whose roots are the rotated squares of a multiset. -/
@[expose] noncomputable def rotatedSquareProduct (x : ℂ) (s : Multiset ℂ) : ℂ[X] :=
  (s.map fun r => X - C (x * r ^ 2)).prod

/-- The rotated square product has precisely the prescribed roots, with multiplicity. -/
theorem roots_rotatedSquareProduct (x : ℂ) (s : Multiset ℂ) :
    (rotatedSquareProduct x s).roots = s.map (fun r => x * r ^ 2) := by
  have h := roots_multiset_prod_X_sub_C (s.map fun r => x * r ^ 2)
  simpa only [rotatedSquareProduct, Multiset.map_map, Function.comp_def] using h

/-- The rotated square product is monic. -/
theorem monic_rotatedSquareProduct (x : ℂ) (s : Multiset ℂ) :
    (rotatedSquareProduct x s).Monic := by
  exact monic_multiset_prod_of_monic _ _ (fun r _ => monic_X_sub_C _)

/-- Its degree is the size of the root multiset. -/
theorem natDegree_rotatedSquareProduct (x : ℂ) (s : Multiset ℂ) :
    (rotatedSquareProduct x s).natDegree = s.card := by
  have h := natDegree_multiset_prod_X_sub_C_eq_card (s.map fun r => x * r ^ 2)
  simpa only [rotatedSquareProduct, Multiset.map_map, Function.comp_def,
    Multiset.card_map] using h

private theorem root_product_pair (x : ℂ) (s : Multiset ℂ) :
    C (x ^ s.card) * (s.map (fun r => X - C r)).prod *
        ((s.map (fun r => X - C r)).prod).comp (-X) =
      C ((-1 : ℂ) ^ s.card) *
        expand ℂ 2 ((rotatedSquareProduct x s).comp (C x * X)) := by
  induction s using Multiset.induction_on with
  | empty => simp [rotatedSquareProduct]
  | @cons r s ih =>
      simp only [Multiset.card_cons, pow_succ, map_mul, Multiset.map_cons,
        Multiset.prod_cons, mul_comp, sub_comp, X_comp, C_comp] at ih ⊢
      have he :
          expand ℂ 2 ((rotatedSquareProduct x (r ::ₘ s)).comp (C x * X)) =
            (C x * X ^ 2 - C (x * r ^ 2)) *
              expand ℂ 2 ((rotatedSquareProduct x s).comp (C x * X)) := by
        simp [rotatedSquareProduct, mul_comp, expand_X]
      rw [he]
      simp only [map_mul, map_pow, C_neg, C_1] at ih ⊢
      linear_combination C x * (X - C r) * (-X - C r) * ih

/-- Pairing a polynomial with its reflection encodes its rotated squared roots. -/
theorem polynomial_pair_rotated_squares (p : ℂ[X]) (x : ℂ) :
    C (x ^ p.natDegree) * (p * p.comp (-X)) =
      C (p.leadingCoeff ^ 2 * (-1 : ℂ) ^ p.natDegree) *
        expand ℂ 2 ((rotatedSquareProduct x p.roots).comp (C x * X)) := by
  have hcard := (IsAlgClosed.splits p).natDegree_eq_card_roots
  have hfactor := (IsAlgClosed.splits p).eq_prod_roots
  have hpair := congrArg (fun f : ℂ[X] => f * f.comp (-X)) hfactor
  simp only [mul_comp, C_comp] at hpair
  rw [hpair, hcard]
  have h := root_product_pair x p.roots
  simp only [map_mul, map_pow] at h ⊢
  linear_combination C (p.leadingCoeff) ^ 2 * h

/-- The even coefficients in the reflected product are nonzero in the part (ii) cone. -/
theorem paired_coeff_ne_zero_of_twoRaySector {x : ℂ} (hx : 0 < x.re) {p : ℂ[X]}
    (hpzero : p.eval 0 ≠ 0) (hroots : ∀ r ∈ p.roots, r ∈ twoRaySector x)
    {n : ℕ} (hn : n ≤ p.natDegree) : (p * p.comp (-X)).coeff (2 * n) ≠ 0 := by
  have hp : p ≠ 0 := by intro h; simp [h] at hpzero
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  let q := rotatedSquareProduct x p.roots
  have hqroots : ∀ z ∈ q.roots, 0 < z.re := by
    intro z hz
    rw [roots_rotatedSquareProduct] at hz
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
    have hr0 : r ≠ 0 := by
      intro h
      apply hpzero
      have hev : p.eval r = 0 := (mem_roots hp).mp hr
      simpa only [h] using hev
    exact twoRaySector_mul_sq_re_pos hx (hroots r hr) hr0
  have hconvex : Convex ℝ {z : ℂ | 0 < z.re} :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm
  have hqcoeff : q.coeff n ≠ 0 := by
    apply coeff_ne_zero_of_roots_mem_convex hconvex (by simp)
      (monic_rotatedSquareProduct x p.roots).ne_zero hqroots
    simpa [q, natDegree_rotatedSquareProduct,
      ← (IsAlgClosed.splits p).natDegree_eq_card_roots] using hn
  have h := congrArg (fun f : ℂ[X] => f.coeff (2 * n))
    (polynomial_pair_rotated_squares p x)
  rw [coeff_C_mul, coeff_C_mul, coeff_expand_mul' (by decide),
    comp_C_mul_X_coeff] at h
  intro heq
  rw [heq, mul_zero] at h
  exact (mul_ne_zero
    (mul_ne_zero (pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hp)) (pow_ne_zero _ (by norm_num)))
    (mul_ne_zero hqcoeff (pow_ne_zero n hx0))) h.symm

end RealRooted.TuranHurwitz
