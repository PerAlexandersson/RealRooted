import RealRooted.LiuOppositeSigns.XSub.SameDegree

/-!
# Liu linear/quadratic x-subtraction leaf

This module contains the normalized linear/quadratic positive-split
x-subtraction leaf used by the right-successor right-degree-two endpoint.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- In the `(1, 2)` positive split root-count case, the lower quadratic root
cannot lie strictly above the linear root. -/
lemma lower_quadratic_root_le_singleton_root_of_positiveSplitRootCountPair_one_two
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    {a b c : ℝ} (hab : a ≤ b) (hfroots : f.roots = {c})
    (hgroots : g.roots = {a, b}) :
    a ≤ c := by
  by_contra hac
  have hca : c < a := lt_of_not_ge hac
  let x : ℝ := (a + c) / 2
  have hcx : c < x := by
    dsimp [x]
    linarith
  have hxa : x ≤ a := by
    dsimp [x]
    linarith
  have hxb : x ≤ b := hxa.trans hab
  have hcount := h.count.right_sub_le_one x
  have hf_count : rootCountAtOrAbove f x = 0 := by
    rw [rootCountAtOrAbove, hfroots]
    rw [Multiset.filter_singleton (fun r : ℝ => x ≤ r),
      if_neg (not_le.mpr hcx)]
    simp
  have hg_count : rootCountAtOrAbove g x = 2 := by
    rw [rootCountAtOrAbove, hgroots]
    simp only [Multiset.insert_eq_cons]
    rw [Multiset.filter_cons_of_pos ({b} : Multiset ℝ) hxa]
    rw [Multiset.filter_singleton (fun r : ℝ => x ≤ r), if_pos hxb]
    simp
  rw [hf_count, hg_count] at hcount
  norm_num at hcount

/-- Discriminant certificate for the degree-one/degree-two x-subtraction
leaf.  The normalized hypotheses say that the quadratic roots `a ≤ b` and
linear root `c` are nonpositive after translation, and that the linear root is
not below the lower quadratic root. -/
def xSubLinearQuadraticDiscrimNonnegStatement : Prop :=
  ∀ {a b c μ : ℝ},
    a ≤ b → a ≤ c → b ≤ 0 → c ≤ 0 → 0 < μ →
      0 ≤ discrim (1 - μ) (-c + μ * (a + b)) (-μ * (a * b))

/-- Explicit discriminant certificate for the normalized case
`a ≤ c ≤ b ≤ 0`. -/
lemma xSubLinearQuadraticDiscrimNonneg_between
    {u v w μ : ℝ} (hu : 0 ≤ u) (_hv : 0 ≤ v) (hw : 0 ≤ w)
    (hμ : 0 < μ) :
    0 ≤ discrim (1 - μ) (v + w - μ * (u + v + 2 * w))
      (-μ * ((u + v + w) * w)) := by
  have hdisc :
      discrim (1 - μ) (v + w - μ * (u + v + 2 * w))
          (-μ * ((u + v + w) * w)) =
        (μ * (u + v) - (v + w)) ^ 2 + 4 * μ * u * w := by
    unfold discrim
    ring_nf
  rw [hdisc]
  positivity

/-- Explicit discriminant certificate for the normalized case
`a ≤ b ≤ c ≤ 0`. -/
lemma xSubLinearQuadraticDiscrimNonneg_right
    {u v w μ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hμ : 0 < μ) :
    0 ≤ discrim (1 - μ) (w - μ * (u + 2 * v + 2 * w))
      (-μ * ((u + v + w) * (v + w))) := by
  have hdisc :
      discrim (1 - μ) (w - μ * (u + 2 * v + 2 * w))
          (-μ * ((u + v + w) * (v + w))) =
        (μ * u + w) ^ 2 + 4 * μ * v * (u + v + w) := by
    unfold discrim
    ring_nf
  rw [hdisc]
  positivity

/-- The discriminant certificate needed in the degree-one/degree-two
x-subtraction leaf. -/
theorem xSubLinearQuadraticDiscrimNonneg :
    xSubLinearQuadraticDiscrimNonnegStatement := by
  intro a b c μ hab hac hb0 hc0 hμ
  by_cases hcb : c ≤ b
  · let u : ℝ := c - a
    let v : ℝ := b - c
    let w : ℝ := -b
    have hu : 0 ≤ u := by
      dsimp [u]
      linarith
    have hv : 0 ≤ v := by
      dsimp [v]
      linarith
    have hw : 0 ≤ w := by
      dsimp [w]
      linarith
    have hdisc :
        discrim (1 - μ) (-c + μ * (a + b)) (-μ * (a * b)) =
          discrim (1 - μ) (v + w - μ * (u + v + 2 * w))
            (-μ * ((u + v + w) * w)) := by
      dsimp [u, v, w]
      unfold discrim
      ring_nf
    rw [hdisc]
    exact xSubLinearQuadraticDiscrimNonneg_between hu hv hw hμ
  · have hbc : b ≤ c := le_of_not_ge hcb
    let u : ℝ := b - a
    let v : ℝ := c - b
    let w : ℝ := -c
    have hu : 0 ≤ u := by
      dsimp [u]
      linarith
    have hv : 0 ≤ v := by
      dsimp [v]
      linarith
    have hw : 0 ≤ w := by
      dsimp [w]
      linarith
    have hdisc :
        discrim (1 - μ) (-c + μ * (a + b)) (-μ * (a * b)) =
          discrim (1 - μ) (w - μ * (u + 2 * v + 2 * w))
            (-μ * ((u + v + w) * (v + w))) := by
      dsimp [u, v, w]
      unfold discrim
      ring_nf
    rw [hdisc]
    exact xSubLinearQuadraticDiscrimNonneg_right hu hv hw hμ

/-- Normalized monic arithmetic leaf for the degree-one/degree-two
x-subtraction endpoint. -/
def xSubLinearQuadraticSplitsStatement : Prop :=
  ∀ {a b c μ : ℝ},
    a ≤ b → a ≤ c → b ≤ 0 → c ≤ 0 → 0 < μ →
      (X * (X - C c) - C μ * ((X - C a) * (X - C b))).Splits

/-- The normalized discriminant certificate implies the monic
linear/quadratic x-subtraction leaf. -/
theorem xSubLinearQuadraticSplits_of_discrim
    (harith : xSubLinearQuadraticDiscrimNonnegStatement) :
    xSubLinearQuadraticSplitsStatement := by
  intro a b c μ hab hac hb0 hc0 hμ
  have hpoly :
      X * (X - C c) - C μ * ((X - C a) * (X - C b)) =
        C (1 - μ) * X ^ 2 + C (-c + μ * (a + b)) * X +
          C (-μ * (a * b)) := by
    simp only [C_add, C_mul, C_neg, C_sub, C_1]
    ring_nf
  have hdisc : 0 ≤ discrim (1 - μ) (-c + μ * (a + b)) (-μ * (a * b)) :=
    harith hab hac hb0 hc0 hμ
  simpa [hpoly] using quadraticPoly_splits_of_discrim_nonneg_or_linear hdisc

/-- The normalized monic degree-one/degree-two x-subtraction leaf. -/
theorem xSubLinearQuadraticSplits : xSubLinearQuadraticSplitsStatement :=
  xSubLinearQuadraticSplits_of_discrim xSubLinearQuadraticDiscrimNonneg

/-- The normalized monic linear/quadratic x-subtraction leaf implies the
degree-one/degree-two positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_one_two_of_monic
    (hmono : xSubLinearQuadraticSplitsStatement)
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 1) (hqdeg : q.natDegree = 2)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  obtain ⟨c, hproots, hpfac⟩ :=
    exists_linear_factor_of_splits_natDegree_one hpair.left_splits hpdeg
  obtain ⟨a, b, hab, hqroots, hqfac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hpair.right_splits hqdeg
  have hac : a ≤ c :=
    lower_quadratic_root_le_singleton_root_of_positiveSplitRootCountPair_one_two
      hpair hab hproots hqroots
  have hb0 : b ≤ 0 := by
    have hb_mem : b ∈ q.roots := by
      rw [hqroots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hqnn b hb_mem
  have hc0 : c ≤ 0 := by
    have hc_mem : c ∈ p.roots := by
      rw [hproots]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hpnn c hc_mem
  let A : ℝ := p.leadingCoeff
  let B : ℝ := q.leadingCoeff
  have hA_pos : 0 < A := by
    dsimp [A]
    exact hpair.left_pos
  have hB_pos : 0 < B := by
    dsimp [B]
    exact hpair.right_pos
  let ν : ℝ := μ * B / A
  have hν_pos : 0 < ν := by
    dsimp [ν]
    exact div_pos (mul_pos hμ hB_pos) hA_pos
  let inner : ℝ[X] := X * (X - C c) - C ν * ((X - C a) * (X - C b))
  have hinner_splits : inner.Splits := by
    dsimp [inner]
    exact hmono hab hac hb0 hc0 hν_pos
  have hpfacA : p = C A * (X - C c) := by
    simpa [A] using hpfac
  have hqfacB : q = C B * ((X - C a) * (X - C b)) := by
    simpa [B] using hqfac
  have hpoly : X * p - C μ * q = C A * inner := by
    rw [hpfacA, hqfacB]
    dsimp [inner, ν]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    field_simp [hA_pos.ne']
  rw [hpoly]
  exact hinner_splits.C_mul A

/-- Degree-one/degree-two positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_one_two
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 1) (hqdeg : q.natDegree = 2)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits :=
  splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_one_two_of_monic
    xSubLinearQuadraticSplits hpair hpnn hqnn hpdeg hqdeg hμ

/-- Degree-two right endpoint case for the right-successor sign-normalized
x-subtraction leaf. -/
theorem positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_two
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree = 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 1 := by
    lia
  have hFdeg : (f.comp (X + C r)).natDegree = 1 := by
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 2 := by
    simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_one_two
    (hpair.comp_X_add_C r) hfnn hgnn hFdeg hGdeg hμ

/-- Endpoint cases through right degree two for the right-successor
sign-normalized x-subtraction leaf. -/
theorem positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree ≤ 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hone : g.natDegree = 1
  · exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
      hpair hfnn hgnn hdeg hone
  · have htwo : g.natDegree = 2 := by
      lia
    exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_two
      hpair hfnn hgnn hdeg htwo

/-- Pack the degree-two right endpoint terminal as a predicate-restricted
right-successor positive-split x-sub family. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 2) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_two
    hpair hfnn hgnn hdeg hgdeg

/-- Pack the endpoint cases through degree two as a predicate-restricted
right-successor positive-split x-sub family. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 2) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
    hpair hfnn hgnn hdeg hgdeg

end LiuOppositeSigns
end RealRooted
