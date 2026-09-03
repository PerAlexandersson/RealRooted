import RealRooted.ChudnovskySeymour
import RealRooted.LiuOppositeSigns.PositiveSplitPair

/-!
# Root-count bridges for Jensen pencils

This file connects the checked Chudnovsky--Seymour common-interleaver theorem
to Liu's closed upper-tail root-count predicate.  It also records the exact
effect of adjoining a factor `X`, which is the bookkeeping step behind the
two-slot Jensen-pencil root-count band.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A `Prec` witness orients strict upper-tail root counts, independently of
whether its endpoints have equal degrees or degrees differing by one. -/
theorem rootCountAboveOriented_of_prec {p q : ℝ[X]} (hprec : Prec p q) :
    ∀ x : ℝ,
      ((p.roots.filter (x < ·)).card : ℤ) ≤ (q.roots.filter (x < ·)).card ∧
      ((q.roots.filter (x < ·)).card : ℤ) ≤
        (p.roots.filter (x < ·)).card + 1 := by
  rcases hprec.natDegree_eq_or_eq_succ with hdeg | hsucc
  · intro x
    exact
      (sameDegreeRootCountAbove_oriented_iff_rootCount_oriented_pointwise
        (f := q) (g := p) hprec.2.1.2 hprec.1.2 hdeg.symm x).mpr
        (sameDegreeRootCountOriented_of_prec hprec hdeg x)
  · exact succDegreeRootCountAboveOriented_of_prec hprec hsucc

namespace Compatible

/-- The zero polynomial is compatible on the left with every polynomial that
is zero or splits. -/
theorem zero_left_of_eq_zero_or_splits {p : ℝ[X]} (hp : p = 0 ∨ p.Splits) :
    Compatible 0 p := by
  by_cases hp0 : p = 0
  · subst p
    intro α β hα hβ
    simp
  have hsplit : p.Splits := hp.resolve_left hp0
  intro α β hα hβ
  by_cases hβ0 : β = 0
  · left
    simp [hβ0]
  · right
    simpa using isRealRooted_C_mul hp0 hsplit hβ0

/-- The zero polynomial is compatible on the right with every polynomial that
is zero or splits. -/
theorem zero_right_of_eq_zero_or_splits {p : ℝ[X]} (hp : p = 0 ∨ p.Splits) :
    Compatible p 0 :=
  (zero_left_of_eq_zero_or_splits hp).comm

end Compatible

namespace LiuOppositeSigns

/-- A common right interleaver forces Liu root-count compatibility, including
when the endpoint polynomials have common or repeated roots. -/
theorem RootCountCompatible.of_commonInterleaver {p q k : ℝ[X]}
    (hpk : Prec p k) (hqk : Prec q k) :
    RootCountCompatible p q := by
  refine RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot
    hpk.1.1 hqk.1.1 ?_
  intro x _hpx _hqx
  obtain ⟨hpk_left, hpk_right⟩ := rootCountAboveOriented_of_prec hpk x
  obtain ⟨hqk_left, hqk_right⟩ := rootCountAboveOriented_of_prec hqk x
  constructor <;> lia

/-- A positive-leading compatible pair satisfies Liu root-count
compatibility.  Common roots are allowed. -/
theorem RootCountCompatible.of_compatible {p q : ℝ[X]}
    (hcompat : Compatible p q)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q) :
    RootCountCompatible p q := by
  obtain ⟨k, hpk, hqk⟩ :=
    compatiblePairHasCommonInterleaver_chudnovskySeymour hp_pos hq_pos hcompat
  exact RootCountCompatible.of_commonInterleaver hpk hqk

/-- Conversely, a nonzero PF pair satisfying Liu's root-count condition is
compatible.  This is the positive-leading specialization of the
Chudnovsky--Seymour root-count/common-interleaver bridge. -/
theorem RootCountCompatible.compatible_of_pf {p q : ℝ[X]}
    (hcount : RootCountCompatible p q)
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    Compatible p q := by
  apply PositiveSplitRootCountPair.compatible
  exact
    ⟨hp.hasNonnegCoeffs.pos_leadingCoeff hp0,
      hq.hasNonnegCoeffs.pos_leadingCoeff hq0,
      hp.2.1.resolve_left hp0, hq.2.1.resolve_left hq0, hcount⟩

/-- Adjoining a factor `X` adds exactly one root to the closed upper tail when
the threshold is nonpositive, and adds none when it is positive. -/
theorem rootCountAtOrAbove_X_mul {p : ℝ[X]} (hp : p ≠ 0) (x : ℝ) :
    rootCountAtOrAbove (X * p) x =
      rootCountAtOrAbove p x + if x ≤ 0 then 1 else 0 := by
  rw [rootCountAtOrAbove, rootCountAtOrAbove,
    Polynomial.roots_mul (mul_ne_zero X_ne_zero hp), Polynomial.roots_X,
    Multiset.filter_add, Multiset.card_add, Multiset.filter_singleton]
  by_cases hx : x ≤ 0 <;> simp [hx, Nat.add_comm]

end LiuOppositeSigns
end RealRooted
