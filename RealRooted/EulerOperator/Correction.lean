/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.EulerOperator
public import RealRooted.PosCombo
public import RealRooted.WagnerX.NonnegativeRoots

/-!
# Corrections to Euler successors

This file packages common-interleaver arguments for adding a nonnegative
correction below the Euler successor `thetaPlusOne p`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- If a nonnegative correction precedes both a PF polynomial and its
zero-adjoined derivative, adding it preserves strict interlacing below the
Euler successor. -/
theorem strictInterl_add_thetaPlusOne_of_correction
    {p u : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : p ≠ 0)
    (hpdeg : 2 ≤ p.natDegree) (hu : HasNonnegCoeffs u)
    (hup : StrictInterl u p)
    (huXder : StrictInterl u (X * p.derivative)) :
    StrictInterl (p + u) (thetaPlusOne p) := by
  have hpnn : HasNonnegCoeffs p := hp.hasNonnegCoeffs
  have hppos : HasPosLeadingCoeff p := hpnn.pos_leadingCoeff hp0
  have hupos : HasPosLeadingCoeff u := hu.pos_leadingCoeff hup.1.1
  have hderp : StrictInterl p.derivative p :=
    (derivative_interlaces_of_natDegree_ne_zero
      (hp.ne_zero_and_splits hp0).2 (by lia)).toStrictInterl
  have hpXder : StrictInterl p (X * p.derivative) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg hderp hpnn.derivative hpnn
  have hXdernn : HasNonnegCoeffs (X * p.derivative) :=
    hasNonnegCoeffs_X.mul hpnn.derivative
  have hXderpos : HasPosLeadingCoeff (X * p.derivative) :=
    hXdernn.pos_leadingCoeff hpXder.2.1.1
  have hsump : StrictInterl (p + u) p := by
    simpa [add_comm] using
      StrictInterl.nonneg_combo_right hup hupos hppos
        (a := 1) (b := 1) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
  have hsumXder : StrictInterl (p + u) (X * p.derivative) := by
    simpa using StrictInterl.sum_right [p, u] (X * p.derivative)
      (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hpXder
        · exact huXder)
      (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hppos
        · exact hupos)
      (by simp)
  have hsumpos : HasPosLeadingCoeff (p + u) :=
    (hpnn.add hu).pos_leadingCoeff hsump.1.1
  have hfinal :
      StrictInterl (p + u)
        (weightedSum [(1, p), (1, X * p.derivative)]) := by
    apply StrictInterl.weightedSum_left_of_common_left
      [(1, p), (1, X * p.derivative)] (p + u)
    · simp
    · intro aq haq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at haq
      rcases haq with rfl | rfl
      · exact hsump
      · exact hsumXder
    · exact hsumpos
    · intro aq haq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at haq
      rcases haq with rfl | rfl
      · exact hppos
      · exact hXderpos
    · simp
  simpa [weightedSum, weightedSum_cons, thetaPlusOne, theta,
    add_comm, add_left_comm, add_assoc] using hfinal

/-- A nontrivial nonnegative combination of `p'` and a polynomial above
`p'` precedes the zero-adjoined derivative. -/
theorem strictInterl_derivative_combo_X_mul
    {p r : ℝ[X]} (hp : HasNonnegCoeffs p) (hr : HasNonnegCoeffs r)
    (hder : StrictInterl p.derivative r) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a ∨ 0 < b) :
    StrictInterl (C a * p.derivative + C b * r) (X * p.derivative) := by
  have hdernn : HasNonnegCoeffs p.derivative := hp.derivative
  have hderpos : HasPosLeadingCoeff p.derivative :=
    hdernn.pos_leadingCoeff hder.1.1
  have hrpos : HasPosLeadingCoeff r :=
    hr.pos_leadingCoeff hder.2.1.1
  have hderself : StrictInterl p.derivative p.derivative :=
    StrictInterl.refl hder.1.1 hder.1.2
  have hderXder : StrictInterl p.derivative (X * p.derivative) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg hderself hdernn hdernn
  have hrXder : StrictInterl r (X * p.derivative) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg hder hdernn hr
  have hsum := StrictInterl.weightedSum_right_of_nonneg
    [(a, p.derivative), (b, r)] (X * p.derivative)
    (by simp_all)
    (by
      intro aq haq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at haq
      rcases haq with rfl | rfl
      · exact hderXder
      · exact hrXder)
    (by
      intro aq haq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at haq
      rcases haq with rfl | rfl
      · exact hderpos
      · exact hrpos)
    (by simp_all)
  simpa [weightedSum, weightedSum_cons] using hsum

/-- A PF polynomial, a positive derivative correction, and a positive
common-left correction together precede the Euler successor. -/
theorem strictInterl_add_derivative_add_thetaPlusOne
    {p r : ℝ[X]} (hp : IsPFPolynomial p)
    (hpdeg : 2 ≤ p.natDegree) (hr : HasNonnegCoeffs r)
    (hrp : StrictInterl r p)
    (hrXder : StrictInterl r (X * p.derivative))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictInterl (p + C a * p.derivative + C b * r)
      (thetaPlusOne p) := by
  have hp0 : p ≠ 0 := hrp.2.1.1
  have hpnn : HasNonnegCoeffs p := hp.hasNonnegCoeffs
  have hderp : StrictInterl p.derivative p :=
    (derivative_interlaces_of_natDegree_ne_zero
      (hp.ne_zero_and_splits hp0).2 (by lia)).toStrictInterl
  have hder0 : p.derivative ≠ 0 := hderp.1.1
  have hdernn : HasNonnegCoeffs p.derivative := hpnn.derivative
  have hderpos : HasPosLeadingCoeff p.derivative :=
    hdernn.pos_leadingCoeff hder0
  have hrpos : HasPosLeadingCoeff r := hr.pos_leadingCoeff hrp.1.1
  let u := C a * p.derivative + C b * r
  have hunn : HasNonnegCoeffs u :=
    (hasNonnegCoeffs_C_mul ha.le hdernn).add
      (hasNonnegCoeffs_C_mul hb.le hr)
  have hup : StrictInterl u p := by
    dsimp [u]
    simpa [weightedSum, weightedSum_cons] using
      StrictInterl.weightedSum_right_of_nonneg
        [(a, p.derivative), (b, r)] p
        (by
          intro cq hcq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcq
          rcases hcq with rfl | rfl
          · exact ha.le
          · exact hb.le)
        (by
          intro cq hcq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcq
          rcases hcq with rfl | rfl
          · exact hderp
          · exact hrp)
        (by
          intro cq hcq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcq
          rcases hcq with rfl | rfl
          · exact hderpos
          · exact hrpos)
        (by simp [ha, hb])
  have hderXder : StrictInterl p.derivative (X * p.derivative) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg
      (StrictInterl.refl hder0 hderp.1.2) hdernn hdernn
  have huXder : StrictInterl u (X * p.derivative) := by
    dsimp [u]
    simpa [weightedSum, weightedSum_cons] using
      StrictInterl.weightedSum_right_of_nonneg
        [(a, p.derivative), (b, r)] (X * p.derivative)
        (by
          intro cq hcq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcq
          rcases hcq with rfl | rfl
          · exact ha.le
          · exact hb.le)
        (by
          intro cq hcq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcq
          rcases hcq with rfl | rfl
          · exact hderXder
          · exact hrXder)
        (by
          intro cq hcq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcq
          rcases hcq with rfl | rfl
          · exact hderpos
          · exact hrpos)
        (by simp [ha, hb])
  simpa [u, add_assoc] using
    strictInterl_add_thetaPlusOne_of_correction
      hp hp0 hpdeg hunn hup huXder

end RealRooted
