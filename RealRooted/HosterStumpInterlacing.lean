import RealRooted.InterlacingSequenceBasic
import RealRooted.QuadraticRoot

open Polynomial

noncomputable section

namespace RealRooted
namespace HosterStump

/-- Source-level real-rootedness convention from Hoster--Stump, Section 2.
The zero polynomial is admitted explicitly; every nonzero polynomial splits. -/
def IsSourceRealRooted (f : ℝ[X]) : Prop :=
  f = 0 ∨ (f ≠ 0 ∧ f.Splits)

/-- Hoster--Stump's Section 2 interlacing relation. Besides zero endpoints and
ordinary oriented proper position, the source declares any two polynomials of
degree at most one to interlace. -/
def SourcePrec (f g : ℝ[X]) : Prop :=
  IsSourceRealRooted f ∧ IsSourceRealRooted g ∧
    (f = 0 ∨ g = 0 ∨
      (f.natDegree ≤ 1 ∧ g.natDegree ≤ 1) ∨ Prec f g)

/-- Source-faithful interlacing sequences from Hoster--Stump, Section 2 and
Lemma 2.3. Empty lists are admitted as a harmless Lean extension; unlike the
weak `IsInterlacingSeq0Nonneg`, singleton lists still record real-rootedness. -/
structure IsInterlacingSeq (fs : List ℝ[X]) : Prop where
  nonneg : ∀ f ∈ fs, HasNonnegCoeffs f
  realRooted : ∀ f ∈ fs, IsSourceRealRooted f
  pairwise : fs.Pairwise SourcePrec

/-- Lower partial sums `[f_0, f_0 + f_1, ...]`, exactly as in Lemma 2.3(2). -/
def lowerPartialSums : List ℝ[X] → List ℝ[X]
  | [] => []
  | f :: fs => f :: (lowerPartialSums fs).map fun g => f + g

/-- Upper partial sums, implemented by reverse/lower-sums/reverse as in the
existing project formula for Lemma 2.3(3). -/
def upperPartialSums (fs : List ℝ[X]) : List ℝ[X] :=
  (lowerPartialSums fs.reverse).reverse

/-- Moving sums of `width + 1` terms from Lemma 2.3(4). The printed tuple ends
at `r_(n-l+1)`, but its displayed index range gives `n-l` windows; this formula
uses the displayed range and therefore has length `fs.length - width`. -/
def movingWindowSums (width : ℕ) (fs : List ℝ[X]) : List ℝ[X] :=
  (List.range (fs.length - width)).map fun k =>
    (fs.drop k |>.take (width + 1)).sum

/-- The `X`-shifted split sums from Hoster--Stump, Lemma 2.3(5). -/
def xShiftedSplitSums (fs : List ℝ[X]) : List ℝ[X] :=
  (List.range (fs.length + 1)).map fun k =>
    X * (fs.take k).sum + (fs.drop k).sum

/-!
## The source low-degree convention

Hoster--Stump, arXiv:2508.15538, p. 4, declares every pair of polynomials of
degree zero or one to interlace. With that convention, Lemma 2.3(2) is false
for mixed linear/quadratic sequences. The following exact example records the
obstruction; in particular, the source-exact predicate must not be used as the
hypothesis of an unconditional lower-partial-sum preservation theorem.
-/

def lowDegreeCounterexampleLeft : ℝ[X] := X + C 1

def lowDegreeCounterexampleMiddle : ℝ[X] := C 2 * (X + C 3)

def lowDegreeCounterexampleRight : ℝ[X] := (X + C 1) * (X + C 3)

private lemma lowDegreeCounterexample_left_prec_right :
    Prec lowDegreeCounterexampleLeft lowDegreeCounterexampleRight := by
  have hbase : Prec (1 : ℝ[X]) (X + C 3) :=
    (interlaces_one_linear (Polynomial.natDegree_X_add_C (3 : ℝ))).toPrec
  have hlinear := isRealRooted_of_degree_one
    (Polynomial.natDegree_X_add_C (1 : ℝ))
  have hcommon := prec_mul_common_factor
    (d := X + C 1) (f := 1) (g := X + C 3) hlinear.1 hlinear.2 hbase
  simpa [lowDegreeCounterexampleLeft, lowDegreeCounterexampleRight] using hcommon

private lemma lowDegreeCounterexample_middle_prec_right :
    Prec lowDegreeCounterexampleMiddle lowDegreeCounterexampleRight := by
  have hbase : Prec (1 : ℝ[X]) (X + C 1) :=
    (interlaces_one_linear (Polynomial.natDegree_X_add_C (1 : ℝ))).toPrec
  have hlinear := isRealRooted_of_degree_one
    (Polynomial.natDegree_X_add_C (3 : ℝ))
  have hcommon := prec_mul_common_factor
    (d := X + C 3) (f := 1) (g := X + C 1) hlinear.1 hlinear.2 hbase
  have hscaled := prec_C_mul_left hcommon (by norm_num : (2 : ℝ) ≠ 0)
  simpa [lowDegreeCounterexampleMiddle, lowDegreeCounterexampleRight, mul_comm]
    using hscaled

/-- The degree-at-most-one convention makes the source version of
Hoster--Stump Lemma 2.3(2) false. The input is source-interlacing, but its first
and third lower partial sums are `X + 1` and `(X + 2) * (X + 5)`, respectively.
-/
theorem source_lowerPartialSums_counterexample :
    IsInterlacingSeq
        [lowDegreeCounterexampleLeft, lowDegreeCounterexampleMiddle,
          lowDegreeCounterexampleRight] ∧
      ¬IsInterlacingSeq
        (lowerPartialSums
          [lowDegreeCounterexampleLeft, lowDegreeCounterexampleMiddle,
            lowDegreeCounterexampleRight]) := by
  have hlr := lowDegreeCounterexample_left_prec_right
  have hmr := lowDegreeCounterexample_middle_prec_right
  have hlrr : IsSourceRealRooted lowDegreeCounterexampleLeft := Or.inr hlr.1
  have hmrr : IsSourceRealRooted lowDegreeCounterexampleMiddle := Or.inr hmr.1
  have hrrr : IsSourceRealRooted lowDegreeCounterexampleRight := Or.inr hlr.2.1
  have hlm : SourcePrec lowDegreeCounterexampleLeft lowDegreeCounterexampleMiddle :=
    ⟨hlrr, hmrr, Or.inr (Or.inr (Or.inl (by
      constructor
      · simpa [lowDegreeCounterexampleLeft] using
          (Polynomial.natDegree_X_add_C (1 : ℝ)).le
      · rw [lowDegreeCounterexampleMiddle,
          natDegree_mul (by norm_num)
            (isRealRooted_of_degree_one
              (Polynomial.natDegree_X_add_C (3 : ℝ))).1]
        simp)))⟩
  have hlr' : SourcePrec lowDegreeCounterexampleLeft lowDegreeCounterexampleRight :=
    ⟨hlrr, hrrr, Or.inr (Or.inr (Or.inr hlr))⟩
  have hmr' : SourcePrec lowDegreeCounterexampleMiddle lowDegreeCounterexampleRight :=
    ⟨hmrr, hrrr, Or.inr (Or.inr (Or.inr hmr))⟩
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl
      · exact hasNonnegCoeffs_X_add_C (by norm_num)
      · exact (hasNonnegCoeffs_C (by norm_num)).mul
          (hasNonnegCoeffs_X_add_C (by norm_num))
      · exact (hasNonnegCoeffs_X_add_C (by norm_num)).mul
          (hasNonnegCoeffs_X_add_C (by norm_num))
    · intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl
      · exact hlrr
      · exact hmrr
      · exact hrrr
    · simpa using (show
        (SourcePrec lowDegreeCounterexampleLeft lowDegreeCounterexampleMiddle ∧
          SourcePrec lowDegreeCounterexampleLeft lowDegreeCounterexampleRight) ∧
          SourcePrec lowDegreeCounterexampleMiddle lowDegreeCounterexampleRight from
        ⟨⟨hlm, hlr'⟩, hmr'⟩)
  · intro hout
    have hsum :
        lowerPartialSums
            [lowDegreeCounterexampleLeft, lowDegreeCounterexampleMiddle,
              lowDegreeCounterexampleRight] =
          [lowDegreeCounterexampleLeft,
            lowDegreeCounterexampleLeft + lowDegreeCounterexampleMiddle,
            lowDegreeCounterexampleLeft +
              (lowDegreeCounterexampleMiddle + lowDegreeCounterexampleRight)] := by
      simp [lowerPartialSums]
    have hfactor :
        lowDegreeCounterexampleLeft +
            (lowDegreeCounterexampleMiddle + lowDegreeCounterexampleRight) =
          (X + C 2) * (X + C 5) := by
      simp only [lowDegreeCounterexampleLeft, lowDegreeCounterexampleMiddle,
        lowDegreeCounterexampleRight]
      rw [show C (1 : ℝ) = (1 : ℝ[X]) by exact map_one C,
        show C (2 : ℝ) = (2 : ℝ[X]) by exact map_ofNat C 2,
        show C (3 : ℝ) = (3 : ℝ[X]) by exact map_ofNat C 3,
        show C (5 : ℝ) = (5 : ℝ[X]) by exact map_ofNat C 5]
      ring
    have hpairs := hout.pairwise
    rw [hsum] at hpairs
    have hfirstLast :
        SourcePrec lowDegreeCounterexampleLeft
          (lowDegreeCounterexampleLeft +
            (lowDegreeCounterexampleMiddle + lowDegreeCounterexampleRight)) :=
      (List.pairwise_cons.mp hpairs).1 _ (by simp)
    rw [hfactor] at hfirstLast
    rcases hfirstLast.2.2 with hzero | hzero | hlow | hprec
    · exact hlr.1.1 hzero
    · have hleft := isRealRooted_of_degree_one
        (Polynomial.natDegree_X_add_C (2 : ℝ))
      have hright := isRealRooted_of_degree_one
        (Polynomial.natDegree_X_add_C (5 : ℝ))
      exact (mul_ne_zero hleft.1 hright.1) hzero
    · have hleft := isRealRooted_of_degree_one
        (Polynomial.natDegree_X_add_C (2 : ℝ))
      have hright := isRealRooted_of_degree_one
        (Polynomial.natDegree_X_add_C (5 : ℝ))
      have hdeg : ((X + C 2) * (X + C 5) : ℝ[X]).natDegree = 2 := by
        rw [natDegree_mul hleft.1 hright.1]
        simp
      lia
    · have hleft := isRealRooted_of_degree_one
        (Polynomial.natDegree_X_add_C (2 : ℝ))
      have hright := isRealRooted_of_degree_one
        (Polynomial.natDegree_X_add_C (5 : ℝ))
      have hbound : ∀ r ∈ ((X + C 2) * (X + C 5) : ℝ[X]).roots, r ≤ -2 := by
        intro r hr
        rw [roots_mul (mul_ne_zero hleft.1 hright.1), roots_X_add_C,
          roots_X_add_C] at hr
        simp only [Multiset.mem_add, Multiset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · norm_num
        · norm_num
      have hleftRoot : (-1 : ℝ) ∈ lowDegreeCounterexampleLeft.roots := by
        change (-1 : ℝ) ∈ (X + C 1 : ℝ[X]).roots
        rw [roots_X_add_C]
        simp
      have := roots_le_of_prec_right hprec hbound (-1) hleftRoot
      norm_num at this

/-- The non-real-rooted polynomial used to check that the old weak sequence
predicate is insufficient when a zero masks a neighboring entry. -/
def weakQuadratic : ℝ[X] := C 1 * X ^ 2 + C 1 * X + C 1

lemma weakQuadratic_hasNonnegCoeffs : HasNonnegCoeffs weakQuadratic := by
  intro n
  simp [weakQuadratic, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_one]
  split_ifs <;> norm_num

lemma weakQuadratic_ne_zero : weakQuadratic ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 2) h
  norm_num [weakQuadratic, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_one] at hcoeff

lemma weakQuadratic_not_splits : ¬weakQuadratic.Splits := by
  simpa [weakQuadratic] using
    (quadraticPoly_not_splits_of_discrim_neg one_ne_zero (by norm_num [discrim]) :
      ¬((C 1 * X ^ 2 + C 1 * X + C 1) : ℝ[X]).Splits)

lemma weakQuadratic_not_sourceRealRooted : ¬IsSourceRealRooted weakQuadratic := by
  rintro (hzero | ⟨_, hsplits⟩)
  · exact weakQuadratic_ne_zero hzero
  · exact weakQuadratic_not_splits hsplits

lemma weakQuadratic_not_prec0_self : ¬Prec0 weakQuadratic weakQuadratic := by
  rintro (hzero | hzero | hprec)
  · exact weakQuadratic_ne_zero hzero
  · exact weakQuadratic_ne_zero hzero
  · exact weakQuadratic_not_splits hprec.1.2

lemma weakQuadratic_not_prec0_X_mul : ¬Prec0 weakQuadratic (X * weakQuadratic) := by
  rintro (hzero | hzero | hprec)
  · exact weakQuadratic_ne_zero hzero
  · exact (mul_ne_zero X_ne_zero weakQuadratic_ne_zero) hzero
  · exact weakQuadratic_not_splits hprec.1.2

private lemma weakInput (fs : List ℝ[X])
    (hpair : fs.Pairwise Prec0) (hmem : ∀ f ∈ fs, f = 0 ∨ f = weakQuadratic) :
    IsInterlacingSeq0Nonneg fs := by
  constructor
  · exact isInterlacingSeq0_iff_pairwise.mpr hpair
  · intro f hf
    rcases hmem f hf with rfl | rfl
    · exact hasNonnegCoeffs_zero
    · exact weakQuadratic_hasNonnegCoeffs

/-- Checked counterexample for the false weak lower-partial-sum interface. -/
theorem weak_lowerPartialSums_counterexample :
    IsInterlacingSeq0Nonneg [weakQuadratic, 0] ∧
      ¬IsInterlacingSeq0Nonneg (lowerPartialSums [weakQuadratic, 0]) := by
  constructor
  · apply weakInput
    · simp [Prec0]
    · simp
  · intro h
    have hp := isInterlacingSeq0_iff_pairwise.mp h.1
    have hout : lowerPartialSums [weakQuadratic, 0] =
        [weakQuadratic, weakQuadratic] := by
      simp [lowerPartialSums]
    rw [hout] at hp
    have hpair : Prec0 weakQuadratic weakQuadratic := by simpa using hp
    exact weakQuadratic_not_prec0_self hpair

/-- Checked counterexample for the false weak upper-partial-sum interface. -/
theorem weak_upperPartialSums_counterexample :
    IsInterlacingSeq0Nonneg [0, weakQuadratic] ∧
      ¬IsInterlacingSeq0Nonneg (upperPartialSums [0, weakQuadratic]) := by
  constructor
  · apply weakInput
    · simp [Prec0]
    · simp
  · intro h
    have hp := isInterlacingSeq0_iff_pairwise.mp h.1
    have hout : upperPartialSums [0, weakQuadratic] =
        [weakQuadratic, weakQuadratic] := by
      simp [upperPartialSums, lowerPartialSums]
    rw [hout] at hp
    have hpair : Prec0 weakQuadratic weakQuadratic := by simpa using hp
    exact weakQuadratic_not_prec0_self hpair

/-- Checked counterexample for the false weak moving-window interface. -/
theorem weak_movingWindowSums_counterexample :
    IsInterlacingSeq0Nonneg [0, weakQuadratic, 0] ∧
      ¬IsInterlacingSeq0Nonneg (movingWindowSums 1 [0, weakQuadratic, 0]) := by
  constructor
  · apply weakInput
    · simp [Prec0]
    · simp
  · intro h
    have hp := isInterlacingSeq0_iff_pairwise.mp h.1
    have hout : movingWindowSums 1 [0, weakQuadratic, 0] =
        [weakQuadratic, weakQuadratic] := by
      norm_num [movingWindowSums, List.range_succ]
    rw [hout] at hp
    have hpair : Prec0 weakQuadratic weakQuadratic := by simpa using hp
    exact weakQuadratic_not_prec0_self hpair

/-- Checked counterexample for the false weak shifted-split-sum interface. -/
theorem weak_xShiftedSplitSums_counterexample :
    IsInterlacingSeq0Nonneg [weakQuadratic] ∧
      ¬IsInterlacingSeq0Nonneg (xShiftedSplitSums [weakQuadratic]) := by
  constructor
  · apply weakInput
    · simp
    · simp
  · intro h
    have hp := isInterlacingSeq0_iff_pairwise.mp h.1
    have hout : xShiftedSplitSums [weakQuadratic] =
        [weakQuadratic, X * weakQuadratic] := by
      norm_num [xShiftedSplitSums, List.range_succ]
    rw [hout] at hp
    have hpair : Prec0 weakQuadratic (X * weakQuadratic) := by simpa using hp
    exact weakQuadratic_not_prec0_X_mul hpair

/-- A singleton is non-vacuous for the source predicate. -/
theorem weakQuadratic_not_sourceInterlacingSeq :
    ¬IsInterlacingSeq [weakQuadratic] := by
  intro h
  exact weakQuadratic_not_sourceRealRooted (h.realRooted weakQuadratic (by simp))

end HosterStump
end RealRooted
