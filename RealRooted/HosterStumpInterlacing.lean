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
