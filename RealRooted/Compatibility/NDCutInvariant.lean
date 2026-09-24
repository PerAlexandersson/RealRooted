import RealRooted.AffineProperPosition
import RealRooted.Compatibility.CutTransformClosure

/-!
# Structural N/D invariant for finite cut transforms

The generic ordered P/Q package is not closed under the cut transform.  This
module retains the additional decomposition `P = N + D`, `Q = X * N + D`
and the zero-aware proper-position order `reverse N ++ D` needed by the
structured recurrence.  The last `D` coordinate is allowed to be zero.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The unmarked coordinatewise mix of two finite state families. -/
def ndCutP {m : ℕ} (N D : Fin m → ℝ[X]) (i : Fin m) : ℝ[X] :=
  N i + D i

/-- The marked coordinatewise mix of two finite state families. -/
def ndCutQ {m : ℕ} (N D : Fin m → ℝ[X]) (i : Fin m) : ℝ[X] :=
  X * N i + D i

/-- The structural state order: reversed non-descent states followed by
forward descent states. -/
def ndCutStateOrder {m : ℕ} (N D : Fin m → ℝ[X]) : List ℝ[X] :=
  (List.ofFn N).reverse ++ List.ofFn D

@[simp]
theorem length_ndCutStateOrder {m : ℕ} (N D : Fin m → ℝ[X]) :
    (ndCutStateOrder N D).length = 2 * m := by
  simp [ndCutStateOrder, two_mul]

/-- A list of nonnegative constant polynomials is a zero-aware nonnegative
interlacing family, with every nonzero member real-rooted. -/
theorem isInterlacingSeq0NonnegRealRooted_of_mem_C_nonneg
    (fs : List ℝ[X])
    (hfs : ∀ p ∈ fs, ∃ a : ℝ, 0 ≤ a ∧ p = C a) :
    IsInterlacingSeq0NonnegRealRooted fs := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise, List.pairwise_iff_get]
    intro i j _
    obtain ⟨a, _, ha⟩ := hfs _ (List.get_mem fs i)
    obtain ⟨b, _, hb⟩ := hfs _ (List.get_mem fs j)
    rw [ha, hb]
    exact interl_C_C a b
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := hfs p hp
    exact hasNonnegCoeffs_C ha
  · intro p hp hp_ne
    obtain ⟨a, _, rfl⟩ := hfs p hp
    exact isRealRooted_of_deg_zero hp_ne (by simp)

/-- Structural data for an ordered two-colour cut recurrence.

The first field is precisely the sound P/Q interface used by the cut-output
closures.  The second field retains information lost by arbitrary P/Q data;
its zero-aware form permits an empty extreme suffix. -/
structure OrderedNDCutCompatible {m : ℕ}
    (N D : Fin m → ℝ[X]) : Prop where
  cutCompatible : OrderedCutCompatible (ndCutP N D) (ndCutQ N D)
  stateInterlacing :
    IsInterlacingSeq0NonnegRealRooted (ndCutStateOrder N D)

namespace OrderedNDCutCompatible

/-- Receiver-style projection to the generic P/Q cut package. -/
theorem toOrderedCutCompatible {m : ℕ} {N D : Fin m → ℝ[X]}
    (h : OrderedNDCutCompatible N D) :
    OrderedCutCompatible (ndCutP N D) (ndCutQ N D) :=
  h.cutCompatible

/-- Every `N` coordinate has nonnegative coefficients. -/
theorem n_nonneg {m : ℕ} {N D : Fin m → ℝ[X]}
    (h : OrderedNDCutCompatible N D) (i : Fin m) :
    HasNonnegCoeffs (N i) := by
  exact h.stateInterlacing.nonnegCoeffs (N i) (by
    apply List.mem_append_left
    simp)

/-- Every `D` coordinate has nonnegative coefficients, including a possible
zero extreme suffix. -/
theorem d_nonneg {m : ℕ} {N D : Fin m → ℝ[X]}
    (h : OrderedNDCutCompatible N D) (i : Fin m) :
    HasNonnegCoeffs (D i) := by
  exact h.stateInterlacing.nonnegCoeffs (D i) (by
    apply List.mem_append_right
    simp)

/-- A nonzero `N` coordinate is real-rooted. -/
theorem n_realRooted {m : ℕ} {N D : Fin m → ℝ[X]}
    (h : OrderedNDCutCompatible N D) (i : Fin m) (hi : N i ≠ 0) :
    N i ≠ 0 ∧ (N i).Splits := by
  apply h.stateInterlacing.realRooted (N i) (by
    apply List.mem_append_left
    simp)
  exact hi

/-- A nonzero `D` coordinate is real-rooted. -/
theorem d_realRooted {m : ℕ} {N D : Fin m → ℝ[X]}
    (h : OrderedNDCutCompatible N D) (i : Fin m) (hi : D i ≠ 0) :
    D i ≠ 0 ∧ (D i).Splits := by
  apply h.stateInterlacing.realRooted (D i) (by
    apply List.mem_append_right
    simp)
  exact hi

end OrderedNDCutCompatible

end RealRooted
