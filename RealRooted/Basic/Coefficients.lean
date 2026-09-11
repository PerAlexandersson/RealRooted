import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Splits
import RealRooted.Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import RealRooted.Mathlib.Data.Nat.Cast.Basic
import RealRooted.Mathlib.Data.Nat.Choose.Cast
import RealRooted.Mathlib.Data.List.Interleave

open Polynomial

noncomputable section

namespace RealRooted

/-- Non-negative coefficients. -/
def HasNonnegCoeffs (p : ℝ[X]) : Prop := ∀ n, 0 ≤ p.coeff n

/-! ### Elementary closure of nonnegative coefficients -/

lemma hasNonnegCoeffs_zero : HasNonnegCoeffs (0 : ℝ[X]) := by
  simp [HasNonnegCoeffs]

lemma hasNonnegCoeffs_one : HasNonnegCoeffs (1 : ℝ[X]) := by
  rintro (_ | n)
  · simp
  · rw [coeff_one]
    simp

lemma hasNonnegCoeffs_C {a : ℝ} (ha : 0 ≤ a) : HasNonnegCoeffs (C a) := by
  rintro (_ | n) <;> simp [ha]

lemma nonnegCoeffs_C_mul {a : ℝ} (ha : 0 ≤ a) {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (C a * p) := by
  intro n
  simpa [coeff_C_mul] using mul_nonneg ha (hp n)

lemma HasNonnegCoeffs.add {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (p + q) := fun n => by
  simpa [coeff_add] using add_nonneg (hp n) (hq n)

lemma hasNonnegCoeffs_finsetSum {ι : Type}
    (s : Finset ι) (f : ι → ℝ[X]) (hf : ∀ i ∈ s, HasNonnegCoeffs (f i)) :
    HasNonnegCoeffs (s.sum f) := by
  classical
  intro n
  simpa [finsetSum_coeff] using Finset.sum_nonneg fun i hi => hf i hi n

lemma hasNonnegCoeffs_sum :
    ∀ ps : List ℝ[X], (∀ p ∈ ps, HasNonnegCoeffs p) → HasNonnegCoeffs ps.sum
  | [], _ => by simpa using hasNonnegCoeffs_zero
  | p :: ps, hps => by
      have hp : HasNonnegCoeffs p := hps p (by simp)
      have htail : HasNonnegCoeffs ps.sum :=
        hasNonnegCoeffs_sum ps (fun q hq => hps q (by simp [hq]))
      simpa using hp.add htail

lemma HasNonnegCoeffs.mul {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (p * q) := by
  intro n
  simpa [coeff_mul] using Finset.sum_nonneg fun ij _ => mul_nonneg (hp ij.1) (hq ij.2)

protected lemma HasNonnegCoeffs.pow {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    ∀ n : ℕ, HasNonnegCoeffs (p ^ n)
  | 0 => hasNonnegCoeffs_one
  | n + 1 => by
      simpa [pow_succ] using (hp.pow n).mul hp

/-- Reflection at an arbitrary degree preserves nonnegative coefficients. -/
lemma HasNonnegCoeffs.reflect {p : ℝ[X]} (hp : HasNonnegCoeffs p) (n : ℕ) :
    HasNonnegCoeffs (reflect n p) := by
  intro k
  simpa [Polynomial.coeff_reflect] using hp (revAt n k)

/-- Positive leading coefficient. -/
def HasPosLeadingCoeff (p : ℝ[X]) : Prop := 0 < p.leadingCoeff

@[simp] lemma not_hasPosLeadingCoeff_zero : ¬ HasPosLeadingCoeff (0 : ℝ[X]) := by
  simp [HasPosLeadingCoeff]

lemma HasPosLeadingCoeff.ne_zero {p : ℝ[X]} (hp : HasPosLeadingCoeff p) : p ≠ 0 := by
  rintro rfl; simp at hp

lemma HasNonnegCoeffs.pos_leadingCoeff {p : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hp0 : p ≠ 0) : HasPosLeadingCoeff p := by
  unfold HasPosLeadingCoeff
  exact lt_of_le_of_ne (hp p.natDegree) (Ne.symm (leadingCoeff_ne_zero.mpr hp0))

/-- A nonzero polynomial with nonnegative coefficients is strictly positive at
every strictly positive real argument. -/
theorem eval_pos_of_hasNonnegCoeffs {p : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hp0 : p ≠ 0) {t : ℝ} (ht : 0 < t) : 0 < p.eval t := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_pos
  · intro n hn
    have hcoeff : 0 < p.coeff n :=
      lt_of_le_of_ne (hp n) (Ne.symm (Polynomial.mem_support_iff.mp hn))
    positivity
  · exact Polynomial.support_nonempty.mpr hp0

/-- A real polynomial with nonnegative coefficients has no positive real roots. -/
theorem roots_nonpos_of_hasNonnegCoeffs {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    ∀ r ∈ p.roots, r ≤ 0 := fun r hr => by
  by_contra hr_nonpos
  have hp0 : p ≠ 0 := fun hp0 => by
    simp [hp0] at hr
  have hr_pos : 0 < r := lt_of_not_ge hr_nonpos
  have hroot : p.IsRoot r := (Polynomial.mem_roots hp0).mp hr
  have heval_pos : 0 < p.eval r := eval_pos_of_hasNonnegCoeffs hp hp0 hr_pos
  rw [Polynomial.IsRoot.def] at hroot
  linarith

/-- A real root of a nonzero polynomial with nonnegative coefficients is
nonpositive. -/
theorem isRoot_nonpos_of_hasNonnegCoeffs {p : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hp_ne : p ≠ 0) {r : ℝ} (hr : p.IsRoot r) :
    r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs hp r ((Polynomial.mem_roots hp_ne).mpr hr)

/-- A point strictly to the left of a real root of a nonzero polynomial with
nonnegative coefficients is negative. -/
theorem lt_zero_of_lt_isRoot_of_hasNonnegCoeffs {p : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hp_ne : p ≠ 0) {x r : ℝ} (hr : p.IsRoot r) (hxr : x < r) :
    x < 0 :=
  lt_of_lt_of_le hxr (isRoot_nonpos_of_hasNonnegCoeffs hp hp_ne hr)

lemma hasPosLeadingCoeff_of_monic {p : ℝ[X]} (hp : p.Monic) :
    HasPosLeadingCoeff p := by
  simp [HasPosLeadingCoeff, hp.leadingCoeff]

lemma hasPosLeadingCoeff_one : HasPosLeadingCoeff (1 : ℝ[X]) :=
  hasPosLeadingCoeff_of_monic monic_one

lemma hasPosLeadingCoeff_C_mul {a : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (C a * p) := by
  simpa [HasPosLeadingCoeff, leadingCoeff_mul] using mul_pos ha hp

lemma HasPosLeadingCoeff.mul {p q : ℝ[X]}
    (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q) :
    HasPosLeadingCoeff (p * q) := by
  simpa [HasPosLeadingCoeff, leadingCoeff_mul] using mul_pos hp hq

lemma hasPosLeadingCoeff_neg {p : ℝ[X]} (hp : p.leadingCoeff < 0) :
    HasPosLeadingCoeff (-p) := by
  simpa [HasPosLeadingCoeff] using hp

lemma HasPosLeadingCoeff.X_mul {p : ℝ[X]} (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (X * p) := by
  simpa [HasPosLeadingCoeff, leadingCoeff_mul, leadingCoeff_X] using hp

/-! ## Elementary interval inequalities -/
end RealRooted
