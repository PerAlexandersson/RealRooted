module

public import RealRooted.PolynomialValueEulerNumerator
public import RealRooted.PFPolynomial
import RealRooted.PolynomialValueEulerNumerator.Product.Brenti
import RealRooted.SequenceClosure

/-!
# Relative h-polynomials of half-open cubes

M. Hlavacek and L. Solus, *Subdivisions of shellable complexes*, J. Combin. Theory Ser. A
(2021), arXiv:2003.07328, Section 4: in a stable shelling of a cubical complex every relative
piece is a half-open cube `[-1, 1]^d_l` (`0 ≤ l ≤ 2d`), and the h-polynomial of the barycentric
subdivision of that piece is the refined type-B Eulerian polynomial `A_{d,l}^{(2)}` for
`l ≤ d`, and `x · I_d A_{d,2d-l}^{(2)}` for `d < l` (Lemmas 4.1 and 4.4).

`cubeColoredEulerian d l` is `A_{d,l}^{(2)}`, defined as the Euler numerator of
`t ↦ (2t)^l (2t+1)^(d-l)`; its generating-series interpretation is
`polynomialValueSeries_eq_eulerNumerator_mul_invOneSubPow`.  Every piece is real-rooted with
nonnegative coefficients (Brenti's theorem, since all roots of the source lie in `[-1, 0]`).

The interlacing of the whole row `cubeRelativeHRow d` (Hlavacek--Solus Lemma 4.1, which rests on
Brändén's 2006 interlacing theorem for Euler numerators) is not formalized yet (issue #1311); with
it, `isRealRooted_polytopalHPolynomial_of_perm_interlacingNonneg` gives the cubical
stable-shelling theorem.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted.HlavacekSolus

/-- The polynomial-valued function `t ↦ (2t)^l (2t+1)^(d-l)`. -/
def cubeValuePolynomial (d l : ℕ) : ℝ[X] :=
  (C 2 * X) ^ l * (C 2 * X + 1) ^ (d - l)

/-- The refined type-B Eulerian polynomial `A_{d,l}^{(2)}`. -/
def cubeColoredEulerian (d l : ℕ) : ℝ[X] :=
  polynomialValueEulerNumerator (cubeValuePolynomial d l)

/-- The relative h-polynomial of a half-open `d`-cube with `l` removed
facets, in the admissible range `0 <= l <= 2d`. -/
def cubeRelativeHPolynomial (d l : ℕ) : ℝ[X] :=
  if l ≤ d then cubeColoredEulerian d l
  else X * (cubeColoredEulerian d (2 * d - l)).reflect d

/-- The admissibly ordered list of all half-open `d`-cube relative
h-polynomials. -/
def cubeRelativeHRow (d : ℕ) : List ℝ[X] :=
  List.ofFn fun l : Fin (2 * d + 1) => cubeRelativeHPolynomial d l

/-- The source polynomial for a refined cube polynomial is nonzero. -/
theorem cubeValuePolynomial_ne_zero (d l : ℕ) :
    cubeValuePolynomial d l ≠ 0 := by
  unfold cubeValuePolynomial
  apply mul_ne_zero
  · exact pow_ne_zero _ (mul_ne_zero (by norm_num) (by simp))
  · apply pow_ne_zero
    intro h
    have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) h
    norm_num at hcoeff

/-- The source polynomial for a refined cube polynomial has nonnegative
coefficients. -/
theorem cubeValuePolynomial_nonneg (d l : ℕ) :
    HasNonnegCoeffs (cubeValuePolynomial d l) := by
  unfold cubeValuePolynomial
  apply HasNonnegCoeffs.mul
  · exact (hasNonnegCoeffs_C_mul (show (0 : ℝ) ≤ 2 by norm_num)
      hasNonnegCoeffs_X).pow l
  · exact ((hasNonnegCoeffs_C_mul (show (0 : ℝ) ≤ 2 by norm_num)
      hasNonnegCoeffs_X).add
      hasNonnegCoeffs_one).pow (d - l)

/-- The source polynomial for a refined cube polynomial splits over the
reals. -/
theorem cubeValuePolynomial_splits (d l : ℕ) :
    (cubeValuePolynomial d l).Splits := by
  unfold cubeValuePolynomial
  apply Polynomial.Splits.mul
  · exact ((Polynomial.Splits.C (2 : ℝ)).mul Polynomial.Splits.X).pow l
  · apply Polynomial.Splits.pow
    exact Polynomial.Splits.of_natDegree_le_one (by compute_degree)

/-- In its intended range, the cube source polynomial has degree at most
`d`. -/
theorem cubeValuePolynomial_natDegree_le {d l : ℕ} (hl : l ≤ d) :
    (cubeValuePolynomial d l).natDegree ≤ d := by
  unfold cubeValuePolynomial
  have hleft : (C (2 : ℝ) * X).natDegree ≤ 1 := by compute_degree
  have hright : (C (2 : ℝ) * X + 1).natDegree ≤ 1 := by compute_degree
  calc
    ((C (2 : ℝ) * X) ^ l * (C 2 * X + 1) ^ (d - l)).natDegree
        ≤ ((C (2 : ℝ) * X) ^ l).natDegree +
          ((C (2 : ℝ) * X + 1) ^ (d - l)).natDegree := natDegree_mul_le
    _ ≤ l + (d - l) := by
      apply Nat.add_le_add
      · calc
          ((C (2 : ℝ) * X) ^ l).natDegree
              ≤ l * (C (2 : ℝ) * X).natDegree := natDegree_pow_le
          _ ≤ l := by
            simpa only [Nat.mul_one] using Nat.mul_le_mul_left l hleft
      · calc
          ((C (2 : ℝ) * X + 1) ^ (d - l)).natDegree
              ≤ (d - l) * (C (2 : ℝ) * X + 1).natDegree := natDegree_pow_le
          _ ≤ d - l := by
            simpa only [Nat.mul_one] using Nat.mul_le_mul_left (d - l) hright
    _ = d := Nat.add_sub_of_le hl

/-- Every root of a cube source polynomial belongs to `[-1, 0]`. -/
theorem cubeValuePolynomial_roots_mem_Icc (d l : ℕ) :
    ∀ r ∈ (cubeValuePolynomial d l).roots, r ∈ Set.Icc (-1 : ℝ) 0 := by
  intro r hr
  have hroot := (mem_roots (cubeValuePolynomial_ne_zero d l)).mp hr
  simp only [IsRoot, cubeValuePolynomial, eval_mul, eval_pow, eval_C, eval_X,
    eval_add, eval_one] at hroot
  rcases mul_eq_zero.mp hroot with hzero | hhalf
  · have : 2 * r = 0 := by
      by_contra hne
      exact (pow_ne_zero l hne) hzero
    constructor <;> linarith
  · have : 2 * r + 1 = 0 := by
      by_contra hne
      exact (pow_ne_zero (d - l) hne) hhalf
    constructor <;> linarith

/-- Every refined cube polynomial is a Pólya-frequency polynomial. -/
theorem cubeColoredEulerian_isPFPolynomial (d l : ℕ) :
    IsPFPolynomial (cubeColoredEulerian d l) := by
  unfold cubeColoredEulerian
  apply IsPFPolynomial.polynomialValueEulerNumerator_of_roots_mem_Icc
  · exact cubeValuePolynomial_splits d l
  · exact cubeValuePolynomial_nonneg d l _
  · exact cubeValuePolynomial_roots_mem_Icc d l

/-- Every refined cube polynomial has nonnegative coefficients. -/
theorem cubeColoredEulerian_nonneg (d l : ℕ) :
    HasNonnegCoeffs (cubeColoredEulerian d l) :=
  (cubeColoredEulerian_isPFPolynomial d l).hasNonnegCoeffs

/-- Every refined cube polynomial is nonzero and splits over the reals. -/
theorem cubeColoredEulerian_ne_zero_and_splits (d l : ℕ) :
    cubeColoredEulerian d l ≠ 0 ∧ (cubeColoredEulerian d l).Splits := by
  exact (cubeColoredEulerian_isPFPolynomial d l).ne_zero_and_splits
    (polynomialValueEulerNumerator_ne_zero (cubeValuePolynomial_ne_zero d l))

/-- In its intended range, a refined cube polynomial has degree at most
`d`. -/
theorem cubeColoredEulerian_natDegree_le {d l : ℕ} (hl : l ≤ d) :
    (cubeColoredEulerian d l).natDegree ≤ d := by
  exact (natDegree_polynomialValueEulerNumerator_le
    (cubeValuePolynomial d l)).trans (cubeValuePolynomial_natDegree_le hl)

/-- Every admissible half-open cube polynomial has nonnegative
coefficients. -/
theorem cubeRelativeHPolynomial_nonneg (d l : ℕ) :
    HasNonnegCoeffs (cubeRelativeHPolynomial d l) := by
  rw [cubeRelativeHPolynomial]
  split_ifs with hld
  · exact cubeColoredEulerian_nonneg d l
  · apply HasNonnegCoeffs.mul hasNonnegCoeffs_X
    exact (cubeColoredEulerian_nonneg d (2 * d - l)).reflect d

/-- Every admissible half-open cube polynomial is nonzero and splits over
the reals. -/
theorem cubeRelativeHPolynomial_ne_zero_and_splits {d l : ℕ}
    (hl : l ≤ 2 * d) :
    cubeRelativeHPolynomial d l ≠ 0 ∧
      (cubeRelativeHPolynomial d l).Splits := by
  rw [cubeRelativeHPolynomial]
  split_ifs with hld
  · exact cubeColoredEulerian_ne_zero_and_splits d l
  · have hindex : 2 * d - l ≤ d := by lia
    have hreflect := reflect_isRealRooted
      (cubeColoredEulerian_ne_zero_and_splits d (2 * d - l))
      (cubeColoredEulerian_natDegree_le hindex)
    exact ⟨mul_ne_zero (by simp) hreflect.1,
      Polynomial.Splits.X.mul hreflect.2⟩

/-- Every member of the admissible cube row is nonzero, real-rooted, and
coefficientwise nonnegative. -/
theorem cubeRelativeHRow_realRooted_nonneg (d : ℕ) :
    ∀ p ∈ cubeRelativeHRow d,
      (p ≠ 0 ∧ p.Splits) ∧ HasNonnegCoeffs p := by
  intro p hp
  rw [cubeRelativeHRow, List.mem_ofFn] at hp
  rcases hp with ⟨l, rfl⟩
  have hl : l.val ≤ 2 * d := by lia
  exact ⟨cubeRelativeHPolynomial_ne_zero_and_splits hl,
    cubeRelativeHPolynomial_nonneg d l⟩

end RealRooted.HlavacekSolus
