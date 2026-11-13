module

public import RealRooted.ArrayPolynomialSchur
public import RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real
import RealRooted.Mathlib.Analysis.SpecialFunctions.Choose
import RealRooted.MultiplierSequence.PolyaSchur.Schur

/-!
# Falling-factorial truncations and scalar Bell rows

We reuse `fallingSchur p f`, whose coefficient of `X ^ j` is
`(p.descFactorial j : ℝ) * f.coeff j`. We identify it with the reflection of
`f(D) (X ^ p)`, reuse Schur's factorial-product theorem for preservation of
real splitting, and recover the symbol as the coefficientwise limit after
rescaling `X` by `1 / p`.

The final application is the scalar big-block reduction from
[issue #1773](https://github.com/PerAlexandersson/RealRooted/issues/1773) and
[issue #2415](https://github.com/PerAlexandersson/RealRooted/issues/2415).
Real-rootedness of every scalar row remains **open**; the supplied notes report
exact checks through rank 25. We prove only the equivalence with all its
falling-factorial truncations, together with the first three rows.
-/

@[expose] public section

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

open FiniteDegreeOrdered

/-- The falling-factorial truncation is the reflected monomial differential test. -/
theorem fallingSchur_eq_jensenDifferentialTest (p : ℕ) (f : ℝ[X]) :
    fallingSchur p f = jensenDifferentialTest p f := by
  ext j
  rw [coeff_fallingSchur_eq_descFactorial]
  by_cases hj : j ≤ p
  · exact (coeff_jensenDifferentialTest_of_le p f hj).symm
  · have hdeg : (jensenDifferentialTest p f).natDegree ≤ p :=
      Polynomial.natDegree_reflect_le.trans
        (max_eq_left (natDegree_finiteDifferentialTest_le p f)).le
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hj)]
    simp only [Nat.cast_zero, zero_mul]
    exact (coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (Nat.lt_of_not_ge hj))).symm

/-- The existing Schur-product definition is the finite falling-factorial sum;
all coefficients above the truncation cap vanish. -/
theorem fallingSchur_eq_sum_range (p : ℕ) (f : ℝ[X]) :
    fallingSchur p f = ∑ j ∈ Finset.range (p + 1),
      ((p.descFactorial j : ℝ) * f.coeff j) • (X : ℝ[X]) ^ j := by
  have hdeg : (fallingSchur p f).natDegree ≤ p :=
    (natDegree_factorialHadamardProduct_le_right f ((X + 1) ^ p)).trans
      (natDegree_X_add_one_pow_le p)
  rw [as_sum_range' (fallingSchur p f) (p + 1) (Nat.lt_succ_of_le hdeg)]
  simp only [coeff_fallingSchur_eq_descFactorial, ← C_mul_X_pow_eq_monomial,
    smul_eq_C_mul]

/-- Falling-factorial coefficient multiplication preserves splitting over the reals,
including zero outputs and inputs with coefficients of either sign. -/
theorem splits_fallingSchur {f : ℝ[X]} (hf : f.Splits) (p : ℕ) :
    (fallingSchur p f).Splits := by
  rcases factorialHadamardProduct_eq_zero_or_splits_of_isPFPolynomial hf
      (isPFPolynomial_X_add_one_pow p) with hzero | hsplit
  · rw [fallingSchur, hzero]
    exact Splits.zero
  · exact hsplit

/-- Once the cap reaches the input degree, falling-factorial truncation preserves
the degree, including for the zero polynomial. -/
theorem natDegree_fallingSchur_of_le (f : ℝ[X]) {p : ℕ} (hp : f.natDegree ≤ p) :
    (fallingSchur p f).natDegree = f.natDegree := by
  by_cases hf0 : f = 0
  · simp [hf0]
  apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_fallingSchur_le p f)
  rw [coeff_fallingSchur_eq_descFactorial, coeff_natDegree]
  exact mul_ne_zero (by exact_mod_cast (Nat.descFactorial_pos.mpr hp).ne')
    (leadingCoeff_ne_zero.mpr hf0)

/-- Each coefficient of the rescaled falling-factorial truncation tends to the
corresponding coefficient of the original polynomial. -/
theorem tendsto_coeff_fallingSchur_comp (f : ℝ[X]) (j : ℕ) :
    Tendsto (fun p : ℕ => ((fallingSchur p f).comp (C ((p : ℝ)⁻¹) * X)).coeff j)
      atTop (𝓝 (f.coeff j)) := by
  simp only [Polynomial.comp_C_mul_X_coeff, coeff_fallingSchur_eq_descFactorial]
  simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_assoc, mul_comm, mul_left_comm] using
    (Nat.tendsto_descFactorial_div_pow_atTop j).mul_const (f.coeff j)

/-- If all falling-factorial truncations split over the reals, then the original
polynomial splits, by bounded-degree closure after rescaling `X ↦ X / p`. -/
theorem splits_of_forall_fallingSchur {f : ℝ[X]}
    (hf : ∀ p : ℕ, (fallingSchur p f).Splits) : f.Splits := by
  let q : ℕ → ℝ[X] := fun p => (fallingSchur p f).comp (C ((p : ℝ)⁻¹) * X)
  have hlinear (p : ℕ) : (C ((p : ℝ)⁻¹) * X : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans natDegree_X_le
  have hdeg (p : ℕ) : (q p).natDegree ≤ f.natDegree :=
    natDegree_comp_le.trans ((Nat.mul_le_mul_left _ (hlinear p)).trans
      (by simpa using natDegree_fallingSchur_le p f))
  have hsplit (p : ℕ) : q p = 0 ∨ (q p).Splits :=
    .inr ((hf p).comp_of_natDegree_le_one (hlinear p))
  have heval (p : ℝ[X]) (hp : p.natDegree ≤ f.natDegree) (z : ℂ) :
      (p.map Complex.ofRealHom).eval z =
        ∑ j ∈ Finset.range (f.natDegree + 1), (p.coeff j : ℂ) * z ^ j := by
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range' Complex.ofRealHom
      (Nat.lt_succ_of_le hp) z]
    rfl
  rcases Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le hdeg hsplit
      (p₀ := f) (fun z => by
        simp only [heval _ (hdeg _) z, heval f le_rfl z]
        refine tendsto_finsetSum _ fun j _ => ?_
        exact ((Complex.continuous_ofReal.tendsto _).comp
          (tendsto_coeff_fallingSchur_comp f j)).mul_const (z ^ j)) with hzero | hsplit
  · rw [hzero]
    exact Splits.zero
  · exact hsplit

/-- A real polynomial splits exactly when every falling-factorial truncation splits.
The convention includes the zero polynomial. -/
theorem forall_splits_fallingSchur_iff (f : ℝ[X]) :
    (∀ p : ℕ, (fallingSchur p f).Splits) ↔ f.Splits :=
  ⟨splits_of_forall_fallingSchur, fun hf p => splits_fallingSchur hf p⟩

/-- The canonical distinguished-block recurrence for two-weight set partitions.
A block of size `r` has weight `α r + X * β r`; values at `r = 0` are unused.
This is the row family of issue #2415, indexed by `a = r - 1`. -/
def weightedBell (α β : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => ∑ a ∈ Finset.range (n + 1),
      C (n.choose a : ℝ) * (C (α (a + 1)) + C (β (a + 1)) * X) *
        weightedBell α β (n - a)

/-- The empty weighted set partition has weight one. -/
@[simp] theorem weightedBell_zero (α β : ℕ → ℝ) : weightedBell α β 0 = 1 := by
  rw [weightedBell]

/-- The distinguished block has size `a + 1` and leaves `n - a` elements. -/
theorem weightedBell_succ (α β : ℕ → ℝ) (n : ℕ) :
    weightedBell α β (n + 1) = ∑ a ∈ Finset.range (n + 1),
      C (n.choose a : ℝ) * (C (α (a + 1)) + C (β (a + 1)) * X) *
        weightedBell α β (n - a) := by
  rw [weightedBell]

/-- The scalar big-block row `𝓑_m`: unmarked singleton weight one, and marked
size-`r` weight `2 / ((r + 1) * (r + 2))`. Equivalently, its intended EGF is
`exp(z + t C(z))`, where `C(z) = ∑_{s ≥ 1} 2 z^s / (s + 2)!`.
Real-rootedness for every rank is open (exact checks through rank 25 in the
supplied notes); see issues #1773 and #2415 linked in the module docstring. -/
def bigBlockScalar (m : ℕ) : ℝ[X] :=
  weightedBell (fun r => if r = 1 then 1 else 0)
    (fun r => 2 / (((r : ℝ) + 1) * ((r : ℝ) + 2))) m

/-- The normalized big-block row `R_{m,p}`, defined by its falling-factorial
coefficient transform. Combinatorially, this is the enumerator of partitions
of `m + 2p` elements with exactly `p` nonsingleton blocks, marking blocks of
size at least three, multiplied by `2^p p! m! / (m + 2p)!`.
The connection with that partition model is explanatory; here the scalar
rows and this transform are defined algebraically. -/
def normalizedBigBlock (m p : ℕ) : ℝ[X] := fallingSchur p (bigBlockScalar m)

/-- The first scalar big-block row. -/
theorem bigBlockScalar_one : bigBlockScalar 1 = 1 + C (1 / 3 : ℝ) * X := by
  norm_num [bigBlockScalar, weightedBell, Finset.sum_range_succ]

/-- The second scalar big-block row. -/
theorem bigBlockScalar_two :
    bigBlockScalar 2 = 1 + C (5 / 6 : ℝ) * X + C (1 / 9 : ℝ) * X ^ 2 := by
  apply Polynomial.funext
  intro x
  norm_num [bigBlockScalar, weightedBell, Finset.sum_range_succ]
  ring

/-- The third scalar big-block row. -/
theorem bigBlockScalar_three :
    bigBlockScalar 3 =
      1 + C (8 / 5 : ℝ) * X + C (1 / 2 : ℝ) * X ^ 2 + C (1 / 27 : ℝ) * X ^ 3 := by
  apply Polynomial.funext
  intro x
  norm_num [bigBlockScalar, weightedBell, Finset.sum_range_succ]
  ring

/-- At each fixed rank, splitting of every normalized truncation is equivalent
to splitting of the scalar big-block row. This does not assert either side. -/
theorem forall_splits_normalizedBigBlock_iff (m : ℕ) :
    (∀ p : ℕ, (normalizedBigBlock m p).Splits) ↔ (bigBlockScalar m).Splits :=
  forall_splits_fallingSchur_iff (bigBlockScalar m)

end RealRooted
