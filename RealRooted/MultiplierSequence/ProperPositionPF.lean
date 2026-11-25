module

import RealRooted.MultiplierSequence.ProperPosition
import RealRooted.PFPolynomial.Closure
import RealRooted.PFPolynomial.CoefficientShape
import RealRooted.BorceaBranden.Applications.HomogenizeStable
import RealRooted.Mathlib.Algebra.Polynomial.Homogenize
import RealRooted.BorceaBranden.Applications.RealUnivariateSymbol.Interlacing
public import RealRooted.MultiplierSequence.Infinite
import RealRooted.Hadamard.Grace
import RealRooted.PosCombo
public import RealRooted.WeightedSum
public import RealRooted.InterlacingSequenceBasic
import RealRooted.Linear
import RealRooted.Mathlib.Data.Nat.Choose.Cast

/-!
# Degree-drop transport for finite PF multiplier sequences

We identify the finite diagonal symbol with the homogenized Jensen polynomial.
The general stable-symbol interlacing theorem then retains the directed,
zero-aware relation, including when top multipliers vanish.
-/

public section

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- A nonzero PF polynomial with positive constant coefficient has positive
coefficients through its natural degree. -/
theorem IsPFPolynomial.coeff_pos_of_coeff_zero_pos
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hzero : 0 < p.coeff 0)
    {k : ℕ} (hk : k ≤ p.natDegree) :
    0 < p.coeff k := by
  have hp0 : p ≠ 0 := by
    intro hpzero
    simp [hpzero] at hzero
  have hnonneg : 0 ≤ p.coeff k := hp.hasNonnegCoeffs k
  apply lt_of_le_of_ne hnonneg
  intro hcoeff
  have hlead : p.coeff p.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hkzero : k ≠ 0 := by
    intro hkzero
    subst k
    exact hzero.ne' hcoeff.symm
  have hktop : p.natDegree ≠ k := by
    intro hktop
    apply hlead
    rw [hktop]
    exact hcoeff.symm
  have hkcoeff := hp.hasNoInternalCoeffZeros 0 k p.natDegree
    (Nat.pos_of_ne_zero hkzero) (lt_of_le_of_ne hk hktop.symm) le_rfl hzero.ne' hlead
  exact hkcoeff hcoeff.symm

/-- The diagonal symbol is the padded homogenization of its Jensen polynomial. -/
private theorem finiteAlgebraicSymbol_diagonalLinearMap (N : ℕ) (gamma : ℕ → ℝ) :
    BorceaBranden.finiteAlgebraicSymbol N (diagonalLinearMap gamma) =
      (jensenPolynomial N gamma).homogenize N := by
  rw [Polynomial.homogenize_eq_sum_range_C_mul_X_pow (natDegree_jensenPolynomial_le N gamma)]
  unfold BorceaBranden.finiteAlgebraicSymbol
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [diagonalLinearMap_apply, Polynomial.X_pow_eq_monomial,
    diagonalOperator_monomial, mul_one, BorceaBranden.polynomialInFirstMv,
    Polynomial.eval₂_monomial, coeff_jensenPolynomial, hkN, ↓reduceIte,
    MvPolynomial.C_mul]
  ring

private theorem diagonalOperator_eq_zero_of_jensenPolynomial_eq_zero
    {N : ℕ} {gamma : ℕ → ℝ}
    (hzero : jensenPolynomial N gamma = 0) {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ N) :
    diagonalOperator gamma p = 0 := by
  have hgamma := jensenPolynomial_eq_zero_iff.mp hzero
  ext k
  rw [coeff_diagonalOperator, coeff_zero]
  by_cases hk : k ≤ N
  · rw [hgamma k hk, zero_mul]
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg (Nat.lt_of_not_le hk)),
      mul_zero]

/-- A finite PF multiplier sequence preserves zero-aware directed
interlacing, even when vanishing top multipliers lower either output degree. -/
theorem IsFinitePFMultiplierSequence.interl_diagonalOperator
    {N : ℕ} {gamma : ℕ → ℝ}
    (hgamma : IsFinitePFMultiplierSequence N gamma)
    {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfg : Interl f g)
    (hfdeg : f.natDegree ≤ N) (hgdeg : g.natDegree ≤ N) :
    Interl (diagonalOperator gamma f) (diagonalOperator gamma g) := by
  have hJ := isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence hgamma
  by_cases hJ0 : jensenPolynomial N gamma = 0
  · rw [diagonalOperator_eq_zero_of_jensenPolynomial_eq_zero hJ0 hfdeg,
      diagonalOperator_eq_zero_of_jensenPolynomial_eq_zero hJ0 hgdeg]
    exact interl_zero_left 0
  by_cases hf0 : f = 0
  · simp only [hf0, diagonalOperator_zero]
    exact interl_zero_left _
  by_cases hg0 : g = 0
  · simp only [hg0, diagonalOperator_zero]
    exact interl_zero_right _
  have hSymbol : MvUpperHalfPlaneStable
      (complexifyMv (BorceaBranden.finiteAlgebraicSymbol N (diagonalLinearMap gamma))) := by
    rw [finiteAlgebraicSymbol_diagonalLinearMap]
    exact BorceaBranden.homogenize_stable_of_splits_nonpos_of_natDegree_le
      (natDegree_jensenPolynomial_le N gamma) hJ0 hJ.splits hJ.roots_nonpos
  apply BorceaBranden.linearMap_interl_of_finiteSymbol_stable
    hSymbol hgdeg hfdeg (hfg.toStrictInterl_of_ne hf0 hg0)
    (hg.hasNonnegCoeffs.pos_leadingCoeff hg0) (hf.hasNonnegCoeffs.pos_leadingCoeff hf0)
  · by_cases h : diagonalOperator gamma g = 0
    · exact Or.inl h
    · exact Or.inr ((hgamma hg hgdeg).hasNonnegCoeffs.pos_leadingCoeff h)
  · by_cases h : diagonalOperator gamma f = 0
    · exact Or.inl h
    · exact Or.inr ((hgamma hf hfdeg).hasNonnegCoeffs.pos_leadingCoeff h)

private theorem natDegree_diagonalOperator_eq
    {gamma : ℕ → ℝ} {p : ℝ[X]} (hp0 : p ≠ 0)
    (hgamma : gamma p.natDegree ≠ 0) :
    (diagonalOperator gamma p).natDegree = p.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_diagonalOperator_le gamma p)
  rw [coeff_diagonalOperator, Polynomial.coeff_natDegree]
  exact mul_ne_zero hgamma (Polynomial.leadingCoeff_ne_zero.mpr hp0)

/-- When adjacent multipliers have nonpositive product, a finite multiplier
sequence reverses directed proper position on an equal positive-degree pair. -/
theorem IsFiniteMultiplierSequence.strictInterl_diagonalOperator_reverse
    {N : ℕ} {gamma : ℕ → ℝ}
    (hgamma : IsFiniteMultiplierSequence N gamma)
    {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hfdeg : f.natDegree ≤ N) (hgdeg : g.natDegree ≤ N)
    (hdegree : f.natDegree = g.natDegree)
    (hgamma_f : gamma f.natDegree ≠ 0)
    (hgamma_g : gamma g.natDegree ≠ 0)
    (hsign : gamma (f.natDegree - 1) * gamma f.natDegree ≤ 0) :
    StrictInterl (diagonalOperator gamma g) (diagonalOperator gamma f) := by
  let delta : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * gamma k
  have hdelta_f : delta f.natDegree ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hgamma_f
  have hdelta_g : delta g.natDegree ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hgamma_g
  have hforward :
      StrictInterl (diagonalOperator delta f) (diagonalOperator delta g) := by
    apply IsFiniteMultiplierSequence.strictInterl_diagonalOperator
      hgamma.alternating hfg hfdeg hgdeg
      hdelta_f hdelta_g
    intro _ hpos
    have hpred : f.natDegree - 1 + 1 = f.natDegree := by lia
    have hpow :
        (-1 : ℝ) ^ (f.natDegree - 1) *
            (-1 : ℝ) ^ (f.natDegree - 1) = 1 := by
      rw [← pow_add, show f.natDegree - 1 + (f.natDegree - 1) =
        2 * (f.natDegree - 1) by lia, pow_mul]
      norm_num
    have hpow_succ : (-1 : ℝ) ^ f.natDegree =
        (-1 : ℝ) ^ (f.natDegree - 1) * -1 := by
      conv_lhs => rw [← hpred, pow_succ]
    have halt :
        delta (f.natDegree - 1) * delta f.natDegree =
          -(gamma (f.natDegree - 1) * gamma f.natDegree) := by
      dsimp [delta]
      rw [hpow_succ]
      rw [show (-1 : ℝ) ^ (f.natDegree - 1) * gamma (f.natDegree - 1) *
          ((-1 : ℝ) ^ (f.natDegree - 1) * -1 * gamma f.natDegree) =
          -((-1 : ℝ) ^ (f.natDegree - 1) *
              (-1 : ℝ) ^ (f.natDegree - 1)) *
            (gamma (f.natDegree - 1) * gamma f.natDegree) by ring, hpow]
      ring
    rw [halt]
    linarith
  have hdelta_degree :
      (diagonalOperator delta f).natDegree =
        (diagonalOperator delta g).natDegree := by
    rw [natDegree_diagonalOperator_eq hfg.1.1 hdelta_f,
      natDegree_diagonalOperator_eq hfg.2.1.1 hdelta_g, hdegree]
  have hreflected := hforward.comp_neg_X_of_natDegree_eq hdelta_degree
  rw [diagonalOperator_alternating, diagonalOperator_alternating] at hreflected
  simpa [Polynomial.comp_assoc] using hreflected

/-- On an equal-degree pair, a nonnegative adjacent multiplier ratio selects
the forward orientation. -/
theorem IsFiniteMultiplierSequence.strictInterl_diagonalOperator_of_ratio_nonneg
    {N : ℕ} {gamma : ℕ → ℝ}
    (hgamma : IsFiniteMultiplierSequence N gamma)
    {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hfdeg : f.natDegree ≤ N) (hgdeg : g.natDegree ≤ N)
    (hgamma_f : gamma f.natDegree ≠ 0)
    (hgamma_g : gamma g.natDegree ≠ 0)
    (hratio : 0 ≤ gamma (f.natDegree - 1) / gamma f.natDegree) :
    StrictInterl (diagonalOperator gamma f) (diagonalOperator gamma g) := by
  apply IsFiniteMultiplierSequence.strictInterl_diagonalOperator hgamma
    hfg hfdeg hgdeg hgamma_f hgamma_g
  intro _hdegree _hpos
  have hrewrite := (div_mul_cancel₀ (gamma (f.natDegree - 1)) hgamma_f).symm
  rw [hrewrite]
  nlinarith [sq_nonneg (gamma f.natDegree)]

/-- On an equal-degree pair, a nonpositive adjacent multiplier ratio selects
the reverse orientation. -/
theorem IsFiniteMultiplierSequence.strictInterl_diagonalOperator_reverse_of_ratio_nonpos
    {N : ℕ} {gamma : ℕ → ℝ}
    (hgamma : IsFiniteMultiplierSequence N gamma)
    {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hfdeg : f.natDegree ≤ N) (hgdeg : g.natDegree ≤ N)
    (hdegree : f.natDegree = g.natDegree)
    (hgamma_f : gamma f.natDegree ≠ 0)
    (hgamma_g : gamma g.natDegree ≠ 0)
    (hratio : gamma (f.natDegree - 1) / gamma f.natDegree ≤ 0) :
    StrictInterl (diagonalOperator gamma g) (diagonalOperator gamma f) := by
  apply IsFiniteMultiplierSequence.strictInterl_diagonalOperator_reverse hgamma
    hfg hfdeg hgdeg hdegree hgamma_f hgamma_g
  have hrewrite := (div_mul_cancel₀ (gamma (f.natDegree - 1)) hgamma_f).symm
  rw [hrewrite]
  nlinarith [sq_nonneg (gamma f.natDegree)]

/-- A zero adjacent multiplier ratio gives both orientations on an
equal-degree pair. -/
theorem IsFiniteMultiplierSequence.strictInterl_diagonalOperator_both_of_ratio_eq_zero
    {N : ℕ} {gamma : ℕ → ℝ}
    (hgamma : IsFiniteMultiplierSequence N gamma)
    {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hfdeg : f.natDegree ≤ N) (hgdeg : g.natDegree ≤ N)
    (hdegree : f.natDegree = g.natDegree)
    (hgamma_f : gamma f.natDegree ≠ 0)
    (hgamma_g : gamma g.natDegree ≠ 0)
    (hratio : gamma (f.natDegree - 1) / gamma f.natDegree = 0) :
    StrictInterl (diagonalOperator gamma f) (diagonalOperator gamma g) ∧
      StrictInterl (diagonalOperator gamma g) (diagonalOperator gamma f) := by
  exact ⟨hgamma.strictInterl_diagonalOperator_of_ratio_nonneg hfg hfdeg hgdeg
      hgamma_f hgamma_g hratio.ge,
    hgamma.strictInterl_diagonalOperator_reverse_of_ratio_nonpos hfg hfdeg hgdeg
      hdegree hgamma_f hgamma_g hratio.le⟩

private theorem HasPosLeadingCoeff.diagonalOperator_of_pos
    {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 < gamma k)
    {p : ℝ[X]} (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (diagonalOperator gamma p) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hdegree := natDegree_diagonalOperator_eq hp0 (hgamma p.natDegree).ne'
  unfold HasPosLeadingCoeff
  rw [Polynomial.leadingCoeff, hdegree, coeff_diagonalOperator,
    Polynomial.coeff_natDegree]
  exact mul_pos (hgamma p.natDegree) hp

/-- A strictly positive multiplier sequence transports a common-left family
and its nontrivial nonnegative weighted sums. -/
theorem IsMultiplierSequence.strictInterl_weightedSum_left_of_pos
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma)
    (hgamma_pos : ∀ k, 0 < gamma k)
    (l : List (ℝ × ℝ[X])) (h : ℝ[X])
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hinterl : ∀ ap ∈ l, StrictInterl h ap.2)
    (hpoly_pos : ∀ ap ∈ l, HasPosLeadingCoeff ap.2)
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    StrictInterl (diagonalOperator gamma h)
      (weightedSum (l.map fun ap => (ap.1, diagonalOperator gamma ap.2))) := by
  apply StrictInterl.weightedSum_left_of_common_left_signed
  · simpa only [List.forall_mem_map] using hnonneg
  · rw [List.forall_mem_map]
    intro bp hbp
    exact IsMultiplierSequence.strictInterl_diagonalOperator_of_pos
      hgamma hgamma_pos (hinterl bp hbp)
  · rw [List.forall_mem_map]
    intro bp hbp
    exact (hpoly_pos bp hbp).diagonalOperator_of_pos hgamma_pos
  · rcases hex with ⟨ap, hap, hpos⟩
    exact ⟨_, List.mem_map.mpr ⟨ap, hap, rfl⟩, hpos⟩

/-- A strictly positive multiplier sequence transports a common-right family
and its nontrivial nonnegative weighted sums. -/
theorem IsMultiplierSequence.strictInterl_weightedSum_right_of_pos
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma)
    (hgamma_pos : ∀ k, 0 < gamma k)
    (l : List (ℝ × ℝ[X])) (h : ℝ[X])
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hinterl : ∀ ap ∈ l, StrictInterl ap.2 h)
    (hpoly_pos : ∀ ap ∈ l, HasPosLeadingCoeff ap.2)
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    StrictInterl
      (weightedSum (l.map fun ap => (ap.1, diagonalOperator gamma ap.2)))
      (diagonalOperator gamma h) := by
  apply StrictInterl.weightedSum_right_of_nonneg
  · simpa only [List.forall_mem_map] using hnonneg
  · rw [List.forall_mem_map]
    intro bp hbp
    exact IsMultiplierSequence.strictInterl_diagonalOperator_of_pos
      hgamma hgamma_pos (hinterl bp hbp)
  · rw [List.forall_mem_map]
    intro bp hbp
    exact (hpoly_pos bp hbp).diagonalOperator_of_pos hgamma_pos
  · rcases hex with ⟨ap, hap, hpos⟩
    exact ⟨_, List.mem_map.mpr ⟨ap, hap, rfl⟩, hpos⟩

/-- Applying a finite PF multiplier coordinatewise preserves zero-aware
nonnegative real-rooted interlacing lists under a uniform degree bound. -/
theorem IsInterlacingSeq0NonnegRealRooted.diagonalOperator_of_finitePF
    {N : ℕ} {gamma : ℕ → ℝ} {fs : List ℝ[X]}
    (hgamma : IsFinitePFMultiplierSequence N gamma)
    (hdeg : ∀ p ∈ fs, p.natDegree ≤ N)
    (hfs : IsInterlacingSeq0NonnegRealRooted fs) :
    IsInterlacingSeq0NonnegRealRooted
      (fs.map (diagonalOperator gamma)) := by
  have hpf (p : ℝ[X]) (hp : p ∈ fs) : IsPFPolynomial p := by
    apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
      (hfs.nonnegCoeffs p hp)
    by_cases hp0 : p = 0
    · exact Or.inl hp0
    · exact Or.inr (hfs.splits hp hp0)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise]
    refine List.pairwise_iff_get.2 ?_
    intro i j hij
    let i' : Fin fs.length := ⟨i.1, by simpa using i.2⟩
    let j' : Fin fs.length := ⟨j.1, by simpa using j.2⟩
    have hi : fs.get i' ∈ fs := List.get_mem _ _
    have hj : fs.get j' ∈ fs := List.get_mem _ _
    have hij' : i' < j' := by simpa [i', j'] using hij
    have hpq := hfs.interlacingSeq0.interl hij'
    simpa [i', j'] using
      IsFinitePFMultiplierSequence.interl_diagonalOperator hgamma
        (hpf _ hi) (hpf _ hj) hpq (hdeg _ hi) (hdeg _ hj)
  · intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact (hgamma (hpf q hq) (hdeg q hq)).hasNonnegCoeffs
  · intro p hp hp0
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact (hgamma (hpf q hq) (hdeg q hq)).ne_zero_and_splits hp0

end RealRooted
