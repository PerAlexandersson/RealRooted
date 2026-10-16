module

public import RealRooted.MultiplierSequence.ProperPosition
public import RealRooted.PFPolynomial.Closure
public import RealRooted.PFPolynomial.CoefficientShape
public import RealRooted.JensenPencilContraction
public import RealRooted.Mathlib.Topology.Algebra.Polynomial

/-!
# Degree-drop transport for finite PF multiplier sequences

We regularize the finite Jensen polynomial by positive translation and by adding
roots which escape to negative infinity.  Coefficientwise PF closure then
retains the directed, zero-aware interlacing relation when top multipliers
vanish.
-/

@[expose] public noncomputable section

open Filter Polynomial Topology

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

private def pfJensenKernel (N : ℕ) (J : ℝ[X]) (ε : ℝ) : ℝ[X] :=
  (((X + C 1 : ℝ[X]) ^ (N - J.natDegree)).comp (C ε * X)) *
    J.comp (X + C ε)

private theorem pfJensenKernel_isPF
    {N : ℕ} {J : ℝ[X]} (hJ : IsPFPolynomial J)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    IsPFPolynomial (pfJensenKernel N J epsilon) := by
  apply IsPFPolynomial.mul
  · simpa using
      ((isPFPolynomial_X_add_C zero_le_one).pow
        (N - J.natDegree)).comp_C_mul_X_add_C hepsilon le_rfl
  · simpa using hJ.comp_C_mul_X_add_C (a := 1) (d := epsilon) zero_lt_one
      hepsilon.le

private theorem pfJensenKernel_natDegree
    {N : ℕ} {J : ℝ[X]} (hJN : J.natDegree ≤ N) (hJ0 : J ≠ 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (pfJensenKernel N J epsilon).natDegree = N := by
  have hfactor0 :
      (((X + C 1 : ℝ[X]) ^ (N - J.natDegree)).comp
        (C epsilon * X)) ≠ 0 := by
    intro hzero
    exact pow_ne_zero _ (Polynomial.X_add_C_ne_zero 1)
      ((Polynomial.comp_C_mul_X_eq_zero_iff (by simpa using hepsilon.ne')).mp hzero)
  rw [pfJensenKernel, Polynomial.natDegree_mul hfactor0
      (Polynomial.comp_X_add_C_ne_zero_iff.mpr hJ0),
    Polynomial.natDegree_comp, Polynomial.natDegree_pow,
    Polynomial.natDegree_X_add_C,
    Polynomial.natDegree_C_mul_X epsilon hepsilon.ne',
    Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C]
  lia

private theorem continuous_coeff_pfJensenKernel (N : ℕ) (J : ℝ[X]) (i : ℕ) :
    Continuous fun epsilon : ℝ => (pfJensenKernel N J epsilon).coeff i := by
  simp_rw [pfJensenKernel, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Polynomial.comp_C_mul_X_coeff]
  apply continuous_finsetSum
  intro j _
  exact (continuous_const.mul (continuous_id.pow j)).mul
    (J.continuous_coeff_comp_X_add_C (i - j))

private theorem pfJensenKernel_zero (N : ℕ) (J : ℝ[X]) :
    pfJensenKernel N J 0 = J := by
  simp [pfJensenKernel]

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
  let J : ℝ[X] := jensenPolynomial N gamma
  have hJpf := isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence hgamma
  by_cases hJ0 : J = 0
  · rw [diagonalOperator_eq_zero_of_jensenPolynomial_eq_zero hJ0 hfdeg,
      diagonalOperator_eq_zero_of_jensenPolynomial_eq_zero hJ0 hgdeg]
    exact interl_zero_left 0
  let epsilon : ℕ → ℝ := fun m => 1 / (m + 1 : ℝ)
  let K : ℕ → ℝ[X] := fun m => pfJensenKernel N J (epsilon m)
  let gammaReg : ℕ → ℕ → ℝ := fun m k =>
    (K m).coeff k / (Nat.choose N k : ℝ)
  have hepsilon_pos (m : ℕ) : 0 < epsilon m := by
    dsimp [epsilon]
    positivity
  have hJdeg : J.natDegree ≤ N := natDegree_jensenPolynomial_le N gamma
  have hKpf (m : ℕ) : IsPFPolynomial (K m) :=
    pfJensenKernel_isPF hJpf (hepsilon_pos m)
  have hKdeg (m : ℕ) : (K m).natDegree = N :=
    pfJensenKernel_natDegree hJdeg hJ0 (hepsilon_pos m)
  have hKzero_pos (m : ℕ) : 0 < (K m).coeff 0 := by
    dsimp [K, pfJensenKernel]
    rw [Polynomial.mul_coeff_zero, Polynomial.comp_C_mul_X_coeff, pow_zero, mul_one,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    norm_num
    have htranslated := hJpf.comp_X_add_C_and_coeff_zero_pos hJ0 (hepsilon_pos m)
    simpa using htranslated.2
  have hgammaReg_pos (m k : ℕ) (hk : k ≤ N) : 0 < gammaReg m k := by
    dsimp [gammaReg]
    exact div_pos (hKpf m |>.coeff_pos_of_coeff_zero_pos (hKzero_pos m) (by
      rw [hKdeg m]
      exact hk)) (by exact_mod_cast Nat.choose_pos hk)
  have hKjensen (m : ℕ) : jensenPolynomial N (gammaReg m) = K m := by
    exact jensenPolynomial_normalized_coeff_eq_of_natDegree_le (by rw [hKdeg m])
  have hgammaReg_mult (m : ℕ) : IsFiniteMultiplierSequence N (gammaReg m) := by
    apply isFiniteMultiplierSequence_of_isPFPolynomial_jensenPolynomial
    rw [hKjensen m]
    exact hKpf m
  have hgammaReg_pf (m : ℕ) : IsFinitePFMultiplierSequence N (gammaReg m) := by
    apply isFinitePFMultiplierSequence_of_finiteMultiplierSequence
    · intro k
      by_cases hk : k ≤ N
      · exact (hgammaReg_pos m k hk).le
      · simp [gammaReg, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hk)]
    · exact hgammaReg_mult m
  have hinterl (m : ℕ) :
      Interl (diagonalOperator (gammaReg m) f)
        (diagonalOperator (gammaReg m) g) := by
    by_cases hf0 : f = 0
    · subst f
      simpa only [diagonalOperator_zero] using interl_zero_left (diagonalOperator (gammaReg m) g)
    by_cases hg0 : g = 0
    · subst g
      simpa only [diagonalOperator_zero] using interl_zero_right (diagonalOperator (gammaReg m) f)
    apply StrictInterl.toInterl
    apply IsFiniteMultiplierSequence.strictInterl_diagonalOperator
      (hgammaReg_mult m)
      (hfg.toStrictInterl_of_ne hf0 hg0) hfdeg hgdeg
      (hgammaReg_pos m f.natDegree hfdeg).ne'
      (hgammaReg_pos m g.natDegree hgdeg).ne'
    intro hdegree hpos
    exact mul_nonneg (hgammaReg_pos m (f.natDegree - 1) (by lia)).le
      (hgammaReg_pos m f.natDegree hfdeg).le
  have hepsilon : Tendsto epsilon atTop (𝓝 0) := by
    simpa [epsilon, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hKcoeff (i : ℕ) : Tendsto (fun m => (K m).coeff i) atTop
      (𝓝 (J.coeff i)) := by
    have hcont : Tendsto
        (fun e : ℝ ↦ (pfJensenKernel N J e).coeff i) (𝓝 0)
          (𝓝 ((pfJensenKernel N J 0).coeff i)) :=
      (continuous_coeff_pfJensenKernel N J i).continuousAt
    change Tendsto ((fun e : ℝ ↦ (pfJensenKernel N J e).coeff i) ∘ epsilon)
      atTop (𝓝 (J.coeff i))
    simpa only [pfJensenKernel_zero] using hcont.comp hepsilon
  have hcoeff (p : ℝ[X]) (hpdeg : p.natDegree ≤ N) (i : ℕ) :
      Tendsto (fun m => (diagonalOperator (gammaReg m) p).coeff i) atTop
        (𝓝 ((diagonalOperator gamma p).coeff i)) := by
    by_cases hi : i ≤ N
    · have hchoose : (Nat.choose N i : ℝ) ≠ 0 :=
        Nat.cast_choose_ne_zero hi
      have hreg : Tendsto (fun m => gammaReg m i) atTop (𝓝 (gamma i)) := by
        dsimp [gammaReg]
        have hdiv := (hKcoeff i).div_const (Nat.choose N i : ℝ)
        simpa only [J, coeff_jensenPolynomial, hi, ite_true,
          mul_div_cancel_left₀ _ hchoose] using hdiv
      simpa only [coeff_diagonalOperator] using hreg.mul_const (p.coeff i)
    · have hip : p.coeff i = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg (Nat.lt_of_not_le hi))
      simp only [coeff_diagonalOperator, hip, mul_zero]
      exact tendsto_const_nhds
  apply interl_of_pf_coeff_tendsto_of_natDegree_le
    (fun m => hgammaReg_pf m hf hfdeg)
    (fun m => hgammaReg_pf m hg hgdeg) hinterl
    (fun m => (natDegree_diagonalOperator_le (gammaReg m) f).trans hfdeg)
    (fun m => (natDegree_diagonalOperator_le (gammaReg m) g).trans hgdeg)
    (hcoeff f hfdeg) (hcoeff g hgdeg)

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
