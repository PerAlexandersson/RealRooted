module

public import RealRooted.PFPolynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import RealRooted.CombinatorialExamples.EvenBinom
public import RealRooted.Interlacing.PencilPreserver
import RealRooted.PFPolynomial.Closure
import Mathlib.Data.Nat.Choose.Vandermonde
import RealRooted.EulerBidiagonal.General
import RealRooted.MaWang.StrictSigns.RootSigns
import RealRooted.PFPolynomial.PreserverClosure
import RealRooted.QuadraticRoot
import RealRooted.RootCounting.SignChanges
import RealRooted.SameDegreeDerivative

/-!
# Coefficient perturbations of even-binomial polynomials

Sharp coefficientwise perturbations of the polynomial with coefficients
`Nat.choose (2 * d) (2 * k)`.
-/

public section

open Filter Polynomial

noncomputable section

namespace RealRooted

/-- Positive values after two opposite sign normalizations have negative product. -/
private theorem mul_neg_of_signed_pos {a b : ℝ} {m n : ℕ}
    (ha : 0 < (-1 : ℝ) ^ m * a) (hb : 0 < (-1 : ℝ) ^ n * b)
    (hodd : Odd (m + n)) : a * b < 0 := by
  have hpow : (-1 : ℝ) ^ m * (-1 : ℝ) ^ n = -1 := by
    rw [← pow_add, hodd.neg_one_pow]
  nlinarith [mul_pos ha hb]

/-- Choosing complete pairs gives at least as many subsets as choosing from the set of pairs. -/
theorem choose_le_even_choose {d k : ℕ} (hk : k ≤ d) :
    d.choose k ≤ (2 * d).choose (2 * k) := by
  rw [show 2 * d = d + d by lia, Nat.add_choose_eq]
  have hmem :
      (k, k) ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) (2 * k) := by
    simp [two_mul]
  calc
    d.choose k ≤ d.choose k * d.choose k := by
      exact Nat.le_mul_of_pos_right _ (Nat.choose_pos hk)
    _ ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) (2 * k),
        d.choose ij.1 * d.choose ij.2 := by
      exact Finset.single_le_sum
        (f := fun ij => d.choose ij.1 * d.choose ij.2)
        (fun _ _ => Nat.zero_le _) hmem

/-- A binomial coefficient bound controls evaluation on the negative real axis. -/
theorem abs_eval_neg_le_binomial_bound {h : ℝ[X]} {d : ℕ} {M t : ℝ}
    (hdegree : h.natDegree ≤ d) (ht : 0 ≤ t)
    (hcoeff : ∀ k ≤ d, |h.coeff k| ≤ M * d.choose k) :
    |h.eval (-t)| ≤ M * (1 + t) ^ d := by
  have heval :
      h.eval (-t) = ∑ k ∈ Finset.range (d + 1), h.coeff k * (-t) ^ k := by
    rw [Polynomial.eval_eq_sum_range' (p := h) (n := d + 1) (by lia)]
  rw [heval]
  calc
    |∑ k ∈ Finset.range (d + 1), h.coeff k * (-t) ^ k| ≤
        ∑ k ∈ Finset.range (d + 1), |h.coeff k * (-t) ^ k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.range (d + 1), |h.coeff k| * t ^ k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg ht]
    _ ≤ ∑ k ∈ Finset.range (d + 1), (M * d.choose k) * t ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right
        (hcoeff k (by simpa using Finset.mem_range.mp hk)) (pow_nonneg ht k)
    _ = ∑ k ∈ Finset.range (d + 1), M * ((d.choose k : ℝ) * t ^ k) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = M * ∑ k ∈ Finset.range (d + 1), (d.choose k : ℝ) * t ^ k := by
      rw [Finset.mul_sum]
    _ = M * (1 + t) ^ d := by
      congr 1
      simpa [Polynomial.eval_eq_sum_range, Polynomial.coeff_one_add_X_pow] using
        (show ((1 + X : ℝ[X]) ^ d).eval t = (1 + t) ^ d by simp)

/-- At the standard trigonometric grid, a strict binomially bounded perturbation keeps
the alternating signs of the scaled even-binomial polynomial. -/
theorem evenBinomPolyReal_add_grid_sign {h : ℝ[X]} {d : ℕ} {alpha M : ℝ}
    (hd : 0 < d) (hdegree : h.natDegree ≤ d) (hMalpha : M < alpha)
    (hcoeff : ∀ j ≤ d, |h.coeff j| ≤ M * d.choose j)
    (k : ℕ) (hk : k < d) :
    0 < (-1 : ℝ) ^ k *
      (C alpha * BigDescents.evenBinomPolyReal (2 * d) + h).eval
        (-(Real.tan (((k : ℝ) * Real.pi) / (2 * (d : ℝ)))) ^ 2) := by
  let theta := ((k : ℝ) * Real.pi) / (2 * (d : ℝ))
  have hdR : (0 : ℝ) < d := by positivity
  have htheta0 : 0 ≤ theta := by
    dsimp [theta]
    positivity
  have hthetalt : theta < Real.pi / 2 := by
    dsimp [theta]
    rw [div_lt_iff₀ (by positivity : 0 < 2 * (d : ℝ))]
    have hkR : (k : ℝ) < d := by exact_mod_cast hk
    nlinarith [Real.pi_pos]
  have hcos : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hthetalt⟩
  have htan : 0 ≤ Real.tan theta ^ 2 := sq_nonneg _
  have hbound := abs_eval_neg_le_binomial_bound hdegree htan hcoeff
  have hone : (1 + Real.tan theta ^ 2) * Real.cos theta ^ 2 = 1 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos.ne']
    nlinarith [Real.sin_sq_add_cos_sq theta]
  have hcosPow : 0 < Real.cos theta ^ (2 * d) := pow_pos hcos _
  have hperturb :
      |h.eval (-(Real.tan theta) ^ 2) * Real.cos theta ^ (2 * d)| ≤ M := by
    rw [abs_mul, abs_of_pos hcosPow]
    calc
      |h.eval (-(Real.tan theta) ^ 2)| * Real.cos theta ^ (2 * d) ≤
          (M * (1 + Real.tan theta ^ 2) ^ d) * Real.cos theta ^ (2 * d) :=
        mul_le_mul_of_nonneg_right hbound hcosPow.le
      _ = M := by
        rw [show Real.cos theta ^ (2 * d) = (Real.cos theta ^ 2) ^ d by
          rw [← pow_mul]]
        rw [show (M * (1 + Real.tan theta ^ 2) ^ d) *
            (Real.cos theta ^ 2) ^ d =
              M * ((1 + Real.tan theta ^ 2) * Real.cos theta ^ 2) ^ d by
                rw [mul_assoc, ← mul_pow]]
        rw [hone, one_pow, mul_one]
  have heven := BigDescents.evenBinomPolyReal_eval_neg_tan_sq_mul_cos_pow
    (2 * d) theta hcos.ne'
  have hphase : (2 * (d : ℝ)) * theta = (k : ℝ) * Real.pi := by
    dsimp [theta]
    field_simp
  have hcast : ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) := by norm_num
  rw [hcast, hphase, Real.cos_nat_mul_pi] at heven
  have heq :
      (C alpha * BigDescents.evenBinomPolyReal (2 * d) + h).eval
          (-(Real.tan theta) ^ 2) * Real.cos theta ^ (2 * d) =
        alpha * (-1 : ℝ) ^ k +
          h.eval (-(Real.tan theta) ^ 2) * Real.cos theta ^ (2 * d) := by
    rw [eval_add, eval_mul, eval_C, add_mul, mul_assoc, heven]
  dsimp [theta] at *
  rcases Nat.even_or_odd k with hevenK | hoddK
  · rw [hevenK.neg_one_pow] at heq ⊢
    have hscaled :
        0 < (C alpha * BigDescents.evenBinomPolyReal (2 * d) + h).eval
            (-(Real.tan (((k : ℝ) * Real.pi) / (2 * (d : ℝ)))) ^ 2) *
              Real.cos (((k : ℝ) * Real.pi) / (2 * (d : ℝ))) ^ (2 * d) := by
      nlinarith [abs_le.mp hperturb]
    have hpos := pos_of_mul_pos_left hscaled hcosPow.le
    simpa using hpos
  · rw [hoddK.neg_one_pow] at heq ⊢
    have hscaled :
        0 < -((C alpha * BigDescents.evenBinomPolyReal (2 * d) + h).eval
            (-(Real.tan (((k : ℝ) * Real.pi) / (2 * (d : ℝ)))) ^ 2) *
              Real.cos (((k : ℝ) * Real.pi) / (2 * (d : ℝ))) ^ (2 * d)) := by
      nlinarith [abs_le.mp hperturb]
    have hneg :
        (C alpha * BigDescents.evenBinomPolyReal (2 * d) + h).eval
            (-(Real.tan (((k : ℝ) * Real.pi) / (2 * (d : ℝ)))) ^ 2) < 0 := by
      nlinarith [hcosPow]
    nlinarith

/-- A strict binomial coefficient bound gives the perturbed polynomial exact degree and
strictly positive coefficients throughout its support. -/
theorem evenBinomPolyReal_add_natDegree_and_coeff_pos
    {h : ℝ[X]} {d : ℕ} {alpha M : ℝ}
    (halpha : 0 < alpha) (hMalpha : M < alpha) (hdegree : h.natDegree ≤ d)
    (hcoeff : ∀ k ≤ d, |h.coeff k| ≤ M * d.choose k) :
    (C alpha * BigDescents.evenBinomPolyReal (2 * d) + h).natDegree = d ∧
      ∀ k ≤ d,
        0 < (C alpha * BigDescents.evenBinomPolyReal (2 * d) + h).coeff k := by
  let p := C alpha * BigDescents.evenBinomPolyReal (2 * d) + h
  have hpcoeff : ∀ k ≤ d, 0 < p.coeff k := by
    intro k hk
    have hchoose := choose_le_even_choose hk
    have hchoosePos := Nat.choose_pos hk
    have hbound := abs_le.mp (hcoeff k hk)
    simp only [p, coeff_add, coeff_C_mul, BigDescents.coeff_evenBinomPolyReal]
    have hchooseR :
        (d.choose k : ℝ) ≤ ((2 * d).choose (2 * k) : ℝ) := by
      exact_mod_cast hchoose
    have hchoosePosR : (0 : ℝ) < d.choose k := by
      exact_mod_cast hchoosePos
    have hmain :
        alpha * (d.choose k : ℝ) ≤ alpha * ((2 * d).choose (2 * k) : ℝ) :=
      mul_le_mul_of_nonneg_left hchooseR halpha.le
    have hgap : 0 < (alpha - M) * (d.choose k : ℝ) :=
      mul_pos (sub_pos.mpr hMalpha) hchoosePosR
    nlinarith
  have hpdegree_le : p.natDegree ≤ d := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · calc
        (C alpha * BigDescents.evenBinomPolyReal (2 * d)).natDegree ≤
            (C alpha).natDegree +
              (BigDescents.evenBinomPolyReal (2 * d)).natDegree := natDegree_mul_le
        _ ≤ d := by simp [BigDescents.evenBinomPolyReal_natDegree]
    · exact hdegree
  refine ⟨natDegree_eq_of_le_of_coeff_ne_zero hpdegree_le (hpcoeff d le_rfl).ne', hpcoeff⟩

/-- The points `-tan²(kπ/(2d))` strictly decrease as `k` runs from `0` to `d - 1`. -/
theorem neg_tan_sq_grid_strictAnti (d : ℕ) (hd : 0 < d) :
    StrictAnti fun k : Fin d =>
      -(Real.tan (((k : ℕ) : ℝ) * Real.pi / (2 * (d : ℝ)))) ^ 2 := by
  intro i j hij
  let ti := ((i : ℕ) : ℝ) * Real.pi / (2 * (d : ℝ))
  let tj := ((j : ℕ) : ℝ) * Real.pi / (2 * (d : ℝ))
  have hti0 : 0 ≤ ti := by
    dsimp [ti]
    positivity
  have htj0 : 0 ≤ tj := by
    dsimp [tj]
    positivity
  have htij : ti < tj := by
    dsimp [ti, tj]
    rw [div_lt_div_iff_of_pos_right (by positivity : 0 < 2 * (d : ℝ))]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) Real.pi_pos
  have htjlt : tj < Real.pi / 2 := by
    dsimp [tj]
    rw [div_lt_iff₀ (by positivity : 0 < 2 * (d : ℝ))]
    have hjd : ((j : ℕ) : ℝ) < d := by exact_mod_cast j.isLt
    nlinarith [Real.pi_pos]
  have htan := Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hti0 htjlt htij
  have htani :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hti0 (htij.le.trans htjlt.le)
  have htanj := Real.tan_nonneg_of_nonneg_of_le_pi_div_two htj0 htjlt.le
  dsimp [ti, tj] at *
  nlinarith

/-- A strict binomially bounded perturbation of the even-binomial polynomial splits and
has only simple real roots. -/
theorem evenBinomPolyReal_add_splits_and_hasSimpleRoots
    {h : ℝ[X]} {d : ℕ} {alpha M : ℝ}
    (hd : 0 < d) (halpha : 0 < alpha) (hMalpha : M < alpha)
    (hdegree : h.natDegree ≤ d)
    (hcoeff : ∀ k ≤ d, |h.coeff k| ≤ M * d.choose k) :
    let p := C alpha * BigDescents.evenBinomPolyReal (2 * d) + h
    p.Splits ∧ HasSimpleRoots p := by
  let p := C alpha * BigDescents.evenBinomPolyReal (2 * d) + h
  let grid : Fin d → ℝ := fun k =>
    -(Real.tan (((k : ℕ) : ℝ) * Real.pi / (2 * (d : ℝ)))) ^ 2
  let r : Fin d → ℝ := fun i =>
    grid ⟨d - 1 - i.1, by lia⟩
  have hpdata := evenBinomPolyReal_add_natDegree_and_coeff_pos
    halpha hMalpha hdegree hcoeff
  have hpdegree : p.natDegree = d := by simpa [p] using hpdata.1
  have hpcoeff : ∀ k ≤ d, 0 < p.coeff k := by simpa [p] using hpdata.2
  have hplead : 0 < p.leadingCoeff := by
    rw [leadingCoeff, hpdegree]
    exact hpcoeff d le_rfl
  have hp0 : p ≠ 0 := leadingCoeff_ne_zero.mp hplead.ne'
  have hgridAnti : StrictAnti grid := by
    simpa [grid] using neg_tan_sq_grid_strictAnti d hd
  have hr : ∀ i j, i < j → r i < r j := by
    intro i j hij
    apply hgridAnti
    simp
    lia
  have hgridSign (k : ℕ) (hk : k < d) :
      0 < (-1 : ℝ) ^ k * p.eval
        (-(Real.tan (((k : ℝ) * Real.pi) / (2 * (d : ℝ)))) ^ 2) := by
    simpa [p] using evenBinomPolyReal_add_grid_sign
      hd hdegree hMalpha hcoeff k hk
  have hfirst : (-1 : ℝ) ^ d * p.eval (r ⟨0, hd⟩) < 0 := by
    have hs := hgridSign (d - 1) (by lia)
    have hpow : (-1 : ℝ) ^ d = -((-1 : ℝ) ^ (d - 1)) := by
      calc
        (-1 : ℝ) ^ d = (-1 : ℝ) ^ (d - 1 + 1) := by congr 1; lia
        _ = -((-1 : ℝ) ^ (d - 1)) := by rw [pow_succ]; ring
    rw [hpow]
    simpa [r, grid] using neg_lt_zero.mpr hs
  have hsign : ∀ (k : ℕ) (hk : k + 1 < d),
      p.eval (r ⟨k, by lia⟩) * p.eval (r ⟨k + 1, hk⟩) < 0 := by
    intro k hk
    have ha := hgridSign (d - 1 - k) (by lia)
    have hb := hgridSign (d - 1 - (k + 1)) (by lia)
    have hodd : Odd ((d - 1 - k) + (d - 1 - (k + 1))) := ⟨d - k - 2, by lia⟩
    simpa [r, grid] using mul_neg_of_signed_pos ha hb hodd
  exact ⟨
    splits_of_sign_changes_with_left_endpoint
      hd hp0 hpdegree hplead r hr hfirst hsign,
    EulerBidiagonal.hasSimpleRoots_of_sign_changes_with_left_endpoint
      hd hp0 hpdegree hplead r hr hfirst hsign⟩

/-- A strict binomially bounded perturbation has positive leading coefficient and only
simple, strictly negative roots. -/
theorem evenBinomPolyReal_add_isNegativeSimple
    {h : ℝ[X]} {d : ℕ} {alpha M : ℝ}
    (hd : 0 < d) (halpha : 0 < alpha) (hMalpha : M < alpha)
    (hdegree : h.natDegree ≤ d)
    (hcoeff : ∀ k ≤ d, |h.coeff k| ≤ M * d.choose k) :
    IsNegativeSimple (C alpha * BigDescents.evenBinomPolyReal (2 * d) + h) := by
  let p := C alpha * BigDescents.evenBinomPolyReal (2 * d) + h
  have hpdata := evenBinomPolyReal_add_natDegree_and_coeff_pos
    halpha hMalpha hdegree hcoeff
  have hpdegree : p.natDegree = d := by simpa [p] using hpdata.1
  have hpcoeff : ∀ k ≤ d, 0 < p.coeff k := by simpa [p] using hpdata.2
  have hplead : 0 < p.leadingCoeff := by
    rw [leadingCoeff, hpdegree]
    exact hpcoeff d le_rfl
  have hp0 : p ≠ 0 := leadingCoeff_ne_zero.mp hplead.ne'
  have hsplitsSimple := evenBinomPolyReal_add_splits_and_hasSimpleRoots
    hd halpha hMalpha hdegree hcoeff
  have hnonneg : HasNonnegCoeffs p := by
    intro k
    by_cases hk : k ≤ d
    · exact (hpcoeff k hk).le
    · rw [coeff_eq_zero_of_natDegree_lt]
      rw [hpdegree]
      exact lt_of_not_ge hk
  have hroots : ∀ r ∈ p.roots, r < 0 := by
    intro r hr
    have hrle := roots_nonpos_of_hasNonnegCoeffs hnonneg r hr
    have hrne : r ≠ 0 := by
      intro hr0
      subst r
      have hroot := (mem_roots hp0).mp hr
      rw [Polynomial.IsRoot.def] at hroot
      have hpzero : 0 < p.eval 0 := by
        rw [← coeff_zero_eq_eval_zero]
        exact hpcoeff 0 (Nat.zero_le d)
      linarith
    exact lt_of_le_of_ne hrle hrne
  exact ⟨hp0, hsplitsSimple.1, hsplitsSimple.2, hplead, hroots⟩

/-- The roots of a strict perturbation are localized one per gap of the tangent grid,
with the final root to the left of the last grid point. -/
theorem evenBinomPolyReal_add_exists_roots_in_tangent_intervals
    {h : ℝ[X]} {d : ℕ} {alpha M : ℝ}
    (hd : 0 < d) (halpha : 0 < alpha) (hMalpha : M < alpha)
    (hdegree : h.natDegree ≤ d)
    (hcoeff : ∀ k ≤ d, |h.coeff k| ≤ M * d.choose k) :
    let p := C alpha * BigDescents.evenBinomPolyReal (2 * d) + h
    let grid := fun j : ℕ =>
      -(Real.tan ((j : ℝ) * Real.pi / (2 * (d : ℝ)))) ^ 2
    (∀ j, j + 1 < d → ∃ x, grid (j + 1) < x ∧ x < grid j ∧ p.IsRoot x) ∧
      ∃ x, x < grid (d - 1) ∧ p.IsRoot x := by
  let p := C alpha * BigDescents.evenBinomPolyReal (2 * d) + h
  let grid := fun j : ℕ =>
    -(Real.tan ((j : ℝ) * Real.pi / (2 * (d : ℝ)))) ^ 2
  have hpdata := evenBinomPolyReal_add_natDegree_and_coeff_pos
    halpha hMalpha hdegree hcoeff
  have hpdegree : p.natDegree = d := by simpa [p] using hpdata.1
  have hpcoeff : ∀ k ≤ d, 0 < p.coeff k := by simpa [p] using hpdata.2
  have hplead : 0 < p.leadingCoeff := by
    rw [leadingCoeff, hpdegree]
    exact hpcoeff d le_rfl
  have hgridSign (k : ℕ) (hk : k < d) :
      0 < (-1 : ℝ) ^ k * p.eval (grid k) := by
    simpa [p, grid] using evenBinomPolyReal_add_grid_sign
      hd hdegree hMalpha hcoeff k hk
  have hgridAnti := neg_tan_sq_grid_strictAnti d hd
  constructor
  · intro j hj
    have hleft : grid (j + 1) < grid j := by
      have hlt := hgridAnti (show (⟨j, by lia⟩ : Fin d) < ⟨j + 1, hj⟩ by simp)
      simpa [grid] using hlt
    have hprod : p.eval (grid (j + 1)) * p.eval (grid j) < 0 := by
      apply mul_neg_of_signed_pos (hgridSign (j + 1) hj) (hgridSign j (by lia))
      exact ⟨j, by lia⟩
    exact MaWang.exists_isRoot_between_of_eval_mul_neg hleft hprod
  · obtain ⟨R, hRleft, hRsign⟩ :=
      exists_left_endpoint_sign hpdegree hplead (grid (d - 1))
    have hlast := hgridSign (d - 1) (by lia)
    have hprod : p.eval R * p.eval (grid (d - 1)) < 0 := by
      apply mul_neg_of_signed_pos hRsign hlast
      exact ⟨d - 1, by lia⟩
    obtain ⟨x, _, hxright, hxroot⟩ :=
      MaWang.exists_isRoot_between_of_eval_mul_neg hRleft hprod
    exact ⟨x, hxright, hxroot⟩

/-- At the closed coefficient bound, every perturbation is a Pólya-frequency
polynomial; degree drops and repeated roots are allowed. -/
theorem evenBinomPolyReal_add_isPFPolynomial_of_coeff_bound
    {h : ℝ[X]} {d : ℕ} {alpha M : ℝ}
    (hd : 0 < d) (halpha : 0 < alpha) (hM : 0 ≤ M) (hMalpha : M ≤ alpha)
    (hdegree : h.natDegree ≤ d)
    (hcoeff : ∀ k ≤ d, |h.coeff k| ≤ M * d.choose k) :
    IsPFPolynomial (C alpha * BigDescents.evenBinomPolyReal (2 * d) + h) := by
  let lam : ℕ → ℝ := fun n => (n : ℝ) / (n + 1)
  let p : ℕ → ℝ[X] := fun n =>
    C alpha * BigDescents.evenBinomPolyReal (2 * d) + C (lam n) * h
  have hlam_nonneg (n : ℕ) : 0 ≤ lam n := by
    dsimp [lam]
    positivity
  have hlam_lt_one (n : ℕ) : lam n < 1 := by
    dsimp [lam]
    rw [div_lt_one (by positivity : (0 : ℝ) < n + 1)]
    norm_num
  have hstrict (n : ℕ) : lam n * M < alpha := by
    by_cases hM0 : M = 0
    · simp [hM0, halpha]
    · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
      exact (mul_lt_of_lt_one_left hMpos (hlam_lt_one n)).trans_le hMalpha
  have hp (n : ℕ) : IsPFPolynomial (p n) := by
    have hscaledDegree : (C (lam n) * h).natDegree ≤ d := by
      exact (natDegree_mul_le.trans (by simpa using hdegree))
    have hscaledCoeff : ∀ k ≤ d,
        |(C (lam n) * h).coeff k| ≤ (lam n * M) * d.choose k := by
      intro k hk
      rw [coeff_C_mul, abs_mul, abs_of_nonneg (hlam_nonneg n)]
      calc
        lam n * |h.coeff k| ≤ lam n * (M * d.choose k) :=
          mul_le_mul_of_nonneg_left (hcoeff k hk) (hlam_nonneg n)
        _ = (lam n * M) * d.choose k := by ring
    apply IsNegativeSimple.isPFPolynomial
    simpa [p] using evenBinomPolyReal_add_isNegativeSimple
      hd halpha (hstrict n) hscaledDegree hscaledCoeff
  apply IsPFPolynomial.of_coeff_tendsto hp
  intro i
  have hlam : Tendsto lam atTop (nhds 1) := by
    simpa [lam] using tendsto_natCast_div_add_atTop (1 : ℝ)
  have hmain :
      Tendsto (fun _ : ℕ => alpha * (BigDescents.evenBinomPolyReal (2 * d)).coeff i)
        atTop
        (nhds (alpha * (BigDescents.evenBinomPolyReal (2 * d)).coeff i)) :=
    tendsto_const_nhds
  have hlim := hmain.add (hlam.mul_const (h.coeff i))
  simpa [p, coeff_add, coeff_C_mul] using hlim

/-- For positive degree, the closed coefficient bound guarantees every perturbation is
Pólya-frequency exactly when `M ≤ alpha`. -/
theorem all_evenBinomPolyReal_add_isPFPolynomial_iff_le
    {d : ℕ} {alpha M : ℝ} (hd : 0 < d) (halpha : 0 < alpha) (hM : 0 ≤ M) :
    (∀ h : ℝ[X], h.natDegree ≤ d →
      (∀ k ≤ d, |h.coeff k| ≤ M * d.choose k) →
      IsPFPolynomial (C alpha * BigDescents.evenBinomPolyReal (2 * d) + h)) ↔
      M ≤ alpha := by
  constructor
  · intro hall
    have hdegree : (C (-M) : ℝ[X]).natDegree ≤ d := by
      simp
    have hcoeff : ∀ k ≤ d, |(C (-M) : ℝ[X]).coeff k| ≤ M * d.choose k := by
      intro k _
      rcases k with _ | k
      · simp [abs_of_nonneg hM]
      · simp only [map_neg, coeff_neg, coeff_C_succ, neg_zero, abs_zero]
        exact mul_nonneg hM (Nat.cast_nonneg _)
    have hnonneg := (hall (C (-M)) hdegree hcoeff).hasNonnegCoeffs 0
    simpa [BigDescents.coeff_evenBinomPolyReal] using hnonneg
  · intro hMalpha h hdegree hcoeff
    exact evenBinomPolyReal_add_isPFPolynomial_of_coeff_bound
      hd halpha hM hMalpha hdegree hcoeff

/-- In degree two, the alternating binomial perturbation ceases to split as soon as
`M > alpha`; its discriminant is `32 * alpha * (alpha - M)`. -/
theorem evenBinomPolyReal_four_add_one_sub_X_sq_not_splits
    {alpha M : ℝ} (halpha : 0 < alpha) (hMalpha : alpha < M) :
    ¬(C alpha * BigDescents.evenBinomPolyReal 4 + C M * (1 - X) ^ 2).Splits := by
  have hpoly :
      C alpha * BigDescents.evenBinomPolyReal 4 + C M * (1 - X) ^ 2 =
        C (alpha + M) * X ^ 2 + C (6 * alpha - 2 * M) * X + C (alpha + M) := by
    have hchoose : Nat.choose 4 2 = 6 := by decide
    norm_num [BigDescents.evenBinomPolyReal, Finset.sum_range_succ]
    rw [hchoose]
    simp only [Polynomial.C_ofNat]
    ring
  rw [hpoly]
  apply quadraticPoly_not_splits_of_discrim_neg
  · exact ne_of_gt (by linarith)
  · rw [discrim]
    nlinarith

end RealRooted
