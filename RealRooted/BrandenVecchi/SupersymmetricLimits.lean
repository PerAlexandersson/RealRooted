import RealRooted.BrandenVecchi.SupersymmetricCoefficients
import RealRooted.Mathlib.Analysis.SpecialFunctions.Choose
import RealRooted.PFPolynomial.Closure
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Coefficient limits of supersymmetric PF symbols

This file constructs the Aissen--Schoenberg--Whitney--Edrei symbol by
convergent products in the coefficientwise topology on real formal power
series. Finite prefixes and the binomial approximation to the exponential are
kept explicit.
-/

open BigOperators Filter Topology
open scoped PowerSeries.WithPiTopology

namespace RealRooted.BrandenVecchi

noncomputable section

private theorem prod_linearDeviation (c : ℕ → ℝ) (s : Finset ℕ) :
    (∏ i ∈ s, PowerSeries.C (c i) * PowerSeries.X) =
      PowerSeries.C (∏ i ∈ s, c i) * PowerSeries.X ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Finset.card_insert_of_notMem hi, ih, pow_succ']
      simp only [map_mul]
      ring

private theorem summable_prod_linearDeviation
    (c : ℕ → ℝ) (hc : Summable fun i => |c i|) :
    Summable (fun s : Finset ℕ =>
      ∏ i ∈ s, PowerSeries.C (c i) * PowerSeries.X) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  have hmajorant : Summable (fun s : Finset ℕ => ∏ i ∈ s, |c i|) :=
    summable_finsetProd_of_summable_nonneg (fun _ => abs_nonneg _) hc
  refine hmajorant.of_norm_bounded (fun s => ?_)
  rw [prod_linearDeviation, PowerSeries.coeff_C_mul_X_pow]
  split
  · rw [Real.norm_eq_abs, Finset.abs_prod]
  · simp only [norm_zero]
    exact Finset.prod_nonneg fun i _ => abs_nonneg (c i)

/-- The coefficientwise convergent product of the linear factors
`1 + c_i X`. -/
def linearFactorProduct (c : ℕ → ℝ) : PowerSeries ℝ :=
  tprod fun i : ℕ => 1 + PowerSeries.C (c i) * PowerSeries.X

/-- Absolute summability of the parameters makes the product of linear
power-series factors convergent. -/
theorem linearFactorProduct_multipliable
    (c : ℕ → ℝ) (hc : Summable fun i => |c i|) :
    Multipliable fun i =>
      1 + PowerSeries.C (c i) * PowerSeries.X := by
  apply multipliable_one_add_of_summable_prod
  exact summable_prod_linearDeviation c hc

/-- Products over initial parameter segments converge coefficientwise to the
infinite linear-factor product. -/
theorem tendsto_linearFactorPrefix
    (c : ℕ → ℝ) (hc : Summable fun i => |c i|) :
    Tendsto
      (fun N => ∏ i ∈ Finset.range N,
        (1 + PowerSeries.C (c i) * PowerSeries.X))
      atTop (𝓝 (linearFactorProduct c)) := by
  let h := linearFactorProduct_multipliable c hc
  apply (h.hasProd_iff_tendsto_nat).mp
  simpa [linearFactorProduct] using h.hasProd

/-- The convergent linear-factor product has constant coefficient one. -/
@[simp]
theorem linearFactorProduct_constantCoeff
    (c : ℕ → ℝ) (hc : Summable fun i => |c i|) :
    PowerSeries.constantCoeff (linearFactorProduct c) = 1 := by
  have hlimit :=
    (PowerSeries.WithPiTopology.continuous_constantCoeff ℝ).continuousAt.tendsto.comp
      (tendsto_linearFactorPrefix c hc)
  have heq : (fun N => PowerSeries.constantCoeff
      (∏ i ∈ Finset.range N,
        (1 + PowerSeries.C (c i) * PowerSeries.X))) = fun _ => 1 := by
    funext N
    simp
  change Tendsto (fun N => PowerSeries.constantCoeff
    (∏ i ∈ Finset.range N,
      (1 + PowerSeries.C (c i) * PowerSeries.X))) atTop
        (𝓝 (PowerSeries.constantCoeff (linearFactorProduct c))) at hlimit
  have hone : Tendsto (fun N => PowerSeries.constantCoeff
      (∏ i ∈ Finset.range N,
        (1 + PowerSeries.C (c i) * PowerSeries.X))) atTop (𝓝 1) := by
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlimit hone

/-- Inversion is coefficientwise continuous along families whose constant
coefficient is fixed at one. -/
theorem tendsto_coeff_inv_of_constantCoeff_one
    {ι : Type*} {l : Filter ι}
    (f : ι → PowerSeries ℝ) (f₀ : PowerSeries ℝ)
    (hf : ∀ a, PowerSeries.constantCoeff (f a) = 1)
    (hf₀ : PowerSeries.constantCoeff f₀ = 1)
    (hcoeff : ∀ d, Tendsto (fun a => PowerSeries.coeff d (f a)) l
      (𝓝 (PowerSeries.coeff d f₀))) :
    ∀ d, Tendsto (fun a => PowerSeries.coeff d (f a)⁻¹) l
      (𝓝 (PowerSeries.coeff d f₀⁻¹)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      cases d with
      | zero =>
          have hleft : (fun a => PowerSeries.coeff 0 (f a)⁻¹) = fun _ => 1 := by
            funext a
            simp [PowerSeries.coeff_inv, hf a]
          have hright : PowerSeries.coeff 0 f₀⁻¹ = 1 := by
            simp [PowerSeries.coeff_inv, hf₀]
          rw [hleft, hright]
          exact tendsto_const_nhds
      | succ d =>
          have hleft (a : ι) : PowerSeries.coeff (d + 1) (f a)⁻¹ =
              -1 * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (d + 1),
                if x.2 < d + 1 then
                  PowerSeries.coeff x.1 (f a) *
                    PowerSeries.coeff x.2 (f a)⁻¹
                else 0 := by
            rw [PowerSeries.coeff_inv, ite_eq_right (Nat.succ_ne_zero d), hf a]
            norm_num
          have hright : PowerSeries.coeff (d + 1) f₀⁻¹ =
              -1 * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (d + 1),
                if x.2 < d + 1 then
                  PowerSeries.coeff x.1 f₀ * PowerSeries.coeff x.2 f₀⁻¹
                else 0 := by
            rw [PowerSeries.coeff_inv, ite_eq_right (Nat.succ_ne_zero d), hf₀]
            norm_num
          simp_rw [hleft, hright]
          refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun x _ => ?_)
          by_cases hx : x.2 < d + 1
          · simp only [ite_eq_left hx]
            exact (hcoeff x.1).mul (ih x.2 hx)
          · simp only [ite_eq_right hx]
            exact tendsto_const_nhds

/-- The `N`-factor binomial approximation to `exp (gamma X)`. -/
def exponentialTruncation (gamma : ℝ) (N : ℕ) : PowerSeries ℝ :=
  (1 + PowerSeries.C (gamma * (N : ℝ)⁻¹) * PowerSeries.X) ^ N

/-- Exact coefficients of the binomial exponential approximation. -/
theorem coeff_exponentialTruncation (gamma : ℝ) (N k : ℕ) :
    PowerSeries.coeff k (exponentialTruncation gamma N) =
      (N.choose k : ℝ) * (gamma * (N : ℝ)⁻¹) ^ k := by
  let a := gamma * (N : ℝ)⁻¹
  have hseries : exponentialTruncation gamma N =
      (((1 + Polynomial.C a * Polynomial.X : Polynomial ℝ) ^ N : Polynomial ℝ) :
        PowerSeries ℝ) := by
    simp [exponentialTruncation, a]
  rw [hseries, Polynomial.coeff_coe]
  calc
    ((1 + Polynomial.C a * Polynomial.X : Polynomial ℝ) ^ N).coeff k =
        (((1 + Polynomial.X : Polynomial ℝ) ^ N).comp
          (Polynomial.C a * Polynomial.X)).coeff k := by
      congr 2
      simp
    _ = ((1 + Polynomial.X : Polynomial ℝ) ^ N).coeff k * a ^ k := by
      rw [Polynomial.comp_C_mul_X_coeff]
    _ = (N.choose k : ℝ) * (gamma * (N : ℝ)⁻¹) ^ k := by
      rw [Polynomial.coeff_one_add_X_pow]

/-- Each fixed coefficient of the binomial approximation converges to the
corresponding coefficient of `exp (gamma X)`. -/
theorem tendsto_coeff_exponentialTruncation (gamma : ℝ) (k : ℕ) :
    Tendsto (fun N => PowerSeries.coeff k (exponentialTruncation gamma N))
      atTop
      (𝓝 (PowerSeries.coeff k
        (PowerSeries.rescale gamma (PowerSeries.exp ℝ)))) := by
  rw [show PowerSeries.coeff k
      (PowerSeries.rescale gamma (PowerSeries.exp ℝ)) =
      gamma ^ k / k.factorial by simp [div_eq_mul_inv]]
  simp_rw [coeff_exponentialTruncation, mul_pow]
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (tendsto_choose_mul_inv_pow_atTop k).mul_const (gamma ^ k)

/-- The binomial approximations converge in the coefficientwise topology. -/
theorem tendsto_exponentialTruncation (gamma : ℝ) :
    Tendsto (exponentialTruncation gamma) atTop
      (𝓝 (PowerSeries.rescale gamma (PowerSeries.exp ℝ))) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  exact tendsto_coeff_exponentialTruncation gamma

/-- The first `N` entries of a parameter sequence, in their original order. -/
def parameterPrefix (c : ℕ → ℝ) (N : ℕ) : List ℝ :=
  List.ofFn fun i : Fin N => c i

/-- Finite numerator product over the first `N` parameters. -/
def supersymmetricNumeratorPrefix (alpha : ℕ → ℝ) (N : ℕ) :
    PowerSeries ℝ :=
  ((parameterPrefix alpha N).map supersymmetricNumeratorFactor).prod

/-- Finite reciprocal-denominator product over the first `N` parameters. -/
def supersymmetricDenominatorPrefix (beta : ℕ → ℝ) (N : ℕ) :
    PowerSeries ℝ :=
  ((parameterPrefix beta N).map supersymmetricDenominatorFactor).prod

private theorem numeratorPrefix_eq_prod_range (alpha : ℕ → ℝ) (N : ℕ) :
    supersymmetricNumeratorPrefix alpha N =
      ∏ i ∈ Finset.range N,
        (1 + PowerSeries.C (alpha i) * PowerSeries.X) := by
  rw [supersymmetricNumeratorPrefix, parameterPrefix, List.map_ofFn,
    List.prod_ofFn, Finset.prod_range]
  apply Finset.prod_congr rfl
  intro i _
  simp [supersymmetricNumeratorFactor]

/-- Numerator prefixes converge coefficientwise to the infinite numerator
product. -/
theorem tendsto_supersymmetricNumeratorPrefix
    (alpha : ℕ → ℝ) (halpha : Summable fun i => |alpha i|) :
    Tendsto (supersymmetricNumeratorPrefix alpha) atTop
      (𝓝 (linearFactorProduct alpha)) := by
  rw [show supersymmetricNumeratorPrefix alpha = fun N =>
      ∏ i ∈ Finset.range N,
        (1 + PowerSeries.C (alpha i) * PowerSeries.X) by
    funext N
    exact numeratorPrefix_eq_prod_range alpha N]
  exact tendsto_linearFactorPrefix alpha halpha

private theorem denominatorPrefix_mul_linearPrefix
    (beta : ℕ → ℝ) (N : ℕ) :
    supersymmetricDenominatorPrefix beta N *
        (∏ i ∈ Finset.range N,
          (1 + PowerSeries.C (-beta i) * PowerSeries.X)) = 1 := by
  let ys := parameterPrefix beta N
  have h := finiteSupersymmetricSeries_mul_denominators ([] : List ℝ) ys
  have hlinear :
      (ys.map fun y => 1 - PowerSeries.C y * PowerSeries.X).prod =
        ∏ i ∈ Finset.range N,
          (1 + PowerSeries.C (-beta i) * PowerSeries.X) := by
    dsimp [ys, parameterPrefix]
    rw [List.map_ofFn, List.prod_ofFn, Finset.prod_range]
    apply Finset.prod_congr rfl
    intro i _
    simp
    ring
  simpa [finiteSupersymmetricSeries, supersymmetricDenominatorPrefix,
    ys, hlinear] using h

/-- The finite reciprocal-denominator product is the inverse of the
corresponding finite linear product. -/
theorem supersymmetricDenominatorPrefix_eq_inv
    (beta : ℕ → ℝ) (N : ℕ) :
    supersymmetricDenominatorPrefix beta N =
      (∏ i ∈ Finset.range N,
        (1 + PowerSeries.C (-beta i) * PowerSeries.X))⁻¹ := by
  let q : PowerSeries ℝ := ∏ i ∈ Finset.range N,
    (1 + PowerSeries.C (-beta i) * PowerSeries.X)
  have hq : PowerSeries.constantCoeff q = 1 := by
    simp [q]
  calc
    supersymmetricDenominatorPrefix beta N =
        supersymmetricDenominatorPrefix beta N * 1 := by rw [mul_one]
    _ = supersymmetricDenominatorPrefix beta N * (q * q⁻¹) := by
      rw [PowerSeries.mul_inv_cancel q (by simp [hq])]
    _ = (supersymmetricDenominatorPrefix beta N * q) * q⁻¹ := by
      rw [mul_assoc]
    _ = q⁻¹ := by
      rw [denominatorPrefix_mul_linearPrefix, one_mul]

/-- Denominator prefixes converge coefficientwise to the inverse infinite
linear-factor product. -/
theorem tendsto_supersymmetricDenominatorPrefix
    (beta : ℕ → ℝ) (hbeta : Summable fun i => |beta i|) :
    Tendsto (supersymmetricDenominatorPrefix beta) atTop
      (𝓝 (linearFactorProduct (fun i => -beta i))⁻¹) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  have hneg : Summable fun i => |-beta i| := by simpa using hbeta
  have hprefix := tendsto_linearFactorPrefix (fun i => -beta i) hneg
  have hcoeff : ∀ e, Tendsto
      (fun N => PowerSeries.coeff e
        (∏ i ∈ Finset.range N,
          (1 + PowerSeries.C (-beta i) * PowerSeries.X))) atTop
      (𝓝 (PowerSeries.coeff e (linearFactorProduct fun i => -beta i))) := by
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at hprefix
    exact hprefix
  have hinv := tendsto_coeff_inv_of_constantCoeff_one
    (fun N => ∏ i ∈ Finset.range N,
      (1 + PowerSeries.C (-beta i) * PowerSeries.X))
    (linearFactorProduct fun i => -beta i)
    (fun N => by simp)
    (linearFactorProduct_constantCoeff (fun i => -beta i) hneg)
    hcoeff d
  simpa only [supersymmetricDenominatorPrefix_eq_inv] using hinv

/-- The infinite Aissen--Schoenberg--Whitney--Edrei symbol, with the numerator
and denominator products interpreted through the convergent linear-factor
products above. -/
def aswEdreiSymbol (gamma : ℝ) (alpha beta : ℕ → ℝ) : PowerSeries ℝ :=
  PowerSeries.rescale gamma (PowerSeries.exp ℝ) * linearFactorProduct alpha *
    (linearFactorProduct fun i => -beta i)⁻¹

/-- Coefficients of the infinite ASW--Edrei symbol. -/
def aswEdreiCoeff (gamma : ℝ) (alpha beta : ℕ → ℝ) (d : ℕ) : ℝ :=
  PowerSeries.coeff d (aswEdreiSymbol gamma alpha beta)

/-- A single finite PF approximation: `N` equal numerator factors approximate
the exponential, followed by the first `N` numerator and denominator
parameters. -/
def aswEdreiTruncationSeries
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (N : ℕ) : PowerSeries ℝ :=
  finiteSupersymmetricSeries
    (List.replicate N (gamma * (N : ℝ)⁻¹) ++ parameterPrefix alpha N)
    (parameterPrefix beta N)

/-- Coefficients of the finite ASW--Edrei approximation. -/
def aswEdreiTruncationCoeff
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (N d : ℕ) : ℝ :=
  PowerSeries.coeff d (aswEdreiTruncationSeries gamma alpha beta N)

/-- The finite approximation separates into its exponential, numerator-prefix,
and reciprocal-denominator-prefix factors. -/
theorem aswEdreiTruncationSeries_eq
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (N : ℕ) :
    aswEdreiTruncationSeries gamma alpha beta N =
      exponentialTruncation gamma N *
        supersymmetricNumeratorPrefix alpha N *
          supersymmetricDenominatorPrefix beta N := by
  simp [aswEdreiTruncationSeries, finiteSupersymmetricSeries,
    exponentialTruncation, supersymmetricNumeratorPrefix,
    supersymmetricDenominatorPrefix, supersymmetricNumeratorFactor]

private theorem summable_parameters_of_sum
    {alpha beta : ℕ → ℝ} (halpha : ∀ i, 0 ≤ alpha i)
    (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) :
    Summable (fun i => |alpha i|) ∧ Summable (fun i => |beta i|) := by
  have ha : Summable alpha := hsum.of_nonneg_of_le halpha
    (fun i => le_add_of_nonneg_right (hbeta i))
  have hb : Summable beta := hsum.of_nonneg_of_le hbeta
    (fun i => le_add_of_nonneg_left (halpha i))
  simpa [abs_of_nonneg, halpha, hbeta] using And.intro ha hb

/-- The stated nonnegative Edrei summability hypothesis gives convergence of
the numerator and reciprocal-denominator prefixes separately. -/
theorem tendsto_supersymmetricPrefixes_of_summable
    {alpha beta : ℕ → ℝ} (halpha : ∀ i, 0 ≤ alpha i)
    (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) :
    Tendsto (supersymmetricNumeratorPrefix alpha) atTop
        (𝓝 (linearFactorProduct alpha)) ∧
      Tendsto (supersymmetricDenominatorPrefix beta) atTop
        (𝓝 (linearFactorProduct (fun i => -beta i))⁻¹) := by
  obtain ⟨ha, hb⟩ := summable_parameters_of_sum halpha hbeta hsum
  exact ⟨tendsto_supersymmetricNumeratorPrefix alpha ha,
    tendsto_supersymmetricDenominatorPrefix beta hb⟩

/-- Every fixed coefficient of the numerator and reciprocal-denominator
prefixes converges under the stated Edrei hypothesis. -/
theorem tendsto_coeff_supersymmetricPrefixes_of_summable
    {alpha beta : ℕ → ℝ} (halpha : ∀ i, 0 ≤ alpha i)
    (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (d : ℕ) :
    Tendsto
        (fun N => PowerSeries.coeff d (supersymmetricNumeratorPrefix alpha N))
        atTop (𝓝 (PowerSeries.coeff d (linearFactorProduct alpha))) ∧
      Tendsto
        (fun N => PowerSeries.coeff d (supersymmetricDenominatorPrefix beta N))
        atTop
        (𝓝 (PowerSeries.coeff d
          (linearFactorProduct (fun i => -beta i))⁻¹)) := by
  obtain ⟨ha, hb⟩ :=
    tendsto_supersymmetricPrefixes_of_summable halpha hbeta hsum
  exact ⟨
    (PowerSeries.WithPiTopology.continuous_coeff ℝ d).continuousAt.tendsto.comp ha,
    (PowerSeries.WithPiTopology.continuous_coeff ℝ d).continuousAt.tendsto.comp hb⟩

/-- Under the Edrei summability hypothesis, the finite PF approximations
converge to the infinite symbol in the coefficientwise power-series topology. -/
theorem tendsto_aswEdreiTruncationSeries
    {gamma : ℝ} {alpha beta : ℕ → ℝ}
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) :
    Tendsto (aswEdreiTruncationSeries gamma alpha beta) atTop
      (𝓝 (aswEdreiSymbol gamma alpha beta)) := by
  obtain ⟨ha, hb⟩ := summable_parameters_of_sum halpha hbeta hsum
  rw [show aswEdreiTruncationSeries gamma alpha beta = fun N =>
      exponentialTruncation gamma N *
        supersymmetricNumeratorPrefix alpha N *
          supersymmetricDenominatorPrefix beta N by
    funext N
    exact aswEdreiTruncationSeries_eq gamma alpha beta N]
  exact ((tendsto_exponentialTruncation gamma).mul
    (tendsto_supersymmetricNumeratorPrefix alpha ha)).mul
      (tendsto_supersymmetricDenominatorPrefix beta hb)

/-- Every fixed coefficient of the finite approximation converges to the
corresponding coefficient of the infinite symbol. -/
theorem tendsto_aswEdreiTruncationCoeff
    {gamma : ℝ} {alpha beta : ℕ → ℝ}
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (d : ℕ) :
    Tendsto (fun N => aswEdreiTruncationCoeff gamma alpha beta N d) atTop
      (𝓝 (aswEdreiCoeff gamma alpha beta d)) := by
  exact (PowerSeries.WithPiTopology.continuous_coeff ℝ d).continuousAt.tendsto.comp
    (tendsto_aswEdreiTruncationSeries halpha hbeta hsum)

/-- Each finite approximation has coefficient zero equal to one. -/
@[simp]
theorem aswEdreiTruncationCoeff_zero
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (N : ℕ) :
    aswEdreiTruncationCoeff gamma alpha beta N 0 = 1 := by
  exact finiteSupersymmetricCoeff_zero
    (List.replicate N (gamma * (N : ℝ)⁻¹) ++ parameterPrefix alpha N)
    (parameterPrefix beta N)

/-- Nonnegative parameters make every finite approximation a
Pólya-frequency sequence. -/
theorem aswEdreiTruncationCoeff_isPolyaFreqSeq
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i) (N : ℕ) :
    IsPolyaFreqSeq (aswEdreiTruncationCoeff gamma alpha beta N) := by
  apply finiteSupersymmetricCoeff_isPolyaFreqSeq
  · intro x hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩ | hx
    · exact mul_nonneg hgamma (inv_nonneg.mpr (Nat.cast_nonneg N))
    · simpa [parameterPrefix] using
        (List.forall_mem_ofFn_iff.mpr fun i : Fin N => halpha i) x hx
  · simpa [parameterPrefix] using
      (List.forall_mem_ofFn_iff.mpr fun i : Fin N => hbeta i)

/-- The infinite ASW--Edrei coefficient sequence is Pólya-frequency, obtained
as the checked coefficientwise limit of the finite PF approximations. -/
theorem aswEdreiCoeff_isPolyaFreqSeq
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) :
    IsPolyaFreqSeq (aswEdreiCoeff gamma alpha beta) := by
  apply IsPolyaFreqSeq.of_tendsto
  · exact aswEdreiTruncationCoeff_isPolyaFreqSeq hgamma halpha hbeta
  · exact tendsto_aswEdreiTruncationCoeff halpha hbeta hsum

/-- The infinite symbol has constant coefficient one. -/
@[simp]
theorem aswEdreiCoeff_zero
    {gamma : ℝ} {alpha beta : ℕ → ℝ}
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) :
    aswEdreiCoeff gamma alpha beta 0 = 1 := by
  exact tendsto_nhds_unique
    (tendsto_aswEdreiTruncationCoeff halpha hbeta hsum 0)
    (by
      simp only [aswEdreiTruncationCoeff_zero]
      exact tendsto_const_nhds)

/-- Coefficients of the infinite symbol are nonnegative. -/
theorem aswEdreiCoeff_nonneg
    {gamma : ℝ} {alpha beta : ℕ → ℝ} (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (d : ℕ) :
    0 ≤ aswEdreiCoeff gamma alpha beta d :=
  (aswEdreiCoeff_isPolyaFreqSeq hgamma halpha hbeta hsum).nonneg d

end

end RealRooted.BrandenVecchi
