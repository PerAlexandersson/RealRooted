import RealRooted.BrandenVecchi.SupersymmetricLimits

/-!
# Edrei--Thoma, the easy direction

The coefficient sequence of a canonical product
`C x ^ m e ^ (γ x) ∏ᵢ (1 + αᵢ x) / ∏ᵢ (1 - βᵢ x)`
with `C, γ, αᵢ, βᵢ ≥ 0` and `∑ᵢ (αᵢ + βᵢ) < ∞` is a Pólya-frequency sequence.

The statement is over formal power series `PowerSeries ℝ` with the coefficientwise
(product) topology.  The numerator product `∏' i, (1 + αᵢ X)` is a `tprod` in that topology, which
converges by `RealRooted.BrandenVecchi.linearFactorProduct_multipliable`.  The denominator is the
formal inverse `(∏' i, (1 - βᵢ X))⁻¹`; by
`tendsto_canonicalPrefixProduct` it is the coefficientwise limit of the finite products of the
geometric series `1 / (1 - βᵢ X) = ∑ₖ βᵢ ^ k X ^ k`.

The proof follows the route:

1. the factors `1 + a X`, `1 / (1 - b X)` and `exp (γ X)` are Pólya-frequency series
   (`isPolyaFreqSeries_one_add_C_mul_X`, `isPolyaFreqSeries_geometricFactor`,
   `isPolyaFreqSeries_rescale_exp`);
2. Pólya-frequency series are closed under products (`IsPolyaFreqSeries.mul`, Cauchy convolution);
3. they are closed under coefficientwise limits (`IsPolyaFreqSeries.of_tendsto`);
4. the infinite products converge coefficientwise (`tendsto_canonicalPrefixProduct`), whence
   `isPolyaFreqSeries_canonicalProduct`.

Only the easy direction is proved here; the converse (every Pólya-frequency sequence has this
form) is not part of this file.
-/

open Filter Topology
open scoped PowerSeries.WithPiTopology

noncomputable section

namespace RealRooted.EdreiThoma

open RealRooted.BrandenVecchi

/-- A formal power series is a Pólya-frequency series if its coefficient sequence is a
Pólya-frequency sequence, i.e. its lower-triangular Toeplitz matrix is totally nonnegative. -/
def IsPolyaFreqSeries (F : PowerSeries ℝ) : Prop :=
  IsPolyaFreqSeq fun n => PowerSeries.coeff n F

namespace IsPolyaFreqSeries

/-- The constant series `1` is a Pólya-frequency series. -/
protected theorem one : IsPolyaFreqSeries 1 := by
  unfold IsPolyaFreqSeries
  convert IsPolyaFreqSeq.one using 1
  funext n
  simp [Polynomial.coeff_one, PowerSeries.coeff_one]

/-- Pólya-frequency series are closed under multiplication (Cauchy convolution of coefficient
sequences). -/
protected theorem mul {F G : PowerSeries ℝ} (hF : IsPolyaFreqSeries F)
    (hG : IsPolyaFreqSeries G) : IsPolyaFreqSeries (F * G) := by
  unfold IsPolyaFreqSeries at hF hG ⊢
  have h := IsPolyaFreqSeq.natCauchyConvolution hF hG
  have h2 : (fun n => PowerSeries.coeff n (F * G)) =
      natCauchyConvolution (fun k => PowerSeries.coeff k F) (fun k => PowerSeries.coeff k G) :=
    funext (coeff_mul_eq_natCauchyConvolution F G)
  rw [h2]
  exact h

/-- Natural powers of a Pólya-frequency series are Pólya-frequency. -/
protected theorem pow {F : PowerSeries ℝ} (hF : IsPolyaFreqSeries F) (n : ℕ) :
    IsPolyaFreqSeries (F ^ n) := by
  induction n with
  | zero => simpa using IsPolyaFreqSeries.one
  | succ n ih => rw [pow_succ]; exact ih.mul hF

/-- Finite products of Pólya-frequency series are Pólya-frequency. -/
protected theorem prod {ι : Type*} (s : Finset ι) {f : ι → PowerSeries ℝ}
    (hf : ∀ i ∈ s, IsPolyaFreqSeries (f i)) : IsPolyaFreqSeries (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPolyaFreqSeries.one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A nonnegative scalar multiple of a Pólya-frequency series is Pólya-frequency. -/
protected theorem C_mul {c : ℝ} (hc : 0 ≤ c) {F : PowerSeries ℝ} (hF : IsPolyaFreqSeries F) :
    IsPolyaFreqSeries (PowerSeries.C c * F) := by
  unfold IsPolyaFreqSeries at hF ⊢
  have h : toeplitz (fun n => PowerSeries.coeff n (PowerSeries.C c * F)) =
      c • toeplitz fun n => PowerSeries.coeff n F := by
    ext i j
    by_cases hji : j ≤ i <;> simp [toeplitz_apply, hji]
  rw [IsPolyaFreqSeq, h]
  exact Matrix.IsTotallyNonneg.smul hF hc

/-- Multiplying a Pólya-frequency series by `X ^ m` (a zero prefix) preserves the property. -/
protected theorem X_pow_mul {F : PowerSeries ℝ} (hF : IsPolyaFreqSeries F) (m : ℕ) :
    IsPolyaFreqSeries (PowerSeries.X ^ m * F) := by
  have h := IsPolyaFreqSeq.prefix_zeros hF m
  unfold IsPolyaFreqSeries
  convert h using 1
  funext n
  rw [PowerSeries.coeff_X_pow_mul']

/-- Pólya-frequency series are closed under coefficientwise limits of sequences. -/
theorem of_tendsto {F : ℕ → PowerSeries ℝ} {F₀ : PowerSeries ℝ}
    (hF : ∀ k, IsPolyaFreqSeries (F k)) (hlim : Tendsto F atTop (𝓝 F₀)) :
    IsPolyaFreqSeries F₀ := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at hlim
  exact IsPolyaFreqSeq.of_tendsto (a := fun k n => PowerSeries.coeff n (F k)) hF hlim

end IsPolyaFreqSeries

/-- The series `C c * X ^ m` is Pólya-frequency for `c ≥ 0`. -/
theorem isPolyaFreqSeries_C_mul_X_pow {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    IsPolyaFreqSeries (PowerSeries.C c * PowerSeries.X ^ m) := by
  simpa using (IsPolyaFreqSeries.one.X_pow_mul m).C_mul hc

/-- The factor `1 + a X` with `a ≥ 0` is a Pólya-frequency series. -/
theorem isPolyaFreqSeries_one_add_C_mul_X {a : ℝ} (ha : 0 ≤ a) :
    IsPolyaFreqSeries (1 + PowerSeries.C a * PowerSeries.X) := by
  have hbase : IsPolyaFreqSeq (Polynomial.X + 1 : Polynomial ℝ).coeff := by
    convert IsPolyaFreqSeq.linear (r := (-1 : ℝ)) (by norm_num) using 1
    funext n
    simp
  have hscaled := hbase.geometricScale a ha
  unfold IsPolyaFreqSeries
  convert hscaled using 1
  funext n
  cases n with
  | zero => simp [geometricScale]
  | succ n =>
    cases n with
    | zero => simp [geometricScale, Polynomial.coeff_one]
    | succ n => simp [geometricScale, Polynomial.coeff_X, Polynomial.coeff_one]

/-- The geometric series `1 / (1 - b X) = ∑ₖ bᵏ Xᵏ`. -/
def geometricFactor (b : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => b ^ k

@[simp]
theorem coeff_geometricFactor (b : ℝ) (k : ℕ) :
    PowerSeries.coeff k (geometricFactor b) = b ^ k := by
  simp [geometricFactor]

/-- The geometric series is the formal inverse of `1 - b X`. -/
theorem geometricFactor_eq_inv (b : ℝ) :
    geometricFactor b = (1 - PowerSeries.C b * PowerSeries.X)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  have h := supersymmetricDenominatorFactor_mul_one_sub b
  have h2 : supersymmetricDenominatorFactor b = geometricFactor b := by
    ext n
    simp
  rwa [h2] at h

/-- The geometric series `1 / (1 - b X)` with `b ≥ 0` is a Pólya-frequency series. -/
theorem isPolyaFreqSeries_geometricFactor {b : ℝ} (hb : 0 ≤ b) :
    IsPolyaFreqSeries (geometricFactor b) := by
  unfold IsPolyaFreqSeries
  simpa using geometric_isPolyaFreqSeq b hb

/-- `exp (γ X)` is a Pólya-frequency series for `γ ≥ 0`: it is the coefficientwise limit of the
Pólya-frequency polynomials `(1 + (γ / N) X) ^ N`. -/
theorem isPolyaFreqSeries_rescale_exp {γ : ℝ} (hγ : 0 ≤ γ) :
    IsPolyaFreqSeries (PowerSeries.rescale γ (PowerSeries.exp ℝ)) := by
  refine IsPolyaFreqSeries.of_tendsto (F := exponentialTruncation γ) (fun N => ?_)
    (tendsto_exponentialTruncation γ)
  exact (isPolyaFreqSeries_one_add_C_mul_X
    (mul_nonneg hγ (inv_nonneg.mpr (Nat.cast_nonneg N)))).pow N

/-- The finite product `∏_{i < N} (1 + αᵢ X)` is a Pólya-frequency series for `αᵢ ≥ 0`. -/
theorem isPolyaFreqSeries_prod_one_add {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (N : ℕ) :
    IsPolyaFreqSeries (∏ i ∈ Finset.range N, (1 + PowerSeries.C (α i) * PowerSeries.X)) :=
  IsPolyaFreqSeries.prod _ fun i _ => isPolyaFreqSeries_one_add_C_mul_X (hα i)

/-- The finite product `∏_{i < N} 1 / (1 - βᵢ X)` is a Pólya-frequency series for `βᵢ ≥ 0`. -/
theorem isPolyaFreqSeries_prod_geometricFactor {β : ℕ → ℝ} (hβ : ∀ i, 0 ≤ β i) (N : ℕ) :
    IsPolyaFreqSeries (∏ i ∈ Finset.range N, geometricFactor (β i)) :=
  IsPolyaFreqSeries.prod _ fun i _ => isPolyaFreqSeries_geometricFactor (hβ i)

private theorem denominatorPrefix_eq_prod_geometricFactor (β : ℕ → ℝ) (N : ℕ) :
    supersymmetricDenominatorPrefix β N = ∏ i ∈ Finset.range N, geometricFactor (β i) := by
  rw [supersymmetricDenominatorPrefix, parameterPrefix, List.map_ofFn, List.prod_ofFn,
    Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  ext n
  simp [supersymmetricDenominatorFactor, geometricFactor]

private theorem summable_abs_of_summable_add {α β : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i)
    (hβ : ∀ i, 0 ≤ β i) (hsum : Summable fun i => α i + β i) :
    Summable (fun i => |α i|) ∧ Summable (fun i => |β i|) :=
  ⟨summable_abs_iff.mpr (hsum.of_nonneg_of_le hα fun i => le_add_of_nonneg_right (hβ i)),
    summable_abs_iff.mpr (hsum.of_nonneg_of_le hβ fun i => le_add_of_nonneg_left (hα i))⟩

private theorem tprod_one_sub_eq (β : ℕ → ℝ) :
    (∏' i, (1 - PowerSeries.C (β i) * PowerSeries.X)) =
      linearFactorProduct fun i => -β i := by
  unfold linearFactorProduct
  congr 1
  funext i
  simp [sub_eq_add_neg]

/-- The infinite numerator product `∏ᵢ (1 + αᵢ X)` is a Pólya-frequency series: it is the
coefficientwise limit of the finite products. -/
theorem isPolyaFreqSeries_tprod_one_add {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i)
    (hs : Summable fun i => |α i|) :
    IsPolyaFreqSeries (∏' i, (1 + PowerSeries.C (α i) * PowerSeries.X)) :=
  IsPolyaFreqSeries.of_tendsto (isPolyaFreqSeries_prod_one_add hα)
    (tendsto_linearFactorPrefix α hs)

/-- The reciprocal of the infinite product `∏ᵢ (1 - βᵢ X)` is a Pólya-frequency series: it is
the coefficientwise limit of the finite products of the geometric series `1 / (1 - βᵢ X)`. -/
theorem isPolyaFreqSeries_inv_tprod_one_sub {β : ℕ → ℝ} (hβ : ∀ i, 0 ≤ β i)
    (hs : Summable fun i => |β i|) :
    IsPolyaFreqSeries (∏' i, (1 - PowerSeries.C (β i) * PowerSeries.X))⁻¹ := by
  rw [tprod_one_sub_eq]
  refine IsPolyaFreqSeries.of_tendsto (F := supersymmetricDenominatorPrefix β) (fun N => ?_)
    (tendsto_supersymmetricDenominatorPrefix β hs)
  rw [denominatorPrefix_eq_prod_geometricFactor]
  exact isPolyaFreqSeries_prod_geometricFactor hβ N

/-- The canonical Edrei--Thoma product
`C X ^ m exp (γ X) ∏ᵢ (1 + αᵢ X) / ∏ᵢ (1 - βᵢ X)` as a formal power series.  The infinite
products are `tprod`s in the coefficientwise topology; the denominator is the formal inverse of
the convergent product `∏ᵢ (1 - βᵢ X)`. -/
def canonicalProduct (c : ℝ) (m : ℕ) (γ : ℝ) (α β : ℕ → ℝ) : PowerSeries ℝ :=
  PowerSeries.C c * PowerSeries.X ^ m * PowerSeries.rescale γ (PowerSeries.exp ℝ) *
    (∏' i, (1 + PowerSeries.C (α i) * PowerSeries.X)) *
      (∏' i, (1 - PowerSeries.C (β i) * PowerSeries.X))⁻¹

/-- The `N`th finite approximation to the canonical product: `exp (γ X)` is replaced by
`(1 + (γ / N) X) ^ N` and the infinite products by their first `N` factors, the denominator
factors being the geometric series `1 / (1 - βᵢ X)`. -/
def canonicalPrefixProduct (c : ℝ) (m : ℕ) (γ : ℝ) (α β : ℕ → ℝ) (N : ℕ) : PowerSeries ℝ :=
  PowerSeries.C c * PowerSeries.X ^ m * exponentialTruncation γ N *
    (∏ i ∈ Finset.range N, (1 + PowerSeries.C (α i) * PowerSeries.X)) *
      (∏ i ∈ Finset.range N, geometricFactor (β i))

/-- Each finite approximation to the canonical product is a Pólya-frequency series (the
finite-parameter statement). -/
theorem isPolyaFreqSeries_canonicalPrefixProduct {c γ : ℝ} (hc : 0 ≤ c) (hγ : 0 ≤ γ)
    {α β : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) (m N : ℕ) :
    IsPolyaFreqSeries (canonicalPrefixProduct c m γ α β N) :=
  (((isPolyaFreqSeries_C_mul_X_pow hc m).mul
    ((isPolyaFreqSeries_one_add_C_mul_X
      (mul_nonneg hγ (inv_nonneg.mpr (Nat.cast_nonneg N)))).pow N)).mul
    (isPolyaFreqSeries_prod_one_add hα N)).mul (isPolyaFreqSeries_prod_geometricFactor hβ N)

/-- Under the Edrei summability hypothesis, the finite approximations converge coefficientwise
to the canonical product. -/
theorem tendsto_canonicalPrefixProduct {c γ : ℝ} {m : ℕ} {α β : ℕ → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) (hsum : Summable fun i => α i + β i) :
    Tendsto (canonicalPrefixProduct c m γ α β) atTop (𝓝 (canonicalProduct c m γ α β)) := by
  obtain ⟨ha, hb⟩ := summable_abs_of_summable_add hα hβ hsum
  have hden : Tendsto (fun N => ∏ i ∈ Finset.range N, geometricFactor (β i)) atTop
      (𝓝 (∏' i, (1 - PowerSeries.C (β i) * PowerSeries.X))⁻¹) := by
    rw [tprod_one_sub_eq]
    have h := tendsto_supersymmetricDenominatorPrefix β hb
    rwa [show supersymmetricDenominatorPrefix β =
      fun N => ∏ i ∈ Finset.range N, geometricFactor (β i) from
        funext (denominatorPrefix_eq_prod_geometricFactor β)] at h
  exact (((tendsto_const_nhds.mul (tendsto_exponentialTruncation γ)).mul
    (tendsto_linearFactorPrefix α ha)).mul hden)

/-- **Edrei--Thoma, easy direction.**  The coefficient sequence of the canonical product
`C x ^ m e ^ (γ x) ∏ᵢ (1 + αᵢ x) / ∏ᵢ (1 - βᵢ x)`, with `C, γ, αᵢ, βᵢ ≥ 0` and
`∑ᵢ (αᵢ + βᵢ) < ∞`, is a Pólya-frequency sequence. -/
theorem isPolyaFreqSeries_canonicalProduct {c γ : ℝ} (hc : 0 ≤ c) (hγ : 0 ≤ γ) (m : ℕ)
    {α β : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hsum : Summable fun i => α i + β i) :
    IsPolyaFreqSeries (canonicalProduct c m γ α β) :=
  IsPolyaFreqSeries.of_tendsto (isPolyaFreqSeries_canonicalPrefixProduct hc hγ hα hβ m)
    (tendsto_canonicalPrefixProduct hα hβ hsum)

/-- The same statement for the coefficient sequence, in `IsPolyaFreqSeq` form. -/
theorem isPolyaFreqSeq_coeff_canonicalProduct {c γ : ℝ} (hc : 0 ≤ c) (hγ : 0 ≤ γ) (m : ℕ)
    {α β : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hsum : Summable fun i => α i + β i) :
    IsPolyaFreqSeq fun n => PowerSeries.coeff n (canonicalProduct c m γ α β) :=
  isPolyaFreqSeries_canonicalProduct hc hγ m hα hβ hsum

/-- The canonical product is `C X ^ m` times the infinite ASW--Edrei symbol of
`RealRooted.BrandenVecchi`. -/
theorem canonicalProduct_eq_C_mul_X_pow_mul_aswEdreiSymbol (c : ℝ) (m : ℕ) (γ : ℝ)
    (α β : ℕ → ℝ) :
    canonicalProduct c m γ α β =
      PowerSeries.C c * PowerSeries.X ^ m * aswEdreiSymbol γ α β := by
  have h : (∏' i, (1 + PowerSeries.C (α i) * PowerSeries.X)) = linearFactorProduct α := rfl
  rw [canonicalProduct, tprod_one_sub_eq, aswEdreiSymbol, h]
  ring

end RealRooted.EdreiThoma
