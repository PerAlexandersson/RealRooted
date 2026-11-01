module

public import RealRooted.BasisTransform.PolynomialSemigroups
import RealRooted.PFPolynomial.Closure
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Translation--Lah words and finite positive moment data

This file develops the algebraic finite-word part of the positive-measure
classification.  The generator bases and their PF preservation come from
`RealRooted.BasisTransform.PolynomialSemigroups`.  A reachable parameter pair
consists of the total Lah time and the finite list of translation atoms
inserted at the then-current Lah times.  It also proves the Hausdorff and
Hankel inequalities for arbitrary finite positive atomic measures.
-/

public section

open Filter Finset Polynomial Topology

noncomputable section

namespace RealRooted

/-- A generator in a finite word of translations and Lah flows. -/
inductive TranslationLahGenerator where
  /-- Translation by the displayed amount. -/
  | translation (a : ℝ)
  /-- Lah flow for the displayed time. -/
  | lah (b : ℝ)
  deriving DecidableEq

/-- The monomial-image basis belonging to one translation--Lah generator. -/
def TranslationLahGenerator.basis : TranslationLahGenerator → ℕ → ℝ[X]
  | .translation a => raySemigroupBasis a 0 1
  | .lah b => raySemigroupBasis 0 b 1

/-- The monomial-image basis of a finite composition, with the head acting
last (by left composition). -/
def translationLahWordBasis : List TranslationLahGenerator → ℕ → ℝ[X]
  | [], n => X ^ n
  | g :: w, n => basisTransform g.basis (translationLahWordBasis w n)

/-- The coefficientwise linear polynomial map encoded by a finite word. -/
def translationLahWordTransform
    (w : List TranslationLahGenerator) (p : ℝ[X]) : ℝ[X] :=
  basisTransform (translationLahWordBasis w) p

/-- The total Lah time of a finite generator word. -/
def translationLahWordBeta : List TranslationLahGenerator → ℝ
  | [] => 0
  | .translation _ :: w => translationLahWordBeta w
  | .lah b :: w => translationLahWordBeta w + b

/-- The translation atoms of a finite word.  The head acts last, so a head
translation is inserted at the total Lah time of the tail. -/
def translationLahWordAtoms :
    List TranslationLahGenerator → List (ℝ × ℝ)
  | [] => []
  | .translation a :: w =>
      (translationLahWordBeta w, a) :: translationLahWordAtoms w
  | .lah _ :: w => translationLahWordAtoms w

/-- A finite translation--Lah word has only nonnegative generator
parameters. -/
def TranslationLahWordValid : List TranslationLahGenerator → Prop
  | [] => True
  | .translation a :: w => 0 ≤ a ∧ TranslationLahWordValid w
  | .lah b :: w => 0 ≤ b ∧ TranslationLahWordValid w

/-- Prepending a generator to a word is left composition by its basis map. -/
theorem translationLahWordTransform_cons
    (g : TranslationLahGenerator) (w : List TranslationLahGenerator)
    (p : ℝ[X]) :
    translationLahWordTransform (g :: w) p =
      basisTransform g.basis (translationLahWordTransform w p) := by
  rw [translationLahWordTransform, translationLahWordTransform,
    basisTransform_basisTransform]
  rfl

private theorem basisTransform_monomialBasis (p : ℝ[X]) :
    basisTransform (fun n : ℕ => (X : ℝ[X]) ^ n) p = p := by
  induction p using Polynomial.induction_on' with
  | add f g hf hg => rw [basisTransform_add, hf, hg]
  | monomial n c =>
      rw [basisTransform_monomial, Polynomial.C_mul_X_pow_eq_monomial]

/-- Every valid translation--Lah word preserves PF polynomials. -/
theorem translationLahWordTransform_isPFPolynomial
    {w : List TranslationLahGenerator} (hw : TranslationLahWordValid w)
    {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (translationLahWordTransform w p) := by
  induction w with
  | nil =>
      simpa [translationLahWordTransform, translationLahWordBasis,
        basisTransform_monomialBasis] using hp
  | cons g w ih =>
      rw [translationLahWordTransform_cons]
      cases g with
      | translation a =>
          simpa [TranslationLahGenerator.basis, raySemigroupTransform] using
            raySemigroupTransform_isPFPolynomial hw.1 (by norm_num) zero_le_one
              (ih hw.2)
      | lah b =>
          simpa [TranslationLahGenerator.basis, raySemigroupTransform] using
            raySemigroupTransform_isPFPolynomial (by norm_num) hw.1 zero_le_one
              (ih hw.2)

/-- The Lah flow `exp (b X D²)`, represented by the library ray semigroup,
preserves every PF polynomial for `b ≥ 0`. -/
theorem lahFlowTransform_isPFPolynomial
    {b : ℝ} (hb : 0 ≤ b) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (raySemigroupTransform 0 b 1 p) :=
  raySemigroupTransform_isPFPolynomial (by norm_num) hb zero_le_one hp

/-- A family of monomial images belongs to the sequential coefficientwise
closure of valid finite translation--Lah words. -/
def IsTranslationLahWordClosure (T : ℕ → ℝ[X]) : Prop :=
  ∃ words : ℕ → List TranslationLahGenerator,
    (∀ M, TranslationLahWordValid (words M)) ∧
      ∀ n i, Tendsto (fun M => (translationLahWordBasis (words M) n).coeff i)
        atTop (𝓝 ((T n).coeff i))

/-- Every coefficientwise limit of valid finite-word operators preserves PF
polynomials. -/
theorem IsTranslationLahWordClosure.isPFPolynomial_basisTransform
    {T : ℕ → ℝ[X]} (hT : IsTranslationLahWordClosure T)
    {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform T p) := by
  obtain ⟨words, hvalid, hlimit⟩ := hT
  apply IsPFPolynomial.of_coeff_tendsto
    (p := fun M => translationLahWordTransform (words M) p)
  · intro M
    exact translationLahWordTransform_isPFPolynomial (hvalid M) hp
  · intro i
    rw [show (fun M => (translationLahWordTransform (words M) p).coeff i) =
        fun M => ∑ n ∈ p.support,
          p.coeff n * (translationLahWordBasis (words M) n).coeff i by
      funext M
      rw [translationLahWordTransform, coeff_basisTransform,
        Polynomial.sum_def]]
    rw [coeff_basisTransform, Polynomial.sum_def]
    exact tendsto_finsetSum _ fun n _ => (hlimit n i).const_mul (p.coeff n)

/-! ## Coefficientwise formal exponential generating functions -/

/-- The substitution series `z / (1 - β z)`, specified coefficientwise. -/
def translationLahSubstitutionSeries (β : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => if n = 0 then 0 else β ^ (n - 1)

/-- The formal logarithm of the finite-word prefactor.  An atom `(u, a)`
contributes `a z / (1 - u z)`. -/
def translationLahLogSeries (atoms : List (ℝ × ℝ)) : PowerSeries ℝ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else (atoms.map fun ua => ua.2 * ua.1 ^ (n - 1)).sum

/-- The finite-word prefactor obtained by formally exponentiating its
atomic logarithm. -/
def translationLahPrefactorSeries (atoms : List (ℝ × ℝ)) : PowerSeries ℝ :=
  (PowerSeries.exp ℝ).subst (translationLahLogSeries atoms)

/-- The exponential generating series of a polynomial row family. -/
def polynomialRowEGF (P : ℕ → ℝ[X]) : PowerSeries ℝ[X] :=
  PowerSeries.mk fun n => C ((n.factorial : ℝ)⁻¹) * P n

/-- A row family has the translation--Lah EGF with the displayed final Lah
time and atomic prefactor.  This is an equality of formal power series, so no
analytic convergence is involved. -/
def HasTranslationLahEGF
    (P : ℕ → ℝ[X]) (β : ℝ) (atoms : List (ℝ × ℝ)) : Prop :=
  polynomialRowEGF P =
    (translationLahPrefactorSeries atoms).map C *
      (PowerSeries.exp ℝ[X]).subst
        (PowerSeries.C X * (translationLahSubstitutionSeries β).map C)

/-- The coefficient of degree `j+1` in the substitution series is `β^j`. -/
@[simp] theorem coeff_translationLahSubstitutionSeries_succ (β : ℝ) (j : ℕ) :
    PowerSeries.coeff (j + 1) (translationLahSubstitutionSeries β) = β ^ j := by
  simp [translationLahSubstitutionSeries]

/-- The constant coefficient of the atomic logarithm is zero. -/
@[simp] theorem constantCoeff_translationLahLogSeries
    (atoms : List (ℝ × ℝ)) :
    PowerSeries.constantCoeff (translationLahLogSeries atoms) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [translationLahLogSeries]

/-- Formal logarithmic coefficients are exactly the moments of the finite
atomic measure encoded by the word. -/
theorem coeff_translationLahLogSeries_succ
    (atoms : List (ℝ × ℝ)) (j : ℕ) :
    PowerSeries.coeff (j + 1) (translationLahLogSeries atoms) =
      (atoms.map fun ua => ua.2 * ua.1 ^ j).sum := by
  simp [translationLahLogSeries]

@[simp] private theorem translationLahLogSeries_nil :
    translationLahLogSeries [] = 0 := by
  ext n
  simp [translationLahLogSeries]

@[simp] private theorem translationLahPrefactorSeries_nil :
    translationLahPrefactorSeries [] = 1 := by
  rw [translationLahPrefactorSeries, translationLahLogSeries_nil,
    PowerSeries.subst_zero_eq_C_constantCoeff]
  simp

@[simp] private theorem translationLahSubstitutionSeries_zero :
    translationLahSubstitutionSeries 0 = PowerSeries.X := by
  ext n
  cases n with
  | zero => simp [translationLahSubstitutionSeries]
  | succ n =>
      cases n with
      | zero => simp [translationLahSubstitutionSeries]
      | succ n =>
          rw [PowerSeries.coeff_X]
          simp [translationLahSubstitutionSeries]

/-- The empty word has EGF `exp (x z)`. -/
theorem hasTranslationLahEGF_nil :
    HasTranslationLahEGF (translationLahWordBasis []) 0 [] := by
  unfold HasTranslationLahEGF
  rw [translationLahPrefactorSeries_nil,
    translationLahSubstitutionSeries_zero]
  simp only [map_one, PowerSeries.map_X, one_mul]
  rw [← PowerSeries.smul_eq_C_mul]
  rw [← PowerSeries.rescale_eq_subst]
  apply PowerSeries.ext
  intro n
  simp [polynomialRowEGF, translationLahWordBasis, PowerSeries.coeff_rescale]

/-- Reachable EGF parameters for finite translation--Lah compositions.

`TranslationLahParameters β atoms` says that the total Lah time is `β` and
that `atoms` records `(location, mass)` for every translation. -/
inductive TranslationLahParameters : ℝ → List (ℝ × ℝ) → Prop where
  /-- The empty word has zero Lah time and no atoms. -/
  | nil : TranslationLahParameters 0 []
  /-- Translation inserts an atom at the current Lah time. -/
  | translation {β : ℝ} {atoms : List (ℝ × ℝ)}
      (h : TranslationLahParameters β atoms) (a : ℝ) (ha : 0 ≤ a) :
      TranslationLahParameters β ((β, a) :: atoms)
  /-- A Lah step increases the total time without moving existing atoms. -/
  | lah {β : ℝ} {atoms : List (ℝ × ℝ)}
      (h : TranslationLahParameters β atoms) (b : ℝ) (hb : 0 ≤ b) :
      TranslationLahParameters (β + b) atoms

/-- Every valid finite word produces its total Lah time and translation
atoms according to `TranslationLahParameters`. -/
theorem translationLahParameters_word
    {w : List TranslationLahGenerator} (hw : TranslationLahWordValid w) :
    TranslationLahParameters (translationLahWordBeta w)
      (translationLahWordAtoms w) := by
  induction w with
  | nil => exact TranslationLahParameters.nil
  | cons g w ih =>
      cases g with
      | translation a =>
          exact (ih hw.2).translation a hw.1
      | lah b =>
          exact (ih hw.2).lah b hw.1

/-- Every reachable finite parameter pair is represented by an actual valid
word of translation and Lah generators. -/
theorem TranslationLahParameters.exists_word
    {β : ℝ} {atoms : List (ℝ × ℝ)}
    (h : TranslationLahParameters β atoms) :
    ∃ w : List TranslationLahGenerator,
      TranslationLahWordValid w ∧
      translationLahWordBeta w = β ∧
      translationLahWordAtoms w = atoms := by
  induction h with
  | nil => exact ⟨[], trivial, rfl, rfl⟩
  | @translation β atoms h a ha ih =>
      obtain ⟨w, hw, hβ, hatoms⟩ := ih
      refine ⟨.translation a :: w, ⟨ha, hw⟩, hβ, ?_⟩
      simp only [translationLahWordAtoms]
      rw [hβ, hatoms]
  | @lah β atoms h b hb ih =>
      obtain ⟨w, hw, hβ, hatoms⟩ := ih
      refine ⟨.lah b :: w, ⟨hb, hw⟩, ?_, hatoms⟩
      simp only [translationLahWordBeta]
      rw [hβ]

/-- Finite translation--Lah parameters have nonnegative total time. -/
theorem TranslationLahParameters.beta_nonneg
    {β : ℝ} {atoms : List (ℝ × ℝ)}
    (h : TranslationLahParameters β atoms) : 0 ≤ β := by
  induction h with
  | nil => simp
  | translation h _ _ ih => exact ih
  | lah h b hb ih => positivity

/-- Every reachable translation atom has nonnegative mass and lies between
zero and the final Lah time. -/
theorem TranslationLahParameters.atom_mem_Icc
    {β : ℝ} {atoms : List (ℝ × ℝ)}
    (h : TranslationLahParameters β atoms) {u a : ℝ}
    (hua : (u, a) ∈ atoms) : 0 ≤ u ∧ u ≤ β ∧ 0 ≤ a := by
  induction h with
  | nil => simp at hua
  | @translation β atoms h a ha ih =>
      simp only [List.mem_cons, Prod.mk.injEq] at hua
      rcases hua with hnew | hold
      · rcases hnew with ⟨rfl, rfl⟩
        exact ⟨h.beta_nonneg, le_rfl, ha⟩
      · exact ih hold
  | @lah β atoms h b hb ih =>
      obtain ⟨hu0, huβ, ha0⟩ := ih hua
      exact ⟨hu0, huβ.trans (by linarith), ha0⟩

/-- Every decreasing list of nonnegative atoms supported in `[0, β]` is
realized by a finite translation--Lah composition. -/
theorem translationLahParameters_of_pairwise
    {β : ℝ} {atoms : List (ℝ × ℝ)} (hβ : 0 ≤ β)
    (hnonneg : ∀ ua ∈ atoms, 0 ≤ ua.1 ∧ 0 ≤ ua.2)
    (hordered : atoms.Pairwise fun ua va => va.1 ≤ ua.1)
    (hupper : ∀ ua ∈ atoms, ua.1 ≤ β) :
    TranslationLahParameters β atoms := by
  induction atoms generalizing β with
  | nil =>
      simpa using TranslationLahParameters.nil.lah β hβ
  | cons ua atoms ih =>
      have hua0 : 0 ≤ ua.1 := (hnonneg ua (by simp)).1
      have huaweight : 0 ≤ ua.2 := (hnonneg ua (by simp)).2
      have htailnonneg : ∀ va ∈ atoms, 0 ≤ va.1 ∧ 0 ≤ va.2 := by
        intro va hva
        exact hnonneg va (by simp [hva])
      have htailupper : ∀ va ∈ atoms, va.1 ≤ ua.1 := by
        intro va hva
        exact (List.pairwise_cons.mp hordered).1 va hva
      have htailordered : atoms.Pairwise fun va wa => wa.1 ≤ va.1 :=
        (List.pairwise_cons.mp hordered).2
      have htail : TranslationLahParameters ua.1 atoms :=
        ih hua0 htailnonneg htailordered htailupper
      have hins : TranslationLahParameters ua.1 (ua :: atoms) := by
        simpa [Prod.eta] using htail.translation ua.2 huaweight
      convert hins.lah (β - ua.1) (sub_nonneg.mpr (hupper ua (by simp))) using 1
      ring

/-- Constructive finite atomic realization: every decreasing list of
nonnegative atoms in `[0, β]` is the atom list of a valid finite word whose
total Lah time is `β`. -/
theorem exists_translationLahWord_of_pairwise
    {β : ℝ} {atoms : List (ℝ × ℝ)} (hβ : 0 ≤ β)
    (hnonneg : ∀ ua ∈ atoms, 0 ≤ ua.1 ∧ 0 ≤ ua.2)
    (hordered : atoms.Pairwise fun ua va => va.1 ≤ ua.1)
    (hupper : ∀ ua ∈ atoms, ua.1 ≤ β) :
    ∃ w : List TranslationLahGenerator,
      TranslationLahWordValid w ∧
      translationLahWordBeta w = β ∧
      translationLahWordAtoms w = atoms :=
  (translationLahParameters_of_pairwise hβ hnonneg hordered hupper).exists_word

/-- The `j`th moment of a finite atomic measure with locations `u` and
weights `w`. -/
def atomicMoment {ι : Type*} (s : Finset ι)
    (w u : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ s, w i * u i ^ j

/-- Moments of a finite positive atomic measure are nonnegative. -/
theorem atomicMoment_nonneg {ι : Type*} {s : Finset ι}
    {w u : ι → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hu : ∀ i ∈ s, 0 ≤ u i) (j : ℕ) :
    0 ≤ atomicMoment s w u j := by
  exact sum_nonneg fun i hi => mul_nonneg (hw i hi) (pow_nonneg (hu i hi) j)

/-- Compact support gives the successive moment bound
`m_(j+1) ≤ β m_j`. -/
theorem atomicMoment_succ_le_mul {ι : Type*} {s : Finset ι}
    {w u : ι → ℝ} {β : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hu0 : ∀ i ∈ s, 0 ≤ u i) (huβ : ∀ i ∈ s, u i ≤ β)
    (j : ℕ) :
    atomicMoment s w u (j + 1) ≤ β * atomicMoment s w u j := by
  rw [atomicMoment, atomicMoment, mul_sum]
  apply sum_le_sum
  intro i hi
  rw [pow_succ]
  have hfactor : 0 ≤ w i * u i ^ j :=
    mul_nonneg (hw i hi) (pow_nonneg (hu0 i hi) j)
  calc
    w i * (u i ^ j * u i) ≤ w i * u i ^ j * β := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left (huβ i hi) hfactor
    _ = β * (w i * u i ^ j) := by ring

/-- The first three moments of a finite positive atomic measure satisfy the
Hankel determinant inequality `m₁² ≤ m₀ m₂`. -/
theorem sq_atomicMoment_one_le_mul_zero_two
    {ι : Type*} {s : Finset ι} {w u : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    atomicMoment s w u 1 ^ 2 ≤
      atomicMoment s w u 0 * atomicMoment s w u 2 := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun i => w i * u i)
    (f := w) (g := fun i => w i * u i ^ 2)
    hw
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg (u i)))
    (fun i _ => le_of_eq (by ring))
  simpa [atomicMoment, pow_two] using h

/-- The alternating binomial combination of atomic moments is the integral
of `u^j (β-u)^k`, written as a finite weighted sum. -/
theorem sum_alternating_choose_mul_atomicMoment
    {ι : Type*} (s : Finset ι) (w u : ι → ℝ)
    (β : ℝ) (j k : ℕ) :
    ∑ i ∈ range (k + 1),
        (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) * β ^ (k - i) *
          atomicMoment s w u (j + i) =
      ∑ q ∈ s, w q * u q ^ j * (β - u q) ^ k := by
  simp_rw [atomicMoment, Finset.mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro q hq
  have hpow :
      (β - u q) ^ k =
        ∑ i ∈ range (k + 1),
          (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) *
            β ^ (k - i) * u q ^ i := by
    rw [show β - u q = -u q + β by ring, add_pow]
    apply sum_congr rfl
    intro i hi
    rw [neg_pow]
    ring
  calc
    ∑ i ∈ range (k + 1),
        (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) * β ^ (k - i) *
          (w q * u q ^ (j + i)) =
        w q * u q ^ j *
          ∑ i ∈ range (k + 1),
            (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) *
              β ^ (k - i) * u q ^ i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [pow_add]
      ring
    _ = w q * u q ^ j * (β - u q) ^ k := by rw [hpow]

/-- All Hausdorff finite differences of the moments of a positive atomic
measure supported in `[0, β]` are nonnegative. -/
theorem sum_alternating_choose_mul_atomicMoment_nonneg
    {ι : Type*} {s : Finset ι} {w u : ι → ℝ} {β : ℝ}
    (hw : ∀ q ∈ s, 0 ≤ w q) (hu0 : ∀ q ∈ s, 0 ≤ u q)
    (huβ : ∀ q ∈ s, u q ≤ β) (j k : ℕ) :
    0 ≤ ∑ i ∈ range (k + 1),
      (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) * β ^ (k - i) *
        atomicMoment s w u (j + i) := by
  rw [sum_alternating_choose_mul_atomicMoment]
  exact sum_nonneg fun q hq =>
    mul_nonneg
      (mul_nonneg (hw q hq) (pow_nonneg (hu0 q hq) j))
      (pow_nonneg (sub_nonneg.mpr (huβ q hq)) k)

/-! ## Arbitrary finite positive measures -/

open MeasureTheory Set Filter

/-- Every power is integrable against a finite measure supported on a compact
nonnegative interval. -/
theorem integrable_pow_of_ae_mem_Icc
    {ν : Measure ℝ} [IsFiniteMeasure ν] {β : ℝ}
    (hsupport : ∀ᵐ u ∂ν, u ∈ Icc 0 β) (j : ℕ) :
    Integrable (fun u : ℝ => u ^ j) ν := by
  apply (integrable_const (|β| ^ j)).mono'
  · exact (continuous_id.pow j).aestronglyMeasurable
  · filter_upwards [hsupport] with u hu
    simp only [Real.norm_eq_abs, abs_pow]
    have hβ0 : 0 ≤ β := hu.1.trans hu.2
    rw [abs_of_nonneg hu.1, abs_of_nonneg hβ0]
    exact pow_le_pow_left₀ hu.1 hu.2 j

/-- Moments of a positive measure supported in `[0, β]` are
nonnegative. -/
theorem integral_pow_nonneg_of_ae_mem_Icc
    {ν : Measure ℝ} {β : ℝ}
    (hsupport : ∀ᵐ u ∂ν, u ∈ Icc 0 β) (j : ℕ) :
    0 ≤ ∫ u : ℝ, u ^ j ∂ν := by
  apply integral_nonneg_of_ae
  filter_upwards [hsupport] with u hu
  exact pow_nonneg hu.1 j

/-- Compact support gives the successive moment bound for an arbitrary
finite positive measure. -/
theorem integral_pow_succ_le_mul_of_ae_mem_Icc
    {ν : Measure ℝ} [IsFiniteMeasure ν] {β : ℝ}
    (hsupport : ∀ᵐ u ∂ν, u ∈ Icc 0 β) (j : ℕ) :
    (∫ u : ℝ, u ^ (j + 1) ∂ν) ≤ β * ∫ u : ℝ, u ^ j ∂ν := by
  rw [← integral_const_mul]
  apply integral_mono_ae
  · exact integrable_pow_of_ae_mem_Icc hsupport (j + 1)
  · exact (integrable_pow_of_ae_mem_Icc hsupport j).const_mul β
  · filter_upwards [hsupport] with u hu
    rw [pow_succ]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left hu.2 (pow_nonneg hu.1 j)

/-- The first three moments of any finite positive measure supported in a
compact nonnegative interval satisfy `m₁² ≤ m₀ m₂`. -/
theorem sq_integral_pow_one_le_mul_zero_two
    {ν : Measure ℝ} [IsFiniteMeasure ν] {β : ℝ}
    (hsupport : ∀ᵐ u ∂ν, u ∈ Icc 0 β) :
    (∫ u : ℝ, u ^ 1 ∂ν) ^ 2 ≤
      (∫ u : ℝ, u ^ 0 ∂ν) * ∫ u : ℝ, u ^ 2 ∂ν := by
  let m0 : ℝ := ∫ u : ℝ, u ^ 0 ∂ν
  let m1 : ℝ := ∫ u : ℝ, u ^ 1 ∂ν
  let m2 : ℝ := ∫ u : ℝ, u ^ 2 ∂ν
  have hm0 : 0 ≤ m0 := integral_pow_nonneg_of_ae_mem_Icc hsupport 0
  have hm1 : 0 ≤ m1 := integral_pow_nonneg_of_ae_mem_Icc hsupport 1
  have hm1le : m1 ≤ β * m0 :=
    integral_pow_succ_le_mul_of_ae_mem_Icc hsupport 0
  by_cases hm0zero : m0 = 0
  · have hm1zero : m1 = 0 := by
      apply le_antisymm
      · simpa [hm0zero] using hm1le
      · exact hm1
    change m1 ^ 2 ≤ m0 * m2
    simp [hm0zero, hm1zero]
  · have hm0pos : 0 < m0 := lt_of_le_of_ne hm0 (Ne.symm hm0zero)
    have h0int := integrable_pow_of_ae_mem_Icc hsupport 0
    have h1int := integrable_pow_of_ae_mem_Icc hsupport 1
    have h2int := integrable_pow_of_ae_mem_Icc hsupport 2
    have hquad : 0 ≤ ∫ u : ℝ, (m0 * u - m1) ^ 2 ∂ν :=
      integral_nonneg_of_ae (Eventually.of_forall fun u => sq_nonneg _)
    have hscaled2 :
        Integrable (fun u : ℝ => m0 ^ 2 * u ^ 2) ν :=
      h2int.const_mul _
    have hscaled1 :
        Integrable (fun u : ℝ => (2 * m0 * m1) * u ^ 1) ν :=
      h1int.const_mul _
    have hconst : Integrable (fun u : ℝ => m1 ^ 2 * u ^ 0) ν :=
      h0int.const_mul _
    have hquad_eq :
        (∫ u : ℝ, (m0 * u - m1) ^ 2 ∂ν) =
          m0 ^ 2 * m2 - (2 * m0 * m1) * m1 + m1 ^ 2 * m0 := by
      rw [show (fun u : ℝ => (m0 * u - m1) ^ 2) =
          fun u =>
            m0 ^ 2 * u ^ 2 - (2 * m0 * m1) * u ^ 1 + m1 ^ 2 * u ^ 0 by
        funext u
        ring]
      calc
        (∫ u : ℝ,
            m0 ^ 2 * u ^ 2 - (2 * m0 * m1) * u ^ 1 +
              m1 ^ 2 * u ^ 0 ∂ν) =
            (∫ u : ℝ, m0 ^ 2 * u ^ 2 ∂ν) -
              (∫ u : ℝ, (2 * m0 * m1) * u ^ 1 ∂ν) +
                ∫ u : ℝ, m1 ^ 2 * u ^ 0 ∂ν := by
          have hadd := integral_add (hscaled2.sub hscaled1) hconst
          have hsub := integral_sub hscaled2 hscaled1
          simp only [Pi.sub_apply] at hadd
          rw [hsub] at hadd
          exact hadd
        _ = m0 ^ 2 * m2 - (2 * m0 * m1) * m1 + m1 ^ 2 * m0 := by
          simp only [integral_const_mul]
          change m0 ^ 2 * m2 - (2 * m0 * m1) * m1 + m1 ^ 2 * m0 = _
          rfl
    have hproduct : 0 ≤ m0 * (m0 * m2 - m1 ^ 2) := by
      rw [hquad_eq] at hquad
      nlinarith
    have hdet : 0 ≤ m0 * m2 - m1 ^ 2 := by
      by_contra hdet
      have hneg : m0 * m2 - m1 ^ 2 < 0 := lt_of_not_ge hdet
      have := mul_neg_of_pos_of_neg hm0pos hneg
      linarith
    change m1 ^ 2 ≤ m0 * m2
    linarith

/-- The alternating binomial combination of moments is the integral of
`u^j (β-u)^k` for any finite measure supported in `[0, β]`. -/
theorem sum_alternating_choose_mul_integral_pow
    {ν : Measure ℝ} [IsFiniteMeasure ν] {β : ℝ}
    (hsupport : ∀ᵐ u ∂ν, u ∈ Icc 0 β) (j k : ℕ) :
    ∑ i ∈ range (k + 1),
        (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) * β ^ (k - i) *
          (∫ u : ℝ, u ^ (j + i) ∂ν) =
      ∫ u : ℝ, u ^ j * (β - u) ^ k ∂ν := by
  have hint : ∀ i ∈ range (k + 1),
      Integrable
        (fun u : ℝ =>
          ((-1 : ℝ) ^ i * (Nat.choose k i : ℝ) * β ^ (k - i)) *
            u ^ (j + i)) ν := by
    intro i hi
    exact (integrable_pow_of_ae_mem_Icc hsupport (j + i)).const_mul _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ hint]
  apply integral_congr_ae
  filter_upwards with u
  have hpow :
      (β - u) ^ k =
        ∑ i ∈ range (k + 1),
          (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) *
            β ^ (k - i) * u ^ i := by
    rw [show β - u = -u + β by ring, add_pow]
    apply sum_congr rfl
    intro i hi
    rw [neg_pow]
    ring
  rw [hpow, mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [pow_add]
  ring

/-- All Hausdorff finite differences of the moments of a finite positive
measure supported in `[0, β]` are nonnegative. -/
theorem sum_alternating_choose_mul_integral_pow_nonneg
    {ν : Measure ℝ} [IsFiniteMeasure ν] {β : ℝ}
    (hsupport : ∀ᵐ u ∂ν, u ∈ Icc 0 β) (j k : ℕ) :
    0 ≤ ∑ i ∈ range (k + 1),
      (-1 : ℝ) ^ i * (Nat.choose k i : ℝ) * β ^ (k - i) *
        (∫ u : ℝ, u ^ (j + i) ∂ν) := by
  rw [sum_alternating_choose_mul_integral_pow hsupport]
  apply integral_nonneg_of_ae
  filter_upwards [hsupport] with u hu
  exact mul_nonneg (pow_nonneg hu.1 j)
    (pow_nonneg (sub_nonneg.mpr hu.2) k)

end RealRooted
