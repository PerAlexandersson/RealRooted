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

/-- The substitution series has zero constant coefficient. -/
@[simp] theorem constantCoeff_translationLahSubstitutionSeries (β : ℝ) :
    PowerSeries.constantCoeff (translationLahSubstitutionSeries β) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
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

/-- Adding a translation atom adds its geometric moment series to the formal
logarithm when the substitution series is known to have zero constant term. -/
theorem translationLahLogSeries_cons_of_constantCoeff_eq_zero
    (u a : ℝ) (atoms : List (ℝ × ℝ))
    (hzero : PowerSeries.constantCoeff (translationLahSubstitutionSeries u) = 0) :
    translationLahLogSeries ((u, a) :: atoms) =
      translationLahLogSeries atoms +
        PowerSeries.C a * translationLahSubstitutionSeries u := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hzero]
  | succ n =>
      simp [coeff_translationLahLogSeries_succ,
        coeff_translationLahSubstitutionSeries_succ]
      ring

/-- Adding a translation atom adds its geometric moment series to the formal
logarithm of the EGF prefactor. -/
theorem translationLahLogSeries_cons (u a : ℝ) (atoms : List (ℝ × ℝ)) :
    translationLahLogSeries ((u, a) :: atoms) =
      translationLahLogSeries atoms +
        PowerSeries.C a * translationLahSubstitutionSeries u :=
  translationLahLogSeries_cons_of_constantCoeff_eq_zero u a atoms (by simp)

private theorem powerSeries_eq_of_derivative_eq_mul
    {f g h : PowerSeries ℝ}
    (hf : PowerSeries.derivative f = f * h)
    (hg : PowerSeries.derivative g = g * h)
    (hzero : PowerSeries.constantCoeff f = PowerSeries.constantCoeff g) :
    f = g := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero
      | succ n =>
          have hfc := congrArg (PowerSeries.coeff n) hf
          have hgc := congrArg (PowerSeries.coeff n) hg
          rw [PowerSeries.coeff_derivative] at hfc hgc
          rw [PowerSeries.coeff_mul] at hfc hgc
          have hsum :
              (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
                PowerSeries.coeff x.1 f * PowerSeries.coeff x.2 h) =
              ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
                PowerSeries.coeff x.1 g * PowerSeries.coeff x.2 h := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [ih x.1 (Finset.Nat.antidiagonal.fst_lt hx)]
          rw [hsum] at hfc
          apply mul_right_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)
          exact hfc.trans hgc.symm

private theorem subst_exp_add {f g : PowerSeries ℝ}
    (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) :
    (PowerSeries.exp ℝ).subst (f + g) =
      (PowerSeries.exp ℝ).subst f * (PowerSeries.exp ℝ).subst g := by
  have hfsubst : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf
  have hgsubst : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hg
  have haddsubst : PowerSeries.HasSubst (f + g) := hfsubst.add hgsubst
  apply powerSeries_eq_of_derivative_eq_mul
    (h := PowerSeries.derivative f + PowerSeries.derivative g)
  · rw [PowerSeries.derivative_subst haddsubst, PowerSeries.derivative_exp,
      PowerSeries.derivative.map_add]
  · rw [PowerSeries.derivative.leibniz,
      PowerSeries.derivative_subst hfsubst, PowerSeries.derivative_exp,
      PowerSeries.derivative_subst hgsubst, PowerSeries.derivative_exp]
    simp only [smul_eq_mul]
    ring
  · have hfg : PowerSeries.constantCoeff (f + g) = 0 := by
      simp [hf, hg]
    have hleft : PowerSeries.constantCoeff
        ((PowerSeries.exp ℝ).subst (f + g)) = 1 := by
      rw [PowerSeries.constantCoeff_eq,
        PowerSeries.constantCoeff_subst_of_constantCoeff_zero hfg]
      simp
    have hfirst : PowerSeries.constantCoeff
        ((PowerSeries.exp ℝ).subst f) = 1 := by
      rw [PowerSeries.constantCoeff_eq,
        PowerSeries.constantCoeff_subst_of_constantCoeff_zero hf]
      simp
    have hsecond : PowerSeries.constantCoeff
        ((PowerSeries.exp ℝ).subst g) = 1 := by
      rw [PowerSeries.constantCoeff_eq,
        PowerSeries.constantCoeff_subst_of_constantCoeff_zero hg]
      simp
    rw [map_mul, hleft, hfirst, hsecond, mul_one]

private theorem translationLahSubstitutionSeries_mul_one_sub (β : ℝ) :
    translationLahSubstitutionSeries β *
        (1 - PowerSeries.C β * PowerSeries.X) =
      PowerSeries.X := by
  rw [mul_sub, mul_one]
  rw [show translationLahSubstitutionSeries β *
      (PowerSeries.C β * PowerSeries.X) =
      PowerSeries.C β *
        (translationLahSubstitutionSeries β * PowerSeries.X) by ring]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp [coeff_translationLahSubstitutionSeries_succ,
          PowerSeries.coeff_succ_mul_X]
      | succ n =>
          simp [coeff_translationLahSubstitutionSeries_succ,
            PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_X, pow_succ]
          ring

/-- Composing two Lah substitution series adds their parameters. -/
theorem translationLahSubstitutionSeries_subst (β b : ℝ) :
    (translationLahSubstitutionSeries b).subst
        (translationLahSubstitutionSeries β) =
      translationLahSubstitutionSeries (β + b) := by
  let P := translationLahSubstitutionSeries β
  let Q := translationLahSubstitutionSeries (β + b)
  let D : PowerSeries ℝ := 1 - PowerSeries.C β * PowerSeries.X
  let R : PowerSeries ℝ := 1 - PowerSeries.C b * P
  have hP : P * D = PowerSeries.X := by
    simpa [P, D] using translationLahSubstitutionSeries_mul_one_sub β
  have hQ : Q * (1 - PowerSeries.C (β + b) * PowerSeries.X) =
      PowerSeries.X := by
    simpa [Q] using translationLahSubstitutionSeries_mul_one_sub (β + b)
  have hPsubst : PowerSeries.HasSubst P := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simp [P]
  have hsub : (translationLahSubstitutionSeries b).subst P * R = P := by
    have hidentity := translationLahSubstitutionSeries_mul_one_sub b
    rw [PowerSeries.C_eq_algebraMap] at hidentity
    have hmap := congrArg (PowerSeries.substAlgHom hPsubst)
      hidentity
    rw [map_mul, map_sub, map_one, map_mul,
      PowerSeries.substAlgHom_X] at hmap
    rw [(PowerSeries.substAlgHom hPsubst).commutes b] at hmap
    simpa [PowerSeries.coe_substAlgHom, PowerSeries.algebraMap_eq,
      PowerSeries.C_apply, R] using hmap
  have hRD : R * D = 1 - PowerSeries.C (β + b) * PowerSeries.X := by
    calc
      R * D = D - PowerSeries.C b * (P * D) := by
        simp only [R]
        ring
      _ = D - PowerSeries.C b * PowerSeries.X := by rw [hP]
      _ = 1 - PowerSeries.C (β + b) * PowerSeries.X := by
        simp only [D, map_add]
        ring
  have hD : D ≠ 0 := by
    intro hzero
    have hconstant := congrArg PowerSeries.constantCoeff hzero
    simp [D] at hconstant
  have hQR : Q * R = P := by
    apply mul_right_cancel₀ hD
    calc
      Q * R * D = Q * (R * D) := by ring
      _ = Q * (1 - PowerSeries.C (β + b) * PowerSeries.X) := by rw [hRD]
      _ = PowerSeries.X := hQ
      _ = P * D := hP.symm
  have hR : R ≠ 0 := by
    intro hzero
    have hconstant := congrArg PowerSeries.constantCoeff hzero
    simp [R, P] at hconstant
  apply mul_right_cancel₀ hR
  exact hsub.trans hQR.symm

/-- Prepending an atom multiplies the prefactor by its formal exponential. -/
theorem translationLahPrefactorSeries_cons
    (u a : ℝ) (atoms : List (ℝ × ℝ)) :
    translationLahPrefactorSeries ((u, a) :: atoms) =
      translationLahPrefactorSeries atoms *
        (PowerSeries.exp ℝ).subst
          (PowerSeries.C a * translationLahSubstitutionSeries u) := by
  rw [translationLahPrefactorSeries, translationLahPrefactorSeries,
    translationLahLogSeries_cons]
  apply subst_exp_add
  · exact constantCoeff_translationLahLogSeries atoms
  · simp

private def basisTransformSeries
    (Q : ℕ → ℝ[X]) (F : PowerSeries ℝ[X]) : PowerSeries ℝ[X] :=
  PowerSeries.mk fun n => basisTransform Q (PowerSeries.coeff n F)

private theorem polynomialRowEGF_basisTransform
    (Q P : ℕ → ℝ[X]) :
    polynomialRowEGF (fun n => basisTransform Q (P n)) =
      basisTransformSeries Q (polynomialRowEGF P) := by
  apply PowerSeries.ext
  intro n
  simp only [polynomialRowEGF, basisTransformSeries, PowerSeries.coeff_mk]
  simpa [Polynomial.smul_eq_C_mul] using
    (basisTransform_smul Q ((n.factorial : ℝ)⁻¹) (P n)).symm

private theorem basisTransformSeries_map_mul
    (Q : ℕ → ℝ[X]) (A : PowerSeries ℝ) (F : PowerSeries ℝ[X]) :
    basisTransformSeries Q (A.map C * F) =
      A.map C * basisTransformSeries Q F := by
  apply PowerSeries.ext
  intro n
  simp only [basisTransformSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    PowerSeries.coeff_map]
  rw [basisTransform_finset_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simpa [Polynomial.smul_eq_C_mul] using
    basisTransform_smul Q (PowerSeries.coeff x.1 A)
      (PowerSeries.coeff x.2 F)

private theorem basisTransformSeries_exp_subst
    (Q : ℕ → ℝ[X]) (B : PowerSeries ℝ)
    (hB : PowerSeries.constantCoeff B = 0) :
    basisTransformSeries Q
        ((PowerSeries.exp ℝ[X]).subst
          (PowerSeries.C X * B.map C)) =
      (polynomialRowEGF Q).subst (B.map C) := by
  have hBmap : PowerSeries.constantCoeff (B.map C) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hB, map_zero]
  have hinner : PowerSeries.constantCoeff
      (PowerSeries.C X * B.map C) = 0 := by
    rw [map_mul, hBmap, mul_zero]
  have hBsubst : PowerSeries.HasSubst (B.map C) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hBmap
  have hinnersubst : PowerSeries.HasSubst
      (PowerSeries.C X * B.map C) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hinner
  apply PowerSeries.ext
  intro n
  simp only [basisTransformSeries, PowerSeries.coeff_mk]
  rw [PowerSeries.coeff_subst' hinnersubst,
    PowerSeries.coeff_subst' hBsubst]
  change (basisTransformₗ Q).toAddMonoidHom (∑ᶠ d : ℕ,
      PowerSeries.coeff d (PowerSeries.exp ℝ[X]) •
        PowerSeries.coeff n ((PowerSeries.C X * B.map C) ^ d)) = _
  rw [AddMonoidHom.map_finsum (basisTransformₗ Q).toAddMonoidHom
    (PowerSeries.coeff_subst_finite' hinnersubst (PowerSeries.exp ℝ[X]) n)]
  apply finsum_congr
  intro d
  simp only [PowerSeries.coeff_exp, polynomialRowEGF,
    PowerSeries.coeff_mk]
  rw [mul_pow, ← map_pow, PowerSeries.coeff_C_mul,
    ← map_pow, PowerSeries.coeff_map]
  have hrat : (algebraMap ℚ ℝ[X]) (1 / (d.factorial : ℚ)) =
      C ((d.factorial : ℝ)⁻¹) := by
    change (algebraMap ℚ ℝ[X]) (1 / (d.factorial : ℚ)) =
      (algebraMap ℝ ℝ[X]) ((d.factorial : ℝ)⁻¹)
    rw [IsScalarTower.algebraMap_apply ℚ ℝ ℝ[X]]
    congr 1
    norm_num
  rw [hrat]
  simp only [smul_eq_mul]
  change basisTransform Q
      (C ((d.factorial : ℝ)⁻¹) *
        (X ^ d * C (PowerSeries.coeff n (B ^ d)))) = _
  rw [show C ((d.factorial : ℝ)⁻¹) *
      (X ^ d * C (PowerSeries.coeff n (B ^ d))) =
      C ((d.factorial : ℝ)⁻¹ * PowerSeries.coeff n (B ^ d)) * X ^ d by
    rw [map_mul]
    ring, basisTransform_C_mul_X_pow, map_mul]
  ring

private theorem polynomialRowEGF_basisTransform_of_comp
    (Q P : ℕ → ℝ[X]) (A D B E : PowerSeries ℝ)
    (hB : PowerSeries.constantCoeff B = 0)
    (hE : PowerSeries.constantCoeff E = 0)
    (hP : polynomialRowEGF P =
      A.map C * (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C))
    (hQ : polynomialRowEGF Q =
      D.map C * (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * E.map C)) :
    polynomialRowEGF (fun n => basisTransform Q (P n)) =
      (A * D.subst B).map C *
        (PowerSeries.exp ℝ[X]).subst
          (PowerSeries.C X * (E.subst B).map C) := by
  have hBmap : PowerSeries.constantCoeff (B.map C) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hB, map_zero]
  have hEmap : PowerSeries.constantCoeff (E.map C) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hE, map_zero]
  have hinner : PowerSeries.constantCoeff
      (PowerSeries.C X * E.map C) = 0 := by
    rw [map_mul, hEmap, mul_zero]
  have hBsubst : PowerSeries.HasSubst (B.map C) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hBmap
  have hinnersubst : PowerSeries.HasSubst
      (PowerSeries.C X * E.map C) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hinner
  have hmapD : (D.map C).subst (B.map C) = (D.subst B).map C := by
    symm
    exact PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' hB) D
  have hmapE : (E.map C).subst (B.map C) = (E.subst B).map C := by
    symm
    exact PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' hB) E
  rw [polynomialRowEGF_basisTransform, hP,
    basisTransformSeries_map_mul,
    basisTransformSeries_exp_subst Q B hB, hQ]
  rw [PowerSeries.subst_mul hBsubst, hmapD]
  rw [PowerSeries.subst_comp_subst_apply hinnersubst hBsubst]
  rw [PowerSeries.subst_mul hBsubst, PowerSeries.subst_C,
    hmapE, map_mul]
  rw [show (MvPowerSeries.C X : PowerSeries ℝ[X]) =
    PowerSeries.C X by rfl]
  exact (mul_assoc _ _ _).symm

private theorem raySemigroupBasis_translation (a : ℝ) (n : ℕ) :
    raySemigroupBasis a 0 1 n = (X + C a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [raySemigroupBasis_succ, ih]
      simp only [zero_mul, add_zero, one_mul, map_zero]
      ring

private theorem polynomialRowEGF_raySemigroupBasis_translation (a : ℝ) :
    polynomialRowEGF (raySemigroupBasis a 0 1) =
      PowerSeries.rescale (X + C a) (PowerSeries.exp ℝ[X]) := by
  apply PowerSeries.ext
  intro n
  simp [polynomialRowEGF, raySemigroupBasis_translation,
    PowerSeries.coeff_rescale]
  ring

private theorem basisTransform_derivative_monomials (p : ℝ[X]) :
    basisTransform (fun n : ℕ => ((X : ℝ[X]) ^ n).derivative) p =
      p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [basisTransform_add, derivative_add, hp, hq]
  | monomial n a =>
      rw [basisTransform_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
        derivative_mul, derivative_C, zero_mul, zero_add]

private theorem polynomialRowEGF_derivative_monomials :
    polynomialRowEGF (fun n : ℕ => ((X : ℝ[X]) ^ n).derivative) =
      PowerSeries.X * PowerSeries.rescale X (PowerSeries.exp ℝ[X]) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [polynomialRowEGF]
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_rescale]
      simp only [polynomialRowEGF, PowerSeries.coeff_mk,
        PowerSeries.coeff_exp, derivative_pow, Nat.cast_add, Nat.cast_one]
      have hfactorial : ((n + 1).factorial : ℝ) =
          (n + 1 : ℝ) * (n.factorial : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hrat : (algebraMap ℚ ℝ[X]) (1 / (n.factorial : ℚ)) =
          C ((n.factorial : ℝ)⁻¹) := by
        change (algebraMap ℚ ℝ[X]) (1 / (n.factorial : ℚ)) =
          (algebraMap ℝ ℝ[X]) ((n.factorial : ℝ)⁻¹)
        rw [IsScalarTower.algebraMap_apply ℚ ℝ ℝ[X]]
        congr 1
        norm_num
      rw [hfactorial]
      rw [hrat]
      simp only [derivative_X, mul_one, Nat.succ_sub_one]
      rw [show C (((n + 1 : ℝ) * (n.factorial : ℝ))⁻¹) *
          (C (n + 1 : ℝ) * X ^ n) =
          (C (((n + 1 : ℝ) * (n.factorial : ℝ))⁻¹) *
            C (n + 1 : ℝ)) * X ^ n by ring]
      rw [← map_mul]
      rw [show (((n + 1 : ℝ) * (n.factorial : ℝ))⁻¹ * (n + 1 : ℝ)) =
          (n.factorial : ℝ)⁻¹ by
        field_simp]
      ring

private theorem basisTransformSeries_derivative_exp_subst
    (B : PowerSeries ℝ) (hB : PowerSeries.constantCoeff B = 0) :
    basisTransformSeries
        (fun n : ℕ => ((X : ℝ[X]) ^ n).derivative)
        ((PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C)) =
      B.map C *
        (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C) := by
  have hBmap : PowerSeries.constantCoeff (B.map C) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hB, map_zero]
  have hBsubst : PowerSeries.HasSubst (B.map C) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hBmap
  rw [basisTransformSeries_exp_subst _ B hB,
    polynomialRowEGF_derivative_monomials]
  rw [PowerSeries.subst_mul hBsubst, PowerSeries.subst_X hBsubst]
  rw [PowerSeries.rescale_eq_subst]
  rw [PowerSeries.smul_eq_C_mul]
  have hlinear : PowerSeries.HasSubst
      (PowerSeries.C X * PowerSeries.X : PowerSeries ℝ[X]) :=
    PowerSeries.HasSubst.X'.mul_right
  rw [PowerSeries.subst_comp_subst_apply hlinear hBsubst]
  rw [PowerSeries.subst_mul hBsubst, PowerSeries.subst_C,
    PowerSeries.subst_X hBsubst]
  rfl

private theorem derivative_translationLahSubstitutionSeries (b : ℝ) :
    PowerSeries.derivative (translationLahSubstitutionSeries b) =
      1 + PowerSeries.C b * translationLahSubstitutionSeries b +
        PowerSeries.C b * PowerSeries.X *
          PowerSeries.derivative (translationLahSubstitutionSeries b) := by
  rw [show PowerSeries.C b * PowerSeries.X *
      PowerSeries.derivative (translationLahSubstitutionSeries b) =
      PowerSeries.C b * (PowerSeries.X *
        PowerSeries.derivative (translationLahSubstitutionSeries b)) by ring]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [PowerSeries.coeff_derivative,
        coeff_translationLahSubstitutionSeries_succ]
  | succ n =>
      rw [PowerSeries.coeff_derivative]
      simp [coeff_translationLahSubstitutionSeries_succ,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, pow_succ]
      ring

private theorem derivative_map_C (B : PowerSeries ℝ) :
    PowerSeries.derivative (B.map C) =
      (PowerSeries.derivative B).map C := by
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.coeff_derivative]

private theorem derivative_exp_subst_translationLahSubstitutionSeries (b : ℝ) :
    let B := translationLahSubstitutionSeries b
    let F := (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C)
    PowerSeries.derivative F =
      PowerSeries.C X * F +
        PowerSeries.C (C b) * PowerSeries.X * PowerSeries.derivative F +
          PowerSeries.C (C b * X) * (B.map C * F) := by
  dsimp only
  let B := translationLahSubstitutionSeries b
  let F := (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C)
  have hBmap : PowerSeries.constantCoeff (B.map C) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [B]
  have hinner : PowerSeries.HasSubst (PowerSeries.C X * B.map C) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    rw [map_mul, hBmap, mul_zero]
  have hderinner : PowerSeries.derivative (PowerSeries.C X * B.map C) =
      PowerSeries.C X * (PowerSeries.derivative B).map C := by
    apply PowerSeries.ext
    intro n
    simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map,
      PowerSeries.coeff_C_mul]
  have hchain : PowerSeries.derivative F =
      F * (PowerSeries.C X * (PowerSeries.derivative B).map C) := by
    dsimp only [F]
    rw [PowerSeries.derivative_subst hinner, PowerSeries.derivative_exp,
      hderinner]
  have hDB := congrArg (PowerSeries.map C)
    (derivative_translationLahSubstitutionSeries b)
  change PowerSeries.derivative F = _
  simp only [map_add, map_mul, map_one, PowerSeries.map_C,
    PowerSeries.map_X] at hDB
  have hbX : PowerSeries.C (C b * X) =
      PowerSeries.C (C b) * PowerSeries.C X := by
    rw [map_mul]
  calc
    PowerSeries.derivative F =
        F * (PowerSeries.C X * (PowerSeries.derivative B).map C) := hchain
    _ = F * (PowerSeries.C X *
        (1 + PowerSeries.C (C b) * B.map C +
          PowerSeries.C (C b) * PowerSeries.X *
            (PowerSeries.derivative B).map C)) := by
      exact congrArg
        (fun G => F * (PowerSeries.C X * G)) hDB
    _ = PowerSeries.C X * F +
        PowerSeries.C (C b) * PowerSeries.X *
          (F * (PowerSeries.C X * (PowerSeries.derivative B).map C)) +
        PowerSeries.C (C b * X) * (B.map C * F) := by
      rw [hbX]
      ring
    _ = PowerSeries.C X * F +
        PowerSeries.C (C b) * PowerSeries.X * PowerSeries.derivative F +
          PowerSeries.C (C b * X) * (B.map C * F) := by
      rw [hchain]

private theorem coeff_mul_exp_subst_translationLahSubstitutionSeries
    (b : ℝ) (n : ℕ) :
    let B := translationLahSubstitutionSeries b
    let F := (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C)
    PowerSeries.coeff n (B.map C * F) =
      (PowerSeries.coeff n F).derivative := by
  dsimp only
  have h := congrArg (PowerSeries.coeff n)
    (basisTransformSeries_derivative_exp_subst
      (translationLahSubstitutionSeries b)
      (constantCoeff_translationLahSubstitutionSeries b))
  simp only [basisTransformSeries, PowerSeries.coeff_mk] at h
  rw [basisTransform_derivative_monomials] at h
  exact h.symm

private theorem coeff_succ_exp_subst_translationLahSubstitutionSeries
    (b : ℝ) (n : ℕ) :
    let B := translationLahSubstitutionSeries b
    let F := (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C)
    C (n + 1 : ℝ) * PowerSeries.coeff (n + 1) F =
      (X + C (b * n)) * PowerSeries.coeff n F +
        C b * X * (PowerSeries.coeff n F).derivative := by
  dsimp only
  let B := translationLahSubstitutionSeries b
  let F := (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C)
  have hode := derivative_exp_subst_translationLahSubstitutionSeries b
  change PowerSeries.derivative F = _ at hode
  rw [show PowerSeries.C (C b) * PowerSeries.X * PowerSeries.derivative F =
      PowerSeries.C (C b) *
        (PowerSeries.X * PowerSeries.derivative F) by ring] at hode
  rw [show PowerSeries.C (C b * X) =
      PowerSeries.C (C b) * PowerSeries.C X by
    rw [map_mul]] at hode
  rw [show PowerSeries.C (C b) * PowerSeries.C X * (B.map C * F) =
      PowerSeries.C (C b) *
        (PowerSeries.C X * (B.map C * F)) by ring] at hode
  have hcoeff := congrArg (PowerSeries.coeff n) hode
  dsimp only [F, B] at hcoeff
  have hpoly := coeff_mul_exp_subst_translationLahSubstitutionSeries b n
  change PowerSeries.coeff n (B.map C * F) = _ at hpoly
  cases n with
  | zero =>
      simp only [map_add, PowerSeries.coeff_C_mul] at hcoeff
      rw [hpoly] at hcoeff
      simp [PowerSeries.coeff_derivative] at hcoeff ⊢
      simpa only [mul_assoc] using hcoeff
  | succ n =>
      simp only [map_add, PowerSeries.coeff_C_mul] at hcoeff
      rw [hpoly] at hcoeff
      simp [PowerSeries.coeff_derivative,
        PowerSeries.coeff_succ_X_mul] at hcoeff ⊢
      ring_nf at hcoeff ⊢
      exact hcoeff

private theorem raySemigroupBasis_lah_eq_coeff (b : ℝ) (n : ℕ) :
    let B := translationLahSubstitutionSeries b
    let F := (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C)
    raySemigroupBasis 0 b 1 n = C (n.factorial : ℝ) * PowerSeries.coeff n F := by
  dsimp only
  let B := translationLahSubstitutionSeries b
  let F := (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C)
  change raySemigroupBasis 0 b 1 n =
    C (n.factorial : ℝ) * PowerSeries.coeff n F
  induction n with
  | zero =>
      have hBmap : PowerSeries.constantCoeff (B.map C) = 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_map,
          PowerSeries.coeff_zero_eq_constantCoeff_apply]
        simp [B]
      have hinner : PowerSeries.constantCoeff (PowerSeries.C X * B.map C) = 0 := by
        rw [map_mul, hBmap, mul_zero]
      have hconst : PowerSeries.constantCoeff F = 1 := by
        dsimp only [F]
        rw [PowerSeries.constantCoeff_eq,
          PowerSeries.constantCoeff_subst_of_constantCoeff_zero hinner]
        simp
      simp [raySemigroupBasis, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        hconst]
  | succ n ih =>
      have hrec :=
        coeff_succ_exp_subst_translationLahSubstitutionSeries b n
      change C (n + 1 : ℝ) * PowerSeries.coeff (n + 1) F = _ at hrec
      rw [raySemigroupBasis_succ, ih]
      simp only [zero_add, one_mul, mul_one]
      rw [derivative_mul, derivative_C, zero_mul, zero_add]
      calc
        (X + C (b * n)) * (C (n.factorial : ℝ) * PowerSeries.coeff n F) +
            C b * X * (C (n.factorial : ℝ) *
              (PowerSeries.coeff n F).derivative) =
            C (n.factorial : ℝ) *
              ((X + C (b * n)) * PowerSeries.coeff n F +
                C b * X * (PowerSeries.coeff n F).derivative) := by ring
        _ = C (n.factorial : ℝ) *
            (C (n + 1 : ℝ) * PowerSeries.coeff (n + 1) F) := by rw [hrec]
        _ = C ((n + 1).factorial : ℝ) * PowerSeries.coeff (n + 1) F := by
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
            map_mul]
          ring

private theorem polynomialRowEGF_raySemigroupBasis_lah (b : ℝ) :
    polynomialRowEGF (raySemigroupBasis 0 b 1) =
      (PowerSeries.exp ℝ[X]).subst
        (PowerSeries.C X * (translationLahSubstitutionSeries b).map C) := by
  apply PowerSeries.ext
  intro n
  rw [polynomialRowEGF, PowerSeries.coeff_mk,
    raySemigroupBasis_lah_eq_coeff]
  rw [← mul_assoc, ← map_mul]
  rw [show (n.factorial : ℝ)⁻¹ * (n.factorial : ℝ) = 1 by
    exact inv_mul_cancel₀ (by positivity)]
  simp

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

/-- A single translation generator has the expected atomic EGF. -/
theorem hasTranslationLahEGF_translation (a : ℝ) :
    HasTranslationLahEGF
      (raySemigroupBasis a 0 1) 0 [(0, a)] := by
  unfold HasTranslationLahEGF
  rw [polynomialRowEGF_raySemigroupBasis_translation,
    translationLahPrefactorSeries_cons,
    translationLahPrefactorSeries_nil,
    translationLahSubstitutionSeries_zero]
  simp only [one_mul, PowerSeries.map_X]
  rw [← PowerSeries.smul_eq_C_mul, ← PowerSeries.rescale_eq_subst,
    ← PowerSeries.rescale_map]
  rw [← PowerSeries.smul_eq_C_mul, ← PowerSeries.rescale_eq_subst]
  simpa [add_comm] using
    (PowerSeries.exp_mul_exp_eq_exp_add (C a) X).symm

/-- A single Lah generator has substitution series `z / (1 - b z)`. -/
theorem hasTranslationLahEGF_lah (b : ℝ) :
    HasTranslationLahEGF (raySemigroupBasis 0 b 1) b [] := by
  unfold HasTranslationLahEGF
  rw [polynomialRowEGF_raySemigroupBasis_lah,
    translationLahPrefactorSeries_nil]
  simp

/-- Prepending a translation generator inserts an atom at the current Lah
time in the EGF data. -/
theorem HasTranslationLahEGF.translation_cons
    {P : ℕ → ℝ[X]} {β : ℝ} {atoms : List (ℝ × ℝ)}
    (h : HasTranslationLahEGF P β atoms) (a : ℝ) :
    HasTranslationLahEGF
      (fun n => basisTransform (raySemigroupBasis a 0 1) (P n))
      β ((β, a) :: atoms) := by
  have hcomp := polynomialRowEGF_basisTransform_of_comp
    (raySemigroupBasis a 0 1) P
    (translationLahPrefactorSeries atoms)
    (translationLahPrefactorSeries [(0, a)])
    (translationLahSubstitutionSeries β)
    (translationLahSubstitutionSeries 0)
    (constantCoeff_translationLahSubstitutionSeries β)
    (constantCoeff_translationLahSubstitutionSeries 0)
    h (hasTranslationLahEGF_translation a)
  have hD :
      (translationLahPrefactorSeries [(0, a)]).subst
          (translationLahSubstitutionSeries β) =
        (PowerSeries.exp ℝ).subst
          (PowerSeries.C a * translationLahSubstitutionSeries β) := by
    rw [translationLahPrefactorSeries_cons,
      translationLahPrefactorSeries_nil,
      translationLahSubstitutionSeries_zero, one_mul]
    have hβsubst : PowerSeries.HasSubst
        (translationLahSubstitutionSeries β) :=
      PowerSeries.HasSubst.of_constantCoeff_zero'
        (constantCoeff_translationLahSubstitutionSeries β)
    have hlinear : PowerSeries.HasSubst
        (PowerSeries.C a * PowerSeries.X) := by
      apply PowerSeries.HasSubst.of_constantCoeff_zero'
      simp
    rw [PowerSeries.subst_comp_subst_apply hlinear hβsubst,
      PowerSeries.subst_mul hβsubst, PowerSeries.subst_C,
      PowerSeries.subst_X hβsubst]
    rfl
  unfold HasTranslationLahEGF
  rw [translationLahPrefactorSeries_cons, ← hD]
  have hzeroSub :
      (translationLahSubstitutionSeries 0).subst
          (translationLahSubstitutionSeries β) =
        translationLahSubstitutionSeries β := by
    rw [translationLahSubstitutionSeries_zero,
      PowerSeries.subst_X]
    exact PowerSeries.HasSubst.of_constantCoeff_zero'
      (constantCoeff_translationLahSubstitutionSeries β)
  rw [hzeroSub] at hcomp
  exact hcomp

/-- Prepending a Lah generator composes the substitution series and adds its
parameter to the current Lah time. -/
theorem HasTranslationLahEGF.lah_cons
    {P : ℕ → ℝ[X]} {β : ℝ} {atoms : List (ℝ × ℝ)}
    (h : HasTranslationLahEGF P β atoms) (b : ℝ) :
    HasTranslationLahEGF
      (fun n => basisTransform (raySemigroupBasis 0 b 1) (P n))
      (β + b) atoms := by
  have hcomp := polynomialRowEGF_basisTransform_of_comp
    (raySemigroupBasis 0 b 1) P
    (translationLahPrefactorSeries atoms)
    (translationLahPrefactorSeries [])
    (translationLahSubstitutionSeries β)
    (translationLahSubstitutionSeries b)
    (constantCoeff_translationLahSubstitutionSeries β)
    (constantCoeff_translationLahSubstitutionSeries b)
    h (hasTranslationLahEGF_lah b)
  unfold HasTranslationLahEGF
  rw [translationLahPrefactorSeries_nil] at hcomp
  have hβsubst : PowerSeries.HasSubst
      (translationLahSubstitutionSeries β) :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (constantCoeff_translationLahSubstitutionSeries β)
  have hone : (1 : PowerSeries ℝ).subst
      (translationLahSubstitutionSeries β) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hβsubst, map_one]
  rw [hone] at hcomp
  simp only [mul_one] at hcomp
  rw [translationLahSubstitutionSeries_subst] at hcomp
  rw [show (MvPowerSeries.map C)
      (translationLahSubstitutionSeries (β + b)) =
      (PowerSeries.map C) (translationLahSubstitutionSeries (β + b)) by rfl]
    at hcomp
  exact hcomp

/-- Every finite translation--Lah word, hence every valid nonempty word, has
the EGF determined by its total Lah time and translation atoms. -/
theorem hasTranslationLahEGF_word (w : List TranslationLahGenerator) :
    HasTranslationLahEGF (translationLahWordBasis w)
      (translationLahWordBeta w) (translationLahWordAtoms w) := by
  induction w with
  | nil => exact hasTranslationLahEGF_nil
  | cons g w ih =>
      cases g with
      | translation a =>
          simpa [translationLahWordBasis, translationLahWordBeta,
            translationLahWordAtoms, TranslationLahGenerator.basis] using
            ih.translation_cons a
      | lah b =>
          simpa [translationLahWordBasis, translationLahWordBeta,
            translationLahWordAtoms, TranslationLahGenerator.basis] using
            ih.lah_cons b

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
