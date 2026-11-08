module

public import RealRooted.FiniteFreeAdditive.FiniteDegreeTests
public import RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests
public import RealRooted.GarloffWagner.KreinData
public import Mathlib.RingTheory.Polynomial.Vieta
import RealRooted.GarloffWagner.Theorem12
import RealRooted.GarloffWagner.KreinExpansion
import RealRooted.Interlacing.QuadraticPFPreservers
import RealRooted.LinearPowerFamily
import RealRooted.Mathlib.Algebra.Polynomial.Coeff
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.ElementarySymmetric
import RealRooted.OperatorMatrix.Directed

/-!
# Companions and multishift finite-degree differential recurrences

This file develops the multishift extension of the finite-degree differential
tests and records the reusable affine-row consequences.
-/

public section

open Polynomial BigOperators

noncomputable section

namespace RealRooted

open HermitePoulain
open FiniteDegreeOrdered

private theorem isPFPolynomial_applyAsDifferentialOperator
    {h p : ℝ[X]} (hh : IsPFPolynomial h) (hp : IsPFPolynomial p) :
    IsPFPolynomial (applyAsDifferentialOperator h p) := by
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
  · rw [applyAsDifferentialOperator]
    apply hasNonnegCoeffs_finsetSum
    intro j _
    exact (hasNonnegCoeffs_C (hh.hasNonnegCoeffs j)).mul
      (hp.hasNonnegCoeffs.iterate_derivative j)
  · by_cases hh0 : h = 0
    · simp [hh0, applyAsDifferentialOperator]
    by_cases hp0 : p = 0
    · simp [hp0, applyAsDifferentialOperator]
    exact differential_operator_preserves_real_rooted
      (hh.ne_zero_and_splits hh0) (hp.ne_zero_and_splits hp0)

/-- A nonnegative expansion in the parent polynomial and its one-root-deleted
Krein summands. -/
def HasKreinCompanionExpansion (h k : ℝ[X]) : Prop :=
  ∃ l : List (ℝ × ℝ[X]),
    k = weightedSum l ∧
      (∀ ap ∈ l, 0 ≤ ap.1) ∧
      ∀ ap ∈ l, IsKreinSummand h ap.2

/-- For a fixed nonzero PF parent, its ordered PF cone is exactly its
nonnegative Krein-summand cone. -/
theorem isPFPolynomial_and_interl_iff_hasKreinCompanionExpansion
    {h k : ℝ[X]} (hh : IsPFPolynomial h) (hh0 : h ≠ 0) :
    IsPFPolynomial k ∧ Interl k h ↔ HasKreinCompanionExpansion h k := by
  constructor
  · rintro ⟨hk, hkh⟩
    rcases hkh with hk0 | hhzero | hstrict
    · subst k
      exact ⟨[], by simp, by simp, by simp⟩
    · exact False.elim (hh0 hhzero)
    · have hkpos := hk.hasNonnegCoeffs.pos_leadingCoeff hstrict.1.1
      have hhpos := hh.hasNonnegCoeffs.pos_leadingCoeff hh0
      rcases StrictInterl.exists_kreinSummandExpansion hstrict hkpos hhpos with
        ⟨l, heq, hnonneg, hsummand, _⟩
      exact ⟨l, heq, hnonneg, hsummand⟩
  · rintro ⟨l, rfl, hnonneg, hsummand⟩
    have hqpf : ∀ ap ∈ l, IsPFPolynomial ap.2 :=
      fun ap hap ↦ (hsummand ap hap).isPFPolynomial hh
    have hnn : HasNonnegCoeffs (weightedSum l) :=
      HasNonnegCoeffs.weightedSum l hnonneg
        (fun ap hap ↦ (hqpf ap hap).hasNonnegCoeffs)
    have horder : Interl (weightedSum l) h :=
      interl_weightedSum_right_of_nonneg l h hnonneg
        (fun ap hap ↦ (hsummand ap hap).interl hh0 (hh.ne_zero_and_splits hh0).2)
        (fun ap hap ↦ (hqpf ap hap).hasNonnegCoeffs)
    refine ⟨?_, horder⟩
    apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hnn
    rcases horder with hzero | hhzero | hstrict
    · exact Or.inl hzero
    · exact False.elim (hh0 hhzero)
    · exact Or.inr hstrict.1.2

private theorem applyAsDifferentialOperator_weightedSum
    (l : List (ℝ × ℝ[X])) (p : ℝ[X]) :
    applyAsDifferentialOperator (weightedSum l) p =
      weightedSum (l.map fun ap ↦
        (ap.1, applyAsDifferentialOperator ap.2 p)) := by
  induction l with
  | nil => simp [applyAsDifferentialOperator]
  | cons ap l ih =>
      rcases ap with ⟨a, q⟩
      simp only [weightedSum_cons, List.map_cons]
      rw [applyAsDifferentialOperator_add,
        applyAsDifferentialOperator_C_mul, ih]

private theorem kreinSummand_image_ordered
    {h q p : ℝ[X]} (hh : IsPFPolynomial h) (hh0 : h ≠ 0)
    (hq : IsKreinSummand h q) (hp : IsPFPolynomial p) :
    IsPFPolynomial (applyAsDifferentialOperator q p) ∧
      Interl (applyAsDifferentialOperator h p)
        (applyAsDifferentialOperator q p) := by
  have hqpf := hq.isPFPolynomial hh
  have hqimage := isPFPolynomial_applyAsDifferentialOperator hqpf hp
  refine ⟨hqimage, ?_⟩
  rcases hq with rfl | ⟨u, hfactor⟩
  · exact hqimage.interl_self
  · have hu : h.IsRoot u := by
      rw [hfactor]
      simp
    have huroot : u ∈ h.roots := (mem_roots hh0).mpr hu
    have hunonpos : u ≤ 0 := hh.roots_nonpos u huroot
    have hinterl := hqimage.interl_affineDerivative_self (neg_nonneg.mpr hunonpos)
    rw [hfactor, applyAsDifferentialOperator_mul,
      show X - C u = X + C (-u) by rw [C_neg]; ring,
      applyAsDifferentialOperator_X_add_C]
    simpa [affineDerivative] using hinterl

/-- Every nonnegative root-deletion expansion yields ordered PF images on
every PF input, including annihilated images. -/
theorem HasKreinCompanionExpansion.preservesOrderedPF
    {h k : ℝ[X]} (hh : IsPFPolynomial h) (hh0 : h ≠ 0)
    (hk : HasKreinCompanionExpansion h k) {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial (applyAsDifferentialOperator h p) ∧
      IsPFPolynomial (applyAsDifferentialOperator k p) ∧
      Interl (applyAsDifferentialOperator h p)
        (applyAsDifferentialOperator k p) := by
  have hkpf : IsPFPolynomial k :=
    ((isPFPolynomial_and_interl_iff_hasKreinCompanionExpansion hh hh0).mpr hk).1
  have hkimage := isPFPolynomial_applyAsDifferentialOperator hkpf hp
  rcases hk with ⟨l, rfl, hnonneg, hsummand⟩
  let f := applyAsDifferentialOperator h p
  let images := l.map fun ap ↦ (ap.1, applyAsDifferentialOperator ap.2 p)
  have hf : IsPFPolynomial f := isPFPolynomial_applyAsDifferentialOperator hh hp
  have himage : ∀ ap ∈ l,
      IsPFPolynomial (applyAsDifferentialOperator ap.2 p) ∧
        Interl f (applyAsDifferentialOperator ap.2 p) := by
    intro ap hap
    exact kreinSummand_image_ordered hh hh0 (hsummand ap hap) hp
  have himages_nonneg : ∀ ap ∈ images, 0 ≤ ap.1 := by
    rintro ⟨a, q⟩ hap
    rcases List.mem_map.mp hap with ⟨ap, hap, heq⟩
    simp only [Prod.mk.injEq] at heq
    rw [← heq.1]
    exact hnonneg ap hap
  have himages_pf : ∀ ap ∈ images, IsPFPolynomial ap.2 := by
    intro ap hap
    rcases List.mem_map.mp hap with ⟨source, hsource, rfl⟩
    exact (himage source hsource).1
  have hinterl : Interl f (weightedSum images) := by
    rw [weightedSum_eq_sum_map]
    apply Interl.sum_left_of_common_left_of_nonneg
    · intro q hq
      rcases List.mem_map.mp hq with ⟨ap, hap, rfl⟩
      rcases List.mem_map.mp hap with ⟨source, hsource, rfl⟩
      exact (himage source hsource).2.C_mul_right_of_nonneg
        (hnonneg source hsource)
    · intro q hq
      rcases List.mem_map.mp hq with ⟨ap, hap, rfl⟩
      exact hasNonnegCoeffs_C_mul (himages_nonneg ap hap)
        (himages_pf ap hap).hasNonnegCoeffs
  rw [applyAsDifferentialOperator_weightedSum] at hkimage ⊢
  exact ⟨hf, hkimage, hinterl⟩

private theorem IsPFPolynomial.const_mul_nonneg {p : ℝ[X]}
    (hp : IsPFPolynomial p) {a : ℝ} (ha : 0 ≤ a) :
    IsPFPolynomial (C a * p) := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using IsPFPolynomial.zero
  · exact hp.const_mul ha

private theorem isPFPolynomial_nonneg_combo_of_interl
    {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfg : Interl f g) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsPFPolynomial (C a * f + C b * g) := by
  exact (hf.const_mul_nonneg ha).add_of_interl (hg.const_mul_nonneg hb)
    ((hfg.C_mul_left_of_nonneg ha).C_mul_right_of_nonneg hb)

/-- A nonnegative two-by-two change of coordinates with the indicated cross
inequality preserves the directed order of a PF pair. -/
theorem interl_nonneg_combos_of_cross
    {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfg : Interl f g) {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcross : a * d ≤ b * c) :
    Interl (C b * f + C d * g) (C a * f + C c * g) := by
  by_cases hb0 : b = 0
  · subst b
    have had : a * d = 0 := by nlinarith
    rcases mul_eq_zero.mp had with ha0 | hd0
    · subst a
      have hself := hg.interl_self
      simpa using
        (hself.C_mul_left_of_nonneg hd).C_mul_right_of_nonneg hc
    · subst d
      simpa using interl_zero_left (C a * f + C c * g)
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    let q := C b * f + C d * g
    have hq : IsPFPolynomial q :=
      isPFPolynomial_nonneg_combo_of_interl hf hg hfg hb hd
    have hqg : Interl q g := by
      apply interl_add_left_of_common_right_of_nonneg
      · exact hfg.C_mul_left_of_nonneg hb
      · exact hg.interl_self.C_mul_left_of_nonneg hd
      · exact hasNonnegCoeffs_C_mul hb hf.hasNonnegCoeffs
      · exact hasNonnegCoeffs_C_mul hd hg.hasNonnegCoeffs
    have hresidue : 0 ≤ (b * c - a * d) / b :=
      div_nonneg (sub_nonneg.mpr hcross) hb
    have hcombo := interl_nonneg_combo_right_of_common_left_of_pf
      hq.interl_self hqg hq hg (div_nonneg ha hb) hresidue
    convert hcombo using 1
    ext n
    simp only [q, coeff_add, coeff_C_mul]
    field_simp
    ring

/-- The determinant-condition affine row is PF and is preceded by its
leading-coefficient row. -/
theorem affineDifferentialRow_pf_and_interl
    {h k p : ℝ[X]}
    (hh : IsPFPolynomial (applyAsDifferentialOperator h p))
    (hk : IsPFPolynomial (applyAsDifferentialOperator k p))
    (horder : Interl (applyAsDifferentialOperator h p)
      (applyAsDifferentialOperator k p))
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcross : a * d ≤ b * c) :
    let lead :=
      C b * applyAsDifferentialOperator h p +
        C d * applyAsDifferentialOperator k p
    let row :=
      (C a + C b * X) * applyAsDifferentialOperator h p +
        (C c + C d * X) * applyAsDifferentialOperator k p
    IsPFPolynomial row ∧ Interl lead row := by
  let f := applyAsDifferentialOperator h p
  let g := applyAsDifferentialOperator k p
  let lead := C b * f + C d * g
  let rest := C a * f + C c * g
  have hlead : IsPFPolynomial lead :=
    isPFPolynomial_nonneg_combo_of_interl hh hk horder hb hd
  have hrest : IsPFPolynomial rest :=
    isPFPolynomial_nonneg_combo_of_interl hh hk horder ha hc
  have hleadrest : Interl lead rest :=
    interl_nonneg_combos_of_cross hh hk horder ha hb hc hd hcross
  have hpf := isPFPolynomial_X_mul_add_C_mul hlead hrest hleadrest zero_le_one
  have hinterl := interl_X_mul_add_C_mul hlead hrest hleadrest zero_le_one
  dsimp only
  change IsPFPolynomial
      ((C a + C b * X) * f + (C c + C d * X) * g) ∧
    Interl lead ((C a + C b * X) * f + (C c + C d * X) * g)
  have hrow :
      (C a + C b * X) * f + (C c + C d * X) * g = X * lead + C 1 * rest := by
    dsimp [lead, rest]
    simp only [C_1, one_mul]
    ring
  rw [hrow]
  exact ⟨hpf, hinterl⟩

/-- The Jensen polynomial attached to a finite vector of nonnegative shifts. -/
def multishiftJensenPolynomial {r : ℕ} (s : Fin r → ℝ) : ℝ[X] :=
  ∏ i, (1 + C (s i) * X)

/-- The multishift differential symbol obtained by inverse Jensen normalization. -/
def multishiftDifferentialSymbol (N : ℕ) {r : ℕ} (s : Fin r → ℝ) : ℝ[X] :=
  capNormalizedDifferentialSymbol N (multishiftJensenPolynomial s)

/-- The shifts viewed as a multiset, retaining multiplicities. -/
def shiftMultiset {r : ℕ} (s : Fin r → ℝ) : Multiset ℝ :=
  (List.ofFn s : Multiset ℝ)

private theorem shiftMultiset_cons {r : ℕ} (a : ℝ) (s : Fin r → ℝ) :
    shiftMultiset (Fin.cons a s) = a ::ₘ shiftMultiset s := by
  simp [shiftMultiset, List.ofFn_succ]

/-- The coefficient of the multishift Jensen polynomial is the corresponding
elementary symmetric function of the shifts. -/
theorem coeff_multishiftJensenPolynomial {r : ℕ} (s : Fin r → ℝ) (j : ℕ) :
    (multishiftJensenPolynomial s).coeff j = (shiftMultiset s).esymm j := by
  induction r generalizing j with
  | zero =>
      rcases j with _ | j
      · simp [multishiftJensenPolynomial, shiftMultiset, Multiset.esymm]
      · rw [Multiset.esymm_of_card_lt (by simp [shiftMultiset])]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [multishiftJensenPolynomial]
        change (1 : ℝ[X]).natDegree < j + 1
        simp
  | succ r ih =>
      rw [multishiftJensenPolynomial, Fin.prod_univ_succ]
      change ((1 + C (s 0) * X) *
        multishiftJensenPolynomial (fun i ↦ s i.succ)).coeff j = _
      have hmultiset : shiftMultiset s =
          s 0 ::ₘ shiftMultiset (fun i ↦ s i.succ) := by
        rw [show s = Fin.cons (s 0) (fun i ↦ s i.succ) from
          (Fin.cons_self_tail s).symm]
        exact shiftMultiset_cons (s 0) (fun i ↦ s i.succ)
      rw [hmultiset]
      rcases j with _ | j
      · rw [Polynomial.coeff_zero_eq_eval_zero]
        simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
          Polynomial.eval_C, Polynomial.eval_X, mul_zero, add_zero, one_mul,
          Multiset.esymm_zero]
        simpa [Polynomial.coeff_zero_eq_eval_zero] using
          ih (fun i : Fin r ↦ s i.succ) 0
      · rw [coeff_one_add_C_mul_X_mul_succ, ih, ih, Multiset.esymm_cons]

/-- The multishift symbol has the advertised elementary-symmetric coefficients. -/
theorem coeff_multishiftDifferentialSymbol
    (N : ℕ) {r : ℕ} (s : Fin r → ℝ) (j : ℕ) :
    (multishiftDifferentialSymbol N s).coeff j =
      (N.descFactorial j : ℝ)⁻¹ * (shiftMultiset s).esymm j := by
  rw [multishiftDifferentialSymbol, coeff_capNormalizedDifferentialSymbol,
    coeff_multishiftJensenPolynomial]

/-- The symbol of the empty shift vector is the identity differential symbol. -/
theorem multishiftDifferentialSymbol_empty (N : ℕ) :
    multishiftDifferentialSymbol N (fun i : Fin 0 ↦ Fin.elim0 i) = 1 := by
  ext j
  rw [coeff_multishiftDifferentialSymbol]
  rcases j with _ | j
  · simp [shiftMultiset, Multiset.esymm]
  · rw [Multiset.esymm_of_card_lt (by simp [shiftMultiset])]
    simp [Polynomial.coeff_one]

/-- The empty-shift recurrence is multiplication by `X`, hence is PF and is
preceded by its input. -/
theorem emptyMultishiftRecurrence_pf_and_interl {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial
        (X * applyAsDifferentialOperator
          (multishiftDifferentialSymbol 0 (fun i : Fin 0 ↦ Fin.elim0 i)) p) ∧
      Interl
        (applyAsDifferentialOperator
          (multishiftDifferentialSymbol 0 (fun i : Fin 0 ↦ Fin.elim0 i)) p)
        (X * applyAsDifferentialOperator
          (multishiftDifferentialSymbol 0 (fun i : Fin 0 ↦ Fin.elim0 i)) p) := by
  rw [multishiftDifferentialSymbol_empty, applyAsDifferentialOperator_one]
  exact ⟨hp.X_mul, (interl_iff_interl_X_mul hp hp).mp hp.interl_self⟩

private theorem natDegree_multishiftJensenPolynomial_le
    {r : ℕ} (s : Fin r → ℝ) :
    (multishiftJensenPolynomial s).natDegree ≤ r := by
  rw [multishiftJensenPolynomial]
  calc
    (∏ i, (1 + C (s i) * X)).natDegree ≤
        ∑ i, (1 + C (s i) * X : ℝ[X]).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin r, 1 := Finset.sum_le_sum fun i _ ↦ by
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)))
    _ = r := by simp

/-- Jensen normalization recovers the product of the affine shift factors. -/
theorem jensenDifferentialTest_multishiftDifferentialSymbol
    {N r : ℕ} (s : Fin r → ℝ) (hrN : r ≤ N) :
    jensenDifferentialTest N (multishiftDifferentialSymbol N s) =
      multishiftJensenPolynomial s := by
  exact jensenDifferentialTest_capNormalizedDifferentialSymbol N _
    ((natDegree_multishiftJensenPolynomial_le s).trans hrN)

private theorem reflect_multishiftJensenPolynomial
    {r : ℕ} (s : Fin r → ℝ) :
    reflect r (multishiftJensenPolynomial s) = ∏ i, (X + C (s i)) := by
  induction r with
  | zero => simp [multishiftJensenPolynomial, Polynomial.reflect_one]
  | succ r ih =>
      rw [multishiftJensenPolynomial, Fin.prod_univ_succ]
      rw [Fin.prod_univ_succ]
      change reflect (r + 1)
          ((1 + C (s 0) * X) *
            multishiftJensenPolynomial (fun i : Fin r ↦ s i.succ)) =
        (X + C (s 0)) * ∏ i : Fin r, (X + C (s i.succ))
      have hreindex :
          reflect (r + 1)
              ((1 + C (s 0) * X) *
                multishiftJensenPolynomial (fun i : Fin r ↦ s i.succ)) =
            reflect (1 + r)
              ((1 + C (s 0) * X) *
                multishiftJensenPolynomial (fun i : Fin r ↦ s i.succ)) :=
        congrArg (fun n ↦ reflect n
          ((1 + C (s 0) * X) *
            multishiftJensenPolynomial (fun i : Fin r ↦ s i.succ))) (by lia)
      rw [hreindex]
      rw [Polynomial.reflect_mul _ _
          (by
            exact (Polynomial.natDegree_add_le _ _).trans
              (max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))))
          (natDegree_multishiftJensenPolynomial_le (fun i : Fin r ↦ s i.succ))]
      have hlinear : reflect 1 (1 + C (s 0) * X : ℝ[X]) = X + C (s 0) := by
        ext j
        rcases j with _ | j
        · simp
        · rcases j with _ | j <;> simp
      rw [hlinear]
      rw [ih]

/-- The monomial image of the multishift symbol is
`X ^ (N - r) * ∏ i, (X + s i)`. -/
theorem differentialTest_multishiftDifferentialSymbol
    {N r : ℕ} (s : Fin r → ℝ) (hrN : r ≤ N) :
    finiteDifferentialTest N (multishiftDifferentialSymbol N s) =
      X ^ (N - r) * ∏ i, (X + C (s i)) := by
  have h := congrArg (reflect N)
    (jensenDifferentialTest_multishiftDifferentialSymbol s hrN)
  rw [jensenDifferentialTest, Polynomial.reflect_reflect] at h
  rw [h]
  calc
    reflect N (multishiftJensenPolynomial s) =
        reflect (r + (N - r)) (multishiftJensenPolynomial s * 1) := by
      rw [Nat.add_sub_of_le hrN, mul_one]
    _ = reflect r (multishiftJensenPolynomial s) * reflect (N - r) 1 := by
      rw [Polynomial.reflect_mul _ _
        (natDegree_multishiftJensenPolynomial_le s) (by simp)]
    _ = X ^ (N - r) * ∏ i, (X + C (s i)) := by
      rw [reflect_multishiftJensenPolynomial, Polynomial.reflect_one]
      ring

/-- A multishift Jensen polynomial with nonnegative shifts is PF. -/
theorem isPFPolynomial_multishiftJensenPolynomial
    {r : ℕ} {s : Fin r → ℝ} (hs : ∀ i, 0 ≤ s i) :
    IsPFPolynomial (multishiftJensenPolynomial s) := by
  rw [multishiftJensenPolynomial]
  induction (Finset.univ : Finset (Fin r)) using Finset.induction with
  | empty => simpa using IsPFPolynomial.one
  | @insert i t hi ih =>
      rw [Finset.prod_insert hi]
      exact (show IsPFPolynomial (1 + C (s i) * X) by
        rw [add_comm]; exact isPFPolynomial_C_mul_X_add_one (hs i)).mul ih

/-- The full multishift Jensen polynomial is the deleted product times its
indexed affine factor. -/
theorem multishiftJensenPolynomial_eq_factor_mul_removeNth
    {r : ℕ} (s : Fin (r + 1) → ℝ) (i : Fin (r + 1)) :
    multishiftJensenPolynomial s =
      (1 + C (s i) * X) * multishiftJensenPolynomial (Fin.removeNth i s) := by
  simpa [multishiftJensenPolynomial, Fin.removeNth] using
    Fin.prod_univ_succAbove (fun j ↦ (1 + C (s j) * X : ℝ[X])) i

/-- Deleting one nonnegative shift gives a Jensen polynomial preceding the
full product. -/
theorem interl_multishiftJensenPolynomial_removeNth
    {r : ℕ} {s : Fin (r + 1) → ℝ} (hs : ∀ i, 0 ≤ s i)
    (i : Fin (r + 1)) :
    Interl (multishiftJensenPolynomial (Fin.removeNth i s))
      (multishiftJensenPolynomial s) := by
  let q := multishiftJensenPolynomial (Fin.removeNth i s)
  have hqpf : IsPFPolynomial q :=
    isPFPolynomial_multishiftJensenPolynomial fun j ↦ hs (i.succAbove j)
  rcases (hs i).eq_or_lt with hzero | hpos
  · rw [multishiftJensenPolynomial_eq_factor_mul_removeNth (s := s) i,
      hzero.symm]
    simpa [q] using hqpf.interl_self
  · have hq0 : q ≠ 0 := by
      intro hzero
      have hcoeff := congrArg (fun p : ℝ[X] ↦ p.coeff 0) hzero
      rw [coeff_multishiftJensenPolynomial, Polynomial.coeff_zero] at hcoeff
      simp [shiftMultiset] at hcoeff
    have hstep := interlaces_self_mul_C_add_C_mul_X_of_nonnegCoeffs
      hq0 hqpf.splits hqpf.hasNonnegCoeffs
      zero_le_one hpos
    rw [multishiftJensenPolynomial_eq_factor_mul_removeNth (s := s) i]
    simpa [q, add_comm] using hstep.toStrictInterl.toInterl

/-- The full and one-shift-deleted multishift symbols give ordered PF images
through their common degree cap. -/
theorem preservesOrderedPFUpTo_multishift_removeNth
    {N r : ℕ} {s : Fin (r + 1) → ℝ} (hrN : r + 1 ≤ N)
    (hs : ∀ i, 0 ≤ s i) (i : Fin (r + 1)) :
    PreservesOrderedPFUpTo N (multishiftDifferentialSymbol N s)
      (multishiftDifferentialSymbol N (Fin.removeNth i s)) := by
  apply (preservesOrderedPFUpTo_iff_jensenDifferentialTests N _ _).mpr
  rw [jensenDifferentialTest_multishiftDifferentialSymbol s hrN,
    jensenDifferentialTest_multishiftDifferentialSymbol (Fin.removeNth i s) (by lia)]
  exact ⟨isPFPolynomial_multishiftJensenPolynomial hs,
    isPFPolynomial_multishiftJensenPolynomial fun j ↦ hs (i.succAbove j),
    interl_multishiftJensenPolynomial_removeNth hs i⟩

private theorem coeff_zero_multishiftDifferentialSymbol
    (N : ℕ) {r : ℕ} (s : Fin r → ℝ) :
    (multishiftDifferentialSymbol N s).coeff 0 = 1 := by
  rw [coeff_multishiftDifferentialSymbol]
  simp [shiftMultiset, Multiset.esymm]

/-- The multishift recurrence row with arbitrary nonnegative deletion weights. -/
def multishiftDifferentialRecurrence
    (N : ℕ) {r : ℕ} (s a : Fin (r + 1) → ℝ) (p : ℝ[X]) : ℝ[X] :=
  X * applyAsDifferentialOperator (multishiftDifferentialSymbol N s) p +
    ∑ i, C (a i) * applyAsDifferentialOperator
      (multishiftDifferentialSymbol N (Fin.removeNth i s)) p

/-- The multishift recurrence is PF and is preceded by its full-symbol image. -/
theorem multishiftDifferentialRecurrence_pf_and_interl
    {N r : ℕ} {s a : Fin (r + 1) → ℝ}
    (hrN : r + 1 ≤ N) (hs : ∀ i, 0 ≤ s i) (ha : ∀ i, 0 ≤ a i)
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hpdeg : p.natDegree ≤ N) :
    IsPFPolynomial (multishiftDifferentialRecurrence N s a p) ∧
      Interl
        (applyAsDifferentialOperator (multishiftDifferentialSymbol N s) p)
        (multishiftDifferentialRecurrence N s a p) := by
  let f := applyAsDifferentialOperator (multishiftDifferentialSymbol N s) p
  let g : Fin (r + 1) → ℝ[X] := fun i ↦
    C (a i) * applyAsDifferentialOperator
      (multishiftDifferentialSymbol N (Fin.removeNth i s)) p
  have hpair : ∀ i, IsPFPolynomial f ∧
      IsPFPolynomial (applyAsDifferentialOperator
        (multishiftDifferentialSymbol N (Fin.removeNth i s)) p) ∧
      Interl f (applyAsDifferentialOperator
        (multishiftDifferentialSymbol N (Fin.removeNth i s)) p) := by
    intro i
    exact preservesOrderedPFUpTo_multishift_removeNth hrN hs i hp hpdeg
  have hf : IsPFPolynomial f := (hpair 0).1
  have hgpf : ∀ i, IsPFPolynomial (g i) := by
    intro i
    rcases (ha i).eq_or_lt with hzero | hpos
    · have hai : a i = 0 := hzero.symm
      change IsPFPolynomial (C (a i) * _)
      rw [hai]
      simpa using IsPFPolynomial.zero
    · exact (hpair i).2.1.const_mul hpos
  have hfg : Interl f (∑ i, g i) := by
    apply Interl.finsetSum_left_of_nonneg f Finset.univ g
    · intro i _
      exact Interl.C_mul_right_of_nonneg (hpair i).2.2 (ha i)
    · intro i _
      exact (hgpf i).hasNonnegCoeffs
  have hgsum : IsPFPolynomial (∑ i, g i) := by
    apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    · exact hasNonnegCoeffs_finsetSum Finset.univ g
        fun i _ ↦ (hgpf i).hasNonnegCoeffs
    · by_cases hp0 : p = 0
      · subst p
        simp [g]
      · have hf0 : f ≠ 0 :=
          applyAsDifferentialOperator_ne_zero_of_coeff_zero_eq_one
            (coeff_zero_multishiftDifferentialSymbol N s) hp0
        rcases hfg with hzero | hzero | hstrict
        · exact False.elim (hf0 hzero)
        · exact Or.inl hzero
        · exact Or.inr hstrict.2.1.2
  have hout := isPFPolynomial_X_mul_add_C_mul hf hgsum hfg zero_le_one
  have hinterl := interl_X_mul_add_C_mul hf hgsum hfg zero_le_one
  simpa [multishiftDifferentialRecurrence, f, g] using And.intro hout hinterl

/-- For a nonzero input, every multishift recurrence raises the degree by one. -/
theorem natDegree_multishiftDifferentialRecurrence
    {N r : ℕ} {s a : Fin (r + 1) → ℝ} {p : ℝ[X]} (hp0 : p ≠ 0) :
    (multishiftDifferentialRecurrence N s a p).natDegree = p.natDegree + 1 := by
  let f := applyAsDifferentialOperator (multishiftDifferentialSymbol N s) p
  let g : Fin (r + 1) → ℝ[X] := fun i ↦
    C (a i) * applyAsDifferentialOperator
      (multishiftDifferentialSymbol N (Fin.removeNth i s)) p
  have hf0 : f ≠ 0 :=
    applyAsDifferentialOperator_ne_zero_of_coeff_zero_eq_one
      (coeff_zero_multishiftDifferentialSymbol N s) hp0
  have hfdeg : f.natDegree = p.natDegree :=
    natDegree_applyAsDifferentialOperator_of_coeff_zero_eq_one
      (coeff_zero_multishiftDifferentialSymbol N s) hp0
  have hleft : (X * f).natDegree = p.natDegree + 1 := by
    rw [Polynomial.natDegree_X_mul hf0, hfdeg]
  have hright : (∑ i, g i).natDegree ≤ p.natDegree := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (natDegree_applyAsDifferentialOperator_le _ _)
  rw [multishiftDifferentialRecurrence]
  change (X * f + ∑ i, g i).natDegree = _
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt
    (hright.trans_lt (by rw [hleft]; lia)), hleft]

/-- Induction wrapper for degree-capped multishift recurrences with arbitrary
nonnegative parameters at every step. -/
theorem multishiftDifferentialRecurrence_induction
    {m : ℕ} {P : ℕ → ℝ[X]} {r : ℕ → ℕ}
    {s a : (n : ℕ) → Fin (r n + 1) → ℝ}
    (hseed : IsPFPolynomial (P m)) (hseeddeg : (P m).natDegree ≤ m)
    (hr : ∀ n, m ≤ n → r n + 1 ≤ n)
    (hs : ∀ n i, 0 ≤ s n i) (ha : ∀ n i, 0 ≤ a n i)
    (hrec : ∀ n, m ≤ n →
      P (n + 1) = multishiftDifferentialRecurrence n (s n) (a n) (P n)) :
    ∀ n, m ≤ n → IsPFPolynomial (P n) ∧ (P n).natDegree ≤ n := by
  intro n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => simpa using And.intro hseed hseeddeg
  | succ k ih =>
      have hmk : m ≤ m + k := by lia
      rw [show m + (k + 1) = (m + k) + 1 by lia, hrec (m + k) hmk]
      have hout := multishiftDifferentialRecurrence_pf_and_interl
        (hr (m + k) hmk) (hs (m + k)) (ha (m + k)) (ih hmk).1 (ih hmk).2
      refine ⟨hout.1, ?_⟩
      by_cases hzero : P (m + k) = 0
      · simp [hzero, multishiftDifferentialRecurrence]
      · rw [natDegree_multishiftDifferentialRecurrence hzero]
        lia

end RealRooted
