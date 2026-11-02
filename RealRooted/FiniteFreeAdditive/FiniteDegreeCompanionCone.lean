module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Basic.Real.Basic
public import RealRooted.PFPolynomial
public import RealRooted.FiniteFreeAdditive.FiniteDegreeTests
public import RealRooted.Basic.ProperPosition
public import Mathlib.Data.Nat.Factorial.Basic
import RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions
import RealRooted.Mathlib.Analysis.SpecialFunctions.Choose
import RealRooted.PFPolynomial.Closure
import RealRooted.Linear

/-!
# Explicit finite-degree companion cones

This file refines the companion expansion by distinct roots and closes the
all-degree implication by coefficientwise limits of finite-degree tests.
-/

public section

open BigOperators Filter Polynomial Topology

noncomputable section

namespace RealRooted

open HermitePoulain
open FiniteDegreeOrdered

/-- The Jensen test rescaled by `X \mapsto X / N`. -/
def rescaledJensenDifferentialTest (N : ℕ) (h : ℝ[X]) : ℝ[X] :=
  (jensenDifferentialTest N h).comp (C (N : ℝ)⁻¹ * X)

/-- Below the cap, rescaled Jensen coefficients are the symbol coefficients
multiplied by `(N)_j / N^j`. -/
theorem coeff_rescaledJensenDifferentialTest_of_le
    (N : ℕ) (h : ℝ[X]) {j : ℕ} (hj : j ≤ N) :
    (rescaledJensenDifferentialTest N h).coeff j =
      (N.descFactorial j : ℝ) / (N : ℝ) ^ j * h.coeff j := by
  rw [rescaledJensenDifferentialTest, Polynomial.comp_C_mul_X_coeff,
    coeff_jensenDifferentialTest_of_le N h hj]
  ring

private theorem natDegree_rescaledJensenDifferentialTest_le
    (N : ℕ) (h : ℝ[X]) :
    (rescaledJensenDifferentialTest N h).natDegree ≤ h.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  by_cases hjN : j ≤ N
  · rw [coeff_rescaledJensenDifferentialTest_of_le N h hjN,
      coeff_eq_zero_of_natDegree_lt hj, mul_zero]
  · have hNlt : N < j := Nat.lt_of_not_ge hjN
    apply coeff_eq_zero_of_natDegree_lt
    apply Polynomial.natDegree_comp_le.trans_lt
    have hinner : (C (N : ℝ)⁻¹ * X).natDegree ≤ 1 :=
      (Polynomial.natDegree_C_mul_le _ X).trans Polynomial.natDegree_X_le
    have houter : (jensenDifferentialTest N h).natDegree ≤ N := by
      rw [jensenDifferentialTest]
      exact Polynomial.natDegree_reflect_le.trans
        (max_le le_rfl (natDegree_finiteDifferentialTest_le N h))
    nlinarith [Nat.zero_le (jensenDifferentialTest N h).natDegree]

private theorem tendsto_coeff_rescaledJensenDifferentialTest_add
    (D : ℕ) (h : ℝ[X]) (j : ℕ) :
    Tendsto
      (fun n : ℕ => (rescaledJensenDifferentialTest (n + D + 1) h).coeff j)
      atTop (nhds (h.coeff j)) := by
  have hjcap : ∀ᶠ n : ℕ in atTop, j ≤ n + D + 1 := by
    filter_upwards [eventually_ge_atTop j] with n hn
    lia
  rw [show h.coeff j = 1 * h.coeff j by simp]
  have ht := ((Nat.tendsto_descFactorial_div_pow_atTop j).comp
    (tendsto_add_atTop_nat (D + 1))).mul_const (h.coeff j)
  apply ht.congr'
  filter_upwards [hjcap] with n hn
  rw [coeff_rescaledJensenDifferentialTest_of_le _ h hn]
  simp [Nat.add_assoc]

/-- If the two differential operators give ordered PF images on every PF
input, then their symbols are PF and have the reversed weak interlacing order. -/
theorem isPFPolynomial_and_interl_of_forall_differential_images
    {h k : ℝ[X]}
    (hpres : ∀ p : ℝ[X], IsPFPolynomial p →
      IsPFPolynomial (applyAsDifferentialOperator h p) ∧
        IsPFPolynomial (applyAsDifferentialOperator k p) ∧
          Interl (applyAsDifferentialOperator h p)
            (applyAsDifferentialOperator k p)) :
    IsPFPolynomial k ∧ Interl k h := by
  let D := max h.natDegree k.natDegree
  let cap : ℕ → ℕ := fun n => n + D + 1
  have hcap_pos (n : ℕ) : 0 < cap n := by
    dsimp [cap]
    lia
  have htests (n : ℕ) :
      IsPFPolynomial (jensenDifferentialTest (cap n) h) ∧
        IsPFPolynomial (jensenDifferentialTest (cap n) k) ∧
          Interl (jensenDifferentialTest (cap n) k)
            (jensenDifferentialTest (cap n) h) := by
    apply (preservesOrderedPFUpTo_iff_jensenDifferentialTests
      (cap n) h k).mp
    intro p hp _
    exact hpres p hp
  have hscale_pos (n : ℕ) : 0 < (cap n : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast hcap_pos n)
  have hhpf (n : ℕ) :
      IsPFPolynomial (rescaledJensenDifferentialTest (cap n) h) := by
    simpa [rescaledJensenDifferentialTest] using
      (htests n).1.comp_C_mul_X_add_C (hscale_pos n) le_rfl
  have hkpf (n : ℕ) :
      IsPFPolynomial (rescaledJensenDifferentialTest (cap n) k) := by
    simpa [rescaledJensenDifferentialTest] using
      (htests n).2.1.comp_C_mul_X_add_C (hscale_pos n) le_rfl
  have horder (n : ℕ) :
      Interl (rescaledJensenDifferentialTest (cap n) k)
        (rescaledJensenDifferentialTest (cap n) h) := by
    exact (htests n).2.2.comp_C_mul_X (hscale_pos n)
  have hhcoeff (j : ℕ) : Tendsto
      (fun n => (rescaledJensenDifferentialTest (cap n) h).coeff j)
      atTop (nhds (h.coeff j)) :=
    tendsto_coeff_rescaledJensenDifferentialTest_add D h j
  have hkcoeff (j : ℕ) : Tendsto
      (fun n => (rescaledJensenDifferentialTest (cap n) k).coeff j)
      atTop (nhds (k.coeff j)) :=
    tendsto_coeff_rescaledJensenDifferentialTest_add D k j
  refine ⟨IsPFPolynomial.of_coeff_tendsto hkpf hkcoeff, ?_⟩
  apply interl_of_pf_coeff_tendsto_of_natDegree_le (N := D) hkpf hhpf horder
    (fun n => (natDegree_rescaledJensenDifferentialTest_le (cap n) k).trans
      (le_max_right _ _))
    (fun n => (natDegree_rescaledJensenDifferentialTest_le (cap n) h).trans
      (le_max_left _ _))
    hkcoeff hhcoeff

/-- For a nonzero PF parent symbol, ordered PF images on every PF input are
equivalent to the reversed PF/interlacing condition on the symbols. -/
theorem forall_differential_images_iff_isPFPolynomial_and_interl
    {h k : ℝ[X]} (hh : IsPFPolynomial h) (hh0 : h ≠ 0) :
    (∀ p : ℝ[X], IsPFPolynomial p →
      IsPFPolynomial (applyAsDifferentialOperator h p) ∧
        IsPFPolynomial (applyAsDifferentialOperator k p) ∧
          Interl (applyAsDifferentialOperator h p)
            (applyAsDifferentialOperator k p)) ↔
      IsPFPolynomial k ∧ Interl k h := by
  constructor
  · exact isPFPolynomial_and_interl_of_forall_differential_images
  · intro hk p hp
    apply HasKreinCompanionExpansion.preservesOrderedPF hh hh0 _ hp
    exact (isPFPolynomial_and_interl_iff_hasKreinCompanionExpansion
      hh hh0).mp hk

/-- The finite-cap companion cone: the parent Jensen test is PF, and either it
vanishes or the child Jensen test has a nonnegative Krein expansion in it. -/
def HasFiniteCapCompanionCone (N : ℕ) (h k : ℝ[X]) : Prop :=
  IsPFPolynomial (jensenDifferentialTest N h) ∧
    if jensenDifferentialTest N h = 0 then
      IsPFPolynomial (jensenDifferentialTest N k)
    else
      HasKreinCompanionExpansion (jensenDifferentialTest N h)
        (jensenDifferentialTest N k)

/-- Ordered PF preservation through a finite cap is equivalent to membership
in the finite-cap companion cone. -/
theorem preservesOrderedPFUpTo_iff_hasFiniteCapCompanionCone
    (N : ℕ) (h k : ℝ[X]) :
    PreservesOrderedPFUpTo N h k ↔ HasFiniteCapCompanionCone N h k := by
  rw [preservesOrderedPFUpTo_iff_jensenDifferentialTests]
  let H := jensenDifferentialTest N h
  let K := jensenDifferentialTest N k
  change
    (IsPFPolynomial H ∧ IsPFPolynomial K ∧ Interl K H) ↔
      IsPFPolynomial H ∧ if H = 0 then IsPFPolynomial K
        else HasKreinCompanionExpansion H K
  constructor
  · rintro ⟨hH, hK, horder⟩
    refine ⟨hH, ?_⟩
    split
    · exact hK
    · rename_i hH0
      exact (isPFPolynomial_and_interl_iff_hasKreinCompanionExpansion
        hH hH0).mp ⟨hK, horder⟩
  · rintro ⟨hH, hcone⟩
    by_cases hH0 : H = 0
    · simp only [hH0, ↓reduceIte] at hcone
      refine ⟨hH, hcone, ?_⟩
      rw [hH0]
      exact interl_zero_right K
    · simp only [hH0, ↓reduceIte] at hcone
      rcases (isPFPolynomial_and_interl_iff_hasKreinCompanionExpansion
        hH hH0).mpr hcone with ⟨hK, horder⟩
      exact ⟨hH, hK, horder⟩

/-- The sum with one coefficient for each distinct root of the parent. -/
def distinctRootCompanionTail (h : ℝ[X]) (w : ℝ → ℝ) : ℝ[X] :=
  ∑ u ∈ h.roots.toFinset,
    C (w u) * (h /ₘ (X - C u))

/-- The canonical companion combination with one parent coefficient and one
coefficient for every distinct root. -/
def distinctRootCompanionCombination
    (h : ℝ[X]) (alpha : ℝ) (w : ℝ → ℝ) : ℝ[X] :=
  C alpha * h + distinctRootCompanionTail h w

/-- A nonnegative canonical companion expansion, indexed once by every
distinct root of the parent. -/
def HasDistinctRootCompanionExpansion (h k : ℝ[X]) : Prop :=
  ∃ alpha : ℝ, ∃ w : ℝ → ℝ,
    0 ≤ alpha ∧
      (∀ u ∈ h.roots.toFinset, 0 ≤ w u) ∧
        k = distinctRootCompanionCombination h alpha w

private theorem natDegree_distinctRootCompanionTail_lt
    {h : ℝ[X]} (hh0 : h ≠ 0) (hhdeg : 0 < h.natDegree) (w : ℝ → ℝ) :
    (distinctRootCompanionTail h w).natDegree < h.natDegree := by
  apply lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le h.roots.toFinset
      (fun u => C (w u) * (h /ₘ (X - C u))) (fun u hu => ?_))
    (Nat.pred_lt hhdeg.ne')
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  exact Nat.le_pred_of_lt (natDegree_lt_of_kreinDeleted_factor hh0 <|
    (mul_divByMonic_eq_iff_isRoot.mpr <|
      (mem_roots hh0).mp (Multiset.mem_toFinset.mp hu)).symm)

private theorem parentCoefficient_eq_of_distinctRootCombination_eq
    {h : ℝ[X]} (hh0 : h ≠ 0) {alpha beta : ℝ} {w v : ℝ → ℝ}
    (heq : distinctRootCompanionCombination h alpha w =
      distinctRootCompanionCombination h beta v) :
    alpha = beta := by
  by_cases hhdeg : h.natDegree = 0
  · have hC : h = C (h.coeff 0) := eq_C_of_natDegree_eq_zero hhdeg
    have hc0 : h.coeff 0 ≠ 0 := by
      intro hc0
      apply hh0
      rw [hC, hc0, C_0]
    have hroots : h.roots.toFinset = ∅ := by
      rw [hC]
      simp
    simp only [distinctRootCompanionCombination, distinctRootCompanionTail,
      hroots, Finset.sum_empty, add_zero] at heq
    have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) heq
    simp only [coeff_C_mul] at hcoeff
    exact mul_right_cancel₀ hc0 hcoeff
  · have hhdeg_pos : 0 < h.natDegree := Nat.pos_of_ne_zero hhdeg
    have hwdeg := natDegree_distinctRootCompanionTail_lt hh0 hhdeg_pos w
    have hvdeg := natDegree_distinctRootCompanionTail_lt hh0 hhdeg_pos v
    have hcoeff := congrArg (fun p : ℝ[X] => p.coeff h.natDegree) heq
    simp only [distinctRootCompanionCombination, coeff_add, coeff_C_mul] at hcoeff
    rw [coeff_eq_zero_of_natDegree_lt hwdeg,
      coeff_eq_zero_of_natDegree_lt hvdeg, add_zero] at hcoeff
    exact mul_right_cancel₀ (show h.coeff h.natDegree ≠ 0 from
      leadingCoeff_ne_zero.mpr hh0) (by simpa only [add_zero] using hcoeff)

private theorem scalar_eq_zero_of_fullRoot_dvd_deletedFactor
    {h q : ℝ[X]} (hh0 : h ≠ 0) {u c : ℝ}
    (hfactor : h = (X - C u) * q)
    (hdvd : (X - C u) ^ h.rootMultiplicity u ∣ C c * q) :
    c = 0 := by
  by_contra hc
  have hq0 : q ≠ 0 := by
    intro hq0
    apply hh0
    rw [hfactor, hq0, mul_zero]
  have hprod0 : (X - C u) * q ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero u) hq0
  have hcprod0 : C c * q ≠ 0 := mul_ne_zero (C_ne_zero.mpr hc) hq0
  have hle : h.rootMultiplicity u ≤ (C c * q).rootMultiplicity u :=
    (le_rootMultiplicity_iff hcprod0).mpr hdvd
  have hparent : h.rootMultiplicity u = 1 + q.rootMultiplicity u := by
    rw [hfactor, rootMultiplicity_mul hprod0, rootMultiplicity_X_sub_C_self]
  have hscalar : (C c * q).rootMultiplicity u = q.rootMultiplicity u := by
    rw [rootMultiplicity_mul hcprod0, rootMultiplicity_C, zero_add]
  rw [hparent, hscalar] at hle
  lia

private theorem fullRoot_dvd_distinctRootTail_erase
    {h : ℝ[X]} (hh0 : h ≠ 0) {u : ℝ}
    (w : ℝ → ℝ) :
    (X - C u) ^ h.rootMultiplicity u ∣
      ∑ x ∈ h.roots.toFinset.erase u,
        C (w x) * (h /ₘ (X - C x)) := by
  apply Finset.dvd_sum
  intro x hx
  have hxroots : x ∈ h.roots.toFinset :=
    Finset.mem_of_mem_erase hx
  have hxu : u ≠ x := (Finset.ne_of_mem_erase hx).symm
  apply dvd_mul_of_dvd_right _ (C (w x))
  exact kreinDeletedSummand_dvd_fullRootMultiplicity_of_ne hh0
    ((mul_divByMonic_eq_iff_isRoot.mpr <|
      (mem_roots hh0).mp (Multiset.mem_toFinset.mp hxroots)).symm) hxu

/-- In a canonical companion combination, the parent coefficient and all
coefficients indexed by distinct roots are unique. This includes repeated
roots: the deleted factor retains every remaining copy. -/
theorem distinctRootCompanionCoefficients_unique
    {h : ℝ[X]} (hh0 : h ≠ 0) {alpha beta : ℝ} {w v : ℝ → ℝ}
    (heq : distinctRootCompanionCombination h alpha w =
      distinctRootCompanionCombination h beta v) :
    alpha = beta ∧ ∀ u ∈ h.roots.toFinset, w u = v u := by
  have hab := parentCoefficient_eq_of_distinctRootCombination_eq hh0 heq
  subst beta
  refine ⟨rfl, ?_⟩
  have htail : distinctRootCompanionTail h w =
      distinctRootCompanionTail h v := by
    exact add_left_cancel heq
  intro u hu
  let q := h /ₘ (X - C u)
  have hroot : h.IsRoot u :=
    (mem_roots hh0).mp (Multiset.mem_toFinset.mp hu)
  have hfactor : h = (X - C u) * q :=
    (mul_divByMonic_eq_iff_isRoot.mpr hroot).symm
  have hisolate :
      C (w u) * q - C (v u) * q =
        (∑ x ∈ h.roots.toFinset.erase u,
          C (v x) * (h /ₘ (X - C x))) -
        ∑ x ∈ h.roots.toFinset.erase u,
          C (w x) * (h /ₘ (X - C x)) := by
    rw [distinctRootCompanionTail, distinctRootCompanionTail,
      ← Finset.add_sum_erase _ _ hu, ← Finset.add_sum_erase _ _ hu] at htail
    dsimp only [q]
    linear_combination htail
  have hdvd : (X - C u) ^ h.rootMultiplicity u ∣
      C (w u - v u) * q := by
    have hdiff := dvd_sub
      (fullRoot_dvd_distinctRootTail_erase hh0 (u := u) v)
      (fullRoot_dvd_distinctRootTail_erase hh0 (u := u) w)
    rw [← hisolate] at hdiff
    convert hdiff using 1
    rw [map_sub]
    ring
  have hzero : w u - v u = 0 :=
    scalar_eq_zero_of_fullRoot_dvd_deletedFactor hh0 hfactor hdvd
  linarith

end RealRooted
