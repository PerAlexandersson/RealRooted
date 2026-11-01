module

public import RealRooted.Laguerre.FiniteCombinations

import RealRooted.MaWang.StrictStep
import RealRooted.QuadraticInterlacingClosure
import RealRooted.Laguerre.Roots
import RealRooted.CommonInterleaver.RightPencil

/-!
# Generalized Bell steps for finite Laguerre combinations

This file formalizes the generalized Bell iteration used in Durán's criterion for fixed finite
combinations of monic Laguerre polynomials.  The sign-reversed iteration is built from the
first-order Laguerre raising step
`p ↦ (X + a) p + X p'`.

Reference: A. J. Durán, *Zeros of linear combinations of Laguerre polynomials*, Theorem 1.3,
arXiv:2507.22425.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The fixed auxiliary polynomial
`∑ j, (-1)^j γ_j (X)_(K-j)` in Durán's monic Laguerre criterion. -/
@[expose] noncomputable def laguerreAuxiliary (K : ℕ) (gamma : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (K + 1),
    C ((-1 : ℝ) ^ j * gamma j) * ascPochhammer ℝ (K - j)

/-- The fixed bandwidth-`K` combination of consecutive classical monic Laguerre polynomials. -/
@[expose] noncomputable def laguerreCombination
    (K : ℕ) (gamma : ℕ → ℝ) (n : ℕ) (alpha : ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (K + 1), C (gamma j) * monicLaguerre (n - j) alpha

/-- The auxiliary polynomial is monic when its leading coordinate is normalized by `γ₀ = 1`. -/
theorem laguerreAuxiliary_monic {K : ℕ} {gamma : ℕ → ℝ} (hgamma : gamma 0 = 1) :
    (laguerreAuxiliary K gamma).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one K
  · rw [laguerreAuxiliary]
    refine natDegree_sum_le_of_forall_le _ _ ?_
    intro j hj
    exact (natDegree_C_mul_le _ _).trans (by
      rw [ascPochhammer_natDegree]
      exact Nat.sub_le K j)
  · rw [laguerreAuxiliary]
    rw [finsetSum_coeff]
    simp only [coeff_C_mul]
    rw [Finset.sum_eq_single 0]
    · have htop := (monic_ascPochhammer (S := ℝ) K).coeff_natDegree
      rw [ascPochhammer_natDegree] at htop
      simpa [hgamma] using htop
    · intro j hj hj0
      simp only [Finset.mem_range] at hj
      rw [coeff_eq_zero_of_natDegree_lt (by
        rw [ascPochhammer_natDegree]
        lia)]
      simp
    · simp

/-- Iteration of the sign-reversed Laguerre raising step over a finite parameter list. -/
@[expose] noncomputable def laguerreRaisingSteps {R : Type*} [CommSemiring R] :
    List R → R[X] → R[X]
  | [], p => p
  | a :: as, p => laguerreRaisingStep a (laguerreRaisingSteps as p)

/-- A Laguerre raising step preserves coefficientwise nonnegativity when its parameter is
nonnegative. -/
theorem HasNonnegCoeffs.laguerreRaisingStep {a : ℝ} (ha : 0 ≤ a)
    {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (laguerreRaisingStep a p) := by
  intro k
  rw [coeff_laguerreRaisingStep]
  split_ifs with hk
  · subst k
    simpa using mul_nonneg ha (hp 0)
  · exact add_nonneg (hp (k - 1)) (mul_nonneg (by positivity) (hp k))

/-- The constant coefficient of a Laguerre raising step. -/
@[simp] theorem coeff_zero_laguerreRaisingStep {R : Type*} [CommSemiring R]
    (a : R) (p : R[X]) :
    (laguerreRaisingStep a p).coeff 0 = a * p.coeff 0 := by
  rw [coeff_laguerreRaisingStep]
  simp

private theorem laguerreRaisingStep_natDegree_le (a : ℝ) (p : ℝ[X]) :
    (laguerreRaisingStep a p).natDegree ≤ p.natDegree + 1 := by
  rw [laguerreRaisingStep]
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · calc
      ((X + C a) * p).natDegree ≤ (X + C a).natDegree + p.natDegree :=
        natDegree_mul_le
      _ ≤ 1 + p.natDegree := Nat.add_le_add (by simp) le_rfl
      _ = p.natDegree + 1 := Nat.add_comm _ _
  · calc
      (X * p.derivative).natDegree ≤ X.natDegree + p.derivative.natDegree :=
        natDegree_mul_le
      _ ≤ 1 + p.natDegree := Nat.add_le_add (by simp)
        (p.natDegree_derivative.le.trans (Nat.sub_le _ _))
      _ = p.natDegree + 1 := Nat.add_comm _ _

private theorem coeff_laguerreRaisingStep_natDegree_succ (a : ℝ) (p : ℝ[X]) :
    (laguerreRaisingStep a p).coeff (p.natDegree + 1) = p.leadingCoeff := by
  rw [coeff_laguerreRaisingStep]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, leadingCoeff]
  rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)]
  ring

/-- A Laguerre raising step sends a monic polynomial to a monic polynomial of successor degree. -/
theorem monic_laguerreRaisingStep (a : ℝ) {p : ℝ[X]} (hp : p.Monic) :
    (laguerreRaisingStep a p).Monic ∧
      (laguerreRaisingStep a p).natDegree = p.natDegree + 1 := by
  have hcoeff : (laguerreRaisingStep a p).coeff (p.natDegree + 1) = 1 := by
    rw [coeff_laguerreRaisingStep_natDegree_succ, hp.leadingCoeff]
  have hmonic := monic_of_natDegree_le_of_coeff_eq_one _
    (laguerreRaisingStep_natDegree_le a p) hcoeff
  have hdegree := natDegree_eq_of_le_of_coeff_ne_zero
    (laguerreRaisingStep_natDegree_le a p) (by simp [hcoeff])
  exact ⟨hmonic, hdegree⟩

/-- A Laguerre raising step strictly interlaces a nonconstant polynomial with simple
negative roots and has simple roots itself. -/
theorem strictInterl_and_hasSimpleRoots_laguerreRaisingStep
    (a : ℝ) {p : ℝ[X]} (hpdegree : 1 ≤ p.natDegree)
    (hpmonic : p.Monic) (hpsplits : p.Splits) (hpsimple : HasSimpleRoots p)
    (hpcoeff : HasNonnegCoeffs p) (hp0 : p.coeff 0 ≠ 0) :
    StrictInterl p (laguerreRaisingStep a p) ∧
      HasSimpleRoots (laguerreRaisingStep a p) := by
  have hmonic := monic_laguerreRaisingStep a hpmonic
  exact strictInterl_and_hasSimpleRoots_of_interlaces_eval_mul_neg_succ
    hpsplits (hasPosLeadingCoeff_of_monic hpmonic)
    (hasPosLeadingCoeff_of_monic hmonic.1) hpdegree hmonic.2 hpsimple
    (u := X + C a) (v := X) (by simp [laguerreRaisingStep])
    (by
      intro r hr
      have hrmem : r ∈ p.roots := (mem_roots hpmonic.ne_zero).mpr hr
      simpa using roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hpcoeff hp0 r hrmem)

private theorem laguerreRaisingStep_package
    {a : ℝ} (ha : 0 < a) {p : ℝ[X]}
    (hpmonic : p.Monic) (hpsplits : p.Splits)
    (hpsimple : HasSimpleRoots p) (hpcoeff : HasNonnegCoeffs p)
    (hp0 : p.coeff 0 ≠ 0) :
    let q := laguerreRaisingStep a p
    q.Monic ∧ q.natDegree = p.natDegree + 1 ∧ q.Splits ∧
      HasSimpleRoots q ∧ HasNonnegCoeffs q ∧
      q.coeff 0 ≠ 0 ∧ ∀ r ∈ q.roots, r < 0 := by
  dsimp
  have hmonic := monic_laguerreRaisingStep a hpmonic
  have hcoeff := hpcoeff.laguerreRaisingStep ha.le
  have hzero : (laguerreRaisingStep a p).coeff 0 ≠ 0 := by
    rw [coeff_zero_laguerreRaisingStep]
    exact mul_ne_zero ha.ne' hp0
  have hneg := roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hcoeff hzero
  by_cases hdeg : p.natDegree = 0
  · have hpone := eq_one_of_monic_natDegree_zero hpmonic hdeg
    subst p
    have heq : laguerreRaisingStep a (1 : ℝ[X]) = X + C a := by
      simp [laguerreRaisingStep]
    rw [heq] at hmonic hcoeff hzero hneg ⊢
    have hsplits : (X + C a : ℝ[X]).Splits :=
      Polynomial.Splits.of_degree_le_one (by simp)
    have hsimple : HasSimpleRoots (X + C a : ℝ[X]) := by
      apply HasSimpleRoots.of_roots_nodup (by
        simpa [sub_eq_add_neg] using X_sub_C_ne_zero (-a))
      rw [show X + C a = X - C (-a) by simp [sub_eq_add_neg], roots_X_sub_C]
      simp
    exact ⟨hmonic.1, hmonic.2, hsplits, hsimple, hcoeff, hzero, hneg⟩
  · have hpair := strictInterl_and_hasSimpleRoots_laguerreRaisingStep
      a (by lia) hpmonic hpsplits hpsimple hpcoeff hp0
    exact ⟨hmonic.1, hmonic.2, hpair.1.2.1.2, hpair.2,
      hcoeff, hzero, hneg⟩

/-- Positive Laguerre raising parameters preserve monicity, splitting, simple negative roots,
coefficientwise nonnegativity, and a nonzero constant coefficient. -/
theorem laguerreRaisingSteps_splits_simple_roots_neg
    {as : List ℝ} (ha : ∀ a ∈ as, 0 < a) {p : ℝ[X]}
    (hpmonic : p.Monic) (hpsplits : p.Splits)
    (hpsimple : HasSimpleRoots p) (hpcoeff : HasNonnegCoeffs p)
    (hp0 : p.coeff 0 ≠ 0) :
    let q := laguerreRaisingSteps as p
    q.Monic ∧ q.natDegree = p.natDegree + as.length ∧ q.Splits ∧
      HasSimpleRoots q ∧ HasNonnegCoeffs q ∧ q.coeff 0 ≠ 0 ∧
      ∀ r ∈ q.roots, r < 0 := by
  induction as with
  | nil =>
      simp only [laguerreRaisingSteps, List.length_nil, Nat.add_zero]
      exact ⟨hpmonic, True.intro, hpsplits, hpsimple, hpcoeff, hp0,
        roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hpcoeff hp0⟩
  | cons a as ih =>
      have htail : ∀ b ∈ as, 0 < b := fun b hb ↦ ha b (by simp [hb])
      rcases ih htail with ⟨hm, hdeg, hs, hsimple, hcoeff, hzero, hneg⟩
      have hstep := laguerreRaisingStep_package (ha a (by simp)) hm hs hsimple hcoeff hzero
      simpa [laguerreRaisingSteps, hdeg, Nat.add_assoc] using hstep

private noncomputable def laguerreRaisingEndomorphism (a : ℝ) :
    Module.End ℝ ℝ[X] where
  toFun := laguerreRaisingStep a
  map_add' p q := by
    simp [laguerreRaisingStep]
    ring
  map_smul' c p := by
    simp [laguerreRaisingStep, smul_eq_C_mul]
    ring

@[simp] private theorem laguerreRaisingEndomorphism_apply (a : ℝ) (p : ℝ[X]) :
    laguerreRaisingEndomorphism a p = laguerreRaisingStep a p :=
  rfl

private theorem aeval_X_sub_C_laguerreRaisingEndomorphism (s theta : ℝ) :
    (aeval (laguerreRaisingEndomorphism s) (X - C theta) : Module.End ℝ ℝ[X]) =
      laguerreRaisingEndomorphism (s - theta) := by
  apply LinearMap.ext
  intro p
  simp [laguerreRaisingEndomorphism, laguerreRaisingStep, smul_eq_C_mul]
  ring

private theorem aeval_ascPochhammer_laguerreRaisingEndomorphism
    (d m : ℕ) (alpha : ℝ) :
    (aeval (laguerreRaisingEndomorphism (alpha + d + 1)) (ascPochhammer ℝ m) :
        Module.End ℝ ℝ[X]) (generalizedLaguerre d alpha) =
      generalizedLaguerre (d + m) alpha := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [ascPochhammer_succ_right, aeval_mul]
      have hcomm := (Commute.all (ascPochhammer ℝ m) (X + (m : ℝ[X]))).map
        (aeval (laguerreRaisingEndomorphism (alpha + d + 1)) :
          ℝ[X] →ₐ[ℝ] Module.End ℝ ℝ[X])
      rw [hcomm.eq, Module.End.mul_apply, ih]
      have hop : (aeval (laguerreRaisingEndomorphism (alpha + d + 1))
          (X + (m : ℝ[X])) : Module.End ℝ ℝ[X]) =
          laguerreRaisingEndomorphism (alpha + (d + m) + 1) := by
        calc
          _ = laguerreRaisingEndomorphism (alpha + d + 1 + (m : ℝ)) := by
            simpa [sub_eq_add_neg] using
              aeval_X_sub_C_laguerreRaisingEndomorphism
                (alpha + d + 1) (-(m : ℝ))
          _ = laguerreRaisingEndomorphism (alpha + (d + m) + 1) := by
            congr 1
            ring
      rw [hop]
      simp only [laguerreRaisingEndomorphism_apply]
      rw [show alpha + ((d : ℝ) + m) + 1 = ((d + m : ℕ) : ℝ) + alpha + 1 by
        push_cast
        ring]
      rw [← generalizedLaguerre_succ]
      congr 1

private theorem aeval_laguerreAuxiliary_eq_sum
    {K n : ℕ} (hKn : K ≤ n) (gamma : ℕ → ℝ) (alpha : ℝ) :
    (aeval (laguerreRaisingEndomorphism (alpha + (n - K : ℕ) + 1))
        (laguerreAuxiliary K gamma) : Module.End ℝ ℝ[X])
        (generalizedLaguerre (n - K) alpha) =
      ∑ j ∈ Finset.range (K + 1),
        C ((-1 : ℝ) ^ j * gamma j) * generalizedLaguerre (n - j) alpha := by
  rw [laguerreAuxiliary, map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [map_mul, Module.End.mul_apply,
    aeval_ascPochhammer_laguerreRaisingEndomorphism]
  simp only [aeval_C, Module.algebraMap_end_apply, smul_eq_C_mul]
  congr 2
  lia

private theorem aeval_prod_X_sub_C_eq_laguerreRaisingSteps
    (roots : List ℝ) (s : ℝ) (p : ℝ[X]) :
    (aeval (laguerreRaisingEndomorphism s)
        ((roots.map fun r ↦ X - C r).prod) : Module.End ℝ ℝ[X]) p =
      laguerreRaisingSteps (roots.map fun r ↦ s - r) p := by
  induction roots with
  | nil => simp [laguerreRaisingSteps]
  | cons r roots ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply,
        aeval_X_sub_C_laguerreRaisingEndomorphism,
        laguerreRaisingEndomorphism_apply, laguerreRaisingSteps]
      rw [ih]

private theorem aeval_eq_laguerreRaisingSteps_of_monic_splits
    {Q : ℝ[X]} (hQmonic : Q.Monic) (hQsplits : Q.Splits)
    (s : ℝ) (p : ℝ[X]) :
    (aeval (laguerreRaisingEndomorphism s) Q : Module.End ℝ ℝ[X]) p =
      laguerreRaisingSteps (Q.roots.toList.map fun r ↦ s - r) p := by
  have hfactor : Q = (Q.roots.toList.map fun r ↦ X - C r).prod := by
    calc
      Q = (Q.roots.map fun r ↦ X - C r).prod :=
        hQsplits.eq_prod_roots_of_monic hQmonic
      _ = (Q.roots.toList.map fun r ↦ X - C r).prod :=
        (Multiset.prod_map_toList Q.roots fun r ↦ X - C r).symm
  conv_lhs => rw [hfactor]
  exact aeval_prod_X_sub_C_eq_laguerreRaisingSteps Q.roots.toList s p

private theorem monicLaguerre_comp_neg_X (n : ℕ) (alpha : ℝ) :
    (monicLaguerre n alpha).comp (-X) =
      C ((-1 : ℝ) ^ n) * generalizedLaguerre n alpha := by
  simp [monicLaguerre, mul_comp, comp_neg_X_comp_neg_X]

/-- Reflection turns a classical finite Laguerre combination into the signed generalized
Laguerre sum used by the generalized Bell iteration. -/
theorem laguerreCombination_comp_neg_X
    {K n : ℕ} (hKn : K ≤ n) (gamma : ℕ → ℝ) (alpha : ℝ) :
    (laguerreCombination K gamma n alpha).comp (-X) =
      C ((-1 : ℝ) ^ n) *
        ∑ j ∈ Finset.range (K + 1),
          C ((-1 : ℝ) ^ j * gamma j) * generalizedLaguerre (n - j) alpha := by
  rw [laguerreCombination, Polynomial.sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjn : j ≤ n := by lia
  have hpow : (-1 : ℝ) ^ (n - j) = (-1) ^ n * (-1) ^ j := by
    have hsplit : (-1 : ℝ) ^ n = (-1) ^ (n - j) * (-1) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hjn]
    rw [hsplit, mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  rw [mul_comp, C_comp, monicLaguerre_comp_neg_X, hpow]
  calc
    C (gamma j) *
          (C (((-1 : ℝ) ^ n) * (-1) ^ j) * generalizedLaguerre (n - j) alpha) =
        C (gamma j * (((-1 : ℝ) ^ n) * (-1) ^ j)) *
          generalizedLaguerre (n - j) alpha := by rw [← mul_assoc, ← C_mul]
    _ = C (((-1 : ℝ) ^ n) * (((-1) ^ j) * gamma j)) *
          generalizedLaguerre (n - j) alpha := by
      congr 2
      ring
    _ = C ((-1 : ℝ) ^ n) *
        (C (((-1 : ℝ) ^ j) * gamma j) * generalizedLaguerre (n - j) alpha) := by
      rw [C_mul, mul_assoc]

/-- The signed generalized Laguerre sum in Durán's criterion has only simple negative roots
when the auxiliary polynomial splits below `α + 1`. -/
theorem generalizedLaguerreSum_splits_simple_roots_neg_of_auxiliary
    {K n : ℕ} (hKn : K ≤ n) {gamma : ℕ → ℝ} {alpha : ℝ}
    (hgamma : gamma 0 = 1) (halpha : -1 < alpha)
    (hQsplits : (laguerreAuxiliary K gamma).Splits)
    (hQroots : ∀ r ∈ (laguerreAuxiliary K gamma).roots, r < alpha + 1) :
    let F := ∑ j ∈ Finset.range (K + 1),
      C ((-1 : ℝ) ^ j * gamma j) * generalizedLaguerre (n - j) alpha
    F.Splits ∧ HasSimpleRoots F ∧ ∀ r ∈ F.roots, r < 0 := by
  dsimp
  let Q := laguerreAuxiliary K gamma
  let s := alpha + (n - K : ℕ) + 1
  let p := generalizedLaguerre (n - K) alpha
  let parameters := Q.roots.toList.map fun r ↦ s - r
  have hQmonic : Q.Monic := laguerreAuxiliary_monic hgamma
  have hparameters : ∀ a ∈ parameters, 0 < a := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨r, hr, rfl⟩
    have hr' : r ∈ Q.roots := Multiset.mem_toList.mp hr
    have hbound : r < alpha + 1 := hQroots r hr'
    have hcast : 0 ≤ ((n - K : ℕ) : ℝ) := Nat.cast_nonneg _
    dsimp [s]
    linarith
  have hp0 : p.coeff 0 ≠ 0 := by
    dsimp [p]
    rw [coeff_zero_eq_eval_zero, generalizedLaguerre_eval_zero]
    exact (ascPochhammer_pos (n - K) (alpha + 1) (by linarith)).ne'
  have hsteps := laguerreRaisingSteps_splits_simple_roots_neg hparameters
    (monic_generalizedLaguerre (n - K) alpha)
    (generalizedLaguerre_splits (n - K) halpha.le)
    (generalizedLaguerre_hasSimpleRoots (n - K) halpha.le)
    (generalizedLaguerre_hasNonnegCoeffs (n - K) halpha.le) hp0
  have heq :
      ∑ j ∈ Finset.range (K + 1),
          C ((-1 : ℝ) ^ j * gamma j) * generalizedLaguerre (n - j) alpha =
        laguerreRaisingSteps parameters p := by
    rw [← aeval_laguerreAuxiliary_eq_sum hKn gamma alpha]
    exact aeval_eq_laguerreRaisingSteps_of_monic_splits hQmonic hQsplits s p
  rw [heq]
  exact ⟨hsteps.2.2.1, hsteps.2.2.2.1, hsteps.2.2.2.2.2.2⟩

/-- Durán's general fixed-bandwidth criterion: a normalized auxiliary polynomial whose roots
are real and lie below `α + 1` gives a classical Laguerre combination with positive simple
roots. -/
theorem laguerreCombination_splits_simple_roots_pos_of_auxiliary
    {K n : ℕ} (hKn : K ≤ n) {gamma : ℕ → ℝ} {alpha : ℝ}
    (hgamma : gamma 0 = 1) (halpha : -1 < alpha)
    (hQsplits : (laguerreAuxiliary K gamma).Splits)
    (hQroots : ∀ r ∈ (laguerreAuxiliary K gamma).roots, r < alpha + 1) :
    (laguerreCombination K gamma n alpha).Splits ∧
      HasSimpleRoots (laguerreCombination K gamma n alpha) ∧
      ∀ r ∈ (laguerreCombination K gamma n alpha).roots, 0 < r := by
  let F := ∑ j ∈ Finset.range (K + 1),
    C ((-1 : ℝ) ^ j * gamma j) * generalizedLaguerre (n - j) alpha
  have hpack := generalizedLaguerreSum_splits_simple_roots_neg_of_auxiliary
    hKn hgamma halpha hQsplits hQroots
  have href := laguerreCombination_comp_neg_X hKn gamma alpha
  have hsign : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcompSplits :
      ((laguerreCombination K gamma n alpha).comp (-X)).Splits := by
    rw [href]
    exact hpack.1.C_mul _
  have hsplits : (laguerreCombination K gamma n alpha).Splits := by
    have h := hcompSplits.comp_neg_X
    simpa [comp_neg_X_comp_neg_X] using h
  have hcompSimple :
      HasSimpleRoots ((laguerreCombination K gamma n alpha).comp (-X)) := by
    rw [href]
    exact hpack.2.1.C_mul hsign
  have hsimple : HasSimpleRoots (laguerreCombination K gamma n alpha) := by
    have h := hcompSimple.comp_C_mul_X_add_C
      (a := (-1 : ℝ)) (b := 0) (by norm_num)
    simpa [comp_neg_X_comp_neg_X] using h
  refine ⟨hsplits, hsimple, ?_⟩
  intro r hr
  have hrroot : (laguerreCombination K gamma n alpha).IsRoot r :=
    (Polynomial.mem_roots hsimple.ne_zero).mp hr
  have hcompRoot :
      ((laguerreCombination K gamma n alpha).comp (-X)).IsRoot (-r) := by
    rw [Polynomial.IsRoot.def] at hrroot ⊢
    simpa [eval_comp] using hrroot
  have hFroot : F.IsRoot (-r) := by
    rw [href] at hcompRoot
    rw [Polynomial.IsRoot.def] at hcompRoot ⊢
    simpa [F, hsign] using hcompRoot
  have hFmem : -r ∈ F.roots :=
    (Polynomial.mem_roots hpack.2.1.ne_zero).mpr hFroot
  linarith [hpack.2.2 (-r) hFmem]

end RealRooted

end
