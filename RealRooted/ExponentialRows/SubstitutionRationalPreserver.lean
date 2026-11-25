module

public import RealRooted.PFPolynomial
import RealRooted.PFPolynomial.PreserverClosure
import RealRooted.OperatorInterlacingUpgrade
import RealRooted.JensenPencilContraction
import RealRooted.PFPolynomial.Closure
import RealRooted.Mathlib.Topology.Algebra.Polynomial
import RealRooted.Mathlib.Algebra.Polynomial.Splits.FinRoots
import RealRooted.LiuWang.FiniteFamily
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import RealRooted.Derivative.Interlacing
import RealRooted.Derivative.Algebra
import RealRooted.PosCombo
import RealRooted.WagnerX.NonnegativeRoots
import Mathlib.Tactic

/-!
# Single-deletion induction for rational substitution

The rational-ODE product rule closes the single-deletion invariant by the
finite-family Liu–Wang criterion. Each deletion multiplier is `b t - d r`;
its sign is nonpositive on the negative real axis. The proof includes zero
parameters, constant intermediate images, and shared roots.

Source: unpublished manuscript, *Degree-raising substitutions for exponential rows*,
Theorem 2, RealRooted issue #2415:
https://github.com/PerAlexandersson/RealRooted/issues/2415#issuecomment-7141592218.
-/

public section

open Polynomial Finset

namespace RealRooted.ExponentialRows

/-- The Euler derivative of a product is the sum of its positive-factor
single deletions, with the corresponding root activities subtracted. -/
private theorem X_mul_derivative_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r : ι → ℝ) :
    X * (∏ j ∈ s, (X + C (r j))).derivative =
      C (s.card : ℝ) * (∏ j ∈ s, (X + C (r j))) -
        ∑ j ∈ s, C (r j) * ∏ k ∈ s.erase j, (X + C (r k)) := by
  have hder : (∏ j ∈ s, (X + C (r j))).derivative =
      ∑ j ∈ s, ∏ k ∈ s.erase j, (X + C (r k)) := by
    simp only [Polynomial.derivative_prod_finset, derivative_add, derivative_X,
      derivative_C, add_zero, mul_one]
  rw [hder, mul_sum]
  have hterm (j : ι) (hj : j ∈ s) :
      X * (∏ k ∈ s.erase j, (X + C (r k))) =
        (∏ k ∈ s, (X + C (r k))) -
          C (r j) * (∏ k ∈ s.erase j, (X + C (r k))) := by
    rw [← Finset.mul_prod_erase s _ hj]
    ring
  simp only [sum_congr rfl hterm, sum_sub_distrib, sum_const, nsmul_eq_mul,
    map_natCast]

/-- The rational-ODE rule on a positive-factor product has the Liu–Wang
form: every deletion is multiplied by `b X - d rⱼ`. -/
private theorem map_prod_rational_rule
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {a b l d : ℝ}
    (hstep : ∀ (r : ℝ) (p : ℝ[X]),
      T ((X + C r) * p) = (C r + C a * X) * T p +
        C l * X * (T p).derivative + C b * X * T p.derivative +
        C d * T (X * p.derivative))
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → ℝ) (v : ℝ) :
    T ((X + C v) * ∏ j ∈ s, (X + C (r j))) =
      (C (v + d * s.card) + C a * X) * T (∏ j ∈ s, (X + C (r j))) +
        C l * X * (T (∏ j ∈ s, (X + C (r j)))).derivative +
        ∑ j ∈ s, (C b * X - C (d * r j)) *
          T (∏ k ∈ s.erase j, (X + C (r k))) := by
  rw [hstep, X_mul_derivative_prod, map_sub, Polynomial.linearMap_C_mul, map_sum]
  have hder : (∏ j ∈ s, (X + C (r j))).derivative =
      ∑ j ∈ s, ∏ k ∈ s.erase j, (X + C (r k)) := by
    simp only [Polynomial.derivative_prod_finset, derivative_add, derivative_X,
      derivative_C, add_zero, mul_one]
  rw [hder, map_sum]
  simp only [Polynomial.linearMap_C_mul, mul_sum, sub_mul, sum_sub_distrib,
    map_add, map_mul, mul_sub, mul_assoc]
  ring

/-- Adjoin the derivative to a finite deletion family and apply Liu–Wang.
The explicit termwise signs retain control at repeated roots. -/
private theorem strictInterl_rational_sum
    {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    {U A F : ℝ[X]} {V : ι → ℝ[X]} {b l d : ℝ}
    (hU : IsPFPolynomial U) (hUne : U ≠ 0)
    (hV : ∀ j ∈ s, StrictInterl (V j) U)
    (hVnn : ∀ j ∈ s, HasNonnegCoeffs (V j))
    (hr : ∀ j ∈ s, 0 ≤ r j) (hb : 0 ≤ b) (hl : 0 ≤ l) (hd : 0 ≤ d)
    (hrec : F = A * U + C l * X * U.derivative +
      ∑ j ∈ s, (C b * X - C (d * r j)) * V j)
    (hFpos : HasPosLeadingCoeff F)
    (hlo : U.natDegree ≤ F.natDegree) (hhi : F.natDegree ≤ U.natDegree + 1) :
    StrictInterl U F := by
  classical
  let G : Option ι → ℝ[X] := fun j => j.elim
    (if U.natDegree = 0 then U else U.derivative) V
  let W : Option ι → ℝ[X] := fun j => j.elim
    (if U.natDegree = 0 then 0 else C l * X)
    (fun j => C b * X - C (d * r j))
  let v := insert none (s.image some)
  have hv (H : Option ι → ℝ[X]) :
      ∑ j ∈ v, H j = H none + ∑ j ∈ s, H (some j) := by
    rw [sum_insert (by simp only [mem_image, Option.some_ne_none, and_false,
      exists_false, not_false_eq_true]), sum_image]
    exact fun _ _ _ _ h => Option.some.inj h
  have hmem (j : ι) (hj : some j ∈ v) : j ∈ s := by
    simpa only [v, mem_insert, Option.some_ne_none, mem_image,
      Option.some.injEq, exists_eq_right, false_or] using hj
  have hG : ∀ j ∈ v, StrictInterl (G j) U := by
    intro j hj
    cases j with
    | none =>
      dsimp only [G, Option.elim_none]
      split_ifs with hz
      · exact StrictInterl.refl hUne hU.splits
      · exact (derivative_interlaces_of_natDegree_ne_zero hU.splits hz).toStrictInterl
    | some j => exact hV j (hmem j hj)
  have hGnn : ∀ j ∈ v, HasNonnegCoeffs (G j) := by
    intro j hj
    cases j with
    | none =>
      dsimp only [G, Option.elim_none]
      split_ifs
      · exact hU.hasNonnegCoeffs
      · exact hU.hasNonnegCoeffs.derivative
    | some j => exact hVnn j (hmem j hj)
  have hW : ∀ j ∈ v, ∀ x, U.IsRoot x → (W j).eval x ≤ 0 := by
    intro j hj x hx
    have hx0 := hU.roots_nonpos x ((Polynomial.mem_roots hUne).mpr hx)
    cases j with
    | none =>
      dsimp only [W, Option.elim_none]
      split_ifs
      · simp only [eval_zero, le_refl]
      · simpa only [eval_mul, eval_C, eval_X] using mul_nonpos_of_nonneg_of_nonpos hl hx0
    | some j =>
      simp only [W, Option.elim_some, eval_sub, eval_mul, eval_C, eval_X]
      exact sub_nonpos.mpr ((mul_nonpos_of_nonneg_of_nonpos hb hx0).trans
        (mul_nonneg hd (hr j (hmem j hj))))
  have hform : A * U + ∑ j ∈ v, W j * G j = F := by
    rw [hv, hrec]
    dsimp only [W, G, Option.elim_none, Option.elim_some]
    split_ifs with hz
    · rw [Polynomial.derivative_eq_zero.mpr hz, mul_zero, zero_mul, add_zero, zero_add]
    · ring
  have H := LiuWang.strictInterl_mul_add_sum_mul_of_eval_nonpos_of_pos
    (hU.hasNonnegCoeffs.pos_leadingCoeff hUne) hU.splits hG
    (fun j hj => (hGnn j hj).pos_leadingCoeff (hG j hj).1.1) hW
    (hform.symm ▸ hFpos) (hform.symm ▸ hlo) (hform.symm ▸ hhi)
  exact hform ▸ H

/-- Degree control for the rational-ODE deletion expansion. -/
private theorem natDegree_rational_sum_le
    {ι : Type*} (s : Finset ι) (r : ι → ℝ) (a b l d v : ℝ)
    {U : ℝ[X]} {V : ι → ℝ[X]}
    (hV : ∀ j ∈ s, (V j).natDegree ≤ U.natDegree) :
    ((C (v + d * s.card) + C a * X) * U + C l * X * U.derivative +
      ∑ j ∈ s, (C b * X - C (d * r j)) * V j).natDegree ≤ U.natDegree + 1 := by
  have hlin (c : ℝ) : (C c * X : ℝ[X]).natDegree ≤ 1 := by
    simpa only [natDegree_X] using (natDegree_C_mul_le c (X : ℝ[X]))
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · apply natDegree_mul_le.trans
      have hc : (C (v + d * s.card) + C a * X).natDegree ≤ 1 :=
        natDegree_add_le_of_degree_le (by simp only [natDegree_C]; lia) (hlin a)
      lia
    · apply natDegree_mul_le.trans
      have hdU := Polynomial.natDegree_derivative_le U
      have hc : (C l * X : ℝ[X]).natDegree ≤ 1 := hlin l
      lia
  · apply natDegree_sum_le_of_forall_le
    intro j hj
    apply natDegree_mul_le.trans
    have hc : (C b * X - C (d * r j)).natDegree ≤ 1 :=
      (natDegree_sub_le_iff_right (hlin b)).mpr (by simp only [natDegree_C]; lia)
    have := hV j hj
    lia

/-- A rational-rule operator preserves the positive-factor single-deletion
invariant. Positivity of the input constant coefficient excludes zero images. -/
theorem interl_map_prod_erase_of_rational_substitution_rule
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {a b l d : ℝ}
    (hb : 0 ≤ b) (hl : 0 ≤ l) (hd : 0 ≤ d)
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hT1 : T 1 = 1)
    (hstep : ∀ (r : ℝ) (p : ℝ[X]),
      T ((X + C r) * p) = (C r + C a * X) * T p +
        C l * X * (T p).derivative + C b * X * T p.derivative +
        C d * T (X * p.derivative))
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 < r i) :
    IsPFPolynomial (T (∏ i ∈ s, (X + C (r i)))) ∧
      ∀ i ∈ s, StrictInterl
        (T (∏ j ∈ s.erase i, (X + C (r j))))
        (T (∏ j ∈ s, (X + C (r j)))) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hnn (u : Finset ι) (hu : u ⊆ s) :
        HasNonnegCoeffs (T (∏ j ∈ u, (X + C (r j)))) := by
      apply hTnn
      exact hasNonnegCoeffs_finsetProd u _ fun j hj =>
        hasNonnegCoeffs_X_add_C (hr j (hu hj)).le
    have hne (u : Finset ι) (hu : u ⊆ s) :
        T (∏ j ∈ u, (X + C (r j))) ≠ 0 := by
      have hp : 0 < (T (∏ j ∈ u, (X + C (r j)))).coeff 0 := by
        rw [hTc, coeff_zero_prod]
        simpa only [coeff_add, coeff_X_zero, coeff_C_zero, zero_add] using
          Finset.prod_pos fun j hj => hr j (hu hj)
      intro hz
      simp only [hz, coeff_zero, lt_self_iff_false] at hp
    have hdel (i : ι) (hi : i ∈ s) :
        StrictInterl (T (∏ j ∈ s.erase i, (X + C (r j))))
          (T (∏ j ∈ s, (X + C (r j)))) := by
      let u := s.erase i
      let p := ∏ j ∈ u, (X + C (r j))
      let U := T p
      let V (j : ι) := T (∏ k ∈ u.erase j, (X + C (r k)))
      have hu : u ⊂ s := Finset.erase_ssubset hi
      have hPu := ih u hu (fun j hj => hr j (hu.subset hj))
      have hUnn : HasNonnegCoeffs U := hnn u hu.subset
      have hUne : U ≠ 0 := hne u hu.subset
      have hUpos : HasPosLeadingCoeff U := hUnn.pos_leadingCoeff hUne
      have hrec := map_prod_rational_rule T hstep u r (r i)
      dsimp only [u] at hrec
      rw [Finset.mul_prod_erase s (fun j => X + C (r j)) hi] at hrec
      have hlo : U.natDegree ≤ (T (∏ j ∈ s, (X + C (r j)))).natDegree := by
        apply Polynomial.le_natDegree_of_ne_zero
        have hXp : HasNonnegCoeffs (T (X * p)) := hTnn _
          (hasNonnegCoeffs_X.mul (hasNonnegCoeffs_finsetProd u _ fun j hj =>
            hasNonnegCoeffs_X_add_C (hr j (hu.subset hj)).le))
        rw [← Finset.mul_prod_erase s (fun j => X + C (r j)) hi, add_mul, map_add,
          Polynomial.linearMap_C_mul, coeff_add, coeff_C_mul]
        exact (add_pos_of_nonneg_of_pos (hXp _) (mul_pos (hr i hi) hUpos)).ne'
      apply strictInterl_rational_sum u r hPu.1 hUne hPu.2
        (fun j _ => hnn (u.erase j) ((erase_subset j u).trans hu.subset))
        (fun j hj => (hr j (hu.subset hj)).le) hb hl hd hrec
        ((hnn s (by rfl)).pos_leadingCoeff (hne s (by rfl))) hlo
      rw [hrec]
      exact natDegree_rational_sum_le u r a b l d (r i)
        (fun j hj => (hPu.2 j hj).natDegree_le)
    refine ⟨?_, hdel⟩
    rcases s.eq_empty_or_nonempty with hs | ⟨i, hi⟩
    · simpa only [hs, prod_empty, hT1] using IsPFPolynomial.one
    · exact IsPFPolynomial.of_realRooted_nonneg (hnn s (by rfl)) (hdel i hi).2.1.2

/-- A rational-rule operator sends every PF polynomial with positive
constant coefficient to a PF polynomial, and preserves its positive-factor
interlacing edges. -/
theorem isPFPolynomial_map_and_strictInterl_of_rational_substitution_rule
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {a b l d : ℝ}
    (hb : 0 ≤ b) (hl : 0 ≤ l) (hd : 0 ≤ d)
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hT1 : T 1 = 1)
    (hstep : ∀ (r : ℝ) (p : ℝ[X]),
      T ((X + C r) * p) = (C r + C a * X) * T p +
        C l * X * (T p).derivative + C b * X * T p.derivative +
        C d * T (X * p.derivative))
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : 0 < p.coeff 0) :
    IsPFPolynomial (T p) ∧
      ∀ r : ℝ, 0 < r → StrictInterl (T p) (T ((X + C r) * p)) := by
  classical
  have hpne : p ≠ 0 := by
    intro h
    simp only [h, coeff_zero, lt_self_iff_false] at hp0
  have hlc : 0 < p.leadingCoeff := hp.hasNonnegCoeffs.pos_leadingCoeff hpne
  obtain ⟨z, hz, hfac⟩ := hp.splits.exists_fin_eq_C_mul_prod
  have hroots (i : Fin p.natDegree) : 0 < -z i := by
    have hmem : z i ∈ p.roots := by
      rw [← hz]
      exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
    have hle := hp.roots_nonpos _ hmem
    have hne : z i ≠ 0 := by
      intro hz0
      have hroot := Polynomial.isRoot_of_mem_roots hmem
      rw [Polynomial.IsRoot.def, hz0, ← coeff_zero_eq_eval_zero] at hroot
      exact hp0.ne' hroot
    exact neg_pos.mpr (lt_of_le_of_ne hle hne)
  have hfac' : p = C p.leadingCoeff * ∏ i : Fin p.natDegree, (X + C (-z i)) := by
    simpa only [sub_eq_add_neg, map_neg] using hfac
  have hmap : T p = C p.leadingCoeff * T (∏ i : Fin p.natDegree, (X + C (-z i))) := by
    conv_lhs => rw [hfac']
    rw [Polynomial.linearMap_C_mul]
  constructor
  · rw [hmap]
    exact (interl_map_prod_erase_of_rational_substitution_rule T hb hl hd hTnn hTc hT1 hstep
      Finset.univ (fun i : Fin p.natDegree => -z i) (fun i _ => hroots i)).1.const_mul hlc
  · intro r hr
    let v : Option (Fin p.natDegree) → ℝ := fun i => i.elim r (fun i => -z i)
    have hv : ∀ i ∈ (Finset.univ : Finset (Option (Fin p.natDegree))), 0 < v i := by
      intro i _
      cases i with
      | none => exact hr
      | some z => exact hroots z
    have H := (interl_map_prod_erase_of_rational_substitution_rule T hb hl hd hTnn hTc hT1 hstep
      Finset.univ v hv).2 none (Finset.mem_univ _)
    have hprod : (∏ i : Option (Fin p.natDegree), (X + C (v i))) =
        (X + C r) * ∏ i : Fin p.natDegree, (X + C (-z i)) := by
      simp only [Fintype.prod_option, v, Option.elim_none, Option.elim_some]
    have hdel : (∏ i ∈ (Finset.univ : Finset (Option (Fin p.natDegree))).erase none,
        (X + C (v i))) = ∏ i : Fin p.natDegree, (X + C (-z i)) := by
      apply mul_left_cancel₀ (Polynomial.X_add_C_ne_zero r)
      exact (Finset.mul_prod_erase Finset.univ
        (fun i : Option (Fin p.natDegree) => X + C (v i))
        (Finset.mem_univ none)).trans hprod
    rw [hprod, hdel] at H
    have hmap' : T ((X + C r) * p) = C p.leadingCoeff *
        T ((X + C r) * ∏ i : Fin p.natDegree, (X + C (-z i))) := by
      conv_lhs => rw [hfac']
      rw [show (X + C r) * (C p.leadingCoeff *
        ∏ i : Fin p.natDegree, (X + C (-z i))) = C p.leadingCoeff *
          ((X + C r) * ∏ i : Fin p.natDegree, (X + C (-z i))) by ring,
        Polynomial.linearMap_C_mul]
    rw [hmap, hmap']
    exact (H.C_mul_left hlc.ne').C_mul_right hlc.ne'

/-- The rational substitution product rule preserves the PF cone, including zero
outputs and roots at zero. -/
theorem isPFPolynomial_map_of_rational_substitution_rule
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {a b l d : ℝ}
    (hb : 0 ≤ b) (hl : 0 ≤ l) (hd : 0 ≤ d)
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hT1 : T 1 = 1)
    (hstep : ∀ (r : ℝ) (p : ℝ[X]),
      T ((X + C r) * p) = (C r + C a * X) * T p +
        C l * X * (T p).derivative + C b * X * T p.derivative +
        C d * T (X * p.derivative))
    {p : ℝ[X]} (hp : IsPFPolynomial p) : IsPFPolynomial (T p) := by
  apply isPFPolynomial_map_of_isNegativeSimple T _ hp
  intro q hq
  have hq0 : 0 < q.coeff 0 := by
    rw [coeff_zero_eq_eval_zero]
    exact eval_pos_of_all_roots_lt hq.1 hq.2.1 hq.2.2.2.1 hq.2.2.2.2
  exact (isPFPolynomial_map_and_strictInterl_of_rational_substitution_rule
    T hb hl hd hTnn hTc hT1 hstep hq.isPFPolynomial hq0).1

/-- A degree-nonincreasing rational-rule operator preserves every directed
PF interlacing, including vanishing outputs. Positive input translation makes
all intermediate constant coefficients positive; bounded-degree closure removes
that translation. -/
theorem interl_map_of_rational_substitution_rule
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {a b l d : ℝ}
    (hb : 0 ≤ b) (hl : 0 ≤ l) (hd : 0 ≤ d)
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hT1 : T 1 = 1)
    (hstep : ∀ (r : ℝ) (p : ℝ[X]),
      T ((X + C r) * p) = (C r + C a * X) * T p +
        C l * X * (T p).derivative + C b * X * T p.derivative +
        C d * T (X * p.derivative))
    (hTdeg : ∀ p, (T p).natDegree ≤ p.natDegree)
    {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfg : Interl f g) : Interl (T f) (T g) := by
  classical
  by_cases hf0 : f = 0
  · simp only [hf0, map_zero]
    exact interl_zero_left _
  by_cases hg0 : g = 0
  · simp only [hg0, map_zero]
    exact interl_zero_right _
  have hstrict := hfg.toStrictInterl_of_ne hf0 hg0
  have hmap {p : ℝ[X]} (hp : IsPFPolynomial p) : IsPFPolynomial (T p) :=
    isPFPolynomial_map_of_rational_substitution_rule T hb hl hd hTnn hTc hT1 hstep hp
  have heps (eps : ℝ) (heps : 0 < eps) :
      StrictInterl (T (f.comp (X + C eps))) (T (g.comp (X + C eps))) := by
    let U : ℝ[X] →ₗ[ℝ] ℝ[X] := T.comp (Polynomial.aeval (X + C eps)).toLinearMap
    have hU (p : ℝ[X]) : U p = T (p.comp (X + C eps)) := by
      change T (Polynomial.aeval (X + C eps) p) = _
      rw [← Polynomial.comp_eq_aeval]
    have hUpf {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : p ≠ 0) :
        IsPFPolynomial (U p) ∧ U p ≠ 0 := by
      have htrans := hp.comp_X_add_C_and_coeff_zero_pos hp0 heps
      have hpos : 0 < (U p).coeff 0 := by rw [hU, hTc]; exact htrans.2
      refine ⟨hmap htrans.1, ?_⟩
      intro hz
      simp only [hz, coeff_zero, lt_self_iff_false] at hpos
    apply strictInterl_map_of_pfLinearFactor (T := U) (D := g.natDegree)
      hstrict hf.hasNonnegCoeffs hg.hasNonnegCoeffs le_rfl
    · intro p hp
      rw [hU]
      apply hTnn
      rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def]
      exact hasNonnegCoeffs_finsetSum _ _ fun n _ =>
        hasNonnegCoeffs_C_mul (hp n) ((hasNonnegCoeffs_X_add_C heps.le).pow n)
    · intro p hp hp0 _
      exact ⟨(hUpf hp hp0).2, (hUpf hp hp0).1.splits⟩
    · intro p r hp hp0 hr _
      have ht := hp.comp_X_add_C_and_coeff_zero_pos hp0 heps
      have H := (isPFPolynomial_map_and_strictInterl_of_rational_substitution_rule
        T hb hl hd hTnn hTc hT1 hstep ht.1 ht.2).2 (r + eps) (by linarith)
      simpa only [hU, mul_comp, add_comp, X_comp, C_comp, map_add, add_assoc,
        add_left_comm, add_comm] using H
  let eps : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hepspos (n : ℕ) : 0 < eps n := by dsimp [eps]; positivity
  have hepslim : Filter.Tendsto eps Filter.atTop (nhds 0) := by
    simpa only [eps, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlim (p : ℝ[X]) : ∀ j, Filter.Tendsto
      (fun n => (T (p.comp (X + C (eps n)))).coeff j) Filter.atTop
      (nhds ((T p).coeff j)) := by
    apply tendsto_coeff_linearMap_apply_of_coeff_tendsto T (d := p.natDegree)
    · intro n
      simp only [natDegree_comp, natDegree_X_add_C, mul_one, le_refl]
    · intro j
      simpa only [Function.comp_def, C_0, add_zero, comp_X] using
        (p.continuous_coeff_comp_X_add_C j).tendsto 0 |>.comp hepslim
  apply interl_of_pf_coeff_tendsto_of_natDegree_le (N := max f.natDegree g.natDegree)
    (fun n => hmap (hf.comp_X_add_C_and_coeff_zero_pos hf0 (hepspos n)).1)
    (fun n => hmap (hg.comp_X_add_C_and_coeff_zero_pos hg0 (hepspos n)).1)
    (fun n => (heps _ (hepspos n)).toInterl)
  · intro n
    apply (hTdeg _).trans
    simpa only [natDegree_comp, natDegree_X_add_C, mul_one] using
      (le_max_left f.natDegree g.natDegree)
  · intro n
    apply (hTdeg _).trans
    simpa only [natDegree_comp, natDegree_X_add_C, mul_one] using
      (le_max_right f.natDegree g.natDegree)
  · exact hlim f
  · exact hlim g


end RealRooted.ExponentialRows
