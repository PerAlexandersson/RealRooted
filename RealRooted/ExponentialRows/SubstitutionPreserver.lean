module

import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
public import RealRooted.PFPolynomial
import RealRooted.PFPolynomial.PreserverClosure
import RealRooted.OperatorInterlacingUpgrade
import RealRooted.JensenPencilContraction
import RealRooted.PFPolynomial.Closure
import RealRooted.Mathlib.Topology.Algebra.Polynomial
import RealRooted.PosCombo
import RealRooted.Mathlib.Algebra.Polynomial.Splits.FinRoots
import RealRooted.Derivative.Interlacing
import Mathlib.Tactic

/-!
# Substitution operators for exponential rows

The single-deletion induction for the operator associated with
`Φ' = a + b X + λ Φ` uses the existing Wagner cones. The polynomial variable
in the input of the operator represents the marked-block parameter.

Source: unpublished manuscript (RealRooted issue #2415), Theorem 1,
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

public section

open Polynomial Finset

namespace RealRooted.ExponentialRows

/-- An operator with the substitution product rule preserves the single-deletion
interlacing invariant on products of strictly positive linear factors.
The coefficient and constant-coefficient assumptions are elementary properties
of the exponential kernel, rather than real-rootedness assumptions. -/
theorem interl_map_prod_erase_of_substitution_rule
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {a b l : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l)
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hT1 : T 1 = 1)
    (hstep : ∀ (r : ℝ) (p : ℝ[X]),
      T ((X + C r) * p) = (C r + C a * X) * T p +
        C l * X * (T p).derivative + C b * X * T p.derivative)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (r : ι → ℝ)
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
        simpa using Finset.prod_pos fun j hj => hr j (hu hj)
      intro hz
      simp [hz] at hp
    have hdel (i : ι) (hi : i ∈ s) :
        StrictInterl (T (∏ j ∈ s.erase i, (X + C (r j))))
          (T (∏ j ∈ s, (X + C (r j)))) := by
      let u := s.erase i
      let P := T (∏ j ∈ u, (X + C (r j)))
      have hu : u ⊂ s := Finset.erase_ssubset hi
      have hPu := ih u hu (fun j hj => hr j (hu.subset hj))
      have hPnn : HasNonnegCoeffs P := hnn u hu.subset
      have hPne : P ≠ 0 := hne u hu.subset
      have hPs : P.Splits := hPu.1.splits
      have hself : Interl P P := (StrictInterl.refl hPne hPs).toInterl
      have hXP : Interl P (X * P) :=
        interl_mul_X_of_interl hself hPnn hPnn
      have hder : Interl P.derivative P := by
        by_cases hd : P.natDegree = 0
        · rw [(Polynomial.derivative_eq_zero).mpr hd]
          exact interl_zero_left P
        · exact (derivative_interlaces_of_natDegree_ne_zero hPs hd).toStrictInterl.toInterl
      have hderX : Interl P (X * P.derivative) :=
        interl_mul_X_of_interl hder hPnn.derivative hPnn
      have hsum : Interl
          (T (∑ j ∈ u, ∏ k ∈ u.erase j, (X + C (r k)))) P := by
        rw [map_sum]
        apply Interl.finsetSum_right_of_nonneg
        · intro j hj
          exact (hPu.2 j hj).toInterl
        · intro j hj
          exact hnn (u.erase j) ((Finset.erase_subset j u).trans hu.subset)
      have hdprod :
          (∏ j ∈ u, (X + C (r j))).derivative =
            ∑ j ∈ u, ∏ k ∈ u.erase j, (X + C (r k)) := by
        simp [Polynomial.derivative_prod_finset]
      rw [← hdprod] at hsum
      have hdnn : HasNonnegCoeffs (T (∏ j ∈ u, (X + C (r j))).derivative) := by
        apply hTnn
        exact (hasNonnegCoeffs_finsetProd u _ fun j hj =>
          hasNonnegCoeffs_X_add_C (hr j (hu.subset hj)).le).derivative
      have hsumX : Interl P (X * T (∏ j ∈ u, (X + C (r j))).derivative) :=
        interl_mul_X_of_interl hsum hdnn hPnn
      have hfirst : Interl P ((C (r i) + C a * X) * P) := by
        rw [add_mul]
        exact interl_add_right_of_common_left_of_nonneg
          (hself.C_mul_right_of_nonneg (hr i hi).le)
          (by simpa [mul_assoc] using hXP.C_mul_right_of_nonneg ha)
          (hasNonnegCoeffs_C_mul (hr i hi).le hPnn)
          (by simpa [mul_assoc] using hasNonnegCoeffs_C_mul ha hPnn.X_mul)
      have hsecond : Interl P
          ((C (r i) + C a * X) * P + C l * X * P.derivative) :=
        interl_add_right_of_common_left_of_nonneg hfirst
          (by simpa [mul_assoc] using hderX.C_mul_right_of_nonneg hl)
          ((hasNonnegCoeffs_C (hr i hi).le |>.add
            (hasNonnegCoeffs_C_mul ha hasNonnegCoeffs_X)).mul hPnn)
          (by simpa [mul_assoc] using hasNonnegCoeffs_C_mul hl hPnn.derivative.X_mul)
      have hout : Interl P (T (∏ j ∈ s, (X + C (r j)))) := by
        rw [← Finset.mul_prod_erase s _ hi, hstep]
        exact interl_add_right_of_common_left_of_nonneg hsecond
          (by simpa [mul_assoc] using hsumX.C_mul_right_of_nonneg hb)
          (((hasNonnegCoeffs_C (hr i hi).le |>.add
            (hasNonnegCoeffs_C_mul ha hasNonnegCoeffs_X)).mul hPnn).add
            (by simpa [mul_assoc] using hasNonnegCoeffs_C_mul hl hPnn.derivative.X_mul))
          (by simpa [mul_assoc] using hasNonnegCoeffs_C_mul hb hdnn.X_mul)
      exact hout.toStrictInterl_of_ne hPne (hne s (by rfl))
    refine ⟨?_, hdel⟩
    rcases s.eq_empty_or_nonempty with hs | ⟨i, hi⟩
    · simpa [hs, hT1] using IsPFPolynomial.one
    · exact IsPFPolynomial.of_realRooted_nonneg (hnn s (by rfl)) (hdel i hi).2.1.2

/-- A substitution-rule operator sends every PF polynomial with positive
constant coefficient to a PF polynomial, and preserves its positive-factor
interlacing edges. -/
theorem isPFPolynomial_map_and_strictInterl_of_substitution_rule
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {a b l : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l)
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hT1 : T 1 = 1)
    (hstep : ∀ (r : ℝ) (p : ℝ[X]),
      T ((X + C r) * p) = (C r + C a * X) * T p +
        C l * X * (T p).derivative + C b * X * T p.derivative)
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : 0 < p.coeff 0) :
    IsPFPolynomial (T p) ∧
      ∀ r : ℝ, 0 < r → StrictInterl (T p) (T ((X + C r) * p)) := by
  classical
  have hpne : p ≠ 0 := by
    intro h
    simp [h] at hp0
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
    simpa [sub_eq_add_neg] using hfac
  have hmap : T p = C p.leadingCoeff * T (∏ i : Fin p.natDegree, (X + C (-z i))) := by
    conv_lhs => rw [hfac']
    rw [Polynomial.linearMap_C_mul]
  constructor
  · rw [hmap]
    exact (interl_map_prod_erase_of_substitution_rule T ha hb hl hTnn hTc hT1 hstep
      Finset.univ (fun i : Fin p.natDegree => -z i) (fun i _ => hroots i)).1.const_mul hlc
  · intro r hr
    let v : Option (Fin p.natDegree) → ℝ := fun i => i.elim r (fun i => -z i)
    have hv : ∀ i ∈ (Finset.univ : Finset (Option (Fin p.natDegree))), 0 < v i := by
      intro i _
      cases i with
      | none => exact hr
      | some z => exact hroots z
    have H := (interl_map_prod_erase_of_substitution_rule T ha hb hl hTnn hTc hT1 hstep
      Finset.univ v hv).2 none (Finset.mem_univ _)
    have hprod : (∏ i : Option (Fin p.natDegree), (X + C (v i))) =
        (X + C r) * ∏ i : Fin p.natDegree, (X + C (-z i)) := by
      simp [v, Fintype.prod_option]
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

/-- The substitution product rule preserves the PF cone, including zero
outputs and roots at zero. -/
theorem isPFPolynomial_map_of_substitution_rule
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {a b l : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l)
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hT1 : T 1 = 1)
    (hstep : ∀ (r : ℝ) (p : ℝ[X]),
      T ((X + C r) * p) = (C r + C a * X) * T p +
        C l * X * (T p).derivative + C b * X * T p.derivative)
    {p : ℝ[X]} (hp : IsPFPolynomial p) : IsPFPolynomial (T p) := by
  apply isPFPolynomial_map_of_isNegativeSimple T _ hp
  intro q hq
  have hq0 : 0 < q.coeff 0 := by
    rw [coeff_zero_eq_eval_zero]
    exact eval_pos_of_all_roots_lt hq.1 hq.2.1 hq.2.2.2.1 hq.2.2.2.2
  exact (isPFPolynomial_map_and_strictInterl_of_substitution_rule
    T ha hb hl hTnn hTc hT1 hstep hq.isPFPolynomial hq0).1

/-- A degree-nonincreasing substitution-rule operator preserves every directed
PF interlacing, including vanishing outputs. Positive input translation makes
all intermediate constant coefficients positive; bounded-degree closure removes
that translation. -/
theorem interl_map_of_substitution_rule
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {a b l : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l)
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hT1 : T 1 = 1)
    (hstep : ∀ (r : ℝ) (p : ℝ[X]),
      T ((X + C r) * p) = (C r + C a * X) * T p +
        C l * X * (T p).derivative + C b * X * T p.derivative)
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
    isPFPolynomial_map_of_substitution_rule T ha hb hl hTnn hTc hT1 hstep hp
  have heps (eps : ℝ) (heps : 0 < eps) :
      StrictInterl (T (f.comp (X + C eps))) (T (g.comp (X + C eps))) := by
    let U : ℝ[X] →ₗ[ℝ] ℝ[X] := T.comp (Polynomial.aeval (X + C eps)).toLinearMap
    have hU (p : ℝ[X]) : U p = T (p.comp (X + C eps)) := by
      simp [U, Polynomial.comp_eq_aeval]
    have hUpf {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : p ≠ 0) :
        IsPFPolynomial (U p) ∧ U p ≠ 0 := by
      have htrans := hp.comp_X_add_C_and_coeff_zero_pos hp0 heps
      have hpos : 0 < (U p).coeff 0 := by rw [hU, hTc]; exact htrans.2
      refine ⟨hmap htrans.1, ?_⟩
      intro hz
      simp [hz] at hpos
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
      have H := (isPFPolynomial_map_and_strictInterl_of_substitution_rule
        T ha hb hl hTnn hTc hT1 hstep ht.1 ht.2).2 (r + eps) (by linarith)
      simpa only [hU, mul_comp, add_comp, X_comp, C_comp, map_add, add_assoc,
        add_left_comm, add_comm] using H
  let eps : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hepspos (n : ℕ) : 0 < eps n := by dsimp [eps]; positivity
  have hepslim : Filter.Tendsto eps Filter.atTop (nhds 0) := by
    simpa [eps, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
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
