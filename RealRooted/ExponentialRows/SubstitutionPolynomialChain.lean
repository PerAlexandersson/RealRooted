module

public import RealRooted.Hermite.Poulain
public import RealRooted.PFPolynomial
import RealRooted.ExponentialRows.SubstitutionDifferential
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import RealRooted.PosCombo
import RealRooted.Hermite.PoulainSymbolDerivative
import RealRooted.Mathlib.Algebra.Polynomial.Splits.FinRoots
import Mathlib.Tactic

/-!
# Prefixes of a factored differential symbol

The endpoint-chain argument applies to every ordering of the linear factors
of a PF outer symbol. It therefore controls every single-factor deletion.
Source: unpublished manuscript, RealRooted #2415, round four.
-/

public section

open Polynomial Finset
open RealRooted.HermitePoulain

namespace RealRooted.ExponentialRows

/-- Prefixes of a nonnegative differential-factor list retain the PF property
and have positive constant coefficient unless they vanish. -/
private theorem differential_prefix_pos (l : List ℝ) (hl : ∀ c ∈ l, 0 ≤ c)
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : 0 < p.coeff 0) :
    ∀ j ≤ l.length,
      IsPFPolynomial (applyAsDifferentialOperator
        ((l.take j).map (fun c => X + C c)).prod p) ∧
      (applyAsDifferentialOperator ((l.take j).map (fun c => X + C c)).prod p ≠ 0 →
        0 < (applyAsDifferentialOperator
          ((l.take j).map (fun c => X + C c)).prod p).coeff 0) := by
  intro j
  induction j with
  | zero => simpa only [List.take_zero, List.map_nil, List.prod_nil,
      applyAsDifferentialOperator_one] using fun _ => And.intro hp (fun _ => hp0)
  | succ j ih =>
    intro hj
    have hj' : j < l.length := by lia
    have hc : 0 ≤ l[j] := hl _ (List.getElem_mem hj')
    have hprev := ih (by lia)
    rw [List.take_succ_eq_append_getElem hj', List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton, mul_comm _ (X + C l[j]),
      applyAsDifferentialOperator_mul, applyAsDifferentialOperator_X_add_C]
    refine ⟨(interl_derivative_add_C_mul hprev.1 hc).1, ?_⟩
    intro hne
    have hpne : applyAsDifferentialOperator
        ((l.take j).map (fun c => X + C c)).prod p ≠ 0 := by
      intro hz
      simp only [hz, derivative_zero, mul_zero, add_zero, ne_eq, not_true_eq_false] at hne
    exact Or.resolve_left
      (eq_zero_or_coeff_zero_pos_derivative_add_C_mul hprev.1 (hprev.2 hpne) hc) hne

/-- If a kernel intertwines `P(D)` with `D + P(0)`, lower-degree interlacing
preservation puts every differential-factor prefix before its seed image. -/
theorem interl_map_differential_prefix
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {P : ℝ[X]} {a : ℝ} (ha : 0 < a)
    (l : List ℝ) (hl : ∀ c ∈ l, 0 ≤ c)
    (hP : P = C a * (l.map (fun c => X + C c)).prod)
    (hP0 : 0 ≤ P.coeff 0)
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hidentity : ∀ p, T (applyAsDifferentialOperator P p) =
      (T p).derivative + C (P.coeff 0) * T p)
    {D : ℕ}
    (hmap : ∀ {p}, IsPFPolynomial p → p.natDegree ≤ D → IsPFPolynomial (T p))
    (hinterl : ∀ {f g}, IsPFPolynomial f → IsPFPolynomial g →
      f.natDegree ≤ D → g.natDegree ≤ D → Interl f g → Interl (T f) (T g))
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : 0 < p.coeff 0) (hpdeg : p.natDegree ≤ D) :
    ∀ j ≤ l.length,
      Interl (T (applyAsDifferentialOperator
        ((l.take j).map (fun c => X + C c)).prod p)) (T p) := by
  let Q (j : ℕ) := applyAsDifferentialOperator
    ((l.take j).map (fun c => X + C c)).prod p
  let c (j : ℕ) := l[j]?.getD 0
  have hstep (j : ℕ) (hj : j < l.length) :
      Q (j + 1) = (Q j).derivative + C (c j) * Q j := by
    simp only [Q, c, List.take_succ_eq_append_getElem hj, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton,
      List.getElem?_eq_getElem hj, Option.getD_some]
    rw [mul_comm _ (X + C l[j]), applyAsDifferentialOperator_mul,
      applyAsDifferentialOperator_X_add_C]
  have hpf (j : ℕ) (hj : j ≤ l.length) := (differential_prefix_pos l hl hp hp0 j hj).1
  have hq0 : Q 0 = p := by
    simp only [Q, List.take_zero, List.map_nil, List.prod_nil,
      applyAsDifferentialOperator_one]
  have hqdeg (j : ℕ) : (Q j).natDegree ≤ D :=
    (natDegree_applyAsDifferentialOperator_le _ _).trans hpdeg
  have hlast : C a * T (Q l.length) = (T p).derivative + C (P.coeff 0) * T p := by
    rw [← hidentity, hP, applyAsDifferentialOperator_C_mul, Polynomial.linearMap_C_mul]
    simp only [Q, List.take_length]
  have hend : Interl (T (Q l.length)) (T p) := by
    have h := (interl_derivative_add_C_mul (hmap hp hpdeg) hP0).2
    rw [← hlast] at h
    have h' := h.C_mul_left_of_nonneg (inv_nonneg.mpr ha.le)
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha.ne', map_one, one_mul] using h'
  have hdeg (hz : T (Q l.length) = 0) : (T p).natDegree = 0 := by
    have hh : (T p).derivative + C (P.coeff 0) * T p = 0 := by
      rw [← hlast, hz, mul_zero]
    apply derivative_eq_zero.mp
    ext j
    have hj := congrArg (fun q : ℝ[X] => q.coeff j) hh
    simp only [coeff_add, coeff_C_mul, coeff_zero] at hj
    have hd := (hTnn p hp.hasNonnegCoeffs).derivative j
    have hn := mul_nonneg hP0 (hTnn p hp.hasNonnegCoeffs j)
    simpa only [coeff_zero] using (show (T p).derivative.coeff j = 0 by linarith)
  have h := interl_map_differential_chain T Q c l.length hstep
    (fun j hj => (differential_prefix_pos l hl hp hp0 j hj).2) hTc
    (fun j hj => hinterl (hpf _ (by lia)) (hpf _ (by lia)) (hqdeg _) (hqdeg _)
      (by
        rw [hstep j hj]
        exact (interl_derivative_add_C_mul (hpf _ (by lia))
          (by simpa only [c, List.getElem?_eq_getElem hj, Option.getD_some] using
            hl _ (List.getElem_mem hj))).2))
    (by simpa only [hq0] using hend) (by simpa only [hq0] using hdeg)
  simpa only [hq0] using h

/-- A finite sum of differential symbols acts as the sum of their operators. -/
private theorem applyDifferential_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ[X]) (p : ℝ[X]) :
    applyAsDifferentialOperator (∑ i ∈ s, f i) p =
      ∑ i ∈ s, applyAsDifferentialOperator (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [sum_empty, sum_empty, show (0 : ℝ[X]) = C 0 from C_0.symm,
      applyAsDifferentialOperator_C, C_0, zero_mul]
  | @insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi, applyAsDifferentialOperator_add, ih]

/-- Lower-degree preservation and the polynomial-symbol identity place
`T(P'(D)p)` before `Tp`. Each deletion is a prefix after ordering its omitted
factor last. No positivity of the root parameters is required. -/
theorem interl_map_applyDifferential_derivative
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) {P : ℝ[X]} (hP : IsPFPolynomial P) (hPne : P ≠ 0)
    (hTnn : ∀ p, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hidentity : ∀ p, T (applyAsDifferentialOperator P p) =
      (T p).derivative + C (P.coeff 0) * T p)
    {D : ℕ}
    (hmap : ∀ {p}, IsPFPolynomial p → p.natDegree ≤ D → IsPFPolynomial (T p))
    (hinterl : ∀ {f g}, IsPFPolynomial f → IsPFPolynomial g →
      f.natDegree ≤ D → g.natDegree ≤ D → Interl f g → Interl (T f) (T g))
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : 0 < p.coeff 0) (hpdeg : p.natDegree ≤ D) :
    Interl (T (applyAsDifferentialOperator P.derivative p)) (T p) := by
  classical
  obtain ⟨z, hz, hfac⟩ := hP.splits.exists_fin_eq_C_mul_prod
  let r (i : Fin P.natDegree) : ℝ := -z i
  have hr (i : Fin P.natDegree) : 0 ≤ r i := by
    apply neg_nonneg.mpr
    apply hP.roots_nonpos
    rw [← hz]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  have hfac' : P = C P.leadingCoeff * ∏ i : Fin P.natDegree, (X + C (r i)) := by
    simpa only [r, sub_eq_add_neg, map_neg] using hfac
  have ha : 0 < P.leadingCoeff := hP.hasNonnegCoeffs.pos_leadingCoeff hPne
  have hdel (i : Fin P.natDegree) :
      Interl (T (applyAsDifferentialOperator
        (∏ j ∈ (univ : Finset (Fin P.natDegree)).erase i, (X + C (r j))) p)) (T p) := by
    let s : Finset (Fin P.natDegree) := univ.erase i
    let l := s.toList.map r ++ [r i]
    have hl : ∀ c ∈ l, 0 ≤ c := by
      intro c hc
      simp only [l, List.mem_append, List.mem_map, List.mem_singleton] at hc
      rcases hc with ⟨j, _, rfl⟩ | rfl
      · exact hr j
      · exact hr i
    have hPl : P = C P.leadingCoeff * (l.map (fun c => X + C c)).prod := by
      calc
        P = C P.leadingCoeff * ∏ j : Fin P.natDegree, (X + C (r j)) := hfac'
        _ = _ := by
          congr 1
          simp only [l, List.map_append, List.prod_append, List.map_map,
            List.map_singleton, List.prod_singleton, Finset.prod_map_toList]
          exact (Finset.prod_erase_mul (univ : Finset (Fin P.natDegree))
            (fun j => X + C (r j)) (mem_univ i)).symm
    have H := interl_map_differential_prefix T ha l hl hPl (hP.hasNonnegCoeffs 0)
      hTnn hTc hidentity hmap hinterl hp hp0 hpdeg
      (s.toList.map r).length (by simp only [l, List.length_append, List.length_singleton]; lia)
    simpa only [l, List.take_left, List.map_map, Finset.prod_map_toList, Function.comp_def] using H
  have hd : P.derivative = C P.leadingCoeff *
      ∑ i : Fin P.natDegree,
        ∏ j ∈ (univ : Finset (Fin P.natDegree)).erase i, (X + C (r j)) := by
    conv_lhs => rw [hfac']
    rw [derivative_C_mul, derivative_prod_finset]
    simp only [map_add, derivative_X, derivative_C, add_zero, mul_one]
  rw [hd, applyAsDifferentialOperator_C_mul, applyDifferential_sum,
    Polynomial.linearMap_C_mul, map_sum]
  apply Interl.C_mul_left_of_nonneg _ ha.le
  apply Interl.finsetSum_right_of_nonneg
  · intro i _
    exact hdel i
  · intro i _
    apply hTnn
    apply hasNonnegCoeffs_applyAsDifferentialOperator
    · exact hasNonnegCoeffs_finsetProd _ _ fun j _ => hasNonnegCoeffs_X_add_C (hr j)
    · exact hp.hasNonnegCoeffs

end RealRooted.ExponentialRows
