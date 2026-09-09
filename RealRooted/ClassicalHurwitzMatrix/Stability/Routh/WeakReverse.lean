import RealRooted.ClassicalHurwitzMatrix.Stability.ClosedLimit
import RealRooted.ClassicalHurwitzMatrix.Stability.Closure
import RealRooted.ClassicalHurwitzMatrix.Stability.Routh.Reverse

/-!
# Weak reverse stability across a nonterminal Routh step

This module propagates weak Hurwitz stability back across a positive Routh
step when the reduced polynomial is nonconstant. The proof translates the
reduced polynomial to obtain strict approximants, applies the strict reverse
Routh theorem, and passes to the limit through the closed-root API.
-/

open Polynomial Filter Topology

noncomputable section

namespace RealRooted

private theorem routhApproxSource_eq (c : ℝ) (u : ℝ[X]) :
    oddEvenPolynomial (Polynomial.contract 2 u)
        (C c * Polynomial.contract 2 u +
          X * Polynomial.contract 2 u.divX) =
      X * u + C c * (Polynomial.contract 2 u).comp (X ^ 2) := by
  have hu := oddEvenPolynomial_contract_divX_contract u
  unfold oddEvenPolynomial at hu ⊢
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_comp]
  linear_combination X * hu

private theorem routhApproxSource_degree_leadingCoeff (c : ℝ) {u : ℝ[X]}
    (hu : u ≠ 0) :
    let source := oddEvenPolynomial (Polynomial.contract 2 u)
      (C c * Polynomial.contract 2 u +
        X * Polynomial.contract 2 u.divX)
    source.natDegree = u.natDegree + 1 ∧ source.leadingCoeff = u.leadingCoeff := by
  let evenTerm := C c * (Polynomial.contract 2 u).comp (X ^ 2)
  let mainTerm := X * u
  have hcontract : (Polynomial.contract 2 u).natDegree ≤ u.natDegree / 2 := by
    apply natDegree_contract_two_le_of_natDegree_le
    have hmod := Nat.mod_lt u.natDegree (by decide : 0 < 2)
    have hdecomp := Nat.mod_add_div u.natDegree 2
    lia
  have hevenTerm : evenTerm.natDegree ≤ u.natDegree := by
    exact (Polynomial.natDegree_C_mul_le c _).trans (by
      rw [natDegree_comp_X_sq]
      calc
        2 * (Polynomial.contract 2 u).natDegree ≤
            2 * (u.natDegree / 2) := Nat.mul_le_mul_left 2 hcontract
        _ = (u.natDegree / 2) * 2 := by ring
        _ ≤ u.natDegree := Nat.div_mul_le_self _ _)
  have hmainTerm : mainTerm.natDegree = u.natDegree + 1 := by
    dsimp only [mainTerm]
    rw [Polynomial.natDegree_mul (by simp) hu, Polynomial.natDegree_X]
    ring
  have hsmall : evenTerm.natDegree < mainTerm.natDegree := by
    rw [hmainTerm]
    lia
  have hsource :
      oddEvenPolynomial (Polynomial.contract 2 u)
          (C c * Polynomial.contract 2 u +
            X * Polynomial.contract 2 u.divX) = mainTerm + evenTerm := by
    exact routhApproxSource_eq c u
  dsimp only
  rw [hsource]
  constructor
  · rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hsmall, hmainTerm]
  · rw [Polynomial.leadingCoeff_add_of_degree_lt'
      (Polynomial.degree_lt_degree hsmall)]
    simp [mainTerm]

private theorem eval_complexify_contract_two (u : ℝ[X]) (z : ℂ) :
    (complexify (Polynomial.contract 2 u)).eval (z ^ 2) =
      ((complexify u).eval z + (complexify u).eval (-z)) / 2 := by
  have hpos := congrArg (fun p : ℝ[X] => (complexify p).eval z)
    (oddEvenPolynomial_contract_divX_contract u)
  have hneg := congrArg (fun p : ℝ[X] => (complexify p).eval (-z))
    (oddEvenPolynomial_contract_divX_contract u)
  simp only [eval_complexify_oddEvenPolynomial] at hpos hneg
  simp only [neg_sq, neg_mul] at hneg
  linear_combination (hpos + hneg) / 2

private theorem eval_complexify_routhApproxSource (c : ℝ) (u : ℝ[X])
    (z : ℂ) :
    (complexify (oddEvenPolynomial (Polynomial.contract 2 u)
      (C c * Polynomial.contract 2 u +
        X * Polynomial.contract 2 u.divX))).eval z =
      z * (complexify u).eval z +
        (c / 2 : ℂ) * ((complexify u).eval z + (complexify u).eval (-z)) := by
  rw [eval_complexify_oddEvenPolynomial]
  have heven :
      (complexify (C c * Polynomial.contract 2 u +
        X * Polynomial.contract 2 u.divX)).eval (z ^ 2) =
        (c : ℂ) * (complexify (Polynomial.contract 2 u)).eval (z ^ 2) +
          z ^ 2 * (complexify (Polynomial.contract 2 u.divX)).eval (z ^ 2) := by
    simp [complexify]
  rw [heven]
  have hcontract := eval_complexify_contract_two u z
  have hu := congrArg (fun p : ℝ[X] => (complexify p).eval z)
    (oddEvenPolynomial_contract_divX_contract u)
  simp only [eval_complexify_oddEvenPolynomial] at hu
  linear_combination z * hu + (c : ℂ) * hcontract

/-- Weak Hurwitz stability of a nonconstant Routh reduction propagates back to
the source polynomial across a positive Routh step. -/
theorem IsHurwitzStable.oddEvenPolynomial_of_routhReducedPolynomial_of_natDegree_ne_zero
    {c : ℝ} {odd even : ℝ[X]}
    (hq : IsHurwitzStable (routhReducedPolynomial c odd even))
    (hc : 0 < c) (hodd0 : 0 < odd.coeff 0)
    (h0 : even.coeff 0 = c * odd.coeff 0)
    (hqdegree : (routhReducedPolynomial c odd even).natDegree ≠ 0) :
    IsHurwitzStable (oddEvenPolynomial odd even) := by
  let q := routhReducedPolynomial c odd even
  have hqne : q ≠ 0 := by
    intro hqzero
    have hne := hq.rightHalfPlaneStable (1 : ℂ) (by norm_num)
    simp [q, hqzero] at hne
  have hqlead : HasPosLeadingCoeff q :=
    hq.hasNonnegCoeffs.pos_leadingCoeff hqne
  have hqdegree' : q.natDegree ≠ 0 := by simpa only [q] using hqdegree
  let ε : ℕ → ℝ := fun k => 1 / (k + 1)
  let qe : ℕ → ℝ[X] := fun k => q.comp (X + C (ε k))
  let oe : ℕ → ℝ[X] := fun k => Polynomial.contract 2 (qe k)
  let re : ℕ → ℝ[X] := fun k => Polynomial.contract 2 (qe k).divX
  let ee : ℕ → ℝ[X] := fun k => C c * oe k + X * re k
  let pe : ℕ → ℝ[X] := fun k => oddEvenPolynomial (oe k) (ee k)
  have hεpos (k : ℕ) : 0 < ε k := by
    dsimp only [ε]
    positivity
  have hqestable (k : ℕ) : IsStrictlyHurwitzStable (qe k) := by
    dsimp only [qe]
    exact hq.strictlyStable_comp_X_add_C (hεpos k)
  have hqelead (k : ℕ) : HasPosLeadingCoeff (qe k) := by
    dsimp only [qe]
    exact hqlead.comp_X_add_C (ε k)
  have hqedegree (k : ℕ) : (qe k).natDegree = q.natDegree := by
    simp [qe, Polynomial.natDegree_comp]
  have hqene (k : ℕ) : qe k ≠ 0 := (hqestable k).ne_zero
  have hred (k : ℕ) : routhReducedOddPart c (oe k) (ee k) = re k := by
    unfold routhReducedOddPart
    have hsub : ee k - C c * oe k = X * re k := by simp [ee]
    rw [hsub]
    ext n
    simp [Polynomial.coeff_divX]
  have hreduced (k : ℕ) :
      routhReducedPolynomial c (oe k) (ee k) = qe k := by
    rw [routhReducedPolynomial, hred]
    exact oddEvenPolynomial_contract_divX_contract (qe k)
  have hee0 (k : ℕ) : (ee k).coeff 0 = c * (oe k).coeff 0 := by
    simp [ee]
  have hpestable (k : ℕ) : IsStrictlyHurwitzStable (pe k) := by
    obtain ⟨hrelead, hoelead, hshape⟩ :=
      (hqestable k).canonicalParityData (hqelead k) (by
        rw [hqedegree]
        exact hqdegree')
    have hredstable :
        IsStrictlyHurwitzStable (routhReducedPolynomial c (oe k) (ee k)) := by
      simpa only [hreduced k] using hqestable k
    have hrelead' :
        HasPosLeadingCoeff (routhReducedOddPart c (oe k) (ee k)) := by
      rw [hred]
      exact hrelead
    have hshape' :
        (oe k).natDegree =
            (routhReducedOddPart c (oe k) (ee k)).natDegree + 1 ∨
          (oe k).natDegree =
            (routhReducedOddPart c (oe k) (ee k)).natDegree := by
      rw [hred]
      exact hshape
    exact hredstable.oddEvenPolynomial_of_routhReducedPolynomial hc (hee0 k)
      hoelead hrelead' hshape'
  have hpedata (k : ℕ) :
      (pe k).natDegree = q.natDegree + 1 ∧
        (pe k).leadingCoeff = q.leadingCoeff := by
    have hdata := routhApproxSource_degree_leadingCoeff c (hqene k)
    have hqelc : (qe k).leadingCoeff = q.leadingCoeff := by
      dsimp only [qe]
      rw [Polynomial.leadingCoeff_comp (by simp),
        Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
    simpa only [pe, oe, ee, re, hqedegree k, hqelc] using hdata
  have hsource :
      oddEvenPolynomial (Polynomial.contract 2 q)
          (C c * Polynomial.contract 2 q +
            X * Polynomial.contract 2 q.divX) =
        oddEvenPolynomial odd even := by
    have hodd : Polynomial.contract 2 q = odd := by
      simp [q, routhReducedPolynomial]
    have hred' : Polynomial.contract 2 q.divX =
        routhReducedOddPart c odd even := by
      simp [q, routhReducedPolynomial]
    rw [hodd, hred']
    rw [← even_eq_C_mul_odd_add_X_mul_routhReducedOddPart c odd even h0]
  let L := q.leadingCoeff
  have hLpos : 0 < L := hqlead
  let normalized : ℕ → ℝ[X] := fun k => C L⁻¹ * pe k
  let P : ℕ → ℂ[X] := fun k => complexify (normalized k)
  let p₀ : ℂ[X] := complexify (C L⁻¹ * oddEvenPolynomial odd even)
  have hp₀ne : p₀ ≠ 0 := by
    have hsource0 : oddEvenPolynomial odd even ≠ 0 := by
      intro hzero
      have hoddzero := (oddEvenPolynomial_eq_zero_iff.mp hzero).1
      exact hodd0.ne' (by simp [hoddzero])
    dsimp only [p₀, complexify]
    exact Polynomial.map_ne_zero
      (mul_ne_zero (by simp [hLpos.ne']) hsource0)
  have hPmonic (k : ℕ) : (P k).Monic := by
    have hreal : (normalized k).Monic := by
      dsimp only [normalized]
      apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
      rw [(hpedata k).2]
      simp [L, hLpos.ne']
    exact hreal.map _
  have hPdegree (k : ℕ) : (P k).natDegree = q.natDegree + 1 := by
    dsimp only [P, normalized, complexify]
    rw [Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective,
      Polynomial.natDegree_C_mul (inv_ne_zero hLpos.ne'), (hpedata k).1]
  have hPstable (k : ℕ) : IsRightHalfPlaneStable (P k) := by
    intro z hz
    have hne := (hpestable k).rightHalfPlaneStable z hz
    dsimp only [P, normalized, complexify]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
      Polynomial.eval_C]
    exact mul_ne_zero (by simp [hLpos.ne']) hne
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hPeval (z : ℂ) :
      Tendsto (fun k => (P k).eval z) atTop (𝓝 (p₀.eval z)) := by
    have hεcomplex : Tendsto (fun k => (ε k : ℂ)) atTop (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp hεzero
    have hplus : Tendsto (fun k => (complexify (qe k)).eval z) atTop
        (𝓝 ((complexify q).eval z)) := by
      have harg : Tendsto (fun k => z + (ε k : ℂ)) atTop (𝓝 (z + 0)) :=
        tendsto_const_nhds.add hεcomplex
      have ht := (complexify q).continuous.continuousAt.tendsto.comp harg
      change Tendsto (fun k => (complexify q).eval (z + (ε k : ℂ)))
        atTop (𝓝 ((complexify q).eval (z + 0))) at ht
      have ht' : Tendsto (fun k => (complexify q).eval (z + (ε k : ℂ)))
          atTop (𝓝 ((complexify q).eval z)) := by
        simpa only [add_zero] using ht
      simpa [qe, complexify, Polynomial.map_comp, Polynomial.eval_comp] using ht'
    have hminus : Tendsto (fun k => (complexify (qe k)).eval (-z)) atTop
        (𝓝 ((complexify q).eval (-z))) := by
      have harg : Tendsto (fun k => -z + (ε k : ℂ)) atTop (𝓝 (-z + 0)) :=
        tendsto_const_nhds.add hεcomplex
      have ht := (complexify q).continuous.continuousAt.tendsto.comp harg
      change Tendsto (fun k => (complexify q).eval (-z + (ε k : ℂ)))
        atTop (𝓝 ((complexify q).eval (-z + 0))) at ht
      have ht' : Tendsto (fun k => (complexify q).eval (-z + (ε k : ℂ)))
          atTop (𝓝 ((complexify q).eval (-z))) := by
        simpa only [add_zero] using ht
      simpa [qe, complexify, Polynomial.map_comp, Polynomial.eval_comp] using ht'
    have hraw : Tendsto
        (fun k => z * (complexify (qe k)).eval z +
          (c / 2 : ℂ) *
            ((complexify (qe k)).eval z + (complexify (qe k)).eval (-z)))
        atTop
        (𝓝 (z * (complexify q).eval z +
          (c / 2 : ℂ) * ((complexify q).eval z +
            (complexify q).eval (-z)))) :=
      (tendsto_const_nhds.mul hplus).add
        (tendsto_const_nhds.mul (hplus.add hminus))
    have hraw' : Tendsto (fun k => (complexify (pe k)).eval z) atTop
        (𝓝 ((complexify (oddEvenPolynomial odd even)).eval z)) := by
      rw [← hsource]
      simpa only [pe, oe, ee, re,
        eval_complexify_routhApproxSource c] using hraw
    simpa only [P, p₀, normalized, complexify, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C] using
      (tendsto_const_nhds.mul hraw')
  refine ⟨?_, ?_⟩
  · have hqnn : HasNonnegCoeffs q := by simpa only [q] using hq.hasNonnegCoeffs
    have hoddnn := hasNonnegCoeffs_right_of_oddEvenPolynomial hqnn
    have hrednn := hasNonnegCoeffs_left_of_oddEvenPolynomial hqnn
    exact hasNonnegCoeffs_oddEvenPolynomial hoddnn
      (by
        rw [even_eq_C_mul_odd_add_X_mul_routhReducedOddPart c odd even h0]
        exact (nonnegCoeffs_C_mul hc.le hoddnn).add hrednn.X_mul)
  · have hlimit := isRightHalfPlaneStable_of_monic_tendsto_eval
      hp₀ne hPmonic hPdegree hPstable hPeval
    intro z hz hroot
    apply hlimit z hz
    dsimp only [p₀, complexify]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
      Polynomial.eval_C]
    exact mul_eq_zero.mpr (Or.inr hroot)

end RealRooted
