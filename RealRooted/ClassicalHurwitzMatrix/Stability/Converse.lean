import RealRooted.ClassicalHurwitzMatrix.Stability.Criterion
import RealRooted.ClassicalHurwitzMatrix.Stability.Routh.Reverse

/-!
# Converse strict Hurwitz criterion

Positivity of the leading classical Hurwitz determinants is propagated down
the canonical Routh reduction and then converted back to root location.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- For a polynomial of degree at least two, its canonical Routh reduction
has degree exactly one less and positive leading coefficient. -/
theorem canonicalRouthReducedPolynomial_degree_and_pos {p : ℝ[X]}
    (hlead : HasPosLeadingCoeff p) (hdegree : 2 ≤ p.natDegree) (c : ℝ) :
    let odd := Polynomial.contract 2 p.divX
    let even := Polynomial.contract 2 p
    let q := routhReducedPolynomial c odd even
    q.natDegree + 1 = p.natDegree ∧ HasPosLeadingCoeff q := by
  let odd := Polynomial.contract 2 p.divX
  let even := Polynomial.contract 2 p
  let red := routhReducedOddPart c odd even
  let q := routhReducedPolynomial c odd even
  have htop : 0 < p.coeff p.natDegree := by
    simpa [HasPosLeadingCoeff] using hlead
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' p.natDegree
  · cases k with
    | zero => exact (by simp_all)
    | succ k =>
        have hevenDegree : even.natDegree = k + 1 := by
          apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
          · apply natDegree_contract_two_le_of_natDegree_le
            lia
          · simpa [even, Polynomial.coeff_contract, hk, Nat.mul_comm]
              using htop.ne'
        have hoddDegree : odd.natDegree ≤ k := by
          apply natDegree_contract_two_divX_le_of_natDegree_le
          lia
        have hdominant : (Polynomial.C c * odd).natDegree < even.natDegree := by
          calc
            (Polynomial.C c * odd).natDegree ≤ odd.natDegree :=
              Polynomial.natDegree_C_mul_le c odd
            _ ≤ k := hoddDegree
            _ < even.natDegree := by rw [hevenDegree]; lia
        have hredDegree : red.natDegree = k := by
          change (routhReducedOddPart c odd even).natDegree = k
          rw [routhReducedOddPart,
            Polynomial.natDegree_divX_eq_natDegree_tsub_one,
            Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdominant,
            hevenDegree]
          lia
        have hredPos : HasPosLeadingCoeff red := by
          unfold HasPosLeadingCoeff Polynomial.leadingCoeff
          rw [hredDegree]
          change 0 < (routhReducedOddPart c odd even).coeff k
          rw [coeff_routhReducedOddPart]
          have hoddTop : odd.coeff (k + 1) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by lia)
          rw [hoddTop, mul_zero, sub_zero]
          change 0 < (Polynomial.contract 2 p).coeff (k + 1)
          rw [Polynomial.coeff_contract (by decide), Nat.mul_comm]
          simpa [hk] using htop
        have hqDegree : q.natDegree = 2 * k + 1 := by
          change (routhReducedPolynomial c odd even).natDegree = 2 * k + 1
          rw [routhReducedPolynomial,
            natDegree_oddEvenPolynomial hredPos.ne_zero, hredDegree,
            max_eq_right (by lia)]
        refine ⟨?_, ?_⟩
        · rw [hqDegree, hk]
          lia
        · unfold HasPosLeadingCoeff Polynomial.leadingCoeff
          rw [hqDegree]
          change 0 < (routhReducedPolynomial c odd even).coeff (2 * k + 1)
          rw [routhReducedPolynomial, coeff_oddEvenPolynomial_odd]
          unfold HasPosLeadingCoeff Polynomial.leadingCoeff at hredPos
          rwa [hredDegree] at hredPos
  · have hoddDegree : odd.natDegree = k := by
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      · apply natDegree_contract_two_divX_le_of_natDegree_le
        lia
      · change (Polynomial.contract 2 p.divX).coeff k ≠ 0
        rw [Polynomial.coeff_contract (by decide),
          Polynomial.coeff_divX, Nat.mul_comm]
        simpa [hk] using htop.ne'
    have hevenDegree : even.natDegree ≤ k := by
      apply natDegree_contract_two_le_of_natDegree_le
      lia
    have hredDegree : red.natDegree ≤ k - 1 := by
      change (routhReducedOddPart c odd even).natDegree ≤ k - 1
      rw [routhReducedOddPart,
        Polynomial.natDegree_divX_eq_natDegree_tsub_one]
      apply Nat.sub_le_sub_right
      calc
        (even - Polynomial.C c * odd).natDegree ≤
            max even.natDegree (Polynomial.C c * odd).natDegree :=
          Polynomial.natDegree_sub_le _ _
        _ ≤ k := max_le hevenDegree (by
          calc
            (Polynomial.C c * odd).natDegree ≤ odd.natDegree :=
              Polynomial.natDegree_C_mul_le c odd
            _ = k := hoddDegree)
    have hqDegree : q.natDegree = 2 * k := by
      change (routhReducedPolynomial c odd even).natDegree = 2 * k
      rw [routhReducedPolynomial, oddEvenPolynomial]
      by_cases hredZero : red = 0
      · simp [red, hredZero, natDegree_comp_X_sq, hoddDegree]
      · have hrightDegree := natDegree_X_mul_comp_X_sq hredZero
        have hleftDegree := natDegree_comp_X_sq odd
        rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt (by
          rw [hrightDegree, hleftDegree, hoddDegree]
          lia), hleftDegree, hoddDegree]
    refine ⟨?_, ?_⟩
    · rw [hqDegree, hk]
    · unfold HasPosLeadingCoeff Polynomial.leadingCoeff
      rw [hqDegree]
      change 0 < (routhReducedPolynomial c odd even).coeff (2 * k)
      rw [routhReducedPolynomial, coeff_oddEvenPolynomial_even]
      change 0 < (Polynomial.contract 2 p.divX).coeff k
      rw [Polynomial.coeff_contract (by decide), Polynomial.coeff_divX,
        Nat.mul_comm]
      simpa [hk] using htop

end RealRooted

namespace Matrix

open RealRooted

/-- Positive leading coefficient and positive leading Hurwitz determinants
through the polynomial degree imply strict Hurwitz stability. -/
theorem strictlyHurwitzStable_of_hurwitzLeadingPrincipal_det_pos
    {p : ℝ[X]} (hlead : HasPosLeadingCoeff p)
    (hdet : ∀ n, 0 < n → n ≤ p.natDegree →
      0 < (hurwitzLeadingPrincipal p.coeff n).det) :
    IsStrictlyHurwitzStable p := by
  by_cases hdegreeZero : p.natDegree = 0
  · have hp : p = Polynomial.C (p.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hdegreeZero
    rw [hp] at hlead ⊢
    apply (IsStrictlyHurwitzStable.C _).2
    simpa using hlead.ne'
  by_cases hdegreeOne : p.natDegree = 1
  · have hconstant : 0 < p.coeff 0 := by
      simpa using hdet 1 (by simp) (by rw [hdegreeOne])
    have hlinear : 0 < p.coeff 1 := by
      simpa [HasPosLeadingCoeff, Polynomial.leadingCoeff, hdegreeOne]
        using hlead
    have hp := Polynomial.eq_X_add_C_of_natDegree_le_one
      (show p.natDegree ≤ 1 by rw [hdegreeOne])
    rw [hp]
    have hfactor :
        Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) =
          Polynomial.C (p.coeff 1) *
            (Polynomial.X + Polynomial.C (p.coeff 0 / p.coeff 1)) := by
      rw [mul_add, ← Polynomial.C_mul]
      field_simp
    rw [hfactor]
    apply IsStrictlyHurwitzStable.mul
    · exact (IsStrictlyHurwitzStable.C _).2 hlinear.ne'
    · apply (IsStrictlyHurwitzStable.X_add_C _).2
      exact div_pos hconstant hlinear
  have hdegreeTwo : 2 ≤ p.natDegree := by lia
  let odd := Polynomial.contract 2 p.divX
  let even := Polynomial.contract 2 p
  let c := routhCoefficient odd even
  let q := routhReducedPolynomial c odd even
  have hreconstruct : oddEvenPolynomial odd even = p := by
    exact oddEvenPolynomial_contract_divX_contract p
  have hevenZero : 0 < even.coeff 0 := by
    have hfirst := hdet 1 (by simp) (by lia)
    rw [← hreconstruct] at hfirst
    rw [Matrix.hurwitzLeadingPrincipal_det_one] at hfirst
    change 0 < (oddEvenPolynomial odd even).coeff (2 * 0) at hfirst
    rw [coeff_oddEvenPolynomial_even] at hfirst
    exact hfirst
  have hoddZero : 0 < odd.coeff 0 := by
    have hsecond := hdet 2 (by simp) hdegreeTwo
    rw [← hreconstruct] at hsecond
    have hproduct : 0 < even.coeff 0 * odd.coeff 0 := by
      rw [Matrix.hurwitzLeadingPrincipal_det_two] at hsecond
      change 0 < (oddEvenPolynomial odd even).coeff (2 * 0) *
        (oddEvenPolynomial odd even).coeff (2 * 0 + 1) at hsecond
      rw [coeff_oddEvenPolynomial_even,
        coeff_oddEvenPolynomial_odd] at hsecond
      exact hsecond
    exact (mul_pos_iff_of_pos_left hevenZero).mp hproduct
  have hc : 0 < c := routhCoefficient_pos hoddZero hevenZero
  have hzero : even.coeff 0 = c * odd.coeff 0 :=
    routhCoefficient_mul_coeff_zero odd even hoddZero.ne'
  obtain ⟨hqDegree, hqLead⟩ :=
    canonicalRouthReducedPolynomial_degree_and_pos hlead hdegreeTwo c
  have hqDet : ∀ n, 0 < n → n ≤ q.natDegree →
      0 < (hurwitzLeadingPrincipal q.coeff n).det := by
    intro n hn hnq
    apply (hurwitzLeadingPrincipal_oddEvenPolynomial_det_succ_pos_iff
      c odd even hzero hevenZero n).mp
    rw [hreconstruct]
    apply hdet (n + 1) (by lia)
    lia
  have hqStable := strictlyHurwitzStable_of_hurwitzLeadingPrincipal_det_pos
    hqLead hqDet
  have hqDegreeNe : q.natDegree ≠ 0 := by lia
  have hparts : HasPosLeadingCoeff (routhReducedOddPart c odd even) ∧
      HasPosLeadingCoeff odd ∧
      (odd.natDegree = (routhReducedOddPart c odd even).natDegree + 1 ∨
        odd.natDegree = (routhReducedOddPart c odd even).natDegree) := by
    simpa [q, routhReducedPolynomial] using
      hqStable.canonicalParityData hqLead hqDegreeNe
  rw [← hreconstruct]
  exact hqStable.oddEvenPolynomial_of_routhReducedPolynomial
    hc hzero hparts.2.1 hparts.1 hparts.2.2
termination_by p.natDegree
decreasing_by lia

end Matrix
