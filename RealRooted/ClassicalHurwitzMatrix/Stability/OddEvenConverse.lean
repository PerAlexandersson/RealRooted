import RealRooted.ClassicalHurwitzMatrix.Stability.Closure
import RealRooted.ClassicalHurwitzMatrix.Stability.CoefficientSigns
import RealRooted.ClassicalHurwitzMatrix.Stability.Extraction
import RealRooted.ClassicalHurwitzMatrix.Stability.Routh
import RealRooted.PFPolynomial.Closure
import RealRooted.VeroneseSection

/-!
# Converse odd/even Hermite--Biehler theorem

For real polynomials `p` and `q`, Hurwitz stability of `q(x²) + x p(x²)` forces
`StrictInterl p q`.  Together with the forward theorem
`isHurwitzStable_oddEvenPolynomial_of_strictInterl`, this characterizes Hurwitz
stability of odd/even polynomials in `isHurwitzStable_oddEvenPolynomial_iff`.

The proof passes to a limit of strictly stable instances.  For `r > 0`, the
translate `F(x + r)` of a Hurwitz-stable `F` is strictly Hurwitz stable, so its
odd and even parts strictly interlace by the Routh step.  Their coefficients
depend continuously on `r`, and `interl_of_pf_coeff_tendsto_of_natDegree_le`
keeps the interlacing orientation in the limit `r → 0`.

As a consequence, the conformal substitution
`hermiteBiehlerStableToHurwitzOddEven` is reversible:
`IsHurwitzStable.isUpperHalfPlaneStable_hermiteBiehlerPolynomial`.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- The odd and even parts of a polynomial of positive degree whose
coefficients are positive up to its degree have positive leading coefficients
and one of the two odd/even degree shapes. -/
private theorem contract_two_parts_of_coeff_pos {G : ℝ[X]}
    (hG : ∀ k ≤ G.natDegree, 0 < G.coeff k) (hdeg : G.natDegree ≠ 0) :
    HasPosLeadingCoeff (contract 2 G.divX) ∧ HasPosLeadingCoeff (contract 2 G) ∧
      ((contract 2 G).natDegree = (contract 2 G.divX).natDegree + 1 ∨
        (contract 2 G).natDegree = (contract 2 G.divX).natDegree) := by
  have hodd : ∀ m, 2 * m + 1 ≤ G.natDegree → G.natDegree ≤ 2 * m + 2 →
      (contract 2 G.divX).natDegree = m ∧ HasPosLeadingCoeff (contract 2 G.divX) := by
    intro m hlo hhi
    have hcoeff : (contract 2 G.divX).coeff m = G.coeff (2 * m + 1) := by
      rw [coeff_contract (by decide), coeff_divX, mul_comm]
    have hm : (contract 2 G.divX).natDegree = m :=
      natDegree_eq_of_le_of_coeff_ne_zero
        (natDegree_contract_two_divX_le_of_natDegree_le hhi)
        (hcoeff ▸ (hG _ hlo).ne')
    refine ⟨hm, ?_⟩
    rw [HasPosLeadingCoeff, leadingCoeff, hm, hcoeff]
    exact hG _ hlo
  have heven : ∀ m, 2 * m ≤ G.natDegree → G.natDegree ≤ 2 * m + 1 →
      (contract 2 G).natDegree = m ∧ HasPosLeadingCoeff (contract 2 G) := by
    intro m hlo hhi
    have hcoeff : (contract 2 G).coeff m = G.coeff (2 * m) := by
      rw [coeff_contract (by decide), mul_comm]
    have hm : (contract 2 G).natDegree = m :=
      natDegree_eq_of_le_of_coeff_ne_zero
        (natDegree_contract_two_le_of_natDegree_le hhi)
        (hcoeff ▸ (hG _ hlo).ne')
    refine ⟨hm, ?_⟩
    rw [HasPosLeadingCoeff, leadingCoeff, hm, hcoeff]
    exact hG _ hlo
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' G.natDegree
  · obtain ⟨hod, hop⟩ := hodd (m - 1) (by lia) (by lia)
    obtain ⟨hed, hep⟩ := heven m (by lia) (by lia)
    exact ⟨hop, hep, Or.inl (by lia)⟩
  · obtain ⟨hod, hop⟩ := hodd m (by lia) (by lia)
    obtain ⟨hed, hep⟩ := heven m (by lia) (by lia)
    exact ⟨hop, hep, Or.inr (by lia)⟩

/-- Converse odd/even Hermite--Biehler theorem: if `q(x²) + x p(x²)` is Hurwitz
stable and `p`, `q` are nonzero, then `p` interlaces `q`.

Related: `isHurwitzStable_oddEvenPolynomial_of_strictInterl` is the forward
direction. -/
theorem strictInterl_of_isHurwitzStable_oddEvenPolynomial {p q : ℝ[X]}
    (hp : p ≠ 0) (hq : q ≠ 0) (hstable : IsHurwitzStable (oddEvenPolynomial p q)) :
    StrictInterl p q := by
  set F := oddEvenPolynomial p q with hF
  have hFpos : HasPosLeadingCoeff F :=
    hstable.hasNonnegCoeffs.pos_leadingCoeff (oddEvenPolynomial_ne_zero_iff.mpr (Or.inl hp))
  have hFdeg : F.natDegree ≠ 0 := by
    rw [hF, natDegree_oddEvenPolynomial hp]
    lia
  let G : ℝ → ℝ[X] := fun r => F.comp (X + C r)
  have hGdeg : ∀ r, (G r).natDegree = F.natDegree := fun r => by
    simp [G, natDegree_comp]
  have hGpos : ∀ r, HasPosLeadingCoeff (G r) := fun r => by
    rw [HasPosLeadingCoeff, leadingCoeff_comp (by simp), leadingCoeff_X_add_C, one_pow,
      mul_one]
    exact hFpos
  let s : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hs : ∀ k, 0 < s k := fun k => by positivity
  have hcoeff : ∀ k, ∀ i ≤ (G (s k)).natDegree, 0 < (G (s k)).coeff i := fun k _ hi =>
    (hstable.strictlyStable_comp_X_add_C (hs k)).coeff_pos (hGpos _) hi
  have hnn : ∀ k, HasNonnegCoeffs (G (s k)) := fun k i => by
    by_cases hi : i ≤ (G (s k)).natDegree
    · exact (hcoeff k i hi).le
    · rw [coeff_eq_zero_of_natDegree_lt (by lia)]
  let odd : ℕ → ℝ[X] := fun k => contract 2 (G (s k)).divX
  let even : ℕ → ℝ[X] := fun k => contract 2 (G (s k))
  have hoddEven : ∀ k, oddEvenPolynomial (odd k) (even k) = G (s k) := fun k =>
    oddEvenPolynomial_contract_divX_contract _
  have hinterl : ∀ k, StrictInterl (odd k) (even k) := by
    intro k
    obtain ⟨ho, he, hshape⟩ :=
      contract_two_parts_of_coeff_pos (hcoeff k) ((hGdeg _).trans_ne hFdeg)
    have hstrict : IsStrictlyHurwitzStable (oddEvenPolynomial (odd k) (even k)) := by
      rw [hoddEven]
      exact hstable.strictlyStable_comp_X_add_C (hs k)
    rcases hshape with hshape | hshape
    · exact hstrict.strictInterl_parts_of_evenShape ho he hshape
    · exact hstrict.strictInterl_parts_of_oddShape ho he hshape
  have hoddPF : ∀ k, IsPFPolynomial (odd k) := fun k =>
    IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_left_of_oddEvenPolynomial ((hoddEven k).symm ▸ hnn k))
      (hinterl k).1.2
  have hevenPF : ∀ k, IsPFPolynomial (even k) := fun k =>
    IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_right_of_oddEvenPolynomial ((hoddEven k).symm ▸ hnn k))
      (hinterl k).2.1.2
  have hlim : ∀ j, Tendsto (fun k => (G (s k)).coeff j) atTop (𝓝 (F.coeff j)) := by
    intro j
    have h := ((F.continuous_coeff_comp_X_add_C j).tendsto 0).comp
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [C_0, add_zero, comp_X] at h
    exact h
  have hlimit : Interl p q := by
    refine interl_of_pf_coeff_tendsto_of_natDegree_le (N := F.natDegree) hoddPF hevenPF
      (fun k => Or.inr (Or.inr (hinterl k)))
      (fun k => natDegree_contract_two_divX_le_of_natDegree_le (by rw [hGdeg]; lia))
      (fun k => natDegree_contract_two_le_of_natDegree_le (by rw [hGdeg]; lia))
      (fun i => ?_) (fun i => ?_)
    · have h := hlim (2 * i + 1)
      rw [hF, coeff_oddEvenPolynomial_odd] at h
      simpa only [odd, coeff_contract two_ne_zero, coeff_divX, mul_comm i 2] using h
    · have h := hlim (2 * i)
      rw [hF, coeff_oddEvenPolynomial_even] at h
      simpa only [even, coeff_contract two_ne_zero, mul_comm i 2] using h
  rcases hlimit with h | h | h
  · exact absurd h hp
  · exact absurd h hq
  · exact h

/-- Hermite--Biehler theorem for odd/even polynomials: for nonzero `p` and
`q`, the polynomial `q(x²) + x p(x²)` is Hurwitz stable exactly when `p` and
`q` have nonnegative coefficients and `p` interlaces `q`. -/
theorem isHurwitzStable_oddEvenPolynomial_iff {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    IsHurwitzStable (oddEvenPolynomial p q) ↔
      HasNonnegCoeffs p ∧ HasNonnegCoeffs q ∧ StrictInterl p q :=
  ⟨fun h => ⟨hasNonnegCoeffs_left_of_oddEvenPolynomial h.hasNonnegCoeffs,
      hasNonnegCoeffs_right_of_oddEvenPolynomial h.hasNonnegCoeffs,
      strictInterl_of_isHurwitzStable_oddEvenPolynomial hp hq h⟩,
    fun ⟨hpnn, hqnn, hpq⟩ => isHurwitzStable_oddEvenPolynomial_of_strictInterl hpnn hqnn hpq⟩

/-- Converse of the conformal substitution `hermiteBiehlerStableToHurwitzOddEven`:
if `q(x²) + x p(x²)` is Hurwitz stable, then `q + i p` has no zeros in the open
upper half-plane. -/
theorem IsHurwitzStable.isUpperHalfPlaneStable_hermiteBiehlerPolynomial {p q : ℝ[X]}
    (h : IsHurwitzStable (oddEvenPolynomial p q)) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p) := by
  by_cases hp : p = 0
  · subst hp
    exact isUpperHalfPlaneStable_hermiteBiehler_of_rhp_left_zero h.rightHalfPlaneStable
  by_cases hq : q = 0
  · subst hq
    exact isUpperHalfPlaneStable_hermiteBiehler_of_rhp_right_zero h.rightHalfPlaneStable
  obtain ⟨hpnn, hqnn, hpq⟩ := (isHurwitzStable_oddEvenPolynomial_iff hp hq).mp h
  exact hermiteBiehlerForwardPos (hqnn.pos_leadingCoeff hq) (hpnn.pos_leadingCoeff hp) hpq

end RealRooted
