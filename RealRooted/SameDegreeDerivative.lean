import RealRooted.Derivative
import RealRooted.PosCombo
import RealRooted.WagnerX

/-!
# Same-degree positive-combination derivative lemmas

This module records two reusable derivative facts for the same-degree
positive-combination route in the Chudnovsky--Seymour project.
-/

open Polynomial

namespace RealRooted

/-- If all roots of a split polynomial of degree at least two are bounded below
by `c`, then all roots of its derivative are bounded below by `c`.

This is the lower-bound counterpart to the common upper-bound use of
`roots_le_of_prec_right` together with `derivative_interlaces`. -/
theorem le_roots_derivative_of_le_roots {p : ℝ[X]} {c : ℝ}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, c ≤ r) :
    ∀ r ∈ p.derivative.roots, c ≤ r := by
  obtain ⟨_, _, _, rs, ss, _, _, hrs_eq, hss_eq, hint⟩ :=
    derivative_interlaces hp hdeg
  intro s hs
  have hs_ss : s ∈ ss := Multiset.mem_coe.mp (by rw [hss_eq]; exact hs)
  have hrs_ne : rs ≠ [] := by
    rintro rfl
    have hcard : p.roots.card = p.natDegree := card_roots_of_splits hp
    have : (0 : ℕ) = p.roots.card := by
      rw [← hrs_eq]
      simp
    rw [hcard] at this
    lia
  obtain ⟨r0, rs', rfl⟩ : ∃ r0 rs', rs = r0 :: rs' := by
    cases rs with
    | nil => exact absurd rfl hrs_ne
    | cons r0 rs' => exact ⟨r0, rs', rfl⟩
  have hr0_mem : r0 ∈ p.roots := by
    rw [← hrs_eq]
    exact Multiset.mem_coe.mpr (List.mem_cons_self ..)
  have hc_r0 : c ≤ r0 := h r0 hr0_mem
  have hr0_le : r0 ≤ s := listInterlaces_all_ge ss rs' r0 hint s hs_ss
  linarith

namespace PosComboRealRooted

/-- Differentiation preserves positive-combination real-rootedness for a
same-degree pair with positive leading coefficients and positive common degree.

For each positive combination, the derivative is the corresponding positive
combination of the derivatives.  The positive common top coefficient ensures
that the original combination has positive degree, so Rolle gives splitting of
the derivative. -/
theorem derivative
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) (hpos : 1 ≤ f.natDegree) :
    PosComboRealRooted f.derivative g.derivative := by
  intro lam μ hlam hμ
  have key : C lam * f.derivative + C μ * g.derivative =
      (C lam * f + C μ * g).derivative := by
    simp
  obtain ⟨_, hp_splits⟩ := hfg (lam := lam) (μ := μ) hlam hμ
  have hfc : f.coeff f.natDegree = f.leadingCoeff := rfl
  have hgc : g.coeff f.natDegree = g.leadingCoeff := by
    have hn : f.natDegree = g.natDegree := hdeg.symm
    rw [hn]
    rfl
  have hcoeff_pos : 0 < (C lam * f + C μ * g).coeff f.natDegree := by
    rw [coeff_add, coeff_C_mul, coeff_C_mul, hfc, hgc]
    have hf_top : 0 < lam * f.leadingCoeff := mul_pos hlam hf
    have hg_top : 0 < μ * g.leadingCoeff := mul_pos hμ hg
    linarith
  have hle : f.natDegree ≤ (C lam * f + C μ * g).natDegree :=
    le_natDegree_of_ne_zero (ne_of_gt hcoeff_pos)
  have hder_ne : (C lam * f + C μ * g).derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  rcases derivative_eq_zero_or_ne_zero_and_splits hp_splits with hzero | hsplit
  · exact absurd hzero hder_ne
  · exact ⟨by rw [key]; exact hder_ne, by rw [key]; exact hsplit.2⟩

end PosComboRealRooted

/-- Non-namespace wrapper for
`RealRooted.PosComboRealRooted.derivative`. -/
theorem posComboRealRooted_derivative
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) (hpos : 1 ≤ f.natDegree)
    (hfg : PosComboRealRooted f g) :
    PosComboRealRooted f.derivative g.derivative :=
  hfg.derivative hf hg hdeg hpos

end RealRooted
