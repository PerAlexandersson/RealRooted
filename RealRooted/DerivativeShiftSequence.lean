import RealRooted.IteratedDerivativeShift

/-!
# Finite sequences of derivative shifts

This file extends the fixed-parameter iteration of `TDeriv` to a finite list of
possibly different positive parameters.  The varying-parameter form is needed
when each derivative shift must satisfy a new local smallness bound.

The main result is `Polynomial.hasSimpleRoots_applyTDerivList_of_natDegree_le_length`:
after at least `p.natDegree` positive shifts, a nonzero splitting polynomial has
simple roots.  Its proof follows the multiplicity descent used for fixed
iterations, tracing a hypothetical multiple root backward through the list.
-/

open RealRooted

namespace Polynomial

noncomputable section

/-- Apply the derivative shifts in `epss` from left to right. -/
def applyTDerivList : List ℝ → ℝ[X] → ℝ[X]
  | [], p => p
  | eps :: epss, p => applyTDerivList epss (TDeriv eps p)

@[simp]
theorem applyTDerivList_nil (p : ℝ[X]) : applyTDerivList [] p = p := rfl

@[simp]
theorem applyTDerivList_cons (eps : ℝ) (epss : List ℝ) (p : ℝ[X]) :
    applyTDerivList (eps :: epss) p = applyTDerivList epss (TDeriv eps p) := rfl

/-- A finite sequence of derivative shifts preserves nonvanishing. -/
theorem applyTDerivList_ne_zero {epss : List ℝ} {p : ℝ[X]} (hp : p ≠ 0) :
    applyTDerivList epss p ≠ 0 := by
  induction epss generalizing p with
  | nil => simpa
  | cons eps epss ih =>
      simpa using ih (TDeriv_ne_zero hp)

/-- Positive derivative shifts preserve splitting throughout a finite sequence. -/
theorem Splits.applyTDerivList {epss : List ℝ} {p : ℝ[X]}
    (hp : p.Splits) (hpos : ∀ eps ∈ epss, 0 < eps) :
    (applyTDerivList epss p).Splits := by
  induction epss generalizing p with
  | nil => simpa
  | cons eps epss ih =>
      have heps : 0 < eps := hpos eps (by simp)
      have htail : ∀ eta ∈ epss, 0 < eta :=
        fun eta heta ↦ hpos eta (List.mem_cons_of_mem eps heta)
      exact ih (splits_tderiv heps hp) htail

/-- A finite sequence of derivative shifts preserves natural degree. -/
@[simp]
theorem natDegree_applyTDerivList (epss : List ℝ) (p : ℝ[X]) :
    (applyTDerivList epss p).natDegree = p.natDegree := by
  induction epss generalizing p with
  | nil => simp
  | cons eps epss ih =>
      rw [applyTDerivList_cons, ih, natDegree_TDeriv]

/-- A finite sequence of derivative shifts preserves the leading coefficient. -/
@[simp]
theorem leadingCoeff_applyTDerivList (epss : List ℝ) (p : ℝ[X]) :
    (applyTDerivList epss p).leadingCoeff = p.leadingCoeff := by
  induction epss generalizing p with
  | nil => simp
  | cons eps epss ih =>
      rw [applyTDerivList_cons, ih, leadingCoeff_TDeriv]

/-- A multiple final root gains one unit of multiplicity at every backward step. -/
theorem rootMultiplicity_applyTDerivList_eq_add_length_of_ge_two
    {epss : List ℝ} {p : ℝ[X]} {a : ℝ}
    (hpos : ∀ eps ∈ epss, 0 < eps) (hp : p.Splits)
    (hm : 2 ≤ (applyTDerivList epss p).rootMultiplicity a) :
    p.rootMultiplicity a =
      (applyTDerivList epss p).rootMultiplicity a + epss.length := by
  induction epss generalizing p with
  | nil => simp
  | cons eps epss ih =>
      have heps : 0 < eps := hpos eps (by simp)
      have htail : ∀ eta ∈ epss, 0 < eta :=
        fun eta heta ↦ hpos eta (List.mem_cons_of_mem eps heta)
      have hTsplit : (TDeriv eps p).Splits := splits_tderiv heps hp
      have htail_eq := ih htail hTsplit hm
      have hm' :
          2 ≤ (applyTDerivList epss (TDeriv eps p)).rootMultiplicity a := by
        simpa only [applyTDerivList_cons] using hm
      have hTmult : 2 ≤ (TDeriv eps p).rootMultiplicity a := by
        rw [htail_eq]
        exact le_trans hm' (Nat.le_add_right _ _)
      have hstep := rootMultiplicity_eq_succ_of_TDeriv_ge_two heps hp hTmult
      simp only [applyTDerivList_cons, List.length_cons]
      lia

/-- Enough positive derivative shifts make every root simple. -/
theorem hasSimpleRoots_applyTDerivList_of_natDegree_le_length
    {epss : List ℝ} {p : ℝ[X]} (hpos : ∀ eps ∈ epss, 0 < eps)
    (hp : p ≠ 0) (hsplit : p.Splits) (hdeg : p.natDegree ≤ epss.length) :
    HasSimpleRoots (applyTDerivList epss p) := by
  intro a ha
  have hfinal_ne : applyTDerivList epss p ≠ 0 := applyTDerivList_ne_zero hp
  have hmult_pos : 0 < (applyTDerivList epss p).rootMultiplicity a :=
    (rootMultiplicity_pos hfinal_ne).mpr ha
  by_contra hne
  have hmult : 2 ≤ (applyTDerivList epss p).rootMultiplicity a := by
    lia
  have hback :=
    rootMultiplicity_applyTDerivList_eq_add_length_of_ge_two hpos hsplit hmult
  have hmult_le : p.rootMultiplicity a ≤ p.natDegree := by
    calc
      p.rootMultiplicity a = p.roots.count a := (count_roots p).symm
      _ ≤ p.roots.card := p.roots.count_le_card a
      _ ≤ p.natDegree := card_roots' p
  lia

end

end Polynomial
