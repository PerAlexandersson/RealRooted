import RealRooted.GarloffWagner.Theorem12
import RealRooted.PFPolynomial.LinearFactor
import RealRooted.Transforms.ReverseHermite.Basic

/-!
# PF and proper-position preservation for the reverse-Hermite transform

The algebraic transform is separated from this real-rootedness layer. A
simultaneous degree induction proves preservation of the polynomial PF cone
and of zero-aware proper position.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The reverse-Hermite transform commutes with finite weighted sums. -/
theorem reverseHermiteTransform_weightedSum :
    ∀ l : List (ℝ × ℝ[X]),
      reverseHermiteTransform (weightedSum l) =
        weightedSum
          (l.map fun ap => (ap.1, reverseHermiteTransform ap.2))
  | [] => by simp
  | (a, p) :: l => by
      rw [weightedSum_cons, reverseHermiteTransform_add,
        reverseHermiteTransform_C_mul,
        reverseHermiteTransform_weightedSum l]
      simp

private theorem reverseHermiteTransform_prec0_of_weightedSum_right
    {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hprec : ∀ ap ∈ l,
      Prec0 (reverseHermiteTransform ap.2)
        (reverseHermiteTransform g))
    (hnn : ∀ ap ∈ l,
      HasNonnegCoeffs (reverseHermiteTransform ap.2)) :
    Prec0 (reverseHermiteTransform f)
      (reverseHermiteTransform g) := by
  rw [hf, reverseHermiteTransform_weightedSum]
  apply prec0_weightedSum_right_of_nonneg
  · grind
  · grind
  · grind

private theorem reverseHermiteTransform_preserves_pf_and_prec0 :
    (∀ {p : ℝ[X]}, IsPFPolynomial p →
      IsPFPolynomial (reverseHermiteTransform p)) ∧
    (∀ {f g : ℝ[X]}, IsPFPolynomial f → IsPFPolynomial g →
      Prec0 f g →
      Prec0 (reverseHermiteTransform f)
        (reverseHermiteTransform g)) := by
  classical
  let P : ℕ → Prop := fun n =>
    (∀ {p : ℝ[X]}, IsPFPolynomial p → p.natDegree = n →
      IsPFPolynomial (reverseHermiteTransform p)) ∧
    (∀ {f g : ℝ[X]}, IsPFPolynomial f → IsPFPolynomial g →
      Prec0 f g → g.natDegree = n →
      Prec0 (reverseHermiteTransform f)
        (reverseHermiteTransform g))
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        have hPF :
            ∀ {p : ℝ[X]}, IsPFPolynomial p → p.natDegree = n →
              IsPFPolynomial (reverseHermiteTransform p) := by
          intro p hp hpdeg
          by_cases hp0 : p = 0
          · simp_all
          by_cases hpdeg0 : p.natDegree = 0
          · have hpC := Polynomial.eq_C_of_natDegree_eq_zero hpdeg0
            rw [hpC] at hp ⊢
            simpa [reverseHermiteTransform, reverseHermiteBasis] using hp
          rcases hp.exists_X_sub_C_factor_of_pos_natDegree
              (Nat.pos_of_ne_zero hpdeg0) with
            ⟨u, q, hu, hfactor, hq, hqdeg⟩
          have hq0 : q ≠ 0 := by simp_all
          have hqT : IsPFPolynomial (reverseHermiteTransform q) := by
            grind
          have hqder : IsPFPolynomial q.derivative := hq.derivative
          have hqderT :
              IsPFPolynomial (reverseHermiteTransform q.derivative) := by
            exact (ih q.derivative.natDegree (by
              rw [← hpdeg]
              have := natDegree_derivative_le q
              lia)).1 hqder rfl
          have hprec :
              Prec0 (reverseHermiteTransform q.derivative)
                (reverseHermiteTransform q) := by
            exact (ih q.natDegree (by lia)).2 hqder hq
              hq.derivative_prec0_self rfl
          rw [hfactor, show X - C u = X + C (-u) by
            grind,
            reverseHermiteTransform_mul_X_add_C]
          simpa [linearFactorStep] using
            linearFactorStep_isPF (r := -u) (by linarith)
              hprec hqderT hqT
        have hPrec0 :
            ∀ {f g : ℝ[X]}, IsPFPolynomial f → IsPFPolynomial g →
              Prec0 f g → g.natDegree = n →
              Prec0 (reverseHermiteTransform f)
                (reverseHermiteTransform g) := by
          intro f g hf hg hfg hgdeg
          rcases hfg with hf0 | hg0 | hstrict
          · rw [hf0, reverseHermiteTransform_zero]
            exact prec0_zero_left _
          · rw [hg0, reverseHermiteTransform_zero]
            exact prec0_zero_right _
          by_cases hgdeg0 : g.natDegree = 0
          · have hfdeg0 : f.natDegree = 0 := by
              have := hstrict.natDegree_le
              lia
            have hfC := Polynomial.eq_C_of_natDegree_eq_zero hfdeg0
            have hgC := Polynomial.eq_C_of_natDegree_eq_zero hgdeg0
            rw [hfC, hgC] at hstrict ⊢
            simpa [reverseHermiteTransform, reverseHermiteBasis] using
              hstrict.toPrec0
          have hfpos : HasPosLeadingCoeff f :=
            hf.hasNonnegCoeffs.pos_leadingCoeff hstrict.1.1
          have hgpos : HasPosLeadingCoeff g :=
            hg.hasNonnegCoeffs.pos_leadingCoeff hstrict.2.1.1
          rcases gwTheorem11PrecKreinSummandExpansion hstrict hfpos hgpos with
            ⟨l, hfexp, hnonneg, hsummand, _⟩
          apply reverseHermiteTransform_prec0_of_weightedSum_right
            hfexp hnonneg
          · intro ap hap
            have hs := hsummand ap hap
            rcases hs with hself | ⟨u, hfactor⟩
            · simpa [hself] using
                (hPF hg hgdeg).prec0_self
            · have hq : IsPFPolynomial ap.2 :=
                hg.of_X_sub_C_mul_factor hfactor
              have hq0 : ap.2 ≠ 0 := by
                intro hzero
                simp_all
              have hqdeg : ap.2.natDegree < g.natDegree := by
                rw [hfactor, natDegree_mul (X_sub_C_ne_zero u) hq0,
                  natDegree_X_sub_C]
                lia
              have hqder : IsPFPolynomial ap.2.derivative := hq.derivative
              have hqT : IsPFPolynomial
                  (reverseHermiteTransform ap.2) :=
                (ih ap.2.natDegree (by lia)).1 hq rfl
              have hqderT : IsPFPolynomial
                  (reverseHermiteTransform ap.2.derivative) :=
                (ih ap.2.derivative.natDegree (by
                  have := natDegree_derivative_le ap.2
                  lia)).1 hqder rfl
              have hder :
                  Prec0 (reverseHermiteTransform ap.2.derivative)
                    (reverseHermiteTransform ap.2) :=
                (ih ap.2.natDegree (by lia)).2 hqder hq
                  hq.derivative_prec0_self rfl
              rw [hfactor, show X - C u = X + C (-u) by
                grind,
                reverseHermiteTransform_mul_X_add_C]
              simpa [linearFactorStep] using
                prec0_linearFactorStep (r := -u) (by
                  have huRoot : g.IsRoot u := by simp_all
                  exact neg_nonneg.mpr
                    (hg.roots_nonpos u
                      ((mem_roots hstrict.2.1.1).mpr huRoot)))
                  hder hqderT hqT
          · intro ap hap
            have hs := hsummand ap hap
            have hp := hs.isPFPolynomial hg
            rcases hs with hself | ⟨u, hfactor⟩
            · simpa [hself] using (hPF hg hgdeg).hasNonnegCoeffs
            · have hp0 : ap.2 ≠ 0 := by
                intro hzero
                simp_all
              have hpdeg : ap.2.natDegree < g.natDegree := by
                rw [hfactor, natDegree_mul (X_sub_C_ne_zero u) hp0,
                  natDegree_X_sub_C]
                lia
              exact ((ih ap.2.natDegree (by lia)).1 hp rfl).hasNonnegCoeffs
        exact ⟨hPF, hPrec0⟩
  constructor
  · intro p hp
    exact (hP p.natDegree).1 hp rfl
  · intro f g hf hg hfg
    exact (hP g.natDegree).2 hf hg hfg rfl

/-- The reverse-Hermite transform preserves the polynomial PF cone. -/
theorem reverseHermiteTransform_preserves_pf {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial (reverseHermiteTransform p) :=
  reverseHermiteTransform_preserves_pf_and_prec0.1 hp

/-- The reverse-Hermite transform preserves zero-aware proper position between
PF polynomials. -/
theorem reverseHermiteTransform_preserves_prec0 {f g : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfg : Prec0 f g) :
    Prec0 (reverseHermiteTransform f) (reverseHermiteTransform g) :=
  reverseHermiteTransform_preserves_pf_and_prec0.2 hf hg hfg

/-- Strict proper position between PF polynomials is transported to the
zero-aware relation by the reverse-Hermite transform. -/
theorem reverseHermiteTransform_prec_to_prec0 {f g : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfg : Prec f g) :
    Prec0 (reverseHermiteTransform f) (reverseHermiteTransform g) :=
  reverseHermiteTransform_preserves_prec0 hf hg hfg.toPrec0

end RealRooted
