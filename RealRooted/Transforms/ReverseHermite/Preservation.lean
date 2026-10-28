module

import RealRooted.GarloffWagner.Theorem12
import RealRooted.PFPolynomial.LinearFactor
public import RealRooted.Transforms.ReverseHermite.Basic
import RealRooted.GarloffWagner.KreinExpansion
public import RealRooted.PFPolynomial
public import RealRooted.WeightedSum

/-!
# PF and interlacing preservation for the reverse-Hermite transform

The algebraic transform is separated from this real-rootedness layer. A
simultaneous degree induction proves preservation of the polynomial PF cone
and of zero-aware interlacing.
-/

public section

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

private theorem reverseHermiteTransform_interl_of_weightedSum_right
    {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hinterl : ∀ ap ∈ l,
      Interl (reverseHermiteTransform ap.2)
        (reverseHermiteTransform g))
    (hnn : ∀ ap ∈ l,
      HasNonnegCoeffs (reverseHermiteTransform ap.2)) :
    Interl (reverseHermiteTransform f)
      (reverseHermiteTransform g) := by
  rw [hf, reverseHermiteTransform_weightedSum]
  apply interl_weightedSum_right_of_nonneg
  · grind
  · grind
  · grind

/-- PF preservation at one degree follows from the lower-degree simultaneous hypotheses. -/
private lemma reverseHermiteTransform_isPF_of_lower_degree
    {n : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p) (hpdeg : p.natDegree = n)
    (hPF_lt : ∀ {q : ℝ[X]}, IsPFPolynomial q → q.natDegree < n →
      IsPFPolynomial (reverseHermiteTransform q))
    (hInterl_lt : ∀ {f g : ℝ[X]}, IsPFPolynomial f → IsPFPolynomial g →
      Interl f g → g.natDegree < n →
        Interl (reverseHermiteTransform f) (reverseHermiteTransform g)) :
    IsPFPolynomial (reverseHermiteTransform p) := by
  by_cases hp0 : p = 0
  · simp_all
  by_cases hpdeg0 : p.natDegree = 0
  · have hpC := Polynomial.eq_C_of_natDegree_eq_zero hpdeg0
    rw [hpC] at hp ⊢
    simpa [reverseHermiteTransform, reverseHermiteBasis] using hp
  rcases hp.exists_X_sub_C_factor_of_pos_natDegree (Nat.pos_of_ne_zero hpdeg0) with
    ⟨u, q, hu, hfactor, hq, hqdeg⟩
  have hqT : IsPFPolynomial (reverseHermiteTransform q) := hPF_lt hq (by lia)
  have hqder : IsPFPolynomial q.derivative := hq.derivative
  have hqderT : IsPFPolynomial (reverseHermiteTransform q.derivative) := by
    apply hPF_lt hqder
    have := natDegree_derivative_le q
    lia
  have hinterl :
      Interl (reverseHermiteTransform q.derivative) (reverseHermiteTransform q) :=
    hInterl_lt hqder hq hq.derivative_interl_self (by lia)
  rw [hfactor, show X - C u = X + C (-u) by grind,
    reverseHermiteTransform_mul_X_add_C]
  simpa [linearFactorStep] using
    linearFactorStep_isPF (r := -u) (by linarith) hinterl hqderT hqT

/-- Interlacing preservation at one degree follows from PF and lower-degree hypotheses. -/
private lemma reverseHermiteTransform_interl_of_lower_degree
    {n : ℕ} {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfg : Interl f g) (hgdeg : g.natDegree = n)
    (hPF : ∀ {p : ℝ[X]}, IsPFPolynomial p → p.natDegree = n →
      IsPFPolynomial (reverseHermiteTransform p))
    (hPF_lt : ∀ {p : ℝ[X]}, IsPFPolynomial p → p.natDegree < n →
      IsPFPolynomial (reverseHermiteTransform p))
    (hInterl_lt : ∀ {f g : ℝ[X]}, IsPFPolynomial f → IsPFPolynomial g →
      Interl f g → g.natDegree < n →
        Interl (reverseHermiteTransform f) (reverseHermiteTransform g)) :
    Interl (reverseHermiteTransform f) (reverseHermiteTransform g) := by
  classical
  rcases hfg with hf0 | hg0 | hstrict
  · rw [hf0, reverseHermiteTransform_zero]
    exact interl_zero_left _
  · rw [hg0, reverseHermiteTransform_zero]
    exact interl_zero_right _
  by_cases hgdeg0 : g.natDegree = 0
  · have hfdeg0 : f.natDegree = 0 := by
      have := hstrict.natDegree_le
      lia
    have hfC := Polynomial.eq_C_of_natDegree_eq_zero hfdeg0
    have hgC := Polynomial.eq_C_of_natDegree_eq_zero hgdeg0
    rw [hfC, hgC] at hstrict ⊢
    simpa [reverseHermiteTransform, reverseHermiteBasis] using hstrict.toInterl
  have hfpos : HasPosLeadingCoeff f :=
    hf.hasNonnegCoeffs.pos_leadingCoeff hstrict.1.1
  have hgpos : HasPosLeadingCoeff g :=
    hg.hasNonnegCoeffs.pos_leadingCoeff hstrict.2.1.1
  rcases hstrict.exists_kreinSummandExpansion hfpos hgpos with
    ⟨l, hfexp, hnonneg, hsummand, _⟩
  apply reverseHermiteTransform_interl_of_weightedSum_right hfexp hnonneg
  · intro ap hap
    have hs := hsummand ap hap
    rcases hs with hself | ⟨u, hfactor⟩
    · simpa [hself] using (hPF hg hgdeg).interl_self
    · have hq : IsPFPolynomial ap.2 := hg.of_X_sub_C_mul_factor hfactor
      have hq0 : ap.2 ≠ 0 := by
        intro hzero
        simp_all
      have hqdeg : ap.2.natDegree < g.natDegree := by
        rw [hfactor, natDegree_mul (X_sub_C_ne_zero u) hq0, natDegree_X_sub_C]
        lia
      have hqder : IsPFPolynomial ap.2.derivative := hq.derivative
      have hqT : IsPFPolynomial (reverseHermiteTransform ap.2) := hPF_lt hq (by lia)
      have hqderT : IsPFPolynomial (reverseHermiteTransform ap.2.derivative) := by
        apply hPF_lt hqder
        have := natDegree_derivative_le ap.2
        lia
      have hder :
          Interl (reverseHermiteTransform ap.2.derivative)
            (reverseHermiteTransform ap.2) :=
        hInterl_lt hqder hq hq.derivative_interl_self (by lia)
      rw [hfactor, show X - C u = X + C (-u) by grind,
        reverseHermiteTransform_mul_X_add_C]
      simpa [linearFactorStep] using
        interl_linearFactorStep (r := -u) (by
          have huRoot : g.IsRoot u := by simp_all
          exact neg_nonneg.mpr
            (hg.roots_nonpos u ((mem_roots hstrict.2.1.1).mpr huRoot)))
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
        rw [hfactor, natDegree_mul (X_sub_C_ne_zero u) hp0, natDegree_X_sub_C]
        lia
      exact (hPF_lt hp (by lia)).hasNonnegCoeffs

private theorem reverseHermiteTransform_preserves_pf_and_interl :
    (∀ {p : ℝ[X]}, IsPFPolynomial p →
      IsPFPolynomial (reverseHermiteTransform p)) ∧
    (∀ {f g : ℝ[X]}, IsPFPolynomial f → IsPFPolynomial g →
      Interl f g →
      Interl (reverseHermiteTransform f)
        (reverseHermiteTransform g)) := by
  classical
  let P : ℕ → Prop := fun n =>
    (∀ {p : ℝ[X]}, IsPFPolynomial p → p.natDegree = n →
      IsPFPolynomial (reverseHermiteTransform p)) ∧
    (∀ {f g : ℝ[X]}, IsPFPolynomial f → IsPFPolynomial g →
      Interl f g → g.natDegree = n →
      Interl (reverseHermiteTransform f)
        (reverseHermiteTransform g))
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        have hPF_lt :
            ∀ {p : ℝ[X]}, IsPFPolynomial p → p.natDegree < n →
              IsPFPolynomial (reverseHermiteTransform p) := by
          intro p hp hdeg
          exact (ih p.natDegree hdeg).1 hp rfl
        have hInterl_lt :
            ∀ {f g : ℝ[X]}, IsPFPolynomial f → IsPFPolynomial g →
              Interl f g → g.natDegree < n →
                Interl (reverseHermiteTransform f)
                  (reverseHermiteTransform g) := by
          intro f g hf hg hfg hdeg
          exact (ih g.natDegree hdeg).2 hf hg hfg rfl
        have hPF :
            ∀ {p : ℝ[X]}, IsPFPolynomial p → p.natDegree = n →
              IsPFPolynomial (reverseHermiteTransform p) := by
          intro p hp hpdeg
          exact reverseHermiteTransform_isPF_of_lower_degree
            hp hpdeg hPF_lt hInterl_lt
        have hInterl :
            ∀ {f g : ℝ[X]}, IsPFPolynomial f → IsPFPolynomial g →
              Interl f g → g.natDegree = n →
              Interl (reverseHermiteTransform f)
                (reverseHermiteTransform g) := by
          intro f g hf hg hfg hgdeg
          exact reverseHermiteTransform_interl_of_lower_degree
            hf hg hfg hgdeg hPF hPF_lt hInterl_lt
        exact ⟨hPF, hInterl⟩
  constructor
  · intro p hp
    exact (hP p.natDegree).1 hp rfl
  · intro f g hf hg hfg
    exact (hP g.natDegree).2 hf hg hfg rfl

/-- The reverse-Hermite transform preserves the polynomial PF cone. -/
theorem reverseHermiteTransform_preserves_pf {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial (reverseHermiteTransform p) :=
  reverseHermiteTransform_preserves_pf_and_interl.1 hp

/-- The reverse-Hermite transform preserves zero-aware interlacing between
PF polynomials. -/
theorem reverseHermiteTransform_preserves_interl {f g : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfg : Interl f g) :
    Interl (reverseHermiteTransform f) (reverseHermiteTransform g) :=
  reverseHermiteTransform_preserves_pf_and_interl.2 hf hg hfg

/-- Strict interlacing between PF polynomials is transported to the
zero-aware relation by the reverse-Hermite transform. -/
theorem reverseHermiteTransform_strictInterl_to_interl {f g : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfg : StrictInterl f g) :
    Interl (reverseHermiteTransform f) (reverseHermiteTransform g) :=
  reverseHermiteTransform_preserves_interl hf hg hfg.toInterl

end RealRooted
