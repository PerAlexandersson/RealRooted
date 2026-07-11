import RealRooted.Mathlib.Algebra.Polynomial.Basic
import RealRooted.MaWang

open Polynomial

noncomputable section

namespace RealRooted

/-- A three-term recurrence in the Favard shape.

We record only the recurrence data relevant for the real-rooted/interlacing
applications: the measure-theoretic orthogonality conclusion can be added later
once the root-theoretic statement is formalized. -/
def SatisfiesFavardRecurrence (P : Nat → ℝ[X]) (α β : Nat → ℝ) : Prop :=
  P 0 = 1 ∧
  P 1 = X - C (α 0) ∧
  ∀ n : Nat,
    P (n + 2) =
      (X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n

/-- Planning stub for Favard's theorem in the form most useful to this project:
strictly positive recurrence coefficients should force a Sturm/interlacing
sequence, and hence real-rootedness of every `P n`. -/
def favardInterlacingStatement : Prop :=
  ∀ {P : Nat → ℝ[X]} {α β : Nat → ℝ},
    SatisfiesFavardRecurrence P α β →
    (∀ n : Nat, 0 < β (n + 1)) →
    ∀ n : Nat, Prec (P n) (P (n + 1))

theorem favardInterlacing :
    favardInterlacingStatement :=
  fun {P α β} hrec hβ => by
  rcases hrec with ⟨hP0, hP1, hstep⟩
  let Q : Nat → Prop := fun n =>
    Interlaces (P n) (P (n + 1)) ∧
      HasPosLeadingCoeff (P n) ∧
      HasPosLeadingCoeff (P (n + 1))
  have hQ : ∀ n : Nat, Q n := by
    intro n
    induction n with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · simp [Interlaces, ListInterlaces, sub_eq_zero, hP0, hP1]
        · simpa [hP0] using hasPosLeadingCoeff_one
        · simpa [hP1] using hasPosLeadingCoeff_X_sub_C (α 0)
    | succ n ih =>
        rcases ih with ⟨hInter, hPos_n, hPos_n1⟩
        let f : ℝ[X] := P (n + 1)
        let g : ℝ[X] := P n
        let aPoly : ℝ[X] := X - C (α (n + 1))
        let bPoly : ℝ[X] := C (-β (n + 1))
        have hdeg_gf : g.natDegree + 1 = f.natDegree := by
          simpa [f, g] using hInter.2.2.1
        have hf_ne : f ≠ 0 := by simpa [f] using hInter.1.1
        have hAf_deg : (aPoly * f).natDegree = f.natDegree + 1 := by
          simpa [aPoly, natDegree_X_sub_C, Nat.add_comm] using
            natDegree_mul (X_sub_C_ne_zero (α (n + 1))) hf_ne
        have hAf_pos : HasPosLeadingCoeff (aPoly * f) := by
          simpa [aPoly] using hasPosLeadingCoeff_X_sub_C_mul hPos_n1
        have hBg_lt_Af : (bPoly * g).natDegree < (aPoly * f).natDegree := by
          have hBg_le : (bPoly * g).natDegree ≤ g.natDegree := by
            simpa [bPoly] using Polynomial.natDegree_C_mul_le (-β (n + 1)) g
          lia
        have hF_pos : HasPosLeadingCoeff (aPoly * f + bPoly * g) := by
          simpa [add_comm] using
            hasPosLeadingCoeff_add_of_natDegree_lt_right hBg_lt_Af hAf_pos
        have hF_deg :
            (aPoly * f + bPoly * g).natDegree = f.natDegree + 1 := by
          simpa [add_comm, hAf_deg] using
            natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hBg_lt_Af hAf_pos
        have hb_nonpos : ∀ r, f.IsRoot r → bPoly.eval r ≤ 0 :=
          fun _ _ => by simpa [bPoly] using neg_nonpos.mpr (hβ n).le
        have hPrec_step : Prec f (aPoly * f + bPoly * g) :=
          prec_of_interlaces_evalCoeff_nonpos
            (f := f) (g := g) (a := aPoly) (b := bPoly)
            hInter hPos_n hF_pos (by lia) (by lia) hb_nonpos
        refine ⟨?_, hPos_n1, ?_⟩
        · simpa [f, g, aPoly, bPoly, sub_eq_add_neg, hstep n] using
            hPrec_step.toInterlaces (by lia)
        · simpa [f, g, aPoly, bPoly, sub_eq_add_neg, hstep n] using hF_pos
  exact fun n => (hQ n).1.toPrec

theorem isRealRooted_of_favard
    {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, ((P n) ≠ 0 ∧ (P n).Splits) :=
  fun n => (favardInterlacing hrec hβ n).1

theorem nonzero_of_favard
    {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n => (favardInterlacing hrec hβ n).1.1

theorem isGeneralizedSturmSeq_reverse_range_map_of_favard
    {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, IsGeneralizedSturmSeq ((List.range (n + 1)).reverse.map P) :=
  fun n => by
  induction n with
  | zero =>
      simp [IsGeneralizedSturmSeq]
  | succ n ih =>
      have hprec : Prec (P n) (P (n + 1)) := favardInterlacing hrec hβ n
      simpa [IsGeneralizedSturmSeq, List.range_succ] using And.intro hprec ih

end RealRooted
