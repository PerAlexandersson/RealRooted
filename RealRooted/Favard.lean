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

private lemma interlaces_one_X_sub_C (a : ℝ) :
    Interlaces (1 : ℝ[X]) (X - C a) := by
  refine ⟨isRealRooted_X_sub_C a,
    isRealRooted_of_deg_zero (p := (1 : ℝ[X])) one_ne_zero (by simp),
    by simp,
    [a], [], by simp, by simp, by simp, by simp, by simp [ListInterlaces]⟩

theorem favardInterlacing :
    favardInterlacingStatement := by
  intro P α β hrec hβ
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
        · rw [hP0, hP1]
          exact interlaces_one_X_sub_C (α 0)
        · rw [hP0]
          unfold HasPosLeadingCoeff
          simp
        · rw [hP1]
          unfold HasPosLeadingCoeff
          simp
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
          dsimp [aPoly]
          rw [natDegree_mul (X_sub_C_ne_zero (α (n + 1))) hf_ne, natDegree_X_sub_C]
          omega
        have hAf_pos : HasPosLeadingCoeff (aPoly * f) := by
          dsimp [aPoly]
          unfold HasPosLeadingCoeff at hPos_n1 ⊢
          simpa [Polynomial.leadingCoeff_mul, leadingCoeff_X_sub_C] using hPos_n1
        have hBg_lt_Af : (bPoly * g).natDegree < (aPoly * f).natDegree := by
          have hBg_le : (bPoly * g).natDegree ≤ g.natDegree := by
            dsimp [bPoly]
            exact Polynomial.natDegree_C_mul_le _ _
          have hg_lt : g.natDegree < f.natDegree := by omega
          calc
            (bPoly * g).natDegree ≤ g.natDegree := hBg_le
            _ < f.natDegree := hg_lt
            _ < f.natDegree + 1 := by omega
            _ = (aPoly * f).natDegree := hAf_deg.symm
        have hF_pos_aux : HasPosLeadingCoeff (bPoly * g + aPoly * f) :=
          hasPosLeadingCoeff_add_of_natDegree_lt_right hBg_lt_Af hAf_pos
        have hF_pos : HasPosLeadingCoeff (aPoly * f + bPoly * g) := by
          simpa [add_comm] using hF_pos_aux
        have hF_deg :
            (aPoly * f + bPoly * g).natDegree = f.natDegree + 1 := by
          have hdeg_aux :
              (bPoly * g + aPoly * f).natDegree = (aPoly * f).natDegree :=
            natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hBg_lt_Af hAf_pos
          simpa [add_comm, hAf_deg] using hdeg_aux
        have hdeg_lo : f.natDegree ≤ (aPoly * f + bPoly * g).natDegree := by
          omega
        have hdeg_hi : (aPoly * f + bPoly * g).natDegree ≤ f.natDegree + 1 := by
          omega
        have hb_nonpos : ∀ r, f.IsRoot r → bPoly.eval r ≤ 0 := by
          intro r _hr
          have hb_le : 0 ≤ β (n + 1) := (hβ n).le
          simpa [bPoly] using (neg_nonpos.mpr hb_le)
        have hPrec_step : Prec f (aPoly * f + bPoly * g) := by
          exact prec_of_interlaces_evalCoeff_nonpos
            (f := f) (g := g) (a := aPoly) (b := bPoly)
            hInter hPos_n hF_pos hdeg_lo hdeg_hi hb_nonpos
        have hInter_step : Interlaces f (aPoly * f + bPoly * g) := by
          exact hPrec_step.toInterlaces (by simp [hF_deg])
        have hP2 :
            P (n + 2) = aPoly * f + bPoly * g := by
          dsimp [aPoly, bPoly, f, g]
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hstep n
        refine ⟨?_, ?_, ?_⟩
        · simpa [f, hP2] using hInter_step
        · exact hPos_n1
        · simpa [f, g, hP2] using hF_pos
  intro n
  exact (hQ n).1.toPrec

theorem isRealRooted_of_favard
    {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, IsRealRooted (P n) := by
  intro n
  exact (favardInterlacing hrec hβ n).1

theorem nonzero_of_favard
    {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, P n ≠ 0 := by
  intro n
  exact (isRealRooted_of_favard hrec hβ n).1

theorem isGeneralizedSturmSeq_reverse_range_map_of_favard
    {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β)
    (hβ : ∀ n : Nat, 0 < β (n + 1)) :
    ∀ n : Nat, IsGeneralizedSturmSeq ((List.range (n + 1)).reverse.map P) := by
  intro n
  induction n with
  | zero =>
      simp [IsGeneralizedSturmSeq]
  | succ n ih =>
      have hprec : Prec (P n) (P (n + 1)) := favardInterlacing hrec hβ n
      have hcons1 :
          ((List.range (n + 2)).reverse.map P) =
            P (n + 1) :: ((List.range (n + 1)).reverse.map P) := by
        rw [List.range_succ, List.reverse_append, List.reverse_singleton]
        simp
      have hcons2 :
          ((List.range (n + 1)).reverse.map P) =
            P n :: ((List.range n).reverse.map P) := by
        rw [List.range_succ, List.reverse_append, List.reverse_singleton]
        simp
      have ih' : IsGeneralizedSturmSeq (P n :: ((List.range n).reverse.map P)) := by
        simpa [hcons2] using ih
      rw [hcons1, hcons2]
      simpa [IsGeneralizedSturmSeq] using And.intro hprec ih'

end RealRooted
