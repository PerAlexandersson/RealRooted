import RealRooted.GeneralizedLiuWang

/-!
# Liu--Wang derivative-lag recursions

This file packages the common recurrence

```text
P_{n+2} = U_n P_{n+1} + V_n P'_{n+1} + W_n P_n
```

as a direct backend theorem.  The lag term `P_n` is the distinguished
Liu--Wang interlacer, while the derivative term is handled as an additional
interlacer of the current row.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- One-step Liu--Wang recursion with an additional derivative term.

The lag polynomial `g` is the distinguished interlacer.  The derivative
`f.derivative` is only used as a tail interlacer, so this theorem does not need
`f` to be squarefree. -/
theorem prec_lw_derivative_lag_of_nonpos {f g u v w : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_pos : HasPosLeadingCoeff f)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative + w * g))
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative + w * g).natDegree)
    (hdeg_hi : (u * f + v * f.derivative + w * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0)
    (hw_nonpos : ∀ r, f.IsRoot r → w.eval r ≤ 0) :
    Prec f (u * f + v * f.derivative + w * g) := by
  have hder : Interlaces f.derivative f := derivative_interlaces hf hdegf
  have hder_pos : HasPosLeadingCoeff f.derivative :=
    hf_pos.derivative (by lia)
  have hsum_eq :
      u * f + polynomialWeightedSum ((w, g) :: [(v, f.derivative)]) =
        u * f + v * f.derivative + w * g := by
    simp [polynomialWeightedSum]
    ring
  have htail_inter :
      ∀ bg ∈ [(v, f.derivative)], Interlaces bg.2 f := by
    intro bg hmem
    rcases List.mem_singleton.mp hmem with rfl
    simpa using hder
  have htail_pos :
      ∀ bg ∈ [(v, f.derivative)], HasPosLeadingCoeff bg.2 := by
    intro bg hmem
    rcases List.mem_singleton.mp hmem with rfl
    simpa using hder_pos
  have htail_nonpos :
      ∀ bg ∈ [(v, f.derivative)], ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0 := by
    intro bg hmem r hr
    rcases List.mem_singleton.mp hmem with rfl
    exact hv_nonpos r hr
  have hF_pos_weighted :
      HasPosLeadingCoeff
        (u * f + polynomialWeightedSum ((w, g) :: [(v, f.derivative)])) := by
    rwa [hsum_eq]
  have hdeg_lo_weighted :
      f.natDegree ≤
        (u * f + polynomialWeightedSum ((w, g) :: [(v, f.derivative)])).natDegree := by
    rwa [hsum_eq]
  have hdeg_hi_weighted :
      (u * f + polynomialWeightedSum ((w, g) :: [(v, f.derivative)])).natDegree ≤
        f.natDegree + 1 := by
    rwa [hsum_eq]
  have hprec :
      Prec f (u * f + polynomialWeightedSum ((w, g) :: [(v, f.derivative)])) :=
    prec_generalizedLiuWang_of_no_common
      (f := f) (g := g) (a := u) (b := w) (l := [(v, f.derivative)])
      hgf hg_pos htail_inter htail_pos htail_nonpos
      hF_pos_weighted hdeg_lo_weighted hdeg_hi_weighted hno hw_nonpos
  simpa [polynomialWeightedSum, add_assoc, add_comm, add_left_comm] using hprec

/-- Sequence-level Liu--Wang induction for derivative-lag recurrences where
the sign checks may use the current row's already proved real-rootedness. -/
theorem prec_lw_derivative_lag_sequence_of_root_signs
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos :
      ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
        ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
        ∀ r, (P (n + 1)).IsRoot r → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  intro n
  induction n with
  | zero =>
      exact hbase
  | succ n ih =>
      have hsource : P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits := ih.2.1
      have hLag_inter : Interlaces (P n) (P (n + 1)) :=
        ih.toInterlaces (hdeg_succ n)
      have hF_pos :
          HasPosLeadingCoeff
            (U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n) := by
        simpa [← hrec n] using hpos (n + 2)
      have hdeg_next :
          (P (n + 1)).natDegree + 1 = (P (n + 2)).natDegree := by
        simpa [Nat.add_assoc] using hdeg_succ (n + 1)
      have hdeg_lo :
          (P (n + 1)).natDegree ≤
            (U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n).natDegree := by
        rw [← hrec n]
        lia
      have hdeg_hi :
          (U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n).natDegree ≤
            (P (n + 1)).natDegree + 1 := by
        rw [← hrec n]
        lia
      have hstep :
          Prec (P (n + 1))
            (U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n) :=
        prec_lw_derivative_lag_of_nonpos
          hsource.2 (hdeg_two n) hLag_inter (hpos n) (hpos (n + 1))
          hF_pos hdeg_lo hdeg_hi (hno n)
          (hV_nonpos n hsource) (hW_nonpos n hsource)
      simpa [← hrec n] using hstep

/-- Sequence-level Liu--Wang induction with direct root-sign side conditions. -/
theorem prec_lw_derivative_lag_sequence
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_lw_derivative_lag_sequence_of_root_signs
    hbase hpos hdeg_two hrec
    (fun n _ r hr => hV_nonpos n r hr)
    (fun n _ r hr => hW_nonpos n r hr)
    hdeg_succ hno

/-- Sequence-level Liu--Wang induction where the two sign checks are certified
on an explicit root window. -/
theorem prec_lw_derivative_lag_sequence_of_root_window
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {lo hi : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ hi n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_lw_derivative_lag_sequence
    hbase hpos hdeg_two hrec
    (fun n r hr => hV_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr))
    (fun n r hr => hW_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr))
    hdeg_succ hno

/-- Real-rootedness corollary for derivative-lag Liu--Wang induction where the
sign checks may use the current row's already proved real-rootedness. -/
theorem isRealRooted_of_lw_derivative_lag_sequence_of_root_signs
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos :
      ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
        ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits →
        ∀ r, (P (n + 1)).IsRoot r → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hprec : ∀ n : Nat, Prec (P n) (P (n + 1)) :=
    prec_lw_derivative_lag_sequence_of_root_signs
      hbase hpos hdeg_two hrec hV_nonpos hW_nonpos hdeg_succ hno
  intro n
  cases n with
  | zero =>
      exact hbase.1
  | succ n =>
      exact (hprec n).2.1

/-- Real-rootedness corollary for derivative-lag Liu--Wang induction with
direct root-sign side conditions. -/
theorem isRealRooted_of_lw_derivative_lag_sequence
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_lw_derivative_lag_sequence_of_root_signs
    hbase hpos hdeg_two hrec
    (fun n _ r hr => hV_nonpos n r hr)
    (fun n _ r hr => hW_nonpos n r hr)
    hdeg_succ hno

/-- Real-rootedness corollary for derivative-lag Liu--Wang induction on an
explicit root window. -/
theorem isRealRooted_of_lw_derivative_lag_sequence_of_root_window
    {P : Nat → ℝ[X]} {U V W : Nat → ℝ[X]} {lo hi : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hroot_lower : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r)
    (hroot_upper : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ hi n)
    (hV_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (V n).eval r ≤ 0)
    (hW_nonpos :
      ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → lo n ≤ r → r ≤ hi n →
        (W n).eval r ≤ 0)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_lw_derivative_lag_sequence
    hbase hpos hdeg_two hrec
    (fun n r hr => hV_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr))
    (fun n r hr => hW_nonpos n r hr (hroot_lower n r hr) (hroot_upper n r hr))
    hdeg_succ hno

end RealRooted
