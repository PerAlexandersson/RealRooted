import RealRooted.ProductFamily

/-!
# Staircase-weighted sums

This file packages interlacing for the staircase-weighted sum
`X * (f_0 + ... + f_{m-1}) + (f_m + ... + f_{n-1})`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The staircase-weighted sum
`X * (f₀ + ··· + f_{m-1}) + (f_m + ··· + f_{n-1})`. -/
def staircaseSum (fs : List ℝ[X]) (m : Nat) : ℝ[X] :=
  X * (fs.take m).sum + (fs.drop m).sum

@[simp] theorem staircaseSum_zero (fs : List ℝ[X]) :
    staircaseSum fs 0 = fs.sum := by
  simp [staircaseSum]

@[simp] theorem staircaseSum_length (fs : List ℝ[X]) :
    staircaseSum fs fs.length = X * fs.sum := by
  simp [staircaseSum]

/-- In an interlacing sequence with nonnegative coefficients, the distinguished
term `f_m` interlaces the staircase-weighted sum built at the same index. -/
theorem prec_get_staircaseSum_of_isInterlacingSeqNonneg
    {fs : List ℝ[X]} {m : Nat}
    (hfs : IsInterlacingSeqNonneg fs)
    (hm : m < fs.length) :
    Prec (fs.get ⟨m, hm⟩) (staircaseSum fs m) := by
  let f : ℝ[X] := fs.get ⟨m, hm⟩
  have hpair : fs.Pairwise Prec := (isInterlacingSeq_iff_pairwise.mp hfs.2)
  have hf_rr : IsRealRooted f := hfs.realRooted f (List.get_mem _ _)
  have hf_nonneg : HasNonnegCoeffs f := hfs.nonnegCoeffs f (List.get_mem _ _)
  by_cases hm0 : m = 0
  · subst hm0
    have hfs_eq : fs = f :: fs.drop 1 := by
      simpa [f] using (List.drop_eq_getElem_cons hm)
    have hf_mem_take : f ∈ fs.take 1 := by
      rw [← List.take_append_drop 1 fs, hfs_eq]
      simp
    have hprec : ∀ p ∈ fs, Prec f p := by
      intro p hp
      rw [hfs_eq] at hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · simpa [f] using prec_refl hf_rr
      · exact hpair.rel_of_mem_take_of_mem_drop hf_mem_take hp'
    have hne : fs ≠ [] := by
      intro hnil
      simp [hnil] at hm
    simpa [staircaseSum] using
      prec_sum_left_of_common_left_signed fs f hprec
        (fun p hp => hfs.posLeadingCoeff p hp) hne
  · have htake_ne : fs.take m ≠ [] := by
      intro hnil
      have hlen : (fs.take m).length = 0 := by simp [hnil]
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hm)] at hlen
      lia
    have hf_mem_drop : f ∈ fs.drop m := by
      rw [List.mem_iff_getElem?]
      refine ⟨0, ?_⟩
      rw [List.getElem?_drop, Nat.add_zero]
      simp [f, hm]
    have hprefix_prec : Prec (fs.take m).sum f := by
      apply prec_sum_right (fs.take m) f
      · intro p hp
        exact hpair.rel_of_mem_take_of_mem_drop hp hf_mem_drop
      · intro p hp
        exact hfs.posLeadingCoeff p (List.mem_of_mem_take hp)
      · exact htake_ne
    have hprefix_nonneg : HasNonnegCoeffs (fs.take m).sum := by
      exact hasNonnegCoeffs_sum (fs.take m)
        (fun p hp => hfs.nonnegCoeffs p (List.mem_of_mem_take hp))
    have hXprefix_prec : Prec f (X * (fs.take m).sum) := by
      exact prec_mul_X_of_prec_of_nonneg hprefix_prec hprefix_nonneg hf_nonneg
    have htake_succ : fs.take (m + 1) = fs.take m ++ [f] := by
      simp [f]
    have hf_mem_take_succ : f ∈ fs.take (m + 1) := by
      rw [htake_succ]
      simp
    have hcommon_left : ∀ p ∈ (X * (fs.take m).sum) :: fs.drop m, Prec f p := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hXprefix_prec
      · rw [List.drop_eq_getElem_cons hm] at hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · simpa [f] using prec_refl hf_rr
        · exact hpair.rel_of_mem_take_of_mem_drop hf_mem_take_succ hp'
    have hpos : ∀ p ∈ (X * (fs.take m).sum) :: fs.drop m, HasPosLeadingCoeff p := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact (hasNonnegCoeffs_X.mul hprefix_nonneg).pos_leadingCoeff hXprefix_prec.2.1.1
      · exact hfs.posLeadingCoeff p (List.mem_of_mem_drop hp)
    have hsum_prec : Prec f (((X * (fs.take m).sum) :: fs.drop m).sum) := by
      exact prec_sum_left_of_common_left_signed
        ((X * (fs.take m).sum) :: fs.drop m) f hcommon_left hpos (by simp)
    simpa [staircaseSum, List.sum_cons] using hsum_prec

/-- Real-rootedness corollary for staircase-weighted sums of an interlacing
sequence with nonnegative coefficients. -/
theorem isRealRooted_staircaseSum_of_isInterlacingSeqNonneg
    {fs : List ℝ[X]} {m : Nat}
    (hfs : IsInterlacingSeqNonneg fs)
    (hm : m < fs.length) :
    IsRealRooted (staircaseSum fs m) :=
  (prec_get_staircaseSum_of_isInterlacingSeqNonneg hfs hm).2.1

end RealRooted
