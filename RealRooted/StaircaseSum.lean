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
  have hf_rr : (f ≠ 0 ∧ f.Splits) := hfs.realRooted f (List.get_mem _ _)
  have hf_nonneg : HasNonnegCoeffs f := hfs.nonnegCoeffs f (List.get_mem _ _)
  by_cases hm0 : m = 0
  · subst hm0
    have hfs_eq : fs = f :: fs.drop 1 := by simpa [f] using (List.drop_eq_getElem_cons hm)
    have hf_mem_take : f ∈ fs.take 1 := by grind
    have hprec : ∀ p ∈ fs, Prec f p := fun p hp => by
      rw [hfs_eq] at hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · simpa [f] using prec_refl hf_rr.1 hf_rr.2
      · exact hpair.rel_of_mem_take_of_mem_drop hf_mem_take hp'
    have hne : fs ≠ [] := by grind
    simpa [staircaseSum, f] using
      prec_sum_left_of_common_left_signed fs f hprec hfs.posLeadingCoeff hne
  · have htake_ne : fs.take m ≠ [] := fun hnil => by
      have hlen : (fs.take m).length = 0 := by simp [hnil]
      grind
    have hf_mem_drop : f ∈ fs.drop m := by
      rw [List.mem_iff_getElem?]
      refine ⟨0, ?_⟩
      grind
    have hprefix_prec : Prec (fs.take m).sum f :=
      prec_sum_right (fs.take m) f
        (fun _ hp => hpair.rel_of_mem_take_of_mem_drop hp hf_mem_drop)
        (fun p hp => hfs.posLeadingCoeff p (List.mem_of_mem_take hp))
        htake_ne
    have hprefix_nonneg : HasNonnegCoeffs (fs.take m).sum :=
      hasNonnegCoeffs_sum (fs.take m)
        (fun p hp => hfs.nonnegCoeffs p (List.mem_of_mem_take hp))
    have hXprefix_prec : Prec f (X * (fs.take m).sum) :=
      prec_mul_X_of_prec_of_nonneg hprefix_prec hprefix_nonneg hf_nonneg
    have htake_succ : fs.take (m + 1) = fs.take m ++ [f] := by simp [f]
    have hf_mem_take_succ : f ∈ fs.take (m + 1) := by simp_all
    have hcommon_left : ∀ p ∈ (X * (fs.take m).sum) :: fs.drop m, Prec f p :=
      fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hXprefix_prec
      · rw [List.drop_eq_getElem_cons hm] at hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · simpa [f] using prec_refl hf_rr.1 hf_rr.2
        · exact hpair.rel_of_mem_take_of_mem_drop hf_mem_take_succ hp'
    have hpos : ∀ p ∈ (X * (fs.take m).sum) :: fs.drop m, HasPosLeadingCoeff p :=
      fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact (hprefix_nonneg.pos_leadingCoeff
          (right_ne_zero_of_mul hXprefix_prec.2.1.1)).X_mul
      · exact hfs.posLeadingCoeff p (List.mem_of_mem_drop hp)
    have hsum_prec : Prec f (((X * (fs.take m).sum) :: fs.drop m).sum) :=
      prec_sum_left_of_common_left_signed
        ((X * (fs.take m).sum) :: fs.drop m) f hcommon_left hpos (by lia)
    simpa [staircaseSum, f, List.sum_cons] using hsum_prec

/-- Real-rootedness corollary for staircase-weighted sums of an interlacing
sequence with nonnegative coefficients. -/
theorem isRealRooted_staircaseSum_of_isInterlacingSeqNonneg
    {fs : List ℝ[X]} {m : Nat}
    (hfs : IsInterlacingSeqNonneg fs)
    (hm : m < fs.length) : ((staircaseSum fs m) ≠ 0 ∧ (staircaseSum fs m).Splits) :=
  (prec_get_staircaseSum_of_isInterlacingSeqNonneg hfs hm).2.1

end RealRooted
