import RealRooted.MaWang
import RealRooted.Interlacing.Multiplicity
import RealRooted.SimpleRoots

/-!
# Strict Ma--Wang steps

The strict root-sign version of the differ-by-one Ma--Wang recurrence step.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A strict differ-by-one Ma--Wang step puts `f` in proper position with `F`
and propagates simple real roots. -/
theorem prec_and_hasSimpleRoots_of_interlaces_eval_mul_neg_succ {f F u v : ℝ[X]}
    (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hF_pos : HasPosLeadingCoeff F) (hdegf : 1 ≤ f.natDegree)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hsimple : HasSimpleRoots f) (hrec : F = u * f + v * f.derivative)
    (hv_neg : ∀ r, f.IsRoot r → v.eval r < 0) :
    Prec f F ∧ HasSimpleRoots F := by
  have hder : Interlaces f.derivative f :=
    interlaces_derivative_of_pos_natDegree hf_pos.ne_zero hf hf_pos hdegf
  have hder_pos : HasPosLeadingCoeff f.derivative :=
    hf_pos.derivative (by lia)
  have hroot_sign :
      ∀ r, f.IsRoot r → F.eval r * f.derivative.eval r < 0 := by
    intro r hr
    have hder_ne := hsimple.eval_derivative_ne_zero hr
    have hstrict : v.eval r * (f.derivative.eval r) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (hv_neg r hr) (sq_pos_iff.mpr hder_ne)
    have hfeval : f.eval r = 0 := hr
    calc
      F.eval r * f.derivative.eval r =
          (u * f + v * f.derivative).eval r * f.derivative.eval r := by
            rw [hrec]
      _ = v.eval r * (f.derivative.eval r) ^ 2 := by
        rw [eval_add, eval_mul, eval_mul, hfeval, mul_zero, zero_add]
        ring
      _ < 0 := hstrict
  have hprec : Prec f F :=
    prec_of_interlaces_eval_mul_neg_succ hder hder_pos hF_pos hdeg hroot_sign
  have hno : ∀ r, f.IsRoot r → ¬ F.IsRoot r := by
    intro r hfr hFr
    have hs := hroot_sign r hfr
    have hFzero : F.eval r = 0 := hFr
    rw [hFzero, zero_mul] at hs
    exact (lt_irrefl 0) hs
  have hnodup : F.roots.Nodup := by
    by_contra hnot
    obtain ⟨r, hFr, hfr⟩ := exists_common_root_of_not_nodup hprec hnot
    exact hno r (isRoot_of_mem_roots hfr) (isRoot_of_mem_roots hFr)
  exact ⟨hprec, HasSimpleRoots.of_roots_nodup hF_pos.ne_zero hnodup⟩

end RealRooted
