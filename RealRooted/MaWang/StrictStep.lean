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

/-- A strictly signed derivative auxiliary remains strict after adding a tail
which is weakly nonpositive relative to the old derivative. -/
theorem eval_mul_derivative_neg_of_auxiliary_sign_add_tail
    {f q t F u v : ℝ[X]}
    (hrec : F = u * f + v * q + t)
    (hq_sign : ∀ r, f.IsRoot r →
      0 < q.eval r * f.derivative.eval r)
    (hv_neg : ∀ r, f.IsRoot r → v.eval r < 0)
    (ht_nonpos : ∀ r, f.IsRoot r →
      t.eval r * f.derivative.eval r ≤ 0)
    {r : ℝ} (hr : f.IsRoot r) :
    F.eval r * f.derivative.eval r < 0 := by
  have hfeval : f.eval r = 0 := hr
  have hhead :
      v.eval r * (q.eval r * f.derivative.eval r) < 0 :=
    mul_neg_of_neg_of_pos (hv_neg r hr) (hq_sign r hr)
  calc
    F.eval r * f.derivative.eval r =
        (u * f + v * q + t).eval r * f.derivative.eval r := by rw [hrec]
    _ = v.eval r * (q.eval r * f.derivative.eval r) +
        t.eval r * f.derivative.eval r := by
      rw [eval_add, eval_add, eval_mul, eval_mul, hfeval, mul_zero, zero_add]
      ring
    _ < 0 := add_neg_of_neg_of_nonpos hhead (ht_nonpos r hr)

/-- If `q` has the derivative's sign at each root of `f`, then multiplying it
by a coefficient which is negative there gives the strict successor sign for
`F = u * f + v * q`. -/
theorem eval_mul_derivative_neg_of_auxiliary_sign
    {f q F u v : ℝ[X]}
    (hrec : F = u * f + v * q)
    (hq_sign : ∀ r, f.IsRoot r →
      0 < q.eval r * f.derivative.eval r)
    (hv_neg : ∀ r, f.IsRoot r → v.eval r < 0)
    {r : ℝ} (hr : f.IsRoot r) :
    F.eval r * f.derivative.eval r < 0 := by
  apply eval_mul_derivative_neg_of_auxiliary_sign_add_tail
    (t := 0) (u := u) (v := v) (q := q)
  · simpa using hrec
  · exact hq_sign
  · exact hv_neg
  · simp
  · exact hr

/-- The strict auxiliary term prevents a common old root even in the presence
of a weakly signed tail. -/
theorem noCommonRoot_of_auxiliary_sign_add_tail
    {f q t F u v : ℝ[X]}
    (hrec : F = u * f + v * q + t)
    (hq_sign : ∀ r, f.IsRoot r →
      0 < q.eval r * f.derivative.eval r)
    (hv_neg : ∀ r, f.IsRoot r → v.eval r < 0)
    (ht_nonpos : ∀ r, f.IsRoot r →
      t.eval r * f.derivative.eval r ≤ 0) :
    ∀ r, f.IsRoot r → ¬ F.IsRoot r := by
  intro r hfr hFr
  have hsign :=
    eval_mul_derivative_neg_of_auxiliary_sign_add_tail
      hrec hq_sign hv_neg ht_nonpos hfr
  have hFzero : F.eval r = 0 := hFr
  rw [hFzero, zero_mul] at hsign
  exact (lt_irrefl 0) hsign

/-- The strict auxiliary sign also prevents `f` and its successor `F` from
sharing a real root. -/
theorem noCommonRoot_of_auxiliary_sign
    {f q F u v : ℝ[X]}
    (hrec : F = u * f + v * q)
    (hq_sign : ∀ r, f.IsRoot r →
      0 < q.eval r * f.derivative.eval r)
    (hv_neg : ∀ r, f.IsRoot r → v.eval r < 0) :
    ∀ r, f.IsRoot r → ¬ F.IsRoot r := by
  apply noCommonRoot_of_auxiliary_sign_add_tail
    (t := 0) (u := u) (v := v) (q := q)
  · simpa using hrec
  · exact hq_sign
  · exact hv_neg
  · simp

/-- A degree-raising recurrence through a strictly signed auxiliary and a
weakly signed tail puts `f` in proper position with `F` and gives `F` simple
roots. -/
theorem prec_and_hasSimpleRoots_of_auxiliary_sign_succ_add_tail
    {f q t F u v : ℝ[X]}
    (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hF_pos : HasPosLeadingCoeff F) (hdegf : 1 ≤ f.natDegree)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hrec : F = u * f + v * q + t)
    (hq_sign : ∀ r, f.IsRoot r →
      0 < q.eval r * f.derivative.eval r)
    (hv_neg : ∀ r, f.IsRoot r → v.eval r < 0)
    (ht_nonpos : ∀ r, f.IsRoot r →
      t.eval r * f.derivative.eval r ≤ 0) :
    Prec f F ∧ HasSimpleRoots F := by
  have hder : Interlaces f.derivative f :=
    interlaces_derivative_of_pos_natDegree hf_pos.ne_zero hf hf_pos hdegf
  have hder_pos : HasPosLeadingCoeff f.derivative :=
    hf_pos.derivative (by lia)
  have hroot_sign : ∀ r, f.IsRoot r →
      F.eval r * f.derivative.eval r < 0 :=
    fun _ hr ↦
      eval_mul_derivative_neg_of_auxiliary_sign_add_tail
        hrec hq_sign hv_neg ht_nonpos hr
  have hprec : Prec f F :=
    prec_of_interlaces_eval_mul_neg_succ hder hder_pos hF_pos hdeg hroot_sign
  have hnoRoot :=
    noCommonRoot_of_auxiliary_sign_add_tail hrec hq_sign hv_neg ht_nonpos
  have hno : ∀ r : ℝ, ¬ (f.IsRoot r ∧ F.IsRoot r) :=
    fun r h ↦ hnoRoot r h.1 h.2
  exact ⟨hprec, (hprec.hasSimpleRoots_of_no_common_root hno).2⟩

/-- A degree-raising recurrence through a derivative-sign auxiliary puts `f`
in proper position with `F` and gives `F` simple roots. -/
theorem prec_and_hasSimpleRoots_of_auxiliary_sign_succ
    {f q F u v : ℝ[X]}
    (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hF_pos : HasPosLeadingCoeff F) (hdegf : 1 ≤ f.natDegree)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hrec : F = u * f + v * q)
    (hq_sign : ∀ r, f.IsRoot r →
      0 < q.eval r * f.derivative.eval r)
    (hv_neg : ∀ r, f.IsRoot r → v.eval r < 0) :
    Prec f F ∧ HasSimpleRoots F := by
  apply prec_and_hasSimpleRoots_of_auxiliary_sign_succ_add_tail
    hf hf_pos hF_pos hdegf hdeg (t := 0)
  · simpa using hrec
  · exact hq_sign
  · exact hv_neg
  · simp

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
