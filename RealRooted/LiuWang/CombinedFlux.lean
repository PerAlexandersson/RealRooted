module

public import RealRooted.MaWang.Weak.DerivativeSign

/-!
# Combined root flux with repeated-root fallback

At simple roots, only the sign of the whole interlacing sum is needed.  At a
repeated root the first-derivative test is vacuous, so we retain the
coefficientwise signs there.  This condition is stable under deletion of a
common linear factor.  Coefficientwise signs at every root imply these
hypotheses, so the result contains the termwise finite-family criterion.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.LiuWang

/-- A finite-family interlacing step from combined root flux at simple roots,
with coefficientwise signs only at repeated roots. -/
theorem strictInterl_mul_add_sum_mul_of_combined_flux_of_pos
    {ι : Type*} {f a : ℝ[X]} {s : Finset ι} {b g : ι → ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hf : f.Splits)
    (hg : ∀ i ∈ s, StrictInterl (g i) f)
    (hg_pos : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (hflux : ∀ r, f.IsRoot r →
      (∑ i ∈ s, b i * g i).eval r * f.derivative.eval r ≤ 0)
    (hrepeated : ∀ i ∈ s, ∀ r, f.IsRoot r → 1 < f.rootMultiplicity r →
      (b i).eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + ∑ i ∈ s, b i * g i))
    (hdeg_lo : f.natDegree ≤ (a * f + ∑ i ∈ s, b i * g i).natDegree)
    (hdeg_hi : (a * f + ∑ i ∈ s, b i * g i).natDegree ≤ f.natDegree + 1) :
    StrictInterl f (a * f + ∑ i ∈ s, b i * g i) := by
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f g with
  | h n ih =>
    subst hn
    by_cases hnodup : f.roots.Nodup
    · refine strictInterl_of_eval_mul_derivative_nonpos hf_pos hf hnodup hF_pos hdeg_lo
        hdeg_hi fun r hr ↦ ?_
      rw [eval_add, eval_mul, hr.eq_zero, mul_zero, zero_add]
      exact hflux r hr
    · have hnot_count : ¬ ∀ r, f.roots.count r ≤ 1 := by
        intro hcount
        exact hnodup (Multiset.nodup_iff_count_le_one.mpr hcount)
      obtain ⟨r, hcount⟩ := not_forall.mp hnot_count
      have hmult : 1 < f.rootMultiplicity r := by
        rw [← count_roots]
        lia
      have hrf : f.IsRoot r :=
        (rootMultiplicity_pos hf_pos.ne_zero).mp (by lia)
      let d : ℝ[X] := X - C r
      let qf : ℝ[X] := f /ₘ d
      let qg : ι → ℝ[X] := fun i ↦ g i /ₘ d
      let qF : ℝ[X] := a * qf + ∑ i ∈ s, b i * qg i
      have hd_ne : d ≠ 0 := by
        simp [d, X_sub_C_ne_zero]
      have hdf : d * qf = f := by
        simpa [d, qf] using (mul_divByMonic_eq_iff_isRoot.mpr hrf)
      have hqf_ne : qf ≠ 0 := by
        intro hqf_zero
        rw [hqf_zero, mul_zero] at hdf
        exact hf_pos.ne_zero hdf.symm
      have hqf_pos : HasPosLeadingCoeff qf := by
        apply hasPosLeadingCoeff_of_X_sub_C_mul (r := r)
        simpa [d] using hdf.symm ▸ hf_pos
      have hqf_splits : qf.Splits :=
        (isRealRooted_of_dvd hf_pos.ne_zero hf hqf_ne (by
          refine ⟨d, ?_⟩
          simpa [mul_comm] using hdf.symm)).2
      have hri : ∀ i ∈ s, (g i).IsRoot r := by
        intro i hi
        have hbound := ((hg i hi).rootMultiplicity_bounds r).2
        apply (rootMultiplicity_pos (hg i hi).1.1).mp
        lia
      have hqg_factor : ∀ i ∈ s, d * qg i = g i := by
        intro i hi
        simpa [d, qg] using (mul_divByMonic_eq_iff_isRoot.mpr (hri i hi))
      have hqg_inter : ∀ i ∈ s, StrictInterl (qg i) qf := by
        intro i hi
        have hinter := hg i hi
        rw [← hqg_factor i hi, ← hdf] at hinter
        simpa [d] using hinter.of_mul_X_sub_C_both
      have hqg_pos : ∀ i ∈ s, HasPosLeadingCoeff (qg i) := by
        intro i hi
        have hprod : HasPosLeadingCoeff (d * qg i) := by
          rw [hqg_factor i hi]
          exact hg_pos i hi
        exact hasPosLeadingCoeff_of_X_sub_C_mul (r := r) (by simpa [d] using hprod)
      have hsum_factor : d * (∑ i ∈ s, b i * qg i) = ∑ i ∈ s, b i * g i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hqg_factor i hi]
        ring
      have hF_factor : d * qF = a * f + ∑ i ∈ s, b i * g i := by
        calc
          d * qF = a * (d * qf) + d * (∑ i ∈ s, b i * qg i) := by
            simp only [qF, mul_add]
            congr 1
            ring
          _ = a * f + ∑ i ∈ s, b i * g i := by rw [hdf, hsum_factor]
      have hqF_pos : HasPosLeadingCoeff qF := by
        rw [← hF_factor] at hF_pos
        simpa [HasPosLeadingCoeff, d, leadingCoeff_mul] using hF_pos
      have hqF_ne : qF ≠ 0 := hqF_pos.ne_zero
      have hqF_deg : (d * qF).natDegree = qF.natDegree + 1 := by
        rw [natDegree_mul hd_ne hqF_ne]
        simp [d, Nat.add_comm]
      have hqf_deg : (d * qf).natDegree = qf.natDegree + 1 := by
        rw [natDegree_mul hd_ne hqf_ne]
        simp [d, Nat.add_comm]
      have hqdeg_lo : qf.natDegree ≤ qF.natDegree := by
        have h : (d * qf).natDegree ≤ (d * qF).natDegree := by
          rw [hdf, hF_factor]
          exact hdeg_lo
        rw [hqf_deg, hqF_deg] at h
        lia
      have hqdeg_hi : qF.natDegree ≤ qf.natDegree + 1 := by
        have h : (d * qF).natDegree ≤ (d * qf).natDegree + 1 := by
          rw [hdf, hF_factor]
          exact hdeg_hi
        rw [hqF_deg, hqf_deg] at h
        lia
      have hqflux : ∀ t, qf.IsRoot t →
          (∑ i ∈ s, b i * qg i).eval t * qf.derivative.eval t ≤ 0 := by
        intro t ht
        by_cases htr : t = r
        · subst t
          rw [eval_finsetSum, Finset.sum_mul]
          refine Finset.sum_nonpos fun i hi ↦ ?_
          rw [eval_mul, mul_assoc]
          exact mul_nonpos_of_nonpos_of_nonneg (hrepeated i hi r hrf hmult)
            ((hqg_inter i hi).eval_mul_eval_derivative_nonneg
              (hqg_pos i hi) hqf_pos ht)
        · have htf : f.IsRoot t := by
            rw [← hdf, Polynomial.IsRoot.def, eval_mul, ht.eq_zero, mul_zero]
          have hder_eval : f.derivative.eval t =
              d.eval t * qf.derivative.eval t := by
            rw [← hdf, derivative_mul, eval_add, eval_mul, eval_mul, ht.eq_zero]
            ring
          have hdt_pos : 0 < (d.eval t) ^ 2 := by
            simp only [d, eval_sub, eval_X, eval_C]
            exact sq_pos_of_ne_zero (sub_ne_zero.mpr htr)
          have horig := hflux t htf
          rw [← hsum_factor, eval_mul, hder_eval] at horig
          ring_nf at horig
          nlinarith
      have hqrepeated : ∀ i ∈ s, ∀ t, qf.IsRoot t →
          1 < qf.rootMultiplicity t → (b i).eval t ≤ 0 := by
        intro i hi t ht htmult
        apply hrepeated i hi t
        · rw [← hdf, Polynomial.IsRoot.def, eval_mul, ht.eq_zero, mul_zero]
        · have hprod_ne : d * qf ≠ 0 := mul_ne_zero hd_ne hqf_ne
          rw [← hdf, rootMultiplicity_mul hprod_ne]
          lia
      have hqf_lt : qf.natDegree < f.natDegree := by
        have hdegf : f.natDegree = qf.natDegree + 1 := by
          rw [← hdf, hqf_deg]
        lia
      have hq : StrictInterl qf qF :=
        ih qf.natDegree hqf_lt hqf_pos hqf_splits hqg_inter hqg_pos hqflux
          hqrepeated hqF_pos hqdeg_lo hqdeg_hi rfl
      have hrestore := hq.mul_X_sub_C_both r
      rw [hdf, hF_factor] at hrestore
      exact hrestore

/-- The derivative--lag specialization of the combined-flux criterion.

The separate signs of `v` and `w` are required only at repeated roots of
`f`; at every root, their two contributions may compensate in the combined
flux inequality. -/
theorem strictInterl_derivative_lag_of_combined_flux
    {f g u v w : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hf : f.Splits)
    (hgf : StrictInterl g f) (hg_pos : HasPosLeadingCoeff g)
    (hflux : ∀ r, f.IsRoot r →
      (v.eval r * f.derivative.eval r + w.eval r * g.eval r) *
        f.derivative.eval r ≤ 0)
    (hv_repeated : ∀ r, f.IsRoot r → 1 < f.rootMultiplicity r → v.eval r ≤ 0)
    (hw_repeated : ∀ r, f.IsRoot r → 1 < f.rootMultiplicity r → w.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative + w * g))
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative + w * g).natDegree)
    (hdeg_hi : (u * f + v * f.derivative + w * g).natDegree ≤ f.natDegree + 1) :
    StrictInterl f (u * f + v * f.derivative + w * g) := by
  by_cases hdeg0 : f.natDegree = 0
  · have hder_zero : f.derivative = 0 := derivative_eq_zero.mpr hdeg0
    have hsingle := strictInterl_mul_add_sum_mul_of_combined_flux_of_pos hf_pos hf
      (s := ({0} : Finset Unit)) (b := fun _ : Unit ↦ w) (g := fun _ : Unit ↦ g)
      (fun i hi ↦ by simpa using hgf)
      (fun i hi ↦ by simpa using hg_pos)
      (fun r hr ↦ by simp [hder_zero])
      (fun i hi r hr hm ↦ by simpa using hw_repeated r hr hm)
      (by simpa [hder_zero] using hF_pos)
      (by simpa [hder_zero] using hdeg_lo)
      (by simpa [hder_zero] using hdeg_hi)
    simpa [hder_zero] using hsingle
  · have hdeg_pos : 1 ≤ f.natDegree := by lia
    have hder : StrictInterl f.derivative f :=
      (interlaces_derivative_of_pos_natDegree hf_pos.ne_zero hf hf_pos hdeg_pos).toStrictInterl
    have hder_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative hdeg0
    let g₂ : Fin 2 → ℝ[X] := fun i ↦ if i = 0 then f.derivative else g
    let b₂ : Fin 2 → ℝ[X] := fun i ↦ if i = 0 then v else w
    have hsum : u * f + ∑ i ∈ (Finset.univ : Finset (Fin 2)), b₂ i * g₂ i =
        u * f + v * f.derivative + w * g := by
      simp [g₂, b₂, Fin.sum_univ_two]
      ring
    have hstep := strictInterl_mul_add_sum_mul_of_combined_flux_of_pos hf_pos hf
      (s := (Finset.univ : Finset (Fin 2))) (b := b₂) (g := g₂)
      (fun i hi ↦ by
        fin_cases i
        · simpa [g₂] using hder
        · simpa [g₂] using hgf)
      (fun i hi ↦ by
        fin_cases i
        · simpa [g₂] using hder_pos
        · simpa [g₂] using hg_pos)
      (fun r hr ↦ by
        simpa [b₂, g₂, Fin.sum_univ_two, eval_add, eval_mul, add_mul] using hflux r hr)
      (fun i hi r hr hm ↦ by
        fin_cases i
        · simpa [b₂] using hv_repeated r hr hm
        · simpa [b₂] using hw_repeated r hr hm)
      (by rw [hsum]; exact hF_pos)
      (by rw [hsum]; exact hdeg_lo)
      (by rw [hsum]; exact hdeg_hi)
    rw [hsum] at hstep
    exact hstep

end RealRooted.LiuWang
