import RealRooted.Interlacing.Multiplicity
import RealRooted.Interlacing.Residue
import RealRooted.MaWang.Weak.DerivativeSign

/-!
# The finite-family Liu--Wang criterion

This file formalizes Theorem 2.3 of Liu--Wang, *A unified approach to polynomial
sequences with only real zeros* (arXiv:math/0509207v5, DOI
10.1016/j.aam.2006.02.003).

The combined condition `F(r) * f'(r) ≤ 0` does not suffice at repeated roots, where it is
vacuous: `f = X^2`, `g = X` and `F = X^3 + X^2 + X` satisfy it at zero, but `F` has two nonreal
roots.  The theorem below keeps the termwise hypotheses `b i (r) ≤ 0` instead.
-/

open Polynomial

noncomputable section

namespace RealRooted.LiuWang

private theorem strictInterl_mul_add_sum_mul_of_eval_nonpos_core
    {ι : Type*} {f a : ℝ[X]} {s : Finset ι} {b g : ι → ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hf : f.Splits)
    (hg : ∀ i ∈ s, StrictInterl (g i) f)
    (hg_pos : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (hb : ∀ i ∈ s, ∀ r, f.IsRoot r → (b i).eval r ≤ 0)
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
      rw [eval_add, eval_mul, hr.eq_zero, mul_zero, zero_add, eval_finsetSum, Finset.sum_mul]
      refine Finset.sum_nonpos fun i hi ↦ ?_
      rw [eval_mul, mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg (hb i hi r hr)
        ((hg i hi).eval_mul_eval_derivative_nonneg (hg_pos i hi) hf_pos hr)
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
        exact hf_pos.divByMonic_X_sub_C hrf
      have hqf_splits : qf.Splits :=
        (isRealRooted_of_dvd hf_pos.ne_zero hf hqf_ne (by
          refine ⟨d, ?_⟩
          simpa [mul_comm] using hdf.symm)).2
      have hqg_inter : ∀ i ∈ s, StrictInterl (qg i) qf := by
        intro i hi
        have hri : (g i).IsRoot r :=
          (hg i hi).isRoot_of_one_lt_rootMultiplicity hmult
        simpa [qf, qg, d] using (hg i hi).cofactor_of_common_root hrf hri
      have hqg_pos : ∀ i ∈ s, HasPosLeadingCoeff (qg i) := by
        intro i hi
        have hri : (g i).IsRoot r :=
          (hg i hi).isRoot_of_one_lt_rootMultiplicity hmult
        exact (hg_pos i hi).divByMonic_X_sub_C hri
      have hqg_factor : ∀ i ∈ s, d * qg i = g i := by
        intro i hi
        have hri : (g i).IsRoot r :=
          (hg i hi).isRoot_of_one_lt_rootMultiplicity hmult
        simpa [d, qg] using (mul_divByMonic_eq_iff_isRoot.mpr hri)
      have hF_factor : d * qF = a * f + ∑ i ∈ s, b i * g i := by
        calc
          d * qF = a * (d * qf) + ∑ i ∈ s, b i * (d * qg i) := by
            simp only [qF, mul_add, Finset.mul_sum]
            congr 1
            · ring
            · apply Finset.sum_congr rfl
              intro i hi
              ring
          _ = a * f + ∑ i ∈ s, b i * g i := by
            rw [hdf]
            apply congrArg (fun p ↦ a * f + p)
            apply Finset.sum_congr rfl
            intro i hi
            rw [hqg_factor i hi]
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
      have hqsign : ∀ i ∈ s, ∀ t, qf.IsRoot t → (b i).eval t ≤ 0 := by
        intro i hi t ht
        apply hb i hi t
        rw [← hdf]
        rw [Polynomial.IsRoot.def] at ht
        rw [Polynomial.IsRoot.def, eval_mul]
        rw [ht, mul_zero]
      have hqf_lt : qf.natDegree < f.natDegree := by
        have hdegf : f.natDegree = qf.natDegree + 1 := by
          rw [← hdf, hqf_deg]
        lia
      have hq : StrictInterl qf qF :=
        ih qf.natDegree hqf_lt hqf_pos hqf_splits hqg_inter hqg_pos hqsign hqF_pos
          hqdeg_lo hqdeg_hi rfl
      have hrestore := hq.mul_X_sub_C_both r
      rw [hdf, hF_factor] at hrestore
      exact hrestore

/-! ## Sign normalization -/

private theorem strictInterl_mul_add_sum_mul_of_eval_nonpos_pos_f
    {ι : Type*} {f a : ℝ[X]} {s : Finset ι} {b g : ι → ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hf : f.Splits)
    (hg : ∀ i ∈ s, StrictInterl (g i) f)
    (hg_pos : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (hb : ∀ i ∈ s, ∀ r, f.IsRoot r → (b i).eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + ∑ i ∈ s, b i * g i))
    (hdeg_lo : f.natDegree ≤ (a * f + ∑ i ∈ s, b i * g i).natDegree)
    (hdeg_hi : (a * f + ∑ i ∈ s, b i * g i).natDegree ≤ f.natDegree + 1) :
    StrictInterl f (a * f + ∑ i ∈ s, b i * g i) :=
  strictInterl_mul_add_sum_mul_of_eval_nonpos_core hf_pos hf hg hg_pos hb hF_pos hdeg_lo hdeg_hi

/-- The finite-family Liu--Wang criterion with positive leading coefficients.

Every member of the finite family is below `f`; the coefficient of each member
is nonpositive at the roots of `f`; and the resulting polynomial has the same
positive leading orientation and one of the two allowed degrees.
-/
theorem strictInterl_mul_add_sum_mul_of_eval_nonpos_of_pos
    {ι : Type*} {f a : ℝ[X]} {s : Finset ι} {b g : ι → ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hf : f.Splits)
    (hg : ∀ i ∈ s, StrictInterl (g i) f)
    (hg_pos : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (hb : ∀ i ∈ s, ∀ r, f.IsRoot r → (b i).eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + ∑ i ∈ s, b i * g i))
    (hdeg_lo : f.natDegree ≤ (a * f + ∑ i ∈ s, b i * g i).natDegree)
    (hdeg_hi : (a * f + ∑ i ∈ s, b i * g i).natDegree ≤ f.natDegree + 1) :
    StrictInterl f (a * f + ∑ i ∈ s, b i * g i) :=
  strictInterl_mul_add_sum_mul_of_eval_nonpos_pos_f
    hf_pos hf hg hg_pos hb hF_pos hdeg_lo hdeg_hi

/-- The finite-family Liu--Wang criterion, allowing either sign for the
leading coefficient of `f`.

The leading coefficients of the interlacers and of the output are positive;
the sign of `f` is absorbed into the multiplier `a`.
-/
theorem strictInterl_mul_add_sum_mul_of_eval_nonpos
    {ι : Type*} {f a : ℝ[X]} {s : Finset ι} {b g : ι → ℝ[X]}
    (hf_ne : f ≠ 0) (hf : f.Splits)
    (hg : ∀ i ∈ s, StrictInterl (g i) f)
    (hg_pos : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (hb : ∀ i ∈ s, ∀ r, f.IsRoot r → (b i).eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + ∑ i ∈ s, b i * g i))
    (hdeg_lo : f.natDegree ≤ (a * f + ∑ i ∈ s, b i * g i).natDegree)
    (hdeg_hi : (a * f + ∑ i ∈ s, b i * g i).natDegree ≤ f.natDegree + 1) :
    StrictInterl f (a * f + ∑ i ∈ s, b i * g i) := by
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hf_ne) with hneg | hpos
  · have hnf_pos : HasPosLeadingCoeff (-f) := by
      simpa [HasPosLeadingCoeff] using hneg
    have hng : ∀ i ∈ s, StrictInterl (g i) (-f) := by
      intro i hi
      simpa using (hg i hi).C_mul_right (a := (-1 : ℝ)) (by norm_num)
    have hF_eq : a * f + ∑ i ∈ s, b i * g i =
        (-a) * (-f) + ∑ i ∈ s, b i * g i := by
      ring
    rw [hF_eq] at hF_pos hdeg_lo hdeg_hi ⊢
    have h := strictInterl_mul_add_sum_mul_of_eval_nonpos_pos_f hnf_pos
      (by simpa using hf) hng hg_pos
      (fun i hi r hr ↦ hb i hi r (by simpa using hr)) hF_pos
      (by simpa [natDegree_neg] using hdeg_lo)
      (by simpa [natDegree_neg] using hdeg_hi)
    simpa using h.C_mul_left (a := (-1 : ℝ)) (by norm_num)
  · exact strictInterl_mul_add_sum_mul_of_eval_nonpos_pos_f
      (by simpa [HasPosLeadingCoeff] using hpos) hf hg hg_pos hb hF_pos hdeg_lo hdeg_hi

/-- The finite-family Liu--Wang criterion for a common nonzero leading sign.

The sign hypothesis is presented as a disjunction so that it records both the
positive and negative common orientations without choosing a normalization.
-/
theorem strictInterl_mul_add_sum_mul_of_eval_nonpos_of_common_sign
    {ι : Type*} {f a : ℝ[X]} {s : Finset ι} {b g : ι → ℝ[X]}
    (hf_ne : f ≠ 0) (hf : f.Splits)
    (hg : ∀ i ∈ s, StrictInterl (g i) f)
    (hb : ∀ i ∈ s, ∀ r, f.IsRoot r → (b i).eval r ≤ 0)
    (hsign : (HasPosLeadingCoeff (a * f + ∑ i ∈ s, b i * g i) ∧
        ∀ i ∈ s, HasPosLeadingCoeff (g i)) ∨
      (HasPosLeadingCoeff (-(a * f + ∑ i ∈ s, b i * g i)) ∧
        ∀ i ∈ s, HasPosLeadingCoeff (-g i)))
    (hdeg_lo : f.natDegree ≤ (a * f + ∑ i ∈ s, b i * g i).natDegree)
    (hdeg_hi : (a * f + ∑ i ∈ s, b i * g i).natDegree ≤ f.natDegree + 1) :
    StrictInterl f (a * f + ∑ i ∈ s, b i * g i) := by
  rcases hsign with hpos | hneg
  · exact strictInterl_mul_add_sum_mul_of_eval_nonpos hf_ne hf hg hpos.2 hb hpos.1 hdeg_lo hdeg_hi
  · have hneg_eq : -(a * f + ∑ i ∈ s, b i * g i) =
        (-a) * f + ∑ i ∈ s, b i * (-g i) := by
      simp only [neg_add, mul_neg]
      rw [← Finset.sum_neg_distrib]
      ring
    have hF_pos : HasPosLeadingCoeff ((-a) * f + ∑ i ∈ s, b i * (-g i)) := by
      rw [← hneg_eq]
      exact hneg.1
    have hdeg_lo' : f.natDegree ≤ ((-a) * f + ∑ i ∈ s, b i * (-g i)).natDegree := by
      rw [← hneg_eq, natDegree_neg]
      exact hdeg_lo
    have hdeg_hi' : ((-a) * f + ∑ i ∈ s, b i * (-g i)).natDegree ≤ f.natDegree + 1 := by
      rw [← hneg_eq, natDegree_neg]
      exact hdeg_hi
    have h := strictInterl_mul_add_sum_mul_of_eval_nonpos hf_ne hf
      (fun i hi ↦ by
        simpa using (hg i hi).C_mul_left (a := (-1 : ℝ)) (by norm_num))
      hneg.2
      (fun i hi r hr ↦ hb i hi r hr)
      hF_pos hdeg_lo' hdeg_hi'
    simpa [hneg_eq, add_comm] using h.C_mul_right (a := (-1 : ℝ)) (by norm_num)

/-! ## Derivative--lag specialization -/

/-- The finite-family criterion for a derivative--lag step.

The derivative and lag summands are treated symmetrically, so common roots are
allowed and the degree bounds include both the plateau and successor cases.
-/
theorem strictInterl_derivative_lag_of_eval_nonpos
    {f g u v w : ℝ[X]}
    (hf_ne : f ≠ 0) (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hgf : StrictInterl g f) (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative + w * g))
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative + w * g).natDegree)
    (hdeg_hi : (u * f + v * f.derivative + w * g).natDegree ≤ f.natDegree + 1)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0)
    (hw_nonpos : ∀ r, f.IsRoot r → w.eval r ≤ 0) :
    StrictInterl f (u * f + v * f.derivative + w * g) := by
  by_cases hdeg0 : f.natDegree = 0
  · have hder_zero : f.derivative = 0 := Polynomial.derivative_eq_zero.mpr hdeg0
    have hsingle := strictInterl_mul_add_sum_mul_of_eval_nonpos hf_ne hf
      (s := ({0} : Finset Unit)) (b := fun _ : Unit ↦ w) (g := fun _ : Unit ↦ g)
      (fun i hi ↦ by simpa using hgf)
      (fun i hi ↦ by simpa using hg_pos)
      (fun i hi r hr ↦ by simpa using hw_nonpos r hr)
      (by simpa [hder_zero] using hF_pos)
      (by simpa [hder_zero] using hdeg_lo)
      (by simpa [hder_zero] using hdeg_hi)
    simpa [hder_zero] using hsingle
  · have hdeg_pos : 1 ≤ f.natDegree := by lia
    have hder : StrictInterl f.derivative f :=
      (interlaces_derivative_of_pos_natDegree hf_ne hf hf_pos hdeg_pos).toStrictInterl
    have hder_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative hdeg0
    let g₂ : Fin 2 → ℝ[X] := fun i ↦ if i = 0 then f.derivative else g
    let b₂ : Fin 2 → ℝ[X] := fun i ↦ if i = 0 then v else w
    have hsum : u * f + ∑ i ∈ (Finset.univ : Finset (Fin 2)), b₂ i * g₂ i =
        u * f + v * f.derivative + w * g := by
      simp [g₂, b₂, Fin.sum_univ_two]
      ring
    have hstep := strictInterl_mul_add_sum_mul_of_eval_nonpos hf_ne hf
      (s := (Finset.univ : Finset (Fin 2))) (b := b₂) (g := g₂)
      (fun i hi ↦ by
        fin_cases i
        · simpa [g₂] using hder
        · simpa [g₂] using hgf)
      (fun i hi ↦ by
        fin_cases i
        · simpa [g₂] using hder_pos
        · simpa [g₂] using hg_pos)
      (fun i hi r hr ↦ by
        fin_cases i
        · simpa [b₂] using hv_nonpos r hr
        · simpa [b₂] using hw_nonpos r hr)
      (by rw [hsum]; exact hF_pos)
      (by rw [hsum]; exact hdeg_lo)
      (by rw [hsum]; exact hdeg_hi)
    rw [hsum] at hstep
    exact hstep

/-! ## Regression examples -/

example : StrictInterl (X ^ 2 : ℝ[X])
    ((1 : ℝ[X]) * X ^ 2 + (0 : ℝ[X]) * X ^ 2) := by
  have hrr : (X ^ 2 : ℝ[X]) ≠ 0 ∧ (X ^ 2 : ℝ[X]).Splits :=
    ⟨by simp, Splits.X_pow 2⟩
  have hsum : (1 : ℝ[X]) * X ^ 2 + (0 : ℝ[X]) * X ^ 2 =
      (1 : ℝ[X]) * X ^ 2 + ∑ i ∈ ({0} : Finset Unit),
        (0 : ℝ[X]) * X ^ 2 := by simp
  rw [hsum]
  apply strictInterl_mul_add_sum_mul_of_eval_nonpos (s := ({0} : Finset Unit))
    (b := fun _ : Unit ↦ (0 : ℝ[X])) (g := fun _ : Unit ↦ (X ^ 2 : ℝ[X])) hrr.1 hrr.2
  · intro i hi
    simpa using StrictInterl.refl hrr.1 hrr.2
  · intro i hi
    simpa using hasPosLeadingCoeff_of_monic (monic_X_pow 2)
  · intro i hi r hr
    simp
  · simp [HasPosLeadingCoeff]
  · simp
  · simp

example : StrictInterl (X ^ 2 : ℝ[X])
    ((1 : ℝ[X]) * X ^ 2 + ∑ _i ∈ (∅ : Finset Unit),
      (0 : ℝ[X]) * X ^ 2) := by
  have hrr : (X ^ 2 : ℝ[X]) ≠ 0 ∧ (X ^ 2 : ℝ[X]).Splits :=
    ⟨by simp, Splits.X_pow 2⟩
  apply strictInterl_mul_add_sum_mul_of_eval_nonpos (s := (∅ : Finset Unit))
    (b := fun _ : Unit ↦ (0 : ℝ[X])) (g := fun _ : Unit ↦ (X ^ 2 : ℝ[X])) hrr.1 hrr.2
  · simp
  · simp
  · simp
  · simp [HasPosLeadingCoeff]
  · simp
  · simp

end RealRooted.LiuWang
