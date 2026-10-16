module

public import RealRooted.BorceaBranden.Applications.PoissonStarGeneral
public import RealRooted.Mathlib.Algebra.Polynomial.Degree.Operations
public import RealRooted.MaWang.CriticalSign

/-!
# Directed proper-position transport for the univariate Poisson product

This file supplies the exact degree, leading-coefficient, next-coefficient, and root-sum
formulas which orient the image of a proper-position pair under multiplication by an admissible
Poisson factor (issue #1494): directed `StrictInterl` transport, the strict Ma–Wang affine step,
and the positive affine recurrence (PF rows, simple negative roots, consecutive interlacing).
-/

@[expose] public noncomputable section

open Polynomial
open scoped BigOperators

namespace RealRooted.Poisson

private def starCTerm (c : ℝ) (f g : ℝ[X]) (j : ℕ) : ℝ[X] :=
  C (c ^ j / (j.factorial : ℝ)) * X ^ j *
    (derivative^[j]) f * (derivative^[j]) g

private theorem natDegree_starCTerm_le_sub {c : ℝ} {f g : ℝ[X]} {j : ℕ}
    (hj : j ≤ f.natDegree) :
    (starCTerm c f g j).natDegree ≤ f.natDegree + g.natDegree - j := by
  by_cases hjg : j ≤ g.natDegree
  · unfold starCTerm
    have hX : (X ^ j : ℝ[X]).natDegree ≤ j := natDegree_X_pow_le j
    have hf := natDegree_iterate_derivative f j
    have hg := natDegree_iterate_derivative g j
    have hCX : (C (c ^ j / (j.factorial : ℝ)) * X ^ j).natDegree ≤ j := by
      refine natDegree_mul_le.trans ?_
      have hC : (C (c ^ j / (j.factorial : ℝ)) : ℝ[X]).natDegree ≤ 0 := by
        simp
      lia
    have hCXf :
        (C (c ^ j / (j.factorial : ℝ)) * X ^ j *
          (derivative^[j]) f).natDegree ≤ f.natDegree := by
      refine natDegree_mul_le.trans ?_
      lia
    refine natDegree_mul_le.trans ?_
    lia
  · have hzero : (derivative^[j]) g = 0 := by
      apply iterate_derivative_eq_zero
      lia
    rw [starCTerm, hzero, mul_zero]
    exact Nat.zero_le _

private theorem starC_eq_sum_starCTerm (c : ℝ) (f g : ℝ[X]) :
    starC c f g = ∑ j ∈ Finset.range (f.natDegree + 1), starCTerm c f g j :=
  rfl

/-- The coefficient in the sum of the input degrees is the product of the two leading
coefficients. -/
theorem coeff_starC_natDegree_add (c : ℝ) (f g : ℝ[X]) :
    (starC c f g).coeff (f.natDegree + g.natDegree) =
      f.leadingCoeff * g.leadingCoeff := by
  rw [starC_eq_sum_starCTerm, finsetSum_coeff, Finset.sum_range_succ']
  have htail :
      ∑ j ∈ Finset.range f.natDegree,
          (starCTerm c f g (j + 1)).coeff (f.natDegree + g.natDegree) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    apply coeff_eq_zero_of_natDegree_lt
    have hjf : j + 1 ≤ f.natDegree := by
      exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
    exact (natDegree_starCTerm_le_sub hjf).trans_lt (by lia)
  rw [htail, zero_add]
  simp only [starCTerm, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    map_one, Function.iterate_zero_apply, one_mul]
  exact coeff_mul_add_eq_of_natDegree_le le_rfl le_rfl

/-- The Poisson product of two nonzero polynomials has degree equal to the sum of their
degrees. -/
theorem natDegree_starC {c : ℝ} {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    (starC c f g).natDegree = f.natDegree + g.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [starC_eq_sum_starCTerm]
    apply natDegree_sum_le_of_forall_le
    intro j hj
    simp only [Finset.mem_range] at hj
    exact (natDegree_starCTerm_le_sub (Nat.le_of_lt_succ hj)).trans (Nat.sub_le _ _)
  · rw [coeff_starC_natDegree_add]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hf) (leadingCoeff_ne_zero.mpr hg)

/-- The leading coefficient of a nonzero Poisson product is the product of the input leading
coefficients. -/
theorem leadingCoeff_starC {c : ℝ} {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    (starC c f g).leadingCoeff = f.leadingCoeff * g.leadingCoeff := by
  rw [leadingCoeff, natDegree_starC hf hg, coeff_starC_natDegree_add]

private theorem nextCoeff_mul_of_ne_zero {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).nextCoeff =
      f.nextCoeff * g.leadingCoeff + f.leadingCoeff * g.nextCoeff := by
  by_cases hfd : f.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hfd, nextCoeff_C_mul]
    simp
  by_cases hgd : g.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hgd, nextCoeff_mul_C]
    simp
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hfd
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hgd
  rw [nextCoeff, natDegree_mul hf hg, hd, he]
  rw [show (d + 1 + (e + 1) - 1) = d + e + 1 by lia,
    coeff_mul_add_add_one_eq_of_natDegree_le (by rw [hd]) (by rw [he]),
    leadingCoeff, leadingCoeff, hd, he]
  rw [nextCoeff, nextCoeff, hd, he]
  simp only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
  have hsumne : d.succ + e.succ ≠ 0 := by lia
  simp only [hsumne, ite_false]
  ring

private theorem coeff_starCTerm_one_pred (c : ℝ) (f g : ℝ[X]) :
    (starCTerm c f g 1).coeff (f.natDegree + g.natDegree - 1) =
      c * f.natDegree * g.natDegree * f.leadingCoeff * g.leadingCoeff := by
  by_cases hfd : f.natDegree = 0
  · have hder : f.derivative = 0 := derivative_eq_zero.mpr hfd
    simp [starCTerm, hfd, hder]
  by_cases hgd : g.natDegree = 0
  · have hder : g.derivative = 0 := derivative_eq_zero.mpr hgd
    simp [starCTerm, hgd, hder]
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hfd
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hgd
  unfold starCTerm
  norm_num only [pow_one, Nat.factorial_one, Nat.cast_one, div_one,
    Function.iterate_one]
  have hCX : (C c * X : ℝ[X]).natDegree ≤ 1 := natDegree_mul_le.trans (by simp)
  have hfder : f.derivative.natDegree ≤ d := by
    simpa only [hd, Nat.succ_sub_one] using natDegree_derivative_le f
  have hgder : g.derivative.natDegree ≤ e := by
    simpa only [he, Nat.succ_sub_one] using natDegree_derivative_le g
  have hleft : (C c * X * f.derivative).natDegree ≤ 1 + d :=
    natDegree_mul_le.trans (add_le_add hCX hfder)
  rw [hd, he, show (d + 1 + (e + 1) - 1) = (1 + d) + e by lia,
    coeff_mul_add_eq_of_natDegree_le hleft hgder,
    coeff_mul_add_eq_of_natDegree_le hCX hfder, coeff_C_mul, coeff_X,
    coeff_derivative, coeff_derivative, leadingCoeff, leadingCoeff, hd, he]
  push_cast
  ring

/-- The coefficient one below the top degree of a nonzero Poisson product has the explicit
Vieta form used to compare its root sum. -/
theorem nextCoeff_starC {c : ℝ} {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    (starC c f g).nextCoeff =
      f.nextCoeff * g.leadingCoeff + f.leadingCoeff * g.nextCoeff +
        c * f.natDegree * g.natDegree * f.leadingCoeff * g.leadingCoeff := by
  by_cases hfd : f.natDegree = 0
  · rw [starC, hfd]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, map_one,
      Function.iterate_zero_apply, one_mul]
    rw [nextCoeff_mul_of_ne_zero hf hg]
    simp
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hfd
  rw [nextCoeff, natDegree_starC hf hg]
  simp only [show f.natDegree + g.natDegree ≠ 0 by lia, ite_false]
  rw [starC_eq_sum_starCTerm, finsetSum_coeff, hd,
    Finset.sum_range_succ', Finset.sum_range_succ']
  have htail :
      ∑ j ∈ Finset.range d,
          (starCTerm c f g (j + 1 + 1)).coeff
            (d.succ + g.natDegree - 1) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    apply coeff_eq_zero_of_natDegree_lt
    have hjf : j + 1 + 1 ≤ f.natDegree := by
      rw [hd]
      exact Nat.succ_le_succ (Nat.succ_le_iff.mpr (Finset.mem_range.mp hj))
    exact (natDegree_starCTerm_le_sub hjf).trans_lt (by lia)
  rw [htail, zero_add]
  have hone := coeff_starCTerm_one_pred c f g
  rw [hd] at hone
  rw [hone]
  have hprod :
      (starCTerm c f g 0).coeff (d.succ + g.natDegree - 1) =
        f.nextCoeff * g.leadingCoeff + f.leadingCoeff * g.nextCoeff := by
    simp only [starCTerm, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      map_one, Function.iterate_zero_apply, one_mul]
    rw [← nextCoeff_mul_of_ne_zero hf hg, nextCoeff, natDegree_mul hf hg]
    rw [hd]
    have hne : d.succ + g.natDegree ≠ 0 := by lia
    simp only [hne, ite_false]
  rw [hprod]
  ring

/-- A Poisson product of two nonzero polynomials is nonzero. -/
theorem starC_ne_zero {c : ℝ} {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    starC c f g ≠ 0 := by
  apply leadingCoeff_ne_zero.mp
  rw [leadingCoeff_starC hf hg]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hf) (leadingCoeff_ne_zero.mpr hg)

/-- The roots of a split nonzero Poisson product have the common additive shift
`-c * deg(f) * deg(g)` relative to the sums of the input roots. -/
theorem roots_sum_starC {c : ℝ} {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfs : f.Splits) (hgs : g.Splits) (hout : (starC c f g).Splits) :
    (starC c f g).roots.sum =
      f.roots.sum + g.roots.sum - c * f.natDegree * g.natDegree := by
  have hf_lc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  have hg_lc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg
  have hout_lc : (starC c f g).leadingCoeff ≠ 0 := by
    rw [leadingCoeff_starC hf hg]
    exact mul_ne_zero hf_lc hg_lc
  rw [hout.sum_roots_eq_neg_nextCoeff_div_leadingCoeff hout_lc,
    nextCoeff_starC hf hg, leadingCoeff_starC hf hg,
    hfs.sum_roots_eq_neg_nextCoeff_div_leadingCoeff hf_lc,
    hgs.sum_roots_eq_neg_nextCoeff_div_leadingCoeff hg_lc]
  field_simp
  ring

/-- Left Poisson multiplication by an admissible nonzero factor preserves the directed
`StrictInterl` relation.  Exact degrees orient successor-degree pairs; the common root-sum
shift orients equal-degree pairs. -/
theorem IsAdmissible.strictInterl_starC {c : ℝ} {f : ℝ[X]}
    (hf : IsAdmissible c f) {g h : ℝ[X]} (hgh : StrictInterl g h) :
    StrictInterl (starC c f g) (starC c f h) := by
  have hg0 : g ≠ 0 := hgh.1.1
  have hh0 : h ≠ 0 := hgh.2.1.1
  have hgs : g.Splits := hgh.1.2
  have hhs : h.Splits := hgh.2.1.2
  have hfg0 : starC c f g ≠ 0 := starC_ne_zero hf.1 hg0
  have hfh0 : starC c f h ≠ 0 := starC_ne_zero hf.1 hh0
  have hfgs : (starC c f g).Splits := by
    rcases hf.preservesRealRootedOrZero g ⟨hg0, hgs⟩ with hzero | hsplits
    · exact (hfg0 hzero).elim
    · exact hsplits
  have hfhs : (starC c f h).Splits := by
    rcases hf.preservesRealRootedOrZero h ⟨hh0, hhs⟩ with hzero | hsplits
    · exact (hfh0 hzero).elim
    · exact hsplits
  have hall : AllComboRealRooted (starC c f g) (starC c f h) :=
    preservesAllComboPairs_of_preservesRealRootedOrZero
      hf.preservesRealRootedOrZero (allComboRealRooted_of_strictInterl hgh)
  rcases hgh.natDegree_eq_or_eq_succ with hsame | hsucc
  · have hdeg : (starC c f g).natDegree = (starC c f h).natDegree := by
      rw [natDegree_starC hf.1 hg0, natDegree_starC hf.1 hh0, hsame]
    have hor := strictInterl_of_allComboRealRooted hfg0 hfgs hfh0 hfhs hall
      (Or.inr hdeg)
    rcases hor with hforward | hreverse
    · exact hforward
    · apply hreverse.of_reverse_of_roots_sum_le hdeg
      rw [roots_sum_starC hf.1 hg0 hf.2.1 hgs hfgs,
        roots_sum_starC hf.1 hh0 hf.2.1 hhs hfhs, hsame]
      linarith [hgh.roots_sum_le_of_sameDegree hsame.symm]
  · have hdeg : (starC c f h).natDegree = (starC c f g).natDegree + 1 := by
      rw [natDegree_starC hf.1 hh0, natDegree_starC hf.1 hg0, hsucc]
      lia
    apply StrictInterl.forward_of_orientation_of_succDegree hdeg
    exact strictInterl_of_allComboRealRooted hfg0 hfgs hfh0 hfhs hall
      (Or.inl hdeg.symm)

/-- A positive affine Poisson step preserves the PF cone and positive constant term, and the
strict Ma--Wang sign at every old root gives simple strictly negative new roots with no common
root. -/
theorem strictInterl_package_starC_affine_of_pos {c a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) {f : ℝ[X]}
    (hf : IsPFPolynomial f) (hsimple : HasSimpleRoots f) (hf_const : 0 < f.coeff 0) :
    let F := starC c (C a + C b * X) f
    IsPFPolynomial F ∧ 0 < F.coeff 0 ∧ StrictInterl f F ∧
      HasSimpleRoots F ∧ (∀ r, f.IsRoot r → ¬ F.IsRoot r) ∧
        ∀ r, F.IsRoot r → r < 0 := by
  dsimp only
  let L : ℝ[X] := C a + C b * X
  have hf0 : f ≠ 0 := hsimple.ne_zero
  have hL_eq : L = C b * X + C a := by
    dsimp [L]
    ring
  have hLdeg : L.natDegree = 1 := by
    rw [hL_eq, natDegree_linear hb.ne']
  have hLlc : L.leadingCoeff = b := by
    rw [hL_eq, leadingCoeff_linear hb.ne']
  have hL0 : L ≠ 0 := by
    intro hzero
    have := congrArg natDegree hzero
    simp only [hLdeg, natDegree_zero] at this
    lia
  have hLpf : IsPFPolynomial L := by
    have hscaled := (isPFPolynomial_X_add_C (div_nonneg ha.le hb.le)).const_mul hb
    rw [hL_eq]
    convert hscaled using 1
    rw [mul_add, ← C_mul]
    field_simp [hb.ne']
  have hFpf : IsPFPolynomial (starC c L f) :=
    RealRooted.Poisson.IsPFPolynomial.preservesPF hc.le hLpf f hf
  have hF0 : starC c L f ≠ 0 := starC_ne_zero hL0 hf0
  have hF_const : 0 < (starC c L f).coeff 0 := by
    rw [hL_eq, add_comm, starC_linear_factor_left, coeff_zero_eq_eval_zero]
    simp only [eval_add, eval_mul, eval_C, eval_X, zero_mul, mul_zero, add_zero]
    rw [← coeff_zero_eq_eval_zero]
    exact mul_pos ha hf_const
  have hf_pos : HasPosLeadingCoeff f :=
    hf.hasNonnegCoeffs.pos_leadingCoeff hf0
  have hF_pos : HasPosLeadingCoeff (starC c L f) := by
    rw [HasPosLeadingCoeff, leadingCoeff_starC hL0 hf0, hLlc]
    exact mul_pos hb hf_pos
  have hFdeg : (starC c L f).natDegree = f.natDegree + 1 := by
    rw [natDegree_starC hL0 hf0, hLdeg, add_comm]
  have hsign : ∀ r, f.IsRoot r →
      (starC c L f).eval r * f.derivative.eval r < 0 := by
    intro r hr
    have hr_mem : r ∈ f.roots := (mem_roots hf0).mpr hr
    have hr_nonpos : r ≤ 0 := hf.roots_nonpos r hr_mem
    have hr_ne : r ≠ 0 := by
      intro hr0
      subst r
      rw [IsRoot.def, ← coeff_zero_eq_eval_zero] at hr
      linarith
    have hr_neg : r < 0 := lt_of_le_of_ne hr_nonpos hr_ne
    have hder_ne : f.derivative.eval r ≠ 0 := hsimple.eval_derivative_ne_zero hr
    rw [hL_eq, add_comm, starC_linear_factor_left]
    rw [IsRoot.def] at hr
    simp only [eval_add, eval_mul, eval_C, eval_X, hr, mul_zero, zero_add]
    calc
      c * b * r * f.derivative.eval r * f.derivative.eval r =
          (c * b * r) * (f.derivative.eval r) ^ 2 := by ring
      _ < 0 := mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (mul_pos hc hb) hr_neg)
        (sq_pos_of_ne_zero hder_ne)
  obtain ⟨hstrict, _, _, _, hFsimple, hno⟩ :=
    strictInterl_package_of_eval_mul_derivative_neg_succ
      (hf.ne_zero_and_splits hf0).2 hf_pos hF_pos rfl hFdeg hsign
  refine ⟨hFpf, hF_const, hstrict, hFsimple, hno, ?_⟩
  intro r hr
  have hr_mem : r ∈ (starC c L f).roots := (mem_roots hF0).mpr hr
  have hr_nonpos : r ≤ 0 := hFpf.roots_nonpos r hr_mem
  have hr_ne : r ≠ 0 := by
    intro hr0
    subst r
    rw [IsRoot.def, ← coeff_zero_eq_eval_zero] at hr
    linarith
  exact lt_of_le_of_ne hr_nonpos hr_ne

/-- In a positive affine Poisson recurrence from `1`, every row is PF with simple strictly
negative roots, and each consecutive pair is in directed proper position with no common root. -/
theorem poisson_affine_recurrence_strict
    {c : ℝ} {a b : ℕ → ℝ} {P : ℕ → ℝ[X]}
    (hc : 0 < c) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (hP0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C (a n) + C (b n) * X) * P n +
        C (c * b n) * X * (P n).derivative) (n : ℕ) :
    IsPFPolynomial (P n) ∧ HasSimpleRoots (P n) ∧
      (∀ r, (P n).IsRoot r → r < 0) ∧ StrictInterl (P n) (P (n + 1)) ∧
        ∀ r, (P n).IsRoot r → ¬ (P (n + 1)).IsRoot r := by
  have hrows : ∀ m, IsPFPolynomial (P m) ∧ 0 < (P m).coeff 0 ∧
      HasSimpleRoots (P m) ∧ ∀ r, (P m).IsRoot r → r < 0 := by
    intro m
    induction m with
    | zero =>
        rw [hP0]
        refine ⟨IsPFPolynomial.one, by simp, ?_, by simp⟩
        simp [HasSimpleRoots]
    | succ m ih =>
        have hstar : P (m + 1) = starC c (C (a m) + C (b m) * X) (P m) := by
          rw [hrec m, starC_linear_factor_left]
        have hstep := strictInterl_package_starC_affine_of_pos hc (ha m) (hb m)
          ih.1 ih.2.2.1 ih.2.1
        rw [← hstar] at hstep
        exact ⟨hstep.1, hstep.2.1, hstep.2.2.2.1, hstep.2.2.2.2.2⟩
  have hn := hrows n
  have hstar : P (n + 1) = starC c (C (a n) + C (b n) * X) (P n) := by
    rw [hrec n, starC_linear_factor_left]
  have hstep := strictInterl_package_starC_affine_of_pos hc (ha n) (hb n)
    hn.1 hn.2.2.1 hn.2.1
  rw [← hstar] at hstep
  exact ⟨hn.1, hn.2.2.1, hn.2.2.2, hstep.2.2.1, hstep.2.2.2.2.1⟩

end RealRooted.Poisson
