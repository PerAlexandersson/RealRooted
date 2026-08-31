import RealRooted.NarayanaTransformation.RootGeometry

/-!
# Narayana transformation basis algebra.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- Basis transforms preserve coefficientwise nonnegativity. -/
theorem HasNonnegCoeffs.basisTransform {P : ℕ → ℝ[X]} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hP : ∀ k, HasNonnegCoeffs (P k)) :
    HasNonnegCoeffs (basisTransform P p) := by
  intro j
  rw [coeff_basisTransform]
  simpa only [Polynomial.sum] using
    Finset.sum_nonneg fun k _ => mul_nonneg (hp k) (hP k j)

/-- Falling factorial `⟨x⟩_k = x (x - 1) ... (x - k + 1)`. -/
def fallingFactorialPolynomial (k : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.range k, (X - C (i : ℝ))

theorem fallingFactorialPolynomial_succ_mul (n : ℕ) :
    fallingFactorialPolynomial (n + 1) =
      (X - C (n : ℝ)) * fallingFactorialPolynomial n := by
  simp [fallingFactorialPolynomial, Finset.prod_range_succ]
  ring

/-- Multiplication by `X` before the Touchard-basis transform becomes the
Touchard differential recurrence after the transform. -/
theorem basisTransform_touchard_X_mul (p : ℝ[X]) :
    basisTransform touchard (X * p) =
      X * basisTransform touchard p + X * (basisTransform touchard p).derivative := by
  exact basisTransform_X_mul_of_succ_derivative touchard X X touchard_succ p

/-- Factor recurrence for the Touchard-basis transform. -/
theorem basisTransform_touchard_mul_X_add_C (r : ℝ) (p : ℝ[X]) :
    basisTransform touchard ((X + C r) * p) =
      (X + C r) * basisTransform touchard p +
        X * (basisTransform touchard p).derivative := by
  exact basisTransform_mul_X_add_C_of_succ_derivative touchard X X touchard_succ r p

/-- The Touchard-basis transform sends a falling factorial back to the
corresponding monomial. -/
theorem basisTransform_touchard_fallingFactorialPolynomial :
    ∀ n : ℕ, basisTransform touchard (fallingFactorialPolynomial n) = X ^ n
  | 0 => by
      rw [show fallingFactorialPolynomial 0 = 1 by simp [fallingFactorialPolynomial]]
      rw [show (1 : ℝ[X]) = C 1 by simp, basisTransform_C]
      simp [touchard]
  | n + 1 => by
      rw [fallingFactorialPolynomial_succ_mul]
      rw [show (X - C (n : ℝ) : ℝ[X]) = X + C (-(n : ℝ)) by
        ext k
        simp [sub_eq_add_neg]]
      rw [basisTransform_touchard_mul_X_add_C,
        basisTransform_touchard_fallingFactorialPolynomial]
      cases n with
      | zero => simp
      | succ n =>
          rw [Polynomial.derivative_X_pow_succ]
          simp only [Nat.cast_add, Nat.cast_one]
          have hC : C (-((n : ℝ) + 1)) = -(C ((n : ℝ) + 1)) := by
            ext k
            simp
          rw [hC]
          ring

/-- The Touchard-basis transform is a left inverse of the falling-factorial
basis transform. -/
theorem basisTransform_touchard_fallingFactorial_leftInverse (p : ℝ[X]) :
    basisTransform touchard (basisTransform fallingFactorialPolynomial p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [basisTransform_add, hp, hq]
  | monomial n a =>
      rw [basisTransform_monomial, Polynomial.C_mul', basisTransform_smul]
      rw [basisTransform_touchard_fallingFactorialPolynomial]
      simp [Polynomial.X_pow_eq_monomial]

private theorem touchardFactorStep_preservesPF {r : ℝ} (hr : 0 ≤ r)
    {f : ℝ[X]} (hf : IsPFPolynomial f) :
    IsPFPolynomial ((X + C r) * f + X * f.derivative) := by
  by_cases hf0 : f = 0
  · simpa [hf0] using IsPFPolynomial.zero
  have hfrr := hf.ne_zero_and_splits hf0
  by_cases hdeg0 : f.natDegree = 0
  · have hfC : f = C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    rw [hfC] at hf ⊢
    simpa using (isPFPolynomial_X_add_C hr).mul hf
  have hdegpos : 1 ≤ f.natDegree := by lia
  have hf_pos : HasPosLeadingCoeff f := hf.hasNonnegCoeffs.pos_leadingCoeff hf0
  have hder_ne : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr hdeg0
  have hder_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
  have hder : Interlaces f.derivative f :=
    interlaces_derivative_of_pos_natDegree hf0 hfrr.2 hf_pos hdegpos
  have hfirst_pos : HasPosLeadingCoeff ((X + C r) * f) :=
    (hasPosLeadingCoeff_X_add_C r).mul hf_pos
  have hfirst_deg : ((X + C r) * f).natDegree = f.natDegree + 1 := by
    rw [Polynomial.natDegree_mul (Polynomial.X_add_C_ne_zero r) hf0,
      Polynomial.natDegree_X_add_C]
    simp [add_comm]
  have hsecond_deg : (X * f.derivative).natDegree = f.natDegree := by
    rw [Polynomial.natDegree_mul X_ne_zero hder_ne, Polynomial.natDegree_X,
      f.natDegree_derivative]
    lia
  have hsum_pos : HasPosLeadingCoeff ((X + C r) * f + X * f.derivative) :=
    hasPosLeadingCoeff_add_of_natDegree_lt_left (by lia) hfirst_pos
  have hsum_deg : ((X + C r) * f + X * f.derivative).natDegree =
      f.natDegree + 1 := by
    rw [natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff]
    · exact hfirst_deg
    · lia
    · exact hfirst_pos
  have hprec : Prec f ((X + C r) * f + X * f.derivative) := by
    apply prec_of_interlaces_evalCoeff_nonpos hder hder_pos hsum_pos
    · rw [hsum_deg]
      lia
    · rw [hsum_deg]
    · intro s hs
      simpa using hf.roots_nonpos s ((mem_roots hf0).mpr hs)
  exact IsPFPolynomial.of_realRooted_nonneg
    (((isPFPolynomial_X_add_C hr).mul hf).hasNonnegCoeffs.add
      hf.derivative.X_mul.hasNonnegCoeffs)
    hprec.2.1.2

private theorem basisTransform_touchard_preservesPF_aux :
    ∀ n (p : ℝ[X]), p.natDegree = n → p ≠ 0 → IsPFPolynomial p →
      IsPFPolynomial (basisTransform touchard p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p hpdeg hp0 hp
      by_cases hn0 : n = 0
      · have hpdeg0 : p.natDegree = 0 := by lia
        have hpC : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hpdeg0
        rw [hpC] at hp ⊢
        simpa [touchard] using hp
      · have hnpos : 0 < p.natDegree := by lia
        rcases hp.exists_X_sub_C_factor_of_pos_natDegree hnpos with
          ⟨u, q, hu, hfactor, hq, hqdeg⟩
        have hq0 : q ≠ 0 := by
          intro hqzero
          apply hp0
          simp [hfactor, hqzero]
        have ihq := ih q.natDegree (by lia) q rfl hq0 hq
        have hfactor' : p = (X + C (-u)) * q := by simpa [sub_eq_add_neg] using hfactor
        rw [hfactor', basisTransform_touchard_mul_X_add_C]
        exact touchardFactorStep_preservesPF (neg_nonneg.mpr hu) ihq

private theorem basisTransform_touchard_preservesPF {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform touchard p) := by
  by_cases hp0 : p = 0
  · simpa [hp0] using IsPFPolynomial.zero
  exact basisTransform_touchard_preservesPF_aux p.natDegree p rfl hp0 hp

/-- The Touchard basis transform preserves PF polynomials. -/
theorem touchardTransformPreservesPF {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform touchard p) :=
  basisTransform_touchard_preservesPF hp

/-- The falling-factorial basis transform is the identity on degree-one
polynomials. -/
theorem basisTransform_fallingFactorial_eq_self_of_natDegree_eq_one {p : ℝ[X]}
    (hpdeg : p.natDegree = 1) :
    basisTransform fallingFactorialPolynomial p = p := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hpdeg.le]
  rw [basisTransform_add]
  rw [Polynomial.C_mul', basisTransform_smul]
  rw [show (X : ℝ[X]) = X ^ 1 by simp, basisTransform_X_pow]
  simp [fallingFactorialPolynomial, Polynomial.C_mul']

/-- Degree-two expansion of the falling-factorial basis transform. -/
theorem basisTransform_fallingFactorial_eq_quadratic_of_natDegree_eq_two {p : ℝ[X]}
    (hpdeg : p.natDegree = 2) :
    basisTransform fallingFactorialPolynomial p =
      C (p.coeff 2) * X ^ 2 + C (p.coeff 1 - p.coeff 2) * X + C (p.coeff 0) := by
  have hpform : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
    Polynomial.eq_quadratic_of_degree_le_two (p := p)
      (Polynomial.degree_le_of_natDegree_le (by rw [hpdeg]))
  have hBX : basisTransform fallingFactorialPolynomial (X : ℝ[X]) = X := by
    rw [show (X : ℝ[X]) = X ^ 1 by simp, basisTransform_X_pow]
    simp [fallingFactorialPolynomial]
  conv_lhs => rw [hpform]
  simp only [basisTransform_add, Polynomial.C_mul', basisTransform_smul, hBX, basisTransform_C]
  simp only [basisTransform_X_pow, fallingFactorialPolynomial, map_natCast, range_zero,
    prod_empty]
  norm_num [Finset.prod_range_succ]
  repeat rw [Polynomial.smul_eq_C_mul]
  rw [map_sub]
  ring_nf

/-- Generalized rising factorial `(x|μ)_k = x (x + μ) ... (x + (k-1) μ)`. -/
def risingFactorialPolynomial (μ : ℝ) (k : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.range k, (X + C ((i : ℝ) * μ))

/-- Append the final factor to a generalized rising factorial. -/
theorem risingFactorialPolynomial_succ_mul (μ : ℝ) (n : ℕ) :
    risingFactorialPolynomial μ (n + 1) =
      risingFactorialPolynomial μ n * (X + C ((n : ℝ) * μ)) := by
  simp [risingFactorialPolynomial, Finset.prod_range_succ]

/-- A generalized rising factorial is `X` times the preceding factorial
translated by `μ`. -/
theorem risingFactorialPolynomial_succ_shift (μ : ℝ) (n : ℕ) :
    risingFactorialPolynomial μ (n + 1) =
      X * (risingFactorialPolynomial μ n).comp (X + C μ) := by
  induction n with
  | zero =>
      simp [risingFactorialPolynomial]
  | succ n ih =>
      rw [risingFactorialPolynomial_succ_mul]
      nth_rewrite 1 [ih]
      rw [risingFactorialPolynomial_succ_mul]
      simp only [mul_comp, X_comp, add_comp, C_comp]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

/-- Multiplication by `X` before the rising-factorial basis transform becomes
multiplication by `X` followed by translation after the transform. -/
theorem basisTransform_risingFactorial_X_mul (μ : ℝ) (p : ℝ[X]) :
    basisTransform (risingFactorialPolynomial μ) (X * p) =
      X * (basisTransform (risingFactorialPolynomial μ) p).comp (X + C μ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [mul_add, basisTransform_add, hp, hq, add_comp]
  | monomial n a =>
      rw [Polynomial.X_mul_monomial]
      simp only [basisTransform_monomial]
      rw [risingFactorialPolynomial_succ_shift]
      simp only [mul_comp, C_comp]
      ring

/-- Su--Yang--Zhang's induction recurrence for the generalized
rising-factorial basis transform. -/
theorem basisTransform_risingFactorial_mul_X_add_C (μ r : ℝ) (p : ℝ[X]) :
    basisTransform (risingFactorialPolynomial μ) ((X + C r) * p) =
      X * (basisTransform (risingFactorialPolynomial μ) p).comp (X + C μ) +
        C r * basisTransform (risingFactorialPolynomial μ) p := by
  rw [add_mul, basisTransform_add, basisTransform_risingFactorial_X_mul]
  rw [Polynomial.C_mul', basisTransform_smul]

private theorem listInterlaces_map_sub_tail_of_pairwise_add_le
    (μ : ℝ) (hμ : 0 ≤ μ) :
    ∀ {r : ℝ} {rs : List ℝ},
      (r :: rs).Pairwise (fun x y => x + μ ≤ y) →
        ListInterlaces (rs.map fun x => x - μ) (r :: rs)
  | _, [], _ => by simp [ListInterlaces]
  | r, s :: ss, hpair => by
      rw [List.pairwise_cons] at hpair
      simp only [List.map_cons, ListInterlaces]
      refine ⟨by linarith [hpair.1 s (by simp)], by linarith, ?_⟩
      exact listInterlaces_map_sub_tail_of_pairwise_add_le μ hμ hpair.2

private theorem listAlternates_map_sub_of_pairwise_add_le
    (μ : ℝ) (hμ : 0 ≤ μ) :
    ∀ {rs : List ℝ}, rs.Pairwise (fun x y => x + μ ≤ y) →
      ListAlternates (rs.map fun x => x - μ) rs
  | [], _ => by simp [ListAlternates]
  | r :: rs, hpair => by
      simp only [List.map_cons, ListAlternates]
      exact ⟨by linarith, listInterlaces_map_sub_tail_of_pairwise_add_le μ hμ hpair⟩

private theorem listInterlaces_roots_sort_of_interlaces {g f : ℝ[X]}
    (h : Interlaces g f) :
    ListInterlaces (g.roots.sort (· ≤ ·)) (f.roots.sort (· ≤ ·)) := by
  rcases h with ⟨_, _, _, rs, ss, hrs, hss, hrs_eq, hss_eq, hint⟩
  have hss_unique : ss = g.roots.sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise' hss (Multiset.pairwise_sort ..)
    exact Multiset.coe_eq_coe.mp (hss_eq.trans (Multiset.sort_eq ..).symm)
  have hrs_unique : rs = f.roots.sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise' hrs (Multiset.pairwise_sort ..)
    exact Multiset.coe_eq_coe.mp (hrs_eq.trans (Multiset.sort_eq ..).symm)
  simpa [hss_unique, hrs_unique] using hint

private theorem pairwise_add_le_of_two_listInterlaces (μ : ℝ) :
    ∀ {ps qs : List ℝ},
      qs.Pairwise (· ≤ ·) →
      ListInterlaces ps qs →
      ListInterlaces (ps.map fun x => x - μ) qs →
      qs.Pairwise (fun x y => x + μ ≤ y)
  | [], [], _, _, _ => by simp
  | [], [_], _, _, _ => by simp
  | [], _ :: _ :: _, _, h, _ => by simp [ListInterlaces] at h
  | _ :: _, [], _, h, _ => by simp [ListInterlaces] at h
  | _ :: _, [_], _, h, _ => by simp [ListInterlaces] at h
  | p :: ps, q₁ :: q₂ :: qs, hsorted, hleft, hshift => by
      simp only [ListInterlaces] at hleft
      simp only [List.map_cons, ListInterlaces] at hshift
      rw [List.pairwise_cons]
      refine ⟨?_, pairwise_add_le_of_two_listInterlaces μ
        (List.pairwise_cons.mp hsorted).2 hleft.2.2 hshift.2.2⟩
      intro q hq
      have hq₂q : q₂ ≤ q := by
        rcases List.mem_cons.mp hq with rfl | hq
        · exact le_rfl
        · exact List.rel_of_pairwise_cons (List.pairwise_cons.mp hsorted).2 hq
      linarith [hleft.2.1, hshift.1]

/-- Two interlacings against a polynomial and its translate recover the root
spacing invariant after a degree-increasing step. -/
private theorem prec_comp_X_add_C_of_two_interlacings
    {μ : ℝ} (hμ : 0 ≤ μ) {p q : ℝ[X]}
    (hpq : Prec p q) (hshiftq : Prec (p.comp (X + C μ)) q)
    (hdeg : p.natDegree + 1 = q.natDegree) :
    Prec (q.comp (X + C μ)) q := by
  let ps := p.roots.sort (· ≤ ·)
  let qs := q.roots.sort (· ≤ ·)
  have hpq_int : ListInterlaces ps qs :=
    listInterlaces_roots_sort_of_interlaces (hpq.toInterlaces hdeg)
  have hshiftdeg : (p.comp (X + C μ)).natDegree + 1 = q.natDegree := by
    simpa [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C] using hdeg
  have hshift_int :
      ListInterlaces ((p.comp (X + C μ)).roots.sort (· ≤ ·)) qs :=
    listInterlaces_roots_sort_of_interlaces (hshiftq.toInterlaces hshiftdeg)
  have hshift_roots :
      (p.comp (X + C μ)).roots.sort (· ≤ ·) = ps.map (fun x => x - μ) := by
    apply List.Perm.eq_of_pairwise' (r := fun x y : ℝ => x ≤ y)
    · exact Multiset.pairwise_sort ..
    · exact pairwise_map_sub_const (Multiset.pairwise_sort ..) μ
    · apply Multiset.coe_eq_coe.mp
      calc
        (↑((p.comp (X + C μ)).roots.sort (· ≤ ·)) : Multiset ℝ) =
            (p.comp (X + C μ)).roots := Multiset.sort_eq ..
        _ = p.roots.map (fun x => x - μ) := roots_comp_X_add_C μ
        _ = (↑ps : Multiset ℝ).map (fun x => x - μ) := by
          rw [show (↑ps : Multiset ℝ) = p.roots by exact Multiset.sort_eq ..]
        _ = (↑(ps.map fun x => x - μ) : Multiset ℝ) := rfl
  rw [hshift_roots] at hshift_int
  have hqs_sorted : qs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hqs_gap : qs.Pairwise (fun x y => x + μ ≤ y) :=
    pairwise_add_le_of_two_listInterlaces μ hqs_sorted hpq_int hshift_int
  have hqrr := hpq.2.1
  refine ⟨isRealRooted_comp_X_add_C hqrr.1 hqrr.2 μ, hqrr,
    qs.map (fun x => x - μ), qs, ?_, hqs_sorted, ?_, Multiset.sort_eq ..,
      Or.inr ⟨by simp, listAlternates_map_sub_of_pairwise_add_le μ hμ hqs_gap⟩⟩
  · grind
  · calc
      (↑(qs.map fun x => x - μ) : Multiset ℝ) =
          (↑qs : Multiset ℝ).map (fun x => x - μ) := rfl
      _ = q.roots.map (fun x => x - μ) := by rw [show (↑qs : Multiset ℝ) = q.roots by
        exact Multiset.sort_eq ..]
      _ = (q.comp (X + C μ)).roots := (roots_comp_X_add_C μ).symm

/-- The Su--Yang--Zhang recurrence preserves both the PF property and the
translate-proper-position invariant encoding `μ`-separated roots. -/
theorem risingFactorialStep_pf_shiftPrec
    {μ r : ℝ} (hμ : 0 ≤ μ) (hr : 0 ≤ r) {f : ℝ[X]}
    (hf : IsPFPolynomial f) (hshift : Prec (f.comp (X + C μ)) f) :
    let g := X * f.comp (X + C μ) + C r * f
    IsPFPolynomial g ∧ Prec (g.comp (X + C μ)) g := by
  dsimp
  let fμ := f.comp (X + C μ)
  have hfrr := hshift.2.1
  have hf_pos : HasPosLeadingCoeff f := hf.hasNonnegCoeffs.pos_leadingCoeff hfrr.1
  have hfμrr : fμ ≠ 0 ∧ fμ.Splits :=
    isRealRooted_comp_X_add_C hfrr.1 hfrr.2 μ
  have hfμnn : HasNonnegCoeffs fμ :=
    hasNonnegCoeffs_comp_X_add_C_of_roots_le hf_pos hfrr.2 fun s hs => by
      linarith [hf.roots_nonpos s hs]
  have hfμ : IsPFPolynomial fμ :=
    IsPFPolynomial.of_realRooted_nonneg hfμnn hfμrr.2
  have hf_Xfμ : Prec f (X * fμ) := by
    simpa [fμ] using
      prec_mul_X_of_prec_of_nonneg hshift hfμ.hasNonnegCoeffs hf.hasNonnegCoeffs
  have hfμ_Xfμ : Prec fμ (X * fμ) :=
    prec_mul_X_of_prec_of_nonneg (prec_refl hfμrr.1 hfμrr.2)
      hfμ.hasNonnegCoeffs hfμ.hasNonnegCoeffs
  have hXfμnn : HasNonnegCoeffs (X * fμ) := hfμ.X_mul.hasNonnegCoeffs
  have hrf_nn : HasNonnegCoeffs (C r * f) :=
    nonnegCoeffs_C_mul hr hf.hasNonnegCoeffs
  have hf_g0 : Prec0 f (X * fμ + C r * f) :=
    prec0_add_right_of_common_left_of_nonneg hf_Xfμ.toPrec0
      (prec0_C_mul_right_of_nonneg hf.prec0_self hr) hXfμnn hrf_nn
  have hfμ_g0 : Prec0 fμ (X * fμ + C r * f) :=
    prec0_add_right_of_common_left_of_nonneg hfμ_Xfμ.toPrec0
      (prec0_C_mul_right_of_nonneg hshift.toPrec0 hr) hXfμnn hrf_nn
  have hg0 : X * fμ + C r * f ≠ 0 := by
    intro hg
    have hcoeff := congrArg
      (fun p : ℝ[X] => p.coeff (X * fμ).natDegree) hg
    have hXpos : HasPosLeadingCoeff (X * fμ) :=
      (hfμ.hasNonnegCoeffs.pos_leadingCoeff hfμrr.1).X_mul
    have hXcoeff : 0 < (X * fμ).coeff (X * fμ).natDegree := by
      change 0 < (X * fμ).coeff (X * fμ).natDegree at hXpos
      exact hXpos
    have hrf_coeff := hrf_nn (X * fμ).natDegree
    simp only [coeff_add, coeff_zero] at hcoeff
    linarith
  have hfg : Prec f (X * fμ + C r * f) :=
    hf_g0.toPrec_of_ne hfrr.1 hg0
  have hfμg : Prec fμ (X * fμ + C r * f) :=
    hfμ_g0.toPrec_of_ne hfμrr.1 hg0
  have hfμdeg : fμ.natDegree = f.natDegree := by simp [fμ, Polynomial.natDegree_comp]
  have hXfμdeg : (X * fμ).natDegree = f.natDegree + 1 := by
    rw [Polynomial.natDegree_mul X_ne_zero hfμrr.1, Polynomial.natDegree_X, hfμdeg]
    simp [add_comm]
  have hrfdeg : (C r * f).natDegree ≤ f.natDegree := Polynomial.natDegree_C_mul_le r f
  have hgdeg : (X * fμ + C r * f).natDegree = f.natDegree + 1 := by
    rw [natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff]
    · exact hXfμdeg
    · rw [hXfμdeg]
      lia
    · exact (hfμ.hasNonnegCoeffs.pos_leadingCoeff hfμrr.1).X_mul
  have hgpf : IsPFPolynomial (X * fμ + C r * f) :=
    IsPFPolynomial.of_realRooted_nonneg (hXfμnn.add hrf_nn) hfg.2.1.2
  exact ⟨hgpf, prec_comp_X_add_C_of_two_interlacings hμ hfg hfμg (by lia)⟩

/-- The generalized rising-factorial basis transform is the identity on
degree-one polynomials. -/
theorem basisTransform_risingFactorial_eq_self_of_natDegree_eq_one {μ : ℝ} {p : ℝ[X]}
    (hpdeg : p.natDegree = 1) :
    basisTransform (risingFactorialPolynomial μ) p = p := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hpdeg.le]
  rw [basisTransform_add]
  rw [Polynomial.C_mul', basisTransform_smul]
  rw [show (X : ℝ[X]) = X ^ 1 by simp, basisTransform_X_pow]
  simp [risingFactorialPolynomial, Polynomial.C_mul']

/-- Degree-two expansion of the generalized rising-factorial basis transform. -/
theorem basisTransform_risingFactorial_eq_quadratic_of_natDegree_eq_two
    {μ : ℝ} {p : ℝ[X]} (hpdeg : p.natDegree = 2) :
    basisTransform (risingFactorialPolynomial μ) p =
      C (p.coeff 2) * X ^ 2 + C (p.coeff 1 + μ * p.coeff 2) * X + C (p.coeff 0) := by
  have hpform : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
    Polynomial.eq_quadratic_of_degree_le_two (p := p)
      (Polynomial.degree_le_of_natDegree_le (by rw [hpdeg]))
  have hBX : basisTransform (risingFactorialPolynomial μ) (X : ℝ[X]) = X := by
    rw [show (X : ℝ[X]) = X ^ 1 by simp, basisTransform_X_pow]
    simp [risingFactorialPolynomial]
  conv_lhs => rw [hpform]
  simp only [basisTransform_add, Polynomial.C_mul', basisTransform_smul, hBX, basisTransform_C]
  simp only [basisTransform_X_pow, risingFactorialPolynomial, map_mul, map_natCast, range_zero,
    prod_empty]
  norm_num [Finset.prod_range_succ]
  repeat rw [Polynomial.smul_eq_C_mul]
  rw [map_add, map_mul]
  ring_nf


end RealRooted
