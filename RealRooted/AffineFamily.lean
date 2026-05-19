/-
# Affine-family criterion for interlacing

Has2x2InterlacingProperty definition, affine-family criterion
(Brändén Lemma 7.8.4), bridge from combo results to Prec.
The remaining live theorem here is `prec_of_affine_family_nonneg`.
-/
import RealRooted.ProductFamily
import RealRooted.AffineDerivative
import RealRooted.PosCombo
import RealRooted.ObreschkoffConverse
import RealRooted.FolkloreLemma
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

open Polynomial

noncomputable section

namespace RealRooted

/-! ## 2×2 interlacing condition

The key condition for matrices preserving interlacing sequences:
for a 2×2 submatrix `[[a, b], [c, d]]`, the weighted sums interlace. -/

/-- The 2×2 interlacing condition: for all `λ, μ > 0`,
    `(λX + C μ) * b + d ⊳ (λX + C μ) * a + c`.

    This matches the 2×2 affine condition in Brändén's Theorem 7.8.5
    (Handbook of Enumerative Combinatorics, §7.8, book p. 460 / PDF p. 485). -/
def Has2x2InterlacingProperty (a b c d : ℝ[X]) : Prop :=
  ∀ (s t : ℝ), 0 < s → 0 < t →
    Prec ((C s * X + C t) * b + d) ((C s * X + C t) * a + c)

/-- Weak zero-aware 2×2 interlacing condition. This is the same affine
2×2 test as `Has2x2InterlacingProperty`, but with `Prec0`, so affine test
members that vanish identically are accepted. -/
def Has2x2InterlacingProperty0 (a b c d : ℝ[X]) : Prop :=
  ∀ (s t : ℝ), 0 < s → 0 < t →
    Prec0 ((C s * X + C t) * b + d) ((C s * X + C t) * a + c)

lemma Has2x2InterlacingProperty.toHas2x2InterlacingProperty0
    {a b c d : ℝ[X]} (h : Has2x2InterlacingProperty a b c d) :
    Has2x2InterlacingProperty0 a b c d := by
  intro s t hs ht
  exact (h s t hs ht).toPrec0

lemma ne_zero_of_self_2x2 (p : ℝ[X])
    (hdiag : Has2x2InterlacingProperty p p p p) :
    p ≠ 0 := by
  have hself :
      Prec
        (((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p)
        (((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p) :=
    hdiag 1 1 zero_lt_one zero_lt_one
  intro hp0
  exact hself.1.1 (by simp [hp0])

lemma isRealRooted_of_self_2x2 (p : ℝ[X])
    (hdiag : Has2x2InterlacingProperty p p p p) :
    IsRealRooted p := by
  have hself :
      Prec
        (((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p)
        (((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p) :=
    hdiag 1 1 zero_lt_one zero_lt_one
  have hcombo_rr :
      IsRealRooted (((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p) :=
    hself.1
  have hp0 : p ≠ 0 := ne_zero_of_self_2x2 p hdiag
  have hdiv : p ∣ (((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p) := by
    refine ⟨(C (1 : ℝ) * X + C (1 : ℝ)) + 1, ?_⟩
    calc
      ((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p
          = p * (C (1 : ℝ) * X + C (1 : ℝ)) + p := by
              simp [mul_comm]
      _ = p * ((C (1 : ℝ) * X + C (1 : ℝ)) + 1) := by
            simp [mul_add, add_comm]
  exact isRealRooted_of_dvd hcombo_rr hp0 hdiv

lemma prec_self_mul_X_of_nonneg {f : ℝ[X]}
    (hf : IsRealRooted f) (hfnn : HasNonnegCoeffs f) :
    Prec f (X * f) := by
  have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf.1
  have hXf : IsRealRooted (X * f) := isRealRooted_X_mul hf
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf hfnn
  have hXf_nonpos : ∀ r ∈ (X * f).roots, r ≤ 0 := by
    intro r hr
    rw [roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X] at hr
    rcases Multiset.mem_add.mp hr with hr0 | hrf
    · have hr0' : r = 0 := by
        simpa [Multiset.mem_singleton] using hr0
      linarith
    · exact hf_nonpos r hrf
  have hXf_pos : HasPosLeadingCoeff (X * f) := by
    unfold HasPosLeadingCoeff at hf_pos ⊢
    rw [leadingCoeff_mul, leadingCoeff_X]
    simpa using hf_pos
  have hdeg : f.natDegree + 1 = (X * f).natDegree := by
    rw [natDegree_X_mul hf.1]
  have hself : Prec (X * f) (X * f) := prec_refl hXf
  exact
    (prec_iff_prec_mul_X_of_roots_nonpos
      (f := f) (g := X * f) hf hXf hf_pos hXf_pos hf_nonpos hXf_nonpos hdeg).mpr hself

lemma prec_to_prec_mul_X_of_nonneg {f g : ℝ[X]}
    (h : Prec f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec g (X * f) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf hfnn
  have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hg hgnn
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hg.2]
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩
  · have hdeg : f.natDegree + 1 = g.natDegree := by
      omega
    exact
      (prec_iff_prec_mul_X_of_roots_nonpos
        (f := f) (g := g)
        hf hg (hfnn.pos_leadingCoeff hf.1) (hgnn.pos_leadingCoeff hg.1)
        hf_nonpos hg_nonpos hdeg).mp
        ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, Or.inl ⟨hlen, by assumption⟩⟩
  · have hdeg : f.natDegree = g.natDegree := by
      omega
    exact
      prec_sameDegree_to_prec_mul_X_of_roots_nonpos
        ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, Or.inr ⟨hlen, by assumption⟩⟩
        hdeg hf_nonpos hg_nonpos

private lemma hasPosLeadingCoeff_of_X_sub_C_mul_local {q : ℝ[X]} {r : ℝ}
    (h : HasPosLeadingCoeff ((X - C r) * q)) :
    HasPosLeadingCoeff q := by
  unfold HasPosLeadingCoeff at h ⊢
  simpa [Polynomial.leadingCoeff_mul, leadingCoeff_X_sub_C] using h

private lemma hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
    {p q : ℝ[X]}
    (hp : IsRealRooted p) (hpnn : HasNonnegCoeffs p)
    (hq : IsRealRooted q) (hq_pos : HasPosLeadingCoeff q)
    (hqp : q ∣ p) :
    HasNonnegCoeffs q := by
  refine (hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hq).mpr ?_
  refine ⟨hq_pos, ?_⟩
  intro r hr
  have hrq : q.IsRoot r := (mem_roots hq.1).mp hr
  have hrp : p.IsRoot r := IsRoot.of_dvd hqp hrq
  exact roots_nonpos_of_nonneg_coeffs hp hpnn r ((mem_roots hp.1).mpr hrp)

private lemma affine_family_common_root_reduction_data
    {f g : ℝ[X]} {r : ℝ}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    ∃ qf qg,
      f = (X - C r) * qf ∧
      g = (X - C r) * qg ∧
      HasNonnegCoeffs qf ∧
      HasNonnegCoeffs qg ∧
      qf ≠ 0 ∧
      qg ≠ 0 ∧
      HasPosLeadingCoeff qf ∧
      HasPosLeadingCoeff qg ∧
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * qf) + qg) := by
  obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
  obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
  have hqf_ne : qf ≠ 0 := by
    exact right_ne_zero_of_mul (by simpa [hqf] using hf.1)
  have hqg_ne : qg ≠ 0 := by
    exact right_ne_zero_of_mul (by simpa [hqg] using hg.1)
  have hqf_rr : IsRealRooted qf := by
    exact isRealRooted_of_dvd hf hqf_ne ⟨X - C r, by simpa [mul_comm] using hqf⟩
  have hqg_rr : IsRealRooted qg := by
    exact isRealRooted_of_dvd hg hqg_ne ⟨X - C r, by simpa [mul_comm] using hqg⟩
  have hqf_pos : HasPosLeadingCoeff qf := by
    exact hasPosLeadingCoeff_of_X_sub_C_mul_local (by simpa [hqf] using hf_pos)
  have hqg_pos : HasPosLeadingCoeff qg := by
    exact hasPosLeadingCoeff_of_X_sub_C_mul_local (by simpa [hqg] using hg_pos)
  have hqf_nonneg : HasNonnegCoeffs qf := by
    exact
      hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
        hf hfnn hqf_rr hqf_pos ⟨X - C r, by simpa [mul_comm] using hqf⟩
  have hqg_nonneg : HasNonnegCoeffs qg := by
    exact
      hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
        hg hgnn hqg_rr hqg_pos ⟨X - C r, by simpa [mul_comm] using hqg⟩
  refine ⟨qf, qg, hqf, hqg, hqf_nonneg, hqg_nonneg, hqf_ne, hqg_ne, hqf_pos, hqg_pos, ?_⟩
  intro s t hs ht
  have hbase : IsRealRooted (((C s * X + C t) * ((X - C r) * qf)) + ((X - C r) * qg)) := by
    simpa [hqf, hqg] using haff hs ht
  have hEq :
      (((C s * X + C t) * ((X - C r) * qf)) + ((X - C r) * qg))
        = (X - C r) * (((C s * X + C t) * qf) + qg) := by
    calc
      (((C s * X + C t) * ((X - C r) * qf)) + ((X - C r) * qg))
          = (X - C r) * ((C s * X + C t) * qf) + (X - C r) * qg := by
              ac_rfl
      _ = (X - C r) * (((C s * X + C t) * qf) + qg) := by
            rw [mul_add]
  have hsum_ne : (((C s * X + C t) * qf) + qg) ≠ 0 := by
    intro hsum0
    have : (((C s * X + C t) * ((X - C r) * qf)) + ((X - C r) * qg)) = 0 := by
      rw [hEq, hsum0]
      simp
    exact hbase.1 this
  exact
    isRealRooted_of_dvd hbase hsum_ne
      ⟨X - C r, by
        calc
          (((C s * X + C t) * ((X - C r) * qf)) + ((X - C r) * qg))
              = (X - C r) * (((C s * X + C t) * qf) + qg) := hEq
          _ = (((C s * X + C t) * qf) + qg) * (X - C r) := by
                rw [mul_comm]
      ⟩

private lemma prec_right_pair_of_common_root_factor
    {f g qf qg : ℝ[X]} {r : ℝ}
    (hf : f = (X - C r) * qf)
    (hg : g = (X - C r) * qg)
    (hprec_q : Prec qg (X * qf)) :
    Prec g (X * f) := by
  have hprec_mul : Prec ((X - C r) * qg) ((X - C r) * (X * qf)) :=
    prec_mul_common_factor (isRealRooted_X_sub_C r) hprec_q
  have hXf_eq : X * f = (X - C r) * (X * qf) := by
    calc
      X * f = X * ((X - C r) * qf) := by simp [hf]
      _ = (X - C r) * (X * qf) := by ring
  simpa [hg, hXf_eq] using hprec_mul

private lemma prec_of_prec_mul_X_of_sameDegree_of_roots_nonpos_local {f g : ℝ[X]}
    (h : Prec g (X * f))
    (hdeg : f.natDegree = g.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0) :
    Prec f g := by
  rcases h with ⟨hg, hXf, ss_g, rs_Xf, hss_g, hrs_Xf, hss_g_eq, hrs_Xf_eq, hshape⟩
  have hf : IsRealRooted f := isRealRooted_of_X_mul hXf
  set rs_f := f.roots.sort (· ≤ ·)
  have hrs_f_eq : (↑rs_f : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_f : rs_f.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_f_nonpos : ∀ r ∈ rs_f, r ≤ 0 := by
    intro r hr
    exact hf_nonpos r (by rw [← hrs_f_eq]; exact Multiset.mem_coe.mpr hr)
  have hrs_f0 : (rs_f ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    exact ⟨hrs_f, List.pairwise_singleton _ _, fun a ha b hb => by
      simp only [List.mem_singleton] at hb
      rw [hb]
      exact hrs_f_nonpos a ha⟩
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X]
  have hrs_Xf_is : rs_Xf = rs_f ++ [(0 : ℝ)] := by
    have hmultiset_eq : (↑rs_Xf : Multiset ℝ) = ↑(rs_f ++ [(0 : ℝ)]) := by
      rw [hrs_Xf_eq, hXf_roots, ← hrs_f_eq, ← Multiset.coe_add]
      simp [add_comm]
    exact List.Perm.eq_of_pairwise' hrs_Xf hrs_f0 (Multiset.coe_eq_coe.mp hmultiset_eq)
  have hlen_fg : rs_f.length = ss_g.length := by
    rw [← Multiset.coe_card, hrs_f_eq, hf.2, ← Multiset.coe_card, hss_g_eq, hg.2, hdeg]
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, _⟩
  · rw [hrs_Xf_is] at hint hlen
    have hlen' : ss_g.length + 1 = (rs_f ++ [(0 : ℝ)]).length := by
      simp [hlen_fg]
    have hrs_f0_nonpos : ∀ r ∈ rs_f ++ [(0 : ℝ)], r ≤ 0 := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hrs_f_nonpos r hr
      · simp at hr
        simp [hr]
    have halt0 :
        ListAlternates (rs_f ++ [(0 : ℝ)]) (ss_g ++ [(0 : ℝ)]) :=
      listAlternates_append_zero ss_g (rs_f ++ [(0 : ℝ)]) hlen' hint hrs_f0_nonpos
    have halt : ListAlternates rs_f ss_g :=
      listAlternates_of_append_zero_both rs_f ss_g hlen_fg halt0
    exact ⟨hf, hg, rs_f, ss_g, hrs_f, hss_g, hrs_f_eq, hss_g_eq, Or.inr ⟨hlen_fg, halt⟩⟩
  · have hss_len : ss_g.length = g.natDegree := by
      rw [← Multiset.coe_card, hss_g_eq, hg.2]
    have hrs_len : rs_Xf.length = (X * f).natDegree := by
      rw [← Multiset.coe_card, hrs_Xf_eq, hXf.2]
    rw [natDegree_X_mul hf.1] at hrs_len
    omega

/-- Backward Wagner wrapper used in the affine-family endgame:
once the right-hand pair `(g, X * f)` is oriented, nonnegative coefficients
recover the original conclusion `Prec f g`. -/
lemma prec_of_prec_mul_X_of_nonneg {f g : ℝ[X]}
    (h : Prec g (X * f)) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec f g := by
  have hprec := h
  have hg : IsRealRooted g := h.1
  have hXf : IsRealRooted (X * f) := h.2.1
  have hf : IsRealRooted f := isRealRooted_of_X_mul hXf
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf hfnn
  rcases hprec with ⟨_, _, ss, rs, _hss, _hrs, hss_eq, hrs_eq, hshape⟩
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩
  · have hss_len : ss.length = g.natDegree := by
      rw [← Multiset.coe_card, hss_eq, hg.2]
    have hrs_len : rs.length = (X * f).natDegree := by
      rw [← Multiset.coe_card, hrs_eq, hXf.2]
    have hdeg : f.natDegree = g.natDegree := by
      rw [natDegree_X_mul hf.1] at hrs_len
      omega
    exact
      prec_of_prec_mul_X_of_sameDegree_of_roots_nonpos_local
        h hdeg hf_nonpos
  · have hss_len : ss.length = g.natDegree := by
      rw [← Multiset.coe_card, hss_eq, hg.2]
    have hrs_len : rs.length = (X * f).natDegree := by
      rw [← Multiset.coe_card, hrs_eq, hXf.2]
    have hdeg : f.natDegree + 1 = g.natDegree := by
      rw [natDegree_X_mul hf.1] at hrs_len
      omega
    exact
      (prec_iff_prec_mul_X_of_roots_nonpos
        (f := f) (g := g)
        hf hg (hfnn.pos_leadingCoeff hf.1) (hgnn.pos_leadingCoeff hg.1)
        hf_nonpos (roots_nonpos_of_nonneg_coeffs hg hgnn) hdeg).mpr h

theorem isRealRooted_affine_combo_of_prec_nonneg {f g : ℝ[X]}
    (h : Prec f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    IsRealRooted (((C s * X + C t) * f) + g) := by
  have hf : IsRealRooted f := h.1
  have hg : IsRealRooted g := h.2.1
  have hXf : IsRealRooted (X * f) := isRealRooted_X_mul hf
  have hg_Xf : Prec g (X * f) := prec_to_prec_mul_X_of_nonneg h hfnn hgnn
  have hf_Xf : Prec f (X * f) := prec_self_mul_X_of_nonneg hf hfnn
  have hsXf : Prec (C s * (X * f)) (X * f) := prec_C_mul_self hXf hs.ne'
  have htf : Prec (C t * f) (X * f) := prec_C_mul_left hf_Xf ht.ne'
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg.1
  have hXf_pos : HasPosLeadingCoeff (X * f) := by
    unfold HasPosLeadingCoeff at ⊢
    rw [leadingCoeff_mul, leadingCoeff_X]
    simpa using hfnn.pos_leadingCoeff hf.1
  have hsXf_pos : HasPosLeadingCoeff (C s * (X * f)) :=
    hasPosLeadingCoeff_C_mul hs hXf_pos
  have htf_pos : HasPosLeadingCoeff (C t * f) :=
    hasPosLeadingCoeff_C_mul ht (hfnn.pos_leadingCoeff hf.1)
  have hmid : Prec (g + C s * (X * f)) (X * f) := by
    exact prec_add_of_prec_right_of_posLeadingCoeff hg_Xf hsXf hg_pos hsXf_pos
  have hmid_nonneg : HasNonnegCoeffs (g + C s * (X * f)) := by
    refine hgnn.add ?_
    exact (nonnegCoeffs_C_mul hs.le (hasNonnegCoeffs_X.mul hfnn))
  have hmid_pos : HasPosLeadingCoeff (g + C s * (X * f)) :=
    hmid_nonneg.pos_leadingCoeff hmid.1.1
  have hsum : Prec (C t * f + (g + C s * (X * f))) (X * f) := by
    exact prec_add_of_prec_right_of_posLeadingCoeff htf hmid htf_pos hmid_pos
  simpa [left_distrib, right_distrib, mul_assoc, add_assoc, add_left_comm, add_comm] using hsum.1

theorem posComboRealRooted_of_affine_family {f g : ℝ[X]}
    (h :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    {t : ℝ} (ht : 0 < t) :
    PosComboRealRooted (C t * f + g) (X * f) := by
  intro lam μ hlam hμ
  have hbase :
      IsRealRooted (((C (μ / lam) * X + C t) * f) + g) :=
    h (by positivity) ht
  have hscaled :
      IsRealRooted (C lam * ((((C (μ / lam) * X + C t) * f) + g))) :=
    isRealRooted_C_mul hbase hlam.ne'
  have hEq :
      C lam * ((((C (μ / lam) * X + C t) * f) + g))
        = C lam * (C t * f + g) + C μ * (X * f) := by
    have hmain : C lam * ((C (μ / lam) * X) * f) = C μ * (X * f) := by
      calc
        C lam * ((C (μ / lam) * X) * f)
            = C lam * (C (μ / lam) * (X * f)) := by rw [mul_assoc]
        _ = (C lam * C (μ / lam)) * (X * f) := by rw [mul_assoc]
        _ = C (lam * (μ / lam)) * (X * f) := by rw [C_mul]
        _ = C μ * (X * f) := by
              congr 1
              field_simp [hlam.ne']
    calc
      C lam * ((((C (μ / lam) * X + C t) * f) + g))
          = C lam * (((C (μ / lam) * X + C t) * f) ) + C lam * g := by
              rw [mul_add]
      _ = (C lam * ((C (μ / lam) * X) * f) + C lam * (C t * f)) + C lam * g := by
            rw [add_mul, mul_add]
      _ = (C μ * (X * f) + C lam * (C t * f)) + C lam * g := by
            rw [hmain]
      _ = C lam * (C t * f + g) + C μ * (X * f) := by
            rw [mul_add]
            ac_rfl
  simpa [hEq] using hscaled

private lemma affine_family_pair_data {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    {t : ℝ} (ht : 0 < t) :
    PosComboRealRooted (C t * f + g) (X * f) ∧
    HasNonnegCoeffs (C t * f + g) ∧
    HasNonnegCoeffs (X * f) ∧
    (C t * f + g) ≠ 0 ∧
    X * f ≠ 0 ∧
    HasPosLeadingCoeff (C t * f + g) ∧
    HasPosLeadingCoeff (X * f) := by
  have hCt_nonneg : HasNonnegCoeffs (C t * f) := nonnegCoeffs_C_mul ht.le hfnn
  have hsum_nonneg : HasNonnegCoeffs (C t * f + g) := hCt_nonneg.add hgnn
  have hXf_nonneg : HasNonnegCoeffs (X * f) := hasNonnegCoeffs_X.mul hfnn
  have hCt_ne : C t * f ≠ 0 := by
    exact mul_ne_zero (C_ne_zero.mpr ht.ne') hf0
  have hsum_ne : C t * f + g ≠ 0 := by
    exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hCt_nonneg hgnn hg0
  have hXf_ne : X * f ≠ 0 := mul_ne_zero X_ne_zero hf0
  refine
    ⟨posComboRealRooted_of_affine_family (f := f) (g := g) haff (t := t) ht,
      hsum_nonneg, hXf_nonneg, hsum_ne, hXf_ne,
      hsum_nonneg.pos_leadingCoeff hsum_ne, hXf_nonneg.pos_leadingCoeff hXf_ne⟩

/-- Closure lemma for a lower-degree right family:
if every `g + μ f` with `μ > 0` is real-rooted and `deg f < deg g`, then `g`
is already real-rooted. This is the clean boundary-`μ → 0` step that the
succ-degree affine-family branch needs. -/
private theorem isRealRooted_of_add_C_mul_right_family_of_natDegree_lt
    {f g : ℝ[X]}
    (hfamily : ∀ {μ : ℝ}, 0 < μ → IsRealRooted (g + C μ * f))
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : f.natDegree < g.natDegree) :
    IsRealRooted g := by
  let f₀ : ℝ[X] := C f.leadingCoeff⁻¹ * f
  let g₀ : ℝ[X] := C g.leadingCoeff⁻¹ * g
  have hf_lc_ne : f.leadingCoeff ≠ 0 := ne_of_gt hf_pos
  have hg_lc_ne : g.leadingCoeff ≠ 0 := ne_of_gt hg_pos
  have hf₀_monic : f₀.Monic := by
    unfold f₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    field_simp [hf_lc_ne]
  have hg₀_monic : g₀.Monic := by
    unfold g₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    field_simp [hg_lc_ne]
  have hf₀_pos : HasPosLeadingCoeff f₀ := by
    simp [HasPosLeadingCoeff, hf₀_monic.leadingCoeff]
  have hg₀_pos : HasPosLeadingCoeff g₀ := by
    simp [HasPosLeadingCoeff, hg₀_monic.leadingCoeff]
  have hdeg₀ : f₀.natDegree < g₀.natDegree := by
    simp [f₀, g₀, natDegree_C_mul, hf_lc_ne, hg_lc_ne, hdeg]
  have hfamily₀ : ∀ {μ : ℝ}, 0 < μ → IsRealRooted (g₀ + C μ * f₀) := by
    intro μ hμ
    have hμ' : 0 < μ * g.leadingCoeff / f.leadingCoeff := by
      exact div_pos (mul_pos hμ hg_pos) hf_pos
    have hbase : IsRealRooted (g + C (μ * g.leadingCoeff / f.leadingCoeff) * f) :=
      hfamily hμ'
    have hscaled :
        IsRealRooted
          (C g.leadingCoeff⁻¹ *
            (g + C (μ * g.leadingCoeff / f.leadingCoeff) * f)) :=
      isRealRooted_C_mul hbase (inv_ne_zero hg_lc_ne)
    have hEq :
        C g.leadingCoeff⁻¹ *
            (g + C (μ * g.leadingCoeff / f.leadingCoeff) * f) =
          g₀ + C μ * f₀ := by
      ext n
      simp [g₀, f₀]
      field_simp [hf_lc_ne, hg_lc_ne]
    simpa [hEq] using hscaled
  have hg₀_rr : IsRealRooted g₀ := by
    have hroots_real :
        ∀ z ∈ (g₀.map (algebraMap ℝ ℂ)).roots, z ∈ (algebraMap ℝ ℂ).range := by
      intro z hz_mem
      have hmap_ne : g₀.map (algebraMap ℝ ℂ) ≠ 0 := by
        exact
          (Polynomial.map_ne_zero_iff (RingHom.injective (algebraMap ℝ ℂ))).2
            hg₀_monic.ne_zero
      have hz_root : (g₀.map (algebraMap ℝ ℂ)).IsRoot z :=
        (Polynomial.mem_roots hmap_ne).1 hz_mem
      have hz_aeval : g₀.aeval z = 0 := by
        have hz_eval_map : (g₀.map (algebraMap ℝ ℂ)).eval z = 0 := by
          simpa [Polynomial.IsRoot.def] using hz_root
        simpa [eval₂_at_apply] using hz_eval_map
      by_contra hz_range
      have hz_im_ne : z.im ≠ 0 := by
        intro hz_im
        apply hz_range
        refine ⟨z.re, ?_⟩
        apply Complex.ext <;> simp [hz_im]
      let δ : ℝ := |z.im| / 2
      let R : ℝ := max ‖z‖ 1
      have hδ_pos : 0 < δ := by
        unfold δ
        exact half_pos (abs_pos.mpr hz_im_ne)
      have hR_pos : 0 < R := by
        unfold R
        exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      have hg₀_deg_pos : 0 < g₀.natDegree := lt_of_le_of_lt (Nat.zero_le _) hdeg₀
      have hdeg_nat_ne : g₀.natDegree ≠ 0 := Nat.ne_of_gt hg₀_deg_pos
      let u : ℝ := δ / (2 * R)
      let ε : ℝ := (u ^ g₀.natDegree) / (g₀.natDegree + 1)
      have hu_nonneg : 0 ≤ u := by
        unfold u
        positivity
      have hu_pos : 0 < u := by
        unfold u
        positivity
      have hε_pos : 0 < ε := by
        unfold ε
        positivity
      let μ : ℝ := ε / (coeffSumRange f₀ + 1)
      have hcoeff_nonneg : 0 ≤ coeffSumRange f₀ := by
        unfold coeffSumRange
        exact Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hμ_pos : 0 < μ := by
        unfold μ
        positivity
      have hμ_bound : μ * coeffSumRange f₀ < ε := by
        unfold μ
        have hden_pos : 0 < coeffSumRange f₀ + 1 := by
          linarith
        have hfrac_lt_one : coeffSumRange f₀ / (coeffSumRange f₀ + 1) < 1 := by
          rw [div_lt_iff₀ hden_pos]
          linarith
        have hcalc :
            (ε / (coeffSumRange f₀ + 1)) * coeffSumRange f₀ =
              ε * (coeffSumRange f₀ / (coeffSumRange f₀ + 1)) := by
          field_simp [show (coeffSumRange f₀ + 1 : ℝ) ≠ 0 by linarith]
        rw [hcalc]
        calc
          ε * (coeffSumRange f₀ / (coeffSumRange f₀ + 1)) < ε * 1 :=
            mul_lt_mul_of_pos_left hfrac_lt_one hε_pos
          _ = ε := by ring
      have hcoeff :
          ∀ i : ℕ, ‖(g₀ + C μ * f₀).coeff i - g₀.coeff i‖ < ε := by
        intro i
        exact lt_of_le_of_lt
          (norm_coeff_sub_add_C_mul_le g₀ f₀ (μ := μ) (M := coeffSumRange f₀)
            hμ_pos.le (fun j => coeff_norm_le_coeffSumRange f₀ j) i)
          hμ_bound
      have hμf_deg_lt : (C μ * f₀).natDegree < g₀.natDegree := by
        simpa [natDegree_C_mul hμ_pos.ne'] using hdeg₀
      have hsum_deg : (g₀ + C μ * f₀).natDegree = g₀.natDegree := by
        exact natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hμf_deg_lt hg₀_pos
      have hsum_monic : (g₀ + C μ * f₀).Monic := by
        unfold Polynomial.Monic Polynomial.leadingCoeff
        rw [hsum_deg, coeff_add, coeff_eq_zero_of_natDegree_lt hμf_deg_lt,
          hg₀_monic.coeff_natDegree, add_zero]
      obtain ⟨w, hw_root, hw_dist⟩ :=
        exists_complex_aroot_near_of_isRealRooted_of_monic_of_coeff_close
          (f := g₀) (g := g₀ + C μ * f₀) (z := z) (ε := ε)
          hε_pos hz_aeval hg₀_monic hsum_monic hsum_deg hcoeff (hfamily₀ hμ_pos)
      have hw_im_zero : w.im = 0 := by
        exact RealRooted.im_eq_zero_of_mem_aroots_of_isRealRooted (hfamily₀ hμ_pos) hw_root
      have hbound_eq :
          ((g₀.natDegree + 1) * ε) ^ ((g₀.natDegree : ℝ)⁻¹) * R = δ / 2 := by
        have hmul :
            ((g₀.natDegree + 1 : ℝ) * ε) = u ^ g₀.natDegree := by
          unfold ε
          field_simp
        calc
          ((g₀.natDegree + 1) * ε) ^ ((g₀.natDegree : ℝ)⁻¹) * R
              = (u ^ g₀.natDegree) ^ ((g₀.natDegree : ℝ)⁻¹) * R := by rw [hmul]
          _ = u * R := by rw [Real.pow_rpow_inv_natCast hu_nonneg hdeg_nat_ne]
          _ = δ / 2 := by
                unfold u
                field_simp [hR_pos.ne']
      have hdist_lt_delta : ‖z - w‖ < δ := by
        calc
          ‖z - w‖ <
              ((g₀.natDegree + 1) * ε) ^ ((g₀.natDegree : ℝ)⁻¹) * max ‖z‖ 1 := hw_dist
          _ = ((g₀.natDegree + 1) * ε) ^ ((g₀.natDegree : ℝ)⁻¹) * R := by simp [R]
          _ = δ / 2 := hbound_eq
          _ < δ := by linarith [hδ_pos]
      have him_le : |z.im| ≤ ‖z - w‖ := by
        simpa [Complex.sub_im, hw_im_zero] using (Complex.abs_im_le_norm (z - w))
      have him_lt : |z.im| < δ := lt_of_le_of_lt him_le hdist_lt_delta
      have hhalf : |z.im| < |z.im| / 2 := by
        simpa [δ] using him_lt
      nlinarith [abs_pos.mpr hz_im_ne, hhalf]
    have hsplit : g₀.Splits := by
      exact
        Polynomial.Splits.of_splits_map (i := algebraMap ℝ ℂ)
          (IsAlgClosed.splits _) hroots_real
    exact ⟨hg₀_monic.ne_zero, (Polynomial.splits_iff_card_roots).1 hsplit⟩
  have hg_scale : C g.leadingCoeff * g₀ = g := by
    unfold g₀
    ext n
    simp [hg_lc_ne]
  have hg_rr_scaled : IsRealRooted (C g.leadingCoeff * g₀) :=
    isRealRooted_C_mul hg₀_rr hg_lc_ne
  simpa [hg_scale] using hg_rr_scaled

/-- Boundary closure for a right family `g + μ f` when the perturbation has no
higher degree than the base polynomial. The equal-degree case is exactly the
existing positive-combination continuity theorem; the strict case is the new
lower-degree closure lemma above. -/
private theorem isRealRooted_of_add_C_mul_right_family_of_natDegree_le
    {f g : ℝ[X]}
    (hfamily : ∀ {μ : ℝ}, 0 < μ → IsRealRooted (g + C μ * f))
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : f.natDegree ≤ g.natDegree) :
    IsRealRooted g := by
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact
      isRealRooted_of_add_C_mul_right_family_of_natDegree_lt
        hfamily hf_pos hg_pos hlt
  · have hcombo : PosComboRealRooted g f := by
      rw [PosComboRealRooted.iff_add_right]
      intro μ hμ
      simpa [add_comm] using hfamily hμ
    exact
      PosComboRealRooted.isRealRooted_left_of_sameDegree
        (f := g) (g := f) hcombo hg_pos hf_pos heq

/-- If the affine family has enough right-hand degree to dominate the `X * f`
perturbation, then the boundary member `C t * f + g` is already real-rooted.
This is the first compiled reduction from the two-parameter family to the
one-parameter boundary family. -/
private lemma isRealRooted_add_left_of_affine_family_of_natDegree_succ_le
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hdeg : f.natDegree + 1 ≤ g.natDegree)
    {t : ℝ} (ht : 0 < t) :
    IsRealRooted (C t * f + g) := by
  obtain ⟨_, _, _, _, _, hsum_pos, hXf_pos⟩ :=
    affine_family_pair_data hfnn hgnn hf0 hg0 haff ht
  have hsum_deg : (C t * f + g).natDegree = g.natDegree := by
    have hCt_deg : (C t * f).natDegree = f.natDegree := by
      rw [natDegree_C_mul ht.ne']
    exact
      natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
        (by rw [hCt_deg]; omega)
        (hgnn.pos_leadingCoeff hg0)
  apply isRealRooted_of_add_C_mul_right_family_of_natDegree_le
  · intro s hs
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, left_distrib, right_distrib] using
      haff hs ht
  · exact hXf_pos
  · exact hsum_pos
  · rw [natDegree_mul X_ne_zero hf0, natDegree_X, hsum_deg]
    omega

/-- In the degree-dominating branch `deg g ≥ deg f + 1`, the affine-family
hypothesis already forces `g` to be real-rooted by first passing to the
boundary family `C t * f + g` and then taking `t → 0`. -/
private lemma isRealRooted_right_of_affine_family_of_natDegree_succ_le
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hdeg : f.natDegree + 1 ≤ g.natDegree) :
    IsRealRooted g := by
  apply isRealRooted_of_add_C_mul_right_family_of_natDegree_le
  · intro t ht
    simpa [add_comm] using
      isRealRooted_add_left_of_affine_family_of_natDegree_succ_le
        hf0 hg0 hfnn hgnn haff hdeg ht
  · exact hfnn.pos_leadingCoeff hf0
  · exact hgnn.pos_leadingCoeff hg0
  · omega

private lemma isRealRooted_pair_of_affine_family_succDegree
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hsucc : f.natDegree + 1 = g.natDegree)
    {t : ℝ} (ht : 0 < t) :
    IsRealRooted (C t * f + g) ∧ IsRealRooted f := by
  obtain ⟨hcombo, _, _, _, _, hsum_pos, hXf_pos⟩ :=
    affine_family_pair_data hfnn hgnn hf0 hg0 haff ht
  have hsum_deg : (C t * f + g).natDegree = g.natDegree := by
    have hCt_deg : (C t * f).natDegree = f.natDegree := by
      rw [natDegree_C_mul ht.ne']
    exact
      natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
        (by rw [hCt_deg]; omega)
        (hgnn.pos_leadingCoeff hg0)
  have hXf_deg : (X * f).natDegree = g.natDegree := by
    rw [natDegree_mul X_ne_zero hf0, natDegree_X]
    omega
  have hdeg_same : (X * f).natDegree = (C t * f + g).natDegree := by
    rw [hXf_deg, hsum_deg]
  have hsum_rr :
      IsRealRooted (C t * f + g) :=
    PosComboRealRooted.isRealRooted_left_of_sameDegree
      hcombo hsum_pos hXf_pos hdeg_same
  have hXf_rr :
      IsRealRooted (X * f) :=
    PosComboRealRooted.isRealRooted_right_of_sameDegree
      hcombo hsum_pos hXf_pos hdeg_same
  exact ⟨hsum_rr, isRealRooted_of_X_mul hXf_rr⟩

private lemma isRealRooted_right_of_affine_family_succDegree
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hsucc : f.natDegree + 1 = g.natDegree) :
    IsRealRooted g := by
  exact
    isRealRooted_right_of_affine_family_of_natDegree_succ_le
      hf0 hg0 hfnn hgnn haff (by omega)

/-- Fix `s > 0`. Passing `t → 0` in the affine family shows that the boundary
member `g + s X f` is already real-rooted. This is the natural right-family
companion to `isRealRooted_add_left_of_affine_family_of_natDegree_succ_le`,
but unlike that lemma it does not require any a priori degree comparison: the
`X * f` term always raises the left degree by one, so the boundary family is
automatically at least as large as `f` itself. -/
private lemma isRealRooted_add_X_mul_right_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    {s : ℝ} (hs : 0 < s) :
    IsRealRooted (g + C s * (X * f)) := by
  have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf0
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  have hXf_nonneg : HasNonnegCoeffs (X * f) := hasNonnegCoeffs_X.mul hfnn
  have hXf_ne : X * f ≠ 0 := mul_ne_zero X_ne_zero hf0
  have hCsXf_nonneg : HasNonnegCoeffs (C s * (X * f)) :=
    nonnegCoeffs_C_mul hs.le hXf_nonneg
  have hCsXf_ne : C s * (X * f) ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hs.ne') hXf_ne
  have hbase_nonneg : HasNonnegCoeffs (g + C s * (X * f)) :=
    hgnn.add hCsXf_nonneg
  have hbase_ne : g + C s * (X * f) ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hgnn hCsXf_nonneg hCsXf_ne
  have hXf_pos : HasPosLeadingCoeff (X * f) :=
    hXf_nonneg.pos_leadingCoeff hXf_ne
  have hCsXf_pos : HasPosLeadingCoeff (C s * (X * f)) :=
    hasPosLeadingCoeff_C_mul hs hXf_pos
  have hbase_pos : HasPosLeadingCoeff (g + C s * (X * f)) := by
    rcases lt_trichotomy g.natDegree (X * f).natDegree with hdeg | hdeg | hdeg
    · have hdeg' : g.natDegree < (C s * (X * f)).natDegree := by
        simpa [natDegree_C_mul hs.ne'] using hdeg
      exact hasPosLeadingCoeff_add_of_natDegree_lt_right hdeg' hCsXf_pos
    · have hdeg' : g.natDegree = (C s * (X * f)).natDegree := by
        simpa [natDegree_C_mul hs.ne'] using hdeg
      exact hasPosLeadingCoeff_add_of_same_natDegree hdeg' hg_pos hCsXf_pos
    · have hdeg' : (C s * (X * f)).natDegree < g.natDegree := by
        simpa [natDegree_C_mul hs.ne'] using hdeg
      exact hasPosLeadingCoeff_add_of_natDegree_lt_left hdeg' hg_pos
  have hbase_deg : f.natDegree ≤ (g + C s * (X * f)).natDegree := by
    rcases lt_trichotomy g.natDegree (X * f).natDegree with hdeg | hdeg | hdeg
    · have hsum_deg : (g + C s * (X * f)).natDegree = (C s * (X * f)).natDegree := by
        exact
          natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
            (by simpa [natDegree_C_mul hs.ne'] using hdeg) hCsXf_pos
      rw [hsum_deg, natDegree_C_mul hs.ne', natDegree_mul X_ne_zero hf0, natDegree_X]
      omega
    · have hsum_deg : (g + C s * (X * f)).natDegree = g.natDegree := by
        exact natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
          (by simpa [natDegree_C_mul hs.ne'] using hdeg) hg_pos hCsXf_pos
      rw [hsum_deg]
      have hXf_deg : (X * f).natDegree = f.natDegree + 1 := by
        simpa [Nat.add_comm] using (natDegree_mul X_ne_zero hf0).trans (by simp [natDegree_X])
      rw [hXf_deg] at hdeg
      omega
    · have hsum_deg : (g + C s * (X * f)).natDegree = g.natDegree := by
        exact
          natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff
            (by simpa [natDegree_C_mul hs.ne'] using hdeg) hg_pos
      rw [hsum_deg]
      have hXf_deg : (X * f).natDegree = f.natDegree + 1 := by
        simpa [Nat.add_comm] using (natDegree_mul X_ne_zero hf0).trans (by simp [natDegree_X])
      rw [hXf_deg] at hdeg
      omega
  apply isRealRooted_of_add_C_mul_right_family_of_natDegree_le
  · intro t ht
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, left_distrib, right_distrib] using
      haff hs ht
  · exact hf_pos
  · exact hbase_pos
  · exact hbase_deg

/-- The affine-family hypothesis already implies that the fixed right-hand pair
`(g, X * f)` satisfies the restricted Obreschkoff condition: every strictly
positive combination `g + μ X f` is real-rooted. This is the honest boundary
package that remains after the earlier `t → 0` refactor. -/
private lemma posComboRealRooted_right_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    PosComboRealRooted g (X * f) := by
  refine PosComboRealRooted.of_add_right ?_
  intro s hs
  exact
    isRealRooted_add_X_mul_right_of_affine_family
      hf0 hg0 hfnn hgnn haff hs

/-- Data package for the fixed right-hand pair `(g, X * f)` extracted from the
affine family after taking the boundary `t → 0`. This is the natural target
pair for the eventual Wagner step `Prec g (X * f) → Prec f g`. -/
private lemma affine_family_right_pair_data {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    PosComboRealRooted g (X * f) ∧
    HasNonnegCoeffs g ∧
    HasNonnegCoeffs (X * f) ∧
    g ≠ 0 ∧
    X * f ≠ 0 ∧
    HasPosLeadingCoeff g ∧
    HasPosLeadingCoeff (X * f) := by
  have hXf_nonneg : HasNonnegCoeffs (X * f) := hasNonnegCoeffs_X.mul hfnn
  have hXf_ne : X * f ≠ 0 := mul_ne_zero X_ne_zero hf0
  refine
    ⟨posComboRealRooted_right_of_affine_family hf0 hg0 hfnn hgnn haff,
      hgnn, hXf_nonneg, hg0, hXf_ne,
      hgnn.pos_leadingCoeff hg0, hXf_nonneg.pos_leadingCoeff hXf_ne⟩

/-! ## Degree control for the affine family

Before trying to orient the fixed right-hand pair `(g, X * f)`, it is useful to
rule out the large-gap regime `deg g ≥ deg f + 2`. The affine hypothesis gives
real-rootedness of every boundary member `C t * f + g` with `t > 0`; after
differentiating `deg f` times, this would force a positive constant-vs-degree-`≥ 2`
positive family, which is impossible.  This is the affine analogue of the
degree-closeness reduction already used in `ObreschkoffConverse`. -/

private lemma iterate_derivative_add :
    ∀ (n : ℕ) (p q : ℝ[X]),
      (derivative^[n]) (p + q) = (derivative^[n]) p + (derivative^[n]) q
  | 0, p, q => by simp
  | n + 1, p, q => by
      simp [Function.iterate_succ_apply', derivative_add, iterate_derivative_add]

private lemma iterate_derivative_C_mul (a : ℝ) :
    ∀ (n : ℕ) (p : ℝ[X]),
      (derivative^[n]) (C a * p) = C a * (derivative^[n]) p
  | 0, p => by simp
  | n + 1, p => by
      simp [Function.iterate_succ_apply', iterate_derivative_C_mul]

private lemma hasNonnegCoeffs_iterate_derivative {p : ℝ[X]} :
    ∀ n : ℕ, HasNonnegCoeffs p → HasNonnegCoeffs ((derivative^[n]) p)
  | 0, hp => by simpa
  | n + 1, hp => by
      rw [Function.iterate_succ_apply']
      exact nonnegCoeffs_derivative (hasNonnegCoeffs_iterate_derivative n hp)

private lemma derivative_eq_zero_or_isRealRooted_local {p : ℝ[X]}
    (hp : IsRealRooted p) :
    p.derivative = 0 ∨ IsRealRooted p.derivative := by
  by_cases h0 : p.derivative = 0
  · exact Or.inl h0
  · right
    by_cases hdeg : 2 ≤ p.natDegree
    · exact (derivative_interlaces hp hdeg).2.1
    · have hpdeg_le : p.natDegree ≤ 1 := by omega
      have hpdeg_pos : 1 ≤ p.natDegree := by
        by_contra hpdeg0
        have hdeg0 : p.natDegree = 0 := by omega
        have : p.derivative = 0 := by
          rw [eq_C_of_natDegree_eq_zero hdeg0, derivative_C]
        exact h0 this
      have hpdeg_eq : p.natDegree = 1 := by omega
      have hder_deg : p.derivative.natDegree = 0 := by
        rw [natDegree_derivative_eq hpdeg_pos, hpdeg_eq]
      exact isRealRooted_of_deg_zero h0 hder_deg

private lemma natDegree_iterate_derivative_eq_sub
    {p : ℝ[X]} {k : ℕ} (hp0 : p ≠ 0) (hk : k ≤ p.natDegree) :
    (derivative^[k] p).natDegree = p.natDegree - k := by
  apply le_antisymm (natDegree_iterate_derivative p k)
  apply Polynomial.le_natDegree_of_ne_zero
  have hcoeff :
      (derivative^[k] p).coeff (p.natDegree - k) ≠ 0 := by
    rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, nsmul_eq_mul, coeff_natDegree]
    exact mul_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hk).ne')
      (leadingCoeff_ne_zero.mpr hp0)
  exact hcoeff

/-- Iterated derivatives stay nonzero as long as we do not differentiate past
the degree. This keeps the constant-vs-degree-`≥ 2` contradiction honest. -/
private lemma iterate_derivative_ne_zero_of_le_natDegree
    {p : ℝ[X]} {k : ℕ} (hp0 : p ≠ 0) (hk : k ≤ p.natDegree) :
    (derivative^[k] p) ≠ 0 := by
  intro hk0
  have hcoeff :
      (derivative^[k] p).coeff (p.natDegree - k) ≠ 0 := by
    rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, nsmul_eq_mul, coeff_natDegree]
    exact mul_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hk).ne')
      (leadingCoeff_ne_zero.mpr hp0)
  simp [hk0] at hcoeff

private lemma isRealRooted_iterate_derivative_of_lt_natDegree
    {p : ℝ[X]} (hp : IsRealRooted p) :
    ∀ {n : ℕ}, n < p.natDegree → IsRealRooted ((derivative^[n]) p)
  | 0, _ => by simpa
  | n + 1, hn => by
      rw [Function.iterate_succ_apply']
      have hprev : IsRealRooted ((derivative^[n]) p) :=
        isRealRooted_iterate_derivative_of_lt_natDegree hp (Nat.lt_of_succ_lt hn)
      have hnonzero :
          derivative ((derivative^[n]) p) ≠ 0 := by
        simpa [Function.iterate_succ_apply'] using
          (iterate_derivative_ne_zero_of_le_natDegree
            (p := p) (k := n + 1) hp.1 (Nat.le_of_lt hn))
      exact
        (derivative_eq_zero_or_isRealRooted_local hprev).elim
          (fun h0 => False.elim (hnonzero h0))
          id

private lemma listInterlaces_all_le_getLast_local :
    ∀ {ss rs : List ℝ},
      (hrs_ne : rs ≠ []) →
      rs.Pairwise (· ≤ ·) →
      ListInterlaces ss rs →
      ∀ s ∈ ss, s ≤ rs.getLast hrs_ne
  | [], [], hrs_ne, _, hint, s, hs => by
      cases (hrs_ne rfl)
  | [], [_], _, _, hint, s, hs => by
      simp at hs
  | s :: ss, [r], _, _, hint, _, _ => by
      simp [ListInterlaces] at hint
  | s :: ss, r₁ :: r₂ :: rs, _, hrs_sorted, hint, t, ht => by
      obtain ⟨_, hs_r₂, htail⟩ := hint
      rcases List.mem_cons.mp ht with rfl | ht
      · exact
          le_trans hs_r₂
            (List.Pairwise.rel_getLast hrs_sorted (by simp [List.mem_cons]))
      · exact
          listInterlaces_all_le_getLast_local (rs := r₂ :: rs) (by simp)
            ((List.pairwise_cons.mp hrs_sorted).2) htail t ht

/-- Translation-invariant form of
`listInterlaces_of_listAlternates_append_zero`: if a same-degree alternating
layout ends with one extra rightmost point `uR`, then deleting that endpoint
produces a genuine `ListInterlaces` layout. This local copy is used in the
same-degree rightmost-factor reduction below. -/
private lemma listInterlaces_of_listAlternates_append_right_local
    {ss qs : List ℝ} {uR : ℝ}
    (hlen : qs.length + 1 = ss.length)
    (halt : ListAlternates ss (qs ++ [uR])) :
    ListInterlaces qs ss := by
  have halt0 :
      ListAlternates (ss.map (· - uR)) ((qs.map (· - uR)) ++ [0]) := by
    simpa [List.map_append] using listAlternates_map_sub_const halt uR
  have hlen0 : (qs.map (· - uR)).length + 1 = (ss.map (· - uR)).length := by
    simpa using hlen
  have hint0 :
      ListInterlaces (qs.map (· - uR)) (ss.map (· - uR)) :=
    listInterlaces_of_listAlternates_append_zero
      (qs.map (· - uR)) (ss.map (· - uR)) hlen0 halt0
  have hfun :
      ((fun x : ℝ => x + uR) ∘ fun x => x - uR) = fun x => x := by
    funext x
    change (x - uR) + uR = x
    ring_nf
  simpa [List.map_map, Function.comp, hfun] using
    listInterlaces_map_sub_const hint0 (-uR)

/-- A positive-leading real-rooted polynomial of degree at least `2` is
nonpositive at its rightmost critical point. This is the same local obstruction
used in the Obreschkoff degree-gap proof, now recorded here because the affine
family needs the positive-shift variant below. -/
private lemma exists_rightmost_root_of_isRealRooted
    {p : ℝ[X]} (hp : IsRealRooted p) (hdeg : 1 ≤ p.natDegree) :
    ∃ r, p.IsRoot r ∧ ∀ s ∈ p.roots, s ≤ r := by
  let rs := p.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = p.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_len : rs.length = p.natDegree := by
    rw [show rs = p.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hp.2]
  have hrs_ne : rs ≠ [] := by
    intro hrs_nil
    simp [hrs_nil] at hrs_len
    omega
  refine ⟨rs.getLast hrs_ne, ?_, ?_⟩
  · have hr_mem : rs.getLast hrs_ne ∈ rs := List.getLast_mem hrs_ne
    have : rs.getLast hrs_ne ∈ p.roots := by
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr hr_mem
    exact (mem_roots hp.1).mp this
  · intro s hs
    have hs_mem : s ∈ rs := by
      apply Multiset.mem_coe.mp
      rwa [hrs_eq]
    exact hrs_sorted.rel_getLast hs_mem

/-- In the same-degree `Prec` case, removing a rightmost root of the right-hand
polynomial turns the quotient into an honest differ-by-1 interlacer for the
left-hand polynomial. This is the local `AffineFamily` copy of the root-list
combinatorics that will be needed in the remaining same-degree sign transport
arguments. -/
private lemma interlaces_of_prec_sameDegree_rightmost_factor_local
    {f g q : ℝ[X]} {uR : ℝ}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hright : ∀ r ∈ g.roots, r ≤ uR)
    (hgq : g = (X - C uR) * q) :
    Interlaces q f := by
  obtain ⟨hf, hg, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩ := hfg
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hg.2]
  have hq_ne : q ≠ 0 := by
    exact right_ne_zero_of_mul (by simpa [hgq] using hg.1)
  have hq : IsRealRooted q := by
    apply isRealRooted_of_dvd hg hq_ne
    exact ⟨X - C uR, by simp [hgq, mul_comm]⟩
  have hq_deg_g : q.natDegree + 1 = g.natDegree := by
    rw [hgq, natDegree_mul (X_sub_C_ne_zero uR) hq_ne, natDegree_X_sub_C]
    omega
  have hq_deg : q.natDegree + 1 = f.natDegree := by
    omega
  rcases hshape with ⟨hlen, _hint⟩ | ⟨_hlen, halt⟩
  · exfalso
    omega
  · let qs := q.roots.sort (· ≤ ·)
    have hqs_eq : (↑qs : Multiset ℝ) = q.roots := Multiset.sort_eq ..
    have hqs_sorted : qs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
    have hqs_len : qs.length = q.natDegree := by
      rw [show qs = q.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hq.2]
    have hqs_le_uR : ∀ r ∈ qs, r ≤ uR := by
      intro r hr
      exact hright r (by
        rw [hgq, roots_mul (mul_ne_zero (X_sub_C_ne_zero uR) hq_ne), roots_X_sub_C]
        apply Multiset.mem_add.mpr
        right
        rw [← hqs_eq]
        exact Multiset.mem_coe.mpr hr)
    have hqs_sorted_right : (qs ++ [uR]).Pairwise (· ≤ ·) := by
      rw [List.pairwise_append]
      refine ⟨hqs_sorted, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact hqs_le_uR a ha
    have hrs_eq_right : rs = qs ++ [uR] := by
      apply List.Perm.eq_of_pairwise' hrs_sorted hqs_sorted_right
      apply Multiset.coe_eq_coe.mp
      calc
        (↑rs : Multiset ℝ) = g.roots := hrs_eq
        _ = ({uR} : Multiset ℝ) + q.roots := by
              rw [hgq, roots_mul (mul_ne_zero (X_sub_C_ne_zero uR) hq_ne), roots_X_sub_C]
        _ = q.roots + ({uR} : Multiset ℝ) := by rw [add_comm]
        _ = q.roots + ↑[uR] := by simp
        _ = (↑qs : Multiset ℝ) + ↑[uR] := by rw [hqs_eq]
        _ = (↑(qs ++ [uR]) : Multiset ℝ) := by rw [Multiset.coe_add]
    have hlen_qs : qs.length + 1 = ss.length := by
      rw [hqs_len, hss_len, hq_deg]
    have halt_right : ListAlternates ss (qs ++ [uR]) := by
      simpa [hrs_eq_right] using halt
    have hshape_qs_rs : ListInterlaces qs ss :=
      listInterlaces_of_listAlternates_append_right_local hlen_qs halt_right
    exact ⟨hf, hq, hq_deg, ss, qs, hss_sorted, hqs_sorted, hss_eq, hqs_eq, hshape_qs_rs⟩

/-- Packaged same-degree rightmost-factor reduction for later sign arguments:
from `Prec f g`, choose the rightmost root of `g`, factor it off, and retain a
genuine differ-by-1 `Interlaces` witness for the quotient against `f`, together
with the explicit rightmost-root bound. -/
theorem exists_rightmost_factor_interlaces_of_prec_sameDegree
    {f g : ℝ[X]}
    (hprec : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree) :
    ∃ uR q,
      g = (X - C uR) * q ∧
      g.IsRoot uR ∧
      (∀ r ∈ g.roots, r ≤ uR) ∧
      Interlaces q f := by
  have hprec_keep : Prec f g := hprec
  obtain ⟨_hf, hg, _ss, _rs, _hss_sorted, _hrs_sorted, _hss_eq, _hrs_eq, _hshape⟩ := hprec
  obtain ⟨uR, huR_root, huR_max⟩ :=
    exists_rightmost_root_of_isRealRooted hg hdeg_pos
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr huR_root
  exact
    ⟨uR, q, hq, huR_root, huR_max,
      interlaces_of_prec_sameDegree_rightmost_factor_local
        (f := f) (g := g) (q := q) (uR := uR)
        hprec_keep hdeg huR_max hq⟩

private lemma exists_strict_root_upper_bound_of_nonneg_of_not_isRoot_zero
    {p : ℝ[X]}
    (hp : IsRealRooted p) (hpnn : HasNonnegCoeffs p)
    (hnot0 : ¬ p.IsRoot 0) :
    ∃ c, (∀ r ∈ p.roots, r ≤ c) ∧ c < 0 := by
  by_cases hdeg0 : p.natDegree = 0
  · refine ⟨-1, ?_, by norm_num⟩
    intro r hr
    have hroots0 : p.roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [hp.2, hdeg0]
    exact False.elim (by simp [hroots0] at hr)
  · have hdeg_pos : 1 ≤ p.natDegree := by omega
    obtain ⟨c, hc_root, hc_top⟩ :=
      exists_rightmost_root_of_isRealRooted hp hdeg_pos
    have hc_le0 : c ≤ 0 :=
      roots_nonpos_of_nonneg_coeffs hp hpnn c ((mem_roots hp.1).mpr hc_root)
    have hc_ne0 : c ≠ 0 := by
      intro hc0
      exact hnot0 (hc0 ▸ hc_root)
    exact ⟨c, hc_top, lt_of_le_of_ne hc_le0 hc_ne0⟩

private lemma isRoot_of_X_mul_of_ne_zero
    {f : ℝ[X]} {r : ℝ}
    (hr : r ≠ 0) (hX : (X * f).IsRoot r) :
    f.IsRoot r := by
  have hX_eval : (X * f).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hX
  have hf_eval : f.eval r = 0 := by
    have hx_eval : r * f.eval r = 0 := by simpa [eval_mul, eval_X] using hX_eval
    exact (mul_eq_zero.mp hx_eval).resolve_left hr
  simpa [Polynomial.IsRoot.def] using hf_eval

private lemma no_common_right_pair_of_no_common_of_not_isRoot_zero
    {f g : ℝ[X]}
    (hno_fg : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg0 : ¬ g.IsRoot 0) :
    ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r := by
  intro r hgr hXr
  by_cases hr0 : r = 0
  · exact hg0 (hr0 ▸ hgr)
  · exact hno_fg r hgr (isRoot_of_X_mul_of_ne_zero hr0 hXr)

private lemma eq_zero_of_common_right_pair_of_no_common
    {f g : ℝ[X]} {r : ℝ}
    (hno_fg : ∀ x, g.IsRoot x → ¬ f.IsRoot x)
    (hgr : g.IsRoot r) (hXr : (X * f).IsRoot r) :
    r = 0 := by
  by_contra hr0
  exact hno_fg r hgr (isRoot_of_X_mul_of_ne_zero hr0 hXr)

private lemma common_right_pair_iff_root_zero_or_common_fg
    {f g : ℝ[X]} :
    (∃ r, g.IsRoot r ∧ (X * f).IsRoot r) ↔
      g.IsRoot 0 ∨ ∃ r, g.IsRoot r ∧ f.IsRoot r := by
  constructor
  · intro h
    rcases h with ⟨r, hgr, hXr⟩
    by_cases hr0 : r = 0
    · left
      simpa [hr0] using hgr
    · right
      exact ⟨r, hgr, isRoot_of_X_mul_of_ne_zero hr0 hXr⟩
  · intro h
    rcases h with hg0 | hcommon
    · exact ⟨0, hg0, by simp [Polynomial.IsRoot.def]⟩
    · rcases hcommon with ⟨r, hgr, hfr⟩
      refine ⟨r, hgr, ?_⟩
      have hf_eval : f.eval r = 0 := by simpa [Polynomial.IsRoot.def] using hfr
      simp [Polynomial.IsRoot.def, eval_mul, eval_X, hf_eval]

private lemma no_common_of_right_pair_root_zero_reduction
    {f g qg : ℝ[X]}
    (hg : g = X * qg)
    (hno_fg : ∀ r, g.IsRoot r → ¬ f.IsRoot r) :
    ∀ r, qg.IsRoot r → ¬ f.IsRoot r := by
  intro r hqgr hfr
  have hqg_eval : qg.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hqgr
  have hg_eval : g.eval r = 0 := by
    simp [hg, eval_mul, eval_X, hqg_eval]
  exact hno_fg r (by simpa [Polynomial.IsRoot.def] using hg_eval) hfr

private lemma roots_strictly_neg_of_nonneg_of_no_common_right_pair
    {f g : ℝ[X]}
    (hg : IsRealRooted g) (hgnn : HasNonnegCoeffs g)
    (hno : ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r) :
    ∀ r ∈ g.roots, r < 0 := by
  intro r hr
  have hr_le : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hg hgnn r hr
  have hr_root : g.IsRoot r := (mem_roots hg.1).mp hr
  have hr_ne : r ≠ 0 := by
    intro hr0
    exact hno 0 (by simpa [hr0] using hr_root) (by simp [Polynomial.IsRoot.def])
  exact lt_of_le_of_ne hr_le hr_ne

private lemma exists_strict_right_root_of_X_mul_of_no_common
    {f g : ℝ[X]}
    (hg : IsRealRooted g) (hgnn : HasNonnegCoeffs g)
    (hno : ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r) :
    ∃ uR, (X * f).IsRoot uR ∧ ∀ r ∈ g.roots, r < uR := by
  refine ⟨0, by simp [Polynomial.IsRoot.def], ?_⟩
  intro r hr
  exact roots_strictly_neg_of_nonneg_of_no_common_right_pair hg hgnn hno r hr

private lemma exists_strict_right_root_of_X_mul_of_no_common_fg_of_not_isRoot_zero
    {f g : ℝ[X]}
    (hg : IsRealRooted g) (hgnn : HasNonnegCoeffs g)
    (hno_fg : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg0 : ¬ g.IsRoot 0) :
    ∃ uR, (X * f).IsRoot uR ∧ ∀ r ∈ g.roots, r < uR := by
  exact
    exists_strict_right_root_of_X_mul_of_no_common hg hgnn
      (no_common_right_pair_of_no_common_of_not_isRoot_zero hno_fg hg0)

/-- In the no-common-roots regime for the affine right-hand pair `(g, X * f)`,
any future Obreschkoff alternative is automatically oriented the correct way:
the distinguished root `0` of `X * f` sits strictly to the right of all roots
of `g`. -/
private lemma prec_right_pair_of_prec_or_revPrec_of_no_common
    {f g : ℝ[X]}
    (h : Prec g (X * f) ∨ Prec (X * f) g)
    (hg : IsRealRooted g) (hgnn : HasNonnegCoeffs g)
    (hno : ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r) :
    Prec g (X * f) := by
  obtain ⟨c, hc_le, hc_lt0⟩ :=
    exists_strict_root_upper_bound_of_nonneg_of_not_isRoot_zero hg hgnn (by
      intro hg0
      exact hno 0 hg0 (by simp [Polynomial.IsRoot.def]))
  exact
    PosComboRealRooted.revPrec_of_prec_or_revPrec_of_root_asymmetry
      (f := g) (g := X * f) (c := c) (r := 0)
      h hc_le (by simp [Polynomial.IsRoot.def]) (by simpa using hc_lt0)

/-- Orientation wrapper for the affine right pair under no-common `f/g` and
`g(0) ≠ 0`: once an Obreschkoff alternative for `(g, X*f)` is available, the
right direction is forced. -/
private lemma prec_right_pair_of_prec_or_revPrec_of_no_common_fg_of_not_isRoot_zero
    {f g : ℝ[X]}
    (h : Prec g (X * f) ∨ Prec (X * f) g)
    (hg : IsRealRooted g) (hgnn : HasNonnegCoeffs g)
    (hno_fg : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg0 : ¬ g.IsRoot 0) :
    Prec g (X * f) := by
  exact
    prec_right_pair_of_prec_or_revPrec_of_no_common h hg hgnn
      (no_common_right_pair_of_no_common_of_not_isRoot_zero hno_fg hg0)

/-- Public orientation selector for the right-hand pair `(g, X * f)` in the
nonnegative-coefficient regime: if an Obreschkoff alternative is known and the
pair has no common root, then the distinguished root `0` of `X * f` forces the
orientation `g ≺ X * f`. -/
theorem prec_right_pair_of_prec_or_revPrec_of_no_common_nonneg
    {f g : ℝ[X]}
    (h : Prec g (X * f) ∨ Prec (X * f) g)
    (hg : IsRealRooted g) (hgnn : HasNonnegCoeffs g)
    (hno : ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r) :
    Prec g (X * f) := by
  exact prec_right_pair_of_prec_or_revPrec_of_no_common h hg hgnn hno

/-- A common root of the right-family pair `(f + g, f + 2g)` is already a
common root of `(f, g)`. This is the elementary subtraction step behind the
`1/2`-family reroute. -/
private lemma no_common_root_right_family_one_two_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, (f + g).IsRoot r → ¬ (f + C (2 : ℝ) * g).IsRoot r := by
  intro r hfg_root hfg2_root
  have hfg_eval : (f + g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hfg_root
  have hfg2_eval : (f + C (2 : ℝ) * g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hfg2_root
  rw [Polynomial.eval_add] at hfg_eval
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hfg2_eval
  have hg_eval : g.eval r = 0 := by
    linarith
  have hf_eval : f.eval r = 0 := by
    linarith
  exact hno r
    (by simpa [Polynomial.IsRoot.def] using hf_eval)
    (by simpa [Polynomial.IsRoot.def] using hg_eval)

/-- A common root of the left-family pair `(f + g, 2f + g)` is already a
common root of `(f, g)`. This is the shifted-pair analogue of the right-family
`1/2` subtraction step. -/
private lemma no_common_root_left_family_one_two_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, (f + g).IsRoot r → ¬ (C (2 : ℝ) * f + g).IsRoot r := by
  intro r hfg_root h2fg_root
  have hfg_eval : (f + g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hfg_root
  have h2fg_eval : (C (2 : ℝ) * f + g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using h2fg_root
  rw [Polynomial.eval_add] at hfg_eval
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at h2fg_eval
  have hf_eval : f.eval r = 0 := by
    linarith
  have hg_eval : g.eval r = 0 := by
    linarith
  exact hno r
    (by simpa [Polynomial.IsRoot.def] using hf_eval)
    (by simpa [Polynomial.IsRoot.def] using hg_eval)

/-- Degree and leading-coefficient bookkeeping for the right-family pair
`(f + g, f + 2g)` when the right summand dominates the degree. -/
private lemma right_family_degree_data_of_posLeadingCoeff
    {f g : ℝ[X]}
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    HasPosLeadingCoeff (f + g) ∧
      HasPosLeadingCoeff (f + C (2 : ℝ) * g) ∧
      (f + g).natDegree = g.natDegree ∧
      (f + C (2 : ℝ) * g).natDegree = g.natDegree := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using
      PosComboRealRooted.family_hasPosLeadingCoeff_right
        (f := f) (g := g) hdeg hf_pos hg_pos (μ := 1) zero_lt_one
  · simpa using
      PosComboRealRooted.family_hasPosLeadingCoeff_right
        (f := f) (g := g) hdeg hf_pos hg_pos (μ := 2) (by norm_num)
  · simpa using
      PosComboRealRooted.family_natDegree_right
        (f := f) (g := g) hdeg hf_pos hg_pos (μ := 1) zero_lt_one
  · simpa using
      PosComboRealRooted.family_natDegree_right
        (f := f) (g := g) hdeg hf_pos hg_pos (μ := 2) (by norm_num)

/-- Degree and leading-coefficient bookkeeping for the left-family pair
`(f + g, 2f + g)` when the left summand dominates the degree. -/
private lemma left_family_degree_data_of_posLeadingCoeff
    {f g : ℝ[X]}
    (hdeg : g.natDegree ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    HasPosLeadingCoeff (f + g) ∧
      HasPosLeadingCoeff (C (2 : ℝ) * f + g) ∧
      (f + g).natDegree = f.natDegree ∧
      (C (2 : ℝ) * f + g).natDegree = f.natDegree := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [one_mul] using
      PosComboRealRooted.family_hasPosLeadingCoeff_left
        (f := f) (g := g) hdeg hf_pos hg_pos (lam := 1) zero_lt_one
  · simpa using
      PosComboRealRooted.family_hasPosLeadingCoeff_left
        (f := f) (g := g) hdeg hf_pos hg_pos (lam := 2) (by norm_num)
  · simpa [one_mul] using
      PosComboRealRooted.family_natDegree_left
        (f := f) (g := g) hdeg hf_pos hg_pos (lam := 1) zero_lt_one
  · simpa using
      PosComboRealRooted.family_natDegree_left
        (f := f) (g := g) hdeg hf_pos hg_pos (lam := 2) (by norm_num)

/-- Right-family packaging specialized to the `1/2` basis change. -/
private lemma right_family_pair_data_one_two
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    PosComboRealRooted (f + g) (f + C (2 : ℝ) * g) ∧
    HasPosLeadingCoeff (f + g) ∧
    HasPosLeadingCoeff (f + C (2 : ℝ) * g) ∧
    (f + g).natDegree = g.natDegree ∧
    (f + C (2 : ℝ) * g).natDegree = g.natDegree ∧
    IsCoprime (f + g) (f + C (2 : ℝ) * g) := by
  simpa using
    PosComboRealRooted.family_pair_data_right
      (f := f) (g := g) hfg hdeg hf_pos hg_pos hno
      (μ₁ := 1) (μ₂ := 2) zero_lt_one (by norm_num) (by norm_num)

/-- Left-family packaging specialized to the `1/2` basis change. -/
private lemma left_family_pair_data_one_two
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    PosComboRealRooted (f + g) (C (2 : ℝ) * f + g) ∧
    HasPosLeadingCoeff (f + g) ∧
    HasPosLeadingCoeff (C (2 : ℝ) * f + g) ∧
    (f + g).natDegree = f.natDegree ∧
    (C (2 : ℝ) * f + g).natDegree = f.natDegree ∧
    IsCoprime (f + g) (C (2 : ℝ) * f + g) := by
  simpa [one_mul] using
    PosComboRealRooted.family_pair_data_left
      (f := f) (g := g) hfg hdeg hf_pos hg_pos hno
      (lam₁ := 1) (lam₂ := 2) zero_lt_one (by norm_num) (by norm_num)

/-- At a root of `f + 2g`, the companion family member `f + g` has the
opposite sign of `g`; no-common-roots makes this strict. -/
private lemma eval_mul_right_family_one_neg_at_root_two_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, (f + C (2 : ℝ) * g).IsRoot r → (f + g).eval r * g.eval r < 0 := by
  intro r hroot
  have hq_eval : (f + C (2 : ℝ) * g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hq_eval
  have hp_eval : (f + g).eval r = -g.eval r := by
    rw [Polynomial.eval_add]
    linarith
  have hg_ne : g.eval r ≠ 0 := by
    intro hg0
    have hf0 : f.eval r = 0 := by
      linarith
    exact hno r
      (by simpa [Polynomial.IsRoot.def] using hf0)
      (by simpa [Polynomial.IsRoot.def] using hg0)
  calc
    (f + g).eval r * g.eval r = -(g.eval r) ^ 2 := by
      rw [hp_eval]
      ring
    _ < 0 := by
      have hsq : 0 < (g.eval r) ^ 2 := sq_pos_iff.mpr hg_ne
      nlinarith

/-- At a root of `f + g`, the companion family member `f + 2g` has the
opposite sign of `f`; no-common-roots makes this strict. -/
private lemma eval_mul_right_family_two_neg_at_root_one_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, (f + g).IsRoot r → (f + C (2 : ℝ) * g).eval r * f.eval r < 0 := by
  intro r hroot
  have hp_eval0 : (f + g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot
  rw [Polynomial.eval_add] at hp_eval0
  have hq_eval : (f + C (2 : ℝ) * g).eval r = -f.eval r := by
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    linarith
  have hf_ne : f.eval r ≠ 0 := by
    intro hf0
    have hg0 : g.eval r = 0 := by
      linarith
    exact hno r
      (by simpa [Polynomial.IsRoot.def] using hf0)
      (by simpa [Polynomial.IsRoot.def] using hg0)
  calc
    (f + C (2 : ℝ) * g).eval r * f.eval r = -(f.eval r) ^ 2 := by
      rw [hq_eval]
      ring
    _ < 0 := by
      have hsq : 0 < (f.eval r) ^ 2 := sq_pos_iff.mpr hf_ne
      nlinarith

/-- At a root of `2f + g`, the companion family member `f + g` has the
opposite sign of `f`; no-common-roots makes this strict. -/
private lemma eval_mul_left_family_one_neg_at_root_two_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, (C (2 : ℝ) * f + g).IsRoot r → (f + g).eval r * f.eval r < 0 := by
  intro r hroot
  have hq_eval : (C (2 : ℝ) * f + g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hq_eval
  have hp_eval : (f + g).eval r = -f.eval r := by
    rw [Polynomial.eval_add]
    linarith
  have hf_ne : f.eval r ≠ 0 := by
    intro hf0
    have hg0 : g.eval r = 0 := by
      linarith
    exact hno r
      (by simpa [Polynomial.IsRoot.def] using hf0)
      (by simpa [Polynomial.IsRoot.def] using hg0)
  calc
    (f + g).eval r * f.eval r = -(f.eval r) ^ 2 := by
      rw [hp_eval]
      ring
    _ < 0 := by
      have hsq : 0 < (f.eval r) ^ 2 := sq_pos_iff.mpr hf_ne
      nlinarith

/-- At a root of `f + g`, the companion family member `2f + g` has the
opposite sign of `g`; no-common-roots makes this strict. -/
private lemma eval_mul_left_family_two_neg_at_root_one_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, (f + g).IsRoot r → (C (2 : ℝ) * f + g).eval r * g.eval r < 0 := by
  intro r hroot
  have hp_eval0 : (f + g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot
  rw [Polynomial.eval_add] at hp_eval0
  have hq_eval : (C (2 : ℝ) * f + g).eval r = -g.eval r := by
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    linarith
  have hg_ne : g.eval r ≠ 0 := by
    intro hg0
    have hf0 : f.eval r = 0 := by
      linarith
    exact hno r
      (by simpa [Polynomial.IsRoot.def] using hf0)
      (by simpa [Polynomial.IsRoot.def] using hg0)
  calc
    (C (2 : ℝ) * f + g).eval r * g.eval r = -(g.eval r) ^ 2 := by
      rw [hq_eval]
      ring
    _ < 0 := by
      have hsq : 0 < (g.eval r) ^ 2 := sq_pos_iff.mpr hg_ne
      nlinarith

private lemma eval_pos_of_all_roots_lt_local {p : ℝ[X]} {r : ℝ}
    (hp : IsRealRooted p) (hp_pos : HasPosLeadingCoeff p)
    (hlt : ∀ t ∈ p.roots, t < r) :
    0 < p.eval r := by
  rw [eval_eq_leadingCoeff_mul_prod_sub hp r]
  have hprod : 0 < (p.roots.map (r - ·)).prod := by
    refine Multiset.prod_pos ?_
    intro y hy
    rcases Multiset.mem_map.mp hy with ⟨t, ht, rfl⟩
    exact sub_pos.mpr (hlt t ht)
  exact mul_pos hp_pos hprod

private lemma strictMonoOn_eval_Ici_of_derivative_roots_le
    {p : ℝ[X]} {c : ℝ}
    (hp' : IsRealRooted p.derivative)
    (hp'_pos : HasPosLeadingCoeff p.derivative)
    (hroots_le : ∀ s ∈ p.derivative.roots, s ≤ c) :
    StrictMonoOn (fun x => p.eval x) (Set.Ici c) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici c) p.continuous.continuousOn ?_
  intro x hx
  have hx' : c < x := by simpa using hx
  have hlt : ∀ t ∈ p.derivative.roots, t < x := by
    intro t ht
    exact lt_of_le_of_lt (hroots_le t ht) hx'
  have hpos_eval : 0 < p.derivative.eval x :=
    eval_pos_of_all_roots_lt_local hp' hp'_pos hlt
  simpa using hpos_eval

private lemma exists_root_ge_of_derivative_root
    {p : ℝ[X]} (hp : IsRealRooted p) (hdeg : 2 ≤ p.natDegree)
    {c : ℝ} (hc : p.derivative.IsRoot c) :
    ∃ r, p.IsRoot r ∧ c ≤ r := by
  obtain ⟨hp_rr, hp'_rr, _hdeg, rs, ss, hrs_sorted, hss_sorted, hrs_eq, hss_eq, hint⟩ :=
    derivative_interlaces hp hdeg
  have hrs_len : rs.length = p.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hp_rr.2]
  have hrs_ne : rs ≠ [] := by
    intro hrs_nil
    simp [hrs_nil] at hrs_len
    omega
  have hc_mem : c ∈ ss := by
    apply Multiset.mem_coe.mp
    rw [hss_eq]
    exact (mem_roots hp'_rr.1).mpr hc
  refine ⟨rs.getLast hrs_ne, ?_, ?_⟩
  · have hr_mem : rs.getLast hrs_ne ∈ rs := List.getLast_mem hrs_ne
    have : rs.getLast hrs_ne ∈ p.roots := by
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr hr_mem
    exact (mem_roots hp_rr.1).mp this
  · exact listInterlaces_all_le_getLast_local hrs_ne hrs_sorted hint c hc_mem

private lemma exists_rightmost_derivative_root_with_eval_nonpos
    {p : ℝ[X]} (hp : IsRealRooted p) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 2 ≤ p.natDegree) :
    ∃ c, p.derivative.IsRoot c ∧
      (∀ s ∈ p.derivative.roots, s ≤ c) ∧
      p.eval c ≤ 0 := by
  have hp' : IsRealRooted p.derivative := (derivative_interlaces hp hdeg).2.1
  have hp'_pos : HasPosLeadingCoeff p.derivative :=
    hasPosLeadingCoeff_derivative hp_pos (by omega)
  have hp'_deg : p.derivative.natDegree = p.natDegree - 1 :=
    natDegree_derivative_eq (by omega)
  obtain ⟨c, hc_root, hc_top⟩ :=
    exists_rightmost_root_of_isRealRooted hp' (by rw [hp'_deg]; omega)
  by_cases hpc : 0 < p.eval c
  · have hmono :
      StrictMonoOn (fun x => p.eval x) (Set.Ici c) := by
      refine strictMonoOn_eval_Ici_of_derivative_roots_le ?_ ?_ ?_
      · exact hp'
      · exact hp'_pos
      · exact hc_top
    obtain ⟨r, hr_root, hcr_le⟩ := exists_root_ge_of_derivative_root hp hdeg hc_root
    have hcr_ne : c ≠ r := by
      intro hcr
      have : p.eval c = 0 := by simpa [Polynomial.IsRoot.def, hcr] using hr_root
      linarith
    have hcr_lt : c < r := lt_of_le_of_ne hcr_le hcr_ne
    have hlt_eval : p.eval c < p.eval r := hmono (by simp) (by exact hcr_le) hcr_lt
    have : p.eval r = 0 := by simpa [Polynomial.IsRoot.def] using hr_root
    linarith
  · exact ⟨c, hc_root, hc_top, le_of_not_gt hpc⟩

/-- For a nonnegative-coefficient real-rooted polynomial of degree at least `2`,
some positive constant shift fails to be real-rooted. The shift is positive
because the rightmost critical value is already nonpositive in the nonnegative
coefficient regime. -/
private lemma exists_pos_shift_not_isRealRooted_of_nonneg_of_natDegree_ge_two
    {p : ℝ[X]} (hp : IsRealRooted p) (hpnn : HasNonnegCoeffs p)
    (hdeg : 2 ≤ p.natDegree) :
    ∃ t : ℝ, 0 < t ∧ ¬ IsRealRooted (C t + p) := by
  have hp_pos : HasPosLeadingCoeff p := hpnn.pos_leadingCoeff hp.1
  obtain ⟨c, hc_root, hc_top, hpc_nonpos⟩ :=
    exists_rightmost_derivative_root_with_eval_nonpos hp hp_pos hdeg
  let t : ℝ := 1 - p.eval c
  have ht_pos : 0 < t := by
    unfold t
    linarith
  refine ⟨t, ht_pos, ?_⟩
  intro hq
  have hqdeg : 2 ≤ (C t + p).natDegree := by
    rw [natDegree_add_eq_right_of_natDegree_lt (by
      rw [natDegree_C]
      omega)]
    exact hdeg
  have hq'_rr : IsRealRooted (C t + p).derivative := (derivative_interlaces hq hqdeg).2.1
  have hmono :
      StrictMonoOn (fun x => (C t + p).eval x) (Set.Ici c) := by
    have hder_eq : (C t + p).derivative = p.derivative := by
      simp
    refine strictMonoOn_eval_Ici_of_derivative_roots_le ?_ ?_ ?_
    · simpa [hder_eq] using hq'_rr
    · simpa [hder_eq] using hasPosLeadingCoeff_derivative hp_pos (by omega)
    · intro s hs
      have hs' : s ∈ p.derivative.roots := by
        simpa [hder_eq] using hs
      exact hc_top s hs'
  have hqc_pos : 0 < (C t + p).eval c := by
    have : (C t + p).eval c = 1 := by
      simp [t]
    linarith
  obtain ⟨r, hr_root, hcr_le⟩ := exists_root_ge_of_derivative_root hq hqdeg (by
    simpa using hc_root)
  by_cases hcr : c = r
  · have : (C t + p).eval c = 0 := by
      simpa [Polynomial.IsRoot.def, hcr] using hr_root
    linarith
  · have hcr_lt : c < r := lt_of_le_of_ne hcr_le hcr
    have hlt_eval :
        (C t + p).eval c < (C t + p).eval r := hmono (by simp) (by exact hcr_le) hcr_lt
    have : (C t + p).eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hr_root
    linarith

/-- A positive constant cannot remain on the right of a degree-`≥ 2`
nonnegative real-rooted polynomial in a `PosComboRealRooted` family. This is
the affine positive-family analogue of the constant-vs-degree-gap obstruction
from the full Obreschkoff converse. -/
private theorem not_posComboRealRooted_right_const_of_natDegree_ge_two
    {c : ℝ} {p : ℝ[X]}
    (hc : 0 < c)
    (hp : IsRealRooted p) (hpnn : HasNonnegCoeffs p)
    (hdeg : 2 ≤ p.natDegree) :
    ¬ PosComboRealRooted p (C c) := by
  intro hpc
  obtain ⟨t, ht, hbad⟩ :=
    exists_pos_shift_not_isRealRooted_of_nonneg_of_natDegree_ge_two hp hpnn hdeg
  have hcombo_t : IsRealRooted (p + C (t / c) * C c) := by
    exact PosComboRealRooted.isRealRooted_add_right hpc (by
      exact div_pos ht hc)
  have hrewrite : p + C (t / c) * C c = p + C t := by
    calc
      p + C (t / c) * C c = p + C ((t / c) * c) := by simp [C_mul]
      _ = p + C t := by
            congr 1
            field_simp [hc.ne']
  exact hbad (by simpa [hrewrite, add_comm] using hcombo_t)

/-- A degree gap of at least `2` is incompatible with a positive left family
`C μ * f + g` once both summands have nonnegative coefficients. -/
private theorem not_degree_gap_ge_two_of_add_left_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfamily :
      ∀ {μ : ℝ}, 0 < μ → IsRealRooted (C μ * f + g))
    (hgap : f.natDegree + 2 ≤ g.natDegree) :
    False := by
  let n : ℕ := f.natDegree
  let fN : ℝ[X] := (derivative^[n]) f
  let gN : ℝ[X] := (derivative^[n]) g
  have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf0
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  have hfamilyN :
      ∀ {μ : ℝ}, 0 < μ → IsRealRooted (gN + C μ * fN) := by
    intro μ hμ
    have hbase : IsRealRooted (C μ * f + g) := hfamily hμ
    have hbase_deg : (C μ * f + g).natDegree = g.natDegree := by
      have hμf_deg : (C μ * f).natDegree = f.natDegree := by
        rw [natDegree_C_mul hμ.ne']
      have hμf_lt : (C μ * f).natDegree < g.natDegree := by
        rw [hμf_deg]
        omega
      exact
        natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
          hμf_lt
          hg_pos
    have hn_lt : n < (C μ * f + g).natDegree := by
      rw [hbase_deg]
      dsimp [n]
      omega
    have hder :
        IsRealRooted ((derivative^[n]) (C μ * f + g)) :=
      isRealRooted_iterate_derivative_of_lt_natDegree hbase hn_lt
    have hEq :
        (derivative^[n]) (C μ * f + g) = gN + C μ * fN := by
      calc
        (derivative^[n]) (C μ * f + g)
            = (derivative^[n]) (C μ * f) + (derivative^[n]) g := by
                rw [iterate_derivative_add]
        _ = C μ * (derivative^[n]) f + (derivative^[n]) g := by
              rw [iterate_derivative_C_mul]
        _ = gN + C μ * fN := by
              simp [fN, gN, add_comm]
    rw [hEq] at hder
    exact hder
  have hfN_deg : fN.natDegree = 0 := by
    dsimp [fN, n]
    simpa using natDegree_iterate_derivative_eq_sub hf0 (le_rfl : f.natDegree ≤ f.natDegree)
  have hfN_ne : fN ≠ 0 := by
    dsimp [fN, n]
    exact iterate_derivative_ne_zero_of_le_natDegree hf0 (le_rfl : f.natDegree ≤ f.natDegree)
  have hfN_nonneg : HasNonnegCoeffs fN := by
    dsimp [fN, n]
    exact hasNonnegCoeffs_iterate_derivative n hfnn
  have hfN_C : fN = C (fN.coeff 0) := eq_C_of_natDegree_eq_zero hfN_deg
  have hfN_coeff_pos : 0 < fN.coeff 0 := by
    have hfN_pos : 0 < fN.leadingCoeff := hfN_nonneg.pos_leadingCoeff hfN_ne
    rw [hfN_C] at hfN_pos
    simpa using hfN_pos
  have hgN_nonneg : HasNonnegCoeffs gN := by
    dsimp [gN, n]
    exact hasNonnegCoeffs_iterate_derivative n hgnn
  have hgN_deg : gN.natDegree = g.natDegree - n := by
    dsimp [gN, n]
    exact natDegree_iterate_derivative_eq_sub hg0 (by omega)
  have hgN_deg_ge2 : 2 ≤ gN.natDegree := by
    rw [hgN_deg]
    dsimp [n]
    omega
  have hgN_ne : gN ≠ 0 := by
    dsimp [gN, n]
    exact iterate_derivative_ne_zero_of_le_natDegree hg0 (by omega)
  have hgN_pos : HasPosLeadingCoeff gN := hgN_nonneg.pos_leadingCoeff hgN_ne
  have hgN_rr : IsRealRooted gN := by
    have hdegN : fN.natDegree < gN.natDegree := by
      rw [hfN_deg]
      omega
    apply isRealRooted_of_add_C_mul_right_family_of_natDegree_lt
    · intro μ hμ
      simpa [add_comm] using hfamilyN hμ
    · exact hfN_nonneg.pos_leadingCoeff hfN_ne
    · exact hgN_pos
    · exact hdegN
  have hposComboN : PosComboRealRooted gN fN := by
    exact PosComboRealRooted.of_add_right hfamilyN
  have hposComboC : PosComboRealRooted gN (C (fN.coeff 0)) := by
    rw [hfN_C] at hposComboN
    exact hposComboN
  exact
    not_posComboRealRooted_right_const_of_natDegree_ge_two
      (p := gN) (c := fN.coeff 0) hfN_coeff_pos hgN_rr hgN_nonneg hgN_deg_ge2
      hposComboC

/-- Affine-family corollary of the positive-family degree-gap obstruction. -/
private theorem not_degree_gap_ge_two_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hgap : f.natDegree + 2 ≤ g.natDegree) :
    False := by
  refine
    not_degree_gap_ge_two_of_add_left_family_nonneg
      hf0 hg0 hfnn hgnn ?_ hgap
  intro μ hμ
  exact
    isRealRooted_add_left_of_affine_family_of_natDegree_succ_le
      hf0 hg0 hfnn hgnn haff (by omega) hμ

/-- Degree control for Brändén's affine-family converse. -/
private theorem natDegree_right_le_succ_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    g.natDegree ≤ f.natDegree + 1 := by
  by_contra hdeg
  exact
    not_degree_gap_ge_two_of_affine_family
      hf0 hg0 hfnn hgnn haff (by omega)

/-- Positive-combination degree control with nonnegative coefficients. This is
the fixed-pair version of the same constant-vs-degree-`≥ 2` obstruction and is
what the affine theorem ultimately wants for the pair `(g, X * f)`. -/
private theorem natDegree_right_le_succ_of_posComboRealRooted_nonneg
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    g.natDegree ≤ f.natDegree + 1 := by
  by_contra hdeg
  refine
    not_degree_gap_ge_two_of_add_left_family_nonneg
      hf0 hg0 hfnn hgnn ?_ (by omega)
  intro μ hμ
  exact PosComboRealRooted.isRealRooted_add_left hfg hμ

private lemma natDegree_cases_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 := by
  have hdeg_right : g.natDegree ≤ f.natDegree + 1 :=
    natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hpair₀ :
      PosComboRealRooted g (X * f) ∧
      HasNonnegCoeffs g ∧
      HasNonnegCoeffs (X * f) ∧
      g ≠ 0 ∧
      X * f ≠ 0 ∧
      HasPosLeadingCoeff g ∧
      HasPosLeadingCoeff (X * f) :=
    affine_family_right_pair_data hfnn hgnn hf0 hg0 haff
  rcases hpair₀ with
    ⟨hpos_pair, hg_nonneg_pair, hXf_nonneg_pair, hg_ne_pair,
      hXf_ne_pair, hg_pos_pair, hXf_pos_pair⟩
  have hdeg_pair_hi : (X * f).natDegree ≤ g.natDegree + 1 :=
    natDegree_right_le_succ_of_posComboRealRooted_nonneg
      hpos_pair hg_ne_pair hXf_ne_pair hg_nonneg_pair hXf_nonneg_pair
  rw [natDegree_mul X_ne_zero hf0, natDegree_X] at hdeg_pair_hi
  omega

private lemma natDegree_cases_right_pair_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    g.natDegree = (X * f).natDegree ∨
      (X * f).natDegree = g.natDegree + 1 := by
  have hpair₀ :
      PosComboRealRooted g (X * f) ∧
      HasNonnegCoeffs g ∧
      HasNonnegCoeffs (X * f) ∧
      g ≠ 0 ∧
      X * f ≠ 0 ∧
      HasPosLeadingCoeff g ∧
      HasPosLeadingCoeff (X * f) :=
    affine_family_right_pair_data hfnn hgnn hf0 hg0 haff
  rcases hpair₀ with
    ⟨hpos_pair, hg_nonneg_pair, hXf_nonneg_pair, hg_ne_pair,
      hXf_ne_pair, _hg_pos_pair, _hXf_pos_pair⟩
  have hdeg_right : g.natDegree ≤ f.natDegree + 1 :=
    natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hdeg_pair_lo : g.natDegree ≤ (X * f).natDegree := by
    rw [natDegree_mul X_ne_zero hf0, natDegree_X]
    simpa [Nat.add_comm] using hdeg_right
  have hdeg_pair_hi : (X * f).natDegree ≤ g.natDegree + 1 :=
    natDegree_right_le_succ_of_posComboRealRooted_nonneg
      hpos_pair hg_ne_pair hXf_ne_pair hg_nonneg_pair hXf_nonneg_pair
  omega

private lemma right_pair_root_zero_reduction_data
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hg_root0 : g.IsRoot 0) :
    ∃ qg,
      g = X * qg ∧
      HasNonnegCoeffs qg ∧
      qg ≠ 0 ∧
      HasPosLeadingCoeff qg ∧
      PosComboRealRooted qg f ∧
      qg.natDegree ≤ f.natDegree ∧
      f.natDegree ≤ qg.natDegree + 1 := by
  have hpair₀ :
      PosComboRealRooted g (X * f) ∧
      HasNonnegCoeffs g ∧
      HasNonnegCoeffs (X * f) ∧
      g ≠ 0 ∧
      X * f ≠ 0 ∧
      HasPosLeadingCoeff g ∧
      HasPosLeadingCoeff (X * f) :=
    affine_family_right_pair_data hfnn hgnn hf0 hg0 haff
  rcases hpair₀ with
    ⟨hpos_pair, hg_nonneg_pair, hXf_nonneg_pair, hg_ne_pair,
      hXf_ne_pair, _hg_pos_pair, _hXf_pos_pair⟩
  obtain ⟨qg, hqg₀⟩ := dvd_iff_isRoot.mpr hg_root0
  have hqg : g = X * qg := by
    simpa using hqg₀
  have hqg_ne : qg ≠ 0 := by
    intro hqg0
    exact hg_ne_pair (by simp [hqg, hqg0])
  have hqg_nonneg : HasNonnegCoeffs qg := by
    intro n
    have hcoeff := hg_nonneg_pair (n + 1)
    simpa [hqg, coeff_X_mul, Nat.succ_ne_zero] using hcoeff
  have hqg_pos : HasPosLeadingCoeff qg := hqg_nonneg.pos_leadingCoeff hqg_ne
  have hpos_q : PosComboRealRooted qg f := by
    have hX_pair : PosComboRealRooted (X * qg) (X * f) := by
      intro lam μ hlam hμ
      simpa [hqg] using hpos_pair hlam hμ
    intro lam μ hlam hμ
    have hEq :
        C lam * (X * qg) + C μ * (X * f) = X * (C lam * qg + C μ * f) := by
      ring
    have hrr : IsRealRooted (X * (C lam * qg + C μ * f)) := by
      simpa [hEq] using hX_pair hlam hμ
    have hcombo_ne : C lam * qg + C μ * f ≠ 0 := by
      exact right_ne_zero_of_mul hrr.1
    exact isRealRooted_of_dvd hrr hcombo_ne ⟨X, by rw [mul_comm]⟩
  have hdeg_right : g.natDegree ≤ f.natDegree + 1 :=
    natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hdeg_q_lo : qg.natDegree ≤ f.natDegree := by
    rw [hqg, natDegree_mul X_ne_zero hqg_ne, natDegree_X] at hdeg_right
    omega
  have hdeg_q_hi : f.natDegree ≤ qg.natDegree + 1 := by
    have hdeg_pair_hi : (X * f).natDegree ≤ g.natDegree + 1 :=
      natDegree_right_le_succ_of_posComboRealRooted_nonneg
        hpos_pair hg_ne_pair hXf_ne_pair hg_nonneg_pair hXf_nonneg_pair
    rw [natDegree_mul X_ne_zero hf0, natDegree_X,
      hqg, natDegree_mul X_ne_zero hqg_ne, natDegree_X] at hdeg_pair_hi
    omega
  exact ⟨qg, hqg, hqg_nonneg, hqg_ne, hqg_pos, hpos_q, hdeg_q_lo, hdeg_q_hi⟩

private lemma right_pair_root_zero_affine_line_data
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hg_root0 : g.IsRoot 0) :
    ∃ qg,
      g = X * qg ∧
      HasNonnegCoeffs qg ∧
      qg ≠ 0 ∧
      HasPosLeadingCoeff qg ∧
      PosComboRealRooted qg f ∧
      qg.natDegree ≤ f.natDegree ∧
      f.natDegree ≤ qg.natDegree + 1 ∧
      (∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (X * (C s * f + qg) + C t * f)) := by
  obtain ⟨qg, hqg, hqg_nonneg, hqg_ne, hqg_pos, hpos_q, hdeg_q_lo, hdeg_q_hi⟩ :=
    right_pair_root_zero_reduction_data hf0 hg0 hfnn hgnn haff hg_root0
  refine ⟨qg, hqg, hqg_nonneg, hqg_ne, hqg_pos, hpos_q, hdeg_q_lo, hdeg_q_hi, ?_⟩
  intro s t hs ht
  have hbase :
      IsRealRooted (((C s * X + C t) * f) + g) := haff hs ht
  have hEq :
      (((C s * X + C t) * f) + g) = X * (C s * f + qg) + C t * f := by
    calc
      (((C s * X + C t) * f) + g)
          = (C s * X) * f + C t * f + X * qg := by
              rw [hqg, add_mul]
      _ = X * (C s * f) + C t * f + X * qg := by
            ac_rfl
      _ = X * (C s * f + qg) + C t * f := by
            rw [mul_add]
            ac_rfl
  simpa [hEq] using hbase

/-- If `r < 0` is a root of the succ-degree affine right-hand polynomial `g`,
specializing the affine family to the line `t = -s r` factors out `X - C r`
and leaves a same-degree positive-combination family for the quotient `qg`. -/
private lemma neg_root_quotient_posCombo_data_of_affine_family_succDegree
    {f g : ℝ[X]} {r : ℝ}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hgr : g.IsRoot r) (hr_neg : r < 0) :
    ∃ qg,
      g = (X - C r) * qg ∧
      qg ≠ 0 ∧
      IsRealRooted qg ∧
      HasPosLeadingCoeff qg ∧
      qg.natDegree = f.natDegree ∧
      PosComboRealRooted qg f := by
  have hg_rr : IsRealRooted g :=
    isRealRooted_right_of_affine_family_succDegree
      hf0 hg0 hfnn hgnn haff hsucc.symm
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hgr
  have hqg_ne : qg ≠ 0 := by
    exact right_ne_zero_of_mul (by simpa [hqg] using hg_rr.1)
  have hqg_rr : IsRealRooted qg := by
    apply isRealRooted_of_dvd hg_rr hqg_ne
    exact ⟨X - C r, by simp [hqg, mul_comm]⟩
  have hqg_pos : HasPosLeadingCoeff qg := by
    exact hasPosLeadingCoeff_of_X_sub_C_mul_local (by simpa [hqg] using hg_pos)
  have hqg_deg : qg.natDegree = f.natDegree := by
    rw [hqg, natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hsucc
    omega
  have hpos_q_left : PosComboRealRooted f qg := by
    refine PosComboRealRooted.of_add_left ?_
    intro s hs
    have hbase :
        IsRealRooted (((C s * X + C (-s * r)) * f) + g) :=
      haff hs (by nlinarith)
    have hlin : C s * (X - C r) = C s * X + C (-s * r) := by
      calc
        C s * (X - C r) = C s * X - C s * C r := by
          rw [mul_sub]
        _ = C s * X - C (s * r) := by
          rw [C_mul]
        _ = C s * X + C (-s * r) := by
          simp [sub_eq_add_neg]
    have hEq :
        (((C s * X + C (-s * r)) * f) + g) =
          (X - C r) * (C s * f + qg) := by
      calc
        (((C s * X + C (-s * r)) * f) + g)
            = (C s * (X - C r)) * f + (X - C r) * qg := by
                rw [hqg, ← hlin]
        _ = (X - C r) * (C s * f) + (X - C r) * qg := by
              ring
        _ = (X - C r) * (C s * f + qg) := by
              rw [mul_add]
    have hcombo_ne : C s * f + qg ≠ 0 := by
      intro hzero
      have hpoly_zero : (((C s * X + C (-s * r)) * f) + g) = 0 := by
        rw [hEq, hzero]
        simp
      exact hbase.1 hpoly_zero
    exact
      isRealRooted_of_dvd hbase hcombo_ne
        ⟨X - C r, by
          calc
            ((C s * X + C (-s * r)) * f + g) = (X - C r) * (C s * f + qg) := hEq
            _ = (C s * f + qg) * (X - C r) := by rw [mul_comm]
        ⟩
  exact ⟨qg, hqg, hqg_ne, hqg_rr, hqg_pos, hqg_deg, hpos_q_left.comm⟩

/-- In the succ-degree affine branch with `g(0) ≠ 0`, the rightmost root of
`g` is strictly negative. Factoring it out gives a same-degree quotient pair
`(qg, f)` with positive-combination real-rootedness. -/
private lemma rightmost_neg_root_quotient_posCombo_data_of_affine_family_succDegree
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hg_root0 : ¬ g.IsRoot 0) :
    ∃ r qg,
      g.IsRoot r ∧
      r < 0 ∧
      g = (X - C r) * qg ∧
      qg ≠ 0 ∧
      IsRealRooted qg ∧
      HasPosLeadingCoeff qg ∧
      qg.natDegree = f.natDegree ∧
      (∀ u ∈ qg.roots, u ≤ r) ∧
      PosComboRealRooted qg f := by
  have hg_rr : IsRealRooted g :=
    isRealRooted_right_of_affine_family_succDegree
      hf0 hg0 hfnn hgnn haff hsucc.symm
  have hdeg_pos : 1 ≤ g.natDegree := by
    omega
  obtain ⟨r, hgr, hr_top⟩ := exists_rightmost_root_of_isRealRooted hg_rr hdeg_pos
  have hr_le : r ≤ 0 := by
    exact roots_nonpos_of_nonneg_coeffs hg_rr hgnn r ((mem_roots hg_rr.1).mpr hgr)
  have hr_neg : r < 0 := by
    have hr_ne : r ≠ 0 := by
      intro hr0
      exact hg_root0 (by simpa [hr0] using hgr)
    exact lt_of_le_of_ne hr_le hr_ne
  obtain ⟨qg, hqg, hqg_ne, hqg_rr, hqg_pos, hqg_deg, hpos_q⟩ :=
    neg_root_quotient_posCombo_data_of_affine_family_succDegree
      hf0 hg0 hfnn hgnn haff hsucc hgr hr_neg
  have hqg_le : ∀ u ∈ qg.roots, u ≤ r := by
    intro u hu
    have hug : u ∈ g.roots := by
      rw [hqg, roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hqg_ne), roots_X_sub_C]
      exact Multiset.mem_add.mpr (Or.inr hu)
    exact hr_top u hug
  exact ⟨r, qg, hgr, hr_neg, hqg, hqg_ne, hqg_rr, hqg_pos, hqg_deg, hqg_le, hpos_q⟩

private lemma prec_right_pair_sameDegree_of_sign_data
    {f g : ℝ[X]}
    (hg : IsRealRooted g)
    (hgnn : HasNonnegCoeffs g)
    (hXf_pos : HasPosLeadingCoeff (X * f))
    (hdeg : (X * f).natDegree = g.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r)
    (hsign :
      let rs := g.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        (X * f).eval r₁ * (X * f).eval r₂ < 0) :
    Prec g (X * f) := by
  have hright :
      let rs := g.roots.sort (· ≤ ·)
      ∃ uR, (X * f).IsRoot uR ∧ ∀ r ∈ rs, r < uR := by
    simpa using exists_strict_right_root_of_X_mul_of_no_common hg hgnn hno
  exact
    PosComboRealRooted.prec_same_of_root_sign_data
      (f := g) (g := X * f) hg hXf_pos hdeg hdeg_pos hsign hright

private lemma prec_right_pair_succDegree_no_common_of_sign_data
    {f g : ℝ[X]}
    (hf0 : f ≠ 0)
    (hg : IsRealRooted g)
    (hgnn : HasNonnegCoeffs g)
    (hXf_pos : HasPosLeadingCoeff (X * f))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno_fg : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg_root0 : ¬ g.IsRoot 0)
    (hsign :
      let rs := g.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        (X * f).eval r₁ * (X * f).eval r₂ < 0) :
    Prec g (X * f) := by
  have hdeg : (X * f).natDegree = g.natDegree := by
    rw [natDegree_mul X_ne_zero hf0, natDegree_X]
    omega
  have hdeg_pos : 1 ≤ g.natDegree := by
    omega
  exact
    prec_right_pair_sameDegree_of_sign_data
      hg hgnn hXf_pos hdeg hdeg_pos
      (no_common_right_pair_of_no_common_of_not_isRoot_zero hno_fg hg_root0)
      hsign

private lemma prec_right_pair_sameDegree_no_common_of_end_sign_data
    {f g : ℝ[X]}
    (hf0 : f ≠ 0)
    (hg : IsRealRooted g)
    (hXf_pos : HasPosLeadingCoeff (X * f))
    (hsame : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hsign :
      let rs := g.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        (X * f).eval r₁ * (X * f).eval r₂ < 0)
    (hright_sign :
      let rs := g.roots.sort (· ≤ ·)
      ∀ hrs_ne : rs ≠ [], (X * f).eval (rs.getLast hrs_ne) < 0)
    (hparity :
      (Even g.natDegree ∧
        let rs := g.roots.sort (· ≤ ·)
        0 < (X * f).eval rs.head!) ∨
      (Odd g.natDegree ∧
        let rs := g.roots.sort (· ≤ ·)
        (X * f).eval rs.head! < 0)) :
    Prec g (X * f) := by
  let rs := g.roots.sort (· ≤ ·)
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_eq : (↑rs : Multiset ℝ) = g.roots := Multiset.sort_eq ..
  have hn : 1 ≤ rs.length := by
    have hrs_len : rs.length = g.natDegree := by
      rw [show rs = g.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hg.2]
    rw [hrs_len]
    exact hdeg_pos
  have hrs_ne : rs ≠ [] := by
    intro hrs_nil
    simp [hrs_nil] at hn
  have hdeg : (X * f).natDegree = g.natDegree + 1 := by
    rw [natDegree_mul X_ne_zero hf0, natDegree_X, hsame]
    ring
  rcases hparity with ⟨hpar, hleft_sign⟩ | ⟨hpar, hleft_sign⟩
  · exact
      prec_of_strict_signs_of_endSigns_even
        (f := g) (F := X * f) (rs := rs)
        hg hXf_pos hrs_sorted hrs_eq hdeg hn hpar
        (by simpa [rs] using hsign)
        (by simpa [rs] using hleft_sign)
        (by simpa [rs] using hright_sign hrs_ne)
  · exact
      prec_of_strict_signs_of_endSigns_odd
        (f := g) (F := X * f) (rs := rs)
        hg hXf_pos hrs_sorted hrs_eq hdeg hn hpar
        (by simpa [rs] using hsign)
        (by simpa [rs] using hleft_sign)
        (by simpa [rs] using hright_sign hrs_ne)

/-- Two nonzero constants satisfy `Prec` trivially because both root lists are
empty. -/
private lemma prec_degree_zero_degree_zero
    {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hf_deg0 : f.natDegree = 0) (hg_deg0 : g.natDegree = 0) :
    Prec f g := by
  have hroots_f : f.roots = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [hf.2, hf_deg0]
  have hroots_g : g.roots = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [hg.2, hg_deg0]
  refine ⟨hf, hg, [], [], by simp, by simp, ?_, ?_, ?_⟩
  · simp [hroots_f]
  · simp [hroots_g]
  · exact Or.inr ⟨by simp, by simp [ListAlternates]⟩

/-- Constant-vs-linear endpoint case for the affine converse. -/
private lemma prec_degree_zero_right_of_degree_one_local
    {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hf_deg0 : f.natDegree = 0) (hg_deg1 : g.natDegree = 1) :
    Prec f g := by
  obtain ⟨r, hr_eq⟩ : ∃ r, g.roots = {r} := by
    apply Multiset.card_eq_one.mp
    simpa [hg_deg1] using hg.2
  have hroots_f : f.roots = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [hf.2, hf_deg0]
  refine ⟨hf, hg, [], [r], by simp, List.pairwise_singleton _ _, ?_, ?_, ?_⟩
  · simp [hroots_f]
  · simp [hr_eq]
  · exact Or.inl ⟨by simp, by simp [ListInterlaces]⟩

/-- In the linear left-hand branch of the affine converse, the right polynomial
must be nonpositive at the unique root of `f`. Otherwise, after translating
that root to `0` and choosing a suitable affine slice, one gets a quadratic
with positive leading coefficient and negative discriminant, contradicting the
real-rooted affine hypothesis. -/
private lemma mul_C_mul_X_mul_C_mul_X (s a : ℝ) :
    (C s * X) * (C a * X) = C (s * a) * X ^ 2 := by
  calc
    (C s * X) * (C a * X) = C s * (X * (C a * X)) := by
      rw [mul_assoc]
    _ = C s * (X * C a * X) := by
      congr 1
      rw [← mul_assoc]
    _ = C s * ((C a * X) * X) := by
      congr 1
      rw [mul_comm X (C a)]
    _ = C s * (C a * (X * X)) := by
      rw [mul_assoc]
    _ = (C s * C a) * (X * X) := by
      rw [← mul_assoc]
    _ = C (s * a) * X ^ 2 := by
      rw [C_mul, pow_two]

private lemma add_quadratic_quadratic (u v w z c : ℝ) :
    C u * X ^ 2 + C v * X + (C w * X ^ 2 + C z * X + C c)
      = C (u + w) * X ^ 2 + C (v + z) * X + C c := by
  calc
    C u * X ^ 2 + C v * X + (C w * X ^ 2 + C z * X + C c)
        = C u * X ^ 2 + C w * X ^ 2 + (C v * X + C z * X) + C c := by
            ac_rfl
    _ = (C u + C w) * X ^ 2 + (C v + C z) * X + C c := by
          rw [← add_mul, ← add_mul]
    _ = C (u + w) * X ^ 2 + C (v + z) * X + C c := by
          rw [← C_add, ← C_add]

set_option maxHeartbeats 800000 in
-- The translated-quadratic contradiction proof below expands several explicit
-- polynomial identities and needs a slightly larger heartbeat budget to
-- elaborate reliably.
private lemma eval_nonpos_at_root_of_degree_one_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hf_deg1 : f.natDegree = 1) :
    ∀ r, f.IsRoot r → g.eval r ≤ 0 := by
  intro r hfr
  have hf_rr : IsRealRooted f := isRealRooted_of_degree_one hf_deg1
  have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf0
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  have hr_nonpos : r ≤ 0 := by
    exact roots_nonpos_of_nonneg_coeffs hf_rr hfnn r ((mem_roots hf_rr.1).mpr hfr)
  by_contra hgr_pos
  have hdeg_cases : g.natDegree = 1 ∨ g.natDegree = 2 := by
    rcases natDegree_cases_of_affine_family hf0 hg0 hfnn hgnn haff with hgdeg | hgdeg
    · left
      simpa [hf_deg1] using hgdeg
    · right
      simpa [hf_deg1] using hgdeg
  let a : ℝ := f.coeff 1
  have ha_pos : 0 < a := by
    unfold HasPosLeadingCoeff at hf_pos
    rw [leadingCoeff, hf_deg1] at hf_pos
    simpa [a] using hf_pos
  have hf_deg_le_one : f.degree ≤ 1 := by
    rw [degree_eq_natDegree hf0, hf_deg1]
    norm_num
  have hf_eq : f = C a * X + C (f.coeff 0) := by
    simpa [a] using (eq_X_add_C_of_degree_le_one (p := f) hf_deg_le_one)
  have hroot_rel : a * r + f.coeff 0 = 0 := by
    have hf_eval : f.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hfr
    rw [hf_eq, eval_add, eval_mul, eval_C, eval_X] at hf_eval
    simpa [a] using hf_eval
  let g' : ℝ[X] := g.comp (X + C r)
  let A : ℝ := g'.coeff 2
  let B : ℝ := g'.coeff 1
  let c : ℝ := g'.coeff 0
  have hc_eq : c = g.eval r := by
    dsimp [c, g']
    rw [coeff_zero_eq_eval_zero, eval_comp]
    simp
  have hc_pos : 0 < c := by
    simpa [hc_eq] using hgr_pos
  have hg'_nonzero : g' ≠ 0 := by
    exact (Polynomial.comp_X_add_C_ne_zero_iff).2 hg0
  have hg'_natDegree : g'.natDegree = g.natDegree := by
    dsimp [g']
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have hg'_deg_le_two : g'.degree ≤ 2 := by
    rcases hdeg_cases with hgdeg | hgdeg
    · rw [degree_eq_natDegree hg'_nonzero, hg'_natDegree, hgdeg]
      norm_num
    · rw [degree_eq_natDegree hg'_nonzero, hg'_natDegree, hgdeg]
      norm_num
  have hg'_eq : g' = C A * X ^ 2 + C B * X + C c := by
    simpa [A, B, c] using eq_quadratic_of_degree_le_two (p := g') hg'_deg_le_two
  have hA_nonneg : 0 ≤ A := by
    rcases hdeg_cases with hgdeg | hgdeg
    · have hg'_deg1 : g'.natDegree = 1 := by
        rw [hg'_natDegree, hgdeg]
      have hA_zero : A = 0 := by
        dsimp [A]
        apply coeff_eq_zero_of_natDegree_lt
        omega
      linarith
    · have hg'_deg2 : g'.natDegree = 2 := by
        rw [hg'_natDegree, hgdeg]
      have hg'_pos : HasPosLeadingCoeff g' := by
        unfold HasPosLeadingCoeff at hg_pos ⊢
        dsimp [g']
        rw [leadingCoeff_comp (by simp), leadingCoeff_X_add_C, one_pow, mul_one]
        exact hg_pos
      have hA_eq_lc : A = g'.leadingCoeff := by
        dsimp [A]
        symm
        rw [leadingCoeff, hg'_deg2]
      have hA_pos : 0 < A := by
        rw [hA_eq_lc]
        exact hg'_pos
      linarith
  let s : ℝ := ((a + B) ^ 2 + 4 * c) / (4 * a * c)
  have hs_pos : 0 < s := by
    dsimp [s]
    have hnum_pos : 0 < (a + B) ^ 2 + 4 * c := by
      have hsq_nonneg : 0 ≤ (a + B) ^ 2 := sq_nonneg (a + B)
      nlinarith
    have hden_pos : 0 < 4 * a * c := by
      positivity
    exact div_pos hnum_pos hden_pos
  let t : ℝ := 1 - s * r
  have ht_pos : 0 < t := by
    dsimp [t]
    nlinarith
  let p : ℝ[X] := (((C s * X + C t) * f) + g)
  have hp_rr : IsRealRooted p := haff hs_pos ht_pos
  let q : ℝ[X] := p.comp (X + C r)
  have hq_rr : IsRealRooted q := by
    dsimp [q, p]
    exact isRealRooted_comp_X_add_C hp_rr r
  have hf_comp : f.comp (X + C r) = C a * X := by
    calc
      f.comp (X + C r) = (C a * X + C (f.coeff 0)).comp (X + C r) := by
            conv_lhs => rw [hf_eq]
      _ = C a * (X + C r) + C (f.coeff 0) := by simp
      _ = C a * X + C (a * r + f.coeff 0) := by
            simp [mul_add, add_left_comm, add_comm, C_mul]
      _ = C a * X := by simp [hroot_rel]
  have hlin_comp :
      (C s * X + C t).comp (X + C r) = C s * X + C (s * r + t) := by
    calc
      (C s * X + C t).comp (X + C r) = C s * (X + C r) + C t := by simp
      _ = C s * X + C (s * r + t) := by
            simp [mul_add, add_assoc, C_mul]
  have hsrt : s * r + t = 1 := by
    dsimp [t]
    ring
  have hq_eq :
      q = C (s * a + A) * X ^ 2 + C (a + B) * X + C c := by
    calc
      q = ((C s * X + C t).comp (X + C r)) * (f.comp (X + C r)) + g' := by
            dsimp [q, p, g']
            rw [add_comp, mul_comp]
      _ = (C s * X + C (s * r + t)) * (C a * X) + g' := by
            rw [hlin_comp, hf_comp]
      _ = (C s * X + C (1 : ℝ)) * (C a * X) + g' := by
            rw [hsrt]
      _ = (C s * X) * (C a * X) + C a * X + g' := by
            rw [add_mul]
            rw [show C (1 : ℝ) * (C a * X) = C a * X by simp]
      _ = C (s * a) * X ^ 2 + C a * X + g' := by
            rw [mul_C_mul_X_mul_C_mul_X]
      _ = C (s * a) * X ^ 2 + C a * X + (C A * X ^ 2 + C B * X + C c) := by
            rw [hg'_eq]
      _ = C (s * a + A) * X ^ 2 + C (a + B) * X + C c := by
            exact add_quadratic_quadratic (u := s * a) (v := a) (w := A) (z := B) (c := c)
  have hsa_pos : 0 < s * a := mul_pos hs_pos ha_pos
  have hquad_pos : 0 < s * a + A := by
    linarith
  have hs_formula : 4 * (s * a) * c = (a + B) ^ 2 + 4 * c := by
    have hden_ne : (4 * a * c) ≠ 0 := by
      have hden_pos : 0 < 4 * a * c := by
        nlinarith
      exact hden_pos.ne'
    calc
      4 * (s * a) * c = s * (4 * a * c) := by ring
      _ = (((a + B) ^ 2 + 4 * c) / (4 * a * c)) * (4 * a * c) := by
            rfl
      _ = (a + B) ^ 2 + 4 * c := by
            field_simp [hden_ne]
  have hdiscrim_neg : discrim (s * a + A) (a + B) c < 0 := by
    have hmain : (a + B) ^ 2 < 4 * (s * a + A) * c := by
      nlinarith [hs_formula, hA_nonneg, hc_pos]
    rw [discrim]
    nlinarith
  have hq_noRoot : ∀ x : ℝ, ¬ q.IsRoot x := by
    intro x hx
    have hq_eval_zero : q.eval x = 0 := by
      simpa [Polynomial.IsRoot.def] using hx
    have hquad_eval :
        (s * a + A) * (x * x) + (a + B) * x + c = 0 := by
      have hq_eval_zero' :
          (C (s * a + A) * X ^ 2 + C (a + B) * X + C c).eval x = 0 := by
        simpa [hq_eq] using hq_eval_zero
      simpa [eval_add, eval_mul, eval_C, eval_X, eval_pow, pow_two] using hq_eval_zero'
    have hdisc_sq :
        discrim (s * a + A) (a + B) c = (2 * (s * a + A) * x + (a + B)) ^ 2 :=
      discrim_eq_sq_of_quadratic_eq_zero hquad_eval
    have hdisc_nonneg : 0 ≤ discrim (s * a + A) (a + B) c := by
      rw [hdisc_sq]
      positivity
    linarith
  have hq_deg2 : q.natDegree = 2 := by
    rw [hq_eq]
    exact natDegree_quadratic (by linarith)
  have hroots_pos : 0 < q.roots.card := by
    rw [hq_rr.2, hq_deg2]
    norm_num
  obtain ⟨x, hx_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
  exact hq_noRoot x ((mem_roots hq_rr.1).mp hx_mem)

/-- Linear left-hand branch of the affine converse. This extracts the
`f.natDegree = 1` case from `prec_of_affine_family_nonneg` so it can later be
reused as the degree-one base case for right-pair recursion. -/
private lemma prec_of_affine_family_nonneg_degree_one
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hdegf1 : f.natDegree = 1) :
    Prec f g := by
  have hdeg_cases : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 :=
    natDegree_cases_of_affine_family hf0 hg0 hfnn hgnn haff
  have hInter : Interlaces (1 : ℝ[X]) f := interlaces_one_linear hdegf1
  have h1_pos : HasPosLeadingCoeff (1 : ℝ[X]) := by
    simp [HasPosLeadingCoeff]
  have hg_pos_local : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  have hdeg_right_local : g.natDegree ≤ f.natDegree + 1 :=
    natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hF_pos :
      HasPosLeadingCoeff ((g / f) * f + (g % f) * (1 : ℝ[X])) := by
    simpa [EuclideanDomain.div_add_mod'] using hg_pos_local
  have hdeg_lo : f.natDegree ≤ ((g / f) * f + (g % f) * (1 : ℝ[X])).natDegree := by
    rcases hdeg_cases with hgdeg | hgdeg <;>
      simpa [EuclideanDomain.div_add_mod'] using (show f.natDegree ≤ g.natDegree by omega)
  have hdeg_hi :
      ((g / f) * f + (g % f) * (1 : ℝ[X])).natDegree ≤ f.natDegree + 1 := by
    simpa [EuclideanDomain.div_add_mod'] using hdeg_right_local
  have hb_nonpos : ∀ r, f.IsRoot r → (g % f).eval r ≤ 0 := by
    intro r hfr
    have hgr_nonpos :
        g.eval r ≤ 0 :=
      eval_nonpos_at_root_of_degree_one_of_affine_family
        hf0 hg0 hfnn hgnn haff hdegf1 r hfr
    have hf_eval : f.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hfr
    have hdivmod_eval :
        (((g / f) * f + g % f).eval r) = g.eval r := by
      exact congrArg (fun p : ℝ[X] => p.eval r) (EuclideanDomain.div_add_mod' g f)
    have hmod_eval : (g % f).eval r = g.eval r := by
      simpa [eval_add, eval_mul, hf_eval] using hdivmod_eval
    simpa [hmod_eval] using hgr_nonpos
  have hprec_lin :
      Prec f (((g / f) * f) + (g % f) * (1 : ℝ[X])) :=
    prec_of_interlaces_evalCoeff_nonpos
      (f := f) (g := (1 : ℝ[X])) (a := g / f) (b := g % f)
      hInter h1_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  simpa [EuclideanDomain.div_add_mod'] using hprec_lin

/-- Degree-one base case for the affine right pair. This is the right-pair
transport of `prec_of_affine_family_nonneg_degree_one`. -/
private lemma prec_right_pair_of_affine_family_degree_one
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hdegf1 : f.natDegree = 1) :
    Prec g (X * f) := by
  exact
    prec_to_prec_mul_X_of_nonneg
      (prec_of_affine_family_nonneg_degree_one hf0 hg0 hfnn hgnn haff hdegf1)
      hfnn hgnn

/-- Public degree-one right-pair form of the affine-family converse.  If
`f.natDegree = 1`, the affine-family hypothesis gives the stronger conclusion
`g ≪ X * f`, not only `f ≪ g`. -/
theorem prec_right_pair_of_affine_family_nonneg_degree_one
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hdegf1 : f.natDegree = 1) :
    Prec g (X * f) :=
  prec_right_pair_of_affine_family_degree_one
    hf0 hg0 hfnn hgnn haff hdegf1

/-- If `g` has an explicit factor `X`, any orientation of `(qg, f)` lifts
immediately to the affine right pair `(g, X * f)` by restoring the common
factor `X`. -/
private lemma prec_right_pair_of_root_zero_factor
    {f g qg : ℝ[X]}
    (hg : g = X * qg)
    (hprec_q : Prec qg f) :
    Prec g (X * f) := by
  have hprec_mul : Prec (X * qg) (X * f) :=
    prec_mul_common_factor isRealRooted_X hprec_q
  simpa [hg, mul_comm] using hprec_mul

/-- A second boundary closure hidden in the affine family: after rescaling the
slice `((C s * X + 1) * f) + g`, one gets `X * f + μ * (f + g)` for every
`μ > 0`, so the same right-family continuity argument also shows `X * f`
itself is real-rooted. -/
private lemma isRealRooted_X_mul_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    IsRealRooted (X * f) := by
  have hdeg_right : g.natDegree ≤ f.natDegree + 1 :=
    natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hfg_nonneg : HasNonnegCoeffs (f + g) := hfnn.add hgnn
  have hfg_ne : f + g ≠ 0 := by
    exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hfnn hgnn hg0
  have hfg_pos : HasPosLeadingCoeff (f + g) := hfg_nonneg.pos_leadingCoeff hfg_ne
  have hXf_nonneg : HasNonnegCoeffs (X * f) := hasNonnegCoeffs_X.mul hfnn
  have hXf_ne : X * f ≠ 0 := mul_ne_zero X_ne_zero hf0
  have hXf_pos : HasPosLeadingCoeff (X * f) := hXf_nonneg.pos_leadingCoeff hXf_ne
  have hdeg_fg : (f + g).natDegree ≤ (X * f).natDegree := by
    have hmax : max f.natDegree g.natDegree ≤ f.natDegree + 1 := by
      refine max_le ?_ hdeg_right
      omega
    have hadd : (f + g).natDegree ≤ max f.natDegree g.natDegree := natDegree_add_le f g
    rw [natDegree_mul X_ne_zero hf0, natDegree_X]
    omega
  apply isRealRooted_of_add_C_mul_right_family_of_natDegree_le
  · intro μ hμ
    have hbase :
        IsRealRooted (((C μ⁻¹ * X + C (1 : ℝ)) * f) + g) :=
      haff (by positivity) zero_lt_one
    have hscaled :
        IsRealRooted
          (C μ * ((((C μ⁻¹ * X + C (1 : ℝ)) * f) + g))) :=
      isRealRooted_C_mul hbase hμ.ne'
    have hmain : C μ * ((C μ⁻¹ * X) * f) = X * f := by
      calc
        C μ * ((C μ⁻¹ * X) * f)
            = C μ * (C μ⁻¹ * (X * f)) := by rw [mul_assoc]
        _ = (C μ * C μ⁻¹) * (X * f) := by rw [mul_assoc]
        _ = C (μ * μ⁻¹) * (X * f) := by rw [C_mul]
        _ = X * f := by simp [hμ.ne']
    have hEq :
        C μ * ((((C μ⁻¹ * X + C (1 : ℝ)) * f) + g))
          = X * f + C μ * (f + g) := by
      calc
        C μ * ((((C μ⁻¹ * X + C (1 : ℝ)) * f) + g))
            = C μ * (((C μ⁻¹ * X + C (1 : ℝ)) * f) ) + C μ * g := by
                rw [mul_add]
        _ = (C μ * ((C μ⁻¹ * X) * f) + C μ * (C (1 : ℝ) * f)) + C μ * g := by
              rw [add_mul, mul_add]
        _ = (X * f + C μ * f) + C μ * g := by
              rw [hmain]
              simp
        _ = X * f + C μ * (f + g) := by
              rw [mul_add]
              ac_rfl
    rw [hEq] at hscaled
    simpa using hscaled
  · exact hfg_pos
  · exact hXf_pos
  · exact hdeg_fg

/-- Repackage the affine family as a one-parameter positive-combination family
for the shifted pair `(g + X * f, f)`. This is the natural shifted target for
the affine converse: proving `Prec f (g + X * f)` would reduce the original
statement to the folklore subtraction step. -/
private lemma posComboRealRooted_shifted_pair_of_affine_family
    {f g : ℝ[X]}
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    PosComboRealRooted (g + X * f) f := by
  intro lam μ hlam hμ
  have hbase :
      IsRealRooted (((C (1 : ℝ) * X + C (μ / lam)) * f) + g) :=
    haff zero_lt_one (by positivity)
  have hscaled :
      IsRealRooted
        (C lam * ((((C (1 : ℝ) * X + C (μ / lam)) * f) + g))) :=
    isRealRooted_C_mul hbase hlam.ne'
  have hmain : C lam * (C (μ / lam) * f) = C μ * f := by
    calc
      C lam * (C (μ / lam) * f) = (C lam * C (μ / lam)) * f := by
        rw [mul_assoc]
      _ = C (lam * (μ / lam)) * f := by rw [C_mul]
      _ = C μ * f := by
            congr 1
            field_simp [hlam.ne']
  have hEq :
      C lam * (((X + C (μ / lam)) * f) + g)
        = C lam * (g + X * f) + C μ * f := by
    calc
      C lam * (((X + C (μ / lam)) * f) + g)
          = C lam * ((X + C (μ / lam)) * f) + C lam * g := by
              rw [mul_add]
      _ = C lam * (X * f + C (μ / lam) * f) + C lam * g := by
            rw [add_mul]
      _ = (C lam * (X * f) + C lam * (C (μ / lam) * f)) + C lam * g := by
            rw [mul_add]
      _ = (C lam * (X * f) + C μ * f) + C lam * g := by
            rw [hmain]
      _ = C lam * (g + X * f) + C μ * f := by
            rw [mul_add]
            ac_rfl
  simpa [hEq] using hscaled

/-- Degree bookkeeping for the shifted affine pair `(g + X * f, f)`: the left
member always has exact succ-degree over `f`. -/
private lemma natDegree_shifted_pair_eq_succ_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    (g + X * f).natDegree = f.natDegree + 1 := by
  have hdeg_right : g.natDegree ≤ f.natDegree + 1 :=
    natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hXf_pos : HasPosLeadingCoeff (X * f) := by
    unfold HasPosLeadingCoeff at ⊢
    rw [leadingCoeff_mul, leadingCoeff_X]
    simpa using hfnn.pos_leadingCoeff hf0
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  rcases lt_or_eq_of_le hdeg_right with hlt | heq
  · have hg_lt : g.natDegree < (X * f).natDegree := by
      rw [natDegree_mul X_ne_zero hf0, natDegree_X]
      omega
    have hsum_deg : (g + X * f).natDegree = (X * f).natDegree := by
      exact
        natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
          hg_lt hXf_pos
    rw [hsum_deg, natDegree_mul X_ne_zero hf0, natDegree_X]
    omega
  · have hg_eq : g.natDegree = (X * f).natDegree := by
      rw [natDegree_mul X_ne_zero hf0, natDegree_X]
      omega
    have hsum_deg : (g + X * f).natDegree = (X * f).natDegree := by
      exact
        natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
          hg_eq hg_pos hXf_pos |>.trans hg_eq
    rw [hsum_deg, natDegree_mul X_ne_zero hf0, natDegree_X]
    omega

/-- Data package for the shifted affine pair `(g + X * f, f)`. This isolates
the clean succ-degree positive-family reformulation of the affine converse. -/
private lemma affine_family_shifted_pair_data
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    PosComboRealRooted (g + X * f) f ∧
    HasNonnegCoeffs (g + X * f) ∧
    HasNonnegCoeffs f ∧
    (g + X * f) ≠ 0 ∧
    f ≠ 0 ∧
    HasPosLeadingCoeff (g + X * f) ∧
    HasPosLeadingCoeff f ∧
    (g + X * f).natDegree = f.natDegree + 1 := by
  have hshift_nonneg : HasNonnegCoeffs (g + X * f) :=
    hgnn.add (hasNonnegCoeffs_X.mul hfnn)
  have hshift_ne : g + X * f ≠ 0 := by
    exact
      add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
        hgnn (hasNonnegCoeffs_X.mul hfnn) (mul_ne_zero X_ne_zero hf0)
  refine
    ⟨posComboRealRooted_shifted_pair_of_affine_family haff,
      hshift_nonneg, hfnn, hshift_ne, hf0,
      hshift_nonneg.pos_leadingCoeff hshift_ne,
      hfnn.pos_leadingCoeff hf0,
      natDegree_shifted_pair_eq_succ_of_affine_family hf0 hg0 hfnn hgnn haff⟩

private lemma common_shifted_pair_iff_common_fg
    {f g : ℝ[X]} :
    (∃ r, (g + X * f).IsRoot r ∧ f.IsRoot r) ↔
      ∃ r, g.IsRoot r ∧ f.IsRoot r := by
  constructor
  · intro h
    rcases h with ⟨r, hshift, hfr⟩
    have hf_eval : f.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hfr
    have hshift_eval : (g + X * f).eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hshift
    have hg_eval : g.eval r = 0 := by
      simpa [eval_add, eval_mul, eval_X, hf_eval] using hshift_eval
    exact ⟨r, by simpa [Polynomial.IsRoot.def] using hg_eval, hfr⟩
  · intro h
    rcases h with ⟨r, hgr, hfr⟩
    have hf_eval : f.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hfr
    have hg_eval : g.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hgr
    refine ⟨r, ?_, hfr⟩
    simp [Polynomial.IsRoot.def, eval_add, eval_mul, eval_X, hf_eval, hg_eval]

private lemma no_common_shifted_pair_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, f.IsRoot r → ¬ (g + X * f).IsRoot r := by
  intro r hfr hshift
  have hf_eval : f.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hfr
  have hshift_eval : (g + X * f).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hshift
  have hg_eval : g.eval r = 0 := by
    simpa [eval_add, eval_mul, eval_X, hf_eval] using hshift_eval
  exact hno r hfr (by simpa [Polynomial.IsRoot.def] using hg_eval)

private lemma not_revPrec_of_shifted_pair_succDegree
    {f s : ℝ[X]}
    (hdeg : s.natDegree = f.natDegree + 1) :
    ¬ Prec s f := by
  intro h
  rcases h with ⟨hs, hf, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hss_len : ss.length = s.natDegree := by
    rw [← Multiset.coe_card, hss_eq, hs.2]
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩ <;> omega

private lemma prec_shifted_pair_of_prec_or_revPrec
    {f g : ℝ[X]}
    (h : Prec f (g + X * f) ∨ Prec (g + X * f) f)
    (hdeg : (g + X * f).natDegree = f.natDegree + 1) :
    Prec f (g + X * f) := by
  rcases h with hfg | hgf
  · exact hfg
  · exact False.elim (not_revPrec_of_shifted_pair_succDegree hdeg hgf)

private lemma prec_of_prec_shifted_pair_sameDegree
    {f g : ℝ[X]}
    (h : Prec f (g + X * f))
    (hf0 : f ≠ 0)
    (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : g.natDegree = f.natDegree) :
    Prec f g := by
  have hf : IsRealRooted f := h.1
  have hshift : IsRealRooted (g + X * f) := h.2.1
  have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf0
  have hshift_nonneg : HasNonnegCoeffs (g + X * f) :=
    hgnn.add (hasNonnegCoeffs_X.mul hfnn)
  have hshift_ne : g + X * f ≠ 0 := hshift.1
  have hshift_pos : HasPosLeadingCoeff (g + X * f) :=
    hshift_nonneg.pos_leadingCoeff hshift_ne
  have hshift_deg : (g + X * f).natDegree = f.natDegree + 1 := by
    have hXf_deg : (X * f).natDegree = f.natDegree + 1 := by
      simpa [Nat.add_comm] using (natDegree_mul X_ne_zero hf0).trans (by simp [natDegree_X])
    have hXf_pos : HasPosLeadingCoeff (X * f) :=
      (hasNonnegCoeffs_X.mul hfnn).pos_leadingCoeff (mul_ne_zero X_ne_zero hf0)
    have hg_lt : g.natDegree < (X * f).natDegree := by
      rw [hdeg, hXf_deg]
      omega
    have hsum_deg : (g + X * f).natDegree = (X * f).natDegree := by
      exact
        natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
          hg_lt hXf_pos
    rw [hsum_deg, hXf_deg]
  let a : ℝ := f.leadingCoeff⁻¹
  have ha_ne : a ≠ 0 := inv_ne_zero (ne_of_gt hf_pos)
  have hf_monic : (C a * f).Monic := by
    unfold a
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    field_simp [ne_of_gt hf_pos]
  have hshift_lc : (g + X * f).leadingCoeff = f.leadingCoeff := by
    have hg_top_zero : g.coeff (f.natDegree + 1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hdeg]
      omega
    rw [leadingCoeff, hshift_deg, coeff_add, coeff_X_mul]
    simp [hg_top_zero]
  have hshift_monic : (C a * (g + X * f)).Monic := by
    unfold a
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [hshift_lc]
    field_simp [ne_of_gt hf_pos]
  have hscaled : Prec (C a * f) (C a * (g + X * f)) :=
    prec_C_mul_right (prec_C_mul_left h ha_ne) ha_ne
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf hfnn
  have hshift_nonpos : ∀ r ∈ (g + X * f).roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hshift hshift_nonneg
  have hprec0 :
      Prec0 (C a * f) (C a * (g + X * f) - X * (C a * f)) := by
    have hdeg_scaled : (C a * f).natDegree + 1 = (C a * (g + X * f)).natDegree := by
      rw [natDegree_C_mul ha_ne, natDegree_C_mul ha_ne, hshift_deg]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using
      prec_sub_X_mul_right
        (f := C a * (g + X * f)) (g := C a * f)
        hscaled hshift_monic hf_monic hdeg_scaled
        (by
          intro r hr
          exact hshift_nonpos r (by simpa [roots_C_mul _ ha_ne] using hr))
        (by
          intro r hr
          exact hf_nonpos r (by simpa [roots_C_mul _ ha_ne] using hr))
  have hEq_sub : C a * (g + X * f) - X * (C a * f) = C a * g := by
    have hCXf : C a * (X * f) = X * (C a * f) := by
      ext n
      cases n <;> simp [coeff_X_mul]
    calc
      C a * (g + X * f) - X * (C a * f)
          = C a * g + C a * (X * f) - X * (C a * f) := by
              rw [mul_add]
      _ = C a * g := by
            rw [hCXf]
            simp
  have hprec_scaled : Prec (C a * f) (C a * g) := by
    rw [hEq_sub] at hprec0
    have hCa_f_ne : C a * f ≠ 0 := mul_ne_zero (C_ne_zero.mpr ha_ne) hf0
    have hCa_g_ne : C a * g ≠ 0 := mul_ne_zero (C_ne_zero.mpr ha_ne) hg0
    rcases hprec0 with hleft0 | hright0 | hprec
    · exact False.elim (hCa_f_ne hleft0)
    · exact False.elim (hCa_g_ne hright0)
    · exact hprec
  have hprec_back :
      Prec (C a⁻¹ * (C a * f)) (C a⁻¹ * (C a * g)) :=
    prec_C_mul_right
      (prec_C_mul_left hprec_scaled (inv_ne_zero ha_ne))
      (inv_ne_zero ha_ne)
  have hcancel_f : C a⁻¹ * (C a * f) = f := by
    calc
      C a⁻¹ * (C a * f) = C (a⁻¹ * a) * f := by rw [C_mul, mul_assoc]
      _ = f := by simp [ha_ne]
  have hcancel_g : C a⁻¹ * (C a * g) = g := by
    calc
      C a⁻¹ * (C a * g) = C (a⁻¹ * a) * g := by rw [C_mul, mul_assoc]
      _ = g := by simp [ha_ne]
  simpa [hcancel_f, hcancel_g] using hprec_back

private lemma prec_right_pair_of_prec_shifted_pair_sameDegree
    {f g : ℝ[X]}
    (h : Prec f (g + X * f))
    (hf0 : f ≠ 0)
    (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : g.natDegree = f.natDegree) :
    Prec g (X * f) := by
  exact
    prec_to_prec_mul_X_of_nonneg
      (prec_of_prec_shifted_pair_sameDegree h hf0 hg0 hfnn hgnn hdeg)
      hfnn hgnn

private lemma shifted_affine_family_of_affine_family
    {f g : ℝ[X]}
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    ∀ {s t : ℝ}, 0 < s → 0 < t →
      IsRealRooted (((C s * X + C t) * f) + (g + X * f)) := by
  intro s t hs ht
  have hbase :
      IsRealRooted (((C (s + 1) * X + C t) * f) + g) :=
    haff (by linarith) ht
  have hEq :
      (((C s * X + C t) * f) + (g + X * f)) =
        (((C (s + 1) * X + C t) * f) + g) := by
    calc
      (((C s * X + C t) * f) + (g + X * f))
          = ((C s * X + C t) * f) + g + X * f := by
              ac_rfl
      _ = (C s * X) * f + C t * f + g + X * f := by
            rw [add_mul]
      _ = C s * (X * f) + C t * f + g + X * f := by
            rw [mul_assoc]
      _ = (C s * (X * f) + X * f) + C t * f + g := by
            ac_rfl
      _ = (C s * (X * f) + C (1 : ℝ) * (X * f)) + C t * f + g := by
            simp
      _ = ((C s + C (1 : ℝ)) * (X * f)) + C t * f + g := by
            rw [← add_mul]
      _ = (C (s + 1) * (X * f)) + C t * f + g := by
            rw [← C_add]
      _ = ((C (s + 1) * X) * f) + C t * f + g := by
            rw [mul_assoc]
      _ = (((C (s + 1) * X + C t) * f) + g) := by
            rw [add_mul]
  simpa [hEq] using hbase

/-- Downward boundary closure: if `g - C μ * f` is real-rooted for all
sufficiently small `μ > 0`, and `f.natDegree < g.natDegree` with both
having positive leading coefficients, then `g` is real-rooted.

The proof is the same complex-root continuity argument as
`isRealRooted_of_add_C_mul_right_family_of_natDegree_lt`, applied with
`-f` as the perturbation (the sign doesn't affect coefficient convergence). -/
private theorem isRealRooted_of_sub_C_mul_right_family_of_natDegree_lt
    {f g : ℝ[X]}
    (hfamily : ∀ {μ : ℝ}, 0 < μ → IsRealRooted (g - C μ * f))
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : f.natDegree < g.natDegree) :
    IsRealRooted g := by
  -- Reduce to the upward-closure lemma by replacing f with -f.
  -- Note: g - C μ * f = g + C μ * (-f) and (-f).natDegree = f.natDegree.
  -- We need HasPosLeadingCoeff (-f) which fails, so we bypass and work
  -- with the monic normalization directly.
  let f₀ : ℝ[X] := C f.leadingCoeff⁻¹ * f
  let g₀ : ℝ[X] := C g.leadingCoeff⁻¹ * g
  have hf_lc_ne : f.leadingCoeff ≠ 0 := ne_of_gt hf_pos
  have hg_lc_ne : g.leadingCoeff ≠ 0 := ne_of_gt hg_pos
  have hf₀_monic : f₀.Monic := by
    unfold f₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    field_simp [hf_lc_ne]
  have hg₀_monic : g₀.Monic := by
    unfold g₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    field_simp [hg_lc_ne]
  have hg₀_pos : HasPosLeadingCoeff g₀ := by
    simp [HasPosLeadingCoeff, hg₀_monic.leadingCoeff]
  have hdeg₀ : f₀.natDegree < g₀.natDegree := by
    simp [f₀, g₀, natDegree_C_mul, hf_lc_ne, hg_lc_ne, hdeg]
  -- Monic subtraction family: g₀ - C μ'' * f₀ is real-rooted for small μ'' > 0.
  have hfamily₀ : ∀ {μ : ℝ}, 0 < μ → IsRealRooted (g₀ - C μ * f₀) := by
    intro μ hμ
    have hμ' : 0 < μ * g.leadingCoeff / f.leadingCoeff := by
      exact div_pos (mul_pos hμ hg_pos) hf_pos
    have hbase : IsRealRooted (g - C (μ * g.leadingCoeff / f.leadingCoeff) * f) :=
      hfamily hμ'
    have hscaled :
        IsRealRooted
          (C g.leadingCoeff⁻¹ *
            (g - C (μ * g.leadingCoeff / f.leadingCoeff) * f)) :=
      isRealRooted_C_mul hbase (inv_ne_zero hg_lc_ne)
    have hEq :
        C g.leadingCoeff⁻¹ *
            (g - C (μ * g.leadingCoeff / f.leadingCoeff) * f) =
          g₀ - C μ * f₀ := by
      ext n
      simp [g₀, f₀, mul_sub]
      field_simp [hf_lc_ne, hg_lc_ne]
    simpa [hEq] using hscaled
  -- Now: g₀ - C μ * f₀ is real-rooted, monic, same degree as g₀, and
  -- its coefficients converge to those of g₀ as μ → 0⁺.
  -- Use the same complex-root continuity argument to show g₀ is real-rooted.
  have hg₀_rr : IsRealRooted g₀ := by
    have hroots_real :
        ∀ z ∈ (g₀.map (algebraMap ℝ ℂ)).roots, z ∈ (algebraMap ℝ ℂ).range := by
      intro z hz_mem
      have hmap_ne : g₀.map (algebraMap ℝ ℂ) ≠ 0 :=
        (Polynomial.map_ne_zero_iff (RingHom.injective (algebraMap ℝ ℂ))).2
          hg₀_monic.ne_zero
      have hz_root : (g₀.map (algebraMap ℝ ℂ)).IsRoot z :=
        (Polynomial.mem_roots hmap_ne).1 hz_mem
      have hz_aeval : g₀.aeval z = 0 := by
        have hz_eval_map : (g₀.map (algebraMap ℝ ℂ)).eval z = 0 := by
          simpa [Polynomial.IsRoot.def] using hz_root
        simpa [eval₂_at_apply] using hz_eval_map
      by_contra hz_range
      have hz_im_ne : z.im ≠ 0 := by
        intro hz_im; apply hz_range; exact ⟨z.re, Complex.ext_iff.2 (by simp [hz_im])⟩
      let δ : ℝ := |z.im| / 2
      let R : ℝ := max ‖z‖ 1
      have hδ_pos : 0 < δ := half_pos (abs_pos.mpr hz_im_ne)
      have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      have hg₀_deg_pos : 0 < g₀.natDegree := lt_of_le_of_lt (Nat.zero_le _) hdeg₀
      have hdeg_nat_ne : g₀.natDegree ≠ 0 := Nat.ne_of_gt hg₀_deg_pos
      let u : ℝ := δ / (2 * R)
      let ε : ℝ := (u ^ g₀.natDegree) / (g₀.natDegree + 1)
      have hu_nonneg : 0 ≤ u := by positivity
      have hu_pos : 0 < u := by positivity
      have hε_pos : 0 < ε := by positivity
      let μ : ℝ := ε / (coeffSumRange f₀ + 1)
      have hcoeff_nonneg : 0 ≤ coeffSumRange f₀ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hμ_pos : 0 < μ := by positivity
      have hμ_bound : μ * coeffSumRange f₀ < ε := by
        unfold μ
        have hden_pos : 0 < coeffSumRange f₀ + 1 := by linarith
        have hfrac_lt_one : coeffSumRange f₀ / (coeffSumRange f₀ + 1) < 1 := by
          rw [div_lt_iff₀ hden_pos]; linarith
        have hcalc :
            (ε / (coeffSumRange f₀ + 1)) * coeffSumRange f₀ =
              ε * (coeffSumRange f₀ / (coeffSumRange f₀ + 1)) := by
          field_simp [show (coeffSumRange f₀ + 1 : ℝ) ≠ 0 by linarith]
        rw [hcalc]
        calc ε * (coeffSumRange f₀ / (coeffSumRange f₀ + 1))
            < ε * 1 := mul_lt_mul_of_pos_left hfrac_lt_one hε_pos
          _ = ε := by ring
      -- Coefficient closeness:
      -- ‖(g₀ - C μ * f₀).coeff i - g₀.coeff i‖ = μ * |f₀.coeff i|
      have hcoeff :
          ∀ i : ℕ, ‖(g₀ - C μ * f₀).coeff i - g₀.coeff i‖ < ε := by
        intro i
        have : (g₀ - C μ * f₀).coeff i - g₀.coeff i = -(μ * f₀.coeff i) := by
          simp [coeff_sub, coeff_C_mul]
        rw [this, norm_neg]
        calc ‖μ * f₀.coeff i‖ = μ * ‖f₀.coeff i‖ := by
              rw [norm_mul, Real.norm_of_nonneg hμ_pos.le]
          _ ≤ μ * coeffSumRange f₀ := by
              exact mul_le_mul_of_nonneg_left (coeff_norm_le_coeffSumRange f₀ i) hμ_pos.le
          _ < ε := hμ_bound
      have hμf_deg_lt : (C μ * f₀).natDegree < g₀.natDegree := by
        simpa [natDegree_C_mul hμ_pos.ne'] using hdeg₀
      have hdiff_deg : (g₀ - C μ * f₀).natDegree = g₀.natDegree := by
        rw [sub_eq_add_neg, ← neg_mul]
        exact natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff
          (by simpa [natDegree_neg, natDegree_C_mul hμ_pos.ne'] using hdeg₀) hg₀_pos
      have hdiff_monic : (g₀ - C μ * f₀).Monic := by
        unfold Polynomial.Monic Polynomial.leadingCoeff
        rw [hdiff_deg, coeff_sub, coeff_eq_zero_of_natDegree_lt hμf_deg_lt,
          hg₀_monic.coeff_natDegree, sub_zero]
      obtain ⟨w, hw_root, hw_dist⟩ :=
        exists_complex_aroot_near_of_isRealRooted_of_monic_of_coeff_close
          (f := g₀) (g := g₀ - C μ * f₀) (z := z) (ε := ε)
          hε_pos hz_aeval hg₀_monic hdiff_monic hdiff_deg hcoeff (hfamily₀ hμ_pos)
      have hw_im_zero : w.im = 0 :=
        RealRooted.im_eq_zero_of_mem_aroots_of_isRealRooted (hfamily₀ hμ_pos) hw_root
      have hbound_eq :
          ((g₀.natDegree + 1) * ε) ^ ((g₀.natDegree : ℝ)⁻¹) * R = δ / 2 := by
        have hmul : ((g₀.natDegree + 1 : ℝ) * ε) = u ^ g₀.natDegree := by
          unfold ε; field_simp
        calc ((g₀.natDegree + 1) * ε) ^ ((g₀.natDegree : ℝ)⁻¹) * R
            = (u ^ g₀.natDegree) ^ ((g₀.natDegree : ℝ)⁻¹) * R := by rw [hmul]
          _ = u * R := by rw [Real.pow_rpow_inv_natCast hu_nonneg hdeg_nat_ne]
          _ = δ / 2 := by
                unfold u
                field_simp [hR_pos.ne']
      have hdist_lt : ‖z - w‖ < δ := by
        calc
          ‖z - w‖ <
              ((g₀.natDegree + 1) * ε) ^ ((g₀.natDegree : ℝ)⁻¹) * max ‖z‖ 1
                := by
                  exact hw_dist
          _ = δ / 2 := hbound_eq
          _ < δ := by linarith [hδ_pos]
      have him_le : |z.im| ≤ ‖z - w‖ := by
        simpa [Complex.sub_im, hw_im_zero] using (Complex.abs_im_le_norm (z - w))
      have him_lt : |z.im| < δ := lt_of_le_of_lt him_le hdist_lt
      have hhalf : |z.im| < |z.im| / 2 := by simpa [δ] using him_lt
      nlinarith [abs_pos.mpr hz_im_ne]
    have hsplit : g₀.Splits :=
      Polynomial.Splits.of_splits_map (i := algebraMap ℝ ℂ)
        (IsAlgClosed.splits _) hroots_real
    exact ⟨hg₀_monic.ne_zero, (Polynomial.splits_iff_card_roots).1 hsplit⟩
  simpa [show C g.leadingCoeff * g₀ = g from by ext n; simp [g₀, hg_lc_ne]] using
    isRealRooted_C_mul hg₀_rr hg_lc_ne

/-- An exact double root has nonvanishing second derivative. This is the local
algebraic input behind the bounded right-family double-root obstruction below. -/
private lemma eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two_local
    {p : ℝ[X]} {x : ℝ}
    (hp0 : p ≠ 0)
    (hmult : p.rootMultiplicity x = 2) :
    p.derivative.derivative.eval x ≠ 0 := by
  have hp_root : p.IsRoot x := by
    exact (rootMultiplicity_pos hp0).mp (by simp [hmult])
  have hp_deg_ge2 : 2 ≤ p.natDegree := by
    calc
      2 = p.rootMultiplicity x := by simp [hmult]
      _ = p.roots.count x := (count_roots p).symm
      _ ≤ p.roots.card := p.roots.count_le_card x
      _ ≤ p.natDegree := card_roots' p
  have hpd_ne : p.derivative ≠ 0 := derivative_ne_zero hp_deg_ge2
  have hpd_rootmult : p.derivative.rootMultiplicity x = 1 := by
    rw [derivative_rootMultiplicity_of_root hp_root, hmult]
  intro hder2
  have hpd_root : p.derivative.IsRoot x := by
    exact (rootMultiplicity_pos hpd_ne).mp (by simp [hpd_rootmult])
  have hpd_der_root : p.derivative.derivative.IsRoot x := by
    simpa [Polynomial.IsRoot.def] using hder2
  have hmult_gt : 1 < p.derivative.rootMultiplicity x := by
    exact (one_lt_rootMultiplicity_iff_isRoot hpd_ne).2 ⟨hpd_root, hpd_der_root⟩
  rw [hpd_rootmult] at hmult_gt
  omega

/-- Local bounded right-family double-root obstruction.

If `p` has an exact double root at `x`, `q(x) ≠ 0`, and every sufficiently
small positive perturbation `p + β q` in a fixed right-family window remains
real-rooted, then the standard non-root second-derivative inequality rules out
the positive-sign case `p''(x) * q(x) > 0`. -/
private lemma false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
    {p q : ℝ[X]} {x βmax : ℝ}
    (hfamily :
      ∀ {β : ℝ}, 0 < β → β ≤ βmax → IsRealRooted (p + C β * q))
    (hβmax : 0 < βmax)
    (hp_mult : p.rootMultiplicity x = 2)
    (hq_eval_ne : q.eval x ≠ 0)
    (hprod_pos : 0 < p.derivative.derivative.eval x * q.eval x) :
    False := by
  have hp0 : p ≠ 0 := by
    intro hp0
    simp [hp0] at hp_mult
  have hp_root : p.IsRoot x := by
    exact (rootMultiplicity_pos hp0).mp (by simp [hp_mult])
  have hp_der_root : p.derivative.IsRoot x := by
    exact isRoot_derivative_of_rootMultiplicity_ge_two (by simp [hp_mult])
  have hp_eval0 : p.eval x = 0 := by
    simpa [Polynomial.IsRoot.def] using hp_root
  have hp_der_eval0 : p.derivative.eval x = 0 := by
    simpa [Polynomial.IsRoot.def] using hp_der_root
  let pp : ℝ := p.derivative.derivative.eval x
  let qx : ℝ := q.eval x
  let qp : ℝ := q.derivative.eval x
  let qq : ℝ := q.derivative.derivative.eval x
  have hpp_ne : pp ≠ 0 := by
    have hprod_ne : p.derivative.derivative.eval x * q.eval x ≠ 0 := ne_of_gt hprod_pos
    dsimp [pp]
    exact (mul_ne_zero_iff.mp hprod_ne).1
  have hqx_ne : qx ≠ 0 := by
    simpa [qx] using hq_eval_ne
  let A : ℝ := pp * qx
  let B : ℝ := qp ^ 2 - qq * qx
  let δ₁ : ℝ := A / (2 * (|B| + 1))
  let δ₂ : ℝ := |pp| / (2 * (|qq| + 1))
  let β₀ : ℝ := min δ₁ δ₂
  let β : ℝ := min β₀ βmax
  have hA_pos : 0 < A := by
    simpa [A, pp, qx] using hprod_pos
  have hβ_pos : 0 < β := by
    dsimp [β, β₀, δ₁, δ₂, A, B]
    positivity
  have hβ_ne : β ≠ 0 := hβ_pos.ne'
  have hβ_le_β₀ : β ≤ β₀ := min_le_left _ _
  have hβ_le_δ₁ : β ≤ δ₁ := by
    exact le_trans hβ_le_β₀ (min_le_left _ _)
  have hβ_le_δ₂ : β ≤ δ₂ := by
    exact le_trans hβ_le_β₀ (min_le_right _ _)
  have hβ_le_max : β ≤ βmax := min_le_right _ _
  have hsecond_small : |β * qq| ≤ |pp| / 2 := by
    calc
      |β * qq| = β * |qq| := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hβ_pos)]
      _ ≤ β * (|qq| + 1) := by nlinarith [hβ_pos, abs_nonneg qq]
      _ ≤ δ₂ * (|qq| + 1) := by
        gcongr
      _ = |pp| / 2 := by
        dsimp [δ₂]
        field_simp
  have hcombo_der2_ne :
      (p.derivative.derivative.eval x + β * q.derivative.derivative.eval x) ≠ 0 := by
    intro hsum
    have hEq : pp = -(β * qq) := by
      linarith [hsum]
    have habs_eq : |pp| = |β * qq| := by
      rw [hEq, abs_neg]
    have hpp_abs_pos : 0 < |pp| := abs_pos.mpr hpp_ne
    rw [habs_eq] at hpp_abs_pos
    linarith
  have hcombo_nonzero :
      p + C β * q ≠ 0 := by
    intro hzero
    have heval := congrArg (fun r : ℝ[X] => r.eval x) hzero
    have heval0 : p.eval x + β * q.eval x = 0 := by
      simpa using heval
    have : β * q.eval x = 0 := by
      simpa [hp_eval0] using heval0
    exact hq_eval_ne ((mul_eq_zero.mp this).resolve_left hβ_ne)
  have hcombo_rr : IsRealRooted (p + C β * q) := hfamily hβ_pos hβ_le_max
  have hcombo_eval_ne :
      (p + C β * q).eval x ≠ 0 := by
    have heval :
        (p + C β * q).eval x = β * q.eval x := by
      simp [hp_eval0]
    rw [heval]
    exact mul_ne_zero hβ_ne hq_eval_ne
  have hcombo_deg_ge2 : 2 ≤ (p + C β * q).natDegree := by
    by_contra hlt
    have hdeg_lt2 : (p + C β * q).natDegree < 2 := by omega
    have hder2_zero : (derivative^[2]) (p + C β * q) = 0 :=
      iterate_derivative_eq_zero hdeg_lt2
    have hder2_eval_zero :
        (p + C β * q).derivative.derivative.eval x = 0 := by
      simpa [Function.iterate_succ_apply'] using congrArg (fun r : ℝ[X] => r.eval x) hder2_zero
    have : p.derivative.derivative.eval x + β * q.derivative.derivative.eval x = 0 := by
      simpa [derivative_add, derivative_C_mul] using hder2_eval_zero
    exact hcombo_der2_ne this
  have hineq_raw :=
    deriv2_mul_lt_deriv_sq_at_non_root hcombo_rr (by omega) hcombo_eval_ne
  have hineq : A < β * B := by
    dsimp [A, B, pp, qx, qp, qq]
    have hineq' := hineq_raw
    simp [hp_eval0, hp_der_eval0, derivative_add] at hineq'
    nlinarith [hβ_pos]
  have hβB_lt : β * |B| < A := by
    calc
      β * |B| ≤ β * (|B| + 1) := by
        nlinarith [hβ_pos, abs_nonneg B]
      _ ≤ δ₁ * (|B| + 1) := by
        gcongr
      _ = A / 2 := by
        dsimp [δ₁]
        field_simp
      _ < A := by linarith
  have hineq_le : β * B ≤ β * |B| := by
    have hB_le : B ≤ |B| := le_abs_self B
    nlinarith [hβ_pos, hB_le]
  exact (lt_irrefl A) (lt_of_lt_of_le hineq (le_trans hineq_le (le_of_lt hβB_lt)))

/-- Affine-family endpoint obstruction for an exact double root of `g`.

At a negative root `r`, the affine family contains the one-parameter right
families
`g + β * ((X - C r + C c) * f)` for every fixed `c > r`.  Choosing `c` so that
`c * g''(r) * f(r) > 0`, the bounded right-family double-root obstruction above
rules out an exact double root of `g` at `r` whenever `f(r) ≠ 0`. -/
private lemma false_of_affine_family_double_root
    {f g : ℝ[X]} {r : ℝ}
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hr_neg : r < 0)
    (hg_mult : g.rootMultiplicity r = 2)
    (hf_eval_ne : f.eval r ≠ 0) :
    False := by
  have hg0 : g ≠ 0 := by
    intro hg0
    simp [hg0] at hg_mult
  let G : ℝ := g.derivative.derivative.eval r * f.eval r
  have hG_ne : G ≠ 0 := by
    dsimp [G]
    exact mul_ne_zero
      (eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two_local hg0 hg_mult)
      hf_eval_ne
  by_cases hG_pos : 0 < G
  · let q : ℝ[X] := (X - C r + C (1 : ℝ)) * f
    have hfamily :
        ∀ {β : ℝ}, 0 < β → β ≤ 1 → IsRealRooted (g + C β * q) := by
      intro β hβ _hβ_le
      have hEq :
          g + C β * q =
            (((C β * X + C (β * (1 - r))) * f) + g) := by
        calc
          g + C β * q
              = g + C β * ((X - C r + C (1 : ℝ)) * f) := by rfl
          _ = g + ((C β * X + C (β * (1 - r))) * f) := by
                rw [show C β * ((X - C r + C (1 : ℝ)) * f) =
                    ((C β * X + C (β * (1 - r))) * f) by
                      calc
                        C β * ((X - C r + C (1 : ℝ)) * f)
                            = (C β * (X - C r + C (1 : ℝ))) * f := by rw [mul_assoc]
                        _ = (C β * X + C (β * (1 - r))) * f := by
                              ext n
                              simp [sub_eq_add_neg]
                              ring_nf]
          _ = (((C β * X + C (β * (1 - r))) * f) + g) := by
                rw [add_comm]
      have hβt_pos : 0 < β * (1 - r) := by
        have : 0 < 1 - r := by linarith
        positivity
      exact hEq ▸ haff hβ hβt_pos
    have hq_eval_ne : q.eval r ≠ 0 := by
      dsimp [q]
      rw [eval_mul]
      have hlin : (X - C r + C (1 : ℝ)).eval r = 1 := by
        simp
      rw [hlin, one_mul]
      exact hf_eval_ne
    have hprod_pos :
        0 < g.derivative.derivative.eval r * q.eval r := by
      dsimp [q, G] at hG_pos ⊢
      rw [eval_mul]
      have hlin : (X - C r + C (1 : ℝ)).eval r = 1 := by
        simp
      rw [hlin, one_mul]
      simpa using hG_pos
    exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := g) (q := q) (x := r) (βmax := 1)
        hfamily zero_lt_one hg_mult hq_eval_ne hprod_pos
  · let c : ℝ := r / 2
    let q : ℝ[X] := (X - C r + C c) * f
    have hc_gt_r : r < c := by
      dsimp [c]
      linarith
    have hc_neg : c < 0 := by
      dsimp [c]
      linarith
    have hfamily :
        ∀ {β : ℝ}, 0 < β → β ≤ 1 → IsRealRooted (g + C β * q) := by
      intro β hβ _hβ_le
      have hEq :
          g + C β * q =
            (((C β * X + C (β * (c - r))) * f) + g) := by
        calc
          g + C β * q
              = g + C β * ((X - C r + C c) * f) := by rfl
          _ = g + ((C β * X + C (β * (c - r))) * f) := by
                rw [show C β * ((X - C r + C c) * f) =
                    ((C β * X + C (β * (c - r))) * f) by
                      calc
                        C β * ((X - C r + C c) * f)
                            = (C β * (X - C r + C c)) * f := by rw [mul_assoc]
                        _ = (C β * X + C (β * (c - r))) * f := by
                              ext n
                              simp [sub_eq_add_neg]
                              ring_nf]
          _ = (((C β * X + C (β * (c - r))) * f) + g) := by
                rw [add_comm]
      have hβt_pos : 0 < β * (c - r) := by
        have : 0 < c - r := by linarith
        positivity
      exact hEq ▸ haff hβ hβt_pos
    have hq_eval_ne : q.eval r ≠ 0 := by
      dsimp [q, c]
      rw [eval_mul]
      have hlin : (X - C r + C (r / 2)).eval r = r / 2 := by
        simp
      rw [hlin]
      exact mul_ne_zero (by linarith) hf_eval_ne
    have hG_neg :
        G < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hG_pos) hG_ne
    have hprod_pos :
        0 < g.derivative.derivative.eval r * q.eval r := by
      have hcG_pos : 0 < c * G := by
        dsimp [c, G]
        nlinarith [hr_neg, hG_neg]
      dsimp [q, c]
      rw [eval_mul]
      have hlin : (X - C r + C (r / 2)).eval r = r / 2 := by
        simp
      rw [hlin]
      simpa [G, mul_assoc, mul_left_comm, mul_comm] using hcG_pos
    exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := g) (q := q) (x := r) (βmax := 1)
        hfamily zero_lt_one hg_mult hq_eval_ne hprod_pos

/-- In the succ-degree affine branch with `g(0) ≠ 0`, the endpoint polynomial
`g` itself has simple roots.

The proof is the endpoint analogue of the interior `iterateTDeriv` shortening
argument used below. If `g` had a multiple root at `r < 0`, we shorten its
multiplicity to an exact double root by a small `iterateTDeriv` run, while
keeping two affine companion families nonvanishing at `r`:
`(X - C r + 1) * f` and `(X - C r + C (r/2)) * f`. Their evaluations at `r`
have opposite signs, so after regularization one of them has the same sign as
the second derivative of the shortened endpoint, and the bounded affine-family
double-root obstruction applies. -/
private lemma hasSimpleRoots_right_of_affine_family_succDegree_not_isRoot_zero
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg_root0 : ¬ g.IsRoot 0) :
    HasSimpleRoots g := by
  have hg_rr : IsRealRooted g :=
    isRealRooted_right_of_affine_family_succDegree hf0 hg0 hfnn hgnn haff hsucc.symm
  have hno_right :
      ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r :=
    no_common_right_pair_of_no_common_of_not_isRoot_zero hno hg_root0
  intro r hgr
  by_contra hmult_ne
  have hmult_pos : 0 < g.rootMultiplicity r := by
    exact (rootMultiplicity_pos hg0).mpr hgr
  have hmult_ge2 : 2 ≤ g.rootMultiplicity r := by
    have hmult_ge1 : 1 ≤ g.rootMultiplicity r := Nat.succ_le_of_lt hmult_pos
    have hmult_not1 : g.rootMultiplicity r ≠ 1 := by
      simpa using hmult_ne
    omega
  have hr_mem : r ∈ g.roots := (mem_roots hg_rr.1).mpr hgr
  have hr_neg : r < 0 :=
    roots_strictly_neg_of_nonneg_of_no_common_right_pair
      hg_rr hgnn hno_right r hr_mem
  have hf_not_root : ¬ f.IsRoot r := hno r hgr
  have hf_eval_ne : f.eval r ≠ 0 := by
    simpa [Polynomial.IsRoot.def] using hf_not_root
  let m : ℕ := g.rootMultiplicity r
  let k : ℕ := m - 2
  let qPos : ℝ[X] := (X - C r + C (1 : ℝ)) * f
  let qNeg : ℝ[X] := (X - C r + C (r / 2)) * f
  have hqPos_eval : qPos.eval r = f.eval r := by
    dsimp [qPos]
    rw [eval_mul]
    have hlin : (X - C r + C (1 : ℝ)).eval r = 1 := by
      simp
    rw [hlin, one_mul]
  have hqNeg_eval : qNeg.eval r = (r / 2) * f.eval r := by
    dsimp [qNeg]
    rw [eval_mul]
    have hlin : (X - C r + C (r / 2)).eval r = r / 2 := by
      simp
    rw [hlin]
  have hqPos_eval_ne : qPos.eval r ≠ 0 := by
    rw [hqPos_eval]
    exact hf_eval_ne
  have hqNeg_eval_ne : qNeg.eval r ≠ 0 := by
    rw [hqNeg_eval]
    exact mul_ne_zero (by linarith) hf_eval_ne
  obtain ⟨δPos, hδPos, hqPos_keep⟩ :=
    exists_delta_eval_mul_pos_iterateTDeriv_at_zero k
      (p := qPos) (x := r) hqPos_eval_ne
  obtain ⟨δNeg, hδNeg, hqNeg_keep⟩ :=
    exists_delta_eval_mul_pos_iterateTDeriv_at_zero k
      (p := qNeg) (x := r) hqNeg_eval_ne
  let η : ℝ := min δPos δNeg / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hη_smallPos : ‖η‖ < δPos := by
    have hη_norm : ‖η‖ = min δPos δNeg / 2 := by
      rw [Real.norm_eq_abs, show η = min δPos δNeg / 2 by rfl, abs_of_pos hη_pos]
    rw [hη_norm]
    have hmin_pos : 0 < min δPos δNeg := lt_min hδPos hδNeg
    have hhalf_lt : min δPos δNeg / 2 < min δPos δNeg := by
      nlinarith
    exact lt_of_lt_of_le hhalf_lt (min_le_left _ _)
  have hη_smallNeg : ‖η‖ < δNeg := by
    have hη_norm : ‖η‖ = min δPos δNeg / 2 := by
      rw [Real.norm_eq_abs, show η = min δPos δNeg / 2 by rfl, abs_of_pos hη_pos]
    rw [hη_norm]
    have hmin_pos : 0 < min δPos δNeg := lt_min hδPos hδNeg
    have hhalf_lt : min δPos δNeg / 2 < min δPos δNeg := by
      nlinarith
    exact lt_of_lt_of_le hhalf_lt (min_le_right _ _)
  let pη : ℝ[X] := iterateTDeriv η k g
  let qPosη : ℝ[X] := iterateTDeriv η k qPos
  let qNegη : ℝ[X] := iterateTDeriv η k qNeg
  have hk_le : k ≤ g.rootMultiplicity r := by
    dsimp [k, m]
    omega
  have hpη_mult : pη.rootMultiplicity r = 2 := by
    calc
      pη.rootMultiplicity r = g.rootMultiplicity r - k := by
        dsimp [pη]
        exact rootMultiplicity_iterateTDeriv_eq_tsub hη_pos hg_rr hk_le
      _ = 2 := by
        dsimp [k, m]
        omega
  have hpη_rr : IsRealRooted pη := by
    dsimp [pη]
    exact isRealRooted_iterateTDeriv hη_pos hg_rr
  have hpη_ne : pη ≠ 0 := hpη_rr.1
  have hpp_ne : pη.derivative.derivative.eval r ≠ 0 := by
    exact
      eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two_local
        hpη_ne hpη_mult
  have hqPosη_keep :
      0 < qPosη.eval r * qPos.eval r := by
    dsimp [qPosη]
    exact hqPos_keep hη_smallPos
  have hqNegη_keep :
      0 < qNegη.eval r * qNeg.eval r := by
    dsimp [qNegη]
    exact hqNeg_keep hη_smallNeg
  have hqPosη_eval_ne : qPosη.eval r ≠ 0 := by
    have : qPosη.eval r * qPos.eval r ≠ 0 := ne_of_gt hqPosη_keep
    exact (mul_ne_zero_iff.mp this).1
  have hqNegη_eval_ne : qNegη.eval r ≠ 0 := by
    have : qNegη.eval r * qNeg.eval r ≠ 0 := ne_of_gt hqNegη_keep
    exact (mul_ne_zero_iff.mp this).1
  have hqOpp :
      qPosη.eval r * qNegη.eval r < 0 := by
    by_cases hqPos_pos : 0 < qPos.eval r
    · have hqPosη_pos : 0 < qPosη.eval r := by
        nlinarith [hqPosη_keep, hqPos_pos]
      have hqNeg_neg : qNeg.eval r < 0 := by
        rw [hqNeg_eval, hqPos_eval] at *
        nlinarith [hr_neg, hqPos_pos]
      have hqNegη_neg : qNegη.eval r < 0 := by
        nlinarith [hqNegη_keep, hqNeg_neg]
      exact mul_neg_of_pos_of_neg hqPosη_pos hqNegη_neg
    · have hqPos_neg : qPos.eval r < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hqPos_pos) hqPos_eval_ne
      have hqPosη_neg : qPosη.eval r < 0 := by
        nlinarith [hqPosη_keep, hqPos_neg]
      have hqNeg_pos : 0 < qNeg.eval r := by
        rw [hqNeg_eval, hqPos_eval] at *
        nlinarith [hr_neg, hqPos_neg]
      have hqNegη_pos : 0 < qNegη.eval r := by
        nlinarith [hqNegη_keep, hqNeg_pos]
      exact mul_neg_of_neg_of_pos hqPosη_neg hqNegη_pos
  have hfamilyPos :
      ∀ {β : ℝ}, 0 < β → β ≤ 1 → IsRealRooted (g + C β * qPos) := by
    intro β hβ _hβ_le
    have hEq :
        g + C β * qPos =
          (((C β * X + C (β * (1 - r))) * f) + g) := by
      calc
        g + C β * qPos
            = g + C β * ((X - C r + C (1 : ℝ)) * f) := by rfl
        _ = g + ((C β * X + C (β * (1 - r))) * f) := by
              rw [show C β * ((X - C r + C (1 : ℝ)) * f) =
                  ((C β * X + C (β * (1 - r))) * f) by
                    calc
                      C β * ((X - C r + C (1 : ℝ)) * f)
                          = (C β * (X - C r + C (1 : ℝ))) * f := by rw [mul_assoc]
                      _ = (C β * X + C (β * (1 - r))) * f := by
                            ext n
                            simp [sub_eq_add_neg]
                            ring_nf]
        _ = (((C β * X + C (β * (1 - r))) * f) + g) := by
              rw [add_comm]
    have hβt_pos : 0 < β * (1 - r) := by
      have : 0 < 1 - r := by linarith
      positivity
    exact hEq ▸ haff hβ hβt_pos
  have hfamilyNeg :
      ∀ {β : ℝ}, 0 < β → β ≤ 1 → IsRealRooted (g + C β * qNeg) := by
    intro β hβ _hβ_le
    have hEq :
        g + C β * qNeg =
          (((C β * X + C (β * (r / 2 - r))) * f) + g) := by
      calc
        g + C β * qNeg
            = g + C β * ((X - C r + C (r / 2)) * f) := by rfl
        _ = g + ((C β * X + C (β * (r / 2 - r))) * f) := by
              rw [show C β * ((X - C r + C (r / 2)) * f) =
                  ((C β * X + C (β * (r / 2 - r))) * f) by
                    calc
                      C β * ((X - C r + C (r / 2)) * f)
                          = (C β * (X - C r + C (r / 2))) * f := by rw [mul_assoc]
                      _ = (C β * X + C (β * (r / 2 - r))) * f := by
                            ext n
                            simp [sub_eq_add_neg]
                            ring_nf]
        _ = (((C β * X + C (β * (r / 2 - r))) * f) + g) := by
              rw [add_comm]
    have hβt_pos : 0 < β * (r / 2 - r) := by
      have : 0 < r / 2 - r := by linarith
      positivity
    exact hEq ▸ haff hβ hβt_pos
  have hfamilyPosη :
      ∀ {β : ℝ}, 0 < β → β ≤ 1 → IsRealRooted (pη + C β * qPosη) := by
    intro β hβ hβ_le
    have hrr : IsRealRooted (g + C β * qPos) := hfamilyPos hβ hβ_le
    have hiter :
        IsRealRooted (iterateTDeriv η k (g + C β * qPos)) := by
      exact isRealRooted_iterateTDeriv hη_pos hrr
    have hEq :
        pη + C β * qPosη = iterateTDeriv η k (g + C β * qPos) := by
      dsimp [pη, qPosη]
      rw [iterateTDeriv_add, iterateTDeriv_C_mul]
    exact hEq ▸ hiter
  have hfamilyNegη :
      ∀ {β : ℝ}, 0 < β → β ≤ 1 → IsRealRooted (pη + C β * qNegη) := by
    intro β hβ hβ_le
    have hrr : IsRealRooted (g + C β * qNeg) := hfamilyNeg hβ hβ_le
    have hiter :
        IsRealRooted (iterateTDeriv η k (g + C β * qNeg)) := by
      exact isRealRooted_iterateTDeriv hη_pos hrr
    have hEq :
        pη + C β * qNegη = iterateTDeriv η k (g + C β * qNeg) := by
      dsimp [pη, qNegη]
      rw [iterateTDeriv_add, iterateTDeriv_C_mul]
    exact hEq ▸ hiter
  by_cases hprodPos :
      0 < pη.derivative.derivative.eval r * qPosη.eval r
  · exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := pη) (q := qPosη) (x := r) (βmax := 1)
        hfamilyPosη zero_lt_one hpη_mult hqPosη_eval_ne hprodPos
  · have hprodPos_ne :
      pη.derivative.derivative.eval r * qPosη.eval r ≠ 0 := by
      exact mul_ne_zero hpp_ne hqPosη_eval_ne
    have hprodPos_neg :
        pη.derivative.derivative.eval r * qPosη.eval r < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hprodPos) hprodPos_ne
    by_cases hqPosη_pos : 0 < qPosη.eval r
    · have hqNegη_neg : qNegη.eval r < 0 := by
        have hqNegη_ne : qNegη.eval r ≠ 0 := hqNegη_eval_ne
        have hqNegη_not_pos : ¬ 0 < qNegη.eval r := by
          intro hqNegη_pos
          exact (not_lt_of_ge (le_of_lt hqOpp)) (mul_pos hqPosη_pos hqNegη_pos)
        exact lt_of_le_of_ne (le_of_not_gt hqNegη_not_pos) hqNegη_ne
      have hpp_neg : pη.derivative.derivative.eval r < 0 := by
        nlinarith [hprodPos_neg, hqPosη_pos]
      have hprodNeg_pos :
          0 < pη.derivative.derivative.eval r * qNegη.eval r := by
        exact mul_pos_of_neg_of_neg hpp_neg hqNegη_neg
      exact
        false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
          (p := pη) (q := qNegη) (x := r) (βmax := 1)
          hfamilyNegη zero_lt_one hpη_mult hqNegη_eval_ne hprodNeg_pos
    · have hqPosη_neg : qPosη.eval r < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hqPosη_pos) hqPosη_eval_ne
      have hqNegη_pos : 0 < qNegη.eval r := by
        have hqNegη_ne : qNegη.eval r ≠ 0 := hqNegη_eval_ne
        have hqNegη_not_neg : ¬ qNegη.eval r < 0 := by
          intro hqNegη_neg
          exact (not_lt_of_ge (le_of_lt hqOpp)) (mul_pos_of_neg_of_neg hqPosη_neg hqNegη_neg)
        exact lt_of_le_of_ne (le_of_not_gt hqNegη_not_neg) (by simpa [eq_comm] using hqNegη_ne)
      have hpp_pos : 0 < pη.derivative.derivative.eval r := by
        nlinarith [hprodPos_neg, hqPosη_neg]
      have hprodNeg_pos :
          0 < pη.derivative.derivative.eval r * qNegη.eval r := by
        exact mul_pos hpp_pos hqNegη_pos
      exact
        false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
          (p := pη) (q := qNegη) (x := r) (βmax := 1)
          hfamilyNegη zero_lt_one hpη_mult hqNegη_eval_ne hprodNeg_pos

private lemma roots_nodup_of_hasSimpleRoots
    {p : ℝ[X]} (hp0 : p ≠ 0) (hsimple : HasSimpleRoots p) :
    p.roots.Nodup := by
  refine Multiset.nodup_iff_count_le_one.mpr ?_
  intro r
  rw [count_roots (a := r) p]
  by_cases hr : p.IsRoot r
  · simp [hsimple r hr]
  · have hmult0 : p.rootMultiplicity r = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact hr ((rootMultiplicity_pos hp0).mp hpos)
    simp [hmult0]

private lemma roots_sort_sortedLT_of_hasSimpleRoots
    {p : ℝ[X]} (hp0 : p ≠ 0) (hsimple : HasSimpleRoots p) :
    (p.roots.sort (· ≤ ·)).SortedLT := by
  have hsorted : (p.roots.sort (· ≤ ·)).SortedLE := by
    simpa using (Multiset.pairwise_sort (s := p.roots) (r := (· ≤ ·))).sortedLE
  have hnodup : (p.roots.sort (· ≤ ·)).Nodup := by
    apply Multiset.coe_nodup.mp
    simpa using roots_nodup_of_hasSimpleRoots hp0 hsimple
  exact hsorted.sortedLT_of_nodup hnodup

/-- Exact double roots are impossible in interior positive combinations of a
positive-combination real-rooted family. This is the local obstruction that the
affine-family frontier can use without leaving the positive cone. -/
private lemma rootMultiplicity_ne_two_add_right_of_posComboRealRooted
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {μ x : ℝ}
    (hμ : 0 < μ) :
    (f + C μ * g).rootMultiplicity x ≠ 2 := by
  intro hmult
  have hp_root : (f + C μ * g).IsRoot x := by
    exact (rootMultiplicity_pos (show f + C μ * g ≠ 0 from
      (PosComboRealRooted.isRealRooted_add_right hfg hμ).1)).mp (by simp [hmult])
  have hg_eval_ne : g.eval x ≠ 0 := by
    intro hg0
    have hp_eval0 : (f + C μ * g).eval x = 0 := by
      simpa [Polynomial.IsRoot.def] using hp_root
    have hf0 : f.eval x = 0 := by
      simp [eval_add, eval_mul, hg0] at hp_eval0
      linarith
    exact hno x
      (by simpa [Polynomial.IsRoot.def] using hf0)
      (by simpa [Polynomial.IsRoot.def] using hg0)
  by_cases hprod_pos :
      0 < (f + C μ * g).derivative.derivative.eval x * g.eval x
  · exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := f + C μ * g) (q := g) (x := x) (βmax := 1)
        (by
          intro β hβ hβ_le
          have hμβ : 0 < μ + β := by linarith
          have hrr := PosComboRealRooted.isRealRooted_add_right hfg hμβ
          have hEq : (f + C μ * g) + C β * g = f + C (μ + β) * g := by
            calc
              (f + C μ * g) + C β * g = f + (C μ * g + C β * g) := by
                simp [add_assoc]
              _ = f + (C μ + C β) * g := by
                rw [← add_mul]
              _ = f + C (μ + β) * g := by
                rw [← C_add]
          simpa [hEq] using hrr)
        zero_lt_one hmult hg_eval_ne hprod_pos
  · have hpp_ne :
        (f + C μ * g).derivative.derivative.eval x ≠ 0 := by
      exact
        eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two_local
          (show f + C μ * g ≠ 0 from (PosComboRealRooted.isRealRooted_add_right hfg hμ).1)
          hmult
    have hprod_ne :
        (f + C μ * g).derivative.derivative.eval x * g.eval x ≠ 0 :=
      mul_ne_zero hpp_ne hg_eval_ne
    have hprod_neg :
        (f + C μ * g).derivative.derivative.eval x * g.eval x < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hprod_pos) hprod_ne
    have hneg_eval_ne : (-g).eval x ≠ 0 := by
      simpa [Polynomial.eval_neg] using neg_ne_zero.mpr hg_eval_ne
    have hneg_pos :
        0 < (f + C μ * g).derivative.derivative.eval x * (-g).eval x := by
      simpa [Polynomial.eval_neg] using neg_pos.mpr hprod_neg
    exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := f + C μ * g) (q := -g) (x := x) (βmax := μ / 2)
        (by
          intro β hβ hβ_le
          have hμβ : 0 < μ - β := by linarith
          have hrr := PosComboRealRooted.isRealRooted_add_right hfg hμβ
          have hEq : (f + C μ * g) + C β * (-g) = f + (C μ - C β) * g := by
            calc
              (f + C μ * g) + C β * (-g) = f + (C μ * g + C β * (-g)) := by
                simp [add_assoc]
              _ = f + (C μ * g - C β * g) := by
                simp [sub_eq_add_neg]
              _ = f + (C μ - C β) * g := by
                rw [← sub_mul]
          have hrr' : IsRealRooted (f + (C μ - C β) * g) := by
            simpa [C_sub] using hrr
          exact hEq ▸ hrr')
        (by positivity) hmult hneg_eval_ne hneg_pos

/-- Every interior positive combination of a no-common positive-combination
family has simple roots.

This is the exact `iterateTDeriv`-shortening step from the completed
Obreschkoff converse, specialized to the positive cone: if
`p = f + C μ * g` had a multiple root at `x`, keep `g` nonvanishing at `x`
along a short `iterateTDeriv` run, shorten the multiplicity of `p` until it
becomes exactly `2`, and then contradict the exact-double-root obstruction
above. -/
private lemma hasSimpleRoots_add_right_of_posComboRealRooted
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {μ : ℝ}
    (hμ : 0 < μ) :
    HasSimpleRoots (f + C μ * g) := by
  let p : ℝ[X] := f + C μ * g
  have hp_rr : IsRealRooted p := PosComboRealRooted.isRealRooted_add_right hfg hμ
  have hp_ne : p ≠ 0 := hp_rr.1
  intro x hx
  by_contra hmult_ne
  have hmult_pos : 0 < p.rootMultiplicity x := by
    exact (rootMultiplicity_pos hp_ne).mpr (by simpa [p] using hx)
  have hmult_gt : 1 < p.rootMultiplicity x := by
    exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hmult_pos) (Ne.symm hmult_ne)
  have hg_not_root : ¬ g.IsRoot x := by
    intro hgx
    have hp_eval0 : p.eval x = 0 := by
      simpa [p, Polynomial.IsRoot.def] using hx
    have hg_eval0 : g.eval x = 0 := by
      simpa [Polynomial.IsRoot.def] using hgx
    have hf_eval0 : f.eval x = 0 := by
      simp [p, eval_add, eval_mul, hg_eval0] at hp_eval0
      linarith
    exact hno x
      (by simpa [Polynomial.IsRoot.def] using hf_eval0)
      hgx
  let m : ℕ := p.rootMultiplicity x
  let k : ℕ := m - 2
  obtain ⟨δ, hδ, hgk_not_root⟩ :=
    exists_delta_not_isRoot_iterateTDeriv_at_point k hg_not_root
  let η : ℝ := δ / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  have hη_small : ‖η‖ < δ := by
    have hη_norm : ‖η‖ = δ / 2 := by
      rw [Real.norm_eq_abs, show η = δ / 2 by rfl, abs_of_pos hη_pos]
    rw [hη_norm]
    linarith
  have hgk_not_root_x : ¬ (iterateTDeriv η k g).IsRoot x := hgk_not_root hη_small
  have hgk_eval_ne : (iterateTDeriv η k g).eval x ≠ 0 := by
    simpa [Polynomial.IsRoot.def] using hgk_not_root_x
  have hk_le : k ≤ p.rootMultiplicity x := by
    dsimp [k, m]
    omega
  have hpk_mult :
      (iterateTDeriv η k p).rootMultiplicity x = 2 := by
    calc
      (iterateTDeriv η k p).rootMultiplicity x = p.rootMultiplicity x - k := by
        exact rootMultiplicity_iterateTDeriv_eq_tsub hη_pos hp_rr hk_le
      _ = 2 := by
        dsimp [k, m]
        omega
  let pη : ℝ[X] := iterateTDeriv η k p
  let gη : ℝ[X] := iterateTDeriv η k g
  have hpη_eq :
      pη = iterateTDeriv η k f + C μ * gη := by
    dsimp [pη, p, gη]
    rw [iterateTDeriv_add, iterateTDeriv_C_mul]
  by_cases hprod_pos :
      0 < pη.derivative.derivative.eval x * gη.eval x
  · exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := pη) (q := gη) (x := x) (βmax := 1)
        (by
          intro β hβ _hβ_le
          have hμβ : 0 < μ + β := by linarith
          have hrr := PosComboRealRooted.isRealRooted_add_right hfg hμβ
          have hiter :
              IsRealRooted (iterateTDeriv η k (f + C (μ + β) * g)) := by
            exact isRealRooted_iterateTDeriv (eps := η) (k := k) hη_pos hrr
          have hEq : pη + C β * gη = iterateTDeriv η k (f + C (μ + β) * g) := by
            calc
              pη + C β * gη
                  = (iterateTDeriv η k f + C μ * gη) + C β * gη := by
                      rw [hpη_eq]
              _ = iterateTDeriv η k f + (C μ * gη + C β * gη) := by
                    simp [add_assoc]
              _ = iterateTDeriv η k f + (C μ + C β) * gη := by
                    rw [← add_mul]
              _ = iterateTDeriv η k f + C (μ + β) * gη := by
                    rw [← C_add]
              _ = iterateTDeriv η k (f + C (μ + β) * g) := by
                    rw [iterateTDeriv_add, iterateTDeriv_C_mul]
          exact hEq ▸ hiter)
        zero_lt_one hpk_mult hgk_eval_ne hprod_pos
  · have hpη_rr : IsRealRooted pη := by
      exact
        isRealRooted_iterateTDeriv (eps := η) (k := k) hη_pos
          (by simpa [p] using PosComboRealRooted.isRealRooted_add_right hfg hμ)
    have hpη_ne : pη ≠ 0 := hpη_rr.1
    have hpηpp_ne :
        pη.derivative.derivative.eval x ≠ 0 := by
      exact
        eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two_local
          hpη_ne hpk_mult
    have hprod_ne :
        pη.derivative.derivative.eval x * gη.eval x ≠ 0 :=
      mul_ne_zero hpηpp_ne hgk_eval_ne
    have hprod_neg :
        pη.derivative.derivative.eval x * gη.eval x < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hprod_pos) hprod_ne
    have hneg_eval_ne : (-gη).eval x ≠ 0 := by
      simpa [Polynomial.eval_neg] using neg_ne_zero.mpr hgk_eval_ne
    have hneg_pos :
        0 < pη.derivative.derivative.eval x * (-gη).eval x := by
      simpa [Polynomial.eval_neg] using neg_pos.mpr hprod_neg
    exact
      false_of_bounded_right_family_of_double_root_and_eval_ne_of_pos
        (p := pη) (q := -gη) (x := x) (βmax := μ / 2)
        (by
          intro β hβ hβ_le
          have hμβ : 0 < μ - β := by linarith
          have hrr := PosComboRealRooted.isRealRooted_add_right hfg hμβ
          have hiter :
              IsRealRooted (iterateTDeriv η k (f + C (μ - β) * g)) := by
            exact isRealRooted_iterateTDeriv (eps := η) (k := k) hη_pos hrr
          have hEq : pη + C β * (-gη) = iterateTDeriv η k (f + C (μ - β) * g) := by
            calc
              pη + C β * (-gη)
                  = (iterateTDeriv η k f + C μ * gη) + C β * (-gη) := by
                      rw [hpη_eq]
              _ = iterateTDeriv η k f + (C μ * gη + C β * (-gη)) := by
                    simp [add_assoc]
              _ = iterateTDeriv η k f + (C μ * gη - C β * gη) := by
                    simp [sub_eq_add_neg]
              _ = iterateTDeriv η k f + (C μ - C β) * gη := by
                    rw [← sub_mul]
              _ = iterateTDeriv η k f + C (μ - β) * gη := by
                    rw [C_sub]
              _ = iterateTDeriv η k (f + C (μ - β) * g) := by
                    rw [iterateTDeriv_add, iterateTDeriv_C_mul]
          exact hEq ▸ hiter)
        (by positivity) hpk_mult hneg_eval_ne hneg_pos

/-- In a one-parameter boundary family `g + t f`, a Wronskian-zero point where
`g` and `f` have opposite signs would force an interior double root. Hence the
Wronskian cannot vanish on the positive-level set of the ratio `-g / f`. -/
private lemma wronskian_eval_ne_zero_of_add_left_family_of_no_common
    {f g : ℝ[X]}
    (hfamily : ∀ {t : ℝ}, 0 < t → IsRealRooted (C t * f + g))
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    {x : ℝ}
    (hopp : g.eval x * f.eval x < 0) :
    f.derivative.eval x * g.eval x - f.eval x * g.derivative.eval x ≠ 0 := by
  have hf_eval_ne : f.eval x ≠ 0 := by
    exact fun hfx => by simpa [hfx] using hopp.ne
  have hg_eval_ne : g.eval x ≠ 0 := by
    exact fun hgx => by simpa [hgx] using hopp.ne
  let t : ℝ := -(g.eval x / f.eval x)
  have ht_pos : 0 < t := by
    have hnum_pos : 0 < -(g.eval x * f.eval x) := by
      linarith
    have hmul_pos : 0 < t * (f.eval x) ^ 2 := by
      dsimp [t]
      have hcalc :
          -(g.eval x / f.eval x) * (f.eval x) ^ 2 = -(g.eval x * f.eval x) := by
        field_simp [hf_eval_ne]
      simpa [hcalc]
        using hnum_pos
    have hsq_nonneg : 0 ≤ (f.eval x) ^ 2 := sq_nonneg _
    nlinarith
  have hcombo : PosComboRealRooted g f := by
    rw [PosComboRealRooted.iff_add_right]
    intro μ hμ
    simpa [add_comm] using hfamily hμ
  have hsimple : HasSimpleRoots (g + C t * f) := by
    exact
      hasSimpleRoots_add_right_of_posComboRealRooted
        hcombo hno ht_pos
  have hp_rr : IsRealRooted (g + C t * f) := by
    simpa [add_comm] using hfamily ht_pos
  have hp_root : (g + C t * f).IsRoot x := by
    rw [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C]
    dsimp [t]
    field_simp [hf_eval_ne]
    ring
  intro hW
  have hp_der_root : (g + C t * f).derivative.IsRoot x := by
    rw [Polynomial.IsRoot.def, derivative_add, derivative_C_mul,
      eval_add, eval_mul, eval_C]
    dsimp [t]
    field_simp [hf_eval_ne]
    nlinarith [hW]
  have hp_ne : g + C t * f ≠ 0 := hp_rr.1
  have hmult :
      1 < (g + C t * f).rootMultiplicity x := by
    exact (one_lt_rootMultiplicity_iff_isRoot hp_ne).2 ⟨hp_root, hp_der_root⟩
  rw [hsimple x hp_root] at hmult
  omega

/-- Derivative of the boundary ratio `x ↦ -g(x) / f(x)` at a point where
`f(x) ≠ 0`, rewritten in the Wronskian form natural for the affine-family
arguments. -/
private lemma hasDerivAt_neg_eval_div_eval
    {f g : ℝ[X]} {x : ℝ}
    (hf_eval_ne : f.eval x ≠ 0) :
    HasDerivAt (fun y : ℝ => -(g.eval y / f.eval y))
      ((f.derivative.eval x * g.eval x - f.eval x * g.derivative.eval x) / (f.eval x)^2) x := by
  have hg' : HasDerivAt (fun y : ℝ => g.eval y) (g.derivative.eval x) x := by
    simpa using (g.differentiable.differentiableAt.hasDerivAt)
  have hf' : HasDerivAt (fun y : ℝ => f.eval y) (f.derivative.eval x) x := by
    simpa using (f.differentiable.differentiableAt.hasDerivAt)
  have hdiv : HasDerivAt (fun y : ℝ => g.eval y / f.eval y)
      ((g.derivative.eval x * f.eval x - g.eval x * f.derivative.eval x) / (f.eval x)^2) x :=
    hg'.div hf' hf_eval_ne
  convert hdiv.neg using 1
  ring

/-- Any local extremum of the positive-level ratio `x ↦ -g(x) / f(x)` forces the
Wronskian numerator to vanish. This is the analytic form of the usual "critical
point of the ratio" obstruction. -/
private lemma wronskian_eq_zero_of_localExtr_neg_eval_div_eval
    {f g : ℝ[X]} {x : ℝ}
    (hlocal : IsLocalExtr (fun y : ℝ => -(g.eval y / f.eval y)) x)
    (hf_eval_ne : f.eval x ≠ 0) :
    f.derivative.eval x * g.eval x - f.eval x * g.derivative.eval x = 0 := by
  have hderiv := hasDerivAt_neg_eval_div_eval (f := f) (g := g) hf_eval_ne
  have hzero := hlocal.hasDerivAt_eq_zero hderiv
  field_simp [hf_eval_ne] at hzero
  linarith

/-- In a one-parameter affine boundary family, the positive ratio
`x ↦ -g(x) / f(x)` cannot have an interior local extremum: that would force a
Wronskian zero at a point where `g(x)` and `f(x)` already have opposite signs,
contradicting `wronskian_eval_ne_zero_of_add_left_family_of_no_common`. -/
private lemma false_of_localExtr_neg_eval_div_eval_pos_of_add_left_family_of_no_common
    {f g : ℝ[X]}
    (hfamily : ∀ {t : ℝ}, 0 < t → IsRealRooted (C t * f + g))
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    {x : ℝ}
    (hlocal : IsLocalExtr (fun y : ℝ => -(g.eval y / f.eval y)) x)
    (hpos : 0 < -(g.eval x / f.eval x)) :
    False := by
  have hf_eval_ne : f.eval x ≠ 0 := by
    intro hfx
    simp [hfx] at hpos
  have hopp : g.eval x * f.eval x < 0 := by
    have hsq_pos : 0 < (f.eval x)^2 := sq_pos_of_ne_zero hf_eval_ne
    have hcalc :
        (-(g.eval x / f.eval x)) * (f.eval x)^2 = -(g.eval x * f.eval x) := by
      field_simp [hf_eval_ne]
    have hnum_pos : 0 < -(g.eval x * f.eval x) := by
      simpa [hcalc] using mul_pos hpos hsq_pos
    nlinarith
  have hW_zero : f.derivative.eval x * g.eval x - f.eval x * g.derivative.eval x = 0 :=
    wronskian_eq_zero_of_localExtr_neg_eval_div_eval (f := f) (g := g) hlocal hf_eval_ne
  exact (wronskian_eval_ne_zero_of_add_left_family_of_no_common hfamily hno hopp) hW_zero

private lemma pairwise_suffix {α : Type*} {R : α → α → Prop} :
    ∀ pre suf : List α, (pre ++ suf).Pairwise R → suf.Pairwise R
  | [], suf, h => by simpa using h
  | _ :: pre, suf, h => by
      simpa [List.cons_append] using
        pairwise_suffix pre suf (List.Pairwise.tail h)

private lemma consecNoRoots_tail {p : ℝ[X]} {a : ℝ} {l : List ℝ} :
    ConsecNoRoots p (a :: l) → ConsecNoRoots p l := by
  cases l with
  | nil =>
      intro _
      trivial
  | cons b rest =>
      intro h
      exact h.2

private lemma consecNoRoots_suffix {p : ℝ[X]} :
    ∀ pre suf : List ℝ, ConsecNoRoots p (pre ++ suf) → ConsecNoRoots p suf
  | [], suf, h => by simpa using h
  | _ :: pre, suf, h => by
      simpa [List.cons_append] using
        consecNoRoots_suffix pre suf (consecNoRoots_tail h)

private lemma pos_neg_div_of_mul_neg {a b : ℝ}
    (hb : b ≠ 0) (hab : a * b < 0) :
    0 < -(a / b) := by
  have hsq_pos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hcalc : (-(a / b)) * b ^ 2 = -(a * b) := by
    field_simp [hb]
  have hnum_pos : 0 < -(a * b) := by
    nlinarith
  have hmul_pos : 0 < (-(a / b)) * b ^ 2 := by
    simpa [hcalc] using hnum_pos
  nlinarith

/-- Recursive root-picker: if a polynomial `F` has a root strictly between each
consecutive pair of a sorted real list `rs`, we can package these roots as a
strictly sorted interlacing list. -/
private theorem exists_roots_strictly_interlacing_of_consecutive_exists {F : ℝ[X]} :
    ∀ (rs : List ℝ),
      rs.Pairwise (· ≤ ·) →
      (∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        ∃ u, r₁ < u ∧ u < r₂ ∧ F.IsRoot u) →
      ∃ us : List ℝ, us.length = rs.length - 1 ∧
        ListInterlaces us rs ∧
        (∀ u ∈ us, F.IsRoot u) ∧
        us.Pairwise (· < ·)
  | [], _, _ => by
      refine ⟨[], by simp, ?_, ?_, ?_⟩
      · simp [ListInterlaces]
      · simp
      · exact List.Pairwise.nil
  | [_], _, _ => by
      refine ⟨[], by simp, ?_, ?_, ?_⟩
      · simp [ListInterlaces]
      · simp
      · exact List.Pairwise.nil
  | r₁ :: r₂ :: rest, hrs_sorted, hexists => by
      obtain ⟨u, hu₁, hu₂, hu_root⟩ := hexists [] rfl
      have htail_sorted : (r₂ :: rest).Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp hrs_sorted).2
      obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
        exists_roots_strictly_interlacing_of_consecutive_exists
          (F := F) (r₂ :: rest) htail_sorted
          (fun pre {a b tail} hEq => by
            have hEq' : r₁ :: r₂ :: rest = (r₁ :: pre) ++ a :: b :: tail := by
              simp [List.cons_append, hEq]
            simpa using hexists (r₁ :: pre) hEq')
      have hu_lt_all : ∀ w ∈ us, u < w := by
        intro w hw
        exact lt_of_lt_of_le hu₂ (listInterlaces_all_ge us rest r₂ hus_int w hw)
      refine ⟨u :: us, ?_, ?_, ?_, ?_⟩
      · simp [hus_len]
      · exact ⟨le_of_lt hu₁, le_of_lt hu₂, hus_int⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv'
        · exact hu_root
        · exact hus_roots v hv'
      · exact List.pairwise_cons.mpr ⟨hu_lt_all, hus_pw⟩

/-- In the hard succ-degree affine branch with `g(0) ≠ 0`, every open interval
between consecutive roots of `g` contains a root of `f`. The proof uses the
boundary-ratio obstruction: if such an interval were root-free for `f`, then
one of the positive ratios `-g/f` or `-g/(X*f)` would have equal endpoint values
and a positive interior local extremum, contradicting the Wronskian lemma. -/
private lemma exists_f_root_between_consecutive_g_roots_of_affine_family_succDegree_not_isRoot_zero
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg_root0 : ¬ g.IsRoot 0)
    {r₁ r₂ : ℝ}
    (hr₁ : g.IsRoot r₁) (hr₂ : g.IsRoot r₂)
    (hr₁r₂ : r₁ < r₂)
    (hno_between_g : ∀ r ∈ g.roots, ¬ (r₁ < r ∧ r < r₂)) :
    ∃ u, r₁ < u ∧ u < r₂ ∧ f.IsRoot u := by
  have hg_rr : IsRealRooted g :=
    isRealRooted_right_of_affine_family_succDegree hf0 hg0 hfnn hgnn haff hsucc.symm
  have hXf_pos : HasPosLeadingCoeff (X * f) :=
    (hasNonnegCoeffs_X.mul hfnn).pos_leadingCoeff (mul_ne_zero X_ne_zero hf0)
  have hposcombo : PosComboRealRooted g (X * f) :=
    posComboRealRooted_right_of_affine_family hf0 hg0 hfnn hgnn haff
  have hno_right :
      ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r :=
    no_common_right_pair_of_no_common_of_not_isRoot_zero hno hg_root0
  have hr₁_mem : r₁ ∈ g.roots := (mem_roots hg0).mpr hr₁
  have hr₂_mem : r₂ ∈ g.roots := (mem_roots hg0).mpr hr₂
  have hr₁_neg : r₁ < 0 :=
    roots_strictly_neg_of_nonneg_of_no_common_right_pair
      hg_rr hgnn hno_right r₁ hr₁_mem
  have hr₂_neg : r₂ < 0 :=
    roots_strictly_neg_of_nonneg_of_no_common_right_pair
      hg_rr hgnn hno_right r₂ hr₂_mem
  let m : ℝ := (r₁ + r₂) / 2
  have hm_mem : m ∈ Set.Ioo r₁ r₂ := by
    dsimp [m]
    constructor <;> nlinarith
  by_contra hexists
  push Not at hexists
  have hg_mid_ne : g.eval m ≠ 0 := by
    intro hgm
    have hroot : g.IsRoot m := by
      simpa [Polynomial.IsRoot.def] using hgm
    exact hno_between_g m ((mem_roots hg0).mpr hroot) hm_mem
  have hf_mid_ne : f.eval m ≠ 0 := by
    intro hfm
    have hroot : f.IsRoot m := by
      simpa [Polynomial.IsRoot.def] using hfm
    exact hexists m hm_mem.1 hm_mem.2 hroot
  by_cases hmid_opp : g.eval m * f.eval m < 0
  · have hfamily_f :
        ∀ {t : ℝ}, 0 < t → IsRealRooted (C t * f + g) := by
      intro t ht
      simpa [add_comm] using
        isRealRooted_add_left_of_affine_family_of_natDegree_succ_le
          hf0 hg0 hfnn hgnn haff (by omega) ht
    have hden_nonzero_f : ∀ x ∈ Set.Icc r₁ r₂, f.eval x ≠ 0 := by
      intro x hx hfx
      have hroot : f.IsRoot x := by
        simpa [Polynomial.IsRoot.def] using hfx
      rcases eq_or_lt_of_le hx.1 with hxr₁ | hx₁
      · have hroot₁ : f.IsRoot r₁ := by
          simpa [hxr₁] using hroot
        exact hno r₁ hr₁ hroot₁
      rcases eq_or_lt_of_le hx.2 with hxr₂ | hx₂
      · have hroot₂ : f.IsRoot r₂ := by
          simpa [hxr₂] using hroot
        exact hno r₂ hr₂ hroot₂
      · exact hexists x hx₁ hx₂ hroot
    have hratio_cont :
        ContinuousOn (fun y : ℝ => -(g.eval y / f.eval y)) (Set.Icc r₁ r₂) := by
      exact (g.continuous.continuousOn.div f.continuous.continuousOn hden_nonzero_f).neg
    have hratio_eq :
        (fun y : ℝ => -(g.eval y / f.eval y)) r₁ =
          (fun y : ℝ => -(g.eval y / f.eval y)) r₂ := by
      have hg₁_eval : g.eval r₁ = 0 := by
        simpa [Polynomial.IsRoot.def] using hr₁
      have hg₂_eval : g.eval r₂ = 0 := by
        simpa [Polynomial.IsRoot.def] using hr₂
      simp [hg₁_eval, hg₂_eval]
    obtain ⟨c, hc_mem, hlocal⟩ :=
      exists_isLocalExtr_Ioo hr₁r₂ hratio_cont hratio_eq
    have hprod_c_neg : g.eval c * f.eval c < 0 := by
      by_cases hmc : m ≤ c
      · have hno_mul :
            ∀ x, m ≤ x → x ≤ c → (g * f).eval x ≠ 0 := by
          intro x hmx hxc
          have hx₁ : r₁ < x := lt_of_lt_of_le hm_mem.1 hmx
          have hx₂ : x < r₂ := lt_of_le_of_lt hxc hc_mem.2
          have hgx_ne : g.eval x ≠ 0 := by
            intro hgx
            have hroot : g.IsRoot x := by
              simpa [Polynomial.IsRoot.def] using hgx
            exact hno_between_g x ((mem_roots hg0).mpr hroot) ⟨hx₁, hx₂⟩
          have hfx_ne : f.eval x ≠ 0 := by
            intro hfx
            have hroot : f.IsRoot x := by
              simpa [Polynomial.IsRoot.def] using hfx
            exact hexists x hx₁ hx₂ hroot
          simpa [eval_mul] using mul_ne_zero hgx_ne hfx_ne
        have hsame :
            0 < (g * f).eval m * (g * f).eval c :=
          eval_same_sign_of_no_roots (p := g * f) hmc hno_mul
        have hprod_c : (g * f).eval c < 0 := by
          have hsame' : 0 < (g.eval m * f.eval m) * (g.eval c * f.eval c) := by
            simpa [eval_mul] using hsame
          have hmid_prod' : g.eval m * f.eval m < 0 := hmid_opp
          have hprod_c' : g.eval c * f.eval c < 0 := by
            nlinarith
          simpa [eval_mul] using hprod_c'
        simpa [eval_mul] using hprod_c
      · have hcm : c ≤ m := le_of_not_ge hmc
        have hno_mul :
            ∀ x, c ≤ x → x ≤ m → (g * f).eval x ≠ 0 := by
          intro x hcx hxm
          have hx₁ : r₁ < x := lt_of_lt_of_le hc_mem.1 hcx
          have hx₂ : x < r₂ := lt_of_le_of_lt hxm hm_mem.2
          have hgx_ne : g.eval x ≠ 0 := by
            intro hgx
            have hroot : g.IsRoot x := by
              simpa [Polynomial.IsRoot.def] using hgx
            exact hno_between_g x ((mem_roots hg0).mpr hroot) ⟨hx₁, hx₂⟩
          have hfx_ne : f.eval x ≠ 0 := by
            intro hfx
            have hroot : f.IsRoot x := by
              simpa [Polynomial.IsRoot.def] using hfx
            exact hexists x hx₁ hx₂ hroot
          simpa [eval_mul] using mul_ne_zero hgx_ne hfx_ne
        have hsame :
            0 < (g * f).eval c * (g * f).eval m :=
          eval_same_sign_of_no_roots (p := g * f) hcm hno_mul
        have hprod_c : (g * f).eval c < 0 := by
          have hsame' : 0 < (g.eval c * f.eval c) * (g.eval m * f.eval m) := by
            simpa [eval_mul] using hsame
          have hmid_prod' : g.eval m * f.eval m < 0 := hmid_opp
          have hprod_c' : g.eval c * f.eval c < 0 := by
            nlinarith
          simpa [eval_mul] using hprod_c'
        simpa [eval_mul] using hprod_c
    have hf_c_ne : f.eval c ≠ 0 :=
      hden_nonzero_f c (Set.mem_Icc.mpr ⟨le_of_lt hc_mem.1, le_of_lt hc_mem.2⟩)
    have hpos_c : 0 < -(g.eval c / f.eval c) :=
      pos_neg_div_of_mul_neg hf_c_ne hprod_c_neg
    exact
      false_of_localExtr_neg_eval_div_eval_pos_of_add_left_family_of_no_common
        hfamily_f hno hlocal hpos_c
  · have hmid_pos : 0 < g.eval m * f.eval m := by
      exact lt_of_le_of_ne (le_of_not_gt hmid_opp) (mul_ne_zero hg_mid_ne hf_mid_ne).symm
    have hm_neg : m < 0 := by
      dsimp [m]
      nlinarith
    have hmid_right :
        g.eval m * (X * f).eval m < 0 := by
      rw [eval_mul]
      simp only [eval_X]
      nlinarith
    have hden_nonzero_Xf : ∀ x ∈ Set.Icc r₁ r₂, (X * f).eval x ≠ 0 := by
      intro x hx hxf
      rw [eval_mul] at hxf
      simp only [eval_X] at hxf
      have hx_neg : x < 0 := by
        rcases eq_or_lt_of_le hx.1 with rfl | hx₁
        · exact hr₁_neg
        exact lt_of_le_of_lt hx.2 hr₂_neg
      have hx_ne : x ≠ 0 := ne_of_lt hx_neg
      have hfx_ne : f.eval x ≠ 0 := by
        intro hfx
        have hroot : f.IsRoot x := by
          simpa [Polynomial.IsRoot.def] using hfx
        rcases eq_or_lt_of_le hx.1 with hxr₁ | hx₁
        · have hroot₁ : f.IsRoot r₁ := by
            simpa [hxr₁] using hroot
          exact hno r₁ hr₁ hroot₁
        rcases eq_or_lt_of_le hx.2 with hxr₂ | hx₂
        · have hroot₂ : f.IsRoot r₂ := by
            simpa [hxr₂] using hroot
          exact hno r₂ hr₂ hroot₂
        · exact hexists x hx₁ hx₂ hroot
      exact (mul_eq_zero.mp hxf).elim hx_ne hfx_ne
    have hratio_cont :
        ContinuousOn (fun y : ℝ => -(g.eval y / (X * f).eval y)) (Set.Icc r₁ r₂) := by
      exact
        (g.continuous.continuousOn.div (X * f).continuous.continuousOn hden_nonzero_Xf).neg
    have hratio_eq :
        (fun y : ℝ => -(g.eval y / (X * f).eval y)) r₁ =
          (fun y : ℝ => -(g.eval y / (X * f).eval y)) r₂ := by
      have hg₁_eval : g.eval r₁ = 0 := by
        simpa [Polynomial.IsRoot.def] using hr₁
      have hg₂_eval : g.eval r₂ = 0 := by
        simpa [Polynomial.IsRoot.def] using hr₂
      simp [hg₁_eval, hg₂_eval]
    obtain ⟨c, hc_mem, hlocal⟩ :=
      exists_isLocalExtr_Ioo hr₁r₂ hratio_cont hratio_eq
    have hprod_c_neg :
        g.eval c * (X * f).eval c < 0 := by
      by_cases hmc : m ≤ c
      · have hno_mul :
            ∀ x, m ≤ x → x ≤ c → (g * (X * f)).eval x ≠ 0 := by
          intro x hmx hxc
          have hx₁ : r₁ < x := lt_of_lt_of_le hm_mem.1 hmx
          have hx₂ : x < r₂ := lt_of_le_of_lt hxc hc_mem.2
          have hgx_ne : g.eval x ≠ 0 := by
            intro hgx
            have hroot : g.IsRoot x := by
              simpa [Polynomial.IsRoot.def] using hgx
            exact hno_between_g x ((mem_roots hg0).mpr hroot) ⟨hx₁, hx₂⟩
          have hXfx_ne : (X * f).eval x ≠ 0 := by
            have hx_neg : x < 0 := lt_trans hx₂ hr₂_neg
            have hx_ne : x ≠ 0 := ne_of_lt hx_neg
            have hfx_ne : f.eval x ≠ 0 := by
              intro hfx
              have hroot : f.IsRoot x := by
                simpa [Polynomial.IsRoot.def] using hfx
              exact hexists x hx₁ hx₂ hroot
            rw [eval_mul]
            simp only [eval_X]
            exact mul_ne_zero hx_ne hfx_ne
          simpa [eval_mul] using mul_ne_zero hgx_ne hXfx_ne
        have hsame :
            0 < (g * (X * f)).eval m * (g * (X * f)).eval c :=
          eval_same_sign_of_no_roots (p := g * (X * f)) hmc hno_mul
        have hsame' :
            0 < (g.eval m * (X * f).eval m) * (g.eval c * (X * f).eval c) := by
          simpa [eval_mul] using hsame
        have hmid_prod' : g.eval m * (X * f).eval m < 0 := hmid_right
        have hprod_c' : g.eval c * (X * f).eval c < 0 := by
          nlinarith
        simpa [eval_mul] using hprod_c'
      · have hcm : c ≤ m := le_of_not_ge hmc
        have hno_mul :
            ∀ x, c ≤ x → x ≤ m → (g * (X * f)).eval x ≠ 0 := by
          intro x hcx hxm
          have hx₁ : r₁ < x := lt_of_lt_of_le hc_mem.1 hcx
          have hx₂ : x < r₂ := lt_of_le_of_lt hxm hm_mem.2
          have hgx_ne : g.eval x ≠ 0 := by
            intro hgx
            have hroot : g.IsRoot x := by
              simpa [Polynomial.IsRoot.def] using hgx
            exact hno_between_g x ((mem_roots hg0).mpr hroot) ⟨hx₁, hx₂⟩
          have hXfx_ne : (X * f).eval x ≠ 0 := by
            have hx_neg : x < 0 := lt_trans hx₂ hr₂_neg
            have hx_ne : x ≠ 0 := ne_of_lt hx_neg
            have hfx_ne : f.eval x ≠ 0 := by
              intro hfx
              have hroot : f.IsRoot x := by
                simpa [Polynomial.IsRoot.def] using hfx
              exact hexists x hx₁ hx₂ hroot
            rw [eval_mul]
            simp only [eval_X]
            exact mul_ne_zero hx_ne hfx_ne
          simpa [eval_mul] using mul_ne_zero hgx_ne hXfx_ne
        have hsame :
            0 < (g * (X * f)).eval c * (g * (X * f)).eval m :=
          eval_same_sign_of_no_roots (p := g * (X * f)) hcm hno_mul
        have hsame' :
            0 < (g.eval c * (X * f).eval c) * (g.eval m * (X * f).eval m) := by
          simpa [eval_mul] using hsame
        have hmid_prod' : g.eval m * (X * f).eval m < 0 := hmid_right
        have hprod_c' : g.eval c * (X * f).eval c < 0 := by
          nlinarith
        simpa [eval_mul] using hprod_c'
    have hXf_c_ne : (X * f).eval c ≠ 0 :=
      hden_nonzero_Xf c (Set.mem_Icc.mpr ⟨le_of_lt hc_mem.1, le_of_lt hc_mem.2⟩)
    have hpos_c : 0 < -(g.eval c / (X * f).eval c) :=
      pos_neg_div_of_mul_neg hXf_c_ne hprod_c_neg
    exact
      false_of_localExtr_neg_eval_div_eval_pos_of_add_left_family_of_no_common
        (fun {_t} ht => by
          simpa [add_comm] using PosComboRealRooted.isRealRooted_add_right hposcombo ht)
        hno_right hlocal hpos_c

/-- Boundary same-degree package for the fixed right pair `(g, X * f)` in the
succ-degree affine branch with `g(0) ≠ 0`.

For every `μ > 0`, the pair `(g, g + μ X f)` stays inside the same positive
cone, the second member has the same degree as `g`, its roots are simple, and
it has no common root with `g`. This is the honest same-degree perturbation data
needed if we want to orient the boundary family directly rather than going
through a converse shortcut. -/
private lemma right_boundary_pair_sameDegree_data_of_affine_family_succDegree_not_isRoot_zero
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg_root0 : ¬ g.IsRoot 0)
    {μ : ℝ}
    (hμ : 0 < μ) :
    PosComboRealRooted g (g + C μ * (X * f)) ∧
    IsRealRooted (g + C μ * (X * f)) ∧
    HasSimpleRoots (g + C μ * (X * f)) ∧
    HasPosLeadingCoeff (g + C μ * (X * f)) ∧
    (g + C μ * (X * f)).natDegree = g.natDegree ∧
    (∀ r, g.IsRoot r → ¬ (g + C μ * (X * f)).IsRoot r) := by
  have hg_rr : IsRealRooted g :=
    isRealRooted_right_of_affine_family_succDegree hf0 hg0 hfnn hgnn haff hsucc.symm
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  have hXf_pos : HasPosLeadingCoeff (X * f) :=
    (hasNonnegCoeffs_X.mul hfnn).pos_leadingCoeff (mul_ne_zero X_ne_zero hf0)
  have hposcombo : PosComboRealRooted g (X * f) :=
    posComboRealRooted_right_of_affine_family hf0 hg0 hfnn hgnn haff
  have hno_right :
      ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r :=
    no_common_right_pair_of_no_common_of_not_isRoot_zero hno hg_root0
  have hpair :
      PosComboRealRooted g (g + C μ * (X * f)) := by
    intro lam ν hlam hν
    have hrr :
        IsRealRooted (C (lam + ν) * g + C (ν * μ) * (X * f)) :=
      hposcombo (lam := lam + ν) (μ := ν * μ) (by positivity) (by positivity)
    have hEq :
        C lam * g + C ν * (g + C μ * (X * f)) =
          C (lam + ν) * g + C (ν * μ) * (X * f) := by
      calc
        C lam * g + C ν * (g + C μ * (X * f))
            = C lam * g + (C ν * g + C ν * (C μ * (X * f))) := by
                rw [mul_add]
        _ = (C lam * g + C ν * g) + C ν * (C μ * (X * f)) := by
              ac_rfl
        _ = (C lam + C ν) * g + (C ν * C μ) * (X * f) := by
              rw [← add_mul, mul_assoc]
        _ = (C lam + C ν) * g + C (ν * μ) * (X * f) := by
              rw [C_mul]
        _ = C (lam + ν) * g + C (ν * μ) * (X * f) := by
              rw [← C_add]
    exact hEq ▸ hrr
  have hμ_rr : IsRealRooted (g + C μ * (X * f)) :=
    PosComboRealRooted.isRealRooted_add_right hposcombo hμ
  have hμ_simple : HasSimpleRoots (g + C μ * (X * f)) :=
    hasSimpleRoots_add_right_of_posComboRealRooted hposcombo hno_right hμ
  have hμ_pos : HasPosLeadingCoeff (g + C μ * (X * f)) := by
    have hdeg : g.natDegree ≤ (X * f).natDegree := by
      rw [natDegree_mul X_ne_zero hf0, natDegree_X]
      omega
    have hsum_nonneg : HasNonnegCoeffs (g + C μ * (X * f)) :=
      hgnn.add (nonnegCoeffs_C_mul hμ.le (hasNonnegCoeffs_X.mul hfnn))
    have hsum_ne : g + C μ * (X * f) ≠ 0 := hμ_rr.1
    exact hsum_nonneg.pos_leadingCoeff hsum_ne
  have hμ_deg : (g + C μ * (X * f)).natDegree = g.natDegree := by
    have hdeg : g.natDegree ≤ (X * f).natDegree := by
      rw [natDegree_mul X_ne_zero hf0, natDegree_X]
      omega
    calc
      (g + C μ * (X * f)).natDegree = (X * f).natDegree :=
        PosComboRealRooted.family_natDegree_right hdeg hg_pos hXf_pos hμ
      _ = g.natDegree := by
        rw [natDegree_mul X_ne_zero hf0, natDegree_X]
        omega
  have hno_boundary :
      ∀ r, g.IsRoot r → ¬ (g + C μ * (X * f)).IsRoot r := by
    intro r hgr hboundary
    have hg_eval : g.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hgr
    have hboundary_eval : (g + C μ * (X * f)).eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hboundary
    have hXf_eval : (X * f).eval r = 0 := by
      rw [eval_add, hg_eval] at hboundary_eval
      simp only [zero_add] at hboundary_eval
      have hμ_ne : μ ≠ 0 := ne_of_gt hμ
      rw [eval_mul, eval_C] at hboundary_eval
      exact mul_eq_zero.mp hboundary_eval |>.resolve_left hμ_ne
    exact hno_right r hgr (by simpa [Polynomial.IsRoot.def] using hXf_eval)
  exact ⟨hpair, hμ_rr, hμ_simple, hμ_pos, hμ_deg, hno_boundary⟩

/-- The affine family `(C s * X + C t) * f + g` being real-rooted for all `s, t > 0`
implies `AllComboRealRooted g f` (all linear combinations `α g + β f` are
real-rooted), provided `f, g` have nonneg coefficients, positive leading
coefficients, no common roots, and `g.natDegree = f.natDegree + 1`.

The key observation is that for `x₀ < 0`, the affine substitution
`y = s x₀ + t` sweeps all of `ℝ` as `(s, t)` ranges over `(0,∞)²`,
so the affine family pins every fibre `g(x₀) + y f(x₀)`.  Combined with
the completed Obreschkoff converse this gives `Prec g f ∨ Prec f g`. -/
private lemma allComboRealRooted_of_affine_family_succDegree_not_isRoot_zero
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg_root0 : ¬ g.IsRoot 0) :
    AllComboRealRooted g f := by
  have hf_rr : IsRealRooted f :=
    isRealRooted_of_X_mul (isRealRooted_X_mul_of_affine_family hf0 hg0 hfnn hgnn haff)
  have hg_rr : IsRealRooted g :=
    isRealRooted_right_of_affine_family_succDegree hf0 hg0 hfnn hgnn haff hsucc.symm
  have hsimple_g : HasSimpleRoots g :=
    hasSimpleRoots_right_of_affine_family_succDegree_not_isRoot_zero
      hf0 hg0 hfnn hgnn haff hsucc hno hg_root0
  let rs := g.roots.sort (· ≤ ·)
  have hrs_sorted : rs.Pairwise (· ≤ ·) := by
    simp [rs]
  have hrs_sortedLT : rs.Pairwise (· < ·) := by
    simpa [rs] using (roots_sort_sortedLT_of_hasSimpleRoots hg0 hsimple_g).pairwise
  have hrs_eq : (↑rs : Multiset ℝ) = g.roots := by
    simp [rs]
  have hgap_rs : ConsecNoRoots g rs :=
    consecNoRoots_of_sorted_eq hrs_eq hrs_sorted
  have hroot_between :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        ∃ u, r₁ < u ∧ u < r₂ ∧ f.IsRoot u := by
    intro pre r₁ r₂ rest hEq
    have hpair_full : (pre ++ r₁ :: r₂ :: rest).Pairwise (· < ·) := by
      simpa [hEq] using hrs_sortedLT
    have hsuf_sortedLT : (r₁ :: r₂ :: rest).Pairwise (· < ·) :=
      pairwise_suffix pre (r₁ :: r₂ :: rest) hpair_full
    have hgap_full : ConsecNoRoots g (pre ++ r₁ :: r₂ :: rest) := by
      simpa [hEq] using hgap_rs
    have hsuf_gap : ConsecNoRoots g (r₁ :: r₂ :: rest) :=
      consecNoRoots_suffix pre (r₁ :: r₂ :: rest) hgap_full
    have hr₁r₂ : r₁ < r₂ := List.rel_of_pairwise_cons hsuf_sortedLT (.head _)
    have hr₁_mem_rs : r₁ ∈ rs := by
      rw [hEq]
      simp
    have hr₂_mem_rs : r₂ ∈ rs := by
      rw [hEq]
      simp
    have hr₁_root : g.IsRoot r₁ := by
      have : r₁ ∈ (↑rs : Multiset ℝ) := Multiset.mem_coe.mpr hr₁_mem_rs
      exact (mem_roots hg0).mp (hrs_eq ▸ this)
    have hr₂_root : g.IsRoot r₂ := by
      have : r₂ ∈ (↑rs : Multiset ℝ) := Multiset.mem_coe.mpr hr₂_mem_rs
      exact (mem_roots hg0).mp (hrs_eq ▸ this)
    exact
      exists_f_root_between_consecutive_g_roots_of_affine_family_succDegree_not_isRoot_zero
        hf0 hg0 hfnn hgnn haff hsucc hno hg_root0
        hr₁_root hr₂_root hr₁r₂ hsuf_gap.1
  obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_exists (F := f) rs hrs_sorted hroot_between
  have hus_sub : (↑us : Multiset ℝ) ≤ f.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hus_pw.imp ne_of_lt))]
    intro x hx
    exact (mem_roots hf0).mpr (hus_roots x (Multiset.mem_coe.mp hx))
  have hrs_len : rs.length = g.natDegree := by
    rw [show rs = g.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hg_rr.2]
  have hus_eq : (↑us : Multiset ℝ) = f.roots := by
    apply Multiset.eq_of_le_of_card_le hus_sub
    calc
      f.roots.card = f.natDegree := hf_rr.2
      _ = g.natDegree - 1 := by omega
      _ = rs.length - 1 := by rw [hrs_len]
      _ = us.length := hus_len.symm
      _ = (↑us : Multiset ℝ).card := (Multiset.coe_card us).symm
      _ ≤ (↑us : Multiset ℝ).card := le_rfl
  have hprec_fg : Prec f g := by
    refine ⟨hf_rr, hg_rr, us, rs, hus_pw.imp le_of_lt, hrs_sorted, hus_eq, hrs_eq, ?_⟩
    left
    exact ⟨by omega, hus_int⟩
  have hall_fg : AllComboRealRooted f g :=
    allComboRealRooted_of_prec hprec_fg
  exact allComboRealRooted_comm hall_fg

private lemma allComboRealRooted_of_affine_family_succDegree
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, g.IsRoot r → ¬ f.IsRoot r) :
    AllComboRealRooted g f := by
  by_cases hg_root0 : g.IsRoot 0
  · have hf_root0_false : ¬ f.IsRoot 0 := hno 0 hg_root0
    have hshift_nonneg : HasNonnegCoeffs (g + f) := hgnn.add hfnn
    have hshift_ne : g + f ≠ 0 :=
      add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hgnn hfnn hf0
    have hshift_succ : (g + f).natDegree = f.natDegree + 1 := by
      have hdeg_lt : f.natDegree < g.natDegree := by omega
      calc
        (g + f).natDegree = g.natDegree :=
          natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff
            hdeg_lt (hgnn.pos_leadingCoeff hg0)
        _ = f.natDegree + 1 := hsucc
    have hshift_aff :
        ∀ {s t : ℝ}, 0 < s → 0 < t →
          IsRealRooted (((C s * X + C t) * f) + (g + f)) := by
      intro s t hs ht
      have hbase :
          IsRealRooted (((C s * X + C (t + 1)) * f) + g) :=
        haff hs (by linarith)
      have hEq :
          (((C s * X + C t) * f) + (g + f)) =
            (((C s * X + C (t + 1)) * f) + g) := by
        calc
          (((C s * X + C t) * f) + (g + f))
              = ((C s * X + C t) * f) + g + f := by
                  ac_rfl
          _ = (C s * X) * f + C t * f + g + f := by
                rw [add_mul]
          _ = (C s * X) * f + (C t * f + C (1 : ℝ) * f) + g := by
                ac_rfl
          _ = (C s * X) * f + (C t + C (1 : ℝ)) * f + g := by
                rw [← add_mul]
          _ = (C s * X) * f + C (t + 1) * f + g := by
                rw [← C_add]
          _ = (((C s * X + C (t + 1)) * f) + g) := by
                rw [add_mul]
      simpa [hEq] using hbase
    have hshift_no : ∀ r, (g + f).IsRoot r → ¬ f.IsRoot r := by
      intro r hshift_root hfr
      have hshift_eval : (g + f).eval r = 0 := by
        simpa [Polynomial.IsRoot.def] using hshift_root
      have hf_eval : f.eval r = 0 := by
        simpa [Polynomial.IsRoot.def] using hfr
      have hg_eval : g.eval r = 0 := by
        rw [eval_add, hf_eval] at hshift_eval
        simpa [Polynomial.IsRoot.def] using hshift_eval
      exact hno r (by simpa [Polynomial.IsRoot.def] using hg_eval) hfr
    have hshift_root0_false : ¬ (g + f).IsRoot 0 := by
      intro hshift_root0
      have hshift_eval : (g + f).eval 0 = 0 := by
        simpa [Polynomial.IsRoot.def] using hshift_root0
      have hg_eval : g.eval 0 = 0 := by
        simpa [Polynomial.IsRoot.def] using hg_root0
      have hf_eval : f.eval 0 = 0 := by
        rw [eval_add, hg_eval] at hshift_eval
        simpa [Polynomial.IsRoot.def] using hshift_eval
      exact hf_root0_false (by simpa [Polynomial.IsRoot.def] using hf_eval)
    have hall_shift : AllComboRealRooted (g + f) f :=
      allComboRealRooted_of_affine_family_succDegree_not_isRoot_zero
        hf0 hshift_ne hfnn hshift_nonneg hshift_aff hshift_succ hshift_no hshift_root0_false
    intro α β
    have hEq :
        C α * g + C β * f =
          C α * (g + f) + C (β - α) * f := by
      have hC : C β = C α + C (β - α) := by
        rw [← C_add]
        congr 1
        ring
      calc
        C α * g + C β * f
            = C α * g + (C α + C (β - α)) * f := by rw [hC]
        _ = C α * g + (C α * f + C (β - α) * f) := by
              rw [add_mul]
        _ = C α * g + C α * f + C (β - α) * f := by
              ac_rfl
        _ = C α * (g + f) + C (β - α) * f := by
              rw [mul_add]
    simpa [hEq] using hall_shift α (β - α)
  · exact
      allComboRealRooted_of_affine_family_succDegree_not_isRoot_zero
        hf0 hg0 hfnn hgnn haff hsucc hno hg_root0

/-- Isolated high-degree frontier for the affine converse after removing the
already-settled shared-root succ-degree branch. What remains is exactly the
genuine no-shortcut core:

* either `(f, g)` have no common root, in which case the fixed right pair
  `(g, X * f)` must be oriented directly;
* or `g` has the same degree as `f`, in which case the shifted pair
  `(g + X * f, f)` should absorb the common-root bookkeeping.

The low-degree branches are handled separately in
`prec_of_affine_family_nonneg`. -/
private lemma prec_right_pair_of_affine_family_high_degree_core
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (_hdegf2 : 2 ≤ f.natDegree)
    (hno_common_fg : ¬ ∃ r, g.IsRoot r ∧ f.IsRoot r) :
    Prec g (X * f) := by
  -- Both degree branches (same and succ) reduce to the AllCombo upgrade
  -- `allComboRealRooted_of_affine_family_succDegree`, applied either to
  -- the original pair (succ case) or to the shifted pair (same case).
  have hXf_rr : IsRealRooted (X * f) :=
    isRealRooted_X_mul_of_affine_family hf0 hg0 hfnn hgnn haff
  have hf_rr : IsRealRooted f := isRealRooted_of_X_mul hXf_rr
  have hdeg_cases : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 :=
    natDegree_cases_of_affine_family hf0 hg0 hfnn hgnn haff
  rcases hdeg_cases with hsame | hsucc
  · -- Same-degree case: apply AllCombo to the shifted pair (g + X*f, f).
    have hshift_nonneg : HasNonnegCoeffs (g + X * f) :=
      hgnn.add (hasNonnegCoeffs_X.mul hfnn)
    have hshift_ne : g + X * f ≠ 0 :=
      add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
        hgnn (hasNonnegCoeffs_X.mul hfnn) (mul_ne_zero X_ne_zero hf0)
    have hshift_deg : (g + X * f).natDegree = f.natDegree + 1 := by
      simpa [hsame] using
        natDegree_shifted_pair_eq_succ_of_affine_family hf0 hg0 hfnn hgnn haff
    have hshift_rr : IsRealRooted (g + X * f) :=
      isRealRooted_right_of_affine_family_succDegree
        hf0 hshift_ne hfnn hshift_nonneg
        (shifted_affine_family_of_affine_family haff) hshift_deg.symm
    have hno_shift : ∀ r, (g + X * f).IsRoot r → ¬ f.IsRoot r := by
      intro r hshift_r hfr
      have hcommon_fg : ∃ r', g.IsRoot r' ∧ f.IsRoot r' :=
        (common_shifted_pair_iff_common_fg).mp ⟨r, hshift_r, hfr⟩
      exact hno_common_fg hcommon_fg
    have hall_shift : AllComboRealRooted (g + X * f) f :=
      allComboRealRooted_of_affine_family_succDegree
        hf0 hshift_ne hfnn hshift_nonneg
        (shifted_affine_family_of_affine_family haff)
        hshift_deg hno_shift
    have hprec_or : Prec f (g + X * f) ∨ Prec (g + X * f) f :=
      prec_of_allComboRealRooted hf_rr hshift_rr
        (allComboRealRooted_comm hall_shift) (Or.inl hshift_deg.symm)
    have hprec_f_shift : Prec f (g + X * f) := by
      rcases hprec_or with hgood | hbad
      · exact hgood
      · -- Prec (g+X*f) f impossible: (g+X*f).natDegree = f.natDegree + 1
        -- but Prec requires (g+X*f).natDegree ≤ f.natDegree.
        exact absurd (natDegree_bounds_of_prec hbad).1
          (by omega)
    exact
      prec_right_pair_of_prec_shifted_pair_sameDegree
        hprec_f_shift hf0 hg0 hfnn hgnn hsame
  · -- Succ-degree case: apply AllCombo directly to (g, f).
    have hg_rr : IsRealRooted g :=
      isRealRooted_right_of_affine_family_succDegree
        hf0 hg0 hfnn hgnn haff hsucc.symm
    have hno_fg_fun : ∀ r, g.IsRoot r → ¬ f.IsRoot r := by
      intro r hgr hfr
      exact hno_common_fg ⟨r, hgr, hfr⟩
    have hall : AllComboRealRooted g f :=
      allComboRealRooted_of_affine_family_succDegree
        hf0 hg0 hfnn hgnn haff hsucc hno_fg_fun
    have hprec_or : Prec f g ∨ Prec g f :=
      prec_of_allComboRealRooted hf_rr hg_rr
        (allComboRealRooted_comm hall) (Or.inl hsucc.symm)
    have hprec_fg : Prec f g := by
      rcases hprec_or with hgood | hbad
      · exact hgood
      · -- Prec g f impossible: g.natDegree = f.natDegree + 1
        -- but Prec requires g.natDegree ≤ f.natDegree.
        exact absurd (natDegree_bounds_of_prec hbad).1
          (by omega)
    exact prec_to_prec_mul_X_of_nonneg hprec_fg hfnn hgnn

/-- Wrapper matching the original high-degree target. The only genuinely hard
branches are delegated to `prec_right_pair_of_affine_family_high_degree_core`,
while the recursive shared-root succ-degree branch is handled in
`prec_right_pair_of_affine_family_high_degree`. -/
private lemma prec_right_pair_of_affine_family_high_degree_remaining
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hdegf2 : 2 ≤ f.natDegree)
    (hno_common_fg : ¬ ∃ r, g.IsRoot r ∧ f.IsRoot r) :
    Prec g (X * f) := by
  exact
    prec_right_pair_of_affine_family_high_degree_core
      hf0 hg0 hfnn hgnn haff hdegf2 hno_common_fg

private lemma prec_right_pair_of_affine_family_high_degree
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (_hdegf2 : 2 ≤ f.natDegree) :
    Prec g (X * f) := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          f ≠ 0 →
          g ≠ 0 →
          HasNonnegCoeffs f →
          HasNonnegCoeffs g →
          (∀ {s t : ℝ}, 0 < s → 0 < t →
            IsRealRooted (((C s * X + C t) * f) + g)) →
          2 ≤ f.natDegree →
          Prec g (X * f))
      f.natDegree ?_ rfl hf0 hg0 hfnn hgnn haff _hdegf2
  intro n ih f g hfdeg hf0 hg0 hfnn hgnn haff hdegf2
  have hXf_rr : IsRealRooted (X * f) :=
    isRealRooted_X_mul_of_affine_family hf0 hg0 hfnn hgnn haff
  have hf_rr : IsRealRooted f := isRealRooted_of_X_mul hXf_rr
  have hdeg_cases : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 :=
    natDegree_cases_of_affine_family hf0 hg0 hfnn hgnn haff
  by_cases hcommon_fg : ∃ r, g.IsRoot r ∧ f.IsRoot r
  · rcases hcommon_fg with ⟨r, hgr, hfr⟩
    rcases hdeg_cases with hsame | hsucc
    · -- Same-degree + common root: use the shifted pair (f, g + X * f).
      -- The shifted pair IS real-rooted and shares the same common root r,
      -- so we can factor (X - C r) from both f and (g + X * f), recurse on
      -- the quotient pair, and lift back.
      have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf0
      have hshift_nonneg : HasNonnegCoeffs (g + X * f) :=
        hgnn.add (hasNonnegCoeffs_X.mul hfnn)
      have hshift_ne : g + X * f ≠ 0 :=
        add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
          hgnn (hasNonnegCoeffs_X.mul hfnn) (mul_ne_zero X_ne_zero hf0)
      have hshift_pos : HasPosLeadingCoeff (g + X * f) :=
        hshift_nonneg.pos_leadingCoeff hshift_ne
      have hshift_deg : (g + X * f).natDegree = f.natDegree + 1 := by
        simpa [hsame] using
          natDegree_shifted_pair_eq_succ_of_affine_family hf0 hg0 hfnn hgnn haff
      have hshift_rr : IsRealRooted (g + X * f) :=
        isRealRooted_right_of_affine_family_succDegree
          hf0 hshift_ne hfnn hshift_nonneg
          (shifted_affine_family_of_affine_family haff) hshift_deg.symm
      -- The common root of (f, g) is also a root of the shifted pair.
      have hshift_root : (g + X * f).IsRoot r := by
        simp only [Polynomial.IsRoot.def, eval_add, eval_mul, eval_X]
        have hgr0 : g.eval r = 0 := by simpa [Polynomial.IsRoot.def] using hgr
        have hfr0 : f.eval r = 0 := by simpa [Polynomial.IsRoot.def] using hfr
        rw [hgr0, hfr0, mul_zero, add_zero]
      -- Factor out the common root from the shifted pair using the
      -- standard reduction machinery.
      obtain ⟨qf, q_shift, hqf, hq_shift, hqf_nonneg, hq_shift_nonneg,
        hqf_ne, hq_shift_ne, _hqf_pos, _hq_shift_pos, hq_aff⟩ :=
        affine_family_common_root_reduction_data
          hf_rr hshift_rr hfnn hshift_nonneg hf_pos hshift_pos
          (shifted_affine_family_of_affine_family haff) hfr hshift_root
      have hqf_deg_lt : qf.natDegree < n := by
        rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne,
          natDegree_X_sub_C]
        omega
      have hqf_deg_pos : 1 ≤ qf.natDegree := by
        rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne,
          natDegree_X_sub_C] at hdegf2
        omega
      -- By induction, the quotient pair satisfies Prec q_shift (X * qf).
      have hprec_q : Prec q_shift (X * qf) := by
        by_cases hqf_deg1 : qf.natDegree = 1
        · exact
            prec_right_pair_of_affine_family_degree_one
              hqf_ne hq_shift_ne hqf_nonneg hq_shift_nonneg hq_aff hqf_deg1
        · exact
            ih qf.natDegree hqf_deg_lt rfl
              hqf_ne hq_shift_ne hqf_nonneg hq_shift_nonneg hq_aff (by omega)
      -- Lift: Prec (g + X * f) (X * f) from Prec q_shift (X * qf).
      have hprec_shift : Prec (g + X * f) (X * f) := by
        have hXf_eq : X * f = (X - C r) * (X * qf) := by
          calc X * f = X * ((X - C r) * qf) := by rw [hqf]
            _ = (X - C r) * (X * qf) := by ring
        have hshift_eq : g + X * f = (X - C r) * q_shift := hq_shift
        rw [hshift_eq, hXf_eq]
        exact prec_mul_common_factor (isRealRooted_X_sub_C r) hprec_q
      -- Step back: Prec f (g + X * f) from Prec (g + X * f) (X * f).
      have hprec_f_shift : Prec f (g + X * f) :=
        prec_of_prec_mul_X_of_nonneg hprec_shift hfnn hshift_nonneg
      -- Conclude: Prec g (X * f) from the shifted-pair Prec.
      exact
        prec_right_pair_of_prec_shifted_pair_sameDegree
          hprec_f_shift hf0 hg0 hfnn hgnn hsame
    · have hg_rr : IsRealRooted g :=
        isRealRooted_right_of_affine_family_succDegree
          hf0 hg0 hfnn hgnn haff hsucc.symm
      have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf0
      have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
      obtain ⟨qf, qg, hqf, hqg, hqf_nonneg, hqg_nonneg, hqf_ne, hqg_ne,
        _hqf_pos, _hqg_pos, hqaff⟩ :=
        affine_family_common_root_reduction_data
          hf_rr hg_rr hfnn hgnn hf_pos hg_pos haff hfr hgr
      have hqf_deg_lt : qf.natDegree < n := by
        rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C]
        omega
      have hqf_deg_pos : 1 ≤ qf.natDegree := by
        rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C] at hdegf2
        omega
      have hprec_q : Prec qg (X * qf) := by
        by_cases hqf_deg1 : qf.natDegree = 1
        · exact
            prec_right_pair_of_affine_family_degree_one
              hqf_ne hqg_ne hqf_nonneg hqg_nonneg hqaff hqf_deg1
        · have hqf_deg2 : 2 ≤ qf.natDegree := by
            omega
          exact
            ih qf.natDegree hqf_deg_lt rfl
              hqf_ne hqg_ne hqf_nonneg hqg_nonneg hqaff hqf_deg2
      exact prec_right_pair_of_common_root_factor hqf hqg hprec_q
  · exact
      prec_right_pair_of_affine_family_high_degree_remaining
        hf0 hg0 hfnn hgnn haff hdegf2 hcommon_fg

/-- Converse affine-family step used in Brändén 7.8.5:
if all positive affine combinations `((C s * X + C t) * f) + g` are real-rooted
and both `f, g` are nonzero with nonnegative coefficients, then `f ≪ g`.

This is exactly the remaining local blocker in the forward matrix argument. -/
theorem prec_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    :
    Prec f g := by
  have hdeg_cases : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 :=
    natDegree_cases_of_affine_family hf0 hg0 hfnn hgnn haff
  have hXf_rr : IsRealRooted (X * f) :=
    isRealRooted_X_mul_of_affine_family hf0 hg0 hfnn hgnn haff
  have hf_rr : IsRealRooted f := isRealRooted_of_X_mul hXf_rr
  by_cases hdegf0 : f.natDegree = 0
  · rcases hdeg_cases with hgdeg | hgdeg
    · have hg_deg0 : g.natDegree = 0 := by simpa [hdegf0] using hgdeg
      have hg_rr : IsRealRooted g := isRealRooted_of_deg_zero hg0 hg_deg0
      exact prec_degree_zero_degree_zero hf_rr hg_rr hdegf0 hg_deg0
    · have hg_deg1 : g.natDegree = 1 := by simpa [hdegf0] using hgdeg
      have hg_rr : IsRealRooted g := isRealRooted_of_degree_one hg_deg1
      exact prec_degree_zero_right_of_degree_one_local hf_rr hg_rr hdegf0 hg_deg1
  by_cases hdegf1 : f.natDegree = 1
  · exact prec_of_affine_family_nonneg_degree_one hf0 hg0 hfnn hgnn haff hdegf1
  have hdegf2 : 2 ≤ f.natDegree := by omega
  have hprec_pair : Prec g (X * f) :=
    prec_right_pair_of_affine_family_high_degree hf0 hg0 hfnn hgnn haff hdegf2
  exact prec_of_prec_mul_X_of_nonneg hprec_pair hfnn hgnn

/-- Right-pair form of the affine-family converse. This is the degree-free
public API: the affine-family hypothesis gives `f ≪ g`, and nonnegative
coefficients transport this to `g ≪ X * f`. -/
theorem prec_right_pair_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    Prec g (X * f) :=
  prec_to_prec_mul_X_of_nonneg
    (prec_of_affine_family_nonneg hf0 hg0 hfnn hgnn haff)
    hfnn hgnn

/-- Closed affine-segment wrapper for `prec_of_affine_family_nonneg`.

For each positive affine factor `sX+t`, assume the two endpoint polynomials
`(sX+t)P0+H0` and `(sX+t)P1+H1` are positively compatible, and assume the
endpoints themselves are real-rooted.  Then every convex interpolation
`Pβ=(1-β)P0+βP1`, `Hβ=(1-β)H0+βH1` satisfies `Pβ ≪ Hβ`, provided the
usual nonzero and nonnegative-coefficient hypotheses for Branden's affine
criterion hold. -/
theorem prec_of_affine_segment_endpoints_nonneg
    {P0 P1 H0 H1 : ℝ[X]} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hPβ0 : C (1 - β) * P0 + C β * P1 ≠ 0)
    (hHβ0 : C (1 - β) * H0 + C β * H1 ≠ 0)
    (hPβnn : HasNonnegCoeffs (C (1 - β) * P0 + C β * P1))
    (hHβnn : HasNonnegCoeffs (C (1 - β) * H0 + C β * H1))
    (hendpoint :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        PosComboRealRooted
          (((C s * X + C t) * P0) + H0)
          (((C s * X + C t) * P1) + H1))
    (hleft :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * P0) + H0))
    (hright :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * P1) + H1)) :
    Prec (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  refine prec_of_affine_family_nonneg hPβ0 hHβ0 hPβnn hHβnn ?_
  intro s t hs ht
  have hseg :
      IsRealRooted
        (C (1 - β) * (((C s * X + C t) * P0) + H0) +
          C β * (((C s * X + C t) * P1) + H1)) :=
    PosComboRealRooted.isRealRooted_closed_segment
      (hendpoint hs ht) (hleft hs ht) (hright hs ht) hβ0 hβ1
  have hEq :
      ((C s * X + C t) * (C (1 - β) * P0 + C β * P1)) +
          (C (1 - β) * H0 + C β * H1) =
        C (1 - β) * (((C s * X + C t) * P0) + H0) +
          C β * (((C s * X + C t) * P1) + H1) := by
    ring
  rw [hEq]
  exact hseg

/-- Variant of `prec_of_affine_segment_endpoints_nonneg` where endpoint
real-rootedness is recovered from positive-combination real-rootedness plus
equal degree and positive leading coefficients at every affine specialization. -/
theorem prec_of_affine_segment_endpoints_sameDegree_nonneg
    {P0 P1 H0 H1 : ℝ[X]} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hPβ0 : C (1 - β) * P0 + C β * P1 ≠ 0)
    (hHβ0 : C (1 - β) * H0 + C β * H1 ≠ 0)
    (hPβnn : HasNonnegCoeffs (C (1 - β) * P0 + C β * P1))
    (hHβnn : HasNonnegCoeffs (C (1 - β) * H0 + C β * H1))
    (hendpoint :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        PosComboRealRooted
          (((C s * X + C t) * P0) + H0)
          (((C s * X + C t) * P1) + H1))
    (hleft_pos :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        HasPosLeadingCoeff (((C s * X + C t) * P0) + H0))
    (hright_pos :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        HasPosLeadingCoeff (((C s * X + C t) * P1) + H1))
    (hdeg :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        (((C s * X + C t) * P1) + H1).natDegree =
          (((C s * X + C t) * P0) + H0).natDegree) :
    Prec (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  refine prec_of_affine_family_nonneg hPβ0 hHβ0 hPβnn hHβnn ?_
  intro s t hs ht
  have hseg :
      IsRealRooted
        (C (1 - β) * (((C s * X + C t) * P0) + H0) +
          C β * (((C s * X + C t) * P1) + H1)) :=
    PosComboRealRooted.isRealRooted_closed_segment_of_sameDegree
      (hendpoint hs ht) (hleft_pos hs ht) (hright_pos hs ht) (hdeg hs ht) hβ0 hβ1
  have hEq :
      ((C s * X + C t) * (C (1 - β) * P0 + C β * P1)) +
          (C (1 - β) * H0 + C β * H1) =
        C (1 - β) * (((C s * X + C t) * P0) + H0) +
          C β * (((C s * X + C t) * P1) + H1) := by
    ring
  rw [hEq]
  exact hseg

/--
ASW/PF version of `prec_of_affine_segment_endpoints_nonneg`.

For every positive affine factor `sX+t`, it is enough to prove Polya-frequency
for the coefficient sequence of each nonzero endpoint pencil `F0 + z F1`,
`z>=0`. ASW turns this Toeplitz-total-nonnegativity input into endpoint
`PosComboRealRooted`; the preceding affine-segment wrapper then gives the
directed segment relation.
-/
theorem prec_of_affine_segment_endpoint_pf_nonneg
    {P0 P1 H0 H1 : ℝ[X]} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hPβ0 : C (1 - β) * P0 + C β * P1 ≠ 0)
    (hHβ0 : C (1 - β) * H0 + C β * H1 ≠ 0)
    (hPβnn : HasNonnegCoeffs (C (1 - β) * P0 + C β * P1))
    (hHβnn : HasNonnegCoeffs (C (1 - β) * H0 + C β * H1))
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hpencil_ne :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        ((((C s * X + C t) * P0) + H0) +
          C z * (((C s * X + C t) * P1) + H1)) ≠ 0)
    (hpencil_nn :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        HasNonnegCoeffs
          ((((C s * X + C t) * P0) + H0) +
            C z * (((C s * X + C t) * P1) + H1)))
    (hpencil_pf :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        IsPolyaFrequencySequence
          (fun n =>
            ((((C s * X + C t) * P0) + H0) +
              C z * (((C s * X + C t) * P1) + H1)).coeff n))
    (hleft :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * P0) + H0))
    (hright :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * P1) + H1)) :
    Prec (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  refine prec_of_affine_segment_endpoints_nonneg hβ0 hβ1 hPβ0 hHβ0 hPβnn hHβnn ?_
    hleft hright
  intro s t hs ht
  exact PosComboRealRooted.of_aissenSchoenbergWhitney_right_pencil
    (f := (((C s * X + C t) * P0) + H0))
    (g := (((C s * X + C t) * P1) + H1))
    hASW
    (fun {z} hz => hpencil_ne hs ht hz)
    (fun {z} hz => hpencil_nn hs ht hz)
    (fun {z} hz => hpencil_pf hs ht hz)

/--
TNN-named version of `prec_of_affine_segment_endpoint_pf_nonneg`.

The LGV certificate layer naturally produces Toeplitz total nonnegativity of
the coefficient sequence.  Since `IsPolyaFrequencySequence` is the same
predicate here, this wrapper avoids a small definitional conversion at the
final handoff.
-/
theorem prec_of_affine_segment_endpoint_tnn_nonneg
    {P0 P1 H0 H1 : ℝ[X]} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hPβ0 : C (1 - β) * P0 + C β * P1 ≠ 0)
    (hHβ0 : C (1 - β) * H0 + C β * H1 ≠ 0)
    (hPβnn : HasNonnegCoeffs (C (1 - β) * P0 + C β * P1))
    (hHβnn : HasNonnegCoeffs (C (1 - β) * H0 + C β * H1))
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hpencil_ne :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        ((((C s * X + C t) * P0) + H0) +
          C z * (((C s * X + C t) * P1) + H1)) ≠ 0)
    (hpencil_nn :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        HasNonnegCoeffs
          ((((C s * X + C t) * P0) + H0) +
            C z * (((C s * X + C t) * P1) + H1)))
    (hpencil_tnn :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        ToeplitzTotallyNonnegative
          (fun n =>
            ((((C s * X + C t) * P0) + H0) +
              C z * (((C s * X + C t) * P1) + H1)).coeff n))
    (hleft :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * P0) + H0))
    (hright :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * P1) + H1)) :
    Prec (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  exact
    prec_of_affine_segment_endpoint_pf_nonneg hβ0 hβ1 hPβ0 hHβ0 hPβnn hHβnn hASW
      hpencil_ne hpencil_nn
      (fun {s t z} hs ht hz => hpencil_tnn hs ht hz)
      hleft hright

/--
Same-degree ASW/PF endpoint wrapper.  This is the version to use when endpoint
real-rootedness should be recovered from positive compatibility plus equal
degree and positive leading coefficients.
-/
theorem prec_of_affine_segment_endpoint_pf_sameDegree_nonneg
    {P0 P1 H0 H1 : ℝ[X]} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hPβ0 : C (1 - β) * P0 + C β * P1 ≠ 0)
    (hHβ0 : C (1 - β) * H0 + C β * H1 ≠ 0)
    (hPβnn : HasNonnegCoeffs (C (1 - β) * P0 + C β * P1))
    (hHβnn : HasNonnegCoeffs (C (1 - β) * H0 + C β * H1))
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hpencil_ne :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        ((((C s * X + C t) * P0) + H0) +
          C z * (((C s * X + C t) * P1) + H1)) ≠ 0)
    (hpencil_nn :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        HasNonnegCoeffs
          ((((C s * X + C t) * P0) + H0) +
            C z * (((C s * X + C t) * P1) + H1)))
    (hpencil_pf :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        IsPolyaFrequencySequence
          (fun n =>
            ((((C s * X + C t) * P0) + H0) +
              C z * (((C s * X + C t) * P1) + H1)).coeff n))
    (hleft_pos :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        HasPosLeadingCoeff (((C s * X + C t) * P0) + H0))
    (hright_pos :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        HasPosLeadingCoeff (((C s * X + C t) * P1) + H1))
    (hdeg :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        (((C s * X + C t) * P1) + H1).natDegree =
          (((C s * X + C t) * P0) + H0).natDegree) :
    Prec (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  refine prec_of_affine_segment_endpoints_sameDegree_nonneg hβ0 hβ1 hPβ0 hHβ0 hPβnn
    hHβnn ?_ hleft_pos hright_pos hdeg
  intro s t hs ht
  exact PosComboRealRooted.of_aissenSchoenbergWhitney_right_pencil
    (f := (((C s * X + C t) * P0) + H0))
    (g := (((C s * X + C t) * P1) + H1))
    hASW
    (fun {z} hz => hpencil_ne hs ht hz)
    (fun {z} hz => hpencil_nn hs ht hz)
    (fun {z} hz => hpencil_pf hs ht hz)

/--
Same-degree TNN-named endpoint wrapper.
-/
theorem prec_of_affine_segment_endpoint_tnn_sameDegree_nonneg
    {P0 P1 H0 H1 : ℝ[X]} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hPβ0 : C (1 - β) * P0 + C β * P1 ≠ 0)
    (hHβ0 : C (1 - β) * H0 + C β * H1 ≠ 0)
    (hPβnn : HasNonnegCoeffs (C (1 - β) * P0 + C β * P1))
    (hHβnn : HasNonnegCoeffs (C (1 - β) * H0 + C β * H1))
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hpencil_ne :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        ((((C s * X + C t) * P0) + H0) +
          C z * (((C s * X + C t) * P1) + H1)) ≠ 0)
    (hpencil_nn :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        HasNonnegCoeffs
          ((((C s * X + C t) * P0) + H0) +
            C z * (((C s * X + C t) * P1) + H1)))
    (hpencil_tnn :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        ToeplitzTotallyNonnegative
          (fun n =>
            ((((C s * X + C t) * P0) + H0) +
              C z * (((C s * X + C t) * P1) + H1)).coeff n))
    (hleft_pos :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        HasPosLeadingCoeff (((C s * X + C t) * P0) + H0))
    (hright_pos :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        HasPosLeadingCoeff (((C s * X + C t) * P1) + H1))
    (hdeg :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        (((C s * X + C t) * P1) + H1).natDegree =
          (((C s * X + C t) * P0) + H0).natDegree) :
    Prec (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  exact
    prec_of_affine_segment_endpoint_pf_sameDegree_nonneg hβ0 hβ1 hPβ0 hHβ0 hPβnn
      hHβnn hASW hpencil_ne hpencil_nn
      (fun {s t z} hs ht hz => hpencil_tnn hs ht hz)
      hleft_pos hright_pos hdeg

/-- Branden's affine-family converse immediately upgrades to the full
Obreschkoff all-combinations conclusion in the nonnegative-coefficient regime:
once `prec_of_affine_family_nonneg` gives `f ≪ g`, every real linear
combination of `f` and `g` is real-rooted. -/
theorem allComboRealRooted_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    AllComboRealRooted f g := by
  exact
    allComboRealRooted_of_prec
      (prec_of_affine_family_nonneg hf0 hg0 hfnn hgnn haff)

/-- Public shifted-pair package extracted from a nonnegative affine family.
This is the corrected same-degree seam after the failed boundary-right-pair
target: the affine family automatically promotes the shifted pair
`(g + X * f, f)` into the clean succ-degree positive-combination regime. -/
theorem shifted_pair_data_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    PosComboRealRooted (g + X * f) f ∧
    HasNonnegCoeffs (g + X * f) ∧
    HasNonnegCoeffs f ∧
    (g + X * f) ≠ 0 ∧
    f ≠ 0 ∧
    HasPosLeadingCoeff (g + X * f) ∧
    HasPosLeadingCoeff f ∧
    (g + X * f).natDegree = f.natDegree + 1 := by
  exact affine_family_shifted_pair_data hf0 hg0 hfnn hgnn haff

/-- A nonnegative affine family already orients the shifted pair:
`f ≺ g + X * f`. This is the public corrected replacement for the earlier
false attempt to orient every boundary pair `(C t * f + g, X * f)`. -/
theorem prec_shifted_pair_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g)) :
    Prec f (g + X * f) := by
  have _hg0 : g ≠ 0 := hg0
  have hshift_nonneg : HasNonnegCoeffs (g + X * f) :=
    hgnn.add (hasNonnegCoeffs_X.mul hfnn)
  have hshift_ne : g + X * f ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      hgnn (hasNonnegCoeffs_X.mul hfnn) (mul_ne_zero X_ne_zero hf0)
  exact
    prec_of_affine_family_nonneg
      hf0 hshift_ne hfnn hshift_nonneg
      (shifted_affine_family_of_affine_family haff)

/-- Same-degree affine families recover the fixed right pair `(g, X * f)` via
the shifted-pair seam. This is the honest same-degree boundary theorem that
survives the linear counterexample to the stronger false bridge. -/
theorem prec_right_pair_of_affine_family_nonneg_sameDegree
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        IsRealRooted (((C s * X + C t) * f) + g))
    (hdeg : g.natDegree = f.natDegree) :
    Prec g (X * f) := by
  exact
    prec_right_pair_of_prec_shifted_pair_sameDegree
      (prec_shifted_pair_of_affine_family_nonneg hf0 hg0 hfnn hgnn haff)
      hf0 hg0 hfnn hgnn hdeg

/-- Public shifted-pair reduction in the same-degree nonnegative regime:
once the corrected shifted pair satisfies `f ≺ g + X * f`, the original pair
already satisfies `f ≺ g`. This packages the internal subtraction step used in
the affine-family same-degree branch. -/
theorem prec_of_prec_shifted_pair_sameDegree_nonneg
    {f g : ℝ[X]}
    (h : Prec f (g + X * f))
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : g.natDegree = f.natDegree) :
    Prec f g := by
  exact
    prec_of_prec_shifted_pair_sameDegree
      h hf0 hg0 hfnn hgnn hdeg

/-- Public wrapper of the internal positive-family degree-gap obstruction:
for a positive-combination real-rooted pair with nonnegative coefficients,
the right degree is at most one more than the left degree. -/
theorem natDegree_right_le_succ_of_posComboRealRooted_of_nonnegCoeffs
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    g.natDegree ≤ f.natDegree + 1 := by
  exact
    natDegree_right_le_succ_of_posComboRealRooted_nonneg
      hfg hf0 hg0 hfnn hgnn

/-- Symmetric degree closeness for positive-combination real-rooted pairs with
nonnegative coefficients. -/
theorem natDegree_close_of_posComboRealRooted_of_nonnegCoeffs
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    f.natDegree ≤ g.natDegree + 1 ∧
      g.natDegree ≤ f.natDegree + 1 := by
  constructor
  · simpa using
      natDegree_right_le_succ_of_posComboRealRooted_of_nonnegCoeffs
        (f := g) (g := f) (PosComboRealRooted.comm hfg) hg0 hf0 hgnn hfnn
  · exact
      natDegree_right_le_succ_of_posComboRealRooted_of_nonnegCoeffs
        (f := f) (g := g) hfg hf0 hg0 hfnn hgnn

lemma isRealRooted_affine_factor {s t : ℝ} (hs : 0 < s) :
    IsRealRooted (C s * X + C t) := by
  have hEq : C s * (X - C (-t / s)) = C s * X + C t := by
    calc
      C s * (X - C (-t / s))
          = C s * X - C s * C (-t / s) := by rw [mul_sub]
      _ = C s * X - C (s * (-t / s)) := by rw [C_mul]
      _ = C s * X - C (-t) := by
            congr 1
            field_simp [hs.ne']
      _ = C s * X + C t := by rw [sub_eq_add_neg, C_neg, neg_neg]
  rw [← hEq]
  exact isRealRooted_C_mul (isRealRooted_X_sub_C (-t / s)) hs.ne'

lemma affine_family_of_zero_left {g : ℝ[X]} (hg : IsRealRooted g) :
    ∀ {s t : ℝ}, 0 < s → 0 < t →
      IsRealRooted (((C s * X + C t) * (0 : ℝ[X])) + g) := by
  intro s t hs ht
  simpa using hg

lemma affine_family_of_zero_right {f : ℝ[X]} (hf : IsRealRooted f) :
    ∀ {s t : ℝ}, 0 < s → 0 < t →
      IsRealRooted (((C s * X + C t) * f) + (0 : ℝ[X])) := by
  intro s t hs ht
  simpa using isRealRooted_mul (isRealRooted_affine_factor (t := t) hs) hf

lemma hasNonnegCoeffs_affine_linear {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasNonnegCoeffs (C a * X + C b) := by
  have hCb : HasNonnegCoeffs (C b) := by
    intro n
    cases n with
    | zero =>
        simp [hb]
    | succ n =>
        simp
  exact (nonnegCoeffs_C_mul ha hasNonnegCoeffs_X).add hCb

lemma prec0_one_affine_linear {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Prec0 (1 : ℝ[X]) (C a * X + C b) := by
  have _hb : 0 < b := hb
  have hInter : Interlaces (1 : ℝ[X]) (C a * X + C b) := by
    refine interlaces_one_linear ?_
    simpa [add_comm] using (Polynomial.natDegree_linear (a := a) (b := b) ha.ne')
  exact hInter.toPrec.toPrec0


end RealRooted
