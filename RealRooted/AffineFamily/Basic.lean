import RealRooted.WagnerRightSum
import RealRooted.WagnerX

/-!
# Affine family: basic conditions and combinations

Definitions and elementary nonnegative affine-combination consequences. The
degree and root-geometry endgame remains in `RealRooted.AffineFamily`.
-/

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
    Has2x2InterlacingProperty0 a b c d :=
  fun s t hs ht => (h s t hs ht).toPrec0

lemma ne_zero_of_self_2x2 (p : ℝ[X])
    (hdiag : Has2x2InterlacingProperty p p p p) :
    p ≠ 0 := by
  have hself :
      Prec
        (((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p)
        (((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p) :=
    hdiag 1 1 zero_lt_one zero_lt_one
  exact fun hp0 => hself.1.1 (by grind)

lemma isRealRooted_of_self_2x2 (p : ℝ[X])
    (hdiag : Has2x2InterlacingProperty p p p p) : (p ≠ 0 ∧ p.Splits) := by
  have hself :
      Prec
        (((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p)
        (((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p) :=
    hdiag 1 1 zero_lt_one zero_lt_one
  have hcombo_rr :
      ((((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p) ≠ 0 ∧
        (((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p).Splits) :=
    hself.1
  have hp0 : p ≠ 0 := ne_zero_of_self_2x2 p hdiag
  have hdiv : p ∣ (((C (1 : ℝ) * X + C (1 : ℝ)) * p) + p) := by simp
  exact isRealRooted_of_dvd hcombo_rr.1 hcombo_rr.2 hp0 hdiv

lemma prec_self_mul_X_of_nonneg {f : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hfnn : HasNonnegCoeffs f) :
    Prec f (X * f) := by
  have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf_ne
  have hXf : ((X * f) ≠ 0 ∧ (X * f).Splits) := isRealRooted_X_mul hf_ne hf_splits
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf_splits hfnn
  have hXf_nonpos : ∀ r ∈ (X * f).roots, r ≤ 0 := by simp_all
  have hXf_pos : HasPosLeadingCoeff (X * f) := hf_pos.X_mul
  have hdeg : f.natDegree + 1 = (X * f).natDegree := by simp_all
  have hself : Prec (X * f) (X * f) := prec_refl hXf.1 hXf.2
  exact
    (prec_iff_prec_mul_X_of_roots_nonpos
      (f := f) (g := X * f) hf_splits hXf.2 hf_pos hXf_pos hf_nonpos hXf_nonpos hdeg).mpr hself

lemma prec_to_prec_mul_X_of_nonneg {f g : ℝ[X]}
    (h : Prec f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec g (X * f) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf.2 hfnn
  have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hg.2 hgnn
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩
  · have hdeg : f.natDegree + 1 = g.natDegree := by lia
    exact
      (prec_iff_prec_mul_X_of_roots_nonpos
        (f := f) (g := g)
        hf.2 hg.2 (hfnn.pos_leadingCoeff hf.1) (hgnn.pos_leadingCoeff hg.1)
        hf_nonpos hg_nonpos hdeg).mp
        ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, Or.inl ⟨hlen, by lia⟩⟩
  · have hdeg : f.natDegree = g.natDegree := by lia
    exact
      prec_sameDegree_to_prec_mul_X_of_roots_nonpos
        ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, Or.inr ⟨hlen, by lia⟩⟩
        hdeg hf_nonpos hg_nonpos

lemma prec_of_prec_mul_X_of_nonneg {f g : ℝ[X]}
    (h : Prec g (X * f)) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec f g := by
  have hprec := h
  have hg : (g ≠ 0 ∧ g.Splits) := h.1
  have hXf : ((X * f) ≠ 0 ∧ (X * f).Splits) := h.2.1
  have hf : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_X_mul hXf.1 hXf.2
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf.2 hfnn
  rcases hprec with ⟨_, _, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩
  · have hss_len : ss.length = g.natDegree := by
      rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hg.2]
    have hrs_len : rs.length = (X * f).natDegree := by
      rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hXf.2]
    have hdeg : f.natDegree = g.natDegree := by simp_all
    exact
      prec_of_prec_mul_X_of_sameDegree_of_roots_nonpos
        h hdeg hf_nonpos
  · have hss_len : ss.length = g.natDegree := by
      rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hg.2]
    have hrs_len : rs.length = (X * f).natDegree := by
      rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hXf.2]
    have hdeg : f.natDegree + 1 = g.natDegree := by simp_all
    exact
      (prec_iff_prec_mul_X_of_roots_nonpos
        (f := f) (g := g)
        hf.2 hg.2 (hfnn.pos_leadingCoeff hf.1) (hgnn.pos_leadingCoeff hg.1)
        hf_nonpos (roots_nonpos_of_nonneg_coeffs hg.2 hgnn) hdeg).mpr h

theorem isRealRooted_affine_combo_of_prec_nonneg {f g : ℝ[X]}
    (h : Prec f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits) := by
  have hf : (f ≠ 0 ∧ f.Splits) := h.1
  have hg : (g ≠ 0 ∧ g.Splits) := h.2.1
  have hXf : ((X * f) ≠ 0 ∧ (X * f).Splits) := isRealRooted_X_mul hf.1 hf.2
  have hg_Xf : Prec g (X * f) := prec_to_prec_mul_X_of_nonneg h hfnn hgnn
  have hf_Xf : Prec f (X * f) := prec_self_mul_X_of_nonneg hf.1 hf.2 hfnn
  have hsXf : Prec (C s * (X * f)) (X * f) := prec_C_mul_self hXf.1 hXf.2 hs.ne'
  have htf : Prec (C t * f) (X * f) := prec_C_mul_left hf_Xf ht.ne'
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg.1
  have hXf_pos : HasPosLeadingCoeff (X * f) :=
    (hfnn.pos_leadingCoeff hf.1).X_mul
  have hsXf_pos : HasPosLeadingCoeff (C s * (X * f)) :=
    hasPosLeadingCoeff_C_mul hs hXf_pos
  have htf_pos : HasPosLeadingCoeff (C t * f) :=
    hasPosLeadingCoeff_C_mul ht (hfnn.pos_leadingCoeff hf.1)
  have hmid : Prec (g + C s * (X * f)) (X * f) :=
    prec_add_of_prec_right_of_posLeadingCoeff hg_Xf hsXf hg_pos hsXf_pos
  have hmid_nonneg : HasNonnegCoeffs (g + C s * (X * f)) := by
    refine hgnn.add ?_
    exact (nonnegCoeffs_C_mul hs.le hfnn.X_mul)
  have hmid_pos : HasPosLeadingCoeff (g + C s * (X * f)) :=
    hmid_nonneg.pos_leadingCoeff hmid.1.1
  have hsum : Prec (C t * f + (g + C s * (X * f))) (X * f) :=
    prec_add_of_prec_right_of_posLeadingCoeff htf hmid htf_pos hmid_pos
  simpa [left_distrib, right_distrib, mul_assoc, add_assoc, add_left_comm, add_comm] using hsum.1

/-- The repeated-column `2 x 2` affine test follows from proper position and
nonnegative coefficients. -/
theorem has2x2InterlacingProperty_sameColumn_of_prec_nonneg {f g : ℝ[X]}
    (h : Prec f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Has2x2InterlacingProperty f f g g := by
  intro s t hs ht
  have hrr := isRealRooted_affine_combo_of_prec_nonneg h hfnn hgnn hs ht
  exact prec_refl hrr.1 hrr.2


end RealRooted
