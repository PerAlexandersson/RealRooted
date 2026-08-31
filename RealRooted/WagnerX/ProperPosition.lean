import RealRooted.Derivative
import RealRooted.WagnerX

/-!
# Wagner `X`-multiplication proper-position bridges

The forward and reverse proper-position transports associated with multiplying
a nonnegative-coefficient polynomial by `X`.
-/

open Polynomial

namespace RealRooted

/-- A split polynomial with nonnegative coefficients precedes its product with
`X`. -/
lemma prec_self_X_mul_of_nonneg {f : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hfnn : HasNonnegCoeffs f) :
    Prec f (X * f) := by
  have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf_ne
  have hXf : ((X * f) ≠ 0 ∧ (X * f).Splits) := isRealRooted_X_mul hf_ne hf_splits
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hf_splits hfnn
  have hXf_nonpos : ∀ r ∈ (X * f).roots, r ≤ 0 := by simp_all
  have hXf_pos : HasPosLeadingCoeff (X * f) := hf_pos.X_mul
  have hdeg : f.natDegree + 1 = (X * f).natDegree := by simp_all
  have hself : Prec (X * f) (X * f) := prec_refl hXf.1 hXf.2
  exact
    (prec_iff_prec_mul_X_of_roots_nonpos
      (f := f) (g := X * f) hf_splits hXf.2 hf_pos hXf_pos hf_nonpos hXf_nonpos hdeg).mpr hself

/-- If `f` precedes `g`, then nonnegative coefficients transport the relation
to `g` and `X * f`. -/
lemma prec_to_X_mul_of_nonneg {f g : ℝ[X]}
    (h : Prec f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec g (X * f) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hf.2 hfnn
  have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hg.2 hgnn
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩
  · have hdeg : f.natDegree + 1 = g.natDegree := by lia
    exact
      (prec_iff_prec_mul_X_of_roots_nonpos
        (f := f) (g := g) hf.2 hg.2 (hfnn.pos_leadingCoeff hf.1)
        (hgnn.pos_leadingCoeff hg.1) hf_nonpos hg_nonpos hdeg).mp
        ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, Or.inl ⟨hlen, by lia⟩⟩
  · have hdeg : f.natDegree = g.natDegree := by lia
    exact
      prec_sameDegree_to_prec_mul_X_of_roots_nonpos
        ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, Or.inr ⟨hlen, by lia⟩⟩
        hdeg hf_nonpos hg_nonpos

/-- The reverse Wagner transport recovers `Prec f g` from `Prec g (X * f)`
when both polynomials have nonnegative coefficients. -/
lemma prec_of_prec_X_mul_of_nonneg {f g : ℝ[X]}
    (h : Prec g (X * f)) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec f g := by
  have hprec := h
  have hg : (g ≠ 0 ∧ g.Splits) := h.1
  have hXf : ((X * f) ≠ 0 ∧ (X * f).Splits) := h.2.1
  have hf : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_X_mul hXf.1 hXf.2
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hf.2 hfnn
  rcases hprec with ⟨_, _, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩
  · have hss_len : ss.length = g.natDegree := by
      rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hg.2]
    have hrs_len : rs.length = (X * f).natDegree := by
      rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hXf.2]
    have hdeg : f.natDegree = g.natDegree := by simp_all
    exact prec_of_prec_mul_X_of_sameDegree_of_roots_nonpos h hdeg hf_nonpos
  · have hss_len : ss.length = g.natDegree := by
      rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hg.2]
    have hrs_len : rs.length = (X * f).natDegree := by
      rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hXf.2]
    have hdeg : f.natDegree + 1 = g.natDegree := by simp_all
    exact
      (prec_iff_prec_mul_X_of_roots_nonpos
        (f := f) (g := g) hf.2 hg.2 (hfnn.pos_leadingCoeff hf.1)
        (hgnn.pos_leadingCoeff hg.1) hf_nonpos
        (roots_nonpos_of_nonneg_coeffs hg.2 hgnn) hdeg).mpr h

/-- The derivative of a split nonnegative-coefficient polynomial preserves the
Wagner `X`-multiplication proper-position relation. -/
theorem prec_X_derivative_X_self_of_splits_nonneg {f : ℝ[X]}
    (hf : f.Splits) (hdeg : 2 ≤ f.natDegree) (hfnn : HasNonnegCoeffs f) :
    Prec (X * f.derivative) (X * f) := by
  have hder : Prec f.derivative f := (derivative_interlaces hf hdeg).toPrec
  exact prec_mul_X_both_of_roots_nonpos hder
    (roots_nonpos_of_nonneg_coeffs hder.1.2 hfnn.derivative)
    (roots_nonpos_of_nonneg_coeffs hf hfnn)

end RealRooted
