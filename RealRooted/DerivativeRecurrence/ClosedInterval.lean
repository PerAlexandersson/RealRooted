module

public import RealRooted.Basic.ProperPosition
public import RealRooted.Basic.Coefficients
import RealRooted.DerivativeRecurrence.EndpointWindow
import RealRooted.MaWang.DerivativeStep
import RealRooted.WagnerX.ListInterlacing
import RealRooted.Interlacing.Residue
import RealRooted.Interlacing.Multiplicity
import RealRooted.Linear
import RealRooted.Mathlib.Algebra.Polynomial.FieldDivision
import RealRooted.WagnerRightSum.Sign
import RealRooted.Mathlib.Algebra.Polynomial.Splits

/-!
# Closed endpoints for derivative recurrences of arbitrary polynomial degree

The derivative coefficient need not be quadratic. We require independently checked degree
growth and positive leading coefficients, so cubic leading-term cancellation is covered.
Endpoint multiplicity zero is included.

Source: Ma--Wang, *q-Eulerian polynomials and polynomials with only real zeros*, Theorem 2
(arXiv:math/0611826v2), and the unpublished manuscript in RealRooted issue #2192.
-/

public section

open Polynomial Set

namespace RealRooted

/-- Cancelling a common power of a real linear factor preserves proper position. -/
private lemma strictInterl_cancel_pow {f g : ℝ[X]} (e : ℝ) (m : ℕ)
    (h : StrictInterl ((X - C e) ^ m * f) ((X - C e) ^ m * g)) :
    StrictInterl f g := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    apply ih
    apply StrictInterl.of_mul_X_sub_C_both (r := e)
    simpa only [pow_succ', mul_assoc] using h

/-- Divide out the input's full endpoint multiplicity, and the same factor from its successor.
The cofactor endpoint value is the Ma--Wang threshold times the input cofactor value. -/
private lemma derivativeStep_endpoint_cofactor {f u v : ℝ[X]} {e : ℝ}
    (hf : HasPosLeadingCoeff f) (hF : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree + 1)
    (hinter : StrictInterl f (u * f + v * f.derivative)) (hv : v.eval e = 0) :
    ∃ q H : ℝ[X], (X - C e) ^ f.rootMultiplicity e * q = f ∧ q.eval e ≠ 0 ∧
      HasPosLeadingCoeff q ∧ HasPosLeadingCoeff H ∧ StrictInterl q H ∧
      H.natDegree = q.natDegree + 1 ∧
      u * f + v * f.derivative = (X - C e) ^ f.rootMultiplicity e * H ∧
      H.eval e = (u.eval e + f.rootMultiplicity e * v.derivative.eval e) * q.eval e := by
  let q := f /ₘ (X - C e) ^ f.rootMultiplicity e
  let w := v /ₘ (X - C e)
  let H := (u + C (f.rootMultiplicity e : ℝ) * w) * q + v * q.derivative
  have hfactor : (X - C e) ^ f.rootMultiplicity e * q = f :=
    f.pow_mul_divByMonic_rootMultiplicity_eq e
  have hqeval : q.eval e ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero e hf.ne_zero
  have hqpos : HasPosLeadingCoeff q :=
    hasPosLeadingCoeff_of_pow_X_sub_C_mul (by rw [hfactor]; exact hf)
  have hw : (X - C e) * w = v := mul_divByMonic_eq_iff_isRoot.mpr hv
  have hwval : w.eval e = v.derivative.eval e := eval_divByMonic_at_root hv
  have hFfactor : u * f + v * f.derivative = (X - C e) ^ f.rootMultiplicity e * H := by
    dsimp [H]
    nth_rw 1 [← hfactor]
    nth_rw 2 [← hfactor]
    generalize f.rootMultiplicity e = m
    rw [← hw]
    cases m with
    | zero => simp
    | succ m =>
      rw [derivative_mul, derivative_X_sub_C_pow]
      simp only [Nat.succ_sub_one]
      ring
  have hHpos : HasPosLeadingCoeff H :=
    hasPosLeadingCoeff_of_pow_X_sub_C_mul (by rw [← hFfactor]; exact hF)
  have hqH : StrictInterl q H := by
    rw [hFfactor] at hinter
    nth_rw 1 [← hfactor] at hinter
    exact strictInterl_cancel_pow e _ hinter
  have hqdeg := natDegree_mul (pow_ne_zero (f.rootMultiplicity e) (X_sub_C_ne_zero e))
    hqpos.ne_zero
  have hHdeg := natDegree_mul (pow_ne_zero (f.rootMultiplicity e) (X_sub_C_ne_zero e))
    hHpos.ne_zero
  rw [hfactor] at hqdeg
  rw [← hFfactor, hdeg] at hHdeg
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one] at hqdeg hHdeg
  refine ⟨q, H, hfactor, hqeval, hqpos, hHpos, hqH, by lia, hFfactor, ?_⟩
  simp [H, hv, hwval]

/-- At an endpoint where `v` vanishes, the multiplicity of `u*f+v*f'` is unchanged unless
the Ma--Wang threshold vanishes, when it increases by exactly one. This includes multiplicity
zero and imposes no degree bound on `u` or `v`. -/
theorem rootMultiplicity_derivativeStep_of_eval_eq_zero {f u v : ℝ[X]} {e : ℝ}
    (hf : HasPosLeadingCoeff f) (hF : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree + 1)
    (hinter : StrictInterl f (u * f + v * f.derivative)) (hv : v.eval e = 0) :
    (u * f + v * f.derivative).rootMultiplicity e =
      if u.eval e + f.rootMultiplicity e * v.derivative.eval e = 0
        then f.rootMultiplicity e + 1 else f.rootMultiplicity e := by
  obtain ⟨q, H, -, hqeval, -, hHpos, hqH, -, hFfactor, hHeval⟩ :=
    derivativeStep_endpoint_cofactor hf hF hdeg hinter hv
  have hq0 : q.rootMultiplicity e = 0 := rootMultiplicity_eq_zero hqeval
  have hm : H.rootMultiplicity e =
      if u.eval e + f.rootMultiplicity e * v.derivative.eval e = 0 then 1 else 0 := by
    split_ifs with heq
    · have hroot : H.IsRoot e := by simp [IsRoot.def, hHeval, heq]
      have hpos := (rootMultiplicity_pos hHpos.ne_zero).2 hroot
      have hle := (hqH.rootMultiplicity_bounds e).2
      rw [hq0] at hle
      lia
    · apply rootMultiplicity_eq_zero
      rw [IsRoot.def, hHeval]
      exact mul_ne_zero heq hqeval
  rw [hFfactor, rootMultiplicity_mul
    (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero e)) hHpos.ne_zero),
    rootMultiplicity_X_sub_C_pow, hm]
  split_ifs <;> rfl

/-- The lower endpoint condition for an interlacing derivative step of arbitrary degree. -/
theorem roots_ge_derivativeStep_iff {f u v : ℝ[X]} {L : ℝ}
    (hf : HasPosLeadingCoeff f) (hF : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree + 1)
    (hinter : StrictInterl f (u * f + v * f.derivative))
    (hroots : ∀ r ∈ f.roots, L ≤ r) (hv : v.eval L = 0) :
    (∀ r ∈ (u * f + v * f.derivative).roots, L ≤ r) ↔
      u.eval L + f.rootMultiplicity L * v.derivative.eval L ≤ 0 := by
  obtain ⟨q, H, hfactor, hqeval, hqpos, hHpos, hqH, hHdeg, hFfactor, hHeval⟩ :=
    derivativeStep_endpoint_cofactor hf hF hdeg hinter hv
  have hqroots : ∀ r ∈ q.roots, L < r := by
    intro r hr
    have hmem : r ∈ f.roots := by
      rw [← hfactor, roots_mul
        (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero L)) hqpos.ne_zero)]
      exact Multiset.mem_add.mpr (Or.inr hr)
    exact lt_of_le_of_ne (hroots r hmem) (fun h => hqeval (h ▸ (mem_roots hqpos.ne_zero).mp hr))
  have hrootiff : (∀ r ∈ (u * f + v * f.derivative).roots, L ≤ r) ↔
      ∀ r ∈ H.roots, L ≤ r := by
    rw [hFfactor, roots_mul
      (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero L)) hHpos.ne_zero)]
    simp only [Multiset.mem_add, roots_pow, roots_X_sub_C, Multiset.mem_nsmul,
      Multiset.mem_singleton]
    constructor
    · exact fun h r hr => h r (Or.inr hr)
    · rintro h r (⟨-, rfl⟩ | hr)
      · exact le_rfl
      · exact h r hr
  rw [hrootiff, roots_ge_iff_neg_one_pow_mul_eval_nonneg_of_interlaces
    (hqH.toInterlaces hHdeg.symm) hHpos hqroots]
  have heq : (-1 : ℝ) ^ H.natDegree * H.eval L =
      -(u.eval L + f.rootMultiplicity L * v.derivative.eval L) *
        ((-1 : ℝ) ^ q.natDegree * q.eval L) := by
    rw [hHdeg, pow_succ, hHeval]
    ring
  have hsign := hqH.1.2.eval_mul_leadingCoeff_neg_one_pow_pos hqpos.ne_zero hqeval
  have hfilter : q.roots.filter (L < ·) = q.roots :=
    Multiset.filter_eq_self.mpr hqroots
  rw [hfilter, Polynomial.splits_iff_card_roots.mp hqH.1.2] at hsign
  have hsign' : 0 < (-1 : ℝ) ^ q.natDegree * q.eval L := by
    apply pos_of_mul_pos_left _ hqpos.le
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsign
  rw [heq, mul_nonneg_iff_of_pos_right hsign', neg_nonneg]

/-- The upper endpoint condition for an interlacing derivative step of arbitrary degree. -/
theorem roots_le_derivativeStep_iff {f u v : ℝ[X]} {U : ℝ}
    (hf : HasPosLeadingCoeff f) (hF : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree + 1)
    (hinter : StrictInterl f (u * f + v * f.derivative))
    (hroots : ∀ r ∈ f.roots, r ≤ U) (hv : v.eval U = 0) :
    (∀ r ∈ (u * f + v * f.derivative).roots, r ≤ U) ↔
      0 ≤ u.eval U + f.rootMultiplicity U * v.derivative.eval U := by
  obtain ⟨q, H, hfactor, hqeval, hqpos, hHpos, hqH, hHdeg, hFfactor, hHeval⟩ :=
    derivativeStep_endpoint_cofactor hf hF hdeg hinter hv
  have hqroots : ∀ r ∈ q.roots, r < U := by
    intro r hr
    have hmem : r ∈ f.roots := by
      rw [← hfactor, roots_mul
        (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero U)) hqpos.ne_zero)]
      exact Multiset.mem_add.mpr (Or.inr hr)
    exact lt_of_le_of_ne (hroots r hmem) (fun h => hqeval (h ▸ (mem_roots hqpos.ne_zero).mp hr))
  have hrootiff : (∀ r ∈ (u * f + v * f.derivative).roots, r ≤ U) ↔
      ∀ r ∈ H.roots, r ≤ U := by
    rw [hFfactor, roots_mul
      (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero U)) hHpos.ne_zero)]
    simp only [Multiset.mem_add, roots_pow, roots_X_sub_C, Multiset.mem_nsmul,
      Multiset.mem_singleton]
    constructor
    · exact fun h r hr => h r (Or.inr hr)
    · rintro h r (⟨-, rfl⟩ | hr)
      · exact le_rfl
      · exact h r hr
  rw [hrootiff, roots_le_iff_eval_nonneg_of_interlaces
    (hqH.toInterlaces hHdeg.symm) hHpos hqroots, hHeval,
    mul_nonneg_iff_of_pos_right (eval_pos_of_all_roots_lt hqpos.ne_zero hqH.1.2 hqpos hqroots)]

/-- The complete closed-interval endpoint criterion for a first derivative step. There is
no restriction on the degrees of the two coefficient polynomials: degree growth is supplied
independently, allowing leading-term cancellation. -/
theorem derivativeStep_roots_mem_Icc_iff {f u v : ℝ[X]} {L U : ℝ}
    (hf : HasPosLeadingCoeff f) (hF : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree + 1)
    (hs : f.Splits) (hroots : ∀ r ∈ f.roots, r ∈ Icc L U)
    (hv : ∀ r ∈ Icc L U, v.eval r ≤ 0) (hvL : v.eval L = 0) (hvU : v.eval U = 0) :
    (u * f + v * f.derivative).Splits ∧ Interlaces f (u * f + v * f.derivative) ∧
      ((∀ r ∈ (u * f + v * f.derivative).roots, r ∈ Icc L U) ↔
        u.eval L + f.rootMultiplicity L * v.derivative.eval L ≤ 0 ∧
        0 ≤ u.eval U + f.rootMultiplicity U * v.derivative.eval U) := by
  have hinter := MaWang.strictInterl_derivative_of_nonpos_of_splits hs
    (by lia) hdeg.le hF hf (fun r hr => hv r (hroots r ((mem_roots hf.ne_zero).mpr hr)))
  refine ⟨hinter.2.1.2, hinter.toInterlaces hdeg.symm, ?_⟩
  have hlo := roots_ge_derivativeStep_iff hf hF hdeg hinter
    (fun r hr => (hroots r hr).1) hvL
  have hup := roots_le_derivativeStep_iff hf hF hdeg hinter
    (fun r hr => (hroots r hr).2) hvU
  constructor
  · intro h
    exact ⟨hlo.mp (fun r hr => (h r hr).1), hup.mp (fun r hr => (h r hr).2)⟩
  · rintro ⟨hl, hu⟩ r hr
    exact ⟨hlo.mpr hl r hr, hup.mpr hu r hr⟩

/-- At a point where the derivative coefficient is nonzero, a derivative step in proper
position preserves simplicity. The point need not be a root of the input. -/
theorem rootMultiplicity_derivativeStep_le_one {f u v : ℝ[X]} {r : ℝ}
    (hinter : StrictInterl f (u * f + v * f.derivative)) (hv : v.eval r ≠ 0)
    (hsimple : f.rootMultiplicity r ≤ 1) :
    (u * f + v * f.derivative).rootMultiplicity r ≤ 1 := by
  by_contra h
  have hlarge : 1 < (u * f + v * f.derivative).rootMultiplicity r := by lia
  have hfroot := hinter.isRoot_of_one_lt_rootMultiplicity hlarge
  have hFroot := (rootMultiplicity_pos hinter.2.1.1).mp (by lia :
    0 < (u * f + v * f.derivative).rootMultiplicity r)
  have hder : f.derivative.IsRoot r := by
    rw [IsRoot.def] at hfroot hFroot ⊢
    simpa only [eval_add, eval_mul, hfroot, mul_zero, zero_add,
      mul_eq_zero, or_iff_right hv] using hFroot
  have hm := (one_lt_rootMultiplicity_iff_isRoot hinter.1.1).mpr ⟨hfroot, hder⟩
  lia

end RealRooted
