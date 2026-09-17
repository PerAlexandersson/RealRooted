import RealRooted.Applications.OEIS.A144696.FactorialWeight
import RealRooted.Interlacing.ResidueCriterion
import RealRooted.MaWang.StrictStep
import RealRooted.Wagner.NonpositiveRoots

/-!
# Strict interlacing for the A144696 Bernstein-image triangle

The factorial-weight endpoint inequality feeds a residue certificate for the
degree-dropping auxiliary polynomial. A strict Ma--Wang step then produces the
shifted vertical edge, and Wagner's two addition theorems propagate it through
the Pascal relation. The mutual induction records proper position, simple
roots, and absence of common roots on every adjacent edge.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted

/-- Every in-range A144696 Bernstein image has positive leading coefficient. -/
theorem hasPosLeadingCoeff_a144696BernsteinImage
    {d k : ℕ} (hk : k ≤ d) :
    HasPosLeadingCoeff (a144696BernsteinImage d k) := by
  rw [HasPosLeadingCoeff, leadingCoeff_a144696BernsteinImage hk]
  positivity

/-- Every in-range A144696 Bernstein image is positive at `1`. -/
theorem eval_one_pos_a144696BernsteinImage
    {d k : ℕ} (hk : k ≤ d) :
    0 < (a144696BernsteinImage d k).eval 1 :=
  eval_pos_of_hasNonnegCoeffs
    (hasNonnegCoeffs_a144696BernsteinImage d k)
    (hasPosLeadingCoeff_a144696BernsteinImage hk).ne_zero
    zero_lt_one

/-- Every root of an in-range A144696 Bernstein image is strictly negative. -/
theorem roots_neg_a144696BernsteinImage
    {d k : ℕ} (hk : k ≤ d) :
    ∀ r ∈ (a144696BernsteinImage d k).roots, r < 0 := by
  intro r hr
  have hnonpos := roots_nonpos_of_hasNonnegCoeffs
    (hasNonnegCoeffs_a144696BernsteinImage d k) r hr
  have hzeroeval : (a144696BernsteinImage d k).eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact (coeff_pos_a144696BernsteinImage hk (by lia)).ne'
  have hrroot : (a144696BernsteinImage d k).IsRoot r :=
    isRoot_of_mem_roots hr
  have hrne : r ≠ 0 := by
    intro hrzero
    subst r
    exact hzeroeval hrroot
  exact lt_of_le_of_ne hnonpos hrne

/-- The A144696 auxiliary is the standard residue auxiliary at `1`. -/
theorem a144696Auxiliary_eq_residueAuxiliary
    {d k : ℕ} (hk : k < d) :
    a144696Auxiliary d k =
      residueAuxiliary 1 (d - k : ℝ)
        (a144696BernsteinImage d k)
        (a144696BernsteinImage (d - 1) k) := by
  rw [a144696Auxiliary, residueAuxiliary,
    natDegree_a144696BernsteinImage hk.le,
    a144696BernsteinImage_pascal hk]
  rw [Nat.cast_sub hk.le]
  simp only [map_sub, map_one]
  have hd : (d : ℝ) = (k : ℝ) + ((d : ℝ) - (k : ℝ)) := by ring
  rw [show C (d : ℝ) = C (k : ℝ) + C ((d : ℝ) - (k : ℝ)) by
    rw [← map_add, ← hd]]
  ring

/-- The factorial-weight endpoint gap in the normalization used by the residue
criterion. -/
theorem a144696_residue_eval_gap {d k : ℕ} (hk : k < d) :
    ((d - k : ℕ) : ℝ) *
        (a144696BernsteinImage (d - 1) k).eval 1 <
      (a144696BernsteinImage d k).eval 1 := by
  have hprevRange : k ≤ d - 1 := by lia
  have hprevEval := eval_one_pos_a144696BernsteinImage hprevRange
  have hgap := a144696_eval_gap_pos (d := d) (k := k) hk
  have hpascal := congrArg (Polynomial.eval 1)
    (a144696BernsteinImage_pascal hk)
  simp only [eval_add] at hpascal
  have hfactor : ((d - k : ℕ) : ℝ) ≤ d + 1 := by
    exact_mod_cast (show d - k ≤ d + 1 by lia)
  have hmul := mul_le_mul_of_nonneg_right hfactor hprevEval.le
  nlinarith

/-- On an internal edge, the factorial endpoint gap gives the auxiliary the
same strict sign as the derivative at every current-row root. -/
theorem a144696Auxiliary_eval_mul_derivative_pos_of_prec
    {d k : ℕ} (hk : k < d)
    (hprec : StrictInterl (a144696BernsteinImage (d - 1) k)
      (a144696BernsteinImage d k))
    (hcurSimple : HasSimpleRoots (a144696BernsteinImage d k))
    {r : ℝ} (hr : (a144696BernsteinImage d k).IsRoot r) :
    0 < (a144696Auxiliary d k).eval r *
      (a144696BernsteinImage d k).derivative.eval r := by
  have hprevRange : k ≤ d - 1 := by lia
  have hcurPos := hasPosLeadingCoeff_a144696BernsteinImage hk.le
  have hprevPos := hasPosLeadingCoeff_a144696BernsteinImage hprevRange
  have hprevDeg : (a144696BernsteinImage (d - 1) k).degree <
      (a144696BernsteinImage d k).natDegree := by
    rw [degree_eq_natDegree hprevPos.ne_zero,
      natDegree_a144696BernsteinImage hprevRange,
      natDegree_a144696BernsteinImage hk.le]
    exact_mod_cast (show d - 1 < d by lia)
  rw [a144696Auxiliary_eq_residueAuxiliary hk]
  apply residueAuxiliary_eval_mul_derivative_pos hprec hcurPos hprevPos
    (by rw [natDegree_a144696BernsteinImage hk.le]; lia)
    hprevDeg hcurSimple (by rw [← Nat.cast_sub hk.le]; positivity)
  · intro s hs
    have hsneg := roots_neg_a144696BernsteinImage hk.le s hs
    linarith
  · simpa [Nat.cast_sub hk.le] using a144696_residue_eval_gap hk
  · exact hr

/-- On an internal edge, the residue auxiliary strictly interlaces the current
Bernstein image. -/
theorem a144696Auxiliary_interlaces_of_prec
    {d k : ℕ} (hk : k < d)
    (hprec : StrictInterl (a144696BernsteinImage (d - 1) k)
      (a144696BernsteinImage d k))
    (hcurSimple : HasSimpleRoots (a144696BernsteinImage d k)) :
    Interlaces (a144696Auxiliary d k) (a144696BernsteinImage d k) := by
  have hprevRange : k ≤ d - 1 := by lia
  have hcurPos := hasPosLeadingCoeff_a144696BernsteinImage hk.le
  have hprevPos := hasPosLeadingCoeff_a144696BernsteinImage hprevRange
  have hprevDeg : (a144696BernsteinImage (d - 1) k).degree <
      (a144696BernsteinImage d k).natDegree := by
    rw [degree_eq_natDegree hprevPos.ne_zero,
      natDegree_a144696BernsteinImage hprevRange,
      natDegree_a144696BernsteinImage hk.le]
    exact_mod_cast (show d - 1 < d by lia)
  rw [a144696Auxiliary_eq_residueAuxiliary hk]
  apply residueAuxiliary_interlaces hprec hcurPos hprevPos
    (by rw [natDegree_a144696BernsteinImage hk.le]; lia)
    hprevDeg hcurSimple (by rw [← Nat.cast_sub hk.le]; positivity)
  · intro r hr
    have hneg := roots_neg_a144696BernsteinImage hk.le r hr
    linarith
  · simpa [Nat.cast_sub hk.le] using a144696_residue_eval_gap hk

/-- On the diagonal edge, the auxiliary has the derivative's strict sign at
every root. -/
theorem a144696Auxiliary_diagonal_eval_mul_derivative_pos
    {d : ℕ}
    (hsimple : HasSimpleRoots (a144696BernsteinImage d d))
    {r : ℝ} (hr : (a144696BernsteinImage d d).IsRoot r) :
    0 < (a144696Auxiliary d d).eval r *
      (a144696BernsteinImage d d).derivative.eval r := by
  let f := a144696BernsteinImage d d
  have hfpos : HasPosLeadingCoeff f :=
    hasPosLeadingCoeff_a144696BernsteinImage (le_refl d)
  have hrmem : r ∈ f.roots := (mem_roots hfpos.ne_zero).mpr hr
  have hrneg := roots_neg_a144696BernsteinImage (le_refl d) r hrmem
  have hderne := hsimple.eval_derivative_ne_zero hr
  have heval : (a144696Auxiliary d d).eval r =
      (1 - r) * f.derivative.eval r := by
    have hreval : f.eval r = 0 := hr
    rw [a144696Auxiliary]
    simp only [Nat.sub_self, Nat.cast_zero, map_zero, eval_add, eval_mul,
      eval_sub, eval_one, eval_X, eval_C, zero_mul, add_zero]
    change (1 - r) * f.derivative.eval r + (d : ℝ) * f.eval r = _
    rw [hreval, mul_zero, add_zero]
  rw [heval]
  calc
    0 < (1 - r) * (f.derivative.eval r) ^ 2 :=
      mul_pos (by linarith) (sq_pos_iff.mpr hderne)
    _ = (1 - r) * f.derivative.eval r * f.derivative.eval r := by ring

/-- The diagonal auxiliary strictly interlaces the diagonal Bernstein image. -/
theorem a144696Auxiliary_diagonal_interlaces
    {d : ℕ} (hd : 1 ≤ d)
    (hsplits : (a144696BernsteinImage d d).Splits)
    (hsimple : HasSimpleRoots (a144696BernsteinImage d d)) :
    Interlaces (a144696Auxiliary d d) (a144696BernsteinImage d d) := by
  let f := a144696BernsteinImage d d
  have hfdeg : f.natDegree = d := by
    exact natDegree_a144696BernsteinImage (le_refl d)
  have hfpos : HasPosLeadingCoeff f :=
    hasPosLeadingCoeff_a144696BernsteinImage (le_refl d)
  have hsplitsF : f.Splits := hsplits
  have hsimpleF : HasSimpleRoots f := hsimple
  have heq : a144696Auxiliary d d = residueAuxiliary 1 0 f 0 := by
    rw [a144696Auxiliary, residueAuxiliary, hfdeg]
    simp only [Nat.sub_self, Nat.cast_zero, map_zero, zero_mul, add_zero,
      mul_zero, sub_zero, map_one]
    ring
  have hdegree : (a144696Auxiliary d d).degree < f.natDegree := by
    rw [heq]
    apply residueAuxiliary_degree_lt
    · rw [hfdeg]
      exact hd
    · rw [hfdeg]
      simp
  have hroots_ne : f.roots ≠ 0 := by
    intro hzero
    have hcard : f.roots.card = f.natDegree := card_roots_of_splits hsplitsF
    rw [hzero] at hcard
    simp [hfdeg] at hcard
    lia
  obtain ⟨r, hrmem⟩ := Multiset.exists_mem_of_ne_zero hroots_ne
  have hrroot : f.IsRoot r := isRoot_of_mem_roots hrmem
  have hrootSign : ∀ r, f.IsRoot r →
      0 < (a144696Auxiliary d d).eval r * f.derivative.eval r :=
    fun _ hr ↦ a144696Auxiliary_diagonal_eval_mul_derivative_pos hsimpleF hr
  have hqne : a144696Auxiliary d d ≠ 0 := by
    intro hzero
    have hsign := hrootSign r hrroot
    simp [hzero] at hsign
  have hqdeg : (a144696Auxiliary d d).natDegree < f.natDegree :=
    (natDegree_lt_iff_degree_lt hqne).2 hdegree
  exact interlaces_of_eval_mul_derivative_pos hsplitsF hfpos hqdeg hrootSign

/-- One strict shifted vertical step from an auxiliary derivative-sign
certificate. -/
theorem a144696BernsteinImage_shifted_step
    {d k : ℕ} (hd : 1 ≤ d) (hk : k ≤ d)
    (hsplits : (a144696BernsteinImage d k).Splits)
    (hauxSign : ∀ r, (a144696BernsteinImage d k).IsRoot r →
      0 < (a144696Auxiliary d k).eval r *
        (a144696BernsteinImage d k).derivative.eval r) :
    StrictInterl (a144696BernsteinImage d k)
        (a144696BernsteinImage (d + 1) (k + 1)) ∧
      (∀ r, (a144696BernsteinImage d k).IsRoot r →
        ¬ (a144696BernsteinImage (d + 1) (k + 1)).IsRoot r) ∧
      HasSimpleRoots (a144696BernsteinImage (d + 1) (k + 1)) := by
  let f := a144696BernsteinImage d k
  let F := a144696BernsteinImage (d + 1) (k + 1)
  have hfpos : HasPosLeadingCoeff f :=
    hasPosLeadingCoeff_a144696BernsteinImage hk
  have hFpos : HasPosLeadingCoeff F :=
    hasPosLeadingCoeff_a144696BernsteinImage (by lia)
  have hfdeg : f.natDegree = d := natDegree_a144696BernsteinImage hk
  have hFdeg : F.natDegree = d + 1 :=
    natDegree_a144696BernsteinImage (by lia)
  have hrec : F = (1 + C 2 * X) * f + X * a144696Auxiliary d k :=
    a144696BernsteinImage_succ_eq_auxiliary hk
  have hXneg : ∀ r, f.IsRoot r → (X : ℝ[X]).eval r < 0 := by
    intro r hr
    rw [eval_X]
    apply roots_neg_a144696BernsteinImage hk r
    exact (mem_roots hfpos.ne_zero).mpr hr
  have hstep := prec_and_hasSimpleRoots_of_auxiliary_sign_succ
    hsplits hfpos hFpos (by rw [hfdeg]; exact hd)
      (by rw [hFdeg, hfdeg]) hrec hauxSign hXneg
  exact ⟨hstep.1,
    noCommonRoot_of_auxiliary_sign hrec hauxSign hXneg,
    hstep.2⟩

private theorem a144696BernsteinImage_zero_zero :
    a144696BernsteinImage 0 0 = (1 : ℝ[X]) := by
  rw [a144696BernsteinImage_diagonal]
  rfl

private theorem a144696BernsteinImage_one_one :
    a144696BernsteinImage 1 1 = (1 + C 2 * X : ℝ[X]) := by
  rw [a144696BernsteinImage_diagonal, a144696Polynomial_succ]
  simp [a144696Polynomial]

private theorem a144696BernsteinImage_one_zero :
    a144696BernsteinImage 1 0 = (2 + C 2 * X : ℝ[X]) := by
  rw [a144696BernsteinImage_eq_sum]
  norm_num [Finset.sum_range_succ, a144696Polynomial]
  ring

private theorem a144696BernsteinImage_one_horizontal :
    StrictInterl (a144696BernsteinImage 1 0)
    (a144696BernsteinImage 1 1) := by
  rw [a144696BernsteinImage_one_zero, a144696BernsteinImage_one_one]
  have hbase : StrictInterl (X + C 1 : ℝ[X]) (X + C (1 / 2 : ℝ)) :=
    (prec_X_add_C_iff (a := (1 / 2 : ℝ)) (b := 1)).2 (by norm_num)
  have hscaled := StrictInterl.C_mul_right
    (StrictInterl.C_mul_left hbase (a := 2) (by norm_num)) (a := 2) (by norm_num)
  have htwo : (2 : ℝ[X]) = C 2 := by
    ext n
    cases n <;> simp
  have hone : (1 : ℝ[X]) = C 1 := by simp
  rw [htwo, hone]
  convert hscaled using 1
  · rw [mul_add, ← map_mul]
    norm_num
    ring
  · rw [mul_add, ← map_mul]
    norm_num
    ring

private structure A144696RowCertificate (d : ℕ) : Prop where
  splits : ∀ k, k ≤ d → (a144696BernsteinImage d k).Splits
  simple : ∀ k, k ≤ d → HasSimpleRoots (a144696BernsteinImage d k)
  horizontal : ∀ k, k < d →
    StrictInterl (a144696BernsteinImage d k) (a144696BernsteinImage d (k + 1))
  horizontalNoCommon : ∀ k, k < d → ∀ r,
    (a144696BernsteinImage d k).IsRoot r →
      ¬ (a144696BernsteinImage d (k + 1)).IsRoot r
  vertical : ∀ k, k < d →
    StrictInterl (a144696BernsteinImage (d - 1) k) (a144696BernsteinImage d k)
  verticalNoCommon : ∀ k, k < d → ∀ r,
    (a144696BernsteinImage (d - 1) k).IsRoot r →
      ¬ (a144696BernsteinImage d k).IsRoot r
  shifted : ∀ k, k < d →
    StrictInterl (a144696BernsteinImage (d - 1) k)
      (a144696BernsteinImage d (k + 1))
  shiftedNoCommon : ∀ k, k < d → ∀ r,
    (a144696BernsteinImage (d - 1) k).IsRoot r →
      ¬ (a144696BernsteinImage d (k + 1)).IsRoot r

private theorem a144696RowCertificate_zero : A144696RowCertificate 0 := by
  constructor
  · intro k hk
    have hk0 : k = 0 := by lia
    subst k
    rw [a144696BernsteinImage_zero_zero]
    simp
  · intro k hk
    have hk0 : k = 0 := by lia
    subst k
    rw [a144696BernsteinImage_zero_zero]
    simp [HasSimpleRoots]
  · intro k hk
    lia
  · intro k hk
    lia
  · intro k hk
    lia
  · intro k hk
    lia
  · intro k hk
    lia
  · intro k hk
    lia

private theorem a144696RowCertificate_one : A144696RowCertificate 1 := by
  have hsplits : ∀ k, k ≤ 1 → (a144696BernsteinImage 1 k).Splits := by
    intro k hk
    exact (isRealRooted_of_degree_one
      (natDegree_a144696BernsteinImage hk)).2
  have hsimple : ∀ k, k ≤ 1 →
      HasSimpleRoots (a144696BernsteinImage 1 k) := by
    intro k hk
    apply hasSimpleRoots_of_natDegree_le_one
      (hasPosLeadingCoeff_a144696BernsteinImage hk).ne_zero
    rw [natDegree_a144696BernsteinImage hk]
  constructor
  · exact hsplits
  · exact hsimple
  · intro k hk
    have hk0 : k = 0 := by lia
    subst k
    exact a144696BernsteinImage_one_horizontal
  · intro k hk
    have hk0 : k = 0 := by lia
    subst k
    intro r hr0 hr1
    rw [a144696BernsteinImage_one_zero] at hr0
    rw [a144696BernsteinImage_one_one] at hr1
    have heval0 : (2 : ℝ) + 2 * r = 0 := by
      simpa [Polynomial.IsRoot.def] using hr0
    have heval1 : (1 : ℝ) + 2 * r = 0 := by
      simpa [Polynomial.IsRoot.def] using hr1
    linarith
  · intro k hk
    have hk0 : k = 0 := by lia
    subst k
    rw [a144696BernsteinImage_zero_zero]
    exact (interlaces_one_linear
      (natDegree_a144696BernsteinImage (show 0 ≤ 1 by lia))).toStrictInterl
  · intro k hk
    have hk0 : k = 0 := by lia
    subst k
    rw [a144696BernsteinImage_zero_zero]
    simp
  · intro k hk
    have hk0 : k = 0 := by lia
    subst k
    rw [a144696BernsteinImage_zero_zero]
    exact (interlaces_one_linear
      (natDegree_a144696BernsteinImage (show 1 ≤ 1 by lia))).toStrictInterl
  · intro k hk
    have hk0 : k = 0 := by lia
    subst k
    rw [a144696BernsteinImage_zero_zero]
    simp

private theorem a144696BernsteinImage_wagnerData
    {d k : ℕ} (hk : k ≤ d)
    (hsplits : (a144696BernsteinImage d k).Splits) :
    Wagner.HasNonposRootsPosLeading (a144696BernsteinImage d k) := by
  exact ⟨hsplits,
    fun r hr ↦ (roots_neg_a144696BernsteinImage hk r hr).le,
    hasPosLeadingCoeff_a144696BernsteinImage hk⟩

private theorem a144696RowCertificate_succ
    {d : ℕ} (hd : 1 ≤ d) (hrow : A144696RowCertificate d) :
    A144696RowCertificate (d + 1) := by
  have hshift : ∀ k, k ≤ d →
      StrictInterl (a144696BernsteinImage d k)
          (a144696BernsteinImage (d + 1) (k + 1)) ∧
        (∀ r, (a144696BernsteinImage d k).IsRoot r →
          ¬ (a144696BernsteinImage (d + 1) (k + 1)).IsRoot r) ∧
        HasSimpleRoots (a144696BernsteinImage (d + 1) (k + 1)) := by
    intro k hk
    have hcurSimple := hrow.simple k hk
    have hauxSign : ∀ r, (a144696BernsteinImage d k).IsRoot r →
        0 < (a144696Auxiliary d k).eval r *
          (a144696BernsteinImage d k).derivative.eval r := by
      rcases lt_or_eq_of_le hk with hlt | rfl
      · exact fun _ hr ↦
          a144696Auxiliary_eval_mul_derivative_pos_of_prec hlt
            (hrow.vertical k hlt) hcurSimple hr
      · exact fun _ hr ↦
          a144696Auxiliary_diagonal_eval_mul_derivative_pos hcurSimple hr
    exact a144696BernsteinImage_shifted_step hd hk
      (hrow.splits k hk) hauxSign
  have hvertical : ∀ k, k ≤ d →
      StrictInterl (a144696BernsteinImage d k)
        (a144696BernsteinImage (d + 1) k) := by
    intro k hk
    have hshiftk := (hshift k hk).1
    have hf := a144696BernsteinImage_wagnerData hk (hrow.splits k hk)
    have hsucc := a144696BernsteinImage_wagnerData (show k + 1 ≤ d + 1 by lia)
      hshiftk.2.1.2
    have hself := prec_refl hf.2.2.ne_zero hf.1
    rw [a144696BernsteinImage_pascal (show k < d + 1 by lia)]
    exact Wagner.commonLeft_add hf hsucc hself hshiftk
  have hhorizontal : ∀ k, k ≤ d →
      StrictInterl (a144696BernsteinImage (d + 1) k)
        (a144696BernsteinImage (d + 1) (k + 1)) := by
    intro k hk
    have hshiftk := (hshift k hk).1
    have hf := a144696BernsteinImage_wagnerData hk (hrow.splits k hk)
    have hsucc := a144696BernsteinImage_wagnerData (show k + 1 ≤ d + 1 by lia)
      hshiftk.2.1.2
    have hself := prec_refl hsucc.2.2.ne_zero hsucc.1
    rw [a144696BernsteinImage_pascal (show k < d + 1 by lia)]
    exact Wagner.commonRight_add hf hsucc hshiftk hself
  have hverticalNoCommon : ∀ k, k ≤ d → ∀ r,
      (a144696BernsteinImage d k).IsRoot r →
        ¬ (a144696BernsteinImage (d + 1) k).IsRoot r := by
    intro k hk r hcur hnext
    rw [a144696BernsteinImage_pascal (show k < d + 1 by lia)] at hnext
    simp only [Nat.add_sub_cancel] at hnext
    have hcurEval : (a144696BernsteinImage d k).eval r = 0 := hcur
    have hnextEval :
        (a144696BernsteinImage d k).eval r +
          (a144696BernsteinImage (d + 1) (k + 1)).eval r = 0 := by
      have hsumZero :
          (a144696BernsteinImage d k +
            a144696BernsteinImage (d + 1) (k + 1)).eval r = 0 := hnext
      simpa only [eval_add] using hsumZero
    have htargetRoot :
        (a144696BernsteinImage (d + 1) (k + 1)).IsRoot r := by
      exact (show (a144696BernsteinImage (d + 1) (k + 1)).eval r = 0 by
        linarith)
    exact (hshift k hk).2.1 r hcur htargetRoot
  have hhorizontalNoCommon : ∀ k, k ≤ d → ∀ r,
      (a144696BernsteinImage (d + 1) k).IsRoot r →
        ¬ (a144696BernsteinImage (d + 1) (k + 1)).IsRoot r := by
    intro k hk r hleft hright
    rw [a144696BernsteinImage_pascal (show k < d + 1 by lia)] at hleft
    simp only [Nat.add_sub_cancel] at hleft
    have hrightEval :
        (a144696BernsteinImage (d + 1) (k + 1)).eval r = 0 := hright
    have hleftEval :
        (a144696BernsteinImage d k).eval r +
          (a144696BernsteinImage (d + 1) (k + 1)).eval r = 0 := by
      have hsumZero :
          (a144696BernsteinImage d k +
            a144696BernsteinImage (d + 1) (k + 1)).eval r = 0 := hleft
      simpa only [eval_add] using hsumZero
    have hcurRoot : (a144696BernsteinImage d k).IsRoot r := by
      exact (show (a144696BernsteinImage d k).eval r = 0 by linarith)
    exact (hshift k hk).2.1 r hcurRoot hright
  constructor
  · intro k hk
    by_cases htop : k = d + 1
    · subst k
      exact (hshift d le_rfl).1.2.1.2
    · exact (hvertical k (by lia)).2.1.2
  · intro k hk
    by_cases htop : k = d + 1
    · subst k
      exact (hshift d le_rfl).2.2
    · exact ((hvertical k (by lia)).hasSimpleRoots_of_no_common_root
          (fun r h ↦ hverticalNoCommon k (by lia) r h.1 h.2)).2
  · intro k hk
    exact hhorizontal k (by lia)
  · intro k hk
    exact hhorizontalNoCommon k (by lia)
  · intro k hk
    simpa using hvertical k (by lia)
  · intro k hk
    simpa using hverticalNoCommon k (by lia)
  · intro k hk
    simpa using (hshift k (by lia)).1
  · intro k hk
    simpa using (hshift k (by lia)).2.1

private theorem a144696RowCertificate_all (d : ℕ) :
    A144696RowCertificate d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      rcases d with _ | d
      · exact a144696RowCertificate_zero
      · rcases d with _ | d
        · exact a144696RowCertificate_one
        · exact a144696RowCertificate_succ (d := d + 1) (by lia)
            (ih (d + 1) (by lia))

/-- Every in-range Bernstein image of A144696 splits over the reals. -/
theorem a144696BernsteinImage_splits {d k : ℕ} (hk : k ≤ d) :
    (a144696BernsteinImage d k).Splits :=
  (a144696RowCertificate_all d).splits k hk

/-- Every in-range Bernstein image of A144696 has only simple roots. -/
theorem hasSimpleRoots_a144696BernsteinImage {d k : ℕ} (hk : k ≤ d) :
    HasSimpleRoots (a144696BernsteinImage d k) :=
  (a144696RowCertificate_all d).simple k hk

/-- Adjacent entries within an A144696 Bernstein-image row are in proper
position. -/
theorem a144696BernsteinImage_horizontal_prec {d k : ℕ} (hk : k < d) :
    StrictInterl (a144696BernsteinImage d k)
      (a144696BernsteinImage d (k + 1)) :=
  (a144696RowCertificate_all d).horizontal k hk

/-- Adjacent entries within an A144696 Bernstein-image row have no common real
root. -/
theorem a144696BernsteinImage_horizontal_noCommonRoot
    {d k : ℕ} (hk : k < d) : ∀ r,
    (a144696BernsteinImage d k).IsRoot r →
      ¬ (a144696BernsteinImage d (k + 1)).IsRoot r :=
  (a144696RowCertificate_all d).horizontalNoCommon k hk

/-- Same-index entries in consecutive A144696 Bernstein-image rows are in
proper position. -/
theorem a144696BernsteinImage_vertical_prec {d k : ℕ} (hk : k < d) :
    StrictInterl (a144696BernsteinImage (d - 1) k)
      (a144696BernsteinImage d k) :=
  (a144696RowCertificate_all d).vertical k hk

/-- Same-index entries in consecutive A144696 Bernstein-image rows have no
common real root. -/
theorem a144696BernsteinImage_vertical_noCommonRoot
    {d k : ℕ} (hk : k < d) : ∀ r,
    (a144696BernsteinImage (d - 1) k).IsRoot r →
      ¬ (a144696BernsteinImage d k).IsRoot r :=
  (a144696RowCertificate_all d).verticalNoCommon k hk

/-- Shifted entries in consecutive A144696 Bernstein-image rows are in proper
position. -/
theorem a144696BernsteinImage_shifted_prec {d k : ℕ} (hk : k < d) :
    StrictInterl (a144696BernsteinImage (d - 1) k)
      (a144696BernsteinImage d (k + 1)) :=
  (a144696RowCertificate_all d).shifted k hk

/-- Shifted entries in consecutive A144696 Bernstein-image rows have no common
real root. -/
theorem a144696BernsteinImage_shifted_noCommonRoot
    {d k : ℕ} (hk : k < d) : ∀ r,
    (a144696BernsteinImage (d - 1) k).IsRoot r →
      ¬ (a144696BernsteinImage d (k + 1)).IsRoot r :=
  (a144696RowCertificate_all d).shiftedNoCommon k hk

end RealRooted
