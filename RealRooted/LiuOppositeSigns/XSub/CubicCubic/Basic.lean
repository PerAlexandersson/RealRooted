import RealRooted.LiuOppositeSigns.XSub.CubicCubic.CubicSubQuadratic

/-!
# Normalized cubic/cubic x-subtraction setup and ordinary interlacing cases.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns
/-- Normalized monic arithmetic leaf for the degree-three/degree-three
same-degree positive-split x-subtraction endpoint.  The finite root-order
inequalities are exactly those supplied by a `(3, 3)`
`PositiveSplitRootCountPair`. -/
def xSubCubicCubicSplitsStatement : Prop :=
  ∀ {a b c u v w μ : ℝ},
    a ≤ b → b ≤ c → u ≤ v → v ≤ w →
      u ≤ b → v ≤ c → a ≤ v → b ≤ w →
        c ≤ 0 → w ≤ 0 → 0 < μ →
          (X * ((X - C a) * (X - C b) * (X - C c)) -
              C μ * ((X - C u) * (X - C v) * (X - C w))).Splits

/-- The normalized cubic/cubic x-subtraction polynomial is a genuine quartic. -/
lemma natDegree_xSubCubicCubic (a b c u v w μ : ℝ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).natDegree = 4 := by
  compute_degree <;> norm_num

/-- The normalized cubic/cubic x-subtraction polynomial is nonzero. -/
lemma xSubCubicCubic_ne_zero (a b c u v w μ : ℝ) :
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w)) ≠ 0 := by
  intro hzero
  have hdeg := natDegree_xSubCubicCubic a b c u v w μ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- The normalized cubic/cubic x-subtraction polynomial has positive leading
coefficient. -/
lemma hasPosLeadingCoeff_xSubCubicCubic (a b c u v w μ : ℝ) :
    HasPosLeadingCoeff
      (X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v) * (X - C w))) := by
  have hcubic_pos : HasPosLeadingCoeff ((X - C a) * (X - C b) * (X - C c)) := by
    exact ((hasPosLeadingCoeff_X_sub_C a).mul (hasPosLeadingCoeff_X_sub_C b)).mul
      (hasPosLeadingCoeff_X_sub_C c)
  have hleft_pos : HasPosLeadingCoeff (X * ((X - C a) * (X - C b) * (X - C c))) :=
    hcubic_pos.X_mul
  have hleft_deg :
      (X * ((X - C a) * (X - C b) * (X - C c))).natDegree = 4 := by
    compute_degree <;> norm_num
  have hdeg_lt : (C μ * ((X - C u) * (X - C v) * (X - C w))).natDegree <
      (X * ((X - C a) * (X - C b) * (X - C c))).natDegree := by
    rw [hleft_deg]
    compute_degree
    norm_num
  unfold HasPosLeadingCoeff at hleft_pos ⊢
  have hdegree_lt :
      degree (C μ * ((X - C u) * (X - C v) * (X - C w))) <
        degree (X * ((X - C a) * (X - C b) * (X - C c))) :=
    degree_lt_degree hdeg_lt
  rw [leadingCoeff_sub_of_degree_lt hdegree_lt]
  exact hleft_pos

/-- Evaluation form of the normalized cubic/cubic x-subtraction leaf. -/
lemma eval_xSubCubicCubic (a b c u v w μ x : ℝ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).eval x =
      x * ((x - a) * (x - b) * (x - c)) -
        μ * ((x - u) * (x - v) * (x - w)) := by
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- The normalized cubic/cubic x-subtraction polynomial tends to `+∞` at
`-∞`. -/
lemma tendsto_eval_xSubCubicCubic_atBot_atTop (a b c u v w μ : ℝ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v) * (X - C w))).eval x)
      atBot atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubCubicCubic a b c u v w μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_xSubCubicCubic]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hP_even : Even P.natDegree := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
    norm_num
  exact tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hP_pos hP_deg_pos hP_even

/-- The normalized cubic/cubic x-subtraction polynomial tends to `+∞` at
`+∞`. -/
lemma tendsto_eval_xSubCubicCubic_atTop_atTop (a b c u v w μ : ℝ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v) * (X - C w))).eval x)
      atTop atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubCubicCubic a b c u v w μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_xSubCubicCubic]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  exact P.tendsto_atTop_of_leadingCoeff_nonneg hP_deg_pos hP_pos.le

/-- A cubic whose roots lie between consecutive roots of the quartic
`X * (X - a) * (X - b) * (X - c)` interlaces that quartic. -/
lemma interlaces_cubic_quartic_of_roots_between {a b c u v w : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hc0 : c ≤ 0)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hw0 : w ≤ 0) :
    Interlaces ((X - C u) * (X - C v) * (X - C w))
      (X * ((X - C a) * (X - C b) * (X - C c))) := by
  let f : ℝ[X] := X * ((X - C a) * (X - C b) * (X - C c))
  let g : ℝ[X] := (X - C u) * (X - C v) * (X - C w)
  have hf_ne : f ≠ 0 := by
    dsimp [f]
    exact mul_ne_zero X_ne_zero
      (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b))
        (X_sub_C_ne_zero c))
  have hg_ne : g ≠ 0 := by
    dsimp [g]
    exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero u) (X_sub_C_ne_zero v))
      (X_sub_C_ne_zero w)
  have hf_split : f.Splits := by
    dsimp [f]
    exact Polynomial.Splits.X.mul
      (((Polynomial.Splits.X_sub_C a).mul (Polynomial.Splits.X_sub_C b)).mul
        (Polynomial.Splits.X_sub_C c))
  have hg_split : g.Splits := by
    dsimp [g]
    exact ((Polynomial.Splits.X_sub_C u).mul (Polynomial.Splits.X_sub_C v)).mul
      (Polynomial.Splits.X_sub_C w)
  have hf_deg : f.natDegree = 4 := by
    dsimp [f]
    compute_degree <;> norm_num
  have hg_deg : g.natDegree = 3 := by
    dsimp [g]
    compute_degree <;> norm_num
  have hf_roots : (↑[a, b, c, 0] : Multiset ℝ) = f.roots := by
    dsimp [f] at hf_ne ⊢
    rw [roots_mul hf_ne, roots_X,
      roots_mul (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero a)
        (X_sub_C_ne_zero b)) (X_sub_C_ne_zero c)),
      roots_mul (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)),
      roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
    change ({a} : Multiset ℝ) + {b} + {c} + {0} =
      ({0} : Multiset ℝ) + ({a} + {b} + {c})
    ac_rfl
  have hg_roots : (↑[u, v, w] : Multiset ℝ) = g.roots := by
    dsimp [g] at hg_ne ⊢
    rw [roots_mul hg_ne, roots_mul (mul_ne_zero (X_sub_C_ne_zero u)
        (X_sub_C_ne_zero v)),
      roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
    rfl
  change Interlaces g f
  exact Interlaces.of_cubic_quartic_root_lists
    hf_ne hf_split hg_ne hg_split hf_deg hg_deg hf_roots.symm hg_roots.symm
    hab hbc hc0 huv hvw hau hub hbv hvc hcw hw0

/-- In the ordinary interlacing subcase of the normalized cubic/cubic leaf, the
desired splitting follows from the Ma--Wang weak-sign theorem. -/
lemma xSubCubicCubicSplits_of_interlacing_roots {a b c u v w μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hc0 : c ≤ 0)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let f : ℝ[X] := X * ((X - C a) * (X - C b) * (X - C c))
  let g : ℝ[X] := (X - C u) * (X - C v) * (X - C w)
  have hgf : Interlaces g f := by
    dsimp [f, g]
    exact interlaces_cubic_quartic_of_roots_between
      hab hbc hc0 huv hvw hau hub hbv hvc hcw hw0
  have hf_deg : f.natDegree = 4 := by
    dsimp [f]
    compute_degree <;> norm_num
  have hF_deg : ((1 : ℝ[X]) * f + (-C μ) * g).natDegree = 4 := by
    dsimp [f, g]
    simpa [sub_eq_add_neg] using natDegree_xSubCubicCubic a b c u v w μ
  have hg_pos : HasPosLeadingCoeff g := by
    dsimp [g]
    exact ((hasPosLeadingCoeff_X_sub_C u).mul (hasPosLeadingCoeff_X_sub_C v)).mul
      (hasPosLeadingCoeff_X_sub_C w)
  have hF_pos : HasPosLeadingCoeff ((1 : ℝ[X]) * f + (-C μ) * g) := by
    dsimp [f, g]
    simpa [sub_eq_add_neg] using hasPosLeadingCoeff_xSubCubicCubic a b c u v w μ
  have hdeg_lo : f.natDegree ≤ ((1 : ℝ[X]) * f + (-C μ) * g).natDegree := by
    rw [hf_deg, hF_deg]
  have hdeg_hi : ((1 : ℝ[X]) * f + (-C μ) * g).natDegree ≤ f.natDegree + 1 := by
    rw [hf_deg, hF_deg]
    norm_num
  have hb_nonpos : ∀ r, f.IsRoot r → (-C μ).eval r ≤ 0 := by
    intro r _
    simpa only [eval_neg, eval_C, Left.neg_nonpos_iff] using le_of_lt hμ
  have hprec : Prec f ((1 : ℝ[X]) * f + (-C μ) * g) :=
    prec_of_interlaces_evalCoeff_nonpos
      hgf hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  have hsplits : ((1 : ℝ[X]) * f + (-C μ) * g).Splits := hprec.2.1.2
  dsimp [f, g] at hsplits ⊢
  simpa [sub_eq_add_neg] using hsplits

/-- If the normalized cubic/cubic x-subtraction endpoints share a linear
factor, the splitting problem reduces to the already proved
quadratic/quadratic leaf. -/
lemma xSubCubicCubicSplits_of_common_root {r a b c d μ : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (had : a ≤ d) (hcb : c ≤ b)
    (hb0 : b ≤ 0) (hd0 : d ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C r) * ((X - C a) * (X - C b))) -
      C μ * ((X - C r) * ((X - C c) * (X - C d)))).Splits := by
  let Q : ℝ[X] := X * ((X - C a) * (X - C b)) -
    C μ * ((X - C c) * (X - C d))
  have hQ : Q.Splits := by
    dsimp [Q]
    exact xSubQuadraticQuadraticSplits hab hcd had hcb hb0 hd0 hμ
  have hfactor :
      X * ((X - C r) * ((X - C a) * (X - C b))) -
        C μ * ((X - C r) * ((X - C c) * (X - C d))) =
        (X - C r) * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul hQ

/-- Boundary case of the normalized cubic/cubic leaf where the lower
right-endpoint root equals the lower left-endpoint root. -/
lemma xSubCubicCubicSplits_of_lower_common_root {a b c v w μ : ℝ}
    (hbc : b ≤ c) (hvw : v ≤ w) (hvc : v ≤ c) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C a) * (X - C v) * (X - C w))).Splits := by
  have hcommon := xSubCubicCubicSplits_of_common_root
    (r := a) (a := b) (b := c) (c := v) (d := w)
    hbc hvw hbw hvc hc0 hw0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon

/-- Boundary case of the normalized cubic/cubic leaf where the middle
right-endpoint root equals the middle left-endpoint root. -/
lemma xSubCubicCubicSplits_of_middle_common_root {a b c u w μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hub : u ≤ b) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C b) * (X - C w))).Splits := by
  have hac : a ≤ c := hab.trans hbc
  have huw : u ≤ w := hub.trans hbw
  have haw : a ≤ w := hab.trans hbw
  have huc : u ≤ c := hub.trans hbc
  have hcommon := xSubCubicCubicSplits_of_common_root
    (r := b) (a := a) (b := c) (c := u) (d := w)
    hac huw haw huc hc0 hw0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon

/-- Boundary case of the normalized cubic/cubic leaf where the upper
right-endpoint root equals the upper left-endpoint root. -/
lemma xSubCubicCubicSplits_of_upper_common_root {a b c u v μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v) (hub : u ≤ b)
    (hav : a ≤ v) (hvc : v ≤ c) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C c))).Splits := by
  have hb0 : b ≤ 0 := hbc.trans hc0
  have hv0 : v ≤ 0 := hvc.trans hc0
  have hcommon := xSubCubicCubicSplits_of_common_root
    (r := c) (a := a) (b := b) (c := u) (d := v)
    hab huv hav hub hb0 hv0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon

end LiuOppositeSigns
end RealRooted
