module

public import RealRooted.Interlacing.QuadraticPFPreservers
public import RealRooted.SimpleRoots
import RealRooted.Interlacing.SecondOrderClassification
import RealRooted.Derivative.Interlacing
import RealRooted.Interlacing.Residue
import RealRooted.Interlacing.RootCountSigns
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import RealRooted.WagnerRightSum

/-!
# Preservation for second-order ray operators

Root-gap sign arguments and preservation consequences for the second-order
operator classified in `RealRooted.Interlacing.SecondOrderClassification`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-! ## Points selected by the logarithmic derivative -/

/-- In a strict same-degree alternating layout, the `i`-th left point has
exactly `length - i` right-hand points strictly above it. -/
private theorem countP_lt_getElem_of_listAlternates_strict :
    ∀ {ss rs : List ℝ},
      ListAlternates ss rs →
      ss.Pairwise (· < ·) →
      rs.Pairwise (· < ·) →
      (∀ s ∈ ss, s ∉ rs) →
      ss.length = rs.length →
      ∀ (i : ℕ) (hi : i < ss.length),
        rs.countP (fun r ↦ decide (ss[i] < r)) = ss.length - i
  | [], [], _, _, _, _, _, i, hi => by simp at hi
  | s :: ss, r :: rs, halt, hss, hrs, hdisj, hlen, 0, _ => by
      obtain ⟨hsr, hint⟩ := halt
      have hsr : s < r := lt_of_le_of_ne hsr fun h ↦
        hdisj s (by simp) (by simp [h])
      have hall : rs.countP (fun x ↦ decide (s < x)) = rs.length := by
        apply List.countP_eq_length.mpr
        intro x hx
        simpa using hsr.trans (List.rel_of_pairwise_cons hrs hx)
      have hrs_len : rs.length = ss.length := by simpa using hlen.symm
      simp [hall, hsr, hrs_len]
  | s :: ss, r :: rs, halt, hss, hrs, hdisj, hlen, i + 1, hi => by
      obtain ⟨hsr, hint⟩ := halt
      have htail_len : ss.length + 1 = (r :: rs).length := by simpa using hlen
      have htail_disj : ∀ x ∈ ss, x ∉ r :: rs := by
        intro x hx hmem
        exact hdisj x (by simp [hx]) (by simp [hmem])
      have htail_count := countP_lt_getElem_of_listInterlaces_strict
        hint hrs htail_disj htail_len i (by simpa using hi)
      simp only [List.getElem_cons_succ]
      rw [htail_count]
      simp only [List.length_cons]
      lia

/-- For a split polynomial `p` with positive leading coefficient, `C v * p + p'` strictly
interlaces `p` for `v > 0`. -/
private theorem strictInterl_C_mul_add_derivative {p : ℝ[X]}
    (hp : p.Splits) (hp_pos : HasPosLeadingCoeff p) (hpdeg : p.natDegree ≠ 0)
    {v : ℝ} (hv : 0 < v) :
    StrictInterl (C v * p + p.derivative) p := by
  have hder : StrictInterl p.derivative p :=
    (derivative_interlaces_of_natDegree_ne_zero hp hpdeg).toStrictInterl
  have hself : StrictInterl (C v * p) p :=
    (StrictInterl.refl hp_pos.ne_zero hp).C_mul_left hv.ne'
  have hself_pos : HasPosLeadingCoeff (C v * p) := by
    unfold HasPosLeadingCoeff at hp_pos ⊢
    simpa using mul_pos hv hp_pos
  exact StrictInterl.add_of_right_of_posLeadingCoeff hself hder hself_pos
    (hp_pos.derivative hpdeg)

/-- A simple polynomial `p` has no common root with `C v * p + p'`. -/
private theorem not_isRoot_C_mul_add_derivative_and_isRoot {p : ℝ[X]}
    (hp_simple : HasSimpleRoots p) (v : ℝ) (r : ℝ) :
    ¬((C v * p + p.derivative).IsRoot r ∧ p.IsRoot r) := by
  intro hr
  have hq0 := hr.1.eq_zero
  simp only [eval_add, eval_mul, eval_C, hr.2.eq_zero, mul_zero, zero_add] at hq0
  exact hp_simple.eval_derivative_ne_zero hr.2 hq0

/-- The root lists of a strictly interlacing same-degree pair `q`, `p` with simple roots
alternate strictly. -/
private theorem exists_strict_alternating_root_lists {q p : ℝ[X]}
    (hp : p.Splits) (hp_simple : HasSimpleRoots p) (hqp : StrictInterl q p)
    (hno : ∀ r : ℝ, ¬(q.IsRoot r ∧ p.IsRoot r)) (hqdeg : q.natDegree = p.natDegree) :
    ∃ ss rs : List ℝ, ListAlternates ss rs ∧ ss.Pairwise (· < ·) ∧ rs.Pairwise (· < ·) ∧
      (∀ s ∈ ss, s ∉ rs) ∧ ss.length = p.natDegree ∧ rs.length = p.natDegree ∧
      (↑ss : Multiset ℝ) = q.roots ∧ (↑rs : Multiset ℝ) = p.roots := by
  have hsimple := hqp.hasSimpleRoots_of_no_common_root hno
  obtain ⟨ss, rs, hss_le, hrs_le, hss_roots, hrs_roots, halt⟩ :=
    hqp.exists_listAlternates_of_natDegree_eq hqdeg
  have hss_lt : ss.Pairwise (· < ·) := by
    exact (hss_le.sortedLE.sortedLT_of_nodup (by
      rw [← Multiset.coe_nodup, hss_roots]
      exact hsimple.1.roots_nodup)).pairwise
  have hrs_lt : rs.Pairwise (· < ·) := by
    exact (hrs_le.sortedLE.sortedLT_of_nodup (by
      rw [← Multiset.coe_nodup, hrs_roots]
      exact hp_simple.roots_nodup)).pairwise
  refine ⟨ss, rs, halt, hss_lt, hrs_lt, ?_, ?_, ?_, hss_roots, hrs_roots⟩
  · intro s hs hsr
    apply hno s
    constructor
    · apply (mem_roots hqp.1.1).mp
      rw [← hss_roots]
      exact Multiset.mem_coe.mpr hs
    · apply (mem_roots hp_simple.ne_zero).mp
      rw [← hrs_roots]
      exact Multiset.mem_coe.mpr hsr
  · rw [← Multiset.coe_card, hss_roots,
      Polynomial.splits_iff_card_roots.mp hqp.1.2, hqdeg]
  · rw [← Multiset.coe_card, hrs_roots, Polynomial.splits_iff_card_roots.mp hp]

/-- For a simple split polynomial with negative roots and every `v > 0`,
there is a point in the gap having exactly `j` input roots to its right where
the logarithmic derivative equals `-v`. -/
theorem secondOrder_exists_gapPoint {p : ℝ[X]}
    (hp : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hp_simple : HasSimpleRoots p)
    (hp_neg : ∀ r ∈ p.roots, r < 0)
    {v : ℝ} (hv : 0 < v) {j : ℕ}
    (hj : 1 ≤ j) (hjdeg : j ≤ p.natDegree) :
    ∃ x : ℝ,
      x < 0 ∧
      (C v * p + p.derivative).IsRoot x ∧
      ¬p.IsRoot x ∧
      p.roots.countP (fun r ↦ x < r) = j ∧
      p.derivative.eval x / p.eval x = -v := by
  let q : ℝ[X] := C v * p + p.derivative
  have htop : (v + 0 * (p.natDegree : ℝ)) * p.leadingCoeff ≠ 0 := by
    simpa using mul_ne_zero hv.ne' hp_pos.ne'
  have hqdeg : q.natDegree = p.natDegree := by
    simpa [q] using
      (Polynomial.natDegree_and_leadingCoeff_C_mul_add_affine_mul_derivative p v 1 0 htop).1
  have hqp : StrictInterl q p := strictInterl_C_mul_add_derivative hp hp_pos (by lia) hv
  have hno := not_isRoot_C_mul_add_derivative_and_isRoot hp_simple v
  obtain ⟨ss, rs, halt, hss_lt, hrs_lt, hdisj, hss_len, hrs_len, hss_roots, hrs_roots⟩ :=
    exists_strict_alternating_root_lists hp hp_simple hqp hno hqdeg
  let i := p.natDegree - j
  have hi : i < ss.length := by
    dsimp [i]
    rw [hss_len]
    lia
  let x := ss[i]
  have hxmem : x ∈ ss := List.getElem_mem hi
  have hxq : q.IsRoot x := by
    apply (mem_roots hqp.1.1).mp
    rw [← hss_roots]
    exact Multiset.mem_coe.mpr hxmem
  have hxnotp : ¬p.IsRoot x := fun hxp ↦ hno x ⟨hxq, hxp⟩
  have hcount_list := countP_lt_getElem_of_listAlternates_strict
    halt hss_lt hrs_lt hdisj (by rw [hss_len, hrs_len]) i hi
  have hcount : p.roots.countP (fun r ↦ x < r) = j := by
    rw [← hrs_roots, Multiset.coe_countP]
    simpa [x, i, hss_len, Nat.sub_sub_self hjdeg] using hcount_list
  have hxneg : x < 0 := by
    obtain ⟨r, hrmem, hxr⟩ : ∃ r ∈ p.roots, x < r := by
      have hpos : 0 < p.roots.countP (fun r ↦ x < r) := by lia
      simpa using (Multiset.countP_pos.mp hpos)
    exact hxr.trans (hp_neg r hrmem)
  have hratio : p.derivative.eval x / p.eval x = -v := by
    have hqeval := hxq.eq_zero
    have hpeval : p.eval x ≠ 0 := by simpa [Polynomial.IsRoot.def] using hxnotp
    dsimp [q] at hqeval
    simp only [eval_add, eval_mul, eval_C] at hqeval
    apply (div_eq_iff hpeval).2
    linarith
  exact ⟨x, hxneg, by simpa [q] using hxq, hxnotp, hcount, hratio⟩

/-- A root `r < 0` of `p` to the right of `x` contributes at least `1` to the root sum. -/
private theorem one_le_div_sub_of_lt {x r : ℝ} (hrneg : r < 0) (hxr : x < r) :
    1 ≤ x / (x - r) := by
  have hden : x - r < 0 := sub_neg.mpr hxr
  have hquot : 0 ≤ r / (x - r) := div_nonneg_iff.mpr (Or.inr ⟨hrneg.le, hden.le⟩)
  have hid : x / (x - r) = 1 + r / (x - r) := by
    apply (div_eq_iff hden.ne).2
    rw [add_mul, one_mul, div_mul_cancel₀ _ hden.ne]
    ring
  rw [hid]
  linarith

/-- If the logarithmic derivative at `x` is `-v`, the terms `x / (x - r)` over the roots add
up to `-v * x`. -/
private theorem sum_filter_div_sub_eq {x v : ℝ} {roots : List ℝ} {m : Multiset ℝ}
    (hroots : (↑roots : Multiset ℝ) = m)
    (hlog : (m.map fun r ↦ 1 / (x - r)).sum = -v) :
    ((roots.filter fun r ↦ x < r).map fun r ↦ x / (x - r)).sum +
      ((roots.filter fun r ↦ ¬x < r).map fun r ↦ x / (x - r)).sum = -v * x := by
  rw [List.sum_map_filter_add_sum_map_filter_not]
  have hall : (roots.map fun r ↦ x / (x - r)).sum = (m.map fun r ↦ x / (x - r)).sum := by
    simpa using congrArg (fun s : Multiset ℝ ↦ (s.map fun r ↦ x / (x - r)).sum) hroots
  rw [hall]
  simp only [div_eq_mul_inv, Multiset.sum_map_mul_left]
  have hlog' : (m.map fun r ↦ (x - r)⁻¹).sum = -v := by
    simpa only [one_div] using hlog
  rw [hlog']
  ring

/-- At a gap point with `j` roots to the right, the actual root-sum terms
satisfy the two sharp square-sum bounds `j ≤ q` and `s² ≤ jq`.

The positive list consists exactly of the roots to the right of `x`; its
terms are at least one. The remaining terms are nonpositive. -/
theorem secondOrder_gap_squareSum_bound {p : ℝ[X]} {x v : ℝ} {j : ℕ}
    (hp : p.Splits)
    (hp_neg : ∀ r ∈ p.roots, r < 0)
    (hx : x < 0) (hxroot : ¬p.IsRoot x) (hv : 0 < v)
    (hratio : p.derivative.eval x / p.eval x = -v)
    (hcount : p.roots.countP (fun r ↦ x < r) = j) :
    let roots := p.roots.sort (· ≤ ·)
    let positive := (roots.filter fun r ↦ x < r).map fun r ↦ x / (x - r)
    let negative := (roots.filter fun r ↦ ¬x < r).map fun r ↦ x / (x - r)
    let s := positive.sum + negative.sum
    let q := (positive.map fun y ↦ y ^ 2).sum +
      (negative.map fun y ↦ y ^ 2).sum
    positive.length = j ∧ s = -v * x ∧
      (j : ℝ) ≤ q ∧ s ^ 2 ≤ (j : ℝ) * q := by
  dsimp only
  let roots := p.roots.sort (· ≤ ·)
  let positive := (roots.filter fun r ↦ x < r).map fun r ↦ x / (x - r)
  let negative := (roots.filter fun r ↦ ¬x < r).map fun r ↦ x / (x - r)
  change positive.length = j ∧
    positive.sum + negative.sum = -v * x ∧
      (j : ℝ) ≤ (positive.map fun y ↦ y ^ 2).sum +
        (negative.map fun y ↦ y ^ 2).sum ∧
      (positive.sum + negative.sum) ^ 2 ≤
        (j : ℝ) * ((positive.map fun y ↦ y ^ 2).sum +
          (negative.map fun y ↦ y ^ 2).sum)
  have hroots : (↑roots : Multiset ℝ) = p.roots := Multiset.sort_eq ..
  have hpositive : ∀ y ∈ positive, 1 ≤ y := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
    have hrmem : r ∈ p.roots := by
      rw [← hroots]
      exact Multiset.mem_coe.mpr (List.mem_of_mem_filter hr)
    exact one_le_div_sub_of_lt (hp_neg r hrmem) (by simpa using (List.mem_filter.mp hr).2)
  have hnegative : ∀ y ∈ negative, y ≤ 0 := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
    have hrle : r ≤ x := not_lt.mp (by simpa using (List.mem_filter.mp hr).2)
    exact div_nonpos_of_nonpos_of_nonneg hx.le (sub_nonneg.mpr hrle)
  have hpos_len : positive.length = j := by
    dsimp only [positive]
    rw [List.length_map, ← List.countP_eq_length_filter, ← Multiset.coe_countP,
      hroots, hcount]
  have hlog : (p.roots.map fun r ↦ 1 / (x - r)).sum = -v := by
    have hder := hp.eval_derivative_eq_eval_mul_sum hxroot
    have heval : p.eval x ≠ 0 := by simpa [Polynomial.IsRoot.def] using hxroot
    have heq : p.derivative.eval x / p.eval x = (p.roots.map fun r ↦ 1 / (x - r)).sum := by
      rw [hder]
      field_simp
    linarith
  have hsum : positive.sum + negative.sum = -v * x := sum_filter_div_sub_eq hroots hlog
  obtain ⟨hcard, hsquare⟩ := sum_sq_ge_card_and_sum_sq positive negative hpositive hnegative
    (by rw [hsum]; exact mul_pos_of_neg_of_neg (neg_neg_of_pos hv) hx)
  rw [hpos_len] at hcard hsquare
  exact ⟨hpos_len, hsum, hcard, hsquare⟩

/-! ## Evaluation of the operator at a selected point -/

/-- Product-form identity for the Laguerre expression away from the roots. -/
private theorem laguerre_eval_eq_eval_sq_mul_rootSumSq
    (c x : ℝ) (roots : Multiset ℝ)
    (hx : ∀ r ∈ roots, x - r ≠ 0) :
    let p : ℝ[X] := C c * (roots.map fun r ↦ X - C r).prod
    p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x =
      p.eval x ^ 2 * (roots.map fun r ↦ (x - r)⁻¹ ^ 2).sum := by
  induction roots using Multiset.induction_on with
  | empty => simp
  | @cons r roots ih =>
      have hxr : x - r ≠ 0 := hx r (by simp)
      have htail : ∀ t ∈ roots, x - t ≠ 0 :=
        fun t ht ↦ hx t (by simp [ht])
      have hih := ih htail
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons,
        Multiset.sum_cons]
      let q : ℝ[X] := C c * (roots.map fun t ↦ X - C t).prod
      have hpoly :
          C c * ((X - C r) * (roots.map fun t ↦ X - C t).prod) =
            (X - C r) * q := by
        dsimp only [q]
        ring
      rw [hpoly]
      change q.derivative.eval x ^ 2 - q.eval x * q.derivative.derivative.eval x =
        q.eval x ^ 2 * (roots.map fun t ↦ (x - t)⁻¹ ^ 2).sum at hih
      simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
        sub_zero, one_mul, derivative_add, eval_add, eval_mul, eval_sub,
        eval_X, eval_C]
      have hinv : (x - r) ^ 2 * (x - r)⁻¹ ^ 2 = 1 := by
        rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hxr)]
      have hscaled := congrArg (fun z : ℝ ↦ (x - r) ^ 2 * z) hih
      ring_nf at hinv hscaled ⊢
      nlinarith

/-- Away from the roots, the Laguerre expression is the value squared times
the sum of the squared reciprocal root distances. -/
theorem laguerre_eval_eq_eval_sq_mul_rootSumSq_of_splits
    {p : ℝ[X]} (hp : p.Splits) {x : ℝ} (hx : ¬p.IsRoot x) :
    p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x =
      p.eval x ^ 2 * (p.roots.map fun r ↦ (x - r)⁻¹ ^ 2).sum := by
  have hdist : ∀ r ∈ p.roots, x - r ≠ 0 := by
    intro r hr hzero
    apply hx
    have hp0 : p ≠ 0 := by
      intro hpzero
      apply hx
      simp [hpzero, Polynomial.IsRoot.def]
    have : x = r := sub_eq_zero.mp hzero
    subst x
    exact (mem_roots hp0).mp hr
  have hmain := laguerre_eval_eq_eval_sq_mul_rootSumSq
    p.leadingCoeff x p.roots hdist
  simpa only [← hp.eq_prod_roots] using hmain

/-- Formula API for the opaque ray operator, derived from its linear-map
package and its values on monomials. -/
theorem secondOrderRayOperator_eq_formula
    (a b c d f : ℝ) (p : ℝ[X]) :
    secondOrderRayOperator a b c d f p =
      (C a + C b * X) * p + (C c + C d * X) * p.derivative +
        C f * X * p.derivative.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hmap := (secondOrderRayOperatorₗ a b c d f).map_add p q
      simp only [secondOrderRayOperatorₗ_apply] at hmap
      rw [hmap, hp, hq]
      simp only [derivative_add]
      ring
  | monomial n z =>
      have hmap := (secondOrderRayOperatorₗ a b c d f).map_smul z (X ^ n)
      simp only [secondOrderRayOperatorₗ_apply, Polynomial.smul_eq_C_mul] at hmap
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      rw [hmap]
      cases n with
      | zero =>
          rw [pow_zero, secondOrderRayOperator_one]
          simp
          ring
      | succ n =>
          rw [secondOrderRayOperator_X_pow_succ]
          cases n with
          | zero =>
              simp
              ring
          | succ n =>
              simp [derivative_pow]
              ring

/-- Exact value of the ray operator at a logarithmic-derivative gap point,
written in the variables used by the square-sum optimization. -/
theorem secondOrderRayOperator_eval_div_at_gapPoint
    (a b c d f : ℝ) {p : ℝ[X]} (hp : p.Splits)
    {x v : ℝ} (hx : x ≠ 0) (hv : v ≠ 0)
    (hxroot : ¬p.IsRoot x)
    (hratio : p.derivative.eval x / p.eval x = -v) :
    let terms := p.roots.map fun r ↦ x / (x - r)
    let s := terms.sum
    let squareSum := (terms.map fun y ↦ y ^ 2).sum
    (secondOrderRayOperator a b c d f p).eval x / p.eval x =
      a - c * v + (d * v - b - f * v ^ 2) * s / v +
        f * v / s * squareSum := by
  dsimp only
  let terms := p.roots.map fun r ↦ x / (x - r)
  let s := terms.sum
  let squareSum := (terms.map fun y ↦ y ^ 2).sum
  change (secondOrderRayOperator a b c d f p).eval x / p.eval x =
    a - c * v + (d * v - b - f * v ^ 2) * s / v +
      f * v / s * squareSum
  have heval : p.eval x ≠ 0 := by
    simpa [Polynomial.IsRoot.def] using hxroot
  have hlog : (p.roots.map fun r ↦ 1 / (x - r)).sum = -v := by
    have hder := hp.eval_derivative_eq_eval_mul_sum hxroot
    have heq : p.derivative.eval x / p.eval x =
        (p.roots.map fun r ↦ 1 / (x - r)).sum := by
      rw [hder]
      field_simp
    linarith
  have hs : s = -v * x := by
    dsimp only [s, terms]
    simp only [div_eq_mul_inv, Multiset.sum_map_mul_left]
    have hlog' : (p.roots.map fun r ↦ (x - r)⁻¹).sum = -v := by
      simpa only [one_div] using hlog
    rw [hlog']
    ring
  have hs0 : s ≠ 0 := by
    rw [hs]
    exact mul_ne_zero (neg_ne_zero.mpr hv) hx
  let rootSq := (p.roots.map fun r ↦ (x - r)⁻¹ ^ 2).sum
  have hsquare : squareSum = x ^ 2 * rootSq := by
    dsimp only [squareSum, terms, rootSq]
    rw [Multiset.map_map]
    simp only [Function.comp_apply, div_eq_mul_inv, mul_pow,
      Multiset.sum_map_mul_left]
  have hder : p.derivative.eval x = -v * p.eval x := by
    apply (div_eq_iff heval).mp
    exact hratio
  have hlag := laguerre_eval_eq_eval_sq_mul_rootSumSq_of_splits hp hxroot
  change p.derivative.eval x ^ 2 -
      p.eval x * p.derivative.derivative.eval x =
        p.eval x ^ 2 * rootSq at hlag
  have hsecond : p.derivative.derivative.eval x =
      p.eval x * (v ^ 2 - rootSq) := by
    have hzero : p.eval x *
        (p.derivative.derivative.eval x - p.eval x * (v ^ 2 - rootSq)) = 0 := by
      rw [hder] at hlag
      nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left heval)
  rw [hs, hsquare]
  rw [secondOrderRayOperator_eq_formula]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  rw [hder, hsecond]
  field_simp [heval, hx, hv]
  ring

/-! ## Alternating-sign root count -/

/-- Alternating signs at `n` ordered simple points, together with positive
leading coefficient and degree `n + 1`, force all roots of the target to be
real. The sign convention includes the left and right exterior intervals. -/
theorem splits_of_gapSigns_with_exterior {g F : ℝ[X]}
    (hg0 : g ≠ 0) (hg : g.Splits) (hg_simple : HasSimpleRoots g)
    (hgdeg : 1 ≤ g.natDegree)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg : F.natDegree = g.natDegree + 1)
    (hsign : ∀ x ∈ g.roots,
      0 < F.eval x *
        (-1 : ℝ) ^ (g.roots.countP (fun r ↦ x < r) + 1)) :
    F.Splits := by
  have hsign' : ∀ x ∈ g.roots,
      F.eval x * (-1 : ℝ) ^ (g.roots.countP (fun r ↦ x < r)) < 0 := by
    intro x hx
    have h := hsign x hx
    rw [pow_succ] at h
    nlinarith
  have hinterl := strictInterl_of_eval_mul_neg_one_pow_countP_neg
    hg0 hg hg_simple.roots_nodup hgdeg hF_pos hdeg hsign'
  exact hinterl.1.2.1.2

/-! ## Shifted-power obstruction -/

/-- After removing the repeated shifted root, the remaining factor is a
cubic in the recentered variable `Y = X + r`. This is the lower-branch
obstruction polynomial. -/
theorem secondOrderRayOperator_shifted_pow_recentered_cubic
    (a b c d f r : ℝ) (n : ℕ) :
    secondOrderRayOperator a b c d f ((X + C r) ^ (n + 2)) =
      (X + C r) ^ n *
        (C b * (X + C r) ^ 3 +
          C (a - b * r + d * (n + 2)) * (X + C r) ^ 2 +
          C ((n + 2) * (c - d * r + f * (n + 1))) * (X + C r) -
          C ((n + 2) * (n + 1) * f * r)) := by
  rw [secondOrderRayOperator_shifted_pow_factor]
  simp only [map_add, map_sub, map_mul]
  ring

end RealRooted
