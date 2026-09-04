import RealRooted.DegreeDropReversal
import RealRooted.ObreschkoffConverse
import RealRooted.ParkingFunctions.ToricContribution.ExceptionalOffset.PencilSplitting
import RealRooted.RootContinuity

/-!
# Exceptional-offset orientation and distinguished parameters

This layer orients the real-rooted exceptional pencil and identifies its two
distinguished parameters with the adjacent toric-contribution polynomials.
-/

open Polynomial
open MeasureTheory Set

noncomputable section

namespace RealRooted
namespace ParkingFunctions
namespace ToricContribution

@[simp]
theorem exceptionalEulerInverse_eval_zero (m ε : ℕ) {γ : ℝ}
    (hγ : γ ≠ 0) :
    (exceptionalEulerInverse m ε γ).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_exceptionalEulerInverse]
  simp [hγ]

/-- The top coefficient of the exceptional Euler inverse has sign `(-1)^m`. -/
theorem negOnePow_mul_exceptionalEulerInverse_leadingCoeff_pos
    (m ε : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    0 < (-1 : ℝ) ^ m *
      (exceptionalEulerInverse m ε γ).leadingCoeff := by
  have hdegree := natDegree_exceptionalEulerInverse m ε hγ
  rw [Polynomial.leadingCoeff, hdegree,
    coeff_exceptionalEulerInverse, if_pos le_rfl,
    exceptionalBaseCoeff,
    exceptional_realRisingFactorial_neg_nat_eq_factorial_div m m le_rfl]
  have hc : 0 < (ε : ℝ) + 1 / 2 := by positivity
  have hcm : 0 < (ε : ℝ) + 1 / 2 + m := by positivity
  have hdenC : 0 < realRisingFactorial ((ε : ℝ) + 1 / 2) m :=
    realRisingFactorial_pos m hc
  have hnumC : 0 < realRisingFactorial
      ((ε : ℝ) + 1 / 2 + m) m :=
    realRisingFactorial_pos m hcm
  have hsignSq : ((-1 : ℝ) ^ m) ^ 2 = 1 :=
    exceptional_neg_one_pow_sq_real m
  have hγm : 0 < γ + (m : ℝ) := by positivity
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [show (-1 : ℝ) ^ m *
        (((-1 : ℝ) ^ m * (m.factorial : ℝ) *
            realRisingFactorial ((ε : ℝ) + 1 / 2 + m) m /
              (realRisingFactorial ((ε : ℝ) + 1 / 2) m * m.factorial)) *
          γ / (γ + m)) =
      realRisingFactorial ((ε : ℝ) + 1 / 2 + m) m * γ /
        (realRisingFactorial ((ε : ℝ) + 1 / 2) m *
          (γ + m)) by
      field_simp [hdenC.ne', hγm.ne']
      rw [hsignSq]
      ring]
  positivity

/-- Every root of a positive-parameter exceptional Euler inverse is positive. -/
theorem exceptionalEulerInverse_roots_pos
    (m ε : ℕ) {γ : ℝ} (hm : 0 < m)
    (hγ : (ε : ℝ) + 1 / 2 + m - 1 < γ) :
    ∀ r ∈ (exceptionalEulerInverse m ε γ).roots, 0 < r := by
  let R := exceptionalEulerInverse m ε γ
  have hmCast : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hε : 0 ≤ (ε : ℝ) := by positivity
  have hγpos : 0 < γ := by linarith
  have hγsucc : (ε : ℝ) + 1 / 2 + m - 1 < γ + 1 := by linarith
  have hsplit : R.Splits := by
    simpa [R] using
      exceptionalEulerInverse_pencil_splits
        m ε (γ₁ := γ) (γ₂ := γ + 1) (a := 1) (b := 0)
          hm hγ hγsucc (by linarith)
  have hdegree : R.natDegree = m := by
    dsimp only [R]
    exact natDegree_exceptionalEulerInverse m ε hγpos
  have hcardRoots : R.roots.card = m := by
    rw [card_roots_of_splits hsplit, hdegree]
  have hOne : R.eval 1 ≠ 0 := by
    have hsign :=
      negOnePow_mul_exceptionalEulerInverse_eval_one_pos
        m ε hm hγ
    intro hzero
    dsimp only [R] at hzero
    rw [hzero, mul_zero] at hsign
    linarith
  have hcardInterior : m - 1 ≤
      (R.roots.filter fun x => 0 < x ∧ x < 1).card := by
    simpa [R] using
      exceptionalEulerInverse_pencil_card_roots_Ioo_ge_sub_one
        m ε (γ₁ := γ) (γ₂ := γ + 1) (a := 1) (b := 0)
          hm hγ hγsucc (by linarith) (Or.inl one_ne_zero) (by simpa using hOne)
  have hzero : R.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero]
    dsimp only [R]
    exact exceptionalEulerInverse_eval_zero m ε hγpos.ne'
  have hprod : 0 < R.roots.prod := by
    have hcoeff := hsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots
    have hlead :=
      negOnePow_mul_exceptionalEulerInverse_leadingCoeff_pos
        m ε hγpos
    rw [hzero, hdegree] at hcoeff
    change 0 < (-1 : ℝ) ^ m * R.leadingCoeff at hlead
    nlinarith
  intro r hr
  change r ∈ R.roots at hr
  by_contra hrpos
  have hrle : r ≤ 0 := le_of_not_gt hrpos
  have hrzero : r ≠ 0 := by
    intro hr0
    subst r
    have hR : R ≠ 0 := by
      intro hRzero
      rw [hRzero] at hdegree
      simp at hdegree
      lia
    have hroot : R.IsRoot 0 := (Polynomial.mem_roots hR).mp hr
    rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero, hzero] at hroot
    norm_num at hroot
  have hrneg : r < 0 := lt_of_le_of_ne hrle hrzero
  let tail := R.roots.erase r
  have hcons : r ::ₘ tail = R.roots := by
    exact Multiset.cons_erase hr
  have htailCard : tail.card = m - 1 := by
    dsimp only [tail]
    rw [Multiset.card_erase_of_mem hr, hcardRoots]
    exact Nat.pred_eq_sub_one
  have hfilterTail :
      (tail.filter fun x => 0 < x ∧ x < 1).card = tail.card := by
    have hfilterEq :
        (R.roots.filter fun x => 0 < x ∧ x < 1) =
          tail.filter fun x => 0 < x ∧ x < 1 := by
      rw [← hcons]
      simp only [Multiset.filter_cons, hrneg.not_gt, false_and,
        ↓reduceIte, zero_add]
    apply le_antisymm
    · exact Multiset.card_le_card (Multiset.filter_le _ _)
    · rw [htailCard, ← hfilterEq]
      exact hcardInterior
  have htailAll : ∀ x ∈ tail, 0 < x ∧ x < 1 := by
    exact Multiset.filter_eq_self.mp
      (Multiset.eq_of_le_of_card_le
        (Multiset.filter_le _ _) hfilterTail.ge)
  have htailProd : 0 < tail.prod := by
    apply Multiset.prod_pos
    intro x hx
    exact (htailAll x hx).1
  rw [← hcons, Multiset.prod_cons] at hprod
  nlinarith

private theorem neg_coeff_one_eq_sum_roots_inv
    {p : ℝ[X]} (hp : p.Splits) (hzero : p.coeff 0 = 1)
    (hdegree : 0 < p.natDegree) :
    -p.coeff 1 = (p.roots.map fun r => r⁻¹).sum := by
  have hzeroNe : p.coeff 0 ≠ 0 := by rw [hzero]; norm_num
  have htrail : p.natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hzeroNe)
  have hrevDegree : p.reverse.natDegree = p.natDegree := by
    rw [Polynomial.reverse_natDegree, htrail, Nat.sub_zero]
  have hrevLead : p.reverse.leadingCoeff = 1 := by
    rw [Polynomial.reverse_leadingCoeff, Polynomial.trailingCoeff,
      htrail, hzero]
  have hrevNext : p.reverse.nextCoeff = p.coeff 1 := by
    rw [Polynomial.nextCoeff, if_neg (by rw [hrevDegree]; lia),
      hrevDegree, Polynomial.coeff_reverse]
    have hindex : Polynomial.revAt p.natDegree
        (p.natDegree - 1) = 1 := by
      rw [Polynomial.revAt_le (Nat.sub_le _ _)]
      lia
    rw [hindex]
  have hroots :=
    DegreeDropReversal.roots_reverse_eq_map_inv_of_splits_coeff_zero_ne
      hp hzeroNe
  have hnext :=
    (DegreeDropReversal.splits_reverse hp).nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [hrevNext, hrevLead, hroots] at hnext
  simp only [neg_mul, one_mul] at hnext
  linarith

private theorem neg_coeff_one_le_of_prec_sameDegree_of_roots_pos
    {f g : ℝ[X]} (hprec : Prec f g)
    (hdegree : f.natDegree = g.natDegree)
    (hfzero : f.coeff 0 = 1) (hgzero : g.coeff 0 = 1)
    (hfdegree : 0 < f.natDegree)
    (hfpos : ∀ r ∈ f.roots, 0 < r) :
    -g.coeff 1 ≤ -f.coeff 1 := by
  rcases hprec with
    ⟨hf, hg, ss, rs, hssSorted, hrsSorted, hssRoots, hrsRoots, hshape⟩
  have hssLength : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hssRoots, card_roots_of_splits hf.2]
  have hrsLength : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrsRoots, card_roots_of_splits hg.2]
  have halt : ListAlternates ss rs := by
    rcases hshape with hinter | halt
    · exfalso
      lia
    · exact halt.2
  have hcoord : List.Forall₂ (fun x y : ℝ => x ≤ y) ss rs :=
    listAlternates_forall₂_le halt
  have hssPos : ∀ x ∈ ss, 0 < x := by
    intro x hx
    apply hfpos x
    rw [← hssRoots]
    exact Multiset.mem_coe.mpr hx
  have hsumInv : (rs.map fun x => x⁻¹).sum ≤
      (ss.map fun x => x⁻¹).sum :=
    sum_map_inv_le_sum_map_inv_of_forall₂_le hcoord hssPos
  have hssMap : (↑(ss.map fun x => x⁻¹) : Multiset ℝ) =
      f.roots.map fun x => x⁻¹ := by
    simpa using congrArg (Multiset.map fun x : ℝ => x⁻¹) hssRoots
  have hrsMap : (↑(rs.map fun x => x⁻¹) : Multiset ℝ) =
      g.roots.map fun x => x⁻¹ := by
    simpa using congrArg (Multiset.map fun x : ℝ => x⁻¹) hrsRoots
  have hsumRoots : (g.roots.map fun x => x⁻¹).sum ≤
      (f.roots.map fun x => x⁻¹).sum := by
    simpa [← Multiset.sum_coe, hssMap, hrsMap] using hsumInv
  have hfCoeff := neg_coeff_one_eq_sum_roots_inv
    hf.2 hfzero hfdegree
  have hgCoeff := neg_coeff_one_eq_sum_roots_inv
    hg.2 hgzero (by rw [← hdegree]; exact hfdegree)
  linarith

/-- The exceptional Euler-inverse family has a fully real-rooted real pencil. -/
theorem exceptionalEulerInverse_allComboRealRooted
    (m ε : ℕ) {γ₁ γ₂ : ℝ} (hm : 0 < m)
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hγ : γ₁ < γ₂) :
    AllComboRealRooted
      (exceptionalEulerInverse m ε γ₁)
      (exceptionalEulerInverse m ε γ₂) := by
  intro a b
  exact exceptionalEulerInverse_pencil_splits
    m ε hm hγ₁ hγ₂ hγ

/-- Larger exceptional Euler parameter gives the left-hand root set in proper
position.  The strict reciprocal-root sum selects this orientation from the
Obreschkoff dichotomy. -/
theorem exceptionalEulerInverse_prec
    (m ε : ℕ) {γ₁ γ₂ : ℝ} (hm : 0 < m)
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hγ : γ₁ < γ₂) :
    Prec (exceptionalEulerInverse m ε γ₂)
      (exceptionalEulerInverse m ε γ₁) := by
  let R₁ := exceptionalEulerInverse m ε γ₁
  let R₂ := exceptionalEulerInverse m ε γ₂
  have hmCast : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hε : 0 ≤ (ε : ℝ) := by positivity
  have hγ₁pos : 0 < γ₁ := by linarith
  have hγ₂pos : 0 < γ₂ := by linarith
  have hdeg₁ : R₁.natDegree = m := by
    dsimp only [R₁]
    exact natDegree_exceptionalEulerInverse m ε hγ₁pos
  have hdeg₂ : R₂.natDegree = m := by
    dsimp only [R₂]
    exact natDegree_exceptionalEulerInverse m ε hγ₂pos
  have hR₁ : R₁ ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg₁
    simp at hdeg₁
    lia
  have hR₂ : R₂ ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg₂
    simp at hdeg₂
    lia
  have hall : AllComboRealRooted R₁ R₂ := by
    simpa only [R₁, R₂] using
      exceptionalEulerInverse_allComboRealRooted
        m ε hm hγ₁ hγ₂ hγ
  have hsplit₁ : R₁.Splits := hall.left_splits
  have hsplit₂ : R₂.Splits := hall.right_splits
  have horient : Prec R₁ R₂ ∨ Prec R₂ R₁ :=
    prec_of_allComboRealRooted hR₁ hsplit₁ hR₂ hsplit₂ hall
      (Or.inr (hdeg₁.trans hdeg₂.symm))
  rcases horient with hforward | hreverse
  · have hzero₁ : R₁.coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero]
      dsimp only [R₁]
      exact exceptionalEulerInverse_eval_zero m ε hγ₁pos.ne'
    have hzero₂ : R₂.coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero]
      dsimp only [R₂]
      exact exceptionalEulerInverse_eval_zero m ε hγ₂pos.ne'
    have hrecipLe :=
      neg_coeff_one_le_of_prec_sameDegree_of_roots_pos
        hforward (hdeg₁.trans hdeg₂.symm) hzero₁ hzero₂
          (by rw [hdeg₁]; exact hm)
          (by
            intro r hr
            exact exceptionalEulerInverse_roots_pos
              m ε hm hγ₁ r (by simpa only [R₁] using hr))
    have hrecipLt :=
      neg_coeff_one_exceptionalEulerInverse_strictMono
        m ε hm hγ₁pos hγ
    dsimp only [R₁, R₂] at hrecipLe
    linarith
  · exact hreverse

/-- The defining Euler equation `(X D + γ) R_γ = γ F`. -/
theorem eulerShiftOperator_exceptionalEulerInverse
    (m ε : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    eulerShiftOperator γ (exceptionalEulerInverse m ε γ) =
      C γ * exceptionalBasePolynomial m ε := by
  ext k
  rw [coeff_eulerShiftOperator, coeff_C_mul,
    coeff_exceptionalEulerInverse, coeff_exceptionalBasePolynomial]
  split_ifs
  · have hden : γ + (k : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  · ring

private theorem realRisingFactorial_mul_shift
    (a : ℝ) (k : ℕ) :
    a * realRisingFactorial (a + 1) k =
      (a + k) * realRisingFactorial a k := by
  rw [← realRisingFactorial_succ_left,
    realRisingFactorial_succ]
  ring

/-- The lower distinguished Euler parameter gives the last
nonexceptional toric-contribution polynomial. -/
theorem exceptionalEulerInverse_lower_eq_rPolynomial
    (m ε : ℕ) (hm : 0 < m) :
    exceptionalEulerInverse m ε
        ((ε : ℝ) + 1 / 2 + m - 1) =
      rPolynomial m ε (m - 1) := by
  let c : ℝ := ε + 1 / 2
  let A : ℝ := c + m - 1
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hA : 0 < A := by
    dsimp only [A]
    have hm_cast : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  ext k
  rw [coeff_exceptionalEulerInverse, coeff_rPolynomial]
  split_ifs with hk
  · have hC : 0 < realRisingFactorial c k :=
      realRisingFactorial_pos k hc
    have hD : 0 < realRisingFactorial (c + m + 1 / 2) k := by
      apply realRisingFactorial_pos
      positivity
    have hF : 0 < (k.factorial : ℝ) := by positivity
    have hAk : A + (k : ℝ) ≠ 0 := by positivity
    have hratio := realRisingFactorial_mul_shift A k
    simp only [exceptionalBaseCoeff, rCoeff]
    change
      (realRisingFactorial (-(m : ℝ)) k *
            realRisingFactorial (c + m) k /
          (realRisingFactorial c k * k.factorial)) * A / (A + k) =
        realRisingFactorial (-(m : ℝ)) k *
            realRisingFactorial ((m : ℝ) + 1 + ε) k *
            realRisingFactorial (c + (m - 1 : ℕ)) k /
          (realRisingFactorial c k *
            realRisingFactorial (c + (m - 1 : ℕ) + 3 / 2) k *
            k.factorial)
    have hm_sub_cast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by lia : 1 ≤ m)]
      norm_num
    rw [hm_sub_cast]
    have hfirst : (m : ℝ) + 1 + ε = c + m + 1 / 2 := by
      dsimp only [c]
      ring
    have hsecond : c + ((m : ℝ) - 1) = A := by
      dsimp only [A]
      ring
    have hthird : A + 3 / 2 = c + m + 1 / 2 := by
      dsimp only [A]
      ring
    rw [hfirst, hsecond, hthird]
    have hratio' :
        A * realRisingFactorial (c + m) k =
          (A + k) * realRisingFactorial A k := by
      have hAone : A + 1 = c + m := by
        dsimp only [A]
        ring
      simpa only [hAone] using hratio
    have hquotient :
        realRisingFactorial (c + m) k * A / (A + k) =
          realRisingFactorial A k := by
      rw [div_eq_iff hAk]
      nlinarith
    calc
      (realRisingFactorial (-(m : ℝ)) k *
              realRisingFactorial (c + m) k /
            (realRisingFactorial c k * k.factorial)) * A / (A + k) =
          (realRisingFactorial (-(m : ℝ)) k /
              (realRisingFactorial c k * k.factorial)) *
            (realRisingFactorial (c + m) k * A / (A + k)) := by ring
      _ = realRisingFactorial (-(m : ℝ)) k /
            (realRisingFactorial c k * k.factorial) *
          realRisingFactorial A k := by rw [hquotient]
      _ = realRisingFactorial (-(m : ℝ)) k *
              realRisingFactorial (c + m + 1 / 2) k *
              realRisingFactorial A k /
            (realRisingFactorial c k *
              realRisingFactorial (c + m + 1 / 2) k *
              k.factorial) := by
        have hDnorm : 0 <
            realRisingFactorial (((c + m) * 2 + 1) / 2) k := by
          apply realRisingFactorial_pos
          positivity
        field_simp [hC.ne', hD.ne', hDnorm.ne', hF.ne']
  · rfl

/-- The upper distinguished Euler parameter is exactly the exceptional
toric-contribution polynomial `R_m`. -/
theorem exceptionalEulerInverse_upper_eq_rPolynomial
    (m ε : ℕ) :
    exceptionalEulerInverse m ε
        ((ε : ℝ) + 1 / 2 + m + 1 / 2) =
      rPolynomial m ε m := by
  let c : ℝ := ε + 1 / 2
  let B : ℝ := c + m + 1 / 2
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  ext k
  rw [coeff_exceptionalEulerInverse, coeff_rPolynomial]
  split_ifs
  · have hC : 0 < realRisingFactorial c k :=
      realRisingFactorial_pos k hc
    have hD : 0 < realRisingFactorial (B + 1) k := by
      apply realRisingFactorial_pos
      positivity
    have hF : 0 < (k.factorial : ℝ) := by positivity
    have hBk : B + (k : ℝ) ≠ 0 := by positivity
    have hratio := realRisingFactorial_mul_shift B k
    simp only [exceptionalBaseCoeff, rCoeff]
    change
      (realRisingFactorial (-(m : ℝ)) k *
            realRisingFactorial (c + m) k /
          (realRisingFactorial c k * k.factorial)) * B / (B + k) =
        realRisingFactorial (-(m : ℝ)) k *
            realRisingFactorial ((m : ℝ) + 1 + ε) k *
            realRisingFactorial (c + m) k /
          (realRisingFactorial c k *
            realRisingFactorial (c + m + 3 / 2) k * k.factorial)
    have hfirst : (m : ℝ) + 1 + ε = B := by
      dsimp only [B, c]
      ring
    have hsecond : c + m + 3 / 2 = B + 1 := by
      dsimp only [B]
      ring
    rw [hfirst, hsecond]
    have hratioDiv :
        realRisingFactorial B k / realRisingFactorial (B + 1) k =
          B / (B + k) := by
      rw [div_eq_div_iff hD.ne' hBk]
      nlinarith
    have hquotient :
        realRisingFactorial B k *
            realRisingFactorial (c + m) k /
              realRisingFactorial (B + 1) k =
          realRisingFactorial (c + m) k * B / (B + k) := by
      calc
        realRisingFactorial B k *
              realRisingFactorial (c + m) k /
                realRisingFactorial (B + 1) k =
            realRisingFactorial (c + m) k *
              (realRisingFactorial B k /
                realRisingFactorial (B + 1) k) := by ring
        _ = realRisingFactorial (c + m) k * (B / (B + k)) := by
          rw [hratioDiv]
        _ = realRisingFactorial (c + m) k * B / (B + k) := by ring
    calc
      (realRisingFactorial (-(m : ℝ)) k *
              realRisingFactorial (c + m) k /
            (realRisingFactorial c k * k.factorial)) * B / (B + k) =
          realRisingFactorial (-(m : ℝ)) k /
              (realRisingFactorial c k * k.factorial) *
            (realRisingFactorial (c + m) k * B / (B + k)) := by ring
      _ = realRisingFactorial (-(m : ℝ)) k /
              (realRisingFactorial c k * k.factorial) *
            (realRisingFactorial B k *
              realRisingFactorial (c + m) k /
                realRisingFactorial (B + 1) k) := by rw [hquotient]
      _ = realRisingFactorial (-(m : ℝ)) k *
              realRisingFactorial B k *
              realRisingFactorial (c + m) k /
            (realRisingFactorial c k *
              realRisingFactorial (B + 1) k * k.factorial) := by ring
  · rfl

/-- The pencil between the lower distinguished parameter and any larger
parameter is real-rooted.  Approximants preserve the top two coefficients,
so the possible degree drop from `m` to `m - 1` is retained in the limit. -/
private theorem exceptionalEulerInverse_lower_allComboRealRooted
    (m ε : ℕ) (hm : 0 < m) {γ : ℝ}
    (hγ : (ε : ℝ) + 1 / 2 + m - 1 < γ) :
    AllComboRealRooted
      (exceptionalEulerInverse m ε
        ((ε : ℝ) + 1 / 2 + m - 1))
      (exceptionalEulerInverse m ε γ) := by
  let A : ℝ := (ε : ℝ) + 1 / 2 + m - 1
  let L := exceptionalEulerInverse m ε A
  let U := exceptionalEulerInverse m ε γ
  have hmCast : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hA : 0 < A := by
    dsimp only [A]
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  have hγpos : 0 < γ := hA.trans hγ
  have hAγ : A ≠ γ := hγ.ne
  have hLdegree : L.natDegree = m := by
    dsimp only [L]
    exact natDegree_exceptionalEulerInverse m ε hA
  have hUdegree : U.natDegree = m := by
    dsimp only [U]
    exact natDegree_exceptionalEulerInverse m ε hγpos
  have hdetLimit :
      L.coeff m * U.coeff (m - 1) -
          U.coeff m * L.coeff (m - 1) ≠ 0 := by
    rw [sub_ne_zero]
    exact exceptionalEulerInverse_topCoeff_det_ne_zero
      m ε hm hA hγpos hAγ
  intro a b
  let Q := C a * L + C b * U
  by_cases hQ : Q = 0
  · rw [show C a * exceptionalEulerInverse m ε
          ((ε : ℝ) + 1 / 2 + m - 1) +
          C b * exceptionalEulerInverse m ε γ = Q by rfl, hQ]
    exact Polynomial.Splits.zero
  have hQlower : m - 1 ≤ Q.natDegree := by
    simpa only [Q, L, U] using
      exceptionalEulerInverse_pencil_natDegree_ge_sub_one
        m ε hm hA hγpos hAγ hQ
  have hQupper : Q.natDegree ≤ m := by
    dsimp only [Q, L, U]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le
        ((Polynomial.natDegree_C_mul_le a _).trans
          (natDegree_exceptionalEulerInverse_le m ε A))
        ((Polynomial.natDegree_C_mul_le b _).trans
          (natDegree_exceptionalEulerInverse_le m ε γ)))
  have hQdegree : Q.natDegree = m - 1 ∨ Q.natDegree = m := by
    lia
  have hQlead : Q.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hQ
  let gap : ℝ := (γ - A) / 2
  let δ : ℕ → ℝ := fun n => gap * ((n + 1 : ℕ) : ℝ)⁻¹
  let γn : ℕ → ℝ := fun n => A + δ n
  let R : ℕ → ℝ[X] := fun n => exceptionalEulerInverse m ε (γn n)
  let D : ℕ → ℝ := fun n =>
    (R n).coeff m * U.coeff (m - 1) -
      U.coeff m * (R n).coeff (m - 1)
  have hδpos : ∀ n, 0 < δ n := by
    intro n
    dsimp only [δ, gap]
    positivity
  have hδle : ∀ n, δ n ≤ gap := by
    intro n
    dsimp only [δ]
    apply mul_le_of_le_one_right
    · dsimp only [gap]
      positivity
    · apply (inv_le_one₀ (by positivity)).2
      norm_num
  have hγnLower : ∀ n, A < γn n := by
    intro n
    dsimp only [γn]
    linarith [hδpos n]
  have hγnUpper : ∀ n, γn n < γ := by
    intro n
    calc
      γn n = A + δ n := by rfl
      _ ≤ A + gap := by linarith [hδle n]
      _ < γ := by
        dsimp only [gap, A]
        linarith
  have hγnPos : ∀ n, 0 < γn n := by
    intro n
    exact hA.trans (hγnLower n)
  have hD : ∀ n, D n ≠ 0 := by
    intro n
    dsimp only [D, R]
    rw [sub_ne_zero]
    exact exceptionalEulerInverse_topCoeff_det_ne_zero
      m ε hm (hγnPos n) hγpos (hγnUpper n).ne
  let an : ℕ → ℝ := fun n =>
    (Q.coeff m * U.coeff (m - 1) -
      U.coeff m * Q.coeff (m - 1)) / D n
  let bn : ℕ → ℝ := fun n =>
    ((R n).coeff m * Q.coeff (m - 1) -
      Q.coeff m * (R n).coeff (m - 1)) / D n
  let Qn : ℕ → ℝ[X] := fun n => C (an n) * R n + C (bn n) * U
  have hQnTop : ∀ n, (Qn n).coeff m = Q.coeff m := by
    intro n
    dsimp only [Qn, an, bn]
    simp only [coeff_add, coeff_C_mul]
    field_simp [hD n]
    ring
  have hQnPrev : ∀ n, (Qn n).coeff (m - 1) = Q.coeff (m - 1) := by
    intro n
    dsimp only [Qn, an, bn]
    simp only [coeff_add, coeff_C_mul]
    field_simp [hD n]
    ring
  have hQnDegree : ∀ n, (Qn n).natDegree = Q.natDegree := by
    intro n
    rcases hQdegree with hdrop | hfull
    · rw [hdrop]
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        intro k hk
        by_cases hkm : k = m
        · subst k
          rw [hQnTop]
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (by lia)
        · have hmk : m < k := by lia
          dsimp only [Qn, R, U]
          simp only [coeff_add, coeff_C_mul,
            coeff_exceptionalEulerInverse, if_neg (not_le.mpr hmk)]
          ring
      · rw [hQnPrev]
        simpa only [Polynomial.leadingCoeff, hdrop] using hQlead
    · rw [hfull]
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      · dsimp only [Qn, R, U]
        exact (Polynomial.natDegree_add_le _ _).trans
          (max_le
            ((Polynomial.natDegree_C_mul_le (an n) _).trans
              (natDegree_exceptionalEulerInverse_le m ε (γn n)))
            ((Polynomial.natDegree_C_mul_le (bn n) _).trans
              (natDegree_exceptionalEulerInverse_le m ε γ)))
      · rw [hQnTop]
        simpa only [Polynomial.leadingCoeff, hfull] using hQlead
  have hQnSplits : ∀ n, (Qn n).Splits := by
    intro n
    dsimp only [Qn, R, U]
    apply exceptionalEulerInverse_pencil_splits m ε hm
    · simpa only [A] using hγnLower n
    · simpa only [A] using hγ
    · exact hγnUpper n
  have hδTendsto : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have hinv : Filter.Tendsto
        (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹)
        Filter.atTop (nhds 0) := by
      have heq : (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) =
          (fun n : ℕ => ((n : ℝ)⁻¹)) ∘ fun n => n + 1 := by
        funext n
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      rw [heq]
      exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1)
    simpa only [δ, mul_zero] using tendsto_const_nhds.mul hinv
  have hγnTendsto : Filter.Tendsto γn Filter.atTop (nhds A) := by
    simpa only [γn, add_zero] using tendsto_const_nhds.add hδTendsto
  have hRcoeffTendsto : ∀ k,
      Filter.Tendsto (fun n => (R n).coeff k) Filter.atTop
        (nhds (L.coeff k)) := by
    intro k
    dsimp only [R, L]
    rw [show (fun n => (exceptionalEulerInverse m ε (γn n)).coeff k) =
        fun n => if k ≤ m then
          exceptionalBaseCoeff m ε k * γn n / (γn n + k)
        else 0 by
          funext n
          rw [coeff_exceptionalEulerInverse]]
    rw [coeff_exceptionalEulerInverse]
    split_ifs
    · exact (tendsto_const_nhds.mul hγnTendsto).div
        (hγnTendsto.add tendsto_const_nhds)
        (by positivity)
    · exact tendsto_const_nhds
  have hDTendsto : Filter.Tendsto D Filter.atTop
      (nhds (L.coeff m * U.coeff (m - 1) -
        U.coeff m * L.coeff (m - 1))) := by
    dsimp only [D]
    exact ((hRcoeffTendsto m).mul_const _).sub
      (tendsto_const_nhds.mul (hRcoeffTendsto (m - 1)))
  have hanLimit :
      (Q.coeff m * U.coeff (m - 1) -
          U.coeff m * Q.coeff (m - 1)) /
          (L.coeff m * U.coeff (m - 1) -
            U.coeff m * L.coeff (m - 1)) = a := by
    apply (div_eq_iff hdetLimit).2
    dsimp only [Q]
    simp only [coeff_add, coeff_C_mul]
    ring
  have hbnLimit :
      (L.coeff m * Q.coeff (m - 1) -
          Q.coeff m * L.coeff (m - 1)) /
          (L.coeff m * U.coeff (m - 1) -
            U.coeff m * L.coeff (m - 1)) = b := by
    apply (div_eq_iff hdetLimit).2
    dsimp only [Q]
    simp only [coeff_add, coeff_C_mul]
    ring
  have hanTendsto : Filter.Tendsto an Filter.atTop (nhds a) := by
    rw [← hanLimit]
    dsimp only [an]
    exact tendsto_const_nhds.div hDTendsto hdetLimit
  have hbnTendsto : Filter.Tendsto bn Filter.atTop (nhds b) := by
    rw [← hbnLimit]
    dsimp only [bn]
    exact ((hRcoeffTendsto m).mul_const _).sub
      (tendsto_const_nhds.mul (hRcoeffTendsto (m - 1))) |>.div
        hDTendsto hdetLimit
  have hQnCoeffTendsto : ∀ k,
      Filter.Tendsto (fun n => (Qn n).coeff k) Filter.atTop
        (nhds (Q.coeff k)) := by
    intro k
    dsimp only [Qn, Q]
    simp only [coeff_add, coeff_C_mul]
    exact (hanTendsto.mul (hRcoeffTendsto k)).add
      (hbnTendsto.mul_const _)
  let q := C Q.leadingCoeff⁻¹ * Q
  let qn : ℕ → ℝ[X] := fun n => C Q.leadingCoeff⁻¹ * Qn n
  have hqMonic : q.Monic := by
    dsimp only [q]
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ hQlead
  have hqnMonic : ∀ n, (qn n).Monic := by
    intro n
    dsimp only [qn]
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [show (Qn n).leadingCoeff = Q.leadingCoeff by
      simp only [Polynomial.leadingCoeff, hQnDegree n]
      rcases hQdegree with hdrop | hfull
      · rw [hdrop, hQnPrev]
      · rw [hfull, hQnTop]]
    exact inv_mul_cancel₀ hQlead
  have hqnDegree : ∀ n, (qn n).natDegree = q.natDegree := by
    intro n
    dsimp only [qn, q]
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hQlead),
      Polynomial.natDegree_C_mul (inv_ne_zero hQlead), hQnDegree]
  have hqnSplits : ∀ n, (qn n).Splits := by
    intro n
    exact (hQnSplits n).C_mul Q.leadingCoeff⁻¹
  have hqnCoeffTendsto : ∀ k,
      Filter.Tendsto (fun n => (qn n).coeff k) Filter.atTop
        (nhds (q.coeff k)) := by
    intro k
    dsimp only [qn, q]
    simp only [coeff_C_mul]
    exact tendsto_const_nhds.mul (hQnCoeffTendsto k)
  have hqSplits := splits_of_monic_of_coeff_tendsto
    hqMonic hqnMonic hqnDegree hqnSplits hqnCoeffTendsto
  have hscaled := hqSplits.C_mul Q.leadingCoeff
  rw [show C Q.leadingCoeff * q = Q by
    dsimp only [q]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hQlead, C_1, one_mul]] at hscaled
  simpa only [Q, L, U, A] using hscaled

/-- The upper distinguished exceptional polynomial is in proper position
before the lower endpoint polynomial. -/
theorem exceptionalEulerInverse_upper_prec_lower
    (m ε : ℕ) (hm : 0 < m) :
    Prec
      (exceptionalEulerInverse m ε
        ((ε : ℝ) + 1 / 2 + m + 1 / 2))
      (exceptionalEulerInverse m ε
        ((ε : ℝ) + 1 / 2 + m - 1)) := by
  let A : ℝ := (ε : ℝ) + 1 / 2 + m - 1
  let B : ℝ := (ε : ℝ) + 1 / 2 + m + 1 / 2
  let L := exceptionalEulerInverse m ε A
  let U := exceptionalEulerInverse m ε B
  have hmCast : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hA : 0 < A := by
    dsimp only [A]
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hAB : A < B := by
    dsimp only [A, B]
    linarith
  have hLdegree : L.natDegree = m := by
    dsimp only [L]
    exact natDegree_exceptionalEulerInverse m ε hA
  have hUdegree : U.natDegree = m := by
    dsimp only [U]
    exact natDegree_exceptionalEulerInverse m ε hB
  have hL : L ≠ 0 := by
    intro hzero
    rw [hzero] at hLdegree
    simp at hLdegree
    lia
  have hU : U ≠ 0 := by
    intro hzero
    rw [hzero] at hUdegree
    simp at hUdegree
    lia
  have hall : AllComboRealRooted L U := by
    simpa only [L, U, A, B] using
      exceptionalEulerInverse_lower_allComboRealRooted
        m ε hm (γ := B) (by dsimp only [B]; linarith)
  have horient : Prec L U ∨ Prec U L :=
    prec_of_allComboRealRooted hL hall.left_splits hU hall.right_splits
      hall (Or.inr (hLdegree.trans hUdegree.symm))
  rcases horient with hwrong | hright
  · have hLzero : L.coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero]
      dsimp only [L]
      exact exceptionalEulerInverse_eval_zero m ε hA.ne'
    have hUzero : U.coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero]
      dsimp only [U]
      exact exceptionalEulerInverse_eval_zero m ε hB.ne'
    have hwrongCoeff :=
      neg_coeff_one_le_of_prec_sameDegree_of_roots_pos
        hwrong (hLdegree.trans hUdegree.symm) hLzero hUzero
          (by rw [hLdegree]; exact hm)
          (by
            intro r hr
            rw [show L = rPolynomial m ε (m - 1) by
              simpa only [L, A] using
                exceptionalEulerInverse_lower_eq_rPolynomial m ε hm] at hr
            exact (rPolynomial_rightClosedIntervalRootData
              m ε (m - 1) hm (by lia)).roots_mem_Ioc r hr |>.1)
    have hstrict := neg_coeff_one_exceptionalEulerInverse_strictMono
      m ε hm hA hAB
    dsimp only [L, U, A, B] at hwrongCoeff
    linarith
  · simpa only [U, L, B, A] using hright

/-- The two exceptional toric-contribution polynomials have the required
weak proper-position orientation. -/
theorem rPolynomial_exceptional_prec (m ε : ℕ) (hm : 0 < m) :
    Prec (rPolynomial m ε m) (rPolynomial m ε (m - 1)) := by
  rw [← exceptionalEulerInverse_upper_eq_rPolynomial m ε,
    ← exceptionalEulerInverse_lower_eq_rPolynomial m ε hm]
  exact exceptionalEulerInverse_upper_prec_lower m ε hm

end ToricContribution
end ParkingFunctions
end RealRooted
