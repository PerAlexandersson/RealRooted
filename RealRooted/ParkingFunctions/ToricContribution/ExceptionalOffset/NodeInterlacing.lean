import RealRooted.CommonInterleaverSeq
import RealRooted.ParkingFunctions.ToricContribution.ExceptionalOffset.ProperPositionAndParameters
import RealRooted.SuccDegreeLeftEndpoint

/-!
# Exceptional-offset Jacobi-node interlacing

This layer combines the exceptional endpoint with the finite offsets, proves
the Jacobi-node sign evaluations, and packages the all-offset consequences.
-/

open Polynomial
open MeasureTheory Set

noncomputable section

namespace RealRooted
namespace ParkingFunctions
namespace ToricContribution

local notation "orderedRoot" => RealRooted.orderedRoot

private theorem finite_roots_sort
    (m ε d : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) :
    ((rPolynomial m ε d).roots.sort (· ≤ ·)) =
      ((signedTriangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε)
        d d).roots.sort (· ≤ ·)) ++ [1] := by
  let S := signedTriangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε)
    d d
  let R := rPolynomial m ε d
  have hS_data : IntervalRootData S (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε d d hm hd le_rfl
    dsimp only [S]
    convert hdata using 1
    lia
  have hS_ne : S ≠ 0 := by
    intro hzero
    apply hS_data.eval_zero_ne
    simp [hzero]
  obtain ⟨k, hk, hcollapse⟩ :=
    exists_one_sub_X_mul_signedTriangleFamily_diagonal_eq_C_mul_rPolynomial
      m ε d hm hd
  have hone_sub_ne : (1 - X : ℝ[X]) ≠ 0 := by
    intro hzero
    have h := congrArg (Polynomial.eval 0) hzero
    norm_num at h
  have hroots : R.roots = {1} + S.roots := by
    have h := congrArg Polynomial.roots hcollapse
    have hproduct_ne : (1 - X) * S ≠ 0 := mul_ne_zero hone_sub_ne hS_ne
    rw [Polynomial.roots_mul hproduct_ne,
      Polynomial.roots_C_mul _ hk.ne'] at h
    have hlinear : (1 - X : ℝ[X]).roots = {1} := by
      rw [show (1 - X : ℝ[X]) = -(X - C 1) by rw [C_1]; ring,
        Polynomial.roots_neg, Polynomial.roots_X_sub_C]
    simpa only [R, S, hlinear] using h.symm
  have hperm :
      (R.roots.sort (· ≤ ·)).Perm (S.roots.sort (· ≤ ·) ++ [1]) := by
    rw [← Multiset.coe_eq_coe]
    calc
      (↑(R.roots.sort (· ≤ ·)) : Multiset ℝ) = R.roots :=
        Multiset.sort_eq _ _
      _ = {1} + S.roots := hroots
      _ = S.roots + {1} := add_comm _ _
      _ = (↑(S.roots.sort (· ≤ ·)) : Multiset ℝ) + ({1} : Multiset ℝ) := by
        rw [Multiset.sort_eq]
      _ = (↑(S.roots.sort (· ≤ ·) ++ [(1 : ℝ)]) : Multiset ℝ) := rfl
  have hleft : (R.roots.sort (· ≤ ·)).Pairwise (· ≤ ·) := by
    simp
  have hright : (S.roots.sort (· ≤ ·) ++ [1]).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨?_, by simp, ?_⟩
    · simp
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact (hS_data.roots_mem_Ioo a ((Multiset.mem_sort _).mp ha)).2.le
  change R.roots.sort (· ≤ ·) = S.roots.sort (· ≤ ·) ++ [1]
  exact hperm.eq_of_pairwise
    (fun a b _ _ hab hba => le_antisymm hab hba) hleft hright

private theorem Interlaces.orderedRoot_bounds {g f : ℝ[X]} {n : ℕ}
    (h : Interlaces g f) (hgdeg : g.natDegree = n)
    (hfdeg : f.natDegree = n + 1) (i : Fin n) :
    orderedRoot f (n + 1) i.castSucc ≤ orderedRoot g n i ∧
      orderedRoot g n i ≤ orderedRoot f (n + 1) i.succ := by
  obtain ⟨hf, hg, _, rs, ss, hrs, hss, hrs_eq, hss_eq, hint⟩ := h
  have hrs_len : rs.length = n + 1 := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2, hfdeg]
  have hss_len : ss.length = n := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hg.2, hgdeg]
  have hrs_canonical : f.roots.sort (· ≤ ·) = rs := by
    rw [← hrs_eq, Multiset.coe_sort]
    exact List.mergeSort_eq_self (· ≤ ·) hrs
  have hss_canonical : g.roots.sort (· ≤ ·) = ss := by
    rw [← hss_eq, Multiset.coe_sort]
    exact List.mergeSort_eq_self (· ≤ ·) hss
  have hbounds := listInterlaces_getD_bounds ss rs hint (by lia)
  constructor
  · change (f.roots.sort (· ≤ ·)).getD i.val 0 ≤
      (g.roots.sort (· ≤ ·)).getD i.val 0
    rw [hrs_canonical, hss_canonical]
    exact hbounds.1 i.val (by lia)
  · change (g.roots.sort (· ≤ ·)).getD i.val 0 ≤
      (f.roots.sort (· ≤ ·)).getD (i.val + 1) 0
    rw [hrs_canonical, hss_canonical]
    exact hbounds.2 i.val (by lia)

private theorem orderedRoot_shiftedJacobi_eq_monicRoot
    (n : ℕ) {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (i : Fin n) :
    orderedRoot (shiftedJacobi n α β) n i =
      shiftedJacobiMonicRoot n i α β := by
  have hscale :
      (((-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n)⁻¹) ≠ 0 := by
    intro hzero
    have hne := (monic_shiftedJacobiMonic n hα hβ).ne_zero
    apply hne
    rw [shiftedJacobiMonic, hzero, C_0, zero_mul]
  rw [RealRooted.orderedRoot, shiftedJacobiMonicRoot, shiftedJacobiMonic,
    Polynomial.roots_C_mul _ hscale]

private theorem shiftedJacobi_eval_derivative_ne_zero
    (n : ℕ) {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (hx : (shiftedJacobi n α β).IsRoot x) :
    (shiftedJacobi n α β).derivative.eval x ≠ 0 := by
  let c : ℝ := (-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n
  have hc : c ≠ 0 := by
    intro hzero
    have hne := (monic_shiftedJacobiMonic n hα hβ).ne_zero
    apply hne
    simp [shiftedJacobiMonic, c, hzero]
  have hrecover : shiftedJacobi n α β =
      C c * shiftedJacobiMonic n α β := by
    rw [shiftedJacobiMonic]
    change shiftedJacobi n α β =
      C c * (C c⁻¹ * shiftedJacobi n α β)
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  have hxMonic : (shiftedJacobiMonic n α β).IsRoot x := by
    rw [Polynomial.IsRoot.def] at hx ⊢
    have heval := congrArg (Polynomial.eval x) hrecover
    simp only [eval_mul, eval_C, hx] at heval
    exact (mul_eq_zero.mp heval.symm).resolve_left hc
  have hmonic := shiftedJacobiMonic_derivative_eval_ne_zero n hα hβ hxMonic
  have hderivative := congrArg derivative hrecover
  simp only [derivative_C_mul] at hderivative
  have heval := congrArg (Polynomial.eval x) hderivative
  simp only [eval_mul, eval_C] at heval
  rw [heval]
  exact mul_ne_zero hc hmonic

private theorem shiftedJacobiMonicRoot_base_interlacing_jacobi
    (n : ℕ) {α : ℝ} (hα : -1 < α) :
    (∀ i : Fin n,
      shiftedJacobiMonicRoot (n + 1) i.castSucc α 0 <
        shiftedJacobiMonicRoot n i (α + 3 / 2) 1) ∧
    ∀ i : Fin n,
      shiftedJacobiMonicRoot n i (α + 3 / 2) 1 <
        shiftedJacobiMonicRoot (n + 1) i.succ α 0 := by
  have hβ : -1 < (0 : ℝ) := by norm_num
  let F := shiftedJacobi (n + 1) α 0
  let D := shiftedJacobi n (α + 1) 1
  have hDF : Interlaces D F := by
    simpa only [D, F, zero_add] using
      shiftedJacobi_interlaces_shift_both n hα hβ
  have hDF_bounds := Interlaces.orderedRoot_bounds hDF
    (natDegree_shiftedJacobi n (by linarith) (by norm_num))
    (natDegree_shiftedJacobi (n + 1) hα hβ)
  have hDF_noCommon : ∀ x, D.IsRoot x → ¬F.IsRoot x := by
    intro x hxD hxF
    have hder := shiftedJacobi_eval_derivative_ne_zero (n + 1) hα hβ hxF
    have hidentity := derivative_shiftedJacobi n α 0
    have heval := congrArg (Polynomial.eval x) hidentity
    rw [Polynomial.IsRoot.def] at hxD
    dsimp only [D] at hxD
    simp only [eval_mul, eval_C] at heval
    have hxD' : (shiftedJacobi n (α + 1) (0 + 1)).eval x = 0 := by
      simpa only [zero_add] using hxD
    rw [hxD', mul_zero] at heval
    exact hder heval
  let DM := shiftedJacobiMonic n (α + 1) 1
  let J := shiftedJacobiMonic n (α + 3 / 2) 1
  have hDJ : StrictPrecSameDegree DM J := by
    dsimp only [DM, J]
    have hprec := shiftedJacobiMonic_prec_alpha_add n
      (α := α + 1) (t := (1 / 2 : ℝ)) (by linarith)
      (by norm_num) (by norm_num)
    rw [show α + 3 / 2 = α + 1 + 1 / 2 by ring]
    exact StrictPrecSameDegree.of_prec_of_no_common hprec
      (by rw [natDegree_shiftedJacobiMonic n (by linarith) (by norm_num),
        natDegree_shiftedJacobiMonic n (by linarith) (by norm_num)])
      (shiftedJacobiMonic_noCommonRoot_alpha_add n
        (by linarith) (by norm_num) (by norm_num))
  have hDJ_bounds := hDJ.interlacing_fin
    (natDegree_shiftedJacobiMonic n (by linarith) (by norm_num))
    (fun i => shiftedJacobiMonicRoot n i (α + 1) 1)
    (fun i => shiftedJacobiMonicRoot_isRoot n i (by linarith) (by norm_num))
    (strictMono_shiftedJacobiMonicRoot n (by linarith) (by norm_num))
    (fun i => shiftedJacobiMonicRoot n i (α + 3 / 2) 1)
    (fun i => shiftedJacobiMonicRoot_isRoot n i (by linarith) (by norm_num))
    (strictMono_shiftedJacobiMonicRoot n (by linarith) (by norm_num))
  let K := shiftedJacobiMonic n (α + 2) 1
  let Q := shiftedJacobiMonic n (α + 2) 0
  have hJK : StrictPrecSameDegree J K := by
    dsimp only [J, K]
    have hprec := shiftedJacobiMonic_prec_alpha_add n
      (α := α + 3 / 2) (t := (1 / 2 : ℝ)) (by linarith)
      (by norm_num) (by norm_num)
    rw [show α + 2 = α + 3 / 2 + 1 / 2 by ring]
    exact StrictPrecSameDegree.of_prec_of_no_common hprec
      (by rw [natDegree_shiftedJacobiMonic n (by linarith) (by norm_num),
        natDegree_shiftedJacobiMonic n (by linarith) (by norm_num)])
      (shiftedJacobiMonic_noCommonRoot_alpha_add n
        (by linarith) (by norm_num) (by norm_num))
  have hKQ : StrictPrecSameDegree K Q := by
    have hprec := shiftedJacobiMonic_prec_beta_add_one n
      (α := α + 2) (β := 0) (by linarith) (by norm_num)
    have hstrict := StrictPrecSameDegree.of_prec_of_no_common hprec
      (by rw [natDegree_shiftedJacobiMonic n (by linarith) (by norm_num),
        natDegree_shiftedJacobiMonic n (by linarith) (by norm_num)])
      (shiftedJacobiMonic_noCommonRoot_beta_add_one n
        (by linarith) (by norm_num))
    simpa only [K, Q, zero_add] using hstrict
  have hQF := shiftedJacobiMonic_interlaces_alpha_add_two_degree_pred n hα hβ
  have hQF_bounds := Interlaces.orderedRoot_bounds hQF
    (natDegree_shiftedJacobiMonic n (by linarith) hβ)
    (natDegree_shiftedJacobiMonic (n + 1) hα hβ)
  have hQF_noCommon : ∀ x,
      Q.IsRoot x → ¬(shiftedJacobiMonic (n + 1) α 0).IsRoot x := by
    intro x hxQ hxF
    have hpos := shiftedJacobiMonic_eval_mul_alpha_add_two_degree_pred_pos
      n hα hβ hxF
    dsimp only [Q] at hxQ
    rw [Polynomial.IsRoot.def] at hxQ
    simp [hxQ] at hpos
  constructor
  · intro i
    have hleft := (hDF_bounds i).1
    have hstrict : orderedRoot F (n + 1) i.castSucc <
        orderedRoot D n i := lt_of_le_of_ne hleft (by
      intro heq
      apply hDF_noCommon (orderedRoot D n i)
      · exact (shiftedJacobi_intervalRootData n (by linarith) (by norm_num)).orderedRoot_isRoot i
      · rw [← heq]
        exact (shiftedJacobi_intervalRootData (n + 1) hα hβ).orderedRoot_isRoot i.castSucc)
    rw [orderedRoot_shiftedJacobi_eq_monicRoot (n + 1) hα hβ,
      orderedRoot_shiftedJacobi_eq_monicRoot n (by linarith) (by norm_num)] at hstrict
    exact hstrict.trans (hDJ_bounds.1 i)
  · intro i
    have hJK_i := (hJK.interlacing_fin
      (natDegree_shiftedJacobiMonic n (by linarith) (by norm_num))
      (fun j => shiftedJacobiMonicRoot n j (α + 3 / 2) 1)
      (fun j => shiftedJacobiMonicRoot_isRoot n j (by linarith) (by norm_num))
      (strictMono_shiftedJacobiMonicRoot n (by linarith) (by norm_num))
      (fun j => shiftedJacobiMonicRoot n j (α + 2) 1)
      (fun j => shiftedJacobiMonicRoot_isRoot n j (by linarith) (by norm_num))
      (strictMono_shiftedJacobiMonicRoot n (by linarith) (by norm_num))).1 i
    have hKQ_i := (hKQ.interlacing_fin
      (natDegree_shiftedJacobiMonic n (by linarith) (by norm_num))
      (fun j => shiftedJacobiMonicRoot n j (α + 2) 1)
      (fun j => shiftedJacobiMonicRoot_isRoot n j (by linarith) (by norm_num))
      (strictMono_shiftedJacobiMonicRoot n (by linarith) (by norm_num))
      (fun j => shiftedJacobiMonicRoot n j (α + 2) 0)
      (fun j => shiftedJacobiMonicRoot_isRoot n j (by linarith) (by norm_num))
      (strictMono_shiftedJacobiMonicRoot n (by linarith) (by norm_num))).1 i
    have hright := (hQF_bounds i).2
    have hright_strict : shiftedJacobiMonicRoot n i (α + 2) 0 <
        orderedRoot (shiftedJacobiMonic (n + 1) α 0) (n + 1) i.succ :=
      lt_of_le_of_ne hright (by
        intro heq
        apply hQF_noCommon (shiftedJacobiMonicRoot n i (α + 2) 0)
        · exact shiftedJacobiMonicRoot_isRoot n i (by linarith) hβ
        · rw [heq]
          exact shiftedJacobiMonicRoot_isRoot (n + 1) i.succ hα hβ)
    exact hJK_i.trans (hKQ_i.trans hright_strict)

private theorem prec_derivative_of_nonpos_of_pos_natDegree
    {p u v : ℝ[X]} (hp : p.Splits) (hdegree : 1 ≤ p.natDegree)
    (hdegreeLower : p.natDegree ≤ (u * p + v * p.derivative).natDegree)
    (hdegreeUpper : (u * p + v * p.derivative).natDegree ≤ p.natDegree + 1)
    (houtputPos : HasPosLeadingCoeff (u * p + v * p.derivative))
    (hpPos : HasPosLeadingCoeff p)
    (hvNonpos : ∀ r, p.IsRoot r → v.eval r ≤ 0) :
    Prec p (u * p + v * p.derivative) := by
  have hderivative : Interlaces p.derivative p :=
    interlaces_derivative_of_pos_natDegree hpPos.ne_zero hp hpPos hdegree
  have hderivativePos : HasPosLeadingCoeff p.derivative :=
    hpPos.derivative (by lia)
  exact prec_of_interlaces_evalCoeff_nonpos
    (f := p) (g := p.derivative) (a := u) (b := v)
    hderivative hderivativePos houtputPos hdegreeLower hdegreeUpper hvNonpos

private theorem exceptionalBasePolynomial_prec_exceptionalEulerInverse
    (m ε : ℕ) {γ : ℝ} (hm : 0 < m) (hγ : 0 < γ)
    (hγlower : (ε : ℝ) + 1 / 2 + m - 1 < γ)
    (hUsplits : (exceptionalEulerInverse m ε γ).Splits) :
    Prec (exceptionalBasePolynomial m ε)
      (exceptionalEulerInverse m ε γ) := by
  let U := exceptionalEulerInverse m ε γ
  let F := exceptionalBasePolynomial m ε
  let u := U.comp (1 - X)
  let f := F.comp (1 - X)
  have hUdegree : U.natDegree = m := by
    exact natDegree_exceptionalEulerInverse m ε hγ
  have hFdegree : F.natDegree = m := by
    obtain ⟨scale, hscalePos⟩ : ∃ scale : ℝ, 0 < scale ∧
        F = C scale * shiftedJacobi m ((ε : ℝ) - 1 / 2) 0 := by
      let scale := (Ring.choose ((m : ℝ) + ((ε : ℝ) - 1 / 2)) m)⁻¹
      have hchoose : 0 < Ring.choose ((m : ℝ) + ((ε : ℝ) - 1 / 2)) m := by
        apply Polynomial.ring_choose_pos
        have hε : 0 ≤ (ε : ℝ) := by positivity
        linarith
      exact ⟨scale, inv_pos.mpr hchoose,
        exceptionalBasePolynomial_eq_C_mul_shiftedJacobi m ε⟩
    rw [hscalePos.2, Polynomial.natDegree_C_mul hscalePos.1.ne',
      natDegree_shiftedJacobi m (by
        have hε : 0 ≤ (ε : ℝ) := by positivity
        linarith) (by norm_num)]
  have hUlead : 0 < (-1 : ℝ) ^ m * U.leadingCoeff := by
    exact negOnePow_mul_exceptionalEulerInverse_leadingCoeff_pos m ε hγ
  have hFlead : 0 < (-1 : ℝ) ^ m * F.leadingCoeff := by
    have hratio : 0 < γ / (γ + m) := by positivity
    have hcoeff : U.leadingCoeff = F.leadingCoeff * (γ / (γ + m)) := by
      rw [Polynomial.leadingCoeff, hUdegree, Polynomial.leadingCoeff, hFdegree,
        coeff_exceptionalEulerInverse, coeff_exceptionalBasePolynomial,
        if_pos le_rfl]
      simp only [if_pos le_rfl]
      ring
    rw [hcoeff] at hUlead
    have heq : (-1 : ℝ) ^ m * (F.leadingCoeff * (γ / (γ + m))) =
        ((-1 : ℝ) ^ m * F.leadingCoeff) * (γ / (γ + m)) := by ring
    rw [heq] at hUlead
    exact pos_of_mul_pos_right (by simpa only [mul_comm] using hUlead) hratio.le
  have honeDegree : (1 - X : ℝ[X]).natDegree = 1 := by
    rw [show (1 - X : ℝ[X]) = -(X - C 1) by rw [C_1]; ring,
      Polynomial.natDegree_neg]
    simpa using (Polynomial.natDegree_X_sub_C (R := ℝ) 1)
  have huDegree : u.natDegree = m := by
    dsimp only [u]
    rw [Polynomial.natDegree_comp, hUdegree, honeDegree, mul_one]
  have hfDegree : f.natDegree = m := by
    dsimp only [f]
    rw [Polynomial.natDegree_comp, hFdegree, honeDegree, mul_one]
  have huPos : HasPosLeadingCoeff u := by
    rw [HasPosLeadingCoeff]
    dsimp only [u]
    rw [Polynomial.leadingCoeff_comp (by rw [honeDegree]; lia), hUdegree]
    have honeLead : (1 - X : ℝ[X]).leadingCoeff = -1 := by
      rw [Polynomial.leadingCoeff, honeDegree, coeff_sub, coeff_one, coeff_X]
      norm_num
    rw [honeLead]
    simpa only [mul_comm] using hUlead
  have hfPos : HasPosLeadingCoeff f := by
    rw [HasPosLeadingCoeff]
    dsimp only [f]
    rw [Polynomial.leadingCoeff_comp (by rw [honeDegree]; lia), hFdegree]
    have honeLead : (1 - X : ℝ[X]).leadingCoeff = -1 := by
      rw [Polynomial.leadingCoeff, honeDegree, coeff_sub, coeff_one, coeff_X]
      norm_num
    rw [honeLead]
    simpa only [mul_comm] using hFlead
  have hUne : U ≠ 0 := by
    intro hzero
    rw [hzero] at hUdegree
    simp at hUdegree
    lia
  have huSplits : u.Splits := by
    exact (isRealRooted_comp_one_sub_X hUne hUsplits).2
  have hrec : C γ * f = C γ * u + -(1 - X) * u.derivative := by
    have heuler := eulerShiftOperator_exceptionalEulerInverse m ε hγ
    have hcomp := congrArg (fun p : ℝ[X] => p.comp (1 - X)) heuler
    dsimp only [eulerShiftOperator] at hcomp
    simp only [add_comp, mul_comp, X_comp, C_comp] at hcomp
    have hderivative : u.derivative = -U.derivative.comp (1 - X) := by
      dsimp only [u]
      exact Polynomial.derivative_comp_one_sub_X U
    rw [hderivative]
    dsimp only [u, f]
    calc
      C γ * F.comp (1 - X) =
          (1 - X) * U.derivative.comp (1 - X) +
            C γ * U.comp (1 - X) := hcomp.symm
      _ = C γ * U.comp (1 - X) +
          -(1 - X) * (-U.derivative.comp (1 - X)) := by ring
  have htargetPos : HasPosLeadingCoeff (C γ * f) :=
    hasPosLeadingCoeff_C_mul hγ hfPos
  have hprecComp : Prec u (C γ * f) := by
    rw [hrec]
    apply prec_derivative_of_nonpos_of_pos_natDegree
    · exact huSplits
    · rw [huDegree]
      exact hm
    · rw [← hrec, Polynomial.natDegree_C_mul hγ.ne', hfDegree, huDegree]
    · rw [← hrec, Polynomial.natDegree_C_mul hγ.ne', hfDegree, huDegree]
      lia
    · rw [← hrec]
      exact htargetPos
    · exact huPos
    · intro x hx
      have hxU : U.IsRoot (1 - x) := by
        rw [Polynomial.IsRoot.def] at hx ⊢
        simpa only [u, eval_comp, eval_sub, eval_one, eval_X] using hx
      have hxPos := exceptionalEulerInverse_roots_pos
        m ε hm hγlower (1 - x) (by
          exact (mem_roots hUne).mpr hxU)
      simp only [eval_neg, eval_sub, eval_one, eval_X]
      linarith
  have hprecComp' : Prec u f := by
    have hscaled := hprecComp.C_mul_right (inv_ne_zero hγ.ne')
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hγ.ne', C_1, one_mul] at hscaled
    exact hscaled
  have hreflect := prec_comp_one_sub_X_of_sameDegree hprecComp'
    (by rw [huDegree, hfDegree])
  have hinvolution : (1 - X : ℝ[X]).comp (1 - X) = X := by
    simp
  dsimp only [u, f] at hreflect
  rw [comp_assoc, comp_assoc, hinvolution, comp_X, comp_X] at hreflect
  exact hreflect

private theorem orderedRoot_finite_eq_signedDiagonalRoot
    (m ε d : ℕ) (hm : 0 < m) (hd : d ≤ m - 1)
    (i : Fin (m - 1)) :
    orderedRoot (rPolynomial m ε d) (m - 1 + 1) i.castSucc =
      signedDiagonalRoot m ε d i := by
  have hSdata : IntervalRootData
      (signedTriangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε)
        d d) (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε d d hm hd le_rfl
    convert hdata using 1
    lia
  rw [RealRooted.orderedRoot, finite_roots_sort m ε d hm hd,
    signedDiagonalRoot, RealRooted.orderedRoot]
  have hi : i.val <
      ((signedTriangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε)
        d d).roots.sort (· ≤ ·)).length := by
    rw [hSdata.roots_sort_length]
    exact i.isLt
  simpa using List.getD_append
    ((signedTriangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε)
      d d).roots.sort (· ≤ ·)) [(1 : ℝ)] 0 i.val hi

private theorem shiftedJacobiMonicRoot_cast_degree
    {n m : ℕ} (h : n = m) (i : Fin n) (α β : ℝ) :
    shiftedJacobiMonicRoot n i α β =
      shiftedJacobiMonicRoot m (Fin.cast h i) α β := by
  subst m
  rfl

private theorem orderedRoot_exceptionalBasePolynomial_eq_monicRoot
    (m ε : ℕ) (i : Fin m) :
    orderedRoot (exceptionalBasePolynomial m ε) m i =
      shiftedJacobiMonicRoot m i ((ε : ℝ) - 1 / 2) 0 := by
  let α : ℝ := (ε : ℝ) - 1 / 2
  let scale : ℝ :=
    (Ring.choose ((m : ℝ) + ((ε : ℝ) - 1 / 2)) m)⁻¹
  have hα : -1 < α := by
    dsimp only [α]
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  have hchoose : 0 < Ring.choose ((m : ℝ) + α) m := by
    apply Polynomial.ring_choose_pos
    linarith
  have hroots : (exceptionalBasePolynomial m ε).roots =
      (shiftedJacobi m α 0).roots := by
    rw [exceptionalBasePolynomial_eq_C_mul_shiftedJacobi]
    exact Polynomial.roots_C_mul _ (inv_ne_zero hchoose.ne')
  rw [RealRooted.orderedRoot, hroots]
  exact orderedRoot_shiftedJacobi_eq_monicRoot m hα (by norm_num) i

private theorem jPolynomialRoot_eq_monicRoot
    (m ε : ℕ) (hm : 0 < m) (i : Fin (m - 1)) :
    jPolynomialRoot m ε i =
      shiftedJacobiMonicRoot (m - 1) i ((ε : ℝ) + 1) 1 := by
  let scale : ℝ :=
    Ring.choose (((m - 1 : ℕ) : ℝ) + ((ε : ℝ) + 1)) (m - 1)
  have hscale : 0 < scale := by
    apply Polynomial.ring_choose_pos
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  have heq := C_mul_jPolynomial_eq_shiftedJacobi m ε hm
  have hroots : (jPolynomial m ε).roots =
      (shiftedJacobi (m - 1) ((ε : ℝ) + 1) 1).roots := by
    have h := congrArg Polynomial.roots heq
    rw [Polynomial.roots_C_mul _ hscale.ne'] at h
    exact h
  rw [jPolynomialRoot, RealRooted.orderedRoot, hroots]
  exact orderedRoot_shiftedJacobi_eq_monicRoot
    (m - 1) (by
      have hε : 0 ≤ (ε : ℝ) := by positivity
      linarith) (by norm_num) i

private theorem exceptionalRoot_interlacing_jPolynomialRoot
    (m ε : ℕ) (hm : 0 < m) :
    (∀ i : Fin (m - 1),
      orderedRoot (rPolynomial m ε m) m (Fin.cast (by lia) i.castSucc) <
        jPolynomialRoot m ε i) ∧
    ∀ i : Fin (m - 1),
      jPolynomialRoot m ε i <
        orderedRoot (rPolynomial m ε m) m (Fin.cast (by lia) i.succ) := by
  have hRmDegree : (rPolynomial m ε m).natDegree = m := by
    rw [← exceptionalEulerInverse_upper_eq_rPolynomial]
    exact natDegree_exceptionalEulerInverse m ε (by positivity)
  have hRprevDegree :=
    (rPolynomial_rightClosedIntervalRootData m ε (m - 1) hm le_rfl).natDegree_eq
  have hleftBounds := Prec.orderedRoot_le
    (rPolynomial_exceptional_prec m ε hm) hRmDegree hRprevDegree
  let B : ℝ := (ε : ℝ) + 1 / 2 + m + 1 / 2
  have hB : 0 < B := by positivity
  have hBlower : (ε : ℝ) + 1 / 2 + m - 1 < B := by
    dsimp only [B]
    linarith
  have hbasePrecUpper : Prec (exceptionalBasePolynomial m ε)
      (rPolynomial m ε m) := by
    rw [← exceptionalEulerInverse_upper_eq_rPolynomial]
    apply exceptionalBasePolynomial_prec_exceptionalEulerInverse
      m ε hm hB hBlower
    exact (exceptionalEulerInverse_upper_prec_lower m ε hm).1.2
  have hbaseDegree : (exceptionalBasePolynomial m ε).natDegree = m := by
    let scale : ℝ :=
      (Ring.choose ((m : ℝ) + ((ε : ℝ) - 1 / 2)) m)⁻¹
    have hchoose : 0 <
        Ring.choose ((m : ℝ) + ((ε : ℝ) - 1 / 2)) m := by
      apply Polynomial.ring_choose_pos
      have hε : 0 ≤ (ε : ℝ) := by positivity
      linarith
    rw [exceptionalBasePolynomial_eq_C_mul_shiftedJacobi,
      Polynomial.natDegree_C_mul (inv_ne_zero hchoose.ne'),
      natDegree_shiftedJacobi m (by
        have hε : 0 ≤ (ε : ℝ) := by positivity
        linarith) (by norm_num)]
  have hrightBounds := Prec.orderedRoot_le
    hbasePrecUpper hbaseDegree hRmDegree
  have hbaseJ := shiftedJacobiMonicRoot_base_interlacing_jacobi
    (m - 1) (α := (ε : ℝ) - 1 / 2) (by
      have hε : 0 ≤ (ε : ℝ) := by positivity
      linarith)
  constructor
  · intro i
    have hweak := hleftBounds (Fin.cast (by lia) i.castSucc)
    rw [show orderedRoot (rPolynomial m ε (m - 1)) m
        (Fin.cast (by lia) i.castSucc) =
          signedDiagonalRoot m ε (m - 1) i by
      simpa [RealRooted.orderedRoot] using
        orderedRoot_finite_eq_signedDiagonalRoot
          m ε (m - 1) hm le_rfl i] at hweak
    exact hweak.trans_lt
      ((signedDiagonalRoot_terminal_interlacing_jPolynomialRoot m ε hm).1 i)
  · intro i
    have hmEq : m - 1 + 1 = m := by lia
    have hnodeBase :
        shiftedJacobiMonicRoot (m - 1) i
            ((ε : ℝ) - 1 / 2 + 3 / 2) 1 <
          shiftedJacobiMonicRoot m (Fin.cast hmEq i.succ)
            ((ε : ℝ) - 1 / 2) 0 := by
      rw [← shiftedJacobiMonicRoot_cast_degree hmEq i.succ]
      exact hbaseJ.2 i
    rw [show (ε : ℝ) - 1 / 2 + 3 / 2 = (ε : ℝ) + 1 by ring,
      ← jPolynomialRoot_eq_monicRoot m ε hm i,
      ← orderedRoot_exceptionalBasePolynomial_eq_monicRoot m ε
        (Fin.cast (by lia) i.succ)] at hnodeBase
    exact hnodeBase.trans_le
      (hrightBounds (Fin.cast (by lia) i.succ))

private theorem orderedRoot_isRoot_of_splits
    {p : ℝ[X]} {n : ℕ} (hpSplits : p.Splits)
    (hpDegree : p.natDegree = n) (i : Fin n) :
    p.IsRoot (orderedRoot p n i) := by
  have hlen : (p.roots.sort (· ≤ ·)).length = n := by
    rw [Multiset.length_sort, card_roots_of_splits hpSplits, hpDegree]
  have hi : i.val < (p.roots.sort (· ≤ ·)).length := by
    rw [hlen]
    exact i.isLt
  rw [RealRooted.orderedRoot, List.getD_eq_getElem _ _ hi]
  apply Polynomial.isRoot_of_mem_roots
  exact (Multiset.mem_sort _).mp (List.getElem_mem ..)

/-- At every indexed Jacobi node, the exceptional toric-contribution
polynomial has the positive derivative-oriented sign. -/
theorem rPolynomial_exceptional_eval_mul_jPolynomial_derivative_pos
    (m ε : ℕ) (hm : 0 < m) (i : Fin (m - 1)) :
    0 < (rPolynomial m ε m).eval (jPolynomialRoot m ε i) *
      (jPolynomial m ε).derivative.eval (jPolynomialRoot m ε i) := by
  cases m with
  | zero => simp at hm
  | succ n =>
      let R := rPolynomial (n + 1) ε (n + 1)
      let J := jPolynomial (n + 1) ε
      let s : Fin (n + 1) → ℝ := orderedRoot R (n + 1)
      let r : Fin n → ℝ := jPolynomialRoot (n + 1) ε
      have hRprec := rPolynomial_exceptional_prec (n + 1) ε (by lia)
      have hRNe : R ≠ 0 := by simpa only [R] using hRprec.1.1
      have hRSplits : R.Splits := by simpa only [R] using hRprec.1.2
      have hRDegree : R.natDegree = n + 1 := by
        dsimp only [R]
        rw [← exceptionalEulerInverse_upper_eq_rPolynomial]
        exact natDegree_exceptionalEulerInverse (n + 1) ε (by positivity)
      have hJData : IntervalRootData J n := by
        have hdata := jPolynomial_signedTriangleFamily_intervalRootData
          (n + 1) ε 0 0 (by lia) (by lia) le_rfl
        simpa [J, signedTriangleFamily] using hdata
      have hJNe : J ≠ 0 := by
        intro hzero
        apply hJData.eval_zero_ne
        simp [hzero]
      have hinter := exceptionalRoot_interlacing_jPolynomialRoot
        (n + 1) ε (by lia)
      have hsLeft : ∀ j : Fin n, s j.castSucc < r j := by
        intro j
        exact hinter.1 j
      have hsRight : ∀ j : Fin n, r j < s j.succ := by
        intro j
        exact hinter.2 j
      have hsMono : StrictMono s := by
        rw [Fin.strictMono_iff_lt_succ]
        intro j
        exact (hsLeft j).trans (hsRight j)
      have hrMono : StrictMono r := hJData.strictMono_orderedRoot
      have hsFirstMono : StrictMono (fun j : Fin n => s j.castSucc) :=
        hsMono.comp Fin.strictMono_castSucc
      have hsCross : ∀ (j k : Fin n), j < k → r j < s k.castSucc := by
        intro j k hjk
        exact (hsRight j).trans_le (hsMono.monotone (by
          change j.val + 1 ≤ k.val
          lia))
      have hprodFirst := StrictMono.prod_sub_mul_prod_sub_pos_of_interlacing
        (fun j : Fin n => s j.castSucc) r hrMono hsLeft hsCross i
      have hlast : r i < s (Fin.last n) := by
        exact (hsRight i).trans_le (hsMono.monotone (Fin.le_last i.succ))
      have hprodFull :
          (∏ j : Fin (n + 1), (r i - s j)) *
              (∏ j ∈ Finset.univ.erase i, (r i - r j)) < 0 := by
        rw [Fin.prod_univ_castSucc]
        have hlastNeg : r i - s (Fin.last n) < 0 := sub_neg.mpr hlast
        calc
          (∏ j : Fin n, (r i - s j.castSucc)) *
                (r i - s (Fin.last n)) *
                (∏ j ∈ Finset.univ.erase i, (r i - r j)) =
              ((∏ j : Fin n, (r i - s j.castSucc)) *
                (∏ j ∈ Finset.univ.erase i, (r i - r j))) *
                (r i - s (Fin.last n)) := by ring
          _ < 0 := mul_neg_of_pos_of_neg hprodFirst hlastNeg
      have hReq : R = C R.leadingCoeff *
          ∏ j : Fin (n + 1), (X - C (s j)) := by
        apply Polynomial.splits_eq_C_mul_prod hRNe hRDegree s
        · intro j
          exact orderedRoot_isRoot_of_splits hRSplits hRDegree j
        · exact hsMono.injective
      have hJeq : J = C J.leadingCoeff *
          ∏ j : Fin n, (X - C (r j)) := by
        apply Polynomial.splits_eq_C_mul_prod hJNe hJData.natDegree_eq r
        · exact hJData.orderedRoot_isRoot
        · exact hrMono.injective
      have hRLead : 0 < (-1 : ℝ) ^ (n + 1) * R.leadingCoeff := by
        dsimp only [R]
        rw [← exceptionalEulerInverse_upper_eq_rPolynomial]
        exact negOnePow_mul_exceptionalEulerInverse_leadingCoeff_pos
          (n + 1) ε (by positivity)
      have hJZero : 0 < J.eval 0 := by
        dsimp only [J]
        rw [jPolynomial_eval_zero (n + 1) ε (by lia)]
        norm_num
      have hJLeadScaled := hJData.hasPosLeadingCoeff_negOnePow_mul hJZero
      have hJLead : 0 < (-1 : ℝ) ^ n * J.leadingCoeff := by
        rw [HasPosLeadingCoeff,
          Polynomial.leadingCoeff_C_mul_of_isUnit
            (isUnit_iff_ne_zero.mpr (pow_ne_zero n (by norm_num)))] at hJLeadScaled
        exact hJLeadScaled
      have hleadProduct : R.leadingCoeff * J.leadingCoeff < 0 := by
        have hsignSq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
          rw [← pow_two, ← pow_mul]
          simp
        rw [pow_succ] at hRLead
        nlinarith [mul_pos hRLead hJLead]
      have hevalR : R.eval (r i) = R.leadingCoeff *
          ∏ j : Fin (n + 1), (r i - s j) := by
        calc
          R.eval (r i) =
              (C R.leadingCoeff *
                ∏ j : Fin (n + 1), (X - C (s j))).eval (r i) :=
            congrArg (Polynomial.eval (r i)) hReq
          _ = R.leadingCoeff * ∏ j : Fin (n + 1), (r i - s j) := by
            simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
      have hevalJ : J.derivative.eval (r i) = J.leadingCoeff *
          ∏ j ∈ Finset.univ.erase i, (r i - r j) := by
        calc
          J.derivative.eval (r i) =
              (C J.leadingCoeff *
                ∏ j : Fin n, (X - C (r j))).derivative.eval (r i) :=
            congrArg (fun p : ℝ[X] => p.derivative.eval (r i)) hJeq
          _ = J.leadingCoeff *
              ∏ j ∈ Finset.univ.erase i, (r i - r j) :=
            Polynomial.eval_derivative_C_mul_prod_X_sub_C_univ_at_root
              J.leadingCoeff r i
      change 0 < R.eval (r i) * J.derivative.eval (r i)
      rw [hevalR, hevalJ]
      nlinarith

/-- The exceptional toric-contribution polynomial has the positive
derivative-oriented sign at every root of the Jacobi interlacer. -/
theorem rPolynomial_exceptional_eval_mul_jPolynomial_derivative_pos_of_isRoot
    (m ε : ℕ) (hm : 0 < m) {x : ℝ}
    (hx : (jPolynomial m ε).IsRoot x) :
    0 < (rPolynomial m ε m).eval x *
      (jPolynomial m ε).derivative.eval x := by
  have hJData : IntervalRootData (jPolynomial m ε) (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε 0 0 hm (by lia) le_rfl
    simpa [signedTriangleFamily] using hdata
  have hJNe : jPolynomial m ε ≠ 0 := by
    intro hzero
    apply hJData.eval_zero_ne
    simp [hzero]
  obtain ⟨i, hi⟩ := exists_index_eq_of_mem_roots
    (jPolynomialRoot m ε) hJData.strictMono_orderedRoot
    (fun i => hJData.orderedRoot_isRoot i) hJNe hJData.natDegree_eq.le
    x ((mem_roots hJNe).mpr hx)
  rw [← hi]
  exact rPolynomial_exceptional_eval_mul_jPolynomial_derivative_pos m ε hm i

/-- Every positive toric-contribution offset, including the exceptional
offset `d = m`, has the positive derivative-oriented sign at each Jacobi
node. -/
theorem rPolynomial_allOffsets_eval_mul_jPolynomial_derivative_pos_of_isRoot
    (m ε d : ℕ) (hm : 0 < m) (hdPos : 0 < d) (hd : d ≤ m)
    {x : ℝ} (hx : (jPolynomial m ε).IsRoot x) :
    0 < (rPolynomial m ε d).eval x *
      (jPolynomial m ε).derivative.eval x := by
  by_cases hfinite : d ≤ m - 1
  · exact rPolynomial_eval_mul_jPolynomial_derivative_pos_of_isRoot
      m ε d hm hdPos hfinite hx
  · have hdEq : d = m := by lia
    subst d
    exact rPolynomial_exceptional_eval_mul_jPolynomial_derivative_pos_of_isRoot
      m ε hm hx

private theorem orderedRoot_finite_last_eq_one
    (m ε d : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) :
    orderedRoot (rPolynomial m ε d) (m - 1 + 1) (Fin.last (m - 1)) = 1 := by
  let S := signedTriangleFamily ((ε : ℝ) + 1 / 2)
    (jPolynomial m ε) d d
  have hSData : IntervalRootData S (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε d d hm hd le_rfl
    dsimp only [S]
    convert hdata using 1
    lia
  rw [RealRooted.orderedRoot, finite_roots_sort m ε d hm hd]
  have hlength :
      ((signedTriangleFamily ((ε : ℝ) + 1 / 2) (jPolynomial m ε)
        d d).roots.sort (· ≤ ·)).length = m - 1 := by
    simpa only [S] using hSData.roots_sort_length
  rw [List.getD_append_right]
  · rw [hlength]
    simp
  · rw [hlength]
    change m - 1 ≤ m - 1
    exact le_rfl

private theorem finiteRoot_interlacing_jPolynomialRoot
    (m ε d : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) :
    (∀ i : Fin (m - 1),
      orderedRoot (rPolynomial m ε d) (m - 1 + 1) i.castSucc ≤
        jPolynomialRoot m ε i) ∧
    ∀ i : Fin (m - 1),
      jPolynomialRoot m ε i ≤
        orderedRoot (rPolynomial m ε d) (m - 1 + 1) i.succ := by
  have hJData : IntervalRootData (jPolynomial m ε) (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε 0 0 hm (by lia) le_rfl
    simpa [signedTriangleFamily] using hdata
  constructor
  · intro i
    rw [orderedRoot_finite_eq_signedDiagonalRoot m ε d hm hd i]
    by_cases hdZero : d = 0
    · subst d
      simp [signedDiagonalRoot, jPolynomialRoot, signedTriangleFamily]
    · exact (signedDiagonalRoot_interlacing_jPolynomialRoot
        m ε d hm (Nat.pos_of_ne_zero hdZero) hd).1 i |>.le
  · intro i
    by_cases hi : i.val + 1 < m - 1
    · let k : Fin (m - 1) := ⟨i.val + 1, hi⟩
      have hright : jPolynomialRoot m ε i ≤ signedDiagonalRoot m ε d k := by
        by_cases hdZero : d = 0
        · subst d
          rw [show signedDiagonalRoot m ε 0 k = jPolynomialRoot m ε k by
            simp [signedDiagonalRoot, jPolynomialRoot, signedTriangleFamily]]
          have hik : i < k := by
            change i.val < k.val
            simp [k]
          exact (hJData.strictMono_orderedRoot hik).le
        · exact (signedDiagonalRoot_interlacing_jPolynomialRoot
            m ε d hm (Nat.pos_of_ne_zero hdZero) hd).2 i k
              (by change i.val < k.val; simp [k]) |>.le
      rw [← orderedRoot_finite_eq_signedDiagonalRoot m ε d hm hd k] at hright
      have hik : i.succ = k.castSucc := by
        apply Fin.ext
        simp [k]
      simpa [hik] using hright
    · have hiLast : i.val = m - 2 := by lia
      have hroot := hJData.roots_mem_Ioo
        (jPolynomialRoot m ε i)
        ((mem_roots (by
          intro hzero
          apply hJData.eval_zero_ne
          simp [hzero])).mpr (hJData.orderedRoot_isRoot i))
      rw [show i.succ = Fin.last (m - 1) by
        apply Fin.ext
        simp [hiLast]
        lia, orderedRoot_finite_last_eq_one m ε d hm hd]
      exact hroot.2.le

private theorem rPolynomial_finite_prec_of_lt
    (m ε d e : ℕ) (hm : 0 < m) (hde : d < e) (he : e ≤ m - 1) :
    Prec (rPolynomial m ε e) (rPolynomial m ε d) := by
  have hd : d ≤ m - 1 := by lia
  have hmTwo : 2 ≤ m := by lia
  have hpData := rPolynomial_rightClosedIntervalRootData m ε e hm he
  have hqData := rPolynomial_rightClosedIntervalRootData m ε d hm hd
  apply (prec_iff_orderedRoot_bounds
    (fun hzero => hpData.eval_zero_ne (by simp [hzero])) hpData.splits
    (fun hzero => hqData.eval_zero_ne (by simp [hzero])) hqData.splits
    hpData.natDegree_eq hqData.natDegree_eq).mpr
  constructor
  · intro i
    by_cases hiLast : i.val < m - 1
    · let k : Fin (m - 1) := ⟨i.val, hiLast⟩
      have hpEq : orderedRoot (rPolynomial m ε e) m i =
          signedDiagonalRoot m ε e k := by
        simpa only [RealRooted.orderedRoot, k, Fin.val_castSucc] using
          orderedRoot_finite_eq_signedDiagonalRoot m ε e hm he k
      have hqEq : orderedRoot (rPolynomial m ε d) m i =
          signedDiagonalRoot m ε d k := by
        simpa only [RealRooted.orderedRoot, k, Fin.val_castSucc] using
          orderedRoot_finite_eq_signedDiagonalRoot m ε d hm hd k
      rw [hpEq, hqEq]
      exact signedDiagonalRoot_le_of_le m ε d e hmTwo hde.le he k
    · have hiEq : i.val = m - 1 := by lia
      have hpEq : orderedRoot (rPolynomial m ε e) m i = 1 := by
        simpa only [RealRooted.orderedRoot, hiEq, Fin.val_last] using
          orderedRoot_finite_last_eq_one m ε e hm he
      have hqEq : orderedRoot (rPolynomial m ε d) m i = 1 := by
        simpa only [RealRooted.orderedRoot, hiEq, Fin.val_last] using
          orderedRoot_finite_last_eq_one m ε d hm hd
      rw [hpEq, hqEq]
  · intro i hi
    let k : Fin (m - 1) := ⟨i.val, by lia⟩
    have hqJ := (finiteRoot_interlacing_jPolynomialRoot m ε d hm hd).1 k
    have hJp := (finiteRoot_interlacing_jPolynomialRoot m ε e hm he).2 k
    simpa only [RealRooted.orderedRoot, k, Fin.val_castSucc, Fin.val_succ] using
      hqJ.trans hJp

/-- Larger reverse offsets precede smaller reverse offsets in proper position.
This is the fixed-row orientation statement behind Xiao's Conjecture 4.2. -/
theorem rPolynomial_prec_rPolynomial_of_lt
    (m ε d e : ℕ) (hm : 0 < m) (hde : d < e) (he : e ≤ m) :
    Prec (rPolynomial m ε e) (rPolynomial m ε d) := by
  by_cases heFinite : e ≤ m - 1
  · exact rPolynomial_finite_prec_of_lt m ε d e hm hde heFinite
  · have heEq : e = m := by lia
    subst e
    have hd : d ≤ m - 1 := by lia
    have hqData := rPolynomial_rightClosedIntervalRootData m ε d hm hd
    have hprevData :=
      rPolynomial_rightClosedIntervalRootData m ε (m - 1) hm le_rfl
    have hpPrecPrev := rPolynomial_exceptional_prec m ε hm
    have hpDegree : (rPolynomial m ε m).natDegree = m := by
      rw [← exceptionalEulerInverse_upper_eq_rPolynomial]
      exact natDegree_exceptionalEulerInverse m ε (by positivity)
    have hpPrevBounds := Prec.orderedRoot_le
      hpPrecPrev hpDegree hprevData.natDegree_eq
    apply (prec_iff_orderedRoot_bounds
      hpPrecPrev.1.1 hpPrecPrev.1.2
      (fun hzero => hqData.eval_zero_ne (by simp [hzero])) hqData.splits
      hpDegree hqData.natDegree_eq).mpr
    constructor
    · intro i
      have hpLePrev := hpPrevBounds i
      by_cases hiLast : i.val < m - 1
      · let k : Fin (m - 1) := ⟨i.val, hiLast⟩
        have hprevEq : orderedRoot (rPolynomial m ε (m - 1)) m i =
            signedDiagonalRoot m ε (m - 1) k := by
          simpa only [RealRooted.orderedRoot, k, Fin.val_castSucc] using
            orderedRoot_finite_eq_signedDiagonalRoot
              m ε (m - 1) hm le_rfl k
        have hqEq : orderedRoot (rPolynomial m ε d) m i =
            signedDiagonalRoot m ε d k := by
          simpa only [RealRooted.orderedRoot, k, Fin.val_castSucc] using
            orderedRoot_finite_eq_signedDiagonalRoot m ε d hm hd k
        rw [hprevEq] at hpLePrev
        rw [hqEq]
        exact hpLePrev.trans (signedDiagonalRoot_le_of_le
          m ε d (m - 1) (by lia) hd le_rfl k)
      · have hiEq : i.val = m - 1 := by lia
        have hprevEq : orderedRoot (rPolynomial m ε (m - 1)) m i = 1 := by
          simpa only [RealRooted.orderedRoot, hiEq, Fin.val_last] using
            orderedRoot_finite_last_eq_one m ε (m - 1) hm le_rfl
        have hqEq : orderedRoot (rPolynomial m ε d) m i = 1 := by
          simpa only [RealRooted.orderedRoot, hiEq, Fin.val_last] using
            orderedRoot_finite_last_eq_one m ε d hm hd
        rw [hprevEq] at hpLePrev
        rw [hqEq]
        exact hpLePrev
    · intro i hi
      let k : Fin (m - 1) := ⟨i.val, by lia⟩
      have hqJ := (finiteRoot_interlacing_jPolynomialRoot m ε d hm hd).1 k
      have hJp := (exceptionalRoot_interlacing_jPolynomialRoot m ε hm).2 k
      exact le_trans (by
        simpa only [RealRooted.orderedRoot, k, Fin.val_castSucc] using hqJ) (by
        simpa only [RealRooted.orderedRoot, k, Fin.val_cast, Fin.val_succ] using
          hJp.le)

private theorem interlaces_of_intervalRootData_orderedRoot_bounds
    {g f : ℝ[X]} {n : ℕ}
    (hg : IntervalRootData g n) (hfNe : f ≠ 0) (hfSplits : f.Splits)
    (hfDegree : f.natDegree = n + 1)
    (hleft : ∀ i : Fin n,
      orderedRoot f (n + 1) i.castSucc ≤ orderedRoot g n i)
    (hright : ∀ i : Fin n,
      orderedRoot g n i ≤ orderedRoot f (n + 1) i.succ) :
    Interlaces g f := by
  let rs := f.roots.sort (· ≤ ·)
  let ss := g.roots.sort (· ≤ ·)
  have hgNe : g ≠ 0 := by
    intro hzero
    apply hg.eval_zero_ne
    simp [hzero]
  have hrsLength : rs.length = n + 1 := by
    rw [show rs = f.roots.sort (· ≤ ·) by rfl, Multiset.length_sort,
      card_roots_of_splits hfSplits, hfDegree]
  have hssLength : ss.length = n := by
    rw [show ss = g.roots.sort (· ≤ ·) by rfl, Multiset.length_sort,
      card_roots_of_splits hg.splits, hg.natDegree_eq]
  refine ⟨⟨hfNe, hfSplits⟩, ⟨hgNe, hg.splits⟩, ?_, rs, ss,
    by simp [rs], by simp [ss], by simp [rs], by simp [ss], ?_⟩
  · rw [hg.natDegree_eq, hfDegree]
  · apply listInterlaces_of_getD_bounds ss rs (by lia)
    · intro k hk
      let i : Fin n := ⟨k, by lia⟩
      simpa only [RealRooted.orderedRoot, rs, ss, i, Fin.val_castSucc] using hleft i
    · intro k hk
      let i : Fin n := ⟨k, by lia⟩
      simpa only [RealRooted.orderedRoot, rs, ss, i, Fin.val_succ] using hright i

/-- The terminating Jacobi polynomial interlaces every normalized
toric-contribution polynomial, including both boundary offsets. -/
theorem jPolynomial_interlaces_rPolynomial
    (m ε d : ℕ) (hm : 0 < m) (hd : d ≤ m) :
    Interlaces (jPolynomial m ε) (rPolynomial m ε d) := by
  have hJData : IntervalRootData (jPolynomial m ε) (m - 1) := by
    have hdata := jPolynomial_signedTriangleFamily_intervalRootData
      m ε 0 0 hm (by lia) le_rfl
    simpa [signedTriangleFamily] using hdata
  have hmSucc : m - 1 + 1 = m := Nat.sub_add_cancel (by lia)
  by_cases hfinite : d ≤ m - 1
  · have hRData := rPolynomial_rightClosedIntervalRootData
      m ε d hm hfinite
    obtain ⟨hleft, hright⟩ :=
      finiteRoot_interlacing_jPolynomialRoot m ε d hm hfinite
    apply interlaces_of_intervalRootData_orderedRoot_bounds hJData
      (fun hzero => hRData.eval_zero_ne (by simp [hzero])) hRData.splits
      (hRData.natDegree_eq.trans hmSucc.symm)
    · simpa only [jPolynomialRoot] using hleft
    · simpa only [jPolynomialRoot] using hright
  · have hdEq : d = m := by lia
    subst d
    have hRPrec := rPolynomial_exceptional_prec m ε hm
    have hRDegree : (rPolynomial m ε m).natDegree = m := by
      rw [← exceptionalEulerInverse_upper_eq_rPolynomial]
      exact natDegree_exceptionalEulerInverse m ε (by positivity)
    obtain ⟨hleft, hright⟩ :=
      exceptionalRoot_interlacing_jPolynomialRoot m ε hm
    apply interlaces_of_intervalRootData_orderedRoot_bounds hJData
      hRPrec.1.1 hRPrec.1.2 (hRDegree.trans hmSucc.symm)
    · intro i
      simpa only [jPolynomialRoot, RealRooted.orderedRoot, Fin.val_cast] using
        (hleft i).le
    · intro i
      simpa only [jPolynomialRoot, RealRooted.orderedRoot, Fin.val_cast] using
        (hright i).le

/-- The top coefficient of every normalized toric-contribution polynomial
has the parity sign predicted by its terminating hypergeometric factor. -/
theorem rPolynomial_top_signed_coeff_pos (m ε d : ℕ) :
    0 < (-1 : ℝ) ^ m * (rPolynomial m ε d).coeff m := by
  rw [coeff_rPolynomial, if_pos le_rfl, rCoeff,
    exceptional_realRisingFactorial_neg_nat_eq_factorial_div m m le_rfl]
  have hleft : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← pow_add, show m + m = 2 * m by lia, pow_mul]
    norm_num
  rw [show (-1 : ℝ) ^ m *
      (((-1 : ℝ) ^ m * m.factorial / (m - m).factorial) *
          realRisingFactorial ((m : ℝ) + 1 + ε) m *
          realRisingFactorial ((ε : ℝ) + 1 / 2 + d) m /
        (realRisingFactorial ((ε : ℝ) + 1 / 2) m *
          realRisingFactorial ((ε : ℝ) + 1 / 2 + d + 3 / 2) m *
          m.factorial)) =
      ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) *
        ((m.factorial : ℝ) / (m - m).factorial *
          realRisingFactorial ((m : ℝ) + 1 + ε) m *
          realRisingFactorial ((ε : ℝ) + 1 / 2 + d) m /
        (realRisingFactorial ((ε : ℝ) + 1 / 2) m *
          realRisingFactorial ((ε : ℝ) + 1 / 2 + d + 3 / 2) m *
          m.factorial)) by ring,
    hleft, one_mul]
  have hA : 0 < realRisingFactorial ((m : ℝ) + 1 + ε) m := by
    apply realRisingFactorial_pos
    positivity
  have hB : 0 < realRisingFactorial ((ε : ℝ) + 1 / 2 + d) m := by
    apply realRisingFactorial_pos
    positivity
  have hC : 0 < realRisingFactorial ((ε : ℝ) + 1 / 2) m := by
    apply realRisingFactorial_pos
    positivity
  have hD : 0 <
      realRisingFactorial ((ε : ℝ) + 1 / 2 + d + 3 / 2) m := by
    apply realRisingFactorial_pos
    positivity
  have hF : 0 < (m.factorial : ℝ) := by positivity
  norm_num only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one]
  positivity

/-- Every normalized toric-contribution polynomial has its full terminating
degree. -/
theorem rPolynomial_natDegree (m ε d : ℕ) :
    (rPolynomial m ε d).natDegree = m := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_rPolynomial_le m ε d)
  intro hzero
  have hpositive := rPolynomial_top_signed_coeff_pos m ε d
  rw [hzero, mul_zero] at hpositive
  exact lt_irrefl 0 hpositive

/-- Multiplication by the parity sign gives every normalized
toric-contribution polynomial positive leading coefficient. -/
theorem negOnePow_mul_rPolynomial_hasPosLeadingCoeff (m ε d : ℕ) :
    HasPosLeadingCoeff (C ((-1 : ℝ) ^ m) * rPolynomial m ε d) := by
  rw [HasPosLeadingCoeff, Polynomial.leadingCoeff_C_mul_of_isUnit
    (isUnit_iff_ne_zero.mpr (pow_ne_zero m (by norm_num))), leadingCoeff,
    rPolynomial_natDegree]
  exact rPolynomial_top_signed_coeff_pos m ε d

end ToricContribution
end ParkingFunctions
end RealRooted
