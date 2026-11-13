module

public import RealRooted.Hermite.Poulain
public import RealRooted.HermiteBiehler.StablePencil
import RealRooted.BorceaBranden.FiniteOrderWeylPreserver
import RealRooted.Mathlib.Algebra.MvPolynomial.PDeriv.ToMvPolynomial
import Mathlib.Tactic

/-!
# Interlacing differential symbols

For a splitting real polynomial `t`, symbol-side proper position reverses:
stability of `q(z) + w p(z)` implies stability, allowing the zero pair, of
`q(D)t - w p(D)t`, equivalently `p(D)t + w q(D)t`.
We use the finite-order Weyl-symbol theorem with the pencil parameter as a
spectator variable. No coefficient-sign hypotheses enter this theorem.

See https://github.com/PerAlexandersson/RealRooted/issues/2549.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted.HermitePoulain

/-- Conjugation turns the stable symbol pencil into the signed Weyl symbol. -/
private theorem signed_symbol_ne_zero {p q : ℝ[X]}
    (h : IsUpperHalfPlaneStablePencil q p)
    {u w : ℂ} (hu : 0 < u.im) (hw : 0 < w.im) :
    (complexify q).eval (-u) - w * (complexify p).eval (-u) ≠ 0 := by
  intro hzero
  have hs := h (-(starRingEnd ℂ u)) (-(starRingEnd ℂ w))
    (by simpa using hu) (by simpa using hw)
  apply hs
  have hc : (starRingEnd ℂ)
      ((complexify q).eval (-u) - w * (complexify p).eval (-u)) = 0 := by
    rw [hzero, map_zero]
  rw [map_sub, map_mul, ← eval_complexify_conj, ← eval_complexify_conj, map_neg] at hc
  simpa only [sub_eq_add_neg, neg_mul] using hc

/-- Transport the existing iterated partial derivative to a univariate input. -/
private theorem iteratedPDerivAt_complexify (j : ℕ) (t : ℝ[X]) :
    iteratedPDerivAt (0 : Fin 2) j ((complexify t).toMvPolynomial 0) =
      (complexify ((derivative^[j]) t)).toMvPolynomial 0 := by
  rw [complexify_iterate_derivative]
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iteratedPDerivAt, ih, MvPolynomial.pderiv_toMvPolynomial,
      Function.iterate_succ_apply']

/-- The Weyl operator with pencil coefficients produces the image pencil. -/
private theorem weylOperator_eq_bivariatePencil (p q t : ℝ[X])
    (m : ℕ) (hp : p.natDegree < m + 1) (hq : q.natDegree < m + 1) :
    BorceaBranden.finiteOrderWeylOperator (0 : Fin 2) m
      (fun j => MvPolynomial.C (q.coeff j : ℂ) -
        MvPolynomial.X 1 * MvPolynomial.C (p.coeff j : ℂ))
      ((complexify t).toMvPolynomial 0) =
      bivariatePencil (applyAsDifferentialOperator q t)
        (-applyAsDifferentialOperator p t) := by
  rw [BorceaBranden.finiteOrderWeylOperator]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, iteratedPDerivAt_complexify]
  change (∑ j : Fin (m + 1),
      (MvPolynomial.C (q.coeff j : ℂ) -
        MvPolynomial.X 1 * MvPolynomial.C (p.coeff j : ℂ)) *
        (complexify ((derivative^[j.val]) t)).toMvPolynomial 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    (MvPolynomial.C (q.coeff j : ℂ) -
      MvPolynomial.X 1 * MvPolynomial.C (p.coeff j : ℂ)) *
      (complexify ((derivative^[j]) t)).toMvPolynomial (0 : Fin 2)) (m + 1)]
  rw [bivariatePencil, applyAsDifferentialOperator_eq_sum_range hq,
    applyAsDifferentialOperator_eq_sum_range hp]
  change _ = (complexify (∑ j ∈ Finset.range (m + 1),
      C (q.coeff j) * (derivative^[j]) t)).toMvPolynomial 0 +
    MvPolynomial.X 1 * (complexify (-∑ j ∈ Finset.range (m + 1),
      C (p.coeff j) * (derivative^[j]) t)).toMvPolynomial 0
  simp only [complexify, Polynomial.map_sum, Polynomial.map_neg, Polynomial.map_mul,
    Polynomial.map_C, map_sum, map_neg, map_mul, Polynomial.toMvPolynomial_C,
    Complex.ofRealHom_eq_coe]
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc]
  rw [← Finset.mul_sum]
  simp only [sub_eq_add_neg, mul_neg]

/-- **Symbol-side Hermite–Poulain theorem.** A stable pencil `q + w p`
gives the reversed stable image pencil `p(D)t + w q(D)t`, or both images
vanish. The symbols have arbitrary real coefficients, and `t` may be zero. -/
theorem eq_zero_pair_or_stablePencil_applyAsDifferentialOperator
    {p q t : ℝ[X]} (h : IsUpperHalfPlaneStablePencil q p) (ht : t.Splits) :
    (applyAsDifferentialOperator p t = 0 ∧ applyAsDifferentialOperator q t = 0) ∨
      IsUpperHalfPlaneStablePencil (applyAsDifferentialOperator p t)
        (applyAsDifferentialOperator q t) := by
  by_cases ht0 : t = 0
  · simp [ht0]
  let m : ℕ := max p.natDegree q.natDegree
  have hp : p.natDegree < m + 1 := by dsimp [m]; lia
  have hq : q.natDegree < m + 1 := by dsimp [m]; lia
  let a : Fin (m + 1) → MvPolynomial (Fin 2) ℂ := fun j =>
    MvPolynomial.C (q.coeff j : ℂ) -
      MvPolynomial.X 1 * MvPolynomial.C (p.coeff j : ℂ)
  have heval (f : ℝ[X]) (hf : f.natDegree < m + 1) (u : ℂ) :
      ∑ j : Fin (m + 1), (f.coeff j : ℂ) * (-u) ^ j.val =
        (complexify f).eval (-u) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun j => (f.coeff j : ℂ) * (-u) ^ j) (m + 1)]
    simpa [complexify, eval_map] using
      (eval₂_eq_sum_range' Complex.ofRealHom hf (-u)).symm
  have hW : MvUpperHalfPlaneStable (BorceaBranden.signedWeylSymbol m a) := by
    intro z hz
    have hs := signed_symbol_ne_zero h (hz none) (hz (some 1))
    convert hs using 1
    simp only [BorceaBranden.signedWeylSymbol, map_sum, MvPolynomial.eval_mul,
      MvPolynomial.eval_rename, MvPolynomial.eval_C, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, a, MvPolynomial.eval_sub, Function.comp_apply]
    simp only [← mul_pow, ← neg_eq_neg_one_mul, sub_mul,
      Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [heval q hq, heval p hp]
  have htStable : MvUpperHalfPlaneStable ((complexify t).toMvPolynomial (0 : Fin 2)) := by
    intro z hz
    rw [MvPolynomial.eval_toMvPolynomial]
    exact RealRooted.Polynomial.Splits.isUpperHalfPlaneStable_complexify ht ht0 (z 0) (hz 0)
  have hout := MvUpperHalfPlaneStable.finiteOrderWeylOperator 0 m a hW htStable
  rw [show a = _ from rfl, weylOperator_eq_bivariatePencil p q t m hp hq] at hout
  rcases hout.eq_zero_pair_or_stablePencil with hzero | hstable
  · exact Or.inl ⟨neg_eq_zero.mp hzero.2, hzero.1⟩
  · right
    simpa using hstable.swap_neg.neg_neg

/-- A nonzero constant term in the symbol preserves the input degree. -/
theorem natDegree_applyAsDifferentialOperator_of_coeff_zero_ne_zero
    {f t : ℝ[X]} (hf : f.coeff 0 ≠ 0) (ht : t ≠ 0) :
    (applyAsDifferentialOperator f t).natDegree = t.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_applyAsDifferentialOperator_le f t
  · rw [coeff_applyAsDifferentialOperator_natDegree, coeff_natDegree]
    exact mul_ne_zero hf (leadingCoeff_ne_zero.mpr ht)

/-- The leading coefficient of a degree-preserving differential image. -/
theorem leadingCoeff_applyAsDifferentialOperator
    {f t : ℝ[X]} (hf : f.coeff 0 ≠ 0) (ht : t ≠ 0) :
    (applyAsDifferentialOperator f t).leadingCoeff = f.coeff 0 * t.leadingCoeff := by
  rw [leadingCoeff, natDegree_applyAsDifferentialOperator_of_coeff_zero_ne_zero hf ht,
    coeff_applyAsDifferentialOperator_natDegree, coeff_natDegree]

/-- The stable-pencil converse also covers pairs of nonzero constants. -/
private theorem strictInterl_of_stablePencil_of_sameDegree {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : IsUpperHalfPlaneStablePencil f g) (hd : f.natDegree = g.natDegree) :
    StrictInterl g f := by
  by_cases hd0 : f.natDegree = 0
  · have hg0 : g.natDegree = 0 := hd.symm.trans hd0
    have hfc : f.coeff 0 ≠ 0 := by simpa [HasPosLeadingCoeff, leadingCoeff, hd0] using hf.ne'
    have hgc : g.coeff 0 ≠ 0 := by simpa [HasPosLeadingCoeff, leadingCoeff, hg0] using hg.ne'
    rw [eq_C_of_natDegree_eq_zero hd0, eq_C_of_natDegree_eq_zero hg0]
    simpa using ((StrictInterl.refl (one_ne_zero : (1 : ℝ[X]) ≠ 0)
      (by simp)).C_mul_left hgc).C_mul_right hfc
  · exact (isUpperHalfPlaneStablePencil_iff_strictInterl hf hg hd0).mp h

/-- Positive constant terms orient the symbol-side images as `q(D)t ≪ p(D)t`.
Only positive leading and constant coefficients of the symbols are needed;
the nonzero splitting input has arbitrary real coefficients. Both images
have the input degree, including degree zero. -/
theorem strictInterl_applyAsDifferentialOperator_of_coeff_zero_pos
    {p q t : ℝ[X]} (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (hpq : StrictInterl p q) (hp0 : 0 < p.coeff 0) (hq0 : 0 < q.coeff 0)
    (ht : t ≠ 0 ∧ t.Splits) :
    StrictInterl (applyAsDifferentialOperator q t) (applyAsDifferentialOperator p t) ∧
      (applyAsDifferentialOperator p t).natDegree = t.natDegree ∧
      (applyAsDifferentialOperator q t).natDegree = t.natDegree := by
  have hpdeg := natDegree_applyAsDifferentialOperator_of_coeff_zero_ne_zero hp0.ne' ht.1
  have hqdeg := natDegree_applyAsDifferentialOperator_of_coeff_zero_ne_zero hq0.ne' ht.1
  have hplc := leadingCoeff_applyAsDifferentialOperator hp0.ne' ht.1
  have hqlc := leadingCoeff_applyAsDifferentialOperator hq0.ne' ht.1
  have hlc : t.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ht.1
  have hpne : applyAsDifferentialOperator p t ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    rw [hplc]
    exact mul_ne_zero hp0.ne' hlc
  have hstable : IsUpperHalfPlaneStablePencil (applyAsDifferentialOperator p t)
      (applyAsDifferentialOperator q t) := by
    rcases eq_zero_pair_or_stablePencil_applyAsDifferentialOperator
      (isUpperHalfPlaneStablePencil_of_strictInterl hq hp hpq) ht.2 with hz | hs
    · exact (hpne hz.1).elim
    · exact hs
  refine ⟨?_, hpdeg, hqdeg⟩
  rcases lt_or_gt_of_ne hlc with hneg | hpos
  · have hpneg : HasPosLeadingCoeff (-applyAsDifferentialOperator p t) := by
      simp only [HasPosLeadingCoeff, leadingCoeff_neg, hplc]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hp0 hneg)
    have hqneg : HasPosLeadingCoeff (-applyAsDifferentialOperator q t) := by
      simp only [HasPosLeadingCoeff, leadingCoeff_neg, hqlc]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hq0 hneg)
    have hstrict := strictInterl_of_stablePencil_of_sameDegree hpneg hqneg
      hstable.neg_neg (by simp only [natDegree_neg]; exact hpdeg.trans hqdeg.symm)
    simpa using (hstrict.C_mul_left (a := -1) (by norm_num)).C_mul_right
      (a := -1) (by norm_num)
  · exact strictInterl_of_stablePencil_of_sameDegree
      (by change 0 < _; rw [hplc]; exact mul_pos hp0 hpos)
      (by change 0 < _; rw [hqlc]; exact mul_pos hq0 hpos)
      hstable (hpdeg.trans hqdeg.symm)

/-- The images of positive-coefficient interlacing symbols have the degree
of the input and sorted root lists in the order
`q₁ ≤ p₁ ≤ q₂ ≤ p₂ ≤ ⋯ ≤ q_d ≤ p_d`, with multiplicities. -/
theorem exists_listAlternates_applyAsDifferentialOperator
    {p q t : ℝ[X]} (hp : ∀ k ≤ p.natDegree, 0 < p.coeff k)
    (hq : ∀ k ≤ q.natDegree, 0 < q.coeff k) (hpq : StrictInterl p q)
    (ht : t ≠ 0 ∧ t.Splits) :
    (applyAsDifferentialOperator p t).natDegree = t.natDegree ∧
      (applyAsDifferentialOperator q t).natDegree = t.natDegree ∧
      ∃ qs ps : List ℝ,
        qs.length = t.natDegree ∧ ps.length = t.natDegree ∧
        qs.Pairwise (· ≤ ·) ∧ ps.Pairwise (· ≤ ·) ∧
        (↑qs : Multiset ℝ) = (applyAsDifferentialOperator q t).roots ∧
        (↑ps : Multiset ℝ) = (applyAsDifferentialOperator p t).roots ∧
        ListAlternates qs ps := by
  obtain ⟨hstrict, hpdeg, hqdeg⟩ :=
    strictInterl_applyAsDifferentialOperator_of_coeff_zero_pos
      (hp _ le_rfl) (hq _ le_rfl) hpq (hp 0 (Nat.zero_le _)) (hq 0 (Nat.zero_le _)) ht
  obtain ⟨qs, ps, hqs, hps, hqroots, hproots, halt⟩ :=
    hstrict.exists_listAlternates_of_natDegree_eq (hqdeg.trans hpdeg.symm)
  exact ⟨hpdeg, hqdeg, qs, ps,
    (hstrict.1.2.length_eq_natDegree_of_coe_eq_roots hqroots).trans hqdeg,
    (hstrict.2.1.2.length_eq_natDegree_of_coe_eq_roots hproots).trans hpdeg,
    hqs, hps, hqroots, hproots, halt⟩

end RealRooted.HermitePoulain
