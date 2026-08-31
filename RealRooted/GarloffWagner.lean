import RealRooted.GarloffWagner.KreinExpansion

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Garloff--Wagner

This compatibility module retains the later Krein and Hadamard theorem-route
layers for the direct Garloff--Wagner proof. The factorial/differential algebra
and Theorem 11 iterated-transform transport live in focused children and
remain available through this path.
-/


/-! ## Theorem 12 infrastructure -/

/-- Degree-zero polynomials are in zero-aware proper position. -/
theorem prec0_of_natDegree_eq_zero {p q : ℝ[X]}
    (hpdeg : p.natDegree = 0) (hqdeg : q.natDegree = 0) :
    Prec0 p q := by
  by_cases hp0 : p = 0
  · exact Or.inl hp0
  by_cases hq0 : q = 0
  · exact Or.inr (Or.inl hq0)
  exact
    (prec_degree_zero_degree_zero hp0
      (Polynomial.Splits.of_natDegree_eq_zero hpdeg) hq0
      (Polynomial.Splits.of_natDegree_eq_zero hqdeg) hpdeg hqdeg).toPrec0

namespace IsGWKreinSummand

/-- Krein summands of a PF polynomial are in proper position with the parent. -/
theorem prec {g q : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg0 : g ≠ 0) (hgs : g.Splits) :
    Prec q g := by
  rcases h with hself | ⟨u, hfactor⟩
  · rw [hself]
    exact prec_refl hg0 hgs
  · obtain ⟨hq0, hqs⟩ :=
      (show IsGWKreinSummand g q from Or.inr ⟨u, hfactor⟩).ne_zero_and_splits
        hg0 hgs
    rw [hfactor]
    exact prec_self_X_sub_C_mul hq0 hqs u

/-- Zero-aware form of `IsGWKreinSummand.prec`. -/
theorem prec0 {g q : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg0 : g ≠ 0) (hgs : g.Splits) :
    Prec0 q g :=
  (h.prec hg0 hgs).toPrec0

/-- Krein summands of a PF polynomial are PF. -/
theorem isPFPolynomial {g q : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg : IsPFPolynomial g) :
    IsPFPolynomial q := by
  rcases h with hself | ⟨u, hfactor⟩
  · simpa [hself] using hg
  · exact hg.of_X_sub_C_mul_factor hfactor

end IsGWKreinSummand

/-- Constant right input base case for Theorem 12(b). -/
theorem gwSchurProduct_prec0_of_right_natDegree_eq_zero
    (f g p : ℝ[X]) (hpdeg : p.natDegree = 0) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct g p) := by
  have hfdeg : (gwSchurProduct f p).natDegree = 0 := by
    exact le_antisymm
      ((natDegree_gwSchurProduct_le_right f p).trans (le_of_eq hpdeg))
      (Nat.zero_le _)
  have hgdeg : (gwSchurProduct g p).natDegree = 0 := by
    exact le_antisymm
      ((natDegree_gwSchurProduct_le_right g p).trans (le_of_eq hpdeg))
      (Nat.zero_le _)
  exact prec0_of_natDegree_eq_zero hfdeg hgdeg

/-- Constant right input base case for Theorem 12(a). -/
theorem gwSchurProduct_pf_of_right_natDegree_eq_zero {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hpdeg : p.natDegree = 0) :
    IsPFPolynomial (gwSchurProduct f p) := by
  have hdeg : (gwSchurProduct f p).natDegree = 0 := by
    exact le_antisymm
      ((natDegree_gwSchurProduct_le_right f p).trans (le_of_eq hpdeg))
      (Nat.zero_le _)
  exact IsPFPolynomial.of_realRooted_nonneg
    (hf.hasNonnegCoeffs.gwSchurProduct hp.hasNonnegCoeffs)
    (Polynomial.Splits.of_natDegree_eq_zero hdeg)

/-- Theorem 12(a) induction step in relational form: if the Schur product of
`D f` with `p` precedes the Schur product of `f` with `p`, then multiplying
the right input by a nonpositive linear factor keeps the previous product as a
left interleaver. -/
theorem gwSchurProduct_prec0_right_linearFactor_of_derivative_prec0
    {f p : ℝ[X]} {u : ℝ}
    (hu : u ≤ 0)
    (hder :
      Prec0 (gwSchurProduct (gwD f) p) (gwSchurProduct f p))
    (hF : IsPFPolynomial (gwSchurProduct f p))
    (hD : IsPFPolynomial (gwSchurProduct (gwD f) p)) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct f ((X - C u) * p)) := by
  have hX :
      Prec0 (gwSchurProduct f p)
        (X * gwSchurProduct (gwD f) p) :=
    prec0_mul_X_of_prec0 hder hD.hasNonnegCoeffs hF.hasNonnegCoeffs
  have hself : Prec0 (gwSchurProduct f p) (gwSchurProduct f p) :=
    hF.prec0_self
  have hcombo :
      Prec0 (gwSchurProduct f p)
        (C (1 : ℝ) * (X * gwSchurProduct (gwD f) p) +
          C (-u) * gwSchurProduct f p) :=
    prec0_nonneg_combo_right_of_common_left_of_nonneg hX hself
      (hD.X_mul.hasNonnegCoeffs) hF.hasNonnegCoeffs zero_le_one (by linarith)
  rw [gwSchurProduct_X_sub_C_mul_right]
  simpa [sub_eq_add_neg] using hcombo

/-- PF-preservation form of
`gwSchurProduct_prec0_right_linearFactor_of_derivative_prec0`. -/
theorem gwSchurProduct_pf_right_linearFactor_of_derivative_prec0
    {f p : ℝ[X]} {u : ℝ}
    (hu : u ≤ 0)
    (hder :
      Prec0 (gwSchurProduct (gwD f) p) (gwSchurProduct f p))
    (hF : IsPFPolynomial (gwSchurProduct f p))
    (hD : IsPFPolynomial (gwSchurProduct (gwD f) p)) :
    IsPFPolynomial (gwSchurProduct f ((X - C u) * p)) := by
  let F : ℝ[X] := gwSchurProduct f p
  let D : ℝ[X] := gwSchurProduct (gwD f) p
  have hprec :
      Prec0 F (gwSchurProduct f ((X - C u) * p)) :=
    gwSchurProduct_prec0_right_linearFactor_of_derivative_prec0
      hu hder hF hD
  have htarget_nn : HasNonnegCoeffs (gwSchurProduct f ((X - C u) * p)) := by
    rw [gwSchurProduct_X_sub_C_mul_right, sub_eq_add_neg]
    have hneg :
        HasNonnegCoeffs (-(C u * gwSchurProduct f p)) := by
      simpa [neg_mul, C_neg] using
        nonnegCoeffs_C_mul (by linarith : 0 ≤ -u) hF.hasNonnegCoeffs
    exact hD.hasNonnegCoeffs.X_mul.add hneg
  by_cases hF0 : F = 0
  · rw [gwSchurProduct_X_sub_C_mul_right]
    change IsPFPolynomial (X * D - C u * F)
    rw [hF0, mul_zero, sub_zero]
    exact hD.X_mul
  · rcases hprec with hleft0 | hright0 | hstrict
    · exact False.elim (hF0 hleft0)
    · simpa [hright0] using IsPFPolynomial.zero
    · exact IsPFPolynomial.of_realRooted_nonneg htarget_nn hstrict.2.1.2

/-- Multiplying the left polynomial in a zero-aware `Prec0` relation by a
nonnegative scalar preserves the relation. -/
theorem prec0_C_mul_left_of_nonneg {f g : ℝ[X]}
    (h : Prec0 f g) {a : ℝ} (ha : 0 ≤ a) :
    Prec0 (C a * f) g := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp [prec0_zero_left]
  rcases h with hf0 | hg0 | hprec
  · simp [hf0, prec0_zero_left]
  · simpa [hg0] using prec0_zero_right (C a * f)
  · exact (prec_C_mul_left hprec ha_pos.ne').toPrec0

/-- Adding two nonnegative-coefficient left summands with a common right bound
preserves zero-aware proper position. -/
theorem prec0_add_left_of_common_right_of_nonneg {p q h : ℝ[X]}
    (hph : Prec0 p h) (hqh : Prec0 q h)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q) :
    Prec0 (p + q) h := by
  classical
  have hsum :
      (Finset.univ.sum (fun b : Bool => cond b p q)) = p + q := by
    simp
  rw [← hsum]
  apply prec0_finsetSum_right_of_nonneg
  · intro b _
    cases b <;> simp [hph, hqh]
  · intro b _
    cases b <;> simp [hpnn, hqnn]

theorem HasNonnegCoeffs.weightedSum :
    ∀ l : List (ℝ × ℝ[X]),
      (∀ ap ∈ l, 0 ≤ ap.1) →
      (∀ ap ∈ l, HasNonnegCoeffs ap.2) →
      HasNonnegCoeffs (weightedSum l)
  | [], _, _ => by
      intro n
      simp
  | (a, p) :: l, hnonneg, hnn => by
      have ha : 0 ≤ a := hnonneg (a, p) (by simp)
      have hp : HasNonnegCoeffs p := hnn (a, p) (by simp)
      have htail_nonneg : ∀ ap ∈ l, 0 ≤ ap.1 :=
        fun ap hap => hnonneg ap (by simp [hap])
      have htail_nn : ∀ ap ∈ l, HasNonnegCoeffs ap.2 :=
        fun ap hap => hnn ap (by simp [hap])
      simpa [weightedSum_cons] using
        (nonnegCoeffs_C_mul ha hp).add
          (HasNonnegCoeffs.weightedSum l htail_nonneg htail_nn)

/-- Zero-aware weighted common-right cone closure. -/
theorem prec0_weightedSum_right_of_nonneg :
    ∀ (l : List (ℝ × ℝ[X])) (h : ℝ[X]),
      (∀ ap ∈ l, 0 ≤ ap.1) →
      (∀ ap ∈ l, Prec0 ap.2 h) →
      (∀ ap ∈ l, HasNonnegCoeffs ap.2) →
      Prec0 (weightedSum l) h
  | [], h, _, _, _ => by
      simp [prec0_zero_left]
  | (a, p) :: l, h, hnonneg, hprec, hnn => by
      have ha : 0 ≤ a := hnonneg (a, p) (by simp)
      have hp_prec : Prec0 p h := hprec (a, p) (by simp)
      have hp_nn : HasNonnegCoeffs p := hnn (a, p) (by simp)
      have htail_nonneg : ∀ ap ∈ l, 0 ≤ ap.1 :=
        fun ap hap => hnonneg ap (by simp [hap])
      have htail_prec : ∀ ap ∈ l, Prec0 ap.2 h :=
        fun ap hap => hprec ap (by simp [hap])
      have htail_nn : ∀ ap ∈ l, HasNonnegCoeffs ap.2 :=
        fun ap hap => hnn ap (by simp [hap])
      have hhead_prec : Prec0 (C a * p) h :=
        prec0_C_mul_left_of_nonneg hp_prec ha
      have htail_prec_sum : Prec0 (weightedSum l) h :=
        prec0_weightedSum_right_of_nonneg l h htail_nonneg htail_prec htail_nn
      have hhead_nn : HasNonnegCoeffs (C a * p) :=
        nonnegCoeffs_C_mul ha hp_nn
      have htail_sum_nn : HasNonnegCoeffs (weightedSum l) :=
        HasNonnegCoeffs.weightedSum l htail_nonneg htail_nn
      simpa [weightedSum_cons] using
        prec0_add_left_of_common_right_of_nonneg hhead_prec htail_prec_sum
          hhead_nn htail_sum_nn

theorem gwSchurProduct_weightedSum_left :
    ∀ (l : List (ℝ × ℝ[X])) (p : ℝ[X]),
      gwSchurProduct (weightedSum l) p =
        weightedSum (l.map fun ap => (ap.1, gwSchurProduct ap.2 p))
  | [], _ => by
      simp
  | (a, q) :: l, p => by
      rw [weightedSum_cons, gwSchurProduct_add_left, gwSchurProduct_C_mul_left,
        gwSchurProduct_weightedSum_left l p]
      rfl

/-- Apply the Schur product to a nonnegative weighted expansion whose summands
all precede the same right Schur product. -/
theorem gwSchurProduct_prec0_of_weightedSum_right {f g p : ℝ[X]}
    {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hprec :
      ∀ ap ∈ l, Prec0 (gwSchurProduct ap.2 p) (gwSchurProduct g p))
    (hnn : ∀ ap ∈ l, HasNonnegCoeffs (gwSchurProduct ap.2 p)) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct g p) := by
  rw [hf, gwSchurProduct_weightedSum_left]
  apply prec0_weightedSum_right_of_nonneg
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hnonneg ap0 hap0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hprec ap0 hap0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hnn ap0 hap0

/-- Theorem 12(b) reducer after Lemma 7 has expanded the left input into
Krein summands of the right input. -/
theorem gwSchurProduct_prec0_of_kreinSummandExpansion {f g p : ℝ[X]}
    {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hsummand : ∀ ap ∈ l, IsGWKreinSummand g ap.2)
    (hprec :
      ∀ q : ℝ[X], IsGWKreinSummand g q →
        Prec0 (gwSchurProduct q p) (gwSchurProduct g p))
    (hnn :
      ∀ q : ℝ[X], IsGWKreinSummand g q →
        HasNonnegCoeffs (gwSchurProduct q p)) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct g p) :=
  gwSchurProduct_prec0_of_weightedSum_right hf hnonneg
    (fun ap hap => hprec ap.2 (hsummand ap hap))
    (fun ap hap => hnn ap.2 (hsummand ap hap))

/-- A PF polynomial's derivative precedes the polynomial itself in the
zero-aware orientation. -/
theorem IsPFPolynomial.derivative_prec0_self {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    Prec0 p.derivative p := by
  by_cases hp0 : p = 0
  · rw [hp0, derivative_zero]
    exact prec0_zero_left 0
  have hps := hp.ne_zero_and_splits hp0
  by_cases hdeg0 : p.natDegree = 0
  · have hder0 : p.derivative = 0 :=
      derivative_eq_zero_of_natDegree_eq_zero hdeg0
    rw [hder0]
    exact prec0_zero_left p
  by_cases hdeg1 : p.natDegree = 1
  · have hder_ne : p.derivative ≠ 0 :=
      Polynomial.derivative_ne_zero.mpr hdeg0
    have hder_deg0 : p.derivative.natDegree = 0 := by rw [p.natDegree_derivative, hdeg1]
    exact
      (prec_degree_zero_right_of_degree_one hder_ne
        (Polynomial.Splits.of_natDegree_eq_zero hder_deg0) hp0 hps.2 hder_deg0
        hdeg1).toPrec0
  · have hdeg2 : 2 ≤ p.natDegree := by lia
    exact (derivative_interlaces hps.2 hdeg2).toPrec.toPrec0

/-- The first one-variable relation in Garloff--Wagner's double-deleted
paragraph: for `u <= 0`, `(1 - uD)Lp` precedes `Lp`. -/
theorem gwL_sub_C_mul_gwD_gwL_prec0_self {p : ℝ[X]} {u : ℝ}
    (hp : IsPFPolynomial p) (hu : u ≤ 0) :
    Prec0 (gwL p - C u * gwD (gwL p)) (gwL p) := by
  have hpL : IsPFPolynomial (gwL p) := by simpa [gwJL_zero_apply] using gwTheorem11PF hp 0
  have hder :
      Prec0 (gwD (gwL p)) (gwL p) := by
    simpa [gwD] using hpL.derivative_prec0_self
  have hscaled :
      Prec0 (C (-u) * gwD (gwL p)) (gwL p) :=
    prec0_C_mul_left_of_nonneg hder (by linarith)
  have hDnn : HasNonnegCoeffs (gwD (gwL p)) := by simpa [gwD] using hpL.derivative.hasNonnegCoeffs
  have hscaled_nn :
      HasNonnegCoeffs (C (-u) * gwD (gwL p)) :=
    nonnegCoeffs_C_mul (by linarith : 0 ≤ -u) hDnn
  have hsum :
      Prec0 (gwL p + C (-u) * gwD (gwL p)) (gwL p) :=
    prec0_add_left_of_common_right_of_nonneg hpL.prec0_self hscaled
      hpL.hasNonnegCoeffs hscaled_nn
  simpa [sub_eq_add_neg, C_neg, neg_mul] using hsum

/-- PF-cone form of `gwL_sub_C_mul_gwD_gwL_prec0_self`. -/
theorem gwL_sub_C_mul_gwD_gwL_pf {p : ℝ[X]} {u : ℝ}
    (hp : IsPFPolynomial p) (hu : u ≤ 0) :
    IsPFPolynomial (gwL p - C u * gwD (gwL p)) := by
  let T : ℝ[X] := gwL p - C u * gwD (gwL p)
  have hpL : IsPFPolynomial (gwL p) := by simpa [gwJL_zero_apply] using gwTheorem11PF hp 0
  have hprec : Prec0 T (gwL p) :=
    gwL_sub_C_mul_gwD_gwL_prec0_self hp hu
  have hDnn : HasNonnegCoeffs (gwD (gwL p)) := by simpa [gwD] using hpL.derivative.hasNonnegCoeffs
  have hTnn : HasNonnegCoeffs T := by
    change HasNonnegCoeffs (gwL p - C u * gwD (gwL p))
    have hscaled_nn :
        HasNonnegCoeffs (C (-u) * gwD (gwL p)) :=
      nonnegCoeffs_C_mul (by linarith : 0 ≤ -u) hDnn
    simpa [sub_eq_add_neg, C_neg, neg_mul] using
      hpL.hasNonnegCoeffs.add hscaled_nn
  by_cases hT0 : T = 0
  · simpa [T, hT0] using IsPFPolynomial.zero
  rcases hprec with hleft0 | hright0 | hstrict
  · exact False.elim (hT0 hleft0)
  · have hp0 : p = 0 := (gwL_eq_zero_iff p).1 hright0
    have hTzero : T = 0 := by simp [T, hp0, gwL_zero, gwD_zero]
    exact False.elim (hT0 hTzero)
  · exact IsPFPolynomial.of_realRooted_nonneg hTnn hstrict.1.2

/-- Theorem 12(a), zero-aware PF-cone form for the factorial Schur product. -/
def gwSchurProductPFStatement : Prop :=
  ∀ {f p : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial p →
    IsPFPolynomial (gwSchurProduct f p)

/-- Theorem 12(b), one fixed Schur-product factor, in the local orientation. -/
def gwSchurProductPrecStatement : Prop :=
  ∀ {f g p : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial g →
    IsPFPolynomial p →
    Prec f g →
    Prec0 (gwSchurProduct f p) (gwSchurProduct g p)

theorem gwSchurProductPF_of_prec
    (h : gwSchurProductPrecStatement) :
    gwSchurProductPFStatement := by
  intro f p hf hp
  by_cases hf0 : f = 0
  · simpa [hf0] using IsPFPolynomial.zero
  have hfs := hf.ne_zero_and_splits hf0
  exact IsPFPolynomial.of_prec0_self
    (hf.hasNonnegCoeffs.gwSchurProduct hp.hasNonnegCoeffs)
    (h hf hf hp (prec_refl hfs.1 hfs.2))

theorem gwSchurProductPrec0_of_prec
    (h : gwSchurProductPrecStatement) :
    ∀ {f g p : ℝ[X]},
      IsPFPolynomial f →
      IsPFPolynomial g →
      IsPFPolynomial p →
      Prec0 f g →
      Prec0 (gwSchurProduct f p) (gwSchurProduct g p) := by
  intro f g p hf hg hp hfg
  rcases hfg with hf0 | hg0 | hstrict
  · simpa [hf0] using prec0_zero_left (gwSchurProduct g p)
  · simpa [hg0] using prec0_zero_right (gwSchurProduct f p)
  · exact h hf hg hp hstrict

theorem gwSchurProduct_derivative_prec0_self_of_prec
    (h : gwSchurProductPrecStatement) {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) :
    Prec0 (gwSchurProduct (gwD f) p) (gwSchurProduct f p) := by
  simpa [gwD] using
    gwSchurProductPrec0_of_prec h hf.derivative hf hp hf.derivative_prec0_self

/-- Symmetric form of the Theorem 12(a) linear-factor step, used for
one-root-deleted Krein summands in Theorem 12(b). -/
theorem gwSchurProduct_prec0_left_linearFactor_of_derivative_prec0
    {q p : ℝ[X]} {u : ℝ}
    (hu : u ≤ 0)
    (hder :
      Prec0 (gwSchurProduct (gwD p) q) (gwSchurProduct p q))
    (hF : IsPFPolynomial (gwSchurProduct p q))
    (hD : IsPFPolynomial (gwSchurProduct (gwD p) q)) :
    Prec0 (gwSchurProduct q p) (gwSchurProduct ((X - C u) * q) p) := by
  rw [gwSchurProduct_comm q p, gwSchurProduct_comm ((X - C u) * q) p]
  exact gwSchurProduct_prec0_right_linearFactor_of_derivative_prec0
    hu hder hF hD

/-- If `q` is obtained from a PF polynomial `g` by deleting one linear root
factor, then the Schur product with `q` precedes the Schur product with `g`,
assuming the derivative-product recursive relation for the other factor. -/
theorem gwSchurProduct_prec0_of_kreinDeletedFactor
    {g q p : ℝ[X]} {u : ℝ}
    (hg : IsPFPolynomial g) (hfactor : g = (X - C u) * q)
    (hder :
      Prec0 (gwSchurProduct (gwD p) q) (gwSchurProduct p q))
    (hF : IsPFPolynomial (gwSchurProduct p q))
    (hD : IsPFPolynomial (gwSchurProduct (gwD p) q)) :
    Prec0 (gwSchurProduct q p) (gwSchurProduct g p) := by
  by_cases hq0 : q = 0
  · have hg0 : g = 0 := by rw [hfactor, hq0, mul_zero]
    simp [hq0, hg0, prec0_zero_left]
  have hg0 : g ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (X_sub_C_ne_zero u) hq0
  have hu_root : g.IsRoot u := by
    rw [hfactor, Polynomial.IsRoot.def, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hu : u ≤ 0 :=
    hg.roots_nonpos u ((mem_roots hg0).mpr hu_root)
  simpa [hfactor] using
    gwSchurProduct_prec0_left_linearFactor_of_derivative_prec0
      (q := q) (p := p) (u := u) hu hder hF hD

namespace IsGWKreinSummand

/-- Per-summand Theorem 12(b) step for a Krein summand of the right input. -/
theorem gwSchurProduct_prec0_of_derivative
    {g q p : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg : IsPFPolynomial g)
    (hgp : IsPFPolynomial (gwSchurProduct g p))
    (hder :
      Prec0 (gwSchurProduct (gwD p) q) (gwSchurProduct p q))
    (hF : IsPFPolynomial (gwSchurProduct p q))
    (hD : IsPFPolynomial (gwSchurProduct (gwD p) q)) :
    Prec0 (gwSchurProduct q p) (gwSchurProduct g p) := by
  rcases h with hself | ⟨u, hfactor⟩
  · simpa [hself] using hgp.prec0_self
  · exact gwSchurProduct_prec0_of_kreinDeletedFactor hg hfactor hder hF hD

end IsGWKreinSummand

/-- Theorem 12(b) reducer in the exact form produced by the Lemma 7 expansion:
it remains only to discharge the recursive derivative/PF obligations for each
Krein summand. -/
theorem gwSchurProduct_prec0_of_kreinSummandExpansion_of_derivative
    {f g p : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hsummand : ∀ ap ∈ l, IsGWKreinSummand g ap.2)
    (hg : IsPFPolynomial g)
    (hgp : IsPFPolynomial (gwSchurProduct g p))
    (hder :
      ∀ (q : ℝ[X]) (u : ℝ), g = (X - C u) * q →
        Prec0 (gwSchurProduct (gwD p) q) (gwSchurProduct p q))
    (hF :
      ∀ (q : ℝ[X]) (u : ℝ), g = (X - C u) * q →
        IsPFPolynomial (gwSchurProduct p q))
    (hD :
      ∀ (q : ℝ[X]) (u : ℝ), g = (X - C u) * q →
        IsPFPolynomial (gwSchurProduct (gwD p) q)) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct g p) :=
  gwSchurProduct_prec0_of_kreinSummandExpansion hf hnonneg hsummand
    (fun q hq => by
      rcases hq with hself | ⟨u, hfactor⟩
      · simpa [hself] using hgp.prec0_self
      · exact gwSchurProduct_prec0_of_kreinDeletedFactor hg hfactor
          (hder q u hfactor) (hF q u hfactor) (hD q u hfactor))
    (fun q hq => by
      rcases hq with hself | ⟨u, hfactor⟩
      · simpa [hself] using hgp.hasNonnegCoeffs
      · simpa [gwSchurProduct_comm q p] using
          (hF q u hfactor).hasNonnegCoeffs)

/-- Garloff--Wagner, Theorem 12, for the factorial Schur product.

The induction is over the total degree of the two active Schur-product
arguments.  At each measure we first prove PF preservation, then use that
same-measure result as the common-right PF input for the fixed-factor
proper-position statement.  All derivative and one-root-deleted calls have
strictly smaller total degree. -/
theorem gwSchurProductPFAndPrec :
    gwSchurProductPFStatement ∧ gwSchurProductPrecStatement := by
  classical
  let P : ℕ → Prop := fun n =>
    (∀ {f p : ℝ[X]},
      IsPFPolynomial f → IsPFPolynomial p →
        f.natDegree + p.natDegree = n →
          IsPFPolynomial (gwSchurProduct f p)) ∧
    (∀ {f g p : ℝ[X]},
      IsPFPolynomial f → IsPFPolynomial g → IsPFPolynomial p →
        Prec0 f g → g.natDegree + p.natDegree = n →
          Prec0 (gwSchurProduct f p) (gwSchurProduct g p))
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        have hA_lt :
            ∀ {f p : ℝ[X]},
              IsPFPolynomial f → IsPFPolynomial p →
                f.natDegree + p.natDegree < n →
                  IsPFPolynomial (gwSchurProduct f p) := by
          intro f p hf hp hlt
          exact (ih (f.natDegree + p.natDegree) hlt).1 hf hp rfl
        have hB_lt :
            ∀ {f g p : ℝ[X]},
              IsPFPolynomial f → IsPFPolynomial g → IsPFPolynomial p →
                Prec0 f g → g.natDegree + p.natDegree < n →
                  Prec0 (gwSchurProduct f p) (gwSchurProduct g p) := by
          intro f g p hf hg hp hfg hlt
          exact (ih (g.natDegree + p.natDegree) hlt).2 hf hg hp hfg rfl
        have hA :
            ∀ {f p : ℝ[X]},
              IsPFPolynomial f → IsPFPolynomial p →
                f.natDegree + p.natDegree = n →
                  IsPFPolynomial (gwSchurProduct f p) := by
          intro f p hf hp hmeasure
          by_cases hf0 : f = 0
          · rw [hf0, gwSchurProduct_zero_left]
            exact IsPFPolynomial.zero
          by_cases hp0 : p = 0
          · rw [hp0, gwSchurProduct_zero_right]
            exact IsPFPolynomial.zero
          by_cases hpdeg0 : p.natDegree = 0
          · exact gwSchurProduct_pf_of_right_natDegree_eq_zero hf hp hpdeg0
          rcases hp.exists_X_sub_C_factor_of_pos_natDegree
              (Nat.pos_of_ne_zero hpdeg0) with
            ⟨u, q, hu, hfactor, hq, hqdeg⟩
          have hF : IsPFPolynomial (gwSchurProduct f q) := by
            apply hA_lt hf hq
            rw [← hmeasure]
            lia
          have hD : IsPFPolynomial (gwSchurProduct (gwD f) q) := by
            have hfD : IsPFPolynomial (gwD f) := by
              change IsPFPolynomial f.derivative
              exact hf.derivative
            apply hA_lt hfD hq
            have hDdeg : (gwD f).natDegree ≤ f.natDegree := by simp [gwD]
            rw [← hmeasure]
            lia
          have hder :
              Prec0 (gwSchurProduct (gwD f) q) (gwSchurProduct f q) := by
            have hfD : IsPFPolynomial (gwD f) := by
              change IsPFPolynomial f.derivative
              exact hf.derivative
            have hprecD : Prec0 (gwD f) f := by
              change Prec0 f.derivative f
              exact hf.derivative_prec0_self
            apply hB_lt hfD hf hq hprecD
            rw [← hmeasure]
            lia
          rw [hfactor]
          exact gwSchurProduct_pf_right_linearFactor_of_derivative_prec0
            hu hder hF hD
        have hB :
            ∀ {f g p : ℝ[X]},
              IsPFPolynomial f → IsPFPolynomial g → IsPFPolynomial p →
                Prec0 f g → g.natDegree + p.natDegree = n →
                  Prec0 (gwSchurProduct f p) (gwSchurProduct g p) := by
          intro f g p hf hg hp hfg hmeasure
          rcases hfg with hf0 | hg0 | hstrict
          · rw [hf0, gwSchurProduct_zero_left]
            exact prec0_zero_left (gwSchurProduct g p)
          · rw [hg0, gwSchurProduct_zero_left]
            exact prec0_zero_right (gwSchurProduct f p)
          by_cases hpdeg0 : p.natDegree = 0
          · exact gwSchurProduct_prec0_of_right_natDegree_eq_zero f g p hpdeg0
          by_cases hgdeg0 : g.natDegree = 0
          · have hfdeg0 : f.natDegree = 0 := by
              have hstrict_le := hstrict.natDegree_le
              lia
            have hleftdeg : (gwSchurProduct f p).natDegree = 0 := by
              exact le_antisymm
                ((natDegree_gwSchurProduct_le_left f p).trans
                  (le_of_eq hfdeg0))
                (Nat.zero_le _)
            have hrightdeg : (gwSchurProduct g p).natDegree = 0 := by
              exact le_antisymm
                ((natDegree_gwSchurProduct_le_left g p).trans
                  (le_of_eq hgdeg0))
                (Nat.zero_le _)
            exact prec0_of_natDegree_eq_zero hleftdeg hrightdeg
          have hgp : IsPFPolynomial (gwSchurProduct g p) :=
            hA hg hp hmeasure
          have hfpos : HasPosLeadingCoeff f :=
            hf.hasNonnegCoeffs.pos_leadingCoeff hstrict.1.1
          have hgpos : HasPosLeadingCoeff g :=
            hg.hasNonnegCoeffs.pos_leadingCoeff hstrict.2.1.1
          rcases gwTheorem11PrecKreinSummandExpansion hstrict hfpos hgpos with
            ⟨l, hfexp, hnonneg, hsummand, _hex⟩
          have hdeleted :
              ∀ (q : ℝ[X]) (u : ℝ), g = (X - C u) * q →
                IsPFPolynomial q ∧ q.natDegree < g.natDegree := by
            intro q u hfactor
            have hq : IsPFPolynomial q := hg.of_X_sub_C_mul_factor hfactor
            have hq0 : q ≠ 0 := by
              intro hq0
              rw [hfactor, hq0, mul_zero] at hstrict
              exact hstrict.2.1.1 rfl
            have hqdeg : q.natDegree < g.natDegree := by
              rw [hfactor, natDegree_mul (X_sub_C_ne_zero u) hq0,
                natDegree_X_sub_C]
              lia
            exact ⟨hq, hqdeg⟩
          exact gwSchurProduct_prec0_of_kreinSummandExpansion_of_derivative
            hfexp hnonneg hsummand hg hgp
            (fun q u hfactor => by
              have hq := (hdeleted q u hfactor).1
              have hqdeg := (hdeleted q u hfactor).2
              have hpD : IsPFPolynomial (gwD p) := by
                change IsPFPolynomial p.derivative
                exact hp.derivative
              have hprecD : Prec0 (gwD p) p := by
                change Prec0 p.derivative p
                exact hp.derivative_prec0_self
              apply hB_lt hpD hp hq hprecD
              rw [← hmeasure]
              lia)
            (fun q u hfactor => by
              have hq := (hdeleted q u hfactor).1
              have hqdeg := (hdeleted q u hfactor).2
              apply hA_lt hp hq
              rw [← hmeasure]
              lia)
            (fun q u hfactor => by
              have hq := (hdeleted q u hfactor).1
              have hqdeg := (hdeleted q u hfactor).2
              have hpD : IsPFPolynomial (gwD p) := by
                change IsPFPolynomial p.derivative
                exact hp.derivative
              apply hA_lt hpD hq
              have hDdeg : (gwD p).natDegree ≤ p.natDegree := by simp [gwD]
              rw [← hmeasure]
              lia)
        exact ⟨hA, hB⟩
  constructor
  · intro f p hf hp
    exact (hP (f.natDegree + p.natDegree)).1 hf hp rfl
  · intro f g p hf hg hp hfg
    exact (hP (g.natDegree + p.natDegree)).2 hf hg hp hfg.toPrec0 rfl

theorem gwSchurProductPF :
    gwSchurProductPFStatement :=
  gwSchurProductPFAndPrec.1

/-- Ordinary Hadamard products preserve PF polynomials, obtained by applying
the Schur-product theorem to the `L`-normalized left input. -/
theorem gwHadamardProductPF {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) := by
  have hpL : IsPFPolynomial (gwL p) := by simpa [gwJL_zero_apply] using gwTheorem11PF hp 0
  simpa [gwSchurProduct_gwL_left] using gwSchurProductPF hpL hq

/-- The `L` operator preserves the PF cone. -/
theorem gwL_pf {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (gwL p) := by
  simpa [gwJL_zero_apply] using gwTheorem11PF hp 0

/-- The `L` operator preserves strict proper position. -/
theorem gwL_prec {f g : ℝ[X]} (hfg : Prec f g) :
    Prec (gwL f) (gwL g) := by
  simpa [gwJL_zero_apply] using gwTheorem11Prec hfg 0

/-- The `L` operator preserves zero-aware proper position. -/
theorem gwL_prec0 {f g : ℝ[X]} (hfg : Prec0 f g) :
    Prec0 (gwL f) (gwL g) := by
  rcases hfg with hf0 | hg0 | hstrict
  · rw [hf0, gwL_zero]
    exact prec0_zero_left (gwL g)
  · rw [hg0, gwL_zero]
    exact prec0_zero_right (gwL f)
  · exact (gwL_prec hstrict).toPrec0

theorem gwSchurProductPrec :
    gwSchurProductPrecStatement :=
  gwSchurProductPFAndPrec.2

theorem gwSchurProductPrec0 :
    ∀ {f g p : ℝ[X]},
      IsPFPolynomial f →
      IsPFPolynomial g →
      IsPFPolynomial p →
      Prec0 f g →
      Prec0 (gwSchurProduct f p) (gwSchurProduct g p) :=
  gwSchurProductPrec0_of_prec gwSchurProductPrec

/-- Symmetric fixed-factor form of `gwSchurProductPrec0`. -/
theorem gwSchurProductPrec0_left {f p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct f q) := by
  simpa [gwSchurProduct_comm f p, gwSchurProduct_comm f q] using
    gwSchurProductPrec0 hp hq hf hpq

/-- Ordinary Hadamard products preserve zero-aware proper position in a fixed
right factor, via `L` and the checked Schur-product theorem. -/
theorem gwHadamardProductPrec0 {f g p : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hp : IsPFPolynomial p)
    (hfg : Prec0 f g) :
    Prec0 (hadamardProduct f p) (hadamardProduct g p) := by
  have hfL : IsPFPolynomial (gwL f) := gwL_pf hf
  have hgL : IsPFPolynomial (gwL g) := gwL_pf hg
  have hfgL : Prec0 (gwL f) (gwL g) := gwL_prec0 hfg
  simpa [gwSchurProduct_gwL_left] using
    gwSchurProductPrec0 hfL hgL hp hfgL

/-- Symmetric fixed-factor form of `gwHadamardProductPrec0`. -/
theorem gwHadamardProductPrec0_left {f p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (hadamardProduct f p) (hadamardProduct f q) := by
  simpa [hadamardProduct_comm f p, hadamardProduct_comm f q] using
    gwHadamardProductPrec0 hp hq hf hpq

/-- The remaining local core of Garloff--Wagner, Theorem 4(b), after the
fixed-factor cases are discharged: both factors are one-root-deleted Krein
summands. -/
def gwSchurProductDoubleDeletedKreinStatement : Prop :=
  ∀ {g q f p : ℝ[X]} {u v : ℝ},
    IsPFPolynomial g →
    IsPFPolynomial q →
    g ≠ 0 →
    q ≠ 0 →
    g = (X - C u) * f →
    q = (X - C v) * p →
    Prec0 (gwSchurProduct f p) (gwSchurProduct g q)

/-- Ordinary-Hadamard version of the double-deleted core in the proof of
Garloff--Wagner, Theorem 4(b).  This is the statement matching the paragraph
which expands `((X - j)g) ⊙ ((X - u)q)` through `L`, `J`, and `D`. -/
def gwHadamardProductDoubleDeletedKreinStatement : Prop :=
  ∀ {g q f p : ℝ[X]} {u v : ℝ},
    IsPFPolynomial g →
    IsPFPolynomial q →
    g ≠ 0 →
    q ≠ 0 →
    g = (X - C u) * f →
    q = (X - C v) * p →
    Prec0 (hadamardProduct f p) (hadamardProduct g q)

/-- First Schur term in Garloff--Wagner's double-deleted paragraph: the base
Hadamard product precedes the `X`-shifted term. -/
theorem gwSchurProduct_firstDoubleDeletedTerm_prec0
    {f p : ℝ[X]} {u : ℝ}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hu : u ≤ 0) :
    Prec0 (gwSchurProduct f (gwL p))
      (X * gwSchurProduct f (gwL p - C u * gwD (gwL p))) := by
  have hpL : IsPFPolynomial (gwL p) := gwL_pf hp
  have hT : IsPFPolynomial (gwL p - C u * gwD (gwL p)) :=
    gwL_sub_C_mul_gwD_gwL_pf hp hu
  have hprecT :
      Prec0 (gwSchurProduct f (gwL p - C u * gwD (gwL p)))
        (gwSchurProduct f (gwL p)) :=
    gwSchurProductPrec0_left hf hT hpL
      (gwL_sub_C_mul_gwD_gwL_prec0_self hp hu)
  exact
    prec0_mul_X_of_prec0 hprecT
      (gwSchurProductPF hf hT).hasNonnegCoeffs
      (gwSchurProductPF hf hpL).hasNonnegCoeffs

/-- Second Schur term in Garloff--Wagner's double-deleted paragraph: the base
Hadamard product precedes the `JL` transported full right factor. -/
theorem gwSchurProduct_secondDoubleDeletedTerm_prec0
    {f q p : ℝ[X]} {u : ℝ}
    (hf : IsPFPolynomial f) (hq : IsPFPolynomial q)
    (hq0 : q ≠ 0) (hfactor : q = (X - C u) * p) :
    Prec0 (gwSchurProduct f (gwL p))
      (gwSchurProduct f (gwJ (gwL p) - C u * gwL p)) := by
  have hsummand : IsGWKreinSummand q p := Or.inr ⟨u, hfactor⟩
  have hp : IsPFPolynomial p := hsummand.isPFPolynomial hq
  have hpL : IsPFPolynomial (gwL p) := gwL_pf hp
  have hqL : IsPFPolynomial (gwL q) := gwL_pf hq
  have hpq : Prec0 p q :=
    hsummand.prec0 hq0 (hq.ne_zero_and_splits hq0).2
  have hLpLq : Prec0 (gwL p) (gwL q) := gwL_prec0 hpq
  have hSchur :
      Prec0 (gwSchurProduct f (gwL p)) (gwSchurProduct f (gwL q)) :=
    gwSchurProductPrec0_left hf hpL hqL hLpLq
  simpa [hfactor, gwL_X_sub_C_mul] using hSchur

/-- Garloff--Wagner's double-deleted compatibility paragraph in Theorem 4(b),
in the ordinary-Hadamard form needed for the two-pair theorem. -/
theorem gwHadamardProductDoubleDeletedKrein :
    gwHadamardProductDoubleDeletedKreinStatement := by
  intro g q f p u v hg hq hg0 hq0 hgfactor hqfactor
  have hfsummand : IsGWKreinSummand g f := Or.inr ⟨u, hgfactor⟩
  have hpsummand : IsGWKreinSummand q p := Or.inr ⟨v, hqfactor⟩
  have hf : IsPFPolynomial f := hfsummand.isPFPolynomial hg
  have hp : IsPFPolynomial p := hpsummand.isPFPolynomial hq
  have hu_root : g.IsRoot u := by
    rw [hgfactor, Polynomial.IsRoot.def, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hv_root : q.IsRoot v := by
    rw [hqfactor, Polynomial.IsRoot.def, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hu : u ≤ 0 :=
    hg.roots_nonpos u ((mem_roots hg0).mpr hu_root)
  have hv : v ≤ 0 :=
    hq.roots_nonpos v ((mem_roots hq0).mpr hv_root)
  let B : ℝ[X] := gwSchurProduct f (gwL p)
  let S₁ : ℝ[X] := gwSchurProduct f (gwL p - C v * gwD (gwL p))
  let S₂ : ℝ[X] := gwSchurProduct f (gwJ (gwL p) - C v * gwL p)
  have hfirst : Prec0 B (X * S₁) := by
    change Prec0 (gwSchurProduct f (gwL p))
      (X * gwSchurProduct f (gwL p - C v * gwD (gwL p)))
    exact gwSchurProduct_firstDoubleDeletedTerm_prec0 hf hp hv
  have hsecond : Prec0 B S₂ := by
    change Prec0 (gwSchurProduct f (gwL p))
      (gwSchurProduct f (gwJ (gwL p) - C v * gwL p))
    exact gwSchurProduct_secondDoubleDeletedTerm_prec0 hf hq hq0 hqfactor
  have hS₁ : IsPFPolynomial S₁ := by
    change IsPFPolynomial (gwSchurProduct f (gwL p - C v * gwD (gwL p)))
    exact gwSchurProductPF hf (gwL_sub_C_mul_gwD_gwL_pf hp hv)
  have hS₂ : IsPFPolynomial S₂ := by
    change IsPFPolynomial (gwSchurProduct f (gwJ (gwL p) - C v * gwL p))
    have hqL : IsPFPolynomial (gwL q) := gwL_pf hq
    simpa [hqfactor, gwL_X_sub_C_mul] using gwSchurProductPF hf hqL
  have hcombo :
      Prec0 B (C (1 : ℝ) * (X * S₁) + C (-u) * S₂) :=
    prec0_nonneg_combo_right_of_common_left_of_nonneg hfirst hsecond
      hS₁.X_mul.hasNonnegCoeffs hS₂.hasNonnegCoeffs zero_le_one (by linarith)
  rw [← gwSchurProduct_gwL_right f p, hgfactor, hqfactor,
    hadamardProduct_X_sub_C_mul_X_sub_C_mul_eq]
  change Prec0 B (X * S₁ - C u * S₂)
  simpa [sub_eq_add_neg, C_neg, neg_mul] using hcombo

namespace IsGWKreinSummand

/-- Fixed-factor Schur products of a Krein summand precede the parent product. -/
theorem gwSchurProduct_prec0 {g q p : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg : IsPFPolynomial g) (hp : IsPFPolynomial p) (hg0 : g ≠ 0) :
    Prec0 (gwSchurProduct q p) (gwSchurProduct g p) :=
  gwSchurProductPrec0 (h.isPFPolynomial hg) hg hp
    (h.prec0 hg0 (hg.ne_zero_and_splits hg0).2)

/-- Two arbitrary Krein summands reduce to the genuinely double-deleted case. -/
theorem gwSchurProduct_prec0_of_doubleDeleted
    (hDouble : gwSchurProductDoubleDeletedKreinStatement)
    {g q f p : ℝ[X]} (hf : IsGWKreinSummand g f)
    (hp : IsGWKreinSummand q p)
    (hg : IsPFPolynomial g) (hq : IsPFPolynomial q)
    (hg0 : g ≠ 0) (hq0 : q ≠ 0) :
    Prec0 (gwSchurProduct f p) (gwSchurProduct g q) := by
  rcases hf with hfg_self | ⟨u, hfg_factor⟩
  · rw [hfg_self]
    simpa [gwSchurProduct_comm p g, gwSchurProduct_comm q g] using
      hp.gwSchurProduct_prec0 hq hg hq0
  rcases hp with hpq_self | ⟨v, hpq_factor⟩
  · rw [hpq_self]
    exact (show IsGWKreinSummand g f from Or.inr ⟨u, hfg_factor⟩).gwSchurProduct_prec0
      hg hq hg0
  · exact hDouble hg hq hg0 hq0 hfg_factor hpq_factor

/-- Fixed-factor ordinary Hadamard products of a Krein summand precede the
parent product. -/
theorem gwHadamardProduct_prec0 {g q p : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg : IsPFPolynomial g) (hp : IsPFPolynomial p) (hg0 : g ≠ 0) :
    Prec0 (hadamardProduct q p) (hadamardProduct g p) :=
  gwHadamardProductPrec0 (h.isPFPolynomial hg) hg hp
    (h.prec0 hg0 (hg.ne_zero_and_splits hg0).2)

/-- Two arbitrary Krein summands reduce to the genuinely double-deleted
ordinary-Hadamard case. -/
theorem gwHadamardProduct_prec0_of_doubleDeleted
    (hDouble : gwHadamardProductDoubleDeletedKreinStatement)
    {g q f p : ℝ[X]} (hf : IsGWKreinSummand g f)
    (hp : IsGWKreinSummand q p)
    (hg : IsPFPolynomial g) (hq : IsPFPolynomial q)
    (hg0 : g ≠ 0) (hq0 : q ≠ 0) :
    Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  rcases hf with hfg_self | ⟨u, hfg_factor⟩
  · rw [hfg_self]
    simpa [hadamardProduct_comm p g, hadamardProduct_comm q g] using
      hp.gwHadamardProduct_prec0 hq hg hq0
  rcases hp with hpq_self | ⟨v, hpq_factor⟩
  · rw [hpq_self]
    exact (show IsGWKreinSummand g f from Or.inr ⟨u, hfg_factor⟩).gwHadamardProduct_prec0
      hg hq hg0
  · exact hDouble hg hq hg0 hq0 hfg_factor hpq_factor

end IsGWKreinSummand

/-- Hadamard product distributes over a weighted sum in the left argument. -/
theorem hadamardProduct_weightedSum_left :
    ∀ (l : List (ℝ × ℝ[X])) (p : ℝ[X]),
      hadamardProduct (weightedSum l) p =
        weightedSum (l.map fun ap => (ap.1, hadamardProduct ap.2 p))
  | [], _ => by
      simp
  | (a, q) :: l, p => by
      rw [weightedSum_cons, hadamardProduct_add_left, hadamardProduct_C_mul_left,
        hadamardProduct_weightedSum_left l p]
      rfl

/-- Hadamard product distributes over a weighted sum in the right argument. -/
theorem hadamardProduct_weightedSum_right :
    ∀ (p : ℝ[X]) (l : List (ℝ × ℝ[X])),
      hadamardProduct p (weightedSum l) =
        weightedSum (l.map fun ap => (ap.1, hadamardProduct p ap.2))
  | _, [] => by
      simp
  | p, (a, q) :: l => by
      rw [weightedSum_cons, hadamardProduct_add_right, hadamardProduct_C_mul_right,
        hadamardProduct_weightedSum_right p l]
      rfl

/-- If the left input is expanded into Krein summands and the right input is a
single Krein summand, every Hadamard summand has the same right bound. -/
theorem hadamardProduct_prec0_of_kreinSummandExpansion_left
    {f g p q : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hsummand : ∀ ap ∈ l, IsGWKreinSummand g ap.2)
    (hp : IsGWKreinSummand q p)
    (hg : IsPFPolynomial g) (hq : IsPFPolynomial q)
    (hg0 : g ≠ 0) (hq0 : q ≠ 0) :
    Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  rw [hf, hadamardProduct_weightedSum_left]
  apply prec0_weightedSum_right_of_nonneg
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hnonneg ap0 hap0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact (hsummand ap0 hap0).gwHadamardProduct_prec0_of_doubleDeleted
      gwHadamardProductDoubleDeletedKrein hp hg hq hg0 hq0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact
      (gwHadamardProductPF ((hsummand ap0 hap0).isPFPolynomial hg)
        (hp.isPFPolynomial hq)).hasNonnegCoeffs

/-- Two Krein expansions assemble the ordinary-Hadamard two-pair theorem. -/
theorem hadamardProduct_prec0_of_kreinSummandExpansions
    {f g p q : ℝ[X]} {lf lp : List (ℝ × ℝ[X])}
    (hf : f = weightedSum lf) (hp : p = weightedSum lp)
    (hfnonneg : ∀ ap ∈ lf, 0 ≤ ap.1)
    (hpnonneg : ∀ ap ∈ lp, 0 ≤ ap.1)
    (hfsummand : ∀ ap ∈ lf, IsGWKreinSummand g ap.2)
    (hpsummand : ∀ ap ∈ lp, IsGWKreinSummand q ap.2)
    (hfPF : IsPFPolynomial f) (hg : IsPFPolynomial g) (hq : IsPFPolynomial q)
    (hg0 : g ≠ 0) (hq0 : q ≠ 0) :
    Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  rw [hp, hadamardProduct_weightedSum_right]
  apply prec0_weightedSum_right_of_nonneg
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hpnonneg ap0 hap0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hadamardProduct_prec0_of_kreinSummandExpansion_left
      hf hfnonneg hfsummand (hpsummand ap0 hap0) hg hq hg0 hq0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact
      (gwHadamardProductPF hfPF
        ((hpsummand ap0 hap0).isPFPolynomial hq)).hasNonnegCoeffs

/-- Garloff--Wagner, Theorem 4(b), for PF polynomials in the local
orientation. -/
theorem gwHadamardProductPrec0_of_prec {f g p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hfg : Prec f g) (hpq : Prec p q) :
    Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  have hfpos : HasPosLeadingCoeff f :=
    hf.hasNonnegCoeffs.pos_leadingCoeff hfg.1.1
  have hgpos : HasPosLeadingCoeff g :=
    hg.hasNonnegCoeffs.pos_leadingCoeff hfg.2.1.1
  have hppos : HasPosLeadingCoeff p :=
    hp.hasNonnegCoeffs.pos_leadingCoeff hpq.1.1
  have hqpos : HasPosLeadingCoeff q :=
    hq.hasNonnegCoeffs.pos_leadingCoeff hpq.2.1.1
  rcases gwTheorem11PrecKreinSummandExpansion hfg hfpos hgpos with
    ⟨lf, hfeq, hfnonneg, hfsummand, _⟩
  rcases gwTheorem11PrecKreinSummandExpansion hpq hppos hqpos with
    ⟨lp, hpeq, hpnonneg, hpsummand, _⟩
  exact hadamardProduct_prec0_of_kreinSummandExpansions
    hfeq hpeq hfnonneg hpnonneg hfsummand hpsummand
    hf hg hq hfg.2.1.1 hpq.2.1.1

/-- Garloff--Wagner, Theorem 4(b), in the nonnegative-coefficient form used by
the `Hadamard` module. -/
theorem gwHadamardProductNonnegPrec {f g p q : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hfg : Prec f g) (hpq : Prec p q) :
    Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  exact gwHadamardProductPrec0_of_prec
    (IsPFPolynomial.of_realRooted_nonneg hf hfg.1.2)
    (IsPFPolynomial.of_realRooted_nonneg hg hfg.2.1.2)
    (IsPFPolynomial.of_realRooted_nonneg hp hpq.1.2)
    (IsPFPolynomial.of_realRooted_nonneg hq hpq.2.1.2)
    hfg hpq

end RealRooted
