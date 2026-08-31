import RealRooted.GarloffWagner.Theorem12

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Garloff--Wagner Hadamard endpoint

The double-deleted Krein reduction and the final two-pair Hadamard
proper-position theorem.
-/

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
