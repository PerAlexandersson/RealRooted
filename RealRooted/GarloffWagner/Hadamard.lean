import RealRooted.GarloffWagner.Theorem12

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Garloff--Wagner Hadamard interlacing theorem

The double-deleted Krein reduction and the final two-pair Hadamard
interlacing theorem.
-/

/-- First Schur term in Garloff--Wagner's double-deleted paragraph: the base
Hadamard product precedes the `X`-shifted term. -/
private theorem factorialHadamardProduct_firstDoubleDeletedTerm_interl
    {f p : ℝ[X]} {u : ℝ}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hu : u ≤ 0) :
    Interl (factorialHadamardProduct f (divFactorial p))
      (X * factorialHadamardProduct f (divFactorial p - C u * derivative (divFactorial p))) := by
  have hpL : IsPFPolynomial (divFactorial p) := hp.divFactorial
  have hT : IsPFPolynomial (divFactorial p - C u * derivative (divFactorial p)) :=
    divFactorial_sub_C_mul_derivative_pf hp hu
  have hinterlT :
      Interl (factorialHadamardProduct f (divFactorial p - C u * derivative (divFactorial p)))
        (factorialHadamardProduct f (divFactorial p)) :=
    Interl.factorialHadamardProduct_left hf hT hpL
      (divFactorial_sub_C_mul_derivative_interl_self hp hu)
  exact
    interl_mul_X_of_interl hinterlT
      (hf.factorialHadamardProduct hT).hasNonnegCoeffs
      (hf.factorialHadamardProduct hpL).hasNonnegCoeffs

/-- Second Schur term in Garloff--Wagner's double-deleted paragraph: the base
Hadamard product precedes the `JL` transported full right factor. -/
private theorem factorialHadamardProduct_secondDoubleDeletedTerm_interl
    {f q p : ℝ[X]} {u : ℝ}
    (hf : IsPFPolynomial f) (hq : IsPFPolynomial q)
    (hq0 : q ≠ 0) (hfactor : q = (X - C u) * p) :
    Interl (factorialHadamardProduct f (divFactorial p))
      (factorialHadamardProduct f (antiderivative (divFactorial p) - C u * divFactorial p)) := by
  have hsummand : IsKreinSummand q p := Or.inr ⟨u, hfactor⟩
  have hp : IsPFPolynomial p := hsummand.isPFPolynomial hq
  have hpL : IsPFPolynomial (divFactorial p) := hp.divFactorial
  have hqL : IsPFPolynomial (divFactorial q) := hq.divFactorial
  have hpq : Interl p q :=
    hsummand.interl hq0 (hq.ne_zero_and_splits hq0).2
  have hLpLq : Interl (divFactorial p) (divFactorial q) := hpq.divFactorial
  have hSchur :
      Interl (factorialHadamardProduct f (divFactorial p))
        (factorialHadamardProduct f (divFactorial q)) :=
    Interl.factorialHadamardProduct_left hf hpL hqL hLpLq
  simpa [hfactor, divFactorial_X_sub_C_mul] using hSchur

/-- Garloff--Wagner's double-deleted compatibility paragraph in Theorem 4(b),
in the ordinary-Hadamard form needed for the two-pair theorem: if `f` and `p`
are one-root-deleted factors of the PF polynomials `g` and `q`, then
`f ⊙ p ≪ g ⊙ q`.  This is the paragraph which expands
`((X - u)f) ⊙ ((X - v)p)` through `L`, `J`, and `D`. -/
private theorem interl_hadamardProduct_of_kreinDeleted {g q f p : ℝ[X]} {u v : ℝ}
    (hg : IsPFPolynomial g) (hq : IsPFPolynomial q) (hg0 : g ≠ 0) (hq0 : q ≠ 0)
    (hgfactor : g = (X - C u) * f) (hqfactor : q = (X - C v) * p) :
    Interl (hadamardProduct f p) (hadamardProduct g q) := by
  have hfsummand : IsKreinSummand g f := Or.inr ⟨u, hgfactor⟩
  have hpsummand : IsKreinSummand q p := Or.inr ⟨v, hqfactor⟩
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
  let B : ℝ[X] := factorialHadamardProduct f (divFactorial p)
  let S₁ : ℝ[X] :=
    factorialHadamardProduct f (divFactorial p - C v * derivative (divFactorial p))
  let S₂ : ℝ[X] :=
    factorialHadamardProduct f (antiderivative (divFactorial p) - C v * divFactorial p)
  have hfirst : Interl B (X * S₁) := by
    change Interl (factorialHadamardProduct f (divFactorial p))
      (X * factorialHadamardProduct f (divFactorial p - C v * derivative (divFactorial p)))
    exact factorialHadamardProduct_firstDoubleDeletedTerm_interl hf hp hv
  have hsecond : Interl B S₂ := by
    change Interl (factorialHadamardProduct f (divFactorial p))
      (factorialHadamardProduct f (antiderivative (divFactorial p) - C v * divFactorial p))
    exact factorialHadamardProduct_secondDoubleDeletedTerm_interl hf hq hq0 hqfactor
  have hS₁ : IsPFPolynomial S₁ := by
    change IsPFPolynomial
      (factorialHadamardProduct f (divFactorial p - C v * derivative (divFactorial p)))
    exact hf.factorialHadamardProduct (divFactorial_sub_C_mul_derivative_pf hp hv)
  have hS₂ : IsPFPolynomial S₂ := by
    change IsPFPolynomial
      (factorialHadamardProduct f (antiderivative (divFactorial p) - C v * divFactorial p))
    simpa [hqfactor, divFactorial_X_sub_C_mul] using hf.factorialHadamardProduct hq.divFactorial
  have hcombo :
      Interl B (C (1 : ℝ) * (X * S₁) + C (-u) * S₂) :=
    interl_nonneg_combo_right_of_common_left_of_nonneg hfirst hsecond
      hS₁.X_mul.hasNonnegCoeffs hS₂.hasNonnegCoeffs zero_le_one (by linarith)
  rw [← factorialHadamardProduct_divFactorial_right f p, hgfactor, hqfactor,
    hadamardProduct_X_sub_C_mul_X_sub_C_mul_eq]
  change Interl B (X * S₁ - C u * S₂)
  simpa [sub_eq_add_neg, C_neg, neg_mul] using hcombo

namespace IsKreinSummand

/-- Fixed-factor Schur products of a Krein summand precede the parent product. -/
theorem interl_factorialHadamardProduct {g q p : ℝ[X]} (h : IsKreinSummand g q)
    (hg : IsPFPolynomial g) (hp : IsPFPolynomial p) (hg0 : g ≠ 0) :
    Interl (factorialHadamardProduct q p) (factorialHadamardProduct g p) :=
  Interl.factorialHadamardProduct_right (h.isPFPolynomial hg) hg hp
    (h.interl hg0 (hg.ne_zero_and_splits hg0).2)

/-- Fixed-factor ordinary Hadamard products of a Krein summand precede the
parent product. -/
theorem interl_hadamardProduct {g q p : ℝ[X]} (h : IsKreinSummand g q)
    (hg : IsPFPolynomial g) (hp : IsPFPolynomial p) (hg0 : g ≠ 0) :
    Interl (hadamardProduct q p) (hadamardProduct g p) :=
  Interl.hadamardProduct_right (h.isPFPolynomial hg) hg hp
    (h.interl hg0 (hg.ne_zero_and_splits hg0).2)

/-- Ordinary Hadamard products of two arbitrary Krein summands precede the
parent product; the genuinely double-deleted case is
`interl_hadamardProduct_of_kreinDeleted`. -/
theorem interl_hadamardProduct_of_both
    {g q f p : ℝ[X]} (hf : IsKreinSummand g f)
    (hp : IsKreinSummand q p)
    (hg : IsPFPolynomial g) (hq : IsPFPolynomial q)
    (hg0 : g ≠ 0) (hq0 : q ≠ 0) :
    Interl (hadamardProduct f p) (hadamardProduct g q) := by
  rcases hf with hfg_self | ⟨u, hfg_factor⟩
  · rw [hfg_self]
    simpa [hadamardProduct_comm p g, hadamardProduct_comm q g] using
      hp.interl_hadamardProduct hq hg hq0
  rcases hp with hpq_self | ⟨v, hpq_factor⟩
  · rw [hpq_self]
    exact (show IsKreinSummand g f from Or.inr ⟨u, hfg_factor⟩).interl_hadamardProduct
      hg hq hg0
  · exact interl_hadamardProduct_of_kreinDeleted hg hq hg0 hq0 hfg_factor hpq_factor

end IsKreinSummand

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
theorem hadamardProduct_interl_of_kreinSummandExpansion_left
    {f g p q : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hsummand : ∀ ap ∈ l, IsKreinSummand g ap.2)
    (hp : IsKreinSummand q p)
    (hg : IsPFPolynomial g) (hq : IsPFPolynomial q)
    (hg0 : g ≠ 0) (hq0 : q ≠ 0) :
    Interl (hadamardProduct f p) (hadamardProduct g q) := by
  rw [hf, hadamardProduct_weightedSum_left]
  apply interl_weightedSum_right_of_nonneg
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hnonneg ap0 hap0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact (hsummand ap0 hap0).interl_hadamardProduct_of_both
      hp hg hq hg0 hq0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact
      (IsPFPolynomial.hadamardProduct ((hsummand ap0 hap0).isPFPolynomial hg)
        (hp.isPFPolynomial hq)).hasNonnegCoeffs

/-- Two Krein expansions assemble the ordinary-Hadamard two-pair theorem. -/
theorem hadamardProduct_interl_of_kreinSummandExpansions
    {f g p q : ℝ[X]} {lf lp : List (ℝ × ℝ[X])}
    (hf : f = weightedSum lf) (hp : p = weightedSum lp)
    (hfnonneg : ∀ ap ∈ lf, 0 ≤ ap.1)
    (hpnonneg : ∀ ap ∈ lp, 0 ≤ ap.1)
    (hfsummand : ∀ ap ∈ lf, IsKreinSummand g ap.2)
    (hpsummand : ∀ ap ∈ lp, IsKreinSummand q ap.2)
    (hfPF : IsPFPolynomial f) (hg : IsPFPolynomial g) (hq : IsPFPolynomial q)
    (hg0 : g ≠ 0) (hq0 : q ≠ 0) :
    Interl (hadamardProduct f p) (hadamardProduct g q) := by
  rw [hp, hadamardProduct_weightedSum_right]
  apply interl_weightedSum_right_of_nonneg
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hpnonneg ap0 hap0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact hadamardProduct_interl_of_kreinSummandExpansion_left
      hf hfnonneg hfsummand (hpsummand ap0 hap0) hg hq hg0 hq0
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap0, hap0, rfl⟩
    exact
      (hfPF.hadamardProduct
        ((hpsummand ap0 hap0).isPFPolynomial hq)).hasNonnegCoeffs

/-- Garloff--Wagner, Theorem 4(b), for PF polynomials in the local
orientation. -/
theorem StrictInterl.interl_hadamardProduct_of_isPFPolynomial {f g p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hfg : StrictInterl f g) (hpq : StrictInterl p q) :
    Interl (hadamardProduct f p) (hadamardProduct g q) := by
  have hfpos : HasPosLeadingCoeff f :=
    hf.hasNonnegCoeffs.pos_leadingCoeff hfg.1.1
  have hgpos : HasPosLeadingCoeff g :=
    hg.hasNonnegCoeffs.pos_leadingCoeff hfg.2.1.1
  have hppos : HasPosLeadingCoeff p :=
    hp.hasNonnegCoeffs.pos_leadingCoeff hpq.1.1
  have hqpos : HasPosLeadingCoeff q :=
    hq.hasNonnegCoeffs.pos_leadingCoeff hpq.2.1.1
  rcases hfg.exists_kreinSummandExpansion hfpos hgpos with
    ⟨lf, hfeq, hfnonneg, hfsummand, _⟩
  rcases hpq.exists_kreinSummandExpansion hppos hqpos with
    ⟨lp, hpeq, hpnonneg, hpsummand, _⟩
  exact hadamardProduct_interl_of_kreinSummandExpansions
    hfeq hpeq hfnonneg hpnonneg hfsummand hpsummand
    hf hg hq hfg.2.1.1 hpq.2.1.1

@[deprecated (since := "2026-10-06")]
alias gwHadamardProductInterl_of_strictInterl :=
  StrictInterl.interl_hadamardProduct_of_isPFPolynomial

/-- Garloff--Wagner, Theorem 4(b), in the nonnegative-coefficient form used by
the `Hadamard` module. -/
theorem StrictInterl.interl_hadamardProduct {f g p q : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hfg : StrictInterl f g) (hpq : StrictInterl p q) :
    Interl (hadamardProduct f p) (hadamardProduct g q) :=
  StrictInterl.interl_hadamardProduct_of_isPFPolynomial
    (IsPFPolynomial.of_realRooted_nonneg hf hfg.1.2)
    (IsPFPolynomial.of_realRooted_nonneg hg hfg.2.1.2)
    (IsPFPolynomial.of_realRooted_nonneg hp hpq.1.2)
    (IsPFPolynomial.of_realRooted_nonneg hq hpq.2.1.2)
    hfg hpq

end RealRooted
