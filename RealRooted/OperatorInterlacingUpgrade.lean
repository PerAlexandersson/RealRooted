import RealRooted.GarloffWagner.KreinExpansion

/-!
# Oriented interlacing upgrades for linear maps

This file isolates the operator-theoretic part of an oriented interlacing
preserver argument.  The first reduction uses the Garloff--Wagner Krein
expansion: it is enough to control the image of a polynomial against the image
of each summand obtained by deleting one root.  For PF polynomials, the second
reduction shows that it is enough to control multiplication by one
nonnegative linear factor.

The remaining input for a concrete basis transform is therefore local: prove
that the transform sends `q` before the transform of `(X + C a) * q` whenever
`q` is PF and `a ≥ 0`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A real-linear map commutes with the finite weighted sums used in Krein
expansions. -/
theorem LinearMap.map_weightedSum (T : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    ∀ l : List (ℝ × ℝ[X]),
      T (weightedSum l) =
        weightedSum (l.map fun ap => (ap.1, T ap.2))
  | [] => by simp
  | (a, p) :: l => by
      simp only [weightedSum_cons, List.map_cons, T.map_add,
        LinearMap.map_weightedSum T l]
      rw [show C a * p = a • p by rw [Polynomial.smul_eq_C_mul],
        T.map_smul, Polynomial.smul_eq_C_mul]

/-- A linear map preserves PF Krein interlacing when every nonzero PF
polynomial remains after each possible one-root deletion in the oriented
order.  The self-summand is included in `IsGWKreinSummand`. -/
def PreservesPFKreinInterlacingOnDegree
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (D : ℕ) : Prop :=
  ∀ ⦃g q : ℝ[X]⦄,
    IsPFPolynomial g → g ≠ 0 → g.natDegree ≤ D →
      IsGWKreinSummand g q →
      StrictInterl (T q) (T g)

/-- A linear map preserves PF linear-factor interlacing when multiplication of
the input by one nonnegative linear factor advances its image in the oriented
interlacing order. -/
def PreservesPFLinearFactorInterlacingOnDegree
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (D : ℕ) : Prop :=
  ∀ ⦃q : ℝ[X]⦄ ⦃a : ℝ⦄,
    IsPFPolynomial q → q ≠ 0 → 0 ≤ a →
      ((X + C a) * q).natDegree ≤ D →
      StrictInterl (T q) (T ((X + C a) * q))

/-- Shift-chain form of the local operator condition.  This is the form
produced by induction over the linear factors of a PF polynomial. -/
def PreservesPFShiftInterlacingOnDegree
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (D : ℕ) : Prop :=
  ∀ ⦃q : ℝ[X]⦄ ⦃m : ℕ⦄,
    IsPFPolynomial q → q ≠ 0 →
      (X ^ (m + 1) * q).natDegree ≤ D →
      StrictInterl (T (X ^ m * q)) (T (X ^ (m + 1) * q))

/-- Every Krein summand of a nonzero PF polynomial is again PF. -/
theorem IsGWKreinSummand.isPFPolynomial {g q : ℝ[X]}
    (h : IsGWKreinSummand g q) (hg : IsPFPolynomial g) (hg0 : g ≠ 0) :
    IsPFPolynomial q := by
  rcases h with rfl | ⟨u, hfactor⟩
  · exact hg
  · exact hg.of_X_sub_C_mul_factor hfactor

/-- Krein-expansion reduction for an oriented interlacing preserver.

If the map preserves coefficientwise nonnegativity and sends every PF Krein
summand before the image of its ambient polynomial, then it preserves every
oriented interlacing pair of nonnegative-coefficient polynomials. -/
theorem strictInterl_map_of_preservesPFKreinInterlacingOnDegree
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {D : ℕ} {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (_hfdeg : f.natDegree ≤ D) (hgdeg : g.natDegree ≤ D)
    (hTnn : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTkrein : PreservesPFKreinInterlacingOnDegree T D) :
    StrictInterl (T f) (T g) := by
  have hfpos : HasPosLeadingCoeff f := hf.pos_leadingCoeff hfg.1.1
  have hgpos : HasPosLeadingCoeff g := hg.pos_leadingCoeff hfg.2.1.1
  have hpf : IsPFPolynomial g :=
    IsPFPolynomial.of_realRooted_nonneg hg hfg.2.1.2
  have hexp : ∃ l : List (ℝ × ℝ[X]),
      f = weightedSum l ∧
        (∀ ap ∈ l, 0 ≤ ap.1) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        ∃ ap ∈ l, 0 < ap.1 := by
    by_cases hgdeg : g.natDegree = 0
    · exact exists_kreinSummandExpansion_nonneg_right_of_natDegree_eq_zero
        hfg hfpos hgpos hgdeg
    · exact exists_kreinSummandExpansion_nonneg_right_of_pos_natDegree
        hfg hfpos hgpos (Nat.pos_of_ne_zero hgdeg)
  obtain ⟨l, hfl, hnonneg, hsummand, hex⟩ := hexp
  rw [hfl, RealRooted.LinearMap.map_weightedSum T l]
  apply StrictInterl.weightedSum_right_of_nonneg
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap₀, hap₀, rfl⟩
    exact hnonneg ap₀ hap₀
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap₀, hap₀, rfl⟩
    exact hTkrein hpf hfg.2.1.1 hgdeg (hsummand ap₀ hap₀)
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨ap₀, hap₀, rfl⟩
    have hinterl : StrictInterl (T ap₀.2) (T g) :=
      hTkrein hpf hfg.2.1.1 hgdeg (hsummand ap₀ hap₀)
    exact (hTnn ((hsummand ap₀ hap₀).isPFPolynomial
      hpf hfg.2.1.1).hasNonnegCoeffs).pos_leadingCoeff hinterl.1.1
  · rcases hex with ⟨ap, hap, hapos⟩
    exact ⟨(ap.1, T ap.2), List.mem_map.mpr ⟨ap, hap, rfl⟩, hapos⟩

/-- The PF linear-factor condition implies the PF Krein condition, provided
nonzero PF inputs have nonzero splitting images. -/
theorem preservesPFKreinInterlacingOnDegree_of_linearFactor
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {D : ℕ}
    (hTrr : ∀ ⦃p : ℝ[X]⦄, IsPFPolynomial p → p ≠ 0 →
      p.natDegree ≤ D → T p ≠ 0 ∧ (T p).Splits)
    (hTfactor : PreservesPFLinearFactorInterlacingOnDegree T D) :
    PreservesPFKreinInterlacingOnDegree T D := by
  intro g q hg hg0 hgdeg hq
  rcases hq with rfl | ⟨u, hfactor⟩
  · exact StrictInterl.refl (hTrr hg hg0 hgdeg).1 (hTrr hg hg0 hgdeg).2
  · have hq0 : q ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hfactor
      exact hg0 hfactor
    have hqpf : IsPFPolynomial q := hg.of_X_sub_C_mul_factor hfactor
    have hu_root : g.IsRoot u := by
      rw [Polynomial.IsRoot.def, hfactor, eval_mul, eval_sub, eval_X, eval_C]
      ring
    have hu_nonpos : u ≤ 0 :=
      hg.roots_nonpos u ((mem_roots hg0).mpr hu_root)
    have hfactor_deg : ((X + C (-u)) * q).natDegree ≤ D := by
      have hlin : (X + C (-u) : ℝ[X]) = X - C u := by
        simp [sub_eq_add_neg]
      rw [hlin, ← hfactor]
      exact hgdeg
    rw [hfactor]
    simpa [sub_eq_add_neg] using
      hTfactor hqpf hq0 (neg_nonneg.mpr hu_nonpos) hfactor_deg

/-- A PF shift chain supplies the one-linear-factor condition.  Linearity
identifies the shifted factor image with a nonnegative weighted sum of the
first two members of the chain. -/
theorem preservesPFLinearFactorInterlacingOnDegree_of_shift
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {D : ℕ}
    (hTnn : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTshift : PreservesPFShiftInterlacingOnDegree T D) :
    PreservesPFLinearFactorInterlacingOnDegree T D := by
  intro q a hq hq0 ha hdeg
  have hXqdeg : (X * q).natDegree ≤ D := by
    have hleft : (X * q).natDegree = q.natDegree + 1 := by
      rw [natDegree_mul X_ne_zero hq0, natDegree_X]
      lia
    have hright : ((X + C a) * q).natDegree = q.natDegree + 1 := by
      rw [natDegree_mul (X_add_C_ne_zero a) hq0, natDegree_X_add_C]
      lia
    rw [hleft, ← hright]
    exact hdeg
  have hstep : StrictInterl (T q) (T (X * q)) := by
    simpa using hTshift (q := q) (m := 0) hq hq0 (by simpa using hXqdeg)
  have hqnn : HasNonnegCoeffs (T q) := hTnn hq.hasNonnegCoeffs
  have hXqnn : HasNonnegCoeffs (T (X * q)) :=
    hTnn (isPFPolynomial_X.mul hq).hasNonnegCoeffs
  have hqpos : HasPosLeadingCoeff (T q) :=
    hqnn.pos_leadingCoeff hstep.1.1
  have hXqpos : HasPosLeadingCoeff (T (X * q)) :=
    hXqnn.pos_leadingCoeff hstep.2.1.1
  have hsum :
      StrictInterl (T q)
        (weightedSum [((1 : ℝ), T (X * q)), (a, T q)]) := by
    apply StrictInterl.weightedSum_left_of_common_left_signed
    · simp [ha]
    · intro ap hap
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hap
      rcases hap with rfl | rfl
      · exact hstep
      · exact StrictInterl.refl hstep.1.1 hstep.1.2
    · intro ap hap
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hap
      rcases hap with rfl | rfl
      · exact hXqpos
      · exact hqpos
    · exact ⟨((1 : ℝ), T (X * q)), by simp, zero_lt_one⟩
  have hinput : (X + C a) * q = X * q + a • q := by
    simp only [smul_eq_C_mul]
    ring
  rw [hinput, T.map_add, T.map_smul]
  simpa [weightedSum_cons, smul_eq_C_mul] using hsum

/-- Linear-factor form of the oriented interlacing upgrade.

For a concrete operator, this theorem leaves only three local obligations:
coefficientwise nonnegativity of the image, nonzero splitness preservation on
PF inputs, and the one-linear-factor interlacing step. -/
theorem strictInterl_map_of_pfLinearFactor
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {D : ℕ} {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hfdeg : f.natDegree ≤ D) (hgdeg : g.natDegree ≤ D)
    (hTnn : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTrr : ∀ ⦃p : ℝ[X]⦄, IsPFPolynomial p → p ≠ 0 →
      p.natDegree ≤ D → T p ≠ 0 ∧ (T p).Splits)
    (hTfactor : PreservesPFLinearFactorInterlacingOnDegree T D) :
    StrictInterl (T f) (T g) :=
  strictInterl_map_of_preservesPFKreinInterlacingOnDegree
    hfg hf hg hfdeg hgdeg hTnn
    (preservesPFKreinInterlacingOnDegree_of_linearFactor hTrr hTfactor)

/-- Shift-chain form of the oriented interlacing upgrade. -/
theorem strictInterl_map_of_pfShift
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {D : ℕ} {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hfdeg : f.natDegree ≤ D) (hgdeg : g.natDegree ≤ D)
    (hTnn : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTrr : ∀ ⦃p : ℝ[X]⦄, IsPFPolynomial p → p ≠ 0 →
      p.natDegree ≤ D → T p ≠ 0 ∧ (T p).Splits)
    (hTshift : PreservesPFShiftInterlacingOnDegree T D) :
    StrictInterl (T f) (T g) :=
  strictInterl_map_of_pfLinearFactor hfg hf hg hfdeg hgdeg hTnn hTrr
    (preservesPFLinearFactorInterlacingOnDegree_of_shift hTnn hTshift)

end RealRooted
