import RealRooted.GarloffWagner.Theorem12
import RealRooted.QuadraticInterlacingClosure

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

/-- The monomial chain extends through every PF factor.  Quadratic tangent
closure advances the two adjacent affine combinations; all remaining work is
algebraic PF factor induction. -/
theorem preservesPFShiftInterlacingOnDegree_of_monomials
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {D : ℕ}
    (hTnn : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTrr : ∀ ⦃p : ℝ[X]⦄, IsPFPolynomial p → p ≠ 0 →
      p.natDegree ≤ D → T p ≠ 0 ∧ (T p).Splits)
    (hmono : ∀ m : ℕ, m + 1 ≤ D →
      StrictInterl (T (X ^ m)) (T (X ^ (m + 1)))) :
    PreservesPFShiftInterlacingOnDegree T D := by
  let P : ℕ → Prop := fun n =>
    ∀ ⦃p : ℝ[X]⦄ ⦃m : ℕ⦄,
      IsPFPolynomial p → p ≠ 0 → p.natDegree = n →
      (X ^ (m + 1) * p).natDegree ≤ D →
      StrictInterl (T (X ^ m * p)) (T (X ^ (m + 1) * p))
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro p m hp hp0 hpdeg hbound
        by_cases hn0 : n = 0
        · have hpdeg0 : p.natDegree = 0 := hpdeg.trans hn0
          let c : ℝ := p.coeff 0
          have hpC : p = C c := by
            simpa [c] using Polynomial.eq_C_of_natDegree_eq_zero hpdeg0
          have hcpos : 0 < c := by
            have hp_pos : HasPosLeadingCoeff p :=
              hp.hasNonnegCoeffs.pos_leadingCoeff hp0
            change 0 < p.leadingCoeff at hp_pos
            rw [leadingCoeff, hpdeg0] at hp_pos
            exact hp_pos
          have hmD : m + 1 ≤ D := by
            have hpow0 : (X : ℝ[X]) ^ (m + 1) ≠ 0 :=
              pow_ne_zero _ X_ne_zero
            rw [natDegree_mul hpow0 hp0, natDegree_pow, natDegree_X,
              hpdeg0] at hbound
            simpa using hbound
          have hbase := hmono m hmD
          have hscaled :
              StrictInterl (C c * T (X ^ m))
                (C c * T (X ^ (m + 1))) :=
            StrictInterl.C_mul_right
              (StrictInterl.C_mul_left hbase hcpos.ne') hcpos.ne'
          have hleft : T (X ^ m * p) = C c * T (X ^ m) := by
            calc
              T (X ^ m * p) = T (C c * X ^ m) := by rw [hpC, mul_comm]
              _ = T (c • X ^ m) := by rw [Polynomial.smul_eq_C_mul]
              _ = c • T (X ^ m) := T.map_smul c (X ^ m)
              _ = C c * T (X ^ m) := by rw [Polynomial.smul_eq_C_mul]
          have hright :
              T (X ^ (m + 1) * p) = C c * T (X ^ (m + 1)) := by
            calc
              T (X ^ (m + 1) * p) = T (C c * X ^ (m + 1)) := by
                rw [hpC, mul_comm]
              _ = T (c • X ^ (m + 1)) := by
                rw [Polynomial.smul_eq_C_mul]
              _ = c • T (X ^ (m + 1)) := T.map_smul c (X ^ (m + 1))
              _ = C c * T (X ^ (m + 1)) := by
                rw [Polynomial.smul_eq_C_mul]
          rwa [hleft, hright]
        · have hpdeg_pos : 0 < p.natDegree := by
            rw [hpdeg]
            exact Nat.pos_of_ne_zero hn0
          obtain ⟨u, q, hu, hfactor, hq, hqdeg⟩ :=
            hp.exists_X_sub_C_factor_of_pos_natDegree hpdeg_pos
          have hq0 : q ≠ 0 := by
            intro hzero
            rw [hzero, mul_zero] at hfactor
            exact hp0 hfactor
          have hpdeg_succ : p.natDegree = q.natDegree + 1 := by
            rw [hfactor, natDegree_mul (X_sub_C_ne_zero u) hq0,
              natDegree_X_sub_C]
            lia
          have htotal : m + 2 + q.natDegree ≤ D := by
            have hpow0 : (X : ℝ[X]) ^ (m + 1) ≠ 0 :=
              pow_ne_zero _ X_ne_zero
            rw [natDegree_mul hpow0 hp0, natDegree_pow, natDegree_X,
              hpdeg_succ] at hbound
            simp only [mul_one] at hbound
            lia
          have hbound_m : (X ^ (m + 1) * q).natDegree ≤ D := by
            rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hq0,
              natDegree_pow, natDegree_X]
            simp only [mul_one]
            lia
          have hbound_succ :
              (X ^ ((m + 1) + 1) * q).natDegree ≤ D := by
            rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hq0,
              natDegree_pow, natDegree_X]
            simp only [mul_one]
            lia
          have hqn : q.natDegree < n := by
            rw [← hpdeg]
            exact hqdeg
          have hFG :
              StrictInterl (T (X ^ m * q))
                (T (X ^ (m + 1) * q)) :=
            ih q.natDegree hqn hq hq0 rfl hbound_m
          have hGH :
              StrictInterl (T (X ^ (m + 1) * q))
                (T (X ^ ((m + 1) + 1) * q)) :=
            ih q.natDegree hqn hq hq0 rfl hbound_succ
          let F : ℝ[X] := T (X ^ m * q)
          let G : ℝ[X] := T (X ^ (m + 1) * q)
          let H : ℝ[X] := T (X ^ (m + 2) * q)
          have hFnn : HasNonnegCoeffs F :=
            hTnn ((isPFPolynomial_X_pow m).mul hq).hasNonnegCoeffs
          have hGnn : HasNonnegCoeffs G :=
            hTnn ((isPFPolynomial_X_pow (m + 1)).mul hq).hasNonnegCoeffs
          have hHnn : HasNonnegCoeffs H :=
            hTnn ((isPFPolynomial_X_pow (m + 2)).mul hq).hasNonnegCoeffs
          have hFG' : StrictInterl F G := by simpa [F, G] using hFG
          have hGH' : StrictInterl G H := by
            simpa only [G, H, show (m + 1) + 1 = m + 2 by lia] using hGH
          have hfamily : ∀ b : ℝ, 0 ≤ b →
              (H + C (2 * b) * G + C (b ^ 2) * F).Splits := by
            intro b hb
            let r : ℝ[X] := X ^ m * (X + C b) ^ 2 * q
            have hrpf : IsPFPolynomial r :=
              ((isPFPolynomial_X_pow m).mul
                ((isPFPolynomial_X_add_C hb).pow 2)).mul hq
            have hr0 : r ≠ 0 := by
              exact mul_ne_zero
                (mul_ne_zero (pow_ne_zero _ X_ne_zero)
                  (pow_ne_zero _ (X_add_C_ne_zero b))) hq0
            have hrdeg : r.natDegree ≤ D := by
              dsimp [r]
              rw [natDegree_mul
                (mul_ne_zero (pow_ne_zero _ X_ne_zero)
                  (pow_ne_zero _ (X_add_C_ne_zero b))) hq0,
                natDegree_mul (pow_ne_zero _ X_ne_zero)
                  (pow_ne_zero _ (X_add_C_ne_zero b)),
                natDegree_pow, natDegree_X, natDegree_pow,
                natDegree_X_add_C]
              simp only [mul_one]
              lia
            have hr_split : (T r).Splits := (hTrr hrpf hr0 hrdeg).2
            have hr_expand :
                r = X ^ (m + 2) * q +
                    C (2 * b) * (X ^ (m + 1) * q) +
                    C (b ^ 2) * (X ^ m * q) := by
              dsimp [r]
              rw [show X ^ (m + 2) = X ^ m * X ^ 2 by
                exact pow_add X m 2,
                show X ^ (m + 1) = X ^ m * X by rw [pow_succ]]
              simp only [map_mul, map_pow, map_ofNat]
              ring
            have hmap :
                T r = H + C (2 * b) * G + C (b ^ 2) * F := by
              rw [hr_expand, T.map_add, T.map_add]
              rw [← Polynomial.smul_eq_C_mul, ← Polynomial.smul_eq_C_mul,
                T.map_smul, T.map_smul, Polynomial.smul_eq_C_mul,
                Polynomial.smul_eq_C_mul]
            rwa [← hmap]
          have ha : 0 ≤ -u := neg_nonneg.mpr hu
          have hAQ := strictInterl_quadraticInterlacingTangent_pencil
            hFnn hGnn hHnn hFG' hGH' hfamily ha
          have hAnn : HasNonnegCoeffs
              (quadraticInterlacingTangent F G (-u)) :=
            hGnn.add (nonnegCoeffs_C_mul ha hFnn)
          have hBnn : HasNonnegCoeffs
              (quadraticInterlacingRight G H (-u)) :=
            hHnn.add (nonnegCoeffs_C_mul ha hGnn)
          have hQnn : HasNonnegCoeffs
              (quadraticInterlacingPencil F G H (-u)) := by
            exact (hHnn.add (nonnegCoeffs_C_mul (mul_nonneg (by norm_num) ha) hGnn)).add
              (nonnegCoeffs_C_mul (sq_nonneg (-u)) hFnn)
          have hB0 : quadraticInterlacingRight G H (-u) ≠ 0 := by
            have hsum : C (-u) * G + H ≠ 0 :=
              add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
                (nonnegCoeffs_C_mul ha hGnn) hHnn hGH'.2.1.1
            simpa [quadraticInterlacingRight, add_comm] using hsum
          have hstep : StrictInterl
              (quadraticInterlacingTangent F G (-u))
              (quadraticInterlacingRight G H (-u)) :=
            strictInterl_quadraticInterlacingRight_of_tangent
              (hAnn.pos_leadingCoeff hAQ.1.1)
              (hBnn.pos_leadingCoeff hB0)
              (hQnn.pos_leadingCoeff hAQ.2.1.1) hAQ
          have hmap_factor : ∀ j : ℕ,
              T (X ^ j * p) =
                T (X ^ (j + 1) * q) + C (-u) * T (X ^ j * q) := by
            intro j
            have hpoly :
                X ^ j * p = X ^ (j + 1) * q + (-u) • (X ^ j * q) := by
              rw [hfactor, show X ^ (j + 1) = X ^ j * X by rw [pow_succ]]
              simp only [Polynomial.smul_eq_C_mul, map_neg]
              ring
            rw [hpoly, T.map_add, T.map_smul, Polynomial.smul_eq_C_mul]
          rw [hmap_factor m, hmap_factor (m + 1)]
          simpa only [quadraticInterlacingTangent, quadraticInterlacingRight,
            F, G, H, show (m + 1) + 1 = m + 2 by lia] using hstep
  intro p m hp hp0 hbound
  exact hP p.natDegree hp hp0 rfl hbound

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
      hpf).hasNonnegCoeffs).pos_leadingCoeff hinterl.1.1
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
