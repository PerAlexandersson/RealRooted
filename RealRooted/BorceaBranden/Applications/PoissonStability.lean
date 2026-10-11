import RealRooted.BorceaBranden.Applications.PoissonStar
import RealRooted.Hyperbolicity

/-!
# Stability of Poisson left multiplication

Left Poisson multiplication by a nonzero real stable `f(z, v)` with nonnegative coefficients
preserves real stability of every right input `g(z, v, x)`, of any degree and with any spectator
block `x` (`spectatorAction_stable`), and transports stable pencils (`spectatorAction_pencil`).  The
signed Weyl symbol of the action is `f(z(1 - w), v(1 - w))`, which is stable by homogenization, so
the finite-order Weyl-symbol theorem `BorceaBranden.finiteOrderWeylOperator_preserves_stability`
applies (Borcea--Brändén, *The Lee--Yang and Pólya--Schur programs. I*, Invent. Math. 177 (2009),
Theorems 1.3--1.4).  The left symbol must not contain unscaled stable parameters:
`not_stable_leftParameterBadSymbol` checks that `a + z(1 - w)` is not stable.
-/

open scoped BigOperators

namespace RealRooted.Poisson

noncomputable section

open RealRooted RealRooted.BorceaBranden

/-- The signed polynomial Weyl symbol `f(z(1-w),v(1-w))` over `ℂ`. -/
def poissonSymbol {τ : Type*} (f : MvPolynomial Bool ℂ) :
    MvPolynomial (Option (Bool ⊕ τ)) ℂ :=
  MvPolynomial.bind₁
    (fun i : Bool =>
      MvPolynomial.X (some (Sum.inl i)) *
        (1 - MvPolynomial.X none))
    f

/-- The signed polynomial Weyl symbol of a real left factor, with an
arbitrary spectator block included in the ambient variable type. -/
def poissonSymbolC {τ : Type*} (f : MvPolynomial Bool ℝ) :
    MvPolynomial (Option (Bool ⊕ τ)) ℂ :=
  poissonSymbol (complexifyMv f)

/-- The Poisson signed Weyl symbol is stable.  The common-rotation input used
here is the checked consequence of ordinary homogenization. -/
theorem poissonSymbolC_stable {τ : Type*} [Finite τ]
    {f : MvPolynomial Bool ℝ} (hf : MvRealStable f)
    (hnn : f.HasNonnegCoeffs) :
    MvUpperHalfPlaneStable (poissonSymbolC (τ := τ) f) := by
  have hrot := hf.commonRotationStable_complexify_of_hasNonnegCoeffs hnn
  intro u hu
  unfold poissonSymbolC poissonSymbol MvPolynomial.eval
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply hrot
  refine ⟨1 / (1 - u none), ?_, ?_⟩
  · have hneg : (1 / (u none - 1)).im < 0 :=
      Complex.one_div_sub_im_neg (by simpa using hu none)
    rw [show 1 - u none = -(u none - 1) by ring, one_div,
      inv_neg, Complex.neg_im]
    change 0 < -((u none - 1)⁻¹).im
    rw [one_div] at hneg
    exact neg_pos.mpr hneg
  · intro i
    have hden : 1 - u none ≠ 0 := by
      intro hzero
      have hone : u none = 1 := (sub_eq_zero.mp hzero).symm
      have := hu none
      rw [hone] at this
      norm_num at this
    have hcancel : (1 / (1 - u none)) *
        (u (some (Sum.inl i)) * (1 - u none)) = u (some (Sum.inl i)) := by
      field_simp
    simp only [map_mul, map_sub, map_one, MvPolynomial.eval₂Hom_X']
    change 0 < (1 / (1 - u none) *
      (u (some (Sum.inl i)) * (1 - u none))).im
    rw [hcancel]
    exact hu (some (Sum.inl i))

/-- The coefficient of the `j`-th derivative in the complex Poisson
operator. -/
def poissonWeylCoeffC {τ : Type*} (f : MvPolynomial Bool ℂ) (j : ℕ) :
    MvPolynomial (Bool ⊕ τ) ℂ :=
  f.coeff.sum fun d c =>
    MvPolynomial.C ((d false + d true).choose j : ℂ) *
      MvPolynomial.rename Sum.inl (MvPolynomial.monomial d c)

/-- The finite family of Weyl coefficients, truncated at `m`. -/
def poissonWeylFamilyC {τ : Type*} (m : ℕ)
    (f : MvPolynomial Bool ℂ) :
    Fin (m + 1) → MvPolynomial (Bool ⊕ τ) ℂ :=
  fun j => poissonWeylCoeffC f j

private theorem poissonWeylCoeffC_monomial {τ : Type*}
    (d : Bool →₀ ℕ) (c : ℂ) (j : ℕ) :
    poissonWeylCoeffC (τ := τ) (MvPolynomial.monomial d c) j =
      MvPolynomial.C ((d false + d true).choose j : ℂ) *
        MvPolynomial.rename Sum.inl (MvPolynomial.monomial d c) := by
  classical
  rw [poissonWeylCoeffC, MvPolynomial.sum_monomial_eq (by simp)]

private theorem poissonWeylCoeffC_add {τ : Type*}
    (f g : MvPolynomial Bool ℂ) (j : ℕ) :
    poissonWeylCoeffC (τ := τ) (f + g) j =
      poissonWeylCoeffC f j + poissonWeylCoeffC g j := by
  classical
  unfold poissonWeylCoeffC
  apply Finsupp.sum_add_index'
  · intro d
    simp
  · intro d a b
    simp only [map_add, mul_add]

private theorem actionAlong_add_left {R σ : Type*} [CommSemiring R]
    (ι : Bool → σ) (f g : MvPolynomial Bool R)
    (P : MvPolynomial σ R) :
    actionAlong ι (f + g) P =
      actionAlong ι f P + actionAlong ι g P := by
  classical
  unfold actionAlong
  apply Finsupp.sum_add_index'
  · intro d
    simp
  · intro d a b
    simp only [map_add, add_mul]

private theorem fin_sum_choose_of_le {σ : Type*} (n m : ℕ)
    (hnm : n ≤ m) (A : ℕ → MvPolynomial σ ℂ) :
    (∑ j : Fin (m + 1),
      MvPolynomial.C (n.choose (j : ℕ) : ℂ) * A j) =
      ∑ j ∈ Finset.range (n + 1),
        MvPolynomial.C (n.choose j : ℂ) * A j := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j => MvPolynomial.C (n.choose j : ℂ) * A j) (m + 1)]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hnm))
  intro j hjm hjn
  simp only [Finset.mem_range] at hjm hjn
  have hlt : n < j := by lia
  rw [Nat.choose_eq_zero_of_lt hlt]
  simp

private theorem finiteOrderWeylOperator_monomial_eq_action
    {τ : Type*} (d : Bool →₀ ℕ) (c : ℂ) (m : ℕ)
    (hdm : d false + d true ≤ m) (P : MvPolynomial (Bool ⊕ τ) ℂ) :
    finiteOrderWeylOperator (Sum.inl true) m
        (poissonWeylFamilyC (τ := τ) m (MvPolynomial.monomial d c)) P =
      actionAlong Sum.inl (MvPolynomial.monomial d c) P := by
  classical
  rw [finiteOrderWeylOperator, actionAlong,
    MvPolynomial.sum_monomial_eq (by simp)]
  simp only [poissonWeylFamilyC, poissonWeylCoeffC_monomial]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  have hsum := fin_sum_choose_of_le (d false + d true) m hdm
    (fun j =>
      MvPolynomial.rename Sum.inl (MvPolynomial.monomial d c) *
        iteratedPDerivAt (Sum.inl true) j P)
  calc
    (∑ j : Fin (m + 1),
        (MvPolynomial.C ((d false + d true).choose (j : ℕ) : ℂ) *
          MvPolynomial.rename Sum.inl (MvPolynomial.monomial d c)) *
            iteratedPDerivAt (Sum.inl true) j P) =
      ∑ j : Fin (m + 1),
        MvPolynomial.C ((d false + d true).choose (j : ℕ) : ℂ) *
          (MvPolynomial.rename Sum.inl (MvPolynomial.monomial d c) *
            iteratedPDerivAt (Sum.inl true) j P) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
    _ = ∑ j ∈ Finset.range (d false + d true + 1),
        MvPolynomial.C ((d false + d true).choose j : ℂ) *
          (MvPolynomial.rename Sum.inl (MvPolynomial.monomial d c) *
            iteratedPDerivAt (Sum.inl true) j P) := hsum
    _ = MvPolynomial.rename Sum.inl (MvPolynomial.monomial d c) *
        shiftDeriv (Sum.inl true) (d false + d true) P := by
      rw [shiftDeriv_eq_sum_iterated, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

private theorem bool_degree_eq (d : Bool →₀ ℕ) :
    d.sum (fun _ e => e) = d false + d true := by
  rw [Finsupp.sum_fintype d (fun _ e => e) (by simp), Fintype.sum_bool]
  rw [add_comm]

private theorem finiteOrderWeylOperator_eq_action {τ : Type*}
    (f : MvPolynomial Bool ℂ) (P : MvPolynomial (Bool ⊕ τ) ℂ) :
    finiteOrderWeylOperator (Sum.inl true) f.totalDegree
        (poissonWeylFamilyC (τ := τ) f.totalDegree f) P =
      actionAlong Sum.inl f P := by
  classical
  rw [finiteOrderWeylOperator, actionAlong]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, poissonWeylFamilyC,
    poissonWeylCoeffC, MvPolynomial.sum_def, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hdm : d false + d true ≤ f.totalDegree := by
    rw [← bool_degree_eq]
    exact MvPolynomial.le_totalDegree hd
  have hmono := finiteOrderWeylOperator_monomial_eq_action
    d (f.coeff d) f.totalDegree hdm P
  rw [finiteOrderWeylOperator, actionAlong,
    MvPolynomial.sum_monomial_eq (by simp)] at hmono
  simp only [LinearMap.coe_mk, AddHom.coe_mk, poissonWeylFamilyC,
    poissonWeylCoeffC_monomial] at hmono
  exact hmono

private theorem signed_binomial_sum {σ : Type*} (R W : MvPolynomial σ ℂ)
    (n m : ℕ) (hnm : n ≤ m) :
    (∑ j : Fin (m + 1),
        MvPolynomial.C (n.choose (j : ℕ) : ℂ) * R *
          MvPolynomial.C (-1 : ℂ) ^ (j : ℕ) * W ^ (j : ℕ)) =
      R * (1 - W) ^ n := by
  have hsum := fin_sum_choose_of_le n m hnm
    (fun j => R * (MvPolynomial.C (-1 : ℂ) ^ j * W ^ j))
  calc
    (∑ j : Fin (m + 1),
        MvPolynomial.C (n.choose (j : ℕ) : ℂ) * R *
          MvPolynomial.C (-1 : ℂ) ^ (j : ℕ) * W ^ (j : ℕ)) =
      ∑ j : Fin (m + 1), MvPolynomial.C (n.choose (j : ℕ) : ℂ) *
        (R * (MvPolynomial.C (-1 : ℂ) ^ (j : ℕ) *
          W ^ (j : ℕ))) := by
      apply Finset.sum_congr rfl
      intro j hj
      ac_rfl
    _ = ∑ j ∈ Finset.range (n + 1), MvPolynomial.C (n.choose j : ℂ) *
        (R * (MvPolynomial.C (-1 : ℂ) ^ j * W ^ j)) := hsum
    _ = R * (1 - W) ^ n := by
      rw [show 1 - W = -W + 1 by ring, add_pow]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [one_pow, mul_one, neg_pow]
      have hchoose :
          (MvPolynomial.C (n.choose j : ℂ) : MvPolynomial σ ℂ) =
            (n.choose j : MvPolynomial σ ℂ) := by
        rw [map_natCast]
      have hminus :
          (MvPolynomial.C (-1 : ℂ) : MvPolynomial σ ℂ) = -1 := by
        rw [map_neg, map_one]
      rw [hchoose, hminus]
      ac_rfl

private theorem signedWeylSymbol_monomial {τ : Type*}
    (d : Bool →₀ ℕ) (c : ℂ) (m : ℕ)
    (hdm : d false + d true ≤ m) :
    signedWeylSymbol m
        (poissonWeylFamilyC (τ := τ) m (MvPolynomial.monomial d c)) =
      poissonSymbol (τ := τ) (MvPolynomial.monomial d c) := by
  classical
  rw [signedWeylSymbol]
  simp only [poissonWeylFamilyC, poissonWeylCoeffC_monomial,
    map_mul, MvPolynomial.rename_C, MvPolynomial.rename_rename]
  rw [poissonSymbol, monomial_bool_eq]
  simp only [map_mul, map_pow, MvPolynomial.bind₁_C_right,
    MvPolynomial.bind₁_X_right, MvPolynomial.rename_X,
    Function.comp_apply]
  rw [MvPolynomial.rename_C]
  rw [signed_binomial_sum _ _ (d false + d true) m hdm]
  rw [mul_pow, mul_pow, pow_add]
  ac_rfl

/-- The signed Weyl symbol of the Poisson coefficient family is exactly
`f(z(1-w),v(1-w))`. -/
theorem signedWeylSymbol_poissonWeylFamilyC {τ : Type*}
    (f : MvPolynomial Bool ℂ) :
    signedWeylSymbol f.totalDegree
        (poissonWeylFamilyC (τ := τ) f.totalDegree f) =
      poissonSymbol (τ := τ) f := by
  classical
  rw [signedWeylSymbol, poissonSymbol]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff f]
  simp only [map_sum, poissonWeylFamilyC, poissonWeylCoeffC,
    MvPolynomial.sum_def, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hdm : d false + d true ≤ f.totalDegree := by
    rw [← bool_degree_eq]
    exact MvPolynomial.le_totalDegree hd
  have hmono := signedWeylSymbol_monomial (τ := τ)
    d (f.coeff d) f.totalDegree hdm
  rw [signedWeylSymbol, poissonSymbol] at hmono
  simp only [poissonWeylFamilyC, poissonWeylCoeffC_monomial] at hmono
  exact hmono

private theorem shiftDeriv_complexify {σ : Type*} (q : σ) (n : ℕ)
    (P : MvPolynomial σ ℝ) :
    complexifyMv (shiftDeriv q n P) =
      shiftDeriv q n (complexifyMv P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [complexifyMv] at ih
      have hreal : shiftDeriv q (n + 1) P =
          MvPolynomial.pderiv q (shiftDeriv q n P) +
            shiftDeriv q n P := by
        rw [shiftDeriv, pow_succ', Module.End.mul_apply]
        rfl
      have hcomplex : shiftDeriv q (n + 1) (complexifyMv P) =
          MvPolynomial.pderiv q (shiftDeriv q n (complexifyMv P)) +
            shiftDeriv q n (complexifyMv P) := by
        rw [shiftDeriv, pow_succ', Module.End.mul_apply]
        rfl
      rw [hreal, hcomplex, complexifyMv, map_add,
        ← MvPolynomial.pderiv_map]
      rw [ih]

private theorem complexify_actionAlong {σ : Type*} (ι : Bool → σ)
    (f : MvPolynomial Bool ℝ) (P : MvPolynomial σ ℝ) :
    complexifyMv (actionAlong ι f P) =
      actionAlong ι (complexifyMv f) (complexifyMv P) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d c =>
      have hs := shiftDeriv_complexify (ι true) (d false + d true) P
      rw [complexifyMv] at hs
      have hm : complexifyMv (MvPolynomial.monomial d c) =
          MvPolynomial.monomial d (Complex.ofRealHom c) := by
        rw [complexifyMv, MvPolynomial.map_monomial]
      rw [actionAlong, MvPolynomial.sum_monomial_eq (by simp)]
      rw [complexifyMv, map_mul, MvPolynomial.map_rename,
        MvPolynomial.map_monomial, hs]
      rw [hm]
      rw [actionAlong, MvPolynomial.sum_monomial_eq (by simp)]
  | add f g hf hg =>
      rw [complexifyMv] at hf hg ⊢
      rw [actionAlong_add_left, map_add, hf, hg]
      have hfg : complexifyMv (f + g) =
          complexifyMv f + complexifyMv g := by
        unfold complexifyMv
        rw [map_add]
      rw [hfg, actionAlong_add_left]

/-- Complexification commutes with Poisson action on a real right input. -/
theorem complexify_spectatorAction {τ : Type*}
    (f : MvPolynomial Bool ℝ) (P : MvPolynomial (Bool ⊕ τ) ℝ) :
    complexifyMv (spectatorAction f P) =
      actionAlong Sum.inl (complexifyMv f) (complexifyMv P) := by
  exact complexify_actionAlong Sum.inl f P

/-- Poisson left multiplication preserves real stability up to the possible
zero output. -/
theorem spectatorAction_stableOrZero {τ : Type*} [Finite τ]
    {f : MvPolynomial Bool ℝ} (hf : MvRealStable f)
    (hnn : f.HasNonnegCoeffs) {P : MvPolynomial (Bool ⊕ τ) ℝ}
    (hP : MvRealStable P) :
    MvRealStableOrZero (spectatorAction f P) := by
  rw [mvRealStableOrZero_iff_complexifyMv, complexify_spectatorAction,
    ← finiteOrderWeylOperator_eq_action]
  apply finiteOrderWeylOperator_preserves_stability
  · rw [signedWeylSymbol_poissonWeylFamilyC]
    exact poissonSymbolC_stable hf hnn
  · exact hP

/-- The positive-order part of the binomial shift derivative. -/
def shiftRemainder {σ : Type*} (q : σ) (n : ℕ)
    (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ j ∈ Finset.range n,
    MvPolynomial.C (n.choose (j + 1) : ℝ) *
      iteratedPDerivAt q (j + 1) P

private theorem shiftDeriv_eq_add_remainder {σ : Type*}
    (q : σ) (n : ℕ) (P : MvPolynomial σ ℝ) :
    shiftDeriv q n P = P + shiftRemainder q n P := by
  rw [shiftDeriv_eq_sum_iterated, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, MvPolynomial.C_1,
    iteratedPDerivAt, one_mul]
  rw [add_comm]
  rfl

private theorem shiftRemainder_nonneg {σ : Type*} (q : σ) (n : ℕ)
    {P : MvPolynomial σ ℝ} (hP : P.HasNonnegCoeffs) :
    (shiftRemainder q n P).HasNonnegCoeffs := by
  unfold shiftRemainder
  apply MvPolynomial.HasNonnegCoeffs.sum
  intro j hj
  apply MvPolynomial.HasNonnegCoeffs.mul
  · exact MvPolynomial.HasNonnegCoeffs.C (Nat.cast_nonneg _)
  · exact iteratedPDerivAt_nonneg hP q (j + 1)

/-- The part of the Poisson action containing at least one derivative. -/
def actionRemainder {σ : Type*} (ι : Bool → σ)
    (f : MvPolynomial Bool ℝ) (P : MvPolynomial σ ℝ) :
    MvPolynomial σ ℝ :=
  f.coeff.sum fun d c =>
    MvPolynomial.rename ι (MvPolynomial.monomial d c) *
      shiftRemainder (ι true) (d false + d true) P

private theorem actionAlong_eq_mul_add_remainder {σ : Type*}
    (ι : Bool → σ) (f : MvPolynomial Bool ℝ) (P : MvPolynomial σ ℝ) :
    actionAlong ι f P =
      MvPolynomial.rename ι f * P + actionRemainder ι f P := by
  classical
  unfold actionAlong actionRemainder
  rw [MvPolynomial.sum_def, MvPolynomial.sum_def]
  conv_lhs =>
    enter [2, d]
    rw [shiftDeriv_eq_add_remainder, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_mul]
  congr 1
  rw [← map_sum, MvPolynomial.support_sum_monomial_coeff]

private theorem actionRemainder_nonneg {σ : Type*} (ι : Bool → σ)
    (hι : Function.Injective ι) {f : MvPolynomial Bool ℝ}
    (hf : f.HasNonnegCoeffs) {P : MvPolynomial σ ℝ}
    (hP : P.HasNonnegCoeffs) :
    (actionRemainder ι f P).HasNonnegCoeffs := by
  classical
  unfold actionRemainder
  rw [MvPolynomial.sum_def]
  apply MvPolynomial.HasNonnegCoeffs.sum
  intro d hd
  apply MvPolynomial.HasNonnegCoeffs.mul
  · exact (hasNonnegCoeffs_monomial d (hf d)).rename_of_injective hι
  · exact shiftRemainder_nonneg (ι true) (d false + d true) hP

private theorem add_ne_zero_of_nonnegative {σ : Type*}
    {P Q : MvPolynomial σ ℝ} (hP : P.HasNonnegCoeffs)
    (hP0 : P ≠ 0) (hQ : Q.HasNonnegCoeffs) : P + Q ≠ 0 := by
  intro hzero
  have hpos := hP.eval_pos hP0 (fun _ => zero_lt_one)
  have hnonneg := hQ.eval_nonneg (fun _ => zero_le_one)
  have heval := congrArg (MvPolynomial.eval fun _ => 1) hzero
  simp only [map_add, map_zero] at heval
  linarith

/-- If the right input also has nonnegative coefficients, Poisson left
multiplication is nonzero and real stable. -/
theorem spectatorAction_stable_of_nonneg {τ : Type*} [Finite τ]
    {f : MvPolynomial Bool ℝ} (hf : MvRealStable f)
    (hfnn : f.HasNonnegCoeffs) {P : MvPolynomial (Bool ⊕ τ) ℝ}
    (hP : MvRealStable P) (hPnn : P.HasNonnegCoeffs) :
    MvRealStable (spectatorAction f P) := by
  have hweak := spectatorAction_stableOrZero hf hfnn hP
  rcases hweak with hzero | hstable
  · exfalso
    have hfrename :
        MvPolynomial.rename (Sum.inl : Bool → Bool ⊕ τ) f ≠ 0 := by
      exact fun hz => hf.ne_zero
        (MvPolynomial.rename_injective
          (Sum.inl : Bool → Bool ⊕ τ) Sum.inl_injective hz)
    have hprod0 :
        MvPolynomial.rename (Sum.inl : Bool → Bool ⊕ τ) f * P ≠ 0 :=
      mul_ne_zero hfrename hP.ne_zero
    have hprodnn := hfnn.rename_of_injective Sum.inl_injective |>.mul hPnn
    have hremnn := actionRemainder_nonneg Sum.inl Sum.inl_injective hfnn hPnn
    have hne := add_ne_zero_of_nonnegative hprodnn hprod0 hremnn
    rw [← actionAlong_eq_mul_add_remainder, ← spectatorAction] at hne
    exact hne hzero
  · exact hstable

/-- With nonnegative inputs, Poisson left multiplication retains
nonnegative coefficients as well as real stability. -/
theorem spectatorAction_closed {τ : Type*} [Finite τ]
    {f : MvPolynomial Bool ℝ} (hf : MvRealStable f)
    (hfnn : f.HasNonnegCoeffs) {P : MvPolynomial (Bool ⊕ τ) ℝ}
    (hP : MvRealStable P) (hPnn : P.HasNonnegCoeffs) :
    MvRealStable (spectatorAction f P) ∧
      (spectatorAction f P).HasNonnegCoeffs := by
  exact ⟨spectatorAction_stable_of_nonneg hf hfnn hP hPnn,
    actionAlong_nonneg Sum.inl Sum.inl_injective hfnn hPnn⟩

private theorem totalDegree_pderiv_add_one_le {σ : Type*}
    {P : MvPolynomial σ ℝ} (q : σ)
    (hD : MvPolynomial.pderiv q P ≠ 0) :
    (MvPolynomial.pderiv q P).totalDegree + 1 ≤ P.totalDegree := by
  classical
  unfold MvPolynomial.totalDegree
  rw [Finset.sup_add (MvPolynomial.support_nonempty.mpr hD)]
  apply Finset.sup_le
  intro d hd
  have hcoeff : (MvPolynomial.pderiv q P).coeff d ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.coeff_pderiv] at hcoeff
  have hPcoeff : P.coeff (d + Finsupp.single q 1) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hcoeff
    exact hcoeff rfl
  have hmem : d + Finsupp.single q 1 ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr hPcoeff
  calc
    d.sum (fun _ e => e) + 1 =
        (d + Finsupp.single q 1).sum (fun _ e => e) := by
      simp [Finsupp.sum_add_index]
    _ ≤ P.support.sup (fun s => s.sum fun _ e => e) :=
      Finset.le_sup (f := fun s => s.sum fun _ e => e) hmem

private theorem totalDegree_iteratedPDerivAt_add_le {σ : Type*}
    (q : σ) (j : ℕ) {P : MvPolynomial σ ℝ}
    (hD : iteratedPDerivAt q j P ≠ 0) :
    (iteratedPDerivAt q j P).totalDegree + j ≤ P.totalDegree := by
  induction j with
  | zero =>
      simpa only [iteratedPDerivAt, add_zero] using
        (le_refl P.totalDegree)
  | succ j ih =>
      change MvPolynomial.pderiv q (iteratedPDerivAt q j P) ≠ 0 at hD
      have hprev : iteratedPDerivAt q j P ≠ 0 := by
        intro hzero
        apply hD
        rw [hzero, map_zero]
      have hstep := totalDegree_pderiv_add_one_le q hD
      have hrest := ih hprev
      change (MvPolynomial.pderiv q
        (iteratedPDerivAt q j P)).totalDegree + (j + 1) ≤ P.totalDegree
      lia

private theorem shiftRemainder_totalDegree_le {σ : Type*}
    (q : σ) (n : ℕ) (P : MvPolynomial σ ℝ) :
    (shiftRemainder q n P).totalDegree ≤ P.totalDegree - 1 := by
  classical
  unfold shiftRemainder
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  by_cases hD : iteratedPDerivAt q (j + 1) P = 0
  · simp only [hD, MvPolynomial.totalDegree_C,
      MvPolynomial.totalDegree_zero, add_zero, zero_le]
  · have hdegree := totalDegree_iteratedPDerivAt_add_le q (j + 1) hD
    simp only [MvPolynomial.totalDegree_C, zero_add]
    lia

private theorem rename_inl_totalDegree_eq {τ : Type*}
    (f : MvPolynomial Bool ℝ) :
    (MvPolynomial.rename (Sum.inl : Bool → Bool ⊕ τ) f).totalDegree =
      f.totalDegree := by
  let leftInverse : Bool ⊕ τ → Bool := Sum.elim id (fun _ => false)
  have hrename : MvPolynomial.rename leftInverse
      (MvPolynomial.rename (Sum.inl : Bool → Bool ⊕ τ) f) = f := by
    rw [MvPolynomial.rename_rename]
    have hcomp : leftInverse ∘ (Sum.inl : Bool → Bool ⊕ τ) = id := rfl
    rw [hcomp, MvPolynomial.rename_id]
    rfl
  apply le_antisymm
  · exact MvPolynomial.totalDegree_rename_le Sum.inl f
  · have hle := MvPolynomial.totalDegree_rename_le leftInverse
        (MvPolynomial.rename (Sum.inl : Bool → Bool ⊕ τ) f)
    rw [hrename] at hle
    exact hle

private theorem actionRemainder_totalDegree_le {τ : Type*}
    (f : MvPolynomial Bool ℝ) (P : MvPolynomial (Bool ⊕ τ) ℝ)
    (hPdeg : 0 < P.totalDegree) :
    (actionRemainder Sum.inl f P).totalDegree ≤
      f.totalDegree + P.totalDegree - 1 := by
  classical
  unfold actionRemainder
  rw [MvPolynomial.sum_def]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hdleft :
      (MvPolynomial.rename (Sum.inl : Bool → Bool ⊕ τ)
        (MvPolynomial.monomial d (f.coeff d))).totalDegree ≤
        f.totalDegree := by
    refine (MvPolynomial.totalDegree_rename_le Sum.inl _).trans ?_
    refine (MvPolynomial.totalDegree_monomial_le d (f.coeff d)).trans ?_
    simpa only [Function.id_def] using MvPolynomial.le_totalDegree hd
  have hdright := shiftRemainder_totalDegree_le
    (Sum.inl true : Bool ⊕ τ) (d false + d true) P
  calc
    (MvPolynomial.rename Sum.inl
          (MvPolynomial.monomial d (f.coeff d))).totalDegree +
        (shiftRemainder (Sum.inl true) (d false + d true) P).totalDegree ≤
      f.totalDegree + (P.totalDegree - 1) :=
        Nat.add_le_add hdleft hdright
    _ = f.totalDegree + P.totalDegree - 1 := by lia

private theorem iteratedPDerivAt_C_succ {σ : Type*} (q : σ)
    (j : ℕ) (c : ℝ) :
    iteratedPDerivAt q (j + 1) (MvPolynomial.C c) = 0 := by
  induction j with
  | zero =>
      rw [iteratedPDerivAt, iteratedPDerivAt,
        MvPolynomial.pderiv_C]
  | succ j ih =>
      rw [iteratedPDerivAt]
      rw [ih, map_zero]

private theorem shiftRemainder_C {σ : Type*} (q : σ) (n : ℕ) (c : ℝ) :
    shiftRemainder q n (MvPolynomial.C c) = 0 := by
  unfold shiftRemainder
  apply Finset.sum_eq_zero
  intro j hj
  rw [iteratedPDerivAt_C_succ, mul_zero]

private theorem actionRemainder_C {τ : Type*}
    (f : MvPolynomial Bool ℝ) (c : ℝ) :
    actionRemainder (Sum.inl : Bool → Bool ⊕ τ) f
      (MvPolynomial.C c) = 0 := by
  classical
  unfold actionRemainder
  rw [MvPolynomial.sum_def]
  apply Finset.sum_eq_zero
  intro d hd
  rw [shiftRemainder_C, mul_zero]

private theorem spectatorAction_ne_zero {τ : Type*}
    {f : MvPolynomial Bool ℝ} (hf : f ≠ 0)
    {P : MvPolynomial (Bool ⊕ τ) ℝ} (hP : P ≠ 0) :
    spectatorAction f P ≠ 0 := by
  have hfrename :
      MvPolynomial.rename (Sum.inl : Bool → Bool ⊕ τ) f ≠ 0 := by
    exact fun hz => hf
      (MvPolynomial.rename_injective
        (Sum.inl : Bool → Bool ⊕ τ) Sum.inl_injective hz)
  have hprod : MvPolynomial.rename Sum.inl f * P ≠ 0 :=
    mul_ne_zero hfrename hP
  have hproddeg : (MvPolynomial.rename Sum.inl f * P).totalDegree =
      f.totalDegree + P.totalDegree := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain hfrename hP,
      rename_inl_totalDegree_eq]
  rw [spectatorAction, actionAlong_eq_mul_add_remainder]
  by_cases hPdeg : P.totalDegree = 0
  · have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hPdeg
    rw [hc] at hprod ⊢
    rw [actionRemainder_C, add_zero]
    exact hprod
  · have hPdegpos : 0 < P.totalDegree := Nat.pos_of_ne_zero hPdeg
    by_cases hrem : actionRemainder Sum.inl f P = 0
    · rw [hrem, add_zero]
      exact hprod
    · have hremdeg := actionRemainder_totalDegree_le f P hPdegpos
      have hlt : (actionRemainder Sum.inl f P).totalDegree <
          (MvPolynomial.rename Sum.inl f * P).totalDegree := by
        rw [hproddeg]
        lia
      intro hzero
      have hdegree :=
        MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt hlt
      rw [hzero, MvPolynomial.totalDegree_zero, hproddeg] at hdegree
      lia

/-- Left Poisson multiplication by a nonzero stable polynomial with
nonnegative coefficients preserves real stability for arbitrary stable right
inputs. -/
theorem spectatorAction_stable {τ : Type*} [Finite τ]
    {f : MvPolynomial Bool ℝ} (hf : MvRealStable f)
    (hfnn : f.HasNonnegCoeffs) {P : MvPolynomial (Bool ⊕ τ) ℝ}
    (hP : MvRealStable P) :
    MvRealStable (spectatorAction f P) := by
  rcases spectatorAction_stableOrZero hf hfnn hP with hzero | hstable
  · exact False.elim (spectatorAction_ne_zero hf.ne_zero hP.ne_zero hzero)
  · exact hstable

private theorem shiftDeriv_add {R σ : Type*} [CommSemiring R]
    (q : σ) (n : ℕ) (P Q : MvPolynomial σ R) :
    shiftDeriv q n (P + Q) = shiftDeriv q n P + shiftDeriv q n Q := by
  unfold shiftDeriv
  exact map_add _ P Q

private theorem actionAlong_add_right {R σ : Type*} [CommSemiring R]
    (ι : Bool → σ) (f : MvPolynomial Bool R)
    (P Q : MvPolynomial σ R) :
    actionAlong ι f (P + Q) = actionAlong ι f P + actionAlong ι f Q := by
  classical
  unfold actionAlong
  rw [MvPolynomial.sum_def, MvPolynomial.sum_def,
    MvPolynomial.sum_def]
  conv_lhs =>
    enter [2, d]
    rw [shiftDeriv_add, mul_add]
  rw [Finset.sum_add_distrib]

private theorem shiftDeriv_X_mul_of_ne {R σ : Type*} [CommSemiring R]
    (q r : σ) (hqr : q ≠ r) (n : ℕ) (P : MvPolynomial σ R) :
    shiftDeriv q n (MvPolynomial.X r * P) =
      MvPolynomial.X r * shiftDeriv q n P := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hleft : shiftDeriv q (n + 1) (MvPolynomial.X r * P) =
          MvPolynomial.pderiv q
              (shiftDeriv q n (MvPolynomial.X r * P)) +
            shiftDeriv q n (MvPolynomial.X r * P) := by
        rw [shiftDeriv, pow_succ', Module.End.mul_apply]
        rfl
      have hright : shiftDeriv q (n + 1) P =
          MvPolynomial.pderiv q (shiftDeriv q n P) +
            shiftDeriv q n P := by
        rw [shiftDeriv, pow_succ', Module.End.mul_apply]
        rfl
      rw [hleft, hright, ih, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_X_of_ne (i := q) (j := r) (Ne.symm hqr)]
      ring

private theorem actionAlong_X_mul_of_ne {R σ : Type*} [CommSemiring R]
    (ι : Bool → σ) (f : MvPolynomial Bool R) (r : σ)
    (hr : ι true ≠ r) (P : MvPolynomial σ R) :
    actionAlong ι f (MvPolynomial.X r * P) =
      MvPolynomial.X r * actionAlong ι f P := by
  classical
  unfold actionAlong
  rw [MvPolynomial.sum_def, MvPolynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [shiftDeriv_X_mul_of_ne (ι true) r hr]
  ring

/-- Poisson action transports a stable pencil in any spectator variable. -/
theorem spectatorAction_pencil {τ : Type*} [Finite τ]
    {f : MvPolynomial Bool ℝ} (hf : MvRealStable f)
    (hfnn : f.HasNonnegCoeffs) (x : τ)
    {G H : MvPolynomial (Bool ⊕ τ) ℝ}
    (hpencil : MvRealStable
      (G + MvPolynomial.X (Sum.inr x) * H)) :
    MvRealStable
      (spectatorAction f G +
        MvPolynomial.X (Sum.inr x) * spectatorAction f H) := by
  have hstable := spectatorAction_stable hf hfnn hpencil
  rw [spectatorAction, actionAlong_add_right,
    actionAlong_X_mul_of_ne Sum.inl f (Sum.inr x) (by simp)] at hstable
  exact hstable

/-- The false extension in which a live left parameter is treated as a
spectator has a concrete upper-half-plane zero. -/
def leftParameterBadSymbol : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.X 0 +
    MvPolynomial.X 1 * (1 - MvPolynomial.X 2)

/-- `a + z(1-w)` is not stable: it vanishes at
`a=-2+2i`, `z=1+i`, `w=1+2i`. -/
theorem not_stable_leftParameterBadSymbol :
    ¬MvUpperHalfPlaneStable leftParameterBadSymbol := by
  intro hstable
  let u : Fin 3 → ℂ := fun i =>
    if i = 0 then -2 + 2 * Complex.I
    else if i = 1 then 1 + Complex.I
    else 1 + 2 * Complex.I
  have hu : ∀ i, 0 < (u i).im := by
    intro i
    fin_cases i <;> norm_num [u]
  have hne := hstable u hu
  apply hne
  simp only [leftParameterBadSymbol, MvPolynomial.eval_add,
    MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_sub,
    map_one]
  change (-2 + 2 * Complex.I) +
    (1 + Complex.I) * (1 - (1 + 2 * Complex.I)) = 0
  rw [show 1 - (1 + 2 * Complex.I) = -2 * Complex.I by ring]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  norm_num

end

end RealRooted.Poisson
