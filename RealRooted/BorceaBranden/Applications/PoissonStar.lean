import RealRooted.BorceaBranden.FiniteOrderWeylPreserver
import RealRooted.Mathlib.Algebra.MvPolynomial.Nonnegative

/-!
# The Poisson star algebra

This file develops the algebraic part of the Poisson star product
`f ⋆ g = ∑_{a,b} f_{a,b} z^a v^b (1 + ∂_v)^{a+b} g`.  The two distinguished variables are indexed
by `Bool`: `false` is `z` and `true` is `v`.  A right input may additionally use an arbitrary
spectator block `τ`.  We prove the monomial law, coefficientwise nonnegativity, the products
`v ⋆ z = z v` and `z ⋆ v = z v + z`, the units, `T_f ∘ T_g = T_(f ⋆ g)`, and associativity
(`star_assoc`).
-/

open scoped BigOperators

namespace RealRooted.Poisson

noncomputable section

open RealRooted

/-- The distinguished `z` variable. -/
abbrev z {R : Type*} [CommSemiring R] : MvPolynomial Bool R :=
  MvPolynomial.X false

/-- The distinguished `v` variable. -/
abbrev v {R : Type*} [CommSemiring R] : MvPolynomial Bool R :=
  MvPolynomial.X true

/-- The linear operator `1 + partial_q`. -/
def shiftMap {R σ : Type*} [CommSemiring R] (q : σ) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (MvPolynomial.pderiv q).toLinearMap + 1

/-- Apply `(1 + partial_q)^n`. -/
def shiftDeriv {R σ : Type*} [CommSemiring R] (q : σ) (n : ℕ)
    (P : MvPolynomial σ R) : MvPolynomial σ R :=
  (shiftMap q ^ n) P

/-- The Poisson operator attached to a polynomial in `z,v`, acting along an
injective choice of those two variables in a larger polynomial ring. -/
def actionAlong {R σ : Type*} [CommSemiring R] (ι : Bool → σ)
    (f : MvPolynomial Bool R) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  f.coeff.sum fun d c =>
    MvPolynomial.rename ι (MvPolynomial.monomial d c) *
      shiftDeriv (ι true) (d false + d true) P

/-- The Poisson star product `f star g = T_f(g)`. -/
def star {R : Type*} [CommSemiring R]
    (f g : MvPolynomial Bool R) : MvPolynomial Bool R :=
  actionAlong id f g

/-- Left Poisson multiplication with an arbitrary spectator block on the
right. -/
def spectatorAction {R τ : Type*} [CommSemiring R]
    (f : MvPolynomial Bool R) (P : MvPolynomial (Bool ⊕ τ) R) :
    MvPolynomial (Bool ⊕ τ) R :=
  actionAlong Sum.inl f P

@[simp] theorem iteratedPDerivAt_monomial
    {R σ : Type*} [CommSemiring R] (q : σ) (j : ℕ)
    (d : σ →₀ ℕ) (c : R) :
    iteratedPDerivAt q j (MvPolynomial.monomial d c) =
      MvPolynomial.monomial (d - Finsupp.single q j)
        ((d q).descFactorial j * c) := by
  induction j with
  | zero =>
      simp only [iteratedPDerivAt, Finsupp.single_zero,
        Nat.descFactorial_zero, Nat.cast_one, one_mul]
      have hzero : d - (0 : σ →₀ ℕ) = d := by
        ext i
        simp
      rw [hzero]
  | succ j ih =>
      rw [iteratedPDerivAt, ih, MvPolynomial.pderiv_monomial]
      have hsub : d - Finsupp.single q j - Finsupp.single q 1 =
          d - Finsupp.single q (j + 1) := by
        ext i
        by_cases hi : i = q
        · subst i
          simp [Nat.sub_sub]
        · simp [hi]
      rw [hsub]
      have hq : (d - Finsupp.single q j) q = d q - j := by simp
      rw [hq, Nat.descFactorial_succ, Nat.cast_mul]
      ring_nf

/-- Explicit monomial formula for the binomial shift-derivative operator. -/
theorem shiftDeriv_monomial {R σ : Type*} [CommSemiring R]
    (q : σ) (n : ℕ) (d : σ →₀ ℕ) (c : R) :
    shiftDeriv q n (MvPolynomial.monomial d c) =
      ∑ j ∈ Finset.range (n + 1),
        MvPolynomial.monomial (d - Finsupp.single q j)
          ((n.choose j : R) * (d q).descFactorial j * c) := by
  rw [shiftDeriv, shiftMap,
    Commute.add_pow (Commute.one_right (MvPolynomial.pderiv q).toLinearMap)]
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Module.End.mul_apply, one_pow, mul_one]
  change ((MvPolynomial.pderiv q).toLinearMap ^ j)
      (n.choose j • MvPolynomial.monomial d c) = _
  rw [map_nsmul, iteratedPDerivAt_eq_pow, iteratedPDerivAt_monomial]
  rw [nsmul_eq_mul]
  change MvPolynomial.C (n.choose j : R) *
      MvPolynomial.monomial (d - Finsupp.single q j)
        ((d q).descFactorial j * c) = _
  rw [MvPolynomial.C_mul_monomial]
  rw [mul_assoc]

/-- Expand the binomial shift derivative into ordinary iterated
derivatives. -/
theorem shiftDeriv_eq_sum_iterated {R σ : Type*} [CommSemiring R]
    (q : σ) (n : ℕ) (P : MvPolynomial σ R) :
    shiftDeriv q n P =
      ∑ j ∈ Finset.range (n + 1),
        MvPolynomial.C (n.choose j : R) * iteratedPDerivAt q j P := by
  rw [shiftDeriv, shiftMap,
    Commute.add_pow (Commute.one_right (MvPolynomial.pderiv q).toLinearMap)]
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Module.End.mul_apply, one_pow, mul_one]
  change ((MvPolynomial.pderiv q).toLinearMap ^ j)
      (n.choose j • P) = _
  rw [map_nsmul, iteratedPDerivAt_eq_pow, nsmul_eq_mul]
  change MvPolynomial.C (n.choose j : R) * iteratedPDerivAt q j P = _
  rfl

private theorem bidegree_apply_false (a b : ℕ) :
    (Finsupp.single false a + Finsupp.single true b : Bool →₀ ℕ) false = a := by
  simp

private theorem bidegree_apply_true (a b : ℕ) :
    (Finsupp.single false a + Finsupp.single true b : Bool →₀ ℕ) true = b := by
  simp

/-- The monomial `c z^a v^b`, in sparse-exponent form. -/
def zvMonomial {R : Type*} [CommSemiring R] (a b : ℕ) (c : R) :
    MvPolynomial Bool R :=
  MvPolynomial.monomial
    (Finsupp.single false a + Finsupp.single true b) c

@[simp] theorem zvMonomial_one {R : Type*} [CommSemiring R] :
    zvMonomial 0 0 (1 : R) = 1 := by
  ext d
  simp [zvMonomial]

@[simp] theorem zvMonomial_zero {R : Type*} [CommSemiring R] (a b : ℕ) :
    zvMonomial a b (0 : R) = 0 := by
  simp [zvMonomial]

@[simp] theorem zvMonomial_z {R : Type*} [CommSemiring R] :
    zvMonomial 1 0 (1 : R) = z := by
  rw [zvMonomial]
  have he : (Finsupp.single false 1 + Finsupp.single true 0 : Bool →₀ ℕ) =
      Finsupp.single false 1 := by
    ext i
    cases i <;> simp
  rw [he, ← MvPolynomial.X_pow_eq_monomial]
  simp only [pow_one]

@[simp] theorem zvMonomial_v {R : Type*} [CommSemiring R] :
    zvMonomial 0 1 (1 : R) = v := by
  rw [zvMonomial]
  have he : (Finsupp.single false 0 + Finsupp.single true 1 : Bool →₀ ℕ) =
      Finsupp.single true 1 := by
    ext i
    cases i <;> simp
  rw [he, ← MvPolynomial.X_pow_eq_monomial]
  simp only [pow_one]

private theorem bidegree_sub_v (a b j : ℕ) :
    (Finsupp.single false a + Finsupp.single true b : Bool →₀ ℕ) -
        Finsupp.single true j =
      Finsupp.single false a + Finsupp.single true (b - j) := by
  ext i
  cases i <;> simp

/-- The Poisson product of two monomials. -/
theorem star_zvMonomial {R : Type*} [CommSemiring R]
    (a b c d : ℕ) (r s : R) :
    star (zvMonomial a b r) (zvMonomial c d s) =
      ∑ j ∈ Finset.range (a + b + 1),
        zvMonomial (a + c) (b + d - j)
          ((a + b).choose j * d.descFactorial j * (r * s)) := by
  classical
  rw [star]
  change actionAlong id
      (MvPolynomial.monomial
        (Finsupp.single false a + Finsupp.single true b) r)
      (zvMonomial c d s) = _
  rw [actionAlong, MvPolynomial.sum_monomial_eq (by simp)]
  simp only [zvMonomial, MvPolynomial.rename_id_apply, id_eq,
    shiftDeriv_monomial,
    bidegree_apply_false, bidegree_apply_true, Finset.mul_sum,
    MvPolynomial.monomial_mul_monomial, bidegree_sub_v]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjd : j ≤ d
  · have hexp :
        (Finsupp.single false a + Finsupp.single true b : Bool →₀ ℕ) +
            (Finsupp.single false c + Finsupp.single true (d - j)) =
          Finsupp.single false (a + c) +
            Finsupp.single true (b + d - j) := by
      ext i
      cases i <;> simp
      lia
    rw [hexp]
    congr 1
    ring
  · have hdj : d < j := Nat.lt_of_not_ge hjd
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hdj]
    simp

/-- Iterated partial differentiation preserves nonnegative coefficients. -/
theorem iteratedPDerivAt_nonneg {σ : Type*}
    {P : MvPolynomial σ ℝ} (hP : P.HasNonnegCoeffs) (q : σ) (j : ℕ) :
    (iteratedPDerivAt q j P).HasNonnegCoeffs := by
  induction j with
  | zero => exact hP
  | succ j ih => exact ih.pderiv q

/-- The binomial shift-derivative preserves coefficientwise nonnegativity. -/
theorem shiftDeriv_nonneg {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : P.HasNonnegCoeffs) (q : σ) (n : ℕ) :
    (shiftDeriv q n P).HasNonnegCoeffs := by
  induction n with
  | zero => exact hP
  | succ n ih =>
      rw [shiftDeriv, pow_succ']
      change (MvPolynomial.pderiv q (shiftDeriv q n P) + shiftDeriv q n P)
        |>.HasNonnegCoeffs
      exact ih.pderiv q |>.add ih

/-- A monomial with nonnegative scalar coefficient has nonnegative
coefficients. -/
theorem hasNonnegCoeffs_monomial {σ : Type*}
    (d : σ →₀ ℕ) {c : ℝ} (hc : 0 ≤ c) :
    (MvPolynomial.monomial d c).HasNonnegCoeffs := by
  classical
  intro e
  rw [MvPolynomial.coeff_monomial]
  split <;> simp_all

/-- Poisson action preserves nonnegative coefficients when both inputs have
nonnegative coefficients. -/
theorem actionAlong_nonneg {σ : Type*} (ι : Bool → σ)
    (hι : Function.Injective ι) {f : MvPolynomial Bool ℝ}
    (hf : f.HasNonnegCoeffs) {P : MvPolynomial σ ℝ}
    (hP : P.HasNonnegCoeffs) :
    (actionAlong ι f P).HasNonnegCoeffs := by
  classical
  rw [actionAlong, MvPolynomial.sum_def]
  apply MvPolynomial.HasNonnegCoeffs.sum
  intro d hd
  exact (hasNonnegCoeffs_monomial d (hf d)).rename_of_injective hι |>.mul
    (shiftDeriv_nonneg hP (ι true) (d false + d true))

/-- The Poisson star product preserves coefficientwise nonnegativity. -/
theorem star_nonneg {f g : MvPolynomial Bool ℝ}
    (hf : f.HasNonnegCoeffs) (hg : g.HasNonnegCoeffs) :
    (star f g).HasNonnegCoeffs := by
  exact actionAlong_nonneg id Function.injective_id hf hg

/-- The first degree-one noncommutativity regression: `v star z = zv`. -/
theorem v_star_z {R : Type*} [CommSemiring R] :
    star (v : MvPolynomial Bool R) z = z * v := by
  have hzv : zvMonomial 1 1 (1 : R) = z * v := by
    rw [zvMonomial]
    calc
      MvPolynomial.monomial
          (Finsupp.single false 1 + Finsupp.single true 1) (1 : R) =
          MvPolynomial.monomial (Finsupp.single false 1) 1 *
            MvPolynomial.monomial (Finsupp.single true 1) 1 := by
        symm
        rw [MvPolynomial.monomial_mul_monomial]
        simp only [one_mul]
      _ = z * v := by
        simp only [← MvPolynomial.X_pow_eq_monomial, pow_one]
  rw [← zvMonomial_v, ← zvMonomial_z, star_zvMonomial]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.descFactorial_zero, Nat.cast_one, one_mul,
    Nat.choose_one_right, Nat.zero_descFactorial_succ, Nat.cast_zero,
    zero_mul, add_zero, Nat.sub_zero, Nat.sub_self, zvMonomial_zero,
    zvMonomial_z, zvMonomial_v]
  exact hzv

/-- The second degree-one regression: `z star v = zv + z`. -/
theorem z_star_v {R : Type*} [CommSemiring R] :
    star (z : MvPolynomial Bool R) v = z * v + z := by
  have hzv : zvMonomial 1 1 (1 : R) = z * v := by
    rw [zvMonomial]
    calc
      MvPolynomial.monomial
          (Finsupp.single false 1 + Finsupp.single true 1) (1 : R) =
          MvPolynomial.monomial (Finsupp.single false 1) 1 *
            MvPolynomial.monomial (Finsupp.single true 1) 1 := by
        symm
        rw [MvPolynomial.monomial_mul_monomial]
        simp only [one_mul]
      _ = z * v := by
        simp only [← MvPolynomial.X_pow_eq_monomial, pow_one]
  rw [← zvMonomial_z, ← zvMonomial_v, star_zvMonomial]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.descFactorial_zero, Nat.cast_one, one_mul,
    Nat.choose_one_right, Nat.descFactorial_one, add_zero, Nat.sub_zero,
    Nat.sub_self, zvMonomial_z, zvMonomial_v]
  rw [hzv]

private def mulLinear {R : Type*} [CommSemiring R]
    (P : MvPolynomial Bool R) : Module.End R (MvPolynomial Bool R) where
  toFun Q := P * Q
  map_add' Q H := by rw [mul_add]
  map_smul' c Q := by
    simp only [RingHom.id_apply, MvPolynomial.smul_eq_C_mul]
    ring

private def opZ {R : Type*} [CommSemiring R] :
    Module.End R (MvPolynomial Bool R) :=
  mulLinear z * shiftMap true

private def opV {R : Type*} [CommSemiring R] :
    Module.End R (MvPolynomial Bool R) :=
  mulLinear v * shiftMap true

private def mulZ {R : Type*} [CommSemiring R] :
    Module.End R (MvPolynomial Bool R) :=
  mulLinear z

private def eulerOp {R : Type*} [CommSemiring R] :
    Module.End R (MvPolynomial Bool R) :=
  opV + mulLinear z * (MvPolynomial.pderiv false).toLinearMap

private theorem pderiv_comm_bool {R : Type*} [CommSemiring R]
    (P : MvPolynomial Bool R) :
    MvPolynomial.pderiv false (MvPolynomial.pderiv true P) =
      MvPolynomial.pderiv true (MvPolynomial.pderiv false P) := by
  classical
  ext d
  simp only [MvPolynomial.coeff_pderiv]
  have he : d + Finsupp.single false 1 + Finsupp.single true 1 =
      d + Finsupp.single true 1 + Finsupp.single false 1 := by
    abel
  rw [he]
  simp only [Finsupp.add_apply,
    Finsupp.single_eq_of_ne (by decide : true ≠ false),
    Finsupp.single_eq_of_ne (by decide : false ≠ true), add_zero]
  ring

private theorem opZ_commute_mulZ {R : Type*} [CommSemiring R] :
    opZ * (mulZ : Module.End R (MvPolynomial Bool R)) = mulZ * opZ := by
  apply LinearMap.ext
  intro P
  change z * (MvPolynomial.pderiv true (z * P) + z * P) =
    z * (z * (MvPolynomial.pderiv true P + P))
  rw [MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X_of_ne (i := true) (j := false) (by decide)]
  ring

private theorem opV_commute_mulZ {R : Type*} [CommSemiring R] :
    opV * (mulZ : Module.End R (MvPolynomial Bool R)) = mulZ * opV := by
  apply LinearMap.ext
  intro P
  change v * (MvPolynomial.pderiv true (z * P) + z * P) =
    z * (v * (MvPolynomial.pderiv true P + P))
  rw [MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X_of_ne (i := true) (j := false) (by decide)]
  ring

private theorem opZ_commute_euler {R : Type*} [CommSemiring R] :
    opZ * (eulerOp : Module.End R (MvPolynomial Bool R)) = eulerOp * opZ := by
  apply LinearMap.ext
  intro P
  change z * (MvPolynomial.pderiv true
      (v * (MvPolynomial.pderiv true P + P) +
        z * MvPolynomial.pderiv false P) +
      (v * (MvPolynomial.pderiv true P + P) +
        z * MvPolynomial.pderiv false P)) =
    v * (MvPolynomial.pderiv true
      (z * (MvPolynomial.pderiv true P + P)) +
      z * (MvPolynomial.pderiv true P + P)) +
    z * MvPolynomial.pderiv false
      (z * (MvPolynomial.pderiv true P + P))
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (i := true) (j := false) (by decide),
    one_mul, zero_mul, zero_add, map_add]
  rw [pderiv_comm_bool]
  ring

private theorem opV_commute_euler {R : Type*} [CommSemiring R] :
    opV * (eulerOp : Module.End R (MvPolynomial Bool R)) = eulerOp * opV := by
  apply LinearMap.ext
  intro P
  change v * (MvPolynomial.pderiv true
      (v * (MvPolynomial.pderiv true P + P) +
        z * MvPolynomial.pderiv false P) +
      (v * (MvPolynomial.pderiv true P + P) +
        z * MvPolynomial.pderiv false P)) =
    v * (MvPolynomial.pderiv true
      (v * (MvPolynomial.pderiv true P + P)) +
      v * (MvPolynomial.pderiv true P + P)) +
    z * MvPolynomial.pderiv false
      (v * (MvPolynomial.pderiv true P + P))
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (i := true) (j := false) (by decide),
    MvPolynomial.pderiv_X_of_ne (i := false) (j := true) (by decide),
    one_mul, zero_mul, zero_add, map_add]
  rw [pderiv_comm_bool]
  ring

private def fallingEnd {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (A : Module.End R M) : ℕ → Module.End R M
  | 0 => 1
  | n + 1 => (A - n) * fallingEnd A n

private theorem opZ_pow_apply {R : Type*} [CommSemiring R]
    (a : ℕ) (P : MvPolynomial Bool R) :
    (opZ ^ a) P = z ^ a * shiftDeriv true a P := by
  induction a with
  | zero => simp [shiftDeriv]
  | succ a ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change z * (MvPolynomial.pderiv true
        (z ^ a * shiftDeriv true a P) +
        z ^ a * shiftDeriv true a P) = _
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
        MvPolynomial.pderiv_X_of_ne (i := true) (j := false) (by decide)]
      change _ = z ^ (a + 1) * (shiftMap true ^ (a + 1)) P
      have hshift : (shiftMap true ^ (a + 1)) P =
          MvPolynomial.pderiv true (shiftDeriv true a P) +
            shiftDeriv true a P := by
        rw [pow_succ', Module.End.mul_apply]
        rfl
      rw [hshift]
      change _ = z ^ (a + 1) *
        (MvPolynomial.pderiv true (shiftDeriv true a P) +
          shiftDeriv true a P)
      ring

private theorem fallingEnd_opV_apply {R : Type*} [CommRing R]
    (b : ℕ) (P : MvPolynomial Bool R) :
    fallingEnd (opV : Module.End R (MvPolynomial Bool R)) b P =
      v ^ b * shiftDeriv true b P := by
  induction b with
  | zero => simp [fallingEnd, shiftDeriv]
  | succ b ih =>
      rw [fallingEnd, Module.End.mul_apply, ih]
      change v * (MvPolynomial.pderiv true
          (v ^ b * shiftDeriv true b P) +
          v ^ b * shiftDeriv true b P) -
        b • (v ^ b * shiftDeriv true b P) = _
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
        MvPolynomial.pderiv_X_self]
      change _ = v ^ (b + 1) * (shiftMap true ^ (b + 1)) P
      have hshift : (shiftMap true ^ (b + 1)) P =
          MvPolynomial.pderiv true (shiftDeriv true b P) +
            shiftDeriv true b P := by
        rw [pow_succ', Module.End.mul_apply]
        rfl
      rw [hshift]
      change _ = v ^ (b + 1) *
        (MvPolynomial.pderiv true (shiftDeriv true b P) +
          shiftDeriv true b P)
      cases b with
      | zero => simp
      | succ b =>
          simp only [Nat.succ_sub_one, pow_succ]
          push_cast
          ring

private theorem shiftDeriv_z_pow_mul {R : Type*} [CommSemiring R]
    (a b : ℕ) (P : MvPolynomial Bool R) :
    shiftDeriv true b (z ^ a * P) = z ^ a * shiftDeriv true b P := by
  induction b with
  | zero => rfl
  | succ b ih =>
      change (shiftMap true ^ (b + 1)) (z ^ a * P) = _
      have hleft : (shiftMap true ^ (b + 1)) (z ^ a * P) =
          MvPolynomial.pderiv true (shiftDeriv true b (z ^ a * P)) +
            shiftDeriv true b (z ^ a * P) := by
        rw [pow_succ', Module.End.mul_apply]
        rfl
      have hright : (shiftMap true ^ (b + 1)) P =
          MvPolynomial.pderiv true (shiftDeriv true b P) +
            shiftDeriv true b P := by
        rw [pow_succ', Module.End.mul_apply]
        rfl
      rw [hleft]
      change _ = z ^ a * (shiftMap true ^ (b + 1)) P
      rw [hright, ih, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_pow,
        MvPolynomial.pderiv_X_of_ne (i := true) (j := false) (by decide)]
      ring

private theorem shiftDeriv_comp {R σ : Type*} [CommSemiring R]
    (q : σ) (a b : ℕ) (P : MvPolynomial σ R) :
    shiftDeriv q b (shiftDeriv q a P) = shiftDeriv q (a + b) P := by
  change (shiftMap q ^ b) ((shiftMap q ^ a) P) =
    (shiftMap q ^ (a + b)) P
  rw [← Module.End.mul_apply, ← pow_add, add_comm a b]

private def termOp {R : Type*} [CommRing R] (a b : ℕ) :
    Module.End R (MvPolynomial Bool R) :=
  fallingEnd opV b * opZ ^ a

private theorem termOp_apply {R : Type*} [CommRing R]
    (a b : ℕ) (P : MvPolynomial Bool R) :
    termOp a b P = z ^ a * v ^ b * shiftDeriv true (a + b) P := by
  rw [termOp, Module.End.mul_apply, fallingEnd_opV_apply, opZ_pow_apply,
    shiftDeriv_z_pow_mul, shiftDeriv_comp]
  ring

private theorem finsupp_bool_decompose (d : Bool →₀ ℕ) :
    d = Finsupp.single false (d false) + Finsupp.single true (d true) := by
  ext i
  cases i <;> simp

/-- A sparse monomial over `Bool` is the corresponding `z,v` monomial. -/
theorem monomial_bool_eq {R : Type*} [CommSemiring R]
    (d : Bool →₀ ℕ) (c : R) :
    MvPolynomial.monomial d c =
      MvPolynomial.C c * z ^ d false * v ^ d true := by
  rw [finsupp_bool_decompose d]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : true ≠ false),
    Finsupp.single_eq_of_ne (by decide : false ≠ true), add_zero, zero_add]
  calc
    MvPolynomial.monomial
        (Finsupp.single false (d false) + Finsupp.single true (d true)) c =
        MvPolynomial.C c * MvPolynomial.monomial
          (Finsupp.single false (d false) + Finsupp.single true (d true)) 1 := by
      rw [MvPolynomial.C_mul_monomial]
      simp only [mul_one]
    _ = MvPolynomial.C c *
          (MvPolynomial.monomial (Finsupp.single false (d false)) 1 *
            MvPolynomial.monomial (Finsupp.single true (d true)) 1) := by
      rw [MvPolynomial.monomial_mul_monomial]
      simp only [one_mul]
    _ = MvPolynomial.C c * z ^ d false * v ^ d true := by
      simp only [← MvPolynomial.X_pow_eq_monomial]
      ring

private def actionEnd {R : Type*} [CommRing R]
    (f : MvPolynomial Bool R) : Module.End R (MvPolynomial Bool R) :=
  ∑ d ∈ f.support, f.coeff d • termOp (d false) (d true)

private theorem actionEnd_apply {R : Type*} [CommRing R]
    (f P : MvPolynomial Bool R) :
    actionEnd f P = star f P := by
  classical
  rw [actionEnd, star, actionAlong, MvPolynomial.sum_def,
    LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [LinearMap.smul_apply, termOp_apply,
    MvPolynomial.rename_id_apply, monomial_bool_eq]
  simp only [MvPolynomial.smul_eq_C_mul, id_eq]
  ring

private theorem natCast_commute {S : Type*} [Ring S] (n : ℕ) (B : S) :
    Commute (n : S) B := by
  induction n with
  | zero => simpa only [Nat.cast_zero] using Commute.zero_left B
  | succ n ih =>
      rw [Nat.cast_succ]
      exact Commute.add_left ih (Commute.one_left B)

private theorem fallingEnd_commute {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {A B : Module.End R M}
    (h : Commute A B) (n : ℕ) : Commute (fallingEnd A n) B := by
  induction n with
  | zero => exact Commute.one_left B
  | succ n ih =>
      apply Commute.mul_left
      · apply Commute.sub_left h
        exact natCast_commute n B
      · exact ih

private theorem termOp_commute_mulZ {R : Type*} [CommRing R]
    (a b : ℕ) :
    Commute (termOp a b) (mulZ : Module.End R (MvPolynomial Bool R)) := by
  exact Commute.mul_left (fallingEnd_commute opV_commute_mulZ b)
    (Commute.pow_left opZ_commute_mulZ a)

private theorem termOp_commute_euler {R : Type*} [CommRing R]
    (a b : ℕ) :
    Commute (termOp a b) (eulerOp : Module.End R (MvPolynomial Bool R)) := by
  exact Commute.mul_left (fallingEnd_commute opV_commute_euler b)
    (Commute.pow_left opZ_commute_euler a)

private theorem commute_smul_left {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (c : R) {A B : Module.End R M}
    (h : Commute A B) : Commute (c • A) B :=
  Commute.smul_left h c

private theorem actionEnd_commute_mulZ {R : Type*} [CommRing R]
    (f : MvPolynomial Bool R) :
    Commute (actionEnd f) (mulZ : Module.End R (MvPolynomial Bool R)) := by
  classical
  rw [actionEnd]
  apply Commute.sum_left
  intro d hd
  exact commute_smul_left (f.coeff d) (termOp_commute_mulZ (d false) (d true))

private theorem actionEnd_commute_euler {R : Type*} [CommRing R]
    (f : MvPolynomial Bool R) :
    Commute (actionEnd f) (eulerOp : Module.End R (MvPolynomial Bool R)) := by
  classical
  rw [actionEnd]
  apply Commute.sum_left
  intro d hd
  exact commute_smul_left (f.coeff d) (termOp_commute_euler (d false) (d true))

private theorem shiftDeriv_one {R σ : Type*} [CommSemiring R]
    (q : σ) (n : ℕ) : shiftDeriv q n (1 : MvPolynomial σ R) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (shiftMap q ^ (n + 1)) (1 : MvPolynomial σ R) = 1
      have hstep : (shiftMap q ^ (n + 1)) (1 : MvPolynomial σ R) =
          MvPolynomial.pderiv q (shiftDeriv q n 1) + shiftDeriv q n 1 := by
        rw [pow_succ', Module.End.mul_apply]
        rfl
      rw [hstep, ih, MvPolynomial.pderiv_one, zero_add]

/-- Every Poisson operator sends `1` to its defining polynomial. -/
theorem star_one_right {R : Type*} [CommRing R]
    (f : MvPolynomial Bool R) : star f 1 = f := by
  classical
  rw [← actionEnd_apply, actionEnd, LinearMap.sum_apply]
  calc
    (∑ d ∈ f.support, (f.coeff d • termOp (d false) (d true)) 1) =
        ∑ d ∈ f.support, MvPolynomial.monomial d (f.coeff d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [LinearMap.smul_apply, termOp_apply, shiftDeriv_one,
        mul_one, MvPolynomial.smul_eq_C_mul, monomial_bool_eq]
      ring
    _ = f := MvPolynomial.support_sum_monomial_coeff f

private theorem eulerOp_v_pow {R : Type*} [CommRing R] (b : ℕ) :
    (eulerOp : Module.End R (MvPolynomial Bool R)) (v ^ b) =
      v ^ (b + 1) + (b : R) • v ^ b := by
  change v * (MvPolynomial.pderiv true (v ^ b) + v ^ b) +
    z * MvPolynomial.pderiv false (v ^ b) = _
  rw [MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X_of_ne (i := false) (j := true) (by decide)]
  cases b with
  | zero => simp
  | succ b =>
      simp only [Nat.succ_sub_one, pow_succ]
      push_cast
      rw [MvPolynomial.smul_eq_C_mul]
      simp only [map_add, map_one, map_natCast]
      ring

private theorem end_eq_on_v_pow {R : Type*} [CommRing R]
    (A B : Module.End R (MvPolynomial Bool R))
    (hAD : Commute A (eulerOp : Module.End R (MvPolynomial Bool R)))
    (hBD : Commute B (eulerOp : Module.End R (MvPolynomial Bool R)))
    (h1 : A 1 = B 1) (b : ℕ) : A (v ^ b) = B (v ^ b) := by
  induction b with
  | zero => simpa using h1
  | succ b ih =>
      have hDeq : A (eulerOp (v ^ b)) = B (eulerOp (v ^ b)) := by
        rw [← Module.End.mul_apply, hAD.eq, Module.End.mul_apply, ih,
          ← Module.End.mul_apply, ← hBD.eq, Module.End.mul_apply]
      rw [eulerOp_v_pow, A.map_add, B.map_add, A.map_smul,
        B.map_smul, ih] at hDeq
      exact add_right_cancel hDeq

private theorem end_eq_on_z_pow_v_pow {R : Type*} [CommRing R]
    (A B : Module.End R (MvPolynomial Bool R))
    (hAZ : Commute A (mulZ : Module.End R (MvPolynomial Bool R)))
    (hBZ : Commute B (mulZ : Module.End R (MvPolynomial Bool R)))
    (hAD : Commute A (eulerOp : Module.End R (MvPolynomial Bool R)))
    (hBD : Commute B (eulerOp : Module.End R (MvPolynomial Bool R)))
    (h1 : A 1 = B 1) (a b : ℕ) :
    A (z ^ a * v ^ b) = B (z ^ a * v ^ b) := by
  induction a with
  | zero => simpa using end_eq_on_v_pow A B hAD hBD h1 b
  | succ a ih =>
      have hA : A (z * (z ^ a * v ^ b)) = z * A (z ^ a * v ^ b) := by
        have hc := congrArg (fun T : Module.End R (MvPolynomial Bool R) =>
          T (z ^ a * v ^ b)) hAZ
        rw [Module.End.mul_apply, Module.End.mul_apply] at hc
        change A (z * (z ^ a * v ^ b)) = z * A (z ^ a * v ^ b) at hc
        exact hc
      have hB : B (z * (z ^ a * v ^ b)) = z * B (z ^ a * v ^ b) := by
        have hc := congrArg (fun T : Module.End R (MvPolynomial Bool R) =>
          T (z ^ a * v ^ b)) hBZ
        rw [Module.End.mul_apply, Module.End.mul_apply] at hc
        change B (z * (z ^ a * v ^ b)) = z * B (z ^ a * v ^ b) at hc
        exact hc
      rw [pow_succ]
      have hz : (z : MvPolynomial Bool R) ^ a * z * v ^ b =
          z * (z ^ a * v ^ b) := by ring
      rw [hz]
      rw [hA, hB, ih]

private theorem end_eq_of_commute {R : Type*} [CommRing R]
    (A B : Module.End R (MvPolynomial Bool R))
    (hAZ : Commute A (mulZ : Module.End R (MvPolynomial Bool R)))
    (hBZ : Commute B (mulZ : Module.End R (MvPolynomial Bool R)))
    (hAD : Commute A (eulerOp : Module.End R (MvPolynomial Bool R)))
    (hBD : Commute B (eulerOp : Module.End R (MvPolynomial Bool R)))
    (h1 : A 1 = B 1) : A = B := by
  apply LinearMap.ext
  intro P
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [monomial_bool_eq]
      have hm : MvPolynomial.C c * z ^ d false * v ^ d true =
          MvPolynomial.C c * (z ^ d false * v ^ d true) := by ring
      rw [hm, ← MvPolynomial.smul_eq_C_mul]
      rw [A.map_smul, B.map_smul,
        end_eq_on_z_pow_v_pow A B hAZ hBZ hAD hBD h1]
  | add P Q hP hQ =>
      rw [A.map_add, B.map_add, hP, hQ]

/-- The unit acts trivially from the left. -/
theorem star_one_left {R : Type*} [CommRing R]
    (g : MvPolynomial Bool R) : star 1 g = g := by
  rw [star]
  change actionAlong id (MvPolynomial.monomial 0 1) g = g
  rw [actionAlong, MvPolynomial.sum_monomial_eq (by simp)]
  simp [shiftDeriv]

/-- Composition of Poisson operators is Poisson multiplication of their
symbols. -/
theorem action_comp {R : Type*} [CommRing R]
    (f g P : MvPolynomial Bool R) :
    star f (star g P) = star (star f g) P := by
  let A := actionEnd f * actionEnd g
  let B := actionEnd (star f g)
  have hAZ : Commute A (mulZ : Module.End R (MvPolynomial Bool R)) :=
    Commute.mul_left (actionEnd_commute_mulZ f) (actionEnd_commute_mulZ g)
  have hBZ : Commute B (mulZ : Module.End R (MvPolynomial Bool R)) :=
    actionEnd_commute_mulZ (star f g)
  have hAD : Commute A (eulerOp : Module.End R (MvPolynomial Bool R)) :=
    Commute.mul_left (actionEnd_commute_euler f) (actionEnd_commute_euler g)
  have hBD : Commute B (eulerOp : Module.End R (MvPolynomial Bool R)) :=
    actionEnd_commute_euler (star f g)
  have h1 : A 1 = B 1 := by
    change (actionEnd f * actionEnd g) 1 = actionEnd (star f g) 1
    calc
      (actionEnd f * actionEnd g) 1 = star f (star g 1) := by
        rw [Module.End.mul_apply, actionEnd_apply, actionEnd_apply]
      _ = star f g := by rw [star_one_right]
      _ = star (star f g) 1 := by rw [star_one_right]
      _ = actionEnd (star f g) 1 := (actionEnd_apply (star f g) 1).symm
  have hEnd : A = B := end_eq_of_commute A B hAZ hBZ hAD hBD h1
  have hP := congrArg (fun T : Module.End R (MvPolynomial Bool R) => T P) hEnd
  change (actionEnd f * actionEnd g) P = actionEnd (star f g) P at hP
  rw [Module.End.mul_apply, actionEnd_apply, actionEnd_apply,
    actionEnd_apply] at hP
  exact hP

/-- The Poisson star product is associative. -/
theorem star_assoc {R : Type*} [CommRing R]
    (f g h : MvPolynomial Bool R) :
    star (star f g) h = star f (star g h) := by
  exact (action_comp f g h).symm

end

end RealRooted.Poisson
