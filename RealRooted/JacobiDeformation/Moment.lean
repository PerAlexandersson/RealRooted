import RealRooted.Jacobi.Orthogonality
import RealRooted.JacobiDeformation.Basic

/-!
# Normalized shifted-Jacobi moments

With positive parameters `c, d` (the library parameters are `α = c - 1` and
`β = d - 1`) we normalize the shifted-Jacobi moment functional by its total
mass, so that `ℓ(t ^ k) = (c)_k / (c + d)_k`, and we normalize the shifted
Jacobi polynomial `φ_j = normalizedShiftedJacobi j c d` to take the value one
at zero.  The main result is the finite moment identity

`ℓ(φ_j(t) (1 - t) ^ k) = k^{(j)} (d)_k / (c + d)_{k + j}`

(`normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow`), valid
for all `j, k`; the falling factorial `k^{(j)}` vanishes for `j > k`.  It is
proved by expanding `φ_j` in monomials and applying the terminating
Chu--Vandermonde identity.  The last section relates `φ_j` to the monic
normalization used by the Favard recurrence.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-! ## The normalized moment functional -/

/-- The shifted-Jacobi functional normalized to send `1` to `1`.

The arguments `c, d` are positive beta parameters; internally this uses the
library convention `α = c - 1`, `β = d - 1`. -/
def normalizedJacobiFunctional (c d : ℝ) (p : ℝ[X]) : ℝ :=
  shiftedJacobiFunctional (c - 1) (d - 1) p /
    shiftedJacobiMoment (c - 1) (d - 1) 0

/-- Iterating the existing first-parameter shift of the Jacobi functional. -/
theorem shiftedJacobiFunctional_X_pow_mul (α β : ℝ) (i : ℕ) (p : ℝ[X]) :
    shiftedJacobiFunctional α β (X ^ i * p) =
      shiftedJacobiFunctional (α + i) β p := by
  induction i generalizing α with
  | zero => simp
  | succ i ih =>
      calc
        shiftedJacobiFunctional α β (X ^ i.succ * p) =
            shiftedJacobiFunctional α β (X * (X ^ i * p)) := by
              rw [pow_succ]
              ring_nf
        _ = shiftedJacobiFunctional (α + 1) β (X ^ i * p) :=
              shiftedJacobiFunctional_X_mul α β _
        _ = shiftedJacobiFunctional (α + 1 + i) β p := ih (α + 1)
        _ = shiftedJacobiFunctional (α + i.succ) β p := by
              congr 1
              push_cast
              ring

/-- Iterating the existing second-parameter shift of the Jacobi functional. -/
theorem shiftedJacobiFunctional_one_sub_X_pow_mul
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (k : ℕ) (p : ℝ[X]) :
    shiftedJacobiFunctional α β ((1 - X) ^ k * p) =
      shiftedJacobiFunctional α (β + k) p := by
  induction k generalizing β with
  | zero => simp
  | succ k ih =>
      calc
        shiftedJacobiFunctional α β ((1 - X) ^ k.succ * p) =
            shiftedJacobiFunctional α β ((1 - X) * ((1 - X) ^ k * p)) := by
              rw [pow_succ]
              ring_nf
        _ = shiftedJacobiFunctional α (β + 1) ((1 - X) ^ k * p) :=
              shiftedJacobiFunctional_one_sub_X_mul hα hβ _
        _ = shiftedJacobiFunctional α (β + 1 + k) p :=
              ih (by linarith)
        _ = shiftedJacobiFunctional α (β + k.succ) p := by
              congr 1
              push_cast
              ring

/-- A gamma value with a rising-factorial shift. -/
theorem gamma_mul_risingFactorial (a : ℝ) (n : ℕ) (ha : 0 < a) :
    Real.Gamma a * risingFactorial a n = Real.Gamma (a + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        Real.Gamma a * risingFactorial a n.succ =
            (Real.Gamma a * risingFactorial a n) * (a + n) := by
              rw [risingFactorial_succ]
              ring
        _ = Real.Gamma (a + n) * (a + n) := by rw [ih]
        _ = Real.Gamma (a + n.succ) := by
              rw [show a + (n.succ : ℕ) = (a + n) + 1 by push_cast; ring,
                Real.Gamma_add_one (by positivity : a + n ≠ 0)]
              ring

/-- The value of the shifted-Jacobi functional at the constant polynomial. -/
theorem shiftedJacobiFunctional_one_eq_gamma (α β : ℝ) :
    shiftedJacobiFunctional α β 1 =
      Real.Gamma (α + 1) * Real.Gamma (β + 1) /
        Real.Gamma (α + β + 2) := by
  simpa [shiftedJacobiMoment] using shiftedJacobiFunctional_X_pow α β 0

/-- The normalized mixed beta moment.

For positive `c,d`, this is the finite functional version of
`E[X^i (1-X)^k] = (c)_i (d)_k / (c+d)_(i+k)`. -/
theorem normalizedJacobiFunctional_mixed_moment
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (i k : ℕ) :
    normalizedJacobiFunctional c d (X ^ i * (1 - X) ^ k) =
      risingFactorial c i * risingFactorial d k /
        risingFactorial (c + d) (i + k) := by
  have hs : 0 < c + d := by linarith
  have hΓc : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc
  have hΓd : 0 < Real.Gamma d := Real.Gamma_pos_of_pos hd
  have hΓs : 0 < Real.Gamma (c + d) := Real.Gamma_pos_of_pos hs
  have hrs : 0 < risingFactorial (c + d) (i + k) :=
    risingFactorial_pos _ hs
  rw [normalizedJacobiFunctional, shiftedJacobiFunctional_X_pow_mul]
  rw [← mul_one ((1 - X) ^ k : ℝ[X])]
  rw [shiftedJacobiFunctional_one_sub_X_pow_mul (by linarith) (by linarith)]
  rw [shiftedJacobiFunctional_one_eq_gamma, shiftedJacobiMoment]
  rw [show c - 1 + (i : ℝ) + 1 = c + i by ring,
    show d - 1 + (k : ℝ) + 1 = d + k by ring,
    show (c - 1 + (i : ℝ)) + (d - 1 + (k : ℝ)) + 2 = c + d + (i + k) by ring,
    show c - 1 + (0 : ℕ) + 1 = c by norm_num,
    show d - 1 + 1 = d by ring,
    show c - 1 + (d - 1) + (0 : ℕ) + 2 = c + d by
      norm_num
      ring]
  rw [show c + d + ((i : ℝ) + (k : ℝ)) = c + d + ((i + k : ℕ) : ℝ) by
    push_cast
    ring]
  rw [← gamma_mul_risingFactorial c i hc,
    ← gamma_mul_risingFactorial d k hd,
    ← gamma_mul_risingFactorial (c + d) (i + k) hs]
  field_simp [hΓc.ne', hΓd.ne', hΓs.ne', hrs.ne']

/-! ## The value-one normalization and the vanishing moments

Orthogonality gives the `j > k` case of the moment identity directly.
-/

/-- The shifted Jacobi polynomial normalized to take value one at zero.

The positive parameters `c,d` correspond to the library parameters
`α = c - 1`, `β = d - 1`. -/
def normalizedShiftedJacobi (j : ℕ) (c d : ℝ) : ℝ[X] :=
  C (Ring.choose ((j : ℝ) + c - 1) j)⁻¹ *
    shiftedJacobi j (c - 1) (d - 1)

theorem normalizedShiftedJacobi_eval_zero
    {c d : ℝ} (hc : 0 < c) (j : ℕ) :
    (normalizedShiftedJacobi j c d).eval 0 = 1 := by
  have hchoose : 0 < Ring.choose ((j : ℝ) + c - 1) j := by
    apply ring_choose_pos
    linarith
  rw [normalizedShiftedJacobi, eval_mul, eval_C,
    shiftedJacobi_eval_zero,
    show (j : ℝ) + (c - 1) = (j : ℝ) + c - 1 by ring]
  exact inv_mul_cancel₀ hchoose.ne'

/-- The normalized Jacobi moment vanishes in the `j > k` boundary case. -/
theorem normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow_eq_zero
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {j k : ℕ} (hkj : k < j) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d * (1 - X) ^ k) = 0 := by
  have horth :
      shiftedJacobiInner (c - 1) (d - 1)
        (shiftedJacobi j (c - 1) (d - 1)) ((1 - X) ^ k) = 0 := by
    apply shiftedJacobiInner_eq_zero
    · linarith
    · linarith
    · rw [natDegree_pow]
      rw [show (1 - X : ℝ[X]).natDegree = 1 by
        simp [sub_eq_add_neg]]
      simpa only [Nat.mul_one] using hkj
  unfold normalizedJacobiFunctional normalizedShiftedJacobi
  change
    shiftedJacobiFunctional (c - 1) (d - 1)
        ((C (Ring.choose ((j : ℝ) + c - 1) j)⁻¹ *
          shiftedJacobi j (c - 1) (d - 1)) * (1 - X) ^ k) /
      shiftedJacobiMoment (c - 1) (d - 1) 0 = 0
  rw [mul_assoc, shiftedJacobiFunctional_C_mul]
  change _ * shiftedJacobiInner (c - 1) (d - 1)
      (shiftedJacobi j (c - 1) (d - 1)) ((1 - X) ^ k) / _ = 0
  rw [horth, mul_zero, zero_div]

/-- The moment identity in the `j > k` boundary case. -/
theorem normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow_of_lt
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {j k : ℕ} (hkj : k < j) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d * (1 - X) ^ k) =
      fallingFactorial (k : ℝ) j * risingFactorial d k /
        risingFactorial (c + d) (k + j) := by
  rw [normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow_eq_zero
    hc hd hkj, fallingFactorial_natCast_eq_zero_of_lt hkj]
  ring

/-! ## Coefficients of normalized shifted Jacobi polynomials

The first lemma is the denominator-cleared generalized-binomial identity used
to normalize the coefficient of `X ^ i` in a shifted Jacobi polynomial.
-/

/-- Clearing the endpoint normalization denominator in a shifted-Jacobi
coefficient. -/
theorem choose_mul_risingFactorial_eq_choose_mul_fallingFactorial
    {c : ℝ} {i j : ℕ} (hij : i ≤ j) :
    Ring.choose ((j : ℝ) + c - 1) (j - i) * risingFactorial c i =
      Ring.choose ((j : ℝ) + c - 1) j * fallingFactorial (j : ℝ) i := by
  let x : ℝ := (j : ℝ) + c - 1
  have hchoose := Ring.choose_smul_choose (R := ℝ) x (n := j) (k := j - i)
    (Nat.sub_le j i)
  have hsub : j - (j - i) = i := by lia
  have harg : x - (j - i : ℕ) = c + i - 1 := by
    dsimp [x]
    rw [Nat.cast_sub hij]
    ring
  rw [hsub, harg] at hchoose
  have hnat : (j.choose (j - i) : ℝ) * (i.factorial : ℝ) =
      fallingFactorial (j : ℝ) i := by
    change (j.choose (j - i) : ℝ) * (i.factorial : ℝ) =
      (descPochhammer ℝ i).eval (j : ℝ)
    rw [Nat.choose_symm hij, Nat.cast_choose_eq_descPochhammer_div]
    field_simp [Nat.factorial_ne_zero]
  have hring : Ring.choose (c + i - 1) i * (i.factorial : ℝ) =
      risingFactorial c i := by
    rw [Ring.choose_eq_smul, smul_eq_mul]
    change (i.factorial : ℝ)⁻¹ *
        (descPochhammer ℤ i).smeval (c + i - 1) * (i.factorial : ℝ) =
      risingFactorial c i
    field_simp [Nat.factorial_ne_zero]
    rw [descPochhammer_smeval_eq_ascPochhammer,
      ascPochhammer_smeval_eq_eval]
    change (ascPochhammer ℝ i).eval (c + (i : ℝ) - 1 - (i : ℝ) + 1) =
      (ascPochhammer ℝ i).eval c
    congr 2; ring_nf
  rw [← hring, ← hnat]
  have hchoose' : (j.choose (j - i) : ℝ) * Ring.choose x j =
      Ring.choose x (j - i) * Ring.choose (c + i - 1) i := by
    simpa only [nsmul_eq_mul] using hchoose
  calc
    Ring.choose ((j : ℝ) + c - 1) (j - i) *
          (Ring.choose (c + i - 1) i * (i.factorial : ℝ)) =
        (Ring.choose x (j - i) * Ring.choose (c + i - 1) i) *
          (i.factorial : ℝ) := by
      dsimp [x]
      ring
    _ = ((j.choose (j - i) : ℝ) * Ring.choose x j) *
          (i.factorial : ℝ) := by rw [hchoose']
    _ = Ring.choose ((j : ℝ) + c - 1) j *
          ((j.choose (j - i) : ℝ) * (i.factorial : ℝ)) := by
      dsimp [x]
      ring

private theorem choose_mul_factorial_eq_risingFactorial
    (j : ℕ) {c d : ℝ} (i : ℕ) :
    Ring.choose ((j : ℝ) + c + d - 2 + i) i * (i.factorial : ℝ) =
      risingFactorial ((j : ℝ) + c + d - 1) i := by
  rw [Ring.choose_eq_smul, smul_eq_mul]
  change (i.factorial : ℝ)⁻¹ *
      (descPochhammer ℤ i).smeval ((j : ℝ) + c + d - 2 + i) *
        (i.factorial : ℝ) =
      risingFactorial ((j : ℝ) + c + d - 1) i
  field_simp [Nat.factorial_ne_zero]
  rw [descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval]
  change (ascPochhammer ℝ i).eval
      ((j : ℝ) + c + d - 2 + (i : ℝ) - (i : ℝ) + 1) =
    (ascPochhammer ℝ i).eval ((j : ℝ) + c + d - 1)
  congr 1
  ring

/-- The in-range coefficient of the shifted Jacobi polynomial normalized at
zero, in the positive parameters `c,d`. -/
theorem coeff_normalizedShiftedJacobi_of_le
    {c d : ℝ} (hc : 0 < c) {i j : ℕ} (hij : i ≤ j) :
    (normalizedShiftedJacobi j c d).coeff i =
      (-1 : ℝ) ^ i * (j.choose i : ℝ) *
        risingFactorial ((j : ℝ) + c + d - 1) i / risingFactorial c i := by
  have hnorm : 0 < Ring.choose ((j : ℝ) + c - 1) j := by
    apply ring_choose_pos
    linarith
  have hrise : 0 < risingFactorial c i := risingFactorial_pos i hc
  have hfirst := choose_mul_risingFactorial_eq_choose_mul_fallingFactorial (c := c) hij
  have hsecond := choose_mul_factorial_eq_risingFactorial j (c := c) (d := d) i
  have hnat : (j.choose i : ℝ) * (i.factorial : ℝ) =
      fallingFactorial (j : ℝ) i := by
    rw [Nat.cast_choose_eq_descPochhammer_div]
    field_simp [Nat.factorial_ne_zero]
    rfl
  rw [normalizedShiftedJacobi, coeff_C_mul, coeff_shiftedJacobi]
  simp only [hij, ↓reduceIte]
  field_simp [hnorm.ne', hrise.ne', Nat.factorial_ne_zero]
  calc
    Ring.choose ((j : ℝ) + (c - 1)) (j - i) *
          Ring.choose ((j : ℝ) + (c - 1) + (d - 1) + i) i *
          risingFactorial c i =
        Ring.choose ((j : ℝ) + (c - 1) + (d - 1) + i) i *
          (Ring.choose ((j : ℝ) + c - 1) (j - i) *
            risingFactorial c i) := by ring_nf
    _ = Ring.choose ((j : ℝ) + (c - 1) + (d - 1) + i) i *
          (Ring.choose ((j : ℝ) + c - 1) j *
            fallingFactorial (j : ℝ) i) := by rw [hfirst]
    _ = Ring.choose ((j : ℝ) + c - 1) j * (j.choose i : ℝ) *
          (Ring.choose ((j : ℝ) + c + d - 2 + i) i *
            (i.factorial : ℝ)) := by rw [← hnat]; ring_nf
    _ = Ring.choose ((j : ℝ) + c - 1) j * (j.choose i : ℝ) *
          risingFactorial ((j : ℝ) + c + d - 1) i := by rw [hsecond]

/-- Coefficients above the Jacobi degree vanish after normalization. -/
theorem coeff_normalizedShiftedJacobi_of_lt
    (j : ℕ) (c d : ℝ) {i : ℕ} (hji : j < i) :
    (normalizedShiftedJacobi j c d).coeff i = 0 := by
  rw [normalizedShiftedJacobi, coeff_C_mul, coeff_shiftedJacobi]
  simp only [Nat.not_le.mpr hji, ↓reduceIte, mul_zero]

/-- The normalized shifted Jacobi polynomial reconstructed from its finite
coefficient expansion. -/
theorem normalizedShiftedJacobi_eq_sum_coeff
    {c d : ℝ} (j : ℕ) :
    normalizedShiftedJacobi j c d =
      ∑ i ∈ Finset.range (j + 1),
        C ((normalizedShiftedJacobi j c d).coeff i) * X ^ i := by
  ext i
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hij : i ≤ j
  · simp [Nat.lt_succ_iff.mpr hij]
  · have hji : j < i := Nat.lt_of_not_ge hij
    rw [coeff_normalizedShiftedJacobi_of_lt j c d hji]
    simp [Nat.lt_succ_iff.not.mpr hij]

/-! ## Reduction to a finite sum -/

/-- The scalar cancellation which converts a mixed normalized beta moment to
the finite Chu--Vandermonde summand. -/
theorem risingFactorial_mixed_moment_cancel
    {c d a : ℝ} (hc : 0 < c) (hd : 0 < d) (i k : ℕ) :
    (risingFactorial a i / risingFactorial c i) *
        (risingFactorial c i * risingFactorial d k /
          risingFactorial (c + d) (i + k)) =
      (risingFactorial d k / risingFactorial (c + d) k) *
        (risingFactorial a i / risingFactorial (c + d + k) i) := by
  have hs : 0 < c + d := by linarith
  have hci : 0 < risingFactorial c i := risingFactorial_pos i hc
  have hsk : 0 < risingFactorial (c + d) k := risingFactorial_pos k hs
  have hski : 0 < risingFactorial (c + d + k) i := by
    apply risingFactorial_pos
    positivity
  have hsplit := (risingFactorial_add (c + d) k i).symm
  rw [show (c + d : ℝ) + k = c + d + k by ring,
    Nat.add_comm] at hsplit
  rw [← hsplit]
  field_simp [hci.ne', hsk.ne', hski.ne']

theorem normalizedJacobiFunctional_sum {ι : Type*} (c d : ℝ)
    (s : Finset ι) (p : ι → ℝ[X]) :
    normalizedJacobiFunctional c d (∑ x ∈ s, p x) =
      ∑ x ∈ s, normalizedJacobiFunctional c d (p x) := by
  unfold normalizedJacobiFunctional
  rw [shiftedJacobiFunctional_sum, Finset.sum_div]

theorem normalizedJacobiFunctional_C_mul (c d a : ℝ) (p : ℝ[X]) :
    normalizedJacobiFunctional c d (C a * p) =
      a * normalizedJacobiFunctional c d p := by
  unfold normalizedJacobiFunctional
  rw [shiftedJacobiFunctional_C_mul]
  ring

/-- Applying the normalized Jacobi functional to a normalized shifted Jacobi
polynomial times `(1 - X)^k` reduces exactly to its finite hypergeometric sum.
The finite sum is intentionally not evaluated here. -/
theorem normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow_eq_sum
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j k : ℕ) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d * (1 - X) ^ k) =
      (risingFactorial d k / risingFactorial (c + d) k) *
        ∑ i ∈ Finset.range (j + 1),
          (-1 : ℝ) ^ i * (j.choose i : ℝ) *
            risingFactorial ((j : ℝ) + c + d - 1) i /
              risingFactorial (c + d + k) i := by
  rw [normalizedShiftedJacobi_eq_sum_coeff j, Finset.sum_mul,
    normalizedJacobiFunctional_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [mul_assoc, normalizedJacobiFunctional_C_mul,
    coeff_normalizedShiftedJacobi_of_le hc hij,
    normalizedJacobiFunctional_mixed_moment hc hd i k]
  calc
    ((-1 : ℝ) ^ i * (j.choose i : ℝ) *
          risingFactorial ((j : ℝ) + c + d - 1) i / risingFactorial c i) *
        (risingFactorial c i * risingFactorial d k /
          risingFactorial (c + d) (i + k)) =
        ((-1 : ℝ) ^ i * (j.choose i : ℝ)) *
          ((risingFactorial ((j : ℝ) + c + d - 1) i / risingFactorial c i) *
            (risingFactorial c i * risingFactorial d k /
              risingFactorial (c + d) (i + k))) := by ring
    _ = ((-1 : ℝ) ^ i * (j.choose i : ℝ)) *
          ((risingFactorial d k / risingFactorial (c + d) k) *
            (risingFactorial ((j : ℝ) + c + d - 1) i /
              risingFactorial (c + d + k) i)) := by
        rw [risingFactorial_mixed_moment_cancel hc hd i k]
    _ = (risingFactorial d k / risingFactorial (c + d) k) *
          ((-1 : ℝ) ^ i * (j.choose i : ℝ) *
            risingFactorial ((j : ℝ) + c + d - 1) i /
              risingFactorial (c + d + k) i) := by ring

/-! ## Evaluation by Chu--Vandermonde -/

/-- The all-degree normalized shifted-Jacobi moment.  The terminating
Chu--Vandermonde identity includes the `j > k` vanishing case. -/
theorem normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j k : ℕ) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d * (1 - X) ^ k) =
      fallingFactorial (k : ℝ) j * risingFactorial d k /
        risingFactorial (c + d) (k + j) := by
  have hs : 0 < c + d := by linarith
  have hsum := chu_vandermonde_terminating j k (c + d) hs
  have hnum : (j : ℝ) + (c + d) - 1 = (j : ℝ) + c + d - 1 := by ring
  rw [hnum] at hsum
  rw [normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow_eq_sum
    hc hd j k, hsum]
  have hsk : 0 < risingFactorial (c + d) k := risingFactorial_pos k hs
  have hskj : 0 < risingFactorial (c + d + k) j := by
    apply risingFactorial_pos
    positivity
  have htotal : 0 < risingFactorial (c + d) (k + j) :=
    risingFactorial_pos (k + j) hs
  have hsplit := (risingFactorial_add (c + d) k j).symm
  field_simp [hsk.ne', hskj.ne', htotal.ne']
  rw [← hsplit]
  ring

/-! ## Monic and value-one normalizations

The two normalizations are scalar multiples of the same shifted Jacobi
polynomial.
-/

/-- The value at zero of the monic shifted-Jacobi polynomial is nonzero in the
positive parameter range. -/
theorem shiftedJacobiMonic_eval_zero_ne_zero
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j : ℕ) :
    (shiftedJacobiMonic j (c - 1) (d - 1)).eval 0 ≠ 0 := by
  have hchoose : 0 < Ring.choose ((j : ℝ) + c - 1) j := by
    apply ring_choose_pos
    linarith
  have hp_nonzero : shiftedJacobiMonic j (c - 1) (d - 1) ≠ 0 :=
    (monic_shiftedJacobiMonic j (by linarith) (by linarith)).ne_zero
  have hscale :
      ((-1 : ℝ) ^ j *
          Ring.choose ((j : ℝ) + (c - 1) + (d - 1) + (j : ℝ)) j)⁻¹ ≠ 0 := by
    intro hzero
    apply hp_nonzero
    rw [shiftedJacobiMonic, hzero, C_0, zero_mul]
  rw [shiftedJacobiMonic, eval_mul, eval_C, shiftedJacobi_eval_zero,
    show (j : ℝ) + (c - 1) = (j : ℝ) + c - 1 by ring]
  apply mul_ne_zero
  · convert hscale using 1; ring_nf
  · exact hchoose.ne'

/-- Multiplying the value-one-at-zero normalization by the monic polynomial's
value at zero recovers that monic shifted-Jacobi polynomial. -/
theorem C_eval_zero_mul_normalizedShiftedJacobi
    {c d : ℝ} (hc : 0 < c) (j : ℕ) :
    C ((shiftedJacobiMonic j (c - 1) (d - 1)).eval 0) *
        normalizedShiftedJacobi j c d =
      shiftedJacobiMonic j (c - 1) (d - 1) := by
  have hchoose : 0 < Ring.choose ((j : ℝ) + c - 1) j := by
    apply ring_choose_pos
    linarith
  rw [shiftedJacobiMonic, normalizedShiftedJacobi, eval_mul, eval_C,
    shiftedJacobi_eval_zero,
    show (j : ℝ) + (c - 1) = (j : ℝ) + c - 1 by ring,
    ← mul_assoc, ← C_mul]
  congr 1
  field_simp [hchoose.ne']

end RealRooted.JacobiDeformation
