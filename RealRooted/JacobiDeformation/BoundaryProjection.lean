import RealRooted.JacobiDeformation.Kernel
import RealRooted.JacobiDeformation.Moment
import RealRooted.JacobiDeformation.Appell

/-!
# The diagonal coefficients of the Jacobi kernel

The boundary row of the Appell--Jacobi kernel at `z = 0` is a terminating
`₂F₁` in `1 - r`.  Pairing it with the value-one shifted-Jacobi polynomial
`φ_j`, the moment identity and a Chu--Vandermonde evaluation give

`ℓ(K_δ(·, 0) φ_j) = w_j(δ)`,

the kernel weight of `RealRooted.JacobiDeformation.Kernel`.  Since the kernel
expansion is diagonal, this identifies all of its coefficients.  The first
section proves the underlying alternating finite-sum identity for the weights.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-! ## The alternating diagonal-weight identity

Its only generic finite-sum input is the cleared terminating Chu--Vandermonde
identity.
-/

private theorem factorial_div_eq_fallingFactorial {m j : ℕ} (hjm : j ≤ m) :
    (m.factorial : ℝ) / ((m - j).factorial : ℝ) =
      fallingFactorial (m : ℝ) j := by
  rw [fallingFactorial_natCast]
  have hsub : m - j + j = m := Nat.sub_add_cancel hjm
  have h := Nat.factorial_mul_descFactorial (n := m) (k := j) hjm
  have hcast : ((m - j).factorial : ℝ) * (m.descFactorial j : ℝ) =
      (m.factorial : ℝ) := by
    simpa [hsub] using congrArg (fun x : ℕ => (x : ℝ)) h
  field_simp [Nat.factorial_ne_zero]
  linarith [hcast]

private theorem diagonal_weight_factorial_identity
    (m j : ℕ) (hjm : j ≤ m) (s : ℝ) (hs : 0 < s) (delta : ℝ) :
    (-1 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ k * (m.choose k : ℝ) *
            risingFactorial ((m : ℝ) + s - 1 + delta) k *
            fallingFactorial (k : ℝ) j / risingFactorial s (k + j)) =
      (m.factorial : ℝ) / ((m - j).factorial : ℝ) *
          risingFactorial ((m : ℝ) + s - 1 + delta) j *
          risingFactorial delta (m - j) / risingFactorial s (m + j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjm
  set b : ℝ := ((j + n : ℕ) : ℝ) + s - 1 + delta with hb
  have hsub : j + n - j = n := by lia
  rw [hsub]
  have hsplit : ∑ k ∈ Finset.range (j + n + 1),
      ((-1 : ℝ) ^ k * ((j + n).choose k : ℝ) * risingFactorial b k *
          fallingFactorial (k : ℝ) j / risingFactorial s (k + j)) =
      ∑ l ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ (j + l) * ((j + n).choose (j + l) : ℝ) *
            risingFactorial b (j + l) * fallingFactorial ((j + l : ℕ) : ℝ) j /
              risingFactorial s ((j + l) + j)) := by
    have hrw : j + n + 1 = j + (n + 1) := by lia
    rw [hrw, Finset.sum_range_add]
    have hzero : ∑ k ∈ Finset.range j,
        ((-1 : ℝ) ^ k * ((j + n).choose k : ℝ) * risingFactorial b k *
            fallingFactorial (k : ℝ) j / risingFactorial s (k + j)) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [fallingFactorial_natCast_eq_zero_of_lt (Finset.mem_range.mp hk)]
      ring
    rw [hzero, zero_add]
  have hterm : ∀ l ∈ Finset.range (n + 1),
      ((-1 : ℝ) ^ (j + l) * ((j + n).choose (j + l) : ℝ) *
          risingFactorial b (j + l) * fallingFactorial ((j + l : ℕ) : ℝ) j /
            risingFactorial s ((j + l) + j)) =
        ((-1 : ℝ) ^ j * ((j + n).descFactorial j : ℝ) *
            risingFactorial b j / risingFactorial s (j + n + j)) *
          ((-1 : ℝ) ^ l * (n.choose l : ℝ) *
            risingFactorial (b + (j : ℝ)) l *
            risingFactorial ((s + ((2 * j : ℕ) : ℝ)) + (l : ℝ)) (n - l)) := by
    intro l hl
    have hln : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have h1 : fallingFactorial ((j + l : ℕ) : ℝ) j =
        ((j + l).descFactorial j : ℝ) := fallingFactorial_natCast _ _
    have h2 : (((j + n).choose (j + l) : ℕ) : ℝ) *
        (((j + l).descFactorial j : ℕ) : ℝ) =
        (((j + n).descFactorial j : ℕ) : ℝ) * ((n.choose l : ℕ) : ℝ) := by
      have hchoose := Nat.choose_mul (n := j + n) (k := j + l) (s := j)
        (Nat.le_add_right j l)
      have h1' : j + n - j = n := by lia
      have h2' : j + l - j = l := by lia
      rw [h1', h2'] at hchoose
      calc
        (((j + n).choose (j + l) : ℕ) : ℝ) *
            (((j + l).descFactorial j : ℕ) : ℝ) =
            ((j.factorial : ℝ) * ((j + n).choose (j + l) : ℝ)) *
              ((j + l).choose j : ℝ) := by
              rw [Nat.descFactorial_eq_factorial_mul_choose]
              norm_num only [Nat.cast_mul]
              ring
        _ = (j.factorial : ℝ) *
            (((j + n).choose (j + l) : ℝ) * ((j + l).choose j : ℝ)) := by ring
        _ = (j.factorial : ℝ) * ((j + n).choose j : ℝ) * (n.choose l : ℝ) := by
              rw [show ((j + n).choose (j + l) : ℝ) * ((j + l).choose j : ℝ) =
                ((j + n).choose j : ℝ) * (n.choose l : ℝ) by
                  exact_mod_cast hchoose]
              ring
        _ = (((j + n).descFactorial j : ℕ) : ℝ) * (n.choose l : ℝ) := by
              rw [Nat.descFactorial_eq_factorial_mul_choose]
              norm_num only [Nat.cast_mul]
    have h3 : risingFactorial b (j + l) =
        risingFactorial b j * risingFactorial (b + (j : ℝ)) l := by
      simpa using risingFactorial_add b j l
    have h4 : risingFactorial s (j + n + j) =
        risingFactorial s ((j + l) + j) *
          risingFactorial ((s + ((2 * j : ℕ) : ℝ)) + (l : ℝ)) (n - l) := by
      have he : j + n + j = ((j + l) + j) + (n - l) := by lia
      rw [he, risingFactorial_add]
      have hcast : (((j + l) + j : ℕ) : ℝ) = ((2 * j : ℕ) : ℝ) + (l : ℝ) := by
        push_cast
        ring
      rw [hcast]
      ring_nf
    have hden1 : risingFactorial s ((j + l) + j) ≠ 0 :=
      (risingFactorial_pos _ hs).ne'
    have hden2 : risingFactorial s (j + n + j) ≠ 0 :=
      (risingFactorial_pos _ hs).ne'
    have hpow : (-1 : ℝ) ^ (j + l) = (-1 : ℝ) ^ j * (-1 : ℝ) ^ l :=
      pow_add _ _ _
    rw [h1, hpow, h3, div_mul_eq_mul_div, div_eq_div_iff hden1 hden2, h4]
    linear_combination ((-1 : ℝ) ^ j * (-1 : ℝ) ^ l * risingFactorial b j *
      risingFactorial (b + (j : ℝ)) l *
      risingFactorial ((s + ((2 * j : ℕ) : ℝ)) + (l : ℝ)) (n - l) *
        risingFactorial s ((j + l) + j)) * h2
  rw [hsplit, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hV := sum_range_neg_one_pow_mul_choose_mul_risingFactorial (b + (j : ℝ))
    (s + ((2 * j : ℕ) : ℝ)) n
  rw [hV]
  have harg : (s + ((2 * j : ℕ) : ℝ)) - (b + (j : ℝ)) =
      1 - delta - (n : ℝ) := by
    rw [hb]
    push_cast
    ring
  rw [harg, risingFactorial_one_sub]
  have hsign : (-1 : ℝ) ^ (j + n) *
      ((-1 : ℝ) ^ j * (-1 : ℝ) ^ n) = 1 := by
    rw [pow_add]
    have h1 : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have h2 : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    calc
      (-1 : ℝ) ^ j * (-1 : ℝ) ^ n *
          ((-1 : ℝ) ^ j * (-1 : ℝ) ^ n) =
          ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) *
            ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) := by ring
      _ = 1 := by rw [h1, h2]; norm_num
  have hfac := factorial_div_eq_fallingFactorial
    (m := j + n) (j := j) (by lia)
  rw [fallingFactorial_natCast, hsub] at hfac
  rw [← hfac]
  linear_combination (((j + n).factorial : ℝ) / (n.factorial : ℝ) *
    risingFactorial b j * risingFactorial delta n /
      risingFactorial s (j + n + j)) * hsign

/-- The alternating diagonal-weight sum is the finite Jacobi kernel
weight.  No sign or nonvanishing condition on `delta` is used. -/
theorem diagonal_weight_identity
    (m j : ℕ) (hjm : j ≤ m) (s : ℝ) (hs : 0 < s) (delta : ℝ) :
    (-1 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ k * (m.choose k : ℝ) *
            risingFactorial ((m : ℝ) + s - 1 + delta) k *
            fallingFactorial (k : ℝ) j / risingFactorial s (k + j)) =
      kernelWeight m delta s j := by
  rw [diagonal_weight_factorial_identity m j hjm s hs delta,
    factorial_div_eq_fallingFactorial hjm]
  rfl

/-! ## Boundary projection of the finite Appell--Jacobi kernel

We identify the Jacobi projection of the `z = 0` Appell row with the finite
kernel weight, and package the normalized Jacobi norm and the orthogonality
facts used to read off diagonal coefficients.
-/

/-- The squared norm of the value-one shifted-Jacobi polynomial for the
normalized Jacobi functional. -/
def normalizedJacobiNorm (c d : ℝ) (j : ℕ) : ℝ :=
  normalizedJacobiFunctional c d
    (normalizedShiftedJacobi j c d * normalizedShiftedJacobi j c d)

/-- The normalized Jacobi squared norm is strictly positive in the classical
parameter range. -/
theorem normalizedJacobiNorm_pos {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j : ℕ) :
    0 < normalizedJacobiNorm c d j := by
  let p := normalizedShiftedJacobi j c d
  have hp : p ≠ 0 := by
    intro hp0
    have heval := congrArg (fun q : ℝ[X] => q.eval 0) hp0
    rw [normalizedShiftedJacobi_eval_zero hc j] at heval
    simp at heval
  have hpair : 0 < shiftedJacobiInner (c - 1) (d - 1) p p := by
    have hpos := shiftedJacobiMomentPairingBilinForm_posDef
      (α := c - 1) (β := d - 1) (by linarith) (by linarith) p hp
    simpa only [LinearMap.BilinMap.toQuadraticMap_apply,
      Polynomial.momentPairingBilinForm_apply, shiftedJacobiInner] using hpos
  have hmass : 0 < shiftedJacobiMoment (c - 1) (d - 1) 0 :=
    shiftedJacobiMoment_zero_pos (by linarith) (by linarith)
  change 0 < shiftedJacobiFunctional (c - 1) (d - 1) (p * p) /
    shiftedJacobiMoment (c - 1) (d - 1) 0
  change 0 < shiftedJacobiFunctional (c - 1) (d - 1) (p * p) at hpair
  exact div_pos hpair hmass

/-- Distinct value-one shifted-Jacobi polynomials are orthogonal for the
normalized Jacobi functional. -/
theorem normalizedJacobiFunctional_pairwise_orthogonal
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {j k : ℕ} (hjk : j ≠ k) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d * normalizedShiftedJacobi k c d) = 0 := by
  have horth := shiftedJacobi_pairwise_orthogonal
    (α := c - 1) (β := d - 1) (by linarith) (by linarith) hjk
  unfold normalizedJacobiFunctional normalizedShiftedJacobi
  rw [show
      (C (Ring.choose ((j : ℝ) + c - 1) j)⁻¹ * shiftedJacobi j (c - 1) (d - 1)) *
          (C (Ring.choose ((k : ℝ) + c - 1) k)⁻¹ *
            shiftedJacobi k (c - 1) (d - 1)) =
        C ((Ring.choose ((j : ℝ) + c - 1) j)⁻¹ *
          (Ring.choose ((k : ℝ) + c - 1) k)⁻¹) *
            (shiftedJacobi j (c - 1) (d - 1) *
              shiftedJacobi k (c - 1) (d - 1)) by rw [C_mul]; ring]
  rw [shiftedJacobiFunctional_C_mul]
  change _ * shiftedJacobiInner (c - 1) (d - 1)
    (shiftedJacobi j (c - 1) (d - 1))
    (shiftedJacobi k (c - 1) (d - 1)) / _ = 0
  rw [horth]
  ring

/-- Projecting the `z = 0` Appell row against the `j`-th normalized
Jacobi polynomial gives the concrete finite kernel weight. -/
theorem normalizedJacobiFunctional_appellJacobiKernel_zero
    {m j : ℕ} (hjm : j ≤ m) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (δ : ℝ) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d *
          appellJacobiKernel m ((m : ℝ) + c + d - 1 + δ) c d 0) =
      kernelWeight m δ (c + d) j := by
  rw [appellJacobiKernel_zero, Finset.mul_sum,
    normalizedJacobiFunctional_sum]
  have hdRise (k : ℕ) : risingFactorial d k ≠ 0 :=
    (risingFactorial_pos k hd).ne'
  have hterm : ∀ k ∈ Finset.range (m + 1),
      normalizedJacobiFunctional c d
          (normalizedShiftedJacobi j c d *
            (C (appellKernelCoefficient m ((m : ℝ) + c + d - 1 + δ) c d 0 k) *
              (1 - X) ^ k)) =
        (-1 : ℝ) ^ (m + k) * (m.choose k : ℝ) *
          risingFactorial ((m : ℝ) + c + d - 1 + δ) k *
            fallingFactorial (k : ℝ) j /
              risingFactorial (c + d) (k + j) := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show normalizedShiftedJacobi j c d *
        (C (appellKernelCoefficient m ((m : ℝ) + c + d - 1 + δ) c d 0 k) *
          (1 - X) ^ k) =
      C (appellKernelCoefficient m ((m : ℝ) + c + d - 1 + δ) c d 0 k) *
        (normalizedShiftedJacobi j c d * (1 - X) ^ k) by ring]
    rw [normalizedJacobiFunctional_C_mul,
      appellKernelCoefficient_zero_left m k _ c d hkm,
      normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow hc hd]
    field_simp [hdRise k]
  rw [Finset.sum_congr rfl hterm]
  have hweight := diagonal_weight_identity m j hjm (c + d) (by linarith) δ
  rw [← hweight]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_add]
  ring_nf

end RealRooted.JacobiDeformation
