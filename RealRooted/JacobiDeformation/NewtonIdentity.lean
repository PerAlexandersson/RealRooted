import RealRooted.JacobiDeformation.Kernel

/-!
# The Newton expansion of the Jacobi kernel weights

For `j ≤ m`, `s > 0` and `0 < δ < 1`, the normalized kernel weights have the
positive Newton expansion

`w_j(δ) / w_0(δ) = ∑_{k ≤ j} a_k(δ) Λ_k(λ_j)`

in the Newton products `Λ_k` of the Jacobi eigenvalues
(`sum_newtonExpansionTerm_eq_kernelWeight_div_kernelWeight_zero`).  Since
`Λ_k(λ_j) = j^{(k)} (j + s - 1)_k`, the right-hand side is a terminating
balanced hypergeometric sum; it is evaluated by the Pfaff--Saalschütz
identity `risingFactorial_pfaffSaalschutz`, after reflecting the negative
rising factorials.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The Pochhammer form of the Newton expansion: for `j ≤ m`, `s > 0` and
`δ > 0`,

`∑_{k ≤ j} (1 - δ)_k j^{(k)} (j + s - 1)_k / ((m + δ - 1)^{(k)} (m + s)_k k!) =
  m^{(j)} (m + s - 1 + δ)_j / ((m + δ - 1)^{(j)} (m + s)_j)`,

where `x^{(k)}` is the falling factorial.  Every denominator is nonzero because
the smallest factor of `(m + δ - 1)^{(k)}` is `m - k + δ ≥ δ > 0`.  After
reflecting the negative rising factorials, this is the Pfaff--Saalschütz
identity. -/
private theorem sum_newton_pochhammer_eq (m j : ℕ) (hjm : j ≤ m) (s delta : ℝ) (hs : 0 < s)
    (hd0 : 0 < delta) :
    ∑ k ∈ Finset.range (j + 1),
        (risingFactorial (1 - delta) k * fallingFactorial (j : ℝ) k * risingFactorial ((j : ℝ) +
            s - 1) k) /
          (fallingFactorial ((m : ℝ) + delta - 1) k * risingFactorial ((m : ℝ) + s) k *
              (k.factorial : ℝ))
      = (fallingFactorial (m : ℝ) j * risingFactorial ((m : ℝ) + s - 1 + delta) j) /
          (fallingFactorial ((m : ℝ) + delta - 1) j * risingFactorial ((m : ℝ) + s) j) := by
  -- positivity of the denominators
  have hposR : ∀ k : ℕ, 0 < risingFactorial ((m : ℝ) + s) k := by
    intro k
    rw [risingFactorial_eq_prod]
    refine Finset.prod_pos fun l _ => ?_
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    linarith
  have hposF : ∀ k : ℕ, k ≤ m → 0 < fallingFactorial ((m : ℝ) + delta - 1) k := by
    intro k hk
    rw [fallingFactorial_eq_prod]
    refine Finset.prod_pos fun l hl => ?_
    simp only [Finset.mem_range] at hl
    have h1 : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hl
    have h2 : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
    linarith
  have hsq : ∀ k : ℕ, ((-1 : ℝ)) ^ k * ((-1 : ℝ)) ^ k = 1 := by
    intro k; rw [← mul_pow]; norm_num
  -- the Pfaff–Saalschütz parameters
  set a : ℝ := (j : ℝ) + s - 1 with ha
  set b : ℝ := 1 - delta with hb
  set c : ℝ := 1 - (m : ℝ) - delta with hc
  -- the two "reflection" identities for the `j`-th risingFactorial factorials
  have hCj : risingFactorial c j = (-1) ^ j * fallingFactorial ((m : ℝ) + delta - 1) j := by
    have : c = -((m : ℝ) + delta - 1) := by rw [hc]; ring
    rw [this, risingFactorial_neg]
  have hDj : risingFactorial (c - a - b) j = (-1) ^ j * risingFactorial ((m : ℝ) + s) j := by
    have : c - a - b = 1 - ((m : ℝ) + s) - (j : ℝ) := by rw [hc, ha, hb]; ring
    rw [this, risingFactorial_one_sub]
  have hCjne : risingFactorial c j ≠ 0 := by
    rw [hCj]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (hposF j hjm))
  have hDjne : risingFactorial (c - a - b) j ≠ 0 := by
    rw [hDj]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (hposR j))
  -- rewrite every summand as a Pfaff–Saalschütz summand divided by a constant
  have hterm : ∀ k ∈ Finset.range (j + 1),
      (risingFactorial b k * fallingFactorial (j : ℝ) k * risingFactorial a k) /
          (fallingFactorial ((m : ℝ) + delta - 1) k * risingFactorial ((m : ℝ) + s) k *
              (k.factorial : ℝ))
        = ((j.choose k : ℝ) * (risingFactorial a k * risingFactorial b k * risingFactorial (c +
            (k : ℝ)) (j - k) *
            risingFactorial (c - a - b) (j - k))) / (risingFactorial c j * risingFactorial (c -
                a - b) j) := by
    intro k hk
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hkm : k ≤ m := le_trans hk hjm
    have hFne : fallingFactorial ((m : ℝ) + delta - 1) k ≠ 0 := ne_of_gt (hposF k hkm)
    have hRne : risingFactorial ((m : ℝ) + s) k ≠ 0 := ne_of_gt (hposR k)
    have hfacne : (k.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    have e1 : risingFactorial c k * risingFactorial (c + (k : ℝ)) (j - k) =
        risingFactorial c j := by
      rw [← risingFactorial_add]
      congr 1
      lia
    have e2 : risingFactorial (c - a - b) (j - k) * ((-1) ^ k * risingFactorial ((m : ℝ) + s) k)
        = risingFactorial (c - a - b) j := by
      have harg : (c - a - b) + ((j - k : ℕ) : ℝ) = 1 - ((m : ℝ) + s) - (k : ℝ) := by
        have hcast : ((j - k : ℕ) : ℝ) = (j : ℝ) - (k : ℝ) := by
          push_cast [Nat.cast_sub hk]; ring
        rw [hc, ha, hb, hcast]; ring
      have hsplit : risingFactorial (c - a - b) ((j - k) + k)
          = risingFactorial (c - a - b) (j - k) * risingFactorial ((c - a - b) + ((j -
              k : ℕ) : ℝ)) k :=
        risingFactorial_add _ _ _
      rw [harg, risingFactorial_one_sub] at hsplit
      rw [← hsplit]
      congr 1
      lia
    have e3 : risingFactorial c k = (-1) ^ k * fallingFactorial ((m : ℝ) + delta - 1) k := by
      have : c = -((m : ℝ) + delta - 1) := by rw [hc]; ring
      rw [this, risingFactorial_neg]
    have e4 : (j.choose k : ℝ) * (k.factorial : ℝ) = fallingFactorial (j : ℝ) k :=
      choose_mul_factorial_eq_fallingFactorial j k
    have e23 : risingFactorial c j * risingFactorial (c - a - b) j
        = (fallingFactorial ((m : ℝ) + delta - 1) k * risingFactorial ((m : ℝ) + s) k) *
          (risingFactorial (c + (k : ℝ)) (j - k) * risingFactorial (c - a - b) (j - k)) := by
      rw [← e1, ← e2, e3]
      linear_combination (fallingFactorial ((m : ℝ) + delta - 1) k * risingFactorial ((m : ℝ) +
          s) k *
        risingFactorial (c + (k : ℝ)) (j - k) * risingFactorial (c - a - b) (j - k)) * hsq k
    rw [eq_div_iff (mul_ne_zero hCjne hDjne), e23, ← e4]
    field_simp
  have hsum : (∑ k ∈ Finset.range (j + 1), (risingFactorial b k * fallingFactorial (j : ℝ) k *
      risingFactorial a k) /
        (fallingFactorial ((m : ℝ) + delta - 1) k * risingFactorial ((m : ℝ) + s) k *
            (k.factorial : ℝ)))
      = ∑ k ∈ Finset.range (j + 1),
          ((j.choose k : ℝ) * (risingFactorial a k * risingFactorial b k * risingFactorial (c +
              (k : ℝ)) (j - k) *
            risingFactorial (c - a - b) (j - k))) / (risingFactorial c j * risingFactorial (c -
                a - b) j) :=
    Finset.sum_congr rfl hterm
  rw [hsum, ← Finset.sum_div, risingFactorial_pfaffSaalschutz j a b c]
  -- finally, identify the closed form
  have hA : risingFactorial (c - a) j =
      (-1) ^ j * risingFactorial ((m : ℝ) + s - 1 + delta) j := by
    have : c - a = 1 - ((m : ℝ) + s - 1 + delta) - (j : ℝ) := by rw [hc, ha]; ring
    rw [this, risingFactorial_one_sub]
  have hB : risingFactorial (c - b) j = (-1) ^ j * fallingFactorial (m : ℝ) j := by
    have : c - b = -(m : ℝ) := by rw [hc, hb]; ring
    rw [this, risingFactorial_neg]
  rw [hA, hB, hCj, hDj]
  have hFne : fallingFactorial ((m : ℝ) + delta - 1) j ≠ 0 := ne_of_gt (hposF j hjm)
  have hRne : risingFactorial ((m : ℝ) + s) j ≠ 0 := ne_of_gt (hposR j)
  rw [div_eq_div_iff (by rw [← hCj, ← hDj]; exact mul_ne_zero hCjne hDjne)
    (mul_ne_zero hFne hRne)]
  ring

/-- The Newton expansion of the kernel weights: evaluating the Newton
polynomial at `λ_j` gives the normalized Jacobi kernel weight `w_j / w_0`. -/
theorem sum_newtonExpansionTerm_eq_kernelWeight_div_kernelWeight_zero
    {m j : ℕ} {δ s : ℝ} (hjm : j ≤ m) (hδ : 0 < δ) (hs : 0 < s) :
    ∑ k ∈ Finset.range (j + 1), newtonExpansionTerm m δ s j k =
      kernelWeight m δ s j / kernelWeight m δ s 0 := by
  calc
    ∑ k ∈ Finset.range (j + 1), newtonExpansionTerm m δ s j k =
        ∑ k ∈ Finset.range (j + 1),
          (risingFactorial (1 - δ) k * fallingFactorial (j : ℝ) k *
              risingFactorial ((j : ℝ) + s - 1) k) /
            (fallingFactorial ((m : ℝ) + δ - 1) k *
              risingFactorial ((m : ℝ) + s) k * (k.factorial : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [newtonExpansionTerm, newtonCoefficient]
          unfold fallingFactorial
          ring
    _ = fallingFactorial (m : ℝ) j *
          risingFactorial ((m : ℝ) + s - 1 + δ) j /
        (fallingFactorial ((m : ℝ) + δ - 1) j *
          risingFactorial ((m : ℝ) + s) j) :=
      sum_newton_pochhammer_eq m j hjm s δ hs hδ
    _ = kernelWeight m δ s j / kernelWeight m δ s 0 := by
      unfold fallingFactorial
      exact (kernelWeight_div_kernelWeight_zero hjm hδ hs).symm

end RealRooted.JacobiDeformation
