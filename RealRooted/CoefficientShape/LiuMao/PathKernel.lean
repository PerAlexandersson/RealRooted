import RealRooted.CoefficientShape.LiuMao.Elevation

/-!
# The lattice-path kernel preserves LC-NIZ

We prove (Liu–Mao, Proposition 3.4 / Corollary 3.5) that the kernel
`K(i, k) = C(i + k, i) * C((m - i) + (d - k), m - i)` maps nonnegative log-concave sequences
without internal zeros on `[0, d]` to such sequences on `[0, m]`.

The proof follows the paper: after degree elevation to level `n` (which preserves LC-NIZ) and
degree reduction back to level `m` (which also preserves LC-NIZ) we obtain an LC-NIZ sequence
which converges, as `n → ∞`, to a positive multiple of the image under the kernel.  Instead of
integrals we use the exact identity "reduction maps the level-`n` moment vector to the
level-`(n-1)` moment vector" together with an explicit `O(1/n)` estimate between the moment
vector and the Bernstein coefficients at level `n`.
-/

open Finset Filter Topology

namespace RealRooted.LiuMao

/-! ### Falling and rising products -/

/-- Falling product `x (x - 1) ⋯ (x - m + 1)`. -/
def desc (x : ℝ) (m : ℕ) : ℝ := ∏ t ∈ range m, (x - t)

/-- Rising product `x (x + 1) ⋯ (x + m - 1)`. -/
def rise (x : ℝ) (m : ℕ) : ℝ := ∏ t ∈ range m, (x + t)

private theorem desc_succ (x : ℝ) (m : ℕ) : desc x (m + 1) = desc x m * (x - m) := by
  unfold desc; rw [prod_range_succ]

private theorem desc_succ' (x : ℝ) (m : ℕ) : desc x (m + 1) = x * desc (x - 1) m := by
  unfold desc; rw [prod_range_succ']
  simp only [Nat.cast_zero, sub_zero, Nat.cast_succ]
  rw [mul_comm]; congr 1
  apply prod_congr rfl; intro t _; ring

private theorem rise_succ (x : ℝ) (m : ℕ) : rise x (m + 1) = rise x m * (x + m) := by
  unfold rise; rw [prod_range_succ]

private theorem rise_succ' (x : ℝ) (m : ℕ) : rise x (m + 1) = x * rise (x + 1) m := by
  unfold rise; rw [prod_range_succ']
  simp only [Nat.cast_zero, add_zero, Nat.cast_succ]
  rw [mul_comm]; congr 1
  apply prod_congr rfl; intro t _; ring

/-- Splitting a falling product. -/
theorem desc_add (x : ℝ) (k l : ℕ) : desc x (k + l) = desc x k * desc (x - k) l := by
  unfold desc; rw [prod_range_add]; congr 1
  apply prod_congr rfl; intro t _; push_cast; ring

/-- Splitting a rising product. -/
theorem rise_add (x : ℝ) (k l : ℕ) : rise x (k + l) = rise x k * rise (x + k) l := by
  unfold rise; rw [prod_range_add]; congr 1
  apply prod_congr rfl; intro t _; push_cast; ring

private theorem desc_nat_eq_zero {a k : ℕ} (h : a < k) : desc (a : ℝ) k = 0 :=
  prod_eq_zero (mem_range.mpr h) (sub_self _)

private theorem desc_self (a : ℕ) : desc (a : ℝ) a = (a.factorial : ℝ) := by
  induction a with
  | zero => simp [desc]
  | succ a ih =>
    rw [desc_succ', Nat.factorial_succ]
    push_cast
    rw [show (a : ℝ) + 1 - 1 = a by ring, ih]

private theorem desc_pos {x : ℝ} {m : ℕ} (h : (m : ℝ) ≤ x) : 0 < desc x m := by
  unfold desc
  apply prod_pos
  intro t ht
  rw [mem_range] at ht
  have : (t : ℝ) + 1 ≤ m := by exact_mod_cast ht
  linarith

/-- A rising product of a positive number is positive. -/
theorem rise_pos {x : ℝ} (hx : 0 < x) (m : ℕ) : 0 < rise x m := by
  unfold rise
  apply prod_pos
  intro t _
  positivity

/-- A rising product starting at a natural number plus one is a binomial times a factorial. -/
theorem rise_nat_add_one (a k : ℕ) :
    rise ((a : ℝ) + 1) k = (k.factorial : ℝ) * ((a + k).choose a : ℝ) := by
  have h1 : rise ((a : ℝ) + 1) k = ((a + 1).ascFactorial k : ℝ) := by
    induction k with
    | zero => simp [rise]
    | succ k ih =>
      rw [rise_succ, ih, Nat.ascFactorial_succ]
      push_cast; ring
  rw [h1, Nat.ascFactorial_eq_factorial_mul_choose, Nat.choose_symm_add]
  push_cast; ring

/-! ### The explicit level-`n` vectors -/

/-- Bernstein coefficients at level `n` of the `k`-th Bernstein basis polynomial of degree `d`
(divided by `C(d, k)`). -/
noncomputable def betaK (d n : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  desc x k * desc ((n : ℝ) - x) (d - k) / desc (n : ℝ) d

/-- Moments at level `n` of the `k`-th Bernstein basis polynomial of degree `d`
(divided by `C(d, k)`). -/
noncomputable def gammaK (d n : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  rise (x + 1) k * rise ((n : ℝ) - x + 1) (d - k) / rise ((n : ℝ) + 2) d

private theorem betaK_elev {d n k : ℕ} (hk : k ≤ d) (hn : d ≤ n) (x : ℝ) :
    x * betaK d n (x - 1) k + ((n : ℝ) + 1 - x) * betaK d n x k =
      ((n : ℝ) + 1) * betaK d (n + 1) x k := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hl : k + l - k = l := by lia
  unfold betaK
  rw [hl]
  have hA : x * desc (x - 1) k = desc x k * (x - k) := by rw [← desc_succ', desc_succ]
  have hB : ((n : ℝ) + 1 - x) * desc ((n : ℝ) - x) l =
      desc ((n : ℝ) + 1 - x) l * ((n : ℝ) + 1 - x - l) := by
    rw [← desc_succ]; rw [desc_succ']; congr 2; ring
  have hE : ((n : ℝ) + 1) * desc (n : ℝ) (k + l) =
      desc ((n : ℝ) + 1) (k + l) * ((n : ℝ) + 1 - (k + l : ℕ)) := by
    rw [← desc_succ, desc_succ']; congr 2; ring
  have h1 : (n : ℝ) - (x - 1) = (n : ℝ) + 1 - x := by ring
  have h2 : ((n + 1 : ℕ) : ℝ) - x = (n : ℝ) + 1 - x := by push_cast; ring
  have h3 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [h1, h2, h3]
  have hp1 : 0 < desc (n : ℝ) (k + l) := desc_pos (by exact_mod_cast hn)
  have hp2 : 0 < desc ((n : ℝ) + 1) (k + l) := desc_pos (by push_cast at hn ⊢; exact_mod_cast (by
    have : ((k + l : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    linarith))
  push_cast at hE
  have step1 : x * (desc (x - 1) k * desc ((n : ℝ) + 1 - x) l / desc (n : ℝ) (k + l)) +
      ((n : ℝ) + 1 - x) * (desc x k * desc ((n : ℝ) - x) l / desc (n : ℝ) (k + l)) =
      ((x * desc (x - 1) k) * desc ((n : ℝ) + 1 - x) l +
        desc x k * (((n : ℝ) + 1 - x) * desc ((n : ℝ) - x) l)) / desc (n : ℝ) (k + l) := by ring
  rw [step1, hA, hB, mul_div_assoc', div_eq_div_iff hp1.ne' hp2.ne']
  linear_combination (-(desc x k * desc ((n : ℝ) + 1 - x) l)) * hE

private theorem gamma_core (x N : ℝ) (hN : 0 < N + 1) (k l : ℕ) :
    (N - x) * (rise (x + 1) k * rise (N - x + 1) l / rise (N + 2) (k + l)) +
      (x + 1) * (rise (x + 1 + 1) k * rise (N - x) l / rise (N + 2) (k + l)) =
    (N + 1) * (rise (x + 1) k * rise (N - x) l / rise (N + 1) (k + l)) := by
  have hA : (x + 1) * rise (x + 1 + 1) k = rise (x + 1) k * (x + 1 + k) := by
    rw [← rise_succ', rise_succ]
  have hB : (N - x) * rise (N - x + 1) l = rise (N - x) l * (N - x + l) := by
    rw [← rise_succ', rise_succ]
  have hE : rise (N + 1) (k + l) * (N + 1 + (k + l : ℕ)) = (N + 1) * rise (N + 2) (k + l) := by
    rw [← rise_succ, rise_succ']; congr 2; ring
  push_cast at hE
  have hp1 : 0 < rise (N + 1) (k + l) := rise_pos hN _
  have hp2 : 0 < rise (N + 2) (k + l) := rise_pos (by linarith) _
  have step1 : (N - x) * (rise (x + 1) k * rise (N - x + 1) l / rise (N + 2) (k + l)) +
      (x + 1) * (rise (x + 1 + 1) k * rise (N - x) l / rise (N + 2) (k + l)) =
      (rise (x + 1) k * ((N - x) * rise (N - x + 1) l) +
        ((x + 1) * rise (x + 1 + 1) k) * rise (N - x) l) / rise (N + 2) (k + l) := by ring
  rw [step1, hA, hB, mul_div_assoc', div_eq_div_iff hp2.ne' hp1.ne']
  linear_combination (rise (x + 1) k * rise (N - x) l) * hE

private theorem gammaK_red {d n k : ℕ} (hk : k ≤ d) (x : ℝ) :
    (((n + 1 : ℕ) : ℝ) - x) * gammaK d (n + 1) x k +
        (x + 1) * gammaK d (n + 1) (x + 1) k =
      (((n + 1 : ℕ) : ℝ) + 1) * gammaK d n x k := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hl : k + l - k = l := by lia
  unfold gammaK
  rw [hl]
  have := gamma_core x ((n : ℝ) + 1) (by positivity) k l
  push_cast
  rw [show (n : ℝ) + 1 - (x + 1) + 1 = (n : ℝ) + 1 - x by ring,
    show (n : ℝ) - x + 1 = (n : ℝ) + 1 - x by ring,
    show (n : ℝ) + 2 = (n : ℝ) + 1 + 1 by ring]
  exact this

/-- Bernstein coefficients at level `n` of `F = ∑ C(d,k) u_k t^k (1-t)^(d-k)`. -/
noncomputable def bvec (d : ℕ) (u : ℕ → ℝ) (n j : ℕ) : ℝ :=
  ∑ k ∈ range (d + 1), u k * (d.choose k : ℝ) * betaK d n j k

/-- Normalised moment vector at level `n` of `F`. -/
noncomputable def gvec (d : ℕ) (u : ℕ → ℝ) (n j : ℕ) : ℝ :=
  ∑ k ∈ range (d + 1), u k * (d.choose k : ℝ) * gammaK d n j k

/-- Iterated degree elevation, starting at level `d`. -/
noncomputable def bseq (d : ℕ) (u : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => u
  | r + 1 => Eop (d + r) (bseq d u r)

private theorem betaK_self {d j : ℕ} (hj : j ≤ d) : (d.choose j : ℝ) * betaK d d j j = 1 := by
  unfold betaK
  rw [show (d : ℝ) - j = ((d - j : ℕ) : ℝ) by rw [Nat.cast_sub hj], desc_self, desc_self, desc_self]
  have h := Nat.choose_mul_factorial_mul_factorial hj
  have h' : (d.choose j : ℝ) * (j.factorial : ℝ) * ((d - j).factorial : ℝ) = (d.factorial : ℝ) := by
    exact_mod_cast h
  have hf : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  field_simp
  linarith

private theorem betaK_self_ne {d j k : ℕ} (hj : j ≤ d) (hjk : k ≠ j) : betaK d d j k = 0 := by
  unfold betaK
  rcases lt_or_gt_of_ne hjk with h | h
  · rw [show (d : ℝ) - j = ((d - j : ℕ) : ℝ) by rw [Nat.cast_sub hj],
      desc_nat_eq_zero (show d - j < d - k by lia)]
    simp
  · rw [desc_nat_eq_zero h]; simp

/-- The iterated elevations are the Bernstein coefficients at the higher level. -/
theorem bseq_eq {d : ℕ} {u : ℕ → ℝ} : ∀ r j, j ≤ d + r → bseq d u r j = bvec d u (d + r) j := by
  intro r
  induction r with
  | zero =>
    intro j hj
    simp only [bseq, Nat.add_zero]
    unfold bvec
    rw [sum_eq_single j]
    · rw [mul_assoc, betaK_self (by lia), mul_one]
    · intro k hk hkj
      rw [mem_range] at hk
      rw [betaK_self_ne (by lia) hkj, mul_zero]
    · intro h; exact absurd (mem_range.mpr (by lia)) h
  | succ r ih =>
    intro j hj
    simp only [bseq]
    unfold Eop
    have e1 : (j : ℝ) * bseq d u r (j - 1) =
        (j : ℝ) * ∑ k ∈ range (d + 1),
          u k * (d.choose k : ℝ) * betaK d (d + r) ((j : ℝ) - 1) k := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp
      · rw [ih (j - 1) (by lia)]
        unfold bvec
        rw [show ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 by rw [Nat.cast_sub h]; simp]
    have e2 : ((((d + r : ℕ) : ℝ)) + 1 - j) * bseq d u r j =
        ((((d + r : ℕ) : ℝ)) + 1 - j) * bvec d u (d + r) j := by
      by_cases h : j ≤ d + r
      · rw [ih j h]
      · rw [show j = d + r + 1 by lia]; push_cast; ring
    rw [e1, e2]
    unfold bvec
    rw [mul_sum, mul_sum, ← sum_add_distrib, sum_div]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have := betaK_elev (d := d) (n := d + r) (k := k) (by lia) (by lia) (j : ℝ)
    rw [show d + (r + 1) = d + r + 1 by lia]
    rw [div_eq_iff (by positivity)]
    calc (j : ℝ) * (u k * (d.choose k : ℝ) * betaK d (d + r) ((j : ℝ) - 1) k) +
          ((((d + r : ℕ) : ℝ)) + 1 - j) * (u k * (d.choose k : ℝ) * betaK d (d + r) (j : ℝ) k)
        = u k * (d.choose k : ℝ) * ((j : ℝ) * betaK d (d + r) ((j : ℝ) - 1) k +
          ((((d + r : ℕ) : ℝ)) + 1 - j) * betaK d (d + r) (j : ℝ) k) := by ring
      _ = _ := by rw [this]; ring

/-- The iterated elevations are globally LC-NIZ. -/
theorem bseq_glcn {d : ℕ} {u : ℕ → ℝ} (hu : GLCN d u) : ∀ r, GLCN (d + r) (bseq d u r) := by
  intro r
  induction r with
  | zero => simpa [bseq] using hu
  | succ r ih =>
    simp only [bseq]
    rw [show d + (r + 1) = d + r + 1 by lia]
    exact ih.elev

private theorem gvec_red (d : ℕ) (u : ℕ → ℝ) (n j : ℕ) :
    Dop (n + 1) (gvec d u (n + 1)) j = gvec d u n j := by
  unfold Dop gvec
  rw [mul_sum, mul_sum, ← sum_add_distrib, sum_div]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  have := gammaK_red (d := d) (n := n) (k := k) (by lia) (j : ℝ)
  rw [div_eq_iff (by positivity)]
  push_cast at this ⊢
  calc ((n : ℝ) + 1 - j) * (u k * (d.choose k : ℝ) * gammaK d (n + 1) (j : ℝ) k) +
        ((j : ℝ) + 1) * (u k * (d.choose k : ℝ) * gammaK d (n + 1) ((j : ℝ) + 1) k)
      = u k * (d.choose k : ℝ) * (((n : ℝ) + 1 - j) * gammaK d (n + 1) (j : ℝ) k +
        ((j : ℝ) + 1) * gammaK d (n + 1) ((j : ℝ) + 1) k) := by ring
    _ = _ := by rw [this]; ring

/-- Iterated degree reduction from level `m + r` down to level `m`. -/
noncomputable def descend (m : ℕ) : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, v => v
  | r + 1, v => descend m r (Dop (m + r + 1) v)

/-- Iterated degree reduction preserves global LC-NIZ. -/
theorem descend_glcn (m : ℕ) : ∀ r (v : ℕ → ℝ), GLCN (m + r) v → GLCN m (descend m r v) := by
  intro r
  induction r with
  | zero => intro v hv; simpa [descend] using hv
  | succ r ih =>
    intro v hv
    simp only [descend]
    apply ih
    rw [show m + (r + 1) = m + r + 1 by lia] at hv
    exact hv.reduce

/-- Iterated degree reduction maps the moment vector at level `m + r` to level `m`. -/
theorem descend_gvec (d : ℕ) (u : ℕ → ℝ) (m : ℕ) :
    ∀ r, descend m r (gvec d u (m + r)) = gvec d u m := by
  intro r
  induction r with
  | zero => simp [descend]
  | succ r ih =>
    simp only [descend]
    have : Dop (m + r + 1) (gvec d u (m + (r + 1))) = gvec d u (m + r) := by
      funext j
      rw [show m + (r + 1) = m + r + 1 by lia]
      exact gvec_red d u (m + r) j
    rw [this, ih]

/-- Degree reduction does not increase the sup-distance between two vectors. -/
theorem descend_contract (m : ℕ) : ∀ r (v v' : ℕ → ℝ) (B : ℝ),
    (∀ j, j ≤ m + r → |v j - v' j| ≤ B) → ∀ i, i ≤ m →
      |descend m r v i - descend m r v' i| ≤ B := by
  intro r
  induction r with
  | zero => intro v v' B h i hi; simpa [descend] using h i (by lia)
  | succ r ih =>
    intro v v' B h i hi
    simp only [descend]
    apply ih _ _ B _ i hi
    intro j hj
    unfold Dop
    have hj1 : (j : ℝ) ≤ (m + r : ℕ) := by exact_mod_cast hj
    have h1 := h j (by lia)
    have h2 := h (j + 1) (by lia)
    have hpos : (0 : ℝ) < ((m + r + 1 : ℕ) : ℝ) + 1 := by positivity
    rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have hc1 : (0 : ℝ) ≤ ((m + r + 1 : ℕ) : ℝ) - j := by push_cast at hj1 ⊢; linarith
    have hc2 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
    calc |(((m + r + 1 : ℕ) : ℝ) - j) * v j + ((j : ℝ) + 1) * v (j + 1) -
          ((((m + r + 1 : ℕ) : ℝ) - j) * v' j + ((j : ℝ) + 1) * v' (j + 1))|
        = |(((m + r + 1 : ℕ) : ℝ) - j) * (v j - v' j) +
            ((j : ℝ) + 1) * (v (j + 1) - v' (j + 1))| := by
          ring_nf
      _ ≤ |(((m + r + 1 : ℕ) : ℝ) - j) * (v j - v' j)| +
            |((j : ℝ) + 1) * (v (j + 1) - v' (j + 1))| :=
          abs_add_le _ _
      _ = (((m + r + 1 : ℕ) : ℝ) - j) * |v j - v' j| +
            ((j : ℝ) + 1) * |v (j + 1) - v' (j + 1)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hc1, abs_of_nonneg hc2]
      _ ≤ (((m + r + 1 : ℕ) : ℝ) - j) * B + ((j : ℝ) + 1) * B := by
          gcongr
      _ = B * (((m + r + 1 : ℕ) : ℝ) + 1) := by ring

end RealRooted.LiuMao

/-!
## The limit argument for the lattice-path kernel

An explicit `O(1/n)` estimate between Bernstein coefficients and moments at level `n`, and the
resulting proof that the lattice-path kernel preserves LC-NIZ.
-/

open Finset Filter Topology

namespace RealRooted.LiuMao

/-! ### Elementary estimates -/

private theorem factor_bound {x n α β c : ℝ} (hc : 1 ≤ c) (hn : 2 * c ≤ n) (hx0 : 0 ≤ x)
    (hxn : x ≤ n) (hα : |α| ≤ c) (hβ : |β| ≤ c) : |(x + α) / (n + β)| ≤ 3 := by
  rw [abs_le] at hα hβ
  have hpos : 0 < n + β := by linarith
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos, abs_le]
  constructor <;> linarith

private theorem factor_diff {x n α β α' β' c : ℝ} (hc : 1 ≤ c) (hn : 2 * c ≤ n) (hx0 : 0 ≤ x)
    (hxn : x ≤ n) (hα : |α| ≤ c) (hβ : |β| ≤ c) (hα' : |α'| ≤ c) (hβ' : |β'| ≤ c) :
    |(x + α) / (n + β) - (x + α') / (n + β')| ≤ 20 * c / n := by
  have hβ1 := abs_le.mp hβ
  have hβ1' := abs_le.mp hβ'
  have hp1 : 0 < n + β := by linarith
  have hp2 : 0 < n + β' := by linarith
  have hn0 : 0 < n := by linarith
  rw [div_sub_div _ _ hp1.ne' hp2.ne', abs_div, abs_of_pos (mul_pos hp1 hp2),
    div_le_div_iff₀ (mul_pos hp1 hp2) hn0]
  have hnum : |(x + α) * (n + β') - (n + β) * (x + α')| ≤ 5 * c * n := by
    have e : (x + α) * (n + β') - (n + β) * (x + α') =
        x * (β' - β) + n * (α - α') + (α * β' - α' * β) := by ring
    rw [e]
    have h1 : |x * (β' - β)| ≤ n * (2 * c) := by
      rw [abs_mul, abs_of_nonneg hx0]
      apply mul_le_mul hxn _ (abs_nonneg _) (by linarith)
      calc |β' - β| ≤ |β'| + |β| := abs_sub _ _
        _ ≤ 2 * c := by linarith
    have h2 : |n * (α - α')| ≤ n * (2 * c) := by
      rw [abs_mul, abs_of_pos hn0]
      apply mul_le_mul_of_nonneg_left _ hn0.le
      calc |α - α'| ≤ |α| + |α'| := abs_sub _ _
        _ ≤ 2 * c := by linarith
    have h3 : |α * β' - α' * β| ≤ 2 * c * c := by
      calc |α * β' - α' * β| ≤ |α * β'| + |α' * β| := abs_sub _ _
        _ = |α| * |β'| + |α'| * |β| := by rw [abs_mul, abs_mul]
        _ ≤ c * c + c * c := by
          gcongr
        _ = 2 * c * c := by ring
    calc |x * (β' - β) + n * (α - α') + (α * β' - α' * β)|
        ≤ |x * (β' - β) + n * (α - α')| + |α * β' - α' * β| := abs_add_le _ _
      _ ≤ |x * (β' - β)| + |n * (α - α')| + |α * β' - α' * β| := by
          gcongr; exact abs_add_le _ _
      _ ≤ n * (2 * c) + n * (2 * c) + 2 * c * c := by linarith
      _ ≤ 5 * c * n := by nlinarith
  have hden : n * n ≤ 4 * ((n + β) * (n + β')) := by nlinarith
  calc |(x + α) * (n + β') - (n + β) * (x + α')| * n ≤ 5 * c * n * n := by
        exact mul_le_mul_of_nonneg_right hnum hn0.le
    _ = 5 * c * (n * n) := by ring
    _ ≤ 5 * c * (4 * ((n + β) * (n + β'))) := by
        apply mul_le_mul_of_nonneg_left hden; linarith
    _ = 20 * c * ((n + β) * (n + β')) := by ring

private theorem abs_prod_le_pow {f : ℕ → ℝ} {M : ℝ} (m : ℕ) (hf : ∀ t, t < m → |f t| ≤ M) :
    |∏ t ∈ range m, f t| ≤ M ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, abs_mul, pow_succ]
    have hM : 0 ≤ M := le_trans (abs_nonneg _) (hf 0 (by lia))
    exact mul_le_mul (ih (fun t ht => hf t (by lia))) (hf m (by lia)) (abs_nonneg _)
      (pow_nonneg hM _)

private theorem abs_prod_sub_prod_le {f g : ℕ → ℝ} {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ) (m : ℕ)
    (hf : ∀ t, t < m → |f t| ≤ M) (hg : ∀ t, t < m → |g t| ≤ M)
    (hfg : ∀ t, t < m → |f t - g t| ≤ δ) :
    |∏ t ∈ range m, f t - ∏ t ∈ range m, g t| ≤ m * M ^ m * δ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, prod_range_succ]
    have ih' := ih (fun t ht => hf t (by lia)) (fun t ht => hg t (by lia))
      (fun t ht => hfg t (by lia))
    have hgp := abs_prod_le_pow m (fun t ht => hg t (by lia))
    have hfm := hf m (by lia)
    have hfgm := hfg m (by lia)
    have hMm : M ^ m ≤ M ^ (m + 1) := pow_le_pow_right₀ hM (by lia)
    have hM0 : 0 ≤ M := by linarith
    calc |(∏ t ∈ range m, f t) * f m - (∏ t ∈ range m, g t) * g m|
        = |(∏ t ∈ range m, f t - ∏ t ∈ range m, g t) * f m +
            (∏ t ∈ range m, g t) * (f m - g m)| := by ring_nf
      _ ≤ |(∏ t ∈ range m, f t - ∏ t ∈ range m, g t) * f m| +
            |(∏ t ∈ range m, g t) * (f m - g m)| := abs_add_le _ _
      _ = |∏ t ∈ range m, f t - ∏ t ∈ range m, g t| * |f m| +
            |∏ t ∈ range m, g t| * |f m - g m| := by rw [abs_mul, abs_mul]
      _ ≤ (m * M ^ m * δ) * M + M ^ m * δ := by
          gcongr
      _ = m * M ^ (m + 1) * δ + M ^ m * δ := by ring
      _ ≤ m * M ^ (m + 1) * δ + M ^ (m + 1) * δ := by gcongr
      _ = ((m + 1 : ℕ) : ℝ) * M ^ (m + 1) * δ := by push_cast; ring

/-! ### Factorisations of `betaK` and `gammaK` -/

private theorem betaK_eq_prod {d n k : ℕ} (hk : k ≤ d) (hn : d ≤ n) (x : ℝ) :
    betaK d n x k = (∏ t ∈ range k, (x + (-(t : ℝ))) / ((n : ℝ) + (-(t : ℝ)))) *
      ∏ t ∈ range (d - k), (((n : ℝ) - x) + (-(t : ℝ))) / ((n : ℝ) + (-((k : ℝ) + t))) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  unfold betaK
  rw [show k + l - k = l by lia, desc_add]
  unfold desc
  rw [prod_div_distrib, prod_div_distrib, mul_div_mul_comm]
  congr 2
  exact prod_congr rfl fun t _ => by ring

private theorem gammaK_eq_prod {d n k : ℕ} (hk : k ≤ d) (x : ℝ) :
    gammaK d n x k = (∏ t ∈ range k, (x + (1 + (t : ℝ))) / ((n : ℝ) + (2 + (t : ℝ)))) *
      ∏ t ∈ range (d - k), (((n : ℝ) - x) + (1 + (t : ℝ))) / ((n : ℝ) + (2 + ((k : ℝ) + t))) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  unfold gammaK
  rw [show k + l - k = l by lia, rise_add]
  unfold rise
  rw [prod_div_distrib, prod_div_distrib, mul_div_mul_comm]
  congr 2 <;> exact prod_congr rfl fun t _ => by ring

private theorem betaK_sub_gammaK {d n k : ℕ} (hk : k ≤ d) (hn : 2 * (2 * (d : ℝ) + 2) ≤ n) {x : ℝ}
    (hx0 : 0 ≤ x) (hxn : x ≤ n) :
    |betaK d n x k - gammaK d n x k| ≤ d * 3 ^ d * (20 * (2 * (d : ℝ) + 2) / n) := by
  set c : ℝ := 2 * (d : ℝ) + 2 with hc
  have hc1 : 1 ≤ c := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hdn : d ≤ n := by
    have : (d : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hn0 : 0 < (n : ℝ) := by linarith
  have hδ : 0 ≤ 20 * c / n := by positivity
  have hkd : (k : ℝ) ≤ d := by exact_mod_cast hk
  rw [betaK_eq_prod hk hdn, gammaK_eq_prod hk]
  set A := ∏ t ∈ range k, (x + (-(t : ℝ))) / ((n : ℝ) + (-(t : ℝ)))
  set B := ∏ t ∈ range (d - k), (((n : ℝ) - x) + (-(t : ℝ))) / ((n : ℝ) + (-((k : ℝ) + t)))
  set A' := ∏ t ∈ range k, (x + (1 + (t : ℝ))) / ((n : ℝ) + (2 + (t : ℝ)))
  set B' := ∏ t ∈ range (d - k), (((n : ℝ) - x) + (1 + (t : ℝ))) / ((n : ℝ) + (2 + ((k : ℝ) + t)))
  have ht1 : ∀ t, t < k → (t : ℝ) + 2 ≤ c := by
    intro t ht; have : (t : ℝ) + 1 ≤ k := by exact_mod_cast ht
    linarith
  have ht2 : ∀ t, t < d - k → (k : ℝ) + t + 2 ≤ c := by
    intro t ht; have : ((k + t : ℕ) : ℝ) + 1 ≤ d := by exact_mod_cast (show k + t + 1 ≤ d by lia)
    push_cast at this; linarith
  have hnx0 : 0 ≤ (n : ℝ) - x := by linarith
  have hnxn : (n : ℝ) - x ≤ n := by linarith
  have abs_le_of {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ c) : |y| ≤ c := by
    rw [abs_of_nonneg h0]; exact h1
  have abs_neg_le_of {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ c) : |-y| ≤ c := by
    rw [abs_neg, abs_of_nonneg h0]; exact h1
  have hA : |A - A'| ≤ k * 3 ^ k * (20 * c / n) := by
    apply abs_prod_sub_prod_le (by norm_num) hδ k
    · intro t ht
      exact factor_bound hc1 hn hx0 hxn (abs_neg_le_of (by positivity) (by linarith [ht1 t ht]))
        (abs_neg_le_of (by positivity) (by linarith [ht1 t ht]))
    · intro t ht
      exact factor_bound hc1 hn hx0 hxn (abs_le_of (by positivity) (by linarith [ht1 t ht]))
        (abs_le_of (by positivity) (by linarith [ht1 t ht]))
    · intro t ht
      exact factor_diff hc1 hn hx0 hxn (abs_neg_le_of (by positivity) (by linarith [ht1 t ht]))
        (abs_neg_le_of (by positivity) (by linarith [ht1 t ht]))
        (abs_le_of (by positivity) (by linarith [ht1 t ht]))
        (abs_le_of (by positivity) (by linarith [ht1 t ht]))
  have hB : |B - B'| ≤ ((d - k : ℕ) : ℝ) * 3 ^ (d - k) * (20 * c / n) := by
    apply abs_prod_sub_prod_le (by norm_num) hδ (d - k)
    · intro t ht
      exact factor_bound hc1 hn hnx0 hnxn (abs_neg_le_of (by positivity) (by linarith [ht2 t ht]))
        (abs_neg_le_of (by positivity) (by linarith [ht2 t ht]))
    · intro t ht
      exact factor_bound hc1 hn hnx0 hnxn (abs_le_of (by positivity) (by linarith [ht2 t ht]))
        (abs_le_of (by positivity) (by linarith [ht2 t ht]))
    · intro t ht
      exact factor_diff hc1 hn hnx0 hnxn (abs_neg_le_of (by positivity) (by linarith [ht2 t ht]))
        (abs_neg_le_of (by positivity) (by linarith [ht2 t ht]))
        (abs_le_of (by positivity) (by linarith [ht2 t ht]))
        (abs_le_of (by positivity) (by linarith [ht2 t ht]))
  have hBb : |B| ≤ 3 ^ (d - k) := by
    apply abs_prod_le_pow
    intro t ht
    exact factor_bound hc1 hn hnx0 hnxn (abs_neg_le_of (by positivity) (by linarith [ht2 t ht]))
      (abs_neg_le_of (by positivity) (by linarith [ht2 t ht]))
  have hAb : |A'| ≤ 3 ^ k := by
    apply abs_prod_le_pow
    intro t ht
    exact factor_bound hc1 hn hx0 hxn (abs_le_of (by positivity) (by linarith [ht1 t ht]))
      (abs_le_of (by positivity) (by linarith [ht1 t ht]))
  have hsplit : (d : ℝ) = k + ((d - k : ℕ) : ℝ) := by push_cast [Nat.cast_sub hk]; ring
  have h3 : (3 : ℝ) ^ d = 3 ^ k * 3 ^ (d - k) := by rw [← pow_add]; congr 1; lia
  calc |A * B - A' * B'| = |(A - A') * B + A' * (B - B')| := by ring_nf
    _ ≤ |(A - A') * B| + |A' * (B - B')| := abs_add_le _ _
    _ = |A - A'| * |B| + |A'| * |B - B'| := by rw [abs_mul, abs_mul]
    _ ≤ (k * 3 ^ k * (20 * c / n)) * 3 ^ (d - k) +
          3 ^ k * (((d - k : ℕ) : ℝ) * 3 ^ (d - k) * (20 * c / n)) := by
        gcongr
    _ = d * 3 ^ d * (20 * c / n) := by rw [hsplit, h3]; ring

private theorem bvec_sub_gvec (d : ℕ) (u : ℕ → ℝ) {n j : ℕ} (hn : 2 * (2 * (d : ℝ) + 2) ≤ n)
    (hj : j ≤ n) :
    |bvec d u n j - gvec d u n j| ≤
      (∑ k ∈ range (d + 1), |u k| * (d.choose k : ℝ)) *
        (d * 3 ^ d * (20 * (2 * (d : ℝ) + 2) / n)) := by
  unfold bvec gvec
  rw [← sum_sub_distrib, sum_mul]
  refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum ?_)
  intro k hk
  rw [mem_range] at hk
  have hjr : (j : ℝ) ≤ n := by exact_mod_cast hj
  have := betaK_sub_gammaK (d := d) (n := n) (k := k) (by lia) hn (x := (j : ℝ))
    (by positivity) hjr
  rw [← mul_sub, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ d.choose k)]
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-! ### The moment vector at level `m` is a multiple of the kernel image -/

private theorem gvec_eq_kernel (d : ℕ) (u : ℕ → ℝ) {m i : ℕ} (hi : i ≤ m) :
    gvec d u m i = ((d.factorial : ℝ) / rise ((m : ℝ) + 2) d) *
      ∑ k ∈ range (d + 1),
        ((i + k).choose i * (m - i + (d - k)).choose (m - i) : ℝ) * u k := by
  unfold gvec
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  unfold gammaK
  rw [show (m : ℝ) - i + 1 = ((m - i : ℕ) : ℝ) + 1 by rw [Nat.cast_sub hi],
    rise_nat_add_one, rise_nat_add_one, Nat.add_comm i k, Nat.choose_symm_add,
    show m - i + (d - k) = (d - k) + (m - i) by lia, Nat.choose_symm_add]
  have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ d by lia)
  have h' : (d.choose k : ℝ) * (k.factorial : ℝ) * ((d - k).factorial : ℝ) = (d.factorial : ℝ) := by
    exact_mod_cast h
  rw [Nat.add_comm k i, Nat.choose_symm_add, Nat.add_comm (d - k) (m - i), Nat.choose_symm_add]
  rw [← h']
  ring

/-! ### The main result -/

/-- The lattice-path kernel maps `LCNIZ` sequences on `[0, d]` to `LCNIZ` sequences on
   `[0, m]` (Liu–Mao, Proposition 3.4 and Corollary 3.5). -/
theorem pathKernel_LCNIZ (m d : ℕ) {w : ℕ → ℝ} (hw : LCNIZ d w) :
    LCNIZ m (fun i => ∑ k ∈ range (d + 1),
      ((i + k).choose i * (m - i + (d - k)).choose (m - i) : ℝ) * w k) := by
  set u := trunc d w with hu
  have hglcn : GLCN d u :=
    ⟨hw.glc_trunc, fun k hk => by rw [hu]; unfold trunc; rw [ite_eq_right (by lia)]⟩
  set f : ℕ → ℝ := fun i => ∑ k ∈ range (d + 1),
      ((i + k).choose i * (m - i + (d - k)).choose (m - i) : ℝ) * w k with hf
  have hfu : ∀ i, f i = ∑ k ∈ range (d + 1),
      ((i + k).choose i * (m - i + (d - k)).choose (m - i) : ℝ) * u k := by
    intro i
    rw [hf]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [hu, trunc_eq_of_le w (by lia)]
  set C0 : ℝ := (d.factorial : ℝ) / rise ((m : ℝ) + 2) d with hC0
  have hC0pos : 0 < C0 :=
    div_pos (by exact_mod_cast Nat.factorial_pos d) (rise_pos (by positivity) d)
  have hg : ∀ i, i ≤ m → gvec d u m i = C0 * f i := by
    intro i hi; rw [hfu i]; exact gvec_eq_kernel d u hi
  obtain ⟨h0, -, hniz⟩ := hw
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    exact sum_nonneg (fun k hk => mul_nonneg (by positivity) (h0 k (by rw [mem_range] at hk; lia)))
  · intro i hi0 him
    -- the approximating LC-NIZ sequences
    set cseq : ℕ → ℕ → ℝ := fun r => descend m (d + r) (bseq d u (m + r)) with hcseq
    have hlc : ∀ r, cseq r (i - 1) * cseq r (i + 1) ≤ cseq r i ^ 2 := by
      intro r
      have hb := bseq_glcn hglcn (m + r)
      rw [show d + (m + r) = m + (d + r) by lia] at hb
      exact (descend_glcn m (d + r) _ hb).1.lc i hi0
    set S : ℝ := ∑ k ∈ range (d + 1), |u k| * (d.choose k : ℝ) with hS
    set K : ℝ := S * (d * 3 ^ d * (20 * (2 * (d : ℝ) + 2))) with hK
    have hconv : ∀ i', i' ≤ m → Tendsto (fun r => cseq r i') atTop (𝓝 (gvec d u m i')) := by
      intro i' hi'
      have hbound : ∀ r, 2 * (2 * (d : ℝ) + 2) ≤ ((r + (m + d) : ℕ) : ℝ) →
          |cseq r i' - gvec d u m i'| ≤ K / ((r + (m + d) : ℕ) : ℝ) := by
        intro r hr
        rw [hcseq]
        simp only
        rw [← descend_gvec d u m (d + r)]
        apply descend_contract m (d + r) _ _ _ _ i' hi'
        intro j hj
        rw [bseq_eq (m + r) j (by lia), show d + (m + r) = m + (d + r) by lia]
        have hn : 2 * (2 * (d : ℝ) + 2) ≤ ((m + (d + r) : ℕ) : ℝ) := by
          rw [show m + (d + r) = r + (m + d) by lia]; exact hr
        have := bvec_sub_gvec d u hn hj
        rw [show m + (d + r) = r + (m + d) by lia] at this ⊢
        rw [hK]
        calc _ ≤ _ := this
          _ = _ := by ring
      have hlim : Tendsto (fun r : ℕ => K / ((r + (m + d) : ℕ) : ℝ)) atTop (𝓝 0) :=
        (tendsto_const_div_atTop_nhds_zero_nat K).comp (tendsto_add_atTop_nat (m + d))
      rw [tendsto_iff_norm_sub_tendsto_zero]
      apply squeeze_zero' (Eventually.of_forall (fun r => norm_nonneg _)) _ hlim
      have hev : ∀ᶠ r : ℕ in atTop, (4 * d + 4 : ℕ) ≤ r := eventually_ge_atTop _
      filter_upwards [hev] with r hr
      rw [Real.norm_eq_abs]
      apply hbound
      have : ((4 * d + 4 : ℕ) : ℝ) ≤ ((r + (m + d) : ℕ) : ℝ) := by
        exact_mod_cast (show 4 * d + 4 ≤ r + (m + d) by lia)
      push_cast at this ⊢
      linarith
    have hlimit : gvec d u m (i - 1) * gvec d u m (i + 1) ≤ gvec d u m i ^ 2 :=
      le_of_tendsto_of_tendsto' (((hconv (i - 1) (by lia)).mul (hconv (i + 1) (by lia))))
        ((hconv i (by lia)).pow 2) hlc
    rw [hg (i - 1) (by lia), hg (i + 1) (by lia), hg i (by lia)] at hlimit
    have : C0 ^ 2 * (f (i - 1) * f (i + 1)) ≤ C0 ^ 2 * f i ^ 2 := by nlinarith [hlimit]
    exact le_of_mul_le_mul_left this (by positivity)
  · intro i j k _ _ _ hi _
    obtain ⟨l, hl, hne⟩ := exists_ne_zero_of_sum_ne_zero hi
    rw [mem_range] at hl
    have hwl : w l ≠ 0 := right_ne_zero_of_mul hne
    have hpos : 0 < w l := lt_of_le_of_ne (h0 l (by lia)) (Ne.symm hwl)
    apply ne_of_gt
    have hterm : 0 < ((j + l).choose j * (m - j + (d - l)).choose (m - j) : ℝ) * w l := by
      apply mul_pos _ hpos
      have h1 : 0 < (j + l).choose j := Nat.choose_pos (by lia)
      have h2 : 0 < (m - j + (d - l)).choose (m - j) := Nat.choose_pos (by lia)
      positivity
    calc (0 : ℝ) < ((j + l).choose j * (m - j + (d - l)).choose (m - j) : ℝ) * w l := hterm
      _ ≤ ∑ k ∈ range (d + 1),
          ((j + k).choose j * (m - j + (d - k)).choose (m - j) : ℝ) * w k := by
        apply single_le_sum
          (f := fun k => ((j + k).choose j * (m - j + (d - k)).choose (m - j) : ℝ) * w k)
          (fun k hk => mul_nonneg (by positivity) (h0 k (by rw [mem_range] at hk; lia)))
          (mem_range.mpr hl)

end RealRooted.LiuMao

/-!
## The Liu–Mao matrix `C = T_a H T_bᵀ`

For sequences `a`, `b` and degrees `d₁`, `d₂` we form the kernel
`H_{i,j} = C(d₁ + i - j, i) * C(d₂ + j - i, j)` (`0 ≤ i ≤ d₂`, `0 ≤ j ≤ d₁`) and the matrix
`C_{r,s} = ∑_{i,j} a_{r-i} H_{i,j} b_{s-j}`.  If `a` and `b` are LC-NIZ then `C` is nonnegative,
`RR₂`, has log-concave rows and columns, and its diagonal has no internal zeros.
-/

open Finset

namespace RealRooted.LiuMao

/-! ### Binomial coefficients are LC-NIZ -/

private theorem binom_glc (N : ℕ) : GLC (fun k => (N.choose k : ℝ)) := by
  refine ⟨fun k => Nat.cast_nonneg _, ?_, ?_⟩
  · intro k hk
    rcases le_or_gt N k with hNk | hNk
    · rw [Nat.choose_eq_zero_of_lt (show N < k + 1 by lia)]; simp
    have e1 := Nat.choose_succ_right_eq N k
    have e2 := Nat.choose_succ_right_eq N (k - 1)
    rw [show k - 1 + 1 = k by lia] at e2
    have e1' : (N.choose (k + 1) : ℝ) * (k + 1) = N.choose k * ((N : ℝ) - k) := by
      have := congr_arg (fun n : ℕ => (n : ℝ)) e1
      push_cast [Nat.cast_sub hNk.le] at this; linarith
    have e2' : (N.choose k : ℝ) * k = N.choose (k - 1) * ((N : ℝ) - k + 1) := by
      have := congr_arg (fun n : ℕ => (n : ℝ)) e2
      push_cast [Nat.cast_sub (show k - 1 ≤ N by lia), Nat.cast_sub (show 1 ≤ k by lia)]
        at this
      linarith
    have hNk' : (k : ℝ) < N := by exact_mod_cast hNk
    have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hpos : (0 : ℝ) < ((N : ℝ) - k + 1) * (k + 1) := by
      apply mul_pos <;> linarith
    have key : (N.choose (k - 1) : ℝ) * N.choose (k + 1) * (((N : ℝ) - k + 1) * (k + 1)) ≤
        (N.choose k : ℝ) ^ 2 * (((N : ℝ) - k + 1) * (k + 1)) := by
      calc (N.choose (k - 1) : ℝ) * N.choose (k + 1) * (((N : ℝ) - k + 1) * (k + 1))
          = (N.choose (k - 1) * ((N : ℝ) - k + 1)) * (N.choose (k + 1) * (k + 1)) := by ring
        _ = (N.choose k : ℝ) ^ 2 * (k * ((N : ℝ) - k)) := by rw [← e2', e1']; ring
        _ ≤ (N.choose k : ℝ) ^ 2 * (((N : ℝ) - k + 1) * (k + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); nlinarith
    exact le_of_mul_le_mul_right key hpos
  · intro i j k hij hjk _ hk
    have : k ≤ N := by
      by_contra h; exact hk (by rw [Nat.choose_eq_zero_of_lt (by lia)]; simp)
    exact_mod_cast (Nat.choose_pos (by lia)).ne'

/-! ### The kernel `H` -/

/-- The Liu–Mao kernel in matrix form, `H_{i,j} = C(d₁ + i - j, i) * C(d₂ + j - i, j)` on the
box `i ≤ d₂`, `j ≤ d₁`, and zero outside. -/
def Hk (d1 d2 i j : ℕ) : ℝ :=
  if i ≤ d2 ∧ j ≤ d1 then ((d1 + i - j).choose i * (d2 + j - i).choose j : ℝ) else 0

private theorem Hk_nonneg (d1 d2 i j : ℕ) : 0 ≤ Hk d1 d2 i j := by
  unfold Hk; split_ifs
  · positivity
  · exact le_refl 0

private theorem Hk_pos {d1 d2 i j : ℕ} (hi : i ≤ d2) (hj : j ≤ d1) : 0 < Hk d1 d2 i j := by
  unfold Hk; rw [ite_eq_left ⟨hi, hj⟩]
  have h1 := Nat.choose_pos (show i ≤ d1 + i - j by lia)
  have h2 := Nat.choose_pos (show j ≤ d2 + j - i by lia)
  positivity

private theorem Hk_symm (d1 d2 i j : ℕ) : Hk d2 d1 j i = Hk d1 d2 i j := by
  unfold Hk
  by_cases h : i ≤ d2 ∧ j ≤ d1
  · rw [ite_eq_left ⟨h.2, h.1⟩, ite_eq_left h]; ring
  · rw [ite_eq_right (fun h' => h ⟨h'.2, h'.1⟩), ite_eq_right h]

private theorem Hk_mul_eq {d1 d2 i j : ℕ} (hi : i ≤ d2) (hj : j ≤ d1) :
    Hk d1 d2 i j * ((d1 + d2).choose (d1 + i - j) : ℝ) *
        ((i.factorial * (d1 - j).factorial * j.factorial * (d2 - i).factorial : ℕ) : ℝ) =
      ((d1 + d2).factorial : ℝ) := by
  unfold Hk; rw [ite_eq_left ⟨hi, hj⟩]
  have h1 := Nat.choose_mul_factorial_mul_factorial (n := d1 + i - j) (k := i) (by lia)
  rw [show d1 + i - j - i = d1 - j by lia] at h1
  have h2 := Nat.choose_mul_factorial_mul_factorial (n := d2 + j - i) (k := j) (by lia)
  rw [show d2 + j - i - j = d2 - i by lia] at h2
  have h3 := Nat.choose_mul_factorial_mul_factorial (n := d1 + d2) (k := d1 + i - j) (by lia)
  rw [show d1 + d2 - (d1 + i - j) = d2 + j - i by lia] at h3
  have key : (d1 + i - j).choose i * (d2 + j - i).choose j * (d1 + d2).choose (d1 + i - j) *
      (i.factorial * (d1 - j).factorial * j.factorial * (d2 - i).factorial) =
      (d1 + d2).factorial := by
    rw [← h3, ← h1, ← h2]; ring
  exact_mod_cast key

/-- The kernel is reverse regular of order two. -/
private theorem Hk_rr2 (d1 d2 : ℕ) {i₁ i₂ j₁ j₂ : ℕ} (hi : i₁ < i₂) (hj : j₁ < j₂) :
    Hk d1 d2 i₁ j₁ * Hk d1 d2 i₂ j₂ ≤ Hk d1 d2 i₁ j₂ * Hk d1 d2 i₂ j₁ := by
  have hnn := mul_nonneg (Hk_nonneg d1 d2 i₁ j₂) (Hk_nonneg d1 d2 i₂ j₁)
  by_cases hb : i₂ ≤ d2 ∧ j₂ ≤ d1
  swap
  · have : Hk d1 d2 i₂ j₂ = 0 := by unfold Hk; rw [ite_eq_right hb]
    rw [this, mul_zero]; exact hnn
  obtain ⟨hi2, hj2⟩ := hb
  set N := d1 + d2
  set F : ℕ → ℕ → ℝ := fun i j => ((N.choose (d1 + i - j) : ℕ) : ℝ)
  set D : ℕ → ℕ → ℝ := fun i j =>
    ((i.factorial * (d1 - j).factorial * j.factorial * (d2 - i).factorial : ℕ) : ℝ)
  have e11 := Hk_mul_eq (d1 := d1) (d2 := d2) (i := i₁) (j := j₁) (by lia) (by lia)
  have e22 := Hk_mul_eq (d1 := d1) (d2 := d2) (i := i₂) (j := j₂) (by lia) (by lia)
  have e12 := Hk_mul_eq (d1 := d1) (d2 := d2) (i := i₁) (j := j₂) (by lia) (by lia)
  have e21 := Hk_mul_eq (d1 := d1) (d2 := d2) (i := i₂) (j := j₁) (by lia) (by lia)
  have hD : D i₁ j₁ * D i₂ j₂ = D i₁ j₂ * D i₂ j₁ := by simp only [D]; push_cast; ring
  have hF : F i₁ j₂ * F i₂ j₁ ≤ F i₁ j₁ * F i₂ j₂ := by
    simp only [F]
    exact (binom_glc N).inner_outer (by lia) (by lia) (by lia)
  have hFpos : 0 < F i₁ j₁ * F i₂ j₂ := by
    simp only [F]
    have := Nat.choose_pos (show d1 + i₁ - j₁ ≤ N by lia)
    have := Nat.choose_pos (show d1 + i₂ - j₂ ≤ N by lia)
    positivity
  have hDpos : 0 < D i₁ j₁ * D i₂ j₂ := by simp only [D]; positivity
  have hDnn : 0 ≤ D i₁ j₂ * D i₂ j₁ := by simp only [D]; positivity
  have key : Hk d1 d2 i₁ j₁ * Hk d1 d2 i₂ j₂ * (F i₁ j₁ * F i₂ j₂ * (D i₁ j₁ * D i₂ j₂)) ≤
      Hk d1 d2 i₁ j₂ * Hk d1 d2 i₂ j₁ * (F i₁ j₁ * F i₂ j₂ * (D i₁ j₁ * D i₂ j₂)) := by
    calc Hk d1 d2 i₁ j₁ * Hk d1 d2 i₂ j₂ * (F i₁ j₁ * F i₂ j₂ * (D i₁ j₁ * D i₂ j₂))
        = (Hk d1 d2 i₁ j₁ * F i₁ j₁ * D i₁ j₁) * (Hk d1 d2 i₂ j₂ * F i₂ j₂ * D i₂ j₂) := by ring
      _ = (Hk d1 d2 i₁ j₂ * F i₁ j₂ * D i₁ j₂) * (Hk d1 d2 i₂ j₁ * F i₂ j₁ * D i₂ j₁) := by
        simp only [F, D]; rw [e11, e22, e12, e21]
      _ = Hk d1 d2 i₁ j₂ * Hk d1 d2 i₂ j₁ * (F i₁ j₂ * F i₂ j₁) * (D i₁ j₂ * D i₂ j₁) := by ring
      _ ≤ Hk d1 d2 i₁ j₂ * Hk d1 d2 i₂ j₁ * (F i₁ j₁ * F i₂ j₂) * (D i₁ j₂ * D i₂ j₁) := by
        apply mul_le_mul_of_nonneg_right _ hDnn
        exact mul_le_mul_of_nonneg_left hF hnn
      _ = Hk d1 d2 i₁ j₂ * Hk d1 d2 i₂ j₁ * (F i₁ j₁ * F i₂ j₂ * (D i₁ j₁ * D i₂ j₂)) := by
        rw [hD]; ring
  exact le_of_mul_le_mul_right key (mul_pos hFpos hDpos)

/-! ### The matrix `C` -/

/-- `C_{r,s} = ∑_{i ≤ d₂} ∑_{j ≤ d₁} a_{r-i} H_{i,j} b_{s-j}`. -/
def Cmat (a b : ℕ → ℝ) (d1 d2 r s : ℕ) : ℝ :=
  ∑ i ∈ range (d2 + 1), ∑ j ∈ range (d1 + 1), toep a r i * Hk d1 d2 i j * toep b s j

private theorem Cmat_swap (a b : ℕ → ℝ) (d1 d2 r s : ℕ) :
    Cmat a b d1 d2 r s = Cmat b a d2 d1 s r := by
  unfold Cmat
  rw [sum_comm]
  apply sum_congr rfl; intro j _; apply sum_congr rfl; intro i _
  rw [Hk_symm]; ring

variable {a b : ℕ → ℝ}

/-- The matrix `C` is nonnegative. -/
theorem Cmat_nonneg (ha : GLC a) (hb : GLC b) (d1 d2 r s : ℕ) : 0 ≤ Cmat a b d1 d2 r s :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg (ha.toep_nonneg _ _) (Hk_nonneg _ _ _ _)) (hb.toep_nonneg _ _)

private theorem Cmat_eq_sum_M (a b : ℕ → ℝ) (d1 d2 r s : ℕ) :
    Cmat a b d1 d2 r s = ∑ j ∈ range (d1 + 1),
      toep b s j * ∑ i ∈ range (d2 + 1), toep a r i * Hk d1 d2 i j := by
  unfold Cmat
  rw [sum_comm]
  apply sum_congr rfl; intro j _
  rw [mul_sum]; apply sum_congr rfl; intro i _; ring

/-- The matrix `C` is reverse regular of order two. -/
theorem Cmat_rr2 (ha : GLC a) (hb : GLC b) (d1 d2 : ℕ) {r₁ r₂ s₁ s₂ : ℕ}
    (hr : r₁ < r₂) (hs : s₁ < s₂) :
    Cmat a b d1 d2 r₁ s₁ * Cmat a b d1 d2 r₂ s₂ ≤ Cmat a b d1 d2 r₁ s₂ * Cmat a b d1 d2 r₂ s₁ := by
  set M : ℕ → ℕ → ℝ := fun r j => ∑ i ∈ range (d2 + 1), toep a r i * Hk d1 d2 i j with hM
  have hMrr : ∀ j j', j < j' → M r₁ j * M r₂ j' ≤ M r₁ j' * M r₂ j := by
    intro j j' hjj
    exact cauchyBinet_rr2 (range (d2 + 1)) (toep a r₁) (toep a r₂)
      (fun i => Hk d1 d2 i j) (fun i => Hk d1 d2 i j')
      (fun i _ i' _ hii => ha.toep_tp2 hr hii)
      (fun i _ i' _ hii => by have := Hk_rr2 d1 d2 hii hjj; linarith)
  have key := cauchyBinet_rr2 (range (d1 + 1)) (toep b s₁) (toep b s₂)
    (M r₁) (M r₂) (fun j _ j' _ hjj => hb.toep_tp2 hs hjj) (fun j _ j' _ hjj => hMrr j j' hjj)
  simp only [Cmat_eq_sum_M]
  linarith

/-- Column `s` of `C` is a convolution of `a` with an LC-NIZ sequence. -/
theorem Cmat_col_glc (ha : GLC a) (hb : GLC b) (d1 d2 s : ℕ) :
    GLC (fun r => Cmat a b d1 d2 r s) := by
  set g : ℕ → ℝ := fun i => ∑ j ∈ range (d1 + 1), Hk d1 d2 i j * toep b s j with hg
  have hw : LCNIZ d1 (fun k => toep b s (d1 - k)) := ((hb.window s).lcniz d1).rev
  have hpk := pathKernel_LCNIZ d2 d1 hw
  have hgl : LCNIZ d2 g := by
    apply hpk.congr
    intro i hi
    simp only [hg]
    rw [← sum_range_reflect]
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    rw [show d1 + 1 - 1 - j = d1 - j by lia, show d1 - (d1 - j) = j by lia]
    unfold Hk
    rw [ite_eq_left ⟨hi, by lia⟩, show i + (d1 - j) = d1 + i - j by lia,
      show d2 - i + j = d2 + j - i by lia]
    rw [show d2 + j - i = (d2 - i) + j by lia, Nat.choose_symm_add]
  have hconv := hgl.glc_trunc.conv ha
  have heq : (fun r => Cmat a b d1 d2 r s) = Hoggar.conv (trunc d2 g) a := by
    funext r
    rw [conv_eq_sum_toep_of_support a (trunc d2 g) d2 r
      (fun i hi => by unfold trunc; rw [ite_eq_right (by lia)])]
    unfold Cmat
    apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    rw [trunc_eq_of_le _ (by lia), hg, mul_sum]
    apply sum_congr rfl; intro j _; ring
  rw [heq]; exact hconv

/-- Row `r` of `C` is `GLC`. -/
theorem Cmat_row_glc (ha : GLC a) (hb : GLC b) (d1 d2 r : ℕ) :
    GLC (fun s => Cmat a b d1 d2 r s) := by
  have := Cmat_col_glc hb ha d2 d1 r
  simp only [← Cmat_swap] at this
  exact this

private theorem Cmat_diag_witness (d1 d2 k : ℕ) (h : Cmat a b d1 d2 k k ≠ 0) :
    ∃ i j, i ≤ d2 ∧ j ≤ d1 ∧ i ≤ k ∧ j ≤ k ∧ a (k - i) ≠ 0 ∧ b (k - j) ≠ 0 := by
  unfold Cmat at h
  obtain ⟨i, hi, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨j, hj, hne'⟩ := exists_ne_zero_of_sum_ne_zero hne
  rw [mem_range] at hi hj
  have h1 := left_ne_zero_of_mul (left_ne_zero_of_mul hne')
  have h2 := right_ne_zero_of_mul hne'
  have hik : i ≤ k := by
    by_contra hik
    exact h1 (by rw [toep, ite_eq_right hik])
  have hjk : j ≤ k := by
    by_contra hjk
    exact h2 (by rw [toep, ite_eq_right hjk])
  rw [toep, ite_eq_left hik] at h1
  rw [toep, ite_eq_left hjk] at h2
  exact ⟨i, j, by lia, by lia, hik, hjk, h1, h2⟩

private theorem Cmat_diag_ne_zero (ha : GLC a) (hb : GLC b) {d1 d2 k i j : ℕ} (hi : i ≤ d2)
    (hj : j ≤ d1) (hik : i ≤ k) (hjk : j ≤ k) (hai : a (k - i) ≠ 0) (hbj : b (k - j) ≠ 0) :
    Cmat a b d1 d2 k k ≠ 0 := by
  unfold Cmat
  intro h0
  have h1 := (sum_eq_zero_iff_of_nonneg (fun x _ => sum_nonneg fun y _ =>
    mul_nonneg (mul_nonneg (ha.toep_nonneg _ _) (Hk_nonneg _ _ _ _)) (hb.toep_nonneg _ _))).mp
    h0 i (by rw [mem_range]; lia)
  have h2 := (sum_eq_zero_iff_of_nonneg (fun y _ =>
    mul_nonneg (mul_nonneg (ha.toep_nonneg _ _) (Hk_nonneg _ _ _ _)) (hb.toep_nonneg _ _))).mp
    h1 j (by rw [mem_range]; lia)
  unfold toep at h2
  rw [ite_eq_left hik, ite_eq_left hjk] at h2
  exact mul_ne_zero (mul_ne_zero hai (Hk_pos hi hj).ne') hbj h2

/-- The diagonal of `C` has no internal zeros. -/
theorem Cmat_diag_niz (ha : GLC a) (hb : GLC b) (d1 d2 : ℕ) {α β γ : ℕ} (hαβ : α < β)
    (hβγ : β < γ) (hα : Cmat a b d1 d2 α α ≠ 0) (hγ : Cmat a b d1 d2 γ γ ≠ 0) :
    Cmat a b d1 d2 β β ≠ 0 := by
  obtain ⟨i₁, j₁, hi₁, hj₁, hi₁k, hj₁k, ha₁, hb₁⟩ := Cmat_diag_witness d1 d2 α hα
  obtain ⟨i₂, j₂, hi₂, hj₂, hi₂k, hj₂k, ha₂, hb₂⟩ := Cmat_diag_witness d1 d2 γ hγ
  set x := max (min (α - i₁) (γ - i₂)) (β - d2) with hx
  set y := max (min (α - j₁) (γ - j₂)) (β - d1) with hy
  have hax : a x ≠ 0 := ha.ne_zero_between ha₁ ha₂ (by lia) (by lia)
  have hby : b y ≠ 0 := hb.ne_zero_between hb₁ hb₂ (by lia) (by lia)
  exact Cmat_diag_ne_zero ha hb (i := β - x) (j := β - y) (by lia) (by lia) (by lia)
    (by lia) (by rw [show β - (β - x) = x by lia]; exact hax)
    (by rw [show β - (β - y) = y by lia]; exact hby)

end RealRooted.LiuMao
