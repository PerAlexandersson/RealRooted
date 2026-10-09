import RealRooted.EulerBidiagonal.GeneralRows

/-!
# Rows with an index-dependent multiplier

`generalRowsDep κ a b u v n` is `P n` for `P 0 = 1`, `P (n + 1) = generalStep κ a b (u n) v (P n)`.
If `u (n + 1) = u n + s` and `u n + v k > 0` for `k ≤ n`, then consecutive rows strictly
interlace.  The proof applies the shifted-cone form of Theorem C′ to
`P (n + 2) = T (P (n + 1)) + s X P (n + 1)` with `T = generalStep κ a b (u n) v`, which also
covers the regimes `u n + v (n + 1) ≤ 0` (A166960, A166961, A166962, A166972).
-/

open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

/-- The rows `P 0 = 1`, `P (n + 1) = generalStep κ a b (u n) v (P n)`. -/
def generalRowsDep (κ a b : ℝ) (u : ℕ → ℝ) (v : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => generalStep κ a b (u n) v (generalRowsDep κ a b u v n)

/-- Shifting the multiplier `u` by `s` adds `s X p`. -/
theorem generalStep_add_left (κ a b u v s : ℝ) (p : ℝ[X]) :
    generalStep κ a b (u + s) v p = generalStep κ a b u v p + C s * (X * p) := by
  simp only [generalStep, C_add]
  ring

/-- The leading coefficient of `T p` is `(u + v m)` times that of `p`. -/
theorem leadingCoeff_generalStep_of_natDegree (κ a b u v : ℝ) (p : ℝ[X]) (m : ℕ)
    (hpd : p.natDegree = m) (hT : (generalStep κ a b u v p).natDegree = m + 1) :
    (generalStep κ a b u v p).leadingCoeff = (u + v * m) * p.leadingCoeff := by
  rw [leadingCoeff, hT, coeff_generalStep]
  have h : p.coeff (m + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
  rw [h]
  simp [leadingCoeff, hpd]

/-- Rows with a shifting multiplier: negative-simple of degree `n`, with consecutive rows
strictly interlacing and without common roots. -/
theorem generalRowsDep_spec (κ a b : ℝ) (u : ℕ → ℝ) (v s : ℝ) (hκ : 0 < κ) (ha : 0 < a)
    (hb : 0 < b) (hshift : ∀ n, u (n + 1) = u n + s)
    (hell : ∀ n k : ℕ, k ≤ n → 0 < u n + v * k)
    (hQ : ∀ n : ℕ, ∀ t ≤ 0, comparisonDefect κ a b (u n) v t < 0) :
    ∀ n : ℕ, IsNegativeSimple (generalRowsDep κ a b u v n) ∧
      (generalRowsDep κ a b u v n).natDegree = n ∧
      StrictInterl (generalRowsDep κ a b u v n) (generalRowsDep κ a b u v (n + 1)) ∧
      ∀ r, ¬ ((generalRowsDep κ a b u v n).IsRoot r ∧
        (generalRowsDep κ a b u v (n + 1)).IsRoot r) := by
  have hone : IsNegativeSimple (1 : ℝ[X]) := by
    refine ⟨by norm_num, Splits.one, ?_, hasPosLeadingCoeff_one, ?_⟩
    · exact fun r hr => absurd hr (by simp)
    · intro r hr
      exact absurd hr (by simp)
  have hnext : ∀ n : ℕ, IsNegativeSimple (generalRowsDep κ a b u v n) →
      (generalRowsDep κ a b u v n).natDegree = n →
      IsNegativeSimple (generalRowsDep κ a b u v (n + 1)) ∧
        (generalRowsDep κ a b u v (n + 1)).natDegree = n + 1 := by
    intro n h1 h2
    exact isNegativeSimple_generalStep_of_natDegree κ a b (u n) v _ n h1 h2 hκ ha hb
      (fun k hk => hell n k hk) (hQ n)
  intro n
  induction n with
  | zero =>
      have h1 := hnext 0 hone (by simp [generalRowsDep])
      refine ⟨by simpa [generalRowsDep] using hone, by simp [generalRowsDep], ?_, ?_⟩
      · exact strictInterl_one_of_natDegree_eq_one h1.1.1 h1.1.2.1 h1.2
      · intro r hr
        have hzero : (1 : ℝ[X]).eval r = 0 := by
          simpa [generalRowsDep, Polynomial.IsRoot.def] using hr.1
        norm_num at hzero
  | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      obtain ⟨h5, h6⟩ := hnext n h1 h2
      have hlc : (generalRowsDep κ a b u v (n + 1)).leadingCoeff =
          (u n + v * n) * (generalRowsDep κ a b u v n).leadingCoeff :=
        leadingCoeff_generalStep_of_natDegree κ a b (u n) v _ n h2 h6
      have hlead : 0 < (u n + v * ((n : ℝ) + 1)) *
            (generalRowsDep κ a b u v (n + 1)).leadingCoeff +
          s * (u n + v * (n : ℝ)) * (generalRowsDep κ a b u v n).leadingCoeff := by
        have hpos : 0 < u (n + 1) + v * ((n + 1 : ℕ) : ℝ) := hell (n + 1) (n + 1) le_rfl
        have hshift' := hshift n
        push_cast at hpos
        have hn : 0 < u n + v * (n : ℝ) := hell n n le_rfl
        have hlc0 : 0 < (generalRowsDep κ a b u v n).leadingCoeff := h1.2.2.2.1
        rw [hlc]
        have : (u n + v * ((n : ℝ) + 1)) * ((u n + v * n) *
            (generalRowsDep κ a b u v n).leadingCoeff) +
            s * (u n + v * (n : ℝ)) * (generalRowsDep κ a b u v n).leadingCoeff =
            (u (n + 1) + v * ((n : ℝ) + 1)) * ((u n + v * n) *
              (generalRowsDep κ a b u v n).leadingCoeff) := by
          rw [hshift']
          ring
        rw [this]
        exact mul_pos hpos (mul_pos hn hlc0)
      have hcone := strictInterl_generalStep_add_C_mul_X_mul_of_strictInterl κ a b (u n) v s
        (generalRowsDep κ a b u v n) (generalRowsDep κ a b u v (n + 1)) n h1 h5 h2 h6 h3
        (fun r hr hr' => h4 r ⟨hr, hr'⟩) hκ ha hb (fun k hk => hell n k hk) hlead (hQ n)
      have hrow : generalRowsDep κ a b u v (n + 2) =
          generalStep κ a b (u n) v (generalRowsDep κ a b u v (n + 1)) +
            C s * (X * generalStep κ a b (u n) v (generalRowsDep κ a b u v n)) := by
        rw [generalRowsDep, hshift n, generalStep_add_left]
        rfl
      refine ⟨h5, h6, ?_, ?_⟩
      · rw [hrow]
        exact hcone.1
      · intro r hr
        rw [hrow] at hr
        exact hcone.2 r hr.1 hr.2

end RealRooted.EulerBidiagonal
