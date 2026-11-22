module

public import RealRooted.ExponentialRows.ProductInsertion
import RealRooted.Mathlib.Algebra.Polynomial.Splits.FinRoots
import RealRooted.PFPolynomial
import RealRooted.PosCombo
import RealRooted.Linear
import Mathlib.Tactic

/-!
# Exponential rows with a factored derivative

We use the auxiliary products `z ∏ (z + rᵢ)` of the derivative of the marked
block polynomial. Unlike the Newton expansion of the block polynomial, this
construction needs no ordering of the nonnegative root parameters.

The scalar update is `Fₙ₊₁ = s Fₙ + c X W₀ / (n + 1)`, where `W` is the
new auxiliary vector. This is the coefficient recurrence of `exp(s z + t B)`
when `B' = c ∏ (z + rᵢ)`. Zero singleton weight and zero auxiliary rows are
included.

Source: unpublished manuscript `exp-families-REPORT.md`, Theorem 1, supplied
with RealRooted issues #2415 and #2590.
-/

@[expose] public section

open Finset Polynomial

namespace RealRooted.ExponentialRows

/-- The derivative-product auxiliary transition at row `n + 1`. Parameters
`r 1, …, r m` are the factors in reverse order; `r 0` is unused. -/
noncomputable def derivativeProductAux (r : ℕ → ℝ) (m n : ℕ)
    (v : Fin (m + 2) → ℝ[X]) (i : Fin (m + 1)) : ℝ[X] :=
  ∑ j, C (partialProductMatrix r (m + 1) (n + 1) i j) * v j

/-- Simultaneous coefficient recurrence for a factored marked derivative and
unmarked singleton weight `s`. The last coordinate is the scalar row. -/
noncomputable def derivativeProductVector (s c : ℝ) (r : ℕ → ℝ) (m : ℕ) :
    ℕ → Fin (m + 2) → ℝ[X]
  | 0 => Fin.lastCases 1 (fun _ => 0)
  | n + 1 => Fin.lastCases
      (C s * derivativeProductVector s c r m n (Fin.last (m + 1)) +
        C (c / (n + 1)) * (X *
          derivativeProductAux r m n (derivativeProductVector s c r m n) 0))
      (derivativeProductAux r m n (derivativeProductVector s c r m n))

/-- The scalar row of the derivative-product recurrence. -/
noncomputable def derivativeProductRow (s c : ℝ) (r : ℕ → ℝ) (m n : ℕ) : ℝ[X] :=
  derivativeProductVector s c r m n (Fin.last (m + 1))

private lemma derivativeProduct_seed (s c : ℝ) (r : ℕ → ℝ) (m : ℕ) :
    IsInterlacingSeq0NonnegRealRooted
      (List.ofFn (derivativeProductVector s c r m 0)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise, List.pairwise_ofFn]
    intro i j hij
    induction i using Fin.lastCases with
    | last => exact (not_lt_of_ge (Fin.le_last j) hij).elim
    | cast i => simpa [derivativeProductVector] using
        interl_zero_left (derivativeProductVector s c r m 0 j)
  · simp only [List.forall_mem_ofFn_iff]
    intro i
    induction i using Fin.lastCases with
    | last => simpa [derivativeProductVector] using hasNonnegCoeffs_one
    | cast i => simpa [derivativeProductVector] using hasNonnegCoeffs_zero
  · simp only [List.forall_mem_ofFn_iff]
    intro i hi
    induction i using Fin.lastCases with
    | last => simp [derivativeProductVector]
    | cast i => simp [derivativeProductVector] at hi

/-- The old scalar row appended to the new auxiliaries remains interlacing.
This is the existing partial-product matrix with zero variable-row weights. -/
private lemma derivativeProductAux_interlacing {r : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) {m n : ℕ} {v : Fin (m + 2) → ℝ[X]}
    (hv : IsInterlacingSeq0NonnegRealRooted (List.ofFn v)) :
    IsInterlacingSeq0NonnegRealRooted
      (List.ofFn (Fin.lastCases (v (Fin.last (m + 1)))
        (derivativeProductAux r m n v))) := by
  have h := partialProductMatrix_variableLastRow_preserves (q := fun _ => 0)
    hr (m := m + 1) (fun _ _ => le_rfl) (by simp) (N := n + 1) (by positivity)
    (List.ofFn v) (by simp) hv
  rw [variableLastRowMatrix_action] at h
  change IsInterlacingSeq0NonnegRealRooted (List.ofFn (Fin.lastCases
    (v (Fin.last (m + 1))) (fun i =>
      ∑ j, C (partialProductMatrix r (m + 1) (n + 1) i j) * v j)))
  simpa using h

/-- A nonnegative combination of a zero-aware interlacing pair splits,
including zero endpoints. -/
private lemma splits_combo {f g : ℝ[X]} (hfg : Interl f g)
    (hf : f.Splits) (hg : g.Splits) (hnf : HasNonnegCoeffs f)
    (hng : HasNonnegCoeffs g) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (C a * f + C b * g).Splits := by
  by_cases hf0 : f = 0
  · simp [hf0, hg]
  by_cases hg0 : g = 0
  · simp [hg0, hf]
  by_cases ha0 : a = 0
  · simp [ha0, hg]
  by_cases hb0 : b = 0
  · simp [hb0, hf]
  exact (hfg.toStrictInterl_of_ne hf0 hg0).isRealRooted_nonneg_combo
    (hnf.pos_leadingCoeff hf0) (hng.pos_leadingCoeff hg0)
    ha hb (Or.inl (lt_of_le_of_ne ha (Ne.symm ha0))) |>.2

/-- Appending the new scalar row closes the derivative-product induction. -/
private lemma derivativeProduct_step {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) {m n : ℕ}
    (hv : IsInterlacingSeq0NonnegRealRooted
      (List.ofFn (derivativeProductVector s c r m n))) :
    IsInterlacingSeq0NonnegRealRooted
      (List.ofFn (derivativeProductVector s c r m (n + 1))) := by
  let v := derivativeProductVector s c r m n
  let w := derivativeProductAux r m n v
  let u : Fin (m + 2) → ℝ[X] := Fin.lastCases (v (Fin.last (m + 1))) w
  have hu := derivativeProductAux_interlacing hr (n := n) hv
  change IsInterlacingSeq0NonnegRealRooted (List.ofFn u) at hu
  have hnn (i : Fin (m + 2)) := hu.nonnegCoeffs _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hsp (i : Fin (m + 2)) := hu.splits_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hint (i j : Fin (m + 2)) (hij : i ≤ j) : Interl (u i) (u j) := by
    rcases lt_or_eq_of_le hij with hij | rfl
    · have h := hu.interlacingSeq0
      rw [isInterlacingSeq0_iff_pairwise, List.pairwise_ofFn] at h
      exact h hij
    · exact Interl.refl (fun _ => hsp i)
  have hdiv : 0 ≤ c / (n + 1 : ℝ) := div_nonneg hc (by positivity)
  have hu0 : u 0 = w 0 := by
    change Fin.lastCases (v (Fin.last (m + 1))) w (0 : Fin (m + 1)).castSucc = w 0
    exact Fin.lastCases_castSucc _
  have hulast : u (Fin.last (m + 1)) = v (Fin.last (m + 1)) := by simp [u]
  have h0i (i : Fin (m + 2)) : Interl (u i) (X * w 0) := by
    simpa only [hu0] using
      interl_mul_X_of_interl (hint 0 i (Fin.zero_le i)) (hnn 0) (hnn i)
  have hnewnn : HasNonnegCoeffs
      (C s * v (Fin.last (m + 1)) + C (c / (n + 1)) * (X * w 0)) :=
    ((hasNonnegCoeffs_C hs).mul (hulast ▸ hnn (Fin.last (m + 1)))).add
      ((hasNonnegCoeffs_C hdiv).mul (hasNonnegCoeffs_X.mul (hu0 ▸ hnn 0)))
  have hnewsp := splits_combo (h0i (Fin.last (m + 1)))
    (hsp (Fin.last (m + 1))) ((by simp : (X : ℝ[X]).Splits).mul (hu0 ▸ hsp 0))
    (hnn (Fin.last (m + 1))) (hasNonnegCoeffs_X.mul (hu0 ▸ hnn 0)) hs hdiv
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise, List.pairwise_ofFn]
    intro i j hij
    induction j using Fin.lastCases with
    | cast j =>
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr
        (Fin.ne_last_of_lt (lt_trans hij (Fin.castSucc_lt_last j)))
      simpa only [derivativeProductVector, Fin.lastCases_castSucc, u, w, v] using
        hint i.castSucc j.castSucc hij.le
    | last =>
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt hij)
      have h := interl_add_right_of_common_left_of_nonneg
        ((hint i.castSucc (Fin.last (m + 1)) (Fin.le_last _)).C_mul_right_of_nonneg hs)
        ((h0i i.castSucc).C_mul_right_of_nonneg hdiv)
        ((hasNonnegCoeffs_C hs).mul (hnn (Fin.last (m + 1))))
        ((hasNonnegCoeffs_C hdiv).mul (hasNonnegCoeffs_X.mul (hu0 ▸ hnn 0)))
      simpa only [derivativeProductVector, Fin.lastCases_castSucc, Fin.lastCases_last,
        u, w, v] using h
  · simp only [List.forall_mem_ofFn_iff]
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [derivativeProductVector, Fin.lastCases_last, v, w] using hnewnn
    | cast i =>
      simpa only [derivativeProductVector, Fin.lastCases_castSucc, u, w, v] using hnn i.castSucc
  · simp only [List.forall_mem_ofFn_iff]
    intro i hi
    refine ⟨hi, ?_⟩
    induction i using Fin.lastCases with
    | last =>
      simpa only [derivativeProductVector, Fin.lastCases_last, hulast, v, w] using hnewsp
    | cast i =>
      simpa only [derivativeProductVector, Fin.lastCases_castSucc, u, w, v] using hsp i.castSucc

/-- All partial-product coordinates and the scalar row form an interlacing
sequence, with nonnegative coefficients and split nonzero entries. -/
theorem derivativeProductVector_interlacing {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (m n : ℕ) :
    IsInterlacingSeq0NonnegRealRooted
      (List.ofFn (derivativeProductVector s c r m n)) := by
  induction n with
  | zero => exact derivativeProduct_seed s c r m
  | succ n ih => exact derivativeProduct_step hs hc hr ih

/-- Every derivative-product row splits over the reals, including zero rows. -/
theorem derivativeProductRow_splits {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (m n : ℕ) :
    (derivativeProductRow s c r m n).Splits :=
  (derivativeProductVector_interlacing hs hc hr m n).splits_of_mem
    (List.mem_ofFn.mpr ⟨Fin.last (m + 1), rfl⟩)

/-- The constant coefficient is `s^n`, so positive singleton weight excludes
zero rows without any restriction on the derivative factors. -/
@[simp] theorem derivativeProductRow_coeff_zero (s c : ℝ) (r : ℕ → ℝ) (m n : ℕ) :
    (derivativeProductRow s c r m n).coeff 0 = s ^ n := by
  induction n with
  | zero => simp [derivativeProductRow, derivativeProductVector]
  | succ n ih =>
    simp only [derivativeProductRow, derivativeProductVector, Fin.lastCases_last]
    change (C s * derivativeProductRow s c r m n +
      C (c / (n + 1)) * (X * derivativeProductAux r m n
        (derivativeProductVector s c r m n) 0)).coeff 0 = _
    simp [ih, pow_succ, mul_comm]

/-- Positive singleton weight makes every recurrence row nonzero. -/
theorem derivativeProductRow_ne_zero {s : ℝ} (hs : 0 < s) (c : ℝ) (r : ℕ → ℝ)
    (m n : ℕ) : derivativeProductRow s c r m n ≠ 0 := by
  intro hz
  have h := derivativeProductRow_coeff_zero s c r m n
  rw [hz, coeff_zero] at h
  exact (pow_pos hs n).ne' h.symm

private lemma derivativeProductAux_of_zero (r : ℕ → ℝ) (m n : ℕ)
    (v : Fin (m + 2) → ℝ[X]) (i : Fin (m + 1))
    (hz : (i : ℕ) + 1 < m + 1 → r ((i : ℕ) + 1) = 0) :
    derivativeProductAux r m n v i =
      C (n + 1 : ℝ) * v ⟨(i : ℕ) + 1, by lia⟩ := by
  unfold derivativeProductAux
  rw [sum_eq_single (⟨(i : ℕ) + 1, by lia⟩ : Fin (m + 2))]
  · simp [partialProductMatrix]
  · intro j _ hj
    by_cases hij : (i : ℕ) < j
    · have hneq : (j : ℕ) ≠ (i : ℕ) + 1 := fun h => hj (Fin.ext h)
      have hlt : (i : ℕ) + 1 < j := by lia
      have hprod : (∏ k ∈ Ico ((i : ℕ) + 1) (j : ℕ), r k) = 0 := by
        apply prod_eq_zero (i := (i : ℕ) + 1)
        · exact mem_Ico.mpr ⟨le_rfl, hlt⟩
        · exact hz (by have := j.isLt; lia)
      simp [partialProductMatrix, hij, hprod]
    · simp [partialProductMatrix, hij]
  · simp

/-- A terminal string of zero derivative factors makes an auxiliary coordinate
a positive factorial multiple of an earlier scalar row. -/
theorem derivativeProductVector_eq_earlier_row (s c : ℝ) (r : ℕ → ℝ) (m n j : ℕ)
    (hj : j ≤ m + 1)
    (hz : ∀ l, m + 2 - j ≤ l → l ≤ m → r l = 0) :
    derivativeProductVector s c r m (n + j) ⟨m + 1 - j, by lia⟩ =
      C ((n + 1).ascFactorial j : ℝ) * derivativeProductRow s c r m n := by
  induction j with
  | zero =>
    simp only [Nat.add_zero, Nat.sub_zero, Nat.ascFactorial_zero, Nat.cast_one,
      map_one, one_mul]
    rfl
  | succ j ih =>
    have hi : m + 1 - (j + 1) < m + 1 := by lia
    have hidx : m + 1 - (j + 1) + 1 = m + 1 - j := by lia
    change derivativeProductVector s c r m (n + j + 1)
      (⟨m + 1 - (j + 1), hi⟩ : Fin (m + 1)).castSucc = _
    simp only [derivativeProductVector, Fin.lastCases_castSucc]
    rw [derivativeProductAux_of_zero r m (n + j) _ _ (by
      intro _
      exact hz _ (by lia) (by lia))]
    simp only [hidx]
    rw [ih (by lia) (fun l hl hlm => hz l (by lia) hlm)]
    rw [← mul_assoc, ← map_mul, Nat.ascFactorial_succ]
    push_cast
    congr 2
    ring

/-- Zero derivative factors give the full weak interlacing window. The
condition on `r` says that the first `j - 1` factors in forward order are zero. -/
theorem derivativeProductRow_interl_add {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (m n j : ℕ) (hj : j ≤ m + 1)
    (hz : ∀ l, m + 2 - j ≤ l → l ≤ m → r l = 0) :
    Interl (derivativeProductRow s c r m n) (derivativeProductRow s c r m (n + j)) := by
  by_cases hj0 : j = 0
  · subst j
    exact Interl.refl (fun _ => derivativeProductRow_splits hs hc hr m n)
  have hv := (derivativeProductVector_interlacing hs hc hr m (n + j)).interlacingSeq0
  rw [isInterlacingSeq0_iff_pairwise, List.pairwise_ofFn] at hv
  have h := hv (i := ⟨m + 1 - j, by lia⟩) (j := Fin.last (m + 1)) (by
    change m + 1 - j < m + 1
    lia)
  rw [derivativeProductVector_eq_earlier_row s c r m n j hj hz] at h
  have hpos : 0 < ((n + 1).ascFactorial j : ℝ) := by
    exact_mod_cast Nat.ascFactorial_pos n j
  have hscaled := h.C_mul_left_of_nonneg (inv_nonneg.mpr hpos.le)
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hpos.ne', map_one, one_mul,
    derivativeProductRow] using hscaled

/-- The derivative polynomial, with its scalar coefficient omitted. -/
noncomputable def derivativeProductFactor (r : ℕ → ℝ) (m : ℕ) : ℝ[X] :=
  ∏ k ∈ Ico 1 (m + 1), (X + C (r k))

/-- The auxiliary factor at reverse index `i`. The scalar coordinate has
factor one, and every other coordinate has a leading factor `z`. -/
noncomputable def derivativeProductPrefix (r : ℕ → ℝ) (m : ℕ)
    (i : Fin (m + 2)) : ℝ[X] :=
  if (i : ℕ) = m + 1 then 1
  else X * ∏ k ∈ Ico ((i : ℕ) + 1) (m + 1), (X + C (r k))

private lemma derivativeProductPrefix_step (r : ℕ → ℝ) {m i : ℕ}
    (hi : i + 1 < m + 1) :
    derivativeProductPrefix r m ⟨i, by lia⟩ =
      (X + C (r (i + 1))) * derivativeProductPrefix r m ⟨i + 1, by lia⟩ := by
  simp only [derivativeProductPrefix, show i ≠ m + 1 by lia,
    show i + 1 ≠ m + 1 by lia, ↓reduceIte]
  rw [prod_eq_prod_Ico_succ_bot hi]
  ring

private lemma derivativeProductAux_last (r : ℕ → ℝ) (m n : ℕ)
    (v : Fin (m + 2) → ℝ[X]) :
    derivativeProductAux r m n v (Fin.last m) =
      C (n + 1 : ℝ) * v (Fin.last (m + 1)) := by
  unfold derivativeProductAux
  rw [Fin.sum_univ_castSucc]
  have hz : (∑ j : Fin (m + 1),
      C (partialProductMatrix r (m + 1) (n + 1) (Fin.last m) j.castSucc) *
        v j.castSucc) = 0 := by
    apply sum_eq_zero
    intro j _
    have hj : ¬ m < (j : ℕ) := by have := j.isLt; lia
    simp [partialProductMatrix, hj]
  rw [hz, zero_add]
  simp [partialProductMatrix]

/-- New auxiliary coordinates are brackets of their prescribed polynomial
factors whenever the old vector is. -/
private lemma derivativeProductAux_eq_bracket (r : ℕ → ℝ) (m n : ℕ)
    (f : PowerSeries ℝ[X]) (v : Fin (m + 2) → ℝ[X])
    (hv : ∀ i, v i = polynomialBracket (derivativeProductPrefix r m i) f n) :
    ∀ i : Fin (m + 1), derivativeProductAux r m n v i =
      polynomialBracket (derivativeProductPrefix r m i.castSucc) f (n + 1) := by
  have haux : ∀ j, j < m + 1 →
      derivativeProductAux r m n v ⟨m - j, by lia⟩ =
        polynomialBracket (derivativeProductPrefix r m ⟨m - j, by lia⟩) f (n + 1) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [show (⟨m - 0, by lia⟩ : Fin (m + 1)) = Fin.last m by rfl,
        derivativeProductAux_last, hv]
      simp only [derivativeProductPrefix, Fin.val_last, ↓reduceIte,
        polynomialBracket_one, Nat.sub_zero, show m ≠ m + 1 by lia,
        Ico_self, prod_empty, mul_one]
      simpa using (polynomialBracket_linear_mul 0 1 f n).symm
    | succ j ih =>
      intro hj
      have hi : m - (j + 1) + 1 < m + 1 := by lia
      have hidx : m - (j + 1) + 1 = m - j := by lia
      have hstep := partialProductMatrix_action_succ r hi (n + 1) v
      change derivativeProductAux r m n v ⟨m - (j + 1), by lia⟩ =
        C (r (m - (j + 1) + 1)) *
          derivativeProductAux r m n v ⟨m - (j + 1) + 1, hi⟩ +
        C (n + 1 : ℝ) * v ⟨m - (j + 1) + 1, by lia⟩ at hstep
      simp only [hidx] at hstep
      rw [hstep, ih (by lia), hv, derivativeProductPrefix_step r hi,
        polynomialBracket_linear_mul]
      simp only [hidx]
  intro i
  have hidx : m - (m - (i : ℕ)) = (i : ℕ) := by have := i.isLt; lia
  have h := haux (m - i) (by lia)
  have hleft : (⟨m - (m - (i : ℕ)), by lia⟩ : Fin (m + 1)) = i := Fin.ext hidx
  have hright : (⟨m - (m - (i : ℕ)), by lia⟩ : Fin (m + 2)) = i.castSucc := Fin.ext hidx
  simpa only [hleft, hright] using h

/-- The derivative-product vector agrees with factorial coefficient extraction
from any series satisfying the exponential differential equation. -/
theorem derivativeProductVector_eq_bracket (s c : ℝ) (r : ℕ → ℝ) (m : ℕ)
    (f : PowerSeries ℝ[X]) (hf0 : factorialCoeff f 0 = 1)
    (hf : ∀ n, factorialCoeff f (n + 1) = C s * factorialCoeff f n +
      C c * X * polynomialBracket (derivativeProductFactor r m) f n) (n : ℕ) :
    ∀ i, derivativeProductVector s c r m n i =
      polynomialBracket (derivativeProductPrefix r m i) f n := by
  induction n with
  | zero =>
    intro i
    induction i using Fin.lastCases with
    | last => simpa [derivativeProductVector, derivativeProductPrefix] using hf0.symm
    | cast i =>
      have hi : (i : ℕ) ≠ m + 1 := by have := i.isLt; lia
      have hz : (derivativeProductPrefix r m i.castSucc).coeff 0 = 0 := by
        simp [derivativeProductPrefix, hi]
      rw [polynomialBracket_zero_of_coeff_zero hz]
      simp [derivativeProductVector]
  | succ n ih =>
    have haux := derivativeProductAux_eq_bracket r m n f _ ih
    intro i
    induction i using Fin.lastCases with
    | cast i =>
      simpa only [derivativeProductVector, Fin.lastCases_castSucc] using haux i
    | last =>
      simp only [derivativeProductPrefix, Fin.val_last, ↓reduceIte, polynomialBracket_one]
      simp only [derivativeProductVector, Fin.lastCases_last]
      change C s * derivativeProductVector s c r m n (Fin.last (m + 1)) +
        C (c / (n + 1)) * (X * derivativeProductAux r m n
          (derivativeProductVector s c r m n) 0) = _
      rw [ih, haux]
      simp only [derivativeProductPrefix, Fin.val_last, Fin.val_castSucc,
        Fin.val_zero, ↓reduceIte, polynomialBracket_one,
        show (0 : ℕ) ≠ m + 1 by lia]
      have hX := polynomialBracket_linear_mul 0 (derivativeProductFactor r m) f n
      simp only [map_zero, add_zero, zero_mul, zero_add] at hX
      change polynomialBracket (X * derivativeProductFactor r m) f (n + 1) = _ at hX
      change C s * factorialCoeff f n + C (c / (n + 1)) *
        (X * polynomialBracket (X * derivativeProductFactor r m) f (n + 1)) = _
      rw [hX, hf]
      have hN : (n + 1 : ℝ) ≠ 0 := by positivity
      have hcancel : c / (n + 1 : ℝ) * (n + 1) = c := div_mul_cancel₀ c hN
      have hpoly : C (c / (n + 1 : ℝ)) * C (n + 1 : ℝ) = C c := by
        rw [← map_mul, hcancel]
      linear_combination hpoly *
        (X * polynomialBracket (derivativeProductFactor r m) f n)

/-- The formal exponent `s z + t B(z)`. -/
noncomputable def singletonExponent (s : ℝ) (B : ℝ[X]) : PowerSeries ℝ[X] :=
  PowerSeries.C (C s) * PowerSeries.X +
    PowerSeries.C X * Polynomial.coeToPowerSeries.algHom ℝ[X] B

/-- The formal exponential with unmarked singleton weight `s`. -/
noncomputable def singletonSeries (s : ℝ) (B : ℝ[X]) : PowerSeries ℝ[X] :=
  (PowerSeries.exp ℝ[X]).subst (singletonExponent s B)

private lemma singletonExponent_constantCoeff (s : ℝ) {B : ℝ[X]}
    (hB : B.coeff 0 = 0) : PowerSeries.constantCoeff (singletonExponent s B) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [singletonExponent, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X, coeff_polynomialSeries, hB, map_zero, mul_zero, add_zero]
  norm_num

private lemma singletonSeries_zero (s : ℝ) {B : ℝ[X]} (hB : B.coeff 0 = 0) :
    factorialCoeff (singletonSeries s B) 0 = 1 := by
  simp only [factorialCoeff, Nat.factorial_zero, Nat.cast_one, map_one, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, singletonSeries]
  rw [PowerSeries.constantCoeff_eq, PowerSeries.constantCoeff_subst_of_constantCoeff_zero
    (singletonExponent_constantCoeff s hB)]
  exact PowerSeries.constantCoeff_exp

private lemma singletonSeries_derivative (s : ℝ) {B : ℝ[X]} (hB : B.coeff 0 = 0) :
    PowerSeries.derivative (singletonSeries s B) =
      (PowerSeries.C (C s) +
        PowerSeries.C X * Polynomial.coeToPowerSeries.algHom ℝ[X] B.derivative) *
          singletonSeries s B := by
  rw [singletonSeries, PowerSeries.derivative_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' (singletonExponent_constantCoeff s hB)),
    PowerSeries.derivative_exp]
  have hd : PowerSeries.derivative (singletonExponent s B) =
      PowerSeries.C (C s) +
        PowerSeries.C X * Polynomial.coeToPowerSeries.algHom ℝ[X] B.derivative := by
    simp only [singletonExponent, map_add, PowerSeries.derivative.leibniz,
      PowerSeries.derivative_C, PowerSeries.derivative_X, smul_eq_mul,
      mul_zero, add_zero, mul_one, derivative_polynomialSeries]
  rw [hd]
  exact mul_comm _ _

/-- The exponential coefficient recurrence uses the factored marked derivative. -/
theorem factorialCoeff_singletonSeries_succ (s c : ℝ) (r : ℕ → ℝ) (m : ℕ)
    {B : ℝ[X]} (hB0 : B.coeff 0 = 0)
    (hB : B.derivative = C c * derivativeProductFactor r m) (n : ℕ) :
    factorialCoeff (singletonSeries s B) (n + 1) =
      C s * factorialCoeff (singletonSeries s B) n +
        C c * X * polynomialBracket (derivativeProductFactor r m) (singletonSeries s B) n := by
  rw [← factorialCoeff_derivative, singletonSeries_derivative s hB0,
    add_mul, factorialCoeff_add, factorialCoeff_C_mul, mul_assoc,
    factorialCoeff_C_mul]
  change _ + X * polynomialBracket B.derivative (singletonSeries s B) n = _
  rw [hB, polynomialBracket_C_mul]
  ring

/-- The recurrence-defined scalar row is the literal exponential coefficient
`n! [zⁿ] exp(s z + t B)` whenever `B'` has the specified factorization. -/
theorem derivativeProductRow_eq_factorialCoeff (s c : ℝ) (r : ℕ → ℝ) (m : ℕ)
    {B : ℝ[X]} (hB0 : B.coeff 0 = 0)
    (hB : B.derivative = C c * derivativeProductFactor r m) (n : ℕ) :
    derivativeProductRow s c r m n = factorialCoeff (singletonSeries s B) n := by
  have h := derivativeProductVector_eq_bracket s c r m (singletonSeries s B)
    (singletonSeries_zero s hB0) (factorialCoeff_singletonSeries_succ s c r m hB0 hB)
    n (Fin.last (m + 1))
  simpa [derivativeProductRow, derivativeProductPrefix] using h

/-- A polynomial marked derivative with nonnegative linear factors gives
real-rooted exponential rows, including the boundary `s = 0`. -/
theorem factorialCoeff_singletonSeries_splits {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (m : ℕ) {B : ℝ[X]} (hB0 : B.coeff 0 = 0)
    (hB : B.derivative = C c * derivativeProductFactor r m) (n : ℕ) :
    (factorialCoeff (singletonSeries s B) n).Splits := by
  rw [← derivativeProductRow_eq_factorialCoeff s c r m hB0 hB]
  exact derivativeProductRow_splits hs hc hr m n

/-- The formal exponent of the family with `A = s z + q B`. -/
noncomputable def exponentialFamilyExponent (s q : ℝ) (B : ℝ[X]) : PowerSeries ℝ[X] :=
  PowerSeries.C (C s) * PowerSeries.X +
    PowerSeries.C (X + C q) * Polynomial.coeToPowerSeries.algHom ℝ[X] B

/-- Literal factorial coefficient extraction from `exp(s z + (q + t) B)`. -/
noncomputable def exponentialFamilyRow (s q : ℝ) (B : ℝ[X]) (n : ℕ) : ℝ[X] :=
  factorialCoeff ((PowerSeries.exp ℝ[X]).subst (exponentialFamilyExponent s q B)) n

/-- Adding `q B` to the unmarked exponent translates the row variable by `q`. -/
theorem exponentialFamilyRow_eq_comp (s q : ℝ) {B : ℝ[X]} (hB : B.coeff 0 = 0)
    (n : ℕ) : exponentialFamilyRow s q B n =
      (factorialCoeff (singletonSeries s B) n).comp (X + C q) := by
  let h : ℝ[X] →+* ℝ[X] := (Polynomial.aeval (X + C q)).toRingHom
  have hC (a : ℝ) : h (C a) = C a := by simp [h]
  have hX : h X = X + C q := by simp [h]
  have hlift : (Polynomial.coeToPowerSeries.algHom ℝ[X] B).map h =
      Polynomial.coeToPowerSeries.algHom ℝ[X] B := by
    apply PowerSeries.ext
    intro k
    rw [PowerSeries.coeff_map, coeff_polynomialSeries, hC]
  have hexp : (singletonExponent s B).map h = exponentialFamilyExponent s q B := by
    simp only [singletonExponent, exponentialFamilyExponent, map_add, map_mul,
      PowerSeries.map_C, PowerSeries.map_X, hlift, hC, hX]
  have hseries : (singletonSeries s B).map h =
      (PowerSeries.exp ℝ[X]).subst (exponentialFamilyExponent s q B) := by
    unfold singletonSeries
    change MvPowerSeries.map h ((PowerSeries.exp ℝ[X]).subst (singletonExponent s B)) = _
    rw [PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' (singletonExponent_constantCoeff s hB))]
    change ((PowerSeries.exp ℝ[X]).map h).subst ((singletonExponent s B).map h) = _
    rw [PowerSeries.map_exp, hexp]
  unfold exponentialFamilyRow factorialCoeff
  rw [← hseries, PowerSeries.coeff_map]
  change C (n.factorial : ℝ) * Polynomial.aeval (X + C q)
    (PowerSeries.coeff n (singletonSeries s B)) = _
  rw [← Polynomial.comp_eq_aeval, mul_comp, C_comp]

/-- The polynomial derivative criterion for real-rooted exponential rows.
The factorization is allowed to contain zero factors and repeated factors;
the translation parameter `q` may be any real number. -/
theorem exponentialFamilyRow_splits_of_derivative_product {s c : ℝ}
    (hs : 0 ≤ s) (hc : 0 ≤ c) {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (m : ℕ)
    {B : ℝ[X]} (hB0 : B.coeff 0 = 0)
    (hB : B.derivative = C c * derivativeProductFactor r m) (q : ℝ) (n : ℕ) :
    (exponentialFamilyRow s q B n).Splits := by
  rw [exponentialFamilyRow_eq_comp s q hB0]
  exact (factorialCoeff_singletonSeries_splits hs hc hr m hB0 hB n).comp_X_add_C q

/-- The weak interlacing window for the literal exponential rows. If `B'`
starts with `z^(k - 1)`, the zero-factor condition holds for every `j ≤ k`. -/
theorem exponentialFamilyRow_interl_add_of_derivative_product {s c : ℝ}
    (hs : 0 ≤ s) (hc : 0 ≤ c) {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (m : ℕ)
    {B : ℝ[X]} (hB0 : B.coeff 0 = 0)
    (hB : B.derivative = C c * derivativeProductFactor r m) (q : ℝ) (n j : ℕ)
    (hj : j ≤ m + 1) (hz : ∀ l, m + 2 - j ≤ l → l ≤ m → r l = 0) :
    Interl (exponentialFamilyRow s q B n) (exponentialFamilyRow s q B (n + j)) := by
  rw [exponentialFamilyRow_eq_comp s q hB0, exponentialFamilyRow_eq_comp s q hB0,
    ← derivativeProductRow_eq_factorialCoeff s c r m hB0 hB,
    ← derivativeProductRow_eq_factorialCoeff s c r m hB0 hB]
  exact (derivativeProductRow_interl_add hs hc hr m n j hj hz).comp_X_add_C q

/-- The pole-free polynomial derivative criterion: if `B'` splits and has
nonnegative coefficients, every nonzero row of `exp(s z + (q + t) B)` is
real-rooted. In fact the zero polynomial is included in the splitting conclusion. -/
theorem exponentialFamilyRow_splits {s : ℝ} (hs : 0 ≤ s) {B : ℝ[X]}
    (hB0 : B.coeff 0 = 0) (hBnn : HasNonnegCoeffs B.derivative)
    (hBs : B.derivative.Splits) (q : ℝ) (n : ℕ) :
    (exponentialFamilyRow s q B n).Splits := by
  obtain ⟨a, ha, hfac⟩ := hBs.exists_fin_eq_C_mul_prod
  let r : ℕ → ℝ := fun k =>
    if hk : k - 1 < B.derivative.natDegree then -a ⟨k - 1, hk⟩ else 0
  have hroot (i : Fin B.derivative.natDegree) : a i ∈ B.derivative.roots := by
    rw [← ha]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  have hr (k : ℕ) : 0 ≤ r k := by
    dsimp [r]
    split_ifs with hk
    · exact neg_nonneg.mpr (roots_nonpos_of_hasNonnegCoeffs hBnn _ (hroot _))
    · exact le_rfl
  have hprod : derivativeProductFactor r B.derivative.natDegree =
      ∏ i, (X - C (a i)) := by
    rw [derivativeProductFactor, prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel_right]
    rw [← Fin.prod_univ_eq_prod_range]
    apply prod_congr rfl
    intro i _
    simp only [r, show 1 + (i : ℕ) - 1 = (i : ℕ) by lia, dite_eq_left i.isLt,
      map_neg, sub_eq_add_neg]
  have hlead : 0 ≤ B.derivative.leadingCoeff := by
    simpa only [coeff_natDegree] using hBnn B.derivative.natDegree
  apply exponentialFamilyRow_splits_of_derivative_product hs hlead hr
    B.derivative.natDegree hB0 (q := q) (n := n)
  rw [hprod]
  exact hfac

end RealRooted.ExponentialRows
