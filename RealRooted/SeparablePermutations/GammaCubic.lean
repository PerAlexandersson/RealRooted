import RealRooted.Mathlib.RingTheory.PowerSeries.LagrangeInversion
import RealRooted.SeparablePermutations.Gamma
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The cubic functional equation for the gamma-polynomials of separable permutations

Zhang (SSRN 7510941, Proposition 3.3) gives the closed form
`Γ_{N+2} = (2 ^ N / N!) * compression N 1 B_N` for the gamma-polynomials of the descent
enumerators of separable permutations, which is the definition of `gammaPolynomial`.  Fu, Lin and
Zeng show that the generating series `G = ∑ Γ_n w ^ n` satisfies the cubic equation
`G = w + w G + x w G² + x G³`.  We prove that the closed form satisfies this equation
coefficientwise in `w`; this is `gammaPolynomial_cubic`.

The proof follows the Lagrange–Bürmann inversion formula.  With `G = w / (1 - V)` and an
auxiliary parameter `s` (later specialized to `s = x w`), the cubic becomes the Lagrange-type
equation `V = w φ(V)` with `φ(u) = 1 + s (2 - u) / (1 - u) ^ 2`.  Inversion
(`PowerSeries.succ_mul_coeff_succ_subst`) gives the coefficients of `G` as
`[w ^ m s ^ k] G / w = (1 / m) C(m, k) [u ^ (m - 1)] (2 - u) ^ k (1 - u) ^ (-2 k - 2)`.
A second induction on the recurrence for `B_N` identifies
`k! 2 ^ N [x ^ k] B_N = N! [u ^ N] (u (2 - u)) ^ k / (1 - u) ^ (2 k + 2)`, and the two
expressions agree with the coefficients of `Γ`.

The proof was found by Aristotle (Harmonic) over `ℚ` as a self-contained development
(`GammaCubic/{Lagrange,SForm,Ev,Zhang,Final}.lean`) and was then ported to Mathlib's current
power-series API and to the real coefficient field used by `gammaPolynomial`.

## Main results

* `RealRooted.SeparablePermutations.gammaPolynomial_cubic`: for `n ≥ 2`,
  `Γ_n = Γ_{n-1} + x ∑_{i+j=n-1} Γ_i Γ_j + x ∑_{i+j+l=n} Γ_i Γ_j Γ_l`
  (with `Γ_0 = 0`, so the index ranges take care of themselves).
-/

noncomputable section

namespace RealRooted.SeparablePermutations.GammaCubic

open PowerSeries Finset

/-- The coefficient ring `ℝ⟦s⟧` of the auxiliary parameter `s`. -/
private abbrev Q : Type := PowerSeries ℝ

private instance : CharZero Q := RingHom.charZero (constantCoeff (R := ℝ))

/-- The auxiliary parameter `s ∈ ℝ⟦s⟧`. -/
private def sA : Q := PowerSeries.X

/-- The geometric series `1 / (1 - X)` over `ℝ⟦s⟧`. -/
private def geom : Q⟦X⟧ := mk 1

private lemma one_sub_mul_geom : (1 - X) * geom = 1 := by
  rw [mul_comm]
  exact mk_one_mul_one_sub_eq_one Q

/-- `φ(u) = 1 + s (2 - u) / (1 - u) ^ 2`. -/
private def phiS : Q⟦X⟧ := 1 + C sA * (2 - X) * geom ^ 2

private lemma derivative_geom : d⁄dX geom = geom ^ 2 := by
  have h := congrArg (fun f : Q⟦X⟧ => d⁄dX f) one_sub_mul_geom
  simp only [Derivation.leibniz, smul_eq_mul, map_sub, Derivation.map_one_eq_zero, derivative_X,
    zero_sub, mul_neg, mul_one] at h
  linear_combination geom * h - d⁄dX geom * one_sub_mul_geom

/-- The solution `J = 1 / (1 - V)` of the parametrized cubic over `ℝ⟦s⟧`, with the coefficients
given by Lagrange inversion. -/
private theorem exists_series_cubic :
    ∃ J : Q⟦X⟧, J - 1 = X * J + C sA * X * J ^ 2 + C sA * X * J ^ 3 ∧
      constantCoeff J = 1 ∧
      ∀ m : ℕ, ((m : Q) + 1) * coeff (m + 1) J = coeff m (geom ^ 2 * phiS ^ (m + 1)) := by
  set c : Q⟦X⟧ := C sA with hc
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ * phiS = 1 := by
    have : IsUnit phiS := by
      rw [isUnit_iff_constantCoeff, isUnit_iff_constantCoeff]
      simp [phiS, geom, sA]
    obtain ⟨u, hu⟩ := this
    exact ⟨↑u⁻¹, by rw [← hu]; simp⟩
  let T : Q⟦X⟧ → Q⟦X⟧ := fun V ↦ 2 * V ^ 2 - V ^ 3 + X * (1 + 2 * c - (2 + c) * V + V ^ 2)
  obtain ⟨S, hS0, hST⟩ := exists_constantCoeff_eq_zero_apply_eq_self T
    (by intro a ha; simp [T, ha])
    (by
      intro a b j ha hb hab
      have : T a - T b = (a - b) * (2 * (a + b) - (a ^ 2 + a * b + b ^ 2) +
          X * (-(2 + c) + a + b)) := by simp only [T]; ring
      rw [this, pow_succ]
      apply mul_dvd_mul hab
      rw [X_dvd_iff]
      simp [ha, hb])
  have hSs : HasSubst S := HasSubst.of_constantCoeff_zero' hS0
  set σ := substAlgHom (R := Q) hSs with hσ
  have hσX : σ X = S := substAlgHom_X hSs
  have hσc : σ c = c := by
    rw [hσ, coe_substAlgHom, hc]
    exact subst_C _
  set J := σ geom with hJdef
  have hJ : (1 - S) * J = 1 := by
    have := congrArg σ one_sub_mul_geom
    rwa [map_mul, map_sub, map_one, hσX] at this
  have e1 : S * (1 - S) ^ 2 - X * ((1 - S) ^ 2 + c * (2 - S)) = 0 := by
    have : T S = S := hST
    simp only [T] at this
    linear_combination -this
  have hσφ : σ phiS = 1 + c * (2 - S) * J ^ 2 := by
    simp only [phiS, map_add, map_mul, map_one, map_sub, map_pow, hσX, ← hc, hσc]
    rw [show (2 : Q⟦X⟧) = 1 + 1 by norm_num, map_add, map_one]
  have hSX : S = X * σ phiS := by
    rw [hσφ]
    linear_combination J ^ 2 * e1 - (S - X) * ((1 - S) * J + 1) * hJ
  have hsubst : subst S (X * ρ) = X := by
    rw [← coe_substAlgHom hSs, ← hσ, map_mul, hσX]
    calc S * σ ρ = X * (σ ρ * σ phiS) := by rw [hSX]; ring
    _ = X := by rw [← map_mul, hρ, map_one, mul_one]
  have hH : d⁄dX (X * geom) = geom ^ 2 := by
    simp only [Derivation.leibniz, derivative_geom, smul_eq_mul, derivative_X, mul_one]
    linear_combination (-geom) * one_sub_mul_geom
  have hσH : subst S (X * geom) = S * J := by
    rw [← coe_substAlgHom hSs, ← hσ, map_mul, hσX]
  refine ⟨J, ?_, ?_, ?_⟩
  · linear_combination J ^ 3 * e1 - (J * ((1 - S) * J + 1) - (((1 - S) * J) ^ 2 +
      (1 - S) * J + 1) - X * J * ((1 - S) * J + 1) - c * X * J ^ 2) * hJ
  · have : J = 1 + S * J := by linear_combination hJ
    rw [this, map_add, map_mul, hS0]
    simp
  · intro m
    have := succ_mul_coeff_succ_subst ρ phiS S (X * geom) hρ hS0 hsubst m
    rw [hσH, hH] at this
    have hJ' : J = 1 + S * J := by linear_combination hJ
    have hcJ : coeff (m + 1) J = coeff (m + 1) (S * J) := by
      conv_lhs => rw [hJ']
      rw [map_add, coeff_one, ite_eq_right (by lia), zero_add]
    rw [hcJ, this]

/-! ### The specialization `s ↦ x w` -/

private lemma sum_antidiagonal_shift {R : Type*} [AddCommMonoid R] (F : ℕ → ℕ → R)
    (n k1 k2 : ℕ) :
    ∑ p ∈ antidiagonal n, (if k1 ≤ p.1 ∧ k2 ≤ p.2 then F (p.1 - k1) (p.2 - k2) else 0) =
      if k1 + k2 ≤ n then ∑ q ∈ antidiagonal (n - (k1 + k2)), F q.1 q.2 else 0 := by
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  split_ifs with h
  · rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    obtain ⟨m, rfl⟩ : ∃ m, n = k1 + m + k2 := ⟨n - k1 - k2, by lia⟩
    rw [show k1 + m + k2 - (k1 + k2) = m by lia, Nat.succ_eq_add_one, Nat.succ_eq_add_one,
      show k1 + m + k2 + 1 = k1 + ((m + 1) + k2) by lia, sum_range_add, sum_range_add]
    rw [sum_eq_zero (fun a ha => by rw [mem_range] at ha; rw [ite_eq_right (by lia)]), zero_add]
    rw [sum_eq_zero (s := range k2)
      (fun a ha => by rw [mem_range] at ha; rw [ite_eq_right (by lia)]), add_zero]
    apply sum_congr rfl
    intro x hx
    rw [mem_range] at hx
    rw [ite_eq_left (by lia)]
    congr 1 <;> lia
  · exact sum_eq_zero (fun a ha => by rw [mem_range] at ha; rw [ite_eq_right (by lia)])

/-- The specialization `s ↦ x w` from `ℝ⟦s⟧⟦w⟧` to `ℝ[x]⟦w⟧`. -/
private def ev (f : Q⟦X⟧) : (Polynomial ℝ)⟦X⟧ :=
  mk fun n ↦ ∑ p ∈ antidiagonal n, Polynomial.monomial p.2 (coeff p.2 (coeff p.1 f))

private lemma coeff_ev (f : Q⟦X⟧) (n k : ℕ) :
    (coeff n (ev f)).coeff k = if k ≤ n then coeff k (coeff (n - k) f) else 0 := by
  rw [ev, coeff_mk, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  split_ifs with h
  · rw [sum_eq_single (n - k, k)]
    · simp
    · rintro ⟨a, b⟩ hab hne
      rw [HasAntidiagonal.mem_antidiagonal] at hab
      rw [ite_eq_right]
      intro hb
      apply hne
      simp only at hb
      subst hb
      ext <;> simp only
      lia
    · intro hn
      exfalso
      apply hn
      rw [HasAntidiagonal.mem_antidiagonal]
      lia
  · apply sum_eq_zero
    rintro ⟨a, b⟩ hab
    rw [HasAntidiagonal.mem_antidiagonal] at hab
    rw [ite_eq_right]
    simp only
    lia

private lemma ev_add (f g : Q⟦X⟧) : ev (f + g) = ev f + ev g := by
  ext n k
  simp only [map_add, Polynomial.coeff_add, coeff_ev]
  split_ifs <;> simp

private lemma ev_mul (f g : Q⟦X⟧) : ev (f * g) = ev f * ev g := by
  ext n k
  rw [coeff_ev]
  conv_rhs => rw [coeff_mul, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_mul, coeff_ev]
  rw [sum_comm (s := antidiagonal n)]
  have : ∀ x ∈ antidiagonal k, (∑ p ∈ antidiagonal n,
      (if x.1 ≤ p.1 then coeff x.1 (coeff (p.1 - x.1) f) else 0) *
      (if x.2 ≤ p.2 then coeff x.2 (coeff (p.2 - x.2) g) else 0)) =
      if k ≤ n then ∑ q ∈ antidiagonal (n - k),
        coeff x.1 (coeff q.1 f) * coeff x.2 (coeff q.2 g) else 0 := by
    intro x hx
    rw [HasAntidiagonal.mem_antidiagonal] at hx
    rw [← hx, ← sum_antidiagonal_shift (fun i j ↦ coeff x.1 (coeff i f) * coeff x.2 (coeff j g))]
    apply sum_congr rfl
    intro p hp
    split_ifs <;> simp_all
  rw [sum_congr rfl this]
  split_ifs with h
  · rw [coeff_mul, map_sum]
    simp only [coeff_mul]
    rw [sum_comm]
  · simp

private lemma ev_one : ev 1 = 1 := by
  ext n k
  rw [coeff_ev]
  by_cases hn : n = 0
  · subst hn
    rcases k with _ | k <;> simp [Polynomial.coeff_one]
  · conv_rhs => rw [coeff_one, ite_eq_right hn, Polynomial.coeff_zero]
    split_ifs with hk
    · rw [coeff_one]
      split_ifs with h0
      · rw [coeff_one, ite_eq_right (by lia)]
      · rw [map_zero]
    · rfl

private lemma ev_X : ev X = X := by
  ext n k
  rw [coeff_ev]
  by_cases hn : n = 1
  · subst hn
    rcases k with _ | _ | k <;> simp [Polynomial.coeff_one]
  · conv_rhs => rw [coeff_X, ite_eq_right hn, Polynomial.coeff_zero]
    split_ifs with hk
    · rw [coeff_X]
      split_ifs with h0
      · rw [coeff_one, ite_eq_right (by lia)]
      · rw [map_zero]
    · rfl

private lemma ev_C_sA : ev (C sA) = C Polynomial.X * X := by
  ext n k
  rw [coeff_ev, coeff_C_mul, coeff_X]
  by_cases hn : n = 1
  · subst hn
    rcases k with _ | _ | k <;> simp [coeff_C, sA, Polynomial.coeff_X]
  · rw [ite_eq_right hn, mul_zero, Polynomial.coeff_zero]
    split_ifs with hk
    · rw [coeff_C]
      by_cases h0 : n - k = 0
      · rw [ite_eq_left h0, sA, coeff_X, ite_eq_right (by lia)]
      · rw [ite_eq_right h0, map_zero]
    · rfl

/-! ### Closed form for the coefficients of Zhang's auxiliary polynomials -/

/-- The geometric series `1 / (1 - X)` over `ℝ`. -/
private def g0 : ℝ⟦X⟧ := mk 1

private lemma one_sub_mul_g0 : (1 - X) * g0 = 1 := by
  rw [mul_comm]
  exact mk_one_mul_one_sub_eq_one ℝ

private lemma derivative_g0 : d⁄dX g0 = g0 ^ 2 := by
  have h := congrArg (fun f : ℝ⟦X⟧ => d⁄dX f) one_sub_mul_g0
  simp only [Derivation.leibniz, smul_eq_mul, map_sub, Derivation.map_one_eq_zero, derivative_X,
    zero_sub, mul_neg, mul_one] at h
  linear_combination g0 * h - d⁄dX g0 * one_sub_mul_g0

/-- `R_k = (X (2 - X)) ^ k / (1 - X) ^ (2 k + 2)`. -/
private def Rk (k : ℕ) : ℝ⟦X⟧ := (X * (2 - X)) ^ k * g0 ^ (2 * k + 2)

private lemma derivative_Rk_zero : (1 - X) * d⁄dX (Rk 0) = 2 * Rk 0 := by
  simp only [Rk, pow_zero, one_mul, mul_zero, zero_add, derivative_pow, derivative_g0]
  push_cast
  linear_combination (2 * g0 ^ 2) * one_sub_mul_g0

private lemma derivative_Rk_succ (k : ℕ) :
    (1 - X) * d⁄dX (Rk (k + 1)) =
      2 * ((k : ℝ⟦X⟧) + 1) * Rk k + (2 * (k : ℝ⟦X⟧) + 4) * Rk (k + 1) := by
  have hy : d⁄dX (X * (2 - X) : ℝ⟦X⟧) = 2 - 2 * X := by
    have h2 : d⁄dX (2 : ℝ⟦X⟧) = 0 := by
      rw [show (2 : ℝ⟦X⟧) = 1 + 1 by norm_num, map_add, Derivation.map_one_eq_zero, add_zero]
    simp only [Derivation.leibniz, map_sub, h2, derivative_X, zero_sub, smul_eq_mul, mul_neg,
      mul_one]
    ring
  simp only [Rk, Derivation.leibniz, derivative_pow, derivative_g0, hy, smul_eq_mul]
  rw [show 2 * (k + 1) + 2 - 1 = 2 * k + 3 by lia, show k + 1 - 1 = k by lia]
  push_cast
  linear_combination (2 * (k + 1) * (X * (2 - X)) ^ k * g0 ^ (2 * k + 2) * ((1 - X) * g0 + 1) +
    (2 * k + 4) * (X * (2 - X)) ^ (k + 1) * g0 ^ (2 * k + 4)) * one_sub_mul_g0

private lemma coeff_zero_Rk (k : ℕ) : coeff 0 (Rk k) = if k = 0 then 1 else 0 := by
  rcases k with _ | k
  · simp [Rk, g0, pow_two]
  · simp [Rk, mul_pow, pow_succ, mul_assoc]

private lemma coeff_derivative_split (f : ℝ⟦X⟧) (N : ℕ) :
    coeff N (d⁄dX f) = coeff N ((1 - X) * d⁄dX f) + N * coeff N f := by
  rw [sub_mul, one_mul, map_sub]
  rcases N with _ | N
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative f N, coeff_derivative f (N + 1)]
    push_cast
    ring

private lemma coeff_succ_Rk_mul (k N : ℕ) :
    ((N + 1 : ℕ) : ℝ) * coeff (N + 1) (Rk k) = coeff N (d⁄dX (Rk k)) := by
  rw [coeff_derivative]
  push_cast
  ring

private lemma aux_coeff_rec (p : Polynomial ℝ) (a : ℝ) (k : ℕ) :
    ((Polynomial.X + Polynomial.C a) * p + Polynomial.X * Polynomial.derivative p).coeff k =
      (if k = 0 then 0 else p.coeff (k - 1)) + (a + k) * p.coeff k := by
  rcases k with _ | k
  · simp [add_mul]
  · simp only [add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_derivative]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right,
      Nat.cast_add, Nat.cast_one]
    ring

/-- Zhang's auxiliary polynomials in closed form: `k! 2 ^ N [x ^ k] B_N = N! [u ^ N] R_k`. -/
private theorem factorial_mul_coeff_auxPolynomial (N k : ℕ) :
    (k.factorial : ℝ) * 2 ^ N * (auxPolynomial N).coeff k = N.factorial * coeff N (Rk k) := by
  induction N generalizing k with
  | zero =>
    rw [auxPolynomial_zero, coeff_zero_Rk, Polynomial.coeff_one]
    rcases k with _ | k <;> simp
  | succ N ih =>
    rw [show ((N + 1).factorial : ℝ) * coeff (N + 1) (Rk k) =
        N.factorial * coeff N (d⁄dX (Rk k)) by
      rw [← coeff_succ_Rk_mul, Nat.factorial_succ]
      push_cast
      ring]
    rw [auxPolynomial_succ, aux_coeff_rec, coeff_derivative_split]
    rcases k with _ | k
    · rw [derivative_Rk_zero]
      have := ih 0
      simp only [ite_true, Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, add_zero,
        zero_add] at this ⊢
      rw [show (2 : ℝ⟦X⟧) = C 2 from (map_ofNat C 2).symm, coeff_C_mul, pow_succ]
      linear_combination ((N : ℝ) + 2) * this
    · rw [derivative_Rk_succ]
      have h1 := ih k
      have h2 := ih (k + 1)
      simp only [ite_eq_right (Nat.succ_ne_zero k), Nat.add_sub_cancel, map_add] at h1 h2 ⊢
      rw [show 2 * ((k : ℝ⟦X⟧) + 1) = C (2 * ((k : ℝ) + 1)) by
          rw [map_mul, map_add, map_natCast, map_one, map_ofNat],
        show 2 * (k : ℝ⟦X⟧) + 4 = C (2 * (k : ℝ) + 4) by
          rw [map_add, map_mul, map_natCast, map_ofNat, map_ofNat], coeff_C_mul, coeff_C_mul]
      rw [Nat.factorial_succ] at h2 ⊢
      push_cast at h1 h2 ⊢
      rw [pow_succ]
      linear_combination (2 * ((k : ℝ) + 1)) * h1 + ((N : ℝ) + 2 * k + 4) * h2

/-! ### The series `G` -/

/-- `F_k = (2 - X) ^ k / (1 - X) ^ (2 k + 2)` over `ℝ`. -/
private def Fk (k : ℕ) : ℝ⟦X⟧ := (2 - X) ^ k * g0 ^ (2 * k + 2)

private lemma coeff_Rk (N k : ℕ) (hk : k ≤ N) : coeff N (Rk k) = coeff (N - k) (Fk k) := by
  rw [Rk, Fk, mul_pow, mul_assoc, coeff_X_pow_mul', ite_eq_left hk]

private lemma geom_eq : geom = map (C : ℝ →+* Q) g0 := by
  ext n
  simp [geom, g0]

private lemma geom_sq_mul_phiS_pow (m : ℕ) : geom ^ 2 * phiS ^ (m + 1) =
    ∑ j ∈ range (m + 1 + 1), C (sA ^ j * ((m + 1).choose j : Q)) * map (C : ℝ →+* Q) (Fk j) := by
  rw [phiS, add_comm, add_pow, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [Fk, geom_eq]
  simp only [one_pow, mul_one, mul_pow, map_mul, map_pow, map_sub, map_X, map_ofNat, map_natCast]
  ring

private lemma coeff_coeff_geom_sq_mul_phiS_pow (m k : ℕ) :
    coeff k (coeff m (geom ^ 2 * phiS ^ (m + 1))) = ((m + 1).choose k : ℝ) * coeff m (Fk k) := by
  rw [geom_sq_mul_phiS_pow, map_sum, map_sum]
  simp only [coeff_C_mul, coeff_map]
  have : ∀ j ∈ range (m + 1 + 1), coeff k (sA ^ j * ((m + 1).choose j : Q) *
      C (coeff m (Fk j))) = if k = j then ((m + 1).choose k : ℝ) * coeff m (Fk k) else 0 := by
    intro j _
    rw [show sA ^ j * ((m + 1).choose j : Q) * C (coeff m (Fk j)) =
      C (((m + 1).choose j : ℝ) * coeff m (Fk j)) * X ^ j by
        rw [sA, map_mul, map_natCast]
        ring, coeff_C_mul_X_pow]
    split_ifs with h <;> simp_all
  rw [sum_congr rfl this, sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_range] at h
    rw [Nat.choose_eq_zero_of_lt (by lia), Nat.cast_zero, zero_mul]

private theorem exists_series_gammaPolynomial : ∃ G : (Polynomial ℝ)⟦X⟧,
    G = X + X * G + C Polynomial.X * X * G ^ 2 + C Polynomial.X * G ^ 3 ∧
    coeff 0 G = 0 ∧ coeff 1 G = 1 ∧
    ∀ N k : ℕ, (coeff (N + 2) G).coeff k =
      if 2 * k ≤ N + 1 then
        ((N + 1 - k).choose k : ℝ) / (N + 1 - k : ℕ) * coeff (N - k) (Fk k) else 0 := by
  obtain ⟨J, hJ, hJ0, hJc⟩ := exists_series_cubic
  have hcJ : ∀ m k : ℕ, coeff k (coeff (m + 1) J) =
      ((m + 1).choose k : ℝ) / (m + 1 : ℕ) * coeff m (Fk k) := by
    intro m k
    have := congrArg (coeff k) (hJc m)
    rw [coeff_coeff_geom_sq_mul_phiS_pow, show ((m : Q) + 1) = C ((m : ℝ) + 1) by simp,
      coeff_C_mul] at this
    rw [div_mul_eq_mul_div, eq_div_iff (by positivity), ← this]
    push_cast
    ring
  refine ⟨X * ev J, ?_, ?_, ?_, ?_⟩
  · have e : J = 1 + X * J + C sA * X * J ^ 2 + C sA * X * J ^ 3 := by
      linear_combination hJ
    have := congrArg ev e
    simp only [ev_add, ev_mul, pow_succ, pow_zero, ev_one, ev_X, ev_C_sA] at this
    conv_lhs => rw [this]
    ring
  · simp
  · rw [coeff_succ_X_mul]
    ext k
    rw [coeff_ev, Polynomial.coeff_one]
    rcases k with _ | k
    · rw [ite_eq_left le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply (R := Q) J, hJ0]
      simp
    · simp
  · intro N k
    rw [coeff_succ_X_mul, coeff_ev]
    by_cases hk : k ≤ N + 1
    · rw [ite_eq_left hk]
      by_cases h2 : 2 * k ≤ N + 1
      · rw [ite_eq_left h2]
        obtain ⟨m, hm⟩ : ∃ m, N + 1 - k = m + 1 := ⟨N - k, by lia⟩
        rw [hm, hcJ, show N - k = m by lia]
      · rw [ite_eq_right h2]
        rcases hm : N + 1 - k with _ | m
        · rw [coeff_zero_eq_constantCoeff_apply (R := Q) J, hJ0, coeff_one,
            ite_eq_right (by lia)]
        · rw [hcJ, Nat.choose_eq_zero_of_lt (by lia)]
          simp
    · rw [ite_eq_right hk, ite_eq_right (by lia)]

end RealRooted.SeparablePermutations.GammaCubic

namespace RealRooted.SeparablePermutations

open Polynomial Finset

/-- The coefficients of `Γ_{N+2}` in the Lagrange-inversion form. -/
private lemma coeff_gammaPolynomial_add_two_eq (N k : ℕ) :
    (gammaPolynomial (N + 2)).coeff k =
      if 2 * k ≤ N + 1 then
        ((N + 1 - k).choose k : ℝ) / (N + 1 - k : ℕ) *
          PowerSeries.coeff (N - k) (GammaCubic.Fk k) else 0 := by
  rw [coeff_gammaPolynomial_add_two]
  by_cases h : 2 * k ≤ N + 1
  · rw [ite_eq_left h, ite_eq_left h]
    have hz := GammaCubic.factorial_mul_coeff_auxPolynomial N k
    rw [GammaCubic.coeff_Rk N k (by lia)] at hz
    have hN : (N.factorial : ℝ) ≠ 0 := by positivity
    have hcF : PowerSeries.coeff (N - k) (GammaCubic.Fk k) =
        k.factorial * 2 ^ N * (auxPolynomial N).coeff k / N.factorial := by
      rw [eq_div_iff hN, hz]
      ring
    rw [hcF]
    obtain ⟨a, ha⟩ : ∃ a, N - k = a := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, N + 1 - 2 * k = r := ⟨_, rfl⟩
    have e1 : N + 1 - k = a + 1 := by lia
    have e2 : a + 1 - k = r := by lia
    rw [ha, hr, e1, Nat.cast_choose ℝ (by lia : k ≤ a + 1), e2, Nat.factorial_succ]
    have : (N.factorial : ℝ) ≠ 0 := by positivity
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    have : (a.factorial : ℝ) ≠ 0 := by positivity
    have : (r.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  · rw [ite_eq_right h, ite_eq_right h]

/-- The generating series `∑ Γ_n w ^ n` of `gammaPolynomial` satisfies the functional equation
`G = w + w G + x w G² + x G³`. -/
private lemma exists_series_gammaPolynomial_cubic : ∃ G : PowerSeries ℝ[X],
    G = PowerSeries.X + PowerSeries.X * G + PowerSeries.C X * PowerSeries.X * G ^ 2 +
      PowerSeries.C X * G ^ 3 ∧ ∀ n, PowerSeries.coeff n G = gammaPolynomial n := by
  obtain ⟨G, hG, hG0, hG1, hGc⟩ := GammaCubic.exists_series_gammaPolynomial
  refine ⟨G, hG, ?_⟩
  intro n
  match n with
  | 0 => rw [hG0, gammaPolynomial_zero]
  | 1 => rw [hG1, gammaPolynomial_one]
  | N + 2 =>
    ext k
    rw [hGc, coeff_gammaPolynomial_add_two_eq]

/-- Fu–Lin–Zeng's functional equation `G = w + w G + x w G² + x G³` for the generating series
`G = ∑ Γ_n w ^ n` of the gamma-polynomials, coefficientwise in `w`: for every `n ≥ 2`,
`Γ_n = Γ_{n-1} + x ∑_{i+j=n-1} Γ_i Γ_j + x ∑_{i+j+l=n} Γ_i Γ_j Γ_l`.  Here `Γ_0 = 0`, so the
index ranges need no further restriction.  The proof uses Lagrange inversion. -/
theorem gammaPolynomial_cubic {n : ℕ} (hn : 2 ≤ n) :
    gammaPolynomial n = gammaPolynomial (n - 1) +
      X * (∑ i ∈ range n, gammaPolynomial i * gammaPolynomial (n - 1 - i)) +
      X * (∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
        gammaPolynomial i * gammaPolynomial j * gammaPolynomial (n - i - j)) := by
  obtain ⟨G, hG, hc⟩ := exists_series_gammaPolynomial_cubic
  have hsq : ∀ j, PowerSeries.coeff j (G ^ 2) =
      ∑ i ∈ range (j + 1), gammaPolynomial i * gammaPolynomial (j - i) := by
    intro j
    rw [pow_two, PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [hc]
  have hcube : PowerSeries.coeff n (G ^ 3) =
      ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
        gammaPolynomial i * gammaPolynomial j * gammaPolynomial (n - i - j) := by
    rw [pow_succ', PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    rw [hc, hsq, show n - i + 1 = n + 1 - i by lia, mul_sum]
    apply sum_congr rfl
    intro j _
    rw [Nat.sub_sub]
    ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  have h := congrArg (PowerSeries.coeff (m + 1)) hG
  rw [map_add, map_add, map_add, PowerSeries.coeff_X, ite_eq_right (show m + 1 ≠ 1 by lia),
    zero_add, PowerSeries.coeff_succ_X_mul, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, hsq, hcube] at h
  rw [← hc, h, hc, Nat.add_sub_cancel]

end RealRooted.SeparablePermutations
