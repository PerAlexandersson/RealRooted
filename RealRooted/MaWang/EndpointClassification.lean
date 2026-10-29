module

public import RealRooted.MaWang.EndpointMultiplicity

/-!
# Classification of affine endpoint sequences

We prove the converse to the affine endpoint-confinement theorem: if every row of an affine
Ma--Wang sequence has all its roots in `[-c, 0)`, then the slope is the reciprocal of a positive
integer and the intercept is an integer multiple of that slope. Combining this with
`affineEndpointSequence` gives the full classification from issue #2087.

The first-hit argument follows Ma and Wang, *q-Eulerian polynomials and polynomials with only
real zeros*, Theorem 2 and Corollary 3
([arXiv:math/0611826](https://arxiv.org/abs/math/0611826)).
-/

public section

open Polynomial

noncomputable section

namespace RealRooted.MaWang

private lemma exists_affine_hit {lambda mu : ℝ} {m : ℕ → ℕ}
    (hlambda : 0 < lambda) (hmzero : m 0 = 0)
    (hstep : ∀ n : ℕ, m (n + 1) =
      if lambda * (n : ℝ) - mu = m n then m n + 1 else m n)
    (hbound : ∀ n : ℕ, lambda * (n : ℝ) - mu ≤ m n) (k : ℕ) :
    ∃ n, m n = k ∧ lambda * (n : ℝ) - mu = k := by
  obtain ⟨N, hN⟩ := exists_nat_gt (((k : ℝ) + mu) / lambda)
  have hkN : (k : ℝ) < lambda * (N : ℝ) - mu := by
    rw [div_lt_iff₀ hlambda] at hN
    nlinarith
  have hmN : k < m N := by
    exact_mod_cast hkN.trans_le (hbound N)
  clear hN hkN
  induction N with
  | zero =>
      rw [hmzero] at hmN
      lia
  | succ N ih =>
      rw [hstep N] at hmN
      by_cases heq : lambda * (N : ℝ) - mu = m N
      · rw [ite_eq_left heq] at hmN
        by_cases hmk : m N = k
        · exact ⟨N, hmk, hmk ▸ heq⟩
        · apply ih
          lia
      · rw [ite_eq_right heq] at hmN
        exact ih hmN

/-- If every row of an affine Ma--Wang sequence stays in `[-c, 0)`, then its slope is the
reciprocal of a positive integer and its intercept is an integer multiple of that slope.
This is the necessity direction of the affine classification in issue #2087. -/
theorem affineEndpointParameters_of_roots_mem_Ico
    {P : ℕ → ℝ[X]} {c a lambda mu : ℝ} {rho : ℕ → ℝ}
    (hc : 0 < c) (hlambda : 0 < lambda) (hmu : 0 ≤ mu) (ha : mu < a)
    (hrec : ∀ n, P (n + 1) = C (rho n) *
      endpointStep c a (c * (a + lambda * (n : ℝ) - mu)) (P n))
    (hrho : ∀ n, 0 < rho n)
    (h0pos : HasPosLeadingCoeff (P 0)) (h0s : (P 0).Splits)
    (h0roots : ∀ z ∈ (P 0).roots, -c < z ∧ z < 0)
    (hall : ∀ n z, z ∈ (P n).roots → -c ≤ z ∧ z < 0) :
    ∃ L r : ℕ, 0 < L ∧ lambda = 1 / (L : ℝ) ∧ mu = (r : ℝ) / L := by
  have ha0 : 0 < a := hmu.trans_lt ha
  have hb : ∀ n : ℕ, 0 < c * (a + lambda * (n : ℝ) - mu) := by
    intro n
    apply mul_pos hc
    have hn : 0 ≤ lambda * (n : ℝ) := mul_nonneg hlambda.le (by positivity)
    linarith
  have h0roots' : ∀ z ∈ (P 0).roots, -c ≤ z ∧ z < 0 := by
    intro z hz
    exact ⟨(h0roots z hz).1.le, (h0roots z hz).2⟩
  have hthreshold := (endpointSequence_roots_mem_Ico_iff
    (P := P) (c := c) (a := fun _ => a)
    (b := fun n => c * (a + lambda * (n : ℝ) - mu)) (ρ := rho)
    hrec (fun _ => ha0) hb hrho h0pos h0s h0roots').mp hall
  let m : ℕ → ℕ := fun n => (P n).rootMultiplicity (-c)
  have hmzero : m 0 = 0 := by
    dsimp [m]
    apply rootMultiplicity_eq_zero
    intro hroot
    have hz : -c ∈ (P 0).roots := (mem_roots h0pos.ne_zero).2 hroot
    exact (lt_irrefl (-c)) (h0roots (-c) hz).1
  have hbound : ∀ n : ℕ, lambda * (n : ℝ) - mu ≤ m n := by
    intro n
    have hn := hthreshold n
    dsimp [m]
    nlinarith
  have hstep : ∀ n : ℕ, m (n + 1) =
      if lambda * (n : ℝ) - mu = m n then m n + 1 else m n := by
    intro n
    have hn := endpointSequence_rootMultiplicity
      (P := P) (c := c) (a := fun _ => a)
      (b := fun j => c * (a + lambda * (j : ℝ) - mu)) (ρ := rho)
      hrec (fun _ => ha0) hb hrho h0pos h0s h0roots' hthreshold n
    have heq :
        c * (a + lambda * (n : ℝ) - mu) =
            c * (a + (P n).rootMultiplicity (-c)) ↔
          lambda * (n : ℝ) - mu = (P n).rootMultiplicity (-c) := by
      constructor <;> intro h <;> nlinarith
    dsimp [m]
    simpa only [heq] using hn
  obtain ⟨r, -, hr⟩ :=
    exists_affine_hit hlambda hmzero hstep hbound 0
  obtain ⟨s, -, hs⟩ :=
    exists_affine_hit hlambda hmzero hstep hbound 1
  norm_num at hr hs
  have hrsReal : (r : ℝ) < s := by
    apply lt_of_mul_lt_mul_left (a := lambda) (by linarith [hr, hs]) hlambda.le
  have hrs : r < s := by
    exact_mod_cast hrsReal
  let L := s - r
  have hL : 0 < L := Nat.sub_pos_of_lt hrs
  have hLcast : (L : ℝ) = (s : ℝ) - r := by
    dsimp [L]
    exact Nat.cast_sub hrs.le
  have hprod : lambda * (L : ℝ) = 1 := by
    rw [hLcast]
    calc
      lambda * ((s : ℝ) - r) =
          (lambda * (s : ℝ) - mu) - (lambda * (r : ℝ) - mu) := by ring
      _ = 1 := by rw [hs, hr]; norm_num
  have hlambdaL : lambda = 1 / (L : ℝ) := by
    exact (eq_div_iff (by positivity : (L : ℝ) ≠ 0)).2 hprod
  refine ⟨L, r, hL, hlambdaL, ?_⟩
  calc
    mu = lambda * (r : ℝ) := (sub_eq_zero.mp hr).symm
    _ = (r : ℝ) / L := by rw [hlambdaL, one_div, inv_mul_eq_div]

/-- An affine Ma--Wang sequence stays in `[-c, 0)` at every index exactly when its slope is the
reciprocal of a positive integer and its intercept is an integer multiple of that slope.
This is the full affine classification from issue #2087. -/
theorem affineEndpointSequence_roots_mem_Ico_iff
    {P : ℕ → ℝ[X]} {c a lambda mu : ℝ} {rho : ℕ → ℝ}
    (hc : 0 < c) (hlambda : 0 < lambda) (hmu : 0 ≤ mu) (ha : mu < a)
    (hrec : ∀ n, P (n + 1) = C (rho n) *
      endpointStep c a (c * (a + lambda * (n : ℝ) - mu)) (P n))
    (hrho : ∀ n, 0 < rho n)
    (h0pos : HasPosLeadingCoeff (P 0)) (h0s : (P 0).Splits)
    (h0roots : ∀ z ∈ (P 0).roots, -c < z ∧ z < 0) :
    (∀ n z, z ∈ (P n).roots → -c ≤ z ∧ z < 0) ↔
      ∃ L r : ℕ, 0 < L ∧ lambda = 1 / (L : ℝ) ∧ mu = (r : ℝ) / L := by
  constructor
  · exact affineEndpointParameters_of_roots_mem_Ico
      hc hlambda hmu ha hrec hrho h0pos h0s h0roots
  · rintro ⟨L, r, hL, hlambdaL, hmuR⟩
    have hrec' : ∀ n, P (n + 1) = C (rho n) *
        endpointStep c a (c * (a + (n : ℝ) / L - (r : ℝ) / L)) (P n) := by
      intro n
      simpa [hlambdaL, hmuR, div_eq_mul_inv, mul_comm] using hrec n
    have haR : (r : ℝ) / L < a := by
      rw [← hmuR]
      exact ha
    have hseq := affineEndpointSequence L r hc hL haR
      hrec' hrho h0pos h0s h0roots
    intro n z hz
    exact (hseq n).2.2.1 z hz

/-- The half-slope, half-intercept instance of the affine classification in issue #2087.
Its endpoint multiplicity is `(n - 1) ⌈/⌉ 2`, and adjacent rows strictly interlace. -/
theorem halfSlopeEndpointSequence
    {P : ℕ → ℝ[X]} {c a : ℝ} {rho : ℕ → ℝ}
    (hc : 0 < c) (ha : (1 : ℝ) / 2 < a)
    (hrec : ∀ n, P (n + 1) = C (rho n) *
      endpointStep c a (c * (a + (n : ℝ) / 2 - (1 : ℝ) / 2)) (P n))
    (hrho : ∀ n, 0 < rho n)
    (h0pos : HasPosLeadingCoeff (P 0)) (h0s : (P 0).Splits)
    (h0roots : ∀ z ∈ (P 0).roots, -c < z ∧ z < 0) :
    ∀ n, HasPosLeadingCoeff (P n) ∧ (P n).Splits ∧
      (∀ z ∈ (P n).roots, -c ≤ z ∧ z < 0) ∧
      (P n).rootMultiplicity (-c) = affineEndpointMultiplicity 2 1 n ∧
      StrictInterl (P n) (P (n + 1)) := by
  have ha' : ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) < a := by
    norm_num at ha ⊢
    exact ha
  have hrec' : ∀ n, P (n + 1) = C (rho n) * endpointStep c a
      (c * (a + (n : ℝ) / ((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)))
        (P n) := by
    intro n
    convert hrec n using 1; norm_num
  exact affineEndpointSequence (P := P) (c := c) (a := a) (rho := rho)
    2 1 hc (by norm_num) ha'
    hrec' hrho h0pos h0s h0roots

end RealRooted.MaWang
