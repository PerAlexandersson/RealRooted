import RealRooted.CommonInterleaver.RootDesc
import RealRooted.DegreeDropDivXPrec
import RealRooted.MaWang.DerivativeStep
import RealRooted.PFPolynomial
import RealRooted.Transforms.BrandenE.BasisImage

/-!
# Proper position for Brändén binomial-basis images

The basis images split over the reals, have all roots in `[-1, 0]`, and form
an adjacent proper-position chain.  The proof combines the Euler differential
step with explicit low-degree seeds and the general consecutive-chain API.
-/

open Polynomial

noncomputable section

namespace RealRooted

private theorem brandenBasisImage_one_zero :
    brandenBasisImage (R := ℝ) 1 0 = X + 1 := by
  rw [brandenBasisImage_succ_zero (R := ℝ) 0, brandenBasisImage_zero]
  simp [brandenEulerStep]

private theorem brandenBasisImage_one_one :
    brandenBasisImage (R := ℝ) 1 1 = X := by
  rw [brandenBasisImage_succ_succ (R := ℝ) 0 0, brandenBasisImage_zero]
  simp [brandenEulerStep]

private theorem brandenBasisImage_two_zero :
    brandenBasisImage (R := ℝ) 2 0 =
      (X + 1) * (C 2 * X + C 1) := by
  rw [brandenBasisImage_succ_zero (R := ℝ) 1,
    brandenBasisImage_one_zero]
  simp [brandenEulerStep]
  norm_num [map_one, map_ofNat]
  ring_nf

private theorem brandenBasisImage_two_one :
    brandenBasisImage (R := ℝ) 2 1 =
      C 2 * X * (X + 1) := by
  rw [brandenBasisImage_succ_succ (R := ℝ) 1 0,
    brandenBasisImage_one_zero]
  simp [brandenEulerStep]
  norm_num [map_one, map_ofNat]
  ring_nf

private theorem brandenBasisImage_two_two :
    brandenBasisImage (R := ℝ) 2 2 =
      X * (C 2 * X + C 1) := by
  rw [brandenBasisImage_succ_succ (R := ℝ) 1 1,
    brandenBasisImage_one_one]
  simp [brandenEulerStep]
  norm_num [map_one, map_ofNat]
  ring_nf

private theorem brandenBasisImage_small_splits
    (n k : ℕ) (hn : n ≤ 2) (hk : k ≤ n) :
    (brandenBasisImage (R := ℝ) n k).Splits := by
  interval_cases n
  · have hk0 : k = 0 := by lia
    subst k
    rw [brandenBasisImage_zero]
    exact Polynomial.Splits.one
  · interval_cases k
    · rw [brandenBasisImage_one_zero]
      simpa using Polynomial.Splits.X_add_C (1 : ℝ)
    · rw [brandenBasisImage_one_one]
      exact Polynomial.Splits.X
  · have hlin : (C 2 * X + C 1 : ℝ[X]).Splits :=
      Polynomial.Splits.of_natDegree_le_one (by compute_degree)
    interval_cases k
    · rw [brandenBasisImage_two_zero]
      exact (Polynomial.Splits.X_add_C (1 : ℝ)).mul hlin
    · rw [brandenBasisImage_two_one]
      exact ((Polynomial.Splits.C (2 : ℝ)).mul Polynomial.Splits.X).mul
        (Polynomial.Splits.X_add_C (1 : ℝ))
    · rw [brandenBasisImage_two_two]
      exact Polynomial.Splits.X.mul hlin

/-- The Euler step places a split polynomial properly before its image when
all roots lie in `[-1, 0]`. -/
theorem brandenEulerStep_prec {r : ℝ} {p : ℝ[X]} {n : ℕ}
    (hp_splits : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : p.natDegree = n)
    (hn : 1 ≤ n)
    (hroot_lo : ∀ x ∈ p.roots, -1 ≤ x)
    (hroot_hi : ∀ x ∈ p.roots, x ≤ 0) :
    Prec p (brandenEulerStep r p) := by
  have hstep := brandenEulerStep_degree_pos (r := r) hp_pos hdeg
  apply prec_mw_derivative_of_nonpos_of_pos_natDegree
      (u := X + C r) (v := X * (1 + X)) hp_splits
  · simpa [hdeg] using hn
  · change p.natDegree ≤ (brandenEulerStep r p).natDegree
    rw [hdeg, hstep.1]
    lia
  · change (brandenEulerStep r p).natDegree ≤ p.natDegree + 1
    rw [hdeg, hstep.1]
  · change HasPosLeadingCoeff (brandenEulerStep r p)
    exact hstep.2
  · exact hp_pos
  · intro x hx
    exact eval_X_mul_one_add_X_nonpos_of_mem_Icc
      (hroot_lo x ((mem_roots hp_pos.ne_zero).mpr hx))
      (hroot_hi x ((mem_roots hp_pos.ne_zero).mpr hx))

/-- Every in-range Brändén binomial-basis image splits over the reals. -/
theorem brandenBasisImage_splits :
    ∀ n k : ℕ, k ≤ n → (brandenBasisImage (R := ℝ) n k).Splits := by
  intro n
  induction n with
  | zero =>
      intro k hk
      exact brandenBasisImage_small_splits 0 k (by norm_num) hk
  | succ n ih =>
      intro k hk
      by_cases hn : n < 2
      · exact brandenBasisImage_small_splits (n + 1) k (by lia) hk
      · have hn2 : 2 ≤ n := by lia
        cases k with
        | zero =>
            rw [brandenBasisImage_succ_zero]
            exact (brandenEulerStep_prec (r := 1) (ih 0 (by lia))
              (brandenBasisImage_degree_pos n 0 (by lia)).2
              (brandenBasisImage_degree_pos n 0 (by lia)).1 (by lia)
              (brandenBasisImage_roots_ge_neg_one n 0 (by lia))
              (brandenBasisImage_roots_nonpos n 0)).2.1.2
        | succ k =>
            have hkn : k ≤ n := by lia
            rw [brandenBasisImage_succ_succ]
            exact (brandenEulerStep_prec (r := 0) (ih k hkn)
              (brandenBasisImage_degree_pos n k hkn).2
              (brandenBasisImage_degree_pos n k hkn).1 (by lia)
              (brandenBasisImage_roots_ge_neg_one n k hkn)
              (brandenBasisImage_roots_nonpos n k)).2.1.2

/-- Every in-range basis image is a Pólya-frequency polynomial. -/
theorem brandenBasisImage_isPFPolynomial (n k : ℕ) (hk : k ≤ n) :
    IsPFPolynomial (brandenBasisImage (R := ℝ) n k) :=
  IsPFPolynomial.of_realRooted_nonneg
    (brandenBasisImage_nonneg n k) (brandenBasisImage_splits n k hk)

/-- Every ordered Bell polynomial splits over the reals. -/
theorem orderedBellPolynomial_splits (n : ℕ) :
    (orderedBellPolynomial (R := ℝ) n).Splits := by
  rw [← brandenBasisImage_self]
  exact brandenBasisImage_splits n n le_rfl

/-- Every ordered Bell polynomial is a Pólya-frequency polynomial. -/
theorem orderedBellPolynomial_isPFPolynomial (n : ℕ) :
    IsPFPolynomial (orderedBellPolynomial (R := ℝ) n) := by
  rw [← brandenBasisImage_self]
  exact brandenBasisImage_isPFPolynomial n n le_rfl

/-- The two endpoint images differ by exchanging the factors `X` and
`X + 1`. -/
theorem brandenBasisImage_endpoint_identity :
    ∀ n : ℕ, 1 ≤ n →
      X * brandenBasisImage (R := ℝ) n 0 =
        (X + 1) * brandenBasisImage n n := by
  intro n hn
  induction n with
  | zero => lia
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        rw [brandenBasisImage_succ_zero, brandenBasisImage_succ_succ,
          brandenBasisImage_zero]
        simp [brandenEulerStep]
        ring
      · have ihn := ih (by lia)
        rw [brandenBasisImage_succ_zero, brandenBasisImage_succ_succ]
        have hder := congrArg Polynomial.derivative ihn
        simp only [Polynomial.derivative_mul, Polynomial.derivative_X,
          Polynomial.derivative_add, Polynomial.derivative_one] at hder
        norm_num at hder
        simp only [brandenEulerStep]
        norm_num [map_one]
        linear_combination X * (X + 1) * hder

theorem brandenBasisImage_endpoint_prec (n : ℕ) (hn : 1 ≤ n) :
    Prec (brandenBasisImage (R := ℝ) n 0) (brandenBasisImage n n) := by
  let g := brandenBasisImage (R := ℝ) n n
  let h := g.divX
  have hg0 : g.coeff 0 = 0 := by
    dsimp [g]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [show 1 + m = m + 1 by lia]
    rw [brandenBasisImage_succ_succ, brandenEulerStep]
    simp [coeff_add, coeff_mul]
  have hg_ne : g ≠ 0 := (brandenBasisImage_degree_pos n n (by lia)).2.ne_zero
  have hg_split : g.Splits := brandenBasisImage_splits n n (by lia)
  have hh_rr : h ≠ 0 ∧ h.Splits :=
    divX_realRooted_of_coeff_zero hg_ne hg0 hg_split
  have hg_factor : g = X * h :=
    DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hg0
  have hf_factor : brandenBasisImage (R := ℝ) n 0 = (X + 1) * h := by
    have hid := brandenBasisImage_endpoint_identity n hn
    have hg_factor' : brandenBasisImage (R := ℝ) n n = X * h := by
      simpa [g] using hg_factor
    rw [hg_factor'] at hid
    apply mul_left_cancel₀ (show (X : ℝ[X]) ≠ 0 by simp)
    calc
      X * brandenBasisImage (R := ℝ) n 0 = (X + 1) * (X * h) := hid
      _ = X * ((X + 1) * h) := by ring
  have hlinear : Prec (X + C 1) X := by
    simpa using (prec_X_add_C_iff (a := 0) (b := 1)).2 (by norm_num)
  have hcommon := prec_mul_common_factor hh_rr.1 hh_rr.2 hlinear
  have hg_factor' : brandenBasisImage (R := ℝ) n n = X * h := by
    simpa [g] using hg_factor
  rw [hf_factor, hg_factor']
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcommon

/-- Consecutive basis images are in proper position in ambient degree at
least three. -/
theorem brandenBasisImage_adjacent_prec
    (n k : ℕ) (hn : 3 ≤ n) (hk : k < n) :
    Prec (brandenBasisImage (R := ℝ) n k) (brandenBasisImage n (k + 1)) := by
  let q := brandenBasisImage (R := ℝ) (n - 1) k
  have hkq : k ≤ n - 1 := by lia
  have hqnext : Prec q (brandenEulerStep 0 q) :=
    brandenEulerStep_prec (r := 0)
      (brandenBasisImage_splits (n - 1) k hkq)
      (brandenBasisImage_degree_pos (n - 1) k hkq).2
      (brandenBasisImage_degree_pos (n - 1) k hkq).1 (by lia)
      (brandenBasisImage_roots_ge_neg_one (n - 1) k hkq)
      (brandenBasisImage_roots_nonpos (n - 1) k)
  have hnext_refl : Prec (brandenEulerStep 0 q) (brandenEulerStep 0 q) :=
    prec_refl hqnext.2.1.1 hqnext.2.1.2
  have hsum : Prec (q + brandenEulerStep 0 q) (brandenEulerStep 0 q) :=
    prec_add_of_prec_right_of_posLeadingCoeff hqnext hnext_refl
      (brandenBasisImage_degree_pos (n - 1) k hkq).2
      (brandenEulerStep_degree_pos (r := 0)
        (brandenBasisImage_degree_pos (n - 1) k hkq).2
        (brandenBasisImage_degree_pos (n - 1) k hkq).1).2
  have hleft : brandenBasisImage (R := ℝ) n k = q + brandenEulerStep 0 q := by
    rw [show n = (n - 1) + 1 by lia,
      brandenBasisImage_succ_same (n - 1) k hkq]
    dsimp [q]
    rw [brandenEulerStep, brandenEulerStep]
    norm_num [map_one]
    ring
  have hright :
      brandenBasisImage (R := ℝ) n (k + 1) = brandenEulerStep 0 q := by
    rw [show n = (n - 1) + 1 by lia, brandenBasisImage_succ_succ]
  rwa [hleft, hright]

/-- The first basis image is in proper position before every in-range image
in ambient degree at least three. -/
theorem brandenBasisImage_first_prec
    (n k : ℕ) (hn : 3 ≤ n) (hk : k ≤ n) :
    Prec (brandenBasisImage (R := ℝ) n 0) (brandenBasisImage n k) :=
  prec_chain_of_consecutive_of_endpoint
    (fun i => brandenBasisImage (R := ℝ) n i) 0 n
    (fun i _ hi => brandenBasisImage_adjacent_prec n i hn hi)
    (brandenBasisImage_endpoint_prec n (by lia)) 0 k (by lia) (by lia) hk

end RealRooted
