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
    StrictInterl p (brandenEulerStep r p) := by
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
    StrictInterl (brandenBasisImage (R := ℝ) n 0) (brandenBasisImage n n) := by
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
  have hlinear : StrictInterl (X + C 1) X := by
    simpa using (StrictInterl.X_add_C_iff (a := 0) (b := 1)).2 (by norm_num)
  have hcommon := hlinear.mul_common_factor hh_rr.1 hh_rr.2
  have hg_factor' : brandenBasisImage (R := ℝ) n n = X * h := by
    simpa [g] using hg_factor
  rw [hf_factor, hg_factor']
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcommon

/-- Consecutive basis images are in proper position in ambient degree at
least two. -/
theorem brandenBasisImage_adjacent_prec
    (n k : ℕ) (hn : 2 ≤ n) (hk : k < n) :
    StrictInterl (brandenBasisImage (R := ℝ) n k) (brandenBasisImage n (k + 1)) := by
  let q := brandenBasisImage (R := ℝ) (n - 1) k
  have hkq : k ≤ n - 1 := by lia
  have hqnext : StrictInterl q (brandenEulerStep 0 q) :=
    brandenEulerStep_prec (r := 0)
      (brandenBasisImage_splits (n - 1) k hkq)
      (brandenBasisImage_degree_pos (n - 1) k hkq).2
      (brandenBasisImage_degree_pos (n - 1) k hkq).1 (by lia)
      (brandenBasisImage_roots_ge_neg_one (n - 1) k hkq)
      (brandenBasisImage_roots_nonpos (n - 1) k)
  have hnext_refl : StrictInterl (brandenEulerStep 0 q) (brandenEulerStep 0 q) :=
    StrictInterl.refl hqnext.2.1.1 hqnext.2.1.2
  have hsum : StrictInterl (q + brandenEulerStep 0 q) (brandenEulerStep 0 q) :=
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

/-- Every earlier in-range Brändén basis image is in proper position
before every later one. The endpoint relation supplies the non-transitive
closure of the adjacent chain. -/
theorem brandenBasisImage_prec
    (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    StrictInterl (brandenBasisImage (R := ℝ) n i) (brandenBasisImage n j) := by
  by_cases heq : i = j
  · subst j
    have hi : i ≤ n := hij.trans hj
    exact StrictInterl.refl (brandenBasisImage_degree_pos n i hi).2.ne_zero
      (brandenBasisImage_splits n i hi)
  by_cases hn : n < 2
  · have hn_cases : n = 0 ∨ n = 1 := by lia
    rcases hn_cases with rfl | rfl
    · exact (heq (by lia)).elim
    · have hi : i = 0 := by lia
      have hj' : j = 1 := by lia
      subst i
      subst j
      exact brandenBasisImage_endpoint_prec 1 (by norm_num)
  · exact prec_chain_of_consecutive_of_endpoint
      (fun k ↦ brandenBasisImage (R := ℝ) n k) 0 n
      (fun k _ hk ↦ brandenBasisImage_adjacent_prec n k (by lia) hk)
      (brandenBasisImage_endpoint_prec n (by lia)) i j (by lia) hij hj

/-- The first basis image precedes every in-range image, without a lower
bound on the ambient degree. -/
theorem brandenBasisImage_zero_prec
    (n k : ℕ) (hk : k ≤ n) :
    StrictInterl (brandenBasisImage (R := ℝ) n 0) (brandenBasisImage n k) :=
  brandenBasisImage_prec n 0 k (by lia) hk

/-- The first basis image is in proper position before every in-range image
in ambient degree at least three. -/
theorem brandenBasisImage_first_prec
    (n k : ℕ) (_hn : 3 ≤ n) (hk : k ≤ n) :
    StrictInterl (brandenBasisImage (R := ℝ) n 0) (brandenBasisImage n k) :=
  brandenBasisImage_zero_prec n k hk

/-- The ordered ambient-degree row of Brändén basis images. -/
def brandenBasisImageRow (n : ℕ) : List ℝ[X] :=
  List.ofFn fun k : Fin (n + 1) ↦ brandenBasisImage n k

/-- Every Brändén basis-image row is an interlacing sequence with
nonnegative coefficients. -/
theorem brandenBasisImageRow_isInterlacingSeqNonneg (n : ℕ) :
    IsInterlacingSeqNonneg (brandenBasisImageRow n) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [brandenBasisImageRow, List.mem_ofFn] at hp
    rcases hp with ⟨k, rfl⟩
    have hk : k.val ≤ n := by lia
    exact ⟨⟨(brandenBasisImage_degree_pos n k hk).2.ne_zero,
      brandenBasisImage_splits n k hk⟩,
      brandenBasisImage_nonneg n k⟩
  · rw [isInterlacingSeq_iff_pairwise, List.pairwise_iff_get]
    intro i j hij
    have hjlt : j.val < n + 1 := by
      simpa [brandenBasisImageRow] using j.isLt
    have hj : j.val ≤ n := by lia
    dsimp only [brandenBasisImageRow] at i j ⊢
    erw [List.get_ofFn, List.get_ofFn]
    exact brandenBasisImage_prec n i j hij.le hj

end RealRooted
