module

public import RealRooted.Applications.EulerianCompendium.EvenTop
public import RealRooted.AffineDerivative
public import RealRooted.MaWang.StrictStep
public import RealRooted.SimpleRoots

/-!
# Negative roots and strict interlacing for even-top descents

This proves `thm:evenTopInterlacing` for the actual permutation enumerator,
using its insertion recurrences.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.EulerianCompendium

private def evenTopGood (n : ℕ) : Prop :=
  (evenTopDescentPolynomial n).Splits ∧
    RealRooted.HasSimpleRoots (evenTopDescentPolynomial n) ∧
    ∀ r ∈ (evenTopDescentPolynomial n).roots, r < 0

private theorem evenTop_roots_negative (n : ℕ) :
    ∀ r ∈ (evenTopDescentPolynomial n).roots, r < 0 := by
  intro r hr
  have hnonpos := RealRooted.roots_nonpos_of_hasNonnegCoeffs
    (evenTopDescentPolynomial_nonneg_coeffs n) r hr
  have hroot : (evenTopDescentPolynomial n).IsRoot r :=
    (Polynomial.mem_roots (evenTopDescentPolynomial_ne_zero n)).mp hr
  have hne : r ≠ 0 := by
    intro heq
    subst r
    have hzero : (evenTopDescentPolynomial n).eval 0 = 0 := by
      simpa [Polynomial.IsRoot.def] using hroot
    linarith [evenTopDescentPolynomial_eval_zero_pos n]
  exact lt_of_le_of_ne hnonpos hne

private theorem evenTopGood_two : evenTopGood 2 := by
  unfold evenTopGood
  rw [evenTopDescentPolynomial_two]
  refine ⟨?_, ?_, ?_⟩
  · simpa [add_comm] using (Polynomial.Splits.X_add_C (1 : ℝ))
  · apply RealRooted.hasSimpleRoots_of_natDegree_le_one
    · simpa [add_comm] using (Polynomial.X_add_C_ne_zero (1 : ℝ))
    · simp
  · simpa [evenTopDescentPolynomial_two] using evenTop_roots_negative 2

private theorem evenTop_degree_lt_index (n : ℕ) (hn : 1 ≤ n) :
    (evenTopDescentPolynomial n).natDegree < n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : n ≠ 0)
  simpa using evenTopDescentPolynomial_natDegree_lt k

private theorem evenTop_alt_of_strict {p q : ℝ[X]}
    (hstrict : RealRooted.StrictInterl p q)
    (hno : ∀ r : ℝ, ¬ (p.IsRoot r ∧ q.IsRoot r)) :
    StrictlyAlternatingRoots p q := by
  obtain ⟨hp, hq⟩ := hstrict.hasSimpleRoots_of_no_common_root hno
  refine ⟨Or.inl hstrict, hp, hq, ?_⟩
  intro r hr hqr
  exact hno r ⟨(Polynomial.mem_roots hp.ne_zero).mp hr,
    (Polynomial.mem_roots hq.ne_zero).mp hqr⟩

private theorem evenTop_odd_successor (n : ℕ) (hn : 2 ≤ n)
    (hgood : evenTopGood n) (hdegree : 1 ≤ (evenTopDescentPolynomial n).natDegree)
    (heven : n % 2 = 0) :
    evenTopGood (n + 1) ∧
      StrictlyAlternatingRoots (evenTopDescentPolynomial n)
        (evenTopDescentPolynomial (n + 1)) ∧
      (evenTopDescentPolynomial (n + 1)).natDegree =
        (evenTopDescentPolynomial n).natDegree := by
  let f := evenTopDescentPolynomial n
  let g := evenTopDescentPolynomial (n + 1)
  have hrec := evenTop_odd_rank_recurrence n (by
    simp [Nat.add_mod, heven])
  have hrec' : g = C ((n + 1 : ℕ) : ℝ) * f + (1 - X) * f.derivative := by
    dsimp [f, g]
    simpa [add_comm] using hrec
  have hupper : f.natDegree < n := by
    exact evenTop_degree_lt_index n (by lia)
  have hc : ((n + 1 : ℕ) : ℝ) ≠ (f.natDegree : ℝ) := by
    exact ne_of_gt (by exact_mod_cast (lt_trans hupper (by lia : n < n + 1)))
  have hstrict : RealRooted.StrictInterl g f := by
    rw [hrec']
    apply RealRooted.strictInterl_affine_derivative'
    · exact hgood.1
    · exact hdegree
    · exact evenTopDescentPolynomial_pos_leadingCoeff n
    · intro r hr
      exact le_of_lt (evenTop_roots_negative n r
        (by simpa [f] using hr))
    · exact_mod_cast (lt_trans hupper (by lia : n < n + 1))
  have hno : ∀ r : ℝ, ¬ (g.IsRoot r ∧ f.IsRoot r) := by
    intro r ⟨hgr, hfr⟩
    have heval := RealRooted.eval_affineDeriv_at_root hfr ((n + 1 : ℕ) : ℝ)
    rw [← hrec'] at heval
    have hrneg : r < 0 := evenTop_roots_negative n r
      ((Polynomial.mem_roots (evenTopDescentPolynomial_ne_zero n)).mpr hfr)
    have hder_ne := hgood.2.1.eval_derivative_ne_zero hfr
    have hzero : g.eval r = 0 := hgr
    rw [hzero] at heval
    have : (1 - r) * f.derivative.eval r = 0 := heval.symm
    rcases mul_eq_zero.mp this with hfac | hder
    · have : 1 - r ≠ 0 := by linarith
      exact this hfac
    · exact hder_ne hder
  have hpair : StrictlyAlternatingRoots g f := evenTop_alt_of_strict hstrict hno
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨hstrict.1.2, hpair.2.1, evenTop_roots_negative (n + 1)⟩
  · refine ⟨Or.inr hstrict, hpair.2.2.1, hpair.2.1, ?_⟩
    intro r hr hgr
    exact hno r ⟨
      (Polynomial.mem_roots (evenTopDescentPolynomial_ne_zero (n + 1))).mp hgr,
      (Polynomial.mem_roots (evenTopDescentPolynomial_ne_zero n)).mp hr⟩
  · change g.natDegree = f.natDegree
    rw [hrec']
    exact RealRooted.natDegree_affineDeriv (evenTopDescentPolynomial_ne_zero n)
      hdegree hc

private theorem evenTop_even_successor (n : ℕ) (_hn : 2 ≤ n)
    (hgood : evenTopGood n) (hdegree : 1 ≤ (evenTopDescentPolynomial n).natDegree)
    (hodd : n % 2 = 1) :
    evenTopGood (n + 1) ∧
      StrictlyAlternatingRoots (evenTopDescentPolynomial n)
        (evenTopDescentPolynomial (n + 1)) ∧
      (evenTopDescentPolynomial (n + 1)).natDegree =
        (evenTopDescentPolynomial n).natDegree + 1 := by
  let f := evenTopDescentPolynomial n
  let g := evenTopDescentPolynomial (n + 1)
  have hrec := evenTop_even_rank_recurrence n (by
    simp [Nat.add_mod, hodd])
  have hrec' : g = (1 + C (n : ℝ) * X) * f +
      (X * (1 - X)) * f.derivative := by
    dsimp [f, g]
    simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hrec
  -- The recurrence raises the degree by one: its coefficient at degree d+1
  -- is (n-d) times the positive leading coefficient of f.
  have hdegree' : g.natDegree = f.natDegree + 1 := by
    let d := f.natDegree
    have hlt : d < n := by
      exact evenTop_degree_lt_index n (by lia)
    have hdpos : 1 ≤ d := hdegree
    have hdsucc : d - 1 + 1 = d := Nat.sub_add_cancel hdpos
    have hcoeff_above : f.coeff (d + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by dsimp [d]; lia)
    have hder_coeff_d : f.derivative.coeff d = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [natDegree_derivative]; lia)
    have hder_coeff_prev : f.derivative.coeff (d - 1) =
        (d : ℝ) * f.leadingCoeff := by
      rw [coeff_derivative, hdsucc]
      rw [show ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) by
        rw [Nat.cast_sub (by lia : 1 ≤ d)]
        ring]
      rw [show f.coeff d = f.leadingCoeff by rfl]
      ring
    have hfactor_coeff : ((1 - X) * f.derivative).coeff d =
        -(d : ℝ) * f.leadingCoeff := by
      rw [show (1 - X : ℝ[X]) * f.derivative =
        f.derivative - X * f.derivative by ring, coeff_sub, hder_coeff_d]
      have hx : (X * f.derivative).coeff d = f.derivative.coeff (d - 1) := by
        rw [show d = d - 1 + 1 by lia, coeff_X_mul]
        rw [show d - 1 + 1 - 1 = d - 1 by lia]
      rw [hx, hder_coeff_prev]
      ring
    have hfirst_coeff : (X * ((1 - X) * f.derivative)).coeff (d + 1) =
        -(d : ℝ) * f.leadingCoeff := by
      have hx : (X * ((1 - X) * f.derivative)).coeff (d + 1) =
          ((1 - X) * f.derivative).coeff d := by
        rw [show d + 1 = Nat.succ d by lia, coeff_X_mul]
      rw [hx, hfactor_coeff]
    have hsecond_coeff : ((1 + C (n : ℝ) * X) * f).coeff (d + 1) =
        (n : ℝ) * f.leadingCoeff := by
      rw [show (1 + C (n : ℝ) * X) * f = f + C (n : ℝ) * (X * f) by ring,
        coeff_add, hcoeff_above, zero_add, coeff_C_mul]
      have hx : (X * f).coeff (d + 1) = f.coeff d := by
        rw [show d + 1 = Nat.succ d by lia, coeff_X_mul]
      rw [hx]
      rw [show f.coeff d = f.leadingCoeff by rfl]
    have hrec'' : g = X * ((1 - X) * f.derivative) +
        (1 + C (n : ℝ) * X) * f := by
      rw [hrec']
      ring
    have hcoeff : g.coeff (d + 1) = ((n : ℝ) - d) * f.leadingCoeff := by
      rw [hrec'', coeff_add, hfirst_coeff, hsecond_coeff]
      ring
    have hcoeffne : g.coeff (d + 1) ≠ 0 := by
      rw [hcoeff]
      exact mul_ne_zero
        (sub_ne_zero.mpr (by exact_mod_cast (Ne.symm (Nat.ne_of_lt hlt))))
        (leadingCoeff_ne_zero.mpr (evenTopDescentPolynomial_ne_zero n))
    have hu_degree : (1 + C (n : ℝ) * X).natDegree ≤ 1 := by
      calc
        (1 + C (n : ℝ) * X).natDegree ≤
            max (1 : ℝ[X]).natDegree (C (n : ℝ) * X).natDegree :=
          natDegree_add_le _ _
        _ ≤ max 0 1 := max_le (by norm_num) (by
          exact (natDegree_C_mul_le (n : ℝ) X).trans (by norm_num))
        _ = 1 := by norm_num
    have hsub_degree : (1 - X : ℝ[X]).natDegree ≤ 1 := by
      calc
        (1 - X : ℝ[X]).natDegree ≤
            max (1 : ℝ[X]).natDegree X.natDegree := natDegree_sub_le _ _
        _ ≤ 1 := by simp
    have hv_degree : (X * (1 - X : ℝ[X])).natDegree ≤ 2 := by
      calc
        (X * (1 - X : ℝ[X])).natDegree ≤
            X.natDegree + (1 - X : ℝ[X]).natDegree :=
          natDegree_mul_le
        _ ≤ 1 + 1 := Nat.add_le_add (by simp) hsub_degree
        _ = 2 := by norm_num
    have hder_degree : f.derivative.natDegree ≤ d - 1 := by
      rw [natDegree_derivative]
    have hle : g.natDegree ≤ d + 1 := by
      rw [hrec']
      calc
        ((1 + C (n : ℝ) * X) * f +
          X * (1 - X : ℝ[X]) * f.derivative).natDegree
            ≤ max ((1 + C (n : ℝ) * X) * f).natDegree
                (X * (1 - X : ℝ[X]) * f.derivative).natDegree := natDegree_add_le _ _
        _ ≤ d + 1 := by
          apply max_le
          · calc
              ((1 + C (n : ℝ) * X) * f).natDegree
                  ≤ (1 + C (n : ℝ) * X).natDegree + f.natDegree :=
                natDegree_mul_le
              _ ≤ 1 + d := Nat.add_le_add hu_degree le_rfl
              _ = d + 1 := by lia
          · calc
              (X * (1 - X : ℝ[X]) * f.derivative).natDegree
                  ≤ (X * (1 - X : ℝ[X])).natDegree + f.derivative.natDegree :=
                natDegree_mul_le
              _ ≤ 2 + (d - 1) := Nat.add_le_add hv_degree hder_degree
              _ ≤ d + 1 := by lia
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle hcoeffne
  have hu : RealRooted.HasPosLeadingCoeff g := evenTopDescentPolynomial_pos_leadingCoeff (n + 1)
  have hvneg : ∀ r : ℝ, f.IsRoot r →
      (X * (1 - X : ℝ[X])).eval r < 0 := by
    intro r hr
    have hrneg := evenTop_roots_negative n r
      ((Polynomial.mem_roots (evenTopDescentPolynomial_ne_zero n)).mpr hr)
    simp only [eval_mul, eval_X, eval_sub, eval_one]
    have hpos : 0 < 1 - r := by linarith
    exact mul_neg_of_neg_of_pos hrneg hpos
  have hstrict_pair := RealRooted.strictInterl_and_hasSimpleRoots_of_interlaces_eval_mul_neg_succ
    hgood.1 (evenTopDescentPolynomial_pos_leadingCoeff n) hu hdegree hdegree'
      hgood.2.1 hrec' hvneg
  have hstrict := hstrict_pair.1
  have hno : ∀ r : ℝ, ¬ (f.IsRoot r ∧ g.IsRoot r) := by
    intro r ⟨hfr, hgr⟩
    have hqsign : ∀ r : ℝ, f.IsRoot r →
        0 < f.derivative.eval r * f.derivative.eval r := by
      intro r hr
      have hne := hgood.2.1.eval_derivative_ne_zero hr
      nlinarith [sq_pos_iff.mpr hne]
    have hno' := RealRooted.noCommonRoot_of_auxiliary_sign hrec' hqsign hvneg
    exact hno' r hfr hgr
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨hstrict.2.1.2, hstrict_pair.2, evenTop_roots_negative (n + 1)⟩
  · exact evenTop_alt_of_strict hstrict (by
      intro r ⟨hfr, hgr⟩
      exact hno r ⟨hfr, hgr⟩)
  · simpa [f, g] using hdegree'

private theorem evenTop_good_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    evenTopGood n ∧ 1 ≤ (evenTopDescentPolynomial n).natDegree := by
  induction n with
  | zero => lia
  | succ n ih =>
    by_cases hn2 : n = 1
    · subst n
      exact ⟨evenTopGood_two, by simp [evenTopDescentPolynomial_two]⟩
    · have hn' : 2 ≤ n := by lia
      obtain ⟨hgood, hdegree⟩ := ih hn'
      by_cases heven : n % 2 = 0
      · obtain ⟨hgood', _, hdegree'⟩ := evenTop_odd_successor n hn' hgood hdegree heven
        exact ⟨hgood', by lia⟩
      · have hodd : n % 2 = 1 := by
          have hneven : n % 2 ≠ 0 := heven
          rcases Nat.mod_two_eq_zero_or_one n with hzero | hone
          · exact (hneven hzero).elim
          · exact hone
        obtain ⟨hgood', _, hdegree'⟩ := evenTop_even_successor n hn' hgood hdegree hodd
        exact ⟨hgood', by lia⟩

/-- The actual even-top descent polynomial has simple negative roots. -/
theorem evenTopDescentPolynomial_hasSimpleNegativeRoots {n : ℕ} (hn : 2 ≤ n) :
    RealRooted.HasSimpleRoots (evenTopDescentPolynomial n) ∧
      ∀ r ∈ (evenTopDescentPolynomial n).roots, r < 0 := by
  obtain ⟨hgood, _⟩ := evenTop_good_of_two_le n hn
  exact ⟨hgood.2.1, hgood.2.2⟩

/-- The actual even-top descent polynomial is real-rooted. -/
theorem evenTopDescentPolynomial_splits {n : ℕ} (hn : 2 ≤ n) :
    (evenTopDescentPolynomial n).Splits :=
  (evenTop_good_of_two_le n hn).1.1

/-- Consecutive actual even-top descent polynomials strictly interlace. -/
theorem evenTopDescentPolynomial_strictlyAlternates {n : ℕ} (hn : 2 ≤ n) :
    StrictlyAlternatingRoots (evenTopDescentPolynomial n)
      (evenTopDescentPolynomial (n + 1)) := by
  obtain ⟨hgood, hdegree⟩ := evenTop_good_of_two_le n hn
  by_cases heven : n % 2 = 0
  · exact (evenTop_odd_successor n hn hgood hdegree heven).2.1
  · have hodd : n % 2 = 1 := by lia
    exact (evenTop_even_successor n hn hgood hdegree hodd).2.1

end RealRooted.EulerianCompendium
