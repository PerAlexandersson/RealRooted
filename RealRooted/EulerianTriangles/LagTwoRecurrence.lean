module

public import RealRooted.EulerianTriangles.LagTwoOperators
import RealRooted.Interlacing.OuterDifference
import RealRooted.Linear
import RealRooted.MaWang.CriticalSign
import RealRooted.MaWang.Weak.DerivativeSign
import RealRooted.PosCombo

/-!
# The general positive lag-two Euler recurrence

We prove simple negative roots and simultaneous adjacent and auxiliary
interlacing for the recurrence governed by `lagTwoEulerStep` and
`lagTwoEulerCore`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The simultaneous induction package for two consecutive rows. -/
structure LagTwoEulerPairCertificate (P : ℕ → ℝ[X]) (n : ℕ) : Prop where
  current : SimpleNegRooted (P n) n
  next : SimpleNegRooted (P (n + 1)) (n + 1)
  adjacent : StrictInterl (P n) (P (n + 1))
  auxiliary : StrictInterl (lagTwoEulerCore n (P n)) (P (n + 1))

private theorem simpleNegRooted_linear {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    SimpleNegRooted (C u + C v * X) 1 := by
  have hdegree : (C u + C v * X : ℝ[X]).natDegree = 1 := by
    compute_degree!
    exact hv.ne'
  have hne : (C u + C v * X : ℝ[X]) ≠ 0 := by
    intro hzero
    have := congrArg (fun p : ℝ[X] ↦ p.coeff 0) hzero
    simp_all
  have hnonneg : HasNonnegCoeffs (C u + C v * X : ℝ[X]) := by
    exact (hasNonnegCoeffs_C hu.le).add
      (hasNonnegCoeffs_C_mul hv.le hasNonnegCoeffs_X)
  exact ⟨hdegree, by
      rw [HasPosLeadingCoeff, leadingCoeff, hdegree]
      simpa using hv,
    hnonneg, by simpa using hu,
    Splits.of_natDegree_le_one hdegree.le,
    hasSimpleRoots_of_natDegree_le_one hne hdegree.le⟩

private theorem lagTwoEuler_base
    {P : ℕ → ℝ[X]} {w u v : ℝ}
    (hw : 0 < w) (hu : 0 < u) (hv : 0 < v)
    (hzero : P 0 = C w) (hone : P 1 = C u + C v * X) :
    LagTwoEulerPairCertificate P 0 := by
  have hP0 : SimpleNegRooted (P 0) 0 := by
    rw [hzero]
    simpa using SimpleNegRooted.one.C_mul hw
  have hP1 : SimpleNegRooted (P 1) 1 := by
    rw [hone]
    exact simpleNegRooted_linear hu hv
  have hadj : StrictInterl (P 0) (P 1) :=
    StrictInterl.of_degree_zero_right_of_degree_one
      hP0.pos.ne_zero hP0.splits hP1.pos.ne_zero hP1.splits
      hP0.natDegree_eq hP1.natDegree_eq
  have hcore : lagTwoEulerCore 0 (P 0) = P 0 := by
    have hder : (P 0).derivative = 0 :=
      derivative_eq_zero.mpr hP0.natDegree_eq
    simp [lagTwoEulerCore, thetaPlusOne, polarTheta, theta, hder]
  exact ⟨hP0, hP1, hadj, by simpa [hcore] using hadj⟩

/-- General lag-two Euler recurrence theorem.  Positive constants start the
sequence; the first row is a positive linear polynomial; and every later row
uses positive `a`, `b ≥ a`, and a nonnegative lag coefficient. -/
theorem lagTwoEuler_recurrence_certificate
    (P : ℕ → ℝ[X]) (a b c : ℕ → ℝ) (w u v : ℝ)
    (hw : 0 < w) (hu : 0 < u) (hv : 0 < v)
    (hzero : P 0 = C w) (hone : P 1 = C u + C v * X)
    (ha : ∀ n, 0 < a (n + 2))
    (hab : ∀ n, a (n + 2) ≤ b (n + 2))
    (hc : ∀ n, 0 ≤ c (n + 2))
    (hrec : ∀ n, P (n + 2) =
      lagTwoEulerStep (n + 1) (a (n + 2)) (b (n + 2)) (P (n + 1)) +
        C (c (n + 2)) * X * lagTwoEulerCore n (P n)) :
    ∀ n, LagTwoEulerPairCertificate P n := by
  intro n
  induction n with
  | zero => exact lagTwoEuler_base hw hu hv hzero hone
  | succ n ih =>
      let A := lagTwoEulerStep (n + 1) (a (n + 2)) (b (n + 2)) (P (n + 1))
      let H := lagTwoEulerCore n (P n)
      let L := C (c (n + 2)) * X * H
      have hAdeg : A.natDegree = n + 2 := by
        dsimp [A]
        simpa using natDegree_lagTwoEulerStep ih.next.natDegree_eq ih.next.pos (ha n)
      have hHdeg : H.natDegree = n := by
        dsimp [H]
        exact natDegree_lagTwoEulerCore ih.current.natDegree_eq ih.current.pos.ne_zero
      have hLdeg : L.natDegree ≤ n + 1 := by
        dsimp [L]
        calc
          (C (c (n + 2)) * X * H).natDegree
              ≤ (C (c (n + 2)) * X).natDegree + H.natDegree := natDegree_mul_le
          _ ≤ X.natDegree + n := Nat.add_le_add
            (natDegree_C_mul_le (c (n + 2)) X) hHdeg.le
          _ = n + 1 := by simp [natDegree_X]; lia
      have hLA : L.natDegree < A.natDegree := by lia
      have houtdeg : (P (n + 2)).natDegree = n + 2 := by
        rw [hrec n]
        exact (natDegree_add_eq_left_of_natDegree_lt hLA).trans hAdeg
      have hAnn : HasNonnegCoeffs A := by
        dsimp [A]
        exact ih.next.nonneg.lagTwoEulerStep ih.next.natDegree_eq
          (ha n).le (hab n)
      have hHnn : HasNonnegCoeffs H := by
        dsimp [H]
        exact ih.current.nonneg.lagTwoEulerCore_nonneg ih.current.natDegree_eq.le
      have hLnn : HasNonnegCoeffs L := by
        dsimp [L]
        simpa [mul_assoc] using hasNonnegCoeffs_C_mul (hc n)
          (hasNonnegCoeffs_X.mul hHnn)
      have houtnn : HasNonnegCoeffs (P (n + 2)) := by
        rw [hrec n]
        exact hAnn.add hLnn
      have hApos : HasPosLeadingCoeff A := by
        rw [HasPosLeadingCoeff, leadingCoeff, hAdeg]
        dsimp [A]
        rw [coeff_lagTwoEulerStep_succ,
          coeff_eq_zero_of_natDegree_lt (by rw [ih.next.natDegree_eq]; lia)]
        have htop : 0 < (P (n + 1)).coeff (n + 1) := by
          simpa [HasPosLeadingCoeff, leadingCoeff, ih.next.natDegree_eq] using ih.next.pos
        nlinarith [mul_pos (ha n) htop]
      have houtpos : HasPosLeadingCoeff (P (n + 2)) := by
        rw [hrec n]
        exact hasPosLeadingCoeff_add_of_natDegree_lt_left hLA hApos
      have houtzero : 0 < (P (n + 2)).coeff 0 := by
        rw [hrec n, coeff_add, coeff_lagTwoEulerStep_zero]
        have hlagzero : L.coeff 0 = 0 := by
          dsimp [L]
          simp
        rw [← show L = C (c (n + 2)) * X * H from rfl, hlagzero]
        simpa using mul_pos (ha n) ih.next.coeff_zero_pos
      have hrootSign : ∀ r, (P (n + 1)).IsRoot r →
          (P (n + 2)).eval r * (P (n + 1)).derivative.eval r < 0 := by
        intro r hr
        have hrneg := ih.next.isRoot_neg hr
        have hderne := ih.next.simple.eval_derivative_ne_zero hr
        have hauxSign := ih.auxiliary.eval_mul_eval_derivative_nonneg
          ih.current.lagTwoEulerCore_preserves.pos ih.next.pos hr
        have heval : (P (n + 2)).eval r =
            b (n + 2) * r * (1 - r) * (P (n + 1)).derivative.eval r +
              c (n + 2) * r * H.eval r := by
          rw [hrec n]
          simp only [eval_add, eval_mul, eval_C, eval_X]
          rw [lagTwoEulerStep_eval_isRoot hr]
        rw [heval]
        have hbpos : 0 < b (n + 2) := lt_of_lt_of_le (ha n) (hab n)
        have hfirst : b (n + 2) * r * (1 - r) *
            (P (n + 1)).derivative.eval r ^ 2 < 0 := by
          exact mul_neg_of_neg_of_pos
            (mul_neg_of_neg_of_pos
              (mul_neg_of_pos_of_neg hbpos hrneg) (by linarith))
            (sq_pos_of_ne_zero hderne)
        have hsecond : c (n + 2) * r *
            (H.eval r * (P (n + 1)).derivative.eval r) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos (hc n) hrneg.le) hauxSign
        nlinarith
      have hpackage := strictInterl_package_of_eval_mul_derivative_neg_succ
        ih.next.splits ih.next.pos houtpos ih.next.natDegree_eq houtdeg hrootSign
      have hout : SimpleNegRooted (P (n + 2)) (n + 2) :=
        ⟨houtdeg, houtpos, houtnn, houtzero, hpackage.2.2.1, hpackage.2.2.2.2.1⟩
      have hqA := ih.next.lagTwoEulerCore_strictInterl_step (ha n) (hab n)
      have hHq := ih.adjacent.lagTwoEulerCore_adjacent ih.current ih.next
      have hqXH : StrictInterl (lagTwoEulerCore (n + 1) (P (n + 1))) (X * H) := by
        exact strictInterl_mul_X_of_strictInterl_of_nonneg hHq
          ih.current.lagTwoEulerCore_preserves.nonneg
          ih.next.lagTwoEulerCore_preserves.nonneg
      have haux : StrictInterl (lagTwoEulerCore (n + 1) (P (n + 1)))
          (P (n + 2)) := by
        have hsum : StrictInterl (lagTwoEulerCore (n + 1) (P (n + 1)))
            (weightedSum [(1, A), (c (n + 2), X * H)]) := by
          apply StrictInterl.weightedSum_left_of_common_left
          · simp [hc n]
          · intro cq hcq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hcq
            rcases hcq with rfl | rfl
            exacts [hqA, hqXH]
          · exact ih.next.lagTwoEulerCore_preserves.pos
          · intro cq hcq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hcq
            rcases hcq with rfl | rfl
            · exact hApos
            · exact ih.current.lagTwoEulerCore_preserves.pos.X_mul
          · exact ⟨(1, A), by simp⟩
        rw [hrec n]
        simpa [A, H, L, weightedSum, weightedSum_cons, mul_assoc] using hsum
      exact ⟨ih.next, hout, hpackage.1, haux⟩

/-- Every row in the general recurrence has its full set of simple negative
roots. -/
theorem lagTwoEuler_recurrence_simpleNegRooted
    (P : ℕ → ℝ[X]) (a b c : ℕ → ℝ) (w u v : ℝ)
    (hw : 0 < w) (hu : 0 < u) (hv : 0 < v)
    (hzero : P 0 = C w) (hone : P 1 = C u + C v * X)
    (ha : ∀ n, 0 < a (n + 2))
    (hab : ∀ n, a (n + 2) ≤ b (n + 2))
    (hc : ∀ n, 0 ≤ c (n + 2))
    (hrec : ∀ n, P (n + 2) =
      lagTwoEulerStep (n + 1) (a (n + 2)) (b (n + 2)) (P (n + 1)) +
        C (c (n + 2)) * X * lagTwoEulerCore n (P n)) (n : ℕ) :
    SimpleNegRooted (P n) n :=
  (lagTwoEuler_recurrence_certificate P a b c w u v hw hu hv hzero hone
    ha hab hc hrec n).current

end RealRooted
