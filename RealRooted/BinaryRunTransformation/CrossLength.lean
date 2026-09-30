import RealRooted.BalancedRunTransformation.Interlacing
import RealRooted.BinaryRunTransformation.Interlacing
import RealRooted.BinaryRunTransformation.KernelIdentities
import RealRooted.DegreeDropReversal
import RealRooted.EulerOperator.Polar.Pencil
import RealRooted.Interlacing.OuterDifference
import RealRooted.PosCombo
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Cross-length transport for the binary-run transformation

For `N = n + 1` and a PF polynomial `g` with nonzero constant term and
`2 ≤ deg g ≤ N / 2`, this file proves

`J_n((N - 2Θ) g) ≪ J_{n+1}(g)`,

where `Θ = X d/dX`.  With `A = J_n(g)`, `P = J_n((N - Θ) g)`,
`F = J_n((N - 2Θ) g)` and `E = K_n(g')`, the kernel identities give
`K_n((N - Θ) g) = F + E`, `2P = F + N A` and `N J_{n+1}(g) = P + X E`.
Interlacing preservation for `J_n` and `K_n` yields `F ≪ A` and `E ≪ F + E`;
the common-left cone then closes `F ≪ P + X E`.
-/

open Polynomial

noncomputable section

namespace RealRooted

private theorem natDegree_theta_le (p : ℝ[X]) : (theta p).natDegree ≤ p.natDegree := by
  rcases eq_or_ne (derivative p) 0 with hd | hd
  · simp [theta, hd]
  · have hp : p.natDegree ≠ 0 := fun h => hd (by rw [eq_C_of_natDegree_eq_zero h]; simp)
    rw [theta, natDegree_X_mul hd]
    have := natDegree_derivative_lt hp
    lia

private theorem binaryRunTransform_C_mul (n : ℕ) (a : ℝ) (p : ℝ[X]) :
    binaryRunTransform n (C a * p) = C a * binaryRunTransform n p := by
  rw [← smul_eq_C_mul, binaryRunTransform_smul]

private theorem natDegree_C_mul_sub_C_mul_theta_le (a b : ℝ) (p : ℝ[X]) :
    (C a * p - C b * theta p).natDegree ≤ p.natDegree :=
  (natDegree_sub_le _ _).trans (max_le (natDegree_C_mul_le _ _)
    ((natDegree_C_mul_le _ _).trans (natDegree_theta_le p)))

/-- A real polar comparison: for a PF polynomial `g` with nonzero constant term
and `2 ≤ deg g`, `(N - 2Θ) g` precedes `g` whenever `2 deg g ≤ N`. -/
theorem strictInterl_C_mul_sub_two_theta_self {N : ℕ} {g : ℝ[X]}
    (hg : IsPFPolynomial g) (hg0 : g.coeff 0 ≠ 0)
    (hdeg2 : 2 ≤ g.natDegree) (hN : 2 * g.natDegree ≤ N) :
    StrictInterl (C (N : ℝ) * g - C 2 * theta g) g ∧
      HasNonnegCoeffs (C (N : ℝ) * g - C 2 * theta g) := by
  set d := g.natDegree with hd
  have hgnn := hg.hasNonnegCoeffs
  have hg_ne : g ≠ 0 := by
    intro h
    simp [h] at hg0
  have hpd : StrictInterl (polarTheta d g) g :=
    strictInterl_polarTheta_self hg le_rfl (by
      rw [reciprocalShift,
        DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne le_rfl hg0]
      exact hdeg2)
  have hPnn : HasNonnegCoeffs (polarTheta d g) :=
    (polarTheta_preserves_pf hg le_rfl).hasNonnegCoeffs
  have hP2 : StrictInterl (C 2 * polarTheta d g) g := hpd.C_mul_left two_ne_zero
  have hP2nn : HasNonnegCoeffs (C 2 * polarTheta d g) := nonnegCoeffs_C_mul (by norm_num) hPnn
  have heq : C (N : ℝ) * g - C 2 * theta g =
      C 2 * polarTheta d g + C ((N : ℝ) - 2 * d) * g := by
    simp only [polarTheta, C_sub, C_mul, map_natCast, map_ofNat]
    ring
  rcases hN.eq_or_lt with hNd | hNd
  · have h0 : ((N : ℝ) - 2 * d) = 0 := by
      rw [← hNd]
      push_cast
      ring
    rw [heq, h0, C_0, zero_mul, add_zero]
    exact ⟨hP2, hP2nn⟩
  · have hpos : (0 : ℝ) < (N : ℝ) - 2 * d := by
      have : ((2 * d : ℕ) : ℝ) < N := by exact_mod_cast hNd
      push_cast at this
      linarith
    have hgg : StrictInterl (C ((N : ℝ) - 2 * d) * g) g :=
      (StrictInterl.refl hg_ne (hg.ne_zero_and_splits hg_ne).2).C_mul_left hpos.ne'
    rw [heq]
    refine ⟨StrictInterl.add_of_right_of_posLeadingCoeff hP2 hgg
      (hP2nn.pos_leadingCoeff hP2.1.1)
      (hasPosLeadingCoeff_C_mul hpos (hgnn.pos_leadingCoeff hg_ne)), ?_⟩
    exact hP2nn.add (nonnegCoeffs_C_mul hpos.le hgnn)

/-- Cross-length transport for the binary-run transformation:
`J_n((N - 2Θ) g) ≪ J_{n+1}(g)` for `N = n + 1`, a PF polynomial `g` with
nonzero constant term, and `2 ≤ deg g ≤ N / 2`. -/
theorem strictInterl_binaryRunTransform_succ
    {n : ℕ} {g : ℝ[X]} (hg : IsPFPolynomial g) (hg0 : g.coeff 0 ≠ 0)
    (hdeg2 : 2 ≤ g.natDegree) (hdeg : 2 * g.natDegree ≤ n + 1) :
    StrictInterl (binaryRunTransform n (C ((n : ℝ) + 1) * g - C 2 * theta g))
      (binaryRunTransform (n + 1) g) := by
  have hgnn := hg.hasNonnegCoeffs
  have hgn : g.natDegree ≤ n := by lia
  have hbox : g.natDegree ≤ (n + 1) / 2 := by lia
  have hn2 : 2 ≤ n := by lia
  -- Inputs.
  obtain ⟨hFin, hFinnn⟩ :=
    strictInterl_C_mul_sub_two_theta_self (N := n + 1) hg hg0 hdeg2 hdeg
  push_cast at hFin hFinnn
  have hpolar_g : StrictInterl (polarTheta (n + 1) g) g :=
    strictInterl_polarTheta_self hg (by lia) (by
      rw [reciprocalShift,
        DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne (by lia) hg0]
      lia)
  have hdP : StrictInterl (derivative g) (polarTheta (n + 1) g) :=
    strictInterl_derivative_polarTheta hg hdeg2 (by lia) hpolar_g
  have hPnn : HasNonnegCoeffs (polarTheta (n + 1) g) :=
    (polarTheta_preserves_pf hg (by lia)).hasNonnegCoeffs
  have hpolar_deg : (polarTheta (n + 1) g).natDegree ≤ (n + 1) / 2 := by
    have h := natDegree_C_mul_sub_C_mul_theta_le ((n + 1 : ℕ) : ℝ) 1 g
    rw [C_1, one_mul] at h
    exact h.trans hbox
  -- The four transformed polynomials.
  set A := binaryRunTransform n g with hA
  set F := binaryRunTransform n (C ((n : ℝ) + 1) * g - C 2 * theta g) with hF
  set P := binaryRunTransform n (polarTheta (n + 1) g) with hP
  set E := balancedRunTransform n (derivative g) with hE
  have hFA : StrictInterl F A :=
    strictInterl_binaryRunTransform hFin hFinnn hgnn
      ((natDegree_C_mul_sub_C_mul_theta_le _ _ g).trans hbox) hbox
  have hEK : StrictInterl E (balancedRunTransform n (polarTheta (n + 1) g)) :=
    strictInterl_balancedRunTransform hn2 hdP hgnn.derivative hPnn
      ((natDegree_derivative_le g).trans (by lia)) hpolar_deg
  -- Linear algebra of the kernels.
  have hlin : ∀ (a b : ℝ) (p q : ℝ[X]), binaryRunTransform n (C a * p - C b * q) =
      C a * binaryRunTransform n p - C b * binaryRunTransform n q := by
    intro a b p q
    rw [← binaryRunTransform_C_mul, ← binaryRunTransform_C_mul]
    exact map_sub (binaryRunTransformLinearMap n) _ _
  have hpolar_eq : polarTheta (n + 1) g = C ((n : ℝ) + 1) * g - C 1 * theta g := by
    simp [polarTheta]
  have hK : balancedRunTransform n (polarTheta (n + 1) g) = F + E := by
    rw [balancedRunTransform_polarTheta_eq hgn, hF, hE, hpolar_eq, hlin, hlin]
    simp only [C_1, one_mul, map_ofNat]
    ring
  have h2P : C 2 * P = F + C ((n : ℝ) + 1) * A := by
    rw [hP, hF, hA, hpolar_eq, hlin, hlin]
    simp only [C_1, one_mul, map_ofNat]
    ring
  have hG : C ((n : ℝ) + 1) * binaryRunTransform (n + 1) g = P + X * E :=
    binaryRunTransform_succ_eq hgn
  -- Nonnegativity and nonvanishing.
  have hFnn : HasNonnegCoeffs F := hFinnn.binaryRunTransform
  have hAnn : HasNonnegCoeffs A := hgnn.binaryRunTransform
  have hEnn : HasNonnegCoeffs E := hgnn.derivative.balancedRunTransform
  have hPnn' : HasNonnegCoeffs P := hPnn.binaryRunTransform
  rw [hK] at hEK
  clear_value A F P E
  have hF0 : F ≠ 0 := hFA.1.1
  have hE0 : E ≠ 0 := hEK.1.1
  have hFpos := hFnn.pos_leadingCoeff hF0
  have hEpos := hEnn.pos_leadingCoeff hE0
  -- `E ≪ F`.
  have hEF : StrictInterl E F := by
    have h := StrictInterl.sub_of_triple_of_posLeadingCoeff
      (StrictInterl.refl hE0 hEK.1.2) hEK hEK hEpos hEpos
      ((hFnn.add hEnn).pos_leadingCoeff hEK.2.1.1) (by rwa [add_sub_cancel_right])
    rwa [add_sub_cancel_right] at h
  -- `F ≪ P`.
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hFP : StrictInterl F P := by
    have hFA' : StrictInterl F (C ((n : ℝ) + 1) * A) := hFA.C_mul_right hn1.ne'
    have hApos := hasPosLeadingCoeff_C_mul hn1 (hAnn.pos_leadingCoeff hFA.2.1.1)
    have h := StrictInterl.sum_left_of_common_left_signed [F, C ((n : ℝ) + 1) * A] F
      (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        exacts [StrictInterl.refl hF0 hFA.1.2, hFA'])
      (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        exacts [hFpos, hApos])
      (List.cons_ne_nil _ _)
    rw [List.sum_cons, List.sum_cons, List.sum_nil, add_zero, ← h2P] at h
    have h2 := h.C_mul_right (a := (1 / 2 : ℝ)) (by norm_num)
    rwa [← mul_assoc, ← C_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, C_1, one_mul] at h2
  -- `F ≪ P + X E`, hence `F ≪ J_{n+1}(g)`.
  have hFXE : StrictInterl F (X * E) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg hEF hEnn hFnn
  have hPpos := hPnn'.pos_leadingCoeff hFP.2.1.1
  have hXEpos := hEnn.X_mul.pos_leadingCoeff hFXE.2.1.1
  have hsum := StrictInterl.sum_left_of_common_left_signed [P, X * E] F
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      exacts [hFP, hFXE])
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      exacts [hPpos, hXEpos])
    (List.cons_ne_nil _ _)
  rw [List.sum_cons, List.sum_cons, List.sum_nil, add_zero, ← hG] at hsum
  have h := hsum.C_mul_right (a := ((n : ℝ) + 1)⁻¹) (inv_ne_zero hn1.ne')
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hn1.ne', C_1, one_mul] at h

end RealRooted
