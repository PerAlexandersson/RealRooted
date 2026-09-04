import Mathlib.Analysis.Complex.Polynomial.Basic
import RealRooted.Bezoutian.RootEvaluation
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex

/-!
# Complex-root exclusion from a positive Bezout matrix

Complexified Bezout evaluation excludes nonreal roots and recovers splitness
of both real polynomials from positive definiteness.
-/

open Polynomial Matrix

noncomputable section

namespace RealRooted

lemma bezoutEntry.bilinear_mul_sub_complex (p q : ℝ[X]) {n : ℕ} (z w : ℂ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (z - w) * ∑ i : Fin n, ∑ j : Fin n,
    (bezoutEntry p q i.val j.val : ℂ) * z ^ i.val * w ^ j.val =
    (p.map Complex.ofRealHom).eval z * (q.map Complex.ofRealHom).eval w -
    (p.map Complex.ofRealHom).eval w * (q.map Complex.ofRealHom).eval z := by
  have hp_zero (k : ℕ) (hk : n < k) : (p.map Complex.ofRealHom).coeff k = 0 := by
    rw [coeff_map]
    simp [coeff_eq_zero_of_natDegree_lt (hp.trans_lt hk)]
  have hq_zero (k : ℕ) (hk : n < k) : (q.map Complex.ofRealHom).coeff k = 0 := by
    rw [coeff_map]
    simp [coeff_eq_zero_of_natDegree_lt (hq.trans_lt hk)]
  have h_eq :
      (z - w) * ∑ i : Fin n, ∑ j : Fin n,
        bezoutSeqEntry (p.map Complex.ofRealHom).coeff (q.map Complex.ofRealHom).coeff
          i.val j.val * z ^ i.val * w ^ j.val =
      (∑ i ∈ Finset.range (n + 1), (p.map Complex.ofRealHom).coeff i * z ^ i) *
        (∑ j ∈ Finset.range (n + 1), (q.map Complex.ofRealHom).coeff j * w ^ j) -
      (∑ i ∈ Finset.range (n + 1), (p.map Complex.ofRealHom).coeff i * w ^ i) *
        (∑ j ∈ Finset.range (n + 1), (q.map Complex.ofRealHom).coeff j * z ^ j) :=
    bezoutSeqEntry.bilinear_mul_sub
      (p.map Complex.ofRealHom).coeff (q.map Complex.ofRealHom).coeff
      n z w hp_zero hq_zero
  simp_rw [← bezoutEntry.cast_complex] at h_eq
  have hp_lim : (p.map Complex.ofRealHom).natDegree < n + 1 := by
    rw [natDegree_map]
    exact Nat.lt_succ_of_le hp
  have hq_lim : (q.map Complex.ofRealHom).natDegree < n + 1 := by
    rw [natDegree_map]
    exact Nat.lt_succ_of_le hq
  simp_rw [Polynomial.eval_eq_sum_range' hp_lim,
    Polynomial.eval_eq_sum_range' hq_lim]
  exact h_eq

lemma PosDef.eq_zero_of_sum_mul_star_eq_zero {m : ℕ} {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.PosDef) (y : Fin m → ℂ)
    (hy_sum : ∑ i : Fin m, ∑ j : Fin m, (B i j : ℂ) * y i * starRingEnd ℂ (y j) = 0) :
    y = 0 := by
  have h_pos (x : Fin m → ℝ) :
      0 ≤ ∑ i : Fin m, ∑ j : Fin m, B i j * x i * x j := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (Matrix.PosDef.sum_pos hB hx).le
  have hre_zero : (fun i ↦ (y i).re) = 0 := by
    by_contra hre_ne
    have hre_pos : 0 < ∑ i : Fin m, ∑ j : Fin m, B i j * (y i).re * (y j).re :=
      Matrix.PosDef.sum_pos hB hre_ne
    have h_re_sum : ∑ i : Fin m, ∑ j : Fin m, B i j * (y i).re * (y j).re +
        ∑ i : Fin m, ∑ j : Fin m, B i j * (y i).im * (y j).im = 0 := by
      have :
          (∑ i : Fin m, ∑ j : Fin m,
            (B i j : ℂ) * y i * starRingEnd ℂ (y j)).re = 0 := by
        rw [hy_sum, Complex.zero_re]
      simp_all only [Complex.ext_iff, Complex.zero_re, Complex.zero_im,
        Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.conj_re, Complex.mul_im, add_zero, Complex.conj_im, mul_neg,
        sub_neg_eq_add, Finset.sum_add_distrib, Complex.im_sum, Finset.sum_neg_distrib]
    linarith [h_pos (fun i ↦ (y i).im), hre_pos, h_re_sum]
  have him_zero : (fun i ↦ (y i).im) = 0 := by
    have h_re_sum : ∑ i : Fin m, ∑ j : Fin m, B i j * (y i).re * (y j).re +
        ∑ i : Fin m, ∑ j : Fin m, B i j * (y i).im * (y j).im = 0 := by
      have :
          (∑ i : Fin m, ∑ j : Fin m,
            (B i j : ℂ) * y i * starRingEnd ℂ (y j)).re = 0 := by
        rw [hy_sum, Complex.zero_re]
      simp_all only [Complex.ext_iff, Complex.zero_re, Complex.zero_im,
        Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.conj_re, Complex.mul_im, add_zero, Complex.conj_im, mul_neg,
        sub_neg_eq_add, Finset.sum_add_distrib, Complex.im_sum, Finset.sum_neg_distrib]
    have hre_zero_pt (i : Fin m) : (y i).re = 0 := by
      have := congr_fun hre_zero i
      simpa using this
    simp only [hre_zero_pt, mul_zero, Finset.sum_const_zero, zero_add] at h_re_sum
    by_contra him_ne
    have him_pos : 0 < ∑ i : Fin m, ∑ j : Fin m, B i j * (y i).im * (y j).im :=
      Matrix.PosDef.sum_pos hB him_ne
    linarith [him_pos, h_re_sum]
  funext i
  exact Complex.ext (congr_fun hre_zero i) (congr_fun him_zero i)

lemma bezoutMatrix.no_complex_root_of_posDef {n : ℕ}
    {p q : ℝ[X]} (hp_deg : p.natDegree ≤ n + 1) (hq_deg : q.natDegree ≤ n + 1)
    (hB : (bezoutMatrix (n + 1) q p).PosDef)
    (z : ℂ) (hz : 0 < z.im) (hroot : (p.map Complex.ofRealHom).eval z = 0) :
    False := by
  have h_star_root : (p.map Complex.ofRealHom).eval (starRingEnd ℂ z) = 0 := by
    simpa [eval_eq_sum_range] using congr_arg Star.star hroot
  have h_bezoutian : (z - starRingEnd ℂ z) * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      (bezoutEntry q p i.val j.val : ℂ) * z ^ i.val * (starRingEnd ℂ z) ^ j.val = 0 := by
    convert bezoutEntry.bilinear_mul_sub_complex q p z
      (starRingEnd ℂ z) hq_deg hp_deg using 1
    simp_all only [eval_map, mul_zero, sub_zero]
  have h_z_ne : z - starRingEnd ℂ z ≠ 0 := by
    intro hdiff
    have him := congr_arg Complex.im hdiff
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
    linarith
  have hsum : ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      (bezoutMatrix (n + 1) q p i j : ℂ) * z ^ i.val * starRingEnd ℂ (z ^ j.val) = 0 := by
    have hsum_aux := (mul_eq_zero.mp h_bezoutian).resolve_left h_z_ne
    simpa only [bezoutMatrix, map_pow] using hsum_aux
  have h_y_ne : (fun (i : Fin (n + 1)) ↦ z ^ i.val) ≠ 0 := fun h ↦
    one_ne_zero (congr_fun h ⟨0, Nat.zero_lt_succ n⟩)
  have h_y_zero :=
    PosDef.eq_zero_of_sum_mul_star_eq_zero hB (fun (i : Fin (n + 1)) ↦ z ^ i.val) hsum
  exact h_y_ne h_y_zero

lemma bezoutMatrix.no_complex_root_q_of_posDef {n : ℕ}
    {p q : ℝ[X]} (hp_deg : p.natDegree ≤ n + 1) (hq_deg : q.natDegree ≤ n + 1)
    (hB : (bezoutMatrix (n + 1) q p).PosDef)
    (z : ℂ) (hz : 0 < z.im) (hroot : (q.map Complex.ofRealHom).eval z = 0) :
    False := by
  have h_no_complex := @bezoutMatrix.no_complex_root_of_posDef
  contrapose! h_no_complex
  use n, q, -p
  refine ⟨hq_deg, ?_, ?_, z, hz, hroot, h_no_complex⟩
  · simp_all
  · convert hB using 1
    ext i j
    simp [bezoutMatrix, bezoutEntry, neg_add_eq_sub, Finset.sum_sub_distrib]

lemma bezoutMatrix.splits_of_posDef {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hB : (bezoutMatrix n q p).PosDef) :
    p.Splits ∧ q.Splits := by
  by_cases hn : n = 0
  · subst hn
    have hp : p.natDegree = 0 := hp_deg
    have hq : q.natDegree = 0 := hq_deg
    obtain ⟨-, hp_splits⟩ := isRealRooted_of_deg_zero (leadingCoeff_ne_zero.mp hp_pos.ne') hp
    obtain ⟨-, hq_splits⟩ := isRealRooted_of_deg_zero (leadingCoeff_ne_zero.mp hq_pos.ne') hq
    simp_all
  · have hn_eq : n = n - 1 + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)).symm
    have hB' : (bezoutMatrix (n - 1 + 1) q p).PosDef := hn_eq ▸ hB
    constructor
    · apply Polynomial.splits_of_all_roots_real
      intro z hz
      by_contra h_im_ne_zero
      rcases lt_or_gt_of_ne h_im_ne_zero with h_neg | h_pos
      · have h_star_im : 0 < (starRingEnd ℂ z).im := by simp [h_neg]
        have h_star_root : (p.map Complex.ofRealHom).eval (starRingEnd ℂ z) = 0 := by
          simpa [eval_eq_sum_range] using congr_arg Star.star hz
        exact bezoutMatrix.no_complex_root_of_posDef (hn_eq ▸ hp_deg.le) (hn_eq ▸ hq_deg.le)
          hB' (starRingEnd ℂ z) h_star_im h_star_root
      · exact bezoutMatrix.no_complex_root_of_posDef (hn_eq ▸ hp_deg.le) (hn_eq ▸ hq_deg.le)
          hB' z h_pos hz
    · apply Polynomial.splits_of_all_roots_real
      intro z hz
      by_contra h_im_ne_zero
      rcases lt_or_gt_of_ne h_im_ne_zero with h_neg | h_pos
      · have h_star_im : 0 < (starRingEnd ℂ z).im := by simp [h_neg]
        have h_star_root : (q.map Complex.ofRealHom).eval (starRingEnd ℂ z) = 0 := by
          simpa [eval_eq_sum_range] using congr_arg Star.star hz
        exact bezoutMatrix.no_complex_root_q_of_posDef (hn_eq ▸ hp_deg.le) (hn_eq ▸ hq_deg.le)
          hB' (starRingEnd ℂ z) h_star_im h_star_root
      · exact bezoutMatrix.no_complex_root_q_of_posDef (hn_eq ▸ hp_deg.le) (hn_eq ▸ hq_deg.le)
          hB' z h_pos hz

end RealRooted
