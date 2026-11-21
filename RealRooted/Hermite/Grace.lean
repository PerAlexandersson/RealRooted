module

public import RealRooted.Hermite.Gaussian
public import RealRooted.Apolarity
import RealRooted.Apolarity.Scaling
import RealRooted.Mathlib.Data.Nat.Choose.Cast

/-!
# Gaussian evaluation and Grace's apolarity theorem

The finite Gaussian coefficient functional is a normalized apolar pairing with
a homogeneous Hermite polynomial. Grace's theorem gives its nonvanishing when
the input roots lie strictly above the Hermite root line. This is the algebraic
step of the unpublished proof in RealRooted issue #2415:
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

public section

open Polynomial Finset

namespace RealRooted

/-- Gaussian evaluation is the apolar pairing against the reduced homogeneous
Hermite polynomial. The first lift may have degree less than `n`. -/
theorem apolarPairing_eq_gaussianEval {n : ℕ} {p f g : ℂ[X]} {s : ℂ}
    (hf : binomialLift n f = p) (hg : binomialLift n g = hermiteHomogeneousPoly s n) :
    apolarPairing n f g = gaussianEval s p := by
  have hp : p.natDegree ≤ n := hf ▸ natDegree_binomialLift_le n f
  rw [gaussianEval, Polynomial.sum_eq_of_subset _ (by simp)
    (show p.support ⊆ range (n + 1) from fun k hk =>
      mem_range_succ_iff.mpr ((le_natDegree_of_mem_supp k hk).trans hp))]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := mem_range_succ_iff.mp hk
  have hpk := congrArg (fun q : ℂ[X] => q.coeff k) hf
  rw [coeff_binomialLift, ite_eq_left hkn] at hpk
  have hgk := congrArg (fun q : ℂ[X] => q.coeff (n - k)) hg
  rw [coeff_binomialLift, ite_eq_left (Nat.sub_le n k), coeff_hermiteHomogeneousPoly,
    Nat.sub_sub_self hkn, Nat.choose_symm hkn] at hgk
  have hgn : g.coeff (n - k) = hermiteHomogeneous 0 s k :=
    mul_left_cancel₀ (Nat.cast_choose_ne_zero (R := ℂ) hkn) hgk
  change (-1 : ℂ) ^ k * (n.choose k : ℂ) * f.coeff k * g.coeff (n - k) = _
  rw [hgn]
  calc
    _ = p.coeff k * ((-1 : ℂ) ^ k * hermiteHomogeneous 0 s k) := by rw [← hpk]; ring
    _ = _ := by rw [neg_one_pow_mul_hermiteHomogeneous_zero]

/-- A finite set of roots strictly above the real line has a positive uniform
lower bound on the imaginary parts. The inserted value `1` handles constants. -/
theorem exists_pos_le_im_of_roots_im_pos {p : ℂ[X]} (hp : p ≠ 0)
    (hroots : ∀ z, p.IsRoot z → 0 < z.im) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z, p.IsRoot z → ε ≤ z.im := by
  classical
  let S := insert 1 (p.roots.toFinset.image Complex.im)
  have hS : S.Nonempty := ⟨1, mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_, ?_⟩
  · have hm := S.min'_mem hS
    rcases mem_insert.mp hm with h | h
    · simp [h]
    · obtain ⟨z, hz, heq⟩ := mem_image.mp h
      rw [← heq]
      exact hroots z (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hz))
  · intro z hz
    exact S.min'_le _ (mem_insert_of_mem (mem_image.mpr
      ⟨z, Multiset.mem_toFinset.mpr ((mem_roots hp).mpr hz), rfl⟩))

/-- Homogeneous Hermite polynomials with negative real quadratic parameter have real roots. -/
theorem im_eq_zero_of_isRoot_hermiteHomogeneousPoly {c : ℝ} (hc : 0 ≤ c)
    {n : ℕ} {z : ℂ} (hz : (hermiteHomogeneousPoly (-(c : ℂ)) n).IsRoot z) : z.im = 0 := by
  have hz' : hermiteHomogeneous z (-(c : ℂ)) n = 0 := by
    simpa only [IsRoot.def, hermiteHomogeneousPoly, eval_hermiteHomogeneous] using hz
  obtain ⟨ν, hν, he⟩ := exists_nonneg_sq_add_eq_zero_of_hermiteHomogeneous_eq_zero hz'
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.zero_im, pow_two, neg_zero, zero_mul,
    mul_zero, sub_zero, add_zero] at hr hi
  have hm : z.re * z.im = 0 := by nlinarith [hi]
  rcases mul_eq_zero.mp hm with h | h
  · nlinarith [mul_nonneg hν hc, sq_nonneg z.im]
  · exact h

/-- Backward Gaussian evaluation of a polynomial whose roots are in the open
upper half-plane is nonzero. This is a finite consequence of Grace's theorem. -/
theorem gaussianEval_ne_zero_of_roots_im_pos {p : ℂ[X]} {c : ℝ} (hc : 0 ≤ c)
    (hroots : ∀ z, p.IsRoot z → 0 < z.im) : gaussianEval (-(c : ℂ)) p ≠ 0 := by
  have hp : p ≠ 0 := by
    intro he
    have hh := hroots (-Complex.I) (by simp [he, IsRoot.def])
    norm_num at hh
  obtain ⟨ε, hε, hεroots⟩ := exists_pos_le_im_of_roots_im_pos hp hroots
  let n := p.natDegree
  obtain ⟨f, hf⟩ := exists_binomialLift_eq p (le_refl n)
  obtain ⟨g, hg⟩ := exists_binomialLift_eq (hermiteHomogeneousPoly (-(c : ℂ)) n)
    (hermiteHomogeneousPoly_monic (-(c : ℂ)) n).2.le
  intro he
  have hap : AreApolar n f g := by
    rw [AreApolar, apolarPairing_eq_gaussianEval hf hg, he]
  obtain ⟨z, hz, hroot⟩ := exists_isRoot_le_im_of_areApolar_of_natDegree_le
    (natDegree_binomialLift_le n f)
    (by rw [hg]; exact (hermiteHomogeneousPoly_monic _ _).2)
    hap (by rw [hf]; exact hεroots)
  rw [hg] at hroot
  have hi := im_eq_zero_of_isRoot_hermiteHomogeneousPoly hc hroot
  linarith

end RealRooted
