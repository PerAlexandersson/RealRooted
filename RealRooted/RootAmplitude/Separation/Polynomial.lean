import RealRooted.RootAmplitude.Polynomial
import RealRooted.RootAmplitude.Separation.Euler
import RealRooted.RootAmplitude.Separation.Roots

/-!
# Polynomial root amplitudes from multiplicative separation

This leaf identifies the canonical finite-sequence amplitude with the
normalized derivative at a simple negative root, then applies the Euler
separation bound.
-/

open Polynomial

namespace RealRooted.RootAmplitude

noncomputable section

private theorem multiset_prod_eq_finset {p : ℝ[X]} (hnd : p.roots.Nodup)
    {s : ℝ} (f : ℝ → ℝ) :
    ((p.roots.erase s).map f).prod = ∏ r ∈ p.roots.toFinset.erase s, f r := by
  classical
  rw [Finset.prod_eq_multiset_prod]
  congr 1
  congr 1
  rw [Finset.erase_val, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]

/-- At the root indexed by the sorted magnitude sequence, the absolute
normalized derivative is the canonical finite amplitude. -/
theorem abs_eval_deriv_root_div_eval_zero_eq_amp
    {p : ℝ[X]} (hp : p.Splits) (hnd : p.roots.Nodup)
    (hzero : p.eval 0 ≠ 0) {k : ℕ}
    (hk : k < (SortedRoots.rootMags p).length) :
    |(-SortedRoots.rootSeq p k) *
        p.derivative.eval (-SortedRoots.rootSeq p k) / p.eval 0|
      = amp (SortedRoots.rootSeq p) (SortedRoots.rootMags p).length k := by
  classical
  have hroot : -SortedRoots.rootSeq p k ∈ p.roots :=
    SortedRoots.rootSeq_mem p hk
  have hcount : p.roots.count (-SortedRoots.rootSeq p k) = 1 :=
    Multiset.count_eq_one_of_mem hnd hroot
  have hvalue := eval_deriv_root_div_eval_zero hp hroot hcount hzero
  rw [hvalue, abs_neg,
    multiset_prod_eq_finset hnd (fun r => 1 - (-SortedRoots.rootSeq p k) / r),
    Finset.abs_prod, ← amp_rootSeq_eq_prod_roots hnd hk]

/-- A split polynomial with negative, exponentially separated roots has a
uniform lower bound on the normalized derivative at every root. -/
theorem exp_neg_pi_sq_div_three_le_abs_eval_deriv_of_root_separation
    {p : ℝ[X]} (hp : p.Splits) (hzero : p.eval 0 ≠ 0)
    (hneg : ∀ r ∈ p.roots, r < 0) {d : ℝ} (hd : 0 < d)
    (hsep : IsMultiplicativelySeparatedOn (Real.exp d)
      (SortedRoots.rootSeq p) (SortedRoots.rootMags p).length)
    {k : ℕ} (hk : k < (SortedRoots.rootMags p).length) :
    Real.exp (-(Real.pi ^ 2 / (3 * d)))
      ≤ |(-SortedRoots.rootSeq p k) *
          p.derivative.eval (-SortedRoots.rootSeq p k) / p.eval 0| := by
  have hpos : ∀ i, i < (SortedRoots.rootMags p).length →
      0 < SortedRoots.rootSeq p i :=
    fun _ hi => SortedRoots.rootSeq_pos p hneg hi
  have hstrict := hsep.strictMonoOnRange (Real.one_lt_exp_iff.mpr hd) hpos
  have hnd : p.roots.Nodup := roots_nodup_of_rootSeq_lt hstrict
  rw [abs_eval_deriv_root_div_eval_zero_eq_amp hp hnd hzero hk]
  exact exp_neg_pi_sq_div_three_le_amp_of_separation hd hpos hsep hk

end

end RealRooted.RootAmplitude
