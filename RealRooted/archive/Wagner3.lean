/-
# Wagner's lemma, form (3): X-multiplication equivalence

For polynomials with non-negative coefficients and non-positive roots:
`Prec f g ↔ Prec g (X * f)`.
-/
import RealRooted.Basic
import RealRooted.Interlacing
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Polynomial

noncomputable section

namespace RealRooted

/-! ## Roots of nonneg-coefficient polynomials are ≤ 0 -/

lemma roots_nonpos_of_nonneg_coeffs {p : ℝ[X]} (hp : IsRealRooted p)
    (hnn : HasNonnegCoeffs p) : ∀ r ∈ p.roots, r ≤ 0 := by
  intro r hr
  by_contra hgt; push_neg at hgt
  have hlc_pos : 0 < p.leadingCoeff := by
    have := hnn p.natDegree; exact lt_of_le_of_ne this (Ne.symm (leadingCoeff_ne_zero.mpr hp.1))
  have heval_pos : 0 < p.eval r := by
    rw [eval_eq_sum_range r]
    calc 0 < p.coeff p.natDegree * r ^ p.natDegree := mul_pos hlc_pos (pow_pos hgt _)
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * r ^ i :=
        Finset.single_le_sum (fun i _ => mul_nonneg (hnn i) (pow_nonneg hgt.le i))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le le_rfl))
  have : p.eval r = 0 := (mem_roots hp.1).mp hr
  linarith

lemma isRealRooted_X : IsRealRooted (X : ℝ[X]) :=
  ⟨X_ne_zero, by rw [roots_X, Multiset.card_singleton, natDegree_X]⟩

lemma isRealRooted_X_mul {f : ℝ[X]} (hf : IsRealRooted f) :
    IsRealRooted (X * f) := isRealRooted_mul isRealRooted_X hf

/-! ## Wagner (3): f ≪ g ↔ g ≪ X·f -/

theorem prec_iff_prec_mul_X {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Prec f g ↔ Prec g (X * f) := by
  have hXf_rr := isRealRooted_X_mul hf
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X]
  have hXf_deg : (X * f).natDegree = g.natDegree := by
    rw [natDegree_X_mul hf.1]; omega
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf hfnn
  have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hg hgnn
  constructor
  · -- Forward: Prec f g → Prec g (X * f)
    intro ⟨_, _, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
    rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, _⟩
    · have hrs_nonpos : ∀ r ∈ rs, r ≤ 0 := fun r hr =>
        hg_nonpos r (by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hr)
      have hss0_eq : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = (X * f).roots := by
        have : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = ↑ss + {(0 : ℝ)} := by
          rw [← Multiset.coe_add]; rfl
        rw [this, hXf_roots, ← hss_eq, add_comm]
      have hss_nonpos : ∀ s ∈ ss, s ≤ 0 := fun s hs =>
        hf_nonpos s (by rw [← hss_eq]; exact Multiset.mem_coe.mpr hs)
      have hss0_sorted : (ss ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by
        rw [List.pairwise_append]
        exact ⟨hss, List.pairwise_singleton _ _, fun a ha b hb => by
          simp only [List.mem_singleton] at hb; rw [hb]; exact hss_nonpos a ha⟩
      exact ⟨hg, hXf_rr, rs, ss ++ [(0 : ℝ)], hrs, hss0_sorted, hrs_eq, hss0_eq,
        Or.inr ⟨by simp; omega, listAlternates_append_zero ss rs hlen hint hrs_nonpos⟩⟩
    · have : ss.length = f.natDegree := by rw [← Multiset.coe_card, hss_eq, hf.2]
      have : rs.length = g.natDegree := by rw [← Multiset.coe_card, hrs_eq, hg.2]
      omega
  · -- Backward: Prec g (X * f) → Prec f g
    intro ⟨_, _, ss_g, rs_xf, hss_g, hrs_xf, hss_g_eq, hrs_xf_eq, hcase⟩
    rcases hcase with ⟨hlen, _⟩ | ⟨hlen, halt⟩
    · have : ss_g.length = g.natDegree := by rw [← Multiset.coe_card, hss_g_eq, hg.2]
      have : rs_xf.length = (X * f).natDegree := by rw [← Multiset.coe_card, hrs_xf_eq, hXf_rr.2]
      omega
    · set ss_f := f.roots.sort (· ≤ ·)
      have hss_f_eq : (↑ss_f : Multiset ℝ) = f.roots := Multiset.sort_eq ..
      have hss_f_sorted : ss_f.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
      have hrs_xf_is : rs_xf = ss_f ++ [(0 : ℝ)] := by
        have hmultiset_eq : (↑rs_xf : Multiset ℝ) = ↑(ss_f ++ [(0 : ℝ)]) := by
          rw [hrs_xf_eq, hXf_roots, ← hss_f_eq, ← Multiset.coe_add]; simp [add_comm]
        have hsorted_concat : (ss_f ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by
          rw [List.pairwise_append]
          exact ⟨hss_f_sorted, List.pairwise_singleton _ _, fun a ha _ hb => by
            simp only [List.mem_singleton] at hb; rw [hb]
            exact hf_nonpos a (by rw [← hss_f_eq]; exact Multiset.mem_coe.mpr ha)⟩
        exact List.Perm.eq_of_pairwise' hrs_xf hsorted_concat
          (Multiset.coe_eq_coe.mp hmultiset_eq)
      rw [hrs_xf_is] at halt
      have hlen' : ss_f.length + 1 = ss_g.length := by
        have : ss_g.length = g.natDegree := by rw [← Multiset.coe_card, hss_g_eq, hg.2]
        have : ss_f.length = f.natDegree := by
          show (f.roots.sort (· ≤ ·)).length = _; rw [Multiset.length_sort, hf.2]
        omega
      exact ⟨hf, hg, ss_f, ss_g, hss_f_sorted, hss_g, hss_f_eq, hss_g_eq,
        Or.inl ⟨by omega, listInterlaces_of_listAlternates_append_zero ss_f ss_g hlen' halt⟩⟩

end RealRooted
