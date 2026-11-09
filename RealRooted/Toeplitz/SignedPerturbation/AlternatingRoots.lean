module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import RealRooted.Basic.ProperPosition
public import RealRooted.SimpleRoots
import RealRooted.MaWang.StrictSigns.Assembly

/-!
# Polynomials with prescribed alternating sign pattern

A monic polynomial `f` of degree `n` with `n` prescribed roots `r 1 > … > r n` is real-rooted with
simple roots.  A polynomial `F` of smaller degree whose values at consecutive roots have opposite
signs strictly interlaces `f` and has no root in common with `f`.
-/

@[expose] public section

open Polynomial

noncomputable section


namespace RealRooted.ToeplitzPerturbation

section Alternating

variable {f F : ℝ[X]} {n : ℕ}

/-- The increasing list `r n, r (n - 1), …, r 1` of the prescribed roots. -/
def increasingRoots (r : ℕ → ℝ) (n : ℕ) : List ℝ :=
  (List.range n).map fun i => r (n - i)

theorem increasingRoots_pairwise {r : ℕ → ℝ}
    (hanti : ∀ i j, 1 ≤ i → i < j → j ≤ n → r j < r i) :
    (increasingRoots r n).Pairwise (· < ·) := by
  unfold increasingRoots
  rw [List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < n := by simpa using hi
  have hj' : j < n := by simpa using hj
  simp only [List.getElem_range]
  exact hanti (n - j) (n - i) (by lia) (by lia) (by lia)

theorem roots_eq_of_distinct_roots (hf : f.IsMonicOfDegree n) (r : ℕ → ℝ)
    (hanti : ∀ i j, 1 ≤ i → i < j → j ≤ n → r j < r i)
    (hroot : ∀ j, 1 ≤ j → j ≤ n → f.IsRoot (r j)) :
    f.roots = ↑(increasingRoots r n) := by
  have hnd : (increasingRoots r n).Nodup := (increasingRoots_pairwise hanti).imp ne_of_lt
  have hsub : (↑(increasingRoots r n) : Multiset ℝ) ≤ f.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnd)]
    intro x hx
    simp only [increasingRoots, Multiset.mem_coe, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [mem_roots hf.ne_zero]
    exact hroot _ (by lia) (by lia)
  symm
  refine Multiset.eq_of_le_of_card_le hsub ?_
  simp only [Multiset.coe_card, increasingRoots, List.length_map, List.length_range]
  have := card_roots' f
  rw [hf.natDegree_eq] at this
  exact this

/-- A monic polynomial of degree `n` with prescribed decreasing roots `r 1 > … > r n` is
real-rooted with simple roots, and a lower-degree polynomial changing sign between consecutive
roots interlaces it. -/
theorem splits_and_strictInterl_of_alternating (hf : f.IsMonicOfDegree n) (hFn : F.natDegree < n)
    (hF : F ≠ 0) (r : ℕ → ℝ) (hanti : ∀ i j, 1 ≤ i → i < j → j ≤ n → r j < r i)
    (hroot : ∀ j, 1 ≤ j → j ≤ n → f.IsRoot (r j))
    (hsign : ∀ j, 1 ≤ j → j < n → F.eval (r j) * F.eval (r (j + 1)) < 0)
    (hne : ∀ j, 1 ≤ j → j ≤ n → F.eval (r j) ≠ 0) :
    f.Splits ∧ HasSimpleRoots f ∧ StrictInterl F f ∧ ∀ x, f.IsRoot x → F.eval x ≠ 0 := by
  have hroots := roots_eq_of_distinct_roots hf r hanti hroot
  have hnd : (increasingRoots r n).Nodup := (increasingRoots_pairwise hanti).imp ne_of_lt
  have hsplit : f.Splits := by
    rw [splits_iff_card_roots, hroots, hf.natDegree_eq]
    simp [increasingRoots]
  refine ⟨hsplit, ?_, ?_, ?_⟩
  · intro x hx
    rw [← count_roots, hroots, Multiset.coe_count]
    refine List.count_eq_one_of_mem hnd ?_
    rw [← Multiset.mem_coe, ← hroots, mem_roots hf.ne_zero]
    exact hx
  · refine Interlaces.toStrictInterl ?_
    refine RealRooted.MaWang.interlaces_of_consecutive_signs_of_natDegree_lt hf.ne_zero hsplit hF
      (by rw [hf.natDegree_eq]; exact hFn) ?_
    have hperm : (f.roots.sort (· ≤ ·)).Perm (increasingRoots r n) := by
      rw [← Multiset.coe_eq_coe, Multiset.sort_eq, hroots]
    have hsort : f.roots.sort (· ≤ ·) = increasingRoots r n :=
      List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _)
        ((increasingRoots_pairwise hanti).imp le_of_lt) hperm
    simp only [hsort]
    have hchain : List.IsChain (fun a b => F.eval a * F.eval b < 0) (increasingRoots r n) := by
      rw [List.isChain_iff_getElem]
      intro i hi
      have hi' : i + 1 < n := by simpa [increasingRoots] using hi
      simp only [increasingRoots, List.getElem_map, List.getElem_range]
      have := hsign (n - (i + 1)) (by lia) (by lia)
      rw [show n - (i + 1) + 1 = n - i by lia] at this
      linarith
    intro pre a b rest h
    exact List.isChain_iff_forall_rel_of_append_cons_cons.mp hchain h
  · intro x hx
    have hx' : x ∈ f.roots := (mem_roots hf.ne_zero).mpr hx
    rw [hroots] at hx'
    simp only [increasingRoots, Multiset.mem_coe, List.mem_map, List.mem_range] at hx'
    obtain ⟨i, hi, rfl⟩ := hx'
    exact hne _ (by lia) (by lia)

end Alternating

end RealRooted.ToeplitzPerturbation
