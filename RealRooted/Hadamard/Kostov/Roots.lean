module

public import RealRooted.Hadamard.Kostov.Eigen
public import RealRooted.Hadamard.Kostov.Interlacing
public import RealRooted.Bezoutian.WronskianConverse
public import RealRooted.Wronskian.Successor.Interlacing

public section

open Polynomial

noncomputable section

namespace RealRooted
namespace Kostov

private theorem eigenpoly_roots_simple_pos {n j : ℕ} (hj : j + 3 ≤ n) {Q : ℝ[X]}
    (hQ : IsEigenpoly n j Q) :
    Q.roots.Nodup ∧ Q.roots.card = j ∧ ∀ r ∈ Q.roots, 0 < r := by
  obtain ⟨w, hinj, hpos, rfl⟩ := isEigenpoly_eq_prod hj hQ
  rw [roots_prod_fin_X_sub_C]
  refine ⟨Multiset.Nodup.map hinj Finset.univ.nodup, by simp, fun r hr => ?_⟩
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hr
  exact hpos i

/-- Consequently `Q` splits over `ℝ`. -/
private theorem eigenpoly_splits {n j : ℕ} (hj : j + 3 ≤ n) {Q : ℝ[X]}
    (hQ : IsEigenpoly n j Q) :
    Q.Splits := by
  rw [splits_iff_card_roots, (eigenpoly_roots_simple_pos hj hQ).2.1, hQ.2.1]

/-! ### Interlacing of consecutive eigenpolynomials -/


/-- **Kostov, Theorem 3 (#1319): consecutive strict interlacing.**  For `1 ≤ j ≤ n - 4` the
roots `x_1 < ... < x_j` of `Q_{n,j}` and `y_1 < ... < y_{j+1}` of `Q_{n,j+1}` satisfy
`y_1 < x_1 < y_2 < ... < x_j < y_{j+1}` (checked exactly for `n ≤ 10`).
(The hypothesis `hj1` turned out not to be needed by the proof; for `j = 0` the claim is
vacuous in `x`.) -/
private theorem eigenpoly_strict_interlacing {n j : ℕ} (_hj1 : 1 ≤ j) (hj : j + 4 ≤ n)
    {Q R : ℝ[X]} (hQ : IsEigenpoly n j Q) (hR : IsEigenpoly n (j + 1) R) :
    ∃ (x : Fin j → ℝ) (y : Fin (j + 1) → ℝ), StrictMono x ∧ StrictMono y ∧
      (∀ i, Q.IsRoot (x i)) ∧ (∀ i, R.IsRoot (y i)) ∧
      ∀ i : Fin j, y i.castSucc < x i ∧ x i < y i.succ := by
  obtain ⟨z, hz, hz01, hGz⟩ := eigPoly_eq_prod_sorted n (j + 2) (by lia) (by lia)
  obtain ⟨u, hu, hu01, hGu⟩ := eigPoly_eq_prod_sorted n (j + 1 + 2) (by lia) (by lia)
  have hQe := isEigenpoly_eq_prod_of (by lia) hQ z hz01 hGz
  have hRe := isEigenpoly_eq_prod_of (by lia) hR u hu01 hGu
  have hbet : ∀ i : Fin j, ∃ l, u i.castSucc < z l ∧ z l < u i.succ := by
    intro i
    have hgroot : ∀ l, (eigPoly n (j + 2 + 1)).eval (u l) = 0 := by
      intro l
      rw [show j + 2 + 1 = j + 1 + 2 from rfl, hGu, eval_mul,
        eval_prod, Finset.prod_eq_zero (Finset.mem_univ l) (by simp), mul_zero]
    obtain ⟨t, ht1, ht2, hft⟩ := zero_between n (j + 2) (by lia) (by lia) (u i.castSucc)
      (u i.succ) (hu01 _).1 (hu (Fin.castSucc_lt_succ (i := i))) (hu01 _).2 (hgroot _) (hgroot _)
    rw [hGz] at hft
    simp only [eval_mul, eval_X, eval_sub, eval_C, eval_prod] at hft
    have ht0 : 0 < t := lt_trans (hu01 _).1 ht1
    have htl : t < 1 := lt_trans ht2 (hu01 _).2
    have htt : t * (t - 1) ≠ 0 := mul_ne_zero ht0.ne' (sub_ne_zero.mpr htl.ne)
    obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.mp ((mul_eq_zero.mp hft).resolve_left htt)
    rw [sub_eq_zero] at hl
    exact ⟨l, hl ▸ ht1, hl ▸ ht2⟩
  have hint := interlace_of_between z u hz hu hbet
  refine ⟨fun i => z i / (1 - z i), fun i => u i / (1 - u i), fun a b h => moebius_lt (hz h)
    (hz01 b).2, fun a b h => moebius_lt (hu h) (hu01 b).2, fun i => ?_, fun i => ?_,
    fun i => ⟨moebius_lt (hint i).1 (hz01 i).2, moebius_lt (hint i).2 (hu01 _).2⟩⟩
  · rw [hQe, IsRoot, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  · rw [hRe, IsRoot, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- The canonical reduced polynomial is an eigenpolynomial in the sense used internally here. -/
theorem eigenpolynomial_isEigenpoly (n j : ℕ) (hj : j + 3 ≤ n) :
    IsEigenpoly n j (eigenpolynomial n j) :=
  ⟨eigenpolynomial_monic n j hj, natDegree_eigenpolynomial n j hj,
    eigenpolynomial_hasEigenvector n j hj⟩

/-- The canonical reduced eigenpolynomial has simple positive roots. -/
theorem eigenpolynomial_roots_simple_pos (n j : ℕ) (hj : j + 3 ≤ n) :
    (eigenpolynomial n j).roots.Nodup ∧ (eigenpolynomial n j).roots.card = j ∧
      ∀ r ∈ (eigenpolynomial n j).roots, 0 < r :=
  eigenpoly_roots_simple_pos hj (eigenpolynomial_isEigenpoly n j hj)

/-- The canonical reduced eigenpolynomial splits over the reals. -/
theorem eigenpolynomial_splits (n j : ℕ) (hj : j + 3 ≤ n) :
    (eigenpolynomial n j).Splits :=
  eigenpoly_splits hj (eigenpolynomial_isEigenpoly n j hj)

/-- Consecutive reduced eigenpolynomials strictly interlace in the repository sense. -/
theorem eigenpolynomial_strictInterl (n j : ℕ) (hj1 : 1 ≤ j) (hj : j + 4 ≤ n) :
    StrictInterl (eigenpolynomial n j) (eigenpolynomial n (j + 1)) := by
  let Q := eigenpolynomial n j
  let R := eigenpolynomial n (j + 1)
  have hQ := eigenpolynomial_isEigenpoly n j (by lia)
  have hR := eigenpolynomial_isEigenpoly n (j + 1) (by lia)
  change IsEigenpoly n j Q at hQ
  change IsEigenpoly n (j + 1) R at hR
  obtain ⟨x, y, hx, hy, hxroot, hyroot, hgap⟩ :=
    eigenpoly_strict_interlacing hj1 hj hQ hR
  have hQne : Q ≠ 0 := (eigenpolynomial_monic n j (by lia)).ne_zero
  have hRne : R ≠ 0 := (eigenpolynomial_monic n (j + 1) (by lia)).ne_zero
  have hQs : Q.Splits := eigenpolynomial_splits n j (by lia)
  have hRs : R.Splits := eigenpolynomial_splits n (j + 1) (by lia)
  have hQd : Q.natDegree = j := natDegree_eigenpolynomial n j (by lia)
  have hRd : R.natDegree = j + 1 := natDegree_eigenpolynomial n (j + 1) (by lia)
  have hQn : Q.roots.Nodup := (eigenpolynomial_roots_simple_pos n j (by lia)).1
  have hRn : R.roots.Nodup := (eigenpolynomial_roots_simple_pos n (j + 1) (by lia)).1
  have hQsurj : ∀ r ∈ Q.roots, ∃ i, x i = r := fun r hr =>
    exists_index_eq_of_mem_roots x hx hxroot hQne hQd.le r hr
  have hRsurj : ∀ r ∈ R.roots, ∃ i, y i = r := fun r hr =>
    exists_index_eq_of_mem_roots y hy hyroot hRne hRd.le r hr
  refine ⟨⟨hQne, hQs⟩, ⟨hRne, hRs⟩, Q.roots.sort (· ≤ ·), R.roots.sort (· ≤ ·),
    Multiset.pairwise_sort _ _, Multiset.pairwise_sort _ _, by simp [Q], by simp [R],
    Or.inl ⟨?_, ?_⟩⟩
  · rw [Multiset.length_sort, Multiset.length_sort,
      ← Splits.natDegree_eq_card_roots hQs, ← Splits.natDegree_eq_card_roots hRs, hQd, hRd]
  · rw [Polynomial.roots_sort_eq_ofFn hQne hQs hQd hQn x hx hQsurj,
      Polynomial.roots_sort_eq_ofFn hRne hRs hRd hRn y hy hRsurj]
    exact listInterlaces_ofFn_succ x y hy hgap

end Kostov
end RealRooted

