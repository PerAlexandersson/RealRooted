import RealRooted.Bezoutian

/-!
# Global forward Wronskian bridge

The existing library proves the reverse direction (global Wronskian positivity implies
interlacing: `StrictPrecSameDegree.of_wronskian_pos`, `prec_of_wronskian_pos_succ`)
and the forward direction at roots only
(`Polynomial.wronskian_at_root_pos_of_interlacing`).

This file provides the missing global forward bridge:

* `RealRooted.wronskian_pos_of_strictPrecSameDegree`: for a strictly
  interlacing same-degree pair (positive leading coefficients, degree at least
  one), the Wronskian `q' * p - q * p'` is positive everywhere on `ℝ`.
* `RealRooted.wronskian_pos_of_prec_succ`: for a strict differ-by-one pair
  (`Prec q p`, `deg p = deg q + 1`, simple roots, no common root), the
  Wronskian `p' * q - p * q'` is positive everywhere on `ℝ`.

The same-degree case follows from the Bezoutian characterization
`strictPrecSameDegree_iff_bezoutMatrix_posDef` combined with
`bezoutMatrix.wronskian_pos_of_posDef`.  The differ-by-one case reduces to the
same-degree case by padding `q` with a linear factor whose root lies above
(respectively below) every root of `p`, and adding the two resulting global
inequalities.
-/

open Polynomial

namespace RealRooted

/-- **Global forward Wronskian bridge, same degree.**  If `p` strictly
interlaces `q` (same degree at least one, both with positive leading
coefficient), then the Wronskian `q' * p - q * p'` is positive everywhere. -/
theorem wronskian_pos_of_strictPrecSameDegree {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hq_deg_pos : 0 < q.natDegree)
    (h : StrictPrecSameDegree p q) (t : ℝ) :
    0 < q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t := by
  obtain ⟨n, hn⟩ : ∃ n, q.natDegree = n + 1 := ⟨q.natDegree - 1, by lia⟩
  have hp_deg : p.natDegree = n + 1 := h.2.2.1.trans hn
  exact bezoutMatrix.wronskian_pos_of_posDef hn.le hp_deg.le
    ((strictPrecSameDegree_iff_bezoutMatrix_posDef hp_pos hq_pos hp_deg hn).mp h) t

/-- A finite certificate for global Wronskian positivity. If `p` splits with
degree `d + 1` and `q' * p - q * p'` is positive at every root of `p`, then it
is positive on all of `ℝ`.

At a root of `p`, this certificate forces that root to be simple. The Bezout
matrix is consequently congruent, through the Vandermonde matrix of the roots,
to a positive diagonal matrix. Its positive definiteness gives the global
conclusion. -/
theorem wronskian_pos_of_pos_at_roots {d : ℕ} {p q : ℝ[X]}
    (hp_splits : p.Splits) (hp_deg : p.natDegree = d + 1)
    (hq_deg : q.natDegree ≤ d + 1)
    (hW : ∀ r : ℝ, p.IsRoot r →
      0 < q.derivative.eval r * p.eval r - q.eval r * p.derivative.eval r) :
    ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t := by
  have hnodup : p.roots.Nodup := by
    apply Polynomial.roots_nodup_of_splits_and_simple
    intro r hr hd
    have hWr := hW r hr
    rw [Polynomial.IsRoot.def] at hr hd
    rw [hr, hd] at hWr
    simp at hWr
  obtain ⟨s, hs_mono, hs_roots⟩ :=
    Polynomial.exists_strictMono_roots hp_splits hp_deg hnodup
  have h_v_eq := bezoutMatrix.vandermonde_eq_diagonal q p (d + 1) s hq_deg
    (le_of_eq hp_deg) (fun k => hs_roots k) hs_mono.injective
  have hPD : (bezoutMatrix (d + 1) q p).PosDef := by
    refine Matrix.PosDef.of_congruent_to_diagonal
      (fun k => hW (s k) (hs_roots k)) ?_ h_v_eq
    simp_all [Matrix.det_vandermonde, Finset.prod_eq_zero_iff, sub_eq_zero,
      hs_mono.injective.eq_iff]
  exact bezoutMatrix.wronskian_pos_of_posDef hq_deg (le_of_eq hp_deg) hPD

/-- Indexed bounds extracted from a differ-by-one `ListInterlaces`:
`rs[k] ≤ ss[k] ≤ rs[k+1]`. -/
lemma listInterlaces_getElem_le {ss rs : List ℝ}
    (h : ListInterlaces ss rs) (hlen : ss.length + 1 = rs.length) :
    ∀ k, (hk : k < ss.length) →
      rs[k]'(by lia) ≤ ss[k]'hk ∧ ss[k]'hk ≤ rs[k + 1]'(by lia) := by
  induction ss generalizing rs with
  | nil => intro k hk; simp at hk
  | cons a ss ih =>
    intro k hk
    rcases rs with _ | ⟨r₁, _ | ⟨r₂, rs'⟩⟩
    · simp [ListInterlaces] at h
    · simp [ListInterlaces] at h
    · obtain ⟨h1, h2, htail⟩ := h
      have hlen' : ss.length + 1 = (r₂ :: rs').length := by
        simpa using hlen
      match k with
      | 0 => exact ⟨h1, h2⟩
      | k + 1 =>
        have hk' : k < ss.length := by simpa using hk
        simpa using ih htail hlen' k hk'

/-- **Global forward Wronskian bridge, degree gap one.**  If `q` strictly
interlaces `p` in the differ-by-one sense (`Prec q p` with
`deg p = deg q + 1`, all roots simple and no common root), then the Wronskian
`p' * q - p * q'` is positive everywhere. -/
theorem wronskian_pos_of_prec_succ {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg_succ : p.natDegree = q.natDegree + 1)
    (hprec : Prec q p)
    (hp_nodup : p.roots.Nodup) (hq_nodup : q.roots.Nodup)
    (hdisj : ∀ x : ℝ, p.IsRoot x → ¬ q.IsRoot x)
    (t : ℝ) :
    0 < p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t := by
  obtain ⟨⟨hq_ne, hq_splits⟩, ⟨hp_ne, hp_splits⟩, ss, rs,
    hss_sorted, hrs_sorted, hss_coe, hrs_coe, hbranch⟩ := hprec
  set n := q.natDegree with hn
  have hp_deg : p.natDegree = n + 1 := hp_deg_succ
  have hss_len : ss.length = n := by
    have h1 : (↑ss : Multiset ℝ).card = q.roots.card := congrArg Multiset.card hss_coe
    rwa [Multiset.coe_card, card_roots_of_splits hq_splits] at h1
  have hrs_len : rs.length = n + 1 := by
    have h1 : (↑rs : Multiset ℝ).card = p.roots.card := congrArg Multiset.card hrs_coe
    rwa [Multiset.coe_card, card_roots_of_splits hp_splits, hp_deg] at h1
  have hinter : ListInterlaces ss rs := by
    rcases hbranch with ⟨_, h⟩ | ⟨hl, _⟩
    · exact h
    · lia
  have hlen : ss.length + 1 = rs.length := by lia
  -- sorted enumerations of the roots
  obtain ⟨s, hs_mono, hs_roots⟩ :=
    Polynomial.exists_strictMono_roots hp_splits hp_deg hp_nodup
  obtain ⟨r, hr_mono, hr_roots⟩ :=
    Polynomial.exists_strictMono_roots hq_splits hn.symm hq_nodup
  have hs_surj : ∀ x ∈ p.roots, ∃ i, s i = x :=
    fun x hx ↦ exists_index_eq_of_mem_roots s hs_mono hs_roots hp_ne hp_deg.le x hx
  have hr_surj : ∀ x ∈ q.roots, ∃ i, r i = x :=
    fun x hx ↦ exists_index_eq_of_mem_roots r hr_mono hr_roots hq_ne (le_of_eq hn.symm) x hx
  -- identify the sorted lists with the enumerations
  have hrs_eq : rs = List.ofFn s := by
    have hperm : List.Perm rs (p.roots.sort (· ≤ ·)) :=
      Multiset.coe_eq_coe.mp (by rw [hrs_coe, Multiset.sort_eq])
    have hsorted2 : (p.roots.sort (· ≤ ·)).Pairwise (· ≤ ·) := by simp
    have h1 : rs = p.roots.sort (· ≤ ·) :=
      List.Perm.eq_of_sortedLE hrs_sorted.sortedLE hsorted2.sortedLE hperm
    rw [h1, Polynomial.roots_sort_eq_ofFn hp_ne hp_splits hp_deg hp_nodup s hs_mono hs_surj]
  have hss_eq : ss = List.ofFn r := by
    have hperm : List.Perm ss (q.roots.sort (· ≤ ·)) :=
      Multiset.coe_eq_coe.mp (by rw [hss_coe, Multiset.sort_eq])
    have hsorted2 : (q.roots.sort (· ≤ ·)).Pairwise (· ≤ ·) := by simp
    have h1 : ss = q.roots.sort (· ≤ ·) :=
      List.Perm.eq_of_sortedLE hss_sorted.sortedLE hsorted2.sortedLE hperm
    rw [h1, Polynomial.roots_sort_eq_ofFn hq_ne hq_splits hn.symm hq_nodup r hr_mono hr_surj]
  -- the strict interlacing chain  s₀ < r₀ < s₁ < ⋯ < r_{n-1} < s_n
  subst hss_eq
  subst hrs_eq
  have hchain : ∀ j, (hj : j < n) →
      s ⟨j, by lia⟩ < r ⟨j, hj⟩ ∧ r ⟨j, hj⟩ < s ⟨j + 1, by lia⟩ := by
    intro j hj
    have hk : j < (List.ofFn r).length := by simpa using hj
    obtain ⟨hle1, hle2⟩ := listInterlaces_getElem_le hinter hlen j hk
    simp only [List.getElem_ofFn] at hle1 hle2
    refine ⟨lt_of_le_of_ne hle1 ?_, lt_of_le_of_ne hle2 ?_⟩
    · intro he
      exact hdisj _ (hs_roots _) (he ▸ hr_roots _)
    · intro he
      exact hdisj _ (hs_roots _) (he ▸ hr_roots _)
  -- padding points above and below everything
  set M : ℝ := max t (s (Fin.last n)) + 1 with hM_def
  set m : ℝ := min t (s 0) - 1 with hm_def
  have htM : t < M := by
    have := le_max_left t (s (Fin.last n)); simp only [hM_def]; linarith
  have hmt : m < t := by
    have := min_le_left t (s 0); simp only [hm_def]; linarith
  have hsM : ∀ k : Fin (n + 1), s k < M := by
    intro k
    have h1 : s k ≤ s (Fin.last n) := hs_mono.monotone (Fin.le_last k)
    have h2 := le_max_right t (s (Fin.last n))
    simp only [hM_def]; linarith
  have hms : ∀ k : Fin (n + 1), m < s k := by
    intro k
    have h1 : s 0 ≤ s k := hs_mono.monotone (Fin.zero_le k)
    have h2 := min_le_right t (s 0)
    simp only [hm_def]; linarith
  have hrM : ∀ k : Fin n, r k < M := by
    intro k
    have h1 := (hchain k.val k.isLt).2
    exact lt_trans h1 (hsM _)
  have hmr : ∀ k : Fin n, m < r k := by
    intro k
    have h1 := (hchain k.val k.isLt).1
    exact lt_trans (hms _) h1
  -- the upper-padded companion  q * (X - M)
  have hXM_ne : (X - C M : ℝ[X]) ≠ 0 := X_sub_C_ne_zero M
  have hqp_ne : q * (X - C M) ≠ 0 := mul_ne_zero hq_ne hXM_ne
  have hqp_splits : (q * (X - C M)).Splits := hq_splits.mul (Splits.X_sub_C M)
  have hqp_deg : (q * (X - C M)).natDegree = n + 1 := by
    rw [natDegree_mul hq_ne hXM_ne, natDegree_X_sub_C]
  have hqp_pos : HasPosLeadingCoeff (q * (X - C M)) :=
    hq_pos.mul (hasPosLeadingCoeff_of_monic (monic_X_sub_C M))
  have hqp_roots : (q * (X - C M)).roots = q.roots + {M} := by
    rw [roots_mul hqp_ne, roots_X_sub_C]
  have hM_not_root : M ∉ q.roots := by
    intro hMr
    obtain ⟨k, hk⟩ := hr_surj M hMr
    have := hrM k
    rw [hk] at this
    exact lt_irrefl M this
  have hqp_nodup : (q * (X - C M)).roots.Nodup := by
    rw [hqp_roots]
    refine Multiset.nodup_add.mpr ⟨hq_nodup, Multiset.nodup_singleton M, ?_⟩
    simpa using hM_not_root
  set rp : Fin (n + 1) → ℝ := fun i => if h : (i : ℕ) < n then r ⟨i, h⟩ else M
    with hrp_def
  have hrp_lt : ∀ (i : Fin (n + 1)) (h : (i : ℕ) < n), rp i = r ⟨i, h⟩ := by
    intro i h; simp [hrp_def, h]
  have hrp_last : ∀ (i : Fin (n + 1)), ¬ (i : ℕ) < n → rp i = M := by
    intro i h; simp [hrp_def, h]
  have hrp_mono : StrictMono rp := by
    intro i j hij
    by_cases hjn : (j : ℕ) < n
    · have hin : (i : ℕ) < n := lt_trans hij hjn
      rw [hrp_lt i hin, hrp_lt j hjn]
      exact hr_mono hij
    · have hin : (i : ℕ) < n := by have := j.isLt; have := (Fin.lt_def.mp hij); lia
      rw [hrp_lt i hin, hrp_last j hjn]
      exact hrM _
  have hrp_roots : ∀ i, (q * (X - C M)).IsRoot (rp i) := by
    intro i
    by_cases hin : (i : ℕ) < n
    · rw [hrp_lt i hin]
      have h0 : q.eval (r ⟨i, hin⟩) = 0 := hr_roots ⟨i, hin⟩
      simp [IsRoot.def, eval_mul, h0]
    · rw [hrp_last i hin]
      simp [IsRoot.def, eval_mul]
  have hrp_surj : ∀ x ∈ (q * (X - C M)).roots, ∃ i, rp i = x := by
    intro x hx
    rw [hqp_roots, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · obtain ⟨k, hk⟩ := hr_surj x hx
      refine ⟨k.castSucc, ?_⟩
      rw [hrp_lt k.castSucc (by simp)]
      simpa using hk
    · refine ⟨Fin.last n, ?_⟩
      rw [hrp_last (Fin.last n) (by simp)]
      exact (Multiset.mem_singleton.mp hx).symm
  have hprec_up : StrictPrecSameDegree p (q * (X - C M)) := by
    refine StrictPrecSameDegree.of_fin_interlacing s rp hs_mono hrp_mono ?_ ?_
      p (q * (X - C M)) hp_ne hqp_ne hp_splits hqp_splits hp_deg hqp_deg
      hp_nodup hqp_nodup hs_surj hrp_surj
    · intro k
      by_cases hkn : (k : ℕ) < n
      · rw [hrp_lt k hkn]
        exact (hchain k.val hkn).1
      · rw [hrp_last k hkn]
        exact hsM k
    · intro i j hij
      have hin : (i : ℕ) < n := by have := j.isLt; have := (Fin.lt_def.mp hij); lia
      rw [hrp_lt i hin]
      calc r ⟨i, hin⟩ < s ⟨(i : ℕ) + 1, by lia⟩ := (hchain i.val hin).2
        _ ≤ s j := hs_mono.monotone (by simpa [Fin.le_def] using Fin.lt_def.mp hij)
  -- the lower-padded companion  q * (X - m)
  have hXm_ne : (X - C m : ℝ[X]) ≠ 0 := X_sub_C_ne_zero m
  have hqm_ne : q * (X - C m) ≠ 0 := mul_ne_zero hq_ne hXm_ne
  have hqm_splits : (q * (X - C m)).Splits := hq_splits.mul (Splits.X_sub_C m)
  have hqm_deg : (q * (X - C m)).natDegree = n + 1 := by
    rw [natDegree_mul hq_ne hXm_ne, natDegree_X_sub_C]
  have hqm_pos : HasPosLeadingCoeff (q * (X - C m)) :=
    hq_pos.mul (hasPosLeadingCoeff_of_monic (monic_X_sub_C m))
  have hqm_roots : (q * (X - C m)).roots = q.roots + {m} := by
    rw [roots_mul hqm_ne, roots_X_sub_C]
  have hm_not_root : m ∉ q.roots := by
    intro hmem
    obtain ⟨k, hk⟩ := hr_surj m hmem
    have := hmr k
    rw [hk] at this
    exact lt_irrefl m this
  have hqm_nodup : (q * (X - C m)).roots.Nodup := by
    rw [hqm_roots]
    refine Multiset.nodup_add.mpr ⟨hq_nodup, Multiset.nodup_singleton m, ?_⟩
    simpa using hm_not_root
  set rm : Fin (n + 1) → ℝ := fun i =>
      if h : (i : ℕ) = 0 then m else r ⟨(i : ℕ) - 1, by have := i.isLt; lia⟩
    with hrm_def
  have hrm_eq_m : ∀ i : Fin (n + 1), (i : ℕ) = 0 → rm i = m := by
    intro i h
    simp only [hrm_def]
    rw [dif_pos h]
  have hrm_zero : rm 0 = m := hrm_eq_m 0 rfl
  have hrm_pos : ∀ (i : Fin (n + 1)) (h : (i : ℕ) ≠ 0),
      rm i = r ⟨(i : ℕ) - 1, by have := i.isLt; lia⟩ := by
    intro i h
    simp only [hrm_def]
    rw [dif_neg h]
  have hrm_mono : StrictMono rm := by
    intro i j hij
    have hj0 : (j : ℕ) ≠ 0 := by have := Fin.lt_def.mp hij; lia
    rw [hrm_pos j hj0]
    by_cases hi0 : (i : ℕ) = 0
    · rw [hrm_eq_m i hi0]
      exact hmr _
    · rw [hrm_pos i hi0]
      exact hr_mono (by simp only [Fin.lt_def]; have := Fin.lt_def.mp hij; lia)
  have hrm_roots : ∀ i, (q * (X - C m)).IsRoot (rm i) := by
    intro i
    by_cases hi0 : (i : ℕ) = 0
    · rw [hrm_eq_m i hi0]
      simp [IsRoot.def, eval_mul]
    · rw [hrm_pos i hi0]
      have h0 : q.eval (r ⟨(i : ℕ) - 1, by have := i.isLt; lia⟩) = 0 := hr_roots _
      simp [IsRoot.def, eval_mul, h0]
  have hrm_surj : ∀ x ∈ (q * (X - C m)).roots, ∃ i, rm i = x := by
    intro x hx
    rw [hqm_roots, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · obtain ⟨k, hk⟩ := hr_surj x hx
      refine ⟨k.succ, ?_⟩
      rw [hrm_pos k.succ (by simp)]
      simpa using hk
    · exact ⟨0, by rw [hrm_zero]; exact (Multiset.mem_singleton.mp hx).symm⟩
  have hprec_lo : StrictPrecSameDegree (q * (X - C m)) p := by
    refine StrictPrecSameDegree.of_fin_interlacing rm s hrm_mono hs_mono ?_ ?_
      (q * (X - C m)) p hqm_ne hp_ne hqm_splits hp_splits hqm_deg hp_deg
      hqm_nodup hp_nodup hrm_surj hs_surj
    · intro k
      by_cases hk0 : (k : ℕ) = 0
      · rw [hrm_eq_m k hk0]
        exact hms k
      · rw [hrm_pos k hk0]
        have hlt : (k : ℕ) - 1 < n := by have := k.isLt; lia
        have h2 := (hchain ((k : ℕ) - 1) hlt).2
        have hkeq : ((k : ℕ) - 1) + 1 = (k : ℕ) := by lia
        calc r ⟨(k : ℕ) - 1, _⟩ < s ⟨((k : ℕ) - 1) + 1, by lia⟩ := h2
          _ = s k := by congr 1; exact Fin.ext (by simpa using hkeq)
    · intro i j hij
      have hj0 : (j : ℕ) ≠ 0 := by have := Fin.lt_def.mp hij; lia
      rw [hrm_pos j hj0]
      have hin : (i : ℕ) < n := by
        have := j.isLt; have := Fin.lt_def.mp hij; lia
      calc s i = s ⟨(i : ℕ), by lia⟩ := rfl
        _ < r ⟨(i : ℕ), hin⟩ := (hchain i.val hin).1
        _ ≤ r ⟨(j : ℕ) - 1, by have := j.isLt; lia⟩ := by
            apply hr_mono.monotone
            simp only [Fin.le_def]
            have := Fin.lt_def.mp hij; lia
  -- apply the same-degree bridge to both companions and combine
  have hW_up := wronskian_pos_of_strictPrecSameDegree hp_pos hqp_pos
    (by lia) hprec_up t
  have hW_lo := wronskian_pos_of_strictPrecSameDegree hqm_pos hp_pos
    (by lia) hprec_lo t
  have e1 : (q * (X - C M)).derivative.eval t =
      q.derivative.eval t * (t - M) + q.eval t := by
    simp only [derivative_mul, derivative_X_sub_C, mul_one, eval_add, eval_mul,
      eval_sub, eval_X, eval_C]
  have e2 : (q * (X - C M)).eval t = q.eval t * (t - M) := by
    simp only [eval_mul, eval_sub, eval_X, eval_C]
  have e3 : (q * (X - C m)).derivative.eval t =
      q.derivative.eval t * (t - m) + q.eval t := by
    simp only [derivative_mul, derivative_X_sub_C, mul_one, eval_add, eval_mul,
      eval_sub, eval_X, eval_C]
  have e4 : (q * (X - C m)).eval t = q.eval t * (t - m) := by
    simp only [eval_mul, eval_sub, eval_X, eval_C]
  rw [e1, e2] at hW_up
  rw [e3, e4] at hW_lo
  nlinarith [hW_up, hW_lo, htM, hmt]

end RealRooted
