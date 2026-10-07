import RealRooted.NewtonAux

/-!
# Newton's and Maclaurin's inequalities

For a multiset `t` of `n` real numbers write `e_k = t.esymm k` and `E k = e_k / (n choose k)`.

* `RealRooted.Maclaurin.newton_normalized`: the normalized form `E (m - 1) * E (m + 1) ≤ E m ^ 2`.
* `RealRooted.Maclaurin.rpow_inv_succ_le_of_logConcave`: the abstract telescoping step.
* `RealRooted.Maclaurin.esymm_div_choose_rpow_le`: **Maclaurin's inequalities**
  `E (k + 1) ^ (1 / (k + 1)) ≤ E k ^ (1 / k)` for nonnegative `t` and `1 ≤ k < n`.

## References

* I. Newton, *Arithmetica Universalis* (1707).
* C. Maclaurin, *A second letter to Martin Folkes, Esq.*, Phil. Trans. 36 (1729).
* G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*, §2.22 (Theorems 51 and 52).
-/

open Polynomial

namespace RealRooted.Maclaurin

/-- Elementary symmetric functions of a multiset of nonnegative reals are nonnegative. -/
theorem esymm_nonneg {t : Multiset ℝ} (ht : ∀ x ∈ t, 0 ≤ x) (k : ℕ) : 0 ≤ t.esymm k := by
  refine Multiset.sum_nonneg fun x hx => ?_
  obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hx
  exact Multiset.prod_nonneg fun y hy =>
    ht y (Multiset.subset_of_le (Multiset.mem_powersetCard.mp hs).1 hy)

/-- For a multiset of nonnegative reals, `e_{k+1} > 0` forces `e_k > 0`. -/
theorem esymm_pos_of_esymm_succ_pos {t : Multiset ℝ} (ht : ∀ x ∈ t, 0 ≤ x) {k : ℕ}
    (h : 0 < t.esymm (k + 1)) : 0 < t.esymm k := by
  obtain ⟨s, hs, hpos⟩ : ∃ s ∈ t.powersetCard (k + 1), 0 < s.prod := by
    by_contra! hcon
    refine h.not_ge ((Multiset.sum_le_card_nsmul _ 0 fun x hx => ?_).trans (by simp))
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hx
    exact hcon s hs
  obtain ⟨hst, hcard⟩ := Multiset.mem_powersetCard.mp hs
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by lia : 0 < Multiset.card s)
  obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem ha
  have hs't : s' ≤ t := (Multiset.le_cons_self s' a).trans hst
  have hprod : 0 < s'.prod := by
    rw [Multiset.prod_cons] at hpos
    exact pos_of_mul_pos_right hpos (ht a (Multiset.subset_of_le hst ha))
  refine hprod.trans_le (Multiset.single_le_sum ?_ _ (Multiset.mem_map.mpr
    ⟨s', Multiset.mem_powersetCard.mpr ⟨hs't, ?_⟩, rfl⟩))
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hx
    exact Multiset.prod_nonneg fun y hy =>
      ht y (Multiset.subset_of_le (Multiset.mem_powersetCard.mp hu).1 hy)
  · simpa using hcard

/-- The abstract telescoping step of Maclaurin's inequalities: a nonnegative sequence with
`E 0 = 1`, no internal zeros and `E (m - 1) * E (m + 1) ≤ E m ^ 2` satisfies
`E (k + 1) ^ k ≤ E k ^ (k + 1)`.  See Hardy–Littlewood–Pólya, *Inequalities*, §2.22. -/
theorem pow_succ_le_pow_of_logConcave {E : ℕ → ℝ} {n : ℕ} (h0 : E 0 = 1)
    (hnn : ∀ k, 0 ≤ E k) (hpos : ∀ k, k < n → 0 < E (k + 1) → 0 < E k)
    (hlc : ∀ m, 0 < m → m < n → E (m - 1) * E (m + 1) ≤ E m ^ 2) :
    ∀ k, 0 < k → k < n → E (k + 1) ^ k ≤ E k ^ (k + 1) := by
  have key : ∀ j, j + 1 < n → E (j + 2) ^ (j + 1) ≤ E (j + 1) ^ (j + 2) := by
    intro j
    induction j with
    | zero =>
      intro hn
      have h := hlc 1 one_pos hn
      simp only [Nat.sub_self, h0, one_mul] at h
      simpa using h
    | succ j ih =>
      intro hn
      rcases (hnn (j + 3)).eq_or_lt with hc | hc
      · rw [← hc, zero_pow (by lia)]
        exact pow_nonneg (hnn _) _
      have hb : 0 < E (j + 2) := hpos (j + 2) (by lia) hc
      have hlc' : E (j + 1) * E (j + 3) ≤ E (j + 2) ^ 2 := hlc (j + 2) (by lia) (by lia)
      have h1 : E (j + 2) ^ (j + 1) * E (j + 3) ^ (j + 2) ≤
          E (j + 1) ^ (j + 2) * E (j + 3) ^ (j + 2) :=
        mul_le_mul_of_nonneg_right (ih (by lia)) (pow_nonneg (hnn _) _)
      have h2 : E (j + 1) ^ (j + 2) * E (j + 3) ^ (j + 2) ≤
          E (j + 2) ^ (j + 1) * E (j + 2) ^ (j + 3) := by
        rw [← mul_pow, ← pow_add, show j + 1 + (j + 3) = 2 * (j + 2) by ring, pow_mul]
        exact pow_le_pow_left₀ (mul_nonneg (hnn _) (hnn _)) hlc' _
      exact le_of_mul_le_mul_left (h1.trans h2) (pow_pos hb _)
  intro k hk hkn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  simpa [add_assoc] using key j (by lia)

/-- **Newton's inequality**, normalized form: for `0 < m < n`,
`E (m - 1) * E (m + 1) ≤ E m ^ 2` where `E k = e_k / (n choose k)`. -/
theorem newton_normalized (t : Multiset ℝ) {n m : ℕ} (hn : Multiset.card t = n)
    (hm0 : 0 < m) (hmn : m < n) :
    t.esymm (m - 1) / n.choose (m - 1) * (t.esymm (m + 1) / n.choose (m + 1)) ≤
      (t.esymm m / n.choose m) ^ 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hm0
  simp only [zero_add, Nat.add_sub_cancel] at hmn ⊢
  have hN := NewtonAux.newton_esymm_ineq t hn (m := j + 1) (by lia) hmn
  simp only [Nat.add_sub_cancel] at hN
  rw [show n - (j + 1) + 1 = n - j by lia] at hN
  set a := t.esymm j
  set b := t.esymm (j + 1)
  set c := t.esymm (j + 1 + 1)
  have hA : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos (by lia)
  have hB : (0 : ℝ) < n.choose (j + 1) := by exact_mod_cast Nat.choose_pos (by lia)
  have hC : (0 : ℝ) < n.choose (j + 1 + 1) := by exact_mod_cast Nat.choose_pos (by lia)
  have hd : (0 : ℝ) < ((n - (j + 1) : ℕ) : ℝ) := by exact_mod_cast (by lia : 0 < n - (j + 1))
  have hAB : (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) = n.choose j * ((n - j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n j
  have hBC : (n.choose (j + 1 + 1) : ℝ) * ((j + 1 + 1 : ℕ) : ℝ) =
      n.choose (j + 1) * ((n - (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n (j + 1)
  rw [div_mul_div_comm, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  refine le_of_mul_le_mul_right ?_ (mul_pos (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ)) hd)
  push_cast at hN hAB hBC ⊢
  calc a * c * (n.choose (j + 1) : ℝ) ^ 2 * ((j + 1) * ((n - (j + 1) : ℕ) : ℝ))
      = n.choose j * n.choose (j + 1 + 1) *
          (a * c * ((j + 1 + 1) * ((n - j : ℕ) : ℝ))) := by
        linear_combination a * c * (n.choose (j + 1) : ℝ) * ((n - (j + 1) : ℕ) : ℝ) * hAB -
          a * c * (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) * hBC
    _ ≤ n.choose j * n.choose (j + 1 + 1) * (b ^ 2 * ((j + 1) * ((n - (j + 1) : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ = b ^ 2 * (n.choose j * n.choose (j + 1 + 1)) * ((j + 1) * ((n - (j + 1) : ℕ) : ℝ)) := by
        ring

/-- Maclaurin's telescoping step for an abstract log-concave sequence: if `E` is nonnegative,
`E 0 = 1`, has no internal zeros and satisfies `E (m - 1) * E (m + 1) ≤ E m ^ 2` for
`0 < m < n`, then `E (k + 1) ^ (1 / (k + 1)) ≤ E k ^ (1 / k)` for `0 < k < n`.

The no-internal-zeros hypothesis `hpos` cannot be dropped: `1, 0, 0, 5, 0` is log-concave in
the above sense but `5 ^ (1 / 3) > 0 ^ (1 / 2)`. -/
theorem rpow_inv_succ_le_of_logConcave {E : ℕ → ℝ} {n : ℕ} (h0 : E 0 = 1)
    (hnn : ∀ k, 0 ≤ E k) (hpos : ∀ k, k < n → 0 < E (k + 1) → 0 < E k)
    (hlc : ∀ m, 0 < m → m < n → E (m - 1) * E (m + 1) ≤ E m ^ 2) {k : ℕ} (hk : 0 < k)
    (hkn : k < n) :
    E (k + 1) ^ ((1 : ℝ) / (k + 1)) ≤ E k ^ ((1 : ℝ) / k) := by
  have hP := pow_succ_le_pow_of_logConcave h0 hnn hpos hlc k hk hkn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  calc E (k + 1) ^ ((1 : ℝ) / (k + 1))
      = (E (k + 1) ^ k) ^ ((1 : ℝ) / (k * (k + 1))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hnn _)]
        congr 1
        field_simp
    _ ≤ (E k ^ (k + 1)) ^ ((1 : ℝ) / (k * (k + 1))) :=
        Real.rpow_le_rpow (pow_nonneg (hnn _) _) hP (by positivity)
    _ = E k ^ ((1 : ℝ) / k) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hnn _)]
        congr 1
        push_cast
        field_simp

/-- **Maclaurin's inequalities.**  For a multiset `t` of `n` nonnegative reals and
`E k = e_k(t) / (n choose k)`, the sequence `E k ^ (1 / k)` is nonincreasing for `1 ≤ k ≤ n`.
See C. Maclaurin, *A second letter to Martin Folkes* (1729), and Hardy–Littlewood–Pólya,
*Inequalities*, Theorem 52. -/
theorem esymm_div_choose_rpow_le (t : Multiset ℝ) {n k : ℕ} (hn : Multiset.card t = n)
    (ht : ∀ x ∈ t, 0 ≤ x) (hk : 0 < k) (hkn : k < n) :
    (t.esymm (k + 1) / n.choose (k + 1)) ^ ((1 : ℝ) / (k + 1)) ≤
      (t.esymm k / n.choose k) ^ ((1 : ℝ) / k) := by
  set E : ℕ → ℝ := fun j => t.esymm j / n.choose j with hE
  have hnn : ∀ j, 0 ≤ E j := fun j => div_nonneg (esymm_nonneg ht j) (Nat.cast_nonneg _)
  have h0 : E 0 = 1 := by simp [hE, Multiset.esymm]
  have hpos : ∀ j, j < n → 0 < E (j + 1) → 0 < E j := by
    intro j hj h
    have h' : 0 < t.esymm (j + 1) := by
      by_contra! h''
      exact h.not_ge (div_nonpos_of_nonpos_of_nonneg h'' (Nat.cast_nonneg _))
    exact div_pos (esymm_pos_of_esymm_succ_pos ht h') (by exact_mod_cast Nat.choose_pos hj.le)
  exact rpow_inv_succ_le_of_logConcave h0 hnn hpos
    (fun m hm hmn => newton_normalized t hn hm hmn) hk hkn

end RealRooted.Maclaurin
