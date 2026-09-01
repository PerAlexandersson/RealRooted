import RealRooted.CommonInterleaver.Sequence

/-!
# Common interleavers: descending-root polynomials

Construction of a polynomial from descending prescribed roots, and the
root-slot arguments which produce right and left `Prec` witnesses.
-/

open Polynomial

noncomputable section

namespace RealRooted

private def polyOfDescRoots (xs : List ℝ) : ℝ[X] :=
  (xs.map fun r => X - C r).prod

private lemma polyOfDescRoots_ne_zero (xs : List ℝ) :
    polyOfDescRoots xs ≠ 0 := by
  unfold polyOfDescRoots
  refine List.prod_ne_zero ?_
  intro h0
  rcases List.mem_map.mp h0 with ⟨r, hr, hr0⟩
  exact (X_sub_C_ne_zero r) hr0

private lemma roots_polyOfDescRoots (xs : List ℝ) :
    (polyOfDescRoots xs).roots = (↑xs : Multiset ℝ) := by
  unfold polyOfDescRoots
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.prod_cons,
        roots_mul (mul_ne_zero (X_sub_C_ne_zero x)
          (by simpa [polyOfDescRoots] using polyOfDescRoots_ne_zero xs)),
        roots_X_sub_C, ih]
      simp

private lemma isRealRooted_polyOfDescRoots (xs : List ℝ) :
    ((polyOfDescRoots xs) ≠ 0 ∧ (polyOfDescRoots xs).Splits) := by
  unfold polyOfDescRoots
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simpa [List.map_cons, List.prod_cons] using
        isRealRooted_mul (isRealRooted_X_sub_C x).1 (isRealRooted_X_sub_C x).2 ih.1 ih.2

private lemma rootSeqDesc_polyOfDescRoots_eq
    {xs : List ℝ} (hxs : xs.Pairwise (· ≥ ·)) :
    rootSeqDesc (polyOfDescRoots xs) = xs := by
  have hrr : ((polyOfDescRoots xs) ≠ 0 ∧
    (polyOfDescRoots xs).Splits) := isRealRooted_polyOfDescRoots xs
  have hroots : (↑xs.reverse : Multiset ℝ) = (polyOfDescRoots xs).roots := by
    rw [roots_polyOfDescRoots]
    simp
  have hdesc :=
    rootSeqDesc_eq_reverse_of_pairwise
      (f := polyOfDescRoots xs)
      (rs := xs.reverse)
      (by grind)
      hroots
  simp_all

private lemma prec_of_slots_polyOfDescRoots
    {f : ℝ[X]} {xs : List ℝ} (hf₀ : f ≠ 0) (hf : f.Splits)
    (hxs : xs.Pairwise (· ≥ ·))
    (hdeg_lo : f.natDegree ≤ xs.length)
    (hdeg_hi : xs.length ≤ f.natDegree + 1)
    (hslot : ∀ j (hj : j < xs.length),
      xs.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j, by
          have : j < f.natDegree + 1 := lt_of_lt_of_le hj hdeg_hi
          simpa [hf] using this⟩) :
    Prec f (polyOfDescRoots xs) := by
  let ss : List ℝ := (rootSeqDesc f).reverse
  let rs : List ℝ := xs.reverse
  have hss_pair : ss.Pairwise (· ≤ ·) := by
    simpa [ss] using (rootSeqDesc_pairwise (f := f)).reverse
  have hrs_pair : rs.Pairwise (· ≤ ·) := by grind
  have hss_eq : (↑ss : Multiset ℝ) = f.roots := by simp [ss, rootSeqDesc, Multiset.sort_eq]
  have hrs_eq : (↑rs : Multiset ℝ) = (polyOfDescRoots xs).roots := by
    simp [rs, roots_polyOfDescRoots]
  have hpoly_rr : ((polyOfDescRoots xs) ≠ 0 ∧
    (polyOfDescRoots xs).Splits) := isRealRooted_polyOfDescRoots xs
  have hlen_cases : xs.length = f.natDegree ∨ xs.length = f.natDegree + 1 := by lia
  refine ⟨⟨hf₀, hf⟩, hpoly_rr, ss, rs, hss_pair, hrs_pair, hss_eq, hrs_eq, ?_⟩
  rcases hlen_cases with hlen | hlen
  · refine Or.inr ?_
    refine ⟨?_, ?_⟩
    · simp [ss, rs, hlen, hf]
    · refine CommonInterleaver.RootSlots.listAlternates_of_index_bounds ?_ ?_ ?_
      · simp [ss, rs, hlen, hf]
      · intro k hk
        have hk_deg : k < f.natDegree := by simpa [ss, hf] using hk
        let j : ℕ := f.natDegree - 1 - k
        have hjx : j < xs.length := by lia
        have hjf : j < (rootSeqDesc f).length + 1 := by grind
        have hmem :
            xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ := by
          grind
        have hroot_ne : rootSeqDesc f ≠ [] := by grind
        have hj_root : j < (rootSeqDesc f).length := by
          rw [rootSeqDesc_length hf]
          lia
        have hlow :
            (rootSeqDesc f).get ⟨j, hj_root⟩ ≤ xs.get ⟨j, hjx⟩ :=
          CommonInterleaver.RootSlots.rootSlot_lower_bound
            (rs := rootSeqDesc f) hroot_ne hj_root hmem
        have hss_get :
            ss.get ⟨k, hk⟩ = (rootSeqDesc f).get ⟨j, hj_root⟩ := by
          have hk_root : k < (rootSeqDesc f).length := by grind
          have hget :=
            CommonInterleaver.RootSlots.get_reverse_eq_get_sub
              (xs := rootSeqDesc f) (k := k) hk_root
          have hidx : (rootSeqDesc f).length - 1 - k = j := by rw [rootSeqDesc_length hf]
          lia
        grind
      · intro k hk
        have hk_deg : k + 1 < f.natDegree := by simpa [ss, rootSeqDesc_length hf] using hk
        let j : ℕ := f.natDegree - 1 - k
        have hj_pos : 0 < j := by lia
        have hjx : j < xs.length := by lia
        have hjf : j < (rootSeqDesc f).length + 1 := by grind
        have hmem :
            xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ := by
          grind
        have hroot_ne : rootSeqDesc f ≠ [] := by grind
        have hj_le : j ≤ (rootSeqDesc f).length := by lia
        have hup :
            xs.get ⟨j, hjx⟩ ≤ (rootSeqDesc f).get ⟨j - 1, by lia⟩ :=
          CommonInterleaver.RootSlots.rootSlot_upper_bound
            (rs := rootSeqDesc f) hroot_ne hj_pos hj_le hmem
        have hrs_get :
            rs.get ⟨k, by
              have : k < f.natDegree := by lia
              simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
              = xs.get ⟨j, hjx⟩ := by
          have hk_xs : k < xs.length := by lia
          have hget := CommonInterleaver.RootSlots.get_reverse_eq_get_sub (xs := xs) (k := k) hk_xs
          have hidx : xs.length - 1 - k = j := by
            dsimp [j]
            lia
          calc
            rs.get ⟨k, by
                have : k < f.natDegree := by lia
                simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
                = xs.get ⟨xs.length - 1 - k, by lia⟩ := by simp [rs]
            _ = xs.get ⟨j, hjx⟩ := by
                  apply congrArg (fun i => xs.get i)
                  apply Fin.ext
                  exact hidx
        have hss_get :
            ss.get ⟨k + 1, hk⟩ = (rootSeqDesc f).get ⟨j - 1, by lia⟩ := by
          have hk1_root : k + 1 < (rootSeqDesc f).length := by
            simpa [ss, rootSeqDesc_length hf] using hk
          have hget :=
            CommonInterleaver.RootSlots.get_reverse_eq_get_sub
              (xs := rootSeqDesc f) (k := k + 1) hk1_root
          have hidx : (rootSeqDesc f).length - 1 - (k + 1) = j - 1 := by
            rw [rootSeqDesc_length hf]
            dsimp [j]
            lia
          calc
            ss.get ⟨k + 1, hk⟩
                = (rootSeqDesc f).get
                  ⟨(rootSeqDesc f).length - 1 - (k + 1), by lia⟩ := by
              simp [ss]
            _ = (rootSeqDesc f).get ⟨j - 1, by lia⟩ := by
                  apply congrArg (fun i => (rootSeqDesc f).get i)
                  apply Fin.ext
                  exact hidx
        rw [hrs_get, hss_get]
        exact hup
  · refine Or.inl ?_
    refine ⟨?_, ?_⟩
    · simp [ss, rs, hlen, rootSeqDesc_length hf]
    · refine CommonInterleaver.RootSlots.listInterlaces_of_index_bounds ?_ ?_ ?_
      · simp [ss, rs, hlen, rootSeqDesc_length hf]
      · intro k hk
        have hk_deg : k < f.natDegree := by simpa [ss, rootSeqDesc_length hf] using hk
        let j : ℕ := f.natDegree - k
        have hj_pos : 0 < j := by lia
        have hjx : j < xs.length := by lia
        have hjf : j < (rootSeqDesc f).length + 1 := by grind
        have hmem :
            xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ := by
          grind
        have hroot_ne : rootSeqDesc f ≠ [] := by grind
        have hj_le : j ≤ (rootSeqDesc f).length := by lia
        have hup :
            xs.get ⟨j, hjx⟩ ≤ (rootSeqDesc f).get ⟨j - 1, by lia⟩ :=
          CommonInterleaver.RootSlots.rootSlot_upper_bound
            (rs := rootSeqDesc f) hroot_ne hj_pos hj_le hmem
        have hrs_get :
            rs.get ⟨k, by
              have : k < f.natDegree + 1 := Nat.lt_succ_of_lt hk_deg
              simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
              = xs.get ⟨j, hjx⟩ := by
          have hk_xs : k < xs.length := by lia
          have hget :=
            CommonInterleaver.RootSlots.get_reverse_eq_get_sub (xs := xs) (k := k) hk_xs
          have hidx : xs.length - 1 - k = j := by
            dsimp [j]
            lia
          calc
            rs.get ⟨k, by
                have : k < f.natDegree + 1 := Nat.lt_succ_of_lt hk_deg
                simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
                = xs.get ⟨xs.length - 1 - k, by lia⟩ := by simp [rs]
            _ = xs.get ⟨j, hjx⟩ := by
                  apply congrArg (fun i => xs.get i)
                  apply Fin.ext
                  exact hidx
        have hss_get :
            ss.get ⟨k, hk⟩ = (rootSeqDesc f).get ⟨j - 1, by lia⟩ := by
          have hk_root : k < (rootSeqDesc f).length := by simpa [ss, rootSeqDesc_length hf] using hk
          have hget :=
            CommonInterleaver.RootSlots.get_reverse_eq_get_sub
              (xs := rootSeqDesc f) (k := k) hk_root
          have hidx : (rootSeqDesc f).length - 1 - k = j - 1 := by
            rw [rootSeqDesc_length hf]
            dsimp [j]
            lia
          calc
            ss.get ⟨k, hk⟩
                = (rootSeqDesc f).get ⟨(rootSeqDesc f).length - 1 - k, by lia⟩ := by simp [ss]
            _ = (rootSeqDesc f).get ⟨j - 1, by lia⟩ := by
                  apply congrArg (fun i => (rootSeqDesc f).get i)
                  apply Fin.ext
                  exact hidx
        rw [hrs_get, hss_get]
        exact hup
      · intro k hk
        have hk_deg : k < f.natDegree := by simpa [ss, rootSeqDesc_length hf] using hk
        let j : ℕ := f.natDegree - 1 - k
        have hjx : j < xs.length := by lia
        have hjf : j < (rootSeqDesc f).length + 1 := by grind
        have hmem :
            xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ := by
          grind
        have hroot_ne : rootSeqDesc f ≠ [] := by grind
        have hj_root : j < (rootSeqDesc f).length := by grind
        have hlow :
            (rootSeqDesc f).get ⟨j, hj_root⟩ ≤ xs.get ⟨j, hjx⟩ :=
          CommonInterleaver.RootSlots.rootSlot_lower_bound
            (rs := rootSeqDesc f) hroot_ne hj_root hmem
        have hss_get :
            ss.get ⟨k, hk⟩ = (rootSeqDesc f).get ⟨j, hj_root⟩ := by
          have hk_root : k < (rootSeqDesc f).length := by grind
          have hget :=
            CommonInterleaver.RootSlots.get_reverse_eq_get_sub
              (xs := rootSeqDesc f) (k := k) hk_root
          have hidx : (rootSeqDesc f).length - 1 - k = j := by rw [rootSeqDesc_length hf]
          lia
        grind

private lemma prec_left_of_shifted_slots_polyOfDescRoots
    {f : ℝ[X]} {xs : List ℝ} (hf₀ : f ≠ 0) (hf : f.Splits)
    (hxs : xs.Pairwise (· ≥ ·))
    (hdeg_lo : xs.length ≤ f.natDegree)
    (hdeg_hi : f.natDegree ≤ xs.length + 1)
    (hslot : ∀ j (hj : j < xs.length),
      xs.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j + 1, by
          have : j < f.natDegree := lt_of_lt_of_le hj hdeg_lo
          simpa [rootSeqDesc_length hf] using Nat.succ_lt_succ this⟩) :
    Prec (polyOfDescRoots xs) f := by
  let ss : List ℝ := xs.reverse
  let rs : List ℝ := (rootSeqDesc f).reverse
  have hss_pair : ss.Pairwise (· ≤ ·) := by grind
  have hrs_pair : rs.Pairwise (· ≤ ·) := by
    simpa [rs] using (rootSeqDesc_pairwise (f := f)).reverse
  have hss_eq : (↑ss : Multiset ℝ) = (polyOfDescRoots xs).roots := by
    simp [ss, roots_polyOfDescRoots]
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := by simp [rs, rootSeqDesc, Multiset.sort_eq]
  have hpoly_rr : ((polyOfDescRoots xs) ≠ 0 ∧
    (polyOfDescRoots xs).Splits) := isRealRooted_polyOfDescRoots xs
  have hlen_cases : f.natDegree = xs.length ∨ f.natDegree = xs.length + 1 := by lia
  have sub_one_sub_lt_self : ∀ {n k : ℕ}, k < n → n - 1 - k < n := by
    intro n k hk
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
    exact lt_of_le_of_lt (Nat.sub_le (n - 1) k)
      (Nat.sub_lt hn (by decide : 0 < 1))
  have sub_one_sub_pos_of_succ_lt : ∀ {n k : ℕ}, k + 1 < n → 0 < n - 1 - k := by
    intro n k hk
    have hklt : k < n - 1 := Nat.lt_of_succ_le (Nat.le_sub_one_of_lt hk)
    exact Nat.sub_pos_of_lt hklt
  have sub_one_sub_add_one_eq_sub :
      ∀ {n k : ℕ}, k < n → n - 1 - k + 1 = n - k := by
    intro n k hk
    have hidx : n - 1 - k = n - k - 1 := by rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]
    rw [hidx]
    exact Nat.sub_add_cancel (Nat.sub_pos_of_lt hk)
  have succ_sub_one_sub_eq :
      ∀ {n k : ℕ}, k < n → (n + 1) - 1 - k = n - 1 - k + 1 := by
    intro n k hk
    calc
      (n + 1) - 1 - k = n - k := by simp
      _ = n - 1 - k + 1 := (sub_one_sub_add_one_eq_sub hk).symm
  refine ⟨hpoly_rr, ⟨hf₀, hf⟩, ss, rs, hss_pair, hrs_pair, hss_eq, hrs_eq, ?_⟩
  rcases hlen_cases with hlen | hlen
  · refine Or.inr ?_
    refine ⟨?_, ?_⟩
    · simp [ss, rs, hlen, rootSeqDesc_length hf]
    · refine CommonInterleaver.RootSlots.listAlternates_of_index_bounds ?_ ?_ ?_
      · simp [ss, rs, hlen, rootSeqDesc_length hf]
      · intro k hk
        let j : ℕ := f.natDegree - 1 - k
        have hkx : k < xs.length := by simpa [ss] using hk
        have hjx : j < xs.length := by
          dsimp [j]
          rw [hlen]
          exact sub_one_sub_lt_self hkx
        have hmem :
            xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f)
              ⟨j + 1, by
                rw [rootSeqDesc_length hf]
                dsimp [j]
                lia⟩ := by
          simpa using hslot j hjx
        have hroot_ne : rootSeqDesc f ≠ [] :=
          CommonInterleaver.rootSeqDesc_ne_nil_of_natDegree_pos hf (by lia)
        have hup :
            xs.get ⟨j, hjx⟩ ≤ (rootSeqDesc f).get ⟨j, by
              rw [rootSeqDesc_length hf]
              dsimp [j]
              lia⟩ := by
          have hraw :=
            CommonInterleaver.RootSlots.rootSlot_upper_bound
              (rs := rootSeqDesc f) hroot_ne (j := j + 1)
              (by lia)
              (by
                rw [rootSeqDesc_length hf]
                dsimp [j]
                lia)
              hmem
          simpa using hraw
        have hss_get :
            ss.get ⟨k, hk⟩ = xs.get ⟨j, hjx⟩ := by
          have hget :=
            CommonInterleaver.RootSlots.get_reverse_eq_get_sub
              (xs := xs) (k := k) (by simpa [ss] using hk)
          have hidx : xs.length - 1 - k = j := by
            dsimp [j]
            rw [hlen]
          calc
            ss.get ⟨k, hk⟩ = xs.get ⟨xs.length - 1 - k, by lia⟩ := by simp [ss]
            _ = xs.get ⟨j, hjx⟩ := by
              apply congrArg (fun i => xs.get i)
              apply Fin.ext
              exact hidx
        have hrs_get :
            rs.get ⟨k, by simpa [ss, rs, hlen, rootSeqDesc_length hf] using hk⟩ =
              (rootSeqDesc f).get ⟨j, by
                rw [rootSeqDesc_length hf]
                dsimp [j]
                lia⟩ := by
          have hk_root : k < (rootSeqDesc f).length := by
            simpa [ss, hlen, rootSeqDesc_length hf] using hk
          have hget :=
            CommonInterleaver.RootSlots.get_reverse_eq_get_sub
              (xs := rootSeqDesc f) (k := k) hk_root
          have hidx : (rootSeqDesc f).length - 1 - k = j := by rw [rootSeqDesc_length hf]
          calc
            rs.get ⟨k, by simpa [ss, rs, hlen, rootSeqDesc_length hf] using hk⟩ =
                (rootSeqDesc f).get
                  ⟨(rootSeqDesc f).length - 1 - k, by lia⟩ := by simp [rs]
            _ = (rootSeqDesc f).get ⟨j, by
                  rw [rootSeqDesc_length hf]
                  dsimp [j]
                  lia⟩ := by
                  apply congrArg (fun i => (rootSeqDesc f).get i)
                  apply Fin.ext
                  exact hidx
        rw [hss_get, hrs_get]
        exact hup
      · intro k hk
        let j : ℕ := f.natDegree - 1 - k
        have hkx_succ : k + 1 < xs.length := by simpa [ss] using hk
        have hkx : k < xs.length := Nat.lt_of_succ_lt hkx_succ
        have hkf : k < f.natDegree := by
          rw [hlen]
          exact hkx
        have hj_lt : j < xs.length := by
          dsimp [j]
          rw [hlen]
          exact sub_one_sub_lt_self hkx
        have hj_pos : 0 < j := by
          dsimp [j]
          rw [hlen]
          exact sub_one_sub_pos_of_succ_lt hkx_succ
        have hjx : j - 1 < xs.length :=
          lt_of_le_of_lt (Nat.sub_le j 1) hj_lt
        have hmem :
            xs.get ⟨j - 1, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f)
              ⟨j, by
                rw [rootSeqDesc_length hf]
                dsimp [j]
                lia⟩ := by
          have hslot' := hslot (j - 1) hjx
          simpa [Nat.sub_add_cancel hj_pos] using hslot'
        have hroot_ne : rootSeqDesc f ≠ [] :=
          CommonInterleaver.rootSeqDesc_ne_nil_of_natDegree_pos hf (by lia)
        have hlow :
            (rootSeqDesc f).get ⟨j, by
              rw [rootSeqDesc_length hf]
              dsimp [j]
              lia⟩ ≤ xs.get ⟨j - 1, hjx⟩ :=
          CommonInterleaver.RootSlots.rootSlot_lower_bound
            (rs := rootSeqDesc f) hroot_ne
            (by
              rw [rootSeqDesc_length hf]
              dsimp [j]
              lia)
            hmem
        have hrs_get :
            rs.get ⟨k, by
              simpa [rs, rootSeqDesc_length hf] using hkf⟩ =
              (rootSeqDesc f).get ⟨j, by
                rw [rootSeqDesc_length hf]
                dsimp [j]
                lia⟩ := by
          have hk_root : k < (rootSeqDesc f).length := by simpa [rootSeqDesc_length hf] using hkf
          have hidx : (rootSeqDesc f).length - 1 - k = j := by rw [rootSeqDesc_length hf]
          calc
            rs.get ⟨k, by
                simpa [rs, rootSeqDesc_length hf] using hkf⟩ =
                (rootSeqDesc f).get
                  ⟨(rootSeqDesc f).length - 1 - k, by lia⟩ := by simp [rs]
            _ = (rootSeqDesc f).get ⟨j, by
                  rw [rootSeqDesc_length hf]
                  dsimp [j]
                  lia⟩ := by
                  apply congrArg (fun i => (rootSeqDesc f).get i)
                  apply Fin.ext
                  exact hidx
        have hss_get :
            ss.get ⟨k + 1, hk⟩ = xs.get ⟨j - 1, hjx⟩ := by
          have hk_xs : k + 1 < xs.length := by simpa [ss] using hk
          have hidx : xs.length - 1 - (k + 1) = j - 1 := by
            dsimp [j]
            lia
          calc
            ss.get ⟨k + 1, hk⟩ = xs.get ⟨xs.length - 1 - (k + 1), by lia⟩ := by simp [ss]
            _ = xs.get ⟨j - 1, hjx⟩ := by
              apply congrArg (fun i => xs.get i)
              apply Fin.ext
              exact hidx
        rw [hrs_get, hss_get]
        exact hlow
  · refine Or.inl ?_
    refine ⟨?_, ?_⟩
    · simp [ss, rs, hlen, rootSeqDesc_length hf]
    · refine CommonInterleaver.RootSlots.listInterlaces_of_index_bounds ?_ ?_ ?_
      · simp [ss, rs, hlen, rootSeqDesc_length hf]
      · intro k hk
        let j : ℕ := xs.length - 1 - k
        have hkx : k < xs.length := by simpa [ss] using hk
        have hjx : j < xs.length := by
          dsimp [j]
          exact sub_one_sub_lt_self hkx
        have hmem :
            xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f)
              ⟨j + 1, by
                rw [rootSeqDesc_length hf]
                dsimp [j]
                lia⟩ := by
          simpa using hslot j hjx
        have hroot_ne : rootSeqDesc f ≠ [] :=
          CommonInterleaver.rootSeqDesc_ne_nil_of_natDegree_pos hf (by lia)
        have hlow :
            (rootSeqDesc f).get ⟨j + 1, by
              rw [rootSeqDesc_length hf]
              dsimp [j]
              lia⟩ ≤ xs.get ⟨j, hjx⟩ :=
          CommonInterleaver.RootSlots.rootSlot_lower_bound
            (rs := rootSeqDesc f) hroot_ne
            (by
              rw [rootSeqDesc_length hf]
              dsimp [j]
              lia)
            hmem
        have hrs_get :
            rs.get ⟨k, by
              have hkf : k < f.natDegree := by
                rw [hlen]
                exact Nat.lt_succ_of_lt hkx
              simpa [rs, rootSeqDesc_length hf] using hkf⟩ =
              (rootSeqDesc f).get ⟨j + 1, by
                rw [rootSeqDesc_length hf]
                dsimp [j]
                lia⟩ := by
          have hk_root : k < (rootSeqDesc f).length := by
            have hkf : k < f.natDegree := by
              rw [hlen]
              exact Nat.lt_succ_of_lt hkx
            simpa [rootSeqDesc_length hf] using hkf
          have hidx : (rootSeqDesc f).length - 1 - k = j + 1 := by
            rw [rootSeqDesc_length hf, hlen]
            dsimp [j]
            exact succ_sub_one_sub_eq hkx
          calc
            rs.get ⟨k, by
                have hkf : k < f.natDegree := by
                  rw [hlen]
                  exact Nat.lt_succ_of_lt hkx
                simpa [rs, rootSeqDesc_length hf] using hkf⟩ =
                (rootSeqDesc f).get
                  ⟨(rootSeqDesc f).length - 1 - k, by lia⟩ := by simp [rs]
            _ = (rootSeqDesc f).get ⟨j + 1, by
                  rw [rootSeqDesc_length hf]
                  dsimp [j]
                  lia⟩ := by
                  apply congrArg (fun i => (rootSeqDesc f).get i)
                  apply Fin.ext
                  exact hidx
        have hss_get :
            ss.get ⟨k, hk⟩ = xs.get ⟨j, hjx⟩ := by
          have hidx : xs.length - 1 - k = j := by dsimp [j]
          calc
            ss.get ⟨k, hk⟩ = xs.get ⟨xs.length - 1 - k, by lia⟩ := by simp [ss]
            _ = xs.get ⟨j, hjx⟩ := by
              apply congrArg (fun i => xs.get i)
              apply Fin.ext
              exact hidx
        rw [hrs_get, hss_get]
        exact hlow
      · intro k hk
        let j : ℕ := xs.length - 1 - k
        have hkx : k < xs.length := by simpa [ss] using hk
        have hjx : j < xs.length := by
          dsimp [j]
          exact sub_one_sub_lt_self hkx
        have hmem :
            xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f)
              ⟨j + 1, by
                rw [rootSeqDesc_length hf]
                dsimp [j]
                lia⟩ := by
          simpa using hslot j hjx
        have hroot_ne : rootSeqDesc f ≠ [] :=
          CommonInterleaver.rootSeqDesc_ne_nil_of_natDegree_pos hf (by lia)
        have hup :
            xs.get ⟨j, hjx⟩ ≤ (rootSeqDesc f).get ⟨j, by
              rw [rootSeqDesc_length hf]
              dsimp [j]
              lia⟩ := by
          have hraw :=
            CommonInterleaver.RootSlots.rootSlot_upper_bound
              (rs := rootSeqDesc f) hroot_ne (j := j + 1)
              (by lia)
              (by
                rw [rootSeqDesc_length hf]
                dsimp [j]
                lia)
              hmem
          simpa using hraw
        have hss_get :
            ss.get ⟨k, hk⟩ = xs.get ⟨j, hjx⟩ := by
          have hidx : xs.length - 1 - k = j := by dsimp [j]
          calc
            ss.get ⟨k, hk⟩ = xs.get ⟨xs.length - 1 - k, by lia⟩ := by simp [ss]
            _ = xs.get ⟨j, hjx⟩ := by
              apply congrArg (fun i => xs.get i)
              apply Fin.ext
              exact hidx
        have hrs_get :
            rs.get ⟨k + 1, by
              have : k + 1 < f.natDegree := by
                rw [hlen]
                exact Nat.succ_lt_succ hkx
              simpa [rs, rootSeqDesc_length hf] using this⟩ =
              (rootSeqDesc f).get ⟨j, by
                rw [rootSeqDesc_length hf]
                dsimp [j]
                lia⟩ := by
          have hk_root : k + 1 < (rootSeqDesc f).length := by
            have : k + 1 < f.natDegree := by
              rw [hlen]
              exact Nat.succ_lt_succ hkx
            simpa [rootSeqDesc_length hf] using this
          have hidx : (rootSeqDesc f).length - 1 - (k + 1) = j := by
            rw [rootSeqDesc_length hf]
            dsimp [j]
            lia
          calc
            rs.get ⟨k + 1, by
                have : k + 1 < f.natDegree := by
                  rw [hlen]
                  exact Nat.succ_lt_succ hkx
                simpa [rs, rootSeqDesc_length hf] using this⟩ =
                (rootSeqDesc f).get
                  ⟨(rootSeqDesc f).length - 1 - (k + 1), by lia⟩ := by simp [rs]
            _ = (rootSeqDesc f).get ⟨j, by
                  rw [rootSeqDesc_length hf]
                  dsimp [j]
                  lia⟩ := by
                  apply congrArg (fun i => (rootSeqDesc f).get i)
                  apply Fin.ext
                  exact hidx
        rw [hss_get, hrs_get]
        exact hup

/-- Internal construction bridge for the compatibility parent and the
finite-family upgrade layer. -/
protected def CommonInterleaver.polyOfDescRoots (xs : List ℝ) : ℝ[X] :=
  polyOfDescRoots xs

/-- Internal root-multiset bridge for the compatibility parent. -/
protected lemma CommonInterleaver.roots_polyOfDescRoots (xs : List ℝ) :
    (CommonInterleaver.polyOfDescRoots xs).roots = (↑xs : Multiset ℝ) := by
  simpa [CommonInterleaver.polyOfDescRoots] using roots_polyOfDescRoots xs

/-- Internal descending-root-sequence bridge for the compatibility parent. -/
protected lemma CommonInterleaver.rootSeqDesc_polyOfDescRoots_eq
    {xs : List ℝ} (hxs : xs.Pairwise (· ≥ ·)) :
    rootSeqDesc (CommonInterleaver.polyOfDescRoots xs) = xs := by
  simpa [CommonInterleaver.polyOfDescRoots] using rootSeqDesc_polyOfDescRoots_eq hxs

/-- Internal right-oriented slot-construction bridge. -/
protected lemma CommonInterleaver.prec_of_slots_polyOfDescRoots
    {f : ℝ[X]} {xs : List ℝ} (hf₀ : f ≠ 0) (hf : f.Splits)
    (hxs : xs.Pairwise (· ≥ ·))
    (hdeg_lo : f.natDegree ≤ xs.length)
    (hdeg_hi : xs.length ≤ f.natDegree + 1)
    (hslot : ∀ j (hj : j < xs.length),
      xs.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j, by
          have : j < f.natDegree + 1 := lt_of_lt_of_le hj hdeg_hi
          simpa [hf] using this⟩) :
    Prec f (CommonInterleaver.polyOfDescRoots xs) := by
  simpa [CommonInterleaver.polyOfDescRoots] using
    prec_of_slots_polyOfDescRoots hf₀ hf hxs hdeg_lo hdeg_hi hslot

/-- Internal left-oriented shifted-slot-construction bridge. -/
protected lemma CommonInterleaver.prec_left_of_shifted_slots_polyOfDescRoots
    {f : ℝ[X]} {xs : List ℝ} (hf₀ : f ≠ 0) (hf : f.Splits)
    (hxs : xs.Pairwise (· ≥ ·))
    (hdeg_lo : xs.length ≤ f.natDegree)
    (hdeg_hi : f.natDegree ≤ xs.length + 1)
    (hslot : ∀ j (hj : j < xs.length),
      xs.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j + 1, by
          have : j < f.natDegree := lt_of_lt_of_le hj hdeg_lo
          simpa [rootSeqDesc_length hf] using Nat.succ_lt_succ this⟩) :
    Prec (CommonInterleaver.polyOfDescRoots xs) f := by
  simpa [CommonInterleaver.polyOfDescRoots] using
    prec_left_of_shifted_slots_polyOfDescRoots hf₀ hf hxs hdeg_lo hdeg_hi hslot

end RealRooted
